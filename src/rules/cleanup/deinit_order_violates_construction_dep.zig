//! Deinit-order-violates-construction-dep detector — within a
//! single fn body, two struct instances `A` and `B` are
//! constructed via `<A> = <T>.init(&<B>, ...)` (so `A` depends
//! on `B`).  Later, the same fn calls `<B>.deinit(...)` BEFORE
//! `<A>.deinit(...)`.  `A`'s deinit may dereference its
//! borrowed `B` pointer — but `B` is already torn down.
//!
//! Real-world: tigerbeetle/tigerbeetle#3732 (`manifest_log_fuzz.zig`:
//! `env.grid_verify.deinit()` ran before `env.manifest_log_verify.deinit()`,
//! and ManifestLog holds a pointer to Grid).
//!
//! Detection (syntactic dep edges, AST deferred scopes):
//!   1. Skip comptime type-builder fns.
//!   2. Collect "dep" edges: `<A> = <T>.init(&<B>, ...)` or
//!      `<A>.init(&<B>, ...)` — meaning A depends on B. Owners are
//!      compared by their complete paths, not their leaf members.
//!   3. Collect `<X>.deinit(...)` calls and their enclosing defer/errdefer.
//!      Compare execution order: separate defers in one scope run
//!      LIFO, while calls within one deferred body keep source order.
//!      Report the dependent's deinit when its dependency runs first.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const skipNestedFn = tokens.skipNestedFn;
const returnsType = tokens.returnsType;
const bodyOf = tokens.bodyOf;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .deinit_order_violates_construction_dep)) return;
    _ = cache;

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        if (returnsType(tree, node)) continue;
        const body = bodyOf(tree, node) orelse continue;
        try checkBody(gpa, tree, body, problems);
    }
}

const Owner = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,

    fn eql(self: Owner, tree: *const Ast, other: Owner) bool {
        if (self.last - self.first != other.last - other.first) return false;
        for (0..self.last - self.first + 1) |offset| {
            const n: Ast.TokenIndex = @intCast(offset);
            if (!std.mem.eql(u8, tree.tokenSlice(self.first + n), tree.tokenSlice(other.first + n))) return false;
        }
        return true;
    }

    fn text(self: Owner, tree: *const Ast) []const u8 {
        const starts = tree.tokens.items(.start);
        return tree.source[starts[self.first] .. starts[self.last] + tree.tokenSlice(self.last).len];
    }
};

const Dep = struct {
    a_name: Owner,
    b_name: Owner,
};

const Deferred = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    scope_last: Ast.TokenIndex,
};

const Deinit = struct {
    recv_name: Owner,
    tok: Ast.TokenIndex,
    deferred: ?Deferred,

    fn runsBefore(self: Deinit, other: Deinit, defers: []const Deferred) bool {
        var self_deferred = self.deferred;
        var other_deferred = other.deferred;
        while (true) {
            const self_at = if (self_deferred) |d| d.scope_last else self.tok;
            const other_at = if (other_deferred) |d| d.scope_last else other.tok;
            if (self_at != other_at) return self_at < other_at;
            if (self_deferred) |self_defer| {
                if (other_deferred) |other_defer| {
                    // Separate registrations reverse. A shared deferred body
                    // instead compares its own immediate and deferred calls.
                    if (self_defer.first != other_defer.first) {
                        return self_defer.first > other_defer.first;
                    }
                    self_deferred = deferredDeinit(defers, self.tok, self_defer.first);
                    other_deferred = deferredDeinit(defers, other.tok, other_defer.first);
                    continue;
                }
            }
            return self.tok < other.tok;
        }
    }
};

/// Return the outermost deferred statement below an already shared body.
/// Each descent increases `after`, so nested cleanup comparisons terminate.
fn deferredDeinit(
    defers: []const Deferred,
    t: Ast.TokenIndex,
    after: Ast.TokenIndex,
) ?Deferred {
    var enclosing: ?Deferred = null;
    for (defers) |d| {
        if (d.first <= after or t <= d.first or t > d.last) continue;
        if (enclosing == null or d.first < enclosing.?.first) enclosing = d;
    }
    return enclosing;
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var deps: std.ArrayListUnmanaged(Dep) = .empty;
    defer deps.deinit(gpa);

    // Collect dep edges: `<A> = ...<T>.init(&<B>, ...)` or
    // `<A>.init(&<B>, ...)`.
    var t: Ast.TokenIndex = first;
    while (t + 3 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Look for `init(` followed by `&<ident>` as first arg.
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "init")) continue;
        if (t == 0 or tags[t - 1] != .period) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (t + 3 > last) continue;
        if (tags[t + 2] != .ampersand) continue;
        if (tags[t + 3] != .identifier) continue;
        const b_name = lastIdentSegment(tree, tags, t + 3, last);
        // Find LHS — walk back to the `=` or to the start of the
        // assignee chain.  Pattern A: `<lhs-chain> = <T>.init(...)`.
        // Pattern B: `<lhs-chain>.init(...)` — first method-call
        // form.
        const a_name = findInitAssignee(tree, tags, first, t) orelse continue;
        try deps.append(gpa, .{ .a_name = a_name, .b_name = b_name });
    }
    if (deps.items.len == 0) return;

    var defers: std.ArrayListUnmanaged(Deferred) = .empty;
    defer defers.deinit(gpa);
    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        var buffer: [2]Ast.Node.Index = undefined;
        const statements = tree.blockStatements(&buffer, node) orelse continue;
        const scope_first = tree.firstToken(node);
        const scope_last = tree.lastToken(node);
        if (scope_first < first or scope_last > last) continue;
        for (statements) |statement| {
            if (tree.nodeTag(statement) != .@"defer" and tree.nodeTag(statement) != .@"errdefer") continue;
            try defers.append(gpa, .{
                .first = tree.firstToken(statement),
                .last = tree.lastToken(statement),
                .scope_last = scope_last,
            });
        }
    }

    // Collect deinit calls in source order: `<chain>.deinit(`.
    var deinits: std.ArrayListUnmanaged(Deinit) = .empty;
    defer deinits.deinit(gpa);
    t = first;
    while (t + 3 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "deinit")) continue;
        if (t == 0 or tags[t - 1] != .period) continue;
        if (tags[t + 1] != .l_paren) continue;
        const recv = lastIdentSegmentBack(tree, tags, t - 1);
        const deferred = deferredDeinit(defers.items, t, 0);
        try deinits.append(gpa, .{ .recv_name = recv, .tok = t, .deferred = deferred });
    }
    if (deinits.items.len < 2) return;

    // Compare actual cleanup order, not the spelling order of registrations.
    for (deinits.items, 0..) |di, i| {
        for (deinits.items[i + 1 ..]) |dj| {
            const di_first = di.runsBefore(dj, defers.items);
            const earlier = if (di_first) di else dj;
            const later = if (di_first) dj else di;
            for (deps.items) |d| {
                if (d.a_name.eql(tree, later.recv_name) and
                    d.b_name.eql(tree, earlier.recv_name))
                {
                    try report(gpa, problems, tree, later.tok, d.a_name.text(tree), d.b_name.text(tree));
                    break;
                }
            }
        }
    }
}

/// Keep the complete source owner path. Equal member names in different
/// objects do not identify the same cleanup target.
fn lastIdentSegment(_: *const Ast, tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, last: Ast.TokenIndex) Owner {
    var end = start;
    while (end + 2 <= last and tags[end + 1] == .period and tags[end + 2] == .identifier) end += 2;
    return .{ .first = start, .last = end };
}

fn lastIdentSegmentBack(_: *const Ast, tags: []const std.zig.Token.Tag, period_tok: Ast.TokenIndex) Owner {
    const end = period_tok - 1;
    var start = end;
    while (start >= 2 and tags[start - 1] == .period and tags[start - 2] == .identifier) start -= 2;
    return .{ .first = start, .last = end };
}

/// The constructor receiver is a type path; an assignment's owner is
/// its LHS. `try` changes neither that owner nor the actual dependency.
fn findInitAssignee(tree: *const Ast, tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, init_tok: Ast.TokenIndex) ?Owner {
    // A declared type annotation sits before `=` too. The declaration's
    // binding token, not that type token, owns the constructor result.
    var index: u32 = 1;
    while (index < tree.nodes.len) : (index += 1) {
        const node: Ast.Node.Index = @enumFromInt(index);
        const declaration = tree.fullVarDecl(node) orelse continue;
        if (tree.firstToken(node) < first) continue;
        const initializer = declaration.ast.init_node.unwrap() orelse continue;
        if (tree.firstToken(initializer) > init_tok or tree.lastToken(initializer) < init_tok) continue;
        const name = declaration.ast.mut_token + 1;
        return .{ .first = name, .last = name };
    }
    if (init_tok < 2 or tags[init_tok - 2] != .identifier) return null;
    const receiver = lastIdentSegmentBack(tree, tags, init_tok - 1);
    var before = receiver.first;
    if (before > first and tags[before - 1] == .keyword_try) before -= 1;
    if (before == 0 or tags[before - 1] != .equal) return receiver;
    if (before < 2 or tags[before - 2] != .identifier) return null;
    return lastIdentSegmentBack(tree, tags, before - 1);
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    deinit_tok: Ast.TokenIndex,
    a_name: []const u8,
    b_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.deinit(...)` runs AFTER `{s}.deinit(...)` — but `{s}` was constructed via `.init(&{s}, ...)`, so `{s}` borrows from `{s}` and its deinit may dereference a torn-down value.  Reverse the order (LIFO)",
        .{ a_name, b_name, a_name, b_name, a_name, b_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "deinit-order-violates-construction-dep",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, deinit_tok),
        .end = try Pos.fromTokenEnd(tree, deinit_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "deinit-order-violates-construction-dep: LIFO violation fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Grid = struct {
        \\    pub fn init() Grid { return .{}; }
        \\    pub fn deinit(_: *Grid) void {}
        \\};
        \\const ManifestLog = struct {
        \\    pub fn init(_: *Grid) ManifestLog { return .{}; }
        \\    pub fn deinit(_: *ManifestLog) void {}
        \\};
        \\pub fn run() void {
        \\    var grid_verify = Grid.init();
        \\    var manifest_log_verify = ManifestLog.init(&grid_verify);
        \\    grid_verify.deinit();
        \\    manifest_log_verify.deinit();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
    try std.testing.expectEqualStrings("deinit-order-violates-construction-dep", problems.items[0].rule_id);
}

test "deinit-order-violates-construction-dep: field receiver chains fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Grid = struct {
        \\    pub fn init() Grid { return .{}; }
        \\    pub fn deinit(_: *Grid) void {}
        \\};
        \\const ManifestLog = struct {
        \\    pub fn init(_: *Grid) ManifestLog { return .{}; }
        \\    pub fn deinit(_: *ManifestLog) void {}
        \\};
        \\const Env = struct { grid: Grid, log: ManifestLog };
        \\pub fn run() void {
        \\    var env: Env = undefined;
        \\    env.grid = Grid.init();
        \\    env.log = ManifestLog.init(&env.grid);
        \\    env.grid.deinit();
        \\    env.log.deinit();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
    try std.testing.expectEqualStrings("deinit-order-violates-construction-dep", problems.items[0].rule_id);
}

test "deinit-order-violates-construction-dep: independent types no fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const A = struct {
        \\    pub fn init() A { return .{}; }
        \\    pub fn deinit(_: *A) void {}
        \\};
        \\const B = struct {
        \\    pub fn init() B { return .{}; }
        \\    pub fn deinit(_: *B) void {}
        \\};
        \\pub fn run() void {
        \\    var a = A.init();
        \\    var b = B.init();
        \\    a.deinit();
        \\    b.deinit();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: correct LIFO order doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Grid = struct {
        \\    pub fn init() Grid { return .{}; }
        \\    pub fn deinit(_: *Grid) void {}
        \\};
        \\const ManifestLog = struct {
        \\    pub fn init(_: *Grid) ManifestLog { return .{}; }
        \\    pub fn deinit(_: *ManifestLog) void {}
        \\};
        \\pub fn run() void {
        \\    var grid_verify = Grid.init();
        \\    var manifest_log_verify = ManifestLog.init(&grid_verify);
        \\    manifest_log_verify.deinit();
        \\    grid_verify.deinit();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: defer LIFO reversal is correct, no fire" {
    // `defer` reverses source order: `defer qc.deinit()` (line 2) runs BEFORE
    // `defer tls_ctx.deinit()` (line 1) at scope exit — correct dependency order.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const TlsCtx = struct {
        \\    pub fn init() TlsCtx { return .{}; }
        \\    pub fn deinit(_: *TlsCtx) void {}
        \\};
        \\const QuicConn = struct {
        \\    pub fn init(_: *TlsCtx) QuicConn { return .{}; }
        \\    pub fn deinit(_: *QuicConn) void {}
        \\};
        \\pub fn run() void {
        \\    var tls_ctx = TlsCtx.init();
        \\    defer tls_ctx.deinit();
        \\    var qc = QuicConn.init(&tls_ctx);
        \\    defer qc.deinit();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: explicit b before deferred a fires" {
    // `b.deinit()` runs immediately (source line 1), `defer a.deinit()` runs at scope
    // exit (after b). a depends on b, so b must outlive a — this is wrong.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const B = struct {
        \\    pub fn init() B { return .{}; }
        \\    pub fn deinit(_: *B) void {}
        \\};
        \\const A = struct {
        \\    pub fn init(_: *B) A { return .{}; }
        \\    pub fn deinit(_: *A) void {}
        \\};
        \\pub fn run() void {
        \\    var b = B.init();
        \\    var a = A.init(&b);
        \\    b.deinit();
        \\    defer a.deinit();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
}

test "deinit-order-violates-construction-dep: conditional defers preserve correct LIFO" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    defer if (typed) context.deinit();
        \\    var resolver = Resolver.init(&context);
        \\    defer if (typed) resolver.deinit();
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: reversed conditional defers fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    var resolver = Resolver.init(&context);
        \\    defer if (typed) resolver.deinit();
        \\    defer if (typed) context.deinit();
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(
        "deinit-order-violates-construction-dep",
        problems.items[0].rule_id,
    );
}

test "deinit-order-violates-construction-dep: conditional defer blocks preserve LIFO" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    defer if (typed) {
        \\        context.deinit();
        \\    };
        \\    var resolver = Resolver.init(&context);
        \\    defer if (typed) {
        \\        resolver.deinit();
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: reversed conditional defer blocks fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    var resolver = Resolver.init(&context);
        \\    defer if (typed) {
        \\        resolver.deinit();
        \\    };
        \\    defer if (typed) {
        \\        context.deinit();
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "deinit-order-violates-construction-dep: one defer keeps internal source order" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    var resolver = Resolver.init(&context);
        \\    defer if (typed) {
        \\        resolver.deinit();
        \\        context.deinit();
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: reversed calls inside one defer fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    var resolver = Resolver.init(&context);
        \\    defer if (typed) {
        \\        context.deinit();
        \\        resolver.deinit();
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "deinit-order-violates-construction-dep: inner conditional defer runs first" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    var resolver = Resolver.init(&context);
        \\    {
        \\        defer if (typed) resolver.deinit();
        \\    }
        \\    defer if (typed) context.deinit();
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: inner dependency defer runs too early" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    var resolver = Resolver.init(&context);
        \\    defer if (typed) resolver.deinit();
        \\    {
        \\        defer if (typed) context.deinit();
        \\    }
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "deinit-order-violates-construction-dep: nested defer preserves dependency" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    var resolver = Resolver.init(&context);
        \\    defer if (typed) {
        \\        defer context.deinit();
        \\        resolver.deinit();
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: nested dependent defer runs too late" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn run(typed: bool) void {
        \\    var context = Context.init();
        \\    var resolver = Resolver.init(&context);
        \\    defer if (typed) {
        \\        defer resolver.deinit();
        \\        context.deinit();
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "deinit-order-violates-construction-dep: typed errdefer construction order" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRuleTyped(gpa, check,
        \\const Root = struct {
        \\    fn init() Root { return .{}; }
        \\    fn deinit(_: *Root) void {}
        \\};
        \\const Dependent = struct {
        \\    fn init(_: *Root) Dependent { return .{}; }
        \\    fn deinit(_: *Dependent) void {}
        \\};
        \\const Alias = Dependent;
        \\fn run() !void {
        \\    var root = Root.init();
        \\    errdefer root.deinit();
        \\    var dependent = Alias.init(&root);
        \\    errdefer dependent.deinit();
        \\    return error.Stop;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: typed reversed errdefer reports" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRuleTyped(gpa, check,
        \\const Root = struct { fn deinit(_: *Root) void {} };
        \\const Dependent = struct {
        \\    fn init(_: *Root) Dependent { return .{}; }
        \\    fn deinit(_: *Dependent) void {}
        \\};
        \\fn run() !void {
        \\    var root: Root = .{};
        \\    var dependent = Dependent.init(&root);
        \\    errdefer dependent.deinit();
        \\    errdefer root.deinit();
        \\    return error.Stop;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "deinit-order-violates-construction-dep: distinct owners and missing cleanup do not match" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRuleTyped(gpa, check,
        \\const Root = struct { fn deinit(_: *Root) void {} };
        \\const Dependent = struct {
        \\    fn init(_: *Root) Dependent { return .{}; }
        \\    fn deinit(_: *Dependent) void {}
        \\};
        \\const Env = struct { root: Root = .{}, child: Dependent = .{} };
        \\fn run() void {
        \\    var left: Env = .{};
        \\    var right: Env = .{};
        \\    left.child = Dependent.init(&left.root);
        \\    right.root.deinit();
        \\    left.child.deinit();
        \\}
        \\fn missing() void {
        \\    var root: Root = .{};
        \\    var dependent = Dependent.init(&root);
        \\    root.deinit();
        \\    _ = dependent;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deinit-order-violates-construction-dep: typed constructor assignee is not its annotation" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRuleTyped(gpa, check,
        \\const Root = struct { fn deinit(_: *Root) void {} };
        \\const Child = struct {
        \\    fn init(_: *Root) Child { return .{}; }
        \\    fn deinit(_: *Child) void {}
        \\};
        \\fn run() void {
        \\    var root: Root = .{};
        \\    var dependent: Child = Child.init(&root);
        \\    root.deinit();
        \\    dependent.deinit();
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "deinit-order-violates-construction-dep: imported constructor alias preserves actual owners" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "owners.zig", .data =
        \\pub const Root = struct { pub fn deinit(_: *Root) void {} };
        \\pub const Child = struct {
        \\    pub fn init(_: *Root) Child { return .{}; }
        \\    pub fn deinit(_: *Child) void {}
        \\};
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "use.zig" });
    defer gpa.free(path);
    const source =
        \\const lib = @import("owners.zig");
        \\const Constructor = lib.Child;
        \\const Env = struct { child: lib.Child = .{}, root: lib.Root = .{} };
        \\fn unsafeOrder() void {
        \\    var env: Env = .{};
        \\    env.child = Constructor.init(&env.root);
        \\    env.root.deinit();
        \\    env.child.deinit();
        \\}
        \\fn safeOrder() !void {
        \\    var env: Env = .{};
        \\    errdefer env.root.deinit();
        \\    env.child = Constructor.init(&env.root);
        \\    errdefer env.child.deinit();
        \\    return error.Stop;
        \\}
    ;
    var context: @import("../../type_resolver.zig").TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    var resolver: @import("../../type_resolver.zig").TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    cache.setZls(&resolver);
    defer cache.deinit();
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    try check(gpa, tree, &cache, &config_mod.Default, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}
