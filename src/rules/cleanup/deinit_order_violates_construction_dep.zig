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
//!      `<A>.init(&<B>, ...)` — meaning A depends on B.  Both
//!      LHS receiver chains (`a`, `env.grid_verify`) are
//!      flattened to the last identifier for comparison.
//!   3. Collect `<X>.deinit(...)` calls and their enclosing defer.
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

const Dep = struct {
    a_name: []const u8, // last identifier of the LHS receiver chain
    b_name: []const u8, // last identifier of the &b argument
};

const Deferred = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    scope_last: Ast.TokenIndex,
};

const Deinit = struct {
    recv_name: []const u8, // Last identifier of `<chain>.deinit(`.
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
            if (tree.nodeTag(statement) != .@"defer") continue;
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
                if (std.mem.eql(u8, d.a_name, later.recv_name) and
                    std.mem.eql(u8, d.b_name, earlier.recv_name))
                {
                    try report(gpa, problems, tree, later.tok, d.a_name, d.b_name);
                    break;
                }
            }
        }
    }
}

/// Walk forward through the receiver chain starting at `start`
/// and return the LAST identifier segment.
fn lastIdentSegment(tree: *const Ast, tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, last: Ast.TokenIndex) []const u8 {
    var t: Ast.TokenIndex = start;
    var last_ident = start;
    while (t <= last) : (t += 1) {
        if (tags[t] == .identifier) last_ident = t;
        if (tags[t] == .period and t + 1 <= last and tags[t + 1] == .identifier) continue;
        if (t > start and tags[t] != .identifier and tags[t] != .period) break;
    }
    return tree.tokenSlice(last_ident);
}

/// Walk backward from `period_tok` (the `.` before `init` /
/// `deinit`) through the receiver chain and return the LAST
/// identifier segment (the closest one to the method).
fn lastIdentSegmentBack(tree: *const Ast, tags: []const std.zig.Token.Tag, period_tok: Ast.TokenIndex) []const u8 {
    if (period_tok == 0) return &.{};
    if (tags[period_tok - 1] != .identifier) return &.{};
    return tree.tokenSlice(period_tok - 1);
}

/// Find the assignee identifier name for an init call.  Walks
/// back from the `init` token to find either `<lhs> = <T>.init(`
/// or `<lhs-chain>.init(` shapes.  Returns the LAST identifier
/// of the LHS (e.g. `grid_verify` for `env.grid_verify = ...`).
fn findInitAssignee(tree: *const Ast, tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, init_tok: Ast.TokenIndex) ?[]const u8 {
    // Walk back across the receiver chain that ends at `.init`.
    var t: Ast.TokenIndex = init_tok;
    if (t < 2) return null;
    t -= 2; // skip `.` and method
    // Walk back across the type-name chain: `<T1>.<T2>...<Tn>`.
    while (t >= 2 and tags[t] == .identifier and tags[t - 1] == .period and tags[t - 2] == .identifier) {
        t -= 2;
    }
    if (tags[t] != .identifier) return null;
    // At this point `t` is the leftmost identifier before the
    // type/method chain.  Two cases:
    //   A) `<a> = <T>.init(...)` — the token before `t` is `=`.
    //      Walk back over `=` and over the LHS receiver chain.
    //   B) `<chain>.init(...)` — `t` IS the assignee's leftmost
    //      receiver (no `=` involved).
    if (t == 0 or tags[t - 1] != .equal) {
        // Case B: assignee is the chain ending here.  Return the
        // chain's LAST identifier (the rightmost).
        return tree.tokenSlice(t);
    }
    // Case A: walk back over `=` then back through `<lhs-chain>`.
    var u: Ast.TokenIndex = t - 2; // skip space + `=`... well, no space tokens; just `=`.
    if (u < first) return null;
    if (tags[u] != .identifier) return null;
    const last_ident = u;
    // (Walk back to find the leftmost segment, even though we
    // return the rightmost — purely to validate the chain shape.)
    while (u >= 2 and tags[u - 1] == .period and tags[u - 2] == .identifier) {
        u -= 2;
    }
    return tree.tokenSlice(last_ident);
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
