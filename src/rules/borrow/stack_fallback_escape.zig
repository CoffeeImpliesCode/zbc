//! ghostty-org/ghostty#9885 class — `std.heap.stackFallback(N,
//! <alloc>)` returns an allocator whose small allocations land in
//! the *caller's* stack frame.  When a value-yielding method on a
//! container built over `<SF>.get()` (e.g. `toOwnedSlice`) is
//! returned without first being copied through the real allocator,
//! the slice points into the dead stack buffer once the fn frame
//! exits — UAF whenever the allocation stays under N.
//!
//! Three phases per fn:
//!   1. Find `var/const <SF> = …stackFallback(…)…` bindings.
//!   2. Track SF-tainted locals: bindings whose RHS contains
//!      `<SF>.get()` (direct taint) or mentions an already-tainted
//!      ident (transitive taint, declaration-order).
//!   3. Walk returns; fire if the value contains a
//!      `<tainted>.<sinkMethod>(...)` call AND has no sanitizing
//!      `.dupe*`/`.alloc*`/`.create*` call (the canonical fix).

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const query = @import("../../ast/token_query.zig");
const problem_mod = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const Atom = query.Atom;
const R = "stack-fallback-escape";

// `stackFallback(...)` anywhere in RHS — sentinel for SF bindings.
const stack_fallback_pattern = &[_]Atom{
    .{ .text = "stackFallback" },
    .{ .tok = .l_paren },
};

// `.<sanitizer>(` — `dupe`/`dupeZ`/`alloc`/`allocSentinel`/`create`.
// Presence in a return value flags it as the canonical fix
// (copy through a real allocator); the rule must NOT fire.
const sanitizer_call_pattern = &[_]Atom{
    .{ .tok = .period },
    .{ .pred = isSanitizingMethod },
    .{ .tok = .l_paren },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .stack_fallback_escape)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Cheap pre-scan: skip fns that don't even mention stackFallback.
    if (!tokens.hasIdentInRange(tree, first, last, "stackFallback")) return;

    const bindings = try cache.localBindings(proto, body);

    // Phase 1: SF bindings.
    var sf_names: std.ArrayListUnmanaged([]const u8) = .empty;
    defer sf_names.deinit(gpa);
    for (bindings.items) |b| {
        if (b.origin == .param) continue;
        if (query.anyMatchAnywhere(tree, stack_fallback_pattern, b.rhs_first, b.rhs_last, null)) {
            try sf_names.append(gpa, b.name);
        }
    }
    if (sf_names.items.len == 0) return;

    // Phase 2: tainted locals.  Bindings are iterated in declaration
    // order (local.build appends in body-token order), so the
    // transitive "RHS mentions a tainted ident" check works as a
    // single forward pass.
    var tainted: std.StringHashMapUnmanaged(void) = .empty;
    defer tainted.deinit(gpa);
    for (bindings.items) |b| {
        if (b.origin == .param) continue;
        if (std.mem.eql(u8, b.name, "_")) continue;
        if (rhsIsTainted(tree, b, sf_names.items, &tainted)) {
            try tainted.put(gpa, b.name, {});
        }
    }

    // Phase 3: scan returns for `<tainted>.<sink>(...)` not preceded
    // by sanitizing `.dupe*`/`.alloc*`/`.create*` in the return value.
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] != .keyword_return) continue;
        const sc = tokens.findStmtSemicolon(tags, t + 1, last) orelse continue;
        if (sc <= t + 1) continue;
        const value_last = sc - 1;
        if (query.anyMatchAnywhere(tree, sanitizer_call_pattern, t + 1, value_last, null)) continue;
        if (findTaintedSinkCall(tree, t + 1, value_last, &tainted)) |hit| {
            try report(gpa, problems, tree, t, hit.local, hit.method);
        }
    }
}

/// True iff the binding's RHS is SF-tainted: either contains
/// `<sf>.get(` for some sf in `sf_names`, or mentions an
/// identifier already in `tainted`.
fn rhsIsTainted(
    tree: *const Ast,
    b: local_bindings.Binding,
    sf_names: []const []const u8,
    tainted: *const std.StringHashMapUnmanaged(void),
) bool {
    // Direct: `<sf>.get(` for some known sf.  Build the pattern at
    // runtime since .text takes any []const u8 slice.
    for (sf_names) |sf| {
        const sf_get = [_]Atom{
            .{ .text = sf },
            .{ .tok = .period },
            .{ .text = "get" },
            .{ .tok = .l_paren },
        };
        if (query.anyMatchAnywhere(tree, &sf_get, b.rhs_first, b.rhs_last, null)) return true;
    }
    // Transitive: any identifier in RHS is already tainted.
    const tags = tree.tokens.items(.tag);
    var u: Ast.TokenIndex = b.rhs_first;
    while (u <= b.rhs_last) : (u += 1) {
        if (tags[u] != .identifier) continue;
        if (tainted.contains(tree.tokenSlice(u))) return true;
    }
    return false;
}

const Hit = struct {
    local: []const u8,
    method: []const u8,
};

/// Find `<tainted_ident>.<sinkMethod>(` in `[start, end]`.
fn findTaintedSinkCall(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    tainted: *const std.StringHashMapUnmanaged(void),
) ?Hit {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var t: Ast.TokenIndex = start;
    while (t + 3 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        const local_name = tree.tokenSlice(t);
        if (!tainted.contains(local_name)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        const method = tree.tokenSlice(t + 2);
        if (!isSinkMethodName(method)) continue;
        return .{ .local = local_name, .method = method };
    }
    return null;
}

fn isSanitizingMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "dupe") or
        std.mem.eql(u8, name, "dupeZ") or
        std.mem.eql(u8, name, "alloc") or
        std.mem.eql(u8, name, "allocSentinel") or
        std.mem.eql(u8, name, "create");
}

fn isSinkMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "toOwnedSlice") or
        std.mem.eql(u8, name, "toOwnedSliceSentinel") or
        std.mem.eql(u8, name, "allocPrint") or
        std.mem.eql(u8, name, "allocPrintZ") or
        std.mem.eql(u8, name, "allocPrintSentinel") or
        std.mem.eql(u8, name, "concat") or
        std.mem.eql(u8, name, "join") or
        std.mem.eql(u8, name, "joinZ");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    return_tok: Ast.TokenIndex,
    local_name: []const u8,
    method: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s}()` returns a slice into the `stackFallback(...)` buffer in the caller's stack frame — escaping it via `return` dangles the pointer once this fn exits.  Bind the result locally and `try <inner_alloc>.dupe*(...)` it before returning",
        .{ local_name, method },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, return_tok),
        .end = try Pos.fromTokenEnd(tree, return_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "`return cmd.toOwnedSlice()` from SF-tainted local fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Builder = struct {
        \\    pub fn init(_: std.mem.Allocator) Builder { return .{}; }
        \\    pub fn toOwnedSlice(_: *Builder) ![]u8 { return &.{}; }
        \\};
        \\const Shell = struct { shell: []u8 };
        \\pub fn setup(alloc: std.mem.Allocator) !Shell {
        \\    var sf = std.heap.stackFallback(4096, alloc);
        \\    var cmd = Builder.init(sf.get());
        \\    return .{ .shell = try cmd.toOwnedSlice() };
        \\}
    );
}

test "dupe through inner allocator is OK" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Builder = struct {
        \\    pub fn init(_: std.mem.Allocator) Builder { return .{}; }
        \\    pub fn toOwnedSlice(_: *Builder) ![]u8 { return &.{}; }
        \\};
        \\const Shell = struct { shell: []u8 };
        \\pub fn setup(alloc: std.mem.Allocator) !Shell {
        \\    var sf = std.heap.stackFallback(4096, alloc);
        \\    var cmd = Builder.init(sf.get());
        \\    const tmp = try cmd.toOwnedSlice();
        \\    return .{ .shell = try alloc.dupe(u8, tmp) };
        \\}
    );
}

test "no stackFallback present is silent" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Builder = struct {
        \\    pub fn init(_: std.mem.Allocator) Builder { return .{}; }
        \\    pub fn toOwnedSlice(_: *Builder) ![]u8 { return &.{}; }
        \\};
        \\pub fn setup(alloc: std.mem.Allocator) ![]u8 {
        \\    var cmd = Builder.init(alloc);
        \\    return try cmd.toOwnedSlice();
        \\}
    );
}

test "SF-tainted local consumed only locally is OK" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Builder = struct {
        \\    pub fn init(_: std.mem.Allocator) Builder { return .{}; }
        \\    pub fn toOwnedSlice(_: *Builder) ![]u8 { return &.{}; }
        \\    pub fn deinit(_: *Builder) void {}
        \\};
        \\pub fn doStuff(alloc: std.mem.Allocator, _: usize) !void {
        \\    var sf = std.heap.stackFallback(4096, alloc);
        \\    var cmd = Builder.init(sf.get());
        \\    defer cmd.deinit();
        \\    const slice = try cmd.toOwnedSlice();
        \\    _ = slice;
        \\}
    );
}

test "transitive taint via inner var fires when returned" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Inner = struct {
        \\    pub fn init(_: std.mem.Allocator) Inner { return .{}; }
        \\};
        \\const Outer = struct {
        \\    pub fn init(_: Inner) Outer { return .{}; }
        \\    pub fn toOwnedSlice(_: *Outer) ![]u8 { return &.{}; }
        \\};
        \\pub fn build(alloc: std.mem.Allocator) ![]u8 {
        \\    var sf = std.heap.stackFallback(4096, alloc);
        \\    const inner = Inner.init(sf.get());
        \\    var outer = Outer.init(inner);
        \\    return try outer.toOwnedSlice();
        \\}
    );
}
