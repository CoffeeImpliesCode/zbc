//! Reports index subtraction when no path-sensitive positive bound is known.
//! Type names, nearby guard text, and assertions in other callers are not proofs.

const std = @import("std");
const Ast = std.zig.Ast;
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");
const budget_mod = @import("../../budget.zig");
const testing = @import("../../testing.zig");
const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "index-minus-one-without-zero-guard";
const peel_depth: u8 = 64;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .index_minus_one_without_zero_guard)) return;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .array_access) continue;
        const access: Ast.Node.Index = @enumFromInt(index);
        // `buf[@intCast(offset - 1)]` subtracts one exactly as `buf[offset
        // - 1]` does; reading the subscript as "anything but a subtraction"
        // drops those sites before the positivity question is asked.
        const subscript = (try peel(tree, tree.nodeData(access).node_and_node[1])) orelse continue;
        if (tree.nodeTag(subscript) != .sub) continue;
        const operands = tree.nodeData(subscript).node_and_node;
        const amount = (try peel(tree, operands[1])) orelse continue;
        if (tree.nodeTag(amount) != .number_literal) continue;
        const literal = std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(amount)), 0) catch continue;
        if (literal != 1) continue;
        const token = tree.nodeMainToken(access);
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        const body = tokens.bodyOf(tree, declaration).?;
        if (!try cache.isRuntimeUse(declaration, token)) continue;
        // The question is of the value the subtraction was computed from,
        // not of the type the cast will store it in: an unsigned
        // destination says how `offset - 1` is spelled, not that `offset`
        // was above zero.
        const source = (try peel(tree, operands[0])) orelse operands[0];
        if (try provesPositive(gpa, tree, body, source, token, cache)) continue;
        try report(gpa, problems, tree, access, operands[0]);
    }
}

/// The expression a subscript computes once parentheses and value casts are
/// taken off it.  `@intCast` and `@as` change how a value is written and
/// nothing else, so they are transparent here; any other builtin and any
/// call is a computation this file cannot see through, and is declined as
/// not a candidate.  A chain longer than the bound is not an answer either
/// — raising `error.AnalysisBudgetExceeded` says the peel did not finish,
/// where a node it never reached would quietly stand in for one it did.
fn peel(tree: *const Ast, node: Ast.Node.Index) (budget_mod.BudgetError || error{SourceTooWide})!?Ast.Node.Index {
    var result = node;
    var budget = peel_depth;
    while (budget != 0) {
        budget -= 1;
        switch (tree.nodeTag(result)) {
            .grouped_expression => result = tree.nodeData(result).node_and_token[0],
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                var buffer: [2]Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&buffer, result) orelse return null;
                const name = tree.tokenSlice(tree.nodeMainToken(result));
                if (params.len == 1 and std.mem.eql(u8, name, "@intCast")) {
                    result = params[0];
                    continue;
                }
                if (params.len == 2 and std.mem.eql(u8, name, "@as")) {
                    result = params[1];
                    continue;
                }
                return null;
            },
            else => return result,
        }
    }
    const token = tree.nodeMainToken(result);
    const site = try Pos.fromTokenStart(tree, token);
    var name: budget_mod.NameBuf = .{};
    if (tokens.enclosingFnDecl(tree, token)) |declaration| {
        var buffer: [1]Ast.Node.Index = undefined;
        if (tokens.fnProto(tree, &buffer, declaration)) |proto| {
            if (proto.name_token) |name_token| name.set(tree.tokenSlice(name_token));
        }
    }
    return budget_mod.fail(.{
        .limit = .index_minus_one_peel_depth,
        .limit_value = peel_depth,
        .reached = peel_depth,
        .byte = site.byte,
        .document = budget_mod.documentForTree(tree),
        .line = site.line,
        .column = site.column,
        .function = name,
    });
}

/// Is `node` provably at least 1 at `use_token`? Keep the complete expression,
/// including `.len`, so the oracle can match callee postconditions to the
/// receiver this use reads. Positivity combines two oracle channels.
///
/// Both are asked of the oracle rather than re-derived here. `provesPositive` carries the facts the
/// body walk recorded — a dominating `!= 0`, a loop bound, a copied depth —
/// and it reads the SIGN of the operand, so a signed `!= 0` is correctly
/// refused where "nonzero" alone would have accepted it.  `boundsAt` is the
/// numeric channel: it is the one query the oracle runs with its range table
/// populated, which is what carries a caller's own bound on the argument
/// through into this body.  Neither subsumes the other, so the bound is
/// positive when either one proves it — and only then.
fn provesPositive(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    node: Ast.Node.Index,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
) !bool {
    if (try value_range.provesPositive(gpa, tree, body, node, use_token, cache)) return true;
    const bounds = try value_range.boundsAt(gpa, tree, body, node, use_token, cache);
    return bounds == .integer and bounds.integer.min >= 1;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    access: Ast.Node.Index,
    operand: Ast.Node.Index,
) !void {
    const starts = tree.tokens.items(.start);
    const last = tree.lastToken(operand);
    const expression = tree.source[starts[tree.firstToken(operand)] .. starts[last] + tree.tokenSlice(last).len];
    const message = try std.fmt.allocPrint(gpa, "no positive lower bound was proved for `{s}` before subtracting 1 for an index; zero would underflow", .{expression});
    errdefer gpa.free(message);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .warning,
        .start = try Pos.fromTokenStart(tree, tree.nodeMainToken(access)),
        .end = try Pos.fromTokenEnd(tree, tree.lastToken(access)),
        .message = message,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "index-minus-one-without-zero-guard: basic fires" {
    try testing.expectFires(check, R,
        \\fn prev(items: []const u8, idx: usize) u8 {
        \\    return items[idx - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: field minus one fires" {
    try testing.expectFires(check, R,
        \\const Self = struct { current: usize, items: []const u8 };
        \\fn prev(self: Self) u8 {
        \\    return self.items[self.current - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: idx - 2 does not fire" {
    try testing.expectNoFire(check,
        \\fn f(items: []const u8, idx: usize) u8 {
        \\    return items[idx - 2];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: idx + 1 does not fire" {
    try testing.expectNoFire(check,
        \\fn f(items: []const u8, idx: usize) u8 {
        \\    return items[idx + 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: plain index does not fire" {
    try testing.expectNoFire(check,
        \\fn f(items: []const u8, idx: usize) u8 {
        \\    return items[idx];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: recv.field.len - 1 fires (Form C)" {
    try testing.expectFires(check, R,
        \\const Self = struct { args: []const u8 };
        \\fn deinit(self: *Self) void {
        \\    _ = self.args[self.args.len - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: recv.field.len - 2 does not fire" {
    try testing.expectNoFire(check,
        \\const Self = struct { args: []const u8 };
        \\fn f(self: *Self) void {
        \\    _ = self.args[self.args.len - 2];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form A suppressed by and-guard" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, x: usize) u8 {
        \\    return if (x > 0 and buf[x - 1] == 0) 1 else 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form A suppressed by != 0 and-guard" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, x: usize) u8 {
        \\    return if (x != 0 and buf[x - 1] == 0) 1 else 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form A fires when guard uses different ident" {
    try testing.expectFires(check, R,
        \\fn f(buf: []const u8, x: usize, y: usize) u8 {
        \\    return if (y > 0 and buf[x - 1] == 0) 1 else 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form B suppressed by and-guard on outer ident" {
    try testing.expectNoFire(check,
        \\fn f(items: []const u8, s: anytype) bool {
        \\    return s.len > 0 and items[s.len - 1] == 0;
        \\}
        \\
    );
}

// ── If-body guard tests ────────────────────────────────────────────────────

test "index-minus-one-without-zero-guard: Form A suppressed by if-body guard (simple)" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, x: usize) void {
        \\    if (x > 0) assert(buf[x - 1] == 0);
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form A suppressed by if-body guard (!= 0)" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, x: usize) void {
        \\    if (x != 0) doSomething(buf[x - 1]);
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form A fires when guard uses different ident (if-body)" {
    try testing.expectFires(check, R,
        \\fn f(buf: []const u8, x: usize, y: usize) void {
        \\    if (y > 0) _ = buf[x - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form A fires when if guard is followed by semicolon" {
    try testing.expectFires(check, R,
        \\fn f(buf: []const u8, x: usize) void {
        \\    if (x > 0) doSomething();
        \\    _ = buf[x - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form A suppressed inside multi-statement block" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, x: usize) void {
        \\    if (x > 0) {
        \\        doSomething();
        \\        _ = buf[x - 1];
        \\    }
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form B suppressed by if-body guard (dotted)" {
    try testing.expectNoFire(check,
        \\fn f(arr: []const u8, s: anytype) void {
        \\    if (s.len > 0) assert(arr[s.len - 1] == 0);
        \\}
        \\
    );
}

// ── Assert guard tests ─────────────────────────────────────────────────────

test "index-minus-one-without-zero-guard: Form A suppressed by assert guard (simple)" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn f(buf: []const u8, n: usize) u8 {
        \\    std.debug.assert(n > 0);
        \\    return buf[n - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form B suppressed by assert guard (dotted)" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn f(buf: []const u8, s: anytype) u8 {
        \\    std.debug.assert(s.len > 0);
        \\    return buf[s.len - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: assert guard with != 0 suppresses" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn f(buf: []const u8, n: usize) u8 {
        \\    std.debug.assert(n != 0);
        \\    return buf[n - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: assert guard on different ident still fires" {
    try testing.expectFires(check, R,
        \\fn f(buf: []const u8, n: usize, m: usize) u8 {
        \\    assert(m > 0);
        \\    return buf[n - 1];
        \\}
        \\
    );
}

// ── Early-return guard tests ───────────────────────────────────────────────

test "index-minus-one-without-zero-guard: Form A suppressed by early-return guard" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, n: usize) !u8 {
        \\    if (n == 0) return error.Empty;
        \\    return buf[n - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: Form B suppressed by early-return guard (dotted)" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, s: anytype) !u8 {
        \\    if (s.len == 0) return error.Empty;
        \\    return buf[s.len - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: early-return guard on different ident still fires" {
    try testing.expectFires(check, R,
        \\fn f(buf: []const u8, n: usize, m: usize) !u8 {
        \\    if (m == 0) return error.Empty;
        \\    return buf[n - 1];
        \\}
        \\
    );
}

// ── Comptime context tests ─────────────────────────────────────────────────

test "index-minus-one-without-zero-guard: comptime assert suppressed" {
    try testing.expectNoFire(check,
        \\fn f(comptime fmt: []const u8) void {
        \\    comptime assert(fmt[fmt.len - 1] == '\n');
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: runtime access still fires" {
    try testing.expectFires(check, R,
        \\fn f(buf: []const u8, n: usize) u8 {
        \\    return buf[n - 1];
        \\}
        \\
    );
}
// ── Else-body guard tests ──────────────────────────────────────────────────

test "index-minus-one-without-zero-guard: else-body guarded by == 0 condition" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, n: usize) u8 {
        \\    return if (n == 0) 0 else buf[n - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: else-block guarded by == 0 condition" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, idx: usize) u8 {
        \\    if (idx == 0) {
        \\        return 0;
        \\    } else {
        \\        return buf[idx - 1];
        \\    }
        \\}
        \\
    );
}

// ── Compound assert guard tests ────────────────────────────────────────────

test "index-minus-one-without-zero-guard: compound assert (and) suppresses" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn f(a: []const u8, b: []const u8) u8 {
        \\    std.debug.assert(a.len > 0 and b.len > 0);
        \\    return b[b.len - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: OR-short-circuit assert suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, n: usize) bool {
        \\    assert(n == 0 or buf[n - 1] == 0);
        \\    return true;
        \\}
        \\
    );
}

// ── Continue / break guard tests ───────────────────────────────────────────

test "index-minus-one-without-zero-guard: continue guard suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8) void {
        \\    for (0..buf.len) |i| {
        \\        if (i == 0) continue;
        \\        _ = buf[i - 1];
        \\    }
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: break guard suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, i: usize) void {
        \\    if (i == 0) break;
        \\    _ = buf[i - 1];
        \\}
        \\
    );
}

// ── Zero-access guard tests ────────────────────────────────────────────────

test "index-minus-one-without-zero-guard: prior [0] access suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8) u8 {
        \\    _ = buf[0];
        \\    return buf[buf.len - 1];
        \\}
        \\
    );
}

// ── Increment guard tests ──────────────────────────────────────────────────

test "index-minus-one-without-zero-guard: += 1 before subscript suppresses" {
    try testing.expectNoFire(check,
        \\fn f(arr: []u8, count: *usize) u8 {
        \\    count.* += 1;
        \\    return arr[count.* - 1];
        \\}
        \\
    );
}

// ── Init-to-one guard tests ────────────────────────────────────────────────

test "index-minus-one-without-zero-guard: var x = 1 suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8) void {
        \\    var count: usize = 1;
        \\    _ = buf[count - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: loop var starting at 1 suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8) void {
        \\    var i: usize = 1;
        \\    while (i < buf.len) : (i += 1) {
        \\        _ = buf[i - 1];
        \\    }
        \\}
        \\
    );
}

// ── Constants guard tests ──────────────────────────────────────────────────

test "index-minus-one-without-zero-guard: constants.X - 1 does not fire" {
    try testing.expectNoFireTyped(check,
        \\const constants = struct { const max_level = 4; };
        \\fn f(levels: anytype) void {
        \\    _ = levels[constants.max_level - 1];
        \\}
        \\
    );
}

// ── For-range (1..N) and literal-array guard tests ────────────────────────

test "index-minus-one-without-zero-guard: for (1..N) capture suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8) void {
        \\    for (1..buf.len) |i| {
        \\        _ = buf[i - 1];
        \\    }
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: for (2..N) capture suppresses" {
    try testing.expectNoFire(check,
        \\fn f(arr: []const u8) void {
        \\    for (2..arr.len) |i| {
        \\        _ = arr[i - 1];
        \\    }
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: for (0..N) capture still fires" {
    try testing.expectFires(check, R,
        \\fn f(arr: []const u8) void {
        \\    for (0..arr.len) |i| {
        \\        _ = arr[i - 1];
        \\    }
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: inline for over all-positive literals suppresses" {
    try testing.expectNoFire(check,
        \\fn f(blocks: []u8) void {
        \\    inline for ([_]usize{ 7, 6, 5, 4, 3, 2, 1 }) |i| {
        \\        blocks[i] = blocks[i - 1];
        \\    }
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: for over array containing 0 still fires" {
    try testing.expectFires(check, R,
        \\fn f(blocks: []u8) void {
        \\    for ([_]usize{ 3, 2, 1, 0 }) |i| {
        \\        blocks[i] = blocks[i - 1];
        \\    }
        \\}
        \\
    );
}

// ── Cross-pass 1: slice-to-len-minus-one guard tests ──────────────────────

test "index-minus-one-without-zero-guard: for input entries[0..entries.len-1] suppresses" {
    try testing.expectNoFire(check,
        \\fn f(entries: []const u8) void {
        \\    for (entries[0 .. entries.len - 1], entries[1..]) |a, b| {
        \\        _ = a;
        \\        _ = b;
        \\    }
        \\    _ = entries[entries.len - 1];
        \\}
        \\
    );
}

// ── Cross-pass 2: function-wide dotted assert tests ────────────────────────

test "index-minus-one-without-zero-guard: dominating standard assertion survives unrelated locals" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn f(buf: []const u8) u8 {
        \\    std.debug.assert(buf.len > 0);
        \\    const n = buf.len;
        \\    const x = n * 2;
        \\    _ = x;
        \\    return buf[buf.len - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: assert on different ident does not suppress" {
    try testing.expectFires(check, R,
        \\fn f(a: []const u8, b: []const u8) u8 {
        \\    assert(a.len > 0);
        \\    return b[b.len - 1];
        \\}
        \\
    );
}

// ── Cross-pass 3: callee postcondition tests ───────────────────────────────

test "index-minus-one-without-zero-guard: callee postcondition does not suppress different local" {
    try testing.expectFires(check, R,
        \\fn getSlice(msg: []const u8) Wrapper {
        \\    return .{ .slice = msg };
        \\}
        \\fn verify(msg: []const u8) void {
        \\    const h = getSlice(msg);
        \\    assert(h.slice.len >= 1);
        \\}
        \\fn use(msg: []const u8, other: []const u8) u8 {
        \\    _ = getSlice(msg);
        \\    return other[other.len - 1];
        \\}
        \\
    );
}

// ── Optional payload (getLastOrNull) guard tests ───────────────────────────

// ── Prior arithmetic guard tests ───────────────────────────────────────────

test "index-minus-one-without-zero-guard: prior arithmetic on different pair still fires" {
    try testing.expectFires(check, R,
        \\fn f(a: anytype, b: anytype, arr: []u8) void {
        \\    arr[0] = @intCast(a.len - 1); // guard on a.len, not b.len
        \\    _ = arr[b.len - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: getLastOrNull different base still fires" {
    try testing.expectFires(check, R,
        \\fn f(a: anytype, b: []const u8) void {
        \\    if (a.getLastOrNull()) |_| {
        \\        _ = b[b.len - 1];
        \\    }
        \\}
        \\
    );
}

// ── Cross-pass 4: alloc-plus-N tests ──────────────────────────────────────

test "index-minus-one-without-zero-guard: alloc with +1 size suppresses" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn f(gpa: std.mem.Allocator, src: []const u8) !void {
        \\    const buf = try gpa.alloc(u8, src.len + 1);
        \\    _ = buf[buf.len - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: alloc with +0 size still fires" {
    try testing.expectFires(check, R,
        \\fn f(gpa: anytype, src: []const u8) void {
        \\    const buf = try gpa.alloc(u8, src.len + 0);
        \\    _ = buf[buf.len - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: alloc different local still fires" {
    try testing.expectFires(check, R,
        \\fn f(gpa: anytype, src: []const u8, other: []const u8) void {
        \\    _ = try gpa.alloc(u8, src.len + 1);
        \\    _ = other[other.len - 1];
        \\}
        \\
    );
}

// ── Cross-variable >= N+M guard tests (#7) ────────────────────────────────

test "index-minus-one-without-zero-guard: x >= y+2 and-guard suppresses" {
    // span_end >= span_start + 2 guarantees span_end >= 2 > 0.
    try testing.expectNoFire(check,
        \\fn f(src: []const u8, span_end: usize, span_start: usize) bool {
        \\    if (span_end >= span_start + 2 and src[span_end - 1] == '{') return true;
        \\    return false;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: x >= y+1 and-guard suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, end: usize, start: usize) u8 {
        \\    return if (end >= start + 1 and buf[end - 1] == 0) 1 else 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: x >= y+2 in if-body suppresses" {
    try testing.expectNoFire(check,
        \\fn f(src: []const u8, end: usize, start: usize) u8 {
        \\    if (end >= start + 2) return src[end - 1];
        \\    return 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: x >= y+0 does not suppress" {
    // N == 0 does not imply x >= 1.
    try testing.expectFires(check, R,
        \\fn f(src: []const u8, end: usize, start: usize) u8 {
        \\    return if (end >= start + 0 and src[end - 1] == 0) 1 else 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: different ident >= y+2 still fires" {
    try testing.expectFires(check, R,
        \\fn f(src: []const u8, end: usize, start: usize, other: usize) u8 {
        \\    return if (other >= start + 2 and src[end - 1] == 0) 1 else 0;
        \\}
        \\
    );
}

// ── Cross-variable early-exit guard tests (#7b) ───────────────────────────

test "index-minus-one-without-zero-guard: if (x < y+N) return suppresses" {
    // After `if (end < start + 2) return null`, end >= start+2 >= 2 > 0.
    try testing.expectNoFire(check,
        \\fn f(tags: []const u8, end: usize, start: usize) ?u8 {
        \\    if (end < start + 2) return null;
        \\    return tags[end - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: if (x < y+1) return suppresses" {
    try testing.expectNoFire(check,
        \\fn f(tags: []const u8, rparen: usize, t: usize) ?u8 {
        \\    if (rparen < t + 1) return null;
        \\    return tags[rparen - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: if (x < y+0) return does not suppress" {
    // N == 0 does not guarantee x >= 1.
    try testing.expectFires(check, R,
        \\fn f(tags: []const u8, end: usize, start: usize) ?u8 {
        \\    if (end < start + 0) return null;
        \\    return tags[end - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: different ident in if-x-lt-y+N still fires" {
    // `other < start + 2` guards `other`, not `end`.
    try testing.expectFires(check, R,
        \\fn f(tags: []const u8, end: usize, start: usize, other: usize) ?u8 {
        \\    if (other < start + 2) return null;
        \\    return tags[end - 1];
        \\}
        \\
    );
}

// ── Compound or early-return guard tests (#8) ─────────────────────────────

test "index-minus-one-without-zero-guard: if (e <= s or ...) return suppresses" {
    // e <= s catches e == 0 (usize), so after the return e >= 1.
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, e: usize, s: usize, len: usize) !u8 {
        \\    if (e <= s or e > len) return error.OutOfRange;
        \\    return buf[e - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: if (e <= s) return suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, e: usize, s: usize) !u8 {
        \\    if (e <= s) return error.Empty;
        \\    return buf[e - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: compound or-return on different ident still fires" {
    try testing.expectFires(check, R,
        \\fn f(buf: []const u8, e: usize, s: usize, other: usize) !u8 {
        \\    if (other <= s or other > buf.len) return error.OutOfRange;
        \\    return buf[e - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: if (A or p.tok_i == 0) return suppresses dotted" {
    // `p.tok_i == 0` is the RHS of OR early-return; after return tok_i != 0.
    try testing.expectNoFireTyped(check,
        \\fn emitJsxGap(p: *Parser, last_child_was_text: bool, starts: []u32, lens: []u16) !void {
        \\    if (last_child_was_text or p.tok_i == 0) return;
        \\    const prev_end = starts[p.tok_i - 1] + lens[p.tok_i - 1];
        \\    _ = prev_end;
        \\}
        \\const Parser = struct { tok_i: usize };
        \\
    );
}

test "index-minus-one-without-zero-guard: if (A or x == 0) return suppresses simple" {
    try testing.expectNoFire(check,
        \\fn f(buf: []const u8, flag: bool, x: usize) !u8 {
        \\    if (flag or x == 0) return error.Empty;
        \\    return buf[x - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: if (A or other == 0) return still fires for different ident" {
    // `other == 0` guards `other`, not `x`.
    try testing.expectFires(check, R,
        \\fn f(buf: []const u8, flag: bool, x: usize, other: usize) !u8 {
        \\    if (flag or other == 0) return error.Empty;
        \\    return buf[x - 1];
        \\}
        \\
    );
}

// ── Derived-variable guard tests (#9) — value-range DiffAlias + lit>=2 ───────
// These exercise the full chain: `const n = end - 0 (or .len)` +
// `if (n < 2) return` → n >= 2 in fall-through → end >= 2 >= 1 → no fire.
// The real-world case `range.end - range.start` (identifier subtrahend) only
// fires in production where ZLS can confirm `range.start` is unsigned.

test "index-minus-one-without-zero-guard: diff-alias n=end-0 + if (n<2) return suppresses" {
    try testing.expectNoFire(check,
        \\fn f(end: usize, buf: []const u8) u8 {
        \\    const n = end - 0;
        \\    if (n < 2) return 0;
        \\    return buf[end - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: diff-alias n=end-other.len + if (n<2) return suppresses" {
    try testing.expectNoFire(check,
        \\fn f(end: usize, other: []const u8, buf: []const u8) u8 {
        \\    const n = end - other.len;
        \\    if (n < 2) return 0;
        \\    return buf[end - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: if (n < 2) return without diff-alias fires" {
    // Guard on unrelated `n` does not suppress `end - 1`.
    try testing.expectFires(check, R,
        \\fn f(end: usize, n: usize, buf: []const u8) u8 {
        \\    if (n < 2) return 0;
        \\    return buf[end - 1];
        \\}
        \\
    );
}

// ── Or-guard (same-expression short-circuit) tests ────────────────────────

test "index-minus-one-without-zero-guard: same-expression i==0 or-guard suppresses" {
    try testing.expectNoFire(check,
        \\fn f(src: []const u8, i: usize) bool {
        \\    if (i == 0 or src[i - 1] == '\n') return true;
        \\    return false;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: or-guard with != still fires (wrong sense)" {
    try testing.expectFires(check, R,
        \\fn f(src: []const u8, i: usize) bool {
        \\    if (i != 0 or src[i - 1] == '\n') return true;
        \\    return false;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: or-guard on different ident still fires" {
    try testing.expectFires(check, R,
        \\fn f(src: []const u8, i: usize, j: usize) bool {
        \\    if (j == 0 or src[i - 1] == '\n') return true;
        \\    return false;
        \\}
        \\
    );
}

// ── Monotone-positive field tests ──────────────────────────────────────────

test "index-minus-one-without-zero-guard: non-monotone field still fires" {
    try testing.expectFires(check, R,
        \\const S = struct {
        \\    limit: usize = 1,
        \\};
        \\fn downgrade(s: *S) void {
        \\    s.limit = 0; // non-@max assignment disqualifies
        \\}
        \\fn use(arr: []const u8, s: S) u8 {
        \\    return arr[s.limit - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: >= 1 and-guard suppresses" {
    try testing.expectNoFire(check,
        \\fn f(s: []const u8, pad: u8) bool {
        \\    return s.len >= 1 and s[s.len - 1] == pad;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: > 1 and-guard suppresses" {
    try testing.expectNoFire(check,
        \\fn f(s: []const u8) u8 {
        \\    if (s.len > 1 and s[s.len - 1] == 0) return 1;
        \\    return 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: len < 2 or-guard suppresses" {
    try testing.expectNoFire(check,
        \\fn f(raw: []const u8) bool {
        \\    if (raw.len < 2 or raw[raw.len - 1] != 'n') return false;
        \\    return true;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: >= 0 and-guard does not suppress" {
    try testing.expectFires(check, R,
        \\fn f(n: usize, buf: []u8) u8 {
        \\    return if (n >= 0 and buf[n - 1] == 0) 1 else 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: while > 0 body suppresses" {
    try testing.expectNoFire(check,
        \\fn f(buf: []i32, n: usize) void {
        \\    var i = n;
        \\    while (i > 0) : (i -= 1) {
        \\        _ = buf[i - 1];
        \\    }
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: while items.len > 0 body suppresses" {
    try testing.expectNoFire(check,
        \\fn f(stack: *std.ArrayList(u32)) u32 {
        \\    while (stack.items.len > 0) {
        \\        return stack.items[stack.items.len - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: while cond without zero-guard still fires" {
    try testing.expectFires(check, R,
        \\fn f(buf: []u8, n: usize) u8 {
        \\    // while condition doesn't constrain n > 0
        \\    var done = false;
        \\    while (!done) { done = true; }
        \\    return buf[n - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: comparison against zero-valued bound suppresses" {
    try testing.expectNoFire(check,
        \\fn f(tags: []const u8, lhs_start: usize) u8 {
        \\    const first: usize = 0;
        \\    if (lhs_start > first) return tags[lhs_start - 1];
        \\    return 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: guarded decrement retains lower bound" {
    try testing.expectNoFire(check,
        \\fn f(tags: []const u8, anchor: usize) u8 {
        \\    const start: usize = 0;
        \\    var k = anchor;
        \\    while (k > start + 1) {
        \\        k -= 1;
        \\        return tags[k - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: subtraction alias follows offset guard" {
    try testing.expectNoFire(check,
        \\fn f(tags: []const u8, other: []const u8, alias_tok: usize) u8 {
        \\    const first: usize = 0;
        \\    if (alias_tok < first + 3 or other[alias_tok - 1] != 0) return 0;
        \\    const name_tok = alias_tok - 2;
        \\    return tags[name_tok - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: infinite-loop break after increment suppresses" {
    try testing.expectNoFire(check,
        \\fn f(names: []const u8, stop: bool) u8 {
        \\    var len: usize = 0;
        \\    while (true) {
        \\        len += 1;
        \\        if (stop) break;
        \\    }
        \\    return names[len - 1];
        \\}
        \\
    );
}

test "index-minus-one-without-zero-guard: early infinite-loop break remains unsafe" {
    try testing.expectFires(check, R,
        \\fn f(names: []const u8, stop_early: bool, delta: usize) u8 {
        \\    var len: usize = 0;
        \\    while (true) {
        \\        if (stop_early) break;
        \\        len += delta;
        \\    }
        \\    return names[len - 1];
        \\}
        \\
    );
}

test "index-minus-one: field writes invalidate a dominating guard" {
    try testing.expectFires(check, R,
        \\const State = struct { index: usize };
        \\fn read(bytes: []const u8, state: *State) u8 {
        \\    if (state.index == 0) return 0;
        \\    state.index = 0;
        \\    return bytes[state.index - 1];
        \\}
    );
}

test "index-minus-one: later assertions cannot guard an earlier access" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn read(bytes: []const u8) u8 {
        \\    const value = bytes[bytes.len - 1];
        \\    std.debug.assert(bytes.len > 0);
        \\    return value;
        \\}
    );
}

test "index-minus-one: namespace spelling does not prove a field positive" {
    try testing.expectFires(check, R,
        \\const State = struct { index: usize };
        \\fn read(bytes: []const u8, constants: State) u8 {
        \\    return bytes[constants.index - 1];
        \\}
    );
}

test "index-minus-one: one caller assertion is not a callee postcondition" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Result = struct { items: []const u8 };
        \\fn make(items: []const u8) Result { return .{ .items = items }; }
        \\fn checked(items: []const u8) void {
        \\    const result = make(items);
        \\    std.debug.assert(result.items.len > 0);
        \\}
        \\fn unchecked(items: []const u8) u8 {
        \\    const result = make(items);
        \\    return result.items[result.items.len - 1];
        \\}
    );
}

test "index-minus-one: writes through aliases invalidate scalar and field facts" {
    try testing.expectFires(check, R,
        \\fn read(bytes: []const u8) u8 {
        \\    var index: usize = 1;
        \\    const alias = &index;
        \\    alias.* = 0;
        \\    return bytes[index - 1];
        \\}
    );
    try testing.expectFires(check, R,
        \\const State = struct { index: usize };
        \\fn read(bytes: []const u8, state: *State) u8 {
        \\    const alias = state;
        \\    if (state.index < 1) return 0;
        \\    alias.index = 0;
        \\    return bytes[state.index - 1];
        \\}
    );
}

test "index-minus-one: unknown calls invalidate previously escaped addresses" {
    try testing.expectFires(check, R,
        \\fn read(bytes: []const u8) u8 {
        \\    var index: usize = 1;
        \\    const alias = &index;
        \\    mutate(alias);
        \\    return bytes[index - 1];
        \\}
    );
}

test "index-minus-one: default fields and method names are not lifecycle proofs" {
    try testing.expectFires(check, R,
        \\const State = struct { index: usize = 1 };
        \\fn read(bytes: []const u8, state: State) u8 {
        \\    return bytes[state.index - 1];
        \\}
        \\fn zero(bytes: []const u8) u8 { return read(bytes, .{ .index = 0 }); }
    );
    try testing.expectFires(check, R,
        \\const State = struct {
        \\    items: []const u8,
        \\    fn getLastOrNull(_: State) ?u8 { return 1; }
        \\};
        \\fn read(state: State) u8 {
        \\    if (state.getLastOrNull()) |_| return state.items[state.items.len - 1];
        \\    return 0;
        \\}
    );
}

test "index-minus-one: condition evaluation invalidates escaped bounds" {
    try testing.expectFires(check, R,
        \\fn reset(index: *usize) bool { index.* = 0; return true; }
        \\fn read(bytes: []const u8) u8 {
        \\    var index: usize = 1;
        \\    if (reset(&index)) {}
        \\    return bytes[index - 1];
        \\}
    );
}

test "index-minus-one: short circuit effects reach subsequent statements" {
    try testing.expectFires(check, R,
        \\fn reset(index: *usize) bool { index.* = 0; return true; }
        \\fn read(bytes: []const u8, flag: bool) u8 {
        \\    var index: usize = 1;
        \\    _ = flag and reset(&index);
        \\    return bytes[index - 1];
        \\}
    );
}

test "index-minus-one: argument effects precede subsequent argument reads" {
    try testing.expectFires(check, R,
        \\fn reset(index: *usize) bool { index.* = 0; return true; }
        \\fn consume(_: bool, _: u8) void {}
        \\fn read(bytes: []const u8) void {
        \\    var index: usize = 1;
        \\    consume(reset(&index), bytes[index - 1]);
        \\}
    );
}

test "index-minus-one: switch mutations invalidate subsequent bounds" {
    try testing.expectFires(check, R,
        \\fn read(bytes: []const u8, flag: bool) u8 {
        \\    var index: usize = 1;
        \\    switch (flag) { true => index = 0, false => {} }
        \\    return bytes[index - 1];
        \\}
    );
}

test "index-minus-one: destructuring invalidates the assigned index" {
    try testing.expectFires(check, R,
        \\fn read(bytes: []const u8) u8 {
        \\    var index: usize = 1;
        \\    index, _ = .{ 0, false };
        \\    return bytes[index - 1];
        \\}
    );
}

test "index-minus-one: predicate effects cannot revive an obsolete guard" {
    try testing.expectFires(check, R,
        \\fn reset(index: *usize) bool { index.* = 0; return true; }
        \\fn read(bytes: []const u8) u8 {
        \\    var index: usize = 1;
        \\    if (index > 0 and reset(&index)) return bytes[index - 1];
        \\    return 0;
        \\}
    );
}

test "index-minus-one: TypeOf does not evaluate index arithmetic" {
    try testing.expectNoFire(check,
        \\fn inspect(bytes: []const u8) void {
        \\    const Element = @TypeOf(bytes[bytes.len - 1]);
        \\    _ = Element;
        \\}
    );
}

test "index-minus-one: atomic mutation invalidates re-established scalar facts" {
    try testing.expectFiresTyped(check, R,
        \\fn last(bytes: []const u8) u8 {
        \\    var count: usize = 1;
        \\    const alias = &count;
        \\    count = 1;
        \\    @atomicStore(usize, alias, 0, .monotonic);
        \\    return bytes[count - 1];
        \\}
    );
}

test "index-minus-one: fallback mutations after a read do not erase its guard" {
    try testing.expectNoFire(check,
        \\fn choose() ?bool { return null; }
        \\fn last(bytes: []const u8) u8 {
        \\    var items: []const u8 = bytes;
        \\    if (items.len == 0) return 0;
        \\    const selected = choose() orelse {
        \\        const value = items[items.len - 1];
        \\        items = items[0..0];
        \\        return value;
        \\    };
        \\    return if (selected) 1 else 0;
        \\}
    );
}

test "index-minus-one: fallback mutations before a read erase its guard" {
    try testing.expectFires(check, R,
        \\fn choose() ?bool { return null; }
        \\fn last(bytes: []const u8) u8 {
        \\    var items: []const u8 = bytes;
        \\    if (items.len == 0) return 0;
        \\    const selected = choose() orelse {
        \\        items = items[0..0];
        \\        return items[items.len - 1];
        \\    };
        \\    return if (selected) 1 else 0;
        \\}
    );
}

test "index-minus-one: failing operand effects reach the fallback read" {
    try testing.expectFires(check, R,
        \\fn clear(items: *[]const u8) ?bool { items.* = items.*[0..0]; return null; }
        \\fn last(bytes: []const u8) u8 {
        \\    var items: []const u8 = bytes;
        \\    if (items.len == 0) return 0;
        \\    const selected = clear(&items) orelse return items[items.len - 1];
        \\    return if (selected) 1 else 0;
        \\}
    );
}

// ── A comparison against a length bounds that length ────────────────────────
//
// `while (i < c.len)` and `if (i < c.len)` both say the container is at
// least as long as `i`.  That is a lower bound on `c`, which is what makes
// `c[c.len - 1]` safe inside — and it holds whichever side of the comparison
// the container is written on.

test "index-minus-one: a cursor loop guard makes the container non-empty" {
    try testing.expectNoFire(check,
        \\fn lastByte(input: []const u8) u8 {
        \\    var cursor: usize = 0;
        \\    while (cursor < input.len) {
        \\        const byte = input[input.len - 1];
        \\        cursor += 1;
        \\        return byte;
        \\    }
        \\    return 0;
        \\}
    );
}

test "index-minus-one: the same expression outside the loop still fires" {
    try testing.expectFires(check, R,
        \\fn lastByte(input: []const u8) u8 {
        \\    var cursor: usize = 0;
        \\    while (cursor < input.len) {
        \\        cursor += 1;
        \\    }
        \\    return input[input.len - 1];
        \\}
    );
}

test "index-minus-one: a non-strict cursor comparison proves nothing about length" {
    try testing.expectFires(check, R,
        \\fn lastByte(input: []const u8) u8 {
        \\    var cursor: usize = 0;
        \\    while (cursor <= input.len) {
        \\        return input[input.len - 1];
        \\    }
        \\    return 0;
        \\}
    );
}

test "index-minus-one: an unsigned cursor whose bound is not comparable still fires" {
    // `start` may be negative: the walk has proved nothing about its sign, so
    // `start < input.len` says nothing about how long `input` is.
    try testing.expectFires(check, R,
        \\fn lastByte(input: []const u8, start: i64) u8 {
        \\    var cursor: i64 = start;
        \\    while (cursor < @as(i64, @intCast(input.len))) {
        \\        return input[input.len - 1];
        \\    }
        \\    return 0;
        \\}
    );
}

test "index-minus-one: a scalar bound greater than one carries the length past one" {
    try testing.expectNoFire(check,
        \\fn lastByte(input: []const u8) u8 {
        \\    if (4 < input.len) {
        \\        return input[input.len - 1];
        \\    }
        \\    return 0;
        \\}
    );
}

test "index-minus-one: a bound on one container says nothing about another" {
    try testing.expectFires(check, R,
        \\fn lastByte(input: []const u8, other: []const u8) u8 {
        \\    var cursor: usize = 0;
        \\    while (cursor < input.len) {
        \\        cursor += 1;
        \\    }
        \\    return other[other.len - 1];
        \\}
    );
}

// ── An assertion's own contract ────────────────────────────────────────────
//
// `std.debug.assert` reports a false condition by panicking, so the
// statements after it run only when it held.  `std.testing.expect` reports it
// by RETURNING an error, which is a different edge: the statements after a
// bare call are reached through its error union, and the edge a reader can be
// standing on there is the one where the condition FAILED.  Only `try` puts
// the reader on the edge where it held.

test "index-minus-one: a tried std.testing.expect proves the length it checked" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn last(items: []const u8) !u8 {
        \\    try std.testing.expect(items.len >= 1);
        \\    return items[items.len - 1];
        \\}
    );
}

test "index-minus-one: the error edge of std.testing.expect proves nothing" {
    // The handler runs exactly when the condition failed, so it inherits the
    // opposite of what it asked about.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn last(items: []const u8) !u8 {
        \\    std.testing.expect(items.len >= 1) catch return 0;
        \\    return items[items.len - 1];
        \\}
    );
}

test "index-minus-one: an expect on a different condition proves nothing" {
    // The call is the one this file's `std` names, but what it asserted was
    // not this container's length.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn last(items: []const u8, other: []const u8) !u8 {
        \\    try std.testing.expect(other.len >= 1);
        \\    return items[items.len - 1];
        \\}
    );
}

// ── A helper's proved length contract ──────────────────────────────────────
//
// `fn nonempty(items: []const u8) bool { return items.len != 0; }` states its
// result as a CONTAINER fact about its parameter, not as a numeric range on
// it.  A caller that dominated the helper's result is standing exactly where
// that fact is true, so the contract travels — under the caller's own
// spelling, and only when the callee could not have rewritten it.

test "index-minus-one: a helper's proved length contract reaches its caller" {
    // The contract crosses the call through the resolver: the callee's
    // declaration, its `bool` result and its `items.len != 0` return are all
    // read through `cache.zls`, exactly as the receiver and return contracts
    // are.  A harness with no resolver attached declines that step, so this
    // proof is asked with the engine on.
    try testing.expectNoFireTyped(check,
        \\fn nonempty(items: []const u8) bool { return items.len != 0; }
        \\fn last(items: []const u8) u8 {
        \\    if (!nonempty(items)) return 0;
        \\    return items[items.len - 1];
        \\}
    );
}

test "index-minus-one: a helper that compares two lengths carries no contract about either" {
    try testing.expectFiresTyped(check, R,
        \\fn sameLength(items: []const u8, other: []const u8) bool { return items.len == other.len; }
        \\fn last(items: []const u8, other: []const u8) u8 {
        \\    if (!sameLength(items, other)) return 0;
        \\    return items[items.len - 1];
        \\}
    );
}

test "index-minus-one: a helper handed an address carries no length contract" {
    // The callee is handed storage it can rewrite, so nothing it concludes
    // about a length is about the caller's slice any more.
    try testing.expectFiresTyped(check, R,
        \\fn nonempty(list: *[]const u8) bool { return list.*.len != 0; }
        \\fn last(items: []const u8) u8 {
        \\    var local = items;
        \\    if (!nonempty(&local)) return 0;
        \\    return local[local.len - 1];
        \\}
    );
}

// ── A block length derived with @min under a bounded loop ───────────────────
//
// `@min(VLEN, input.len - cursor)` is at least one exactly when both of its
// halves are: `VLEN` is a nonzero comptime constant, and the loop condition
// the block is derived under proves `input.len > cursor`.  Either half alone
// is not enough, and neither is the pair outside the loop that ordered them.

test "index-minus-one: a @min block length uses the loop condition it is derived under" {
    try testing.expectNoFire(check,
        \\const VLEN: usize = 64;
        \\fn scan(input: []const u8) void {
        \\    var cursor: usize = 0;
        \\    while (cursor < input.len) : (cursor += VLEN) {
        \\        const valid_count = @min(VLEN, input.len - cursor);
        \\        _ = input[valid_count - 1];
        \\    }
        \\}
    );
}

test "index-minus-one: a zero-width vector length underflows however far the cursor is behind" {
    try testing.expectFires(check, R,
        \\const VLEN: usize = 64;
        \\const WIDTH: usize = 0;
        \\fn scan(input: []const u8) void {
        \\    var cursor: usize = 0;
        \\    while (cursor < input.len) : (cursor += VLEN) {
        \\        const valid_count = @min(WIDTH, input.len - cursor);
        \\        _ = input[valid_count - 1];
        \\    }
        \\}
    );
}

test "index-minus-one: a non-strict loop condition leaves the subtraction at zero" {
    // `cursor == input.len` is a body iteration too, and there the block
    // length is zero.
    try testing.expectFires(check, R,
        \\const VLEN: usize = 64;
        \\fn scan(input: []const u8) void {
        \\    var cursor: usize = 0;
        \\    while (cursor <= input.len) : (cursor += VLEN) {
        \\        const valid_count = @min(VLEN, input.len - cursor);
        \\        _ = input[valid_count - 1];
        \\    }
        \\}
    );
}

test "index-minus-one: the same block length outside the loop still fires" {
    try testing.expectFires(check, R,
        \\const VLEN: usize = 64;
        \\fn scan(input: []const u8) void {
        \\    var cursor: usize = 0;
        \\    while (cursor < input.len) : (cursor += VLEN) {}
        \\    const valid_count = @min(VLEN, input.len - cursor);
        \\    _ = input[valid_count - 1];
        \\}
    );
}

// ── A cast around the subscript ─────────────────────────────────────────────
//
// `buf[@intCast(offset - 1)]` subtracts one from `offset` exactly as
// `buf[offset - 1]` does; the cast only changes how the result is spelled.
// Reading the subscript as "anything that is not a bare subtraction" skips
// every such site before the positivity question is even asked, which is a
// missing report rather than a quiet file.

test "index-minus-one: a signed offset cast into the subscript type still fires (#47c0)" {
    try testing.expectFiresTyped(check, R,
        \\pub fn read(offset: isize, items: []const u8) u8 {
        \\    if (offset == 0) return 0;
        \\    // `offset` is signed: it can be -1 here, so `offset - 1` is not a
        \\    // positive index.
        \\    return items[@intCast(offset - 1)];
        \\}
        \\
        \\pub fn main() void { const bytes=[_]u8{7}; _=read(-1,&bytes); }
    );
}

test "index-minus-one: a nonzero anytype offset cast into the subscript type still fires (#47c2)" {
    try testing.expectFiresTyped(check, R,
        \\pub fn read(offset: anytype, items: []const u8) u8 {
        \\    const n = offset;
        \\    if (n == 0) return 0;
        \\    return items[@intCast(n - 1)];
        \\}
        \\
        \\pub fn main() void { const bytes=[_]u8{7}; _=read(@as(isize,-1),&bytes); }
    );
}

test "index-minus-one: nested @as and @intCast require a positive signed guard" {
    try testing.expectNoFireTyped(check,
        \\fn prev(buf: []const u8, offset: i32) u8 {
        \\    if (offset <= 0) return 0;
        \\    return buf[@as(usize, @intCast(offset - 1))];
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn read(offset: isize, items: []const u8) u8 {
        \\    if (offset == 0) return 0;
        \\    return items[@as(usize, @intCast(offset - 1))];
        \\}
    );
}

test "index-minus-one: only intCast and as are transparent to the subscript" {
    // `@abs` computes something this file cannot see through, so it is not
    // read as `index - 1` at all — the rule declines it rather than
    // claiming a subtraction it never saw.
    try testing.expectNoFire(check,
        \\fn prev(items: []const u8, index: i32) u8 {
        \\    return items[@abs(index - 1)];
        \\}
    );
}

test "index-minus-one: an intCast around the subscript carries the guard it wraps" {
    // The same cast, unsigned and unguarded: the destination type says how
    // `offset - 1` is spelled, not that `offset` was above zero.
    try testing.expectFiresTyped(check, R,
        \\pub fn read(offset: usize, items: []const u8) u8 {
        \\    return items[@intCast(offset - 1)];
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn read(offset: usize, items: []const u8) u8 {
        \\    if (offset == 0) return 0;
        \\    // `offset` is `usize`, so nonzero means at least 1.
        \\    return items[@intCast(offset - 1)];
        \\}
        \\
        \\pub fn main() void { const bytes=[_]u8{7}; if(read(1,&bytes)!=7 or read(0,&bytes)!=0)unreachable; }
    );
}

// ── A relational early return, signed and unsigned (#70) ────────────────────

test "index-minus-one: an unsigned end the early return bounds is non-empty (#70c0)" {
    try testing.expectNoFireTyped(check,
        \\fn lastByte(bytes: []u8, start: usize, end: usize) void {
        \\    // `end` is a usize, so rejecting `start >= end` leaves end >= 1 on
        \\    // every path that reaches the read.
        \\    if (start >= end) return;
        \\    _ = bytes[end - 1];
        \\}
        \\
        \\pub fn main() void {var bytes=[_]u8{10,20};lastByte(&bytes,0,2);lastByte(&bytes,2,2);}
    );
}

test "index-minus-one: a signed relational early return proves no positivity (#70c1)" {
    try testing.expectFiresTyped(check, R,
        \\fn lastByte(bytes: []u8, start: isize, end: isize) void {
        \\    // `end` is SIGNED here, so `start < end` proves nothing about end.
        \\    if (start >= end) return;
        \\    _ = bytes[@intCast(end - 1)];
        \\}
        \\
        \\pub fn main() void {var bytes=[_]u8{10,20};lastByte(&bytes,-2,-1);}
    );
}

// ── A short circuit over two relations (#72) ────────────────────────────────

test "index-minus-one: an unsigned index past its start survives the short circuit (#72c1)" {
    try testing.expectNoFireTyped(check,
        \\// SAFE: the guard now also excludes every index below `start`, and
        \\// `index >= start` with `start == 0` leaves `index >= 1` on the only path
        \\// that reaches the subscript.
        \\pub fn previousIsSpace(input: []const u8, index: usize, start: usize) bool {
        \\    if (index < start) return false;
        \\    if (index == start or input[index - 1] == ' ') return true;
        \\    return false;
        \\}
        \\
        \\pub fn main() void {const input="a ";if(!previousIsSpace(input,0,0) or !previousIsSpace(input,2,0) or previousIsSpace(input,0,1))unreachable;}
    );
}

test "index-minus-one: reversed unsigned order survives the short circuit" {
    try testing.expectNoFireTyped(check,
        \\pub fn previousIsSpace(input: []const u8, index: usize, start: usize) bool {
        \\    if (start > index) return false;
        \\    if (index == start or input[index - 1] == ' ') return true;
        \\    return false;
        \\}
    );
}

test "index-minus-one: a signed index past its start is still negative (#72c4)" {
    try testing.expectFiresTyped(check, R,
        \\// The same self-excluding form on a SIGNED operand proves nothing:
        \\// `index == start` does not make `index - 1` positive.
        \\pub fn previousIsSpace(input: []const u8, index: isize, start: isize) bool {
        \\    if (index == start or input[@intCast(index - 1)] == ' ') return true;
        \\    return false;
        \\}
        \\
        \\pub fn main() void {_=previousIsSpace("a ",-1,0);}
    );
}

// ── A callee that cannot reach the guard's variable (#30, #35) ──────────────

test "index-minus-one: a by-value callee keeps the length guard (#30)" {
    try testing.expectNoFireTyped(check,
        \\pub fn last(items: []const u8) u8 {
        \\    if (items.len == 0) return 0;
        \\    observe(items);
        \\    return items[items.len - 1];
        \\}
        \\fn observe(items: []const u8) void { _ = items.len; }
        \\
        \\pub fn main() void { const bytes=[_]u8{7}; if(last(&bytes)!=7 or last(&.{})!=0)unreachable; }
    );
    try testing.expectFiresTyped(check, R,
        \\fn observe(items: *[]const u8) void { items.* = items.*[0..0]; }
        \\pub fn last(src: []const u8) u8 { var items=src; if(items.len==0)return 0; observe(&items); return items[items.len-1]; }
        \\
        \\pub fn main() void { const bytes=[_]u8{7}; _=last(&bytes); }
    );
}

test "index-minus-one: a callee that only reads the index keeps the guard (#35)" {
    // `keep` is handed the address and does nothing with it, so the
    // `index != 0` the left operand established still holds at the read.
    try testing.expectNoFireTyped(check,
        \\fn keep(p: *usize) bool { _ = p; return true; }
        \\pub fn read(seed: usize, bytes: []const u8) u8 {
        \\    var index = seed;
        \\    if (!(index == 0) and keep(&index)) return bytes[index - 1];
        \\    return 0;
        \\}
        \\
        \\pub fn main() void { const bytes=[_]u8{7}; if(read(1,&bytes)!=7 or read(0,&bytes)!=0)unreachable; }
    );
    try testing.expectFiresTyped(check, R,
        \\// Synthetic mutation shape, not an executed historical witness:
        \\fn zero(p: *usize) bool { p.* = 0; return true; }
        \\pub fn read(seed: usize, bytes: []const u8) u8 {
        \\    var index = seed;
        \\    if (!(index == 0) and zero(&index)) return bytes[index - 1];
        \\    return 0;
        \\}
        \\
        \\pub fn main() void { const bytes=[_]u8{7}; _=read(1,&bytes); }
    );
}

// ── A pointer alias and its target (#42) ────────────────────────────────────

test "index-minus-one: the guarded pointee keeps its bound under its own name (#42)" {
    try testing.expectNoFireTyped(check,
        \\pub fn read(first: *usize, other: *usize, items: []const u8) u8 {
        \\    var p = first;
        \\    if (p.* < 10) return 0;
        \\    p = other;
        \\    // The read goes through the ORIGINAL pointee, spelled directly.
        \\    return items[first.* - 1];
        \\}
        \\
        \\pub fn main() void { var first:usize=10; var other:usize=0; const bytes=[_]u8{7} ** 10; if(read(&first,&other,&bytes)!=7)unreachable; }
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn read(first: *usize, other: *usize, items: []const u8) u8 {
        \\    var p = first;
        \\    if (p.* < 10) return 0;
        \\    // `p` now names a different object, whose `.*` may hold 0.
        \\    p = other;
        \\    return items[p.* - 1];
        \\}
        \\
        \\pub fn main() void { var first:usize=10; var other:usize=0; const bytes=[_]u8{7} ** 10; _=read(&first,&other,&bytes); }
    );
}

test "index-minus-one: a pointer alias that is never rebound keeps its bound (#42)" {
    try testing.expectNoFireTyped(check,
        \\pub fn read(first: *usize, other: *usize, items: []const u8) u8 {
        \\    const p = first;
        \\    if (p.* < 10) return 0;
        \\    _ = other;
        \\    return items[p.* - 1];
        \\}
    );
}

// ── A copied depth outlives the field it was read from (#48) ────────────────

test "index-minus-one: a copied depth survives the reset of its owner field (#48)" {
    try testing.expectNoFireTyped(check,
        \\const Frame=struct {indent:u32}; const Walker=struct {frames:[]Frame,depth:usize,fn reset(self:*Walker)void{self.depth=0;}};
        \\pub fn walk(walker:*Walker,out:[]u32)usize { const depth=walker.depth; var count:usize=0; while(depth!=0){walker.reset();if(count<out.len)out[count]=walker.frames[depth-1].indent;count+=1;if(count>64)break;}return count;}
        \\
        \\pub fn main() void {var frames=[_]Frame{.{.indent=7}};var walker=Walker{.frames=&frames,.depth=1};var out:[65]u32=undefined;if(walk(&walker,&out)!=65 or out[64]!=7)unreachable;}
    );
    // Reading the field again takes what the reset call wrote.
    try testing.expectFiresTyped(check, R,
        \\const Frame=struct {indent:u32}; const Walker=struct {frames:[]Frame,depth:usize,fn reset(self:*Walker)void{self.depth=0;}};
        \\pub fn walk(walker:*Walker,out:[]u32)usize {var count:usize=0;while(walker.depth!=0){walker.reset();if(count<out.len)out[count]=walker.frames[walker.depth-1].indent;count+=1;if(count>64)break;}return count;}
        \\
        \\pub fn main() void {var frames=[_]Frame{.{.indent=7}};var walker=Walker{.frames=&frames,.depth=1};var out:[65]u32=undefined;_=walk(&walker,&out);}
    );
}

// ── An allocation sized past the body it holds (#74) ────────────────────────

test "index-minus-one: an allocation two bytes past its body length stays non-empty (#74c0)" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\
        \\fn lastByte(gpa: std.mem.Allocator, body_len: usize) !u8 {
        \\    // `body_len` is an unsigned parameter, so `body_len + 2 >= 2` follows
        \\    // from the parameter type alone: the proof needs no help from a caller.
        \\    const buf = try gpa.alloc(u8, body_len + 2);
        \\    defer gpa.free(buf);
        \\    @memset(buf, 0);
        \\    // The allocation size IS the length of the slice the call returns, so
        \\    // `buf.len - 1` is at least 1.
        \\    return buf[buf.len - 1];
        \\}
        \\
        \\pub fn main() !void {if(try lastByte(std.heap.page_allocator,0)!=0 or try lastByte(std.heap.page_allocator,7)!=0)unreachable;}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\
        \\fn lastByte(gpa: std.mem.Allocator, body_len: usize) !u8 {
        \\    // No positive addend: the length can genuinely be 0.
        \\    const buf = try gpa.alloc(u8, body_len + 0);
        \\    defer gpa.free(buf);
        \\    @memset(buf, 0);
        \\    return buf[buf.len - 1];
        \\}
        \\
        \\pub fn main() !void {_=try lastByte(std.heap.page_allocator,0);}
    );
}

// ── Every caller of a helper that is not reachable from outside ─────────────
//
// A file-private helper has exactly the callers the file spells.  When each
// of them reaches the call under its own zero guard, the subtraction the
// helper performs is as proved as the guards are; one caller without the
// guard is one reachable path to the same subtraction.

test "index-minus-one: every caller of a private helper guards its index" {
    try testing.expectNoFireTyped(check,
        \\fn previous(items: []const u8, index: usize) u8 {
        \\    return items[index - 1];
        \\}
        \\fn left(items: []const u8, index: usize) u8 {
        \\    if (index == 0) return 0;
        \\    return previous(items, index);
        \\}
        \\fn right(items: []const u8, index: usize) u8 {
        \\    if (index == 0) return 0;
        \\    return previous(items, index);
        \\}
        \\pub fn main() void {
        \\    const bytes = [_]u8{7};
        \\    if (left(&bytes, 1) != 7 or right(&bytes, 1) != 7 or left(&bytes, 0) != 0 or right(&bytes, 0) != 0) unreachable;
        \\}
    );
}

test "index-minus-one: one unguarded caller reopens a private helper's index" {
    try testing.expectFiresTyped(check, R,
        \\fn previous(items: []const u8, index: usize) u8 {
        \\    return items[index - 1];
        \\}
        \\fn left(items: []const u8, index: usize) u8 {
        \\    if (index == 0) return 0;
        \\    return previous(items, index);
        \\}
        \\fn right(items: []const u8, index: usize) u8 {
        \\    return previous(items, index);
        \\}
        \\pub fn main() void {
        \\    const bytes = [_]u8{7};
        \\    _ = left(&bytes, 1);
        \\    _ = right(&bytes, 0);
        \\}
    );
}

test "index-minus-one: a guarded caller does not make a public helper safe" {
    // `previous` is reachable from outside the file, so the one guarded
    // caller says nothing about the others.
    try testing.expectFiresTyped(check, R,
        \\pub fn previous(items: []const u8, index: usize) u8 {
        \\    return items[index - 1];
        \\}
        \\pub fn guarded(items: []const u8, index: usize) u8 {
        \\    if (index == 0) return 0;
        \\    return previous(items, index);
        \\}
    );
}

test "index-minus-one: an unfinished cast peel returns a located refusal, not a clean result" {
    const gpa = std.testing.allocator;
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    try source.appendSlice(gpa, "pub fn deep(items: []const u8, index: usize) u8 {\n    return items[");
    const nesting: usize = peel_depth + 1;
    for (0..nesting) |_| try source.append(gpa, '(');
    try source.appendSlice(gpa, "index - 1");
    for (0..nesting) |_| try source.append(gpa, ')');
    try source.appendSlice(gpa, "];\n}\n");

    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(
        error.AnalysisBudgetExceeded,
        testing.runRuleTyped(gpa, check, source.items),
    );
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.index_minus_one_peel_depth, failure.limit);
    try std.testing.expectEqualStrings("deep", failure.function.slice());
    try std.testing.expect(failure.byte != 0);
    try std.testing.expect(failure.line != 0);
}

test "index-minus-one: a callee increment establishes a positive count" {
    try testing.expectNoFireTyped(check,
        \\const State = struct {
        \\    items: [8]u8 = @splat(0),
        \\    count: usize,
        \\    fn emit(self: *State) void { self.items[self.count] = 42; self.count += 1; }
        \\};
        \\pub fn last(state: *State) u8 { state.emit(); return state.items[state.count - 1]; }
    );
}

test "index-minus-one: a callee successful early return does not establish a count" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct {
        \\    items: [8]u8 = @splat(0),
        \\    count: usize,
        \\    fn emit(self: *State, skip: bool) void { if (skip) return; self.count += 1; }
        \\};
        \\pub fn last(state: *State, skip: bool) u8 { state.emit(skip); return state.items[state.count - 1]; }
    );
}

test "index-minus-one: a successful append helper establishes a nonempty field" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const State = struct {
        \\    items: std.ArrayList(u8) = .empty,
        \\    fn emit(self: *State, allocator: std.mem.Allocator) !void { try self.items.append(allocator, 42); }
        \\};
        \\pub fn last(state: *State, allocator: std.mem.Allocator) !u8 {
        \\    try state.emit(allocator);
        \\    return state.items.items[state.items.items.len - 1];
        \\}
    );
}

test "index-minus-one: a caught failed append helper does not establish a field" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const State = struct {
        \\    items: std.ArrayList(u8) = .empty,
        \\    fn emit(self: *State, allocator: std.mem.Allocator) !void { try self.items.append(allocator, 42); }
        \\};
        \\pub fn last(state: *State, allocator: std.mem.Allocator) u8 {
        \\    state.emit(allocator) catch {};
        \\    return state.items.items[state.items.items.len - 1];
        \\}
    );
}

test "index-minus-one: a loop min end remains positive after cursor advances" {
    try testing.expectNoFireTyped(check,
        \\pub fn scan(input: []const u8) u8 {
        \\    var cursor: usize = 0;
        \\    var result: u8 = 0;
        \\    while (cursor < input.len) {
        \\        const block_end = @min(cursor + 16, input.len);
        \\        cursor = block_end;
        \\        result ^= input[block_end - 1];
        \\    }
        \\    return result;
        \\}
    );
}

test "index-minus-one: a zero-width loop min end can be zero" {
    try testing.expectFiresTyped(check, R,
        \\pub fn scan(input: []const u8) u8 {
        \\    var cursor: usize = 0;
        \\    while (cursor < input.len) {
        \\        const block_end = @min(cursor + 0, input.len);
        \\        cursor = block_end;
        \\        return input[block_end - 1];
        \\    }
        \\    return 0;
        \\}
    );
}

test "index-minus-one: a comptime assertion supplies the scanner width floor" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn scan(comptime width: usize, input: []const u8) u8 {
        \\    comptime std.debug.assert(width > 0);
        \\    var cursor: usize = 0;
        \\    var result: u8 = 0;
        \\    while (cursor < input.len) {
        \\        const block_end = @min(cursor + width, input.len);
        \\        cursor = block_end;
        \\        result ^= input[block_end - 1];
        \\    }
        \\    return result;
        \\}
    );
}

test "index-minus-one: an unknown callee cannot establish a positive count" {
    try testing.expectFiresTyped(check, R,
        \\pub fn last(state: anytype) u8 { state.emit(); return state.items[state.count - 1]; }
    );
}

test "index-minus-one: a callee error return is not a successful zero count" {
    try testing.expectNoFireTyped(check,
        \\const State = struct {
        \\    items: [8]u8 = @splat(0),
        \\    count: usize,
        \\    fn emit(self: *State, fail: bool) !void {
        \\        if (fail) return error.Failed;
        \\        self.count += 1;
        \\    }
        \\};
        \\pub fn last(state: *State, fail: bool) !u8 { try state.emit(fail); return state.items[state.count - 1]; }
    );
}

test "index-minus-one: an ignored error union leaves zero-count paths reachable" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct {
        \\    items: [8]u8 = @splat(0),
        \\    count: usize,
        \\    fn emit(self: *State, fail: bool) !void {
        \\        if (fail) return error.Failed;
        \\        self.count += 1;
        \\    }
        \\};
        \\pub fn last(state: *State, fail: bool) u8 { _ = state.emit(fail); return state.items[state.count - 1]; }
    );
}

test "index-minus-one: successful helper ignores error-only rollback" {
    try testing.expectNoFireTyped(check,
        \\const State = struct {
        \\    items: [8]u8 = @splat(0),
        \\    count: usize,
        \\    fn emit(self: *State, fail: bool) !void {
        \\        self.count += 1;
        \\        errdefer self.count = 0;
        \\        if (fail) return error.Failed;
        \\    }
        \\};
        \\pub fn last(state: *State, fail: bool) !u8 { try state.emit(fail); return state.items[state.count - 1]; }
    );
}

test "index-minus-one: unconditional deferred reset destroys helper positivity" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct {
        \\    items: [8]u8 = @splat(0),
        \\    count: usize,
        \\    fn emit(self: *State) void {
        \\        self.count += 1;
        \\        defer self.count = 0;
        \\    }
        \\};
        \\pub fn last(state: *State) u8 { state.emit(); return state.items[state.count - 1]; }
    );
}

test "index-minus-one: raw fallible wrapper cannot export propagated success facts" {
    try testing.expectFiresTyped(check, R,
        \\fn validate(fail: bool) !void { if (fail) return error.Failed; }
        \\const State = struct {
        \\    items: [8]u8 = @splat(0),
        \\    count: usize,
        \\    fn emit(self: *State, fail: bool) !void { try validate(fail); self.count += 1; }
        \\};
        \\pub fn last(state: *State, fail: bool) u8 { _ = state.emit(fail); return state.items[state.count - 1]; }
    );
}

test "index-minus-one: nested caught error rollback remains conservative" {
    try testing.expectFiresTyped(check, R,
        \\fn validate(fail: bool) !void { if (fail) return error.Failed; }
        \\const State = struct {
        \\    items: [8]u8 = @splat(0),
        \\    count: usize,
        \\    fn emit(self: *State, fail: bool) !void {
        \\        self.count = 1;
        \\        const result: anyerror!void = blk: {
        \\            errdefer self.count = 0;
        \\            break :blk try validate(fail);
        \\        };
        \\        result catch {};
        \\    }
        \\};
        \\pub fn last(state: *State, fail: bool) !u8 { try state.emit(fail); return state.items[state.count - 1]; }
    );
}

test "index-minus-one: foreign successful append exports only universal nonempty fields" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{
        .sub_path = "remote.zig",
        .data =
        \\const std = @import("std");
        \\pub const State = struct {
        \\    items: std.ArrayList(u8) = .empty,
        \\    pub fn emit(self: *State, allocator: std.mem.Allocator, fail: bool) !void {
        \\        try self.items.append(allocator, 42);
        \\        errdefer _ = self.items.pop();
        \\        if (fail) return error.Failed;
        \\    }
        \\    pub fn maybe(self: *State, allocator: std.mem.Allocator, skip: bool) !void {
        \\        if (skip) return;
        \\        try self.emit(allocator, false);
        \\    }
        \\};
        ,
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    for ([_][]const u8{ "emit", "maybe" }, 0..) |method, expected| {
        const source = try std.fmt.allocPrint(
            gpa,
            "const std = @import(\"std\");\n" ++
                "const State = @import(\"{s}/remote.zig\").State;\n" ++
                "pub fn last(state: *State, allocator: std.mem.Allocator, flag: bool) !u8 {{\n" ++
                "    try state.{s}(allocator, flag);\n" ++
                "    return state.items.items[state.items.items.len - 1];\n" ++
                "}}\n",
            .{ directory, method },
        );
        defer gpa.free(source);
        const engine = @import("type_engine");
        var context: engine.TypeContext = undefined;
        try context.init(gpa, io);
        defer context.deinit();
        context.store.source_policy = .{ .roots = &.{directory} };
        const caller_path = try std.fs.path.join(gpa, &.{ directory, "caller.zig" });
        defer gpa.free(caller_path);
        const source_z = try gpa.dupeZ(u8, source);
        defer gpa.free(source_z);
        var resolver: engine.TypeResolver = undefined;
        try resolver.init(&context, gpa, caller_path, source_z);
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        if (tree.errors.len != 0) return error.InvalidSyntax;
        var cache = file_cache_mod.FileCache.init(gpa, tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer testing.freeProblems(gpa, &problems);
        try check(gpa, tree, &cache, &config_mod.Default, &problems);
        try std.testing.expectEqual(expected, problems.items.len);
        for (problems.items) |problem| try std.testing.expectEqualStrings(R, problem.rule_id);
    }
}

test "index-minus-one: return operand effects precede exported callee floors" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct {
        \\    items: [8]u8 = @splat(0),
        \\    count: usize,
        \\    fn reset(self: *State) void { self.count = 0; }
        \\    fn emit(self: *State) void { self.count = 1; return self.reset(); }
        \\};
        \\pub fn last(state: *State) u8 { state.emit(); return state.items[state.count - 1]; }
    );
}

test "index-minus-one Ocean effects: element stores keep independent loop indices" {
    try testing.expectNoFireTyped(check,
        \\pub fn sort(ids: []u32, indices: []usize, begin: usize) void {
        \\    for (begin..ids.len) |i| {
        \\        const current = ids[i];
        \\        var insertion = i;
        \\        while (insertion > begin and ids[insertion - 1] > current) : (insertion -= 1) {
        \\            indices[insertion] = indices[insertion - 1];
        \\            ids[insertion] = ids[insertion - 1];
        \\        }
        \\    }
        \\}
    );
}

test "index-minus-one Ocean effects: element stores still invalidate aliased counters" {
    try testing.expectFiresTyped(check, R,
        \\pub fn f(items: []u32, count: *u32, slot: usize) u32 {
        \\    if (count.* == 0) return 0;
        \\    items[slot] = 0;
        \\    return items[count.* - 1];
        \\}
    );
}

test "index-minus-one Ocean effects: same-value element store preserves pointer count" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn push(out: []u32, mapping: []u32, node: usize, count: *u32) !void {
        \\    if (count.* == std.math.maxInt(u32)) return error.Full;
        \\    count.* += 1;
        \\    mapping[node] = count.*;
        \\    out[count.* - 1] = 0;
        \\}
    );
}

test "index-minus-one Ocean effects: aliased standard expect retains nonempty success" {
    try testing.expectNoFireTyped(check,
        \\const testing = @import("std").testing;
        \\pub fn last(bytes: []const u8, limit: usize) !u8 {
        \\    try testing.expect(bytes.len >= 1);
        \\    try testing.expect(bytes.len <= limit);
        \\    return bytes[bytes.len - 1];
        \\}
    );
}

test "index-minus-one Ocean effects: custom expect alias proves nothing" {
    try testing.expectFiresTyped(check, R,
        \\const testing = struct { fn expect(_: bool) !void {} };
        \\pub fn last(bytes: []const u8) !u8 {
        \\    try testing.expect(bytes.len >= 1);
        \\    return bytes[bytes.len - 1];
        \\}
    );
}

test "index-minus-one Ocean effects: caught standard expect proves no success fact" {
    try testing.expectFiresTyped(check, R,
        \\const testing = @import("std").testing;
        \\pub fn last(bytes: []const u8) u8 {
        \\    testing.expect(bytes.len >= 1) catch {};
        \\    return bytes[bytes.len - 1];
        \\}
    );
}

test "index-minus-one Ocean effects: unrelated errdefer keeps pointer stack guard" {
    try testing.expectNoFireTyped(check,
        \\const Context = struct { items: []u8 };
        \\const Outcome = struct { fn deinit(_: *Outcome) void {} };
        \\pub fn last(ctx: *Context) !u8 {
        \\    if (ctx.items.len == 0) return error.Empty;
        \\    var out: Outcome = .{};
        \\    errdefer out.deinit();
        \\    return ctx.items[ctx.items.len - 1];
        \\}
    );
}

test "index-minus-one Ocean effects: actual cleanup mutation invalidates stack guard" {
    try testing.expectFiresTyped(check, R,
        \\const Context = struct {
        \\    items: []u8,
        \\    fn clear(self: *Context) void { self.items = self.items[0..0]; }
        \\};
        \\pub fn last(ctx: *Context) !u8 {
        \\    if (ctx.items.len == 0) return error.Empty;
        \\    ctx.clear();
        \\    return ctx.items[ctx.items.len - 1];
        \\}
    );
}

test "index-minus-one Ocean effects: positive range capture survives unrelated append" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn place(count: usize, output: *std.ArrayList(u8), allocator: std.mem.Allocator, placements: []usize) !void {
        \\    for (1..count + 1) |raw| {
        \\        try output.appendSlice(allocator, &.{1});
        \\        placements[raw - 1] = output.items.len;
        \\    }
        \\}
    );
}

test "index-minus-one Ocean effects: zero-start range remains unsafe after append" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn place(count: usize, output: *std.ArrayList(u8), allocator: std.mem.Allocator, placements: []usize) !void {
        \\    for (0..count) |raw| {
        \\        try output.appendSlice(allocator, &.{1});
        \\        placements[raw - 1] = output.items.len;
        \\    }
        \\}
    );
}

test "index-minus-one Ocean effects: readonly leaf clone keeps length equality" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = struct {
        \\    entries: []u8,
        \\    limit: usize,
        \\    fn clone(self: *const List) []u8 { return self.entries; }
        \\};
        \\pub fn last(list: *List) ?u8 {
        \\    std.debug.assert(list.limit > 0);
        \\    if (list.entries.len == list.limit) {
        \\        const copied = list.clone();
        \\        _ = copied;
        \\        return list.entries[list.entries.len - 1];
        \\    }
        \\    return null;
        \\}
    );
}

test "index-minus-one Ocean effects: clone name does not promise length preservation" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = struct {
        \\    entries: []u8,
        \\    limit: usize,
        \\    fn clone(self: *List) []u8 {
        \\        self.entries = self.entries[0..0];
        \\        return self.entries;
        \\    }
        \\};
        \\pub fn last(list: *List) ?u8 {
        \\    std.debug.assert(list.limit > 0);
        \\    if (list.entries.len == list.limit) {
        \\        _ = list.clone();
        \\        return list.entries[list.entries.len - 1];
        \\    }
        \\    return null;
        \\}
    );
}

test "index-minus-one Ocean effects: unaligned same-value stores retain no alias bound" {
    try testing.expectFiresTyped(check, R,
        \\pub fn f(items: []align(1) u32, count: *align(1) u32, slot: usize) u32 {
        \\    if (count.* == 0) return 0;
        \\    items[slot] = count.*;
        \\    return items[count.* - 1];
        \\}
    );
}

test "index-minus-one Ocean effects: distinct pointer names may alias guarded stack" {
    try testing.expectFiresTyped(check, R,
        \\const Context = struct {
        \\    items: []u8,
        \\    fn clear(self: *Context) void { self.items = self.items[0..0]; }
        \\};
        \\pub fn last(ctx: *Context, other: *Context) !u8 {
        \\    if (ctx.items.len == 0) return error.Empty;
        \\    other.clear();
        \\    return ctx.items[ctx.items.len - 1];
        \\}
    );
}

test "index-minus-one Ocean effects: nested readonly clone keeps guarded length" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn identity(bytes: []u8) []u8 { return bytes; }
        \\const List = struct {
        \\    entries: []u8,
        \\    limit: usize,
        \\    fn clone(self: *const List) []u8 { return identity(self.entries); }
        \\};
        \\pub fn last(list: *List) ?u8 {
        \\    std.debug.assert(list.limit > 0);
        \\    if (list.entries.len == list.limit) {
        \\        _ = list.clone();
        \\        return list.entries[list.entries.len - 1];
        \\    }
        \\    return null;
        \\}
    );
}

test "index-minus-one Ocean effects: const clone with nested write remains unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = struct {
        \\    entries: []u8,
        \\    limit: usize,
        \\    fn clear(self: *List) void { self.entries = self.entries[0..0]; }
        \\    fn clone(self: *const List) void { clear(@constCast(self)); }
        \\};
        \\pub fn last(list: *List) ?u8 {
        \\    std.debug.assert(list.limit > 0);
        \\    if (list.entries.len == list.limit) {
        \\        list.clone();
        \\        return list.entries[list.entries.len - 1];
        \\    }
        \\    return null;
        \\}
    );
}

test "index-minus-one Ocean Module: checked accessor result survives OR rejection" {
    try testing.expectNoFireTyped(check,
        \\const Key = struct { value: usize, fn index(self: Key) usize { return self.value; } };
        \\const Module = struct { callables: []const u8 };
        \\pub fn get(module: *const Module, key: Key) ?u8 {
        \\    const raw_id = key.index();
        \\    if (raw_id == 0 or raw_id > module.callables.len) return null;
        \\    return module.callables[raw_id - 1];
        \\}
    );
}

test "index-minus-one Ocean Module: upper-only accessor rejection still warns" {
    try testing.expectFiresTyped(check, R,
        \\const Key = struct { value: usize, fn index(self: Key) usize { return self.value; } };
        \\const Module = struct { callables: []const u8 };
        \\pub fn get(module: *const Module, key: Key) ?u8 {
        \\    const raw_id = key.index();
        \\    if (raw_id > module.callables.len) return null;
        \\    return module.callables[raw_id - 1];
        \\}
    );
}

test "index-minus-one Ocean Timing: copied union row retains ordinal rejection" {
    try testing.expectNoFireTyped(check,
        \\const Row = struct { ordinal: usize };
        \\const Event = union(enum) { model: Row, other: void };
        \\const State = struct { models: []const u8, ok: bool };
        \\pub fn walk(state: *State, event: Event) ?u8 {
        \\    switch (event) {
        \\        .model => |row| {
        \\            if (row.ordinal == 0 or row.ordinal > state.models.len) {
        \\                state.ok = false;
        \\                return null;
        \\            }
        \\            return state.models[row.ordinal - 1];
        \\        },
        \\        .other => return null,
        \\    }
        \\}
    );
}

test "index-minus-one Ocean Timing: copied union row without zero rejection warns" {
    try testing.expectFiresTyped(check, R,
        \\const Row = struct { ordinal: usize };
        \\const Event = union(enum) { model: Row, other: void };
        \\const State = struct { models: []const u8, ok: bool };
        \\pub fn walk(state: *State, event: Event) ?u8 {
        \\    switch (event) {
        \\        .model => |row| {
        \\            if (row.ordinal > state.models.len) {
        \\                state.ok = false;
        \\                return null;
        \\            }
        \\            return state.models[row.ordinal - 1];
        \\        },
        \\        .other => return null,
        \\    }
        \\}
    );
}

test "index-minus-one Ocean induction: one-based counter with independent zero sum" {
    try testing.expectNoFireTyped(check,
        \\pub fn sumThree(items: [3]u8) u8 {
        \\    var id: usize = 1;
        \\    var sum: u8 = 0;
        \\    while (id <= 3) : (id += 1) sum +%= items[id - 1];
        \\    return sum;
        \\}
    );
}

test "index-minus-one Ocean induction: zero-based counter still warns" {
    try testing.expectFiresTyped(check, R,
        \\pub fn sumThree(items: [3]u8) u8 {
        \\    var id: usize = 0;
        \\    var sum: u8 = 0;
        \\    while (id <= 3) : (id += 1) sum +%= items[id - 1];
        \\    return sum;
        \\}
    );
}

test "index-minus-one Ocean induction: body reset invalidates the counter floor" {
    try testing.expectFiresTyped(check, R,
        \\pub fn sumThree(items: [3]u8, reset: bool) u8 {
        \\    var id: usize = 1;
        \\    var sum: u8 = 0;
        \\    while (id <= 3) : (id += 1) {
        \\        if (reset) id = 0;
        \\        sum +%= items[id - 1];
        \\    }
        \\    return sum;
        \\}
    );
}

test "index-minus-one Ocean induction: wrapping backedge still warns" {
    try testing.expectFiresTyped(check, R,
        \\pub fn sumThree(items: [3]u8) u8 {
        \\    var id: usize = 1;
        \\    var sum: u8 = 0;
        \\    while (id <= 3) : (id +%= 1) sum +%= items[id - 1];
        \\    return sum;
        \\}
    );
}

test "index-minus-one Ocean return: nonempty anonymous array header" {
    try testing.expectNoFireTyped(check,
        \\pub fn last() u8 {
        \\    const entries = nonEmpty();
        \\    return entries[entries.len - 1];
        \\}
        \\fn nonEmpty() []const u8 { return &.{ 7, 9 }; }
    );
}

test "index-minus-one Ocean return: empty anonymous array header still warns" {
    try testing.expectFiresTyped(check, R,
        \\pub fn last() u8 {
        \\    const entries = empty();
        \\    return entries[entries.len - 1];
        \\}
        \\fn empty() []const u8 { return &.{}; }
    );
}

test "index-minus-one Ocean return: an empty alternate return still warns" {
    try testing.expectFiresTyped(check, R,
        \\pub fn last(short: bool) u8 {
        \\    const entries = choose(short);
        \\    return entries[entries.len - 1];
        \\}
        \\fn choose(short: bool) []const u8 {
        \\    if (short) return &.{};
        \\    return &.{ 7, 9 };
        \\}
    );
}

test "index-minus-one Ocean Memory: successful append emitter returns a positive node" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Trace = struct {
        \\    nodes: std.ArrayList(u8),
        \\    fn emit(self: *Trace, allocator: std.mem.Allocator) !usize {
        \\        try self.nodes.append(allocator, 7);
        \\        return @intCast(self.nodes.items.len);
        \\    }
        \\};
        \\pub fn set(trace: *Trace, allocator: std.mem.Allocator) !void {
        \\    const node = try trace.emit(allocator);
        \\    trace.nodes.items[node - 1] = 9;
        \\}
    );
}

test "index-minus-one Ocean Memory: emitter without append still warns" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Trace = struct {
        \\    nodes: std.ArrayList(u8),
        \\    fn emit(self: *Trace) !usize { return @intCast(self.nodes.items.len); }
        \\};
        \\pub fn set(trace: *Trace) !void {
        \\    const node = try trace.emit();
        \\    trace.nodes.items[node - 1] = 9;
        \\}
    );
}

test "index-minus-one Ocean Memory: continuing catch cannot inherit success floor" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Trace = struct {
        \\    nodes: std.ArrayList(u8),
        \\    fn emit(self: *Trace, allocator: std.mem.Allocator) !usize {
        \\        try self.nodes.append(allocator, 7);
        \\        return @intCast(self.nodes.items.len);
        \\    }
        \\};
        \\pub fn set(trace: *Trace, allocator: std.mem.Allocator) void {
        \\    const node = trace.emit(allocator) catch 0;
        \\    trace.nodes.items[node - 1] = 9;
        \\}
    );
}

test "index-minus-one Ocean return: selected nonempty table headers" {
    try testing.expectNoFireTyped(check,
        \\const Kind = enum { short, long };
        \\pub fn last(kind: Kind) u8 {
        \\    const entries = table(kind);
        \\    return entries[entries.len - 1];
        \\}
        \\fn table(kind: Kind) []const u8 {
        \\    return switch (kind) {
        \\        .short => &.{7},
        \\        .long => &.{ 7, 9 },
        \\    };
        \\}
    );
}

test "index-minus-one Ocean return: selected table with an empty header still warns" {
    try testing.expectFiresTyped(check, R,
        \\const Kind = enum { short, long };
        \\pub fn last(kind: Kind) u8 {
        \\    const entries = table(kind);
        \\    return entries[entries.len - 1];
        \\}
        \\fn table(kind: Kind) []const u8 {
        \\    return switch (kind) {
        \\        .short => &.{},
        \\        .long => &.{ 7, 9 },
        \\    };
        \\}
    );
}

test "index-minus-one Ocean return: effectful array operand cannot export a stale floor" {
    try testing.expectFiresTyped(check, R,
        \\pub fn last() u8 {
        \\    const entries = choose();
        \\    return entries[entries.len - 1];
        \\}
        \\var backing: [2]u8 = .{ 7, 9 };
        \\var view: []const u8 = &backing;
        \\fn erase() u8 { view = &.{}; return 0; }
        \\fn choose() []const u8 {
        \\    _ = .{erase()};
        \\    return view;
        \\}
    );
}

test "index-minus-one Ocean Memory: explicit error return does not erase success floor" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Trace = struct {
        \\    nodes: std.ArrayList(u8),
        \\    fn emit(self: *Trace, allocator: std.mem.Allocator, fail: bool) !usize {
        \\        if (fail) return error.Refused;
        \\        try self.nodes.append(allocator, 7);
        \\        return @intCast(self.nodes.items.len);
        \\    }
        \\};
        \\pub fn set(trace: *Trace, allocator: std.mem.Allocator, fail: bool) !void {
        \\    const node = try trace.emit(allocator, fail);
        \\    trace.nodes.items[node - 1] = 9;
        \\}
    );
}

test "index-minus-one Ocean Memory: zero successful return still warns" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Trace = struct {
        \\    nodes: std.ArrayList(u8),
        \\    fn emit(self: *Trace, allocator: std.mem.Allocator, skip: bool) !usize {
        \\        if (skip) return 0;
        \\        try self.nodes.append(allocator, 7);
        \\        return @intCast(self.nodes.items.len);
        \\    }
        \\};
        \\pub fn set(trace: *Trace, allocator: std.mem.Allocator, skip: bool) !void {
        \\    const node = try trace.emit(allocator, skip);
        \\    trace.nodes.items[node - 1] = 9;
        \\}
    );
}

test "index-minus-one Ocean return: direct selected table length is positive" {
    try testing.expectNoFireTyped(check,
        \\const Kind = enum { short, long };
        \\pub fn last(kind: Kind) u8 {
        \\    return table(kind)[table(kind).len - 1];
        \\}
        \\fn table(kind: Kind) []const u8 {
        \\    return switch (kind) {
        \\        .short => &.{7},
        \\        .long => &.{ 7, 9 },
        \\    };
        \\}
    );
}

test "index-minus-one Ocean return: direct selected empty table length still warns" {
    try testing.expectFiresTyped(check, R,
        \\const Kind = enum { short, long };
        \\pub fn last(kind: Kind) u8 {
        \\    return table(kind)[table(kind).len - 1];
        \\}
        \\fn table(kind: Kind) []const u8 {
        \\    return switch (kind) {
        \\        .short => &.{},
        \\        .long => &.{ 7, 9 },
        \\    };
        \\}
    );
}

test "index-minus-one Ocean return: direct header extent snapshots pre-call arguments" {
    try testing.expectFiresTyped(check, R,
        \\var backing: [2]u8 = .{ 7, 9 };
        \\pub fn last() u8 {
        \\    var n: usize = 0;
        \\    return backing[take(n, &n).len - 1];
        \\}
        \\fn take(n: usize, out: *usize) []const u8 {
        \\    out.* = 1;
        \\    return backing[0..n];
        \\}
    );
}
