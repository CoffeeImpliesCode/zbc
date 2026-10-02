//! Reports index subtraction when no path-sensitive positive bound is known.
//! Type names, nearby guard text, and assertions in other callers are not proofs.

const std = @import("std");
const Ast = std.zig.Ast;
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");
const testing = @import("../../testing.zig");
const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "index-minus-one-without-zero-guard";

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
        const subscript = ungroup(tree, tree.nodeData(access).node_and_node[1]);
        if (tree.nodeTag(subscript) != .sub) continue;
        const operands = tree.nodeData(subscript).node_and_node;
        const amount = ungroup(tree, operands[1]);
        if (tree.nodeTag(amount) != .number_literal) continue;
        const literal = std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(amount)), 0) catch continue;
        if (literal != 1) continue;
        const token = tree.nodeMainToken(access);
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        const body = tokens.bodyOf(tree, declaration).?;
        if (!tokens.isRuntimeUse(tree, declaration, token)) continue;
        if (try value_range.provesPositive(gpa, tree, body, ungroup(tree, operands[0]), token, cache)) continue;
        try report(gpa, problems, tree, access, operands[0]);
    }
}

fn ungroup(tree: *const Ast, node: Ast.Node.Index) Ast.Node.Index {
    var result = node;
    for (0..64) |_| {
        if (tree.nodeTag(result) != .grouped_expression) return result;
        result = tree.nodeData(result).node_and_token[0];
    }
    return result;
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
        .start = Pos.fromTokenStart(tree, tree.nodeMainToken(access)),
        .end = Pos.fromTokenEnd(tree, tree.lastToken(access)),
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
