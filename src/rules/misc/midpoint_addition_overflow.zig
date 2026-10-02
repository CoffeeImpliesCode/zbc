//! Report midpoint sums without a proved non-overflowing integer range.
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

const R = "midpoint-addition-overflow";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .midpoint_addition_overflow)) return;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [2]Ast.Node.Index = undefined;
        const operands: [2]Ast.Node.Index = switch (tag) {
            .div => tree.nodeData(node).node_and_node,
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => blk: {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (!std.mem.eql(u8, name, "@divTrunc") and
                    !std.mem.eql(u8, name, "@divFloor") and
                    !std.mem.eql(u8, name, "@divExact")) continue;
                const params = tree.builtinCallParams(&buffer, node).?;
                if (params.len != 2) continue;
                break :blk .{ params[0], params[1] };
            },
            else => continue,
        };
        if (tree.nodeTag(operands[1]) != .number_literal) continue;
        const divisor = std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(operands[1])), 0) catch continue;
        if (divisor != 2) continue;
        const sum = addition(tree, operands[0]) orelse continue;
        if (cache.isFloatType(sum) == true) continue;
        const token = tree.firstToken(sum);
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        if (!tokens.isRuntimeUse(tree, declaration, token)) continue;
        if (cache.intInfoOf(sum)) |integer| {
            const bounds = try value_range.boundsAt(gpa, tree, tokens.bodyOf(tree, declaration).?, sum, token, cache);
            if (bounds.fitsInteger(integer.bits, integer.signed)) continue;
        }
        const message = try gpa.dupe(u8, "the midpoint sum was not proved to fit its integer type before division; prove bounds for the addition or widen the operands before adding");
        errdefer gpa.free(message);
        try problems.append(gpa, .{
            .rule_id = R,
            .severity = .warning,
            .start = Pos.fromTokenStart(tree, token),
            .end = Pos.fromTokenEnd(tree, tree.lastToken(node)),
            .message = message,
        });
    }
}

fn addition(tree: *const Ast, original: Ast.Node.Index) ?Ast.Node.Index {
    var node = original;
    for (0..64) |_| {
        if (tree.nodeTag(node) == .add) return node;
        if (tree.nodeTag(node) != .grouped_expression) return null;
        node = tree.nodeData(node).node_and_token[0];
    }
    return null;
}

test "midpoint-addition-overflow: range proof accepts bounded operands" {
    try testing.expectNoFireTyped(check,
        \\fn middle(left: u32, right: u32) u32 {
        \\    if (left > 100 or right > 100) return 0;
        \\    return (left + right) / 2;
        \\}
    );
}

test "midpoint-addition-overflow: range proof ignores unrelated float declarations" {
    try testing.expectFiresTyped(check, R,
        \\fn middle(x: u32, y: u32) u32 {
        \\    const left = x;
        \\    const scale: f32 = 0.0;
        \\    _ = scale;
        \\    const right = y;
        \\    return (left + right) / 2;
        \\}
    );
}

test "midpoint-addition-overflow: unbounded sum remains uncertain" {
    try testing.expectFiresTyped(check, R,
        \\fn midpoint(left: usize, right: usize) usize { return (left + right) / 2; }
    );
}

test "midpoint-addition-overflow: floating arithmetic is not integer overflow" {
    try testing.expectNoFireTyped(check,
        \\fn midpoint(left: f64, right: f64) f64 { return (left + right) / 2; }
    );
}

test "midpoint-addition-overflow: subtraction formulation is outside this rule" {
    try testing.expectNoFireTyped(check,
        \\fn midpoint(left: usize, right: usize) usize { return left + (right - left) / 2; }
    );
}

test "midpoint-addition-overflow: loop induction proves a fixed table envelope" {
    try testing.expectNoFireTyped(check,
        \\fn search(value: f64, table: *const [29]f64) usize {
        \\    var lower: usize = 0;
        \\    var upper: usize = table.len;
        \\    while (lower + 1 < upper) {
        \\        const middle = (lower + upper) / 2;
        \\        if (table[middle] < value) lower = middle else upper = middle;
        \\    }
        \\    return lower;
        \\}
    );
}

test "midpoint-addition-overflow: loop induction rejects a growing upper bound" {
    try testing.expectFiresTyped(check, R,
        \\fn search(table: *const [256]bool) u8 {
        \\    var lower: u8 = 0;
        \\    var upper: u8 = 100;
        \\    while (lower + 1 < upper) {
        \\        const middle = (lower + upper) / 2;
        \\        if (table[middle]) lower = middle else upper += 100;
        \\    }
        \\    return lower;
        \\}
    );
}

test "midpoint-addition-overflow: signed division builtins retain addition risk" {
    try testing.expectFiresTyped(check, R,
        \\fn midpoint(left: i32, right: i32) i32 {
        \\    return @divTrunc(left + right, 2);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn midpoint(left: i32, right: i32) i32 {
        \\    if (left < -100 or left > 100 or right < -100 or right > 100) return 0;
        \\    return @divFloor(left + right, 2);
        \\}
    );
}

test "midpoint-addition-overflow: body invariants exclude terminating search states" {
    try testing.expectNoFireTyped(check,
        \\fn search(value: i64, table: *const [97]i64) i32 {
        \\    var lower: i32 = 0;
        \\    var upper: i32 = @intCast(table.len - 1);
        \\    while (lower <= upper) {
        \\        const middle = @divTrunc(lower + upper, 2);
        \\        const element = table[@intCast(middle)];
        \\        if (element < value) lower = middle + 1
        \\        else if (element > value) upper = middle - 1
        \\        else return middle;
        \\    }
        \\    return -1;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn search(value: i64, table: *const [97]i64) i8 {
        \\    var lower: i8 = 0;
        \\    var upper: i8 = @intCast(table.len - 1);
        \\    while (lower <= upper) {
        \\        const middle = @divTrunc(lower + upper, 2);
        \\        const element = table[@intCast(middle)];
        \\        if (element < value) lower = middle + 1
        \\        else if (element > value) upper = middle - 1
        \\        else return middle;
        \\    }
        \\    return -1;
        \\}
    );
}

test "midpoint-addition-overflow: nested searches preserve only unchanged outer bounds" {
    try testing.expectNoFireTyped(check,
        \\fn search(value: i64, table: *const [97]i64) i32 {
        \\    var lower: i32 = 0;
        \\    var upper: i32 = @intCast(table.len - 1);
        \\    while (lower <= upper) {
        \\        const middle = @divTrunc(lower + upper, 2);
        \\        const element = table[@intCast(middle)];
        \\        if (element < value) lower = middle + 1
        \\        else if (element > value) upper = middle - 1
        \\        else {
        \\            var offset: i8 = -1;
        \\            while (offset <= 1) : (offset += 1) {
        \\                if (offset == 0) return middle;
        \\            }
        \\            break;
        \\        }
        \\    }
        \\    return -1;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn growing(limit: u8) u8 {
        \\    const lower: u8 = 16;
        \\    var upper: u8 = 96;
        \\    while (lower <= upper) {
        \\        const middle = (lower + upper) / 2;
        \\        if (middle == limit) return middle;
        \\        var index: u8 = 0;
        \\        while (index < 2) : (index += 1) upper += 1;
        \\    }
        \\    return 0;
        \\}
    );
}
