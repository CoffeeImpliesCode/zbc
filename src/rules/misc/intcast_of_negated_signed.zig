//! Check signed negation before checking the destination integer range.
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

const R = "intcast-of-negated-signed";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .intcast_of_negated_signed)) return;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const token = tree.nodeMainToken(node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "@intCast")) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, node).?;
        if (params.len != 1) continue;
        const negative = negation(tree, params[0]) orelse continue;
        const operand = tree.nodeData(negative).node;
        const source = cache.intInfoOf(operand);
        if (source) |integer| {
            if (!integer.signed) continue;
        }
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        if (!tokens.isRuntimeUse(tree, declaration, token)) continue;
        const bounds = try value_range.boundsAt(gpa, tree, tokens.bodyOf(tree, declaration).?, negative, token, cache);
        const negation_fits = if (source) |integer|
            bounds.fitsInteger(integer.bits, true)
        else
            cache.comptimeIntValueOf(operand) != null;
        if (negation_fits) {
            if (cache.intInfoOf(node)) |destination| {
                if (bounds.fitsInteger(destination.bits, destination.signed)) continue;
            }
        }
        const message = try gpa.dupe(u8,
            "the negation and destination conversion were not both proved in range; negating the signed minimum overflows even under a negative-sign guard; use @abs for an unsigned magnitude and separately check any narrower destination");
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

fn negation(tree: *const Ast, original: Ast.Node.Index) ?Ast.Node.Index {
    var node = original;
    for (0..64) |_| {
        if (tree.nodeTag(node) == .negation) return node;
        if (tree.nodeTag(node) != .grouped_expression) return null;
        node = tree.nodeData(node).node_and_token[0];
    }
    return null;
}

test "intcast-of-negated-signed: range proof retains minimum in the negative branch" {
    try testing.expectFiresTyped(check, R,
        \\fn magnitude(value: i32) u32 {
        \\    if (value < 0) return @intCast(-value);
        \\    return @intCast(value);
        \\}
    );
}

test "intcast-of-negated-signed: range proof excludes the signed minimum" {
    try testing.expectNoFireTyped(check,
        \\fn negate(value: i8) i8 {
        \\    if (value == -128) return 0;
        \\    return @intCast(-value);
        \\}
    );
}


test "intcast-of-negated-signed: the destination must also fit" {
    try testing.expectFiresTyped(check, R,
        \\fn magnitude(value: i32) u8 {
        \\    if (value < -1000 or value > 0) return 0;
        \\    return @intCast(-value);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn magnitude(value: i32) u8 {
        \\    if (value < -255 or value > 0) return 0;
        \\    return @intCast(-value);
        \\}
    );
}

test "intcast-of-negated-signed: unsigned magnitude and constant negation are safe" {
    try testing.expectNoFireTyped(check,
        \\fn magnitude(value: i64) u64 { return @abs(value); }
        \\fn constant() i32 { return @intCast(-1); }
    );
}
