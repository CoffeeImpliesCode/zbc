//! Report collection-length casts whose input does not have a proved destination range.
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

const R = "index-type-narrowing-wraparound";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .index_type_narrowing_wraparound)) return;
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
        if (params.len != 1 or !containsLength(tree, params[0], 0)) continue;
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        if (!tokens.isRuntimeUse(tree, declaration, token)) continue;
        if (cache.intInfoOf(node)) |destination| {
            if (cache.intInfoOf(params[0])) |source| {
                if (value_range.NumericRange.integerType(source.bits, source.signed).fitsInteger(destination.bits, destination.signed)) continue;
            }
            const bounds = try value_range.boundsAt(gpa, tree, tokens.bodyOf(tree, declaration).?, params[0], token, cache);
            if (bounds.fitsInteger(destination.bits, destination.signed)) continue;
        }
        const message = try gpa.dupe(u8,
            "the collection length was not proved to fit the destination integer; an out-of-range @intCast traps in Debug/ReleaseSafe and causes undefined behavior in unchecked builds, rather than defined wrapping; prove a bound or use a sufficient integer range");
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

fn containsLength(tree: *const Ast, node: Ast.Node.Index, depth: u8) bool {
    if (depth == 64) return false;
    if (tree.nodeTag(node) == .field_access) {
        if (std.mem.eql(u8, tree.tokenSlice(tree.nodeData(node).node_and_token[1]), "len")) return true;
    }
    var children = @import("type_engine").AstIterator.init(tree, node);
    while (children.next(tree)) |child| {
        if (containsLength(tree, child, depth + 1)) return true;
    }
    return false;
}

test "index-type-narrowing-wraparound: range proof accepts a fixed array" {
    try testing.expectNoFireTyped(check,
        \\fn end(array: *const [128]u8) i16 {
        \\    var index: i16 = @intCast(array.len);
        \\    index -= 1;
        \\    return index;
        \\}
    );
}

test "index-type-narrowing-wraparound: range proof ignores maximum spelling" {
    try testing.expectFiresTyped(check, R,
        \\const max_i16 = 70000;
        \\fn end(array: []const u8) i16 {
        \\    var index: i16 = @intCast(@min(array.len, max_i16));
        \\    index -= 1;
        \\    return index;
        \\}
    );
}


test "index-type-narrowing-wraparound: signed index spelling is not a narrowing conversion" {
    try testing.expectNoFireTyped(check,
        \\fn first(array: []const u8) u8 {
        \\    var index: i16 = 0;
        \\    index += 1;
        \\    return array[@intCast(index)];
        \\}
    );
}

test "index-type-narrowing-wraparound: unsigned destinations also require bounds" {
    try testing.expectFiresTyped(check, R,
        \\fn size(array: []const u8) u16 { return @intCast(array.len); }
    );
    try testing.expectNoFireTyped(check,
        \\fn size(array: []const u8) u16 {
        \\    if (array.len > 65535) return 0;
        \\    return @intCast(array.len);
        \\}
    );
}

test "index-type-narrowing-wraparound: trusted clipping uses the actual destination maximum" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn size(array: []const u8) i16 { return @intCast(@min(array.len, std.math.maxInt(i16))); }
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn size(array: []const u8) i16 { return @intCast(@min(array.len, std.math.maxInt(i32))); }
    );
}
