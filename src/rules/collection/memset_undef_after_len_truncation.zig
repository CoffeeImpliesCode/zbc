//! Detect empty undefined fills immediately after a proved length reduction.
const std = @import("std");
const Ast = std.zig.Ast;
const Iterator = @import("type_engine").AstIterator;
const budget_mod = @import("../../budget.zig");
const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");
const problem = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const R = "memset-undef-after-len-truncation";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    if (!config_mod.isEnabled(config, .memset_undef_after_len_truncation)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    _: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    var frames: [256]Iterator = undefined;
    frames[0] = .{ .array = .{ body.toOptional(), .none, .none, .none, .none } };
    var depth: usize = 1;
    while (depth != 0) {
        const node = frames[depth - 1].next(tree) orelse {
            depth -= 1;
            continue;
        };
        switch (tree.nodeTag(node)) {
            .fn_decl, .@"comptime" => continue,
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                var statements = Iterator.init(tree, node);
                var previous: ?Ast.Node.Index = null;
                while (statements.next(tree)) |current| {
                    if (previous) |assignment|
                        try checkPair(gpa, tree, cache, body, assignment, current, problems);
                    previous = current;
                }
            },
            else => {},
        }
        if (depth == frames.len) return budget_mod.fail(.{ .limit = .memset_walk_depth, .limit_value = frames.len, .reached = frames.len });
        frames[depth] = Iterator.init(tree, node);
        depth += 1;
    }
}

fn checkPair(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    body: Ast.Node.Index,
    assignment: Ast.Node.Index,
    fill: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    if (tree.nodeTag(assignment) != .assign) return;
    const lhs, const rhs = tree.nodeData(assignment).node_and_node;
    if (tree.nodeTag(lhs) != .field_access) return;
    const collection, const field = tree.nodeData(lhs).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(field), "len")) return;
    var buffer: [2]Ast.Node.Index = undefined;
    const arguments = tree.builtinCallParams(&buffer, fill) orelse return;
    if (arguments.len != 2 or !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(fill)), "@memset")) return;
    if (!std.mem.eql(u8, tree.getNodeSource(arguments[1]), "undefined")) return;

    const empty_fill = if (tree.fullSlice(arguments[0])) |slice|
        slice.ast.end == .none and slice.ast.sentinel == .none and
            sameExpression(tree, slice.ast.sliced, collection) and
            (sameExpression(tree, slice.ast.start, rhs) or sameExpression(tree, slice.ast.start, lhs))
    else
        sameExpression(tree, arguments[0], collection) and (cache.comptimeIntValueOf(rhs) orelse 1) == 0;
    if (!empty_fill) return;
    if (!try value_range.provesLessThan(gpa, tree, body, rhs, lhs, tree.firstToken(assignment), cache)) return;
    const message = try gpa.dupe(u8, "this undefined fill is empty after a proved length reduction. Fill the removed range before changing .len. Alternatively, use its saved backing pointer and original bound.");
    errdefer gpa.free(message);
    const token = tree.nodeMainToken(fill);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .warning,
        .start = try problem.Pos.fromTokenStart(tree, token),
        .end = try problem.Pos.fromTokenEnd(tree, token),
        .message = message,
    });
}

fn sameExpression(tree: *const Ast, a: Ast.Node.Index, b: Ast.Node.Index) bool {
    var left = tree.firstToken(a);
    var right = tree.firstToken(b);
    const left_end = tree.lastToken(a);
    const right_end = tree.lastToken(b);
    while (left <= left_end and right <= right_end) {
        if (!std.mem.eql(u8, tree.tokenSlice(left), tree.tokenSlice(right))) return false;
        left += 1;
        right += 1;
    }
    return left > left_end and right > right_end;
}

test "shrink then empty tail memset fires" {
    try testing.expectFiresTyped(check, R,
        \\const T = struct {
        \\    items: []u8,
        \\    pub fn shrink(self: *T, new_len: usize) void {
        \\        if (new_len >= self.items.len) return;
        \\        self.items.len = new_len;
        \\        @memset(self.items[new_len..], undefined);
        \\    }
        \\};
    );
}

test "clear then empty whole-slice memset fires" {
    try testing.expectFiresTyped(check, R,
        \\const T = struct {
        \\    items: []u8,
        \\    pub fn clear(self: *T) void {
        \\        if (self.items.len == 0) return;
        \\        self.items.len = 0;
        \\        @memset(self.items, undefined);
        \\    }
        \\};
    );
}

test "memset before truncation clears the original tail" {
    try testing.expectNoFireTyped(check,
        \\const T = struct {
        \\    items: []u8,
        \\    pub fn shrink(self: *T, new_len: usize) void {
        \\        if (new_len >= self.items.len) return;
        \\        @memset(self.items[new_len..], undefined);
        \\        self.items.len = new_len;
        \\    }
        \\};
    );
}

test "memset on a different field does not clear a truncated tail" {
    try testing.expectNoFireTyped(check,
        \\const T = struct {
        \\    items: []u8,
        \\    other: []u8,
        \\    pub fn shrink(self: *T, new_len: usize) void {
        \\        if (new_len >= self.items.len) return;
        \\        self.items.len = new_len;
        \\        @memset(self.other, undefined);
        \\    }
        \\};
    );
}

test "append growth and initialization are not truncation" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn append(list: *std.ArrayList(u8), gpa: std.mem.Allocator, count: usize) !void {
        \\    const old_len = list.items.len;
        \\    const new_len = try std.math.add(usize, old_len, count);
        \\    try list.ensureTotalCapacity(gpa, new_len);
        \\    list.items.len = new_len;
        \\    @memset(list.items[old_len..new_len], 0);
        \\}
    );
}

test "a saved removed range remains valid through its backing pointer" {
    try testing.expectNoFireTyped(check,
        \\const List = struct {
        \\    items: []u8,
        \\    pub fn shrink(self: *List, new_len: usize) void {
        \\        if (new_len >= self.items.len) return;
        \\        const old_len = self.items.len;
        \\        self.items.len = new_len;
        \\        @memset(self.items.ptr[new_len..old_len], undefined);
        \\    }
        \\};
    );
}

test "clearing retained elements is not an attempt to clear the removed tail" {
    try testing.expectNoFireTyped(check,
        \\const List = struct {
        \\    items: []u8,
        \\    pub fn shrink(self: *List) void {
        \\        if (self.items.len <= 3) return;
        \\        self.items.len = 3;
        \\        @memset(self.items, undefined);
        \\    }
        \\};
    );
}

test "a stale shrinking guard cannot prove a later growth is truncation" {
    try testing.expectNoFireTyped(check,
        \\const List = struct {
        \\    items: []u8,
        \\    pub fn change(self: *List, count: usize) void {
        \\        var new_len = count;
        \\        if (new_len >= self.items.len) return;
        \\        new_len = self.items.len + 1;
        \\        self.items.len = new_len;
        \\        @memset(self.items[new_len..], undefined);
        \\    }
        \\};
    );
}
