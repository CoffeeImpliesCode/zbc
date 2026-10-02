//! Detect empty undefined fills immediately after a proved length reduction.
const std = @import("std");
const Ast = std.zig.Ast;
const Iterator = @import("type_engine").AstIterator;
const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");
const problem = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const budget_mod = @import("../../budget.zig");
const R = "memset-undef-after-len-truncation";

/// Depth of the explicit iterator stack.  One `Iterator` is pushed per
/// nesting level, so this is also the walk's frame bound.
const max_frames: usize = 256;

/// A walk counter widened to the diagnostic's 32-bit field.  Clamping
/// keeps the reported bound equal to the real bound for every file that
/// could be parsed at all, instead of trapping on a 64-bit node count.
fn bound(value: usize) u32 {
    return @intCast(@min(value, std.math.maxInt(u32)));
}

/// Record which cap the walk hit — bound, how far the counter got, the
/// enclosing function and the node the walk was on — and return the
/// error every bounded walk propagates.  A caller that swallows the
/// error still knows from the record exactly why the file was skipped.
fn giveUp(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    node: Ast.Node.Index,
    limit: budget_mod.Limit,
    limit_value: u32,
    reached: u32,
) budget_mod.BudgetError {
    var name: budget_mod.NameBuf = .{};
    if (proto.name_token) |name_tok| name.set(tree.tokenSlice(name_tok));
    const site = problem.Pos.fromTokenStart(tree, tree.nodeMainToken(node));
    return budget_mod.fail(.{
        .limit = limit,
        .limit_value = limit_value,
        .reached = reached,
        .byte = site.byte,
        .line = site.line,
        .column = site.column,
        .function = name,
    });
}

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
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    var frames: [max_frames]Iterator = undefined;
    frames[0] = .{ .array = .{ body.toOptional(), .none, .none, .none, .none } };
    var depth: usize = 1;
    var visited: usize = 0;
    while (depth != 0) {
        const node = frames[depth - 1].next(tree) orelse {
            depth -= 1;
            continue;
        };
        if (visited == tree.nodes.len) return giveUp(tree, proto, node, .memset_walk_nodes, bound(tree.nodes.len), bound(visited));
        visited += 1;
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
        if (depth == frames.len) return giveUp(tree, proto, node, .memset_walk_depth, bound(frames.len), bound(depth));
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
        .start = problem.Pos.fromTokenStart(tree, token),
        .end = problem.Pos.fromTokenEnd(tree, token),
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

test "a walk past the frame cap names the cap, the bound, the function and the site" {
    const gpa = std.testing.allocator;
    // Nesting deeper than the explicit iterator stack allows.  The bare
    // `error.AnalysisBudgetExceeded` this used to return named none of
    // it: the CLI could only report "some walk gave up" without saying
    // which cap, how deep it got, or where.
    const nesting = max_frames + 8;
    var src: std.ArrayListUnmanaged(u8) = .empty;
    defer src.deinit(gpa);
    try src.appendSlice(gpa,
        \\const T = struct {
        \\    pub fn deep(self: *T) void {
    );
    var i: usize = 0;
    while (i < nesting) : (i += 1) try src.appendSlice(gpa, "{");
    try src.appendSlice(gpa, "\n");
    i = 0;
    while (i < nesting) : (i += 1) try src.appendSlice(gpa, "}");
    try src.appendSlice(gpa, "\n}\n};\n");

    budget_mod.clear();
    try std.testing.expectError(
        error.AnalysisBudgetExceeded,
        testing.runRuleTyped(gpa, check, src.items),
    );
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.memset_walk_depth, failure.limit);
    try std.testing.expectEqual(@as(u32, @intCast(max_frames)), failure.limit_value);
    try std.testing.expectEqual(@as(u32, @intCast(max_frames)), failure.reached);
    try std.testing.expectEqualStrings("deep", failure.function.slice());
    try std.testing.expect(failure.byte != 0);
    try std.testing.expect(failure.line != 0);
}
