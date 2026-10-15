//! oven-sh/bun#29968 detector — `<x>.free(X);` immediately followed by
//! `X = try …;` with no intervening reset of `X` to a sentinel.
//! If the `try` propagates an error, `X` is left pointing at
//! freed memory; a subsequent `deinit` then re-frees it.
//!
//! A deferred release is a registration, not an inline free. Its failure
//! domain instead requires a defined value and no duplicate live cleanup.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const query = @import("../../ast/token_query.zig");
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");
const fresh_storage = @import("../../cache/fresh_storage.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const Atom = query.Atom;

const bodyOf = tokens.bodyOf;

// `<recv>.free(<arg>);` — captures the freed arg as range slot 0.
const free_call = &[_]Atom{
    .{ .tok = .period },
    .{ .text = "free" },
    .{ .tok = .l_paren },
    .{ .capture_until = .{ .slot = 0, .stops = &.{.r_paren} } },
    .{ .tok = .r_paren },
    .{ .tok = .semicolon },
};

// `<same-tokens-as-slot-0> = try ...` — the dangling-reassignment shape.
const realloc_pattern = &[_]Atom{
    .{ .ref_range = 0 },
    .{ .tok = .equal },
    .{ .tok = .keyword_try },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .free_then_try_realloc)) return;
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const body = bodyOf(tree, node) orelse continue;
        try checkBody(gpa, tree, cache, node, body, problems);
    }
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    declaration: Ast.Node.Index,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    const frees = try query.findAllInBody(gpa, tree, free_call, first, last);
    defer gpa.free(frees);

    for (frees) |fm| {
        // After the free's `;`, skip any closing `}` tokens — the
        // free might be inside `if (cond) { … }` while the realloc
        // sits in the enclosing scope.  Don't skip past other
        // tokens — intervening code may legitimately change <arg>.
        var next: Ast.TokenIndex = fm.end + 1;
        while (next <= last and tags[next] == .r_brace) : (next += 1) {}
        if (next > last) continue;

        if (query.matchAt(tree, realloc_pattern, next, last, &fm) == null) continue;

        const range = fm.range_captures[0].?;
        const call_index = try cache.getCallIndex();
        // CallOperands.queryToken uses the member expression's `.` token.
        // Keep the following identifier only for the reported location.
        const call_node = call_index.by_callee_token.get(fm.start) orelse continue;
        const actual = try cache.actualCallSummaryAt(fm.start, null);
        if (actual) |record| {
            const primitive = try fresh_storage.allocatorPrimitive(cache, record, .{
                .claim = .{ .first = fm.start, .last = fm.end }, .depth = 0,
            });
            if (primitive == null and
                try cache.callEffectAt(fm.start, .{ .whole = record.callee }, .{}) == .read_only) continue;
        }
        const deferred = deferredAt(tree, call_node, body);
        if (deferred) |registration| {
            if (try initializedBefore(cache, declaration, body, range, tree.firstToken(registration)) and
                !duplicateDeferred(tree, frees, range, fm.start, body, registration)) continue;
        } else if (errorResetBefore(tree, body, range, tree.firstToken(call_node))) continue;
        try report(gpa, problems, tree, fm.start, range, deferred != null);
    }
}

fn deferredAt(tree: *const Ast, call: Ast.Node.Index, body: Ast.Node.Index) ?Ast.Node.Index {
    var selected: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .@"defer" and tag != .@"errdefer") continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(node) < tree.firstToken(body) or tree.lastToken(node) > tree.lastToken(body)) continue;
        if (tree.firstToken(node) <= tree.firstToken(call) and tree.lastToken(call) <= tree.lastToken(node)) {
            if (selected == null or tree.firstToken(node) > tree.firstToken(selected.?)) selected = node;
        }
    }
    return selected;
}

fn sameRange(tree: *const Ast, left: query.TokenRange, right: query.TokenRange) bool {
    if (left.end - left.start != right.end - right.start) return false;
    for (0..left.end - left.start + 1) |offset| {
        const i: Ast.TokenIndex = @intCast(offset);
        if (tree.tokenTag(left.start + i) != tree.tokenTag(right.start + i) or
            !std.mem.eql(u8, tree.tokenSlice(left.start + i), tree.tokenSlice(right.start + i))) return false;
    }
    return true;
}

fn duplicateDeferred(tree: *const Ast, frees: []const query.Match, range: query.TokenRange, current: Ast.TokenIndex, body: Ast.Node.Index, registration: Ast.Node.Index) bool {
    for (frees) |other| {
        if (other.start == current or !sameRange(tree, range, other.range_captures[0].?)) continue;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .@"defer" and tag != .@"errdefer") continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (tree.firstToken(node) < tree.firstToken(body) or tree.lastToken(node) > tree.lastToken(body)) continue;
            // The query includes the statement's semicolon. A single-call
            // defer AST ends at `)`, so compare the invocation, not `;`.
            // Both registrations read the same current slot at cleanup time.
            if (tree.firstToken(node) <= other.start and other.end - 1 <= tree.lastToken(node) and
                registrationScope(tree, node, body) == registrationScope(tree, registration, body)) return true;
        }
    }
    return false;
}

fn registrationScope(tree: *const Ast, statement: Ast.Node.Index, body: Ast.Node.Index) Ast.Node.Index {
    var selected = body;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(node) < tree.firstToken(selected) or tree.lastToken(node) > tree.lastToken(selected)) continue;
        if (tree.firstToken(node) <= tree.firstToken(statement) and tree.lastToken(statement) <= tree.lastToken(node))
            selected = node;
    }
    return selected;
}

fn initializedBefore(cache: *file_cache_mod.FileCache, declaration: Ast.Node.Index, body: Ast.Node.Index, range: query.TokenRange, before: Ast.TokenIndex) !bool {
    const tree = cache.tree;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
    const bindings = (try cache.localBindings(proto, body)).*;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .assign) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(node) < tree.firstToken(body) or tree.lastToken(node) >= before) continue;
        const lhs, const rhs = tree.nodeData(node).node_and_node;
        if (!sameRange(tree, range, .{ .start = tree.firstToken(lhs), .end = tree.lastToken(lhs) })) continue;
        if (containsUndefined(tree, rhs)) return false;
    }
    if (range.start == range.end and tree.tokenTag(range.start) == .identifier) {
        const binding = bindings.findAt(tree.tokenSlice(range.start), range.start) orelse return false;
        if (binding.origin == .param) return true;
        if (binding.rhs_last >= before) return false;
        const initializer = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
        if (containsUndefined(tree, initializer)) return false;
        if (binding.asCall() != null) return cache.normalCleanupFresh(initializer);
        return binding.origin == .literal;
    }
    if (range.end == range.start + 2 and tree.tokenTag(range.start + 1) == .period) {
        const binding = bindings.findAt(tree.tokenSlice(range.start), range.start) orelse return false;
        if (binding.origin == .param) return true;
        const initializer = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = tree.fullStructInit(&buffer, initializer) orelse return false;
        for (literal.ast.fields) |field| {
            const value_token = tree.firstToken(field);
            if (value_token < 2) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(value_token - 2), tree.tokenSlice(range.end))) continue;
            return !std.mem.eql(u8, tree.tokenSlice(value_token), "undefined");
        }
    }
    return false;
}

fn containsUndefined(tree: *const Ast, node: Ast.Node.Index) bool {
    var token = tree.firstToken(node);
    while (token <= tree.lastToken(node)) : (token += 1) {
        if (tree.tokenTag(token) == .identifier and std.mem.eql(u8, tree.tokenSlice(token), "undefined")) return true;
    }
    return false;
}

fn errorResetBefore(tree: *const Ast, body: Ast.Node.Index, range: query.TokenRange, before: Ast.TokenIndex) bool {
    var buffer: [2]Ast.Node.Index = undefined;
    const statements = tree.blockStatements(&buffer, body) orelse return false;
    for (statements, 0..) |statement, index| {
        if (tree.firstToken(statement) >= before) break;
        if (tree.nodeTag(statement) != .@"errdefer") continue;
        const reset = tree.nodeData(statement).opt_token_and_node[1];
        if (tree.nodeTag(reset) != .assign) continue;
        const lhs, const rhs = tree.nodeData(reset).node_and_node;
        if (!sameRange(tree, range, .{ .start = tree.firstToken(lhs), .end = tree.lastToken(lhs) })) continue;
        // LIFO cleanup must reset the header before another cleanup can use
        // it. A later registration runs first and cannot receive this credit.
        for (statements[index + 1 ..]) |later| {
            if (tree.firstToken(later) >= before) break;
            if (tree.nodeTag(later) == .@"defer" or tree.nodeTag(later) == .@"errdefer") return false;
        }
        if (tree.nodeTag(rhs) == .identifier) {
            const value = tree.tokenSlice(tree.nodeMainToken(rhs));
            if (std.mem.eql(u8, value, "null")) return true;
        }
        if (tree.nodeTag(rhs) == .address_of) {
            const value = tree.nodeData(rhs).node;
            if (tree.fullArrayInit(&buffer, value)) |literal| {
                if (literal.ast.elements.len == 0) return true;
            }
            if (tree.fullStructInit(&buffer, value)) |literal| {
                if (literal.ast.fields.len == 0) return true;
            }
        }
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    period_tok: Ast.TokenIndex,
    arg_range: query.TokenRange,
    deferred: bool,
) !void {
    const starts = tree.tokens.items(.start);
    const arg_start = starts[arg_range.start];
    const arg_end = starts[arg_range.end] + tree.tokenSlice(arg_range.end).len;
    const arg_text = tree.source[arg_start..arg_end];

    const msg = if (deferred)
        try std.fmt.allocPrint(gpa,
            "deferred release of `{s}` is active before a fallible reassignment; an undefined initial value or another active release of the rebound slot makes cleanup invalid. Initialize the slot before registration and keep one cleanup per live owner",
            .{arg_text})
    else
        try std.fmt.allocPrint(gpa,
            "`{s}` is freed here and then reassigned through `try`; a failing replacement leaves the owner dangling. Reset `{s}` before the fallible call or reset it on every error-cleanup exit",
            .{ arg_text, arg_text });
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "free-then-try-realloc",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, period_tok + 1),
        .end = try Pos.fromTokenEnd(tree, period_tok + 1),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "free-then-try-realloc: adjacent free + try-alloc fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\const S = struct { columns: []T = &.{} };
        \\pub fn refill(s: *S, n: usize) !void {
        \\    std.heap.page_allocator.free(s.columns);
        \\    s.columns = try std.heap.page_allocator.alloc(T, n);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("free-then-try-realloc", problems.items[0].rule_id);
}

test "free-then-try-realloc: clearing between free and try is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\const S = struct { columns: []T = &.{} };
        \\pub fn refill(s: *S, n: usize) !void {
        \\    std.heap.page_allocator.free(s.columns);
        \\    s.columns = &.{};
        \\    s.columns = try std.heap.page_allocator.alloc(T, n);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-then-try-realloc: `catch unreachable` instead of `try` is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\const S = struct { columns: []T = &.{} };
        \\pub fn refill(s: *S, n: usize) void {
        \\    std.heap.page_allocator.free(s.columns);
        \\    s.columns = std.heap.page_allocator.alloc(T, n) catch unreachable;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-then-try-realloc: free in inner `if`, try in outer scope still fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\const S = struct { columns: []T = &.{} };
        \\pub fn refill(s: *S, n: usize, cond: bool) !void {
        \\    if (cond) {
        \\        std.heap.page_allocator.free(s.columns);
        \\    }
        \\    s.columns = try std.heap.page_allocator.alloc(T, n);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "free-then-try-realloc: free followed by unrelated stmt then try doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\const S = struct { columns: []T = &.{} };
        \\pub fn refill(s: *S, n: usize) !void {
        \\    std.heap.page_allocator.free(s.columns);
        \\    const x: u32 = 0;
        \\    _ = x;
        \\    s.columns = try std.heap.page_allocator.alloc(T, n);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-then-try-realloc: lifetime registered cleanup is not inline free" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) ![]u8 {
        \\    var bytes = try gpa.alloc(u8, 4);
        \\    errdefer gpa.free(bytes);
        \\    bytes = try gpa.alloc(u8, 8);
        \\    return bytes;
        \\}
    );
}

test "free-then-try-realloc: lifetime no-op project free" {
    try testing.expectNoFireTyped(check,
        \\const Allocator = struct {
        \\    fn free(_: Allocator, _: []u8) void {}
        \\    fn alloc(_: Allocator) ![]u8 { return &.{}; }
        \\};
        \\fn rebuild(allocator: Allocator, bytes: *[]u8) !void {
        \\    allocator.free(bytes.*);
        \\    bytes.* = try allocator.alloc();
        \\}
    );
}

test "free-then-try-realloc: lifetime failing replacement retains deferred double free" {
    try testing.expectFiresTyped(check, "free-then-try-realloc",
        \\const std = @import("std");
        \\fn rebuild(gpa: std.mem.Allocator) !void {
        \\    var bytes = try gpa.alloc(u8, 4);
        \\    defer gpa.free(bytes);
        \\    gpa.free(bytes);
        \\    bytes = try gpa.alloc(u8, 8);
        \\}
    );
}

test "free-then-try-realloc: lifetime errdefer reset protects replacement failure" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct { bytes: []u8 };
        \\fn rebuild(gpa: std.mem.Allocator, owner: *Owner) !void {
        \\    errdefer owner.bytes = &.{};
        \\    gpa.free(owner.bytes);
        \\    owner.bytes = try gpa.alloc(u8, 8);
        \\}
    );
}

test "free-then-try-realloc: undefined field before cleanup registration remains invalid" {
    try testing.expectFiresTyped(check, "free-then-try-realloc",
        \\const std = @import("std");
        \\const Owner = struct { bytes: []u8 };
        \\fn build(gpa: std.mem.Allocator) !Owner {
        \\    var self: Owner = .{ .bytes = undefined };
        \\    errdefer gpa.free(self.bytes);
        \\    self.bytes = try gpa.alloc(u8, 8);
        \\    return self;
        \\}
    );
}

test "free-then-try-realloc: cleanup registrations observe the same rebound owner" {
    try testing.expectFiresTyped(check, "free-then-try-realloc",
        \\const std = @import("std");
        \\fn read(gpa: std.mem.Allocator) !void {
        \\    var path = try gpa.alloc(u8, 4);
        \\    defer gpa.free(path);
        \\    path = try std.fmt.allocPrint(gpa, "{s}/child", .{path});
        \\    defer gpa.free(path);
        \\    return error.Missing;
        \\}
    );
}

test "free-then-try-realloc: later-running reset cannot protect earlier cleanup" {
    try testing.expectFiresTyped(check, "free-then-try-realloc",
        \\const std = @import("std");
        \\const Owner = struct { bytes: []u8 };
        \\fn rebuild(gpa: std.mem.Allocator, owner: *Owner) !void {
        \\    errdefer owner.bytes = &.{};
        \\    defer gpa.free(owner.bytes);
        \\    gpa.free(owner.bytes);
        \\    owner.bytes = try gpa.alloc(u8, 8);
        \\}
    );
}

test "free-then-try-realloc: source-proven project release is not a no-op" {
    try testing.expectFiresTyped(check, "free-then-try-realloc",
        \\const std = @import("std");
        \\const Allocator = struct {
        \\    backing: std.mem.Allocator,
        \\    fn free(self: Allocator, bytes: []u8) void { self.backing.free(bytes); }
        \\    fn alloc(self: Allocator) ![]u8 { return self.backing.alloc(u8, 8); }
        \\};
        \\fn rebuild(allocator: Allocator, bytes: *[]u8) !void {
        \\    allocator.free(bytes.*);
        \\    bytes.* = try allocator.alloc();
        \\}
    );
}
