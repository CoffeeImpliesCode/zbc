//! oven-sh/bun#29968 detector — `<x>.free(X);` immediately followed by
//! `X = try …;` with no intervening reset of `X` to a sentinel.
//! If the `try` propagates an error, `X` is left pointing at
//! freed memory; a subsequent `deinit` then re-frees it.
//!
//! Rewritten via the query DSL: `capture_until` captures the freed
//! arg's token range; `ref_range` checks the next statement starts
//! with the same range followed by `= try`.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const query = @import("../../ast/token_query.zig");
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

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
    _ = cache;

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const body = bodyOf(tree, node) orelse continue;
        try checkBody(gpa, tree, body, problems);
    }
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
        try report(gpa, problems, tree, fm.start, range);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    period_tok: Ast.TokenIndex,
    arg_range: query.TokenRange,
) !void {
    const starts = tree.tokens.items(.start);
    const arg_start = starts[arg_range.start];
    const arg_end = starts[arg_range.end] + tree.tokenSlice(arg_range.end).len;
    const arg_text = tree.source[arg_start..arg_end];

    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` is freed here and then immediately reassigned through `try`; if the `try`'s alloc fails, `{s}` is left dangling and a later `deinit` re-frees it.  Insert `{s} = &.{{}};` (or `null`/`undefined` per the field's type) between the free and the realloc",
        .{ arg_text, arg_text, arg_text },
    );
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
