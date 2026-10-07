//! Detects `catch |err| @panic(...)` and `catch |err| std.debug.panic(...)` —
//! catching a named error and immediately panicking prevents callers from
//! handling recoverable conditions and turns user-triggerable errors into DoS.
//!
//! In Zig the idiomatic responses to an unexpected error are:
//!   - `try` to propagate it up the call stack
//!   - `catch unreachable` when the error is genuinely impossible (compiler-
//!     verified in safe modes)
//!   - `catch |err| return err` to explicitly re-return
//!
//! `catch |err| @panic(...)` is different: the programmer named the error
//! (signaling awareness) but then chose to crash the process instead of
//! returning it.  For errors triggered by user-controlled inputs this turns
//! a recoverable error into an unconditional crash.
//!
//! Real-world instance:
//!   - oven-sh/bun#30082 (S3 URL encoding): four `var buff: [1024]u8 = undefined`
//!     encode calls used `catch |err| std.debug.panic(...)` on
//!     `error.BufferTooSmall`.  S3 keys can exceed 341 bytes (which triple-
//!     encode past 1024), so any legitimate over-sized key triggered the panic.
//!     Fix: size buffer to `input.len * 3` and use `try`.
//!
//! Detection (Tier 1, token walk inside fn bodies):
//!   Pattern A: `catch pipe identifier pipe builtin("@panic") l_paren` — 6 tokens
//!   Pattern B: `catch pipe identifier pipe identifier("std") period
//!               identifier("debug") period identifier("panic") l_paren` — 10 tokens
//!   Fire at the `keyword_catch` token.
//!   `catch unreachable` does NOT fire (no pipe-identifier-pipe).
//!   `catch |_| @panic(...)` fires — the discard form is equally suspicious.
//!   Suppression: function bodies whose first token falls inside a `test { … }`
//!   block are skipped — panicking on error is reasonable in test infrastructure.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "catch-error-panic";

const Range = struct { start: Ast.TokenIndex, end: Ast.TokenIndex };
const State = struct {
    problems: *std.ArrayListUnmanaged(Problem),
    test_ranges: *const std.ArrayListUnmanaged(Range),
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .catch_error_panic)) return;
    _ = cache;

    var test_ranges: std.ArrayListUnmanaged(Range) = .empty;
    defer test_ranges.deinit(gpa);
    try collectTestRanges(gpa, tree, &test_ranges);

    var state = State{ .problems = problems, .test_ranges = &test_ranges };
    try tokens.forEachFnBody(gpa, tree, &state, checkBody);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    state: *State,
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Skip function bodies inside test blocks — panic-on-error is acceptable
    // in test infrastructure where verbose failure is the goal.
    if (isInTestRange(state.test_ranges.items, first)) return;

    if (first + 5 > last) return;

    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        if (tags[t] != .keyword_catch) continue;
        if (tags[t + 1] != .pipe) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .pipe) continue;

        // Pattern A: catch |err| @panic(
        if (tags[t + 4] == .builtin and
            std.mem.eql(u8, tree.tokenSlice(t + 4), "@panic") and
            tags[t + 5] == .l_paren)
        {
            // `catch |e| @panic(@errorName(e))` is strictly better than
            // `catch unreachable` — it crashes with a named error message
            // instead of silent UB.  Treat it as the documented-safe form
            // and do not flag it.
            if (t + 7 <= last and
                tags[t + 6] == .builtin and
                std.mem.eql(u8, tree.tokenSlice(t + 6), "@errorName") and
                tags[t + 7] == .l_paren) continue;
            try report(gpa, state.problems, tree, t, t + 5);
            continue;
        }

        // Pattern B: catch |err| std.debug.panic(
        if (t + 9 <= last and
            tags[t + 4] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 4), "std") and
            tags[t + 5] == .period and
            tags[t + 6] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 6), "debug") and
            tags[t + 7] == .period and
            tags[t + 8] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 8), "panic") and
            tags[t + 9] == .l_paren)
        {
            try report(gpa, state.problems, tree, t, t + 9);
            continue;
        }
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    catch_tok: Ast.TokenIndex,
    end_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`catch |err| @panic(...)` — catching an error and immediately panicking turns a recoverable error into a process crash; use `try` to propagate the error, or `catch unreachable` only if the error is provably impossible in this call path",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, catch_tok),
        .end = try Pos.fromTokenEnd(tree, end_tok),
        .message = msg,
    });
}

fn collectTestRanges(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    out: *std.ArrayListUnmanaged(Range),
) !void {
    if (tree.tokens.len == 0) return;
    const tags = tree.tokens.items(.tag);
    // The root decl ends on the final token of the stream, so `last` is the
    // index the old half-open `@intCast(tags.len)` bound stood for.  Every
    // loop below is therefore inclusive of it, and no `usize` stream length
    // is narrowed into the token index type.
    const last: Ast.TokenIndex = tree.lastToken(.root);
    var i: Ast.TokenIndex = 0;
    while (i <= last) : (i += 1) {
        if (tags[i] != .keyword_test) continue;
        var j = i + 1;
        while (j <= last and tags[j] != .l_brace) : (j += 1) {
            if (tags[j] == .semicolon or tags[j] == .r_brace) break;
        }
        if (j > last or tags[j] != .l_brace) continue;
        var depth: u32 = 0;
        var k = j;
        while (k <= last) : (k += 1) {
            if (tags[k] == .l_brace) depth += 1 else if (tags[k] == .r_brace) {
                depth -= 1;
                if (depth == 0) break;
            }
        }
        if (k > last) break;
        try out.append(gpa, .{ .start = i, .end = k });
        i = k;
    }
}

fn isInTestRange(ranges: []const Range, tok: Ast.TokenIndex) bool {
    for (ranges) |r| {
        if (tok >= r.start and tok <= r.end) return true;
    }
    return false;
}

// ── Tests ──────────────────────────────────────────────────

test "catch-error-panic: @panic form fires" {
    try testing.expectFires(check, R,
        \\fn encode(buf: []u8, input: []const u8) !void { _ = buf; _ = input; }
        \\fn run(input: []const u8) void {
        \\    var buff: [1024]u8 = undefined;
        \\    encode(&buff, input) catch |err| @panic("encode failed");
        \\    _ = err;
        \\}
        \\
    );
}

test "catch-error-panic: std.debug.panic form fires" {
    try testing.expectFires(check, R,
        \\fn encode(buf: []u8, input: []const u8) !void { _ = buf; _ = input; }
        \\fn run(input: []const u8) void {
        \\    var buff: [1024]u8 = undefined;
        \\    encode(&buff, input) catch |err| std.debug.panic("encode failed: {}", .{err});
        \\}
        \\
    );
}

test "catch-error-panic: catch unreachable does not fire" {
    try testing.expectNoFire(check,
        \\fn encode(buf: []u8, input: []const u8) !void { _ = buf; _ = input; }
        \\fn run(input: []const u8) void {
        \\    var buff: [1024]u8 = undefined;
        \\    encode(&buff, input) catch unreachable;
        \\}
        \\
    );
}

test "catch-error-panic: try form does not fire" {
    try testing.expectNoFire(check,
        \\fn encode(buf: []u8, input: []const u8) !void { _ = buf; _ = input; }
        \\fn run(input: []const u8) !void {
        \\    var buff: [1024]u8 = undefined;
        \\    try encode(&buff, input);
        \\}
        \\
    );
}

test "catch-error-panic: catch return does not fire" {
    try testing.expectNoFire(check,
        \\fn encode(buf: []u8, input: []const u8) !void { _ = buf; _ = input; }
        \\fn run(input: []const u8) !void {
        \\    var buff: [1024]u8 = undefined;
        \\    encode(&buff, input) catch |err| return err;
        \\}
        \\
    );
}

test "catch-error-panic: catch |e| @panic(@errorName(e)) does not fire" {
    // @panic(@errorName(e)) is strictly better than catch unreachable:
    // named crash message instead of UB in ReleaseFast.
    try testing.expectNoFire(check,
        \\fn finish(self: *Self) void {
        \\    self.flattenCpPools() catch |e| @panic(@errorName(e));
        \\}
        \\
    );
}

test "catch-error-panic: catch |e| @panic(fixed-string) still fires" {
    // A fixed-string panic hides which error occurred; still suspicious.
    try testing.expectFires(check, R,
        \\fn run(input: []const u8) void {
        \\    encode(input) catch |e| @panic("unexpected error");
        \\    _ = e;
        \\}
        \\fn encode(_: []const u8) !void {}
        \\
    );
}

test "catch-error-panic: a nested helper in a trailing test block is suppressed" {
    // The `test` block is the LAST decl in the file, so its range closes only
    // if the scan's upper bound includes the final token — the span the old
    // half-open `@intCast(tags.len)` walk covered.  Both functions carry the
    // same pattern, so the count separates a lost test range (2 findings)
    // from a body walk that never reached either function (0 findings).
    try testing.expectCount(check, R, 1,
        \\const std = @import("std");
        \\fn encode(input: []const u8) !void { _ = input; }
        \\fn report(input: []const u8) void {
        \\    encode(input) catch |err| std.debug.panic("encode failed: {s}", .{@errorName(err)});
        \\}
        \\test "nested helper" {
        \\    const Helpers = struct {
        \\        fn helper(input: []const u8) void {
        \\            encode(input) catch |err| std.debug.panic("encode failed: {s}", .{@errorName(err)});
        \\        }
        \\    };
        \\    Helpers.helper("x");
        \\}
        \\
    );
}
