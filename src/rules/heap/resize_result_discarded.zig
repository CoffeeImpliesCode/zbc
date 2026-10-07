//! Detects `_ = allocator.resize(slice, new_len)` — discarding the
//! boolean return value of `Allocator.resize`.
//!
//! `std.mem.Allocator.resize` attempts an in-place resize.  It returns
//! `true` on success and `false` when in-place growth is impossible.
//! When the caller discards the result with `_ = ...`, it doesn't know
//! whether the slice actually grew.  Any subsequent use of the slice
//! assuming `new_len` elements are valid is out-of-bounds if `resize`
//! returned false.
//!
//! Common mistake:
//!   _ = allocator.resize(buf, buf.len + extra);
//!   // BUG: buf may still be old length; writing buf[old_len..] is OOB
//!
//! Fix: use `realloc` (which always succeeds or errors) or capture the
//! bool and fall back to a reallocation on false:
//!   if (!allocator.resize(buf, new_len)) {
//!       buf = try allocator.realloc(buf, new_len);
//!   }
//!
//! Real-world shape: common when adapting C code that uses `realloc` which
//! always returns a new pointer; also seen in custom container grow methods
//! ported from languages where resize is always successful.
//!
//! Detection (Tier 1, token walk):
//!   6-token pattern:
//!     t+0: identifier("_")   t+1: equal
//!     t+2: identifier        t+3: period
//!     t+4: identifier("resize")  t+5: l_paren
//!   Fire at the `equal` token (t+1).

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "resize-result-discarded";

/// Returns `SourceTooWide` if the source or token count exceeds the AST position domain.
pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .resize_result_discarded)) return;
    _ = cache;

    if (tree.source.len >= std.math.maxInt(u32)) return error.SourceTooWide;
    const tok_count = std.math.cast(u32, tree.tokens.len) orelse return error.SourceTooWide;
    const tags = tree.tokens.items(.tag);
    const last_tok: Ast.TokenIndex = tok_count -| 1;

    var t: Ast.TokenIndex = 0;
    while (t < last_tok and last_tok - t >= 5) : (t += 1) {
        // Pattern: `_ = identifier.resize(`
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "_")) continue;
        if (tags[t + 1] != .equal) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 4), "resize")) continue;
        if (tags[t + 5] != .l_paren) continue;

        try report(gpa, problems, tree, t + 1, tree.tokenSlice(t + 2));
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    eq_tok: Ast.TokenIndex,
    recv: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`_ = {s}.resize(…)` discards the return value — `Allocator.resize` returns `false` when in-place growth fails; ignoring it means the slice may still be at the old length and any write beyond the old end is out-of-bounds; use `{s}.realloc(…)` (which always succeeds or errors) or check the bool: `if (!{s}.resize(…)) {{ buf = try {s}.realloc(…); }}`",
        .{ recv, recv, recv, recv },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, eq_tok),
        .end = try Pos.fromTokenEnd(tree, eq_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "resize-result-discarded: basic discard fires" {
    try testing.expectFires(check, R,
        \\fn grow(gpa: std.mem.Allocator, buf: *[]u8, new_len: usize) void {
        \\    _ = gpa.resize(buf.*, new_len);
        \\}
        \\
    );
}

test "resize-result-discarded: captured bool does not fire" {
    try testing.expectNoFire(check,
        \\fn tryGrow(gpa: std.mem.Allocator, buf: *[]u8, new_len: usize) !void {
        \\    if (!gpa.resize(buf.*, new_len)) {
        \\        buf.* = try gpa.realloc(buf.*, new_len);
        \\    }
        \\}
        \\
    );
}

test "resize-result-discarded: realloc does not fire" {
    try testing.expectNoFire(check,
        \\fn grow(gpa: std.mem.Allocator, buf: *[]u8, new_len: usize) !void {
        \\    buf.* = try gpa.realloc(buf.*, new_len);
        \\}
        \\
    );
}

test "resize-result-discarded: different method name does not fire" {
    // `resizeContext` is not `resize` — rule matches exact method name only.
    try testing.expectNoFire(check,
        \\fn grow(alloc: Allocator, buf: *[]u8, n: usize, ctx: anytype) void {
        \\    _ = alloc.resizeContext(buf.*, n, ctx);
        \\}
        \\
    );
}

test "resize-result-discarded: captured result does not fire" {
    // Assigning to a named variable (not `_`) does not trigger the rule.
    try testing.expectNoFire(check,
        \\fn grow(gpa: std.mem.Allocator, buf: *[]u8, new_len: usize) !void {
        \\    const ok = gpa.resize(buf.*, new_len);
        \\    if (!ok) buf.* = try gpa.realloc(buf.*, new_len);
        \\}
        \\
    );
}

test "resize-result-discarded: two discarded resizes both fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\fn growBoth(a: std.mem.Allocator, x: *[]u8, y: *[]u8, n: usize) void {
        \\    _ = a.resize(x.*, n);
        \\    _ = a.resize(y.*, n);
        \\}
        \\
    );
    defer testing.freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 2), problems.items.len);
}
