//! Detects `@truncate(expr.len)` — silently truncating a slice length value.
//! In Zig, `.len` on a slice is `usize` (64-bit on 64-bit platforms).
//! `@truncate` discards the upper bits without any overflow check: for user-
//! controlled data (files, network payloads, form fields) a length ≥ the target
//! type's maximum wraps silently, producing a garbage size that corrupts all
//! subsequent length-based reads, copies, and allocations.
//!
//! Real-world instance:
//!   - oven-sh/bun#27443 (multipart form-data): `bun.Semver.String` stored
//!     `length: u32`.  `@as(u32, @truncate(in.len))` truncated multipart body
//!     lengths ≥ 4 GB to a small value, silently dropping bytes when the
//!     subsequent read used the truncated size.
//!     Fix: switched to `[]const u8` (pointer + length) instead of a u32-bounded
//!     type, eliminating the truncation entirely.
//!
//! Detection (Tier 1, flat token walk):
//!   Form A: `@truncate ( identifier . identifier("len") )` — 6 tokens
//!   Form B: `@truncate ( identifier . identifier . identifier("len") )` — 8 tokens
//!   Fire at the `@truncate` builtin token.
//!   `@as(T, @truncate(X.len))` also contains this inner pattern and fires.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "truncate-len-to-narrow-int";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .truncate_len_to_narrow_int)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 5 <= last_tok) : (t += 1) {
        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@truncate")) continue;
        if (tags[t + 1] != .l_paren) continue;

        // Suppress `@as(usize, @truncate(X.len))` / `@as(u64, …)`: narrowing a
        // `usize` length to `usize`/`u64` is an identity conversion on both
        // 32- and 64-bit targets — no upper bits are discarded, so no data is
        // lost.  Shape: `@as ( TYPE , @truncate` → t-4 builtin "@as",
        // t-3 l_paren, t-2 identifier(TYPE), t-1 comma.
        if (t >= 4 and
            tags[t - 1] == .comma and
            tags[t - 2] == .identifier and
            tags[t - 3] == .l_paren and
            tags[t - 4] == .builtin and
            std.mem.eql(u8, tree.tokenSlice(t - 4), "@as"))
        {
            const ty = tree.tokenSlice(t - 2);
            if (std.mem.eql(u8, ty, "usize") or std.mem.eql(u8, ty, "u64")) continue;
        }

        // Form A: @truncate ( identifier . identifier("len") )
        if (tags[t + 2] == .identifier and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 4), "len") and
            tags[t + 5] == .r_paren)
        {
            try report(gpa, problems, tree, t, t + 5);
            continue;
        }

        // Form B: @truncate ( identifier . identifier . identifier("len") )
        if (t + 7 <= last_tok and
            tags[t + 2] == .identifier and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier and
            tags[t + 5] == .period and
            tags[t + 6] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 6), "len") and
            tags[t + 7] == .r_paren)
        {
            try report(gpa, problems, tree, t, t + 7);
            continue;
        }
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    start_tok: Ast.TokenIndex,
    end_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`@truncate(X.len)` — silently discards the upper bits of a slice length; for user-controlled data (files, network payloads) a length ≥ the target type's max wraps to a small value, corrupting all subsequent size-based operations; use a checked conversion or widen the storage type to `usize`",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, start_tok),
        .end = Pos.fromTokenEnd(tree, end_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "truncate-len-to-narrow-int: form A fires" {
    try testing.expectFires(check, R,
        \\fn setLen(s: *Header, buf: []const u8) void {
        \\    s.length = @truncate(buf.len);
        \\}
        \\
    );
}

test "truncate-len-to-narrow-int: form B fires" {
    try testing.expectFires(check, R,
        \\fn setLen(s: *Header, req: Request) void {
        \\    s.length = @truncate(req.body.len);
        \\}
        \\
    );
}

test "truncate-len-to-narrow-int: @as(usize, @truncate(len)) is identity, no fire" {
    try testing.expectNoFire(check,
        \\fn count(buf: []const u8) usize {
        \\    return @as(usize, @truncate(buf.len));
        \\}
        \\
    );
}

test "truncate-len-to-narrow-int: @as(u32, @truncate(len)) still fires" {
    try testing.expectFires(check, R,
        \\fn count(buf: []const u8) u32 {
        \\    return @as(u32, @truncate(buf.len));
        \\}
        \\
    );
}

test "truncate-len-to-narrow-int: truncate of non-len does not fire" {
    try testing.expectNoFire(check,
        \\fn narrow(n: usize) u32 {
        \\    return @truncate(n);
        \\}
        \\
    );
}

test "truncate-len-to-narrow-int: truncate of subtraction does not fire" {
    try testing.expectNoFire(check,
        \\fn narrow(a: usize, b: usize) u32 {
        \\    return @truncate(a - b);
        \\}
        \\
    );
}
