//! Detects `@intCast(std.time.<fn>())` — casting a signed timestamp directly
//! to an unsigned integer without a non-negative guard.
//!
//! `std.time.milliTimestamp()`, `std.time.timestamp()`, and
//! `std.time.nanoTimestamp()` all return `i64`.  On systems with severe clock
//! skew, a VMs clock reset, or a deliberately manipulated clock, the return
//! value can be negative.  `@intCast(negative_i64)` to `usize`/`u64`/`u32`
//! panics in debug/safe builds and wraps to a huge positive value in
//! ReleaseFast — commonly producing a corrupted seed, an invalid timeout, or
//! a 5000-year cache expiry.
//!
//! The safe pattern is to guard before casting:
//!   `@intCast(@max(0, std.time.milliTimestamp()))`
//! or to bind to a local variable first and check before casting.
//!
//! Note: `@intCast(@max(0, std.time.milliTimestamp()))` does NOT fire because
//! the 8-token pattern `@intCast l_paren std period time period <fn> l_paren`
//! only matches when the timestamp call is the DIRECT (unguarded) argument to
//! `@intCast`, not when wrapped in `@max`.
//!
//! Real-world shapes:
//!   oven-sh/bun#10365 — `@as(u64, @intCast(std.time.milliTimestamp()))` used
//!     as a PRNG seed; negative timestamps (from clock resets on CI runners)
//!     panicked or produced bad seeds.
//!
//! Detection (Tier 1, token walk):
//!   8-token pattern:
//!     t+0: builtin("@intCast")   t+1: l_paren
//!     t+2: identifier("std")     t+3: period
//!     t+4: identifier("time")    t+5: period
//!     t+6: identifier(FN)        t+7: l_paren
//!   where FN ∈ {milliTimestamp, timestamp, nanoTimestamp}.
//!   Fire at t+0.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "intcast-signed-timestamp";

const timestamp_fns = [_][]const u8{
    "milliTimestamp",
    "timestamp",
    "nanoTimestamp",
};

fn isTimestampFn(name: []const u8) bool {
    for (timestamp_fns) |fn_name| {
        if (std.mem.eql(u8, name, fn_name)) return true;
    }
    return false;
}

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .intcast_signed_timestamp)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 7 <= last_tok) : (t += 1) {
        // Pattern: @intCast ( std . time . <fn> (
        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@intCast")) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "std")) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 4), "time")) continue;
        if (tags[t + 5] != .period) continue;
        if (tags[t + 6] != .identifier) continue;
        if (!isTimestampFn(tree.tokenSlice(t + 6))) continue;
        if (tags[t + 7] != .l_paren) continue;

        const fn_name = tree.tokenSlice(t + 6);
        try report(gpa, problems, tree, t, fn_name);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    intcast_tok: Ast.TokenIndex,
    fn_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`@intCast(std.time.{s}())` casts a signed `i64` timestamp directly to an unsigned type — a negative value (from clock skew or reset) panics in debug/safe builds and wraps to a huge value in ReleaseFast; use `@intCast(@max(0, std.time.{s}()))` or guard with `if (ts < 0) 0 else @intCast(ts)` first",
        .{ fn_name, fn_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, intcast_tok),
        .end = try Pos.fromTokenEnd(tree, intcast_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "intcast-signed-timestamp: milliTimestamp fires" {
    try testing.expectFires(check, R,
        \\fn seed() u64 {
        \\    return @intCast(std.time.milliTimestamp());
        \\}
        \\
    );
}

test "intcast-signed-timestamp: nanoTimestamp fires" {
    try testing.expectFires(check, R,
        \\fn seed() u64 {
        \\    return @intCast(std.time.nanoTimestamp());
        \\}
        \\
    );
}

test "intcast-signed-timestamp: max-guarded does not fire" {
    try testing.expectNoFire(check,
        \\fn seed() u64 {
        \\    return @intCast(@max(0, std.time.milliTimestamp()));
        \\}
        \\
    );
}

test "intcast-signed-timestamp: local variable does not fire" {
    try testing.expectNoFire(check,
        \\fn seed() u64 {
        \\    const ms = std.time.milliTimestamp();
        \\    return @intCast(@max(0, ms));
        \\}
        \\
    );
}
