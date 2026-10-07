//! Detects `@max(expr, std.math.maxInt(T))` and `@min(expr, std.math.minInt(T))`
//! — using the wrong clamping direction, which makes the clamp a no-op or
//! causes `@intCast` to panic instead of saturate.
//!
//! `@max(x, std.math.maxInt(T))` ensures the result is AT LEAST maxInt(T),
//! so if x > maxInt(T), the result exceeds T's range and any downstream
//! `@intCast` to T will panic (ReleaseSafe) or overflow (ReleaseFast).  The
//! correct pattern to clamp-then-cast is `@intCast(@min(x, std.math.maxInt(T)))`.
//!
//! `@min(x, std.math.minInt(T))` is the symmetric mistake for signed types:
//! the result is always ≤ minInt(T), so any `@intCast` to T succeeds only for
//! exactly minInt(T) and panics for every larger value.  The correct form is
//! `@intCast(@max(x, std.math.minInt(T)))`.
//!
//! Real-world instance:
//!   - oven-sh/bun#29813 (S3 queueSize): `@intCast(@max(queueSize, std.math.maxInt(u8)))`
//!     forced queueSize to at least 255, causing `@intCast` to panic for any
//!     queueSize in 0..254.  Fix: replace `@max` with `@min`.
//!
//! Detection (Tier 1, paren-balanced token walk):
//!   Form A (second arg):  `@max ( EXPR , std . math . maxInt (`
//!   Form B (first arg):   `@max ( std . math . maxInt (`
//!   Forms C/D: symmetric with `@min` and `minInt`.
//!   Fire at the `@max`/`@min` builtin token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "clamp-wrong-direction";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .clamp_wrong_direction)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 9) return;
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 8 <= last_tok) : (t += 1) {
        if (tags[t] != .builtin) continue;
        const fn_name = tree.tokenSlice(t);
        const is_max = std.mem.eql(u8, fn_name, "@max");
        const is_min = std.mem.eql(u8, fn_name, "@min");
        if (!is_max and !is_min) continue;
        if (tags[t + 1] != .l_paren) continue;

        const int_fn = if (is_max) "maxInt" else "minInt";

        // Form B / D: first arg is std.math.maxInt/minInt
        // @max ( std . math . maxInt (
        //  t  t+1 t+2 t+3 t+4  t+5   t+6  t+7
        if (t + 7 <= last_tok and
            tags[t + 2] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 2), "std") and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 4), "math") and
            tags[t + 5] == .period and
            tags[t + 6] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 6), int_fn) and
            tags[t + 7] == .l_paren)
        {
            try report(gpa, problems, tree, t, is_max);
            continue;
        }

        // Form A / C: second arg is std.math.maxInt/minInt
        // Skip the first argument (paren-balanced) to find the separator comma.
        var i = t + 2;
        var depth: u32 = 1;
        while (i <= last_tok and depth > 0) : (i += 1) {
            switch (tags[i]) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => depth -= 1,
                .comma => if (depth == 1) break,
                else => {},
            }
        }
        // i is at the comma; i+1 starts the second arg
        if (i > last_tok or tags[i] != .comma) continue;
        const j = i + 1;
        if (j + 5 > last_tok) continue;
        if (tags[j] != .identifier or !std.mem.eql(u8, tree.tokenSlice(j), "std")) continue;
        if (tags[j + 1] != .period) continue;
        if (tags[j + 2] != .identifier or !std.mem.eql(u8, tree.tokenSlice(j + 2), "math")) continue;
        if (tags[j + 3] != .period) continue;
        if (tags[j + 4] != .identifier or !std.mem.eql(u8, tree.tokenSlice(j + 4), int_fn)) continue;
        if (tags[j + 5] != .l_paren) continue;

        try report(gpa, problems, tree, t, is_max);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    builtin_tok: Ast.TokenIndex,
    is_max: bool,
) !void {
    const msg = if (is_max)
        try gpa.dupe(
            u8,
            "`@max(expr, std.math.maxInt(T))` ensures the result is AT LEAST maxInt(T), making it larger than T can hold; use `@min(expr, std.math.maxInt(T))` to clamp to T's maximum before `@intCast`",
        )
    else
        try gpa.dupe(
            u8,
            "`@min(expr, std.math.minInt(T))` ensures the result is AT MOST minInt(T), making it the minimum of T; use `@max(expr, std.math.minInt(T))` to clamp to T's minimum before `@intCast`",
        );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, builtin_tok),
        .end = try Pos.fromTokenEnd(tree, builtin_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "clamp-wrong-direction: fires on @max(x, std.math.maxInt(u8))" {
    try testing.expectFires(check, R,
        \\fn clampQueue(queueSize: usize) u8 {
        \\    return @intCast(@max(queueSize, std.math.maxInt(u8)));
        \\}
        \\
    );
}

test "clamp-wrong-direction: fires on @max(std.math.maxInt(u8), x) (first-arg form)" {
    try testing.expectFires(check, R,
        \\fn clampBad(x: usize) u8 {
        \\    return @intCast(@max(std.math.maxInt(u8), x));
        \\}
        \\
    );
}

test "clamp-wrong-direction: fires on @min(x, std.math.minInt(i8))" {
    try testing.expectFires(check, R,
        \\fn clampSigned(x: i32) i8 {
        \\    return @intCast(@min(x, std.math.minInt(i8)));
        \\}
        \\
    );
}

test "clamp-wrong-direction: correct @min(@max clamp does not fire" {
    try testing.expectNoFire(check,
        \\fn clampCorrect(queueSize: usize) u8 {
        \\    return @intCast(@min(queueSize, std.math.maxInt(u8)));
        \\}
        \\
    );
}

test "clamp-wrong-direction: plain @max without maxInt does not fire" {
    try testing.expectNoFire(check,
        \\fn maxOf(a: u32, b: u32) u32 {
        \\    return @max(a, b);
        \\}
        \\
    );
}

test "clamp-wrong-direction: @max with literal zero does not fire" {
    try testing.expectNoFire(check,
        \\fn clampNeg(x: i32) u32 {
        \\    return @intCast(@max(x, 0));
        \\}
        \\
    );
}
