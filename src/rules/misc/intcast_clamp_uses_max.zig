//! Detects `@intCast(@max(expr, std.math.maxInt(T)))` (or with operands
//! swapped) — using `@max` to clamp a value before narrowing it.
//!
//! The intent is to cap the value at `maxInt(T)` before calling `@intCast`.
//! But `@max(x, maxInt(T))` returns the *larger* operand: it returns
//! `maxInt(T)` when `x <= maxInt(T)`, and returns `x` when `x > maxInt(T)`.
//! In the overflow case, `@intCast(x)` then panics in debug builds or wraps
//! silently in release builds — exactly the scenario the clamp was meant to
//! prevent.
//!
//! The correct builtin is `@min`, not `@max`:
//!   `@intCast(@min(expr, std.math.maxInt(T)))`
//! `@min(x, 255)` returns 255 when `x > 255`, safely capping the value.
//!
//! Real-world shape: oven-sh/bun#29813
//!   `@intCast(@max(queueSize, std.math.maxInt(u8)))` — intended to cap the
//!   queue size at 255 but panics on any `queueSize > 255`.
//!
//! Detection (Tier 1, token walk):
//!   4-token prefix:
//!     t+0: builtin("@intCast")   t+1: l_paren
//!     t+2: builtin("@max")       t+3: l_paren
//!   Then scan the @max argument list (depth-tracked) for the 5-token
//!   sub-pattern: identifier("std") period identifier("math") period
//!   identifier("maxInt").
//!   Fire at the `@intCast` token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "intcast-clamp-uses-max";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .intcast_clamp_uses_max)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 3 <= last_tok) : (t += 1) {
        // Prefix: @intCast ( @max (
        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@intCast")) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "@max")) continue;
        if (tags[t + 3] != .l_paren) continue;

        // Scan inside @max's argument list for `std.math.maxInt`.
        const open = t + 3;
        if (!containsMaxInt(tree, tags, open, last_tok)) continue;

        try report(gpa, problems, tree, t);
    }
}

/// Returns true iff `std.math.maxInt` appears inside the @max argument list
/// starting at `open_paren`, depth-tracked to stay within that call.
fn containsMaxInt(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    open_paren: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    var depth: u32 = 1;
    var u: Ast.TokenIndex = open_paren + 1;
    while (u + 4 <= last and depth > 0) : (u += 1) {
        switch (tags[u]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => {
                depth -= 1;
                if (depth == 0) break;
            },
            .identifier => {
                if (depth == 1 and
                    std.mem.eql(u8, tree.tokenSlice(u), "std") and
                    u + 4 <= last and
                    tags[u + 1] == .period and
                    tags[u + 2] == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(u + 2), "math") and
                    tags[u + 3] == .period and
                    tags[u + 4] == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(u + 4), "maxInt"))
                {
                    return true;
                }
            },
            else => {},
        }
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    intcast_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`@intCast(@max(…, std.math.maxInt(T)))` uses `@max` to clamp before narrowing, but `@max` returns the *larger* operand — when the input exceeds `maxInt(T)`, it is passed through unchanged and `@intCast` panics (debug) or wraps (release); use `@min` instead: `@intCast(@min(…, std.math.maxInt(T)))`",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, intcast_tok),
        .end = Pos.fromTokenEnd(tree, intcast_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "intcast-clamp-uses-max: basic fires" {
    try testing.expectFires(check, R,
        \\fn clamp(n: usize) u8 {
        \\    return @intCast(@max(n, std.math.maxInt(u8)));
        \\}
        \\
    );
}

test "intcast-clamp-uses-max: min does not fire" {
    try testing.expectNoFire(check,
        \\fn clamp(n: usize) u8 {
        \\    return @intCast(@min(n, std.math.maxInt(u8)));
        \\}
        \\
    );
}

test "intcast-clamp-uses-max: intCast without max does not fire" {
    try testing.expectNoFire(check,
        \\fn cast(n: usize) u8 {
        \\    return @intCast(n);
        \\}
        \\
    );
}

test "intcast-clamp-uses-max: max without maxInt does not fire" {
    try testing.expectNoFire(check,
        \\fn clamp(n: usize) usize {
        \\    return @intCast(@max(n, 255));
        \\}
        \\
    );
}
