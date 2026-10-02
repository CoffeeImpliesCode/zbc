//! Detects `if (COND) EXPR else 0 + ADDEND` — an operator-precedence trap
//! where the addend after `else 0` is absorbed into the else-branch, silently
//! dropping it from the result when COND is true.
//!
//! In Zig, `if` expressions have LOWER precedence than arithmetic operators.
//! So `if (cond) 1 else 0 + n` parses as:
//!   `if (cond) 1 else (0 + n)`  — NOT  `(if (cond) 1 else 0) + n`
//!
//! When COND is true the result is 1 and `n` is completely dropped.
//! When COND is false the result is `0 + n = n`.
//!
//! This is almost always a capacity-calculation bug: the programmer wanted to
//! add `n` unconditionally and add 1 only when COND is true, but instead they
//! only add `n` when COND is false and drop it when COND is true.
//!
//! The fix is to parenthesize the if-expression or use `@intFromBool`:
//!   (if (cond) 1 else 0) + n
//!   @intFromBool(cond) + n
//!
//! Found by Fuzzilli. Real-world shape: oven-sh/bun#30466 and 20+ duplicate
//! PRs (all crashing `Bun.build` with many conditions because the `if`
//! expression in `ensureTotalCapacity(defaults.len + 2 + if (allow_addons) 1
//! else 0 + conditions.len)` dropped `conditions.len` whenever `allow_addons`
//! was true, causing `putAssumeCapacity` to assert past the reserved slots).
//!
//! Detection (Tier 1, token walk):
//!   3-token pattern:
//!     t+0: keyword_else
//!     t+1: number_literal("0" or "1")
//!     t+2: plus
//!   Fire at t+0.
//!   The naturally suppressed form `(if (cond) x else 0) + n` has `)` at t+2,
//!   not `plus`, so it does not fire.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "else-literal-absorbs-addend";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .else_literal_absorbs_addend)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 2 <= last_tok) : (t += 1) {
        // Pattern: else 0 + ... OR else 1 + ...
        if (tags[t] != .keyword_else) continue;
        if (tags[t + 1] != .number_literal) continue;
        const lit = tree.tokenSlice(t + 1);
        if (!std.mem.eql(u8, lit, "0") and !std.mem.eql(u8, lit, "1")) continue;
        // The `+` must be the regular addition, not `+|` (saturating) or `+%` (wrapping).
        if (tags[t + 2] != .plus) continue;

        try report(gpa, problems, tree, t, lit);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    else_tok: Ast.TokenIndex,
    lit: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`else {s} + <addend>` — Zig's `if` expression has lower precedence than `+`, so this parses as `else ({s} + <addend>)`, absorbing the addend into the else-branch and dropping it when the `if` condition is true; wrap the `if` expression in parentheses `(if (…) … else {s}) + <addend>` or use `@intFromBool(cond) + <addend>`",
        .{ lit, lit, lit },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, else_tok),
        .end = Pos.fromTokenEnd(tree, else_tok + 2),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "else-literal-absorbs-addend: else 0 plus fires" {
    try testing.expectFires(check, R,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    return base + if (cond) 1 else 0 + extra;
        \\}
        \\
    );
}

test "else-literal-absorbs-addend: else 1 plus fires" {
    try testing.expectFires(check, R,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    return base + if (cond) 0 else 1 + extra;
        \\}
        \\
    );
}

test "else-literal-absorbs-addend: parenthesized does not fire" {
    try testing.expectNoFire(check,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    return base + (if (cond) 1 else 0) + extra;
        \\}
        \\
    );
}

test "else-literal-absorbs-addend: intFromBool does not fire" {
    try testing.expectNoFire(check,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    return base + @intFromBool(cond) + extra;
        \\}
        \\
    );
}

test "else-literal-absorbs-addend: else 0 as last term does not fire" {
    try testing.expectNoFire(check,
        \\fn capacity(base: usize, cond: bool) usize {
        \\    return base + if (cond) 1 else 0;
        \\}
        \\
    );
}

test "else-literal-absorbs-addend: else 2 plus does not fire" {
    try testing.expectNoFire(check,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    return base + if (cond) 0 else 2 + extra;
        \\}
        \\
    );
}
