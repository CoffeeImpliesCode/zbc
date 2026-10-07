//! Detects the pattern `(-value << N)` where `value` is a signed integer
//! variable and there is no preceding `minInt` guard.
//!
//! In two's complement, `std.math.minInt(i32)` (and similar) has no
//! positive representation: `-minInt` overflows, producing `minInt` again.
//! Left-shifting the result then produces wrong output or a signed-integer
//! overflow (undefined behaviour in ReleaseFast / C-undefined semantics).
//! Zig's safety-checked modes trap on the overflow at runtime, but
//! ReleaseFast silently wraps.
//!
//! The canonical fix for VLQ / zigzag / sign-bit encoding is:
//!   return if (value >= 0)
//!       @as(u32, @bitCast(value)) << 1
//!   else
//!       (@as(u32, @bitCast(-value - 1)) << 1) | 1;
//!
//! Real-world shape: oven-sh/bun#10782 (sourcemap.zig encodeVLQ: when
//! `value == std.math.minInt(i32)`, `-value` overflowed back to
//! `minInt(i32)`, and the subsequent `<< 1` produced garbage).
//!
//! Detection (Tier 1, per-fn body token walk):
//!   1. Scan for `minus identifier(X) angle_bracket_angle_bracket_left`
//!      (i.e., `-X <<`), which is the minimal signature of a negate-then-
//!      shift expression.
//!   2. To reduce false positives: require that the minus is either
//!      preceded by `l_paren` (the common `(-x << N)` form) OR immediately
//!      follows `keyword_else` or `equal` (assignment / ternary arm).
//!   3. Suppression: if `minInt` appears anywhere in the fn body as an
//!      identifier, the programmer has considered the minInt edge case.
//!   4. Fire at the `minus` token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const skipNestedFn = tokens.skipNestedFn;
const hasIdentInRange = tokens.hasIdentInRange;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "negate-then-shift-without-minint-check";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .negate_then_shift_without_minint_check)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
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

    // Early exit: suppression — if `minInt` appears anywhere in the fn body,
    // the programmer has already accounted for the signed minimum.
    if (hasIdentInRange(tree, first, last, "minInt")) return;

    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        // Skip nested fn bodies.
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Pattern: `minus identifier angle_bracket_angle_bracket_left`
        //   (i.e., `-X <<`)
        if (tags[t] != .minus) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .angle_bracket_angle_bracket_left) continue;

        // Require a contextual anchor so we don't fire on binary `a - b << c`:
        // The minus must follow `l_paren`, `equal`, `keyword_else`,
        // `keyword_return`, `comma`, or be at the start of the fn body.
        if (!isUnaryContext(tags, t, first)) continue;

        const ident = tree.tokenSlice(t + 1);
        try report(gpa, problems, tree, t, ident);
    }
}

/// Returns true iff the token at position `t` is in a unary-minus context:
/// preceded by `l_paren`, `equal`, `keyword_else`, `keyword_return`,
/// `comma`, `plus_plus`, or at the start of the fn body.
fn isUnaryContext(
    tags: []const std.zig.Token.Tag,
    t: Ast.TokenIndex,
    first: Ast.TokenIndex,
) bool {
    if (t == first) return true;
    return switch (tags[t - 1]) { // zbc-disable-line: index-minus-one-without-zero-guard — t==first returns early above; t>first>=1 in fall-through
        .l_paren,
        .equal,
        .keyword_else,
        .keyword_return,
        .comma,
        .l_bracket,
        .semicolon,
        .l_brace,
        .colon,
        // Catch `((-x << N))` — nested parens.
        .minus,
        => true,
        else => false,
    };
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    minus_tok: Ast.TokenIndex,
    ident: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`-{s} <<` negates then left-shifts a signed integer — when `{s} == std.math.minInt(@TypeOf({s}))`, negation overflows (wraps in ReleaseFast); add a `std.math.minInt` guard or use `@bitCast` / `@as(u32, @intCast({s}))` to avoid the signed overflow",
        .{ ident, ident, ident, ident },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, minus_tok),
        .end = try Pos.fromTokenEnd(tree, minus_tok + 1),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "negate-then-shift-without-minint-check: basic pattern fires" {
    try testing.expectFires(check, R,
        \\fn encodeVlq(value: i32) u32 {
        \\    return if (value >= 0) @intCast(value << 1) else @intCast((-value << 1) | 1);
        \\}
        \\
    );
}

test "negate-then-shift-without-minint-check: assignment context fires" {
    try testing.expectFires(check, R,
        \\fn zigzag(n: i64) u64 {
        \\    const result = -n << 1;
        \\    return @intCast(result);
        \\}
        \\
    );
}

test "negate-then-shift-without-minint-check: minInt guard suppresses" {
    try testing.expectNoFire(check,
        \\fn encodeVlq(value: i32) u32 {
        \\    if (value == std.math.minInt(i32)) @panic("overflow");
        \\    return if (value >= 0) @intCast(value << 1) else @intCast((-value << 1) | 1);
        \\}
        \\
    );
}

test "negate-then-shift-without-minint-check: binary subtraction does not fire" {
    try testing.expectNoFire(check,
        \\fn f(a: i32, b: i32) i32 {
        \\    return a - b << 1;
        \\}
        \\
    );
}

test "negate-then-shift-without-minint-check: no shift after negate does not fire" {
    try testing.expectNoFire(check,
        \\fn f(value: i32) i32 {
        \\    return -value;
        \\}
        \\
    );
}
