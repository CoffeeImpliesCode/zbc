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
//! Detection (Tier 1, AST structure):
//!   An addition directly owns an unparenthesized `if` as its right operand.
//!   The parsed else branch starts with `0 +` or `1 +`.
//!   Explicitly grouped conditionals and branch sums are not candidates.
//!   Standalone conditional branch arithmetic is also not a candidate.

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
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .add) continue;
        const addition: Ast.Node.Index = @enumFromInt(index);
        const conditional = tree.nodeData(addition).node_and_node[1];
        // Do not peel parentheses here. They explicitly make the conditional
        // one addend rather than an ungrouped continuation of the outer sum.
        const branch = tree.fullIf(conditional) orelse continue;
        if (branch.error_token != null) continue;
        const otherwise = branch.ast.else_expr.unwrap() orelse continue;
        if (tree.nodeTag(otherwise) != .add) continue;
        const first = tree.firstToken(otherwise);
        if (first != branch.else_token + 1 or tags[first] != .number_literal) continue;
        const lit = tree.tokenSlice(first);
        if (!std.mem.eql(u8, lit, "0") and !std.mem.eql(u8, lit, "1")) continue;
        // Check the start of this parsed branch, not any neighboring branch.
        // Explicit branch grouping and wrapping/saturating addition stay quiet.
        if (tags[first + 1] != .plus) continue;
        try report(gpa, problems, tree, branch.else_token, lit);
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
        .start = try Pos.fromTokenStart(tree, else_tok),
        .end = try Pos.fromTokenEnd(tree, else_tok + 2),
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

test "else-literal-absorbs-addend: grouped conditional suffix branch does not fire" {
    try testing.expectNoFire(check,
        \\fn length(root: []const u8, suffix: []const u8) usize {
        \\    return root.len + (if (suffix.len == 0) 0 else 1 + suffix.len);
        \\}
    );
}

test "else-literal-absorbs-addend: standalone nullable branch arithmetic does not fire" {
    try testing.expectNoFire(check,
        \\fn value(zero: bool, random: anytype) u32 {
        \\    const result: u32 = if (zero) 0 else 1 + random.range(u32, 0, 8);
        \\    return result;
        \\}
    );
}

test "else-literal-absorbs-addend: standalone multi line branch arithmetic does not fire" {
    try testing.expectNoFire(check,
        \\fn count(nominal: bool, random: anytype) usize {
        \\    return if (nominal)
        \\        random.range(u8, 0, 9)
        \\    else
        \\        1 + random.range(u8, 0, 8);
        \\}
    );
}

test "else-literal-absorbs-addend: explicitly grouped else sum does not fire" {
    try testing.expectNoFire(check,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    return base + if (cond) 1 else (0 + extra);
        \\}
    );
}

test "else-literal-absorbs-addend: multiply grouped conditional does not fire" {
    try testing.expectNoFire(check,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    return base + ((if (cond) 1 else 0 + extra));
        \\}
    );
}

test "else-literal-absorbs-addend: outer grouping does not hide trap" {
    try testing.expectFires(check, R,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    return (base + if (cond) 1 else 0 + extra);
        \\}
    );
}

test "else-literal-absorbs-addend: nested true branch trap fires" {
    try testing.expectFires(check, R,
        \\fn capacity(base: usize, outer: bool, cond: bool, extra: usize) usize {
        \\    return if (outer) base + if (cond) 1 else 0 + extra else 0;
        \\}
    );
}

test "else-literal-absorbs-addend: nested intentional conditional branch does not fire" {
    try testing.expectNoFire(check,
        \\fn capacity(base: usize, outer: bool, cond: bool, extra: usize) usize {
        \\    return base + (if (outer) 0 else if (cond) 1 else 0 + extra);
        \\}
    );
}

test "else-literal-absorbs-addend: separate preceding addition does not fire" {
    try testing.expectNoFire(check,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    const sum = base + extra;
        \\    return if (cond) sum else 0 + extra;
        \\}
    );
}

test "else-literal-absorbs-addend: wrapping and saturating branches do not fire" {
    try testing.expectNoFire(check,
        \\fn capacity(base: usize, cond: bool, extra: usize) usize {
        \\    const wrapped = base + if (cond) 1 else 0 +% extra;
        \\    return wrapped + if (cond) 1 else 0 +| extra;
        \\}
    );
}
