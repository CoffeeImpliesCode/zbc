//! Detects a bounds check of the form `data.len < (a + b)` (or variants
//! with `<=`, `>`, `>=`) where the sum `(a + b)` may be computed in a
//! narrower integer type than `usize`, wrap to a small value, and bypass
//! the guard entirely.
//!
//! In Zig, integer arithmetic is typed: if `a` and `b` are `u32`, the
//! addition `a + b` is performed in `u32`.  When `a + b > 0xFFFF_FFFF`
//! it wraps to a small number.  The comparison `data.len < (wrapped_small)`
//! then evaluates `false` even though the intended slice would be huge —
//! the guard is bypassed and the downstream slice triggers OOB or discloses
//! memory.
//!
//! Canonical fix: subtract instead of add to keep everything in `usize`:
//!   if (data.len - a < b) return error.TruncatedInput;
//!   const msg = data[a..][0..b];
//!
//! Real-world shape: oven-sh/bun#30157 (IPC message decoder):
//!   if (data.len < (header_length + message_len)) { ... }
//! where both were `u32`; `message_len = 0xFFFFFFFB` wrapped the sum to 0,
//! bypassing the check and allowing a ~4 GiB slice to be returned.
//!
//! Detection (Tier 1, token walk):
//!   Two 9-token patterns:
//!   Form A: `identifier . len COMP l_paren identifier plus identifier r_paren`
//!   Form B: `l_paren identifier plus identifier r_paren COMP identifier . len`
//!   where COMP ∈ {`<`, `<=`, `>`, `>=`}.
//!   Fire at the comparison operator token.
//!   Suppression: if `@as` or `@intCast` appears inside the l_paren…r_paren
//!   range (explicit widening cast), suppress.

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
const R = "int-sum-overflow-in-bounds-cmp";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .int_sum_overflow_in_bounds_cmp)) return;
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

    if (first + 8 > last) return;

    var t: Ast.TokenIndex = first;
    while (t + 8 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Form A: identifier.len COMP (a + b)
        if (matchFormA(tree, tags, t)) |comp_tok| {
            try report(gpa, problems, tree, comp_tok);
            continue;
        }

        // Form B: (a + b) COMP identifier.len
        if (matchFormB(tree, tags, t)) |comp_tok| {
            try report(gpa, problems, tree, comp_tok);
        }
    }
}

/// Form A: `identifier . len COMP ( identifier + identifier )`
/// Returns the COMP token index, or null.
fn matchFormA(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    t: Ast.TokenIndex,
) ?Ast.TokenIndex {
    if (tags[t] != .identifier) return null;
    if (tags[t + 1] != .period) return null;
    if (tags[t + 2] != .identifier) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "len")) return null;
    if (!isCompOp(tags[t + 3])) return null;
    if (tags[t + 4] != .l_paren) return null;
    if (tags[t + 5] != .identifier) return null;
    if (tags[t + 6] != .plus) return null;
    if (tags[t + 7] != .identifier) return null;
    if (tags[t + 8] != .r_paren) return null;

    // Suppress if there's an explicit widening cast inside the parens.
    if (hasCastInRange(tree, tags, t + 4, t + 8)) return null;

    return t + 3;
}

/// Form B: `( identifier + identifier ) COMP identifier . len`
/// Returns the COMP token index, or null.
fn matchFormB(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    t: Ast.TokenIndex,
) ?Ast.TokenIndex {
    if (tags[t] != .l_paren) return null;
    if (tags[t + 1] != .identifier) return null;
    if (tags[t + 2] != .plus) return null;
    if (tags[t + 3] != .identifier) return null;
    if (tags[t + 4] != .r_paren) return null;
    if (!isCompOp(tags[t + 5])) return null;
    if (tags[t + 6] != .identifier) return null;
    if (tags[t + 7] != .period) return null;
    if (tags[t + 8] != .identifier) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(t + 8), "len")) return null;

    if (hasCastInRange(tree, tags, t, t + 4)) return null;

    return t + 5;
}

fn isCompOp(tag: std.zig.Token.Tag) bool {
    return tag == .angle_bracket_left or
        tag == .angle_bracket_left_equal or
        tag == .angle_bracket_right or
        tag == .angle_bracket_right_equal;
}

/// True iff any token in [start+1, end) is `@as`, `@intCast`, or `@truncate`
/// — indicating an explicit widening that makes the cast intent clear.
fn hasCastInRange(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    var i: Ast.TokenIndex = start + 1;
    while (i < end) : (i += 1) {
        if (tags[i] != .builtin) continue;
        const s = tree.tokenSlice(i);
        if (std.mem.eql(u8, s, "@as") or
            std.mem.eql(u8, s, "@intCast") or
            std.mem.eql(u8, s, "@truncate")) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    comp_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "bounds check uses `(a + b)` in a comparison against `.len` — if `a` and `b` are typed narrower than `usize` (e.g. `u32`), their sum is computed in the narrower type and may wrap to a small value, bypassing the guard; rewrite as `slice.len - a < b` (subtract, keeping everything in `usize`) or explicitly widen: `@as(usize, a) + @as(usize, b)`",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, comp_tok),
        .end = try Pos.fromTokenEnd(tree, comp_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "int-sum-overflow-in-bounds-cmp: form A fires" {
    try testing.expectFires(check, R,
        \\fn decode(data: []const u8, header_len: u32, msg_len: u32) ![]const u8 {
        \\    if (data.len < (header_len + msg_len)) return error.TruncatedInput;
        \\    return data[header_len..][0..msg_len];
        \\}
        \\
    );
}

test "int-sum-overflow-in-bounds-cmp: form B fires" {
    try testing.expectFires(check, R,
        \\fn decode(data: []const u8, a: u32, b: u32) !void {
        \\    if ((a + b) > data.len) return error.TruncatedInput;
        \\}
        \\
    );
}

test "int-sum-overflow-in-bounds-cmp: @as cast suppresses" {
    try testing.expectNoFire(check,
        \\fn decode(data: []const u8, a: u32, b: u32) !void {
        \\    if (data.len < (@as(usize, a) + b)) return error.TruncatedInput;
        \\}
        \\
    );
}

test "int-sum-overflow-in-bounds-cmp: @intCast suppresses" {
    try testing.expectNoFire(check,
        \\fn decode(data: []const u8, a: u32, b: u32) !void {
        \\    if (data.len < (@intCast(a) + b)) return error.TruncatedInput;
        \\}
        \\
    );
}

test "int-sum-overflow-in-bounds-cmp: single variable does not fire" {
    try testing.expectNoFire(check,
        \\fn decode(data: []const u8, offset: usize) !void {
        \\    if (data.len < offset) return error.TruncatedInput;
        \\}
        \\
    );
}
