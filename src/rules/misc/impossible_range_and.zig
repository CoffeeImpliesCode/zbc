//! Detects `x < A and x > B` — a range validation that uses `and` instead
//! of `or`, making the guard permanently dead.
//!
//! No value can be simultaneously less than A and greater than B (when A ≤ B),
//! so the `if` body is unreachable.  The correct out-of-range check is
//! `x < A or x > B`.  Note: `x > A and x < B` is the valid *in-range* check
//! and is NOT flagged by this rule.
//!
//! Real-world shape: oven-sh/bun#25905 (S3 credentials validation)
//!   Three adjacent copy-paste occurrences in `s3/credentials.zig`:
//!     pageSize < MIN and pageSize > MAX
//!     partSize < MIN and partSize > MAX
//!     retry   < 0   and retry   > 255
//!   All silently never threw the intended RangeError.
//!
//! Detection (Tier 1, token walk):
//!   Anchor on `identifier(X) angle_bracket_left` (t, t+1).
//!   Scan forward up to 20 tokens for `keyword_and`.
//!   After `keyword_and`, check `identifier(X) angle_bracket_right` appears
//!   at positions +1 and +2 relative to `keyword_and`.
//!   Fire at the `identifier(X)` anchor token.
//!
//!   Suppression:
//!   - The reversed form `x > A and x < B` (valid in-range check) is NOT flagged.
//!   - When B is the literal `0`: `x < N and x > 0` is the standard in-range
//!     guard and is suppressed.
//!   - When both A and B are integer literals: fire only when A ≤ B (making the
//!     AND truly impossible).  When A > B (e.g. `x < 76 and x > 65`), the range
//!     (65, 76) is valid and the pattern is suppressed.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "impossible-range-and";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .impossible_range_and)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 3 <= last_tok) : (t += 1) {
        // Anchor: identifier(X) < ...
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .angle_bracket_left) continue;

        const x_name = tree.tokenSlice(t);

        // Scan forward (capped) for `and`.
        const scan_end = @min(last_tok, t + 20);
        var u: Ast.TokenIndex = t + 2;
        while (u + 2 <= scan_end) : (u += 1) {
            if (tags[u] != .keyword_and) continue;
            // After `and`: identifier(X) > ...
            if (tags[u + 1] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(u + 1), x_name)) continue;
            if (tags[u + 2] != .angle_bracket_right) continue;

            // Suppress valid ranges.
            // 1. `x < N and x > 0` — right bound is 0, a common in-range guard.
            // 2. Both bounds are integer literals: fire only when left ≤ right
            //    (impossible range).  When left > right the range is valid.
            if (u + 3 <= last_tok and tags[u + 3] == .number_literal) {
                const right_str = tree.tokenSlice(u + 3);
                if (std.mem.eql(u8, right_str, "0")) break; // valid: x < N and x > 0
                if (tags[t + 2] == .number_literal) {
                    const left_str = tree.tokenSlice(t + 2);
                    const lv = std.fmt.parseUnsigned(u64, left_str, 0) catch null;
                    const rv = std.fmt.parseUnsigned(u64, right_str, 0) catch null;
                    if (lv != null and rv != null and lv.? > rv.?) break; // valid range
                }
            }

            // 3. Valid in-range shapes where the LEFT operand is the UPPER
            //    bound and the RIGHT operand is the LOWER bound — i.e.
            //    `x < UPPER and x > LOWER`.  The impossible-range bug (which
            //    should have used `or`) always has the MIN on the left, so
            //    these are safe to suppress without losing the TP class:
            //      (a) `x < maxInt(..) and x > minInt(..)` — maxInt > minInt
            //          for every integer type, so this is the full-range
            //          membership test (always valid).
            //      (b) `x < something.len and x > LOWER` — a `.len` is the
            //          natural upper bound of an index/slice range; this is a
            //          bounded-range check, not an and/or confusion.
            {
                const left_has_maxint = rangeHasIdent(tree, tags, t + 2, u, "maxInt");
                const right_end = @min(u + 12, last_tok + 1);
                const right_has_minint = rangeHasIdent(tree, tags, u + 3, right_end, "minInt");
                if (left_has_maxint and right_has_minint) break;
                if (leftBoundIsDotLen(tags, tree, t + 2, u)) break;
            }

            try report(gpa, problems, tree, t, x_name);
            break;
        }
    }
}

/// True iff the token range [start, end) contains an identifier whose slice
/// equals `name`.
fn rangeHasIdent(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) bool {
    var i = start;
    while (i < end) : (i += 1) {
        if (tags[i] == .identifier and std.mem.eql(u8, tree.tokenSlice(i), name)) return true;
    }
    return false;
}

/// True iff the left-bound token range [start, end) contains a `. len` field
/// access — i.e. the upper bound is a slice/array length.
fn leftBoundIsDotLen(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    var i = start;
    while (i + 1 < end) : (i += 1) {
        if (tags[i] == .period and
            tags[i + 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(i + 1), "len")) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    anchor_tok: Ast.TokenIndex,
    x_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s} < … and {s} > …` is an impossible range: no value can be simultaneously less than the lower bound and greater than the upper bound — the guard is permanently dead; use `or` instead of `and` for an out-of-range check",
        .{ x_name, x_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, anchor_tok),
        .end = Pos.fromTokenEnd(tree, anchor_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "impossible-range-and: simple literal fires" {
    try testing.expectFires(check, R,
        \\fn validate(retry: i64) bool {
        \\    return retry < 0 and retry > 255;
        \\}
        \\
    );
}

test "impossible-range-and: qualified constant fires" {
    try testing.expectFires(check, R,
        \\fn validate(pageSize: i64) bool {
        \\    return pageSize < Options.MIN and pageSize > Options.MAX;
        \\}
        \\
    );
}

test "impossible-range-and: or form does not fire" {
    try testing.expectNoFire(check,
        \\fn validate(retry: i64) bool {
        \\    return retry < 0 or retry > 255;
        \\}
        \\
    );
}

test "impossible-range-and: valid in-range check does not fire" {
    try testing.expectNoFire(check,
        \\fn inRange(x: i64) bool {
        \\    return x > 0 and x < 100;
        \\}
        \\
    );
}

test "impossible-range-and: different variables do not fire" {
    try testing.expectNoFire(check,
        \\fn check(a: i64, b: i64) bool {
        \\    return a < 0 and b > 255;
        \\}
        \\
    );
}

test "impossible-range-and: literal valid range does not fire (left > right)" {
    try testing.expectNoFire(check,
        \\fn isAsciiUpper(code: u8) bool {
        \\    return code < 76 and code > 65;
        \\}
        \\
    );
}

test "impossible-range-and: right-bound 0 does not fire" {
    try testing.expectNoFire(check,
        \\fn trim(buf: []u8, max: usize) []u8 {
        \\    return if (max < buf.len and max > 0) buf[0..max] else buf;
        \\}
        \\
    );
}

test "impossible-range-and: maxInt/minInt full-range check does not fire" {
    try testing.expectNoFire(check,
        \\fn fits(value: f64) bool {
        \\    return value < std.math.maxInt(i32) and value > std.math.minInt(i32);
        \\}
        \\
    );
}

test "impossible-range-and: dot-len upper bound does not fire" {
    try testing.expectNoFire(check,
        \\fn scan(content: []const u8, end: usize, beg: usize) bool {
        \\    return end < content.len and end > beg;
        \\}
        \\
    );
}

test "impossible-range-and: literal-left + named-max still fires" {
    try testing.expectFires(check, R,
        \\fn validate(id: i64) bool {
        \\    return id < 0 and id > MAX_STREAM_ID;
        \\}
        \\
    );
}
