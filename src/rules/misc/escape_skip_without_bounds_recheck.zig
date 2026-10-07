//! Detects the escape-skip + unconditional-increment double-advance bug:
//!
//!   while (i < buf.len) {
//!       if (buf[i] == '\\') {
//!           i += 1;          // skip escaped char — may push i to buf.len
//!       }
//!       i += 1;              // unconditional bump — OOB read on next iteration
//!   }
//!
//! If the if condition checks `buf[i] == ESCAPE_CHAR` without a preceding
//! bounds guard (`i + 1 < buf.len`), the escape-skip can advance `i` to
//! exactly `buf.len`.  The subsequent unconditional `i += 1` (or the next
//! loop iteration's `buf[i]` read) runs past the end.
//!
//! Fix: add `i + 1 < buf.len and` before the array access in the if
//! condition, or `break` / `continue` after the inner increment.
//!
//! Real-world shape: oven-sh/bun#31435 (fmt.zig JS syntax highlighter).
//!
//! Detection (Tier 1, per-fn body token walk):
//!   1. Scan for `keyword_if l_paren CONDITION r_paren l_brace BODY r_brace`.
//!   2. CONDITION must contain `l_bracket identifier(IDX) r_bracket` (array
//!      subscript) AND `equal_equal char_literal` (equality with a char).
//!   3. BODY must be exactly `identifier(IDX) plus_equal number_literal semicolon`
//!      (a single increment of the index variable).
//!   4. Immediately after the `r_brace`, the next tokens must be
//!      `identifier(IDX) plus_equal` (same IDX, unconditional increment).
//!   5. No `keyword_else` immediately after the `r_brace` (if-else pattern
//!      has different semantics).
//!   6. Suppression: if CONDITION contains `identifier(IDX) plus` or
//!      `identifier(IDX) angle_bracket_left` before the `l_bracket`, the
//!      caller already guards the index — do not fire.
//!   7. Fire at the outer unconditional `identifier(IDX)` token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const matchBrace = tokens.matchBrace;
const matchParen = tokens.matchParen;
const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "escape-skip-without-bounds-recheck";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .escape_skip_without_bounds_recheck)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
}

/// Info extracted from an if condition that looks like an escape check.
const EscapeInfo = struct {
    /// Index variable name (e.g., "i").
    name: []const u8,
    /// Token position of the `l_bracket` in `buf[IDX]`.
    bracket_tok: Ast.TokenIndex,
};

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        // Skip nested fn bodies.
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Pattern: `keyword_if l_paren`.
        if (tags[t] != .keyword_if) continue;
        if (t + 1 > last or tags[t + 1] != .l_paren) continue;

        // Find matching r_paren for the if condition.
        const rparen = matchParen(tags, t + 1, last) orelse continue;

        // Condition is [t+2, rparen-1] inclusive.
        if (rparen < t + 2) continue; // empty condition
        const cond_start = t + 2;
        const cond_end = rparen -| 1;
        if (cond_start > cond_end) continue;

        // Condition must contain `l_bracket identifier(IDX) r_bracket` AND
        // `equal_equal char_literal`.
        const ei = findEscapeCheck(tree, tags, cond_start, cond_end) orelse continue;

        // After r_paren there must be `l_brace`.
        if (rparen + 1 > last or tags[rparen + 1] != .l_brace) continue;
        const lbrace = rparen + 1;

        // Find matching r_brace.
        const rbrace = matchBrace(tags, lbrace, last) orelse continue;

        // No `else` after r_brace (if-else has different semantics).
        if (rbrace + 1 <= last and tags[rbrace + 1] == .keyword_else) continue;

        // If body [lbrace+1, rbrace-1] must be exactly:
        // identifier(IDX) plus_equal number_literal semicolon
        if (rbrace == 0 or lbrace + 1 > rbrace - 1) continue; // empty body
        const body_start = lbrace + 1;
        const body_end = rbrace - 1;
        if (!isSimpleIncrement(tree, tags, body_start, body_end, ei.name)) continue;

        // After r_brace, check for unconditional `identifier(IDX) plus_equal`.
        if (rbrace + 2 > last) continue;
        if (tags[rbrace + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(rbrace + 1), ei.name)) continue;
        if (tags[rbrace + 2] != .plus_equal) continue;

        // Suppression: condition already contains a bounds check for IDX
        // (e.g., `IDX + 1 < len` or `IDX < len`) before the array subscript.
        if (condHasBoundsCheck(tree, tags, cond_start, ei.bracket_tok, ei.name)) continue;

        // Fire at the outer unconditional increment.
        try report(gpa, problems, tree, rbrace + 1, ei.name);

        // Skip past the fired region to avoid duplicate reports.
        t = rbrace + 1;
    }
}

/// In the token range `[start, end]` (inclusive), find:
///   `l_bracket identifier(IDX) r_bracket` AND `equal_equal char_literal`
///   (or `char_literal equal_equal`).
/// Returns info about the index variable and bracket position, or null.
fn findEscapeCheck(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) ?EscapeInfo {
    if (start > end) return null;

    // Find `l_bracket identifier r_bracket` in the condition.
    var bracket_tok: ?Ast.TokenIndex = null;
    var idx_name: ?[]const u8 = null;
    {
        var t: Ast.TokenIndex = start;
        while (t + 2 <= end) : (t += 1) {
            if (tags[t] == .l_bracket and
                tags[t + 1] == .identifier and
                tags[t + 2] == .r_bracket)
            {
                bracket_tok = t;
                idx_name = tree.tokenSlice(t + 1);
                break;
            }
        }
    }
    const bt = bracket_tok orelse return null;
    const name = idx_name orelse return null;

    // Find `equal_equal char_literal` (or reversed) in the condition.
    var has_char_check = false;
    {
        var t: Ast.TokenIndex = start;
        while (t + 1 <= end) : (t += 1) {
            if ((tags[t] == .equal_equal and tags[t + 1] == .char_literal) or
                (tags[t] == .char_literal and tags[t + 1] == .equal_equal))
            {
                has_char_check = true;
                break;
            }
        }
    }
    if (!has_char_check) return null;

    return .{ .name = name, .bracket_tok = bt };
}

/// Returns true iff the token range `[start, end]` (inclusive) is exactly:
///   `identifier(name) plus_equal number_literal semicolon`
fn isSimpleIncrement(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) bool {
    if (end != start + 3) return false;
    if (tags[start] != .identifier) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(start), name)) return false;
    if (tags[start + 1] != .plus_equal) return false;
    if (tags[start + 2] != .number_literal) return false;
    if (tags[start + 3] != .semicolon) return false;
    return true;
}

/// Returns true iff the range `[cond_start, bracket_tok - 1]` contains a
/// bounds check for `name`: `identifier(name) plus` or
/// `identifier(name) angle_bracket_left` (i.e., `name + N` or `name <`).
fn condHasBoundsCheck(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    cond_start: Ast.TokenIndex,
    bracket_tok: Ast.TokenIndex,
    name: []const u8,
) bool {
    if (cond_start >= bracket_tok) return false;
    var t: Ast.TokenIndex = cond_start;
    while (t + 1 < bracket_tok) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        // `name + ...` — typical in `name + 1 < len`
        if (tags[t + 1] == .plus) return true;
        // `name < ...` — typical in `name < len`
        if (tags[t + 1] == .angle_bracket_left) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    tok: Ast.TokenIndex,
    idx_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "unconditional `{s} += 1` after escape-skip `if (buf[{s}] == '\\\\') {{ {s} += 1; }}` — if the escape character is the last byte, the skip advances `{s}` to `buf.len`; the next `+= 1` reads past the end; add `{s} + 1 < buf.len and` before the array access in the if condition",
        .{ idx_name, idx_name, idx_name, idx_name, idx_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, tok),
        .end = try Pos.fromTokenEnd(tree, tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "escape-skip-without-bounds-recheck: basic backslash escape pattern fires" {
    try testing.expectFires(check, R,
        \\fn scan(buf: []const u8) void {
        \\    var i: usize = 0;
        \\    while (i < buf.len) {
        \\        if (buf[i] == '\\') {
        \\            i += 1;
        \\        }
        \\        i += 1;
        \\    }
        \\}
        \\
    );
}

test "escape-skip-without-bounds-recheck: slash escape pattern fires" {
    try testing.expectFires(check, R,
        \\fn scan(buf: []const u8) void {
        \\    var i: usize = 0;
        \\    while (i < buf.len) {
        \\        if (buf[i] == '/') {
        \\            i += 1;
        \\        }
        \\        i += 1;
        \\    }
        \\}
        \\
    );
}

test "escape-skip-without-bounds-recheck: bounds check before array access suppresses" {
    try testing.expectNoFire(check,
        \\fn scan(buf: []const u8) void {
        \\    var i: usize = 0;
        \\    while (i < buf.len) {
        \\        if (i + 1 < buf.len and buf[i] == '\\') {
        \\            i += 1;
        \\        }
        \\        i += 1;
        \\    }
        \\}
        \\
    );
}

test "escape-skip-without-bounds-recheck: if-else does not fire" {
    try testing.expectNoFire(check,
        \\fn scan(buf: []const u8) void {
        \\    var i: usize = 0;
        \\    while (i < buf.len) {
        \\        if (buf[i] == '\\') {
        \\            i += 1;
        \\        } else {
        \\            doSomething(buf[i]);
        \\        }
        \\        i += 1;
        \\    }
        \\}
        \\
    );
}

test "escape-skip-without-bounds-recheck: no outer increment does not fire" {
    try testing.expectNoFire(check,
        \\fn scan(buf: []const u8) void {
        \\    var i: usize = 0;
        \\    while (i < buf.len) : (i += 1) {
        \\        if (buf[i] == '\\') {
        \\            i += 1;
        \\        }
        \\        doSomething();
        \\    }
        \\}
        \\
    );
}

test "escape-skip-without-bounds-recheck: multi-statement if body does not fire" {
    try testing.expectNoFire(check,
        \\fn scan(buf: []const u8) void {
        \\    var i: usize = 0;
        \\    while (i < buf.len) {
        \\        if (buf[i] == '\\') {
        \\            i += 1;
        \\            doSomethingElse();
        \\        }
        \\        i += 1;
        \\    }
        \\}
        \\
    );
}

test "escape-skip-without-bounds-recheck: non-subscript condition does not fire" {
    try testing.expectNoFire(check,
        \\fn scan(c: u8) void {
        \\    var i: usize = 0;
        \\    while (i < 10) {
        \\        if (c == '\\') {
        \\            i += 1;
        \\        }
        \\        i += 1;
        \\    }
        \\}
        \\
    );
}
