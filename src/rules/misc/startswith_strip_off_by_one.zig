//! Detects `startsWith(SLICE, "LITERAL")` followed by `SLICE[N..]` where
//! `N == "LITERAL".len - 1` — an off-by-one when stripping the prefix leaves
//! one character behind.
//!
//! Real-world instance:
//!   - oven-sh/bun#27970 (node_fs_watcher, node_fs_stat_watcher):
//!     `if (startsWith(slice, "file://")) { slice = slice[6..]; }`
//!     — "file://" is 7 chars; `slice[6..]` retains the leading '/'.
//!     Fix: `slice["file://".len..]` (= `slice[7..]`).
//!
//! Detection (Tier 1, flat token walk):
//!   Scan for `startsWith ( identifier , string_literal` (5-token prefix, Form A)
//!   OR `startsWith ( identifier , identifier , string_literal` (6-token prefix, Form B
//!   — the std.mem.startsWith(u8, slice, "literal") shape).
//!   Record the SLICE identifier and compute literal length.
//!   In the next 40 tokens, search for `SLICE [ integer_literal ..` where
//!   integer_literal == literal_len - 1.  Fire at the `[` token.
//!
//!   Skips string literals that contain backslash escape sequences (length
//!   calculation would be incorrect for those).
//!
//!   Suppression:
//!   - `or startsWith(…)`: when `startsWith` is immediately preceded by `or`,
//!     the strip body is shared across multiple branch conditions and may
//!     intentionally not strip the full last prefix.  Suppress.
//!   - Same-slice re-appearance: the scan stops when another
//!     `startsWith(_, SLICE, _)` appears for the same SLICE — indicates a
//!     different loop or condition branch whose strip is unrelated.
//!   - Open-ended slices only: `SLICE[N..]` fires; bounded `SLICE[N..end]`
//!     is suppressed (typically a trailing-character removal, not prefix strip).

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "startswith-strip-off-by-one";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .startswith_strip_off_by_one)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 8) return;
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 5 <= last_tok) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "startsWith")) continue;
        // Skip when this startsWith is the tail of an `or`-chained condition:
        //   `or startsWith(…)`          → or at t-1
        //   `or X.startsWith(…)`        → or at t-3
        //   `or std.mem.startsWith(…)`  → or at t-5
        // Scan backward up to 5 tokens; stop early on a statement boundary.
        {
            var or_before = false;
            var k: Ast.TokenIndex = 1;
            while (k <= 5 and k <= t) : (k += 1) {
                const prev = tags[t - k];
                if (prev == .keyword_or) {
                    or_before = true;
                    break;
                }
                if (prev == .l_paren or prev == .semicolon or
                    prev == .l_brace or prev == .r_brace) break;
            }
            if (or_before) continue;
        }
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .identifier) continue;

        // Form A: startsWith ( SLICE , "literal"
        //   t+2=SLICE, t+3=comma, t+4=string_literal
        // Form B: startsWith ( TYPE , SLICE , "literal"
        //   t+2=TYPE, t+3=comma, t+4=SLICE, t+5=comma, t+6=string_literal
        var slice_tok: Ast.TokenIndex = undefined;
        var lit_tok: Ast.TokenIndex = undefined;

        if (tags[t + 3] == .comma and
            tags[t + 4] == .string_literal)
        {
            // Form A
            slice_tok = t + 2;
            lit_tok = t + 4;
        } else if (t + 6 <= last_tok and
            tags[t + 3] == .comma and
            tags[t + 4] == .identifier and
            tags[t + 5] == .comma and
            tags[t + 6] == .string_literal)
        {
            // Form B
            slice_tok = t + 4;
            lit_tok = t + 6;
        } else {
            continue;
        }

        const slice_name = tree.tokenSlice(slice_tok);
        const lit_slice = tree.tokenSlice(lit_tok);

        // Skip string literals with escape sequences (length calc would be wrong)
        if (std.mem.indexOfScalar(u8, lit_slice, '\\') != null) continue;
        // lit_slice is like "file://" (with surrounding quotes)
        if (lit_slice.len < 2) continue;
        const lit_len: usize = lit_slice.len - 2; // subtract opening and closing quote
        if (lit_len == 0) continue;
        const off_by_one: usize = lit_len - 1;

        // Scan the next 40 tokens for: SLICE [ N-1 ..
        const scan_end = @min(lit_tok + 40, last_tok);
        var j = lit_tok + 1;
        while (j + 2 <= scan_end) : (j += 1) {
            // Stop when another startsWith(_, SLICE, _) appears in the same window.
            // That signals a different condition branch (e.g. an `or`-chained check
            // or a second loop) so the strip below belongs to a different context.
            if (tags[j] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(j), "startsWith") and
                j + 4 <= scan_end)
            {
                // Form A: startsWith( SLICE, ... )
                const same_a = tags[j + 2] == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(j + 2), slice_name);
                // Form B: startsWith( TYPE, SLICE, ... )
                const same_b = tags[j + 4] == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(j + 4), slice_name);
                if (same_a or same_b) break;
            }
            if (tags[j] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(j), slice_name)) continue;
            if (tags[j + 1] != .l_bracket) continue;
            if (tags[j + 2] != .number_literal) continue;
            if (j + 3 > last_tok) continue;
            if (tags[j + 3] != .ellipsis2) continue;
            // Require open-ended `SLICE[N..]`, not a bounded `SLICE[N..end]`.
            // Bounded slices (e.g. removing a trailing character) are unrelated
            // to prefix-stripping and produce false positives.
            if (j + 4 > scan_end or tags[j + 4] != .r_bracket) continue;

            // Check that the integer equals lit_len - 1
            const num_str = tree.tokenSlice(j + 2);
            const num = std.fmt.parseInt(usize, num_str, 10) catch continue;
            if (num != off_by_one) continue;

            try report(gpa, problems, tree, j + 1, slice_name, lit_slice, lit_len);
            break; // one report per startsWith
        }
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    bracket_tok: Ast.TokenIndex,
    slice_name: []const u8,
    literal: []const u8,
    literal_len: usize,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}[{d}..]` strips one fewer character than {s} (length {d}); use `{s}[{d}..]` or `{s}[{s}.len..]` to strip the full prefix",
        .{ slice_name, literal_len - 1, literal, literal_len, slice_name, literal_len, slice_name, literal },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, bracket_tok),
        .end = Pos.fromTokenEnd(tree, bracket_tok + 2),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "startswith-strip-off-by-one: fires on bun-style (form A)" {
    try testing.expectFires(check, R,
        \\fn stripFilePrefix(path: []const u8) []const u8 {
        \\    if (strings.startsWith(path, "file://")) {
        \\        return path[6..];
        \\    }
        \\    return path;
        \\}
        \\
    );
}

test "startswith-strip-off-by-one: fires on std-style (form B, u8 type arg)" {
    try testing.expectFires(check, R,
        \\fn stripPrefix(s: []const u8) []const u8 {
        \\    if (std.mem.startsWith(u8, s, "https://")) {
        \\        return s[7..];
        \\    }
        \\    return s;
        \\}
        \\
    );
}

test "startswith-strip-off-by-one: correct length does not fire" {
    try testing.expectNoFire(check,
        \\fn stripPrefix(path: []const u8) []const u8 {
        \\    if (strings.startsWith(path, "file://")) {
        \\        return path[7..];
        \\    }
        \\    return path;
        \\}
        \\
    );
}

test "startswith-strip-off-by-one: using .len form does not fire" {
    try testing.expectNoFire(check,
        \\fn stripPrefix(path: []const u8) []const u8 {
        \\    if (strings.startsWith(path, "file://")) {
        \\        return path["file://".len..];
        \\    }
        \\    return path;
        \\}
        \\
    );
}

test "startswith-strip-off-by-one: different variable does not fire" {
    try testing.expectNoFire(check,
        \\fn process(path: []const u8, other: []const u8) []const u8 {
        \\    if (strings.startsWith(path, "file://")) {
        \\        return other[6..];
        \\    }
        \\    return path;
        \\}
        \\
    );
}

test "startswith-strip-off-by-one: second startsWith for same var stops scan" {
    try testing.expectNoFire(check,
        \\fn stripPrefixes(result: []const u8) []const u8 {
        \\    var r = result;
        \\    while (r.len >= 3 and std.mem.startsWith(u8, r, "../")) {
        \\        r = r[3..];
        \\    }
        \\    while (r.len >= 2 and std.mem.startsWith(u8, r, "./")) {
        \\        r = r[2..];
        \\    }
        \\    return r;
        \\}
        \\
    );
}

test "startswith-strip-off-by-one: or-chained tail does not fire" {
    try testing.expectNoFire(check,
        \\fn serialize(unit: []const u8, writer: anytype) !void {
        \\    if (std.mem.startsWith(u8, unit, "e-") or std.mem.startsWith(u8, unit, "E-")) {
        \\        try writer.writeAll("\\65 ");
        \\        try writer.writeAll(unit[1..]);
        \\    }
        \\}
        \\
    );
}

test "startswith-strip-off-by-one: bounded slice does not fire" {
    try testing.expectNoFire(check,
        \\fn stripTrailingComma(s: []const u8) []const u8 {
        \\    var r = s;
        \\    if (std.mem.startsWith(u8, r, "-") and r[r.len - 1] == ',') {
        \\        r = r[0 .. r.len - 1];
        \\    }
        \\    return r;
        \\}
        \\
    );
}
