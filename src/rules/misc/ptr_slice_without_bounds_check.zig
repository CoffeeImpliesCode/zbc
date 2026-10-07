//! Detects `slice.ptr[0..N]` for small fixed N (2, 3, 4) — accessing a
//! raw pointer window into a slice without the slice's built-in bounds
//! checking.
//!
//! Zig slices carry a length and enforce bounds at runtime.  Writing
//! `slice.ptr[0..N]` strips the length field from the access: if `slice`
//! has fewer than N bytes, this reads beyond the allocation.  In Debug /
//! ReleaseSafe mode the many-pointer arithmetic is unchecked; in ReleaseFast
//! the OOB read is silent memory disclosure or garbage.
//!
//! The pattern is commonly used to feed a fixed-size window to a multi-byte
//! decoder (e.g., UTF-8 decode reads up to 4 bytes) while avoiding a
//! "slice operand of runtime size" issue, but it forgets that the caller
//! may provide a buffer shorter than the window.
//!
//! Real-world shape: oven-sh/bun#29999 (strings/CodepointIterator.next:
//! `self.bytes.ptr[0..4]` without checking `self.bytes.len >= 4`).
//!
//! Detection (Tier 1, token walk):
//!   Scan for the 7-token pattern:
//!     t+0: `.period`
//!     t+1: `identifier("ptr")`
//!     t+2: `l_bracket`
//!     t+3: `integer_literal("0")`
//!     t+4: `ellipsis2` (..)
//!     t+5: `integer_literal` (value 2, 3, or 4)
//!     t+6: `r_bracket`
//!   Fire at the `l_bracket` token (t+2).
//!   Suppression: skip if `integer_literal` or `identifier` immediately
//!   before t+1 is already a `@sizeOf` or similar expression — those are
//!   explicitly sized and deliberate.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");
const testing = @import("../../testing.zig");

const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "ptr-slice-without-bounds-check";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .ptr_slice_without_bounds_check)) return;
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

    if (first + 6 > last) return;

    var t: Ast.TokenIndex = first;
    while (t + 6 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Pattern: .ptr[0..N] for N in {2, 3, 4}
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "ptr")) continue;
        if (tags[t + 2] != .l_bracket) continue;
        if (tags[t + 3] != .number_literal) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 3), "0")) continue;
        if (tags[t + 4] != .ellipsis2) continue;
        if (tags[t + 5] != .number_literal) continue;
        if (tags[t + 6] != .r_bracket) continue;

        const n_str = tree.tokenSlice(t + 5);
        const n = std.fmt.parseInt(u32, n_str, 10) catch continue;
        if (n < 2 or n > 4) continue;

        // Suppress when the slice is PROVABLY at least N long: a dominating
        // `if (recv.len >= N)` / `if (recv.len < N) return` guard makes the
        // `recv.ptr[0..N]` window in-bounds (value-range, issue #23).  Only
        // when the receiver of `.ptr` is a plain identifier / field path
        // (`buf`, `self.bytes`); call results etc. aren't tracked.
        if (t >= 1 and tags[t - 1] == .identifier) {
            var start = t - 1;
            while (start >= 2 and tags[start - 1] == .period and tags[start - 2] == .identifier) start -= 2;
            const recv = tree.source[tree.tokenStart(start)..(tree.tokenStart(t - 1) + tree.tokenSlice(t - 1).len)];
            if (try value_range.provesMinLen(gpa, tree, body, recv, n, t + 2, null)) continue;
        }

        try report(gpa, problems, tree, t + 2, n);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    lbracket_tok: Ast.TokenIndex,
    n: u32,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`.ptr[0..{d}]` bypasses slice bounds checking — if the slice has fewer than {d} bytes this reads past the allocation (silent OOB in ReleaseFast); add `if (slice.len < {d}) return error.Truncated;` before this access",
        .{ n, n, n },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, lbracket_tok),
        .end = try Pos.fromTokenEnd(tree, lbracket_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "ptr-slice-without-bounds-check: [0..4] fires" {
    try testing.expectFires(check, R,
        \\fn decode(bytes: []const u8) u21 {
        \\    const window = bytes.ptr[0..4];
        \\    _ = window;
        \\    return 0;
        \\}
        \\
    );
}

test "ptr-slice-without-bounds-check: [0..2] fires" {
    try testing.expectFires(check, R,
        \\fn readU16(buf: []const u8) u16 {
        \\    return std.mem.readInt(u16, buf.ptr[0..2], .big);
        \\}
        \\
    );
}

test "ptr-slice-without-bounds-check: [0..3] fires" {
    try testing.expectFires(check, R,
        \\fn decode(buf: []const u8) void {
        \\    const w = buf.ptr[0..3];
        \\    _ = w;
        \\}
        \\
    );
}

test "ptr-slice-without-bounds-check: [0..1] does not fire" {
    try testing.expectNoFire(check,
        \\fn first(buf: []const u8) u8 {
        \\    return buf.ptr[0..1][0];
        \\}
        \\
    );
}

test "ptr-slice-without-bounds-check: [0..5] does not fire" {
    try testing.expectNoFire(check,
        \\fn readFive(buf: []const u8) void {
        \\    _ = buf.ptr[0..5];
        \\}
        \\
    );
}

test "ptr-slice-without-bounds-check: normal slice does not fire" {
    try testing.expectNoFire(check,
        \\fn slice(buf: []const u8) []const u8 {
        \\    return buf[0..4];
        \\}
        \\
    );
}

test "ptr-slice-without-bounds-check: suppressed by `len >= N` guard (#23)" {
    try testing.expectNoFire(check,
        \\fn decode(bytes: []const u8) u8 {
        \\    if (bytes.len >= 4) {
        \\        const window = bytes.ptr[0..4];
        \\        return window[0];
        \\    }
        \\    return 0;
        \\}
        \\
    );
}

test "ptr-slice-without-bounds-check: suppressed by early-return `len < N` guard (#23)" {
    try testing.expectNoFire(check,
        \\fn decode(bytes: []const u8) u8 {
        \\    if (bytes.len < 4) return 0;
        \\    const window = bytes.ptr[0..4];
        \\    return window[0];
        \\}
        \\
    );
}

test "ptr-slice-without-bounds-check: guard for smaller N does NOT suppress larger window (#23)" {
    // `len >= 2` does not justify a `[0..4]` window — must still fire.
    try testing.expectFires(check, R,
        \\fn decode(bytes: []const u8) u8 {
        \\    if (bytes.len >= 2) {
        \\        const window = bytes.ptr[0..4];
        \\        return window[0];
        \\    }
        \\    return 0;
        \\}
        \\
    );
}
