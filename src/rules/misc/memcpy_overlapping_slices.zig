//! Detects `@memcpy(base[A..B], base[C..D])` where both arguments derive from
//! the same base identifier — the source and destination may overlap, which
//! causes an "arguments alias" safety panic in Debug/ReleaseSafe and undefined
//! behaviour in ReleaseFast.  Use `std.mem.copyForwards` or
//! `std.mem.copyBackwards` instead, which handle overlapping regions.
//!
//! Real-world instances:
//!   - ziglang/zig#21447 (std.compress.lzma): `@memcpy(input[0..N], input[M..])`
//!     aliased when the decompressed window overlapped the source.
//!   - ziglang/zig#17400 (RingBuffer): similar slice-aliased @memcpy.
//!   - ziglang/zig#19289 (xz block): same pattern.
//!
//! Detection (Tier 1, bracket-balanced token walk):
//!   Pattern: `@memcpy ( BASE_IDENT [ ... ] , BASE_IDENT [ ...`
//!   — find `@memcpy (`, record the first identifier token after `(`, then after
//!   the `[...]` of the first arg skip to `,`, and check if the next identifier
//!   equals the first.  Fire at the `@memcpy` builtin token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "memcpy-overlapping-slices";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .memcpy_overlapping_slices)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 8) return;
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 4 <= last_tok) : (t += 1) {
        // @memcpy (
        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@memcpy")) continue;
        if (tags[t + 1] != .l_paren) continue;

        // First argument base: identifier [
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_bracket) continue;
        const base1 = tree.tokenSlice(t + 2);

        // Skip the first [...] index expression (depth-balanced)
        var i = t + 4;
        var depth: u32 = 1;
        while (i <= last_tok and depth > 0) : (i += 1) {
            switch (tags[i]) {
                .l_bracket => depth += 1,
                .r_bracket => depth -= 1,
                else => {},
            }
        }
        if (depth != 0) continue;
        // i is now one past the closing ']' of the first argument

        // Expect a comma separating the two arguments
        if (i > last_tok) continue;
        if (tags[i] != .comma) continue;

        // Second argument base: identifier [
        const j = i + 1;
        if (j + 1 > last_tok) continue;
        if (tags[j] != .identifier) continue;
        if (tags[j + 1] != .l_bracket) continue;
        const base2 = tree.tokenSlice(j);

        if (!std.mem.eql(u8, base1, base2)) continue;

        try report(gpa, problems, tree, t, base1);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    memcpy_tok: Ast.TokenIndex,
    base: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`@memcpy({s}[...], {s}[...])` — source and destination derive from the same slice and may overlap; `@memcpy` requires non-aliasing arguments and panics in Debug/ReleaseSafe when they overlap; use `std.mem.copyForwards` or `std.mem.copyBackwards` instead",
        .{ base, base },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, memcpy_tok),
        .end = try Pos.fromTokenEnd(tree, memcpy_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "memcpy-overlapping-slices: fires on same base ident" {
    try testing.expectFires(check, R,
        \\fn slide(buf: []u8, n: usize) void {
        \\    @memcpy(buf[0..buf.len - n], buf[n..]);
        \\}
        \\
    );
}

test "memcpy-overlapping-slices: fires on simple indexed form" {
    try testing.expectFires(check, R,
        \\fn compress(input: []u8, offset: usize, count: usize) void {
        \\    @memcpy(input[0..count], input[offset..]);
        \\}
        \\
    );
}

test "memcpy-overlapping-slices: different bases do not fire" {
    try testing.expectNoFire(check,
        \\fn copy(src: []const u8, dst: []u8) void {
        \\    @memcpy(dst[0..src.len], src[0..]);
        \\}
        \\
    );
}

test "memcpy-overlapping-slices: non-slice first arg does not fire" {
    try testing.expectNoFire(check,
        \\fn copy(dst: []u8, src: []const u8) void {
        \\    @memcpy(dst, src);
        \\}
        \\
    );
}

test "memcpy-overlapping-slices: fires with complex index expression" {
    try testing.expectFires(check, R,
        \\fn rotate(data: []u8, k: usize) void {
        \\    @memcpy(data[0 .. data.len - k], data[k .. data.len]);
        \\}
        \\
    );
}
