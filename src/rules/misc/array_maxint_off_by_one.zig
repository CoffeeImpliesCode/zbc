//! Detects `[std.math.maxInt(T)]SomeType` — an array whose length is
//! `maxInt(T)` instead of `maxInt(T) + 1`, making index `maxInt(T)` an
//! out-of-bounds access when the array is later indexed by a value of type T.
//!
//! `std.math.maxInt(u8)` = 255, so `[255]u8` only covers indices 0..254.
//! A `u8` value of 255 then reads one past the end of the array.
//! In debug builds this panics; in ReleaseFast it silently reads from the
//! adjacent `.rodata` or stack frame.
//!
//! The correct declaration is `[std.math.maxInt(T) + 1]SomeType` or,
//! equivalently, the concrete count `256` for T=u8.
//!
//! Real-world shapes:
//!   oven-sh/bun#29976 — `hex_table: [255]u8` indexed by decoded hex byte
//!     (byte 0xFF caused panic / OOB read in `.rodata`)
//!   oven-sh/bun#29973 — `sort_table: [std.math.maxInt(u8)]u8` indexed by
//!     filename bytes (byte 0xFF caused panic / OOB read)
//!
//! Detection (Tier 1, token walk):
//!   10-token pattern:
//!     t+0: l_bracket   t+1: identifier("std")   t+2: period
//!     t+3: identifier("math")   t+4: period
//!     t+5: identifier("maxInt")   t+6: l_paren   t+7: identifier(T)
//!     t+8: r_paren   t+9: r_bracket
//!   The r_bracket at t+9 is the suppression: if the length is
//!   `maxInt(T) + 1` or any other expression, t+9 will not be r_bracket
//!   and the rule does not fire.
//!   Fire at the `l_bracket` token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "array-maxint-off-by-one";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .array_maxint_off_by_one)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 9 <= last_tok) : (t += 1) {
        // Pattern: [ std . math . maxInt ( T ) ]
        if (tags[t] != .l_bracket) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "std")) continue;
        if (tags[t + 2] != .period) continue;
        if (tags[t + 3] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 3), "math")) continue;
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 5), "maxInt")) continue;
        if (tags[t + 6] != .l_paren) continue;
        if (tags[t + 7] != .identifier) continue;
        if (tags[t + 8] != .r_paren) continue;
        // t+9 must be r_bracket immediately (no `+ 1` or other modifier)
        if (tags[t + 9] != .r_bracket) continue;

        const type_name = tree.tokenSlice(t + 7);
        try report(gpa, problems, tree, t, type_name);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    bracket_tok: Ast.TokenIndex,
    type_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`[std.math.maxInt({s})]` declares an array with `maxInt({s})` slots, leaving index `maxInt({s})` out of bounds — any {s} value equal to `maxInt({s})` is an OOB access (panic in debug, silent read in release); use `[std.math.maxInt({s}) + 1]` so all {s} values are valid indices",
        .{ type_name, type_name, type_name, type_name, type_name, type_name, type_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, bracket_tok),
        .end = try Pos.fromTokenEnd(tree, bracket_tok + 9),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "array-maxint-off-by-one: u8 fires" {
    try testing.expectFires(check, R,
        \\const hex_table: [std.math.maxInt(u8)]u8 = undefined;
        \\
    );
}

test "array-maxint-off-by-one: u16 fires" {
    try testing.expectFires(check, R,
        \\const sort_table: [std.math.maxInt(u16)]u8 = undefined;
        \\
    );
}

test "array-maxint-off-by-one: plus-one does not fire" {
    try testing.expectNoFire(check,
        \\const hex_table: [std.math.maxInt(u8) + 1]u8 = undefined;
        \\
    );
}

test "array-maxint-off-by-one: non-maxInt does not fire" {
    try testing.expectNoFire(check,
        \\const table: [256]u8 = undefined;
        \\
    );
}
