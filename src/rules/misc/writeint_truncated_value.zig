//! Detects `writeInt(NarrowType, @as(NarrowType, @truncate(EXPR)), endian)` —
//! writing a value through `writeInt` where the value argument is an explicit
//! `@as(T, @truncate(...))` coercion.  The `@truncate` silently discards high
//! bits of wider source values; for values that may exceed the narrow type's
//! range (e.g., 64-bit addresses, symbol offsets) this corrupts the serialised
//! output without any error or panic in any build mode.
//!
//! Real-world instance:
//!   - ziglang/zig#22233 (Elf.Atom relocs): `writer.writeInt(i32, @as(i32, @truncate(S + A)), .little)`
//!     where `S + A` is `i64`.  For symbol + addend values above 2 GB the
//!     truncation silently dropped the upper 32 bits, corrupting dynAbs relocs.
//!     Fix: widen the writeInt target to `i64` so no truncation occurs.
//!
//! Detection (Tier 1, flat token walk):
//!   Pattern: `identifier("writeInt") ( identifier , @as ( identifier , @truncate`
//!   — 8 tokens.  Fire at the `writeInt` identifier token.
//!   Also matches the `try writer.writeInt(...)` form since the outer `try` does
//!   not change the token offset.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "writeint-truncated-value";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .writeint_truncated_value)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 8) return;
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 7 <= last_tok) : (t += 1) {
        // Pattern: writeInt ( identifier , @as ( identifier , @truncate
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "writeInt")) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .comma) continue;
        if (tags[t + 4] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 4), "@as")) continue;
        if (tags[t + 5] != .l_paren) continue;
        if (tags[t + 6] != .identifier) continue;
        if (tags[t + 7] != .comma) continue;
        // Check that the next non-comma token is @truncate
        if (t + 8 > last_tok) continue;
        if (tags[t + 8] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 8), "@truncate")) continue;

        const type_name = tree.tokenSlice(t + 2);
        try report(gpa, problems, tree, t, type_name);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    writeint_tok: Ast.TokenIndex,
    type_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`writeInt({s}, @as({s}, @truncate(...)))` — `@truncate` silently discards high bits of the source value for values exceeding the `{s}` range; widen the `writeInt` target type to match the actual value width, or add an explicit bounds check",
        .{ type_name, type_name, type_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, writeint_tok),
        .end = try Pos.fromTokenEnd(tree, writeint_tok + 8),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "writeint-truncated-value: fires on writeInt with @truncate" {
    try testing.expectFires(check, R,
        \\fn writeReloc(writer: anytype, s: i64, a: i64) !void {
        \\    try writer.writeInt(i32, @as(i32, @truncate(s + a)), .little);
        \\}
        \\
    );
}

test "writeint-truncated-value: writeInt without truncate does not fire" {
    try testing.expectNoFire(check,
        \\fn writeReloc(writer: anytype, s: i32) !void {
        \\    try writer.writeInt(i32, s, .little);
        \\}
        \\
    );
}

test "writeint-truncated-value: writeInt with intCast does not fire" {
    try testing.expectNoFire(check,
        \\fn writeReloc(writer: anytype, s: i64) !void {
        \\    try writer.writeInt(i64, s, .little);
        \\}
        \\
    );
}

test "writeint-truncated-value: fires on u16 narrowing" {
    try testing.expectFires(check, R,
        \\fn writeCount(writer: anytype, n: u32) !void {
        \\    try writer.writeInt(u16, @as(u16, @truncate(n)), .big);
        \\}
        \\
    );
}
