//! Detects `self.field = @as(T, @intCast(self.field))` and similar self-
//! assign-through-cast patterns — the assignment is a no-op because the
//! same field is read, cast, and written back unchanged.  This is almost
//! always a copy-paste error where the programmer intended to use a
//! freshly-computed local variable on the RHS but accidentally kept the
//! field reference.
//!
//! Real-world instance:
//!   - oven-sh/bun#25905 (BufferReadStream.seek): `this.pos = @as(usize, @intCast(this.pos))`
//!     was written instead of `this.pos = @as(usize, @intCast(new_pos))`.
//!     The seek operation silently became a no-op — the read cursor never
//!     advanced, causing every seek to leave the stream at the same position.
//!
//! Detection (Tier 1, flat token walk):
//!   Form A: `ident.ident = @as(type, @intCast(ident.ident))`        — 15 tokens
//!   Form B: `ident.ident = @intCast(ident.ident)`                    — 10 tokens
//!   Form C: `ident.ident = @as(type, ident.ident)`                   — 12 tokens
//!   Fire when the LHS `receiver.field` matches the innermost RHS `receiver.field`.
//!   Fire at the LHS identifier token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "field-self-assign-with-cast";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .field_self_assign_with_cast)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 9 <= last_tok) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .equal) continue;

        // Form A: ident.ident = @as(ident, @intCast(ident.ident))
        // t+4..t+14
        if (t + 14 <= last_tok and
            tags[t + 4] == .builtin and std.mem.eql(u8, tree.tokenSlice(t + 4), "@as") and
            tags[t + 5] == .l_paren and
            tags[t + 6] == .identifier and
            tags[t + 7] == .comma and
            tags[t + 8] == .builtin and std.mem.eql(u8, tree.tokenSlice(t + 8), "@intCast") and
            tags[t + 9] == .l_paren and
            tags[t + 10] == .identifier and
            tags[t + 11] == .period and
            tags[t + 12] == .identifier and
            tags[t + 13] == .r_paren and
            tags[t + 14] == .r_paren and
            std.mem.eql(u8, tree.tokenSlice(t), tree.tokenSlice(t + 10)) and
            std.mem.eql(u8, tree.tokenSlice(t + 2), tree.tokenSlice(t + 12)))
        {
            try report(gpa, problems, tree, t, t + 14);
            continue;
        }

        // Form B: ident.ident = @intCast(ident.ident)
        // t+4..t+9
        if (tags[t + 4] == .builtin and std.mem.eql(u8, tree.tokenSlice(t + 4), "@intCast") and
            tags[t + 5] == .l_paren and
            tags[t + 6] == .identifier and
            tags[t + 7] == .period and
            tags[t + 8] == .identifier and
            tags[t + 9] == .r_paren and
            std.mem.eql(u8, tree.tokenSlice(t), tree.tokenSlice(t + 6)) and
            std.mem.eql(u8, tree.tokenSlice(t + 2), tree.tokenSlice(t + 8)))
        {
            try report(gpa, problems, tree, t, t + 9);
            continue;
        }

        // Form C: ident.ident = @as(ident, ident.ident)
        // t+4..t+11
        if (t + 11 <= last_tok and
            tags[t + 4] == .builtin and std.mem.eql(u8, tree.tokenSlice(t + 4), "@as") and
            tags[t + 5] == .l_paren and
            tags[t + 6] == .identifier and
            tags[t + 7] == .comma and
            tags[t + 8] == .identifier and
            tags[t + 9] == .period and
            tags[t + 10] == .identifier and
            tags[t + 11] == .r_paren and
            std.mem.eql(u8, tree.tokenSlice(t), tree.tokenSlice(t + 8)) and
            std.mem.eql(u8, tree.tokenSlice(t + 2), tree.tokenSlice(t + 10)))
        {
            try report(gpa, problems, tree, t, t + 11);
            continue;
        }
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    start_tok: Ast.TokenIndex,
    end_tok: Ast.TokenIndex,
) !void {
    const recv = tree.tokenSlice(start_tok);
    const field = tree.tokenSlice(start_tok + 2);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s} = @…cast({s}.{s})` — field assigned to itself through a cast; this is a no-op and is almost always a copy-paste error where a freshly-computed local variable was intended on the RHS",
        .{ recv, field, recv, field },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, start_tok),
        .end = try Pos.fromTokenEnd(tree, end_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "field-self-assign-with-cast: form A fires" {
    try testing.expectFires(check, R,
        \\fn seek(this: *Stream, offset: i64) void {
        \\    const new_pos: i64 = this.pos + offset;
        \\    this.pos = @as(usize, @intCast(this.pos));
        \\    _ = new_pos;
        \\}
        \\
    );
}

test "field-self-assign-with-cast: form B fires" {
    try testing.expectFires(check, R,
        \\fn fixup(self: *Encoder) void {
        \\    self.offset = @intCast(self.offset);
        \\}
        \\
    );
}

test "field-self-assign-with-cast: form C fires" {
    try testing.expectFires(check, R,
        \\fn coerce(s: *State) void {
        \\    s.len = @as(u32, s.len);
        \\}
        \\
    );
}

test "field-self-assign-with-cast: different variable on RHS does not fire" {
    try testing.expectNoFire(check,
        \\fn seek(this: *Stream, offset: i64) void {
        \\    const new_pos: i64 = this.pos + offset;
        \\    this.pos = @as(usize, @intCast(new_pos));
        \\}
        \\
    );
}

test "field-self-assign-with-cast: different field on RHS does not fire" {
    try testing.expectNoFire(check,
        \\fn advance(this: *Stream) void {
        \\    this.pos = @intCast(this.end);
        \\}
        \\
    );
}

test "field-self-assign-with-cast: different receiver does not fire" {
    try testing.expectNoFire(check,
        \\fn copy(dst: *Stream, src: *Stream) void {
        \\    dst.pos = @intCast(src.pos);
        \\}
        \\
    );
}
