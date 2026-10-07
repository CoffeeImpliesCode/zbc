//! Detects a position/cursor field being assigned a value deserialized from
//! untrusted data (e.g. a file stream) without a preceding bounds check.
//!
//! Pattern:
//!   const end_pos = try reader.readInt(u64, .little);
//!   stream.pos = end_pos;         // ← BUG: end_pos may exceed stream.buffer.len
//!   _ = stream.buffer[start..end_pos]; // downstream OOB
//!
//! Real-world shape: oven-sh/bun#12105 (lockfile.zig Buffers.readArray):
//! both `start_pos` and `end_pos` were read from untrusted lockfile data
//! and used to set `stream.pos` and slice `stream.buffer` without any
//! validation that they are within bounds.
//!
//! Detection (Tier 3 — LocalBindings + FnSummary):
//!   1. For each fn body, build LocalBindings and find bindings whose RHS
//!      is a method call to any of the "readInt"-family names (readInt,
//!      readIntLittle, readIntBig, readU64, readU32, readU16, readU8,
//!      readByte, read_int, read_u32, read_u64).
//!   2. For each such binding NAME, scan forward in the fn body for
//!      `identifier PERIOD identifier(POS_FIELD) EQUAL identifier(NAME)`,
//!      where POS_FIELD ∈ {pos, position, offset, cursor, index, idx}.
//!   3. Suppression: if `keyword_if l_paren ... identifier(NAME)` appears
//!      between the binding end and the assignment, a bounds check is
//!      present — do not fire.
//!   4. Fire at the assignment's `EQUAL` token.

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
const R = "readint-unchecked-position-assignment";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .readint_unchecked_position_assignment)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const bindings = try cache.localBindings(proto, body);
    const tags = tree.tokens.items(.tag);
    const last = tree.lastToken(body);

    // Collect bindings that originate from readInt-like method calls.
    const DeserPos = struct {
        name: []const u8,
        after_rhs: Ast.TokenIndex,
    };
    var deser: std.ArrayListUnmanaged(DeserPos) = .empty;
    defer deser.deinit(gpa);

    for (bindings.items) |b| {
        if (b.origin == .param) continue;
        const ca = b.asCall() orelse continue;
        const method = ca.method orelse continue;
        if (!isReadIntName(method)) continue;
        try deser.append(gpa, .{
            .name = b.name,
            .after_rhs = b.rhs_last + 1,
        });
    }

    if (deser.items.len == 0) return;

    for (deser.items) |dp| {
        const scan_start = dp.after_rhs;
        if (scan_start > last) continue;

        // Find unchecked assignment: `RECV . POS_FIELD = dp.name`
        const assign_eq_tok = findPositionAssignment(tree, tags, scan_start, last, dp.name) orelse continue;

        // Suppress if there's a `keyword_if` containing `dp.name` before this.
        if (hasBoundsCheckBefore(tree, tags, scan_start, assign_eq_tok, dp.name)) continue;

        try report(gpa, problems, tree, assign_eq_tok, dp.name);
    }
}

/// True iff `name` is a readInt-family method name.
fn isReadIntName(name: []const u8) bool {
    return std.mem.eql(u8, name, "readInt") or
        std.mem.eql(u8, name, "readIntLittle") or
        std.mem.eql(u8, name, "readIntBig") or
        std.mem.eql(u8, name, "readIntNative") or
        std.mem.eql(u8, name, "readU64") or
        std.mem.eql(u8, name, "readU32") or
        std.mem.eql(u8, name, "readU16") or
        std.mem.eql(u8, name, "readU8") or
        std.mem.eql(u8, name, "readByte") or
        std.mem.eql(u8, name, "read_int") or
        std.mem.eql(u8, name, "read_u64") or
        std.mem.eql(u8, name, "read_u32") or
        std.mem.eql(u8, name, "read_u16");
}

/// Position-field names that, if assigned an unchecked deserialized value,
/// could cause an out-of-bounds access when the cursor is used later.
fn isPositionFieldName(name: []const u8) bool {
    return std.mem.eql(u8, name, "pos") or
        std.mem.eql(u8, name, "position") or
        std.mem.eql(u8, name, "offset") or
        std.mem.eql(u8, name, "cursor") or
        std.mem.eql(u8, name, "index") or
        std.mem.eql(u8, name, "idx") or
        std.mem.eql(u8, name, "start") or
        std.mem.eql(u8, name, "end");
}

/// Scan `[start, last]` for the pattern:
///   `identifier PERIOD identifier(POS_FIELD) EQUAL identifier(pos_name) SEMICOLON`
/// Returns the token index of the `EQUAL` token, or null.
fn findPositionAssignment(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    pos_name: []const u8,
) ?Ast.TokenIndex {
    if (start + 3 > last) return null;
    var t: Ast.TokenIndex = start;
    while (t + 3 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Pattern: `identifier.POS_FIELD = pos_name`
        //   t+0: identifier (receiver, e.g. "stream")
        //   t+1: period
        //   t+2: identifier (field, e.g. "pos")
        //   t+3: equal
        //   t+4: identifier (the pos_name)
        if (tags[t] != .identifier) continue;
        if (t + 4 > last) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .equal) continue;
        if (tags[t + 4] != .identifier) continue;

        const field_name = tree.tokenSlice(t + 2);
        if (!isPositionFieldName(field_name)) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 4), pos_name)) continue;

        return t + 3; // the `=` token
    }
    return null;
}

/// Returns true iff a `keyword_if` containing `identifier(pos_name)` appears
/// in the range `[start, end_exclusive)`.  This indicates a bounds check.
fn hasBoundsCheckBefore(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end_exclusive: Ast.TokenIndex,
    pos_name: []const u8,
) bool {
    if (start >= end_exclusive) return false;
    var in_if_cond: bool = false;
    var t: Ast.TokenIndex = start;
    while (t < end_exclusive) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, end_exclusive -| 1);
            continue;
        }
        if (tags[t] == .keyword_if) {
            in_if_cond = true;
            continue;
        }
        if (in_if_cond) {
            if (tags[t] == .l_brace) {
                in_if_cond = false;
                continue;
            }
            if (tags[t] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(t), pos_name))
                return true;
        }
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    eq_tok: Ast.TokenIndex,
    pos_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` was read from the stream without a bounds check; assigning it to a position/cursor field before validating `{s} <= stream.buffer.len` allows an out-of-bounds access when the buffer is subsequently indexed; add `if ({s} > stream.buffer.len) return error.CorruptData;` before this assignment",
        .{ pos_name, pos_name, pos_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, eq_tok),
        .end = try Pos.fromTokenEnd(tree, eq_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "readint-unchecked-position-assignment: basic pattern fires" {
    try testing.expectFires(check, R,
        \\const S = struct {
        \\    pub fn readArray(stream: *Stream, reader: anytype) !void {
        \\        const end_pos = try reader.readInt(u64, .little);
        \\        stream.pos = end_pos;
        \\    }
        \\};
        \\
    );
}

test "readint-unchecked-position-assignment: bounds check before assignment suppresses" {
    try testing.expectNoFire(check,
        \\const S = struct {
        \\    pub fn readArray(stream: *Stream, reader: anytype) !void {
        \\        const end_pos = try reader.readInt(u64, .little);
        \\        if (end_pos > stream.buffer.len) return error.CorruptData;
        \\        stream.pos = end_pos;
        \\    }
        \\};
        \\
    );
}

test "readint-unchecked-position-assignment: readU32 method name fires" {
    try testing.expectFires(check, R,
        \\const S = struct {
        \\    pub fn parse(cur: *Cursor, r: anytype) !void {
        \\        const off = try r.readU32();
        \\        cur.offset = off;
        \\    }
        \\};
        \\
    );
}

test "readint-unchecked-position-assignment: non-readInt call does not fire" {
    try testing.expectNoFire(check,
        \\const S = struct {
        \\    pub fn parse(cur: *Cursor, r: anytype) !void {
        \\        const pos = try r.computeOffset();
        \\        cur.pos = pos;
        \\    }
        \\};
        \\
    );
}
