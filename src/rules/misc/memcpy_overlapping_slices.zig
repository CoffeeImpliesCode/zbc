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
//! Detection: inspect builtin arguments as AST slices with the same identifier.
//! Suppress only when the canonical numeric oracle proves one half-open end
//! is at or below the other start. Both copy directions use that same test.
//! Endpoint calls/blocks and unknown arithmetic retain the diagnostic. Distinct
//! identifiers remain outside this rule's existing alias scope.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");
const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");

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
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const token = tree.nodeMainToken(node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "@memcpy")) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const arguments = tree.builtinCallParams(&buffer, node) orelse continue;
        if (arguments.len != 2) continue;
        const destination = tree.fullSlice(arguments[0]) orelse continue;
        const source = tree.fullSlice(arguments[1]) orelse continue;
        // Keep the existing same-identifier alias scope. Distinct identifiers
        // are not a proof that the underlying storage differs.
        if (tree.nodeTag(destination.ast.sliced) != .identifier or
            tree.nodeTag(source.ast.sliced) != .identifier) continue;
        const base = tree.tokenSlice(tree.nodeMainToken(destination.ast.sliced));
        if (!std.mem.eql(u8, base, tree.tokenSlice(tree.nodeMainToken(source.ast.sliced)))) continue;
        if (tokens.enclosingFnDecl(tree, token)) |declaration| {
            if (tokens.bodyOf(tree, declaration)) |body| {
                if (callFree(tree, arguments[0]) and callFree(tree, arguments[1]) and
                    (try endsBefore(gpa, tree, cache, body, destination, source, token) or
                        try endsBefore(gpa, tree, cache, body, source, destination, token))) continue;
            }
        }
        try report(gpa, problems, tree, token, base);
    }
}

/// Endpoint calls or blocks can change a header between the two arguments.
/// Decline them before comparing offsets into what must be the same header.
/// This is an effect restriction, not a second arithmetic evaluator.
fn callFree(tree: *const Ast, node: Ast.Node.Index) bool {
    const tags = tree.tokens.items(.tag);
    var token = tree.firstToken(node);
    const last = tree.lastToken(node);
    while (token <= last) : (token += 1) {
        switch (tags[token]) {
            .l_paren, .l_brace, .builtin => return false,
            else => {},
        }
    }
    return true;
}

/// Half-open intervals do not overlap when one end equals the other start.
/// Read both endpoints at this call through the canonical numeric oracle:
/// unknown arithmetic and alias writes must not retain an old endpoint.
fn endsBefore(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    body: Ast.Node.Index,
    left: Ast.full.Slice,
    right: Ast.full.Slice,
    token: Ast.TokenIndex,
) !bool {
    const end = left.ast.end.unwrap() orelse return false;
    const finish = try value_range.boundsAt(gpa, tree, body, end, token, cache);
    const begin = try value_range.boundsAt(gpa, tree, body, right.ast.start, token, cache);
    return finish == .integer and begin == .integer and
        finish.integer.min >= 0 and begin.integer.min >= 0 and
        finish.integer.max <= begin.integer.min;
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

test "memcpy-overlapping-slices: adjacent half-open ranges in either direction" {
    try testing.expectNoFireTyped(check,
        \\pub fn copy(bytes: []u8) void {
        \\    @memcpy(bytes[32..64], bytes[0..32]);
        \\    @memcpy(bytes[0..32], bytes[32..64]);
        \\    @memcpy(bytes[0..0], bytes[0..0]);
        \\}
    );
}

test "memcpy-overlapping-slices: one byte overlap remains unsafe" {
    try testing.expectFiresTyped(check, R,
        \\pub fn copy(bytes: []u8) void {
        \\    @memcpy(bytes[31..63], bytes[0..32]);
        \\}
    );
}

test "memcpy-overlapping-slices: canonical endpoint constants" {
    try testing.expectNoFireTyped(check,
        \\const stride = 16 * 2;
        \\pub fn copy(bytes: []u8) void {
        \\    @memcpy(bytes[stride .. stride * 2], bytes[0..stride]);
        \\}
    );
}

test "memcpy-overlapping-slices: mutated endpoint is not an old constant" {
    try testing.expectFiresTyped(check, R,
        \\extern fn change(value: *usize) void;
        \\pub fn copy(bytes: []u8) void {
        \\    var boundary: usize = 32;
        \\    const alias = &boundary;
        \\    change(alias);
        \\    @memcpy(bytes[boundary..64], bytes[0..32]);
        \\}
    );
}

test "memcpy-overlapping-slices: endpoint call cannot change the shared header" {
    try testing.expectFiresTyped(check, R,
        \\fn move(header: *[]u8) usize {
        \\    header.* = header.*[32..];
        \\    return 0;
        \\}
        \\pub fn copy(input: []u8) void {
        \\    var bytes = input;
        \\    @memcpy(bytes[32..64], bytes[move(&bytes)..32]);
        \\}
    );
}

test "memcpy-overlapping-slices: literal adjacency needs no type resolver" {
    try testing.expectNoFire(check,
        \\fn copy(bytes: []u8) void {
        \\    @memcpy(bytes[32..64], bytes[0..32]);
        \\}
    );
}
