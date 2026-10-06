//! Detects `?*?T` — a doubly-optional pointer.  Almost always a
//! copy-paste error: the author wrote one `?` and meant either a nullable
//! pointer (`?*T`, for a nullable out-parameter) or a pointer to an
//! optional (`*?T`, for a non-null container whose value may be absent),
//! not both.
//!
//! Why it matters: the shape has two independent reasons to be null, and
//! every dereference has to answer both.  A call site that unwraps once
//! still holds a value the type says may be null, so a second unwrap is
//! required — and a single `orelse` that handled the "absent" case leaves
//! the "absent pointer" case live.  That is a null dereference at the next
//! use.
//!
//! Detection (Tier 1, flat token walk over parameter type expressions):
//!   Pattern: `question_mark asterisk question_mark <identifier>`
//!   Fire at the parameter's type expression.
//!   `?*T` and `*?T` do not fire — only the nesting of both.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "double-optional-ptr";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .double_optional_ptr)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkBody);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    _ = cache;
    _ = body;
    const tags = tree.tokens.items(.tag);

    var it = proto.iterate(tree);
    while (it.next()) |param| {
        const type_expr = param.type_expr orelse continue;
        const first = tree.firstToken(type_expr);
        const last = tree.lastToken(type_expr);
        if (first + 3 > last) continue;
        if (!isDoubleOptionalPointer(tags, first, last)) continue;
        try report(gpa, problems, tree, first, last);
    }
}

/// True iff the span `[first, last]` spells `?*?T` — the optional marker,
/// the pointer marker, the optional marker again, then the pointee type.
fn isDoubleOptionalPointer(tags: []const tokens.TokenTag, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    var k = first;
    var question_marks: usize = 0;
    var stars: usize = 0;
    while (k <= last) : (k += 1) {
        switch (tags[k]) {
            .question_mark => question_marks += 1,
            .asterisk => stars += 1,
            else => {},
        }
    }
    return question_marks >= 2 and stars >= 1;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`?*?T` — doubly-optional pointer, almost always a copy-paste error; for a nullable out-param use `?*T`, for a non-null pointer to an optional use `*?T`",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, first),
        .end = Pos.fromTokenEnd(tree, last),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "double-optional-ptr: ?*?T parameter fires" {
    try testing.expectFires(check, R,
        \\fn writeOut(out: ?*?u32) void {
        \\    if (out) |p| {
        \\        p.?.* = 1;
        \\    }
        \\}
        \\
    );
}

test "double-optional-ptr: nullable out-param ?*T does not fire" {
    try testing.expectNoFire(check,
        \\fn writeOut(out: ?*u32) void {
        \\    if (out) |p| {
        \\        p.* = 1;
        \\    }
        \\}
        \\
    );
}

test "double-optional-ptr: pointer to optional *?T does not fire" {
    try testing.expectNoFire(check,
        \\fn lookup(entry: *?u32) u32 {
        \\    return entry.? orelse 0;
        \\}
        \\
    );
}

test "double-optional-ptr: plain pointer does not fire" {
    try testing.expectNoFire(check,
        \\fn writeOut(out: *u32) void {
        \\    out.* = 1;
        \\}
        \\
    );
}

test "double-optional-ptr: optional value alone does not fire" {
    try testing.expectNoFire(check,
        \\fn maybe() ?u32 {
        \\    return null;
        \\}
        \\
    );
}
