//! Detects `.toUTF8(alloc).slice()` written as an inline chain — the
//! `LazyUTF8` temporary created by `toUTF8()` is destroyed at the end of
//! the expression, so `.slice()` returns a `[]const u8` that immediately
//! points into freed memory.
//!
//! Real-world instance:
//!   - oven-sh/bun#29600 (ResolveMessage): `referrer.toUTF8(bun.default_allocator).slice()`
//!     was passed to `ResolveMessage.create()`, which stored the slice in a
//!     heap JS error object.  The temporary buffer was freed at statement end,
//!     leaving the stored `.referrer` field as a dangling pointer.
//!
//! Fix: bind `toUTF8()` to a local and add a `defer`:
//!   const utf8 = referrer.toUTF8(alloc);
//!   defer utf8.deinit(alloc);
//!   use(utf8.slice());
//!
//! Detection (Tier 1, token walk inside fn bodies):
//!   Form A: `toUTF8 ( identifier ) . slice ( )` — 8 tokens
//!   Form B: `toUTF8 ( identifier . identifier ) . slice ( )` — 10 tokens
//!   Fire at the `toUTF8` identifier token.
//!   The safe pattern (`tmp = …toUTF8(…); … tmp.slice()`) has `slice` NOT
//!   immediately after the closing `)` of `toUTF8`, so it does not fire.

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
const R = "toutf8-inline-slice-borrow";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .toutf8_inline_slice_borrow)) return;
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

    if (first + 7 > last) return;

    var t: Ast.TokenIndex = first;
    while (t + 7 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "toUTF8")) continue;
        if (tags[t + 1] != .l_paren) continue;

        // Form A: toUTF8 ( identifier ) . slice ( )
        if (tags[t + 2] == .identifier and
            tags[t + 3] == .r_paren and
            tags[t + 4] == .period and
            tags[t + 5] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 5), "slice") and
            tags[t + 6] == .l_paren and
            tags[t + 7] == .r_paren)
        {
            try report(gpa, problems, tree, t, t + 7);
            continue;
        }

        // Form B: toUTF8 ( identifier . identifier ) . slice ( )
        if (t + 9 <= last and
            tags[t + 2] == .identifier and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier and
            tags[t + 5] == .r_paren and
            tags[t + 6] == .period and
            tags[t + 7] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 7), "slice") and
            tags[t + 8] == .l_paren and
            tags[t + 9] == .r_paren)
        {
            try report(gpa, problems, tree, t, t + 9);
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
    const msg = try std.fmt.allocPrint(
        gpa,
        "`.toUTF8(alloc).slice()` inline chain — the `LazyUTF8` temporary created by `toUTF8()` is freed at statement end, so the returned slice immediately dangles; bind the result: `const utf8 = x.toUTF8(alloc); defer utf8.deinit(alloc); utf8.slice()`",
        .{},
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

test "toutf8-inline-slice-borrow: form A fires" {
    try testing.expectFires(check, R,
        \\fn getName(s: anytype, alloc: std.mem.Allocator) []const u8 {
        \\    return s.toUTF8(alloc).slice();
        \\}
        \\
    );
}

test "toutf8-inline-slice-borrow: form B fires" {
    try testing.expectFires(check, R,
        \\fn getName(s: anytype) []const u8 {
        \\    return s.toUTF8(bun.default_allocator).slice();
        \\}
        \\
    );
}

test "toutf8-inline-slice-borrow: bound temporary does not fire" {
    try testing.expectNoFire(check,
        \\fn getName(s: anytype, alloc: std.mem.Allocator) []const u8 {
        \\    const utf8 = s.toUTF8(alloc);
        \\    defer utf8.deinit(alloc);
        \\    return utf8.slice();
        \\}
        \\
    );
}

test "toutf8-inline-slice-borrow: toUTF8 without slice does not fire" {
    try testing.expectNoFire(check,
        \\fn convert(s: anytype, alloc: std.mem.Allocator) SomeType {
        \\    return s.toUTF8(alloc);
        \\}
        \\
    );
}
