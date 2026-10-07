//! Detects `@intCast(rc.int())` where `rc` is a libuv return code —
//! `ReturnCode.int()` returns `c_int` (32-bit signed), but libuv's `req.result`
//! is `ssize_t` (64-bit on 64-bit platforms).  When a single I/O call transfers
//! more than `INT_MAX` (~2 GB) bytes the result wraps to a small or negative
//! `c_int`, and `@intCast` to `usize` panics in safe builds.
//!
//! Real-world instance:
//!   - oven-sh/bun#29327 (windows readFile): `@intCast(rc.int())` panicked with
//!     files > 2 GB because `rc.int()` returned the truncated 32-bit value.
//!     Fix: read `req.result` (the untruncated `ssize_t`) instead of `rc.int()`.
//!
//! Detection (Tier 1, token walk inside fn bodies):
//!   Form A: `@intCast ( identifier . int ( ) )` — 8 tokens
//!   Form B: `@intCast ( identifier . identifier . int ( ) )` — 10 tokens
//!   Fire at the `@intCast` builtin token.
//!   Using `@as(i64, rc.int())` does not fire (not `@intCast`).

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
const R = "uv-return-value-intcast-truncation";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .uv_return_value_intcast_truncation)) return;
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
    _ = proto;
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

        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@intCast")) continue;
        if (tags[t + 1] != .l_paren) continue;

        // Form A: @intCast ( identifier . int ( ) )
        if (tags[t + 2] == .identifier and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 4), "int") and
            tags[t + 5] == .l_paren and
            tags[t + 6] == .r_paren and
            tags[t + 7] == .r_paren)
        {
            // SEMANTIC: suppress when `.int()` returns an integer NARROWER than
            // `c_int` (32-bit).  The bug is `c_int` hiding a 64-bit `ssize_t`;
            // a `.int()` returning u4/u8/u16 is a packed-flags accessor (e.g.
            // ghostty `CsiUMods.int()`→u4), not the libuv truncation.  `c_int`
            // is a simple_type → intInfoOfExpr returns null → still fires.
            if (!intReturnNarrowerThanCInt(cache, t + 2, t + 6))
                try report(gpa, problems, tree, t, t + 7);
            continue;
        }

        // Form B: @intCast ( identifier . identifier . int ( ) )
        if (t + 9 <= last and
            tags[t + 2] == .identifier and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier and
            tags[t + 5] == .period and
            tags[t + 6] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 6), "int") and
            tags[t + 7] == .l_paren and
            tags[t + 8] == .r_paren and
            tags[t + 9] == .r_paren)
        {
            if (!intReturnNarrowerThanCInt(cache, t + 2, t + 8))
                try report(gpa, problems, tree, t, t + 9);
            continue;
        }
    }
}

/// True iff the call expression spanning [start, end] (`recv.int()` /
/// `recv.field.int()`) resolves to an integer type narrower than `c_int`
/// (< 32 bits) — i.e. a packed-flags accessor, not libuv's `c_int` return.
/// False when unresolved (`c_int` is a simple_type → null) or ≥32-bit, so the
/// libuv truncation bug keeps firing.  No-op without the type engine.
fn intReturnNarrowerThanCInt(
    cache: *file_cache_mod.FileCache,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    const info = cache.intInfoOfExpr(start, end) orelse return false;
    return info.bits < 32;
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
        "`@intCast(rc.int())` — `.int()` returns `c_int` (32-bit), but the underlying libuv result is `ssize_t` (64-bit); for I/O transfers larger than 2 GB the 32-bit value wraps, and `@intCast` to `usize` panics; use `req.result` (the untruncated `ssize_t`) instead",
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

test "uv-return-value-intcast-truncation: form A fires" {
    try testing.expectFires(check, R,
        \\fn bytesRead(rc: uv.ReturnCode) usize {
        \\    return @intCast(rc.int());
        \\}
        \\
    );
}

test "uv-return-value-intcast-truncation: form B fires" {
    try testing.expectFires(check, R,
        \\fn bytesRead(req: uv.fs_t) usize {
        \\    return @intCast(req.rc.int());
        \\}
        \\
    );
}

test "uv-return-value-intcast-truncation: plain identifier does not fire" {
    try testing.expectNoFire(check,
        \\fn bytesRead(n: usize) usize {
        \\    return @intCast(n);
        \\}
        \\
    );
}

test "uv-return-value-intcast-truncation: at-as does not fire" {
    try testing.expectNoFire(check,
        \\fn bytesRead(rc: uv.ReturnCode) i64 {
        \\    return @as(i64, rc.int());
        \\}
        \\
    );
}
