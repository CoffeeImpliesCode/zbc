//! Detects a direct write to `list.items[list.items.len]` — writing one
//! slot past the initialized region without ensuring capacity first.
//!
//! Pattern:
//!   output.items[output.items.len] = 0;        // ← BUG: may write past backing alloc
//!   return output.items[0..output.items.len+1 :0];
//!
//! When the ArrayList is sized exactly right, `items.len == capacity` and
//! writing to `items[items.len]` writes into allocator bookkeeping bytes
//! (or triggers a safety-checked OOB trap in Debug mode).  The correct
//! approach is:
//!   try output.ensureUnusedCapacity(1);
//!   output.appendAssumeCapacity(sentinel_value);
//!
//! Real-world shape: oven-sh/bun#29982 (toUTF16Alloc sentinel branch).
//!
//! Detection (Tier 1, token walk):
//!   Scan for the 11-token pattern:
//!     t+0: identifier(X)   t+1: .period   t+2: identifier("items")
//!     t+3: .l_bracket
//!     t+4: identifier(X)   t+5: .period   t+6: identifier("items")
//!     t+7: .period         t+8: identifier("len")
//!     t+9: .r_bracket      t+10: .equal
//!   where the receiver name at t+0 and t+4 match.
//!   Fire at the `equal` token (t+10).

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
const R = "arraylist-sentinel-write-without-capacity";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .arraylist_sentinel_write_without_capacity)) return;
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

    if (first + 10 > last) return;

    var t: Ast.TokenIndex = first;
    while (t + 10 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Pattern: X.items[X.items.len] =
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_bracket) continue;
        if (tags[t + 4] != .identifier) continue;
        if (tags[t + 5] != .period) continue;
        if (tags[t + 6] != .identifier) continue;
        if (tags[t + 7] != .period) continue;
        if (tags[t + 8] != .identifier) continue;
        if (tags[t + 9] != .r_bracket) continue;
        if (tags[t + 10] != .equal) continue;

        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "items")) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 6), "items")) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 8), "len")) continue;

        // Receiver names must match.
        const recv = tree.tokenSlice(t);
        if (!std.mem.eql(u8, tree.tokenSlice(t + 4), recv)) continue;

        try report(gpa, problems, tree, t, t + 10, recv);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    recv_tok: Ast.TokenIndex,
    eq_tok: Ast.TokenIndex,
    recv: []const u8,
) !void {
    _ = recv_tok;
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.items[{s}.items.len] = …` writes one slot past the initialized region without ensuring capacity; when `items.len == capacity` this writes into allocator bookkeeping bytes (Debug: safety-checked OOB trap; ReleaseFast: silent corruption); use `try {s}.ensureUnusedCapacity(1); {s}.appendAssumeCapacity(value);` instead",
        .{ recv, recv, recv, recv },
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

test "arraylist-sentinel-write-without-capacity: basic pattern fires" {
    try testing.expectFires(check, R,
        \\fn toSentinel(output: *std.ArrayList(u16)) ![]const u16 {
        \\    output.items[output.items.len] = 0;
        \\    return output.items;
        \\}
        \\
    );
}

test "arraylist-sentinel-write-without-capacity: different receiver names do not fire" {
    try testing.expectNoFire(check,
        \\fn f(a: *std.ArrayList(u8), b: *std.ArrayList(u8)) !void {
        \\    a.items[b.items.len] = 0;
        \\}
        \\
    );
}

test "arraylist-sentinel-write-without-capacity: valid len-1 access does not fire" {
    try testing.expectNoFire(check,
        \\fn f(list: *std.ArrayList(u8)) u8 {
        \\    return list.items[list.items.len - 1];
        \\}
        \\
    );
}

test "arraylist-sentinel-write-without-capacity: read access does not fire" {
    try testing.expectNoFire(check,
        \\fn f(list: *std.ArrayList(u8)) u8 {
        \\    const x = list.items[list.items.len];
        \\    return x;
        \\}
        \\
    );
}
