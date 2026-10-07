//! Detects `something.tryGet() orelse unreachable` — `tryGet()` on a JSRef
//! returns `null` when the backing JSObject has been finalized.  Using
//! `orelse unreachable` converts a null return into SIGILL (undefined behavior
//! in ReleaseFast) or a panic in safe builds when the object is finalized
//! before the method is called.
//!
//! Real-world instance:
//!   - oven-sh/bun#29210 (valkey client): `updatePollRef()` called
//!     `subscriptionCallbackMap()` → `this.parent().this_value.tryGet() orelse unreachable`.
//!     After `finalize()` set `flags.finalized`, `tryGet()` returned null and the
//!     `unreachable` branch fired as SIGILL.  Fix: add
//!     `if (this.client.flags.finalized) return;` before the call.
//!
//! Detection (Tier 1, token walk inside fn bodies):
//!   Pattern: `identifier("tryGet") l_paren r_paren keyword_orelse keyword_unreachable`
//!   — 5 tokens.  Fire at the `tryGet` identifier token.
//!   `tryGet() orelse return` and `tryGet() orelse null` do not fire.

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
const R = "tryget-orelse-unreachable";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .tryget_orelse_unreachable)) return;
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

    if (first + 4 > last) return;

    var t: Ast.TokenIndex = first;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Pattern: tryGet ( ) orelse unreachable
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "tryGet")) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .r_paren) continue;
        if (tags[t + 3] != .keyword_orelse) continue;
        if (tags[t + 4] != .keyword_unreachable) continue;

        try report(gpa, problems, tree, t);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    tryget_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`tryGet() orelse unreachable` — `tryGet()` returns `null` for finalized JSRef objects, so this becomes SIGILL (ReleaseFast) or a panic (safe builds) if called after finalization; guard with an early `if (flags.finalized) return;` or use `orelse return`",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, tryget_tok),
        .end = try Pos.fromTokenEnd(tree, tryget_tok + 4),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "tryget-orelse-unreachable: fires" {
    try testing.expectFires(check, R,
        \\fn update(this: *Self) void {
        \\    const parent = this.jsValue.tryGet() orelse unreachable;
        \\    _ = parent;
        \\}
        \\
    );
}

test "tryget-orelse-unreachable: orelse return does not fire" {
    try testing.expectNoFire(check,
        \\fn update(this: *Self) void {
        \\    const parent = this.jsValue.tryGet() orelse return;
        \\    _ = parent;
        \\}
        \\
    );
}

test "tryget-orelse-unreachable: orelse null does not fire" {
    try testing.expectNoFire(check,
        \\fn maybeParent(this: *Self) ?*Parent {
        \\    return this.jsValue.tryGet() orelse null;
        \\}
        \\
    );
}

test "tryget-orelse-unreachable: tryGet alone does not fire" {
    try testing.expectNoFire(check,
        \\fn maybeParent(this: *Self) ?*Parent {
        \\    return this.jsValue.tryGet();
        \\}
        \\
    );
}
