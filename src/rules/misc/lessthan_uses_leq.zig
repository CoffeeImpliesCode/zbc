//! Detects `<=` inside functions named `lessThan` — Zig sort comparators
//! must implement strict weak ordering: `lessThan(a, a)` must return `false`.
//! Using `<=` instead of `<` makes `lessThan(a, a)` return `true`, violating
//! strict weak ordering and causing `std.sort` to exhibit undefined behavior
//! (infinite loops, incorrect ordering, heap corruption depending on the sort
//! algorithm).
//!
//! Real-world instance:
//!   - oven-sh/bun#24146 (sourcemap sort): `Mapping.List.LessThan.lessThan`
//!     returned `a.lines < b.lines or (a.lines == b.lines and a.columns <= b.columns)`.
//!     When `a.lines == b.lines and a.columns == b.columns`, both
//!     `lessThan(a, b)` and `lessThan(b, a)` returned `true` simultaneously,
//!     breaking `std.sort.block`'s loop termination invariant.
//!     Fix: replaced `<=` with `<` and added an index tiebreaker.
//!
//! Detection (Tier 1, flat token walk with brace-depth tracking):
//!   Scans for `keyword_fn identifier("lessThan") l_paren`.
//!   Then tracks brace depth to isolate the function body.
//!   Fires on any `angle_bracket_left_equal` (`<=`) inside the body.
//!   The outer `fn lessThan` constraint limits false positives to
//!   non-comparator uses of `<=` inside functions coincidentally named
//!   `lessThan`, which are extremely rare.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "lessthan-uses-leq";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .lessthan_uses_leq)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 2 <= last_tok) : (t += 1) {
        // Find `fn lessThan(`
        if (tags[t] != .keyword_fn) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "lessThan")) continue;
        if (tags[t + 2] != .l_paren) continue;

        // Skip the parameter list (paren-balanced).
        var i = t + 2;
        var depth: u32 = 1;
        i += 1;
        while (i <= last_tok and depth > 0) : (i += 1) {
            if (tags[i] == .l_paren) depth += 1 else if (tags[i] == .r_paren) depth -= 1;
        }
        // `i` is now past the closing `)`.

        // Skip to the opening `{` of the function body (past return type).
        while (i <= last_tok and tags[i] != .l_brace) : (i += 1) {}
        if (i > last_tok) continue;

        // Scan the function body.
        depth = 1;
        i += 1;
        while (i <= last_tok and depth > 0) : (i += 1) {
            switch (tags[i]) {
                .l_brace => depth += 1,
                .r_brace => depth -= 1,
                .angle_bracket_left_equal => {
                    if (depth > 0) try report(gpa, problems, tree, i);
                },
                else => {},
            }
        }

        // Jump `t` past the scanned body so we don't re-enter it.
        t = if (i > 0) i - 1 else 0;
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    leq_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`<=` inside a `lessThan` comparator violates strict weak ordering — `lessThan(a, a)` returns `true` for equal elements, causing `std.sort` to loop or produce incorrect results; use `<` with a tiebreaker instead",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, leq_tok),
        .end = try Pos.fromTokenEnd(tree, leq_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "lessthan-uses-leq: fires" {
    try testing.expectFires(check, R,
        \\const Cmp = struct {
        \\    fn lessThan(ctx: void, a: Item, b: Item) bool {
        \\        _ = ctx;
        \\        return a.line < b.line or (a.line == b.line and a.col <= b.col);
        \\    }
        \\};
        \\
    );
}

test "lessthan-uses-leq: strict comparison does not fire" {
    try testing.expectNoFire(check,
        \\const Cmp = struct {
        \\    fn lessThan(ctx: void, a: Item, b: Item) bool {
        \\        _ = ctx;
        \\        return a.line < b.line or (a.line == b.line and a.col < b.col);
        \\    }
        \\};
        \\
    );
}

test "lessthan-uses-leq: leq outside lessThan does not fire" {
    try testing.expectNoFire(check,
        \\fn clamp(x: i32, max: i32) i32 {
        \\    return if (x <= max) x else max;
        \\}
        \\
    );
}

test "lessthan-uses-leq: top-level fn (not method) fires" {
    // Rule fires regardless of whether lessThan is a method or a free function.
    try testing.expectFires(check, R,
        \\fn lessThan(a: u32, b: u32) bool {
        \\    return a <= b;
        \\}
        \\
    );
}

test "lessthan-uses-leq: leq inside nested block fires" {
    // `<=` inside a nested if block still counts — rule tracks brace depth.
    try testing.expectFires(check, R,
        \\const Cmp = struct {
        \\    fn lessThan(_: void, a: Item, b: Item) bool {
        \\        if (a.primary == b.primary) {
        \\            return a.secondary <= b.secondary;
        \\        }
        \\        return a.primary < b.primary;
        \\    }
        \\};
        \\
    );
}

test "lessthan-uses-leq: lessThanOrEqual name does not fire" {
    // The rule matches only the exact token "lessThan", not longer names.
    try testing.expectNoFire(check,
        \\fn lessThanOrEqual(a: u32, b: u32) bool {
        \\    return a <= b;
        \\}
        \\
    );
}

test "lessthan-uses-leq: greaterOrEqual inside lessThan does not fire" {
    // The rule only checks for `<=`, not `>=`.
    try testing.expectNoFire(check,
        \\fn lessThan(a: u32, b: u32) bool {
        \\    return !(a >= b);
        \\}
        \\
    );
}
