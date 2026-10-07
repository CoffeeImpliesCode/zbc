//! Detects `initCapacity(allocator, size + N)` where `N` is a small integer
//! literal and `size` is an identifier.  The plain `+` overflows when `size`
//! is near `maxInt(usize)`, wrapping the capacity to a small value and causing
//! the allocation to be much smaller than intended.
//!
//! Real-world instances:
//!   - oven-sh/bun#29284 (read_file.zig): `initCapacity(default_allocator, this.size + 16)`
//!     fixed to `this.size +| 16`.
//!   - oven-sh/bun#26999 (cron parser): `initCapacity(allocator, input.len + 16)`.
//!
//! Detection (Tier 1, token walk):
//!   Two patterns:
//!   Form A: `initCapacity ( identifier , identifier + number_literal )`
//!     — 8 tokens (t+0..t+7)
//!   Form B: `initCapacity ( identifier , identifier . identifier + number_literal )`
//!     — 10 tokens (t+0..t+9)
//!   Fire at the `+` operator token.
//!   Suppression: if the `+` is `plus_percent` (wrapping `+%`) or
//!   `pipe_percent` / saturating add — that is an explicit overflow choice
//!   and is not flagged.  Only plain `.plus` fires.

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
const R = "initcapacity-plain-add-overflow";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .initcapacity_plain_add_overflow)) return;
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
        if (!std.mem.eql(u8, tree.tokenSlice(t), "initCapacity")) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .comma) continue;

        // Form A: initCapacity ( alloc , identifier + number_literal )
        //   t+4: identifier
        //   t+5: plus
        //   t+6: number_literal
        //   t+7: r_paren
        if (matchFormA(tags, t)) {
            try report(gpa, problems, tree, t + 5);
            continue;
        }

        // Form B: initCapacity ( alloc , identifier . identifier + number_literal )
        //   t+4: identifier
        //   t+5: period
        //   t+6: identifier
        //   t+7: plus
        //   t+8: number_literal
        //   t+9: r_paren
        if (t + 9 <= last and matchFormB(tags, t)) {
            try report(gpa, problems, tree, t + 7);
            continue;
        }
    }
}

fn matchFormA(tags: []const std.zig.Token.Tag, t: Ast.TokenIndex) bool {
    return tags[t + 4] == .identifier and
        tags[t + 5] == .plus and
        tags[t + 6] == .number_literal and
        tags[t + 7] == .r_paren;
}

fn matchFormB(tags: []const std.zig.Token.Tag, t: Ast.TokenIndex) bool {
    return tags[t + 4] == .identifier and
        tags[t + 5] == .period and
        tags[t + 6] == .identifier and
        tags[t + 7] == .plus and
        tags[t + 8] == .number_literal and
        tags[t + 9] == .r_paren;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    plus_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`initCapacity(alloc, size + N)` — plain `+` overflows when `size` is near `maxInt(usize)`, wrapping the capacity to a value smaller than intended and causing heap corruption or a panic on subsequent writes; use saturating add `+|` instead: `initCapacity(alloc, size +| N)`",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, plus_tok),
        .end = try Pos.fromTokenEnd(tree, plus_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "initcapacity-plain-add-overflow: form A fires" {
    try testing.expectFires(check, R,
        \\fn makeBuffer(allocator: std.mem.Allocator, size: usize) !std.ArrayList(u8) {
        \\    return std.ArrayList(u8).initCapacity(allocator, size + 16);
        \\}
        \\
    );
}

test "initcapacity-plain-add-overflow: form B fires" {
    try testing.expectFires(check, R,
        \\const Blob = struct { size: usize };
        \\fn makeBuffer(allocator: std.mem.Allocator, this: Blob) !std.ArrayList(u8) {
        \\    return std.ArrayList(u8).initCapacity(allocator, this.size + 16);
        \\}
        \\
    );
}

test "initcapacity-plain-add-overflow: saturating add does not fire" {
    try testing.expectNoFire(check,
        \\fn makeBuffer(allocator: std.mem.Allocator, size: usize) !std.ArrayList(u8) {
        \\    return std.ArrayList(u8).initCapacity(allocator, size +| 16);
        \\}
        \\
    );
}

test "initcapacity-plain-add-overflow: plain identifier does not fire" {
    try testing.expectNoFire(check,
        \\fn makeBuffer(allocator: std.mem.Allocator, cap: usize) !std.ArrayList(u8) {
        \\    return std.ArrayList(u8).initCapacity(allocator, cap);
        \\}
        \\
    );
}

test "initcapacity-plain-add-overflow: two identifiers added does not fire" {
    // Form A requires number_literal as the RHS of +, not another identifier.
    try testing.expectNoFire(check,
        \\fn makeBuffer(allocator: std.mem.Allocator, a: usize, b: usize) !std.ArrayList(u8) {
        \\    return std.ArrayList(u8).initCapacity(allocator, a + b);
        \\}
        \\
    );
}
