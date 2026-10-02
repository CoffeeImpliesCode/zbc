//! Detects `.items(.FIELD)[index].* = VALUE` on a MultiArrayList — dereferencing
//! the result of `MultiArrayList.items(.field)` as if it were a slice of pointers.
//! `items(.field)` returns a `[]FieldType` (a slice of values, not pointers);
//! `[index].*` interprets the field value as a memory address and dereferences it,
//! which is undefined behaviour.  Use direct assignment: `list.items(.field)[index] = value`.
//!
//! Real-world instance:
//!   - ziglang/zig#22968 (ArrayHashMap setKey with store_hash=true):
//!     `self.entries.items(.hash)[index].* = checkedHash(ctx, key_ptr.*)`
//!     — `.items(.hash)` returns `[]u32`; the `.* =` tries to dereference a u32 as a pointer.
//!     Fix: removed the `.*`.
//!
//! Detection (Tier 1, bracket-balanced token walk):
//!   Pattern:
//!     `. items ( . field_ident ) [`  — 7-token prefix
//!     ... index expression ...
//!     `] .* =`                       — 3-token suffix (.* is period_asterisk)
//!   Fire at the `.*` (period + asterisk) tokens.
//!   The bracket-balanced skip handles nested `[...]` in the index expression.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "multiarray-items-deref-assign";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .multiarray_items_deref_assign)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 12) return;
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 6 <= last_tok) : (t += 1) {
        // Prefix: . items ( . identifier ) [
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "items")) continue;
        if (tags[t + 2] != .l_paren) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        if (tags[t + 5] != .r_paren) continue;
        if (tags[t + 6] != .l_bracket) continue;

        // Skip to matching ']' (depth-balanced)
        var i = t + 7;
        var depth: u32 = 1;
        while (i <= last_tok and depth > 0) : (i += 1) {
            switch (tags[i]) {
                .l_bracket => depth += 1,
                .r_bracket => depth -= 1,
                else => {},
            }
        }
        if (depth != 0) continue; // unbalanced — skip
        // i is now one past the matching ']', so the ']' is at i-1
        const close_bracket = i - 1;

        // Suffix: ] .* =   (.* is a single period_asterisk token)
        if (close_bracket + 2 > last_tok) continue;
        if (tags[close_bracket + 1] != .period_asterisk) continue;
        if (tags[close_bracket + 2] != .equal) continue;

        const field_name = tree.tokenSlice(t + 4);
        try report(gpa, problems, tree, close_bracket + 1, field_name);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    dot_tok: Ast.TokenIndex,
    field_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`.items(.{s})[i].* =` — `MultiArrayList.items(.{s})` returns a `[]FieldType` slice of values, not pointers; `[i].*` dereferences the field value as a memory address (UB); remove the `.*` and assign directly: `.items(.{s})[i] = value`",
        .{ field_name, field_name, field_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, dot_tok),
        .end = Pos.fromTokenEnd(tree, dot_tok + 1),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "multiarray-items-deref-assign: fires on .items(.field)[i].* =" {
    try testing.expectFires(check, R,
        \\fn setHash(self: *Self, index: usize, h: u32) void {
        \\    self.entries.items(.hash)[index].* = h;
        \\}
        \\
    );
}

test "multiarray-items-deref-assign: direct assignment does not fire" {
    try testing.expectNoFire(check,
        \\fn setHash(self: *Self, index: usize, h: u32) void {
        \\    self.entries.items(.hash)[index] = h;
        \\}
        \\
    );
}

test "multiarray-items-deref-assign: read dereference does not fire" {
    try testing.expectNoFire(check,
        \\fn getHash(self: *Self, index: usize) u32 {
        \\    return self.entries.items(.hash)[index];
        \\}
        \\
    );
}

test "multiarray-items-deref-assign: fires with complex index expression" {
    try testing.expectFires(check, R,
        \\fn update(list: *MAList, i: usize, off: usize, val: u64) void {
        \\    list.items(.value)[i + off].* = val;
        \\}
        \\
    );
}

test "multiarray-items-deref-assign: regular slice deref does not fire" {
    try testing.expectNoFire(check,
        \\fn assign(ptrs: []*u32, i: usize, v: u32) void {
        \\    ptrs[i].* = v;
        \\}
        \\
    );
}
