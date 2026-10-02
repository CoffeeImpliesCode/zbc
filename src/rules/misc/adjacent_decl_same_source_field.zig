//! Detects two consecutive `const` declarations that bind the same struct field
//! via `orelse`:
//!   const user = uri.user orelse "";
//!   const password = uri.user orelse "";  // should be uri.password
//! Both variables silently alias the same source field — the second declaration
//! likely intended a different field.
//!
//! Real-world instance:
//!   - ziglang/zig#25099: `const user = uri.user orelse ...; const password = uri.user orelse ...`
//!     — `uri.password` was never read; both variables held the username value.
//!
//! Detection (Tier 1, flat token walk):
//!   Pattern: `const VAR1 = STRUCT . FIELD orelse ... ; const VAR2 = STRUCT . FIELD orelse`
//!   — find the 7-token prefix `const VAR = STRUCT . FIELD orelse`, skip to `;` at depth 0,
//!   then check whether the immediately following statement matches the same (STRUCT, FIELD) pair.
//!   Fire at the second `const` token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "adjacent-decl-same-source-field";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .adjacent_decl_same_source_field)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 8) return;
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 6 <= last_tok) : (t += 1) {
        // Pattern prefix: const VAR = STRUCT . FIELD orelse
        if (tags[t] != .keyword_const) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .identifier) continue;
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] != .identifier) continue;
        if (tags[t + 6] != .keyword_orelse) continue;

        const var1 = tree.tokenSlice(t + 1);
        const struct1 = tree.tokenSlice(t + 3);
        const field1 = tree.tokenSlice(t + 5);

        // Skip to ';' at paren/brace/bracket depth 0
        var i = t + 7;
        var depth: u32 = 0;
        while (i <= last_tok) : (i += 1) {
            switch (tags[i]) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => if (depth > 0) {
                    depth -= 1;
                },
                .semicolon => if (depth == 0) break,
                else => {},
            }
        }
        if (i > last_tok) continue;

        // Check the immediately following declaration
        const next = i + 1;
        if (next + 6 > last_tok) continue;
        if (tags[next] != .keyword_const) continue;
        if (tags[next + 1] != .identifier) continue;
        if (tags[next + 2] != .equal) continue;
        if (tags[next + 3] != .identifier) continue;
        if (tags[next + 4] != .period) continue;
        if (tags[next + 5] != .identifier) continue;
        if (tags[next + 6] != .keyword_orelse) continue;

        const var2 = tree.tokenSlice(next + 1);
        const struct2 = tree.tokenSlice(next + 3);
        const field2 = tree.tokenSlice(next + 5);

        if (!std.mem.eql(u8, struct1, struct2)) continue;
        if (!std.mem.eql(u8, field1, field2)) continue;
        if (std.mem.eql(u8, var1, var2)) continue; // identical names = compiler error anyway

        try report(gpa, problems, tree, next, var1, var2, struct1, field1);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    second_tok: Ast.TokenIndex,
    var1: []const u8,
    var2: []const u8,
    struct_name: []const u8,
    field_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` and `{s}` both bind `{s}.{s}` via `orelse`; the second declaration likely intended a different source field",
        .{ var1, var2, struct_name, field_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, second_tok),
        .end = Pos.fromTokenEnd(tree, second_tok + 6),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "adjacent-decl-same-source-field: fires on same struct.field" {
    try testing.expectFires(check, R,
        \\fn parseUri(uri: Uri) void {
        \\    const user = uri.user orelse "";
        \\    const password = uri.user orelse "";
        \\    _ = user;
        \\    _ = password;
        \\}
        \\
    );
}

test "adjacent-decl-same-source-field: different fields do not fire" {
    try testing.expectNoFire(check,
        \\fn parseUri(uri: Uri) void {
        \\    const user = uri.user orelse "";
        \\    const password = uri.password orelse "";
        \\    _ = user;
        \\    _ = password;
        \\}
        \\
    );
}

test "adjacent-decl-same-source-field: different struct does not fire" {
    try testing.expectNoFire(check,
        \\fn parseUri(a: Uri, b: Uri) void {
        \\    const user = a.user orelse "";
        \\    const password = b.user orelse "";
        \\    _ = user;
        \\    _ = password;
        \\}
        \\
    );
}

test "adjacent-decl-same-source-field: non-adjacent statements do not fire" {
    try testing.expectNoFire(check,
        \\fn parseUri(uri: Uri) void {
        \\    const user = uri.user orelse "";
        \\    const host = uri.host orelse "";
        \\    const password = uri.user orelse "";
        \\    _ = user;
        \\    _ = host;
        \\    _ = password;
        \\}
        \\
    );
}

test "adjacent-decl-same-source-field: orelse with complex expr fires" {
    try testing.expectFires(check, R,
        \\fn parseUri(uri: Uri) void {
        \\    const user = uri.user orelse return error.Missing;
        \\    const password = uri.user orelse return error.Missing;
        \\    _ = user;
        \\    _ = password;
        \\}
        \\
    );
}
