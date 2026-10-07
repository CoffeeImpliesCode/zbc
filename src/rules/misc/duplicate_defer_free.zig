//! Detects `defer allocator.free(X)` appearing twice at the outermost level
//! of the same function body — both defers fire at function exit in LIFO order,
//! freeing the same allocation twice (double-free).
//!
//! Real-world instance:
//!   - oven-sh/bun#22978 (createArgv): two separate `defer allocator.free(args)`
//!     at the top level of the function body; both fired at fn exit, causing a
//!     double-free of the argv allocation.
//!
//! Detection (Tier 1, fn-body token walk):
//!   Pattern: `keyword_defer identifier period identifier("free") l_paren
//!             identifier r_paren` — 7 tokens.
//!   Scopes to brace-depth == 1 inside each fn body to avoid FPs from sibling
//!   `if`/`while` blocks or nested fn definitions at deeper depths.
//!   Fires at the second occurrence when the same (allocator-name, slice-name)
//!   pair appears more than once at the outermost fn body level.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "duplicate-defer-free";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .duplicate_defer_free)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 2 <= last_tok) : (t += 1) {
        // Find `fn name(`
        if (tags[t] != .keyword_fn) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;

        // Skip the parameter list (paren-balanced).
        var i = t + 2;
        var depth: u32 = 1;
        i += 1;
        while (i <= last_tok and depth > 0) : (i += 1) {
            if (tags[i] == .l_paren) depth += 1 else if (tags[i] == .r_paren) depth -= 1;
        }

        // Skip to the opening `{` of the function body (past return type).
        while (i <= last_tok and tags[i] != .l_brace) : (i += 1) {}
        if (i > last_tok) continue;

        // Scan the function body at outermost level only (depth == 1).
        depth = 1;
        i += 1;

        // Fixed-size buffer: functions rarely have more than a handful of
        // defer-free statements, so a stack array avoids allocation.
        var defers_buf: [32]Ast.TokenIndex = undefined;
        var defers_len: usize = 0;

        while (i <= last_tok and depth > 0) : (i += 1) {
            switch (tags[i]) {
                .l_brace => depth += 1,
                .r_brace => depth -= 1,
                .keyword_defer => {
                    if (depth != 1) continue;
                    if (i + 6 > last_tok) continue;
                    if (tags[i + 1] != .identifier) continue;
                    if (tags[i + 2] != .period) continue;
                    if (tags[i + 3] != .identifier) continue;
                    if (!std.mem.eql(u8, tree.tokenSlice(i + 3), "free")) continue;
                    if (tags[i + 4] != .l_paren) continue;
                    if (tags[i + 5] != .identifier) continue;
                    if (tags[i + 6] != .r_paren) continue;

                    const alloc = tree.tokenSlice(i + 1);
                    const slice_name = tree.tokenSlice(i + 5);
                    for (defers_buf[0..defers_len]) |prev| {
                        if (std.mem.eql(u8, tree.tokenSlice(prev + 1), alloc) and
                            std.mem.eql(u8, tree.tokenSlice(prev + 5), slice_name))
                        {
                            try report(gpa, problems, tree, i);
                            break;
                        }
                    }
                    if (defers_len < defers_buf.len) {
                        defers_buf[defers_len] = i;
                        defers_len += 1;
                    }
                },
                else => {},
            }
        }

        t = if (i > 0) i - 1 else 0;
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    defer_tok: Ast.TokenIndex,
) !void {
    const alloc = tree.tokenSlice(defer_tok + 1);
    const slice_name = tree.tokenSlice(defer_tok + 5);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`defer {s}.free({s})` appears twice in this function body — both fire at function exit (LIFO), freeing `{s}` twice; remove the duplicate `defer`",
        .{ alloc, slice_name, slice_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, defer_tok),
        .end = try Pos.fromTokenEnd(tree, defer_tok + 6),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "duplicate-defer-free: fires on duplicate defer free" {
    try testing.expectFires(check, R,
        \\fn createArgv(allocator: std.mem.Allocator) ![][]u8 {
        \\    const args = try allocator.alloc([]u8, 10);
        \\    defer allocator.free(args);
        \\    _ = args.len;
        \\    defer allocator.free(args);
        \\    return args;
        \\}
        \\
    );
}

test "duplicate-defer-free: single defer free does not fire" {
    try testing.expectNoFire(check,
        \\fn createArgv(allocator: std.mem.Allocator) ![][]u8 {
        \\    const args = try allocator.alloc([]u8, 10);
        \\    defer allocator.free(args);
        \\    return args;
        \\}
        \\
    );
}

test "duplicate-defer-free: different slices do not fire" {
    try testing.expectNoFire(check,
        \\fn foo(allocator: std.mem.Allocator) void {
        \\    const buf1 = allocator.alloc(u8, 10) catch unreachable;
        \\    defer allocator.free(buf1);
        \\    const buf2 = allocator.alloc(u8, 20) catch unreachable;
        \\    defer allocator.free(buf2);
        \\}
        \\
    );
}

test "duplicate-defer-free: different allocators do not fire" {
    try testing.expectNoFire(check,
        \\fn foo(gpa: std.mem.Allocator, arena: std.mem.Allocator) void {
        \\    const buf = gpa.alloc(u8, 10) catch unreachable;
        \\    defer gpa.free(buf);
        \\    defer arena.free(buf);
        \\}
        \\
    );
}

test "duplicate-defer-free: defer in nested block does not fire" {
    try testing.expectNoFire(check,
        \\fn foo(allocator: std.mem.Allocator) void {
        \\    if (true) {
        \\        const buf = allocator.alloc(u8, 10) catch unreachable;
        \\        defer allocator.free(buf);
        \\    }
        \\    if (false) {
        \\        const buf = allocator.alloc(u8, 20) catch unreachable;
        \\        defer allocator.free(buf);
        \\    }
        \\}
        \\
    );
}
