//! oven-sh/bun#29452 detector — `<allocator>.realloc(slice, <expr> *
//! @sizeOf(T))`.  Zig's `Allocator.realloc` takes an ELEMENT count,
//! not bytes, so the `* @sizeOf(T)` over-allocates by `@sizeOf(T)×`.
//!
//! Detection is a purely-syntactic token scan over the whole file:
//! find any `.realloc(` call whose second argument contains
//! `… * @sizeOf(…)` (or `@sizeOf(…) * …`) inside the same paren
//! depth as the call's own `(` — i.e. the multiplication is in the
//! new-length slot, not nested in a different sub-expression.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

/// Returns `SourceTooWide` if the source or token count exceeds the AST position domain.
pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .realloc_byte_count)) return;
    _ = cache;

    if (tree.source.len >= std.math.maxInt(u32)) return error.SourceTooWide;
    const tok_count = std.math.cast(u32, tree.tokens.len) orelse return error.SourceTooWide;
    const tags = tree.tokens.items(.tag);
    const last_tok: Ast.TokenIndex = tok_count -| 1;
    var t: Ast.TokenIndex = 0;
    while (t < last_tok and last_tok - t > 3) : (t += 1) {
        // Match `.realloc (`.
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "realloc")) continue;
        if (tags[t + 2] != .l_paren) continue;

        // Find the matching `)` and the top-level `,` that separates
        // arg1 (the slice) from arg2 (the new length).
        const open = t + 2;
        var depth: u32 = 1;
        var comma: ?Ast.TokenIndex = null;
        var u: Ast.TokenIndex = open + 1;
        while (u <= last_tok) : (u += 1) {
            switch (tags[u]) {
                .l_paren => depth += 1,
                .r_paren => {
                    depth -= 1;
                    if (depth == 0) break;
                },
                .comma => if (depth == 1 and comma == null) {
                    comma = u;
                },
                else => {},
            }
        }
        if (depth != 0) continue;
        const close = u;
        const sep = comma orelse continue;
        // arg2 spans (sep, close).  Scan for `@sizeOf(` AT depth 1 of
        // the realloc's outer paren — i.e. don't dive into nested
        // calls.  Then verify the @sizeOf is paired with an `*` on
        // either side at depth 1 (the multiplication that signals
        // "treating element count as byte count").
        if (arg2ContainsSizeofMul(tree, sep + 1, close)) {
            try report(gpa, problems, tree, t);
        }
        t = close;
    }
}

/// Walk tokens from `start` (inclusive) to `end` (exclusive) and
/// return true iff a `* @sizeOf(<X>)` or `@sizeOf(<X>) * <expr>`
/// pattern appears at the OUTER call-arg's paren depth — i.e. not
/// buried inside an unrelated nested call.
fn arg2ContainsSizeofMul(tree: *const Ast, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    var depth: u32 = 0;
    var t: Ast.TokenIndex = start;
    while (t < end) : (t += 1) {
        switch (tags[t]) {
            .l_paren => depth += 1,
            .r_paren => if (depth > 0) {
                depth -= 1;
            },
            .builtin => {
                if (depth != 0) continue;
                if (!std.mem.eql(u8, tree.tokenSlice(t), "@sizeOf")) continue;
                // Pattern `<lhs> * @sizeOf(…)` — preceding token at
                // depth 0 must be `*` (with whitespace allowed via
                // direct token adjacency).
                if (t > start and tags[t - 1] == .asterisk) return true;
                // Pattern `@sizeOf(…) * <rhs>` — find the matching
                // `)` for this builtin call, then check the next
                // top-level token.
                if (end - t <= 1 or tags[t + 1] != .l_paren) continue;
                var d: u32 = 1;
                var u: Ast.TokenIndex = t + 2;
                while (u < end) : (u += 1) {
                    switch (tags[u]) {
                        .l_paren => d += 1,
                        .r_paren => {
                            d -= 1;
                            if (d == 0) break;
                        },
                        else => {},
                    }
                }
                if (d != 0) continue;
                if (end - u > 1 and tags[u + 1] == .asterisk) return true;
            },
            else => {},
        }
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    period_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`realloc` takes an element count, not bytes — the `* @sizeOf(…)` multiplier in the second argument over-allocates by `@sizeOf(…)×`; drop the multiplier (or pre-bind to `const new_bytes = …;` for a genuine `[]u8` reallocation)",
        .{},
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "realloc-byte-count",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, period_tok + 1),
        .end = try Pos.fromTokenEnd(tree, period_tok + 1),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "realloc-byte-count: `n * @sizeOf(T)` fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\pub fn grow(a: std.mem.Allocator, p: [*]T, len: usize, n: usize) []T {
        \\    return a.realloc(p[0..len], n * @sizeOf(T)) catch unreachable;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("realloc-byte-count", problems.items[0].rule_id);
}

test "realloc-byte-count: `@sizeOf(T) * n` (left-side) also fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\pub fn grow(a: std.mem.Allocator, p: [*]T, len: usize, n: usize) []T {
        \\    return a.realloc(p[0..len], @sizeOf(T) * n) catch unreachable;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "realloc-byte-count: plain element count is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\pub fn grow(a: std.mem.Allocator, p: [*]T, cap: usize, n: usize) []T {
        \\    return a.realloc(p[0..cap], n) catch unreachable;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "realloc-byte-count: pre-bound byte count via local is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\pub fn grow(a: std.mem.Allocator, p: [*]u8, cap: usize, n: usize) []u8 {
        \\    const new_bytes = n * @sizeOf(T);
        \\    return a.realloc(p[0..cap], new_bytes) catch unreachable;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "realloc-byte-count: @sizeOf inside a nested call doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct { x: u32 };
        \\pub fn grow(a: std.mem.Allocator, p: [*]T, cap: usize) []T {
        \\    return a.realloc(p[0..cap], doubleOf(2 * @sizeOf(T))) catch unreachable;
        \\}
        \\fn doubleOf(x: usize) usize { return x * 2; }
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
