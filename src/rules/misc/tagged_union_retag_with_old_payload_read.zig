//! Tagged-union retag-with-old-payload-read detector — a statement
//! `<path> = .{ .<NewTag> = .{ ... <path>.<OldTag>... ... } };`
//! where the RHS reads `<path>.<OldTag>...` while assigning a
//! different tag.  Under Zig's x86_64 self-hosted backend (post-
//! 0.15) the active-tag flip happens BEFORE the RHS evaluates, so
//! the read of the old tag's payload may see undefined / garbage.
//! LLVM hid this for years; the bug surfaces when the backend
//! changes.
//!
//! Real-world: tigerbeetle/tigerbeetle#3317 and #2200 (same file
//! `src/lsm/scan_tree.zig`, same shape, 14 months apart).  Fix
//! hoists the old-tag read into a local before the union assignment:
//!
//!   self.state = iterating: {
//!       const key = self.state.loading_index.key_exclusive_next;
//!       break :iterating .{ .iterating = .{ .key_exclusive_next = key, ... } };
//!   };
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Skip comptime type-builder fns.
//!   2. Walk for `=` tokens at statement depth.
//!   3. Walk back from `=` to extract the LHS path `<recv>.<field>`
//!      (one-or-more dotted identifiers).
//!   4. After `=`, require the RHS to start with `.{ .<NewTag> = ...`.
//!   5. Within the `.{ ... }` body, scan for the LHS path tokens
//!      followed by `.<OldTag>` where `OldTag ≠ NewTag`.
//!   6. Fire at the OldTag access site.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const matchBrace = tokens.matchBrace;
const skipNestedFn = tokens.skipNestedFn;
const returnsType = tokens.returnsType;
const bodyOf = tokens.bodyOf;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .tagged_union_retag_with_old_payload_read)) return;
    _ = cache;

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        if (returnsType(tree, node)) continue;
        const body = bodyOf(tree, node) orelse continue;
        try checkBody(gpa, tree, body, problems);
    }
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

    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .equal) continue;
        // RHS must start with `.{ .<NewTag> = ...`.
        if (t + 4 > last) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .l_brace) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        if (t + 5 > last or tags[t + 5] != .equal) continue;
        const new_tag_tok = t + 4;
        const new_tag = tree.tokenSlice(new_tag_tok);

        // RHS must be a SINGLE-field anonymous struct literal — that
        // distinguishes a tagged-union variant init (`.{ .Variant =
        // payload }`) from a plain struct literal with multiple
        // fields (`.{ .a = ..., .b = ... }`).  Plain struct literals
        // don't have the tag-flip-then-eval-RHS hazard.
        if (literalHasTopLevelComma(tags, t + 1, last)) continue;

        // LHS path: walk back from t-1 across `.<ident>.<ident>...`.
        var lhs_end: Ast.TokenIndex = t;
        if (lhs_end == 0) continue;
        lhs_end -= 1;
        if (tags[lhs_end] != .identifier) continue;
        var lhs_start: Ast.TokenIndex = lhs_end;
        while (lhs_start >= 2 and tags[lhs_start - 1] == .period and tags[lhs_start - 2] == .identifier) {
            lhs_start -= 2;
        }
        // Stop scanning before reaching the start of the body — make
        // sure the LHS we extracted is preceded by a statement
        // boundary (`{`, `;`, `}`, `else`, `=>`, etc.), not by
        // another part of an expression.
        if (lhs_start > first) {
            const prev = tags[lhs_start - 1];
            // Conservative: allow only common statement-start tokens.
            const ok = prev == .semicolon or prev == .l_brace or
                prev == .r_brace or prev == .keyword_return or
                prev == .equal_angle_bracket_right or prev == .pipe;
            if (!ok) continue;
        }

        // Find matching `}` of the outer struct literal.
        const rbrace = matchBrace(tags, t + 2, last) orelse continue;

        // Scan inside `.{ ... }` for `<LHS path> . <OldTag>` where
        // `OldTag != new_tag`.
        var u: Ast.TokenIndex = t + 6;
        while (u <= rbrace) : (u += 1) {
            if (!pathMatches(tree, u, lhs_start, lhs_end)) continue;
            const after = u + (lhs_end - lhs_start) + 1;
            if (after + 1 > rbrace) continue;
            if (tags[after] != .period) continue;
            if (tags[after + 1] != .identifier) continue;
            const old_tag_tok = after + 1;
            const old_tag = tree.tokenSlice(old_tag_tok);
            if (std.mem.eql(u8, old_tag, new_tag)) continue;
            // Skip when the "OldTag" is actually a method call —
            // `<path>.toOwnedSlice(...)`, `<path>.fmt(...)`, etc.
            // These are not union variants.
            if (after + 2 <= last and tags[after + 2] == .l_paren) continue;
            // Skip when the OldTag access is `.len` / `.ptr` — slice
            // field accesses, not union variants.  Conservative
            // allowlist of common non-tag suffixes that would
            // otherwise FP.
            if (isFieldAccessNotTag(old_tag)) continue;
            try report(gpa, problems, tree, old_tag_tok, new_tag);
            break;
        }
        t = rbrace;
    }
}

/// True iff the anonymous literal at `period_tok` (= `.` followed
/// by `{`) has MORE THAN ONE top-level field — `.{ .a = …, .b = … }`.
/// Single-field literals (canonical union variant init) and
/// single-field-with-trailing-comma return false.  Counts `.<ident>
/// =` openings at outer-brace depth 0.
fn literalHasTopLevelComma(
    tags: []const std.zig.Token.Tag,
    period_tok: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (period_tok + 1 > last) return false;
    if (tags[period_tok + 1] != .l_brace) return false;
    const rbrace = matchBrace(tags, period_tok + 1, last) orelse return false;
    var paren: u32 = 0;
    var brace: u32 = 0;
    var bracket: u32 = 0;
    var fields: u32 = 0;
    var t: Ast.TokenIndex = period_tok + 2;
    while (t + 2 < rbrace) : (t += 1) {
        switch (tags[t]) {
            .l_paren => paren += 1,
            .r_paren => if (paren > 0) {
                paren -= 1;
            },
            .l_brace => brace += 1,
            .r_brace => if (brace > 0) {
                brace -= 1;
            },
            .l_bracket => bracket += 1,
            .r_bracket => if (bracket > 0) {
                bracket -= 1;
            },
            .period => if (paren == 0 and brace == 0 and bracket == 0) {
                // Field opener `.<ident> =`.
                if (tags[t + 1] == .identifier and tags[t + 2] == .equal) {
                    fields += 1;
                    if (fields > 1) return true;
                }
            },
            else => {},
        }
    }
    return false;
}

/// True iff the field name is a known non-tag field access (slice
/// methods, common struct fields).  Used to suppress FPs where the
/// LHS is a non-union struct.
fn isFieldAccessNotTag(name: []const u8) bool {
    return std.mem.eql(u8, name, "len") or
        std.mem.eql(u8, name, "ptr") or
        std.mem.eql(u8, name, "items") or
        std.mem.eql(u8, name, "capacity");
}

/// True iff the token sequence `[start, start + (path_end -
/// path_start)]` matches the token sequence `[path_start, path_end]`
/// (identifier text and tag).
fn pathMatches(
    tree: *const Ast,
    start: Ast.TokenIndex,
    path_start: Ast.TokenIndex,
    path_end: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    const len = path_end - path_start + 1;
    var i: u32 = 0;
    while (i < len) : (i += 1) {
        if (tags[start + i] != tags[path_start + i]) return false;
        if (tags[start + i] == .identifier) {
            if (!std.mem.eql(u8, tree.tokenSlice(start + i), tree.tokenSlice(path_start + i))) return false;
        }
    }
    return true;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    old_tag_tok: Ast.TokenIndex,
    new_tag: []const u8,
) !void {
    const old_tag = tree.tokenSlice(old_tag_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "read of `.{s}` payload while assigning new tag `.{s}` to the same union — under Zig's x86_64 self-hosted backend (post-0.15) the active-tag flip happens BEFORE the RHS evaluates; the old payload may be undefined.  Hoist the read into a local before the union assignment",
        .{ old_tag, new_tag },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "tagged-union-retag-with-old-payload-read",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, old_tag_tok),
        .end = try Pos.fromTokenEnd(tree, old_tag_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "tagged-union-retag: TigerBeetle scan_tree.zig pattern fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const State = union(enum) {
        \\    loading_index: struct { key_exclusive_next: u32 = 0 },
        \\    iterating: struct { key_exclusive_next: u32, values: u32 },
        \\};
        \\const Self = struct {
        \\    state: State,
        \\    pub fn advance(self: *Self) void {
        \\        self.state = .{
        \\            .iterating = .{
        \\                .key_exclusive_next = self.state.loading_index.key_exclusive_next,
        \\                .values = 0,
        \\            },
        \\        };
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("tagged-union-retag-with-old-payload-read", problems.items[0].rule_id);
}

test "tagged-union-retag: hoisted read into a local doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const State = union(enum) {
        \\    loading_index: struct { key_exclusive_next: u32 = 0 },
        \\    iterating: struct { key_exclusive_next: u32, values: u32 },
        \\};
        \\const Self = struct {
        \\    state: State,
        \\    pub fn advance(self: *Self) void {
        \\        const key = self.state.loading_index.key_exclusive_next;
        \\        self.state = .{ .iterating = .{ .key_exclusive_next = key, .values = 0 } };
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "tagged-union-retag: same-tag retag doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const State = union(enum) {
        \\    active: struct { count: u32 },
        \\    inactive: void,
        \\};
        \\const Self = struct {
        \\    state: State,
        \\    pub fn bump(self: *Self) void {
        \\        self.state = .{ .active = .{ .count = self.state.active.count + 1 } };
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "tagged-union-retag: different LHS than RHS path doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const State = union(enum) { a: u32, b: u32 };
        \\const Self = struct {
        \\    state: State,
        \\    other: State,
        \\    pub fn copy(self: *Self) void {
        \\        self.state = .{ .b = self.other.a };
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "tagged-union-retag: slice-like fields (.len, .ptr) are not tag accesses" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    buf: []u8,
        \\    state: union(enum) { active: usize, inactive: void },
        \\    pub fn reset(self: *Self) void {
        \\        self.state = .{ .active = self.buf.len };
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
