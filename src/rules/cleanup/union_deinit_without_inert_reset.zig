//! Tagged-union switch arm calls `.deinit()` / `.free()` /
//! `.release()` on the payload but doesn't reset the active tag to
//! an inert variant — next time the enclosing fn runs (it's named
//! `reset`/`clear`/`end`-style, i.e. idempotent by convention) the
//! same arm fires and double-frees the already-freed payload.
//!
//! Real-world: ghostty-org/ghostty#2257 / #8307 — both in
//! `src/terminal/osc.zig`, same shape, two PRs apart fixing the
//! same arm and then a sibling arm:
//!
//!   switch (self.command) {
//!       .kitty_color_protocol => |*v| {
//!           v.list.deinit();
//!           // BUG: missing `self.command = .{ .hyperlink_end = {} };`
//!       },
//!       else => {},
//!   }
//!
//! The fn is an `end()` / `reset()` — designed to be called
//! multiple times across the parser's lifetime.  Without the
//! retag, the second call sees the same `.kitty_color_protocol`
//! tag, runs the arm again, and deinits the freed list a second
//! time → assertion or heap corruption.
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Skip comptime type-builder fns.
//!   2. Limit to fn names matching reset/clear/end family.
//!   3. Walk for `switch (<recv>.<field>)` constructs where `<recv>`
//!      is a single identifier (commonly `self` / `this`).
//!   4. Inside the switch body, walk each arm `.<Tag> => [|*v|]
//!      <body>` (block or inline).
//!   5. Within the arm body, find any payload-cleanup call shape
//!      `<v>.<method>(...)` or `<v>.<sub>.<method>(...)` where
//!      `<method>` ∈ {deinit, free, release, deref, destroy, close}.
//!   6. If cleanup found, also require the arm body to contain a
//!      retag `<recv>.<field> = ...` or `<recv>.* = ...`.
//!   7. Fire when cleanup is present but retag is absent.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const testing = @import("../../testing.zig");
const matchBrace = tokens.matchBrace;
const skipNestedFn = tokens.skipNestedFn;
const returnsType = tokens.returnsType;
const fnProto = tokens.fnProto;
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
    if (!config_mod.isEnabled(config, .union_deinit_without_inert_reset)) return;
    _ = cache;

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        if (returnsType(tree, node)) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const fp = fnProto(tree, &buf, node) orelse continue;
        const name_tok = fp.name_token orelse continue;
        if (!isIdempotentResetFn(tree.tokenSlice(name_tok))) continue;
        const body = bodyOf(tree, node) orelse continue;
        try checkBody(gpa, tree, body, problems);
    }
}

/// Fn name patterns for idempotent reset/clear/end methods.  These
/// are the only fns where the bug actually surfaces — `deinit` /
/// `destroy` are single-shot and a missing retag doesn't matter.
fn isIdempotentResetFn(name: []const u8) bool {
    return std.mem.eql(u8, name, "reset") or
        std.mem.eql(u8, name, "clear") or
        std.mem.eql(u8, name, "clearRetainingCapacity") or
        std.mem.eql(u8, name, "end") or
        std.mem.eql(u8, name, "endCommand") or
        std.mem.eql(u8, name, "endOperation") or
        std.mem.eql(u8, name, "finish") or
        std.mem.startsWith(u8, name, "reset") or
        std.mem.startsWith(u8, name, "clear") or
        std.mem.startsWith(u8, name, "end_");
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
    while (t + 6 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_switch) continue;
        if (tags[t + 1] != .l_paren) continue;
        // Switch operand: `<recv>.<field>`.
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        if (tags[t + 5] != .r_paren) continue;
        if (tags[t + 6] != .l_brace) continue;
        const recv = tree.tokenSlice(t + 2);
        const field = tree.tokenSlice(t + 4);
        const sw_body_start = t + 6;
        const sw_body_end = matchBrace(tags, sw_body_start, last) orelse continue;
        // The retag may appear inside the arm body OR anywhere in
        // the same fn body AFTER the switch closes (a common idiom
        // is `switch (self.x) { ... }` then `self.x = .invalid;`).
        // Skip the whole switch if such a post-switch retag exists.
        if (hasRetag(tree, sw_body_end + 1, last, recv, field)) {
            t = sw_body_end;
            continue;
        }
        try checkSwitchBody(gpa, tree, sw_body_start + 1, sw_body_end - 1, recv, field, problems);
        t = sw_body_end;
    }
}

fn checkSwitchBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
    field: []const u8,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        // Find arm `.<Tag> =>`.  Skip `else =>`.
        const tag_tok: Ast.TokenIndex = blk: {
            if (tags[t] == .period and tags[t + 1] == .identifier) {
                break :blk t + 1;
            }
            // We don't fire on `else` arms — they're catch-alls; no
            // specific variant is being deinit'd.
            continue;
        };
        // Find `=>` that follows (may be after comma-list or capture).
        var fa: Ast.TokenIndex = tag_tok + 1;
        while (fa <= end and tags[fa] != .equal_angle_bracket_right) : (fa += 1) {}
        if (fa > end) break;
        // Optional capture `|*v|` or `|v|`.
        var arm_body_start: Ast.TokenIndex = fa + 1;
        var capture_name: ?[]const u8 = null;
        if (arm_body_start <= end and tags[arm_body_start] == .pipe) {
            var p: Ast.TokenIndex = arm_body_start + 1;
            // Optional `*`.
            if (p <= end and tags[p] == .asterisk) p += 1;
            if (p <= end and tags[p] == .identifier) {
                capture_name = tree.tokenSlice(p);
            }
            // Skip to closing `|`.
            while (p <= end and tags[p] != .pipe) : (p += 1) {}
            if (p > end) break;
            arm_body_start = p + 1;
        }
        if (arm_body_start > end) break;
        // Arm body: block or inline.
        const arm_body_end = if (tags[arm_body_start] == .l_brace)
            (matchBrace(tags, arm_body_start, end) orelse break)
        else
            (findArmEnd(tags, arm_body_start, end) orelse break);
        const body_scan_start = if (tags[arm_body_start] == .l_brace)
            arm_body_start + 1
        else
            arm_body_start;
        const body_scan_end = if (tags[arm_body_start] == .l_brace)
            arm_body_end - 1
        else
            arm_body_end;
        if (capture_name) |cap| {
            if (hasCleanupCall(tree, body_scan_start, body_scan_end, cap) and
                !hasRetag(tree, body_scan_start, body_scan_end, recv, field))
            {
                try report(gpa, problems, tree, tag_tok, recv, field);
            }
        }
        t = arm_body_end;
    }
}

const isCleanupMethodName = method_names.isCleanupMethodName;

/// True iff `[start, end]` contains a `<cap>.<cleanup>(...)` or
/// `<cap>.<sub>.<cleanup>(...)` call.
fn hasCleanupCall(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    cap: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 3 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), cap)) continue;
        if (tags[t + 1] != .period) continue;
        // Walk the dotted chain until we hit `(` — the LAST ident
        // before `(` is the method name.
        var u: Ast.TokenIndex = t + 2;
        var last_ident: ?Ast.TokenIndex = null;
        while (u <= end) {
            if (tags[u] == .identifier) {
                last_ident = u;
                u += 1;
                if (u <= end and tags[u] == .period) {
                    u += 1;
                    continue;
                }
                if (u <= end and tags[u] == .l_paren) {
                    if (last_ident) |m| {
                        if (isCleanupMethodName(tree.tokenSlice(m))) return true;
                    }
                    break;
                }
                break;
            }
            break;
        }
    }
    return false;
}

/// True iff `[start, end]` contains an assignment that retags the
/// switch operand: `<recv>.<field> = ...` or `<recv>.* = ...` or
/// `<recv>.<field> = undefined`.
fn hasRetag(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
    field: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        if (tags[t + 1] != .period) continue;
        // `<recv>.* = ...`.
        if (tags[t + 2] == .asterisk) {
            if (t + 3 <= end and tags[t + 3] == .equal) return true;
            continue;
        }
        // `<recv>.<field> = ...`.
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field)) continue;
        if (t + 3 > end) continue;
        if (tags[t + 3] == .equal) return true;
    }
    return false;
}

/// For an inline arm body (no `{`), find the end of the arm — the
/// next `,` at switch-arm depth.
fn findArmEnd(
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?Ast.TokenIndex {
    var paren: u32 = 0;
    var brace: u32 = 0;
    var bracket: u32 = 0;
    var t: Ast.TokenIndex = start;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_paren => paren += 1,
            .r_paren => if (paren > 0) {
                paren -= 1;
            },
            .l_brace => brace += 1,
            .r_brace => if (brace > 0) {
                brace -= 1;
            } else return t - 1,
            .l_bracket => bracket += 1,
            .r_bracket => if (bracket > 0) {
                bracket -= 1;
            },
            .comma => if (paren == 0 and brace == 0 and bracket == 0) return t - 1,
            else => {},
        }
    }
    return null;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    tag_tok: Ast.TokenIndex,
    recv: []const u8,
    field: []const u8,
) !void {
    const tag_name = tree.tokenSlice(tag_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "switch arm `.{s}` deinit'd the payload but didn't retag `{s}.{s}` to an inert variant — this fn looks like an idempotent reset/clear/end; the next call will fire the same arm and double-free.  Add `{s}.{s} = .{{ .<inert_tag> = {{}} }};` after the cleanup",
        .{ tag_name, recv, field, recv, field },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "union-deinit-without-inert-reset",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, tag_tok),
        .end = try Pos.fromTokenEnd(tree, tag_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "union-deinit-without-inert-reset: ghostty osc.zig pattern fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const List = struct { pub fn deinit(_: *List) void {} };
        \\const Command = union(enum) {
        \\    kitty_color_protocol: struct { list: List },
        \\    hyperlink_end: void,
        \\};
        \\const Parser = struct {
        \\    command: Command,
        \\    pub fn end(self: *Parser) void {
        \\        switch (self.command) {
        \\            .kitty_color_protocol => |*v| {
        \\                v.list.deinit();
        \\            },
        \\            else => {},
        \\        }
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("union-deinit-without-inert-reset", problems.items[0].rule_id);
}

test "union-deinit-without-inert-reset: with retag doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const List = struct { pub fn deinit(_: *List) void {} };
        \\const Command = union(enum) {
        \\    kitty_color_protocol: struct { list: List },
        \\    hyperlink_end: void,
        \\};
        \\const Parser = struct {
        \\    command: Command,
        \\    pub fn end(self: *Parser) void {
        \\        switch (self.command) {
        \\            .kitty_color_protocol => |*v| {
        \\                v.list.deinit();
        \\                self.command = .{ .hyperlink_end = {} };
        \\            },
        \\            else => {},
        \\        }
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "union-deinit-without-inert-reset: deinit-named fn (single-shot) skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const List = struct { pub fn deinit(_: *List) void {} };
        \\const Command = union(enum) { kitty_color_protocol: struct { list: List }, hyperlink_end: void };
        \\const Parser = struct {
        \\    command: Command,
        \\    pub fn deinit(self: *Parser) void {
        \\        switch (self.command) {
        \\            .kitty_color_protocol => |*v| v.list.deinit(),
        \\            else => {},
        \\        }
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "union-deinit-without-inert-reset: inline arm body works" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const List = struct { pub fn deinit(_: *List) void {} };
        \\const Command = union(enum) { kitty: struct { list: List }, none: void };
        \\const Parser = struct {
        \\    command: Command,
        \\    pub fn reset(self: *Parser) void {
        \\        switch (self.command) {
        \\            .kitty => |*v| v.list.deinit(),
        \\            else => {},
        \\        }
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "union-deinit-without-inert-reset: arm with no capture skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Command = union(enum) { x: u32, none: void };
        \\const Parser = struct {
        \\    command: Command,
        \\    pub fn reset(self: *Parser) void {
        \\        switch (self.command) {
        \\            .x => doStuff(),
        \\            else => {},
        \\        }
        \\    }
        \\};
        \\fn doStuff() void {}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
