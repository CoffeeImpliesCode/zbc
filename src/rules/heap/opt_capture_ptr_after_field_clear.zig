//! Inside `if (<recv>.<field>) |*<cap>| { … }`, a local pointer `<ptr>` is
//! derived from `<cap>` (the mutable pointer to the optional payload).
//! The block then contains an inline `<recv>.<field> = …` assignment that
//! destroys or replaces the optional — invalidating the storage `<ptr>`
//! points into.  Any use of `<ptr>` after the assignment is a UAF.
//!
//! Real-world shape: oven-sh/bun#29979 — `clips = &clips_and_vp.*[0]`
//! inside `if (this.clips) |*clips_and_vp|`, then `this.clips = null`
//! (via `flush`; the inline variant is caught here; the callee variant
//! is covered by the CFG's heap-use-after-free rule when FnSummary
//! may_free_fields is available).
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Find `if (<recv>.<field>) |*<cap>| {` — optional mutable capture.
//!   2. Inside the block, find `const/var <ptr> = …` where the RHS
//!      contains `<cap>` — any binding derived from the captured payload.
//!   3. After the ptr binding's `;`, find `<recv>.<field> = …` —
//!      inline field reassignment that invalidates `<cap>`.
//!   4. After the reassignment `;`, find any identifier use of `<ptr>`.
//!   5. Fire at the use of `<ptr>`.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const matchBrace = tokens.matchBrace;
const matchParen = tokens.matchParen;
const findStmtSemicolon = tokens.findStmtSemicolon;
const skipFnDecl = tokens.skipFnDecl;
const findIdentInScope = tokens.findIdentInScope;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "opt-capture-ptr-after-field-clear";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .opt_capture_ptr_after_field_clear)) return;
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

    var t: Ast.TokenIndex = first;
    while (t + 9 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipFnDecl(tags, t, last);
            continue;
        }

        // Pattern: `if ( obj . field ) | * cap | {`
        //   t+0: keyword_if
        //   t+1: l_paren
        //   t+2: identifier(recv)
        //   t+3: period
        //   t+4: identifier(field)
        //   t+5: r_paren
        //   t+6: pipe
        //   t+7: asterisk
        //   t+8: identifier(cap)
        //   t+9: pipe
        // then: l_brace (may not be immediately after; optional else)
        if (tags[t] != .keyword_if) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        if (tags[t + 5] != .r_paren) continue;
        if (tags[t + 6] != .pipe) continue;
        if (tags[t + 7] != .asterisk) continue;
        if (tags[t + 8] != .identifier) continue;
        if (tags[t + 9] != .pipe) continue;

        const recv = tree.tokenSlice(t + 2);
        const field = tree.tokenSlice(t + 4);
        const cap = tree.tokenSlice(t + 8);

        // Find the `{` that starts the if-body (skipping optional type annotation).
        var body_start: Ast.TokenIndex = t + 10;
        while (body_start <= last and tags[body_start] != .l_brace) : (body_start += 1) {}
        if (body_start > last) continue;
        const body_end = matchBrace(tags, body_start, last) orelse continue;

        // Walk inside the if-block for pointer bindings derived from `cap`.
        try checkBlock(gpa, tree, body_start + 1, body_end, recv, field, cap, problems);

        // Advance past the block to avoid nested re-scanning.
        t = body_end;
    }
}

/// Within `[block_start, block_end)`, look for:
///   - A `const/var <ptr> = …` binding whose RHS contains `cap`.
///   - After that, `recv.field = …` (field reassignment).
///   - After that, any use of `ptr`.
fn checkBlock(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    block_start: Ast.TokenIndex,
    block_end: Ast.TokenIndex,
    recv: []const u8,
    field: []const u8,
    cap: []const u8,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);

    var t: Ast.TokenIndex = block_start;
    while (t + 3 <= block_end) : (t += 1) {
        // Find `const/var <ptr> = …` binding inside the block.
        const kw_tok = t;
        if (tags[kw_tok] != .keyword_const and tags[kw_tok] != .keyword_var) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;

        const ptr_name = tree.tokenSlice(t + 1);

        // RHS: everything from t+3 until the `;`.
        const rhs_start = t + 3;
        const sc = findStmtSemicolon(tags, rhs_start, block_end) orelse continue;

        // RHS must contain `cap` identifier.
        if (findIdentInRange(tree, rhs_start, sc, cap) == null) continue;

        // From sc+1 to block_end, look for `recv.field = …` assignment.
        const assign_tok = findFieldAssign(tree, sc + 1, block_end, recv, field) orelse continue;

        // Find the `;` ending the field assignment.
        const assign_sc = findStmtSemicolon(tags, assign_tok, block_end) orelse continue;

        // From assign_sc+1 to block_end, look for any use of `ptr`.
        const use_tok = findIdentInScope(tree, assign_sc + 1, block_end, ptr_name) orelse continue;

        try report(gpa, problems, tree, use_tok, ptr_name, recv, field, cap);
    }
}

/// Find an identifier `name` in `[start, end]` at any depth.
fn findIdentInRange(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var t: Ast.TokenIndex = start;
    while (t <= end) : (t += 1) {
        if (tags[t] == .identifier and std.mem.eql(u8, tree.tokenSlice(t), name)) return t;
    }
    return null;
}

/// Find `recv.field = …` assignment in `[start, end]`.
/// Returns the `=` token, or null.
fn findFieldAssign(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
    field: []const u8,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var t: Ast.TokenIndex = start;
    while (t + 3 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field)) continue;
        if (tags[t + 3] != .equal) continue;
        return t + 3;
    }
    return null;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    use_tok: Ast.TokenIndex,
    ptr_name: []const u8,
    recv: []const u8,
    field: []const u8,
    cap: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` is derived from `{s}` (the payload pointer of `{s}.{s}`), but `{s}.{s}` was reassigned — `{s}` now points into freed/invalid storage",
        .{ ptr_name, cap, recv, field, recv, field, ptr_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, use_tok),
        .end = try Pos.fromTokenEnd(tree, use_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "opt-capture-ptr-after-field-clear: interior ptr then field = null fires" {
    try testing.expectFires(check, R,
        \\const Clips = struct {
        \\    pub fn deinit(_: *Clips, _: u32) void {}
        \\};
        \\const Self = struct {
        \\    clips: ?[2]Clips = null,
        \\};
        \\pub fn buggy(self: *Self, alloc: u32) void {
        \\    if (self.clips) |*cap| {
        \\        var clips = &cap.*[0];
        \\        self.clips = null;
        \\        clips.deinit(alloc);
        \\    }
        \\}
        \\
    );
}

test "opt-capture-ptr-after-field-clear: use before field clear doesn't fire" {
    try testing.expectNoFire(check,
        \\const Clips = struct {
        \\    pub fn deinit(_: *Clips, _: u32) void {}
        \\};
        \\const Self = struct {
        \\    clips: ?[2]Clips = null,
        \\};
        \\pub fn safe(self: *Self, alloc: u32) void {
        \\    if (self.clips) |*cap| {
        \\        var clips = &cap.*[0];
        \\        clips.deinit(alloc);   // use BEFORE clear — safe
        \\        self.clips = null;
        \\    }
        \\}
        \\
    );
}

test "opt-capture-ptr-after-field-clear: no field clear, no fire" {
    try testing.expectNoFire(check,
        \\const Self = struct { data: ?u32 = null };
        \\pub fn ok(self: *Self) void {
        \\    if (self.data) |*cap| {
        \\        var ptr = &cap.*;
        \\        _ = ptr;
        \\    }
        \\}
        \\
    );
}

test "opt-capture-ptr-after-field-clear: non-ptr capture |cap| doesn't fire" {
    try testing.expectNoFire(check,
        \\const Self = struct { data: ?u32 = null };
        \\pub fn ok(self: *Self) void {
        \\    if (self.data) |cap| {
        \\        _ = cap;
        \\        self.data = null;
        \\    }
        \\}
        \\
    );
}

test "opt-capture-ptr-after-field-clear: ptr not from cap doesn't fire" {
    try testing.expectNoFire(check,
        \\const T = struct { pub fn deinit(_: *T) void {} };
        \\const Other = struct { x: T = .{} };
        \\const Self = struct { data: ?u32 = null };
        \\pub fn ok(self: *Self, other: *Other) void {
        \\    if (self.data) |*cap| {
        \\        _ = cap;
        \\        var ptr = &other.x;
        \\        self.data = null;
        \\        ptr.deinit();
        \\    }
        \\}
        \\
    );
}
