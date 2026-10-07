//! Detects the pattern where a boolean flag (`<recv>.<field>`) whose name
//! contains `"in_progress"` is set to `true`, a method call is made that
//! may re-entrantly set the flag to `true` again, and then the flag is
//! unconditionally reset to `false` — clobbering the re-entrant update.
//!
//! Real-world shape: oven-sh/bun#29899 — `this.write_in_progress = true`
//! early in a write path; `this.emitError(err)` may re-enter and set
//! `this.write_in_progress = true` again; the line
//! `this.write_in_progress = false` after the call clobbers the re-entrant
//! setting, leaving cleanup code free to destroy native state while the
//! re-entrant write is still in flight.
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Find `<recv>.<field> = true` where `field` contains `"in_progress"`.
//!   2. Find the `;` after this (set_sc).
//!   3. Forward-scan from `set_sc+1` for `<recv>.<field> = false` with the
//!      same recv and field names (false_tok).
//!   4. In the range `[set_sc+1, false_tok)`, look for any `.method(` token
//!      sequence (period + identifier + l_paren) — a method call that may
//!      trigger re-entrant code.
//!   5. If a method call is found between the `= true` and `= false`
//!      statements, fire at the `= false` assignment token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const findStmtSemicolon = tokens.findStmtSemicolon;
const skipFnDecl = tokens.skipFnDecl;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "flag-reset-after-callback";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .flag_reset_after_callback)) return;
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
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipFnDecl(tags, t, last);
            continue;
        }

        // Pattern: `recv . field = true`
        //   t+0: identifier(recv)
        //   t+1: period
        //   t+2: identifier(field)
        //   t+3: equal
        //   t+4: keyword_true
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .equal) continue;
        if (tags[t + 4] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 4), "true")) continue;

        const recv = tree.tokenSlice(t);
        const field = tree.tokenSlice(t + 2);

        // Field name must contain "in_progress".
        if (std.mem.indexOf(u8, field, "in_progress") == null) continue;
        // Basic sanity: recv and field must be different tokens.
        if (std.mem.eql(u8, recv, field)) continue;

        // Find the `;` that terminates the `= true` statement.
        const set_sc = findStmtSemicolon(tags, t + 4, last) orelse continue;

        // Forward-scan for the matching `recv.field = false`.
        const false_tok = findFieldSetFalse(tree, set_sc + 1, last, recv, field) orelse continue;

        // Check for any `.method(` in the range [set_sc+1, false_tok).
        if (!hasMethodCall(tags, set_sc + 1, false_tok -| 1)) continue;

        try report(gpa, problems, tree, false_tok, recv, field);
    }
}

/// Find `recv.field = false` in `[start, end]`.
/// Returns the token index of the `false` keyword, or null.
fn findFieldSetFalse(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
    field: []const u8,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var t: Ast.TokenIndex = start;
    while (t + 4 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field)) continue;
        if (tags[t + 3] != .equal) continue;
        if (tags[t + 4] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 4), "false")) continue;
        return t + 4;
    }
    return null;
}

/// Returns true if there is any `.method(` sequence (period + identifier +
/// l_paren) in `[start, end]` — indicating a method call that may trigger
/// re-entrant code.
fn hasMethodCall(tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    if (start > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] == .period and
            tags[t + 1] == .identifier and
            tags[t + 2] == .l_paren) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    false_tok: Ast.TokenIndex,
    recv: []const u8,
    field: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "field `{s}.{s}` is cleared AFTER a function call that may trigger re-entrant access; if the call sets `{s}.{s} = true` again, this `false` assignment clobbers it — clear the flag before the call",
        .{ recv, field, recv, field },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, false_tok),
        .end = try Pos.fromTokenEnd(tree, false_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "flag-reset-after-callback: set true, call, set false fires" {
    try testing.expectFires(check, R,
        \\const Self = struct {
        \\    write_in_progress: bool = false,
        \\    pub fn buggy(this: *Self) void {
        \\        this.write_in_progress = true;
        \\        this.doSomething();
        \\        this.write_in_progress = false;
        \\    }
        \\    pub fn doSomething(this: *Self) void { _ = this; }
        \\};
        \\
    );
}

test "flag-reset-after-callback: cleared BEFORE call doesn't fire" {
    try testing.expectNoFire(check,
        \\const Self = struct {
        \\    write_in_progress: bool = false,
        \\    pub fn safe(this: *Self) void {
        \\        this.write_in_progress = true;
        \\        this.write_in_progress = false;
        \\        this.doSomething();
        \\    }
        \\    pub fn doSomething(this: *Self) void { _ = this; }
        \\};
        \\
    );
}

test "flag-reset-after-callback: no method call between set and clear doesn't fire" {
    try testing.expectNoFire(check,
        \\const Self = struct {
        \\    write_in_progress: bool = false,
        \\    pub fn ok(this: *Self) void {
        \\        this.write_in_progress = true;
        \\        this.write_in_progress = false;
        \\    }
        \\};
        \\
    );
}

test "flag-reset-after-callback: field without in_progress doesn't fire" {
    try testing.expectNoFire(check,
        \\const Self = struct {
        \\    count: bool = false,
        \\    pub fn ok(this: *Self) void {
        \\        this.count = true;
        \\        this.doSomething();
        \\        this.count = false;
        \\    }
        \\    pub fn doSomething(this: *Self) void { _ = this; }
        \\};
        \\
    );
}
