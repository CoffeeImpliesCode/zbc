//! Detects functions registered as at-exit callbacks (via add_exit_callback,
//! addExitCallback, etc.) whose body accesses mutable state via `self.`
//! field accesses without a `is_main_thread()` / `isMainThread()` /
//! `isCLIThread()` guard.  When process exit is triggered from a worker
//! thread, the callback runs there and races with main-thread teardown.
//!
//! Real-world shape: oven-sh/bun#31376.
//!
//! Detection (Tier 1 token walk):
//!   1. Scan each fn body for bare calls `NAME(...)` where NAME matches
//!      isExitCallbackRegisterName and the argument is a single identifier.
//!   2. Look up the argument NAME as a top-level fn in this file via
//!      cache.summaryByName.  If not found → skip (can't inspect body).
//!   3. Find NAME's body (via FnDeclIter) and check:
//!      a. Does it contain `self.` or `this.` field access?
//!      b. Does it contain a call to is_main_thread / isMainThread / isCLIThread?
//!   4. Fire at the registration call site if (a) and NOT (b).

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const method_names = @import("../../model/method_names.zig");
const budget_mod = @import("../../budget.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "exit-callback-cross-thread";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .exit_callback_cross_thread)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    _: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Pattern: bare call `REGISTER_NAME ( CALLBACK_NAME )`
        //   t+0: identifier with isExitCallbackRegisterName text
        //   t+1: l_paren
        //   t+2: identifier (the callback fn name)
        //   t+3: r_paren
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_paren) continue;
        // Must not be preceded by `.` — bare call only.
        if (t > first and tags[t - 1] == .period) continue;

        const register_name = tree.tokenSlice(t);
        if (!method_names.isExitCallbackRegisterName(register_name)) continue;

        // Check argument: single identifier.
        if (t + 3 > last) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .r_paren) continue;

        const callback_name = tree.tokenSlice(t + 2);

        // Look up callback_name as a top-level fn in this file.
        // If not present we can't inspect — skip.  A summary that ran out of
        // budget is not an absent one: it propagates, so a callback the
        // analysis could not finish reading never reads as one that was
        // cleared.
        _ = (try cache.summaryByName(callback_name)) orelse continue;

        // Find the actual fn body of callback_name to inspect.
        const cb_body = findFnBody(tree, callback_name) orelse continue;
        const cb_first = tree.firstToken(cb_body);
        const cb_last = tree.lastToken(cb_body);

        // Does the callback body access self/this fields?
        if (!hasSelfFieldAccess(tags, tree, cb_first, cb_last)) continue;

        // Does it have a thread guard?
        if (hasThreadGuard(tags, tree, cb_first, cb_last)) continue;

        // Fire at the registration call token (the register fn name).
        try report(gpa, problems, tree, t, callback_name);
    }
}

/// Find the body node of a top-level fn named `name`.
fn findFnBody(tree: *const Ast, name: []const u8) ?Ast.Node.Index {
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |entry| {
        if (std.mem.eql(u8, tree.tokenSlice(entry.name_token), name)) {
            return entry.body;
        }
    }
    return null;
}

/// True iff `[first, last]` contains `self.FIELD` or `this.FIELD` —
/// identifier("self" or "this") + period + identifier.
fn hasSelfFieldAccess(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (first + 2 > last) return false;
    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        const ident = tree.tokenSlice(t);
        if (!std.mem.eql(u8, ident, "self") and !std.mem.eql(u8, ident, "this")) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        return true;
    }
    return false;
}

/// True iff `[first, last]` contains a call to a main-thread guard:
/// `is_main_thread(`, `isMainThread(`, or `isCLIThread(`.
fn hasThreadGuard(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (first + 1 > last) return false;
    var t: Ast.TokenIndex = first;
    while (t + 1 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_paren) continue;
        const name = tree.tokenSlice(t);
        if (isMainThreadGuardName(name)) return true;
    }
    return false;
}

fn isMainThreadGuardName(name: []const u8) bool {
    return std.mem.eql(u8, name, "is_main_thread") or
        std.mem.eql(u8, name, "isMainThread") or
        std.mem.eql(u8, name, "isCLIThread") or
        std.mem.eql(u8, name, "isMainCLIThread");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    call_tok: Ast.TokenIndex,
    callback_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` is registered as an at-exit callback — if process exit is triggered from a non-main thread, this function runs there and may race with main-thread state; add `if (!is_main_thread()) return;` guard",
        .{callback_name},
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, call_tok),
        .end = try Pos.fromTokenEnd(tree, call_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "exit-callback-cross-thread: add_exit_callback with unguarded self access fires" {
    try testing.expectFires(check, R,
        \\fn cleanup(self: *State) void {
        \\    self.context = 0;
        \\}
        \\pub fn setup(self: *State) void {
        \\    add_exit_callback(cleanup);
        \\}
        \\
    );
}

test "exit-callback-cross-thread: callback with is_main_thread guard doesn't fire" {
    try testing.expectNoFire(check,
        \\fn cleanup(self: *State) void {
        \\    if (!is_main_thread()) return;
        \\    self.context = 0;
        \\}
        \\pub fn setup(self: *State) void {
        \\    add_exit_callback(cleanup);
        \\}
        \\
    );
}

test "exit-callback-cross-thread: callback not defined in this file doesn't fire" {
    try testing.expectNoFire(check,
        \\pub fn init() void {
        \\    add_exit_callback(externalCleanup);
        \\}
        \\
    );
}

test "exit-callback-cross-thread: method call add_exit_callback doesn't fire" {
    // `self.add_exit_callback(cb)` — preceded by `.`, rule skips method calls.
    try testing.expectNoFire(check,
        \\fn cleanup(self: *State) void {
        \\    self.ctx = 0;
        \\}
        \\pub fn init(self: *Handler) void {
        \\    self.add_exit_callback(cleanup);
        \\}
        \\
    );
}

test "exit-callback-cross-thread: callback with no self field access doesn't fire" {
    // Callback only touches a global/static, not instance state — no race.
    try testing.expectNoFire(check,
        \\var g_done: bool = false;
        \\fn cleanup() void {
        \\    g_done = true;
        \\}
        \\pub fn setup() void {
        \\    add_exit_callback(cleanup);
        \\}
        \\
    );
}

test "exit-callback-cross-thread: isMainThread guard doesn't fire" {
    // camelCase variant of the guard name.
    try testing.expectNoFire(check,
        \\fn cleanup(self: *State) void {
        \\    if (!isMainThread()) return;
        \\    self.context = 0;
        \\}
        \\pub fn setup(self: *State) void {
        \\    add_exit_callback(cleanup);
        \\}
        \\
    );
}

test "exit-callback-cross-thread: a callback summary that exhausts its budget is an error, not a clean pass" {
    const gpa = std.testing.allocator;
    // The callback body nests deeper than one normal-cleanup proof may follow,
    // so reading its summary gives up.  Treating that as "no summary" would
    // clear a callback the analysis never finished reading.
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    try source.appendSlice(gpa, "fn cleanup(self: *State) void {\n");
    for (0..80) |_| try source.appendSlice(gpa, "{");
    try source.appendSlice(gpa, "self.context = 0;");
    for (0..80) |_| try source.appendSlice(gpa, "}");
    try source.appendSlice(gpa, "\n}\npub fn setup(self: *State) void {\n    add_exit_callback(cleanup);\n}\n");
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, testing.runRule(gpa, check, source.items));
    const diagnostic = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.normal_cleanup_depth, diagnostic.limit);
}
