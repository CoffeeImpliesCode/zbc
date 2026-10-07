//! Detects a lock acquired and then leaked on an early-exit path: the
//! function unlocks the same receiver later, but a `return` or `try`
//! between the `lock()` and that `unlock()` can exit the function with
//! the lock still held — the next acquirer then deadlocks.
//!
//!   m.lock();
//!   const v = try parse(x);   // ← on error, returns WITH the lock held
//!   m.unlock();
//!   return v;
//!
//!   m.lock();
//!   if (bad) return error.X;  // ← early return skips the unlock below
//!   work();
//!   m.unlock();
//!
//! The safe idiom is `m.lock(); defer m.unlock();` — `defer` releases on
//! every exit (normal, error, early return), so a `defer <recv>.unlock()`
//! after the lock suppresses this rule.
//!
//! Real-world shape: the missing-`defer` lock leak is a recurring deadlock
//! source in critical sections that grew an early `return`/`try`.
//!
//! Detection (Tier 1, token walk):
//!   1. Find `<recv> . lock|lockShared ( )`.
//!   2. Skip if a `defer <recv>.unlock*()` follows it (covers all exits).
//!   3. Find the first manual `<recv>.unlock*()` after the lock.  If there
//!      is NONE, the function hands the lock back to its caller (a
//!      lock/unlock split) — do NOT fire (avoids that false positive).
//!   4. If a `return` or `try` appears between the lock and that unlock,
//!      the early exit bypasses it → fire at the lock.

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
const R = "lock-held-across-early-exit";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .lock_held_across_early_exit)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
}

fn isLockMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "lock") or std.mem.eql(u8, name, "lockShared");
}
fn isUnlockMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "unlock") or std.mem.eql(u8, name, "unlockShared");
}

/// `<recv> . <method> (` at token `t`, with `pred(method)` true.
fn methodCallAt(tree: *const Ast, tags: []const std.zig.Token.Tag, t: Ast.TokenIndex, end: Ast.TokenIndex, recv: []const u8, comptime pred: fn ([]const u8) bool) bool {
    if (t + 3 >= end) return false;
    if (tags[t] != .identifier) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) return false;
    if (tags[t + 1] != .period) return false;
    if (tags[t + 2] != .identifier) return false;
    if (tags[t + 3] != .l_paren) return false;
    return pred(tree.tokenSlice(t + 2));
}

/// A `defer <recv>.unlock*()` (optionally `defer { … }`) in [start, end).
fn hasDeferUnlock(tree: *const Ast, tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, end: Ast.TokenIndex, recv: []const u8) bool {
    var t = start;
    while (t < end) : (t += 1) {
        if (tags[t] != .keyword_defer) continue;
        var k = t + 1;
        if (k < end and tags[k] == .l_brace) k += 1;
        if (methodCallAt(tree, tags, k, end, recv, isUnlockMethod)) return true;
    }
    return false;
}

/// First manual `<recv>.unlock*()` in [start, end), or null.
fn firstUnlock(tree: *const Ast, tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, end: Ast.TokenIndex, recv: []const u8) ?Ast.TokenIndex {
    var t = start;
    while (t < end) : (t += 1) {
        if (methodCallAt(tree, tags, t, end, recv, isUnlockMethod)) return t;
    }
    return null;
}

/// First `return` / `try` in [start, end_excl) (skipping nested fns), or null.
fn firstEarlyExit(tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, end_excl: Ast.TokenIndex) ?Ast.TokenIndex {
    var t = start;
    while (t < end_excl) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, end_excl);
            continue;
        }
        if (tags[t] == .keyword_return or tags[t] == .keyword_try) return t;
    }
    return null;
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
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Pattern: <recv> . lock|lockShared ( )
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        if (tags[t + 4] != .r_paren) continue;
        if (!isLockMethod(tree.tokenSlice(t + 2))) continue;

        const recv = tree.tokenSlice(t);
        const after = t + 5;

        // Safe idiom: `defer <recv>.unlock()` releases on every exit.
        if (hasDeferUnlock(tree, tags, after, last, recv)) continue;

        // No manual unlock in this fn → lock is handed to the caller; skip.
        const unlock_tok = firstUnlock(tree, tags, after, last, recv) orelse continue;

        // An early exit before that unlock leaks the lock on that path.
        if (firstEarlyExit(tags, after, unlock_tok)) |_| {
            try report(gpa, problems, tree, t, recv);
        }
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    lock_recv_tok: Ast.TokenIndex,
    recv: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.lock()` is released by a later `{s}.unlock()`, but a `return`/`try` in between can exit with the lock still held — leaking it (the next acquirer deadlocks); use `defer {s}.unlock();` right after locking so it releases on every path",
        .{ recv, recv, recv },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, lock_recv_tok),
        .end = try Pos.fromTokenEnd(tree, lock_recv_tok + 4),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "lock-held-across-early-exit: early return before unlock fires" {
    try testing.expectFires(check, R,
        \\fn f(m: *Mutex, bad: bool) !void {
        \\    m.lock();
        \\    if (bad) return error.X;
        \\    work();
        \\    m.unlock();
        \\}
        \\
    );
}

test "lock-held-across-early-exit: `try` before unlock fires" {
    try testing.expectFires(check, R,
        \\fn f(m: *Mutex) !u8 {
        \\    m.lock();
        \\    const v = try parse();
        \\    m.unlock();
        \\    return v;
        \\}
        \\
    );
}

test "lock-held-across-early-exit: defer unlock does NOT fire" {
    try testing.expectNoFire(check,
        \\fn f(m: *Mutex, bad: bool) !void {
        \\    m.lock();
        \\    defer m.unlock();
        \\    if (bad) return error.X;
        \\    work();
        \\}
        \\
    );
}

test "lock-held-across-early-exit: unlock before the return does NOT fire" {
    try testing.expectNoFire(check,
        \\fn f(m: *Mutex, bad: bool) void {
        \\    m.lock();
        \\    if (bad) {
        \\        m.unlock();
        \\        return;
        \\    }
        \\    m.unlock();
        \\}
        \\
    );
}

test "lock-held-across-early-exit: no unlock at all (caller handoff) does NOT fire" {
    try testing.expectNoFire(check,
        \\fn acquire(m: *Mutex) void {
        \\    m.lock();
        \\    return;
        \\}
        \\
    );
}

test "lock-held-across-early-exit: straight-line lock/unlock does NOT fire" {
    try testing.expectNoFire(check,
        \\fn f(m: *Mutex) void {
        \\    m.lock();
        \\    work();
        \\    m.unlock();
        \\}
        \\
    );
}
