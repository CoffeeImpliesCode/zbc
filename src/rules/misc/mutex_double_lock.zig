//! Detects a Mutex (or RwLock / Mutex-like) locked twice on the same
//! receiver without an intervening unlock — a self-deadlock (if the
//! mutex is non-reentrant) or an assertion failure.
//!
//! Zig's `std.Thread.Mutex` is non-reentrant: calling `lock()` while
//! already holding the lock on the same thread deadlocks in Release mode
//! (spins forever) and asserts in Debug (`lock_count == 0` assertion).
//! `std.Thread.RwLock.lock()` / `.lockShared()` have the same property.
//!
//! Pattern (fires):
//!   mutex.lock();
//!   doSomething();
//!   mutex.lock();   // ← BUG: never reached after first lock succeeds
//!
//! Pattern (safe — unlock in between):
//!   mutex.lock();
//!   doSomething();
//!   mutex.unlock();
//!   mutex.lock();   // OK: re-acquired after release
//!
//! Real-world shape: oven-sh/bun#28907 (ThreadPool sync: missing unlock
//! before re-acquire in the notification path, leading to deadlock when
//! the notified thread tried to lock the same sync object).
//!
//! Detection (Tier 1, token walk):
//!   1. Scan fn body for `receiver . lock ( )` or
//!      `receiver . lockShared ( )` (5-token pattern).
//!   2. Record each (receiver_name, lock_tok).
//!   3. For each lock, scan forward in the fn for another lock on the
//!      same receiver before `receiver.unlock()` or
//!      `receiver.unlockShared()` appears.
//!   4. Suppress if `keyword_return` appears between the two locks
//!      (function may exit before reaching the second path).
//!   5. Fire at the SECOND lock token.

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
const R = "mutex-double-lock";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .mutex_double_lock)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
}

const LockSite = struct {
    recv: []const u8,
    lock_tok: Ast.TokenIndex,
};

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var locks: std.ArrayListUnmanaged(LockSite) = .empty;
    defer locks.deinit(gpa);

    // Collect all lock sites in the fn body.
    var t: Ast.TokenIndex = first;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Pattern: identifier . lock ( )
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        if (tags[t + 4] != .r_paren) continue;

        const method = tree.tokenSlice(t + 2);
        if (!isLockMethod(method)) continue;

        try locks.append(gpa, .{
            .recv = tree.tokenSlice(t),
            .lock_tok = t,
        });
    }

    if (locks.items.len < 2) return;

    // For each lock, check if the same receiver is locked again without
    // an unlock between.
    for (locks.items, 0..) |a, i| {
        for (locks.items[i + 1 ..]) |b| {
            if (!std.mem.eql(u8, a.recv, b.recv)) continue;
            // Check that no unlock or return appears between a and b.
            if (hasUnlockOrReturn(tree, tags, a.lock_tok + 5, b.lock_tok, a.recv)) continue;
            try report(gpa, problems, tree, b.lock_tok, a.recv, a.lock_tok);
            break;
        }
    }
}

fn isLockMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "lock") or
        std.mem.eql(u8, name, "lockShared");
}

fn isUnlockMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "unlock") or
        std.mem.eql(u8, name, "unlockShared") or
        std.mem.eql(u8, name, "upgradeShared");
}

/// Returns true iff `receiver.unlock*()` or `keyword_return` appears
/// in [start, end_exclusive).
fn hasUnlockOrReturn(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end_exclusive: Ast.TokenIndex,
    recv: []const u8,
) bool {
    if (start >= end_exclusive) return false;
    var t: Ast.TokenIndex = start;
    while (t + 3 < end_exclusive) : (t += 1) {
        if (tags[t] == .keyword_return) return true;
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        if (isUnlockMethod(tree.tokenSlice(t + 2))) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    second_lock_tok: Ast.TokenIndex,
    recv: []const u8,
    first_lock_tok: Ast.TokenIndex,
) !void {
    _ = first_lock_tok;
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.lock()` called a second time without a preceding `{s}.unlock()` — Zig's `std.Thread.Mutex` is non-reentrant; this deadlocks in release mode (spinning) and asserts in debug (`lock_count == 0`); add `{s}.unlock()` before re-acquiring",
        .{ recv, recv, recv },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, second_lock_tok),
        .end = try Pos.fromTokenEnd(tree, second_lock_tok + 4),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "mutex-double-lock: direct double lock fires" {
    try testing.expectFires(check, R,
        \\fn f(m: *std.Thread.Mutex) void {
        \\    m.lock();
        \\    doWork();
        \\    m.lock();
        \\}
        \\
    );
}

test "mutex-double-lock: unlock between does not fire" {
    try testing.expectNoFire(check,
        \\fn f(m: *std.Thread.Mutex) void {
        \\    m.lock();
        \\    doWork();
        \\    m.unlock();
        \\    m.lock();
        \\    doMoreWork();
        \\    m.unlock();
        \\}
        \\
    );
}

test "mutex-double-lock: different receivers do not fire" {
    try testing.expectNoFire(check,
        \\fn f(a: *std.Thread.Mutex, b: *std.Thread.Mutex) void {
        \\    a.lock();
        \\    b.lock();
        \\    a.unlock();
        \\    b.unlock();
        \\}
        \\
    );
}

test "mutex-double-lock: return between suppresses" {
    try testing.expectNoFire(check,
        \\fn f(m: *std.Thread.Mutex, cond: bool) void {
        \\    m.lock();
        \\    if (cond) {
        \\        m.unlock();
        \\        return;
        \\    }
        \\    m.lock();
        \\}
        \\
    );
}

test "mutex-double-lock: single lock does not fire" {
    try testing.expectNoFire(check,
        \\fn f(m: *std.Thread.Mutex) void {
        \\    m.lock();
        \\    defer m.unlock();
        \\}
        \\
    );
}
