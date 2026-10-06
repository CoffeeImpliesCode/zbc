//! Detects `for (<recv>.items) |...| { ... call() ... }` where `call`
//! transitively invokes an ArrayList-grow method (append, resize, etc.),
//! potentially reallocating the backing buffer mid-iteration.  After the
//! reallocation, the for-loop's implicit slice pointer — captured at the
//! start of the first iteration — dangles into freed memory.
//!
//! Real-world shape: oven-sh/bun#29981 — iterating
//! `globalObject.m_pendingNapiModules` while `executePendingNapiModule`
//! can append to it; oven-sh/bun#29483 — `for (dependencies.items)`
//! while `enqueueDependency` can grow the slice.
//!
//! Complements `arraylist-items-slice` (which catches direct same-fn
//! grow calls) and `iterator-invalidation-mutation` (HashMap variant).
//!
//! Detection:
//!   1. For each `for ( <expr> ) |...|` loop, check if the iterated
//!      expression contains `<recv>.items`.
//!   2. Inside the loop body, scan for:
//!      a. Direct grow: `<recv>.<growMethod>(` on the same recv — fire.
//!      b. Bare call: `<fn>( ` (not preceded by `.`) — look up callee
//!         FnSummary; if `may_grow_collections`, fire.
//!   3. Fire at the call token.
//!
//! Requires `FileCache.resolveTransitiveTakes()` to have run so that
//! `may_grow_collections` is transitively propagated through same-file
//! call chains.  `check()` calls it automatically.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const method_names = @import("../../model/method_names.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const matchBrace = tokens.matchBrace;
const matchParen = tokens.matchParen;
const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "slice-loop-reentrant-grow";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .slice_loop_reentrant_grow)) return;
    try cache.resolveTransitiveTakes();
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
        if (tags[t] != .keyword_for) continue;
        if (tags[t + 1] != .l_paren) continue;

        const rp = matchParen(tags, t + 1, last) orelse continue;

        // Look for `<recv>.items` inside the for-condition parens.
        const recv = findItemsRecv(tree, t + 2, rp - 1) orelse continue;

        // Find the loop body `{...}` after the capture `|...|`.
        const body_start = findLoopBody(tags, rp + 1, last) orelse continue;
        const body_end = matchBrace(tags, body_start, last) orelse continue;
        const capture_by_value = loopCaptureByValue(tags, rp + 1, body_start);

        // Scan the loop body for calls that may grow collections.
        try checkLoopBody(
            gpa,
            tree,
            cache,
            body_start + 1,
            body_end - 1,
            recv,
            capture_by_value,
            problems,
        );
    }
}

/// Find `<recv>.items` inside `[start, end]`.  Returns the receiver
/// identifier text, or null if not found.
fn findItemsRecv(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var s: Ast.TokenIndex = start;
    while (s + 2 <= end) : (s += 1) {
        if (tags[s] != .identifier) continue;
        if (tags[s + 1] != .period) continue;
        if (tags[s + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(s + 2), "items")) continue;
        return tree.tokenSlice(s);
    }
    return null;
}

/// Find the `{` that opens the loop body.  Skips the capture `|...|`
/// (including optional second index capture) and optional `else`.
fn findLoopBody(
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?Ast.TokenIndex {
    var s: Ast.TokenIndex = start;
    while (s <= last) : (s += 1) {
        if (tags[s] == .l_brace) return s;
        if (tags[s] == .semicolon) return null;
    }
    return null;
}

/// Return true for a by-value first loop capture (`|item|`), not
/// pointer capture (`|*item|`). Only the former is detached before
/// a collection growth operation.
fn loopCaptureByValue(
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    body_start: Ast.TokenIndex,
) bool {
    var s = start;
    while (s < body_start and tags[s] != .pipe) : (s += 1) {}
    if (s >= body_start) return false;
    s += 1;
    return s < body_start and tags[s] == .identifier;
}

/// Scan `[start, end]` (the loop body interior) for calls that may
/// grow a collection. `recv` is the list being iterated.
fn checkLoopBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
    capture_by_value: bool,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (start > end) return;
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t + 1 <= end) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, end);
            continue;
        }

        // Direct grow: `recv.growMethod(`
        if (tags[t] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t), recv) and
            t + 3 <= end and
            tags[t + 1] == .period and
            tags[t + 2] == .identifier and
            tags[t + 3] == .l_paren)
        {
            const method = tree.tokenSlice(t + 2);
            if (method_names.isArrayListGrowMethodName(method)) {
                if (!(capture_by_value and callImmediatelyReturns(tags, t + 3, end))) {
                    try report(gpa, problems, tree, t + 2, recv, method);
                }
                t += 3;
                continue;
            }
        }

        // Bare function call: `fnName(` not preceded by `.`
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (t > start and tags[t - 1] == .period) continue;

        const callee = tree.tokenSlice(t);
        const summary = (cache.summaryByName(callee) catch null) orelse continue;
        if (!summary.may_grow_collections) continue;

        // Suppress when `recv` doesn't appear anywhere in the call's
        // argument list. If the callee can't reach the iterated
        // collection (it isn't passed as an argument), it cannot
        // reallocate it — the slice pointer remains valid.
        const call_rp = matchParen(tags, t + 1, end) orelse {
            try reportCallee(gpa, problems, tree, t, callee, recv);
            continue;
        };
        if (!identAppearsIn(tree, tags, t + 2, call_rp - 1, recv)) {
            t = call_rp;
            continue;
        }

        if (!(capture_by_value and callImmediatelyReturns(tags, t + 1, end))) {
            try reportCallee(gpa, problems, tree, t, callee, recv);
        }
        t = call_rp;
    }
}

fn identAppearsIn(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) bool {
    if (start > end) return false;
    var s: Ast.TokenIndex = start;
    while (s <= end) : (s += 1) {
        if (tags[s] == .identifier and std.mem.eql(u8, tree.tokenSlice(s), name)) return true;
    }
    return false;
}

/// True when a call, with at most an empty catch block, immediately returns.
fn callImmediatelyReturns(
    tags: []const std.zig.Token.Tag,
    lp: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    if (lp > end or tags[lp] != .l_paren) return false;
    const rp = matchParen(tags, lp, end) orelse return false;
    var next = rp + 1;
    if (next + 2 <= end and
        tags[next] == .keyword_catch and
        tags[next + 1] == .l_brace and
        tags[next + 2] == .r_brace)
    {
        next += 3;
    }
    if (next <= end and tags[next] == .semicolon) next += 1;
    return next <= end and tags[next] == .keyword_return;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    call_tok: Ast.TokenIndex,
    recv: []const u8,
    method: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s}` inside `for ({s}.items)` may reallocate the backing buffer — the loop's implicit slice pointer is invalidated; move the call outside the loop or capture needed data before growing",
        .{ recv, method, recv },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, call_tok),
        .end = Pos.fromTokenEnd(tree, call_tok),
        .message = msg,
    });
}

fn reportCallee(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    call_tok: Ast.TokenIndex,
    callee: []const u8,
    recv: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}(...)` inside `for ({s}.items)` may grow a collection — if it reallocates the iterated slice, the loop's implicit pointer is invalidated; ensure `{s}` cannot grow `{s}` during iteration",
        .{ callee, recv, callee, recv },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, call_tok),
        .end = Pos.fromTokenEnd(tree, call_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "slice-loop-reentrant-grow: direct grow on iterated list fires" {
    try testing.expectFires(check, R,
        \\const List = std.ArrayList(u32);
        \\pub fn buggy(list: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        list.append(99) catch {};
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: bare callee with may_grow fires" {
    try testing.expectFires(check, R,
        \\const List = std.ArrayList(u32);
        \\fn grow(list: *List) void {
        \\    list.append(1) catch {};
        \\}
        \\pub fn buggy(list: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        grow(list);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: grow outside loop doesn't fire" {
    try testing.expectNoFire(check,
        \\const List = std.ArrayList(u32);
        \\pub fn safe(list: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\    }
        \\    list.append(99) catch {};
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: grow on different recv doesn't fire" {
    try testing.expectNoFire(check,
        \\const List = std.ArrayList(u32);
        \\pub fn safe(a: *List, b: *List) void {
        \\    for (a.items) |item| {
        \\        _ = item;
        \\        b.append(99) catch {};
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: may_grow callee not passed recv doesn't fire" {
    try testing.expectNoFire(check,
        \\const List = std.ArrayList(u32);
        \\fn growOther(other: *List) void {
        \\    other.append(1) catch {};
        \\}
        \\pub fn safe(list: *List, other: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        growOther(other);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: may_grow callee passed recv fires" {
    try testing.expectFires(check, R,
        \\const List = std.ArrayList(u32);
        \\fn mayGrow(list: *List, x: u32) void {
        \\    _ = x;
        \\    list.append(1) catch {};
        \\}
        \\pub fn buggy(list: *List) void {
        \\    for (list.items) |item| {
        \\        mayGrow(list, item);
        \\    }
        \\}
        \\
    );
}

test "skript regression: by-value reentrant grow returns before next iteration" {
    try testing.expectNoFire(check,
        \\const List = std.ArrayList(u32);
        \\pub fn take(list: *List) u32 {
        \\    for (list.items) |item| {
        \\        list.append(item) catch {};
        \\        return item;
        \\    }
        \\    return 0;
        \\}
        \\
    );
}

test "skript regression: pointer reentrant grow remains unsafe after return" {
    try testing.expectFires(check, R,
        \\const List = std.ArrayList(u32);
        \\pub fn take(list: *List) u32 {
        \\    for (list.items) |*item| {
        \\        list.append(item.*) catch {};
        \\        return item.*;
        \\    }
        \\    return 0;
        \\}
        \\
    );
}
