//! `<recv>.<addref>()` call immediately before `init(<recv>, …)` —
//! the caller bumps the refcount by 1, but the `init`-style callee
//! takes ownership and decrements exactly once.  The extra ref is never
//! balanced: the object's refcount never reaches zero and it leaks.
//!
//! Real-world: oven-sh/bun#30137 — `query.ref()` before
//! `MySQLQuery.init(query, allocator, …)`.  The init stored the query
//! and decremented it on cleanup; the extra `.ref()` was never released.
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Walk the fn body for zero-arg `<recv>.<addref>()` calls where
//!      addref ∈ {ref, retain, reference, addRef, addref}.
//!   2. Capture `<recv>` and the statement's terminating `;`.
//!   3. Scan forward for `init(<recv>,` or `init(<recv>)` — any `init(`
//!      call whose first argument is exactly `<recv>`.
//!   4. If `[addref_sc + 1, init_tok)` contains `<recv>.<release>(`
//!      (release ∈ release/deref/unref/removeRef), skip — the inline
//!      release balances the bump.
//!   5. If `[addref_sc + 1, body_last]` contains a `defer`/`errdefer`
//!      whose body includes `<recv>.<release>(`, skip — the author is
//!      explicitly managing the lifecycle balance.
//!   6. Fire at the addref call site.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const testing = @import("../../testing.zig");

const matchBrace = tokens.matchBrace;
const matchParen = tokens.matchParen;
const findStmtSemicolon = tokens.findStmtSemicolon;
const skipDeferStmt = tokens.skipDeferStmt;
const skipFnDecl = tokens.skipFnDecl;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "ref-before-ownership-transfer";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .ref_before_ownership_transfer)) return;
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
        // Skip nested fn declarations entirely.
        if (tags[t] == .keyword_fn) {
            t = skipFnDecl(tags, t, last);
            continue;
        }

        // Pattern: identifier(recv) . identifier(addref) ( ) ;
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!isAddrefMethodName(tree.tokenSlice(t + 2))) continue;
        if (tags[t + 3] != .l_paren) continue;
        if (tags[t + 4] != .r_paren) continue; // zero-arg only

        const recv = tree.tokenSlice(t);
        const addref_tok = t + 2;

        const sc = findStmtSemicolon(tags, t + 4, last) orelse continue;

        // Scan forward for `init(recv,…)` or `init(recv)`.
        const init_tok = findInitWithFirstArg(tree, sc + 1, last, recv) orelse continue;

        // Inline release between addref and init — intentional balance.
        if (rangeHasRecvRelease(tree, sc + 1, init_tok, recv)) continue;

        // defer/errdefer containing a release of recv anywhere after
        // the addref — author is managing the lifecycle explicitly.
        if (bodyHasRecvReleaseDeferOrErrdefer(tree, sc + 1, last, recv)) continue;

        try report(gpa, problems, tree, addref_tok, recv);
    }
}

fn isAddrefMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "ref") or
        method_names.isAcquireMethodName(name);
}

/// Find the first `init(` token in `[start, last]` whose first
/// argument is exactly the identifier `recv`.  Returns the `init`
/// identifier token, or null.
fn findInitWithFirstArg(
    tree: *const Ast,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    recv: []const u8,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (start > last) return null;
    var t: Ast.TokenIndex = start;
    while (t + 1 <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "init")) continue;
        if (tags[t + 1] != .l_paren) continue;
        const lp = t + 1;
        const rp = matchParen(tags, lp, last) orelse continue;
        if (firstArgIsIdent(tree, lp, rp, recv)) return t;
    }
    return null;
}

/// True iff the first argument in the call `(lp … rp)` is a lone
/// identifier with text `name` — i.e. `name` followed immediately
/// by `,` or `)`.
fn firstArgIsIdent(
    tree: *const Ast,
    lp: Ast.TokenIndex,
    rp: Ast.TokenIndex,
    name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    const a = lp + 1;
    if (a >= rp) return false;
    if (tags[a] != .identifier) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(a), name)) return false;
    const nxt = a + 1;
    if (nxt > rp) return true;
    return tags[nxt] == .comma or tags[nxt] == .r_paren;
}

/// True iff `[start, end)` contains `<recv>.<release>(` — an inline
/// release of the bumped reference before the init call.
fn rangeHasRecvRelease(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start >= end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 3 < end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!method_names.isReleaseMethodName(tree.tokenSlice(t + 2))) continue;
        if (tags[t + 3] != .l_paren) continue;
        return true;
    }
    return false;
}

/// True iff any `defer`/`errdefer` statement in `[start, last]`
/// contains `<recv>.<release>(` in its body.
fn bodyHasRecvReleaseDeferOrErrdefer(
    tree: *const Ast,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    recv: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t <= last) : (t += 1) {
        if (tags[t] != .keyword_defer and tags[t] != .keyword_errdefer) continue;
        // Skip optional `|err|` capture after `errdefer`.
        var body_start = t + 1;
        if (body_start <= last and tags[body_start] == .pipe) {
            var p = body_start + 1;
            while (p <= last and tags[p] != .pipe) : (p += 1) {}
            if (p > last) return false;
            body_start = p + 1;
        }
        if (body_start > last) return false;
        const body_end = if (tags[body_start] == .l_brace)
            (matchBrace(tags, body_start, last) orelse last)
        else
            (findStmtSemicolon(tags, body_start, last) orelse last);
        if (rangeHasRecvRelease(tree, body_start, body_end + 1, recv)) return true;
        t = body_end;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    addref_tok: Ast.TokenIndex,
    recv: []const u8,
) !void {
    const method = tree.tokenSlice(addref_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s}()` bumps the refcount, but `{s}` is immediately passed to `init(...)` which takes ownership and decrements once — the extra ref leaks",
        .{ recv, method, recv },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, addref_tok),
        .end = try Pos.fromTokenEnd(tree, addref_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "ref-before-ownership-transfer: ref then init fires" {
    try testing.expectFires(check, R,
        \\const Query = struct {
        \\    pub fn ref(_: *Query) void {}
        \\    pub fn deref(_: *Query) void {}
        \\    pub fn init(_: *Query, _: u32) void {}
        \\};
        \\pub fn setup(query: *Query) void {
        \\    query.ref();
        \\    Query.init(query, 42);
        \\}
        \\
    );
}

test "ref-before-ownership-transfer: retain variant fires" {
    try testing.expectFires(check, R,
        \\const Obj = struct {
        \\    pub fn retain(_: *Obj) void {}
        \\    pub fn release(_: *Obj) void {}
        \\    pub fn init(_: *Obj, _: u8) void {}
        \\};
        \\pub fn build(obj: *Obj) void {
        \\    obj.retain();
        \\    Obj.init(obj, 1);
        \\}
        \\
    );
}

test "ref-before-ownership-transfer: inline deref between ref and init suppresses" {
    try testing.expectNoFire(check,
        \\const Query = struct {
        \\    pub fn ref(_: *Query) void {}
        \\    pub fn deref(_: *Query) void {}
        \\    pub fn init(_: *Query, _: u32) void {}
        \\};
        \\pub fn setup(query: *Query) void {
        \\    query.ref();
        \\    query.deref();
        \\    Query.init(query, 42);
        \\}
        \\
    );
}

test "ref-before-ownership-transfer: defer deref suppresses" {
    try testing.expectNoFire(check,
        \\const Query = struct {
        \\    pub fn ref(_: *Query) void {}
        \\    pub fn deref(_: *Query) void {}
        \\    pub fn init(_: *Query, _: u32) void {}
        \\};
        \\pub fn setup(query: *Query) void {
        \\    query.ref();
        \\    defer query.deref();
        \\    Query.init(query, 42);
        \\}
        \\
    );
}

test "ref-before-ownership-transfer: ref without following init doesn't fire" {
    try testing.expectNoFire(check,
        \\const Obj = struct {
        \\    pub fn ref(_: *Obj) void {}
        \\    pub fn deref(_: *Obj) void {}
        \\};
        \\pub fn keep(obj: *Obj) void {
        \\    obj.ref();
        \\    _ = obj;
        \\}
        \\
    );
}

test "ref-before-ownership-transfer: init with different first arg doesn't fire" {
    try testing.expectNoFire(check,
        \\const Query = struct {
        \\    pub fn ref(_: *Query) void {}
        \\    pub fn init(_: *Query, _: u32) void {}
        \\};
        \\const Other = struct { v: u32 };
        \\pub fn setup(query: *Query, other: *Other) void {
        \\    query.ref();
        \\    Other.init(other, 99);
        \\}
        \\
    );
}

test "ref-before-ownership-transfer: reference variant fires" {
    try testing.expectFires(check, R,
        \\const Node = struct {
        \\    pub fn reference(_: *Node) void {}
        \\    pub fn release(_: *Node) void {}
        \\    pub fn init(_: *Node, _: i32) void {}
        \\};
        \\pub fn link(node: *Node) void {
        \\    node.reference();
        \\    Node.init(node, 7);
        \\}
        \\
    );
}
