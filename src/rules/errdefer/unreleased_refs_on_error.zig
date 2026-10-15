//! `<chain>.<addref>()` calls (in a loop OR at top level) acquire
//! refcounted references, followed by a later `try` in the same fn
//! with no `defer`/`errdefer` containing a `.release()` / `.deref()`
//! cleanup.  On the try's error path every reference taken leaks.
//!
//! Two real-world shapes:
//!  - Loop shape (hexops/mach `sysgpu/vulkan.zig:1887` —
//!    `PipelineLayout.init`): `for (...) |layout| layout.manager
//!    .reference();` then `try vkd.createPipelineLayout(...);` —
//!    N BindGroupLayout refs leak per error.
//!  - Single-addref shape (oven-sh/bun#29329, #29900, #29901,
//!    #29907 — pendingActivityRef family): `this.pendingActivityRef();`
//!    then `try doSomething();` — single ref leaks per error.
//!
//! Detection:
//!   1. Select non-type-builder functions containing a later `try`.
//!   2. Keep the existing caller-side release-class defer/errdefer guard.
//!      That syntactic guard is not a reference-balance certificate.
//!   3. Find method calls named `reference`, `retain`, `addRef`, `addref`,
//!      or `pendingActivityRef`, at top level or in a loop.
//!   4. For an acquired result, ask whether canonical source evidence links
//!      it to rollback registered in the later fallible callee.
//!   5. Report at the acquisition unless that evidence makes the leak unknown.
//!
//! Related callee rollback is not a reference-balance certificate. An exact
//! acquired value, source-proved scalar erasure, and an already registered
//! cleanup that reaches its counter key can make a definite leak UNKNOWN.
//! Known no-op, unrelated-key, conditional, and late cleanup still report.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const reference_ownership = @import("../../model/reference_ownership.zig");
const fresh_storage = @import("../../cache/fresh_storage.zig");

const tokens = @import("../../ast/tokens.zig");
const query = @import("../../ast/token_query.zig");
const method_names = @import("../../model/method_names.zig");
const testing = @import("../../testing.zig");
const matchBrace = tokens.matchBrace;
const findStmtSemicolon = tokens.findStmtSemicolon;
const hasTokenInRange = tokens.hasTokenInRange;
const Atom = query.Atom;

// `.<addrefMethod>(` — preceded by `.` so it's a method call.
// Capture slot $0 = the addref method token (report site).
const addref_call_pattern = &[_]Atom{
    .{ .tok = .period },
    .{ .pred_at = .{ .slot = 0, .pred = isStrictAddrefMethodName } },
    .{ .tok = .l_paren },
};

// `.<releaseMethod>(` — used inside defer/errdefer body scans.
const release_call_pattern = &[_]Atom{
    .{ .tok = .period },
    .{ .pred = method_names.isReleaseMethodName },
    .{ .tok = .l_paren },
};

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .unreleased_refs_on_error)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkBody);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Gate: only fns that actually use `try` (proxy for error union
    // return).  Without a `try` there can't be the error path this
    // rule fires on.
    if (!hasTokenInRange(tags, first, last, .keyword_try)) return;

    // Preserve the existing lexical caller-side guard. The private callee
    // query below does not strengthen this into a balance certificate.
    if (fnHasReleaseDeferOrErrdefer(tree, first, last)) return;

    // Walk for addref call sites — anywhere in the fn body, skipping
    // nested fns.  For each, require a `try` later in the body
    // (the error path that would leak the unreleased ref).
    const addrefs = try query.findAllInBody(gpa, tree, addref_call_pattern, first, last);
    defer gpa.free(addrefs);
    var evidence: reference_ownership.Query = .{};
    for (addrefs) |m| {
        const method_tok = m.captures[0].?;
        const sc = findStmtSemicolon(tags, m.end, last) orelse continue;
        if (!hasReachableLaterTry(tree, body, method_tok, sc)) continue;
        // A typed report requires a source-proved acquire. Missing source or
        // an incomplete callback stays unknown, not nonowning or balanced.
        if (cache.zls != null) switch (try evidence.acquisitionAt(cache, method_tok - 1)) {
            .increment => {},
            .unknown, .refused => continue,
        };
        if (try evidence.errorCleanupMayConsume(cache, proto, body, method_tok, sc)) continue;
        try report(gpa, problems, tree, method_tok);
    }
    if (cache.zls == null) return;
    // Typed acquisition follows the actual counter protocol, not the spelling
    // or whether the method returns the retained resource.
    const declaration = tokens.enclosingFnDecl(tree, first) orelse return;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        const at = tree.firstToken(node);
        if (at < first or at > last or tokens.enclosingFnDecl(tree, at) != declaration) continue;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
        const method_tok = tree.nodeData(call.ast.fn_expr).node_and_token[1];
        if (isStrictAddrefMethodName(tree.tokenSlice(method_tok))) continue;
        const sc = findStmtSemicolon(tags, tree.lastToken(node) + 1, last) orelse continue;
        if (!hasReachableLaterTry(tree, body, method_tok, sc)) continue;
        switch (try evidence.acquisitionAt(cache, fresh_storage.calleeQueryToken(tree, call))) {
            .increment => {},
            .unknown, .refused => continue,
        }
        if (try evidence.errorCleanupMayConsume(cache, proto, body, method_tok, sc)) continue;
        try report(gpa, problems, tree, method_tok);
    }
}

/// A textual try in a sibling branch is not an error path from this acquire.
/// Only direct terminal returns settle an enclosing block; conditional returns,
/// loops, catches and unknown calls do not establish unreachability.
fn hasReachableLaterTry(tree: *const Ast, body: Ast.Node.Index, acquisition: Ast.TokenIndex, after: Ast.TokenIndex) bool {
    const declaration = tokens.enclosingFnDecl(tree, acquisition) orelse return true;
    var terminal = tree.lastToken(body) + 1;
    for (tree.nodes.items(.tag), 0..) |_, block_index| {
        const block: Ast.Node.Index = @enumFromInt(block_index);
        if (tree.firstToken(block) < tree.firstToken(body) or tree.lastToken(block) > tree.lastToken(body)) continue;
        if (acquisition < tree.firstToken(block) or acquisition > tree.lastToken(block)) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const statements = tree.blockStatements(&buffer, block) orelse continue;
        for (statements) |statement| {
            if (tree.nodeTag(statement) != .@"return" or tree.lastToken(statement) < acquisition) continue;
            const tags = tree.tokens.items(.tag);
            const before_return = @max(acquisition, tree.firstToken(statement));
            if (hasTokenInRange(tags, acquisition, before_return, .keyword_break) or
                hasTokenInRange(tags, acquisition, before_return, .keyword_continue)) break;
            terminal = @min(terminal, @max(acquisition, tree.firstToken(statement)));
            break;
        }
    }
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .@"try") continue;
        const candidate: Ast.Node.Index = @enumFromInt(index);
        const at = tree.firstToken(candidate);
        if (at <= after or at >= terminal) continue;
        if (tokens.enclosingFnDecl(tree, at) == declaration) return true;
    }
    return false;
}


/// Names of methods that acquire a refcounted reference.  Kept tight
/// to avoid coincidental matches — `ref` alone is excluded (too
/// generic; collides with "borrow a sub-reference" usage like
/// `cmd.ref(buf)` in command-buffer APIs).  `pendingActivityRef`
/// is included for Bun's JSC pattern (#29329 family).
fn isStrictAddrefMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "reference") or
        std.mem.eql(u8, name, "retain") or
        std.mem.eql(u8, name, "addRef") or
        std.mem.eql(u8, name, "addref") or
        std.mem.eql(u8, name, "pendingActivityRef");
}

/// True iff some `defer` or `errdefer` in `[start, end]` contains
/// (in its inline or block body) a `.<release-method>(` call.
/// `defer` is even stronger than `errdefer` (fires on success AND
/// error), so authors who set up a `defer obj.release()` have
/// explicitly opted into the release pairing.
fn fnHasReleaseDeferOrErrdefer(tree: *const Ast, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t <= end) : (t += 1) {
        if (tags[t] != .keyword_errdefer and tags[t] != .keyword_defer) continue;
        // Skip optional `|err|` capture.
        var scan_start: Ast.TokenIndex = t + 1;
        if (scan_start <= end and tags[scan_start] == .pipe) {
            var p: Ast.TokenIndex = scan_start + 1;
            while (p <= end and tags[p] != .pipe) : (p += 1) {}
            if (p > end) return false;
            scan_start = p + 1;
        }
        if (scan_start > end) return false;
        const range_end = if (tags[scan_start] == .l_brace)
            (matchBrace(tags, scan_start, end) orelse end)
        else
            (findStmtSemicolon(tags, scan_start, end) orelse end);
        if (rangeHasReleaseCall(tree, scan_start, range_end)) return true;
        t = range_end;
    }
    return false;
}

fn rangeHasReleaseCall(tree: *const Ast, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    return query.anyMatchAnywhere(tree, release_call_pattern, start, end, null);
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    method_tok: Ast.TokenIndex,
) !void {
    const method = tree.tokenSlice(method_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}()` acquires a refcounted reference, but a later `try` can propagate an error without a proved rollback for that reference; register cleanup before fallible work",
        .{method},
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "unreleased-refs-on-error",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, method_tok),
        .end = try Pos.fromTokenEnd(tree, method_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "unreleased-refs-on-error: loop with .reference() then try without errdefer fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const BindGroupLayout = struct {
        \\    manager: Manager = .{},
        \\    pub const Manager = struct {
        \\        pub fn reference(_: *Manager) void {}
        \\        pub fn release(_: *Manager) void {}
        \\    };
        \\};
        \\pub fn init(allocator: std.mem.Allocator, layouts: []*BindGroupLayout) !*u8 {
        \\    const group_layouts = try allocator.alloc(*BindGroupLayout, layouts.len);
        \\    errdefer allocator.free(group_layouts);
        \\    for (layouts, 0..) |layout, i| {
        \\        layout.manager.reference();
        \\        group_layouts[i] = layout;
        \\    }
        \\    const out = try allocator.create(u8);
        \\    return out;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("unreleased-refs-on-error", problems.items[0].rule_id);
}

test "unreleased-refs-on-error: with errdefer .release() loop is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const BindGroupLayout = struct {
        \\    manager: Manager = .{},
        \\    pub const Manager = struct {
        \\        pub fn reference(_: *Manager) void {}
        \\        pub fn release(_: *Manager) void {}
        \\    };
        \\};
        \\pub fn init(allocator: std.mem.Allocator, layouts: []*BindGroupLayout) !*u8 {
        \\    const group_layouts = try allocator.alloc(*BindGroupLayout, layouts.len);
        \\    errdefer allocator.free(group_layouts);
        \\    var taken: usize = 0;
        \\    errdefer for (group_layouts[0..taken]) |l| l.manager.release();
        \\    for (layouts, 0..) |layout, i| {
        \\        layout.manager.reference();
        \\        group_layouts[i] = layout;
        \\        taken += 1;
        \\    }
        \\    const out = try allocator.create(u8);
        \\    return out;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "unreleased-refs-on-error: no try after loop doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Manager = struct { pub fn reference(_: *Manager) void {} };
        \\pub fn init(items: []*Manager) !void {
        \\    for (items) |m| m.reference();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "unreleased-refs-on-error: non-error-union fn (no try) doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Manager = struct { pub fn reference(_: *Manager) void {} };
        \\pub fn init(items: []*Manager) void {
        \\    for (items) |m| m.reference();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "unreleased-refs-on-error: retain (ObjC-style) variant also caught" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Obj = struct {
        \\    pub fn retain(_: *Obj) void {}
        \\    pub fn release(_: *Obj) void {}
        \\};
        \\pub fn build(items: []*Obj) !void {
        \\    for (items) |o| {
        \\        o.retain();
        \\    }
        \\    _ = try makeSomething();
        \\}
        \\fn makeSomething() !u8 { return 0; }
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "unreleased-refs-on-error: errdefer .deref() (Bun-style) also protects" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Obj = struct {
        \\    pub fn retain(_: *Obj) void {}
        \\    pub fn deref(_: *Obj) void {}
        \\};
        \\pub fn build(items: []*Obj) !void {
        \\    for (items) |o| o.retain();
        \\    errdefer for (items) |o| o.deref();
        \\    _ = try makeSomething();
        \\}
        \\fn makeSomething() !u8 { return 0; }
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "unreleased-refs-on-error: single-addref (pendingActivityRef) shape fires" {
    // Bun #29329 family — `this.pendingActivityRef();` at fn entry
    // followed by a fallible try with no paired
    // `pendingActivityUnref` errdefer.  Loop body NOT required.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const This = struct {
        \\    pub fn pendingActivityRef(_: *This) void {}
        \\    pub fn pendingActivityUnref(_: *This) void {}
        \\};
        \\pub fn work(this: *This) !void {
        \\    this.pendingActivityRef();
        \\    _ = try otherFallible();
        \\}
        \\fn otherFallible() !u8 { return 0; }
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
}

test "unreleased-refs-on-error: single-addref WITH defer-release doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const This = struct {
        \\    pub fn pendingActivityRef(_: *This) void {}
        \\    pub fn pendingActivityUnref(_: *This) void {}
        \\};
        \\pub fn work(this: *This) !void {
        \\    this.pendingActivityRef();
        \\    defer this.pendingActivityUnref();
        \\    _ = try otherFallible();
        \\}
        \\fn otherFallible() !u8 { return 0; }
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "unreleased-refs-on-error: comptime type-builder fn skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Manager = struct { pub fn reference(_: *Manager) void {} };
        \\pub fn Wrap(comptime _: type) type {
        \\    return struct {
        \\        pub fn build(items: []*Manager) !void {
        \\            for (items) |m| m.reference();
        \\            _ = try makeSomething();
        \\        }
        \\        fn makeSomething() !u8 { return 0; }
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // The inner fn does have the bug — we should fire on it once, but
    // NOT double-count via the outer Wrap fn.
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "unreleased-refs-on-error: related callee rollback is unknown, never a balance certificate" {
    // The source has a related decrement on errors. This does not prove balance,
    // but it prevents claiming that the acquired reference definitely leaks.
    try testing.expectNoFireTyped(check,
        \\const Handle = struct { refs: *usize, fn release(self: Handle) void { self.refs.* -= 1; } };
        \\const Session = struct {
        \\    fn retain(_: *Session, h: Handle) !Handle { h.refs.* += 1; return h; }
        \\};
        \\fn install(h: Handle, fail: bool) !void {
        \\    errdefer h.release();
        \\    if (fail) return error.Failed;
        \\    h.release();
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    const retained = try session.retain(source);
        \\    try install(retained, fail);
        \\}
    );
}

test "unreleased-refs-on-error: rollback on unrelated parameter does not protect retained result" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error",
        \\const Handle = struct { refs: *usize, fn release(self: Handle) void { self.refs.* -= 1; } };
        \\const Session = struct {
        \\    fn retain(_: *Session, h: Handle) !Handle { h.refs.* += 1; return h; }
        \\};
        \\fn install(h: Handle, other: Handle, fail: bool) !void {
        \\    errdefer other.release();
        \\    if (fail) return error.Failed;
        \\    h.release();
        \\}
        \\pub fn replace(session: *Session, source: Handle, other: Handle, fail: bool) !void {
        \\    const retained = try session.retain(source);
        \\    try install(retained, other, fail);
        \\}
    );
}

test "unreleased-refs-on-error: rollback installed after fallible action still fires" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error",
        \\const Handle = struct { refs: *usize, fn release(self: Handle) void { self.refs.* -= 1; } };
        \\const Session = struct {
        \\    fn retain(_: *Session, h: Handle) !Handle { h.refs.* += 1; return h; }
        \\};
        \\fn install(h: Handle, fail: bool) !void {
        \\    if (fail) return error.Failed;
        \\    errdefer h.release();
        \\    h.release();
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    const retained = try session.retain(source);
        \\    try install(retained, fail);
        \\}
    );
}

test "unreleased-refs-on-error: caller rollback protects retained result passed to borrower" {
    try testing.expectNoFire(check,
        \\const Handle = struct { refs: *usize, fn release(self: Handle) void { self.refs.* -= 1; } };
        \\const Session = struct {
        \\    fn retain(_: *Session, h: Handle) !Handle { h.refs.* += 1; return h; }
        \\};
        \\fn inspect(_: Handle, fail: bool) !void {
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    const retained = try session.retain(source);
        \\    errdefer retained.release();
        \\    try inspect(retained, fail);
        \\    retained.release();
        \\}
    );
}

const erased_ref_prelude =
    \\const Slot = struct { strong: usize = 0, other: usize = 0 };
    \\const Erased = struct {
    \\    key: usize = 0, ticket: usize = 0,
    \\    fn change(self: *Erased) void { self.key += 1; }
    \\};
    \\const Handle = struct {
    \\    key: usize = 0, ticket: usize = 0,
    \\    fn erase(self: *Handle) Erased {
    \\        const result: Erased = .{ .key = self.key, .ticket = self.ticket };
    \\        self.* = .{};
    \\        return result;
    \\    }
    \\};
    \\const Session = struct {
    \\    slots: [4]Slot = .{.{}} ** 4,
    \\    fn retain(self: *Session, handle: Handle) !Handle {
    \\        self.slots[handle.key].strong += 1;
    \\        return handle;
    \\    }
    \\    fn releaseErased(self: *Session, handle: *Erased) void {
    \\        const key = handle.key;
    \\        handle.* = .{};
    \\        self.slots[key].strong -= 1;
    \\    }
    \\};
;

test "unreleased-refs-on-error: scalar erasure and registered related rollback do not prove a leak" {
    try testing.expectNoFireTyped(check, erased_ref_prelude ++
        \\fn install(session: *Session, input: ?Erased, fail: bool) !void {
        \\    var pending = input;
        \\    errdefer if (pending) |*handle| session.releaseErased(handle);
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: no-op related error cleanup cannot hide an outstanding ref" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn noop(_: Erased) void {}
        \\fn install(input: Erased, fail: bool) !void {
        \\    errdefer noop(input);
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: decrementing an unrelated counter does not consume the acquired ref" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn irrelevant(session: *Session, input: Erased) void {
        \\    session.slots[input.key].other -= 1;
        \\}
        \\fn install(session: *Session, input: Erased, fail: bool) !void {
        \\    errdefer irrelevant(session, input);
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: late related rollback still leaves a proved error exit" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn install(session: *Session, input: Erased, fail: bool) !void {
        \\    var pending = input;
        \\    if (fail) return error.Failed;
        \\    errdefer session.releaseErased(&pending);
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: skipped related rollback cannot hide an outstanding ref" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn install(session: *Session, input: Erased, fail: bool) !void {
        \\    var pending = input;
        \\    errdefer if (false) session.releaseErased(&pending);
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: a different erased field cannot select the acquired slot" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn irrelevant(session: *Session, input: Erased) void {
        \\    session.slots[input.ticket].strong -= 1;
        \\}
        \\fn install(session: *Session, input: Erased, fail: bool) !void {
        \\    errdefer irrelevant(session, input);
        \\    if (fail) return error.Failed;
        \\}
        \\fn replace(session: *Session, model: Handle, fail: bool) !void {
        \\    var retained = try session.retain(model);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: an offset related key selects a different slot" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn irrelevant(session: *Session, input: Erased) void {
        \\    session.slots[input.key + 1].strong -= 1;
        \\}
        \\fn install(session: *Session, input: Erased, fail: bool) !void {
        \\    errdefer irrelevant(session, input);
        \\    if (fail) return error.Failed;
        \\}
        \\fn replace(session: *Session, model: Handle, fail: bool) !void {
        \\    var retained = try session.retain(model);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: discarding the erased argument cannot release a related slot" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn irrelevant(session: *Session, input: Erased) void {
        \\    _ = input;
        \\    session.slots[0].strong -= 1;
        \\}
        \\fn install(session: *Session, input: Erased, fail: bool) !void {
        \\    errdefer irrelevant(session, input);
        \\    if (fail) return error.Failed;
        \\}
        \\fn replace(session: *Session, model: Handle, fail: bool) !void {
        \\    var retained = try session.retain(model);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: a conditional related release leaves a known unprotected arm" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn install(session: *Session, input: Erased, release: bool, fail: bool) !void {
        \\    var pending = input;
        \\    errdefer if (release) session.releaseErased(&pending);
        \\    if (fail) return error.Failed;
        \\}
        \\fn replace(session: *Session, model: Handle, release: bool, fail: bool) !void {
        \\    var retained = try session.retain(model);
        \\    try install(session, retained.erase(), release, fail);
        \\}
    );
}

test "unreleased-refs-on-error: nested slot lookup and ticket rollback are related source evidence" {
    try testing.expectNoFireTyped(check,
        \\const Key = struct { slot: usize };
        \\const Slot = struct { strong: usize = 0 };
        \\const Erased = struct { key: Key = .{ .slot = 0 }, ticket: usize = 0 };
        \\const Handle = struct {
        \\    key: Key = .{ .slot = 0 }, ticket: usize = 0,
        \\    fn erase(self: *Handle) Erased {
        \\        const result: Erased = .{ .key = self.key, .ticket = self.ticket };
        \\        self.* = .{};
        \\        return result;
        \\    }
        \\};
        \\const Session = struct {
        \\    slots: [4]Slot = .{.{}} ** 4, next_ticket: usize = 1,
        \\    fn slotForKey(self: *Session, key: Key) !?*Slot {
        \\        if (key.slot >= self.slots.len) return null;
        \\        return &self.slots[key.slot];
        \\    }
        \\    fn ownedSlot(self: *Session, key: Key, ticket: usize) !*Slot {
        \\        if (ticket == 0) return error.Stale;
        \\        return (try self.slotForKey(key)) orelse return error.Stale;
        \\    }
        \\    fn retain(self: *Session, handle: Handle) !Handle {
        \\        const slot = try self.ownedSlot(handle.key, handle.ticket);
        \\        const ticket = self.next_ticket;
        \\        self.next_ticket += 1;
        \\        slot.strong += 1;
        \\        return .{ .key = handle.key, .ticket = ticket };
        \\    }
        \\    fn releaseOwned(_: *Session, key: Key, ticket: usize, slot: *Slot) void {
        \\        _ = key; _ = ticket;
        \\        slot.strong -= 1;
        \\    }
        \\    fn releaseErased(self: *Session, handle: *Erased) !void {
        \\        const slot = try self.ownedSlot(handle.key, handle.ticket);
        \\        const key = handle.key;
        \\        const ticket = handle.ticket;
        \\        handle.* = .{};
        \\        self.releaseOwned(key, ticket, slot);
        \\    }
        \\};
        \\const App = struct {
        \\    session: *Session,
        \\    fn install(self: *App, input: ?Erased, fail: bool) !void {
        \\        var pending = input;
        \\        errdefer if (pending) |*handle| {
        \\            self.session.releaseErased(handle) catch @panic("rollback failed");
        \\        };
        \\        if (fail) return error.Failed;
        \\    }
        \\    fn replace(self: *App, source: Handle, fail: bool) !void {
        \\        var retained = try self.session.retain(source);
        \\        try self.install(retained.erase(), fail);
        \\    }
        \\};
    );
}

test "unreleased-refs-on-error: same counter declaration with a different key still leaks" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn install(session: *Session, input: Erased, other: Erased, fail: bool) !void {
        \\    errdefer {
        \\        _ = input;
        \\        session.slots[other.key].strong -= 1;
        \\    }
        \\    if (fail) return error.Failed;
        \\}
        \\fn replace(session: *Session, source: Handle, other: Erased, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), other, fail);
        \\}
    );
}

const permuted_ref_prelude =
    \\const Slot = struct { strong: usize = 0 };
    \\const Erased = struct { key: usize, ticket: usize };
    \\const Handle = struct {
    \\    key: usize = 0, ticket: usize = 0,
    \\    fn erase(self: *Handle) Erased {
    \\        const result: Erased = .{ .key = self.ticket, .ticket = self.key };
    \\        self.* = .{};
    \\        return result;
    \\    }
    \\};
    \\const Session = struct {
    \\    slots: [4]Slot = .{.{}} ** 4,
    \\    fn retain(self: *Session, handle: Handle) !Handle {
    \\        self.slots[handle.key].strong += 1;
    \\        return handle;
    \\    }
    \\};
;

test "unreleased-refs-on-error: erasure preserves a renamed counter key" {
    try testing.expectNoFireTyped(check, permuted_ref_prelude ++
        \\fn rollback(session: *Session, input: Erased) void {
        \\    session.slots[input.ticket].strong -= 1;
        \\}
        \\fn install(session: *Session, input: Erased, fail: bool) !void {
        \\    errdefer rollback(session, input);
        \\    if (fail) return error.Failed;
        \\}
        \\fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: erasure does not equate different scalar fields" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", permuted_ref_prelude ++
        \\fn rollback(session: *Session, input: Erased) void {
        \\    session.slots[input.key].strong -= 1;
        \\}
        \\fn install(session: *Session, input: Erased, fail: bool) !void {
        \\    errdefer rollback(session, input);
        \\    if (fail) return error.Failed;
        \\}
        \\fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}


test "unreleased-refs-on-error: typed reference query has no acquire effect" {
    try testing.expectNoFireTyped(check,
        \\const Source = struct {
        \\    value: u32,
        \\    fn reference(self: *const Source) ?u32 { return self.value; }
        \\};
        \\fn fail() !void { return error.Failed; }
        \\pub fn work(source: *const Source) !void {
        \\    _ = source.reference();
        \\    try fail();
        \\}
    );
}

test "unreleased-refs-on-error: a terminal retained branch cannot reach sibling tries" {
    try testing.expectNoFireTyped(check,
        \\const Owner = struct {
        \\    refs: usize,
        \\    fn retain(self: *Owner) void { self.refs += 1; }
        \\    fn release(self: *Owner) void { self.refs -= 1; }
        \\};
        \\fn fail() !void { return error.Failed; }
        \\pub fn work(owner: *Owner, shared: bool) !*Owner {
        \\    if (shared) {
        \\        owner.retain();
        \\        return owner;
        \\    }
        \\    try fail();
        \\    return owner;
        \\}
    );
}

test "unreleased-refs-on-error: read-only name does not hide actual counter acquisition" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error",
        \\const Owner = struct {
        \\    refs: usize,
        \\    fn reference(self: *Owner) void { self.refs += 1; }
        \\    fn release(self: *Owner) void { self.refs -= 1; }
        \\};
        \\fn fail() !void { return error.Failed; }
        \\pub fn work(owner: *Owner) !void {
        \\    owner.reference();
        \\    try fail();
        \\}
    );
}

test "unreleased-refs-on-error: a later try in the same branch still leaks" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error",
        \\const Owner = struct {
        \\    refs: usize,
        \\    fn retain(self: *Owner) void { self.refs += 1; }
        \\    fn release(self: *Owner) void { self.refs -= 1; }
        \\};
        \\fn fail() !void { return error.Failed; }
        \\pub fn work(owner: *Owner, shared: bool) !*Owner {
        \\    if (shared) {
        \\        owner.retain();
        \\        try fail();
        \\        return owner;
        \\    }
        \\    return owner;
        \\}
    );
}

test "unreleased-refs-on-error: a retained clone is distinct from a returned borrowed handle" {
    const prelude =
        \\const Handle = struct { refs: *usize };
        \\const Pool = struct {
        \\    fn snapshot(_: *Pool, h: Handle) Handle { h.refs.* += 1; return h; }
        \\    fn reference(_: *Pool, h: Handle) Handle { return h; }
        \\};
        \\fn fail() !void { return error.Failed; }
    ;
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", prelude ++
        \\pub fn work(pool: *Pool, source: Handle) !void {
        \\    const clone = pool.snapshot(source);
        \\    _ = clone;
        \\    try fail();
        \\}
    );
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn work(pool: *Pool, source: Handle) !void {
        \\    const borrowed = pool.reference(source);
        \\    _ = borrowed;
        \\    try fail();
        \\}
    );
}

test "unreleased-refs-on-error: imported aliases preserve query and retained-clone declaration effects" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "owners.zig", .data =
        \\pub const Handle = struct { refs: *usize };
        \\pub const Pool = struct {
        \\    pub fn snapshot(_: *Pool, h: Handle) Handle { h.refs.* += 1; return h; }
        \\    pub fn reference(_: *Pool, h: Handle) Handle { return h; }
        \\};
    });
    const source: [:0]const u8 =
        \\const imported = @import("owners.zig");
        \\const Pool = imported.Pool;
        \\const Handle = imported.Handle;
        \\fn fail() !void { return error.Failed; }
        \\pub fn borrow(pool: *Pool, source: Handle) !void {
        \\    _ = pool.reference(source);
        \\    try fail();
        \\}
        \\pub fn leak(pool: *Pool, source: Handle) !void {
        \\    const clone = pool.snapshot(source);
        \\    _ = clone;
        \\    try fail();
        \\}
    ;
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "caller.zig" });
    defer gpa.free(path);
    try tmp.dir.writeFile(io, .{ .sub_path = "caller.zig", .data = source });
    const engine = @import("type_engine");
    var context: engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const project_mod = @import("../../cache/project_cache.zig");
    var project = project_mod.ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
    defer project.deinit();
    project.type_context = &context;
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.setProject(&project, path);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer testing.freeProblems(gpa, &problems);
    try check(gpa, tree, &cache, &config_mod.Default, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqual(@as(u32, 10), problems.items[0].start.line);
    try std.testing.expectEqualStrings("unreleased-refs-on-error", problems.items[0].rule_id);
}

test "unreleased-refs-on-error: opaque acquisition is unknown rather than a noownership certificate" {
    try testing.expectNoFireTyped(check,
        \\const Source = struct { retain: *const fn (*anyopaque) void, context: *anyopaque };
        \\fn fail() !void { return error.Failed; }
        \\pub fn work(source: Source) !void {
        \\    source.retain(source.context);
        \\    try fail();
        \\}
    );
}

test "unreleased-refs-on-error: a loop break can bypass a terminal return before later failure" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error",
        \\const Owner = struct {
        \\    refs: usize,
        \\    fn retain(self: *Owner) void { self.refs += 1; }
        \\    fn release(self: *Owner) void { self.refs -= 1; }
        \\};
        \\fn fail() !void { return error.Failed; }
        \\pub fn work(owner: *Owner, exit: bool) !*Owner {
        \\    while (true) {
        \\        owner.retain();
        \\        if (exit) break;
        \\        return owner;
        \\    }
        \\    try fail();
        \\    return owner;
        \\}
    );
}

test "unreleased-refs-on-error: canonical increment differs from a mutation" {
    const prelude =
        \\const Ref = struct {
        \\    count: usize,
        \\    fn retain(self: *Ref) void { self.count |= 1; }
        \\    fn reference(self: *Ref) void { self.count += 1; }
        \\    fn release(self: *Ref) void { self.count -= 1; }
        \\};
        \\fn fail() !void { return error.Failed; }
    ;
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn work(value: *Ref) !void { value.retain(); try fail(); }
    );
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", prelude ++
        \\pub fn work(value: *Ref) !void {
        \\    value.reference();
        \\    try fail();
        \\}
    );
}

test "unreleased-refs-on-error: partial increments and metric results are not retained references" {
    const prelude =
        \\const Ref = struct {
        \\    count: usize,
        \\    metrics: usize,
        \\    fn acquire(self: *Ref) *Ref { self.count += 1; return self; }
        \\    fn partial(self: *Ref, flag: bool) *Ref {
        \\        if (flag) self.count += 1;
        \\        return self;
        \\    }
        \\    fn falseRetain(self: *Ref) *Ref { if (false) self.count += 1; return self; }
        \\    fn metric(self: *Ref) *Ref { self.metrics += 1; return self; }
        \\    fn uncertain(self: *Ref, action: *const fn () void) *Ref { self.count += 1; action(); return self; }
        \\    fn alternate(self: *Ref, other: *Ref, flag: bool) *Ref {
        \\        if (flag) { self.count += 1; return self; }
        \\        return other;
        \\    }
        \\    fn release(self: *Ref) void { self.count -= 1; }
        \\};
        \\fn fail() !void { return error.Failed; }
    ;
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", prelude ++
        \\pub fn work(value: *Ref) !void {
        \\    const retained = value.acquire();
        \\    _ = retained;
        \\    try fail();
        \\}
    );
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn work(value: *Ref, flag: bool) !void {
        \\    _ = value.partial(flag);
        \\    try fail();
        \\}
    );
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn work(value: *Ref) !void {
        \\    _ = value.falseRetain();
        \\    try fail();
        \\}
    );
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn work(value: *Ref) !void {
        \\    _ = value.metric();
        \\    try fail();
        \\}
    );
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn work(value: *Ref, action: *const fn () void) !void {
        \\    _ = value.uncertain(action);
        \\    try fail();
        \\}
    );
    try testing.expectNoFireTyped(check, prelude ++
        \\pub fn work(value: *Ref, other: *Ref, flag: bool) !void {
        \\    _ = value.alternate(other, flag);
        \\    try fail();
        \\}
    );
}

test "unreleased-refs-on-error: whole retained pointer rollback selects the same object" {
    const prelude =
        \\const Ref = struct {
        \\    count: usize,
        \\    child: *Ref,
        \\    fn acquire(self: *Ref) *Ref { self.count += 1; return self; }
        \\    fn release(self: *Ref) void { self.count -= 1; }
        \\};
    ;
    const caller =
        \\pub fn work(original: *Ref, fail: bool) !void {
        \\    const retained = original.acquire();
        \\    try install(retained, fail);
        \\}
    ;
    try testing.expectNoFireTyped(check, prelude ++
        \\fn install(value: *Ref, fail: bool) !void {
        \\    errdefer value.release();
        \\    if (fail) return error.Failed;
        \\}
    ++ caller);
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", prelude ++
        \\fn install(value: *Ref, fail: bool) !void {
        \\    errdefer value.child.release();
        \\    if (fail) return error.Failed;
        \\}
    ++ caller);
}

test "unreleased-refs-on-error: later rollback cannot cover an earlier failing call" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn fail() !void { return error.Failed; }
        \\fn install(session: *Session, input: Erased, failing: bool) !void {
        \\    var pending = input;
        \\    errdefer session.releaseErased(&pending);
        \\    if (failing) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, source: Handle, failing: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try fail();
        \\    try install(session, retained.erase(), failing);
        \\}
    );
}

test "unreleased-refs-on-error: equal keys in different owners are different counter instances" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn install(other: *Session, input: Erased, fail: bool) !void {
        \\    var pending = input;
        \\    errdefer other.releaseErased(&pending);
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, other: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(other, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: rollback with a successful bypass is not proved consumption" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error",
        \\const Handle = struct {
        \\    refs: *usize,
        \\    fn retain(self: Handle) Handle { self.refs.* += 1; return self; }
        \\};
        \\fn rollback(handle: Handle, skip: bool) void {
        \\    if (skip) return;
        \\    handle.refs.* -= 1;
        \\}
        \\fn install(handle: Handle, skip: bool, fail: bool) !void {
        \\    errdefer rollback(handle, skip);
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(source: Handle, skip: bool, fail: bool) !void {
        \\    const retained = source.retain();
        \\    try install(retained, skip, fail);
        \\}
    );
}

test "unreleased-refs-on-error: a void acquisition uses its source protocol instead of its spelling" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error",
        \\const Owner = struct {
        \\    count: usize,
        \\    fn observe(self: *Owner) void { self.count += 1; }
        \\    fn release(self: *Owner) void { self.count -= 1; }
        \\};
        \\fn fail() !void { return error.Failed; }
        \\pub fn work(owner: *Owner) !void {
        \\    owner.observe();
        \\    try fail();
        \\}
    );
}

test "unreleased-refs-on-error: a pointer-captured rollback observes writes inside its cleanup" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn install(session: *Session, input: ?Erased, fail: bool) !void {
        \\    var pending = input;
        \\    errdefer if (pending) |*handle| {
        \\        handle.key += 1;
        \\        session.releaseErased(handle);
        \\    };
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: deferred rollback reads the key at the later error horizon" {
    inline for (.{
        "pending.?.key += 1;",
        "pending = null;",
        "const alias = &pending.?; alias.key += 1;",
        "mutate(&pending);",
        "pending.?.change();",
    }) |mutation| {
        try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
            \\extern fn mutate(input: *?Erased) void;
            \\fn fail() !void { return error.Failed; }
            \\fn install(session: *Session, input: ?Erased) !void {
            \\    var pending = input;
            \\    errdefer if (pending) |*handle| session.releaseErased(handle);
        ++ "\n    " ++ mutation ++ "\n" ++
            \\    try fail();
            \\}
            \\pub fn replace(session: *Session, source: Handle) !void {
            \\    var retained = try session.retain(source);
            \\    try install(session, retained.erase());
            \\}
        );
    }
}

test "unreleased-refs-on-error: a key changed before its immutable snapshot is not the acquired key" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn changedRollback(session: *Session, handle: *Erased) void {
        \\    handle.key += 1;
        \\    const key = handle.key;
        \\    handle.* = .{};
        \\    session.slots[key].strong -= 1;
        \\}
        \\fn install(session: *Session, input: ?Erased, fail: bool) !void {
        \\    var pending = input;
        \\    errdefer if (pending) |*handle| changedRollback(session, handle);
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}

test "unreleased-refs-on-error: a later-registered cleanup changes the key before rollback" {
    try testing.expectFiresTyped(check, "unreleased-refs-on-error", erased_ref_prelude ++
        \\fn install(session: *Session, input: ?Erased, fail: bool) !void {
        \\    var pending = input;
        \\    errdefer if (pending) |*handle| session.releaseErased(handle);
        \\    errdefer if (pending) |*later| {
        \\        later.key += 1;
        \\    };
        \\    if (fail) return error.Failed;
        \\}
        \\pub fn replace(session: *Session, source: Handle, fail: bool) !void {
        \\    var retained = try session.retain(source);
        \\    try install(session, retained.erase(), fail);
        \\}
    );
}
