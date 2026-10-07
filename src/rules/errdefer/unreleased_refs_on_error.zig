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
//! Detection (purely syntactic, per-fn token walk):
//!   1. For each non-type-builder fn whose body contains at least
//!      one `try` keyword (proxy for "returns error union").
//!   2. Pre-pass: any `defer` / `errdefer` containing a release-
//!      class method call (`release`, `deref`, `unref`,
//!      `removeRef`) suppresses the WHOLE fn.  We can't verify the
//!      release matches the addref, so we lean toward zero FPs and
//!      trust that any release-class defer/errdefer means the
//!      author thought about the leak.
//!   3. Walk the fn body for `<chain>.<addref>(` calls where
//!      `addref ∈ {reference, retain, addRef, addref,
//!      pendingActivityRef}`.  Both loop-body and top-level
//!      addref sites are caught.
//!   4. For each addref, check there's a later `try` in the fn body.
//!   5. Fire at the addref call site.
//!
//! Callee rollback is not a lexical release defer. Storage-free summaries
//! do not certify reference-count balance or ownership through erased handles,
//! optional captures, and publication. Without that certificate a callee's
//! release-named call cannot discharge the caller's acquired reference.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

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

    // Gate: only fns that actually use `try` (proxy for error union
    // return).  Without a `try` there can't be the error path this
    // rule fires on.
    if (!hasTokenInRange(tags, first, last, .keyword_try)) return;

    // Cheap pre-pass: any release-class defer / errdefer in this fn
    // body?  If so, every addref in it is considered protected and
    // we skip the whole fn.  This is the rule's main precision
    // lever — broader release-method list = fewer fires = lower FP
    // rate.
    if (fnHasReleaseDeferOrErrdefer(tree, first, last)) return;

    // Walk for addref call sites — anywhere in the fn body, skipping
    // nested fns.  For each, require a `try` later in the body
    // (the error path that would leak the unreleased ref).
    const addrefs = try query.findAllInBody(gpa, tree, addref_call_pattern, first, last);
    defer gpa.free(addrefs);
    for (addrefs) |m| {
        const method_tok = m.captures[0].?;
        const sc = findStmtSemicolon(tags, m.end, last) orelse continue;
        if (!hasTokenInRange(tags, sc + 1, last, .keyword_try)) continue;
        try report(gpa, problems, tree, method_tok);
    }
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
        "`{s}()` inside this loop acquires a refcounted reference, but the enclosing fn has a later `try` with no `errdefer` calling `.release()` / `.deref()` — every reference taken leaks if that `try` propagates an error",
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

test "unreleased-refs-on-error: uncertified callee rollback remains conservative" {
    // Safe at runtime, but no reference-count ownership certificate exists.
    // Do not turn a cleanup-named call in a different function into proof.
    try testing.expectFires(check, "unreleased-refs-on-error",
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
    try testing.expectFires(check, "unreleased-refs-on-error",
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
    try testing.expectFires(check, "unreleased-refs-on-error",
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
