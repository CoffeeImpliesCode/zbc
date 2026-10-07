//! `Thread.spawn(.{}, <fn>, .{ &<local>, ... })` /
//! `<pool>.spawn(<fn>, .{ &<local>, ... })` — passing the address
//! of a function-LOCAL variable into a spawned thread.  The
//! thread keeps running after the spawning fn returns; the local
//! dies with the frame; the thread now reads/writes through a
//! dangling pointer.
//!
//! Spawned threads' lifetimes are independent of the spawning
//! fn — `.detach()` / `.join()` separation lets the thread out-
//! live the caller.  Even with `defer thread.join()`, the join
//! happens at scope exit AFTER any subsequent local mutation
//! (the locals are still observable from the thread between
//! spawn and join).
//!
//! Detection (per-fn token walk):
//!   1. Skip comptime type-builder fns.
//!   2. Walk for `Thread.spawn(` / `<recv>.spawn(` calls.
//!   3. Find the LAST argument (the args struct literal).
//!   4. Scan args for `&<local>` where `<local>` is a fn-local
//!      var/const (NOT a parameter — caller-supplied pointer is
//!      typically the caller's responsibility) and NOT a static
//!      variable (file-top-level decl).
//!   5. Fire on the `&<local>` site.
//!
//! Conservative — only matches the canonical `&<single-ident>`
//! shape; `&<container>.<field>` is left to the existing
//! stack-escape detection.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

const matchParen = tokens.matchParen;
const skipNestedFn = tokens.skipNestedFn;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .thread_spawn_local_pointer)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

fn checkFn(
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

    // Build the set of param names; we exclude `&<param>` from
    // the rule (caller-supplied pointer; not a stack-frame leak).
    const bindings = try cache.localBindings(proto, body);
    var locals_only: std.StringHashMapUnmanaged(void) = .empty;
    defer locals_only.deinit(gpa);
    for (bindings.items) |b| {
        if (b.origin == .param) continue;
        try locals_only.put(gpa, b.name, {});
    }

    var t: Ast.TokenIndex = first;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Look for `<id>.spawn(` shape — `<id>` is some Thread /
        // pool identifier; we don't require a specific name to
        // catch wrappers like `bun.JSC.spawn` / `pool.spawn`.
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        const meth = tree.tokenSlice(t + 2);
        if (!isSpawnMethodName(meth)) continue;
        const lp = t + 3;
        const cp = matchParen(tags, lp, last) orelse continue;
        // Find the LAST argument (args struct literal).  Walk
        // back from `cp` to the `.{` start.  In Zig the trailing
        // arg of a spawn-style call is the args tuple — typically
        // `.{ ... }`.
        const args_range = lastArgRange(tags, lp + 1, cp - 1) orelse continue;
        // Discriminator: the last arg MUST start with `.{` —
        // Zig's `Thread.spawn(.{}, fn, .{args})` / pool's
        // `.spawn(fn, .{args})` shape.  libuv-style
        // `uv.spawn(loop, &opts)` (last arg `&opts`) is NOT a
        // thread-spawn-with-captured-args pattern; the out-param
        // is consumed synchronously and the call returns.
        if (args_range.first + 1 > args_range.last) continue;
        if (tags[args_range.first] != .period or tags[args_range.first + 1] != .l_brace) continue;
        // Synchronisation skip: if the rest of the fn body contains
        // a `.join()` / `.wait()` / `.await()` / `.waitForCompletion()`
        // call, the spawning fn explicitly synchronises with the
        // worker before returning — locals stay alive for the
        // duration of the spawned task.  Conservative: any join-
        // like call anywhere after the spawn (in this fn) counts;
        // we don't verify it's reached on all paths.
        if (joinCallAfter(tree, cp + 1, last)) {
            t = cp;
            continue;
        }
        // Scan that range for `& <ident>` where ident is a local
        // (not a param).
        var k: Ast.TokenIndex = args_range.first;
        while (k + 1 <= args_range.last) : (k += 1) {
            if (tags[k] != .ampersand) continue;
            if (tags[k + 1] != .identifier) continue;
            // Reject `& <ident> .` or `& <ident> [` — borrows into
            // heap-allocated storage (field or slice element).
            if (k + 2 <= args_range.last and
                (tags[k + 2] == .period or tags[k + 2] == .l_bracket)) continue;
            const name = tree.tokenSlice(k + 1);
            if (!locals_only.contains(name)) continue;
            try report(gpa, problems, tree, k, name);
        }
        t = cp;
    }
}

/// True iff `[start, end]` contains a `<recv>.<sync-method>(`
/// call — `join` / `wait` / `await` / `waitForCompletion` /
/// `joinAll` / `deinit`.  Used to suppress the rule when the
/// spawning fn explicitly synchronises with the worker before
/// returning, so the worker can't outlive the local.
fn joinCallAfter(tree: *const Ast, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    if (start > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 3 <= end) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        if (isSyncMethodName(tree.tokenSlice(t + 1))) return true;
    }
    return false;
}

fn isSyncMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "join") or
        std.mem.eql(u8, name, "joinAll") or
        std.mem.eql(u8, name, "wait") or
        std.mem.eql(u8, name, "await") or
        std.mem.eql(u8, name, "waitForCompletion") or
        std.mem.eql(u8, name, "waitAndWork") or
        std.mem.eql(u8, name, "deinit");
}

fn isSpawnMethodName(name: []const u8) bool {
    // Conservative — only canonical thread-spawn names.  `schedule`
    // is ambiguous (`thread_pool.schedule(batch)` vs
    // `batch.schedule(...)` which is batch-builder) and would
    // cause FPs.  Other patterns can be added with care.
    return std.mem.eql(u8, name, "spawn") or
        std.mem.eql(u8, name, "spawnTask");
}

const Range = struct { first: Ast.TokenIndex, last: Ast.TokenIndex };

/// Find the range covering the LAST comma-separated argument in
/// `[start, end]` at paren-depth 0.  Used to isolate the args
/// tuple `.{ ... }` from a `spawn(.{}, fn, .{...})` call.
fn lastArgRange(tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, end: Ast.TokenIndex) ?Range {
    if (start > end) return null;
    var last_comma: ?Ast.TokenIndex = null;
    var depth: u32 = 0;
    var t: Ast.TokenIndex = start;
    while (t <= end) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => if (depth > 0) {
                depth -= 1;
            },
            .comma => if (depth == 0) {
                last_comma = t;
            },
            else => {},
        }
    }
    const first: Ast.TokenIndex = if (last_comma) |c| c + 1 else start;
    return .{ .first = first, .last = end };
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    amp_tok: Ast.TokenIndex,
    local_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`&{s}` passed to a spawned thread/task — the function-local `{s}` dies with this frame, but the spawned worker continues independently and may read/write the dangling pointer.  Either heap-allocate `{s}` (and let the worker own it via `.detach()`/`.join()` semantics) or restructure to await/join the worker BEFORE the local goes out of scope.  Stack-allocated args are safe ONLY when the spawning fn explicitly `.join()`s before returning",
        .{ local_name, local_name, local_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = "thread-spawn-local-pointer",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, amp_tok),
        .end = try Pos.fromTokenEnd(tree, amp_tok + 1),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "thread-spawn-local-pointer: &local in spawn args fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\fn run(p: *u32) void { _ = p; }
        \\pub fn main() !void {
        \\    var counter: u32 = 0;
        \\    const t = try std.Thread.spawn(.{}, run, .{&counter});
        \\    t.detach();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("thread-spawn-local-pointer", problems.items[0].rule_id);
}

test "thread-spawn-local-pointer: &param does NOT fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\fn run(p: *u32) void { _ = p; }
        \\pub fn forward(caller_counter: *u32) !void {
        \\    const t = try std.Thread.spawn(.{}, run, .{caller_counter});
        \\    t.detach();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "thread-spawn-local-pointer: heap-allocated arg does NOT fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\fn run(p: *u32) void { _ = p; }
        \\pub fn main(allocator: std.mem.Allocator) !void {
        \\    const counter = try allocator.create(u32);
        \\    counter.* = 0;
        \\    const t = try std.Thread.spawn(.{}, run, .{counter});
        \\    t.detach();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // `counter` is passed directly (not `&counter`) — already a
    // heap pointer.  Rule must not fire.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "thread-spawn-local-pointer: &slice[i] element address does NOT fire (heap slice)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Worker = struct { val: u32 };
        \\fn run(w: *Worker) void { _ = w; }
        \\pub fn init(allocator: std.mem.Allocator, n: usize) !void {
        \\    const workers = try allocator.alloc(Worker, n);
        \\    for (0..n) |i| {
        \\        const t = try std.Thread.spawn(.{}, run, .{&workers[i]});
        \\        t.detach();
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // &workers[i] is a pointer into a heap-allocated slice — not a stack address.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "thread-spawn-local-pointer: pool.spawn variant also fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Pool = struct {
        \\    pub fn spawn(self: *Pool, comptime f: anytype, args: anytype) !void {
        \\        _ = self; _ = f; _ = args;
        \\    }
        \\};
        \\fn run(p: *u32) void { _ = p; }
        \\pub fn submit(pool: *Pool) !void {
        \\    var local: u32 = 0;
        \\    try pool.spawn(run, .{&local});
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}
