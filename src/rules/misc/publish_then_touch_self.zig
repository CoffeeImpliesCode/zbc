//! Publish-then-touch-self detector — `<thing>.<publish>(this);`
//! (or `(self)`) where `<publish>` dispatches onto a concurrent
//! queue / thread pool / cross-thread channel, followed by any
//! further use of `this`/`self` in the same scope.  The consumer
//! thread may have already freed `this` before the second access
//! lands → cross-thread UAF.
//!
//! Real-world: oven-sh/bun#29128 (RuntimeTranspilerStore —
//! `transpiler_store.queue.push(this); ... transpiler_store.<field>`
//! after `this` was potentially freed by the worker), #31177
//! (mimalloc TLS slot race), #30185 (cross-thread Strong<> copy
//! in lambda capture).
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Skip comptime type-builder fns.
//!   2. Find call `<chain>.<publish-method>(<arg>)` where
//!      <arg> is bare `this` or `self`, and either:
//!        a. the receiver chain contains a "concurrency" token
//!           (`queue`, `pool`, `thread`, `cross_thread`,
//!           `concurrent`, `dispatch`), OR
//!        b. the method name contains "Concurrent" / "Thread" /
//!           "cross" / matches a known concurrent-dispatch name
//!           (`enqueueTaskConcurrent`, `postToMain`, etc.)
//!   3. After the publish, scan for any use of `this`/`self` in
//!      the same fn body at the same lexical depth.
//!   4. Fire on the first such use.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const query = @import("../../ast/token_query.zig");
const scope = @import("../../ast/scope_iter.zig");
const method_names = @import("../../model/method_names.zig");
const testing = @import("../../testing.zig");
const findStmtSemicolon = tokens.findStmtSemicolon;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const Atom = query.Atom;

// `.<method>(<this|self>)` — preceded by `.` so it's a method call
// on a chain.  Capture slots: $0 = method, $1 = arg (this|self).
const publish_call = &[_]Atom{
    .{ .tok = .period },
    .{ .capture = 0 },
    .{ .tok = .l_paren },
    .{ .pred_at = .{ .slot = 1, .pred = method_names.isSelfReceiverName } },
    .{ .tok = .r_paren },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .publish_then_touch_self)) return;
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

    const calls = try query.findAllInBody(gpa, tree, publish_call, first, last);
    defer gpa.free(calls);
    for (calls) |m| {
        const method_tok = m.captures[0].?;
        const method = tree.tokenSlice(method_tok);
        const arg = m.captureText(tree, 1).?;
        // Concurrency check: method name OR chain receiver suggests
        // concurrent dispatch.
        const chain_start = walkBackChain(tags, method_tok);
        if (!isConcurrentDispatch(tree, method, chain_start, method_tok)) continue;
        // Type-inference suppression: if we can prove `this` is NOT
        // individually heap-managed, the UAF hazard cannot materialise.
        //
        // Tier-1 (specific): resolve arg's param type → look for any
        // method on that type with takes_ownership_of == 0.
        //   false  → type known, no self-destructor → suppress
        //   true   → type known, has self-destructor → keep
        //   null   → type unknown (file-level struct, @fieldParentPtr
        //             local, cross-file type) → fall to tier-2
        //
        // Tier-2 (file-level fallback): if NO function anywhere in this
        // file self-destructs its first param, nothing in the file is
        // individually heap-managed → suppress.
        const type_inference_suppress = blk: {
            if (try cache.receiverTypeHasSelfDestructor(proto, arg)) |has_destructor| {
                break :blk !has_destructor;
            }
            // null → tier-2
            break :blk !(try cache.fileHasDirectSelfDestructor());
        };
        if (type_inference_suppress) continue;
        // Check for a `defer arg.X` statement appearing BEFORE the publish
        // in token order — it fires AFTER publish at function exit, creating
        // the same use-after-publish hazard.
        //   pub fn notify(this: *T) void {
        //       defer this.manager.wake();           // ← fires AFTER push
        //       this.queue.push(this);               // ← publish
        //   }
        if (findDeferredArgUseBefore(tree, tags, first, m.start, arg)) |tok| {
            try report(gpa, problems, tree, tok, method, arg);
            continue;
        }
        // Find next use of `arg` (this/self) in the same scope.
        const sc = findStmtSemicolon(tags, m.end + 1, last) orelse continue;
        const use_tok = scope.findIdentUseInEnclosingScope(tree, sc + 1, last, arg) orelse continue;
        try report(gpa, problems, tree, use_tok, method, arg);
    }
}

/// Scan backward from `before` (the publish call start) looking for a
/// `defer <arg>.<field>` statement.  A registered defer fires at function
/// exit — i.e., AFTER the publish — so it's a use-after-publish hazard
/// even though it appears earlier in the source text.
fn findDeferredArgUseBefore(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    from: Ast.TokenIndex,
    before: Ast.TokenIndex,
    arg: []const u8,
) ?Ast.TokenIndex {
    if (before == 0 or from >= before) return null;
    var t: Ast.TokenIndex = from;
    while (t + 2 < before) : (t += 1) {
        if (tags[t] != .keyword_defer) continue;
        // Inline form: `defer <arg>.<field>...`
        if (t + 2 < before and
            tags[t + 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 1), arg) and
            tags[t + 2] == .period)
        {
            return t + 1;
        }
        // Block form: `defer { ... <arg>. ... }`
        if (t + 1 < before and tags[t + 1] == .l_brace) {
            var u: Ast.TokenIndex = t + 2;
            var depth: u32 = 1;
            while (u < before and depth > 0) : (u += 1) {
                switch (tags[u]) {
                    .l_brace => depth += 1,
                    .r_brace => depth -= 1,
                    .identifier => if (depth == 1 and
                        std.mem.eql(u8, tree.tokenSlice(u), arg) and
                        u + 1 < before and tags[u + 1] == .period)
                    {
                        return u;
                    },
                    else => {},
                }
            }
        }
    }
    return null;
}

/// Walk backward from the `.method` to find the chain's start token.
/// Returns the first token of the chain (the leftmost identifier).
fn walkBackChain(tags: []const std.zig.Token.Tag, method_tok: Ast.TokenIndex) Ast.TokenIndex {
    // method_tok is at the .method's identifier; method_tok-1 is `.`.
    // Walk back through `.<ident>` segments.
    var t: Ast.TokenIndex = method_tok;
    while (t >= 2 and tags[t - 1] == .period and tags[t - 2] == .identifier) {
        t -= 2;
    }
    return t;
}

/// True iff the call's method name OR receiver chain suggests
/// concurrent / cross-thread dispatch (ownership transfer, not
/// observation).
fn isConcurrentDispatch(
    tree: *const Ast,
    method: []const u8,
    chain_start: Ast.TokenIndex,
    method_tok: Ast.TokenIndex,
) bool {
    // Observer-method blocklist: even on a concurrent-chain
    // receiver, these methods don't transfer ownership.
    if (isObserverMethod(method)) return false;
    // Method-name signal (strong).
    if (containsConcurrencyToken(method)) return true;
    if (isExactConcurrentMethod(method)) return true;
    // Receiver-chain signal: any identifier in the chain matches
    // a concurrency keyword AND the method looks like a publish
    // (push / send / submit) — bare `register`/`tick` on a
    // concurrent chain doesn't count.
    if (!isPublishMethod(method)) return false;
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = chain_start;
    while (t < method_tok) : (t += 1) {
        if (tags[t] != .identifier) continue;
        const seg = tree.tokenSlice(t);
        if (isConcurrencyChainToken(seg)) return true;
    }
    return false;
}

fn isObserverMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "register") or
        std.mem.eql(u8, name, "unregister") or
        std.mem.eql(u8, name, "subscribe") or
        std.mem.eql(u8, name, "unsubscribe") or
        std.mem.eql(u8, name, "observe") or
        std.mem.eql(u8, name, "tick") or
        std.mem.eql(u8, name, "step");
}

fn isPublishMethod(name: []const u8) bool {
    return std.mem.eql(u8, name, "push") or
        std.mem.eql(u8, name, "send") or
        std.mem.eql(u8, name, "submit") or
        std.mem.eql(u8, name, "enqueue") or
        std.mem.eql(u8, name, "post") or
        std.mem.eql(u8, name, "schedule") or
        std.mem.eql(u8, name, "dispatch");
}

fn containsConcurrencyToken(name: []const u8) bool {
    // Only `Concurrent` as a suffix is a reliable signal of
    // ownership transfer (`enqueueTaskConcurrent`,
    // `postConcurrent`).  `Thread` / `Cross` / `Async` are too
    // loose — `toThreadSafe` (a synchronous converter), `register`
    // on a `ThreadPool` (an observer, not a publisher), and many
    // async helpers don't transfer ownership.
    return std.mem.endsWith(u8, name, "Concurrent");
}

fn isExactConcurrentMethod(name: []const u8) bool {
    // Narrow allowlist of methods that conventionally PUBLISH
    // (transfer ownership of) their argument to a different
    // thread / queue / pool.  Excludes:
    //   - `register` / `unregister` / `subscribe` — observation,
    //     not transfer.
    //   - `dispatch` — too generic; many synchronous "dispatch
    //     to handler" patterns use this name.
    //   - `spawn` — typically a constructor, not a transfer
    //     of an existing `this`.
    return std.mem.eql(u8, name, "postToMain") or
        std.mem.eql(u8, name, "postTask") or
        std.mem.eql(u8, name, "scheduleTask") or
        std.mem.eql(u8, name, "enqueueTaskConcurrent") or
        std.mem.eql(u8, name, "submitConcurrent");
}

fn isConcurrencyChainToken(name: []const u8) bool {
    // Exact short keywords
    if (std.mem.eql(u8, name, "queue") or
        std.mem.eql(u8, name, "pool") or
        std.mem.eql(u8, name, "thread") or
        std.mem.eql(u8, name, "cross_thread") or
        std.mem.eql(u8, name, "concurrent") or
        std.mem.eql(u8, name, "dispatcher") or
        std.mem.eql(u8, name, "scheduler") or
        std.mem.eql(u8, name, "work_pool") or
        std.mem.eql(u8, name, "workPool") or
        std.mem.eql(u8, name, "thread_pool") or
        std.mem.eql(u8, name, "threadPool")) return true;
    // Compound names: `*_queue` / `*Queue` (task_queue, patch_task_queue,
    // async_network_task_queue, …) are clearly concurrent queues even though
    // they don't match the short exact form above.
    if (std.mem.indexOf(u8, name, "queue") != null) return true;
    // Compound pool names: `*_pool` / `*Pool`
    if (std.mem.endsWith(u8, name, "_pool") or
        std.mem.endsWith(u8, name, "Pool")) return true;
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    use_tok: Ast.TokenIndex,
    method: []const u8,
    arg: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "use of `{s}` after `.{s}({s})` published it to a concurrent queue / thread pool — the consumer may have freed `{s}` before this access lands.  Hoist any post-publish reads into locals BEFORE the publish call",
        .{ arg, method, arg, arg },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "publish-then-touch-self",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, use_tok),
        .end = try Pos.fromTokenEnd(tree, use_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "publish-then-touch-self: queue.push(this) then this.field fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const bun = struct { pub fn destroy(x: anytype) void { _ = x; } };
        \\const Self = struct {
        \\    vm: usize,
        \\    pub fn dispatch(this: *Self, store: anytype) void {
        \\        store.queue.push(this);
        \\        _ = this.vm;
        \\    }
        \\    pub fn deinit(this: *Self) void { bun.destroy(this); }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("publish-then-touch-self", problems.items[0].rule_id);
}

test "publish-then-touch-self: Concurrent-named method also caught" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const bun = struct { pub fn destroy(x: anytype) void { _ = x; } };
        \\const Self = struct {
        \\    x: u32,
        \\    pub fn work(self: *Self, loop: anytype) void {
        \\        loop.enqueueTaskConcurrent(self);
        \\        _ = self.x;
        \\    }
        \\    pub fn deinit(self: *Self) void { bun.destroy(self); }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "publish-then-touch-self: hoisted reads before publish doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Self = struct {
        \\    vm: usize,
        \\    pub fn dispatch(this: *Self, store: anytype) void {
        \\        const vm = this.vm;
        \\        _ = vm;
        \\        store.queue.push(this);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "publish-then-touch-self: non-concurrent receiver/method doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Self = struct {
        \\    x: u32,
        \\    pub fn work(self: *Self, list: anytype) void {
        \\        list.append(self);
        \\        _ = self.x;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "publish-then-touch-self: thread_pool.dispatch(this) caught" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const bun = struct { pub fn destroy(x: anytype) void { _ = x; } };
        \\const Self = struct {
        \\    x: u32,
        \\    pub fn work(this: *Self, ctx: anytype) void {
        \\        ctx.thread_pool.dispatch(this);
        \\        _ = this.x;
        \\    }
        \\    pub fn deinit(this: *Self) void { bun.destroy(this); }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "publish-then-touch-self: compound queue name (task_queue) caught" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        // heap-managed Self with task_queue publish then access
        \\const bun = struct { pub fn destroy(x: anytype) void { _ = x; } };
        \\const Self = struct {
        \\    installer: *Installer,
        \\    pub fn complete(this: *Self) void {
        \\        this.installer.task_queue.push(this);
        \\        this.installer.manager.wake();
        \\    }
        \\    pub fn deinit(this: *Self) void { bun.destroy(this); }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("publish-then-touch-self", problems.items[0].rule_id);
}

test "publish-then-touch-self: patch_task_queue (compound name) caught" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        // Mirrors patch_install.zig: push on compound queue name
        \\const bun = struct { pub fn destroy(x: anytype) void { _ = x; } };
        \\const Self = struct {
        \\    manager: *Manager,
        \\    pub fn complete(this: *Self) void {
        \\        this.manager.patch_task_queue.push(this);
        \\        this.manager.wake();
        \\    }
        \\    pub fn deinit(this: *Self) void { bun.destroy(this); }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "publish-then-touch-self: defer this.X before push fires after (inline)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        // Mirrors patch_install.zig notify(): defer fires AFTER push at fn exit
        \\const bun = struct { pub fn destroy(x: anytype) void { _ = x; } };
        \\const Self = struct {
        \\    manager: *Manager,
        \\    pub fn notify(this: *Self) void {
        \\        defer this.manager.wake();
        \\        this.manager.patch_task_queue.push(this);
        \\    }
        \\    pub fn deinit(this: *Self) void { bun.destroy(this); }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("publish-then-touch-self", problems.items[0].rule_id);
}

test "publish-then-touch-self: defer this.X before push fires after (block)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        // Block-form defer — same hazard
        \\const bun = struct { pub fn destroy(x: anytype) void { _ = x; } };
        \\const Self = struct {
        \\    manager: *Manager,
        \\    pub fn notify(this: *Self) void {
        \\        defer { this.manager.wake(); }
        \\        this.manager.task_queue.push(this);
        \\    }
        \\    pub fn deinit(this: *Self) void { bun.destroy(this); }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "publish-then-touch-self: non-self defer before push doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        // `defer other.cleanup()` — not `this`/`self`, safe
        \\const Self = struct {
        \\    manager: *Manager,
        \\    pub fn notify(this: *Self, other: anytype) void {
        \\        defer other.cleanup();
        \\        this.manager.task_queue.push(this);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "publish-then-touch-self: type with no self-destructor suppressed (Installer.Task FP)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        // Mirrors Installer.zig: Task lives in `tasks: []Task` (slice element,
        // never bun.destroy'd).  No self-freeing method → suppress.
        \\const Task = struct {
        \\    installer: *Installer,
        \\    pub fn complete(this: *Task) void {
        \\        this.installer.task_queue.push(this);
        \\        this.installer.manager.wake();
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "publish-then-touch-self: type with bun.destroy(this) kept (PatchTask TP)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        // Mirrors patch_install.zig: PatchTask is bun.new'd and bun.destroy'd
        // in deinit() — self-freeing destructor → keep the finding.
        \\const bun = struct { pub fn destroy(x: anytype) void { _ = x; } };
        \\const PatchTask = struct {
        \\    manager: *Manager,
        \\    pub fn notify(this: *PatchTask) void {
        \\        this.manager.patch_task_queue.push(this);
        \\        this.manager.wake();
        \\    }
        \\    pub fn deinit(this: *PatchTask) void {
        \\        bun.destroy(this);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("publish-then-touch-self", problems.items[0].rule_id);
}
