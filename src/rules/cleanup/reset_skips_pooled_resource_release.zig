//! A struct has both `deinit` and `reset` methods.  `deinit` calls
//! release/free/destroy/close/deinit on owned handles (typically
//! pool slots or external resources).  `reset` either does nothing
//! for those handles or just zeroes the struct.  State is logically
//! "freed" after `reset` but the pool / sub-allocator still
//! considers slots held → leak.
//!
//! Real-world: tigerbeetle/tigerbeetle#3436 (`SegmentedArray.reset`
//! forgot to release pool nodes that `deinit` does release;
//! callers expected reset to free pool capacity) and
//! tigerbeetle/tigerbeetle#1734 (`scan_buffer_pool` — same shape).
//!
//! Detection (token-walk per file):
//!   1. Walk for `keyword_struct` followed by `{` to find struct
//!      bodies.
//!   2. Within each struct body, find `pub fn deinit(` and
//!      `pub fn reset(` decls.
//!   3. For each, collect the set of `<obj>.<cleanup>(` calls
//!      where cleanup ∈ {`release`, `free`, `destroy`, `close`,
//!      `deinit`, `unref`, `deref`}.
//!   4. If `deinit` calls any `<obj>.<cleanup>` that `reset`
//!      doesn't, fire on the `reset` fn name.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const testing = @import("../../testing.zig");
const matchBrace = tokens.matchBrace;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .reset_skips_pooled_resource_release)) return;
    _ = cache;

    if (tree.tokens.len == 0) return;
    const tags = tree.tokens.items(.tag);
    // The root decl runs to the final token of the stream, so its last token
    // is exactly the old `tok_count - 1` — the exclusive upper bound the walk
    // below needs — without narrowing a `usize` length into the token index
    // type on the way in.
    const last: Ast.TokenIndex = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 1 < last) : (t += 1) {
        if (tags[t] != .keyword_struct) continue;
        if (tags[t + 1] != .l_brace) continue;
        const body_start = t + 1;
        const body_end = matchBrace(tags, body_start, last) orelse continue;
        try checkStruct(gpa, tree, body_start + 1, body_end - 1, problems);
        t = body_end;
    }
}

const FnInfo = struct {
    name_tok: Ast.TokenIndex,
    body_start: Ast.TokenIndex,
    body_end: Ast.TokenIndex,
};

fn checkStruct(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    var deinit_fn: ?FnInfo = null;
    var reset_fn: ?FnInfo = null;

    // Cross-fn analysis input: bodies of all non-lifecycle methods
    // (everything that isn't init/deinit/reset/clear).  If one of
    // these methods re-acquires the resource, then it's per-cycle
    // and reset MUST release.  If no non-lifecycle method touches
    // the resource, the resource is pool-lifetime and reset's
    // omission is intentional.
    var other_fns: std.ArrayListUnmanaged(FnInfo) = .empty;
    defer other_fns.deinit(gpa);

    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] == .l_brace) {
            t = matchBrace(tags, t, end) orelse break;
            continue;
        }
        if (tags[t] != .keyword_fn) continue;
        if (tags[t + 1] != .identifier) continue;
        const name = tree.tokenSlice(t + 1);
        const is_deinit = std.mem.eql(u8, name, "deinit");
        const is_reset = std.mem.eql(u8, name, "reset");
        const is_init = std.mem.eql(u8, name, "init");
        const is_clear = std.mem.eql(u8, name, "clear") or
            std.mem.eql(u8, name, "clearRetainingCapacity") or
            std.mem.eql(u8, name, "clearAndFree");
        // Find the body `{` for this fn.
        var u: Ast.TokenIndex = t + 2;
        while (u <= end and tags[u] != .l_brace) : (u += 1) {}
        if (u > end) break;
        const fn_body_end = matchBrace(tags, u, end) orelse break;
        const info: FnInfo = .{
            .name_tok = t + 1,
            .body_start = u + 1,
            .body_end = fn_body_end - 1,
        };
        if (is_deinit and deinit_fn == null) deinit_fn = info;
        if (is_reset and reset_fn == null) reset_fn = info;
        if (!is_deinit and !is_reset and !is_init and !is_clear) {
            try other_fns.append(gpa, info);
        }
        t = fn_body_end;
    }

    if (deinit_fn == null or reset_fn == null) return;

    var deinit_cleanups: std.ArrayListUnmanaged(Cleanup) = .empty;
    defer deinit_cleanups.deinit(gpa);
    try collectCleanups(gpa, tree, deinit_fn.?.body_start, deinit_fn.?.body_end, &deinit_cleanups);

    var reset_cleanups: std.ArrayListUnmanaged(Cleanup) = .empty;
    defer reset_cleanups.deinit(gpa);
    try collectCleanups(gpa, tree, reset_fn.?.body_start, reset_fn.?.body_end, &reset_cleanups);

    // Find cleanups in deinit that aren't in reset.  Match by
    // RECEIVER only — `cache.deinit(alloc)` in deinit and
    // `cache.reset()` / `cache.clearRetainingCapacity()` in reset
    // both qualify as "cleanup on the same receiver".
    //
    // Suppression layers (semantic signals):
    //  (1) Receiver-matched cleanup in reset → suppress.
    //  (2) Reset is a PARTIAL CLEAR — it already does ≥1 cleanup
    //      but doesn't touch this receiver → suppress.  The author
    //      has demonstrated cleanup-awareness; receivers they
    //      didn't touch are intentionally persistent (e.g.,
    //      IncrementalGraph.reset clears current-chunk state but
    //      intentionally leaves graph state alone).
    //  (3) Cross-fn analysis — only run when reset is a MINIMAL
    //      reset (no cleanups at all).  If a non-lifecycle method
    //      re-acquires the receiver → per-cycle leak (fire).  If
    //      not → pool-lifetime (suppress).
    const reset_has_any_cleanup = reset_cleanups.items.len > 0;
    for (deinit_cleanups.items) |dc| {
        var matched_in_reset = false;
        for (reset_cleanups.items) |rc| {
            if (std.mem.eql(u8, dc.recv, rc.recv)) {
                matched_in_reset = true;
                break;
            }
        }
        if (matched_in_reset) continue;
        // Layer 2: partial-clear suppression.  Reset has cleanup
        // logic but intentionally skipped this receiver — author
        // was aware of cleanup duties and chose to leave this
        // resource alone (canonical pattern: state-machine reset
        // clears current-cycle state, leaves persistent state).
        if (reset_has_any_cleanup) continue;
        // Layer 3: cross-fn analysis for minimal resets (no
        // cleanups at all).  If a non-lifecycle method re-acquires
        // the receiver → per-cycle leak (fire).  If not →
        // pool-lifetime (suppress).
        if (!receiverReacquiredElsewhere(tree, other_fns.items, dc.recv)) continue;
        try report(gpa, problems, tree, reset_fn.?.name_tok, dc);
    }
}

/// True iff some non-lifecycle method body contains a call
/// `<recv>.<acquire-method>(` matching the cleanup's receiver.
/// `<acquire-method>` allowlist: methods that conventionally take a
/// fresh ref / pool slot, paired with the cleanup-release methods.
fn receiverReacquiredElsewhere(
    tree: *const Ast,
    others: []const FnInfo,
    recv: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    for (others) |fn_info| {
        var t: Ast.TokenIndex = fn_info.body_start;
        while (t + 3 <= fn_info.body_end) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
            if (tags[t + 1] != .period) continue;
            if (tags[t + 2] != .identifier) continue;
            if (tags[t + 3] != .l_paren) continue;
            const m = tree.tokenSlice(t + 2);
            if (isAcquireMethodName(m)) return true;
        }
    }
    return false;
}

fn isAcquireMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "acquire") or
        std.mem.eql(u8, name, "reference") or
        std.mem.eql(u8, name, "retain") or
        std.mem.eql(u8, name, "addRef") or
        std.mem.eql(u8, name, "addref") or
        std.mem.eql(u8, name, "ref") or
        std.mem.eql(u8, name, "take") or
        std.mem.eql(u8, name, "grab") or
        std.mem.eql(u8, name, "request") or
        std.mem.eql(u8, name, "alloc") or
        std.mem.eql(u8, name, "create") or
        std.mem.eql(u8, name, "init") or
        std.mem.eql(u8, name, "get_block") or
        std.mem.eql(u8, name, "get_node") or
        std.mem.eql(u8, name, "get_buffer") or
        std.mem.eql(u8, name, "append") or
        std.mem.eql(u8, name, "appendSlice");
}

const Cleanup = struct {
    recv: []const u8,
    method: []const u8,
};

fn collectCleanups(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    out: *std.ArrayListUnmanaged(Cleanup),
) !void {
    const tags = tree.tokens.items(.tag);
    if (start > end) return;
    var t: Ast.TokenIndex = start;
    while (t + 3 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        const method = tree.tokenSlice(t + 2);
        if (!isCleanupMethodName(method)) continue;
        const recv = tree.tokenSlice(t);
        // Skip allocator-ish receivers — `alloc.free(self.nodes)`
        // in deinit is freeing the BACKING STORAGE, which `reset`
        // legitimately keeps (reset's whole point is to keep
        // capacity).  The bug shape this rule targets is missing
        // POOL-slot releases — external resources owned by a pool /
        // refcount helper, not the struct's own heap memory.
        if (isAllocatorishName(recv)) continue;
        // Dedup.
        var already = false;
        for (out.items) |c| {
            if (std.mem.eql(u8, c.recv, recv) and std.mem.eql(u8, c.method, method)) {
                already = true;
                break;
            }
        }
        if (!already) {
            try out.append(gpa, .{ .recv = recv, .method = method });
        }
    }
}

const isAllocatorishName = method_names.isAllocatorishName;

fn isCleanupMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "release") or
        std.mem.eql(u8, name, "free") or
        std.mem.eql(u8, name, "destroy") or
        std.mem.eql(u8, name, "close") or
        std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "unref") or
        std.mem.eql(u8, name, "deref") or
        // Reset-side equivalents: receiver-matching against these
        // counts as "reset cleans up this resource."  Includes
        // common variants across std and project-specific naming
        // (`clearAndRetainCapacity` is Ghostty's variant).
        std.mem.eql(u8, name, "reset") or
        std.mem.eql(u8, name, "clear") or
        std.mem.eql(u8, name, "clearRetainingCapacity") or
        std.mem.eql(u8, name, "clearAndRetainCapacity") or
        std.mem.eql(u8, name, "clearAndFree") or
        std.mem.eql(u8, name, "shrinkRetainingCapacity") or
        std.mem.eql(u8, name, "shrinkAndFree");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    reset_name_tok: Ast.TokenIndex,
    missing: Cleanup,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`reset` is missing `{s}.{s}(...)` — `deinit` releases this resource but `reset` doesn't, so callers using `reset` to free the struct will leak the pool / sub-allocator slot",
        .{ missing.recv, missing.method },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "reset-skips-pooled-resource-release",
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, reset_name_tok),
        .end = Pos.fromTokenEnd(tree, reset_name_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "reset-skips: deinit releases pool, reset doesn't, AND per-cycle acquire elsewhere — fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const NodePool = struct {
        \\    pub fn acquire(_: *NodePool) *u8 { return undefined; }
        \\    pub fn release(_: *NodePool, _: anytype) void {}
        \\};
        \\const SegmentedArray = struct {
        \\    nodes: []*u8,
        \\    node_count: usize,
        \\    pub fn deinit(self: *SegmentedArray, alloc: std.mem.Allocator, node_pool: *NodePool) void {
        \\        for (self.nodes[0..self.node_count]) |node| node_pool.release(node);
        \\        alloc.free(self.nodes);
        \\    }
        \\    pub fn reset(self: *SegmentedArray) void {
        \\        self.node_count = 0;
        \\    }
        \\    pub fn grow(self: *SegmentedArray, node_pool: *NodePool) void {
        \\        self.nodes[self.node_count] = node_pool.acquire();
        \\        self.node_count += 1;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
    try std.testing.expectEqualStrings("reset-skips-pooled-resource-release", problems.items[0].rule_id);
}

test "reset-skips: partial-clear (reset does some cleanup) suppresses non-touched receivers" {
    // Real-world IncrementalGraph pattern — reset clears only the
    // current-chunk state (intentionally) while deinit tears down
    // the entire graph including persistent fields.  The presence
    // of ANY cleanup in reset signals the author was aware; the
    // fields they didn't touch are intentionally persistent.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Pool = struct {
        \\    pub fn release(_: *Pool, _: anytype) void {}
        \\    pub fn acquire(_: *Pool) *u8 { return undefined; }
        \\};
        \\const G = struct {
        \\    bundled_files: std.ArrayList(u8),
        \\    current_chunk: std.ArrayList(u8),
        \\    nodes: []*u8,
        \\    node_count: usize,
        \\    pub fn deinit(g: *G, alloc: std.mem.Allocator, pool: *Pool) void {
        \\        g.bundled_files.deinit(alloc);
        \\        g.current_chunk.deinit(alloc);
        \\        for (g.nodes[0..g.node_count]) |n| pool.release(n);
        \\    }
        \\    pub fn reset(g: *G) void {
        \\        g.current_chunk.clearRetainingCapacity();
        \\    }
        \\    pub fn use(g: *G, pool: *Pool) void {
        \\        g.nodes[g.node_count] = pool.acquire();
        \\        g.node_count += 1;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    // `reset` clears `current_chunk` and intentionally leaves
    // `bundled_files` and `pool` (graph state) alone.  Even though
    // `use` re-acquires from `pool` (per-cycle signal), the
    // partial-clear heuristic suppresses the fire.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: pool-lifetime asymmetry (no non-init acquire) is suppressed" {
    // Canonical ScanBufferPool shape — resources are acquired once
    // in init, released in deinit; reset just zeros the counter.
    // No other method re-acquires, so the asymmetry is intentional
    // and must NOT fire.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Grid = struct { pub fn block_unref(_: *Grid, _: anytype) void {} };
        \\const ScanBuffer = struct {
        \\    index_block: u32,
        \\    pub fn init(self: *ScanBuffer, _: *Grid) void { self.* = .{ .index_block = 0 }; }
        \\    pub fn deinit(self: *ScanBuffer, grid: *Grid) void { grid.block_unref(self.index_block); }
        \\};
        \\const ScanBufferPool = struct {
        \\    scan_buffers: [4]ScanBuffer,
        \\    scan_buffer_used: u8,
        \\    pub fn init(self: *ScanBufferPool, grid: *Grid) void {
        \\        self.scan_buffer_used = 0;
        \\        for (&self.scan_buffers) |*sb| sb.init(grid);
        \\    }
        \\    pub fn deinit(self: *ScanBufferPool, grid: *Grid) void {
        \\        for (&self.scan_buffers) |*sb| sb.deinit(grid);
        \\    }
        \\    pub fn reset(self: *ScanBufferPool) void {
        \\        self.scan_buffer_used = 0;
        \\    }
        \\    pub fn acquire(self: *ScanBufferPool) *ScanBuffer {
        \\        const r = &self.scan_buffers[self.scan_buffer_used];
        \\        self.scan_buffer_used += 1;
        \\        return r;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: deinit and reset both release — doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const NodePool = struct {
        \\    pub fn release(_: *NodePool, _: anytype) void {}
        \\};
        \\const SegmentedArray = struct {
        \\    nodes: []*u8,
        \\    node_count: usize,
        \\    pub fn deinit(self: *SegmentedArray, alloc: std.mem.Allocator, node_pool: *NodePool) void {
        \\        for (self.nodes[0..self.node_count]) |node| node_pool.release(node);
        \\        alloc.free(self.nodes);
        \\    }
        \\    pub fn reset(self: *SegmentedArray, node_pool: *NodePool) void {
        \\        for (self.nodes[0..self.node_count]) |node| node_pool.release(node);
        \\        self.node_count = 0;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: no deinit/reset pair doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct {
        \\    pub fn deinit(_: *T) void {}
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: pool-release in deinit only — fires (allocator-only deinit doesn't)" {
    // Allocator-only deinit (`gpa.free(self.x)`, `alloc.destroy(...)`)
    // is intentionally NOT a trigger — reset legitimately keeps
    // backing storage.  Only POOL / EXTERNAL-resource releases
    // missing from reset count as bugs.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct {
        \\    pub fn deinit(self: *T, gpa: std.mem.Allocator) void {
        \\        gpa.destroy(self);
        \\    }
        \\    pub fn reset(self: *T) void {
        \\        self.* = .{};
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    // allocator-only cleanup: NOT a bug per rule scope.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: pool-release in deinit with per-cycle reference() elsewhere — fires" {
    // Per-cycle: another method calls `rc.reference()`, so the
    // resource is acquired per-cycle and reset must release it.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Refcount = struct {
        \\    pub fn reference(_: *Refcount) void {}
        \\    pub fn release(_: *Refcount) void {}
        \\};
        \\const T = struct {
        \\    rc: *Refcount,
        \\    pub fn deinit(self: *T) void { self.rc.release(); }
        \\    pub fn reset(self: *T) void { _ = self; }
        \\    pub fn use(self: *T) void { self.rc.reference(); }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
}
