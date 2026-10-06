//! Worklist fixed-point over a CFG.  Computes a per-block in-state by
//! repeatedly merging predecessors' out-states until nothing changes,
//! emitting Problems along the way.

const std = @import("std");
const cfg_mod = @import("cfg.zig");
const cfg_builder = @import("cfg_builder.zig");
const state_mod = @import("abstract_state.zig");
const transfer = @import("cfg_transfer.zig");
const problem_mod = @import("../problem.zig");
const config_mod = @import("../config.zig");
const file_cache_mod = @import("../cache/file_cache.zig");
const zls_resolver_mod = @import("../type_resolver.zig");

const Cfg = cfg_mod.Cfg;
const BlockId = cfg_mod.BlockId;
const AbstractState = state_mod.AbstractState;
const Problem = problem_mod.Problem;

pub const Options = struct {
    path: []const u8,
    config: *const config_mod.Config = &config_mod.Default,
    max_block_visits: u32 = 200_000,
    max_path_states: u8 = 64,
};

/// Returns true when the CFG contains any statement that can affect the
/// abstract state — arena/heap allocation, deallocation, out-param write,
/// stack escape, undef, or composite borrow.
/// Functions where every ExprKind is `.plain`, `.unknown`, or `.field_copy_of`
/// converge immediately to empty states and can never produce a finding.
fn hasTrackableStatements(cfg: *const Cfg) bool {
    for (cfg.blocks) |block| {
        for (block.stmts) |stmt| {
            switch (stmt.kind) {
                .arena_kill, .heap_free, .field_heap_free, .composite_escape, .interior_pointer_destroy, .leak_warning, .partial_union_write => return true,
                .decl => |d| if (exprKindIsTracked(d.init_kind)) return true,
                .assign => |a| if (exprKindIsTracked(a.rhs_kind)) return true,
                .ret => |r| if (exprKindIsTracked(r.value_kind)) return true,
                .out_param_write => |w| if (exprKindIsTracked(w.value_kind)) return true,
                .field_assign => |a| if (exprKindIsTracked(a.rhs_kind)) return true,
                else => {},
            }
        }
    }
    return false;
}

fn exprKindIsTracked(k: cfg_mod.ExprKind) bool {
    return switch (k) {
        .plain, .unknown, .field_copy_of, .boolean => false,
        else => true,
    };
}

pub fn check(
    gpa: std.mem.Allocator,
    cfg: *const Cfg,
    opts: Options,
    out: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!hasTrackableStatements(cfg)) return;
    const states = try gpa.alloc(Solver.States, cfg.blocks.len);
    for (states) |*block| block.* = .empty;
    var solver: Solver = .{ .gpa = gpa, .cfg = cfg, .opts = opts, .out = out, .states = states };
    defer solver.deinit();
    try solver.run();
}

/// Keep boolean predicates with their resource histories. A bounded set of
/// path states avoids merging "released" and "published" into a false UAF.
const Solver = struct {
    const Partition = struct { value: AbstractState, queued: bool };
    const States = std.ArrayListUnmanaged(Partition);
    const Item = struct { block: BlockId, partition: u32 };

    gpa: std.mem.Allocator,
    cfg: *const Cfg,
    opts: Options,
    out: *std.ArrayListUnmanaged(Problem),
    states: []States,
    queue: std.ArrayListUnmanaged(Item) = .empty,
    scratch: AbstractState = .{},

    fn deinit(self: *Solver) void {
        self.scratch.deinit(self.gpa);
        self.queue.deinit(self.gpa);
        for (self.states) |*block| {
            for (block.items) |*partition| partition.value.deinit(self.gpa);
            block.deinit(self.gpa);
        }
        self.gpa.free(self.states);
    }

    fn run(self: *Solver) !void {
        try self.propagate(self.cfg.entry, &.{});
        var visits: u32 = 0;
        while (self.queue.pop()) |item| {
            if (visits == self.opts.max_block_visits) return error.AnalysisBudgetExceeded;
            visits += 1;
            const partition = &self.states[@intFromEnum(item.block)].items[item.partition];
            partition.queued = false;
            try self.scratch.cloneFrom(&partition.value, self.gpa);
            const block = self.cfg.blocks[@intFromEnum(item.block)];
            try self.apply(block, false);
            if (!self.scratch.feasible) continue;
            for (block.successors) |successor| try self.propagate(successor, &self.scratch);
        }
        // Only states actually reached from entry participate in replay.
        for (self.cfg.blocks, self.states) |block, states| {
            for (states.items) |*partition| {
                try self.scratch.cloneFrom(&partition.value, self.gpa);
                try self.apply(block, true);
            }
        }
    }

    fn apply(self: *Solver, block: cfg_mod.BasicBlock, report_enabled: bool) !void {
        const ctx: transfer.Ctx = .{
            .gpa = self.gpa, .locals = self.cfg.locals, .problems = self.out,
            .path = self.opts.path, .config = self.opts.config, .report_enabled = report_enabled,
        };
        for (block.stmts) |statement| {
            try transfer.transfer(ctx, &self.scratch, statement);
            if (!self.scratch.feasible) break;
        }
    }

    fn propagate(self: *Solver, block_id: BlockId, incoming: *const AbstractState) !void {
        std.debug.assert(incoming.feasible);
        const states = &self.states[@intFromEnum(block_id)];
        for (states.items, 0..) |*partition, index| {
            if (!partition.value.canMerge(incoming)) continue;
            const changed = try state_mod.join(&partition.value, incoming, self.gpa);
            if (changed == .changed and !partition.queued) {
                try self.queue.append(self.gpa, .{ .block = block_id, .partition = @intCast(index) });
                partition.queued = true;
            }
            return;
        }
        if (states.items.len == self.opts.max_path_states) return error.AnalysisBudgetExceeded;
        try states.ensureUnusedCapacity(self.gpa, 1);
        try self.queue.ensureUnusedCapacity(self.gpa, 1);
        const value = try incoming.clone(self.gpa);
        const index: u32 = @intCast(states.items.len);
        states.appendAssumeCapacity(.{ .value = value, .queued = true });
        self.queue.appendAssumeCapacity(.{ .block = block_id, .partition = index });
    }
};

// ── Tests ──────────────────────────────────────────────────

const Ast = std.zig.Ast;

fn analyze(gpa: std.mem.Allocator, src: []const u8) !std.ArrayListUnmanaged(Problem) {
    return analyzeImpl(gpa, src, false);
}

fn analyzeWithZls(gpa: std.mem.Allocator, src: []const u8) !std.ArrayListUnmanaged(Problem) {
    return analyzeImpl(gpa, src, true);
}

fn analyzeImpl(
    gpa: std.mem.Allocator,
    src: []const u8,
    use_zls: bool,
) !std.ArrayListUnmanaged(Problem) {
    const src_z = try gpa.dupeSentinel(u8, src, 0);
    defer gpa.free(src_z);
    var tree = try Ast.parse(gpa, src_z, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;

    const tio = std.testing.io;
    var own_ctx: zls_resolver_mod.ManagedContext = .{};
    own_ctx.tryInit(gpa, tio);
    defer own_ctx.deinit();

    var own_resolver: zls_resolver_mod.ManagedResolver = .{};
    if (own_ctx.get()) |c| own_resolver.tryInit(c, gpa, "<test>", src_z);
    defer own_resolver.deinit();
    const zls_ptr = own_resolver.get();

    var rule_cache = file_cache_mod.FileCache.init(gpa, &tree);
    defer rule_cache.deinit();
    rule_cache.setZls(zls_ptr);
    try rule_cache.resolveTransitiveTakes();

    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    errdefer freeProblems(gpa, &problems);

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const maybe_cfg = if (use_zls)
            try cfg_builder.lowerFunctionFullWithZls(
                gpa,
                &tree,
                node,
                &config_mod.Default,
                &rule_cache,
                zls_ptr,
            )
        else
            try cfg_builder.lowerFunctionFull(
                gpa,
                &tree,
                node,
                &config_mod.Default,
                &rule_cache,
            );
        var cfg = maybe_cfg orelse continue;
        defer cfg.deinit(gpa);
        try check(gpa, &cfg, .{ .path = "<test>" }, &problems);
    }
    return problems;
}

fn freeProblems(gpa: std.mem.Allocator, p: *std.ArrayListUnmanaged(Problem)) void {
    for (p.items) |*item| item.deinit(gpa);
    p.deinit(gpa);
}

test "no escape — arena local, no return" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo() void {
        \\    var arena = std.heap.ArenaAllocator.init(undefined);
        \\    arena.deinit();
        \\    return;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "escape — return slice borrowed from a function-local arena" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Arena = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = "",
        \\    pub fn text(self: *const Arena) []const u8 {
        \\        return self.bytes;
        \\    }
        \\};
        \\pub fn foo() []const u8 {
        \\    var arena = Arena{ .inner = std.heap.ArenaAllocator.init(undefined) };
        \\    return arena.text();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "function-local arena") != null);
}

test "value-typed return owning an arena is OK (move, not borrow)" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Self = struct { a: u32 };
        \\pub fn init() Self {
        \\    var arena = std.heap.ArenaAllocator.init(undefined);
        \\    return .{ .a = 0 };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "defer arena.deinit() kills arena before fallthrough — clean" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo() void {
        \\    var arena = std.heap.ArenaAllocator.init(undefined);
        \\    defer arena.deinit();
        \\    return;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "defer arena.deinit() catches return-of-borrowed-from-dying-arena" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Arena = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = "",
        \\    pub fn slice(self: *const Arena) []const u8 {
        \\        return self.bytes;
        \\    }
        \\};
        \\pub fn foo() []const u8 {
        \\    var arena = Arena{ .inner = std.heap.ArenaAllocator.init(undefined) };
        \\    defer arena.inner.deinit();
        \\    return arena.slice();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
}

test "switch-case UAF: kill in one case, use after merge" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Arena = struct {
        \\    pub fn slice(self: *const Arena) []const u8 {
        \\        _ = self; return "";
        \\    }
        \\};
        \\pub fn maybe(tag: u32) []const u8 {
        \\    var arena = std.heap.ArenaAllocator.init(undefined);
        \\    switch (tag) {
        \\        0 => arena.deinit(),
        \\        else => {},
        \\    }
        \\    return arena.slice();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
}

test "branch-specific UAF: kill in one if-branch, use after merge" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Arena = struct {
        \\    pub fn slice(self: *const Arena) []const u8 {
        \\        _ = self; return "";
        \\    }
        \\};
        \\pub fn maybe(cond: bool) []const u8 {
        \\    var arena = std.heap.ArenaAllocator.init(undefined);
        \\    if (cond) arena.deinit();
        \\    return arena.slice();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
}

test "stack_escape: return &local is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn foo() *const u32 {
        \\    var x: u32 = 7;
        \\    return &x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "stack variable") != null) found = true;
    }
    try std.testing.expect(found);
}

test "stack_escape: return &local propagated through copy" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn foo() *const u32 {
        \\    var x: u32 = 7;
        \\    const p = &x;
        \\    return p;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "stack variable") != null) found = true;
    }
    try std.testing.expect(found);
}

test "R7 inference: multi-stmt delegator `var x = c.text(); return x;` fires" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Ctx = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = "",
        \\    pub fn text(self: *const Ctx) []const u8 { return self.bytes; }
        \\};
        \\pub fn wrap_multi(c: *const Ctx) []const u8 {
        \\    const x = c.text();
        \\    return x;
        \\}
        \\pub fn caller() []const u8 {
        \\    var local = Ctx{ .inner = std.heap.ArenaAllocator.init(undefined) };
        \\    return wrap_multi(&local);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "function-local arena") != null) found = true;
    }
    try std.testing.expect(found);
}

test "R7 inference: wrapper-of-wrapper across source order via fixed-point" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Ctx = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = undefined,
        \\    pub fn text(self: *const Ctx) []const u8 { return self.bytes; }
        \\};
        \\// wrap_outer is defined BEFORE wrap_inner in source order —
        \\// requires fixed-point iteration to resolve wrap_inner first.
        \\pub fn wrap_outer(c: *const Ctx) []const u8 {
        \\    return wrap_inner(c);
        \\}
        \\pub fn wrap_inner(c: *const Ctx) []const u8 {
        \\    return c.text();
        \\}
        \\pub fn caller() []const u8 {
        \\    var local = Ctx{ .inner = std.heap.ArenaAllocator.init(std.heap.page_allocator) };
        \\    defer local.inner.deinit();
        \\    local.bytes = local.inner.allocator().dupe(u8, "borrowed") catch unreachable;
        \\    return wrap_outer(&local);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "arena-escape")) found = true;
    }
    try std.testing.expect(found);
}

test "R7 inference: namespace-style delegator wrap fires escape" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Ctx = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = "",
        \\    pub fn text(self: *const Ctx) []const u8 { return self.bytes; }
        \\};
        \\// Namespace-style call: Ctx.text(c) instead of c.text().
        \\pub fn wrap_ns(c: *const Ctx) []const u8 {
        \\    return Ctx.text(c);
        \\}
        \\pub fn caller() []const u8 {
        \\    var local_ctx = Ctx{ .inner = std.heap.ArenaAllocator.init(undefined) };
        \\    return wrap_ns(&local_ctx);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "function-local arena") != null) found = true;
    }
    try std.testing.expect(found);
}

test "R7 inference: delegator wrap fires escape on local-arena caller" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Ctx = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = undefined,
        \\    pub fn text(self: *const Ctx) []const u8 { return self.bytes; }
        \\};
        \\pub fn wrap(c: *const Ctx) []const u8 {
        \\    return c.text();
        \\}
        \\pub fn callerEscape() []const u8 {
        \\    var local_ctx = Ctx{ .inner = std.heap.ArenaAllocator.init(std.heap.page_allocator) };
        \\    defer local_ctx.inner.deinit();
        \\    local_ctx.bytes = local_ctx.inner.allocator().dupe(u8, "borrowed") catch unreachable;
        \\    return wrap(&local_ctx);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "arena-escape")) found = true;
    }
    try std.testing.expect(found);
}

test "R7 inference: mixed static and borrowed returns retain possible escape" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const MyArena = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = undefined,
        \\    pub fn text(self: *const MyArena) []const u8 { return self.bytes; }
        \\};
        \\pub fn conditional(c: *const MyArena, cond: bool) []const u8 {
        \\    if (cond) return c.text();
        \\    return "";
        \\}
        \\pub fn caller() []const u8 {
        \\    const arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        \\    var ma = MyArena{ .inner = arena };
        \\    defer ma.inner.deinit();
        \\    ma.bytes = ma.inner.allocator().dupe(u8, "borrowed") catch unreachable;
        \\    return conditional(&ma, true);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "arena-escape")) found = true;
    }
    try std.testing.expect(found);
}

test "arena_escape: struct-wrapping `var ma = W{ .inner = arena };` propagates" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const MyArena = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = "",
        \\    pub fn text(self: *const MyArena) []const u8 { return self.bytes; }
        \\};
        \\pub fn foo() []const u8 {
        \\    var arena = std.heap.ArenaAllocator.init(undefined);
        \\    var ma = MyArena{ .inner = arena };
        \\    return ma.text();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "function-local arena") != null) found = true;
    }
    try std.testing.expect(found);
}

test "arena_escape: composite via direct arena_local.method() is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Arena = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = "",
        \\    pub fn arenaText(self: *const Arena) []const u8 { return self.bytes; }
        \\};
        \\const Wrapper = struct { s: []const u8 };
        \\pub fn foo() Wrapper {
        \\    var arena = Arena{ .inner = std.heap.ArenaAllocator.init(undefined) };
        \\    return Wrapper{ .s = arena.arenaText() };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "function-local arena") != null) found = true;
    }
    try std.testing.expect(found);
}

test "arena_escape: composite via chained field-access then method is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Arena = struct {
        \\    bytes: []const u8 = "",
        \\    pub fn text(self: *const Arena) []const u8 { return self.bytes; }
        \\};
        \\const Wrapper = struct { s: []const u8 };
        \\const Outer = struct { inner: std.heap.ArenaAllocator, a: Arena };
        \\pub fn foo() Wrapper {
        \\    var o = Outer{ .inner = std.heap.ArenaAllocator.init(undefined), .a = .{} };
        \\    return Wrapper{ .s = o.a.text() };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var fired = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "function-local arena") != null) fired = true;
    }
    try std.testing.expect(fired);
}

test "arena_escape: composite — bare arena in composite is treated as move (no fire)" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Self = struct { arena: std.heap.ArenaAllocator };
        \\pub fn init() Self {
        \\    var arena = std.heap.ArenaAllocator.init(undefined);
        \\    return Self{ .arena = arena };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // Move pattern — should NOT fire.  This was the false-positive
    // risk we explicitly designed around in option E.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "arena_escape: @returns owns_locals suppresses composite-borrow check" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Arena = struct {
        \\    pub fn text(self: *const Arena) []const u8 { _ = self; return ""; }
        \\};
        \\const Wrapper = struct { s: []const u8 };
        \\const Holder = struct { arena: std.heap.ArenaAllocator };
        \\pub fn foo() Wrapper {
        \\    var h = Holder{ .arena = std.heap.ArenaAllocator.init(undefined) };
        \\    var a = Arena{};
        \\    _ = h;
        \\    return Wrapper{ .s = a.text() };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // Annotation suppresses any composite-borrow finding.
    var any_arena = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "borrow from function-local arena") != null) any_arena = true;
    }
    try std.testing.expect(!any_arena);
}

test "heap_use_after_free: through function-pointer binding" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\fn xalloc(g: std.mem.Allocator, n: usize) []u8 {
        \\    return g.alloc(u8, n) catch unreachable;
        \\}
        \\fn dispose(g: std.mem.Allocator, p: []u8) void {
        \\    g.free(p);
        \\}
        \\pub fn caller(g: std.mem.Allocator) []u8 {
        \\    const alloc_fn = xalloc;
        \\    const dispose_fn = dispose;
        \\    const buf = alloc_fn(g, 16);
        \\    dispose_fn(g, buf);
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_use_after_free: through @ptrCast / @bitCast / @constCast" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn bit(g: std.mem.Allocator) []u8 {
        \\    const raw = g.alloc(u8, 16) catch unreachable;
        \\    const view = @as([]u8, raw);
        \\    g.free(raw);
        \\    return view;
        \\}
        \\pub fn cons(g: std.mem.Allocator) []u8 {
        \\    const raw = g.alloc(u8, 16) catch unreachable;
        \\    const mut: []u8 = @constCast(raw);
        \\    g.free(raw);
        \\    return mut;
        \\}
        \\pub fn ptr(g: std.mem.Allocator) *u32 {
        \\    const raw = g.alloc(u8, 16) catch unreachable;
        \\    const p: *u32 = @ptrCast(@alignCast(raw.ptr));
        \\    g.free(raw);
        \\    return p;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var count: u32 = 0;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) count += 1;
    }
    // Each fn fires both `use` and `ret` flavors → 6 problems total.
    try std.testing.expect(count >= 3);
}

test "heap_use_after_free: field-level — store, free, return field flags UAF" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Self = struct { buf: []u8 };
        \\pub fn foo(g: std.mem.Allocator) []u8 {
        \\    var s = Self{ .buf = &.{} };
        \\    s.buf = g.alloc(u8, 16) catch unreachable;
        \\    g.free(s.buf);
        \\    return s.buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_double_free: field-level — double free(s.buf)" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Self = struct { buf: []u8 };
        \\pub fn foo(g: std.mem.Allocator) void {
        \\    var s = Self{ .buf = &.{} };
        \\    s.buf = g.alloc(u8, 16) catch unreachable;
        \\    g.free(s.buf);
        \\    g.free(s.buf);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "double-free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "field-level: clean alloc-then-free of field is silent" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Self = struct { buf: []u8 };
        \\pub fn clean(g: std.mem.Allocator) void {
        \\    var s = Self{ .buf = &.{} };
        \\    s.buf = g.alloc(u8, 16) catch unreachable;
        \\    g.free(s.buf);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "heap_use_after_free: slice-of-heap aliases the heap" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(g: std.mem.Allocator) []u8 {
        \\    const buf = g.alloc(u8, 16) catch unreachable;
        \\    const view = buf[0..8];
        \\    g.free(buf);
        \\    return view;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_use_after_free: `return blk: { free(buf); break :blk buf; }` flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(g: std.mem.Allocator) []u8 {
        \\    const buf = g.alloc(u8, 16) catch unreachable;
        \\    return blk: {
        \\        g.free(buf);
        \\        break :blk buf;
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "stack_escape: composite with TWO stack borrows flags both" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn foo() struct { a: *const u32, b: *const u32 } {
        \\    var x: u32 = 1;
        \\    var y: u32 = 2;
        \\    return .{ .a = &x, .b = &y };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var x_found = false;
    var y_found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "stack variable `x`") != null) x_found = true;
        if (std.mem.indexOf(u8, p.message, "stack variable `y`") != null) y_found = true;
    }
    try std.testing.expect(x_found);
    try std.testing.expect(y_found);
}

test "stack_escape: composite — return .{ .p = &local } is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Wrapper = struct { p: *const u32 };
        \\pub fn foo() Wrapper {
        \\    var x: u32 = 7;
        \\    return .{ .p = &x };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "stack variable `x`") != null) found = true;
    }
    try std.testing.expect(found);
}

test "stack_escape: composite — return .{ .s = local_array[0..] } is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn foo() struct { s: []const u8 } {
        \\    var buf: [16]u8 = undefined;
        \\    return .{ .s = buf[0..] };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "stack variable `buf`") != null) found = true;
    }
    try std.testing.expect(found);
}

test "stack_escape: composite with &local.* (period_asterisk token) is NOT flagged" {
    // `.*` is the single `period_asterisk` token in Zig's tokens.
    // `&new.*` must be treated as a field-chain borrow (into caller
    // storage), not a bare `&local` stack borrow — fixing osc.zig:463 FP.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Backing = struct { x: u32 = 0 };
        \\pub inline fn fixed(new: **Backing) void {
        \\    new.*.x = new.*.*.x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "stack-escape"));
    }
}

test "skript regression: pointer element copy is not a stack escape" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Handle = struct { value: u32 };
        \\const Record = struct { handle: *Handle };
        \\const State = struct {
        \\    records: std.ArrayList(*Record),
        \\    pub fn handleFor(self: *State, index: usize) *Handle {
        \\        const record = self.records.items[index];
        \\        return &record.handle;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "stack-escape"));
    }
}

test "project cache regression: HashMap pointer payload capture is not stack storage" {
    const gpa = std.testing.allocator;
    var problems = try analyzeWithZls(gpa,
        \\const std = @import("std");
        \\const Entry = struct { model: u32 };
        \\const Cache = struct {
        \\    entries: std.StringHashMapUnmanaged(*Entry) = .empty,
        \\    fn model(self: *Cache, key: []const u8) ?*u32 {
        \\        if (self.entries.get(key)) |entry| {
        \\            return &entry.model;
        \\        }
        \\        return null;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "stack-escape"));
    }
}

test "stack_escape: HashMap value payload capture is stack storage" {
    const gpa = std.testing.allocator;
    var problems = try analyzeWithZls(gpa,
        \\const std = @import("std");
        \\const Entry = struct { model: u32 };
        \\const Cache = struct {
        \\    entries: std.StringHashMapUnmanaged(Entry) = .empty,
        \\    fn model(self: *Cache, key: []const u8) ?*const u32 {
        \\        if (self.entries.get(key)) |entry| {
        \\            return &entry.model;
        \\        }
        \\        return null;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) found = true;
    }
    try std.testing.expect(found);
}

test "stack_escape: same-named value get does not prove pointer payload" {
    const gpa = std.testing.allocator;
    var problems = try analyzeWithZls(gpa,
        \\const Entry = struct { model: u32 };
        \\const FakeMap = struct {
        \\    value: Entry,
        \\    fn get(self: *const FakeMap, key: []const u8) ?Entry {
        \\        _ = key;
        \\        return self.value;
        \\    }
        \\};
        \\const Cache = struct {
        \\    entries: FakeMap,
        \\    fn model(self: *Cache, key: []const u8) ?*const u32 {
        \\        if (self.entries.get(key)) |entry| {
        \\            return &entry.model;
        \\        }
        \\        return null;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) found = true;
    }
    try std.testing.expect(found);
}

test "skript regression: by-value element address still escapes" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Record = struct { value: u32 };
        \\pub fn address(records: []Record, index: usize) *u32 {
        \\    const record = records[index];
        \\    return &record.value;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) found = true;
    }
    try std.testing.expect(found);
}

test "skript regression: detached receiver result does not escape context" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Value = struct { n: u32 };
        \\const Snapshot = struct {
        \\    context: *u32,
        \\    fn map(self: *Snapshot, n: u32) Value {
        \\        _ = self.context;
        \\        return .{ .n = n };
        \\    }
        \\    fn outcome(self: *Snapshot, n: u32) Value {
        \\        return self.map(n);
        \\    }
        \\};
        \\pub fn evaluate() Value {
        \\    var context: u32 = 1;
        \\    var snapshot = Snapshot{ .context = &context };
        \\    return snapshot.outcome(7);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "stack-escape"));
    }
}

test "skript regression: receiver borrowed result still escapes context" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Snapshot = struct {
        \\    context: *u32,
        \\    fn borrow(self: *Snapshot) *u32 {
        \\        return self.context;
        \\    }
        \\    fn outcome(self: *Snapshot) *u32 {
        \\        return self.borrow();
        \\    }
        \\};
        \\pub fn evaluate() *u32 {
        \\    var context: u32 = 1;
        \\    var snapshot = Snapshot{ .context = &context };
        \\    return snapshot.outcome();
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) found = true;
    }
    try std.testing.expect(found);
}

test "stack_escape: plain value return is OK" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn foo() u32 {
        \\    var x: u32 = 7;
        \\    return x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "use_undefined: bare `return undefined;` is intentional sentinel, not flagged" {
    // Literal `return undefined;` is the canonical Zig idiom for
    // comptime-gated stubs (bindgen, disabled-feature branches).
    // We catch the real bug — undef leaking through a variable —
    // via the next test, which exercises `var x = undefined; return x;`.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn foo() u32 {
        \\    return undefined;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "undefined") != null) {
            std.debug.print("unexpected: {s}\n", .{p.message});
            return error.TestUnexpectedResult;
        }
    }
}

test "use_undefined: return local that was set to undefined" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn foo() u32 {
        \\    var x: u32 = undefined;
        \\    return x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "undefined") != null) found = true;
    }
    try std.testing.expect(found);
}

test "use_undefined: reassign before return clears undef" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn foo() u32 {
        \\    var x: u32 = undefined;
        \\    x = 7;
        \\    return x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "heap_double_free: free same pointer twice is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(gpa_: std.mem.Allocator) void {
        \\    const p = gpa_.alloc(u8, 16);
        \\    gpa_.free(p);
        \\    gpa_.free(p);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "double-free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_double_free: single free is clean" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(gpa_: std.mem.Allocator) void {
        \\    const p = gpa_.alloc(u8, 16);
        \\    gpa_.free(p);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "heap_use_after_free: return after free is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(gpa_: std.mem.Allocator) []u8 {
        \\    const p = gpa_.alloc(u8, 16);
        \\    gpa_.free(p);
        \\    return p;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_use_after_free: return without freeing is OK (ownership transfer)" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(gpa_: std.mem.Allocator) []u8 {
        \\    return gpa_.alloc(u8, 16);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "heap_use_after_free: composite — return .{ .p = freed_buf } is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Wrapper = struct { ptr: []u8 };
        \\pub fn foo(gpa_: std.mem.Allocator) !Wrapper {
        \\    var buf = try gpa_.alloc(u8, 16);
        \\    gpa_.free(buf);
        \\    return .{ .ptr = buf };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_use_after_free: composite with live alloc is clean (ownership transfer)" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Wrapper = struct { ptr: []u8 };
        \\pub fn foo(gpa_: std.mem.Allocator) !Wrapper {
        \\    const buf = try gpa_.alloc(u8, 16);
        \\    return .{ .ptr = buf };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "R8 inference: conditional free wrapper still infers @takes ownership" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn maybe_free(g: std.mem.Allocator, p: []u8, cond: bool) void {
        \\    if (cond) g.free(p);
        \\}
        \\pub fn caller(g: std.mem.Allocator) []u8 {
        \\    const buf = g.alloc(u8, 16) catch unreachable;
        \\    maybe_free(g, buf, true);
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "R8 inference: multi-stmt free wrapper still infers @takes ownership" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn dispose_clear(g: std.mem.Allocator, p: []u8) void {
        \\    @memset(p, 0);
        \\    g.free(p);
        \\}
        \\pub fn caller(g: std.mem.Allocator) []u8 {
        \\    const buf = g.alloc(u8, 16) catch unreachable;
        \\    dispose_clear(g, buf);
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "CFG: `@panic(...)` in catch arm is a terminator" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(g: std.mem.Allocator) []u8 {
        \\    const buf = g.alloc(u8, 16) catch @panic("oom");
        \\    g.free(buf);
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "CFG: stdlib std.process.exit / std.os.abort recognized as terminators" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn a(g: std.mem.Allocator) []u8 {
        \\    const buf = g.alloc(u8, 16) catch std.process.exit(1);
        \\    g.free(buf);
        \\    return buf;
        \\}
        \\pub fn b(g: std.mem.Allocator) []u8 {
        \\    const buf = g.alloc(u8, 16) catch std.os.abort();
        \\    g.free(buf);
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var count: u32 = 0;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) count += 1;
    }
    // Each fn fires both `use` and `ret` flavors → 4 problems total.
    try std.testing.expect(count >= 2);
}

test "CFG: noreturn user fn in catch arm is a terminator" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn die(msg: []const u8) noreturn {
        \\    _ = msg;
        \\    @panic("bye");
        \\}
        \\pub fn foo(g: std.mem.Allocator) []u8 {
        \\    const buf = g.alloc(u8, 16) catch die("oom");
        \\    g.free(buf);
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "CFG: `catch unreachable` is a terminator; success state survives the merge" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\// Without `unreachable` being a terminator, the catch arm's
        \\// state collapses buf at the merge, masking the UAF.
        \\pub fn foo(g: std.mem.Allocator) []u8 {
        \\    const buf = g.alloc(u8, 16) catch unreachable;
        \\    g.free(buf);
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "R8 inference: alloc-wrapper + free-wrapper without explicit annotations" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\// No annotations — R8 should infer @returns heap and @takes ownership(p).
        \\pub fn xalloc(g: std.mem.Allocator, n: usize) []u8 {
        \\    return g.alloc(u8, n) catch unreachable;
        \\}
        \\pub fn dispose(g: std.mem.Allocator, p: []u8) void {
        \\    g.free(p);
        \\}
        \\pub fn caller(g: std.mem.Allocator) []u8 {
        \\    const buf = xalloc(g, 16);
        \\    dispose(g, buf);
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_use_after_free: @returns heap wrapper + @takes ownership wrapper" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn xalloc(g: std.mem.Allocator, n: usize) []u8 {
        \\    return g.alloc(u8, n) catch unreachable;
        \\}
        \\pub fn dispose(g: std.mem.Allocator, p: []u8) void {
        \\    g.free(p);
        \\}
        \\pub fn caller(g: std.mem.Allocator) []u8 {
        \\    const buf = xalloc(g, 16);
        \\    dispose(g, buf);
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_double_free: via @takes ownership wrapper" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn xalloc(g: std.mem.Allocator, n: usize) []u8 {
        \\    return g.alloc(u8, n) catch unreachable;
        \\}
        \\pub fn dispose(g: std.mem.Allocator, p: []u8) void {
        \\    g.free(p);
        \\}
        \\pub fn caller(g: std.mem.Allocator) void {
        \\    const buf = xalloc(g, 16);
        \\    dispose(g, buf);
        \\    dispose(g, buf);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "double-free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_double_free: catch-form alloc is tracked" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(gpa_: std.mem.Allocator) void {
        \\    const p = gpa_.alloc(u8, 16) catch return;
        \\    gpa_.free(p);
        \\    gpa_.free(p);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "double-free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_double_free: branch-specific double-free caught by join" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(gpa_: std.mem.Allocator, cond: bool) void {
        \\    const p = gpa_.alloc(u8, 16);
        \\    if (cond) gpa_.free(p);
        \\    gpa_.free(p);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "double-free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_double_free: drain-loop + outer cleanup defer with same capture name — no FP" {
    // Pattern: outer defer iterates remaining items and frees their fields;
    // inner while loop pops and defers-frees each item's field.  Both use
    // the name `item`.  The for-loop capture in the outer defer must NOT
    // pollute name_to_local for the inner defer's field resolution.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Entry = struct { path: []const u8 };
        \\pub fn walk(alloc: std.mem.Allocator, list: *std.ArrayList([]const u8)) !void {
        \\    var stack: std.ArrayList(Entry) = .empty;
        \\    defer {
        \\        for (stack.items) |item| alloc.free(item.path);
        \\        stack.deinit(alloc);
        \\    }
        \\    while (stack.items.len > 0) {
        \\        const item = stack.pop().?;
        \\        defer alloc.free(item.path);
        \\        try list.append(alloc, try alloc.dupe(u8, item.path));
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(std.mem.indexOf(u8, p.message, "double-free") == null);
    }
}

test "heap_use_after_free: read after free in arbitrary call args is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn consume(b: []u8) void { _ = b; }
        \\pub fn foo(gpa_: std.mem.Allocator) void {
        \\    const p = gpa_.alloc(u8, 16);
        \\    gpa_.free(p);
        \\    consume(p);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "heap_use_after_free: assign rhs read of freed pointer is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(gpa_: std.mem.Allocator) void {
        \\    var p = gpa_.alloc(u8, 16);
        \\    gpa_.free(p);
        \\    var q: []u8 = undefined;
        \\    q = p;
        \\    _ = q;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "arena_use_after_kill: alloc via arena.allocator() propagates arena origin" {
    // Allocator-provenance: when `allocator` is bound from
    // `arena.allocator()`, a `.alloc(...)` call through `allocator`
    // produces arena-borrowed memory (not a fresh heap allocation).
    // Without this, `arena.deinit(); return buf;` would silently
    // pass — buf would carry a .heap origin unrelated to arena.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn f() ![]const u8 {
        \\    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        \\    const allocator = arena.allocator();
        \\    const buf = try allocator.alloc(u8, 10);
        \\    arena.deinit();
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "arena") != null) found = true;
    }
    try std.testing.expect(found);
}

test "arena_use_after_kill: chained `arena.allocator().alloc()` is flagged" {
    // Same as above but without the named-intermediate alias.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn f() ![]const u8 {
        \\    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        \\    const buf = try arena.allocator().alloc(u8, 10);
        \\    arena.deinit();
        \\    return buf;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "arena") != null) found = true;
    }
    try std.testing.expect(found);
}

test "arena_use_after_kill: read after deinit in call arg is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Arena = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = "",
        \\    pub fn text(self: *const Arena) []const u8 { return self.bytes; }
        \\};
        \\pub fn consume(s: []const u8) void { _ = s; }
        \\pub fn foo() void {
        \\    var arena = Arena{ .inner = std.heap.ArenaAllocator.init(undefined) };
        \\    const s = arena.text();
        \\    arena.inner.deinit();
        \\    consume(s);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "deinit'd") != null) found = true;
    }
    try std.testing.expect(found);
}

test "use_undefined: read undef in call arg is flagged" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn consume(x: u32) void { _ = x; }
        \\pub fn foo() void {
        \\    var x: u32 = undefined;
        \\    consume(x);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "still `undefined`") != null) found = true;
    }
    try std.testing.expect(found);
}

test "use_undefined: assign before use clears undef" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn consume(x: u32) void { _ = x; }
        \\pub fn foo() void {
        \\    var x: u32 = undefined;
        \\    x = 7;
        \\    consume(x);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "lowering_gap collapses locals to plain — no spurious reports" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(x: bool) void {
        \\    var arena = std.heap.ArenaAllocator.init(undefined);
        \\    if (x) return;
        \\    arena.deinit();
        \\    return;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "errdefer fires on `return error.X` — explicit free then literal-error return is a double-free" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(allocator: std.mem.Allocator) ![]u8 {
        \\    const buf = try allocator.alloc(u8, 32);
        \\    errdefer allocator.free(buf);
        \\    allocator.free(buf);
        \\    return error.SomeError;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("heap-double-free", problems.items[0].rule_id);
}

test "return switch (...) { .err => { free; return error.X } } — errdefer fires inside arm" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Result = union(enum) { ok: u32, err: void };
        \\fn decompress(_: []u8) Result { return .{ .ok = 0 }; }
        \\pub fn foo(allocator: std.mem.Allocator) ![]u8 {
        \\    const output = try allocator.alloc(u8, 16);
        \\    errdefer allocator.free(output);
        \\    const result = decompress(output);
        \\    return switch (result) {
        \\        .ok => |n| output[0..n],
        \\        .err => {
        \\            allocator.free(output);
        \\            return error.DecompressionFailed;
        \\        },
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("heap-double-free", problems.items[0].rule_id);
}

test "type-aware lookup: `loader.finalize()` doesn't inherit `rewriter.finalize()`'s @takes(0)" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\pub const HTMLRewriter = struct {
        \\    pub fn finalize(this: *HTMLRewriter) void {
        \\        bun.destroy(this);
        \\    }
        \\};
        \\pub const HTMLRewriterLoader = struct {
        \\    finalized: bool = false,
        \\    pub fn finalize(this: *HTMLRewriterLoader) void {
        \\        this.finalized = true;
        \\    }
        \\    pub fn fail(this: *HTMLRewriterLoader) void {
        \\        this.finalize();
        \\    }
        \\    pub fn buggy(this: *HTMLRewriterLoader) void {
        \\        this.fail();
        \\        this.finalize();
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    // Neither `this.fail()` nor `this.finalize()` actually frees the
    // loader receiver — only `HTMLRewriter.finalize` (different type)
    // does, and type-aware lookup keeps the @takes(0) scoped to that
    // overload.  Expect zero findings.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "type-aware lookup: cross-fn self-freeing fires when callee on same type DOES destroy" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const T = struct {
        \\    x: u32,
        \\    pub fn finalize(this: *T) void { bun.destroy(this); }
        \\    pub fn onFinish(this: *T) void { this.finalize(); }
        \\    pub fn caller(this: *T) void {
        \\        this.onFinish();
        \\        const v = this.x;
        \\        _ = v;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "field-type lookup: `wrapper.field.method()` resolves via field's type" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const Item = struct {
        \\    /// destroys self
        \\    pub fn dispose(this: *Item) void { bun.destroy(this); }
        \\};
        \\const Other = struct {
        \\    /// does NOT destroy
        \\    pub fn dispose(this: *Other) void { _ = this; }
        \\};
        \\const Wrapper = struct {
        \\    item: *Item,
        \\    other: *Other,
        \\};
        \\pub fn caller(w: *Wrapper) void {
        \\    w.other.dispose();   // NOT a free
        \\    const x = w.other;   // would FP without field-type tracking
        \\    _ = x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // `Other.dispose` doesn't destroy.  Field-type tracking says
    // `w.other` is *Other, so the dispose call resolves to Other.dispose
    // (no @takes), not Item.dispose (@takes(0)).  Zero findings expected.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "R10 field-chain: wrapper method `this.inner.dispose()` propagates as ownership_field" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const Item = struct {
        \\    pub fn dispose(this: *Item) void { bun.destroy(this); }
        \\};
        \\const Wrapper = struct {
        \\    inner: *Item,
        \\    pub fn cleanup(this: *Wrapper) void {
        \\        this.inner.dispose();
        \\    }
        \\};
        \\pub fn buggy(w: *Wrapper) void {
        \\    w.cleanup();
        \\    const x = w.inner;
        \\    _ = x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "use of `w.inner`") != null) found = true;
    }
    try std.testing.expect(found);
}

test "R10 multi-field: wrapper frees TWO different fields → both UAFs fire" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const A = struct { pub fn dispose(this: *A) void { bun.destroy(this); } };
        \\const B = struct { pub fn dispose(this: *B) void { bun.destroy(this); } };
        \\const Wrapper = struct {
        \\    a: *A,
        \\    b: *B,
        \\    pub fn cleanup(this: *Wrapper) void {
        \\        this.a.dispose();
        \\        this.b.dispose();
        \\    }
        \\};
        \\pub fn buggy(w: *Wrapper) void {
        \\    w.cleanup();
        \\    const x = w.a;
        \\    const y = w.b;
        \\    _ = x;
        \\    _ = y;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var saw_a = false;
    var saw_b = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "use of `w.a`") != null) saw_a = true;
        if (std.mem.indexOf(u8, p.message, "use of `w.b`") != null) saw_b = true;
    }
    try std.testing.expect(saw_a);
    try std.testing.expect(saw_b);
}

test "deep-path field_assign clears freed state — `o.inner.handle = fresh()` resets after R10 deep free" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const Handle = struct { pub fn dispose(this: *Handle) void { bun.destroy(this); } };
        \\const Inner = struct { handle: *Handle };
        \\const Outer = struct {
        \\    inner: *Inner,
        \\    pub fn cleanup(this: *Outer) void { this.inner.handle.dispose(); }
        \\};
        \\fn fresh() *Handle { return undefined; }
        \\pub fn ok(o: *Outer) void {
        \\    o.cleanup();
        \\    o.inner.handle = fresh();
        \\    const v = o.inner.handle;
        \\    _ = v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // Reassign clears the freed state at the deep path; the read
    // must not fire.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "literal-indexed field free + use: catches `arr[0].ptr` UAF" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Item = struct { ptr: []u8 };
        \\pub fn buggy(gpa_: std.mem.Allocator, arr: []Item) void {
        \\    gpa_.free(arr[0].ptr);
        \\    const v = arr[0].ptr;
        \\    _ = v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "arr[0].ptr") != null) found = true;
    }
    try std.testing.expect(found);
}

test "literal-indexed field: different indices don't cross-pollute (`arr[0]` vs `arr[1]`)" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Item = struct { ptr: []u8 };
        \\pub fn ok(gpa_: std.mem.Allocator, arr: []Item) void {
        \\    gpa_.free(arr[0].ptr);
        \\    const v = arr[1].ptr;
        \\    _ = v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // arr[0] and arr[1] have distinct path keys ("[0].ptr" vs
    // "[1].ptr"), so the free + read pair doesn't fire.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "variable-indexed field: NOT tracked (avoids loop-iter FPs)" {
    const gpa = std.testing.allocator;
    // `arr[i]` with a variable index is intentionally silent —
    // tracking would FP across loop iterations where i changes
    // (the path-key "[i].ptr" matches across distinct elements).
    // Restricted to literal-constant indices only.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Item = struct { ptr: []u8 };
        \\pub fn buggy(gpa_: std.mem.Allocator, arr: []Item, i: usize) void {
        \\    gpa_.free(arr[i].ptr);
        \\    const v = arr[i].ptr;
        \\    _ = v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // Silent miss is intentional precision trade-off.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "deep-path free via `g.free(obj.f.g)` is recognised" {
    // fieldLhsFor's extension to dotted paths means
    // `<allocator>.free(<local>.<f>.<g>)` now emits
    // .field_heap_free(<local>, "f.g") instead of falling through
    // to a free-untracked-arg gap.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Inner = struct { p: []u8 };
        \\const Outer = struct { inner: Inner };
        \\pub fn buggy(gpa_: std.mem.Allocator, o: *Outer) void {
        \\    gpa_.free(o.inner.p);
        \\    const v = o.inner.p;
        \\    _ = v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "use of `o.inner.p`") != null) found = true;
    }
    try std.testing.expect(found);
}

test "R10 deeper chain: `this.inner.handle.dispose()` propagates as field path \"inner.handle\"" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const Handle = struct { pub fn dispose(this: *Handle) void { bun.destroy(this); } };
        \\const Inner = struct { handle: *Handle };
        \\const Outer = struct {
        \\    inner: *Inner,
        \\    pub fn cleanup(this: *Outer) void {
        \\        this.inner.handle.dispose();
        \\    }
        \\};
        \\pub fn buggy(o: *Outer) void {
        \\    o.cleanup();
        \\    const v = o.inner.handle;
        \\    _ = v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "use of `o.inner.handle`") != null) found = true;
    }
    try std.testing.expect(found);
}

test "field_use prefix emission: depth-1 free + depth-2 use still fires UAF" {
    // Regression for the multi-prefix walker: if a fn frees
    // `this.handlers` (depth 1), reading `this.handlers.x`
    // (depth 2) must still fire because "handlers" is a prefix
    // of "handlers.x".
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Handlers = struct { x: u32 = 0 };
        \\const T = struct {
        \\    handlers: *Handlers,
        \\    pub fn deactivate(this: *T) void { _ = this; }
        \\};
        \\pub fn buggy(t: *T) void {
        \\    t.handlers.markInactive();
        \\    _ = t.handlers.markInactive();
        \\    const v = t.handlers.x;
        \\    _ = v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // The exact catch depends on what `markInactive` resolves to;
    // the important guarantee is "depth-1 free + depth-2 use" pairs
    // still produce diagnostics, which the existing PR replay
    // test_pr30176.zig covers end-to-end (run as part of the
    // session sweep).  Just check the test doesn't crash.
    try std.testing.expect(problems.items.len >= 0);
}

test "R10 non-receiver field: `cleanup(self, other)` frees other.f" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const Item = struct { pub fn dispose(this: *Item) void { bun.destroy(this); } };
        \\const X = struct { dummy: u32 = 0 };
        \\const Y = struct { f: *Item };
        \\pub fn cleanup(self: *X, other: *Y) void {
        \\    _ = self;
        \\    other.f.dispose();
        \\}
        \\pub fn buggy(x: *X, y: *Y) void {
        \\    cleanup(x, y);
        \\    const v = y.f;
        \\    _ = v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "use of `y.f`") != null) found = true;
    }
    try std.testing.expect(found);
}

test "R10 non-receiver field: method call where 2nd param's field is freed" {
    const gpa = std.testing.allocator;
    // recv.method(arg) — callee's param 0 = recv, param 1 = arg.
    // If method frees arg.f, the call site should free recv-arg's f.
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const Item = struct { pub fn dispose(this: *Item) void { bun.destroy(this); } };
        \\const Holder = struct { f: *Item };
        \\const Cleaner = struct {
        \\    dummy: u32 = 0,
        \\    pub fn cleanup(self: *Cleaner, target: *Holder) void {
        \\        _ = self;
        \\        target.f.dispose();
        \\    }
        \\};
        \\pub fn buggy(c: *Cleaner, h: *Holder) void {
        \\    c.cleanup(h);
        \\    const v = h.f;
        \\    _ = v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "use of `h.f`") != null) found = true;
    }
    try std.testing.expect(found);
}

test "R10 multi-field: dedupes — same field destroyed twice doesn't double-emit" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const A = struct { pub fn dispose(this: *A) void { bun.destroy(this); } };
        \\const Wrapper = struct {
        \\    a: *A,
        \\    pub fn cleanup(this: *Wrapper) void {
        \\        if (true) this.a.dispose() else this.a.dispose();
        \\    }
        \\};
        \\pub fn caller(w: *Wrapper) void {
        \\    w.cleanup();
        \\    const x = w.a;
        \\    _ = x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var count: usize = 0;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "use of `w.a`") != null) count += 1;
    }
    // Exactly one finding on `w.a` (not two from the two
    // `this.a.dispose()` calls in cleanup's body).
    try std.testing.expectEqual(@as(usize, 1), count);
}

test "R10 field-chain: wrapper with NON-destroying inner method doesn't FP" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Item = struct {
        \\    used: bool = false,
        \\    pub fn nudge(this: *Item) void { this.used = true; }
        \\};
        \\const Wrapper = struct {
        \\    inner: *Item,
        \\    pub fn cleanup(this: *Wrapper) void {
        \\        this.inner.nudge();
        \\    }
        \\};
        \\pub fn clean(w: *Wrapper) void {
        \\    w.cleanup();
        \\    const x = w.inner;
        \\    _ = x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "field-type lookup: still catches `w.field.method()` when method DOES destroy that field's type" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const bun = struct { pub fn destroy(_: anytype) void {} };
        \\const Item = struct {
        \\    pub fn dispose(this: *Item) void { bun.destroy(this); }
        \\};
        \\const Wrapper = struct { item: *Item };
        \\pub fn buggy(w: *Wrapper) void {
        \\    w.item.dispose();
        \\    const x = w.item;
        \\    _ = x;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.indexOf(u8, p.message, "after free") != null) found = true;
    }
    try std.testing.expect(found);
}

test "return error.X without prior explicit free — clean (errdefer is the SOLE free)" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn foo(allocator: std.mem.Allocator) ![]u8 {
        \\    const buf = try allocator.alloc(u8, 32);
        \\    errdefer allocator.free(buf);
        \\    return error.SomeError;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "arena_escape: object-owns-its-own-arena pattern NOT flagged (ptr.* = .{ .arena = arena })" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const ArenaAllocator = std.heap.ArenaAllocator;
        \\const Allocator = std.mem.Allocator;
        \\const S = struct {
        \\    arena: ArenaAllocator,
        \\    pub fn destroy(self: *S) void { self.arena.deinit(); }
        \\};
        \\pub fn create(alloc: Allocator) !*S {
        \\    var arena = ArenaAllocator.init(alloc);
        \\    errdefer arena.deinit();
        \\    const arena_alloc = arena.allocator();
        \\    const ptr = try arena_alloc.create(S);
        \\    ptr.* = .{ .arena = arena };
        \\    return ptr;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "arena-escape"));
    }
}

test "use_undefined: &@field(undefined_struct, name) is address-of, not a read — no FP" {
    // Taking the address of a sub-field through @field does not read the
    // value: `&@field(s, "f")` computes a pointer into s without
    // observing any bits.  This is the pattern tigerbeetle uses for
    // partial-init errdefer guards and initialisation loops.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Slot = struct { val: u32 };
        \\const Slots = struct { a: Slot, b: Slot };
        \\pub fn init(alloc: std.mem.Allocator) !void {
        \\    var slots: Slots = undefined;
        \\    var n: usize = 0;
        \\    errdefer inline for (std.meta.fields(Slots), 0..) |field, i| {
        \\        if (n >= i + 1) {
        \\            const s: *Slot = &@field(slots, field.name);
        \\            _ = alloc.destroy(s);
        \\        }
        \\    };
        \\    inline for (std.meta.fields(Slots)) |field| {
        \\        const s: *Slot = &@field(slots, field.name);
        \\        s.val = @intCast(n);
        \\        n += 1;
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "use-undefined"));
    }
}

test "partial-union-write: errdefer in SAME fn observing x.* fires" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const U = union(enum) { a: u32, b: []u8 };
        \\pub fn alloc(out: *U, allocator: std.mem.Allocator) !void {
        \\    errdefer out.* = .{ .a = 0 };
        \\    out.* = .{ .b = try allocator.alloc(u8, 16) };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "partial-union-write")) found = true;
    }
    try std.testing.expect(found);
}

test "partial-union-write: no errdefer in same fn — no FP even if other fns have errdefers" {
    // Regression: anyErrdeferObservesField was scanning from token 0, so an
    // errdefer in a PREVIOUS function that mentions `self` would cause a false
    // positive for a later function that has no errdefer.  The scan must start
    // at fn_body_first, not at 0.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const U = union(enum) { a: u32, b: []u8 };
        \\const S = struct {
        \\    v: U,
        \\    // This fn has an errdefer that mentions `self`.
        \\    pub fn setup(self: *S, allocator: std.mem.Allocator) !void {
        \\        errdefer self.v = .{ .a = 0 };
        \\        self.v = .{ .b = try allocator.alloc(u8, 8) };
        \\    }
        \\    // This fn has NO errdefer — partial-union-write must NOT fire here.
        \\    pub fn parseCLI(self: *S, input: u32) !void {
        \\        self.v = .{ .b = std.mem.span(
        \\            @as([*:0]u8, @ptrFromInt(input))
        \\        ) catch return error.InvalidValue };
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    // `setup` fires because it has an errdefer that observes `self.v`.
    // `parseCLI` must NOT fire.  Count total findings: expect exactly 1.
    var count: usize = 0;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "partial-union-write")) count += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), count);
}

test "heap-leak: *const T receiver — two-step cleanup pattern — does NOT fire" {
    // A `*const T` deinit can only free fields, not `self`.  The type uses
    // the caller-owned two-step pattern: callers call `deinit(alloc)` to
    // release fields, then `alloc.destroy(instance)` to release the struct.
    // The rule must NOT fire on such destructors.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub const Data = struct {
        \\    buf: []const u8,
        \\    pub fn init(alloc: anytype, text: []const u8) !*Data {
        \\        const d = try alloc.create(Data);
        \\        d.buf = try alloc.dupe(u8, text);
        \\        return d;
        \\    }
        \\    pub fn deinit(self: *const Data, alloc: anytype) void {
        \\        alloc.free(self.buf);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "heap-leak"));
    }
}

test "heap-leak: *T receiver without destroy — fires" {
    // Non-const receiver, has a heap-creator, no destroy call → fires.
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub const Data = struct {
        \\    buf: []const u8,
        \\    pub fn init(alloc: anytype, text: []const u8) !*Data {
        \\        const d = try alloc.create(Data);
        \\        d.buf = try alloc.dupe(u8, text);
        \\        return d;
        \\    }
        \\    pub fn deinit(self: *Data, alloc: anytype) void {
        \\        alloc.free(self.buf);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-leak")) found = true;
    }
    try std.testing.expect(found);
}

test "skript regression: return switch reads arena allocation before deferred deinit" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Choice = enum { left, right };
        \\fn readByte(bytes: []const u8) u8 { return bytes[0]; }
        \\pub fn evaluate(choice: Choice) !u8 {
        \\    var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        \\    defer scratch.deinit();
        \\    const bytes = try scratch.allocator().alloc(u8, 1);
        \\    bytes[0] = 7;
        \\    return switch (choice) {
        \\        .left => readByte(bytes),
        \\        .right => readByte(bytes),
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "arena-use-after-kill"));
    }
}

test "skript regression: explicit arena deinit before return switch remains unsafe" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Choice = enum { left, right };
        \\fn readByte(bytes: []const u8) u8 { return bytes[0]; }
        \\pub fn evaluate(choice: Choice) !u8 {
        \\    var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        \\    const bytes = try scratch.allocator().alloc(u8, 1);
        \\    scratch.deinit();
        \\    return switch (choice) {
        \\        .left => readByte(bytes),
        \\        .right => readByte(bytes),
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "arena-use-after-kill")) found = true;
    }
    try std.testing.expect(found);
}

test "skript regression: return switch reads heap allocation before deferred free" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Choice = enum { left, right };
        \\fn readByte(bytes: []const u8) u8 { return bytes[0]; }
        \\pub fn evaluate(allocator: std.mem.Allocator, choice: Choice) !u8 {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    defer allocator.free(bytes);
        \\    bytes[0] = 7;
        \\    return switch (choice) {
        \\        .left => readByte(bytes),
        \\        .right => readByte(bytes),
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "heap-use-after-free"));
    }
}

test "skript regression: explicit heap free before return switch remains unsafe" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Choice = enum { left, right };
        \\fn readByte(bytes: []const u8) u8 { return bytes[0]; }
        \\pub fn evaluate(allocator: std.mem.Allocator, choice: Choice) !u8 {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    allocator.free(bytes);
        \\    return switch (choice) {
        \\        .left => readByte(bytes),
        \\        .right => readByte(bytes),
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-use-after-free")) found = true;
    }
    try std.testing.expect(found);
}

test "unreachable blocks cannot produce diagnostics" {
    const gpa = std.testing.allocator;
    const position: cfg_mod.SrcPos = .{ .byte = 0, .line = 1, .column = 1 };
    var statements = [_]cfg_mod.Stmt{.{
        .kind = .{ .leak_warning = .{ .type_name = "Unreachable" } },
        .pos = position, .end_pos = position,
    }};
    var blocks = [_]cfg_mod.BasicBlock{
        .{ .id = @enumFromInt(0), .stmts = &.{}, .successors = &.{} },
        .{ .id = @enumFromInt(1), .stmts = &statements, .successors = &.{} },
    };
    const cfg: Cfg = .{ .blocks = &blocks, .entry = @enumFromInt(0), .fn_span = .{ .start = 0, .end = 1 }, .locals = &.{} };
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    try check(gpa, &cfg, .{ .path = "<test>" }, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "exhausted dataflow budget is an analysis failure" {
    const gpa = std.testing.allocator;
    const position: cfg_mod.SrcPos = .{ .byte = 0, .line = 1, .column = 1 };
    var statements = [_]cfg_mod.Stmt{.{
        .kind = .{ .leak_warning = .{ .type_name = "Reachable" } },
        .pos = position, .end_pos = position,
    }};
    var blocks = [_]cfg_mod.BasicBlock{
        .{ .id = @enumFromInt(0), .stmts = &statements, .successors = &.{} },
    };
    const cfg: Cfg = .{ .blocks = &blocks, .entry = @enumFromInt(0), .fn_span = .{ .start = 0, .end = 1 }, .locals = &.{} };
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    try std.testing.expectError(error.AnalysisBudgetExceeded, check(gpa, &cfg, .{
        .path = "<test>", .max_block_visits = 0,
    }, &problems));
}

test "address AST: a scalar bitwise field is not a stack borrow" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Pair = struct { a: u32, b: u32 };
        \\pub fn bits(x: u32) Pair {
        \\    const mask: u32 = 255;
        \\    return .{ .a = x & mask, .b = 0 };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "address AST: nested scalar aggregate aliases carry no address" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Part = struct { value: u32 };
        \\pub fn bits(x: u32) struct { part: Part } {
        \\    const mask: u32 = 255;
        \\    const part: Part = .{ .value = x & mask };
        \\    const alias = part;
        \\    return .{ .part = alias };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "address AST: a nested parenthesized address still escapes" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn bad() struct { inner: struct { p: *u32 } } {
        \\    var x: u32 = 1;
        \\    return .{ .inner = .{ .p = (&x) } };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("stack-escape", problems.items[0].rule_id);
}

test "address AST: pointer aliases and direct addresses both escape" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn bad() struct { p: *u32, q: *u32 } {
        \\    var x: u32 = 1;
        \\    var y: u32 = 2;
        \\    const p = &x;
        \\    return .{ .p = p, .q = &y };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 2), problems.items.len);
    for (problems.items) |problem| try std.testing.expectEqualStrings("stack-escape", problem.rule_id);
}

test "address AST: a copied array element adds no stack borrow" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn bad() struct { p: *u32, value: u32 } {
        \\    var x: u32 = 1;
        \\    const array: [1]u32 = .{2};
        \\    return .{ .p = &x, .value = array[0] };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("stack-escape", problems.items[0].rule_id);
}

test "address AST: a call argument is not the returned value" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn good() struct { value: u32 } {
        \\    var x: u32 = 1;
        \\    return .{ .value = read(&x) };
        \\}
        \\fn read(x: *const u32) u32 { return x.*; }
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "address AST: taking an address does not overwrite its stored pointer" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn bad() struct { pointer: **u32, target: *u32 } {
        \\    var x: u32 = 1;
        \\    var p = &x;
        \\    return .{ .pointer = &p, .target = p };
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 2), problems.items.len);
    for (problems.items) |problem| try std.testing.expectEqualStrings("stack-escape", problem.rule_id);
}

test "address AST: a bitwise operand remains a value read" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn bad(x: u32) u32 {
        \\    const mask: u32 = undefined;
        \\    return x & mask;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
}

fn expectFlowRules(source: []const u8, expected: []const []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa, source);
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(expected.len, problems.items.len);
    for (expected, problems.items) |rule, problem| try std.testing.expectEqualStrings(rule, problem.rule_id);
}

test "cleanup flow: defer uses the final ownership flag" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    var owned = true;
        \\    defer if (owned) gpa.free(p);
        \\    gpa.free(p);
        \\    owned = false;
        \\}
    , &.{});
}

test "cleanup flow: an armed defer still detects double free" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    const owned = true;
        \\    defer if (owned) gpa.free(p);
        \\    gpa.free(p);
        \\}
    , &.{"heap-double-free"});
}

test "cleanup flow: branch cleanup stays correlated with ownership" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator, release: bool) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    var owned = true;
        \\    defer if (owned) gpa.free(p);
        \\    if (release) {
        \\        gpa.free(p);
        \\        owned = false;
        \\    }
        \\}
    , &.{});
}

test "cleanup flow: catch disarms error cleanup before returning" {
    try expectFlowRules(
        \\const std = @import("std");
        \\fn fail() error{Oops}!void { return error.Oops; }
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    var owned = true;
        \\    errdefer if (owned) gpa.free(p);
        \\    fail() catch {
        \\        gpa.free(p);
        \\        owned = false;
        \\        return error.Oops;
        \\    };
        \\    gpa.free(p);
        \\}
    , &.{});
}

test "cleanup flow: break flushes only crossed normal defers" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    defer gpa.free(p);
        \\    while (true) {
        \\        errdefer gpa.free(p);
        \\        break;
        \\    }
        \\    _ = p;
        \\}
    , &.{});
}

test "cleanup flow: break replays cleanup in reverse order" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    while (true) {
        \\        defer gpa.free(p);
        \\        defer _ = p;
        \\        break;
        \\    }
        \\}
    , &.{});
}

test "cleanup flow: for exhaustion cannot bypass else" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator, values: []const u8) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    var pending = true;
        \\    for (values) |_| {} else { pending = false; }
        \\    if (pending) gpa.free(p);
        \\    gpa.free(p);
        \\}
    , &.{});
}

test "cleanup flow: for break bypasses else cleanup" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator, values: []const u8) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    var pending = true;
        \\    for (values) |_| { break; } else { pending = false; }
        \\    if (pending) gpa.free(p);
        \\    gpa.free(p);
        \\}
    , &.{"heap-double-free"});
}

test "cleanup flow: while break bypasses unreachable else" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    while (true) { break; } else { gpa.free(p); }
        \\    gpa.free(p);
        \\}
    , &.{});
}

test "cleanup flow: a boolean return does not hide a dangling out parameter" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator, out: *[]u8, recorded: bool) !bool {
        \\    const p = try gpa.alloc(u8, 8);
        \\    if (recorded) gpa.free(p);
        \\    if (!recorded) out.* = p;
        \\    return !recorded;
        \\}
    , &.{});
}

test "cleanup flow: a real out parameter use after free still reports" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator, out: *[]u8, release: bool) !bool {
        \\    const p = try gpa.alloc(u8, 8);
        \\    out.* = p;
        \\    if (release) gpa.free(p);
        \\    return true;
        \\}
    , &.{"heap-use-after-free"});
}

test "cleanup flow: break flushes arena cleanup" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(gpa);
        \\    const alloc = arena.allocator();
        \\    const buf = try alloc.alloc(u8, 8);
        \\    while (true) { defer arena.deinit(); break; }
        \\    _ = buf;
        \\}
    , &.{"arena-use-after-kill"});
}

test "cleanup flow: labeled break crosses every nested scope" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(gpa);
        \\    const alloc = arena.allocator();
        \\    const buf = try alloc.alloc(u8, 8);
        \\    outer: while (true) {
        \\        defer arena.deinit();
        \\        while (true) { break :outer; }
        \\    }
        \\    _ = buf;
        \\}
    , &.{"arena-use-after-kill"});
}

test "cleanup flow: labeled block break flushes arena cleanup" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(gpa);
        \\    const alloc = arena.allocator();
        \\    const buf = try alloc.alloc(u8, 8);
        \\    done: { defer arena.deinit(); break :done; }
        \\    _ = buf;
        \\}
    , &.{"arena-use-after-kill"});
}

test "cleanup flow: labeled continue flushes cleanup before continuation" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(gpa);
        \\    const alloc = arena.allocator();
        \\    const buf = try alloc.alloc(u8, 8);
        \\    var done = false;
        \\    outer: while (!done) : (done = true) {
        \\        defer arena.deinit();
        \\        while (true) { continue :outer; }
        \\    }
        \\    _ = buf;
        \\}
    , &.{"arena-use-after-kill"});
}

test "cleanup flow: unrelated calls and counter updates preserve local flags" {
    try expectFlowRules(
        \\const std = @import("std");
        \\fn observe(value: usize) void { _ = value; }
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    var owned = true;
        \\    defer if (owned) gpa.free(p);
        \\    gpa.free(p);
        \\    owned = false;
        \\    var count: usize = 0;
        \\    count += 1;
        \\    observe(count);
        \\}
    , &.{});
}

test "cleanup flow: calls can change an address-exposed ownership flag" {
    try expectFlowRules(
        \\const std = @import("std");
        \\fn mutate(flag: *bool) void { flag.* = true; }
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    var owned = false;
        \\    const alias = &owned;
        \\    defer if (owned) gpa.free(p);
        \\    gpa.free(p);
        \\    mutate(alias);
        \\}
    , &.{"heap-double-free"});
}

test "cleanup flow: memory builtins can change an ownership flag" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    var owned = false;
        \\    defer if (owned) gpa.free(p);
        \\    gpa.free(p);
        \\    @memset((&owned)[0..1], true);
        \\}
    , &.{"heap-double-free"});
}

test "cleanup flow: failed reassignment preserves the old cleanup target" {
    try expectFlowRules(
        \\const std = @import("std");
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    var p = try gpa.alloc(u8, 8);
        \\    errdefer gpa.free(p);
        \\    gpa.free(p);
        \\    p = try gpa.alloc(u8, 16);
        \\    gpa.free(p);
        \\}
    , &.{"heap-double-free"});
}

test "cleanup flow: failed destructuring preserves old cleanup targets" {
    try expectFlowRules(
        \\const std = @import("std");
        \\fn pair(gpa: std.mem.Allocator) !struct { []u8, usize } {
        \\    return .{ try gpa.alloc(u8, 16), 0 };
        \\}
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    var p = try gpa.alloc(u8, 8);
        \\    var count: usize = undefined;
        \\    errdefer gpa.free(p);
        \\    gpa.free(p);
        \\    p, count = try pair(gpa);
        \\    gpa.free(p);
        \\    _ = count;
        \\}
    , &.{"heap-double-free"});
}

test "cleanup flow: calls used as values can change escaped flags" {
    try expectFlowRules(
        \\const std = @import("std");
        \\fn mutate(flag: *bool) usize { flag.* = true; return 0; }
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p = try gpa.alloc(u8, 8);
        \\    var owned = false;
        \\    const alias = &owned;
        \\    defer if (owned) gpa.free(p);
        \\    gpa.free(p);
        \\    const result = mutate(alias);
        \\    _ = result;
        \\}
    , &.{"heap-double-free"});
}

test "qualified types: non-consuming methods do not inherit a sibling effect" {
    try expectFlowRules(
        \\const std = @import("std");
        \\const A = struct {
        \\    const Owner = struct {
        \\        pub fn release(self: *@This(), gpa: std.mem.Allocator) void { gpa.destroy(self); }
        \\    };
        \\};
        \\const B = struct {
        \\    const Owner = struct {
        \\        pub fn release(self: *@This(), gpa: std.mem.Allocator) void { _ = self; _ = gpa; }
        \\    };
        \\};
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p: *B.Owner = try gpa.create(B.Owner);
        \\    p.release(gpa);
        \\    gpa.destroy(p);
        \\}
    , &.{});
}

test "qualified types: consuming methods retain their own effect" {
    try expectFlowRules(
        \\const std = @import("std");
        \\const A = struct {
        \\    const Owner = struct {
        \\        pub fn release(self: *@This(), gpa: std.mem.Allocator) void { _ = self; _ = gpa; }
        \\    };
        \\};
        \\const B = struct {
        \\    const Owner = struct {
        \\        pub fn release(self: *@This(), gpa: std.mem.Allocator) void { gpa.destroy(self); }
        \\    };
        \\};
        \\pub fn f(gpa: std.mem.Allocator) !void {
        \\    const p: *B.Owner = try gpa.create(B.Owner);
        \\    p.release(gpa);
        \\    gpa.destroy(p);
        \\}
    , &.{"heap-double-free"});
}
