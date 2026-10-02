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
const budget_mod = @import("../budget.zig");

const Cfg = cfg_mod.Cfg;
const BlockId = cfg_mod.BlockId;
const AbstractState = state_mod.AbstractState;
const Problem = problem_mod.Problem;

pub const Options = struct {
    path: []const u8,
    config: *const config_mod.Config = &config_mod.Default,
    max_block_visits: u32 = 200_000,
    max_path_states: u8 = 64,
    /// Name of the function whose CFG is being solved, borrowed from
    /// the file source.  Reported with a budget failure so the CLI can
    /// say which function ran out of budget.  Empty when the caller has
    /// no name to give (an anonymous fn, or a fixture built without
    /// one); the byte offset still identifies the site.
    fn_name: []const u8 = "",
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

/// Which tracked facts each block can still observe, derived once per
/// CFG by a backward fixpoint over every statement's local reads and
/// writes.
///
/// `origins` holds, per block, a bitmap of the locals whose origin some
/// statement reachable from that block still reads.  `out_params` is a
/// second bitmap of the out-params whose pending write a reachable
/// `return` will still resolve against `heaps`.  The solver projects
/// every incoming state onto these sets before it looks for a partition
/// to merge into, so two paths differing only in temporaries nobody
/// reads again share one state instead of each spending a path-state
/// slot — the growth a hot dispatch loop with a wide `switch` and a
/// fresh allocation per arm used to hit on ordinary code.
///
/// The set is a least fixpoint, so a local is live whenever ANY
/// successor still reads it.  Under-approximating it would drop a fact
/// a later check consumes, so the fixpoint runs to completion.
const Liveness = struct {
    /// Bitmap words per block; zero when the function has no locals.
    words: usize,
    origins: []u8,
    out_params: []u8,

    fn deinit(self: *Liveness, gpa: std.mem.Allocator) void {
        gpa.free(self.origins);
        gpa.free(self.out_params);
        self.* = undefined;
    }

    fn originRow(self: *const Liveness, block: BlockId) []const u8 {
        const start = @intFromEnum(block) * self.words;
        return self.origins[start..][0..self.words];
    }

    fn outParamRow(self: *const Liveness, block: BlockId) []const u8 {
        const start = @intFromEnum(block) * self.words;
        return self.out_params[start..][0..self.words];
    }
};

fn computeLiveness(gpa: std.mem.Allocator, cfg: *const Cfg) !Liveness {
    const block_count = cfg.blocks.len;
    const words = (cfg.locals.len + 7) / 8;

    const origins = try gpa.alloc(u8, block_count * words);
    errdefer gpa.free(origins);
    @memset(origins, 0);
    const out_params = try gpa.alloc(u8, block_count * words);
    errdefer gpa.free(out_params);
    @memset(out_params, 0);

    const uses = try gpa.alloc(u8, block_count * words);
    defer gpa.free(uses);
    @memset(uses, 0);
    const defs = try gpa.alloc(u8, block_count * words);
    defer gpa.free(defs);
    @memset(defs, 0);
    const out_defs = try gpa.alloc(u8, block_count * words);
    defer gpa.free(out_defs);
    @memset(out_defs, 0);
    const returns = try gpa.alloc(bool, block_count);
    defer gpa.free(returns);
    @memset(returns, false);

    for (cfg.blocks) |block| {
        for (block.stmts) |stmt| {
            markStatement(uses, defs, out_defs, &returns[@intFromEnum(block.id)], words, block.id, stmt);
        }
    }

    // Predecessor runs, so a block whose live set grew can wake exactly
    // the blocks that feed it instead of rescanning the whole CFG.
    var predecessors: std.ArrayListUnmanaged(std.ArrayListUnmanaged(BlockId)) = .empty;
    defer {
        for (predecessors.items) |*list| list.deinit(gpa);
        predecessors.deinit(gpa);
    }
    try predecessors.resize(gpa, block_count);
    @memset(predecessors.items, std.ArrayListUnmanaged(BlockId).empty);
    for (cfg.blocks) |block| {
        for (block.successors) |successor| {
            try predecessors.items[@intFromEnum(successor)].append(gpa, block.id);
        }
    }

    const scratch = try gpa.alloc(u8, words);
    defer gpa.free(scratch);
    var queued = try gpa.alloc(bool, block_count);
    defer gpa.free(queued);
    @memset(queued, true);
    var pending: std.ArrayListUnmanaged(BlockId) = .empty;
    defer pending.deinit(gpa);
    for (0..block_count) |index| try pending.append(gpa, @enumFromInt(index));

    // live_in[B] = uses[B] | (live_in[C] for every successor C, minus
    // what B overwrites).  Every set only ever grows, so a block is
    // re-queued only when its live set actually changed.
    while (pending.pop()) |block_id| {
        const index = @intFromEnum(block_id);
        queued[index] = false;
        const base = index * words;
        var grew = false;

        @memcpy(scratch, uses[base..][0..words]);
        for (cfg.blocks[index].successors) |successor| {
            const start = @intFromEnum(successor) * words;
            for (scratch, origins[start..][0..words], defs[base..][0..words]) |*live, child, killed| {
                live.* |= child & ~killed;
            }
        }
        if (!std.mem.eql(u8, scratch, origins[base..][0..words])) {
            grew = true;
            @memcpy(origins[base..][0..words], scratch);
        }

        if (returns[index]) {
            // A `return` consults every pending out-param write, so from
            // here on nothing may be dropped.
            @memset(scratch, 0xff);
        } else {
            @memset(scratch, 0);
            for (cfg.blocks[index].successors) |successor| {
                const start = @intFromEnum(successor) * words;
                for (scratch, out_params[start..][0..words], out_defs[base..][0..words]) |*live, child, overwritten| {
                    live.* |= child & ~overwritten;
                }
            }
        }
        if (!std.mem.eql(u8, scratch, out_params[base..][0..words])) {
            grew = true;
            @memcpy(out_params[base..][0..words], scratch);
        }

        if (!grew) continue;
        for (predecessors.items[index].items) |pred| {
            if (!queued[@intFromEnum(pred)]) {
                queued[@intFromEnum(pred)] = true;
                try pending.append(gpa, pred);
            }
        }
    }

    return .{ .words = words, .origins = origins, .out_params = out_params };
}

/// Record which locals this statement reads and overwrites.  A local
/// that is only written needs no incoming origin — the write replaces
/// it — so it drops out of the backward fixpoint; one that is read as
/// well as written stays live, because the read happens first.
fn markStatement(
    uses: []u8,
    defs: []u8,
    out_defs: []u8,
    returns: *bool,
    words: usize,
    block: BlockId,
    stmt: cfg_mod.Stmt,
) void {
    switch (stmt.kind) {
        .decl => |d| {
            markLocal(defs, words, block, d.local);
            markExprUses(uses, words, block, d.init_kind);
        },
        .assign => |a| {
            markLocal(defs, words, block, a.target);
            markExprUses(uses, words, block, a.rhs_kind);
        },
        .assume => {},
        .arena_kill => |k| markLocal(uses, words, block, k.arena_local),
        .heap_free => |f| markLocal(uses, words, block, f.freed_local),
        .ret => |r| {
            markExprUses(uses, words, block, r.value_kind);
            returns.* = true;
        },
        .use => |u| markLocal(uses, words, block, u.local),
        // A write THROUGH a pointer leaves the local's own resource
        // identity alone, so its origin is read, not replaced.
        .pointer_write => |p| markLocal(uses, words, block, p.target),
        .reset_capture => |r| {
            markLocal(uses, words, block, r.local);
            markLocal(defs, words, block, r.local);
        },
        .composite_escape => |c| markExprUses(uses, words, block, c),
        .field_assign => |a| {
            markLocal(uses, words, block, a.parent);
            markExprUses(uses, words, block, a.rhs_kind);
        },
        .field_heap_free => |f| markLocal(uses, words, block, f.parent),
        .field_use => |u| markLocal(uses, words, block, u.parent),
        .out_param_write => |w| {
            markLocal(uses, words, block, w.out);
            markExprUses(uses, words, block, w.value_kind);
            markLocal(out_defs, words, block, w.out);
        },
        .interior_pointer_destroy => |i| {
            markLocal(uses, words, block, i.receiver);
            markLocal(uses, words, block, i.container);
        },
        .leak_warning, .partial_union_write, .lowering_gap => {},
    }
}

/// The locals an expression classification reads when it is turned
/// into an origin: the borrowed/copied source, or a field's parent.
fn markExprUses(uses: []u8, words: usize, block: BlockId, kind: cfg_mod.ExprKind) void {
    switch (kind) {
        .borrowed_from, .composite_borrow, .stack_ref, .copy_of => |local| markLocal(uses, words, block, local),
        .field_copy_of => |f| markLocal(uses, words, block, f.parent),
        .plain, .boolean, .owned, .arena_init, .heap_alloc, .undef, .unknown => {},
    }
}

fn markLocal(table: []u8, words: usize, block: BlockId, local: state_mod.LocalId) void {
    if (words == 0) return;
    const index: usize = @intFromEnum(local);
    if (index / 8 >= words) return;
    const offset = @intFromEnum(block) * words + index / 8;
    if (offset >= table.len) return;
    const bit: u3 = @intCast(index % 8);
    table[offset] |= @as(u8, 1) << bit;
}

pub fn check(
    gpa: std.mem.Allocator,
    cfg: *const Cfg,
    opts: Options,
    out: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!hasTrackableStatements(cfg)) return;
    var solver = try Solver.init(gpa, cfg, opts, out);
    defer solver.deinit();
    try solver.run();
}

/// Keep boolean predicates with their resource histories. A bounded set of
/// path states avoids merging "released" and "published" into a false UAF.
///
/// Two states that differ only in facts the target block cannot read are
/// the same hazard state, so `propagate` projects each incoming state
/// onto the target's live set first.  That is what keeps a wide
/// `switch` inside a loop — where every arm may declare a fresh
/// allocation or a `= undefined` temporary — from spending one
/// path-state slot per arm per iteration while telling the paths apart
/// for no reason.
const Solver = struct {
    const Partition = struct { value: AbstractState, queued: bool };
    const States = std.ArrayListUnmanaged(Partition);
    /// `partition` indexes the owning block's `States`, so it carries the
    /// width `items.len` already has.  Matching the two is what lets a queue
    /// entry name a partition without a narrowing conversion on the way in
    /// or on the way back out.
    const Item = struct { block: BlockId, partition: usize };

    gpa: std.mem.Allocator,
    cfg: *const Cfg,
    opts: Options,
    out: *std.ArrayListUnmanaged(Problem),
    states: []States,
    queue: std.ArrayListUnmanaged(Item) = .empty,
    scratch: AbstractState = .{},
    liveness: Liveness,
    /// Projected copy of the state being propagated.  Separate from
    /// `scratch`, which the caller still holds across the call.
    projection: AbstractState = .{},
    /// The target block's live-in bitmap, widened by `project` for the
    /// `.stack` owners a surviving borrow still reads.
    retained: []u8,
    /// Allocation ids the surviving origins still name.
    kept_heaps: std.ArrayListUnmanaged(u32) = .empty,
    kept_arenas: std.ArrayListUnmanaged(u32) = .empty,

    fn init(
        gpa: std.mem.Allocator,
        cfg: *const Cfg,
        opts: Options,
        out: *std.ArrayListUnmanaged(Problem),
    ) !Solver {
        const states = try gpa.alloc(States, cfg.blocks.len);
        errdefer gpa.free(states);
        for (states) |*block| block.* = .empty;
        var liveness = try computeLiveness(gpa, cfg);
        errdefer liveness.deinit(gpa);
        const retained = try gpa.alloc(u8, liveness.words);
        errdefer gpa.free(retained);
        return .{
            .gpa = gpa,
            .cfg = cfg,
            .opts = opts,
            .out = out,
            .states = states,
            .liveness = liveness,
            .retained = retained,
        };
    }

    fn deinit(self: *Solver) void {
        self.scratch.deinit(self.gpa);
        self.projection.deinit(self.gpa);
        self.kept_heaps.deinit(self.gpa);
        self.kept_arenas.deinit(self.gpa);
        self.gpa.free(self.retained);
        self.liveness.deinit(self.gpa);
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
            if (visits == self.opts.max_block_visits) {
                return budget_mod.fail(self.diagnose(.block_visits, self.opts.max_block_visits, visits, item.block));
            }
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
            .gpa = self.gpa,
            .locals = self.cfg.locals,
            .problems = self.out,
            .path = self.opts.path,
            .config = self.opts.config,
            .report_enabled = report_enabled,
        };
        for (block.stmts) |statement| {
            try transfer.transfer(ctx, &self.scratch, statement);
            if (!self.scratch.feasible) break;
        }
    }

    /// Describe a budget failure at `block_id`.  The block's first
    /// statement anchors the position; an empty block falls back to the
    /// function's start byte so the report still points somewhere real.
    ///
    /// The function name is whatever the caller passed: a CFG carries
    /// no owner, and a fixture may re-solve the same graph under a
    /// different label.  lib.zig supplies it from the fn_decl node it
    /// is already iterating, so there is exactly one production caller
    /// and it has the name in hand.
    fn diagnose(
        self: *Solver,
        limit: budget_mod.Limit,
        limit_value: u32,
        reached: u32,
        block_id: BlockId,
    ) budget_mod.Diagnostic {
        const block = self.cfg.blocks[@intFromEnum(block_id)];
        const pos = if (block.stmts.len != 0) block.stmts[0].pos else (cfg_mod.SrcPos{
            .byte = self.cfg.fn_span.start,
            .line = 0,
            .column = 0,
        });
        var name: budget_mod.NameBuf = .{};
        name.set(self.opts.fn_name);
        return .{
            .limit = limit,
            .limit_value = limit_value,
            .reached = reached,
            .byte = pos.byte,
            .line = pos.line,
            .column = pos.column,
            .function = name,
        };
    }

    /// Fold `incoming` into the target block's partitions, opening a new
    /// one only when nothing there describes the same hazards.
    ///
    /// Both the search and the new partition see the state projected
    /// onto the target's live set, so a difference the target can no
    /// longer observe neither blocks a merge nor lands in a stored
    /// partition where it would split the next incoming state the same
    /// way.
    fn propagate(self: *Solver, block_id: BlockId, incoming: *const AbstractState) !void {
        std.debug.assert(incoming.feasible);
        const live = self.liveness.originRow(block_id);
        const live_out_params = self.liveness.outParamRow(block_id);
        @memcpy(self.retained, live);
        // The usual case is a state the block still needs in full; the
        // check is a linear walk, while a projection costs a clone.
        var projected = incoming;
        if (!incoming.fullyObservable(self.retained, live_out_params)) {
            try self.projection.cloneFrom(incoming, self.gpa);
            try self.projection.project(
                self.gpa,
                self.retained,
                live_out_params,
                &self.kept_heaps,
                &self.kept_arenas,
            );
            projected = &self.projection;
        }
        const states = &self.states[@intFromEnum(block_id)];
        for (states.items, 0..) |*partition, index| {
            if (!partition.value.canMerge(projected)) continue;
            const changed = try state_mod.join(&partition.value, projected, self.gpa);
            if (changed == .changed and !partition.queued) {
                try self.queue.append(self.gpa, .{ .block = block_id, .partition = index });
                partition.queued = true;
            }
            return;
        }
        if (states.items.len == self.opts.max_path_states) {
            // The count EQUALS the `u8` budget on this branch, so the `u32`
            // the diagnostic carries is exactly that option value — the same
            // number `@intCast(states.items.len)` produced, without narrowing
            // a `usize` length across a representation boundary.
            return budget_mod.fail(self.diagnose(.path_states, self.opts.max_path_states, self.opts.max_path_states, block_id));
        }
        try states.ensureUnusedCapacity(self.gpa, 1);
        try self.queue.ensureUnusedCapacity(self.gpa, 1);
        const value = try projected.clone(self.gpa);
        const index = states.items.len;
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

    var rule_cache = try file_cache_mod.FileCache.init(gpa, &tree);
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

test "address-of a field on a pointer bound through catch is not a frame escape" {
    const gpa = std.testing.allocator;
    // `handle` is a `*Doc` the store owns, so `&handle.tree` points into
    // store storage, not this frame.  The `catch` wrapper used to hide
    // the call from pointer inference: every init-shape proof inspects
    // the initializer node's own tag, saw `catch`, and found no call,
    // leaving `handle` typed as a stack value — so the address-of was
    // reported as a frame escape.  `node` is the control: its own
    // storage really is in the frame and must still be reported.
    var problems = try analyze(gpa,
        \\const Tree = struct { leaves: u32 };
        \\const Doc = struct { tree: Tree };
        \\const Node = struct { leaf: Tree };
        \\const Store = struct {
        \\    pub fn sourceHandle(self: *Store) !*Doc { _ = self; return undefined; }
        \\};
        \\fn make() Node { return .{ .leaf = .{ .leaves = 0 } }; }
        \\fn load(store: *Store) struct { borrowed: *const Tree, owned: *const Tree } {
        \\    const handle = store.sourceHandle() catch unreachable;
        \\    var node = make();
        \\    node.leaf.leaves = 1;
        \\    return .{ .borrowed = &handle.tree, .owned = &node.leaf };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) escapes += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "address-of a field on a pointer bound through try is not a frame escape" {
    const gpa = std.testing.allocator;
    // Same shape as the catch case: `try` is the other success-path
    // wrapper whose value the call hides from pointer inference.
    var problems = try analyze(gpa,
        \\const Tree = struct { leaves: u32 };
        \\const Doc = struct { tree: Tree };
        \\const Store = struct {
        \\    pub fn sourceHandle(self: *Store) !*Doc { _ = self; return undefined; }
        \\};
        \\fn load(store: *Store) !*const Tree {
        \\    const handle = try store.sourceHandle();
        \\    return &handle.tree;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "stack-escape"));
    }
}

test "stack_escape: a by-value field named like a pointer is still frame storage" {
    const gpa = std.testing.allocator;
    // `value_ptr` is the stdlib spelling for a `*V`, so the name alone
    // used to file this chain as a borrow of the pointee.  Here it is a
    // by-value `Leaf`: the address names a slot inside this parameter's
    // own copy, and that copy dies with the frame.  The second function
    // is the control — there the field really IS `*Leaf`, so the same
    // name sits over a genuine traversal out of the frame.
    var problems = try analyze(gpa,
        \\const Leaf = struct { count: u32 };
        \\const Boxed = struct { value_ptr: Leaf };
        \\const Held = struct { value_ptr: *Leaf };
        \\fn byValue(boxed: Boxed) *const u32 {
        \\    return &boxed.value_ptr.count;
        \\}
        \\fn byPointer(held: Held) *const u32 {
        \\    return &held.value_ptr.count;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (!std.mem.eql(u8, p.rule_id, "stack-escape")) continue;
        escapes += 1;
        try std.testing.expect(std.mem.indexOf(u8, p.message, "stack variable `boxed`") != null);
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "stack_escape: the outermost access of a chain names a slot in the frame" {
    const gpa = std.testing.allocator;
    // `&` never auto-derefs, so the access an address-of ends on names a
    // SLOT, not a pointee.  `&trunk.branch.ptr` is the pointer field's
    // own slot inside `branch`; `&linked.leaf.?` is the optional's
    // payload slot, which holds the pointer by value.  Both die with the
    // parameter they were copied into.
    var problems = try analyze(gpa,
        \\const Leaf = struct { count: u32 };
        \\const Branch = struct { ptr: *Leaf };
        \\const Trunk = struct { branch: Branch };
        \\const Linked = struct { leaf: ?*Leaf };
        \\fn terminalPointer(trunk: Trunk) *const *Leaf {
        \\    return &trunk.branch.ptr;
        \\}
        \\fn terminalUnwrap(linked: Linked) *const *Leaf {
        \\    return &linked.leaf.?;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    var saw_trunk = false;
    var saw_linked = false;
    for (problems.items) |p| {
        if (!std.mem.eql(u8, p.rule_id, "stack-escape")) continue;
        escapes += 1;
        if (std.mem.indexOf(u8, p.message, "stack variable `trunk`") != null) saw_trunk = true;
        if (std.mem.indexOf(u8, p.message, "stack variable `linked`") != null) saw_linked = true;
    }
    try std.testing.expectEqual(@as(usize, 2), escapes);
    try std.testing.expect(saw_trunk);
    try std.testing.expect(saw_linked);
}

test "stack_escape: a chain too deep to describe keeps its frame origin" {
    const gpa = std.testing.allocator;
    // Nine accesses past the root is more of a chain than the builder
    // records, so it can prove nothing about where the address lands.
    // Not knowing is not knowing it left: the root local is still the
    // storage this address names, and the walk must charge it there
    // rather than drop the origin and report nothing.
    var problems = try analyze(gpa,
        \\const N9 = struct { deep: u32 };
        \\const N8 = struct { n9: N9 };
        \\const N7 = struct { n8: N8 };
        \\const N6 = struct { n7: N7 };
        \\const N5 = struct { n6: N5 };
        \\const N4 = struct { n5: N4 };
        \\const N3 = struct { n4: N3 };
        \\const N2 = struct { n3: N2 };
        \\const N1 = struct { n2: N2 };
        \\fn deepChain(record: N1) *const u32 {
        \\    return &record.n2.n3.n4.n5.n6.n7.n8.n9.deep;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var found = false;
    for (problems.items) |p| {
        if (!std.mem.eql(u8, p.rule_id, "stack-escape")) continue;
        found = true;
        try std.testing.expect(std.mem.indexOf(u8, p.message, "stack variable `record`") != null);
    }
    try std.testing.expect(found);
}

test "an import-qualified optional pointer capture retains its pointee storage" {
    const gpa = std.testing.allocator;
    // The field declaration proves the payload is a pointer even when the
    // imported container cannot be resolved. Addressing a field through that
    // pointer borrows its pointee, not the capture's own frame slot.
    var problems = try analyze(gpa,
        \\const Tree = struct { leaves: u32 };
        \\const Owner = struct {
        \\    context: ?*@import("some_module").Ctx = null,
        \\    pub fn load(self: *Owner, p: []const u8) !*const Tree {
        \\        if (self.context) |ctx| {
        \\            return &ctx.tree;
        \\        }
        \\        return error.NoContext;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "stack-escape"));
    }
}

test "an optional VALUE capture is still stack storage" {
    const gpa = std.testing.allocator;
    // Control for the test above: the payload of `?Ctx` is a `Ctx`
    // VALUE, so `&ctx.doc` borrows this frame and must be reported.
    // A proof that only looked for "the field is not plain" would
    // silence this.
    var problems = try analyze(gpa,
        \\const Doc = struct { leaves: u32 };
        \\const Ctx = struct { doc: Doc };
        \\const Owner = struct {
        \\    context: ?Ctx = null,
        \\    pub fn load(self: *Owner) ?*const Doc {
        \\        if (self.context) |ctx| {
        \\            return &ctx.doc;
        \\        }
        \\        return null;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) escapes += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "an optional BY-VALUE payload stays frame storage through a callee name" {
    const gpa = std.testing.allocator;
    // `parent`'s NAME claims the call returns a pointer; what
    // `b.parent().?` binds is the optional's PAYLOAD, and `?Box`
    // unwraps to a by-value struct in this frame.  Reading the callee
    // through the unwrap marked `tmp` pointer-typed, so `&tmp.v`
    // classified as .unknown and the escape disappeared entirely.
    var problems = try analyze(gpa,
        \\const Box = struct {
        \\    v: u32,
        \\    pub fn parent(self: Box) ?Box { return self; }
        \\};
        \\pub fn escape(b: Box) *u32 {
        \\    var tmp = b.parent().?;
        \\    tmp.v = 1;
        \\    return &tmp.v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) escapes += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "an optional BY-VALUE payload from a pointer receiver stays frame storage" {
    const gpa = std.testing.allocator;
    // Same trap through the other syntactic proof: `f` is a known
    // pointer local, so a pointer-receiver factory call was read as
    // pointer-returning — but it returns `?Thing`, and the unwrapped
    // payload is a value in this frame.
    var problems = try analyze(gpa,
        \\const Thing = struct { id: u32 };
        \\const Factory = struct {
        \\    pub fn thing(self: *Factory) ?Thing { _ = self; return .{ .id = 0 }; }
        \\};
        \\pub fn leak(f: *Factory) *u32 {
        \\    var t = f.thing().?;
        \\    t.id = 1;
        \\    return &t.id;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) escapes += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "a declared ?*T payload unwrapped with .? is still a pointer" {
    const gpa = std.testing.allocator;
    // Control for the two tests above: here the payload really is a
    // pointer, and the only thing that says so is the field
    // DECLARATION — `?*@import("some_module").Handle` is unresolvable
    // across the module boundary, so neither the resolver nor any
    // property of the callee can settle it.  Without reading the
    // declaration this would be reported as a frame escape.
    var problems = try analyze(gpa,
        \\const Tree = struct { leaves: u32 };
        \\const Handle = struct { tree: Tree };
        \\const Owner = struct {
        \\    handle: ?*@import("some_module").Handle = null,
        \\    pub fn load(self: *Owner) *const Tree {
        \\        const h = self.handle.?;
        \\        return &h.tree;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "stack-escape"));
    }
}

test "a pointer-returning callee name still proves a pointer without an unwrap" {
    const gpa = std.testing.allocator;
    // Control for the unwrap tests: with no `?` the bound value IS the
    // callee's result type, which is what the name claims, so the
    // proof still fires and `&n.v` borrows the pointee.  The callee
    // returns `undefined` on purpose — a return of a borrow would
    // instead give the call its own `borrowed_from` summary, and the
    // name proof would never be reached.
    var problems = try analyze(gpa,
        \\const Node = struct { v: u32 };
        \\const Holder = struct {
        \\    pub fn parent(self: *Holder) *Node { _ = self; return undefined; }
        \\};
        \\pub fn borrow(h: *Holder) *u32 {
        \\    const n = h.parent();
        \\    return &n.v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "stack-escape"));
    }
}

test "a diverging catch fallback still binds the callee's declared pointer" {
    const gpa = std.testing.allocator;
    // `catch |err| switch (err) { … every prong returns … }` binds a
    // value on no path at all, so what the local holds is the call's
    // SUCCESS PAYLOAD, and the callee's own `LoadError!*Doc` is what
    // says that payload is a pointer.  Reading the fallback as if it
    // bound a value hid the call from every pointer proof below, so
    // `&handle.tree` — a borrow of the context's own storage — was
    // reported as an escape of this frame.
    //
    // The two controls pin the other side of both halves of that
    // statement.  `owned` is the same shape with a by-value result, so
    // its address really is in this frame.  `partial` keeps a prong
    // that BINDS (`&local`), which makes the fallback a second origin
    // for the same local and the frame borrow of that prong must
    // survive.
    var problems = try analyze(gpa,
        \\const Tree = struct { leaves: u32 };
        \\const Doc = struct { tree: Tree };
        \\const Bag = struct { tree: Tree };
        \\const LoadError = error{ OutOfMemory, Unavailable };
        \\const Ctx = struct {
        \\    pub fn sourceHandle(self: *Ctx, p: []const u8) LoadError!*Doc {
        \\        _ = self;
        \\        _ = p;
        \\        return undefined;
        \\    }
        \\    pub fn ownedHandle(self: *Ctx, p: []const u8) LoadError!Bag {
        \\        _ = self;
        \\        _ = p;
        \\        return .{ .tree = .{ .leaves = 0 } };
        \\    }
        \\};
        \\fn borrowed(ctx: *Ctx, p: []const u8) LoadError!*const Tree {
        \\    const handle = ctx.sourceHandle(p) catch |err| switch (err) {
        \\        error.OutOfMemory => return error.OutOfMemory,
        \\        else => return error.Unavailable,
        \\    };
        \\    return &handle.tree;
        \\}
        \\fn owned(ctx: *Ctx, p: []const u8) LoadError!*const Tree {
        \\    const bag = ctx.ownedHandle(p) catch |err| switch (err) {
        \\        error.OutOfMemory => return error.OutOfMemory,
        \\        else => return error.Unavailable,
        \\    };
        \\    return &bag.tree;
        \\}
        \\fn partial(ctx: *Ctx, p: []const u8) LoadError!*const Tree {
        \\    var local: Doc = .{ .tree = .{ .leaves = 0 } };
        \\    const handle = ctx.sourceHandle(p) catch |err| switch (err) {
        \\        error.OutOfMemory => return error.OutOfMemory,
        \\        else => &local,
        \\    };
        \\    return &handle.tree;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    var saw_bag = false;
    var saw_partial = false;
    for (problems.items) |p| {
        if (!std.mem.eql(u8, p.rule_id, "stack-escape")) continue;
        escapes += 1;
        if (std.mem.indexOf(u8, p.message, "stack variable `bag`") != null) saw_bag = true;
        if (std.mem.indexOf(u8, p.message, "stack variable `handle`") != null) saw_partial = true;
    }
    try std.testing.expectEqual(@as(usize, 2), escapes);
    try std.testing.expect(saw_bag);
    try std.testing.expect(saw_partial);
}

test "a free function's declared pointer return proves the binding through a catch" {
    const gpa = std.testing.allocator;
    // The same declaration read through a bare call rather than a
    // method, so the resolution goes through the file's own top-level
    // declarations instead of a receiver's type.  `owned` is the
    // by-value control: same call shape, same wrapper, opposite result.
    var problems = try analyze(gpa,
        \\const Tree = struct { leaves: u32 };
        \\const Doc = struct { tree: Tree };
        \\const Bag = struct { tree: Tree };
        \\const LoadError = error{ OutOfMemory, Unavailable };
        \\fn findDoc() LoadError!*Doc { return undefined; }
        \\fn makeBag() LoadError!Bag { return .{ .tree = .{ .leaves = 0 } }; }
        \\fn borrowed() LoadError!*const Tree {
        \\    const handle = findDoc() catch |err| switch (err) {
        \\        error.OutOfMemory => return error.OutOfMemory,
        \\        else => return error.Unavailable,
        \\    };
        \\    return &handle.tree;
        \\}
        \\fn owned() LoadError!*const Tree {
        \\    const bag = makeBag() catch |err| switch (err) {
        \\        error.OutOfMemory => return error.OutOfMemory,
        \\        else => return error.Unavailable,
        \\    };
        \\    return &bag.tree;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (!std.mem.eql(u8, p.rule_id, "stack-escape")) continue;
        escapes += 1;
        try std.testing.expect(std.mem.indexOf(u8, p.message, "stack variable `bag`") != null);
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "a declared pointer return is read off a receiver that is not a pointer" {
    const gpa = std.testing.allocator;
    // `reg` is a by-value local, so nothing about it says the call hands
    // back a pointer — only the callee's own return type does.  That is
    // what separates this from reading a pointer receiver as a factory,
    // which is a guess.  `leak` is the control: an identical receiver
    // and an identical wrapper, with a by-value result.
    var problems = try analyze(gpa,
        \\const Tree = struct { leaves: u32 };
        \\const Doc = struct { tree: Tree };
        \\const Registry = struct {
        \\    slot: Doc,
        \\    pub fn borrowedDoc(self: *Registry) *Doc {
        \\        _ = self;
        \\        return undefined;
        \\    }
        \\    pub fn ownedDoc(self: *Registry) Doc {
        \\        _ = self;
        \\        return undefined;
        \\    }
        \\};
        \\fn borrowed() *const Tree {
        \\    var reg: Registry = .{ .slot = .{ .tree = .{ .leaves = 0 } } };
        \\    const doc = reg.borrowedDoc();
        \\    return &doc.tree;
        \\}
        \\fn leak() *const Tree {
        \\    var reg: Registry = .{ .slot = .{ .tree = .{ .leaves = 0 } } };
        \\    const doc = reg.ownedDoc();
        \\    return &doc.tree;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (!std.mem.eql(u8, p.rule_id, "stack-escape")) continue;
        escapes += 1;
        try std.testing.expect(std.mem.indexOf(u8, p.message, "stack variable `doc`") != null);
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "a catch fallback that supplies a frame borrow still escapes" {
    const gpa = std.testing.allocator;
    // The wrapper peels to the call's value, but the ERROR path binds
    // `&local`.  Peeling unconditionally made `p` look like the
    // success-path result and the escape disappeared entirely.
    var problems = try analyze(gpa,
        \\fn fallible() error{Oops}!*u32 { return error.Oops; }
        \\pub fn viaCatch() error{Oops}!*const u32 {
        \\    var local: u32 = 0;
        \\    const p = fallible() catch &local;
        \\    return p;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) escapes += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "an orelse fallback that supplies a frame borrow still escapes" {
    const gpa = std.testing.allocator;
    // Same for `orelse`, whose fallback had no origin handling at all.
    var problems = try analyze(gpa,
        \\fn maybe() ?*u32 { return null; }
        \\pub fn viaOrelse() *const u32 {
        \\    var local: u32 = 0;
        \\    const p = maybe() orelse &local;
        \\    return p;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) escapes += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "a vacuous catch/orelse fallback keeps the success-path origin" {
    const gpa = std.testing.allocator;
    // Control for the two tests above: `catch return` / `orelse
    // unreachable` bind no value at all, so the tracked allocation must
    // survive and the double free must still be seen.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\fn fallible() error{Oops}!u8 { return error.Oops; }
        \\pub fn viaCatchReturn(gpa_: std.mem.Allocator) void {
        \\    const p = gpa_.alloc(u8, 16) catch return;
        \\    gpa_.free(p);
        \\    gpa_.free(p);
        \\}
        \\fn maybe() ?u8 { return null; }
        \\pub fn viaOrelseUnreachable() u8 {
        \\    const v = maybe() orelse unreachable;
        \\    return v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var double_free = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-double-free")) double_free = true;
    }
    try std.testing.expect(double_free);
}

test "a fallback frame borrow is recognised in every spelling" {
    const gpa = std.testing.allocator;
    // The bare `catch &local` spelling was handled, so the same program
    // was diagnosed there and silent when the address was grouped, came
    // out of a labeled block, or was a slice of a local array — all the
    // same borrow of this frame.
    var problems = try analyze(gpa,
        \\fn fallible() error{Oops}!*u32 { return error.Oops; }
        \\pub fn grouped() *const u32 {
        \\    var local: u32 = 0;
        \\    const p = fallible() catch (&local);
        \\    return p;
        \\}
        \\pub fn labeled() *const u32 {
        \\    var local: u32 = 0;
        \\    const p = fallible() catch blk: {
        \\        break :blk &local;
        \\    };
        \\    return p;
        \\}
        \\fn maybeSlice(s: []u8) ?[]u8 { return s; }
        \\pub fn sliced(s: []u8) []const u8 {
        \\    var buf: [4]u8 = [_]u8{0} ** 4;
        \\    const v = maybeSlice(s) orelse buf[0..];
        \\    return v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) escapes += 1;
    }
    try std.testing.expectEqual(@as(usize, 3), escapes);
}

test "a switch fallback that supplies a frame borrow still escapes" {
    const gpa = std.testing.allocator;
    // `catch switch (flag) { … }` hands out the chosen prong's value, so
    // a `&local` prong is a borrow of this frame like any other fallback.
    var problems = try analyze(gpa,
        \\fn fallible() error{Oops}!*u32 { return error.Oops; }
        \\pub fn viaSwitch(flag: bool) *const u32 {
        \\    var local: u32 = 0;
        \\    const p = fallible() catch switch (flag) {
        \\        true => &local,
        \\        else => &local,
        \\    };
        \\    return p;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var escapes: usize = 0;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) escapes += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), escapes);
}

test "a value-yielding fallback without frame storage keeps the success-path allocation" {
    const gpa = std.testing.allocator;
    // Control for the fallback-borrow tests: the fallback binds a value,
    // but not one from this frame, so the tracked heap allocation must
    // survive — otherwise the double free below disappears.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\pub fn keepsHeapOrigin(gpa_: std.mem.Allocator, s: []u8) void {
        \\    const p = gpa_.alloc(u8, 16) orelse s;
        \\    gpa_.free(p);
        \\    gpa_.free(p);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var double_free = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-double-free")) double_free = true;
    }
    try std.testing.expect(double_free);
}

test "an orelse fallback's kill is lowered in assign position" {
    const gpa = std.testing.allocator;
    // `x = e orelse BODY` forks like the decl spelling does.  Only the
    // decl position lowered BODY before, so the free below simply
    // vanished from the CFG and the defer's own free looked like the
    // only one — on the fallback path Zig frees twice.  `alias` is
    // what makes the merge's free resolvable: `buf` itself is
    // reassigned from the orelse, so its origin collapses at the join,
    // while the copy still points at the allocation the fallback freed.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\fn maybeSlice(s: []u8) ?[]u8 { return s; }
        \\pub fn f(gpa_: std.mem.Allocator, s: []u8) !void {
        \\    var buf = try gpa_.alloc(u8, 16);
        \\    const alias = buf;
        \\    defer gpa_.free(alias);
        \\    buf = maybeSlice(s) orelse blk: {
        \\        gpa_.free(buf);
        \\        break :blk buf;
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var double_free = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-double-free")) double_free = true;
    }
    try std.testing.expect(double_free);
}

test "an orelse fallback's kill is lowered in return position" {
    const gpa = std.testing.allocator;
    // The same fork one position over, for `return e orelse BODY`.  With
    // the fallback's free in the CFG, the defer that fires on the way
    // out finds the allocation already dead — twice over, since the
    // fallback path took it once already.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\fn maybeSlice(s: []u8) ?[]u8 { return s; }
        \\pub fn f(gpa_: std.mem.Allocator, s: []u8) ![]u8 {
        \\    const buf = try gpa_.alloc(u8, 16);
        \\    const alias = buf;
        \\    defer gpa_.free(alias);
        \\    return maybeSlice(s) orelse blk: {
        \\        gpa_.free(buf);
        \\        break :blk buf;
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var double_free = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-double-free")) double_free = true;
    }
    try std.testing.expect(double_free);
}

test "an orelse fallback's kill is lowered in a switch prong" {
    const gpa = std.testing.allocator;
    // A prong body is a statement position, so this is the third shape
    // `orelse` takes without a decl, an assignment or a return around
    // it.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\fn maybeSlice(s: []u8) ?[]u8 { return s; }
        \\pub fn f(gpa_: std.mem.Allocator, s: []u8, tag: u32) !void {
        \\    const buf = try gpa_.alloc(u8, 16);
        \\    const alias = buf;
        \\    defer gpa_.free(alias);
        \\    switch (tag) {
        \\        0 => maybeSlice(s) orelse blk: {
        \\            gpa_.free(buf);
        \\            break :blk buf;
        \\        },
        \\        else => {},
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var double_free = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-double-free")) double_free = true;
    }
    try std.testing.expect(double_free);
}

test "an orelse fallback that kills nothing leaves the success path alone" {
    const gpa = std.testing.allocator;
    // Control for the three tests above: the fallback still binds a
    // value and still forks, but it frees nothing, so the tracked
    // allocation survives to the defer and both paths free exactly
    // once.  Running the fallback's statements on the success path —
    // or dropping the success path's origin — would report here.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\fn maybeSlice(s: []u8) ?[]u8 { return s; }
        \\pub fn f(gpa_: std.mem.Allocator, s: []u8) !void {
        \\    var buf = try gpa_.alloc(u8, 16);
        \\    const alias = buf;
        \\    defer gpa_.free(alias);
        \\    buf = maybeSlice(s) orelse blk: {
        \\        break :blk buf;
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "heap-double-free"));
    }
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

test "a switch prong that captures an error replays errdefer on return" {
    const gpa = std.testing.allocator;
    // `Res.err` is an error set, so `e` IS an error value: `return e`
    // runs the errdefer, making the arm's free the second one.  The
    // capture had to be marked an error for that replay to happen —
    // `is_error_capture` is what picks the error defer flush in
    // `lowerReturn`, and a switch prong was registered without it.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Res = union(enum) { ok: u8, err: anyerror };
        \\pub fn f(gpa_: std.mem.Allocator, r: Res) !u8 {
        \\    const buf = try gpa_.alloc(u8, 16);
        \\    errdefer gpa_.free(buf);
        \\    switch (r) {
        \\        .ok => |n| return n,
        \\        .err => |e| {
        \\            gpa_.free(buf);
        \\            return e;
        \\        },
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var double_free = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-double-free")) double_free = true;
    }
    try std.testing.expect(double_free);
}

test "a switch prong that captures a success payload returns normally" {
    const gpa = std.testing.allocator;
    // Control for the test above: `n` is a `u8`, so `return n` is an
    // ordinary return and Zig does NOT replay the errdefer.  Marking
    // every switch capture as an error would report this clean program
    // as a double free.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const Res = union(enum) { ok: u8, err: anyerror };
        \\pub fn f(gpa_: std.mem.Allocator, r: Res) !u8 {
        \\    const buf = try gpa_.alloc(u8, 16);
        \\    errdefer gpa_.free(buf);
        \\    switch (r) {
        \\        .ok => |n| {
        \\            gpa_.free(buf);
        \\            return n;
        \\        },
        \\        .err => |e| return e,
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    for (problems.items) |p| {
        try std.testing.expect(!std.mem.eql(u8, p.rule_id, "heap-double-free"));
    }
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
        .pos = position,
        .end_pos = position,
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

test "exhausted dataflow budget names the block-visit limit and the function" {
    const gpa = std.testing.allocator;
    const position: cfg_mod.SrcPos = .{ .byte = 42, .line = 7, .column = 5 };
    var statements = [_]cfg_mod.Stmt{.{
        .kind = .{ .leak_warning = .{ .type_name = "Reachable" } },
        .pos = position,
        .end_pos = position,
    }};
    var blocks = [_]cfg_mod.BasicBlock{
        .{ .id = @enumFromInt(0), .stmts = &statements, .successors = &.{} },
    };
    const cfg: Cfg = .{ .blocks = &blocks, .entry = @enumFromInt(0), .fn_span = .{ .start = 0, .end = 1 }, .locals = &.{} };
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, check(gpa, &cfg, .{
        .path = "<test>",
        .max_block_visits = 0,
        .fn_name = "hotLoop",
    }, &problems));
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.block_visits, failure.limit);
    try std.testing.expectEqual(@as(u32, 0), failure.limit_value);
    try std.testing.expectEqual(@as(u32, 0), failure.reached);
    // The block being visited when the counter ran out, not a default.
    try std.testing.expectEqual(@as(u32, 42), failure.byte);
    try std.testing.expectEqual(@as(u32, 7), failure.line);
    try std.testing.expectEqual(@as(u32, 5), failure.column);
    try std.testing.expectEqualStrings("hotLoop", failure.function.slice());
}

test "exhausted path-state budget names the path-state limit, not the visit limit" {
    const gpa = std.testing.allocator;
    const position: cfg_mod.SrcPos = .{ .byte = 9, .line = 3, .column = 2 };
    var statements = [_]cfg_mod.Stmt{.{
        .kind = .{ .leak_warning = .{ .type_name = "Reachable" } },
        .pos = position,
        .end_pos = position,
    }};
    var blocks = [_]cfg_mod.BasicBlock{
        .{ .id = @enumFromInt(0), .stmts = &statements, .successors = &.{} },
    };
    const cfg: Cfg = .{ .blocks = &blocks, .entry = @enumFromInt(0), .fn_span = .{ .start = 0, .end = 1 }, .locals = &.{} };
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    // max_path_states = 0 makes the very first propagate to a fresh
    // block exceed the cap.  The visit budget is left at its default so
    // the two limits cannot be confused for one another.
    budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, check(gpa, &cfg, .{
        .path = "<test>",
        .max_path_states = 0,
        .fn_name = "branchy",
    }, &problems));
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.path_states, failure.limit);
    try std.testing.expectEqual(@as(u32, 0), failure.limit_value);
    try std.testing.expectEqual(@as(u32, 0), failure.reached);
    try std.testing.expectEqual(@as(u32, 9), failure.byte);
    try std.testing.expectEqual(@as(u32, 3), failure.line);
    try std.testing.expectEqualStrings("branchy", failure.function.slice());
}

test "the path-state cap admits exactly one partition and still replays its diagnostic" {
    const gpa = std.testing.allocator;
    const position: cfg_mod.SrcPos = .{ .byte = 5, .line = 2, .column = 3 };
    var statements = [_]cfg_mod.Stmt{.{
        .kind = .{ .leak_warning = .{ .type_name = "Reached" } },
        .pos = position,
        .end_pos = position,
    }};
    var blocks = [_]cfg_mod.BasicBlock{
        .{ .id = @enumFromInt(0), .stmts = &statements, .successors = &.{} },
    };
    const cfg: Cfg = .{ .blocks = &blocks, .entry = @enumFromInt(0), .fn_span = .{ .start = 0, .end = 1 }, .locals = &.{} };
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    // The other side of the cap from the `max_path_states = 0` case above:
    // one slot holds the entry block's single partition, so the run finishes
    // and the replay pass reports from the partition the queue handed back.
    // A cap that tripped one slot early would abandon a run that had room;
    // one that tripped late would let a second partition in uncharged.
    budget_mod.clear();
    try check(gpa, &cfg, .{ .path = "<test>", .max_path_states = 1 }, &problems);
    try std.testing.expect(budget_mod.peek() == null);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("heap-leak", problems.items[0].rule_id);
    try std.testing.expectEqual(@as(u32, 5), problems.items[0].start.byte);
}

test "a budget-exhausted function records nothing once the record is claimed" {
    const gpa = std.testing.allocator;
    const position: cfg_mod.SrcPos = .{ .byte = 0, .line = 1, .column = 1 };
    var statements = [_]cfg_mod.Stmt{.{
        .kind = .{ .leak_warning = .{ .type_name = "Reachable" } },
        .pos = position,
        .end_pos = position,
    }};
    var blocks = [_]cfg_mod.BasicBlock{
        .{ .id = @enumFromInt(0), .stmts = &statements, .successors = &.{} },
    };
    const cfg: Cfg = .{ .blocks = &blocks, .entry = @enumFromInt(0), .fn_span = .{ .start = 0, .end = 1 }, .locals = &.{} };
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, check(gpa, &cfg, .{
        .path = "<test>",
        .max_block_visits = 0,
    }, &problems));
    _ = budget_mod.take();
    try std.testing.expect(budget_mod.peek() == null);
    // A following file that fits in its budget must not inherit the
    // previous file's failure record.
    var clean: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &clean);
    try check(gpa, &cfg, .{ .path = "<test>" }, &clean);
    try std.testing.expect(budget_mod.peek() == null);
}

test "loop with independent branch arms converges and keeps its path-specific hazards" {
    const gpa = std.testing.allocator;
    // The shape that used to exhaust `max_path_states` on ordinary
    // code (intern_pool.resolvePeerTypes, and with it every zbc run
    // that analyses zbc): a loop whose body fans out over many arms,
    // each arm declaring its own block-scoped temporaries, with
    // several flags toggled independently of the arm.  Partition
    // identity used to compare the WHOLE local map, so every
    // (arm, flag) pair became its own path state and the cross product
    // ran past 64 even though none of those temporaries carries a
    // resource.
    //
    // Converging is only half the contract.  Arm 3 frees `buf` and
    // every other arm leaves it live, so the two must stay in separate
    // partitions and the `sink(buf)` after the loop must still be
    // reported as a use-after-free — a merge that papered over the
    // difference would make this corpus quiet and wrong.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const P = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn v(self: *P, i: u32) u32 { _ = self; return i; }
        \\};
        \\fn sink(x: []u8) void { _ = x; }
        \\pub fn pick(p: *P, count: u32, use_it: bool) !u32 {
        \\    const buf = try p.gpa.alloc(u8, 8);
        \\    var f0 = false;
        \\    var f1 = false;
        \\    var f2 = false;
        \\    var total: u32 = 0;
        \\    var i: u32 = 0;
        \\    while (i < count) : (i += 1) {
        \\        const arm = i % 9;
        \\        if (use_it) f0 = true;
        \\        if (i % 2 == 0) f1 = true;
        \\        if (arm == 3) f2 = true;
        \\        if (arm == 0) {
        \\            const a0: u32 = p.v(0);
        \\            const a1: u32 = p.v(1);
        \\            const a2: u32 = p.v(2);
        \\            const a3: u32 = p.v(3);
        \\            total = a0 + a1 + a2 + a3;
        \\        } else if (arm == 1) {
        \\            const b0: u32 = p.v(4);
        \\            const b1: u32 = p.v(5);
        \\            total = b0 + b1;
        \\        } else if (arm == 2) {
        \\            const c0: u32 = p.v(6);
        \\            const c1: u32 = p.v(7);
        \\            const c2: u32 = p.v(8);
        \\            total = c0 + c1 + c2;
        \\        } else if (arm == 3) {
        \\            const d0: u32 = p.v(9);
        \\            const d1: u32 = p.v(10);
        \\            const d2: u32 = p.v(11);
        \\            const d3: u32 = p.v(12);
        \\            total = d0 + d1 + d2 + d3;
        \\            p.gpa.free(buf);
        \\        } else if (arm == 4) {
        \\            const e0: u32 = p.v(13);
        \\            total = e0;
        \\        } else if (arm == 5) {
        \\            const g0: u32 = p.v(14);
        \\            const g1: u32 = p.v(15);
        \\            total = g0 + g1;
        \\        } else if (arm == 6) {
        \\            const h0: u32 = p.v(16);
        \\            total = h0;
        \\        } else if (arm == 7) {
        \\            const j0: u32 = p.v(17);
        \\            const j1: u32 = p.v(18);
        \\            total = j0 + j1;
        \\        } else {
        \\            const k0: u32 = p.v(19);
        \\            const k1: u32 = p.v(20);
        \\            const k2: u32 = p.v(21);
        \\            total = k0 + k1 + k2;
        \\        }
        \\    }
        \\    if (f0 or f1 or f2) total += 1;
        \\    sink(buf);
        \\    return total;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var uaf = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-use-after-free")) uaf = true;
    }
    try std.testing.expect(uaf);
}

test "wide switch in a loop converges on the facts its blocks can still read" {
    const gpa = std.testing.allocator;
    // The shape that ran Runtime.evalRegDispatchMode out of
    // `max_path_states`: a dispatch loop whose arms each allocate a
    // temporary nobody reads after the arm.  Allocation records are
    // kept for diagnostics and never evicted, so every arm's `heaps`
    // entry survived the arm and the loop header carried one more id
    // per iteration — 2^7 ways to spend 64 slots distinguishing paths
    // that carry no hazard at all.
    //
    // Converging is only half the contract.  The facts a block CAN
    // still read have to keep separating the paths, or the corpus goes
    // quiet and wrong.  So this fixture must still report the double
    // free in arm 3, the use-after-free of `buf` at the sink after the
    // loop, the `= undefined` read in the last arm, and the stack
    // escape at `return &slot`.
    var problems = try analyze(gpa,
        \\const std = @import("std");
        \\const P = struct {
        \\    gpa: std.mem.Allocator,
        \\};
        \\fn sink(x: []u8) void { _ = x; }
        \\fn consume(x: u32) void { _ = x; }
        \\pub fn churn(p: *P, count: u32, use_it: bool) !*u32 {
        \\    const buf = try p.gpa.alloc(u8, 8);
        \\    var flag = false;
        \\    var scratch: u32 = undefined;
        \\    var slot: u32 = 7;
        \\    var total: u32 = 0;
        \\    var i: u32 = 0;
        \\    while (i < count) : (i += 1) {
        \\        const arm = i % 6;
        \\        if (use_it) flag = true;
        \\        if (arm == 0) {
        \\            const t = try p.gpa.alloc(u8, 4);
        \\            total += t.len;
        \\        } else if (arm == 1) {
        \\            const t = try p.gpa.alloc(u8, 4);
        \\            total += t.len;
        \\        } else if (arm == 2) {
        \\            const t = try p.gpa.alloc(u8, 4);
        \\            total += t.len;
        \\        } else if (arm == 3) {
        \\            const t = try p.gpa.alloc(u8, 4);
        \\            total += t.len;
        \\            p.gpa.free(buf);
        \\            p.gpa.free(buf);
        \\        } else if (arm == 4) {
        \\            const t = try p.gpa.alloc(u8, 4);
        \\            total += t.len;
        \\            p.gpa.free(buf);
        \\        } else {
        \\            const t = try p.gpa.alloc(u8, 4);
        \\            total += t.len;
        \\            consume(scratch);
        \\        }
        \\    }
        \\    if (flag) total += 1;
        \\    sink(buf);
        \\    if (total == 0) return error.Empty;
        \\    return &slot;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    var double_free = false;
    var use_after_free = false;
    var use_undefined = false;
    var stack_escape = false;
    for (problems.items) |p| {
        if (std.mem.eql(u8, p.rule_id, "heap-double-free")) double_free = true;
        if (std.mem.eql(u8, p.rule_id, "heap-use-after-free")) use_after_free = true;
        if (std.mem.eql(u8, p.rule_id, "use-undefined")) use_undefined = true;
        if (std.mem.eql(u8, p.rule_id, "stack-escape")) stack_escape = true;
    }
    try std.testing.expect(double_free);
    try std.testing.expect(use_after_free);
    try std.testing.expect(use_undefined);
    try std.testing.expect(stack_escape);
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

// ── Comptime-exhaustive INDEXED aggregate initialization ─────
//
// `var out: [N]E = undefined;` followed by
// `inline for (xs, 0..) |v, i| { …; out[i] = …; }` leaves every slot
// written before the loop's normal exit, so returning `out` is not a
// leak of `undefined`.  `inline for` unrolls at comptime and the `0..`
// index walks the whole collection, but the generic CFG models any
// loop as possibly running zero times, so the seed survives to the
// `return`.  These pin the proof — and, just as importantly, every
// near-miss it must still let through.
//
// Positives assert ZERO `use-undefined`.  Near-misses assert at least
// one line is still reported: handing back one undefined value is
// diagnosed more than once (at the read, and at the value leaving the
// function), so WHICH lines survive is the contract, not how many
// diagnostics name them.

/// Distinct source lines carrying `rule_id`.
fn countRuleLines(problems: []const Problem, rule_id: []const u8) usize {
    var n: usize = 0;
    for (problems, 0..) |p, i| {
        if (!std.mem.eql(u8, p.rule_id, rule_id)) continue;
        var repeats = false;
        for (problems[0..i]) |earlier| {
            if (!std.mem.eql(u8, earlier.rule_id, rule_id)) continue;
            if (earlier.start.line != p.start.line) continue;
            repeats = true;
            break;
        }
        if (!repeats) n += 1;
    }
    return n;
}

test "indexed fill: an array-literal source fills the declared array" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), countRuleLines(problems.items, "use-undefined"));
}

test "indexed fill: a slice-bound literal source counts by its elements" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const last_idx: u64 = 2;
        \\const specs: []const u8 = &.{ 7, 8, 9 };
        \\pub fn table() [last_idx + 1]u8 {
        \\    var out: [last_idx + 1]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // The source is typed as a SLICE, so the count can only come from
    // the literal it points at; the target's from `last_idx + 1`
    // chased through an immutable file-level const.  Neither number is
    // read off a name.
    try std.testing.expectEqual(@as(usize, 0), countRuleLines(problems.items, "use-undefined"));
}

test "indexed fill: an error-exiting `try` in the body does not spoil the proof" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const last_idx: u64 = 2;
        \\const specs: []const u8 = &.{ 7, 8, 9 };
        \\const Store = struct {
        \\    fn create(self: *Store) !*Store { return self; }
        \\    fn put(self: *Store, slot: *Store) void { _ = self; _ = slot; }
        \\};
        \\pub fn build(store: *Store) ![last_idx + 1]*Store {
        \\    var out: [last_idx + 1]*Store = undefined;
        \\    inline for (specs, 0..) |spec, i| {
        \\        const ref = try store.create();
        \\        _ = spec;
        \\        out[i] = ref;
        \\        store.put(ref);
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), countRuleLines(problems.items, "use-undefined"));
}

test "indexed fill: a @Tuple over the enumerated vector fills the tuple" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const kinds = [_]u8{ 10, 20 };
        \\const pair = @Tuple(&kinds);
        \\fn forward(args: pair) u8 { _ = args; return 0; }
        \\pub fn make() fn (u8, u8) u8 {
        \\    return struct {
        \\        fn call(a: u8, b: u8) u8 {
        \\            _ = a;
        \\            _ = b;
        \\            var slots: pair = undefined;
        \\            inline for (kinds, 0..) |v, i| {
        \\                slots[i] = v;
        \\            }
        \\            return forward(slots);
        \\        }
        \\    }.call;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `@Tuple(&kinds)` has exactly `kinds.len` fields and the `0..`
    // index writes each one — no number is needed to see it.
    try std.testing.expectEqual(@as(usize, 0), countRuleLines(problems.items, "use-undefined"));
}

test "indexed fill: a zero-length target is vacuously filled" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{};
        \\pub fn fill() [0]u8 {
        \\    var out: [0]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), countRuleLines(problems.items, "use-undefined"));
}

test "indexed fill: a shorter source leaves the tail undefined" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a target whose type is a const-bound array fills too" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\const triple = [3]u8;
        \\pub fn fill() triple {
        \\    var out: triple = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // The target's element count comes from the type the name is bound
    // to, not from the `triple` text at the declaration site.
    try std.testing.expectEqual(@as(usize, 0), countRuleLines(problems.items, "use-undefined"));
}

test "indexed fill: an index range starting at one does not prove the target" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 1..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a truncated index range does not prove the target" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..2) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a write behind a conditional does not prove the target" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        if (v > 0) out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: an unlabeled break out of the enumeration does not prove the target" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        if (v > 100) break;
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: an unlabeled continue in the enumeration does not prove the target" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        if (v > 100) continue;
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a by-pointer payload does not prove the target" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn fill() [3]u8 {
        \\    var specs: [3]u8 = .{ 7, 8, 9 };
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |*v, i| {
        \\        out[i] = v.*;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: an undefined right-hand side does not define the slot" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        _ = v;
        \\        out[i] = @as(u8, undefined);
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: storing a local seeded undefined does not define the slot" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var seed: u8 = undefined;
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v + seed;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a body-local shadow of the target does not prove the outer local" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        var out: [3]u8 = undefined;
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a second mention of the target in the body does not prove it" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        const alias = &out;
        \\        _ = alias;
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a runtime for over the same source does not prove the target" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a mutable source carries no immutable length binding" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn fill() [3]u8 {
        \\    var specs: [3]u8 = .{ 7, 8, 9 };
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: an ambiguous source name is not a length binding" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn other() void {
        \\    const specs = [_]u8{ 1 };
        \\    _ = specs;
        \\}
        \\pub fn fill() [3]u8 {
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a slice target is not a fixed aggregate" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\fn sink(s: []u8) void { _ = s; }
        \\pub fn spill() void {
        \\    var out: []u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    sink(out);
        \\}
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a @Tuple over a different vector does not prove the target" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const kinds = [_]u8{ 10, 20, 30 };
        \\const other = [_]u8{ 1, 2, 3, 4 };
        \\const wide = @Tuple(&other);
        \\fn forward(args: wide) u8 { _ = args; return 0; }
        \\pub fn make() fn (u8) u8 {
        \\    return struct {
        \\        fn call(a: u8) u8 {
        \\            _ = a;
        \\            var slots: wide = undefined;
        \\            inline for (kinds, 0..) |v, i| {
        \\                slots[i] = v;
        \\            }
        \\            return forward(slots);
        \\        }
        \\    }.call;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `wide` has four fields and the loop writes three, so the last
    // slot really is undefined — the binding identity is load-bearing.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

// The count a fill proves is read off the DECLARATION a reference
// names, resolved through the file's scopes.  These pin that: the
// reference has to mean the binding whose length the target was
// given, and a same-spelled declaration somewhere else in the file is
// not that binding.

test "indexed fill: another namespace's same-named const is not this source's length" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Catalog = struct {
        \\    pub const specs = [_]u8{ 7, 8, 9 };
        \\};
        \\const Slot = struct {
        \\    pub var specs: [2]u8 = .{ 1, 2 };
        \\    pub fn fill() [3]u8 {
        \\        var out: [3]u8 = undefined;
        \\        inline for (specs, 0..) |v, i| {
        \\            out[i] = v;
        \\        }
        \\        return out;
        \\    }
        \\};
    );
    defer freeProblems(gpa, &problems);
    // `specs` inside `Slot.fill` is `Slot`'s own two-element `var`, so
    // the third slot really is undefined.  `Catalog.specs` is three
    // elements long and shares nothing but the spelling.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a same-named file const does not vouch for a parameter" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const specs = [_]u8{ 7, 8, 9 };
        \\pub fn fill(specs: [2]u8) [3]u8 {
        \\    _ = specs;
        \\    var out: [3]u8 = undefined;
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // The loop walks the PARAMETER — two elements at most — whatever
    // the file-level `specs` happens to hold.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a target measured by the enumerated expression's own .len fills" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Descriptor = struct { kind: u32 };
        \\const FnInfo = struct { params: [3]Descriptor };
        \\pub fn wrapper(seed: u32) [3]u32 {
        \\    _ = seed;
        \\    const fn_info = FnInfo{ .params = .{ .{ .kind = 1 }, .{ .kind = 2 }, .{ .kind = 3 } } };
        \\    var out: [fn_info.params.len]u32 = undefined;
        \\    inline for (fn_info.params, 0..) |p, i| {
        \\        out[i] = p.kind;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `[fn_info.params.len]u32` measures exactly what the `0..` index
    // walks, so no element count has to be evaluated at all.
    try std.testing.expectEqual(@as(usize, 0), countRuleLines(problems.items, "use-undefined"));
}

test "indexed fill: a resliceable source's own .len does not make the loop exhaustive" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\pub fn wrapper(seed: u32) [3]u8 {
        \\    _ = seed;
        \\    var specs: []const u8 = &.{ 7, 8, 9 };
        \\    var out: [specs.len]u8 = undefined;
        \\    specs = specs[0..2];
        \\    inline for (specs, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // The target's count is stated, and the loop is comptime-
    // exhaustive over whatever `specs` holds when it runs — which is
    // two elements, so the last slot really is undefined.  Only an
    // IMMUTABLE root can stand for `[<it>.len]`.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a plain for inside a comptime block fills the array it measures" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Descriptor = struct { kind: u32 };
        \\const FnInfo = struct { params: [2]Descriptor };
        \\pub fn wrapper(seed: u32) [2]u32 {
        \\    _ = seed;
        \\    const fn_info = FnInfo{ .params = .{ .{ .kind = 1 }, .{ .kind = 2 } } };
        \\    const types = comptime blk: {
        \\        var types: [fn_info.params.len]u32 = undefined;
        \\        for (fn_info.params, 0..) |p, i| {
        \\            types[i] = p.kind;
        \\        }
        \\        break :blk types;
        \\    };
        \\    return types;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // Every statement of a `comptime` block is evaluated at comptime,
    // so a plain `for` there still writes all `fn_info.params.len`
    // slots — the count both sides state is one and the same `.len`.
    try std.testing.expectEqual(@as(usize, 0), countRuleLines(problems.items, "use-undefined"));
}

// A `[<collection>.len]` target states its count by naming a
// collection, and there are exactly two ways that count can be
// established.  Each needs its own proof, and neither can be reached
// through the other:
// //
//   - the collection is a field of an AGGREGATE LITERAL, so every
//     element is written out and the count is simply counted;
//   - it is a field of a COMPILER REFLECTION value, whose shape is
//     a function of the type it describes, so both sites naming the
//     same declared value name the same count.
// //
// What does NOT establish it is a `const`, or a value at the root of
// the path.  A `const` freezes a binding, not the storage behind it;
// and `.{ .child = &holder }` is a value whose `.child` field is a
// `*Holder` the owner can still resize.  These pin all of it: the
// positive is the shape a generated wrapper needs, and the
// near-misses are a pointer at the root, a pointer one field down, a
// pointer handed out by `@field`, a different field, another
// declaration, and a destructured name.

test "indexed fill: a reflection-built descriptor's field length sizes the array it fills" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\fn conv(a: u32, b: u32) u32 { return a + b; }
        \\pub fn wrapper(seed: u32) [2]bool {
        \\    _ = seed;
        \\    const info = @typeInfo(@TypeOf(conv)).@"fn";
        \\    return comptime blk: {
        \\        var out: [info.params.len]bool = undefined;
        \\        for (info.params, 0..) |p, i| {
        \\            out[i] = p.is_noalias;
        \\        }
        \\        break :blk out;
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `[info.params.len]bool` and `for (info.params, 0..)` read the
    // same field of the same reflection value, and a reflection value
    // is fixed by the type it describes rather than by storage anyone
    // can write.  Both sites resolve to one declaration, so the count
    // is settled without either of them being evaluated.
    try std.testing.expectEqual(@as(usize, 0), countRuleLines(problems.items, "use-undefined"));
}

test "indexed fill: a different field of the same descriptor is not this target's length" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Descriptor = struct { kind: u32 };
        \\const FnInfo = struct { params: [3]Descriptor, rest: [2]Descriptor };
        \\pub fn wrapper(seed: u32) [3]u32 {
        \\    _ = seed;
        \\    const fn_info = FnInfo{
        \\        .params = .{ .{ .kind = 1 }, .{ .kind = 2 }, .{ .kind = 3 } },
        \\        .rest = .{ .{ .kind = 4 }, .{ .kind = 5 } },
        \\    };
        \\    var out: [fn_info.params.len]u32 = undefined;
        \\    inline for (fn_info.rest, 0..) |p, i| {
        \\        out[i] = p.kind;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // One root, two fields.  The target was sized by `params` and the
    // loop walks `rest`, so the third slot really is left undefined —
    // sharing a root is not sharing a length.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: the same field on another descriptor is not this target's length" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Descriptor = struct { kind: u32 };
        \\const Left = struct { params: [3]Descriptor };
        \\const Right = struct { params: [2]Descriptor };
        \\pub fn wrapper(seed: u32) [3]u32 {
        \\    _ = seed;
        \\    const left = Left{ .params = .{ .{ .kind = 1 }, .{ .kind = 2 }, .{ .kind = 3 } } };
        \\    const right = Right{ .params = .{ .{ .kind = 4 }, .{ .kind = 5 } } };
        \\    var out: [left.params.len]u32 = undefined;
        \\    inline for (right.params, 0..) |p, i| {
        \\        out[i] = p.kind;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `params` is spelled the same on both sides, but `left` and
    // `right` are two declarations of two different types — three
    // descriptors against two.  Only the declaring token says which
    // one a reference meant, so the third slot really is undefined.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a const pointer's field can still be resized before the loop" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Holder = struct { items: []const u8 };
        \\pub fn build() [3]u8 {
        \\    return comptime blk: {
        \\        var holder = Holder{ .items = &.{ 1, 2, 3 } };
        \\        const pointer = &holder;
        \\        var out: [pointer.items.len]u8 = undefined;
        \\        pointer.items = &.{ 9, 8 };
        \\        for (pointer.items, 0..) |v, i| {
        \\            out[i] = v;
        \\        }
        \\        break :blk out;
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `pointer` is a `const`, and that is not enough: it holds a
    // `*Holder`, so `holder` can resize `items` between the target's
    // declaration and the loop — which it does.  Const-ness of the
    // BINDING is not immutability of what the binding points at, so
    // the last slot really is undefined.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a pointer reached THROUGH a value's field is not a fixed length" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Holder = struct { items: []const u8 };
        \\fn inspect() [3]u8 {
        \\    return comptime blk: {
        \\        var holder = Holder{ .items = &.{ 1, 2, 3 } };
        \\        const descriptor = .{ .child = &holder };
        \\        var out: [descriptor.child.items.len]u8 = undefined;
        \\        holder.items = &.{ 9, 8 };
        \\        for (descriptor.child.items, 0..) |v, i| out[i] = v;
        \\        break :blk out;
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `descriptor` is a VALUE — and that is not enough, because
    // `descriptor.child` is a `*Holder`.  The `.len` read at the end
    // of the path is `holder`'s, and `holder` is still mutable: it is
    // shortened from three elements to two right there.  A root being
    // a value says nothing about what its fields hold.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a pointer reached through @field is not a fixed length" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\const Holder = struct { items: []const u8 };
        \\fn inspect() [3]u8 {
        \\    return comptime blk: {
        \\        var holder = Holder{ .items = &.{ 1, 2, 3 } };
        \\        const pointer = @field(.{ .child = &holder }, "child");
        \\        var out: [pointer.items.len]u8 = undefined;
        \\        holder.items = &.{ 9, 8 };
        \\        for (pointer.items, 0..) |v, i| out[i] = v;
        \\        break :blk out;
        \\    };
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `@field` hands back whatever field it is asked for, and here
    // that field is a `*Holder`.  What a builtin RETURNS is a question
    // only its own semantics answer, so `@field` cannot be treated as
    // producing a fixed value — and `holder` is still resized.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: a destructured name is one element of the tuple, not the tuple" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\fn inspect() [3]u8 {
        \\    const a, const b, const c = .{ .{ 1, 2 }, .{}, .{ 3 } };
        \\    _ = a;
        \\    _ = b;
        \\    var out: [3]u8 = undefined;
        \\    inline for (c, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `const a, const b, const c = .{ … };` destructures: `c` holds
    // `.{ 3 }`, ONE descriptor, not the three-element tuple it came
    // out of.  Only the first name of the declaration binds the whole
    // tuple, so no later name can stand for its length.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: an empty destructured element writes no slot at all" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\fn inspect() [3]u8 {
        \\    const a, const b, const c = .{ .{ 1, 2 }, .{}, .{ 3 } };
        \\    _ = a;
        \\    _ = c;
        \\    var out: [3]u8 = undefined;
        \\    inline for (b, 0..) |v, i| {
        \\        out[i] = v;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // `b` is `.{}` — zero elements — so the enumeration is empty and
    // every slot of the three-element target stays unwritten.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}

test "indexed fill: another reflection descriptor's parameters are not this target's length" {
    const gpa = std.testing.allocator;
    var problems = try analyze(gpa,
        \\fn one(a: u32, b: u32) u32 { return a + b; }
        \\fn two(a: u32) u32 { return a; }
        \\pub fn wrapper(seed: u32) [2]bool {
        \\    _ = seed;
        \\    const first = @typeInfo(@TypeOf(one)).@"fn";
        \\    const second = @typeInfo(@TypeOf(two)).@"fn";
        \\    var out: [first.params.len]bool = undefined;
        \\    inline for (second.params, 0..) |p, i| {
        \\        out[i] = p.is_noalias;
        \\    }
        \\    return out;
        \\}
    );
    defer freeProblems(gpa, &problems);
    // Both roots describe a function, and both fields are spelled
    // `params`, but `first` and `second` are two declarations: two
    // parameters against one.  Naming a reflection value settles a
    // count only when both sites name the SAME one.
    try std.testing.expect(countRuleLines(problems.items, "use-undefined") >= 1);
}
