//! Transfer functions per StmtKind.  Each takes an AbstractState and a
//! Stmt, mutates the state to reflect the statement's effect, and may
//! emit Problems.
//!
//! Design rule: never abort on unknown shapes — `.lowering_gap` and
//! `.unknown` are conservative-fall-through.  False negatives on
//! exotic syntax are preferred over false positives.

const std = @import("std");
const problem_mod = @import("../problem.zig");
const cfg = @import("cfg.zig");
const state_mod = @import("abstract_state.zig");
const config_mod = @import("../config.zig");
const type_query = @import("../model/type_query.zig");

const Problem = problem_mod.Problem;
const Severity = problem_mod.Severity;

const Stmt = cfg.Stmt;
const StmtKind = cfg.StmtKind;
const ExprKind = cfg.ExprKind;
const LocalInfo = cfg.LocalInfo;

const AbstractState = state_mod.AbstractState;
const Origin = state_mod.Origin;
const LocalId = state_mod.LocalId;

/// The identities of the diagnostics one analysis run has already
/// emitted.  The solver owns one and hands it to every [Ctx] it builds,
/// because it replays each block once per path state that block holds:
/// without a memo of what has already been said, every report at an
/// already-reported site re-derives its message and re-reads the whole
/// finding list to discover it is a duplicate.
///
/// Identity is the pair the old scan compared — the rule and the byte
/// its primary span starts at — so two reports agree exactly when they
/// name one source operation, and a second rule or a second site at
/// the same byte is still its own finding.  [Context] carries that
/// comparison on the rule's bytes, never on a `Problem`'s raw bytes.
///
/// The rule id in a key is BORROWED, never copied.  A report's rule id
/// is a `comptime` parameter, so it is a string literal with static
/// lifetime; an adopted one is `Problem.rule_id`, which the module
/// already requires to outlive the findings carrying it, because
/// `Problem.deinit` never frees it.  Both outlive this memo, whose
/// lifetime ends inside the `check` call that owns the list.
pub const Seen = struct {
    const Key = struct { rule_id: []const u8, byte: u32 };

    keys: std.ArrayHashMapUnmanaged(Key, void, Context, true) = .empty,
    /// Findings the caller already held, and whether they have been
    /// folded in yet.  Both are set by [adopt] and consumed by the
    /// first [record].
    unadopted: ?[]const Problem = null,
    adopted: bool = false,

    /// Identity is BYTES, not addresses.  `std.hash_map.AutoContext`
    /// cannot be used here: it routes to `std.hash.autoHash`, which
    /// rejects any key containing a slice outright, and its equality
    /// is `std.meta.eql`, which compares a slice by `ptr` + `len`.  A
    /// rule id adopted from `ctx.problems` and the same rule id passed
    /// to `report` are equal strings at different addresses, so an
    /// address comparison would report a source operation twice — the
    /// exact answer the scan over `ctx.problems` never gave.  Hashing
    /// the bytes keeps distinct rule ids apart and identical ones
    /// together, which is what the scan's `std.mem.eql` did.
    const Context = struct {
        pub fn hash(_: Context, key: Key) u32 {
            return @truncate(std.hash.Wyhash.hash(
                std.hash_map.hashString(key.rule_id),
                std.mem.asBytes(&key.byte),
            ));
        }

        pub fn eql(_: Context, a: Key, b: Key, _: usize) bool {
            return a.byte == b.byte and std.mem.eql(u8, a.rule_id, b.rule_id);
        }
    };

    pub fn init() Seen {
        return .{};
    }

    pub fn deinit(self: *Seen, gpa: std.mem.Allocator) void {
        self.keys.deinit(gpa);
    }

    /// Record `rule_id` at `byte`.  Returns false when that diagnostic
    /// has already been recorded — the caller's cue to skip building a
    /// message and a note for a finding nobody will read twice.
    ///
    /// Failing to remember a diagnostic is an analysis failure, not a
    /// silent one: reporting without the memo would hand back the same
    /// finding once per path state.
    pub fn record(self: *Seen, gpa: std.mem.Allocator, rule_id: []const u8, byte: u32) !bool {
        // The findings [adopt] was given are folded in HERE, on the
        // first diagnostic this run actually emits.  A function that
        // reports nothing never consults the memo, so it never pays to
        // walk a list it was never going to read — the scan this
        // replaced likewise ran only on a real report.
        if (!self.adopted) {
            self.adopted = true;
            if (self.unadopted) |existing| {
                // Nothing has been appended since [adopt] captured this
                // slice: a run records a diagnostic before it appends
                // it, so the list cannot have moved under the seed.
                for (existing) |problem| _ = try self.put(gpa, problem.rule_id, problem.start.byte);
            }
        }
        return self.put(gpa, rule_id, byte);
    }

    fn put(self: *Seen, gpa: std.mem.Allocator, rule_id: []const u8, byte: u32) !bool {
        const slot = try self.keys.getOrPut(gpa, .{ .rule_id = rule_id, .byte = byte });
        if (slot.found_existing) return false;
        slot.value_ptr.* = {};
        return true;
    }

    /// Remember the findings the caller already holds, so a run that
    /// writes into a non-empty list keeps the same "first one wins"
    /// answer the scan over that list gave it.  Recording what to adopt
    /// costs nothing; the pass itself belongs to [record], and runs
    /// only if this run emits anything at all.
    pub fn adopt(self: *Seen, problems: []const Problem) void {
        self.unadopted = problems;
    }
};

pub const Ctx = struct {
    gpa: std.mem.Allocator,
    locals: []const LocalInfo,
    /// Where to push problems.
    problems: *std.ArrayListUnmanaged(Problem),
    /// Source file path for diagnostics.
    path: []const u8,
    /// The run's record of what has already been reported, owned by
    /// whoever outlives the [Ctx] — the solver, which builds one [Ctx]
    /// per block visit and replays every block once per path state.
    seen: *Seen,
    /// Invariant gating.  Some checks run inside transfer (arena_escape
    /// fires from transferRet, not from a dedicated Stmt) — those
    /// consult the config to honor Config.enabled.
    config: *const config_mod.Config = &config_mod.Default,
    report_enabled: bool = true,
};

/// Mutate `state` to reflect the effect of `stmt`.  Emit any problems
/// to `ctx.problems`.
pub fn transfer(ctx: Ctx, state: *AbstractState, stmt: Stmt) !void {
    if (!state.feasible) return;
    switch (stmt.kind) {
        .decl => |d| try transferDecl(ctx, state, d, stmt.pos),
        .assign => |a| try transferAssign(ctx, state, a, stmt.pos),
        .assume => |condition| state.feasible = switch (condition) {
            .constant => |value| value,
            .local => |local| try state.facts.assumeBoolean(ctx.gpa, local, true, !ctx.locals[@intFromEnum(local)].address_taken),
            .not_local => |local| try state.facts.assumeBoolean(ctx.gpa, local, false, !ctx.locals[@intFromEnum(local)].address_taken),
        },
        .guard_fact => |g| state.feasible = try state.facts.assumeGuard(ctx.gpa, g.guard, g.holds),
        .arena_kill => |k| try transferArenaKill(ctx, state, k, stmt.pos, stmt.end_pos),
        .heap_free => |f| try transferHeapFree(ctx, state, f, stmt.pos, stmt.end_pos),
        .ret => |r| try transferRet(ctx, state, r, stmt.pos, stmt.end_pos),
        .use => |u| try transferUse(ctx, state, u, stmt.pos, stmt.end_pos),
        .pointer_write => |p| {
            state.facts.forgetLocal(p.target);
            if (state.locals.get(p.target)) |origin| {
                if (origin == .stack) {
                    state.facts.forgetLocal(origin.stack);
                }
                if (origin == .undef) try state.locals.put(ctx.gpa, p.target, .plain);
            }
        },
        .reset_capture => |r| {
            state.facts.forgetLocal(r.local);
            try state.locals.put(ctx.gpa, r.local, .plain);
            // Also clear any tracked FIELD origins for this local —
            // `for (bins) |bin| ctx.allocator.free(bin.path);` frees
            // `bin.path` once per iteration; without clearing the
            // field, iter N+1 sees iter N's freed state and reports
            // a spurious double-free of `bin.path`.
            state.forgetFields(r.local);
        },
        .composite_escape => |c| try transferCompositeEscape(ctx, state, c, stmt.pos, stmt.end_pos),
        .field_assign => |a| try transferFieldAssign(ctx, state, a, stmt.pos),
        .field_heap_free => |f| try transferFieldHeapFree(ctx, state, f, stmt.pos, stmt.end_pos),
        .field_use => |u| try transferFieldUse(ctx, state, u, stmt.pos, stmt.end_pos),
        .out_param_write => |w| try transferOutParamWrite(ctx, state, w, stmt.pos, stmt.end_pos),
        .interior_pointer_destroy => |i| try transferInteriorPointerDestroy(ctx, state, i, stmt.pos, stmt.end_pos),
        .leak_warning => |l| try transferLeakWarning(ctx, l, stmt.pos, stmt.end_pos),
        .partial_union_write => |p| try transferPartialUnionWrite(ctx, p, stmt.pos, stmt.end_pos),
        .lowering_gap => |g| transferGap(state, g),
    }
}

fn booleanValue(state: *const AbstractState, value: cfg.BooleanValue) ?bool {
    return switch (value) {
        .constant => |v| v,
        .local => |local| state.facts.boolean(local),
        .not_local => |local| if (state.facts.boolean(local)) |v| !v else null,
    };
}

fn bindBoolean(ctx: Ctx, state: *AbstractState, local: LocalId, kind: ExprKind) !void {
    const value = if (ctx.locals[@intFromEnum(local)].address_taken) null else switch (kind) {
        .boolean => |v| booleanValue(state, v),
        .copy_of => |source| state.facts.boolean(source),
        else => null,
    };
    try state.facts.bindBoolean(ctx.gpa, local, value);
}

fn transferLeakWarning(
    ctx: Ctx,
    l: @TypeOf(@as(StmtKind, undefined).leak_warning),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    if (!config_mod.isEnabled(ctx.config, .heap_leak)) return;
    try report(ctx, "heap-leak", pos, end_pos, .@"error", "destructor for `{s}` does not free `self` — instances allocated by the type's heap-creator leak (no `allocator.destroy(self)` reachable from this destructor)", .{l.type_name});
}

fn transferPartialUnionWrite(
    ctx: Ctx,
    p: @TypeOf(@as(StmtKind, undefined).partial_union_write),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    if (!config_mod.isEnabled(ctx.config, .partial_union_write)) return;
    try report(ctx, "partial-union-write", pos, end_pos, .@"error", "tagged-union literal writes the `.{s}` tag before evaluating its payload; an early-exit (`try` / `catch return`) in the payload leaves the LHS with the new tag and stale/garbage payload bytes — hoist the fallible expression into a local first", .{p.tag_name});
}

fn transferInteriorPointerDestroy(
    ctx: Ctx,
    state: *AbstractState,
    i: @TypeOf(@as(StmtKind, undefined).interior_pointer_destroy),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    _ = state;
    if (!config_mod.isEnabled(ctx.config, .interior_pointer_destroy)) return;
    const receiver_name = ctx.locals[@intFromEnum(i.receiver)].name;
    const container_name = ctx.locals[@intFromEnum(i.container)].name;
    try report(ctx, "interior-pointer-destroy", pos, end_pos, .@"error", "destroying `{s}` — an interior pointer into `{s}` — is undefined behavior under typical allocators (the pointer wasn't returned by allocator.create)", .{ receiver_name, container_name });
}

fn transferDecl(
    ctx: Ctx,
    state: *AbstractState,
    d: @TypeOf(@as(StmtKind, undefined).decl),
    pos: cfg.SrcPos,
) !void {
    try bindBoolean(ctx, state, d.local, d.init_kind);
    const origin = try originOfInit(ctx, state, d.init_kind, pos);
    try state.locals.put(ctx.gpa, d.local, scalarBindingOrigin(ctx, d.local, origin));
    // Clear any stale field state for this local — a fresh decl
    // (e.g. `const source = ...` inside a loop body) creates a new
    // instance; prior-iteration field tracking for the same LocalId
    // is a back-edge artifact that would spuriously fire double-free
    // / UAF on the new instance.
    state.forgetFields(d.local);
}

/// A binding DECLARED with a primitive scalar type cannot hold an
/// address, so a resource origin flowing into one is a mis-attribution
/// rather than a claim about its lifetime.
///
/// `var out: u8 = 0; … defer out = observe(p); defer gpa.free(p);`
/// assigns a callee result whose own origin is `copy_of(p)` into that
/// `u8`.  The `u8` holds a byte copied OUT of `p`, not `p` itself;
/// binding it to the allocation makes the later `return out` read a
/// freed heap — a use-after-free of a value that was never an
/// address.  The origin it arrived with comes from the callee's own
/// `@returns borrowed_from(0)` reading, which is right for a
/// pointer-typed result and wrong for one the declared type cannot
/// carry; the DECLARED TYPE is what settles it here.
///
/// Every other answer keeps the origin.  A binding with no declared
/// type, a pointer, a slice, an array, a struct, a generic or an
/// opaque one can hold any of them, and downgrading there would lose
/// a real use-after-free.  Only a positively-proven address-free type
/// downgrades, which is exactly what [type_query.
/// isReservedScalarTypeName] claims and no more.
fn scalarBindingOrigin(ctx: Ctx, local: LocalId, origin: Origin) Origin {
    switch (origin) {
        .heap, .arena, .arena_borrow => {},
        else => return origin,
    }
    const type_name = ctx.locals[@intFromEnum(local)].type_name orelse return origin;
    if (!type_query.isReservedScalarTypeName(type_name)) return origin;
    return .plain;
}

fn transferAssign(
    ctx: Ctx,
    state: *AbstractState,
    a: @TypeOf(@as(StmtKind, undefined).assign),
    pos: cfg.SrcPos,
) !void {
    try bindBoolean(ctx, state, a.target, a.rhs_kind);
    const origin = try originOfInit(ctx, state, a.rhs_kind, pos);
    try state.locals.put(ctx.gpa, a.target, scalarBindingOrigin(ctx, a.target, origin));
    // Whole-local reassignment invalidates any tracked field
    // origins for this local — the new value is independent of the
    // old.  Common cases: `&local` passed to a fn (cfg emits an
    // .assign with .unknown to clear .undef; the called fn may
    // also have initialised any field), and `x = foo()` rebinding
    // x.  Stale field state would surface as use-undefined / leak
    // FPs on the new value's fields.
    state.forgetFields(a.target);
}

fn transferArenaKill(
    ctx: Ctx,
    state: *AbstractState,
    k: @TypeOf(@as(StmtKind, undefined).arena_kill),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    const origin = state.locals.get(k.arena_local) orelse return;
    switch (origin) {
        .arena => |aid| {
            try state.arenas.put(ctx.gpa, aid, .{
                .state = .dead,
                .killed_at = killSiteOf(pos, end_pos),
            });
        },
        else => {},
    }
}

/// Separator between a parent local name and its field path in
/// diagnostic messages.  Field paths starting with `[` (subscript
/// like "[0].field") want no dot — `arr[0].field` not
/// `arr.[0].field`.  Field paths starting with an ident want a `.`
/// for readability — `obj.field` not `objfield`.
fn pathSep(name: []const u8) []const u8 {
    if (name.len > 0 and name[0] == '[') return "";
    return ".";
}

fn killSiteOf(pos: cfg.SrcPos, end_pos: cfg.SrcPos) state_mod.KillSite {
    return .{
        .line = pos.line,
        .column = pos.column,
        .byte = pos.byte,
        .end_line = end_pos.line,
        .end_column = end_pos.column,
        .end_byte = end_pos.byte,
    };
}

fn transferHeapFree(
    ctx: Ctx,
    state: *AbstractState,
    f: @TypeOf(@as(StmtKind, undefined).heap_free),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    if (state.locals.get(f.freed_local)) |origin| {
        switch (origin) {
            .heap => |hid| {
                const st = state.heaps.get(hid) orelse return;
                if (st.state == .dead) {
                    if (config_mod.isEnabled(ctx.config, .heap_double_free)) {
                        const name = ctx.locals[@intFromEnum(f.freed_local)].name;
                        try reportWithNote(ctx, "heap-double-free", pos, end_pos, .@"error", "double-free of `{s}`", .{name}, if (st.killed_at) |ks|
                            .{ .site = ks, .label = "first freed here" }
                        else
                            null);
                    }
                    return;
                }
                // Allocator-mismatch check.  Only fire when BOTH
                // sides resolve to a known local AND those locals
                // differ.  Same-local: definitely-same allocator;
                // either-side-null: unknown, no fire.  Different
                // locals: possible mismatch (might be aliased via
                // `var a2 = a;` but we accept that conservative FP
                // class — the user can rebind or skip the check).
                if (st.allocator_local != null and f.allocator_local != null and
                    st.allocator_local.? != f.allocator_local.?)
                {
                    if (config_mod.isEnabled(ctx.config, .allocator_mismatch)) {
                        const freed_name = ctx.locals[@intFromEnum(f.freed_local)].name;
                        const alloc_alloc = ctx.locals[@intFromEnum(st.allocator_local.?)].name;
                        const free_alloc = ctx.locals[@intFromEnum(f.allocator_local.?)].name;
                        try report(ctx, "allocator-mismatch", pos, end_pos, .@"error", "`{s}` was allocated by `{s}` but freed by `{s}` — allocators must match", .{ freed_name, alloc_alloc, free_alloc });
                    }
                    return;
                }
                try state.heaps.put(ctx.gpa, hid, .{
                    .state = .dead,
                    .killed_at = killSiteOf(pos, end_pos),
                    .allocator_local = st.allocator_local,
                });
                return;
            },
            .plain, .undef => {
                // Fall through to fallback below — plain/undef
                // means we have no tracked heap id, but the @takes
                // annotation says callee took ownership, so any
                // subsequent use of this local is UB.
            },
            else => return, // .arena, .arena_borrow, .stack — not a free target
        }
    }
    // Inter-procedural fallback: local has no tracked .heap origin
    // (e.g. it's a `*T` parameter whose allocation happened in the
    // caller).  The @takes ownership annotation tells us the callee
    // freed it; record via fallback_hid so subsequent uses fire UAF.
    try state.heaps.put(ctx.gpa, f.fallback_hid, .{
        .state = .dead,
        .killed_at = killSiteOf(pos, end_pos),
        .is_inter_procedural = true,
    });
    try state.locals.put(ctx.gpa, f.freed_local, .{ .heap = f.fallback_hid });
}

fn transferRet(
    ctx: Ctx,
    state: *AbstractState,
    r: @TypeOf(@as(StmtKind, undefined).ret),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    try transferRetValueChecks(ctx, state, r, pos, end_pos);
    try transferRetOutParamDanglingHeaps(ctx, state, pos, end_pos);
}

/// At function exit, scan `state.out_param_writes` for entries
/// whose recorded HeapId is now dead.  Fires when a value written
/// through a `*T` parameter is freed (typically via `defer`) before
/// the function returns — the caller's pointee dangles.  Closes the
/// oven-sh/bun#30151-shape gap:
///
///     defer buf.deinit();
///     out.* = buf.slice();      // at write time buf is live
///     return;                    // at return defer fires → buf dead
fn transferRetOutParamDanglingHeaps(
    ctx: Ctx,
    state: *AbstractState,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    if (!config_mod.isEnabled(ctx.config, .heap_use_after_free)) return;
    for (state.out_param_writes.keys(), state.out_param_writes.values()) |out_local, hid| {
        const st = state.heaps.get(hid) orelse continue;
        if (st.state != .dead) continue;
        const out_name = ctx.locals[@intFromEnum(out_local)].name;
        try reportWithNote(ctx, "heap-use-after-free", pos, end_pos, .@"error", "value written through `{s}` was freed before return — caller's pointee dangles", .{out_name}, if (st.killed_at) |ks|
            .{ .site = ks, .label = "value freed here" }
        else
            null);
    }
}

fn transferRetValueChecks(
    ctx: Ctx,
    state: *AbstractState,
    r: @TypeOf(@as(StmtKind, undefined).ret),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    // Only borrowed-shape return types can leak a borrowed origin.
    // Value-typed returns MOVE the value (and any arena it owns) to
    // the caller — that's idiomatic, not a bug.
    const origin = try originOfInit(ctx, state, r.value_kind, pos);

    // Undefined-return check: not gated on return type — returning
    // garbage is wrong for value types and pointers alike.
    //
    // EXCEPTION: literal `return undefined;` — the author explicitly
    // typed the keyword as the return value, almost always as a
    // comptime-gated sentinel for paths the caller is guaranteed not
    // to use (bindgen stubs, comptime-disabled features).  The real
    // bug class — undef leaking through a variable — still fires
    // because that path produces .undef via an identifier expr, which
    // doesn't set is_literal_undef.
    if (origin == .undef and !r.is_literal_undef and
        config_mod.isEnabled(ctx.config, .use_undefined))
    {
        try report(ctx, "use-undefined", pos, end_pos, .@"error", "returning a value that is still `undefined`", .{});
        return;
    }

    // Stack escape isn't gated on return type — a value-shape return
    // can still embed a pointer to a stack local (e.g. `return .{
    // .p = &x }`).  Unlike arenas (which can move), stack storage
    // always dies with the frame, so any .stack origin reaching ret
    // is wrong regardless of the outer return type.
    if (origin == .stack and config_mod.isEnabled(ctx.config, .stack_escape)) {
        const name = ctx.locals[@intFromEnum(origin.stack)].name;
        if (r.is_borrowed_return_type) {
            try report(ctx, "stack-escape", pos, end_pos, .@"error", "returning a pointer to a function-local stack variable `{s}` (escapes its frame)", .{name});
        } else {
            try report(ctx, "stack-escape", pos, end_pos, .@"error", "returning a value that holds a pointer to function-local stack variable `{s}` (escapes its frame)", .{name});
        }
        return;
    }

    // Composite-borrow returns: the embedded local is a borrow
    // regardless of the outer return type, so apply escape checks
    // unconditionally.  Direct borrow-shape returns (`return &x`,
    // `return arena.text()`) still go through the existing
    // is_borrowed_return_type gate.
    const is_composite = r.value_kind == .composite_borrow;
    const apply_check = r.is_borrowed_return_type or is_composite;
    if (!apply_check) return;
    switch (origin) {
        .arena, .arena_borrow => |aid| {
            if (!config_mod.isEnabled(ctx.config, .arena_escape)) return;
            const ast = state.arenas.get(aid) orelse return;
            // Arena moved into returned struct ("object owns its own
            // arena" pattern): when the arena was stored as a field of
            // the heap-allocated return value, its lifetime transfers
            // to the heap — the struct manages its own cleanup.
            if (ast.is_heap_allocated) return;
            if (is_composite) {
                try report(ctx, "arena-escape", pos, end_pos, .@"error", "returning a value that holds a borrow from function-local arena (escapes its lifetime)", .{});
            } else {
                try report(ctx, "arena-escape", pos, end_pos, .@"error", "returning a value borrowed from a function-local arena (escapes its lifetime)", .{});
            }
        },
        .heap => |hid| {
            if (!config_mod.isEnabled(ctx.config, .heap_use_after_free)) return;
            const st = state.heaps.get(hid) orelse return;
            if (st.state == .dead) {
                try reportWithNote(ctx, "heap-use-after-free", pos, end_pos, .@"error", "returning a heap pointer after free", .{}, if (st.killed_at) |ks|
                    .{ .site = ks, .label = "value freed here" }
                else
                    null);
            }
        },
        else => {},
    }
}

fn transferFieldAssign(
    ctx: Ctx,
    state: *AbstractState,
    a: @TypeOf(@as(StmtKind, undefined).field_assign),
    pos: cfg.SrcPos,
) !void {
    const origin = try originOfInit(ctx, state, a.rhs_kind, pos);
    const key: state_mod.FieldKey = .{ .parent = a.parent, .name = a.name };
    try state.fields.putContext(ctx.gpa, key, origin, .{});

    // "Object owns its own arena" pattern: when the arena ITSELF is
    // stored into a field of a HEAP-allocated struct (`ptr.*.arena =
    // arena` where ptr is heap/arena-allocated), the arena is moved
    // into the heap struct.  Its lifetime is now tied to the struct,
    // not the stack frame — mark it heap-allocated so the arena-escape
    // check knows the arena won't die with the frame.
    // Only applies when the parent local is heap/arena-origin; when the
    // parent is a plain stack local (`var ma = W{ .inner = arena }`),
    // the arena stays stack-bound and the escape check still fires.
    blk: {
        const aid = switch (origin) {
            .arena_borrow => |id| id,
            else => break :blk,
        };
        // Only suppress when the parent is a heap/arena-allocated
        // POINTER local — i.e. the struct was allocated on the heap.
        // Stack locals like `var ma = W{ .inner = arena }` have
        // is_pointer=false; a pointer to a heap allocation has
        // is_pointer=true.  Both may have .arena_borrow origin when
        // the arena is wrapped; the pointer check distinguishes them.
        if (!ctx.locals[@intFromEnum(a.parent)].is_pointer) break :blk;
        const parent_origin = state.locals.get(a.parent) orelse break :blk;
        switch (parent_origin) {
            .heap, .arena, .arena_borrow => {},
            else => break :blk,
        }
        if (state.arenas.getPtr(aid)) |st| {
            if (!st.is_heap_allocated) st.is_heap_allocated = true;
        }
    }

    // Field assignment initializes the parent (partially).  Clear
    // the parent's .undef so `var x = undefined; x.field = val;
    // return x;` doesn't fire spuriously — common Zig idiom.
    if (state.locals.get(a.parent)) |parent_origin| {
        if (parent_origin == .undef) {
            try state.locals.put(ctx.gpa, a.parent, .plain);
        }
    }
}

fn transferFieldHeapFree(
    ctx: Ctx,
    state: *AbstractState,
    f: @TypeOf(@as(StmtKind, undefined).field_heap_free),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    const key: state_mod.FieldKey = .{ .parent = f.parent, .name = f.name };
    if (state.fields.getContext(key, .{})) |origin| {
        switch (origin) {
            .heap => |hid| {
                const st = state.heaps.get(hid) orelse return;
                if (st.state == .dead) {
                    if (config_mod.isEnabled(ctx.config, .heap_double_free)) {
                        const parent_name = ctx.locals[@intFromEnum(f.parent)].name;
                        try reportWithNote(ctx, "heap-double-free", pos, end_pos, .@"error", "double-free of `{s}{s}{s}`", .{ parent_name, pathSep(f.name), f.name }, if (st.killed_at) |ks|
                            .{ .site = ks, .label = "first freed here" }
                        else
                            null);
                    }
                    return;
                }
                try state.heaps.put(ctx.gpa, hid, .{
                    .state = .dead,
                    .killed_at = killSiteOf(pos, end_pos),
                });
                return;
            },
            else => {},
        }
    }
    // Inter-procedural fallback: field had no prior tracked alloc
    // (e.g. it was allocated by the caller before passing `*T` in).
    // Use the cfg-minted fallback_hid to record the free so later
    // .field_use reads on the same field flag UAF.
    try state.heaps.put(ctx.gpa, f.fallback_hid, .{
        .state = .dead,
        .killed_at = killSiteOf(pos, end_pos),
        .is_inter_procedural = true,
    });
    try state.fields.putContext(ctx.gpa, key, .{ .heap = f.fallback_hid }, .{});
}

fn transferFieldUse(
    ctx: Ctx,
    state: *AbstractState,
    u: @TypeOf(@as(StmtKind, undefined).field_use),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    // Reading a field dereferences its owner, whatever origin the
    // FIELD itself carries.  A dead heap owner invalidates the read,
    // and an owner that is still `undefined` has no bytes to read at
    // all — `var x: T = undefined; use(x.field)` reads uninitialized
    // memory whatever the field's own record says, and the field has
    // no record of its own until something assigns it.
    //
    // This check is on the owner's own state, never on how that state
    // was reached: a regular alloc-and-free in this function and an
    // inter-procedural `@takes` both leave the owner dead, and both
    // invalidate the read.  `ArenaState.is_inter_procedural` is part of
    // the partition identity (see `sameLiveness`), not a filter here.
    //
    // OWNER WINS OVER FIELD.  The two prongs below and the field
    // arms after them describe one read, and `Seen` keys on
    // (rule_id, byte) — a second rule at the same byte is a second
    // finding, not a duplicate.  So an owner that reports takes the
    // statement: it names the whole access and needs no field context
    // to justify itself.  `transferRetValueChecks` settles the same
    // precedence for the same reason, by folding the gate into the
    // branch condition rather than guarding the whole function.
    //
    // "TOOK THE STATEMENT" MEANS REPORTED — never "the owner prong ran".
    // An owner whose own rule is off has said nothing about this byte,
    // and returning on its behalf would hand one `--disable=<unrelated
    // rule>` the field-origin analysis too: a `.heap` payload whose
    // allocation is already dead, or a `.stack`/`.arena` borrow whose
    // owner is, stay use-after-frees whichever way the OUTER local was
    // never initialised.  Those findings carry their own rule ids and
    // answer to their own gates, so a gate that is off here must not
    // silence them.  (`.undef` parent + `field_heap_free` fallback +
    // `field_use` reaches exactly this: the fallback records a dead
    // field origin WITHOUT touching `state.locals[parent]`, so the two
    // coexist.)
    if (state.locals.get(u.parent)) |parent_origin| switch (parent_origin) {
        .undef => {
            if (config_mod.isEnabled(ctx.config, .use_undefined)) {
                const owner_name = ctx.locals[@intFromEnum(u.parent)].name;
                try report(ctx, "use-undefined", pos, end_pos, .@"error", "use of `{s}{s}{s}` while `{s}` is still `undefined`", .{ owner_name, pathSep(u.name), u.name, owner_name });
                return;
            }
        },
        .heap => |hid| {
            const st = state.heaps.get(hid);
            if (st) |s| if (s.state == .dead) {
                if (config_mod.isEnabled(ctx.config, .heap_use_after_free)) {
                    const parent_name = ctx.locals[@intFromEnum(u.parent)].name;
                    try reportWithNote(ctx, "heap-use-after-free", pos, end_pos, .@"error", "use of `{s}` after free", .{parent_name}, if (s.killed_at) |ks|
                        .{ .site = ks, .label = "value freed here" }
                    else
                        null);
                    return;
                }
            };
        },
        else => {},
    };
    const key: state_mod.FieldKey = .{ .parent = u.parent, .name = u.name };
    const origin = state.fields.getContext(key, .{}) orelse return;
    const parent_name = ctx.locals[@intFromEnum(u.parent)].name;
    switch (origin) {
        .arena, .arena_borrow => |aid| {
            if (!config_mod.isEnabled(ctx.config, .arena_use_after_kill)) return;
            const st = state.arenas.get(aid) orelse return;
            if (st.state == .dead) {
                try reportWithNote(ctx, "arena-use-after-kill", pos, end_pos, .@"error", "`{s}{s}{s}` borrows from an arena that was deinit'd", .{ parent_name, pathSep(u.name), u.name }, if (st.killed_at) |ks|
                    .{ .site = ks, .label = "arena deinit'd here" }
                else
                    null);
            }
        },
        .heap => |hid| {
            if (!config_mod.isEnabled(ctx.config, .heap_use_after_free)) return;
            const st = state.heaps.get(hid) orelse return;
            if (st.state == .dead) {
                try reportWithNote(ctx, "heap-use-after-free", pos, end_pos, .@"error", "use of `{s}{s}{s}` after free", .{ parent_name, pathSep(u.name), u.name }, if (st.killed_at) |ks|
                    .{ .site = ks, .label = "value freed here" }
                else
                    null);
            }
        },
        .undef => {
            if (!config_mod.isEnabled(ctx.config, .use_undefined)) return;
            try report(ctx, "use-undefined", pos, end_pos, .@"error", "use of `{s}{s}{s}` while still `undefined`", .{ parent_name, pathSep(u.name), u.name });
        },
        .stack => |owner_id| {
            // Field borrows from a stack owner — mirrors the .stack
            // arm in checkOriginAlive.  When the field carries an
            // owner-borrow origin (set via classifyExpr's @borrowed-
            // field route, or via struct-literal unpack of a
            // borrowed-field read), a kill of the owner invalidates
            // this read.
            if (!config_mod.isEnabled(ctx.config, .heap_use_after_free)) return;
            const owner_origin = state.locals.get(owner_id) orelse return;
            switch (owner_origin) {
                .heap => |hid| {
                    const st = state.heaps.get(hid) orelse return;
                    if (st.state == .dead) {
                        try reportWithNote(ctx, "heap-use-after-free", pos, end_pos, .@"error", "use of `{s}{s}{s}` (borrow from `{s}`) after free", .{ parent_name, pathSep(u.name), u.name, ctx.locals[@intFromEnum(owner_id)].name }, if (st.killed_at) |ks|
                            .{ .site = ks, .label = "value freed here" }
                        else
                            null);
                    }
                },
                else => {},
            }
        },
        else => {},
    }
}

/// Check direct stack addresses and the current origins of aggregate aliases.
fn transferCompositeEscape(
    ctx: Ctx,
    state: *AbstractState,
    c: @TypeOf(@as(StmtKind, undefined).composite_escape),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    // The producer is another module, so its `ExprKind` set is not this
    // function's to rely on: a variant added there has to degrade to a
    // documented no-op here, never to a build-mode-dependent panic in
    // the middle of analyzing someone's file.
    //
    // The two borrow shapes are the ones this check models, and the
    // narrowing is not a no-op by construction: `.borrowed_from` and
    // `.composite_borrow` resolve to their SOURCE local, so a `.stack`
    // source would reach the report below and the loop would widen,
    // not hold.  What the switch guarantees is narrower than "silence"
    // and stronger: a shape nobody here has argued about reports
    // nothing, and widening it again needs that shape's own
    // reachability argument rather than origin resolution alone.
    switch (c) {
        .stack_ref, .copy_of => {},
        else => return,
    }
    if (!config_mod.isEnabled(ctx.config, .stack_escape)) return;
    const origin = try originOfInit(ctx, state, c, pos);
    if (origin != .stack) return;
    const name = ctx.locals[@intFromEnum(origin.stack)].name;
    try report(ctx, "stack-escape", pos, end_pos, .@"error", "returning a value that holds a pointer to function-local stack variable `{s}` (escapes its frame)", .{name});
}

/// Write-through-pointer escape check.  `out.* = X` (or
/// `out.field = X` where `out` is `*T`) makes whatever `X`'s
/// origin is reachable from caller-owned storage.  If that origin
/// is a function-local arena / stack reference, the lifetime
/// ends with this frame — surface the same arena-escape /
/// stack-escape diagnostics that fire at `return`.
///
/// Heap origins are left alone here: heap allocations are
/// owned-and-transferable, so writing one to caller-storage is
/// legitimate (the canonical out-param return-allocator pattern).
/// The case where a heap allocation is freed via `defer` BEFORE
/// the function returns — and the write therefore leaves a
/// dangling caller pointer — needs a deferred check at fn exit
/// that this pass doesn't do yet.
fn transferOutParamWrite(
    ctx: Ctx,
    state: *AbstractState,
    w: @TypeOf(@as(StmtKind, undefined).out_param_write),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    const origin = try originOfInit(ctx, state, w.value_kind, pos);
    const out_name = ctx.locals[@intFromEnum(w.out)].name;
    switch (origin) {
        .stack => |src_local| {
            // `out.field = &local` / `out.* = &local` — unambiguous
            // stack-frame escape regardless of out's pointee type.
            if (!config_mod.isEnabled(ctx.config, .stack_escape)) return;
            // Scope-bounded install: when `out` itself is a HEAP
            // LOCAL (allocated in this fn via `allocator.create(T)`
            // / `bun.new(T)` etc.) — as opposed to a parameter
            // pointing at caller-owned storage — both `out` and the
            // borrowed local share this frame's lifecycle.  Either
            // `out` is destroyed via defer in the same fn (in which
            // case the borrowed pointee never outlives the borrower)
            // OR the heap descriptor leaks, which is a separate
            // class of bug other rules catch.  Either way, firing
            // stack-escape here is wrong: the borrow IS the
            // intended install protocol, scoped to this fn.
            const out_info = ctx.locals[@intFromEnum(w.out)];
            if (out_info.init_hint == .heap_local) return;
            // Stack-derived pointer: when `out` itself was initialized
            // as `&local.field` (a borrow into this fn's stack frame),
            // both `out` and the value written through it are scoped
            // to this fn.  Writing `&src` through a stack-field pointer
            // is an in-frame self-referential install, not an escape.
            // Canonical: `const packet = &request.packet; packet.user_data = &request;`
            if (state.locals.get(w.out)) |out_origin| {
                if (out_origin == .stack) return;
            }
            const src_name = ctx.locals[@intFromEnum(src_local)].name;
            try report(ctx, "stack-escape", pos, end_pos, .@"error", "writing a pointer to function-local stack variable `{s}` through `{s}` (escapes its frame)", .{ src_name, out_name });
        },
        .heap => |hid| {
            // Record the write for the deferred check at fn exit
            // (transferRet).  At write time the heap is live, so
            // it's not yet an escape — but if a defer subsequently
            // frees it, the caller's pointee dangles on return.
            // Last-write-wins per out-param.
            try state.out_param_writes.put(ctx.gpa, w.out, hid);
        },
        .plain, .undef => {
            // Last-write-wins: a primitive / null / undefined
            // sentinel write through `this.<field>` REPLACES any
            // prior heap-owning value we'd tracked for this
            // out-param.  Without removing it, an err-path
            // `this.statement = null; destroy(stmt); deref(this);
            // return err;` keeps the stale entry and the
            // deferred check fires "heap freed before return" on
            // a slot that's already been nulled out.
            _ = state.out_param_writes.swapRemove(w.out);
        },
        .arena, .arena_borrow => |aid| {
            // Arena-shaped value written to caller storage.  Only a
            // stack-allocated arena (`var a = ArenaAllocator.init(...)`)
            // dies with the frame — heap-allocated arenas
            // (`var a = gpa.create(ArenaAllocator)`) carry their
            // descriptor on the heap and survive the function.
            // Tracked via `ArenaState.is_heap_allocated`.
            if (!config_mod.isEnabled(ctx.config, .arena_escape)) return;
            const st = state.arenas.get(aid) orelse return;
            if (st.is_heap_allocated) return;
            // Installation, not escape: `this.<field> = ArenaAllocator.init(...)`
            // moves the freshly-created arena INTO the caller-visible
            // storage.  The arena's lifetime extends to the storage's
            // lifetime — `this` lives at least as long as the fn, so
            // installing an arena into `this.<field>` is the canonical
            // setup-time pattern, not an escape.  The bug shape is
            // `arena.allocator().alloc(...)` written through — a BORROW
            // FROM the arena leaving the frame — which arrives here
            // with value_kind != .arena_init.
            if (w.value_kind == .arena_init) return;
            try report(ctx, "arena-escape", pos, end_pos, .@"error", "writing a value borrowed from a function-local arena through `{s}` (escapes its lifetime)", .{out_name});
        },
        else => {},
    }
}

fn transferUse(
    ctx: Ctx,
    state: *AbstractState,
    u: @TypeOf(@as(StmtKind, undefined).use),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    const origin = state.locals.get(u.local) orelse return;
    // Method-call on a still-undef local: not a read of garbage,
    // it's the conventional init pattern (`var x: T = undefined;
    // x.decodeInternal(...);`).  Treat as a write that clears
    // .undef → .plain, suppressing the spurious use_undefined.
    // For .heap / .arena / .stack origins the call IS a real
    // use — fall through to the normal liveness check.
    if (u.from_method_call and origin == .undef) {
        try state.locals.put(ctx.gpa, u.local, .plain);
        return;
    }
    try checkOriginAlive(ctx, state, origin, pos, end_pos, ctx.locals[@intFromEnum(u.local)].name);
}

fn transferGap(
    state: *AbstractState,
    g: @TypeOf(@as(StmtKind, undefined).lowering_gap),
) void {
    // A gap the builder marked `may_assign_locals = false` is a
    // statement that provably CANNOT write a local: `call-untracked`
    // carries no pointer argument, and `assign-target`'s `arr[i] = X`
    // writes one ELEMENT, not the array.  Collapsing origins for it
    // erases facts the statement never touched, and the flag is the
    // only thing that distinguishes the two claims — reading past it
    // made every gap a claim about locals no gap can support.
    if (!g.may_assign_locals) return;
    state.facts.forgetAllLocals();
    // Conservative: collapse .undef → .plain since an unknown stmt
    // may have written through a passed pointer to initialize the
    // local.  But PRESERVE resource origins (.heap, .arena,
    // .arena_borrow, .stack_ref) — an unknown call can't free a
    // tracked allocation or kill an arena unless it matches a free /
    // arena-kill pattern (in which case cfg lowers it as the proper
    // op, not a gap).  Without this preservation, a single
    // `foo(args)` between `alloc(args)` and `free(args)` wipes the
    // .heap origin and defeats double-free / use-after-free tracking
    // for the rest of the function.
    var it = state.locals.iterator();
    while (it.next()) |entry| {
        if (entry.value_ptr.* == .undef) entry.value_ptr.* = .plain;
    }
}

/// Map an ExprKind (RHS classification) to the Origin it produces.
/// Emits a fresh ArenaId for arena_init.  copy_of follows through to
/// the source local's current origin.
fn originOfInit(
    ctx: Ctx,
    state: *const AbstractState,
    kind: ExprKind,
    pos: cfg.SrcPos,
) !Origin {
    _ = pos;
    return switch (kind) {
        .plain, .boolean => .plain,
        .owned => .plain,
        .arena_init => |info| blk: {
            // OVERWRITE to .live on every visit — the decl represents
            // a fresh resource at this call site.  Inside a loop,
            // back-edges propagate dead state from a prior iteration's
            // free back to the body's start; without this reset, the
            // fresh allocation would inherit that stale dead state and
            // spurious UAF would fire on later uses.
            const mut_state: *AbstractState = @constCast(state);
            try mut_state.arenas.put(ctx.gpa, info.id, .{
                .state = .live,
                .is_heap_allocated = info.is_heap_allocated,
            });
            break :blk .{ .arena = info.id };
        },
        .stack_ref => |src_local| .{ .stack = src_local },
        .composite_borrow => |src_local| state.locals.get(src_local) orelse .plain,
        .heap_alloc => |info| blk: {
            const mut_state: *AbstractState = @constCast(state);
            try mut_state.heaps.put(ctx.gpa, info.id, .{
                .state = .live,
                .allocator_local = info.allocator_local,
            });
            break :blk .{ .heap = info.id };
        },
        .undef => .undef,
        .borrowed_from => |src_local| state.locals.get(src_local) orelse .plain,
        .copy_of => |src_local| blk: {
            const src_origin = state.locals.get(src_local) orelse break :blk .plain;
            // A copy / view of an .arena (the arena itself) yields a
            // BORROW, not a second reference to the arena identity.
            // Without this, `dep.deinit()` on a derived list would
            // kill the underlying arena.
            if (src_origin == .arena) break :blk .{ .arena_borrow = src_origin.arena };
            break :blk src_origin;
        },
        .field_copy_of => |fc| blk: {
            const key: state_mod.FieldKey = .{ .parent = fc.parent, .name = fc.name };
            break :blk state.fields.getContext(key, .{}) orelse .plain;
        },
        .unknown => .plain,
    };
}

/// Verify that the named origin is still live at the use point.
fn checkOriginAlive(
    ctx: Ctx,
    state: *const AbstractState,
    origin: Origin,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
    local_name: []const u8,
) !void {
    switch (origin) {
        .arena, .arena_borrow => |aid| {
            if (!config_mod.isEnabled(ctx.config, .arena_use_after_kill)) return;
            const st = state.arenas.get(aid) orelse return;
            if (st.state == .dead) {
                try reportWithNote(ctx, "arena-use-after-kill", pos, end_pos, .@"error", "`{s}` borrows from an arena that was deinit'd", .{local_name}, if (st.killed_at) |ks|
                    .{ .site = ks, .label = "arena deinit'd here" }
                else
                    null);
            }
        },
        .heap => |hid| {
            if (!config_mod.isEnabled(ctx.config, .heap_use_after_free)) return;
            const st = state.heaps.get(hid) orelse return;
            if (st.state == .dead) {
                try reportWithNote(ctx, "heap-use-after-free", pos, end_pos, .@"error", "use of `{s}` after free", .{local_name}, if (st.killed_at) |ks|
                    .{ .site = ks, .label = "value freed here" }
                else
                    null);
            }
        },
        .undef => {
            if (!config_mod.isEnabled(ctx.config, .use_undefined)) return;
            try report(ctx, "use-undefined", pos, end_pos, .@"error", "use of `{s}` while still `undefined`", .{local_name});
        },
        .stack => |owner_id| {
            // Stack-borrow liveness — the borrow inherits the owner
            // local's death.  Today this fires when `owner` was the
            // target of an inter-procedural @takes-ownership call
            // (transferHeapFree's fallback path rewrites
            // state.locals[owner] to .heap(fake_dead)), so a borrow
            // taken via `&owner.field` then used after `owner.die()`
            // surfaces as UAF on the borrow itself.  Stack-frame
            // death across return is still handled by transferRet.
            if (!config_mod.isEnabled(ctx.config, .heap_use_after_free)) return;
            const owner_origin = state.locals.get(owner_id) orelse return;
            switch (owner_origin) {
                .heap => |hid| {
                    const st = state.heaps.get(hid) orelse return;
                    if (st.state == .dead) {
                        try reportWithNote(ctx, "heap-use-after-free", pos, end_pos, .@"error", "use of `{s}` (borrow from `{s}`) after free", .{ local_name, ctx.locals[@intFromEnum(owner_id)].name }, if (st.killed_at) |ks|
                            .{ .site = ks, .label = "value freed here" }
                        else
                            null);
                    }
                },
                else => {},
            }
        },
        else => {},
    }
}

fn report(
    ctx: Ctx,
    comptime rule_id: []const u8,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
    severity: Severity,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    try reportWithNote(ctx, rule_id, pos, end_pos, severity, fmt, args, null);
}

fn reportWithNote(
    ctx: Ctx,
    comptime rule_id: []const u8,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
    severity: Severity,
    comptime fmt: []const u8,
    args: anytype,
    kill_site: ?struct { site: state_mod.KillSite, label: []const u8 },
) !void {
    if (!ctx.report_enabled) return;
    // One source operation can be reached through several cleanup paths,
    // and the solver replays the block holding it once per path state.
    // The memo answers "has this already been said" without touching
    // the finding list or the strings below; a new identity costs one
    // insert, an old one one lookup.  The FIRST report still wins, so
    // the finding that lands — and the note it carries — is the one the
    // scan over `ctx.problems` used to keep.
    if (!try ctx.seen.record(ctx.gpa, rule_id, pos.byte)) return;
    const msg = try std.fmt.allocPrint(ctx.gpa, fmt, args);
    errdefer ctx.gpa.free(msg);
    const real_end: cfg.SrcPos = if (end_pos.byte > pos.byte)
        end_pos
    else
        .{ .line = pos.line, .column = pos.column + 1, .byte = pos.byte + 1 };
    var notes: []problem_mod.Note = &.{};
    if (kill_site) |ks| {
        const label = try ctx.gpa.dupe(u8, ks.label);
        errdefer ctx.gpa.free(label);
        notes = try ctx.gpa.alloc(problem_mod.Note, 1);
        notes[0] = .{
            .start = .{ .line = ks.site.line, .column = ks.site.column, .byte = ks.site.byte },
            .end = .{ .line = ks.site.end_line, .column = ks.site.end_column, .byte = ks.site.end_byte },
            .label = label,
        };
    }
    errdefer {
        for (notes) |note| ctx.gpa.free(note.label);
        ctx.gpa.free(notes);
    }
    try ctx.problems.append(ctx.gpa, .{
        .rule_id = rule_id,
        .severity = severity,
        .start = .{ .line = pos.line, .column = pos.column, .byte = pos.byte },
        .end = .{ .line = real_end.line, .column = real_end.column, .byte = real_end.byte },
        .message = msg,
        .notes = notes,
    });
}

// ── Tests ──────────────────────────────────────────────────
//
// These unit tests exercise each statement transfer's state-mutation contract
// in isolation. They localize failures to a single transfer.

const testing = std.testing;
const LocalInfoSlice = []const LocalInfo;

fn pos0() cfg.SrcPos {
    return .{ .line = 1, .column = 1, .byte = 0 };
}
fn pos1() cfg.SrcPos {
    return .{ .line = 1, .column = 2, .byte = 1 };
}

const LId = state_mod.LocalId;
const AId = state_mod.ArenaId;
const HId = state_mod.HeapId;

fn mkLocals(comptime names: []const []const u8) LocalInfoSlice {
    comptime var infos: [names.len]LocalInfo = undefined;
    inline for (names, 0..) |n, i| {
        infos[i] = .{ .name = n, .decl_pos = .{ .line = 1, .column = 1, .byte = 0 } };
    }
    const out = infos;
    return &out;
}

fn freeProblems(gpa: std.mem.Allocator, list: *std.ArrayListUnmanaged(Problem)) void {
    for (list.items) |*p| p.deinit(gpa);
    list.deinit(gpa);
}

/// Every default invariant EXCEPT `use_undefined` — the CLI's
/// `--disable=use_undefined`, spelled out.  Derived from
/// `all_invariants` instead of hand-listed on purpose: a fixture that
/// enabled only the handful of rules it cared about would pass even if
/// the gate under test were ignored, because the gate being open and
/// the rule being listed are the same fact from there.
const enabled_without_use_undefined: [config_mod.all_invariants.len - 1]config_mod.Invariant = blk: {
    var buf: [config_mod.all_invariants.len - 1]config_mod.Invariant = undefined;
    var n: usize = 0;
    for (config_mod.all_invariants) |inv| {
        if (inv == .use_undefined) continue;
        buf[n] = inv;
        n += 1;
    }
    break :blk buf;
};

test "transfer: a cloned guard still prunes a contradictory use" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"saved"}), .problems = &problems, .seen = &seen, .path = "test" };
    const saved: LId = @enumFromInt(0);
    const guard: state_mod.GuardId = @enumFromInt(0);
    try transfer(ctx, &state, .{ .kind = .{ .decl = .{ .local = saved, .init_kind = .{ .heap_alloc = .{ .id = @enumFromInt(0) } } } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &state, .{ .kind = .{ .heap_free = .{ .freed_local = saved, .fallback_hid = @enumFromInt(0) } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &state, .{ .kind = .{ .guard_fact = .{ .guard = guard, .holds = true } }, .pos = pos0(), .end_pos = pos1() });

    var contradicted = try state.clone(gpa);
    defer contradicted.deinit(gpa);
    try transfer(ctx, &contradicted, .{ .kind = .{ .guard_fact = .{ .guard = guard, .holds = false } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &contradicted, .{ .kind = .{ .use = .{ .local = saved } }, .pos = pos0(), .end_pos = pos1() });
    try testing.expect(!contradicted.feasible);
    try testing.expectEqual(@as(usize, 0), problems.items.len);

    var reachable = try state.clone(gpa);
    defer reachable.deinit(gpa);
    try transfer(ctx, &reachable, .{ .kind = .{ .guard_fact = .{ .guard = guard, .holds = true } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &reachable, .{ .kind = .{ .use = .{ .local = saved } }, .pos = pos0(), .end_pos = pos1() });
    try testing.expect(reachable.feasible);
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("heap-use-after-free", problems.items[0].rule_id);
}

test "transfer: joining boolean alternatives does not prune a reachable use" {
    const gpa = testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{ "flag", "saved" }), .problems = &problems, .seen = &seen, .path = "test" };
    const flag: LId = @enumFromInt(0);
    const saved: LId = @enumFromInt(1);
    try transfer(ctx, &lhs, .{ .kind = .{ .decl = .{ .local = flag, .init_kind = .{ .boolean = .{ .constant = true } } } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &lhs, .{ .kind = .{ .decl = .{ .local = saved, .init_kind = .undef } }, .pos = pos0(), .end_pos = pos1() });
    var rhs = try lhs.clone(gpa);
    defer rhs.deinit(gpa);
    try transfer(ctx, &rhs, .{ .kind = .{ .assign = .{ .target = flag, .rhs_kind = .{ .boolean = .{ .constant = false } } } }, .pos = pos0(), .end_pos = pos1() });
    try testing.expect(lhs.canMerge(&rhs));
    _ = try state_mod.join(&lhs, &rhs, gpa);

    try transfer(ctx, &lhs, .{ .kind = .{ .assume = .{ .not_local = flag } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &lhs, .{ .kind = .{ .use = .{ .local = saved } }, .pos = pos0(), .end_pos = pos1() });
    try testing.expect(lhs.feasible);
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
}

test "transfer: local writes invalidate predicates before a later use" {
    const gpa = testing.allocator;
    const flag: LId = @enumFromInt(0);
    const saved: LId = @enumFromInt(1);
    const writes = [_]StmtKind{
        .{ .decl = .{ .local = flag, .init_kind = .unknown } },
        .{ .assign = .{ .target = flag, .rhs_kind = .unknown } },
        .{ .pointer_write = .{ .target = flag } },
        .{ .reset_capture = .{ .local = flag } },
        .{ .lowering_gap = .{ .note = "unclassified write", .may_assign_locals = true } },
    };
    for (writes) |write| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{ "flag", "saved" }), .problems = &problems, .seen = &seen, .path = "test" };
        try transfer(ctx, &state, .{ .kind = .{ .decl = .{ .local = flag, .init_kind = .{ .boolean = .{ .constant = true } } } }, .pos = pos0(), .end_pos = pos1() });
        try transfer(ctx, &state, .{ .kind = .{ .decl = .{ .local = saved, .init_kind = .{ .heap_alloc = .{ .id = @enumFromInt(0) } } } }, .pos = pos0(), .end_pos = pos1() });
        try transfer(ctx, &state, .{ .kind = .{ .heap_free = .{ .freed_local = saved, .fallback_hid = @enumFromInt(0) } }, .pos = pos0(), .end_pos = pos1() });
        try transfer(ctx, &state, .{ .kind = write, .pos = pos0(), .end_pos = pos1() });
        try transfer(ctx, &state, .{ .kind = .{ .assume = .{ .not_local = flag } }, .pos = pos0(), .end_pos = pos1() });
        try transfer(ctx, &state, .{ .kind = .{ .use = .{ .local = saved } }, .pos = pos0(), .end_pos = pos1() });
        try testing.expect(state.feasible);
        try testing.expectEqual(@as(usize, 1), problems.items.len);
        try testing.expectEqualStrings("heap-use-after-free", problems.items[0].rule_id);
    }
}

test "transferDecl: heap_alloc binds local to .heap and marks heap live" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    const locals = mkLocals(&.{"x"});
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = locals, .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    const hid: HId = @enumFromInt(7);
    try transferDecl(ctx, &state, .{
        .local = x,
        .init_kind = .{ .heap_alloc = .{ .id = hid } },
    }, pos0());

    const origin = state.locals.get(x).?;
    try testing.expect(origin == .heap);
    try testing.expectEqual(hid, origin.heap);
    try testing.expect(state.heaps.get(hid).?.state == .live);
}

test "transferDecl: undef init produces .undef origin" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"x"}), .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    try transferDecl(ctx, &state, .{ .local = x, .init_kind = .undef }, pos0());
    try testing.expect(state.locals.get(x).? == .undef);
}

test "transferDecl: stack_ref produces .stack" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{ "x", "y" }), .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    const y: LId = @enumFromInt(1);
    try transferDecl(ctx, &state, .{ .local = y, .init_kind = .{ .stack_ref = x } }, pos0());
    const o = state.locals.get(y).?;
    try testing.expect(o == .stack);
    try testing.expectEqual(x, o.stack);
}

test "transferAssign: overwrites prior origin" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"x"}), .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    try state.locals.put(gpa, x, .undef);
    try transferAssign(ctx, &state, .{ .target = x, .rhs_kind = .plain }, pos0());
    try testing.expect(state.locals.get(x).? == .plain);
}

test "transferArenaKill: marks arena dead with kill site" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"a"}), .problems = &problems, .seen = &seen, .path = "test" };

    const a: LId = @enumFromInt(0);
    const aid: AId = @enumFromInt(3);
    try state.arenas.put(gpa, aid, .{ .state = .live });
    try state.locals.put(gpa, a, .{ .arena = aid });

    try transferArenaKill(ctx, &state, .{ .arena_local = a }, pos0(), pos1());

    const st = state.arenas.get(aid).?;
    try testing.expect(st.state == .dead);
    try testing.expect(st.killed_at != null);
}

test "transferHeapFree: live heap marked dead, no problem" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{ "p", "gpa_l" }), .problems = &problems, .seen = &seen, .path = "test" };

    const p: LId = @enumFromInt(0);
    const hid: HId = @enumFromInt(1);
    try state.heaps.put(gpa, hid, .{ .state = .live });
    try state.locals.put(gpa, p, .{ .heap = hid });

    try transferHeapFree(ctx, &state, .{
        .freed_local = p,
        .fallback_hid = @enumFromInt(99),
    }, pos0(), pos1());

    try testing.expect(state.heaps.get(hid).?.state == .dead);
    try testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "transferHeapFree: second free fires heap-double-free" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"p"}), .problems = &problems, .seen = &seen, .path = "test" };

    const p: LId = @enumFromInt(0);
    const hid: HId = @enumFromInt(2);
    try state.heaps.put(gpa, hid, .{ .state = .dead });
    try state.locals.put(gpa, p, .{ .heap = hid });

    try transferHeapFree(ctx, &state, .{
        .freed_local = p,
        .fallback_hid = @enumFromInt(99),
    }, pos0(), pos1());

    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("heap-double-free", problems.items[0].rule_id);
}

test "transferHeapFree: allocator mismatch fires" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{ "p", "gpa_a", "gpa_b" }), .problems = &problems, .seen = &seen, .path = "test" };

    const p: LId = @enumFromInt(0);
    const ga: LId = @enumFromInt(1);
    const gb: LId = @enumFromInt(2);
    const hid: HId = @enumFromInt(3);
    try state.heaps.put(gpa, hid, .{ .state = .live, .allocator_local = ga });
    try state.locals.put(gpa, p, .{ .heap = hid });

    try transferHeapFree(ctx, &state, .{
        .freed_local = p,
        .fallback_hid = @enumFromInt(99),
        .allocator_local = gb,
    }, pos0(), pos1());

    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("allocator-mismatch", problems.items[0].rule_id);
}

test "transferHeapFree: inter-procedural fallback records dead heap" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"p"}), .problems = &problems, .seen = &seen, .path = "test" };

    const p: LId = @enumFromInt(0);
    const fb: HId = @enumFromInt(42);
    try state.locals.put(gpa, p, .plain);

    try transferHeapFree(ctx, &state, .{
        .freed_local = p,
        .fallback_hid = fb,
    }, pos0(), pos1());

    const st = state.heaps.get(fb).?;
    try testing.expect(st.state == .dead);
    try testing.expect(st.is_inter_procedural);
    try testing.expect(state.locals.get(p).? == .heap);
}

test "transferUse: live heap origin produces no problem" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"x"}), .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    const hid: HId = @enumFromInt(1);
    try state.heaps.put(gpa, hid, .{ .state = .live });
    try state.locals.put(gpa, x, .{ .heap = hid });

    try transferUse(ctx, &state, .{ .local = x }, pos0(), pos1());
    try testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "transferUse: dead heap origin fires heap-use-after-free" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"x"}), .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    const hid: HId = @enumFromInt(1);
    try state.heaps.put(gpa, hid, .{ .state = .dead });
    try state.locals.put(gpa, x, .{ .heap = hid });

    try transferUse(ctx, &state, .{ .local = x }, pos0(), pos1());
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("heap-use-after-free", problems.items[0].rule_id);
}

test "transferUse: method-call on .undef clears to .plain (no fire)" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"x"}), .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    try state.locals.put(gpa, x, .undef);

    try transferUse(ctx, &state, .{ .local = x, .from_method_call = true }, pos0(), pos1());

    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try testing.expect(state.locals.get(x).? == .plain);
}

test "transferUse: bare read of .undef fires use-undefined" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"x"}), .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    try state.locals.put(gpa, x, .undef);

    try transferUse(ctx, &state, .{ .local = x }, pos0(), pos1());

    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
}

test "transferGap: collapses .undef → .plain, preserves resource origins" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);

    const u: LId = @enumFromInt(0);
    const h: LId = @enumFromInt(1);
    const a: LId = @enumFromInt(2);
    try state.locals.put(gpa, u, .undef);
    try state.locals.put(gpa, h, .{ .heap = @enumFromInt(1) });
    try state.locals.put(gpa, a, .{ .arena = @enumFromInt(1) });

    transferGap(&state, .{ .note = "test" });

    try testing.expect(state.locals.get(u).? == .plain);
    try testing.expect(state.locals.get(h).? == .heap);
    try testing.expect(state.locals.get(a).? == .arena);
}

test "transferRet: returning .arena from borrowed-return-type fires arena-escape" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"x"}), .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    const aid: AId = @enumFromInt(1);
    // arena must be registered in state.arenas — the escape check
    // only fires when the arena id is tracked (function-local arenas).
    try state.arenas.put(gpa, aid, .{ .state = .live });
    // copy_of of an .arena local yields .arena_borrow per originOfInit's
    // own contract; arena-escape covers both .arena and .arena_borrow.
    try state.locals.put(gpa, x, .{ .arena = aid });

    try transferRet(ctx, &state, .{
        .value_kind = .{ .copy_of = x },
        .is_borrowed_return_type = true,
    }, pos0(), pos1());

    try testing.expect(problems.items.len >= 1);
    try testing.expectEqualStrings("arena-escape", problems.items[0].rule_id);
}

test "transferRet: returning .stack fires stack-escape" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{ "y", "buf" }), .problems = &problems, .seen = &seen, .path = "test" };

    const y: LId = @enumFromInt(0);
    const buf: LId = @enumFromInt(1);
    try state.locals.put(gpa, y, .{ .stack = buf });

    try transferRet(ctx, &state, .{
        .value_kind = .{ .copy_of = y },
        .is_borrowed_return_type = true,
    }, pos0(), pos1());

    try testing.expect(problems.items.len >= 1);
    try testing.expectEqualStrings("stack-escape", problems.items[0].rule_id);
}

test "transferFieldHeapFree: tracks field origin as dead" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"obj"}), .problems = &problems, .seen = &seen, .path = "test" };

    const obj: LId = @enumFromInt(0);
    const hid: HId = @enumFromInt(5);
    try state.heaps.put(gpa, hid, .{ .state = .live });
    try state.fields.putContext(gpa, .{ .parent = obj, .name = "buf" }, .{ .heap = hid }, .{});

    try transferFieldHeapFree(ctx, &state, .{
        .parent = obj,
        .name = "buf",
        .fallback_hid = @enumFromInt(99),
    }, pos0(), pos1());

    try testing.expect(state.heaps.get(hid).?.state == .dead);
}

test "transferDecl: re-declaring a killed allocation makes it live again" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"item"}), .problems = &problems, .seen = &seen, .path = "test" };

    const item: LId = @enumFromInt(0);
    // One call site mints ONE HeapId, so every iteration of a loop that
    // allocates here rebinds the same id.  The kill is the previous
    // iteration's destroy arriving over the back-edge.
    const hid: HId = @enumFromInt(0);
    try transferDecl(ctx, &state, .{
        .local = item,
        .init_kind = .{ .heap_alloc = .{ .id = hid } },
    }, pos0());
    try transferHeapFree(ctx, &state, .{
        .freed_local = item,
        .fallback_hid = @enumFromInt(1),
    }, pos0(), pos1());
    try testing.expect(state.heaps.get(hid).?.state == .dead);

    try transferDecl(ctx, &state, .{
        .local = item,
        .init_kind = .{ .heap_alloc = .{ .id = hid } },
    }, pos0());

    // This reset is what keeps a back-edge's dead entry from cascading
    // into the next iteration's reads.  Without it every field read in a
    // loop that re-allocates would see a dead owner.
    try testing.expect(state.heaps.get(hid).?.state == .live);
    try testing.expect(state.locals.get(item).? == .heap);
    try testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "transferCompositeEscape: an out-of-domain ExprKind is a silent no-op, not a widening" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{ "inner", "src" }), .problems = &problems, .seen = &seen, .path = "test" };

    const inner: LId = @enumFromInt(0);
    const src: LId = @enumFromInt(1);
    try state.locals.put(gpa, inner, .undef);
    try state.locals.put(gpa, src, .{ .stack = inner });
    // `.composite_borrow` and `.borrowed_from` resolve through to their
    // SOURCE local, so `src`'s `.stack` origin would satisfy the report
    // below.  The narrowing is what keeps a shape this function has no
    // argument for from reporting an escape nobody proved: the two
    // variants the producer actually emits still fire, and these two
    // reach the same origin by a different route and stay silent.
    try transferCompositeEscape(ctx, &state, .{ .composite_borrow = src }, pos0(), pos1());
    try transferCompositeEscape(ctx, &state, .{ .borrowed_from = src }, pos0(), pos1());
    try testing.expectEqual(@as(usize, 0), problems.items.len);

    // The same source reached through the shapes the producer DOES emit
    // still reports, so the control above is about the narrowing and not
    // about `src` failing to carry a stack origin.
    try transferCompositeEscape(ctx, &state, .{ .stack_ref = src }, pos0(), pos1());
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("stack-escape", problems.items[0].rule_id);
}

test "transferFieldUse: a locally killed parent guards a field with no origin of its own" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"item"}), .problems = &problems, .seen = &seen, .path = "test" };

    const item: LId = @enumFromInt(0);
    const hid: HId = @enumFromInt(0);
    try state.heaps.put(gpa, hid, .{
        .state = .dead,
        .killed_at = .{ .line = 1, .column = 1, .byte = 10, .end_line = 1, .end_column = 2, .end_byte = 11 },
    });
    try state.locals.put(gpa, item, .{ .heap = hid });
    // `count` is a `u32`: an assignment of it never records a field
    // origin, so `state.fields` stays empty and the parent's own
    // liveness is the ONLY thing that can report the read.  This is the
    // state an in-function `create` + `destroy` pair leaves behind —
    // `is_inter_procedural` is false — so gating this report on that
    // flag would silence a real use-after-free of a locally-owned value.
    try testing.expectEqual(@as(usize, 0), state.fields.count());
    try transferFieldUse(ctx, &state, .{ .parent = item, .name = "count" }, pos0(), pos1());

    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("heap-use-after-free", problems.items[0].rule_id);
}

test "transferFieldUse: a live field origin does not excuse a dead owner" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"item"}), .problems = &problems, .seen = &seen, .path = "test" };

    const item: LId = @enumFromInt(0);
    const owner: HId = @enumFromInt(0);
    const buf: HId = @enumFromInt(1);
    try state.heaps.put(gpa, owner, .{
        .state = .dead,
        .killed_at = .{ .line = 1, .column = 1, .byte = 10, .end_line = 1, .end_column = 2, .end_byte = 11 },
    });
    try state.heaps.put(gpa, buf, .{ .state = .live });
    try state.locals.put(gpa, item, .{ .heap = owner });
    try state.fields.putContext(gpa, .{ .parent = item, .name = "buf" }, .{ .heap = buf }, .{});
    // The field's payload is separately owned and still live, which is
    // exactly the case that makes skipping the parent check unsound:
    // `item.buf` is reached THROUGH `item`, so the read itself runs on a
    // pointer whose storage has already been handed back.  A live
    // payload makes the copy wrong, not the access safe.  This is the
    // control any narrowing of the parent-liveness guard has to survive.
    try transferFieldUse(ctx, &state, .{ .parent = item, .name = "buf" }, pos0(), pos1());

    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("heap-use-after-free", problems.items[0].rule_id);
}

test "transferFieldUse: an inter-procedural dead parent guards the same read" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"item"}), .problems = &problems, .seen = &seen, .path = "test" };

    const item: LId = @enumFromInt(0);
    const hid: HId = @enumFromInt(0);
    try state.heaps.put(gpa, hid, .{
        .state = .dead,
        .killed_at = .{ .line = 1, .column = 1, .byte = 10, .end_line = 1, .end_column = 2, .end_byte = 11 },
        .is_inter_procedural = true,
    });
    try state.locals.put(gpa, item, .{ .heap = hid });
    // The callee freed a pointer this function never saw allocated, so
    // no field-level tracking exists to fall back on: the parent report
    // is the whole signal.  Whatever is done about the locally-killed
    // case above, this one has to keep firing.
    try transferFieldUse(ctx, &state, .{ .parent = item, .name = "count" }, pos0(), pos1());

    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("heap-use-after-free", problems.items[0].rule_id);
}

test "transferFieldUse: a live parent reports nothing on its own" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"item"}), .problems = &problems, .seen = &seen, .path = "test" };

    const item: LId = @enumFromInt(0);
    const hid: HId = @enumFromInt(0);
    try state.heaps.put(gpa, hid, .{ .state = .live });
    try state.locals.put(gpa, item, .{ .heap = hid });
    // Control for the tests above: the parent's liveness alone must
    // never produce a finding while the allocation is alive.
    try transferFieldUse(ctx, &state, .{ .parent = item, .name = "count" }, pos0(), pos1());

    try testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "transferFieldUse: the owner prong yields the statement only to a rule it reported" {
    const gpa = testing.allocator;
    const without_undef: config_mod.Config = .{ .enabled = &enabled_without_use_undefined };
    // Both arms run the IDENTICAL statement sequence — only `config`
    // differs — so the pair answers "does this gate decide this
    // finding?" and not "did these two fixtures happen to differ?".
    // `heap-use-after-free` stays ON in both: the subject arm turns
    // off `use_undefined`, an unrelated rule, and must still find it.
    const arms = [_]struct { config: *const config_mod.Config, rule: []const u8 }{
        .{ .config = &config_mod.Default, .rule = "use-undefined" },
        .{ .config = &without_undef, .rule = "heap-use-after-free" },
    };
    for (arms) |arm| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{
            .gpa = gpa,
            .locals = mkLocals(&.{"item"}),
            .problems = &problems,
            .seen = &seen,
            .path = "test",
            .config = arm.config,
        };
        const item: LId = @enumFromInt(0);
        const freed: HId = @enumFromInt(0);

        // `var item: Item = undefined;`
        try transferDecl(ctx, &state, .{ .local = item, .init_kind = .undef }, pos0());
        // `gpa.free(item.buf);` — nothing has tracked this field, so
        // the free takes `transferFieldHeapFree`'s inter-procedural
        // FALLBACK and records it as a dead heap.  Both halves of the
        // fixture therefore come out of the real transfers: "this
        // field's allocation is dead" is a fact the analysis reached,
        // not one the test wrote into the state.  The fallback touches
        // only `state.fields`, which is what leaves the parent `.undef`
        // and a dead field origin coexisting.
        try transferFieldHeapFree(ctx, &state, .{
            .parent = item,
            .name = "buf",
            .fallback_hid = freed,
        }, pos0(), pos1());
        try testing.expect(state.locals.get(item).? == .undef);
        try testing.expect(state.heaps.get(freed).?.state == .dead);

        // `sink(item.buf);`
        try transferFieldUse(ctx, &state, .{ .parent = item, .name = "buf" }, pos0(), pos1());

        // Exactly one finding either way.  Under the defaults the owner
        // still wins the byte (`use-undefined` names the read); with
        // `use_undefined` off the owner prong has reported nothing, so
        // the field's own dead origin has to get its say instead of
        // being dropped on the owner's behalf.
        try testing.expectEqual(@as(usize, 1), problems.items.len);
        try testing.expectEqualStrings(arm.rule, problems.items[0].rule_id);
    }
}

test "originOfInit: copy_of arena yields .arena_borrow" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{ "a", "b" }), .problems = &problems, .seen = &seen, .path = "test" };

    const a: LId = @enumFromInt(0);
    const aid: AId = @enumFromInt(7);
    try state.locals.put(gpa, a, .{ .arena = aid });

    const o = try originOfInit(ctx, &state, .{ .copy_of = a }, pos0());
    try testing.expect(o == .arena_borrow);
    try testing.expectEqual(aid, o.arena_borrow);
}

test "originOfInit: arena_init mints + registers live arena" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"a"}), .problems = &problems, .seen = &seen, .path = "test" };

    const aid: AId = @enumFromInt(11);
    const o = try originOfInit(ctx, &state, .{ .arena_init = .{ .id = aid } }, pos0());
    try testing.expect(o == .arena);
    try testing.expectEqual(aid, o.arena);
    try testing.expect(state.arenas.get(aid).?.state == .live);
}

test "transfer: reset_capture clears local to .plain + drops field tracking" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"bin"}), .problems = &problems, .seen = &seen, .path = "test" };

    const bin: LId = @enumFromInt(0);
    try state.locals.put(gpa, bin, .{ .heap = @enumFromInt(1) });
    try state.fields.putContext(gpa, .{ .parent = bin, .name = "path" }, .{ .heap = @enumFromInt(2) }, .{});

    const stmt: Stmt = .{
        .kind = .{ .reset_capture = .{ .local = bin } },
        .pos = pos0(),
        .end_pos = pos1(),
    };
    try transfer(ctx, &state, stmt);

    try testing.expect(state.locals.get(bin).? == .plain);
    try testing.expect(state.fields.count() == 0);
}

test "transfer: dispatches each StmtKind without panic" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = mkLocals(&.{"x"}), .problems = &problems, .seen = &seen, .path = "test" };

    const x: LId = @enumFromInt(0);
    try state.locals.put(gpa, x, .plain);

    // Smoke-test the dispatcher: every kind should at least not crash
    // on a minimal valid input.
    const kinds = [_]Stmt{
        .{ .kind = .{ .decl = .{ .local = x, .init_kind = .plain } }, .pos = pos0(), .end_pos = pos1() },
        .{ .kind = .{ .assign = .{ .target = x, .rhs_kind = .plain } }, .pos = pos0(), .end_pos = pos1() },
        .{ .kind = .{ .pointer_write = .{ .target = x } }, .pos = pos0(), .end_pos = pos1() },
        .{ .kind = .{ .use = .{ .local = x } }, .pos = pos0(), .end_pos = pos1() },
        .{ .kind = .{ .lowering_gap = .{ .note = "smoke" } }, .pos = pos0(), .end_pos = pos1() },
    };
    for (kinds) |s| try transfer(ctx, &state, s);
}

test "transfer: aliasable boolean reads do not retain assumptions" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "flag", .decl_pos = pos0(), .address_taken = true },
        .{ .name = "saved", .decl_pos = pos0() },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const flag: LId = @enumFromInt(0);
    const saved: LId = @enumFromInt(1);
    try transfer(ctx, &state, .{ .kind = .{ .decl = .{ .local = saved, .init_kind = .{ .heap_alloc = .{ .id = @enumFromInt(0) } } } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &state, .{ .kind = .{ .heap_free = .{ .freed_local = saved, .fallback_hid = @enumFromInt(0) } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &state, .{ .kind = .{ .assume = .{ .local = flag } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &state, .{ .kind = .{ .assume = .{ .not_local = flag } }, .pos = pos0(), .end_pos = pos1() });
    try transfer(ctx, &state, .{ .kind = .{ .use = .{ .local = saved } }, .pos = pos0(), .end_pos = pos1() });
    try testing.expect(state.feasible);
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("heap-use-after-free", problems.items[0].rule_id);
}
