//! Layer 2 abstract state.
//!
//! Each value carries an `Origin` tagging where its lifetime is bound;
//! the state tracks which arenas are still live.  Use-validity is a
//! lookup, not a borrow-graph traversal.
//!
//! Algorithm: worklist fixed-point over a CFG, with `join` conservatively
//! combining states at merge points.
//!
//! Which way a path has already read lives in [Facts], which owns those
//! predicates' lifecycle and the rule for when two paths may still be
//! folded together.

const std = @import("std");

// ── Identity tokens ────────────────────────────────────────

/// Local-variable slot id, function-scoped.
pub const LocalId = enum(u32) { _ };

/// Identifies a particular arena at its construction site.  Two distinct
/// ArenaIds == two distinct lifetimes; they never compare equal.
pub const ArenaId = enum(u32) { _ };

/// Identifies a particular heap allocation at its site (gpa.alloc /
/// gpa.create / dupe / etc.).  Distinct HeapIds == distinct allocations.
pub const HeapId = enum(u32) { _ };

/// CFG block identifier — see cfg.zig.
pub const BlockId = enum(u32) { _ };

/// Identity of an `if` condition within one function.  Minted at
/// lowering time by the pair that says two conditions are the SAME
/// expression — same text, same bindings, and nothing in between
/// could have changed any of the operands.  Two `if`s reading one
/// condition share an id; two that merely look alike do not.
pub const GuardId = enum(u32) { _ };

// ── Origin ─────────────────────────────────────────────────

/// What a value's lifetime is bound to.
pub const Origin = union(enum) {
    /// No lifetime constraint — plain primitives, comptime consts, ints,
    /// caller-owned heap allocations.
    plain,
    /// Pointer/slice into an arena's bump memory.  Use is invalid once
    /// the arena is dead; return is invalid when the arena is
    /// function-local (escape).
    arena: ArenaId,
    /// Value whose storage lives inside the arena (e.g. allocator
    /// returned from `arena.allocator()`, list initialized from such
    /// an allocator, slice duped through it).  Distinct from .arena
    /// so that `.deinit()` on the borrowed value does NOT kill the
    /// underlying arena — only deinit on the arena ITSELF (.arena)
    /// fires arena_kill.  Use-after-deinit semantics are identical
    /// to .arena.
    arena_borrow: ArenaId,
    /// Pointer/slice to a function-local stack variable.  Returning
    /// such a value past the function's frame is undefined behavior
    /// — the storage is reclaimed on return.  LocalId is the source
    /// stack variable, retained for diagnostics.
    stack: LocalId,
    /// Heap allocation (gpa.alloc / gpa.create / dupe / ...).  Use
    /// after the corresponding free is UB; the second free is a
    /// double-free.
    heap: HeapId,
    /// Local was initialized to `undefined` and not yet assigned a
    /// real value.  Reading or returning it is a bug.
    undef,
    /// Multiple origins (e.g. struct of borrows).  Conservative: any
    /// constituent dying makes the composite invalid.
    composite: []const Origin,

    pub fn eql(a: Origin, b: Origin) bool {
        if (@as(@typeInfo(Origin).@"union".tag_type.?, a) != @as(@typeInfo(Origin).@"union".tag_type.?, b)) return false;
        return switch (a) {
            .plain => true,
            .arena => |x| x == b.arena,
            .arena_borrow => |x| x == b.arena_borrow,
            .stack => |x| x == b.stack,
            .heap => |x| x == b.heap,
            .undef => true,
            .composite => |xs| blk: {
                const ys = b.composite;
                if (xs.len != ys.len) break :blk false;
                for (xs, ys) |xi, yi| if (!xi.eql(yi)) break :blk false;
                break :blk true;
            },
        };
    }
};

// ── ArenaState ─────────────────────────────────────────────

/// Where a kill (free / arena.deinit) happened — full position so
/// diagnostics can render a secondary span with the source line, not
/// just a byte offset.
pub const KillSite = struct {
    line: u32,
    column: u32,
    byte: u32,
    end_line: u32,
    end_column: u32,
    end_byte: u32,
};

pub const ArenaState = struct {
    state: enum { live, dead },
    /// When dead, the source position of the kill site — used in
    /// diagnostics.
    killed_at: ?KillSite = null,
    /// True when this entry was created by the inter-procedural
    /// fallback in transferHeapFree / transferFieldHeapFree (i.e.,
    /// the local had no prior tracked .heap origin but a
    /// takes-ownership call took it).  No report branches on it: it
    /// is part of the partition identity `livenessAgrees` compares,
    /// so a path this function freed never joins a path a callee
    /// freed, and the merged record names neither source of the death.
    is_inter_procedural: bool = false,
    /// True iff the arena descriptor itself sits on the heap
    /// (`var a = gpa.create(ArenaAllocator)`).  Stack-allocated
    /// arenas (`var a = ArenaAllocator.init(...)`) leave this
    /// false.  Both still mint an `ArenaId` for UAK tracking, but
    /// out-param escape needs to distinguish them: a heap-
    /// allocated arena's descriptor outlives the function, so
    /// writing its pointer through `*T` is ownership transfer,
    /// not escape.
    is_heap_allocated: bool = false,
    /// The allocator local that produced this heap allocation —
    /// e.g. for `var buf = gpa.alloc(...)`, the LocalId of `gpa`.
    /// Compared against the free-site allocator at
    /// `transferHeapFree` to surface allocator-mismatch bugs
    /// (oven-sh/bun#29840 class: `mimalloc_arena.alloc(...)` then
    /// `default.free(...)`).  Null when the alloc receiver
    /// wasn't a known local (dotted chain, stdlib reference,
    /// fallback heap from inter-procedural @takes, etc.) — no
    /// check fires in that case.
    allocator_local: ?LocalId = null,
};

// ── Facts ───────────────────────────────────────────────────

/// Which way this path has already been shown to read: the boolean
/// locals it evaluated, and the `if` conditions it tested.
///
/// Both maps are one owner because they answer one question — which way
/// this path went — and `join` / `canMerge` consume them as one answer.
/// A fact that survives a merge is a claim about EVERY path in the
/// partition, so the maps are copied, intersected and compared together;
/// splitting them lets a merge keep a predicate one side never
/// established, and the correlation between a path's predicates and the
/// resources that path touched disappears.  Invalidation is the one
/// policy that is deliberately NOT shared: a rebind invalidates the
/// local's predicate and no guard, because a guard names a condition
/// rather than a slot — see `forgetLocal`.
pub const Facts = struct {
    /// What each boolean local reads on this path, for the locals a
    /// predicate has already been read from.  An absent entry means
    /// "not read yet", which a later `.assume` may fill in and a rebind
    /// drops.
    booleans: std.AutoArrayHashMapUnmanaged(LocalId, bool) = .empty,

    /// Which way each `if` condition this path has already been shown
    /// to read.  Keyed by [GuardId]; the value is the truth value the
    /// path carries.
    ///
    /// This is what makes a local initialised UNDER a guard readable
    /// under a later, re-tested spelling of that guard:
    ///
    ///     var saved: Frame = undefined;
    ///     if (top < stack.len) { saved = stack[top]; }
    ///     …
    ///     if (top < stack.len) { use(saved); }
    ///
    /// The two paths through the first `if` are separated anyway —
    /// `saved` is defined on one and not on the other — and this map is
    /// what says WHICH.  The path that left the first `if` with the
    /// condition false is then cut off at the second, because the two
    /// conditions are one expression over bindings nothing in between
    /// could have changed (see [GuardId]).  A read anywhere else is
    /// untouched, and stays diagnosed.
    guards: std.AutoArrayHashMapUnmanaged(GuardId, bool) = .empty,

    pub fn deinit(self: *Facts, gpa: std.mem.Allocator) void {
        self.booleans.deinit(gpa);
        self.guards.deinit(gpa);
    }

    /// Copy `src` over `self` under the same contract
    /// `AbstractState.cloneFrom` runs on the maps beside these: clear,
    /// reserve what `src` needs, refill.  A failure partway through
    /// leaves the maps already refilled owned by the caller's errdefer,
    /// as there is nothing half-built to unwind per map.
    pub fn cloneFrom(self: *Facts, src: *const Facts, gpa: std.mem.Allocator) !void {
        try copyMap(@TypeOf(self.booleans), &self.booleans, &src.booleans, gpa);
        try copyMap(@TypeOf(self.guards), &self.guards, &src.guards, gpa);
    }

    /// What `local` reads on this path, or null when no predicate has
    /// been read from it yet.
    pub fn boolean(self: *const Facts, local: LocalId) ?bool {
        return self.booleans.get(local);
    }

    /// Record what `local` reads, or forget it when `value` is null.
    /// A fresh `decl` and a whole-local rebind both land here: whatever
    /// the previous value was read as, the slot now holds something
    /// else.
    pub fn bindBoolean(self: *Facts, gpa: std.mem.Allocator, local: LocalId, value: ?bool) !void {
        if (value) |reads| {
            try self.booleans.put(gpa, local, reads);
        } else self.forgetLocal(local);
    }

    /// Drop what `local` was read as, leaving its guards standing.  A
    /// guard names a condition rather than a slot, and lowering minted
    /// its id for the condition — no rebind of a local makes a tested
    /// condition untested.
    pub fn forgetLocal(self: *Facts, local: LocalId) void {
        if (self.booleans.getIndex(local)) |index| {
            _ = self.booleans.swapRemoveAt(index);
        }
    }

    /// Drop every local predicate, for a statement that may have written
    /// any of them through an alias.  Guard facts survive it for the same
    /// reason they survive `forgetLocal`.
    pub fn forgetAllLocals(self: *Facts) void {
        self.booleans.clearRetainingCapacity();
    }

    /// Assert that `local` reads `holds` on this path.  False means the
    /// path already carries the opposite reading and therefore describes
    /// no real program; nothing is written in that case.
    ///
    /// `remember` is false for a local whose address is taken: an alias
    /// can rewrite it behind this path's back, so what the assumption
    /// just learned may not be recorded.  A fact the path ALREADY
    /// carries still contradicts this one either way.
    pub fn assumeBoolean(self: *Facts, gpa: std.mem.Allocator, local: LocalId, holds: bool, remember: bool) !bool {
        if (self.booleans.get(local)) |known| return known == holds;
        if (remember) try self.booleans.put(gpa, local, holds);
        return true;
    }

    /// Record which way `guard` read.  False means this path had already
    /// recorded the opposite value, so it contradicted itself and
    /// nothing downstream of it describes a real program.
    ///
    /// The identity is minted only for a pair of conditions the lowering
    /// proved to be one expression — same text, same bindings, and
    /// nothing between them able to change an operand — so the two tests
    /// really are two readings of one value.
    ///
    /// Recording only; nothing here decides whether a local is
    /// initialised.  What the pruning buys is that the surviving path
    /// into a later `if (COND) { use(x); }` is the one where `COND` held
    /// at the earlier `if` too — and that is exactly the path that wrote
    /// `x`.  A read anywhere else is untouched, and still diagnosed.
    pub fn assumeGuard(self: *Facts, gpa: std.mem.Allocator, guard: GuardId, holds: bool) !bool {
        if (self.guards.get(guard)) |known| return known == holds;
        try self.guards.put(gpa, guard, holds);
        return true;
    }

    /// Intersect `other`'s predicates into `self`; true when anything
    /// was dropped, i.e. when the join changed what this path claims.
    /// A fact survives only when BOTH paths carry it: the joined state
    /// must assert no more than every path in the partition said.
    fn joinFrom(self: *Facts, other: *const Facts) bool {
        const changed = intersectPredicates(@TypeOf(self.booleans), &self.booleans, &other.booleans);
        // A guard survives the join only when BOTH paths tested it and got
        // the same answer.  A one-sided entry means one path never reached
        // that `if` at all, so it knows nothing about the condition — and
        // keeping the other's answer for it would let a path that never
        // evaluated the condition prune itself at a later test.
        return intersectPredicates(@TypeOf(self.guards), &self.guards, &other.guards) or changed;
    }

    /// How the two states' predicates compare.  `AbstractState.canMerge`
    /// turns this into a decision; keeping the classification next to the
    /// maps keeps the cap next to the rule that applies it.
    ///
    /// IDENTICAL means nothing here separated the two paths, so liveness
    /// may be joined freely.  REQUIRES_SAME_LIVENESS means they DID read
    /// something differently, but only within what the join policy
    /// tolerates, so the caller has to confirm the resources agree before
    /// folding them together.  SEPARATE means joining would throw away
    /// the whole correlation.
    ///
    /// Liveness agreement is NECESSARY but not sufficient once the
    /// predicates differ at all, which is why the boolean map is capped
    /// separately: at most ONE flag may disagree, and only when both
    /// sides carry it.  Past that the join would drop every predicate
    /// that separated the two paths and the correlation the partition
    /// exists to keep would be gone.  Within the cap the merge is still
    /// sound, because dropping a boolean can only stop a later `.assume`
    /// from pruning — `joinFrom` never inserts one — so the merged state
    /// asserts strictly LESS than either input rather than something
    /// neither of them said.
    fn relationTo(self: *const Facts, other: *const Facts) MergeRelation {
        // Guard facts must agree EXACTLY, with no one-sided entries.
        // Unlike a boolean local — where a path that never read it can
        // simply be assumed — a guard says this path DID test a
        // condition, and a path that never reached that `if` knows
        // nothing about it.  Merging the two would let one path's answer
        // stand in for the other's, which is precisely the "the condition
        // held here, so the local is initialized" inference this map
        // exists to make.
        if (!self.guardsAgree(other)) return .separate;
        var different: usize = 0;
        var only_self: usize = 0;
        var only_other: usize = 0;
        for (self.booleans.keys(), self.booleans.values()) |key, value| {
            if (other.booleans.get(key)) |other_value| {
                if (value != other_value) different += 1;
            } else only_self += 1;
        }
        for (other.booleans.keys()) |key| {
            if (!self.booleans.contains(key)) only_other += 1;
        }
        if (different == 0 and only_self == 0 and only_other == 0) return .identical;
        // Differing only by a flag ONE side never read costs nothing:
        // `joinFrom` drops it, and a path that never read a local can
        // simply assume it later.
        if (different == 0 and (only_self == 0) != (only_other == 0)) return .requires_same_liveness;
        if (different == 1 and only_self == 0 and only_other == 0) return .requires_same_liveness;
        return .separate;
    }

    /// Both states carry exactly the same guards with the same truth
    /// values.
    fn guardsAgree(self: *const Facts, other: *const Facts) bool {
        if (self.guards.count() != other.guards.count()) return false;
        for (self.guards.keys(), self.guards.values()) |key, value| {
            const mirror = other.guards.get(key) orelse return false;
            if (mirror != value) return false;
        }
        return true;
    }
};

/// How one state's predicates relate to another's.  `canMerge` resolves
/// the middle case against liveness and decides the other two outright.
const MergeRelation = enum { identical, requires_same_liveness, separate };

/// Copy every entry of `src` into `dest`, reusing whatever capacity
/// `dest` already holds.  One body for all seven maps a state owns —
/// clear, reserve what `src` needs, refill — and every array hash map
/// takes its context on the put, so the six auto-context maps and the
/// `fields` map are the same call here.  Every one of those contexts is
/// a stateless empty struct — the auto one by construction, `FieldKey`'s
/// by hand — which is what makes `{}` the whole context argument a
/// caller can be asked for.
///
/// `Map` is passed explicitly at each call site rather than inferred
/// from the pointers, so the map a call names is visible in the call.
fn copyMap(comptime Map: type, dest: *Map, src: *const Map, gpa: std.mem.Allocator) !void {
    dest.clearRetainingCapacity();
    try dest.ensureTotalCapacity(gpa, src.count());
    for (src.keys(), src.values()) |key, value| {
        dest.putAssumeCapacityContext(key, value, .{});
    }
}

/// `joinFrom` filters the two predicate maps the same way: walk once,
/// keep only the entries `other` also carries with the same reading, and
/// `swapRemove` the rest so the swap does not shift the scan.  True when
/// anything was dropped.
fn intersectPredicates(comptime Map: type, self_map: *Map, other: *const Map) bool {
    var changed = false;
    var index: usize = 0;
    while (index < self_map.count()) {
        const key = self_map.keys()[index];
        if (other.get(key) != self_map.values()[index]) {
            _ = self_map.swapRemoveAt(index);
            changed = true;
        } else index += 1;
    }
    return changed;
}

// ── AbstractState ──────────────────────────────────────────

pub const AbstractState = struct {
    feasible: bool = true,
    /// Which way this path has already been shown to read — see [Facts],
    /// which owns the maps, their lifecycle and the merge rule over them.
    facts: Facts = .{},

    /// Per-local origin tracking.
    locals: std.AutoArrayHashMapUnmanaged(LocalId, Origin) = .empty,

    /// Per-arena liveness.  Killed arenas remain in the map (with .dead)
    /// so we can surface "use-after-kill at L; killed at K" diagnostics.
    arenas: std.AutoArrayHashMapUnmanaged(ArenaId, ArenaState) = .empty,

    /// Per-heap-allocation liveness.  Same shape as arenas.
    heaps: std.AutoArrayHashMapUnmanaged(HeapId, ArenaState) = .empty,

    /// Field-level origin tracking.  Keyed by (parent local, field
    /// name); lets `s.buf = alloc(); free(s.buf); use(s.buf);` catch
    /// UAF.  Name slices borrow from source — caller keeps it alive.
    fields: std.ArrayHashMapUnmanaged(FieldKey, Origin, FieldKey.Context, true) = .empty,
    /// `*T` out-parameter writes that carried a heap origin.  Keyed
    /// by the out-param local; value is the HeapId of the most
    /// recently written value.  Checked at function exit
    /// (`transferRet`): if the heap has been freed by a defer
    /// between the write and the return, the caller's pointee now
    /// dangles — fire `heap-use-after-free`.  See
    /// `transferOutParamWrite` and `transferRet` for the producer
    /// and consumer.
    out_param_writes: std.AutoArrayHashMapUnmanaged(LocalId, HeapId) = .empty,

    pub fn deinit(self: *AbstractState, gpa: std.mem.Allocator) void {
        self.locals.deinit(gpa);
        self.arenas.deinit(gpa);
        self.heaps.deinit(gpa);
        self.fields.deinit(gpa);
        self.out_param_writes.deinit(gpa);
        self.facts.deinit(gpa);
    }

    /// Forget every field record belonging to `parent`.
    ///
    /// The one place a whole-local rebind drops field tracking: a fresh
    /// `decl` creates a new instance, a whole-local `assign` rebinds one,
    /// and `reset_capture` re-points one at a new frame.  Whatever the
    /// fields described belonged to the value that is gone, so keeping
    /// it would read as a stale ownership correlation — the back-edge
    /// artifact that fires double-free / UAF on a value no longer there.
    pub fn forgetFields(self: *AbstractState, parent: LocalId) void {
        retainWhere(&self.fields, parent, fieldNotOwnedBy);
    }

    pub fn clone(self: *const AbstractState, gpa: std.mem.Allocator) !AbstractState {
        var out: AbstractState = .{};
        errdefer out.deinit(gpa);
        try out.cloneFrom(self, gpa);
        return out;
    }

    /// Copy `src` into `self`, reusing existing allocated capacity.
    /// Maps are cleared then refilled; if capacity is already
    /// sufficient, no allocator call is made for that map.
    pub fn cloneFrom(self: *AbstractState, src: *const AbstractState, gpa: std.mem.Allocator) !void {
        self.feasible = src.feasible;
        try copyMap(@TypeOf(self.locals), &self.locals, &src.locals, gpa);
        try copyMap(@TypeOf(self.arenas), &self.arenas, &src.arenas, gpa);
        try copyMap(@TypeOf(self.heaps), &self.heaps, &src.heaps, gpa);
        try copyMap(@TypeOf(self.fields), &self.fields, &src.fields, gpa);
        try copyMap(@TypeOf(self.out_param_writes), &self.out_param_writes, &src.out_param_writes, gpa);
        try self.facts.cloneFrom(&src.facts, gpa);
    }

    /// Drop every fact the target block can no longer observe, so two
    /// paths that differ only in temporaries nobody reads again become
    /// one state.
    ///
    /// `keep` is the caller's bitmap of locals whose origin is still
    /// readable, derived from a backward fixpoint over the whole CFG;
    /// `live_out_params` is the parallel set for `out_param_writes`,
    /// which only a `return` reads.  `project` widens `keep` for the one
    /// dynamic edge below and never narrows it.
    ///
    /// Sound because a fact the block cannot read is a fact no statement
    /// reachable from it can read either, and because the solver stores
    /// only projected states: whatever consumed a dropped origin runs in
    /// a block whose own live set kept it.  `kept_heaps` / `kept_arenas`
    /// are reusable scratch — the ids surviving origins still name.
    ///
    /// The widening edge is the `.stack` owner.  A `.stack` origin names
    /// the local whose frame it points into, and both
    /// `checkOriginAlive` and `transferFieldUse` read that owner's
    /// origin, so the owner stays observable even when the block never
    /// names it — and so does anything it in turn borrows from.  Each
    /// `retainStackOwners` pass either adds a borrow or stops, so the
    /// loop runs at most once per borrow chain.  Widening writes only
    /// into `keep`, never into a map, so it can never introduce a fact:
    /// once every stored local, field and pending out-param key — and
    /// every allocation record the surviving origins still name — is
    /// retained, no fact left in this state can be dropped.  That is the
    /// question `projectionIsIdentity` reports on, and it is the only
    /// place the retention rule is argued.
    pub fn project(
        self: *AbstractState,
        gpa: std.mem.Allocator,
        keep: []u8,
        live_out_params: []const u8,
        kept_heaps: *std.ArrayListUnmanaged(u32),
        kept_arenas: *std.ArrayListUnmanaged(u32),
    ) !void {
        // Widen `keep` to the owners of the `.stack` origins that survive
        // it; see this function's doc for why that edge is sound.
        var grew = true;
        while (grew) grew = retainStackOwners(self, keep);

        retainWhere(&self.locals, keep, isRetained);
        retainWhere(&self.fields, keep, fieldParentIsRetained);

        // An allocation record is only observable while something still
        // names it: a surviving origin, or an out-param write a `return`
        // will still resolve against `heaps`.
        kept_heaps.clearRetainingCapacity();
        kept_arenas.clearRetainingCapacity();
        for (self.locals.values()) |origin| try noteAllocation(gpa, kept_heaps, kept_arenas, origin);
        for (self.fields.values()) |origin| try noteAllocation(gpa, kept_heaps, kept_arenas, origin);
        for (self.out_param_writes.values()) |heap| try kept_heaps.append(gpa, @intFromEnum(heap));

        retainWhere(&self.heaps, kept_heaps.items, allocationIsNamed);
        retainWhere(&self.arenas, kept_arenas.items, allocationIsNamed);

        // Pending out-param writes carry their own live set: only a
        // `return` reads them, so the fixpoint over the CFG decides.
        retainWhere(&self.out_param_writes, live_out_params, isRetained);

        // `facts` is NOT filtered here, and that is the sound direction
        // rather than an omission: a predicate records which way this
        // path was already asked, and the join it feeds keeps a fact
        // only when every path carries it.  Dropping the predicates of a
        // local this block stopped reading would therefore let two paths
        // that were separated by that condition look identical, which
        // is the correlation `canMerge` exists to preserve.  Keeping
        // them costs partitions, never reports — and the same reasoning
        // is why `projectionIsIdentity` does not look at them either.
    }

    /// True when `project` would hand this state back unchanged, so the
    /// solver can propagate the original instead of cloning it.
    ///
    /// The answer is about the STATE: `project`'s widening may still add
    /// ids to `keep` afterwards, which changes nothing here, so this asks
    /// only whether any stored entry would be dropped.  See `project` for
    /// the retention rule and its soundness argument.
    pub fn projectionIsIdentity(
        self: *const AbstractState,
        keep: []const u8,
        live_out_params: []const u8,
    ) bool {
        for (self.locals.keys()) |local| if (!isRetained(keep, local)) return false;
        for (self.fields.keys()) |key| if (!isRetained(keep, key.parent)) return false;
        for (self.out_param_writes.keys()) |out| if (!isRetained(live_out_params, out)) return false;
        // A handful of allocation records against a handful of origins:
        // cheaper than copying the whole map to find out the same thing.
        for (self.heaps.keys()) |heap| if (!self.namesAllocation(.{ .heap = heap })) return false;
        for (self.arenas.keys()) |arena| if (!self.namesAllocation(.{ .arena = arena })) return false;
        return true;
    }

    /// True when a tracked local, field, or pending out-param write still
    /// points at `wanted`.
    fn namesAllocation(self: *const AbstractState, wanted: Origin) bool {
        for (self.locals.values()) |origin| if (originNamesAllocation(origin, wanted)) return true;
        for (self.fields.values()) |origin| if (originNamesAllocation(origin, wanted)) return true;
        if (wanted == .heap) {
            for (self.out_param_writes.values()) |pending| {
                if (pending == wanted.heap) return true;
            }
        }
        return false;
    }

    fn originNamesAllocation(origin: Origin, wanted: Origin) bool {
        switch (origin) {
            .arena_borrow => |arena| if (wanted == .arena) return arena == wanted.arena,
            .composite => |parts| {
                for (parts) |part| if (originNamesAllocation(part, wanted)) return true;
                return false;
            },
            else => {},
        }
        return origin.eql(wanted);
    }

    /// True when `other` may be folded into this partition without
    /// erasing a resource hazard.
    ///
    /// `join` is only faithful when the two states already agree on
    /// the facts a transfer function acts on, and those agreements have
    /// to hold BEFORE any join:
    ///
    ///  * `locals` / `fields` origins.  `join` collapses two different
    ///    origins to `.plain`, which erases the resource identity that
    ///    the later `.use` / `.ret` / `.field_use` check reads.  Merging
    ///    there loses the diagnostic outright, so those states stay in
    ///    separate partitions.
    ///  * liveness, whenever the path predicates DIFFER.  `join` keeps
    ///    `dead` if either side is dead, so joining while a predicate
    ///    tells the two paths apart reports a kill that only one of them
    ///    performed.  When the predicates are IDENTICAL there is no
    ///    correlation left to lose and liveness is joined — that is what
    ///    makes `if (c) free(p); ... use(p)` fire at the merge.
    ///
    /// How many predicates may differ — and which of them a guard fact
    /// is — belongs to `facts`, which owns both predicate maps:
    /// `relationTo` names the three cases, and only the middle one has
    /// to consult liveness.  Liveness agreement is therefore NECESSARY
    /// whenever the predicates differ at all, and not consulted when
    /// they do not.
    ///
    /// Origins equal to `.plain` are skipped throughout.  `.plain` means
    /// "no lifetime constraint"; every consumer in cfg_transfer.zig
    /// treats an absent entry and a `.plain` entry identically, and the
    /// block-scoped temporaries of one switch arm are the bulk of a
    /// function's local map.  Counting them made each arm its own
    /// partition and exhausted `max_path_states` on ordinary code.
    pub fn canMerge(self: *const AbstractState, other: *const AbstractState) bool {
        if (!self.originsAgree(other)) return false;
        return switch (self.facts.relationTo(&other.facts)) {
            .identical => true,
            .requires_same_liveness => self.sameLiveness(other),
            .separate => false,
        };
    }

    /// Every non-`.plain` origin tracked here is tracked in `other` with
    /// the same identity.  `join` only ever weakens an origin, so this is
    /// the precondition under which joining cannot drop a hazard.
    fn originsAgree(self: *const AbstractState, other: *const AbstractState) bool {
        for (self.locals.keys(), self.locals.values()) |key, value| {
            if (value == .plain) continue;
            const mirror = other.locals.get(key) orelse return false;
            if (mirror == .plain or !mirror.eql(value)) return false;
        }
        for (other.locals.keys(), other.locals.values()) |key, value| {
            if (value == .plain) continue;
            const mirror = self.locals.get(key) orelse return false;
            if (mirror == .plain or !mirror.eql(value)) return false;
        }
        for (self.fields.keys(), self.fields.values()) |key, value| {
            if (value == .plain) continue;
            const mirror = other.fields.getContext(key, .{}) orelse return false;
            if (mirror == .plain or !mirror.eql(value)) return false;
        }
        for (other.fields.keys(), other.fields.values()) |key, value| {
            if (value == .plain) continue;
            const mirror = self.fields.getContext(key, .{}) orelse return false;
            if (mirror == .plain or !mirror.eql(value)) return false;
        }
        return true;
    }

    /// Arenas, heaps and out-param writes describe the same hazard state.
    /// `killed_at` is deliberately excluded: it only chooses which source
    /// span a "freed here" note points at, never whether a report fires,
    /// so two paths that kill the same allocation at different sites
    /// belong in one partition.
    fn sameLiveness(self: *const AbstractState, other: *const AbstractState) bool {
        if (self.arenas.count() != other.arenas.count()) return false;
        for (self.arenas.keys(), self.arenas.values()) |key, value| {
            const mirror = other.arenas.get(key) orelse return false;
            if (!livenessAgrees(value, mirror)) return false;
        }
        if (self.heaps.count() != other.heaps.count()) return false;
        for (self.heaps.keys(), self.heaps.values()) |key, value| {
            const mirror = other.heaps.get(key) orelse return false;
            if (!livenessAgrees(value, mirror)) return false;
        }
        if (self.out_param_writes.count() != other.out_param_writes.count()) return false;
        for (self.out_param_writes.keys(), self.out_param_writes.values()) |key, value| {
            if (value != (other.out_param_writes.get(key) orelse return false)) return false;
        }
        return true;
    }
};

/// Two liveness records name the same hazard state when every field a
/// transfer function branches on agrees.  `killed_at` is a diagnostic
/// label, not a hazard fact — see `sameLiveness`.
fn livenessAgrees(a: ArenaState, b: ArenaState) bool {
    return a.state == b.state and
        a.is_inter_procedural == b.is_inter_procedural and
        a.is_heap_allocated == b.is_heap_allocated and
        a.allocator_local == b.allocator_local;
}

/// Bitmap membership for a projected state's retained-local set.  An id
/// past the end of the bitmap counts as retained: a state handed to
/// `project` without one must keep every fact it carries.
fn isRetained(keep: []const u8, local: LocalId) bool {
    const index: usize = @intFromEnum(local);
    const byte = index / 8;
    if (byte >= keep.len) return true;
    const bit: u3 = @intCast(index % 8);
    return keep[byte] & (@as(u8, 1) << bit) != 0;
}

fn markRetained(keep: []u8, local: LocalId) void {
    const index: usize = @intFromEnum(local);
    const byte = index / 8;
    if (byte >= keep.len) return;
    const bit: u3 = @intCast(index % 8);
    keep[byte] |= @as(u8, 1) << bit;
}

/// `project` and `forgetFields` filter their maps the same way: walk
/// once, keep the entries the callback accepts, `swapRemove` the rest so
/// the swap does not shift the scan.  One loop for every one of them;
/// each map supplies only the key projection its own notion of "keeps"
/// needs, and the predicate itself is always a plain function of
/// `context` and the key.
fn retainWhere(
    map: anytype,
    context: anytype,
    comptime keepKey: anytype,
) void {
    var index: usize = 0;
    while (index < map.count()) {
        if (keepKey(context, map.keys()[index])) {
            index += 1;
        } else {
            _ = map.swapRemoveAt(index);
        }
    }
}

fn fieldParentIsRetained(keep: []const u8, key: FieldKey) bool {
    return isRetained(keep, key.parent);
}

fn allocationIsNamed(named: []const u32, key: anytype) bool {
    return namesId(named, @intFromEnum(key));
}

fn fieldNotOwnedBy(parent: LocalId, key: FieldKey) bool {
    return key.parent != parent;
}

/// Add to `keep` every local that a surviving `.stack` origin points
/// into — whether the origin sits in `locals` or in `fields` — and report
/// whether anything was added.  `project` drives this to a false and
/// carries the argument for why those owners stay observable; this is
/// the operational contract alone.
fn retainStackOwners(self: *const AbstractState, keep: []u8) bool {
    var grew = false;
    for (self.locals.keys(), self.locals.values()) |local, origin| {
        switch (origin) {
            .stack => |owner| {
                if (isRetained(keep, local) and !isRetained(keep, owner)) {
                    markRetained(keep, owner);
                    grew = true;
                }
            },
            else => {},
        }
    }
    for (self.fields.keys(), self.fields.values()) |key, origin| {
        switch (origin) {
            .stack => |owner| {
                if (isRetained(keep, key.parent) and !isRetained(keep, owner)) {
                    markRetained(keep, owner);
                    grew = true;
                }
            },
            else => {},
        }
    }
    return grew;
}

fn noteAllocation(
    gpa: std.mem.Allocator,
    kept_heaps: *std.ArrayListUnmanaged(u32),
    kept_arenas: *std.ArrayListUnmanaged(u32),
    origin: Origin,
) !void {
    switch (origin) {
        .heap => |heap| try kept_heaps.append(gpa, @intFromEnum(heap)),
        .arena, .arena_borrow => |arena| try kept_arenas.append(gpa, @intFromEnum(arena)),
        .composite => |parts| {
            for (parts) |part| try noteAllocation(gpa, kept_heaps, kept_arenas, part);
        },
        .plain, .stack, .undef => {},
    }
}

fn namesId(ids: []const u32, id: u32) bool {
    for (ids) |candidate| if (candidate == id) return true;
    return false;
}

pub const FieldKey = struct {
    parent: LocalId,
    name: []const u8,

    pub const Context = struct {
        pub fn hash(_: Context, k: FieldKey) u32 {
            var h: u32 = @intFromEnum(k.parent) *% 2654435761;
            for (k.name) |c| h = h *% 33 +% c;
            return h;
        }
        pub fn eql(_: Context, a: FieldKey, b: FieldKey, _: usize) bool {
            return a.parent == b.parent and std.mem.eql(u8, a.name, b.name);
        }
    };
};

const JoinResult = enum { unchanged, changed };

/// Conservative CFG-merge join:
///   - Locals: same origin → keep; different → collapse to .plain
///   - Arenas: dead on either side → dead on merge
pub fn join(
    self: *AbstractState,
    other: *const AbstractState,
    gpa: std.mem.Allocator,
) !JoinResult {
    std.debug.assert(self.feasible);
    std.debug.assert(other.feasible);
    // The predicate maps join on their own rule: a fact survives only
    // when BOTH paths carry it.  Nothing above or below may insert one.
    var changed = self.facts.joinFrom(&other.facts);

    for (other.locals.keys(), other.locals.values()) |local, other_val| {
        const gop = try self.locals.getOrPut(gpa, local);
        if (!gop.found_existing) {
            gop.value_ptr.* = other_val;
            changed = true;
            continue;
        }
        if (gop.value_ptr.* != .plain and !gop.value_ptr.eql(other_val)) {
            gop.value_ptr.* = .plain;
            changed = true;
        }
    }

    for (other.arenas.keys(), other.arenas.values()) |arena, other_state| {
        const gop = try self.arenas.getOrPut(gpa, arena);
        if (!gop.found_existing) {
            gop.value_ptr.* = other_state;
            changed = true;
            continue;
        }
        if (gop.value_ptr.state == .live and other_state.state == .dead) {
            gop.value_ptr.* = other_state;
            changed = true;
        }
    }

    for (other.heaps.keys(), other.heaps.values()) |heap, other_state| {
        const gop = try self.heaps.getOrPut(gpa, heap);
        if (!gop.found_existing) {
            gop.value_ptr.* = other_state;
            changed = true;
            continue;
        }
        if (gop.value_ptr.state == .live and other_state.state == .dead) {
            gop.value_ptr.* = other_state;
            changed = true;
        }
    }

    for (other.fields.keys(), other.fields.values()) |fk, other_val| {
        const gop = try self.fields.getOrPutContext(gpa, fk, .{});
        if (!gop.found_existing) {
            gop.value_ptr.* = other_val;
            changed = true;
            continue;
        }
        if (gop.value_ptr.* != .plain and !gop.value_ptr.eql(other_val)) {
            gop.value_ptr.* = .plain;
            changed = true;
        }
    }

    // Out-param writes: a write recorded on ANY merging path is
    // potentially live at the join.  Keep existing entries; add new
    // ones from `other`.  When the same out_local maps to different
    // HeapIds across paths, keep the existing (conservative — at
    // exit we'll check the kept entry's liveness; missing the
    // other's heap is acceptable precision loss for v1).
    for (other.out_param_writes.keys(), other.out_param_writes.values()) |out_local, other_hid| {
        const gop = try self.out_param_writes.getOrPut(gpa, out_local);
        if (!gop.found_existing) {
            gop.value_ptr.* = other_hid;
            changed = true;
        }
    }

    return if (changed) .changed else .unchanged;
}

// ── Tests ──────────────────────────────────────────────────

test "Origin.eql arena-vs-arena" {
    const a: ArenaId = @enumFromInt(1);
    const b: ArenaId = @enumFromInt(2);
    try std.testing.expect(Origin.eql(.{ .arena = a }, .{ .arena = a }));
    try std.testing.expect(!Origin.eql(.{ .arena = a }, .{ .arena = b }));
    try std.testing.expect(!Origin.eql(.{ .arena = a }, .plain));
}

test "canMerge: plain temporaries do not split a partition" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const owned: LocalId = @enumFromInt(0);
    const h: HeapId = @enumFromInt(0);
    // The same allocation reached through two arms that each declared
    // their own block-scoped temporaries.  A `.plain` origin is what
    // every consumer sees for an absent local, so these are one state;
    // counting the temporaries is what exhausted `max_path_states` on
    // ordinary code.
    try lhs.locals.put(gpa, owned, .{ .heap = h });
    try lhs.locals.put(gpa, @enumFromInt(1), .plain);
    try rhs.locals.put(gpa, owned, .{ .heap = h });
    try rhs.locals.put(gpa, @enumFromInt(2), .plain);
    try rhs.locals.put(gpa, @enumFromInt(3), .plain);
    try std.testing.expect(lhs.canMerge(&rhs));
}

test "canMerge: differing origins keep their partitions apart" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const l: LocalId = @enumFromInt(0);
    // Identical predicates used to short-circuit to "merge", and `join`
    // then collapsed the two heap identities to `.plain` — erasing the
    // allocation every later `.use` / `.ret` check had to consult.
    try lhs.locals.put(gpa, l, .{ .heap = @enumFromInt(0) });
    try rhs.locals.put(gpa, l, .{ .heap = @enumFromInt(1) });
    try std.testing.expect(!lhs.canMerge(&rhs));
    try std.testing.expect(!rhs.canMerge(&lhs));
}

test "canMerge: identical predicates join a kill only one path made" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const l: LocalId = @enumFromInt(0);
    const h: HeapId = @enumFromInt(0);
    try lhs.locals.put(gpa, l, .{ .heap = h });
    try rhs.locals.put(gpa, l, .{ .heap = h });
    try lhs.heaps.put(gpa, h, .{ .state = .live });
    try rhs.heaps.put(gpa, h, .{ .state = .dead });
    // Nothing tells the two paths apart, so the kill really did happen
    // on one of them — merging is what lets a later use be reported.
    try std.testing.expect(lhs.canMerge(&rhs));
}

test "canMerge: differing predicates do not join a kill only one path made" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const l: LocalId = @enumFromInt(0);
    const h: HeapId = @enumFromInt(0);
    const flag: LocalId = @enumFromInt(1);
    try lhs.locals.put(gpa, l, .{ .heap = h });
    try rhs.locals.put(gpa, l, .{ .heap = h });
    try lhs.heaps.put(gpa, h, .{ .state = .live });
    try rhs.heaps.put(gpa, h, .{ .state = .dead });
    try lhs.facts.bindBoolean(gpa, flag, true);
    try rhs.facts.bindBoolean(gpa, flag, false);
    // The predicate is the only thing separating these paths, so the
    // two resource histories must stay correlated.
    try std.testing.expect(!lhs.canMerge(&rhs));
}

test "canMerge: one differing predicate flag still joins when liveness agrees" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const l: LocalId = @enumFromInt(0);
    const h: HeapId = @enumFromInt(0);
    const flag: LocalId = @enumFromInt(1);
    try lhs.locals.put(gpa, l, .{ .heap = h });
    try rhs.locals.put(gpa, l, .{ .heap = h });
    try lhs.heaps.put(gpa, h, .{ .state = .live });
    try rhs.heaps.put(gpa, h, .{ .state = .live });
    try lhs.facts.bindBoolean(gpa, flag, true);
    try rhs.facts.bindBoolean(gpa, flag, false);
    // Same allocation, same liveness: no kill is being reported for one
    // path only, so there is no hazard correlation to lose.  The flag
    // itself is dropped by `join`, which only costs a later `.assume`
    // the ability to prune — it cannot invent a fact.  This is the
    // disjunct the documented precondition permits, and it had no test,
    // so a "correction" of the code to a misreading of the doc would
    // have gone unnoticed.
    try std.testing.expect(lhs.canMerge(&rhs));
    try std.testing.expect(rhs.canMerge(&lhs));
}

test "canMerge: two differing predicate flags keep their partitions apart" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const h: HeapId = @enumFromInt(0);
    const first: LocalId = @enumFromInt(0);
    const second: LocalId = @enumFromInt(1);
    try lhs.heaps.put(gpa, h, .{ .state = .live });
    try rhs.heaps.put(gpa, h, .{ .state = .live });
    try lhs.facts.bindBoolean(gpa, first, true);
    try rhs.facts.bindBoolean(gpa, first, false);
    try lhs.facts.bindBoolean(gpa, second, true);
    try rhs.facts.bindBoolean(gpa, second, false);
    // One differing flag is tolerated; two are the cap.  Past the cap
    // the joined state would have lost every predicate that separated
    // these paths, so the correlation the partition exists to keep is
    // gone and they must stay apart.
    try std.testing.expect(!lhs.canMerge(&rhs));
    try std.testing.expect(!rhs.canMerge(&lhs));
}

test "canMerge: the kill site is a note, not a hazard fact" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const l: LocalId = @enumFromInt(0);
    const h: HeapId = @enumFromInt(0);
    try lhs.locals.put(gpa, l, .{ .heap = h });
    try rhs.locals.put(gpa, l, .{ .heap = h });
    try lhs.heaps.put(gpa, h, .{ .state = .dead, .killed_at = .{
        .line = 1,
        .column = 1,
        .byte = 10,
        .end_line = 1,
        .end_column = 2,
        .end_byte = 11,
    } });
    try rhs.heaps.put(gpa, h, .{ .state = .dead, .killed_at = .{
        .line = 9,
        .column = 3,
        .byte = 90,
        .end_line = 9,
        .end_column = 4,
        .end_byte = 91,
    } });
    // Both are dead; only the "freed here" note differs.
    try std.testing.expect(lhs.canMerge(&rhs));
}

test "join: same locals unchanged" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const l: LocalId = @enumFromInt(0);
    const a: ArenaId = @enumFromInt(0);
    try lhs.locals.put(gpa, l, .{ .arena = a });
    try rhs.locals.put(gpa, l, .{ .arena = a });
    const result = try join(&lhs, &rhs, gpa);
    try std.testing.expectEqual(JoinResult.unchanged, result);
    try std.testing.expect(Origin.eql(lhs.locals.get(l).?, .{ .arena = a }));
}

test "join: differing locals collapse to plain" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const l: LocalId = @enumFromInt(0);
    try lhs.locals.put(gpa, l, .{ .arena = @enumFromInt(1) });
    try rhs.locals.put(gpa, l, .{ .arena = @enumFromInt(2) });
    const result = try join(&lhs, &rhs, gpa);
    try std.testing.expectEqual(JoinResult.changed, result);
    try std.testing.expect(Origin.eql(lhs.locals.get(l).?, .plain));
}

test "join: dead-on-either-side wins for arenas" {
    const gpa = std.testing.allocator;
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    const a: ArenaId = @enumFromInt(0);
    try lhs.arenas.put(gpa, a, .{ .state = .live });
    const kill: KillSite = .{ .line = 1, .column = 1, .byte = 42, .end_line = 1, .end_column = 2, .end_byte = 43 };
    try rhs.arenas.put(gpa, a, .{ .state = .dead, .killed_at = kill });
    const result = try join(&lhs, &rhs, gpa);
    try std.testing.expectEqual(JoinResult.changed, result);
    try std.testing.expect(lhs.arenas.get(a).?.state == .dead);
    try std.testing.expectEqual(@as(u32, 42), lhs.arenas.get(a).?.killed_at.?.byte);
}

test "clone: predicate facts arrive intact and stop being shared" {
    const gpa = std.testing.allocator;
    var src: AbstractState = .{};
    defer src.deinit(gpa);
    const flag: LocalId = @enumFromInt(0);
    const guard: GuardId = @enumFromInt(0);
    try src.facts.bindBoolean(gpa, flag, true);
    _ = try src.facts.assumeGuard(gpa, guard, false);

    var copy = try src.clone(gpa);
    defer copy.deinit(gpa);
    // `canMerge` reads the copy's own facts, so a clone that dropped
    // them would fold two differently-correlated paths into one state.
    try std.testing.expectEqual(@as(?bool, true), copy.facts.boolean(flag));
    try std.testing.expect(try copy.facts.assumeGuard(gpa, guard, false));
    try std.testing.expect(!try copy.facts.assumeGuard(gpa, guard, true));

    // A fact written to one state must not be readable from the other:
    // a shared map would make the copy's rebind delete the source's
    // predicate as well, and the copy is what the solver keeps walking.
    copy.facts.forgetLocal(flag);
    try std.testing.expectEqual(@as(?bool, null), copy.facts.boolean(flag));
    try std.testing.expectEqual(@as(?bool, true), src.facts.boolean(flag));
    // A guard names a condition, not a slot, so dropping what a local
    // reads leaves the recorded condition standing.
    try std.testing.expect(try copy.facts.assumeGuard(gpa, guard, false));
}

/// Fill one entry into every map a clone copies — both `Facts` maps
/// included — then clone.  Run under a failing allocator this walks the
/// sweep across all seven maps' allocation sites.
fn cloneOneEntryPerMap(gpa: std.mem.Allocator) !void {
    var src: AbstractState = .{};
    defer src.deinit(gpa);
    const local: LocalId = @enumFromInt(0);
    const heap: HeapId = @enumFromInt(0);
    try src.locals.put(gpa, local, .{ .heap = heap });
    try src.arenas.put(gpa, @enumFromInt(0), .{ .state = .live });
    try src.heaps.put(gpa, heap, .{ .state = .live });
    try src.out_param_writes.put(gpa, local, heap);
    const field = try src.fields.getOrPutContext(gpa, .{ .parent = local, .name = "buf" }, .{});
    field.value_ptr.* = .{ .heap = heap };
    try src.facts.bindBoolean(gpa, @enumFromInt(1), true);
    _ = try src.facts.assumeGuard(gpa, @enumFromInt(0), true);

    // A clone that dies partway through owns every map it had already
    // refilled through its errdefer.  The failure propagates so the
    // sweep below counts this allocation point as failed and moves on
    // to the next one.
    var copy = try src.clone(gpa);
    defer copy.deinit(gpa);
    // And a clone that succeeds is mergeable with its source, which is
    // only true when the fact maps came across too.
    try std.testing.expect(src.canMerge(&copy));
}

test "clone: a failure partway through leaves nothing allocated" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, cloneOneEntryPerMap, .{});
}
