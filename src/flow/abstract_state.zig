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
//!
//! Initialization coverage is separate from lifetime origins: sparse exact
//! elements, fixed prefixes, bounded affine prefixes, and complete-base holes.
//! Joins retain only common coverage. Projection keeps live comparison and
//! array/counter dependencies, without changing predicate partition policy.
//! Integer type endpoints are immutable CFG context, borrowed by every state.
//! They bound values, never their definedness or the payload they index.

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

/// The bounded affine terms understood by initialization transfer.
pub const IndexTerm = union(enum) {
    unknown,
    constant: u64,
    local: struct { local: LocalId, offset: i8 = 0 },
    field: struct { parent: LocalId, name: []const u8, offset: i8 = 0, is_unsigned: bool = false },
};

/// A selected element in a contiguous group of `scale` values per lane.
pub const ScaledElement = struct { index: LocalId, scale: u64, offset: u64 = 0 };

/// Immutable binding type context. The CFG owns rows; states only borrow them.
pub const IntegerDomain = struct {
    kind: enum(u8) { unknown, unsigned_unbounded, unsigned, signed, signed_unbounded } = .unknown,
    bits: u8 = 0,
};

comptime {
    std.debug.assert(@sizeOf(IntegerDomain) == 2);
    std.debug.assert(@alignOf(IntegerDomain) == 1);
}

pub const Comparison = struct {
    lhs: IndexTerm,
    rhs: IndexTerm,
    op: enum { eq, ne, lt, le, gt, ge },
};

const ElementKey = struct { array: LocalId, index: u64 };
const PrefixKey = struct { array: LocalId, counter: LocalId };
/// Bounded prefixes also constrain the counter. Capped prefixes cover
/// [0, min(max(counter + offset, 0), extent)) without constraining it.
const SymbolicPrefix = struct { offset: i8, extent: u64, capped: bool = false, scale: u64 = 1 };
const TermBounds = struct {
    lower: ?i128 = null,
    upper: ?i128 = null,

    fn valid(self: TermBounds) bool {
        const lower = self.lower orelse return true;
        const upper = self.upper orelse return true;
        return lower <= upper;
    }

    fn raiseLower(self: *TermBounds, endpoint: i128) void {
        self.lower = if (self.lower) |old| @max(old, endpoint) else endpoint;
    }

    fn lowerUpper(self: *TermBounds, endpoint: i128) void {
        self.upper = if (self.upper) |old| @min(old, endpoint) else endpoint;
    }

    fn intersect(self: *TermBounds, other: TermBounds) void {
        if (other.lower) |lower| self.raiseLower(lower);
        if (other.upper) |upper| self.lowerUpper(upper);
    }

    fn offset(self: TermBounds, amount: i8) TermBounds {
        return .{
            .lower = if (self.lower) |lower| std.math.add(i128, lower, amount) catch null else null,
            .upper = if (self.upper) |upper| std.math.add(i128, upper, amount) catch null else null,
        };
    }
};

const integer_endpoints = blk: {
    var unsigned: [65]TermBounds = undefined;
    var signed: [65]TermBounds = undefined;
    for (0..65) |bits| {
        unsigned[bits] = .{ .lower = 0, .upper = (@as(i128, 1) << @intCast(bits)) - 1 };
        signed[bits] = if (bits == 0)
            .{ .lower = 0, .upper = 0 }
        else
            .{ .lower = -(@as(i128, 1) << @intCast(bits - 1)), .upper = (@as(i128, 1) << @intCast(bits - 1)) - 1 };
    }
    break :blk .{ .unsigned = unsigned, .signed = signed };
};

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
    /// Borrowed immutable LocalId table, shared by every state in this CFG.
    integer_domains: []const IntegerDomain = &.{},
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
    /// Defined descriptor bits do not prove initialized array payloads.
    /// Only writes that lack a definite value need a sparse negative entry.
    unknown_field_values: std.ArrayHashMapUnmanaged(FieldKey, void, FieldKey.Context, true) = .empty,
    /// Sparse uncertainty for scalar values and selected aggregate payloads.
    unknown_values: std.AutoArrayHashMapUnmanaged(LocalId, void) = .empty,
    /// Diagnostic taint, separate from missing value certificates.
    may_undefined_values: std.AutoArrayHashMapUnmanaged(LocalId, void) = .empty,
    undefined_field_values: std.ArrayHashMapUnmanaged(FieldKey, void, FieldKey.Context, true) = .empty,
    /// Byte-write witnesses, independent of value/resource certificates.
    written_fields: std.ArrayHashMapUnmanaged(FieldKey, void, FieldKey.Context, true) = .empty,
    /// `*T` out-parameter writes that carried a heap origin.  Keyed
    /// by the out-param local; value is the HeapId of the most
    /// recently written value.  Checked at function exit
    /// (`transferRet`): if the heap has been freed by a defer
    /// between the write and the return, the caller's pointee now
    /// dangles — fire `heap-use-after-free`.  See
    /// `transferOutParamWrite` and `transferRet` for the producer
    /// and consumer.
    out_param_writes: std.AutoArrayHashMapUnmanaged(LocalId, HeapId) = .empty,

    /// Flat sparse keys own no nested allocations and never scale with array extent.
    exact_elements: std.AutoArrayHashMapUnmanaged(ElementKey, void) = .empty,
    undefined_elements: std.AutoArrayHashMapUnmanaged(ElementKey, void) = .empty,
    complete_arrays: std.AutoArrayHashMapUnmanaged(LocalId, void) = .empty,
    fixed_prefixes: std.AutoArrayHashMapUnmanaged(LocalId, u64) = .empty,
    symbolic_prefixes: std.AutoArrayHashMapUnmanaged(PrefixKey, SymbolicPrefix) = .empty,
    scalar_values: std.AutoArrayHashMapUnmanaged(LocalId, u64) = .empty,
    nonnegative_locals: std.AutoArrayHashMapUnmanaged(LocalId, void) = .empty,
    comparisons: std.ArrayListUnmanaged(Comparison) = .empty,

    pub fn deinit(self: *AbstractState, gpa: std.mem.Allocator) void {
        self.locals.deinit(gpa);
        self.arenas.deinit(gpa);
        self.heaps.deinit(gpa);
        self.fields.deinit(gpa);
        self.unknown_field_values.deinit(gpa);
        self.unknown_values.deinit(gpa);
        self.may_undefined_values.deinit(gpa);
        self.undefined_field_values.deinit(gpa);
        self.written_fields.deinit(gpa);
        self.out_param_writes.deinit(gpa);
        self.facts.deinit(gpa);
        self.exact_elements.deinit(gpa);
        self.undefined_elements.deinit(gpa);
        self.complete_arrays.deinit(gpa);
        self.fixed_prefixes.deinit(gpa);
        self.symbolic_prefixes.deinit(gpa);
        self.scalar_values.deinit(gpa);
        self.nonnegative_locals.deinit(gpa);
        self.comparisons.deinit(gpa);
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
        retainWhere(&self.unknown_field_values, parent, fieldNotOwnedBy);
        _ = self.unknown_values.swapRemove(parent);
        _ = self.may_undefined_values.swapRemove(parent);
        retainWhere(&self.undefined_field_values, parent, fieldNotOwnedBy);
        retainWhere(&self.written_fields, parent, fieldNotOwnedBy);
    }

    /// A whole-location write removes prior undefined bytes, not certificates
    /// or resource identities retained for the other rules.
    pub fn forgetUndefinedBytes(self: *AbstractState, parent: LocalId) void {
        _ = self.may_undefined_values.swapRemove(parent);
        retainWhere(&self.undefined_field_values, parent, fieldNotOwnedBy);
        for (self.fields.keys(), self.fields.values()) |key, *origin| {
            if (key.parent == parent and origin.* == .undef) origin.* = .plain;
        }
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
        self.integer_domains = src.integer_domains;
        try copyMap(@TypeOf(self.locals), &self.locals, &src.locals, gpa);
        try copyMap(@TypeOf(self.arenas), &self.arenas, &src.arenas, gpa);
        try copyMap(@TypeOf(self.heaps), &self.heaps, &src.heaps, gpa);
        try copyMap(@TypeOf(self.fields), &self.fields, &src.fields, gpa);
        try copyMap(@TypeOf(self.unknown_field_values), &self.unknown_field_values, &src.unknown_field_values, gpa);
        try copyMap(@TypeOf(self.unknown_values), &self.unknown_values, &src.unknown_values, gpa);
        try copyMap(@TypeOf(self.may_undefined_values), &self.may_undefined_values, &src.may_undefined_values, gpa);
        try copyMap(@TypeOf(self.undefined_field_values), &self.undefined_field_values, &src.undefined_field_values, gpa);
        try copyMap(@TypeOf(self.written_fields), &self.written_fields, &src.written_fields, gpa);
        try copyMap(@TypeOf(self.out_param_writes), &self.out_param_writes, &src.out_param_writes, gpa);
        try self.facts.cloneFrom(&src.facts, gpa);
        try copyMap(@TypeOf(self.exact_elements), &self.exact_elements, &src.exact_elements, gpa);
        try copyMap(@TypeOf(self.undefined_elements), &self.undefined_elements, &src.undefined_elements, gpa);
        try copyMap(@TypeOf(self.complete_arrays), &self.complete_arrays, &src.complete_arrays, gpa);
        try copyMap(@TypeOf(self.fixed_prefixes), &self.fixed_prefixes, &src.fixed_prefixes, gpa);
        try copyMap(@TypeOf(self.symbolic_prefixes), &self.symbolic_prefixes, &src.symbolic_prefixes, gpa);
        try copyMap(@TypeOf(self.scalar_values), &self.scalar_values, &src.scalar_values, gpa);
        try copyMap(@TypeOf(self.nonnegative_locals), &self.nonnegative_locals, &src.nonnegative_locals, gpa);
        try self.comparisons.ensureTotalCapacity(gpa, src.comparisons.items.len);
        self.comparisons.clearRetainingCapacity();
        self.comparisons.appendSliceAssumeCapacity(src.comparisons.items);
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
        while (grew) {
            grew = retainStackOwners(self, keep);
            grew = self.retainInitializationDependencies(keep) or grew;
        }

        retainWhere(&self.locals, keep, isRetained);
        retainWhere(&self.fields, keep, fieldParentIsRetained);
        retainWhere(&self.unknown_field_values, keep, fieldParentIsRetained);
        retainWhere(&self.unknown_values, keep, isRetained);
        retainWhere(&self.may_undefined_values, keep, isRetained);
        retainWhere(&self.undefined_field_values, keep, fieldParentIsRetained);
        retainWhere(&self.written_fields, keep, fieldParentIsRetained);
        self.projectInitialization(keep);

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
        for (self.unknown_field_values.keys()) |key| if (!isRetained(keep, key.parent)) return false;
        for (self.unknown_values.keys()) |local| if (!isRetained(keep, local)) return false;
        for (self.may_undefined_values.keys()) |local| if (!isRetained(keep, local)) return false;
        for (self.undefined_field_values.keys()) |key| if (!isRetained(keep, key.parent)) return false;
        for (self.written_fields.keys()) |key| if (!isRetained(keep, key.parent)) return false;
        for (self.out_param_writes.keys()) |out| if (!isRetained(live_out_params, out)) return false;
        if (!self.initializationProjectionIsIdentity(keep)) return false;
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

    pub fn baseComplete(self: *const AbstractState, array: LocalId) bool {
        return self.complete_arrays.contains(array);
    }

    pub fn isArrayComplete(self: *const AbstractState, array: LocalId) bool {
        if (!self.baseComplete(array)) return false;
        for (self.undefined_elements.keys()) |key| if (key.array == array) return false;
        return true;
    }

    /// Copy the physical initialized-element mask, not a counter alias.
    pub fn copyArrayInitialization(self: *AbstractState, gpa: std.mem.Allocator, target: LocalId, source: LocalId) !void {
        if (target == source) return;
        self.forgetInitializationArray(target);
        if (self.baseComplete(source)) try self.complete_arrays.put(gpa, target, {});
        if (self.fixed_prefixes.get(source)) |prefix| try self.fixed_prefixes.put(gpa, target, prefix);
        const exact_count = self.exact_elements.count();
        var index: usize = 0;
        while (index < exact_count) : (index += 1) {
            const key = self.exact_elements.keys()[index];
            if (key.array == source) try self.exact_elements.put(gpa, .{ .array = target, .index = key.index }, {});
        }
        const hole_count = self.undefined_elements.count();
        index = 0;
        while (index < hole_count) : (index += 1) {
            const key = self.undefined_elements.keys()[index];
            if (key.array == source) try self.undefined_elements.put(gpa, .{ .array = target, .index = key.index }, {});
        }
        const prefix_count = self.symbolic_prefixes.count();
        index = 0;
        while (index < prefix_count) : (index += 1) {
            const key = self.symbolic_prefixes.keys()[index];
            const prefix = self.symbolic_prefixes.values()[index];
            if (key.array == source) try self.symbolic_prefixes.put(gpa, .{ .array = target, .counter = key.counter }, prefix);
        }
    }

    pub fn fieldValueIsDefined(self: *const AbstractState, parent: LocalId, path: []const u8) bool {
        return self.fieldValueIsDefinedWithLimit(parent, path, self.unknown_field_values.count(), false, true);
    }

    /// Unknown payloads do not report. Only reached undefined bytes do.
    pub fn fieldValueMayBeUndefined(self: *const AbstractState, parent: LocalId, path: []const u8) bool {
        const repaired_prefix = self.writtenFieldPrefix(parent, path);
        for (self.undefined_field_values.keys()) |key| {
            if (key.parent != parent) continue;
            if (fieldPathPrefix(key.name, path)) {
                if (repaired_prefix == null or repaired_prefix.? < key.name.len) return true;
            } else if (fieldPathPrefix(path, key.name)) {
                const repair = self.writtenFieldPrefix(parent, key.name);
                if (repair == null or repair.? < key.name.len) return true;
            }
        }
        if (repaired_prefix == null) {
            if (self.may_undefined_values.contains(parent)) return true;
            if (self.locals.get(parent)) |origin| if (origin == .undef) return true;
        }
        for (self.fields.keys(), self.fields.values()) |key, origin| {
            if (key.parent != parent or origin != .undef) continue;
            if (fieldPathPrefix(key.name, path) and repaired_prefix == null) return true;
            if (fieldPathPrefix(path, key.name) and self.writtenFieldPrefix(parent, key.name) == null) return true;
        }
        return false;
    }

    pub fn fieldBytesAreWritten(self: *const AbstractState, parent: LocalId, path: []const u8) bool {
        return self.writtenFieldPrefix(parent, path) != null and !self.fieldValueMayBeUndefined(parent, path);
    }

    fn writtenFieldPrefix(self: *const AbstractState, parent: LocalId, path: []const u8) ?usize {
        var prefix: ?usize = null;
        for (self.written_fields.keys()) |key| {
            if (key.parent != parent or !fieldPathPrefix(key.name, path)) continue;
            if (prefix == null or key.name.len > prefix.?) prefix = key.name.len;
        }
        return prefix;
    }

    pub fn bindWrittenField(self: *AbstractState, gpa: std.mem.Allocator, key: FieldKey, may_undefined: bool) !void {
        var index: usize = 0;
        while (index < self.written_fields.count()) {
            const old = self.written_fields.keys()[index];
            if (old.parent == key.parent and fieldPathPrefix(key.name, old.name)) {
                _ = self.written_fields.swapRemoveAt(index);
            } else index += 1;
        }
        index = 0;
        while (index < self.undefined_field_values.count()) {
            const old = self.undefined_field_values.keys()[index];
            if (old.parent == key.parent and fieldPathPrefix(key.name, old.name)) {
                _ = self.undefined_field_values.swapRemoveAt(index);
            } else index += 1;
        }
        if (!may_undefined) try self.written_fields.putContext(gpa, key, {}, .{});
    }

    pub fn forgetWrittenFields(self: *AbstractState, parent: LocalId) void {
        retainWhere(&self.written_fields, parent, fieldNotOwnedBy);
    }

    /// Array copies apply sparse element holes separately from the base proof.
    pub fn fieldArrayBaseIsDefined(self: *const AbstractState, parent: LocalId, path: []const u8) bool {
        return self.fieldValueIsDefinedWithLimit(parent, path, self.unknown_field_values.count(), true, true);
    }

    /// Appended join negatives must not change the incoming certificate.
    fn fieldValueIsDefinedWithLimit(
        self: *const AbstractState,
        parent: LocalId,
        path: []const u8,
        negative_count: usize,
        ignore_elements: bool,
        unproved_root_is_unknown: bool,
    ) bool {
        std.debug.assert(negative_count <= self.unknown_field_values.count());
        const negatives = self.unknown_field_values.keys()[0..negative_count];
        const unknown_root = (unproved_root_is_unknown and self.unknown_values.contains(parent)) or
            (if (self.locals.get(parent)) |origin| origin == .undef else false);
        var initialized_prefix: ?usize = null;
        for (self.fields.keys(), self.fields.values()) |key, origin| {
            if (key.parent != parent or origin == .undef or !fieldPathPrefix(key.name, path)) continue;
            const negative_index = self.unknown_field_values.getIndexContext(key, .{});
            const uncertain_record = unproved_root_is_unknown and
                (if (negative_index) |index| index < negative_count else false);
            if (!uncertain_record and (initialized_prefix == null or key.name.len > initialized_prefix.?)) {
                initialized_prefix = key.name.len;
            }
        }
        for (negatives) |key| {
            if (!unproved_root_is_unknown) break;
            if (key.parent != parent) continue;
            if (ignore_elements and key.name.len > path.len and
                std.mem.startsWith(u8, key.name, path) and key.name[path.len] == '[') continue;
            if (fieldPathPrefix(path, key.name)) return false;
            if (fieldPathPrefix(key.name, path) and
                (initialized_prefix == null or initialized_prefix.? <= key.name.len)) return false;
        }
        for (self.fields.keys(), self.fields.values()) |key, origin| {
            if (key.parent != parent or origin != .undef) continue;
            if (ignore_elements and key.name.len > path.len and
                std.mem.startsWith(u8, key.name, path) and key.name[path.len] == '[') continue;
            if (fieldPathPrefix(path, key.name)) return false;
            if (fieldPathPrefix(key.name, path) and
                (initialized_prefix == null or initialized_prefix.? <= key.name.len)) return false;
        }
        // A specific initialized field can repair an uncertain ancestor,
        // but cannot initialize its siblings or an enclosing whole payload.
        return !unknown_root or initialized_prefix != null;
    }

    pub fn bindFieldValue(self: *AbstractState, gpa: std.mem.Allocator, key: FieldKey, defined: bool) !void {
        if (defined) try self.bindWrittenField(gpa, key, false);
        var index: usize = 0;
        while (index < self.unknown_field_values.count()) {
            const old = self.unknown_field_values.keys()[index];
            if (old.parent == key.parent and fieldPathPrefix(key.name, old.name)) {
                _ = self.unknown_field_values.swapRemoveAt(index);
            } else index += 1;
        }
        index = 0;
        while (index < self.fields.count()) {
            const old = self.fields.keys()[index];
            if (old.parent == key.parent and fieldPathPrefix(key.name, old.name)) {
                _ = self.fields.swapRemoveAt(index);
            } else index += 1;
        }
        if (!defined) try self.unknown_field_values.putContext(gpa, key, {}, .{});
    }

    pub fn markArrayComplete(self: *AbstractState, gpa: std.mem.Allocator, array: LocalId) !void {
        try self.complete_arrays.put(gpa, array, {});
        retainWhere(&self.undefined_elements, array, elementNotOwnedBy);
        self.forgetUndefinedBytes(array);
    }

    pub fn hasExactElement(self: *const AbstractState, array: LocalId, index: u64) bool {
        const key: ElementKey = .{ .array = array, .index = index };
        if (self.undefined_elements.contains(key)) return false;
        return self.baseComplete(array) or self.exact_elements.contains(key) or
            index < self.fixedPrefix(array);
    }

    pub fn fixedPrefix(self: *const AbstractState, array: LocalId) u64 {
        return self.fixed_prefixes.get(array) orelse 0;
    }

    pub fn setFixedPrefix(
        self: *AbstractState,
        gpa: std.mem.Allocator,
        array: LocalId,
        count: u64,
    ) !void {
        try self.fixed_prefixes.put(gpa, array, count);
    }

    /// Union an initialized range with the existing prefix and sparse suffix.
    /// Disconnected ranges add no fact; holes outside the range remain intact.
    pub fn markArrayRangeComplete(
        self: *AbstractState,
        gpa: std.mem.Allocator,
        array: LocalId,
        start: u64,
        end: u64,
    ) !void {
        std.debug.assert(start <= end);
        if (start == end) return;
        var hole_index: usize = 0;
        while (hole_index < self.undefined_elements.count()) {
            const hole = self.undefined_elements.keys()[hole_index];
            if (hole.array == array and hole.index >= start and hole.index < end) {
                _ = self.undefined_elements.swapRemoveAt(hole_index);
            } else hole_index += 1;
        }
        if (self.baseComplete(array) or self.fixedPrefix(array) < start) return;
        try self.advanceExactPrefix(gpa, array, @max(self.fixedPrefix(array), end));
    }

    pub fn setExactElement(
        self: *AbstractState,
        gpa: std.mem.Allocator,
        array: LocalId,
        index: u64,
        initialized: bool,
    ) !void {
        const key: ElementKey = .{ .array = array, .index = index };
        if (!initialized) {
            // A base initializer survives except for the selected sparse hole.
            try self.undefined_elements.put(gpa, key, {});
            _ = self.exact_elements.swapRemove(key);
            if (self.fixed_prefixes.getPtr(array)) |prefix| prefix.* = @min(prefix.*, index);
            retainWhere(&self.symbolic_prefixes, array, prefixNotOwnedBy);
            return;
        }
        _ = self.undefined_elements.swapRemove(key);
        if (self.baseComplete(array)) {
            _ = self.undefined_elements.swapRemove(key);
            return;
        }
        try self.exact_elements.put(gpa, key, {});
        try self.advanceExactPrefix(gpa, array, self.fixedPrefix(array));
    }

    fn advanceExactPrefix(
        self: *AbstractState,
        gpa: std.mem.Allocator,
        array: LocalId,
        count: u64,
    ) !void {
        var prefix = count;
        // Each advance consumes a distinct stored fact, not an extent-sized scan.
        var remaining = self.exact_elements.count();
        while (remaining > 0 and prefix < std.math.maxInt(u64)) : (remaining -= 1) {
            if (!self.exact_elements.contains(.{ .array = array, .index = prefix })) break;
            prefix += 1;
        }
        if (prefix != self.fixedPrefix(array)) try self.setFixedPrefix(gpa, array, prefix);
    }

    pub fn symbolicPrefixOffset(
        self: *const AbstractState,
        array: LocalId,
        counter: LocalId,
    ) ?i8 {
        return if (self.symbolic_prefixes.get(.{ .array = array, .counter = counter })) |prefix|
            if (prefix.scale == 1) prefix.offset else null
        else
            null;
    }

    pub fn setSymbolicPrefix(
        self: *AbstractState,
        gpa: std.mem.Allocator,
        array: LocalId,
        counter: LocalId,
        offset: i8,
        fixed_extent: u64,
    ) !void {
        std.debug.assert(offset >= -1 and offset <= 1);
        try self.symbolic_prefixes.put(gpa, .{ .array = array, .counter = counter }, .{
            .offset = offset,
            .extent = fixed_extent,
        });
    }

    pub fn setScaledSymbolicPrefix(self: *AbstractState, gpa: std.mem.Allocator, array: LocalId, counter: LocalId, scale: u64, extent: u64) !void {
        if (scale == 0) return;
        try self.symbolic_prefixes.put(gpa, .{ .array = array, .counter = counter }, .{
            .offset = 0,
            .extent = extent,
            .scale = scale,
        });
    }

    pub fn hasInitializedScaledElement(self: *const AbstractState, array: LocalId, element: ScaledElement) bool {
        if (element.scale == 0 or element.offset >= element.scale) return false;
        const index: IndexTerm = .{ .local = .{ .local = element.index } };
        if (!self.provesNonNegative(index)) return false;
        for (self.undefined_elements.keys()) |hole| if (hole.array == array) return false;
        for (self.symbolic_prefixes.keys(), self.symbolic_prefixes.values()) |key, prefix| {
            if (key.array == array and prefix.scale == element.scale and prefix.offset == 0 and !prefix.capped and
                self.provesLessThan(index, .{ .local = .{ .local = key.counter } })) return true;
        }
        return false;
    }

    pub fn scalarValue(self: *const AbstractState, local: LocalId) ?u64 {
        return self.scalar_values.get(local);
    }

    pub fn setScalarValue(
        self: *AbstractState,
        gpa: std.mem.Allocator,
        local: LocalId,
        value: ?u64,
    ) !void {
        self.forgetInitializationLocal(local);
        if (value) |known| {
            try self.scalar_values.put(gpa, local, known);
            try self.nonnegative_locals.put(gpa, local, {});
        }
    }

    /// Copy the current numeric value and its coverage bounds, not an alias
    /// to the source slot. Later writes to either slot invalidate only that
    /// slot's predicates.
    pub fn copyCounterValue(self: *AbstractState, gpa: std.mem.Allocator, target: LocalId, source: LocalId) !void {
        if (target == source) return;
        const value = self.scalarValue(source);
        const nonnegative = self.provesNonNegative(.{ .local = .{ .local = source } });
        const source_bounds = self.termBounds(.{ .local = .{ .local = source } });
        self.forgetInitializationLocal(target);
        if (value) |known| try self.scalar_values.put(gpa, target, known);
        if (nonnegative) try self.nonnegative_locals.put(gpa, target, {});
        const prefix_count = self.symbolic_prefixes.count();
        var index: usize = 0;
        while (index < prefix_count) : (index += 1) {
            const key = self.symbolic_prefixes.keys()[index];
            const prefix = self.symbolic_prefixes.values()[index];
            if (key.counter == source) {
                try self.symbolic_prefixes.put(gpa, .{ .array = key.array, .counter = target }, prefix);
            }
        }
        const comparison_count = self.comparisons.items.len;
        index = 0;
        while (index < comparison_count) : (index += 1) {
            const premise = self.comparisons.items[index];
            if (!termNamesLocal(premise.lhs, source) and !termNamesLocal(premise.rhs, source)) continue;
            try self.comparisons.append(gpa, .{
                .lhs = copiedCounterTerm(premise.lhs, source, target),
                .rhs = copiedCounterTerm(premise.rhs, source, target),
                .op = premise.op,
            });
        }
        // Snapshot current finite endpoints, not the source binding's type.
        // Copied facts or the destination's own type may already imply them.
        if (value == null and source_bounds.valid()) {
            const target_term: IndexTerm = .{ .local = .{ .local = target } };
            if (source_bounds.lower) |lower| {
                if (lower > 0 and lower <= std.math.maxInt(u64)) {
                    const bound: Comparison = .{ .lhs = target_term, .rhs = .{ .constant = @intCast(lower) }, .op = .ge };
                    if (!self.provesComparison(bound)) try self.comparisons.append(gpa, bound);
                }
            }
            if (source_bounds.upper) |upper| {
                if (upper >= 0 and upper <= std.math.maxInt(u64)) {
                    const bound: Comparison = .{ .lhs = target_term, .rhs = .{ .constant = @intCast(upper) }, .op = .le };
                    if (!self.provesComparison(bound)) try self.comparisons.append(gpa, bound);
                }
            }
        }
    }

    pub fn forgetInitializationArray(self: *AbstractState, array: LocalId) void {
        retainWhere(&self.written_fields, array, fieldNotOwnedPayload);
        _ = self.complete_arrays.swapRemove(array);
        _ = self.fixed_prefixes.swapRemove(array);
        retainWhere(&self.exact_elements, array, elementNotOwnedBy);
        retainWhere(&self.undefined_elements, array, elementNotOwnedBy);
        retainWhere(&self.symbolic_prefixes, array, prefixNotOwnedBy);
    }

    pub fn forgetInitializationLocal(self: *AbstractState, local: LocalId) void {
        _ = self.scalar_values.swapRemove(local);
        _ = self.nonnegative_locals.swapRemove(local);
        retainWhere(&self.symbolic_prefixes, local, prefixCounterIsNot);
        self.forgetComparisonsLocal(local);
    }

    pub fn forgetAllComparisons(self: *AbstractState) void {
        self.comparisons.clearRetainingCapacity();
    }

    fn forgetComparisonsLocal(self: *AbstractState, local: LocalId) void {
        var index: usize = 0;
        while (index < self.comparisons.items.len) {
            const premise = self.comparisons.items[index];
            if (termNamesLocal(premise.lhs, local) or termNamesLocal(premise.rhs, local)) {
                _ = self.comparisons.swapRemove(index);
            } else index += 1;
        }
    }

    pub fn forgetFieldComparisons(self: *AbstractState, parent: LocalId) void {
        var index: usize = 0;
        while (index < self.comparisons.items.len) {
            const premise = self.comparisons.items[index];
            if ((premise.lhs == .field and premise.lhs.field.parent == parent) or
                (premise.rhs == .field and premise.rhs.field.parent == parent))
            {
                _ = self.comparisons.swapRemove(index);
            } else index += 1;
        }
    }

    pub fn provesNonNegative(self: *const AbstractState, term: IndexTerm) bool {
        if (!termSupported(term)) return false;
        const bounds = self.termBounds(term);
        return bounds.valid() and if (bounds.lower) |lower| lower >= 0 else false;
    }

    pub fn provesCounterPositive(self: *const AbstractState, local: LocalId) bool {
        return self.provesComparison(.{
            .lhs = .{ .local = .{ .local = local } },
            .rhs = .{ .constant = 0 },
            .op = .gt,
        });
    }

    pub fn provesLessThan(self: *const AbstractState, lhs: IndexTerm, rhs: IndexTerm) bool {
        return self.provesComparison(.{ .lhs = lhs, .rhs = rhs, .op = .lt });
    }

    pub fn provesIndexInBounds(self: *const AbstractState, index: IndexTerm, extent: u64) bool {
        return self.provesNonNegative(index) and
            self.provesLessThan(index, .{ .constant = extent });
    }

    pub fn hasInitializedElement(
        self: *const AbstractState,
        array: LocalId,
        index: IndexTerm,
    ) bool {
        if (!self.provesNonNegative(index)) return false;
        // Dynamic selection must exclude every hole, not merely fit a prefix.
        for (self.undefined_elements.keys()) |hole| {
            if (hole.array == array and !self.provesComparison(.{
                .lhs = index,
                .rhs = .{ .constant = hole.index },
                .op = .ne,
            })) return false;
        }
        if (self.baseComplete(array)) return true;
        if (self.concreteTerm(index)) |known| {
            if (self.hasExactElement(array, known)) return true;
        }
        if (self.provesLessThan(index, .{ .constant = self.fixedPrefix(array) })) return true;
        for (self.symbolic_prefixes.keys(), self.symbolic_prefixes.values()) |key, prefix| {
            if (key.array == array and prefix.scale == 1 and
                (!prefix.capped or self.provesLessThan(index, .{ .constant = prefix.extent })) and
                self.provesLessThan(index, .{
                    .local = .{ .local = key.counter, .offset = prefix.offset },
                })) return true;
        }
        return false;
    }

    pub fn hasInitializedPrefix(self: *const AbstractState, array: LocalId, count: u64) bool {
        if (count == 0) return true;
        for (self.undefined_elements.keys()) |hole| {
            if (hole.array == array and hole.index < count) return false;
        }
        if (self.baseComplete(array) or self.fixedPrefix(array) >= count) return true;
        for (self.symbolic_prefixes.keys(), self.symbolic_prefixes.values()) |key, prefix| {
            if (key.array == array and prefix.scale == 1 and (!prefix.capped or count <= prefix.extent) and self.provesComparison(.{
                .lhs = .{ .constant = count },
                .rhs = .{ .local = .{ .local = key.counter, .offset = prefix.offset } },
                .op = .le,
            })) return true;
        }
        return false;
    }

    fn concreteTerm(self: *const AbstractState, term: IndexTerm) ?u64 {
        switch (term) {
            .unknown, .field => return null,
            .constant => |value| return value,
            .local => |value| {
                if (value.offset < -1 or value.offset > 1) return null;
                const scalar = self.scalarValue(value.local) orelse return null;
                const result = @as(i128, scalar) + value.offset;
                if (result < 0 or result > std.math.maxInt(u64)) return null;
                return @intCast(result);
            },
        }
    }

    fn integerDomainBounds(self: *const AbstractState, local: LocalId) TermBounds {
        const id = @intFromEnum(local);
        if (self.integer_domains.len == 0) return .{};
        std.debug.assert(id < self.integer_domains.len);
        const domain = self.integer_domains[id];
        return switch (domain.kind) {
            .unknown, .signed_unbounded => .{},
            .unsigned_unbounded => .{ .lower = 0 },
            .unsigned => if (domain.bits <= 64) integer_endpoints.unsigned[domain.bits] else .{ .lower = 0 },
            .signed => if (domain.bits <= 64) integer_endpoints.signed[domain.bits] else .{},
        };
    }

    fn termBounds(self: *const AbstractState, term: IndexTerm) TermBounds {
        if (!termSupported(term)) return .{};
        if (term == .constant) return .{ .lower = term.constant, .upper = term.constant };
        var bounds: TermBounds = if (term == .local) self.integerDomainBounds(term.local.local) else .{};
        var nonnegative = switch (term) {
            .local => |value| self.nonnegative_locals.contains(value.local),
            .field => |value| value.is_unsigned,
            else => unreachable,
        };
        if (term == .field and !nonnegative) {
            for (self.comparisons.items) |premise| {
                if ((premise.lhs == .field and premise.lhs.field.is_unsigned and termSameBase(term, premise.lhs)) or
                    (premise.rhs == .field and premise.rhs.field.is_unsigned and termSameBase(term, premise.rhs)))
                {
                    nonnegative = true;
                    break;
                }
            }
        }
        if (nonnegative) bounds.raiseLower(0);
        if (term == .local) {
            if (self.scalarValue(term.local.local)) |known| bounds.intersect(.{ .lower = known, .upper = known });
            for (self.symbolic_prefixes.keys(), self.symbolic_prefixes.values()) |key, prefix| {
                if (key.counter != term.local.local or prefix.capped) continue;
                bounds.raiseLower(-@as(i128, prefix.offset));
                bounds.lowerUpper(@as(i128, prefix.extent / prefix.scale) - prefix.offset);
            }
        }
        for (self.comparisons.items) |original| {
            var premise = original;
            if (termSameBase(premise.rhs, term)) premise = reverseComparison(premise);
            if (!termSameBase(premise.lhs, term)) continue;
            const known = self.concreteTerm(premise.rhs) orelse continue;
            const endpoint = @as(i128, known) - termOffset(premise.lhs);
            switch (premise.op) {
                .eq => bounds.intersect(.{ .lower = endpoint, .upper = endpoint }),
                .lt => bounds.lowerUpper(endpoint - 1),
                .le => bounds.lowerUpper(endpoint),
                .gt => bounds.raiseLower(endpoint + 1),
                .ge => bounds.raiseLower(endpoint),
                .ne => {},
            }
        }
        // Apply exclusions after intersecting base bounds, then add the offset.
        for (self.comparisons.items) |original| {
            var premise = original;
            if (termSameBase(premise.rhs, term)) premise = reverseComparison(premise);
            if (premise.op != .ne or !termSameBase(premise.lhs, term)) continue;
            const known = self.concreteTerm(premise.rhs) orelse continue;
            const endpoint = @as(i128, known) - termOffset(premise.lhs);
            if (bounds.lower) |lower| {
                if (lower == endpoint) bounds.lower = std.math.add(i128, lower, 1) catch null;
            }
            if (bounds.upper) |upper| {
                if (upper == endpoint) bounds.upper = std.math.sub(i128, upper, 1) catch null;
            }
        }
        return bounds.offset(termOffset(term));
    }

    fn directComparison(self: *const AbstractState, comparison: Comparison) bool {
        if (!termSupported(comparison.lhs) or !termSupported(comparison.rhs)) return false;
        if (termSameBase(comparison.lhs, comparison.rhs)) {
            return compareIntegers(termOffset(comparison.lhs), termOffset(comparison.rhs), comparison.op);
        }
        for (self.comparisons.items) |premise| {
            if (comparisonImplies(premise, comparison) or
                comparisonImplies(reverseComparison(premise), comparison)) return true;
        }
        const lhs = self.termBounds(comparison.lhs);
        const rhs = self.termBounds(comparison.rhs);
        return boundsProveComparison(lhs, rhs, comparison.op);
    }

    pub fn provesComparison(self: *const AbstractState, comparison: Comparison) bool {
        if (self.directComparison(comparison)) return true;
        var normalized = comparison;
        if (normalized.op == .gt or normalized.op == .ge) normalized = reverseComparison(normalized);
        if (normalized.op != .lt and normalized.op != .le) return false;
        if (normalized.op == .lt and self.directComparison(.{
            .lhs = normalized.lhs,
            .rhs = normalized.rhs,
            .op = .le,
        }) and self.directComparison(.{
            .lhs = normalized.lhs,
            .rhs = normalized.rhs,
            .op = .ne,
        })) return true;
        // One explicit comparison bridge suffices for index<count<=capacity.
        // This is bounded by stored premises; no recursive arithmetic closure is used.
        for (self.comparisons.items) |original| {
            var premise = original;
            if (premise.op == .gt or premise.op == .ge) premise = reverseComparison(premise);
            if (premise.op != .lt and premise.op != .le and premise.op != .eq) continue;
            if (!self.directComparison(.{ .lhs = normalized.lhs, .rhs = premise.lhs, .op = .le })) continue;
            const first_strict = premise.op == .lt or self.directComparison(.{
                .lhs = normalized.lhs,
                .rhs = premise.lhs,
                .op = .lt,
            });
            const bridge_op: @TypeOf(normalized.op) =
                if (normalized.op == .le or first_strict) .le else .lt;
            if (self.directComparison(.{
                .lhs = premise.rhs,
                .rhs = normalized.rhs,
                .op = bridge_op,
            })) return true;
        }
        return false;
    }

    pub fn assumeComparison(
        self: *AbstractState,
        gpa: std.mem.Allocator,
        comparison: Comparison,
    ) !bool {
        if (!termSupported(comparison.lhs) or !termSupported(comparison.rhs)) return true;
        var opposite = comparison;
        opposite.op = negateComparisonOp(comparison.op);
        if (self.provesComparison(opposite)) return false;
        if (!self.directComparison(comparison)) try self.comparisons.append(gpa, comparison);
        return true;
    }

    pub fn stepCounter(
        self: *AbstractState,
        gpa: std.mem.Allocator,
        local: LocalId,
        step: i8,
    ) !void {
        if (step != 1 and step != -1) {
            self.forgetInitializationLocal(local);
            return;
        }
        const term: IndexTerm = .{ .local = .{ .local = local } };
        const valid = if (step == -1) self.provesCounterPositive(local) else self.provesComparison(.{
            .lhs = term,
            .rhs = .{ .constant = std.math.maxInt(u64) },
            .op = .lt,
        });
        const nonnegative = valid and self.provesNonNegative(term);
        const old_value = self.scalarValue(local);
        for (self.symbolic_prefixes.keys(), self.symbolic_prefixes.values()) |key, prefix| {
            if (key.counter == local and self.hasInitializedPrefix(key.array, prefix.extent)) {
                try self.setFixedPrefix(gpa, key.array, prefix.extent);
            }
        }
        self.forgetComparisonsLocal(local);
        _ = self.scalar_values.swapRemove(local);
        _ = self.nonnegative_locals.swapRemove(local);
        if (nonnegative) try self.nonnegative_locals.put(gpa, local, {});
        if (valid) {
            if (old_value) |known| {
                const next: u64 = if (step == 1) known + 1 else known - 1;
                try self.scalar_values.put(gpa, local, next);
            }
        }
        var index: usize = 0;
        while (index < self.symbolic_prefixes.count()) {
            const key = self.symbolic_prefixes.keys()[index];
            if (key.counter != local) {
                index += 1;
                continue;
            }
            const prefix = &self.symbolic_prefixes.values()[index];
            const offset = @as(i16, prefix.offset) - step;
            if (prefix.scale != 1 or (!valid and !(step == 1 and prefix.capped)) or offset < -1) {
                _ = self.symbolic_prefixes.swapRemoveAt(index);
            } else {
                // A pop can weaken a longer initialized suffix to one
                // element without inventing a store. An extra push cannot.
                prefix.offset = @intCast(@min(offset, 1));
                index += 1;
            }
        }
    }

    fn retainInitializationDependencies(self: *const AbstractState, keep: []u8) bool {
        var grew = false;
        for (self.symbolic_prefixes.keys()) |key| {
            if (isRetained(keep, key.array) or isRetained(keep, key.counter)) {
                grew = retainLocal(keep, key.array) or grew;
                grew = retainLocal(keep, key.counter) or grew;
            }
        }
        for (self.comparisons.items) |comparison| {
            if (termIsRetained(keep, comparison.lhs) or termIsRetained(keep, comparison.rhs)) {
                grew = retainTerm(keep, comparison.lhs) or grew;
                grew = retainTerm(keep, comparison.rhs) or grew;
            }
        }
        return grew;
    }

    fn projectInitialization(self: *AbstractState, keep: []const u8) void {
        retainWhere(&self.exact_elements, keep, elementIsRetained);
        retainWhere(&self.undefined_elements, keep, elementIsRetained);
        retainWhere(&self.complete_arrays, keep, isRetained);
        retainWhere(&self.fixed_prefixes, keep, isRetained);
        retainWhere(&self.scalar_values, keep, isRetained);
        retainWhere(&self.nonnegative_locals, keep, isRetained);
        retainWhere(&self.symbolic_prefixes, keep, prefixIsRetained);
        var index: usize = 0;
        while (index < self.comparisons.items.len) {
            const comparison = self.comparisons.items[index];
            if (!termIsRetained(keep, comparison.lhs) and
                !termIsRetained(keep, comparison.rhs))
            {
                _ = self.comparisons.swapRemove(index);
            } else index += 1;
        }
    }

    fn initializationProjectionIsIdentity(self: *const AbstractState, keep: []const u8) bool {
        for (self.exact_elements.keys()) |key| if (!elementIsRetained(keep, key)) return false;
        for (self.undefined_elements.keys()) |key| if (!elementIsRetained(keep, key)) return false;
        for (self.complete_arrays.keys()) |key| if (!isRetained(keep, key)) return false;
        for (self.fixed_prefixes.keys()) |key| if (!isRetained(keep, key)) return false;
        for (self.scalar_values.keys()) |key| if (!isRetained(keep, key)) return false;
        for (self.nonnegative_locals.keys()) |key| if (!isRetained(keep, key)) return false;
        for (self.symbolic_prefixes.keys()) |key| if (!prefixIsRetained(keep, key)) return false;
        for (self.comparisons.items) |comparison| {
            if (comparison.lhs == .local and
                !isRetained(keep, comparison.lhs.local.local)) return false;
            if (comparison.rhs == .local and
                !isRetained(keep, comparison.rhs.local.local)) return false;
        }
        return true;
    }

    fn entailedPrefixOffset(
        self: *const AbstractState,
        key: PrefixKey,
        wanted: SymbolicPrefix,
    ) ?struct { offset: i8, capped: bool } {
        const mirror = self.symbolic_prefixes.get(key);
        if (wanted.scale != 1) {
            const prefix = mirror orelse return null;
            if (prefix.scale != wanted.scale or prefix.offset != wanted.offset or prefix.capped != wanted.capped) return null;
            return .{ .offset = wanted.offset, .capped = wanted.capped };
        }
        if (mirror) |prefix| if (prefix.scale != 1) return null;
        // A skipped store at capacity is safe only when that capacity is
        // already initialized. It proves a clipped endpoint, not count<=len.
        if (self.hasInitializedPrefix(key.array, wanted.extent) and
            (wanted.capped or mirror == null or mirror.?.capped or mirror.?.offset < wanted.offset))
        {
            return .{ .offset = wanted.offset, .capped = true };
        }
        if (mirror) |prefix| return .{
            .offset = @min(prefix.offset, wanted.offset),
            .capped = prefix.capped or wanted.capped,
        };
        const scalar = self.scalarValue(key.counter) orelse return null;
        var offset: i8 = wanted.offset;
        while (offset >= -1) : (offset -= 1) {
            const endpoint = @as(i128, scalar) + offset;
            if (!wanted.capped and (endpoint < 0 or endpoint > wanted.extent)) continue;
            const clipped: u64 = @intCast(@min(@max(endpoint, 0), wanted.extent));
            if (self.hasInitializedPrefix(key.array, clipped)) {
                return .{ .offset = offset, .capped = wanted.capped };
            }
        }
        return null;
    }

    fn joinInitialization(
        self: *AbstractState,
        other: *const AbstractState,
        gpa: std.mem.Allocator,
    ) !bool {
        var changed = false;
        // A guard can be implicit in one input's exact scalar and explicit
        // in the other. Preserve common predicates before weakening either
        // input's scalar or prefix proof.
        for (other.comparisons.items) |premise| {
            var recorded = false;
            for (self.comparisons.items) |existing| {
                if (comparisonEql(existing, premise) or
                    comparisonEql(existing, reverseComparison(premise)))
                {
                    recorded = true;
                    break;
                }
            }
            if (!recorded and self.provesComparison(premise)) {
                try self.comparisons.append(gpa, premise);
                changed = true;
            }
        }
        var comparison_index: usize = 0;
        while (comparison_index < self.comparisons.items.len) {
            if (!other.provesComparison(self.comparisons.items[comparison_index])) {
                _ = self.comparisons.swapRemove(comparison_index);
                changed = true;
            } else comparison_index += 1;
        }
        // Evaluate inductive candidates before weakening exact scalar/coverage facts.
        for (other.symbolic_prefixes.keys(), other.symbolic_prefixes.values()) |key, prefix| {
            if (self.symbolic_prefixes.contains(key)) continue;
            if (self.entailedPrefixOffset(key, prefix)) |entailed| {
                try self.symbolic_prefixes.put(gpa, key, .{
                    .offset = entailed.offset,
                    .extent = prefix.extent,
                    .capped = entailed.capped,
                    .scale = prefix.scale,
                });
                changed = true;
            }
        }
        var index: usize = 0;
        while (index < self.symbolic_prefixes.count()) {
            const key = self.symbolic_prefixes.keys()[index];
            const prefix = &self.symbolic_prefixes.values()[index];
            if (other.entailedPrefixOffset(key, prefix.*)) |entailed| {
                const capped = prefix.capped or entailed.capped;
                const extent = if (other.symbolic_prefixes.get(key)) |mirror|
                    (if (capped) @min(prefix.extent, mirror.extent) else @max(prefix.extent, mirror.extent))
                else
                    prefix.extent;
                if (entailed.offset != prefix.offset or extent != prefix.extent or capped != prefix.capped) changed = true;
                prefix.* = .{ .offset = entailed.offset, .extent = extent, .capped = capped, .scale = prefix.scale };
                index += 1;
            } else {
                _ = self.symbolic_prefixes.swapRemoveAt(index);
                changed = true;
            }
        }
        index = 0;
        while (index < self.exact_elements.count()) {
            const key = self.exact_elements.keys()[index];
            if (!other.hasInitializedElement(key.array, .{ .constant = key.index })) {
                _ = self.exact_elements.swapRemoveAt(index);
                changed = true;
            } else index += 1;
        }
        index = 0;
        while (index < self.fixed_prefixes.count()) {
            const array = self.fixed_prefixes.keys()[index];
            const prefix = &self.fixed_prefixes.values()[index];
            const common = if (other.hasInitializedPrefix(array, prefix.*)) prefix.* else @min(prefix.*, other.fixedPrefix(array));
            if (common != prefix.*) {
                prefix.* = common;
                changed = true;
            }
            index += 1;
        }
        index = 0;
        while (index < self.complete_arrays.count()) {
            const array = self.complete_arrays.keys()[index];
            if (!other.baseComplete(array)) {
                _ = self.complete_arrays.swapRemoveAt(index);
                changed = true;
            } else index += 1;
        }
        for (other.undefined_elements.keys()) |key| {
            if (!self.undefined_elements.contains(key)) {
                try self.undefined_elements.put(gpa, key, {});
                changed = true;
            }
        }
        changed = intersectPredicates(@TypeOf(self.scalar_values), &self.scalar_values, &other.scalar_values) or changed;
        index = 0;
        while (index < self.nonnegative_locals.count()) {
            const local = self.nonnegative_locals.keys()[index];
            if (!other.provesNonNegative(.{ .local = .{ .local = local } })) {
                _ = self.nonnegative_locals.swapRemoveAt(index);
                changed = true;
            } else index += 1;
        }
        return changed;
    }
};

fn elementNotOwnedBy(array: LocalId, key: ElementKey) bool {
    return key.array != array;
}

fn prefixNotOwnedBy(array: LocalId, key: PrefixKey) bool {
    return key.array != array;
}

fn prefixCounterIsNot(counter: LocalId, key: PrefixKey) bool {
    return key.counter != counter;
}

fn elementIsRetained(keep: []const u8, key: ElementKey) bool {
    return isRetained(keep, key.array);
}

fn copiedCounterTerm(term: IndexTerm, source: LocalId, target: LocalId) IndexTerm {
    return switch (term) {
        .local => |value| if (value.local == source)
            .{ .local = .{ .local = target, .offset = value.offset } }
        else
            term,
        else => term,
    };
}

fn prefixIsRetained(keep: []const u8, key: PrefixKey) bool {
    return isRetained(keep, key.array) and isRetained(keep, key.counter);
}

fn termNamesLocal(term: IndexTerm, local: LocalId) bool {
    return switch (term) {
        .local => |value| value.local == local,
        .field => |value| value.parent == local,
        else => false,
    };
}

fn termSupported(term: IndexTerm) bool {
    return switch (term) {
        .unknown => false,
        .constant => true,
        .local => |value| value.offset >= -1 and value.offset <= 1,
        .field => |value| value.offset >= -1 and value.offset <= 1,
    };
}

fn termEql(lhs: IndexTerm, rhs: IndexTerm) bool {
    return switch (lhs) {
        .unknown => rhs == .unknown,
        .constant => |value| rhs == .constant and value == rhs.constant,
        .local => |value| rhs == .local and value.local == rhs.local.local and
            value.offset == rhs.local.offset,
        .field => |value| rhs == .field and value.parent == rhs.field.parent and
            std.mem.eql(u8, value.name, rhs.field.name) and value.offset == rhs.field.offset,
    };
}

fn termSameBase(lhs: IndexTerm, rhs: IndexTerm) bool {
    return switch (lhs) {
        .local => |value| rhs == .local and value.local == rhs.local.local,
        .field => |value| rhs == .field and value.parent == rhs.field.parent and
            std.mem.eql(u8, value.name, rhs.field.name),
        else => false,
    };
}

fn termOffset(term: IndexTerm) i8 {
    return switch (term) {
        .local => |value| value.offset,
        .field => |value| value.offset,
        else => 0,
    };
}

fn comparisonEql(lhs: Comparison, rhs: Comparison) bool {
    return lhs.op == rhs.op and termEql(lhs.lhs, rhs.lhs) and termEql(lhs.rhs, rhs.rhs);
}

fn reverseComparison(comparison: Comparison) Comparison {
    return .{
        .lhs = comparison.rhs,
        .rhs = comparison.lhs,
        .op = switch (comparison.op) {
            .eq => .eq,
            .ne => .ne,
            .lt => .gt,
            .le => .ge,
            .gt => .lt,
            .ge => .le,
        },
    };
}

fn negateComparisonOp(op: @TypeOf(@as(Comparison, undefined).op)) @TypeOf(op) {
    return switch (op) {
        .eq => .ne,
        .ne => .eq,
        .lt => .ge,
        .le => .gt,
        .gt => .le,
        .ge => .lt,
    };
}

fn compareIntegers(lhs: i128, rhs: i128, op: @TypeOf(@as(Comparison, undefined).op)) bool {
    return switch (op) {
        .eq => lhs == rhs,
        .ne => lhs != rhs,
        .lt => lhs < rhs,
        .le => lhs <= rhs,
        .gt => lhs > rhs,
        .ge => lhs >= rhs,
    };
}

fn comparisonImplies(premise: Comparison, query: Comparison) bool {
    if (!(termSameBase(premise.lhs, query.lhs) or termEql(premise.lhs, query.lhs)) or
        !(termSameBase(premise.rhs, query.rhs) or termEql(premise.rhs, query.rhs))) return false;
    // Move offsets to the difference between the same two storage values.
    // Thus length<=count also proves length-1<count, without dropping the
    // separate nonnegative-index requirement.
    const shift = @as(i16, termOffset(query.lhs)) - termOffset(query.rhs) -
        (@as(i16, termOffset(premise.lhs)) - termOffset(premise.rhs));
    const bounds: TermBounds = switch (premise.op) {
        .eq => .{ .lower = shift, .upper = shift },
        .lt => .{ .upper = @as(i128, shift) - 1 },
        .le => .{ .upper = shift },
        .gt => .{ .lower = @as(i128, shift) + 1 },
        .ge => .{ .lower = shift },
        .ne => return shift == 0 and query.op == .ne,
    };
    return boundsProveComparison(bounds, .{ .lower = 0, .upper = 0 }, query.op);
}

fn boundsProveComparison(lhs: TermBounds, rhs: TermBounds, op: @TypeOf(@as(Comparison, undefined).op)) bool {
    if (!lhs.valid() or !rhs.valid()) return false;
    return switch (op) {
        .eq => blk: {
            const lhs_lower = lhs.lower orelse break :blk false;
            const lhs_upper = lhs.upper orelse break :blk false;
            const rhs_lower = rhs.lower orelse break :blk false;
            const rhs_upper = rhs.upper orelse break :blk false;
            break :blk lhs_lower == lhs_upper and rhs_lower == rhs_upper and lhs_lower == rhs_lower;
        },
        .ne => boundsProveComparison(lhs, rhs, .lt) or boundsProveComparison(lhs, rhs, .gt),
        .lt => if (lhs.upper) |upper| if (rhs.lower) |lower| upper < lower else false else false,
        .le => if (lhs.upper) |upper| if (rhs.lower) |lower| upper <= lower else false else false,
        .gt => if (lhs.lower) |lower| if (rhs.upper) |upper| lower > upper else false else false,
        .ge => if (lhs.lower) |lower| if (rhs.upper) |upper| lower >= upper else false else false,
    };
}

fn termIsRetained(keep: []const u8, term: IndexTerm) bool {
    return switch (term) {
        .local => |value| isRetained(keep, value.local),
        .field => |value| isRetained(keep, value.parent),
        else => false,
    };
}

fn retainLocal(keep: []u8, local: LocalId) bool {
    if (isRetained(keep, local)) return false;
    markRetained(keep, local);
    return true;
}

fn retainTerm(keep: []u8, term: IndexTerm) bool {
    return switch (term) {
        .local => |value| retainLocal(keep, value.local),
        .field => |value| retainLocal(keep, value.parent),
        else => false,
    };
}

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

fn fieldNotOwnedPayload(parent: LocalId, key: FieldKey) bool {
    return key.parent != parent or std.mem.eql(u8, key.name, "ptr") or std.mem.eql(u8, key.name, "len");
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

fn nextFieldPathByte(path: []const u8, index: *usize, quoted: *bool, escaped: *bool) ?u8 {
    while (index.* < path.len) {
        const byte = path[index.*];
        index.* += 1;
        if (!quoted.* and std.ascii.isWhitespace(byte)) continue;
        if (byte == '"' and !escaped.*) quoted.* = !quoted.*;
        const was_escaped = escaped.*;
        escaped.* = quoted.* and byte == '\\' and !was_escaped;
        return byte;
    }
    return null;
}

fn fieldPathPrefix(prefix: []const u8, path: []const u8) bool {
    if (prefix.len == 0) return true;
    var left: usize = 0;
    var right: usize = 0;
    var left_quoted = false;
    var right_quoted = false;
    var left_escaped = false;
    var right_escaped = false;
    while (nextFieldPathByte(prefix, &left, &left_quoted, &left_escaped)) |byte| {
        const actual = nextFieldPathByte(path, &right, &right_quoted, &right_escaped) orelse return false;
        if (actual != byte) return false;
    }
    const next = nextFieldPathByte(path, &right, &right_quoted, &right_escaped) orelse return true;
    return next == '.' or next == '[';
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
    std.debug.assert(self.integer_domains.len == other.integer_domains.len);
    std.debug.assert(self.integer_domains.len == 0 or self.integer_domains.ptr == other.integer_domains.ptr);
    // The predicate maps join on their own rule: a fact survives only
    // when BOTH paths carry it.  Nothing above or below may insert one.
    var changed = self.facts.joinFrom(&other.facts);
    changed = (try self.joinInitialization(other, gpa)) or changed;
    for (other.written_fields.keys()) |key| {
        if (!self.fieldBytesAreWritten(key.parent, key.name)) continue;
        const entry = try self.written_fields.getOrPutContext(gpa, key, .{});
        if (!entry.found_existing) changed = true;
    }
    var written_index: usize = 0;
    while (written_index < self.written_fields.count()) {
        const key = self.written_fields.keys()[written_index];
        if (!other.fieldBytesAreWritten(key.parent, key.name)) {
            _ = self.written_fields.swapRemoveAt(written_index);
            changed = true;
        } else written_index += 1;
    }
    for (other.may_undefined_values.keys()) |local| {
        const entry = try self.may_undefined_values.getOrPut(gpa, local);
        if (!entry.found_existing) changed = true;
    }
    for (other.undefined_field_values.keys()) |key| {
        const entry = try self.undefined_field_values.getOrPutContext(gpa, key, .{});
        if (!entry.found_existing) changed = true;
    }
    for (self.locals.keys(), self.locals.values()) |local, origin| {
        if (origin == .undef) {
            const entry = try self.may_undefined_values.getOrPut(gpa, local);
            if (!entry.found_existing) changed = true;
        }
    }
    for (other.locals.keys(), other.locals.values()) |local, origin| {
        if (origin == .undef) {
            const entry = try self.may_undefined_values.getOrPut(gpa, local);
            if (!entry.found_existing) changed = true;
        }
    }
    for (self.fields.keys(), self.fields.values()) |key, origin| {
        if (origin == .undef) {
            const entry = try self.undefined_field_values.getOrPutContext(gpa, key, .{});
            if (!entry.found_existing) changed = true;
        }
    }
    for (other.fields.keys(), other.fields.values()) |key, origin| {
        if (origin == .undef) {
            const entry = try self.undefined_field_values.getOrPutContext(gpa, key, .{});
            if (!entry.found_existing) changed = true;
        }
    }
    // Physical field origins join by union below. They cannot certify a
    // selected opaque payload unless that field was defined on both paths.
    // ArrayHashMap appends without reordering old keys here. Retain the
    // incoming boundary so first-loop negatives cannot poison second-loop
    // common descendant proofs. No certificate snapshot allocation is needed.
    const incoming_negative_count = self.unknown_field_values.count();
    if (other.unknown_values.count() != 0) {
        for (self.fields.keys()) |key| {
            if (other.unknown_values.contains(key.parent) and !other.fieldValueIsDefined(key.parent, key.name)) {
                const entry = try self.unknown_field_values.getOrPutContext(gpa, key, .{});
                if (!entry.found_existing) changed = true;
            }
        }
    }
    if (self.unknown_values.count() != 0) {
        for (other.fields.keys()) |key| {
            if (self.unknown_values.contains(key.parent) and
                !self.fieldValueIsDefinedWithLimit(key.parent, key.name, incoming_negative_count, false, true))
            {
                const entry = try self.unknown_field_values.getOrPutContext(gpa, key, .{});
                if (!entry.found_existing) changed = true;
            }
        }
    }
    for (other.unknown_field_values.keys()) |key| {
        const entry = try self.unknown_field_values.getOrPutContext(gpa, key, .{});
        if (!entry.found_existing) changed = true;
    }
    for (other.unknown_values.keys()) |local| {
        const entry = try self.unknown_values.getOrPut(gpa, local);
        if (!entry.found_existing) changed = true;
    }

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

/// Fill every owned map and the comparison list, then clone under a failing
/// allocator to exercise partial construction and cleanup.
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
    try src.unknown_field_values.putContext(gpa, .{ .parent = local, .name = "bytes" }, {}, .{});
    try src.unknown_values.put(gpa, local, {});
    try src.facts.bindBoolean(gpa, @enumFromInt(1), true);
    _ = try src.facts.assumeGuard(gpa, @enumFromInt(0), true);
    const array: LocalId = @enumFromInt(2);
    const counter: LocalId = @enumFromInt(3);
    try src.setExactElement(gpa, array, 0, true);
    try src.markArrayComplete(gpa, @enumFromInt(4));
    try src.setExactElement(gpa, @enumFromInt(4), 1, false);
    try src.setScalarValue(gpa, counter, 0);
    try src.setSymbolicPrefix(gpa, array, counter, 0, 16);
    _ = try src.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = @enumFromInt(5) } },
        .rhs = .{ .constant = 16 },
        .op = .lt,
    });

    // A clone that dies partway through owns every map it had already
    // refilled through its errdefer.  The failure propagates so the
    // sweep below counts this allocation point as failed and moves on
    // to the next one.
    var copy = try src.clone(gpa);
    defer copy.deinit(gpa);
    // And a clone that succeeds is mergeable with its source, which is
    // only true when the fact maps came across too.
    try std.testing.expect(src.canMerge(&copy));
    // Payload consumers must remain conservative in the independently owned copy.
    try std.testing.expect(!copy.fieldValueIsDefined(local, "bytes"));
    copy.forgetFields(local);
    try std.testing.expect(copy.fieldValueIsDefined(local, "bytes"));
    try std.testing.expect(!src.fieldValueIsDefined(local, "bytes"));

    _ = try join(&copy, &src, gpa);
    try std.testing.expect(!copy.fieldValueIsDefined(local, "bytes"));
    var keep = [_]u8{1};
    const live_out = [_]u8{1};
    var heaps: std.ArrayListUnmanaged(u32) = .empty;
    defer heaps.deinit(gpa);
    var arenas: std.ArrayListUnmanaged(u32) = .empty;
    defer arenas.deinit(gpa);
    try copy.project(gpa, &keep, &live_out, &heaps, &arenas);
    try std.testing.expect(!copy.fieldValueIsDefined(local, "bytes"));
    @memset(&keep, 0);
    try copy.project(gpa, &keep, &.{0}, &heaps, &arenas);
    try std.testing.expect(copy.fieldValueIsDefined(local, "bytes"));
}

test "clone: a failure partway through leaves nothing allocated" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, cloneOneEntryPerMap, .{});
}

// Initialization facts must remain sparse even for a very large fixed extent.
test "initialization: exact stores preserve gaps and undefined holes" {
    const gpa = std.testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    const array: LocalId = @enumFromInt(0);
    try state.setFixedPrefix(gpa, array, 0);
    try state.setExactElement(gpa, array, 2, true);
    try std.testing.expect(state.hasExactElement(array, 2));
    try std.testing.expect(!state.hasInitializedElement(array, .{ .constant = 0 }));
    try std.testing.expect(!state.hasInitializedPrefix(array, std.math.maxInt(u64)));
    try state.markArrayComplete(gpa, array);
    try state.setExactElement(gpa, array, 0, false);
    try std.testing.expect(state.baseComplete(array));
    try std.testing.expect(!state.isArrayComplete(array));
    try std.testing.expect(state.hasInitializedElement(array, .{ .constant = 1 }));
    try std.testing.expect(!state.hasInitializedElement(array, .{ .constant = 0 }));
    try std.testing.expect(!state.hasInitializedPrefix(array, 2));
    try state.setExactElement(gpa, array, 0, true);
    try std.testing.expect(state.isArrayComplete(array));
}

// An exclusive prefix does not credit its endpoint or an unguarded negative index.
test "initialization: affine prefix bounds and guarded counter steps" {
    const gpa = std.testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const index: LocalId = @enumFromInt(2);
    try state.setSymbolicPrefix(gpa, array, count, 0, 16);
    try std.testing.expect(!state.hasInitializedElement(array, .{ .local = .{ .local = count } }));
    try std.testing.expect(!state.hasInitializedElement(array, .{ .local = .{ .local = count, .offset = -1 } }));
    try std.testing.expect(try state.assumeComparison(gpa, .{
        .lhs = .{ .constant = 0 },
        .rhs = .{ .local = .{ .local = count } },
        .op = .lt,
    }));
    try std.testing.expect(state.hasInitializedElement(array, .{ .local = .{ .local = count, .offset = -1 } }));
    try std.testing.expect(try state.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = count } },
        .rhs = .{ .constant = 16 },
        .op = .ne,
    }));
    try std.testing.expect(state.provesIndexInBounds(.{ .local = .{ .local = count } }, 16));
    try state.setScalarValue(gpa, index, 0);
    try std.testing.expect(try state.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = count } },
        .rhs = .{ .local = .{ .local = index } },
        .op = .gt,
    }));
    try std.testing.expect(state.hasInitializedElement(array, .{ .local = .{ .local = index } }));
    state.forgetInitializationLocal(index);
    try std.testing.expect(!state.hasInitializedElement(array, .{ .local = .{ .local = index } }));
    try state.stepCounter(gpa, count, -1);
    try std.testing.expectEqual(@as(?i8, 1), state.symbolicPrefixOffset(array, count));
    try std.testing.expect(state.hasInitializedElement(array, .{ .local = .{ .local = count } }));
}

test "initialization: scaled slice prefixes retain lane bounds through joins and revoke on mutation" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const index: LocalId = @enumFromInt(2);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.setScaledSymbolicPrefix(gpa, array, count, 2, 8);
    try state.setScalarValue(gpa, index, 0);
    try std.testing.expect(try state.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = index } },
        .rhs = .{ .local = .{ .local = count } },
        .op = .lt,
    }));
    try std.testing.expect(state.hasInitializedScaledElement(array, .{ .index = index, .scale = 2 }));
    try std.testing.expect(state.hasInitializedScaledElement(array, .{ .index = index, .scale = 2, .offset = 1 }));
    try std.testing.expect(!state.hasInitializedScaledElement(array, .{ .index = count, .scale = 2 }));
    try std.testing.expect(!state.hasInitializedScaledElement(array, .{ .index = index, .scale = 3 }));
    var mirror = try state.clone(gpa);
    defer mirror.deinit(gpa);
    _ = try join(&state, &mirror, gpa);
    try std.testing.expect(state.hasInitializedScaledElement(array, .{ .index = index, .scale = 2, .offset = 1 }));
    try state.stepCounter(gpa, count, -1);
    try std.testing.expect(!state.hasInitializedScaledElement(array, .{ .index = index, .scale = 2 }));
}

test "initialization: unequal scaled prefixes do not survive an intersection" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    try lhs.setScaledSymbolicPrefix(gpa, array, count, 2, 8);
    try rhs.setScaledSymbolicPrefix(gpa, array, count, 3, 8);
    _ = try join(&lhs, &rhs, gpa);
    try std.testing.expectEqual(@as(usize, 0), lhs.symbolic_prefixes.count());
}

// The zero-count entry path entails an empty prefix at the loop header.
test "initialization: join synthesizes inductive prefix and unions complete holes" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    var entry: AbstractState = .{};
    defer entry.deinit(gpa);
    try entry.setFixedPrefix(gpa, array, 0);
    try entry.setScalarValue(gpa, count, 0);
    var back: AbstractState = .{};
    defer back.deinit(gpa);
    try back.setSymbolicPrefix(gpa, array, count, 0, 16);
    _ = try join(&entry, &back, gpa);
    try std.testing.expectEqual(@as(?i8, 0), entry.symbolicPrefixOffset(array, count));
    try std.testing.expectEqual(@as(?u64, null), entry.scalarValue(count));
    try entry.markArrayComplete(gpa, array);
    try back.markArrayComplete(gpa, array);
    try entry.setExactElement(gpa, array, 0, false);
    try back.setExactElement(gpa, array, 1, false);
    _ = try join(&entry, &back, gpa);
    try std.testing.expect(!entry.hasInitializedElement(array, .{ .constant = 0 }));
    try std.testing.expect(!entry.hasInitializedElement(array, .{ .constant = 1 }));
    try std.testing.expect(entry.hasInitializedElement(array, .{ .constant = 2 }));
}

test "initialization: join keeps bounds entailed by different scalar facts" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const term: IndexTerm = .{ .local = .{ .local = count } };
    for ([_]@TypeOf(@as(Comparison, undefined).op){ .lt, .ne }) |op| {
        var first: AbstractState = .{};
        defer first.deinit(gpa);
        try first.setScalarValue(gpa, count, 0);
        try first.setFixedPrefix(gpa, array, 0);
        var later: AbstractState = .{};
        defer later.deinit(gpa);
        try later.setSymbolicPrefix(gpa, array, count, 0, 2);
        const guard: Comparison = .{ .lhs = term, .rhs = .{ .constant = 2 }, .op = op };
        try std.testing.expect(try later.assumeComparison(gpa, guard));
        _ = try join(&first, &later, gpa);
        try std.testing.expectEqual(@as(?u64, null), first.scalarValue(count));
        try std.testing.expect(first.provesComparison(guard));
        try std.testing.expect(first.provesComparison(.{ .lhs = term, .rhs = .{ .constant = 2 }, .op = .lt }));
        _ = try join(&later, &first, gpa);
        try std.testing.expect(later.provesComparison(guard));
    }
}

// Cloning and projection retain dependencies without sharing mutable fact storage.
test "initialization: clone projection and alias invalidation" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const index: LocalId = @enumFromInt(2);
    var source: AbstractState = .{};
    defer source.deinit(gpa);
    try source.setSymbolicPrefix(gpa, array, count, 0, 16);
    try source.setScalarValue(gpa, index, 0);
    _ = try source.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = index } },
        .rhs = .{ .local = .{ .local = count } },
        .op = .lt,
    });
    var copy = try source.clone(gpa);
    defer copy.deinit(gpa);
    var keep = [_]u8{1};
    const out = [_]u8{0};
    var heaps: std.ArrayListUnmanaged(u32) = .empty;
    defer heaps.deinit(gpa);
    var arenas: std.ArrayListUnmanaged(u32) = .empty;
    defer arenas.deinit(gpa);
    try copy.project(gpa, &keep, &out, &heaps, &arenas);
    try std.testing.expect(isRetained(&keep, count));
    try std.testing.expect(isRetained(&keep, index));
    try std.testing.expect(copy.hasInitializedElement(array, .{ .local = .{ .local = index } }));
    copy.forgetInitializationArray(array);
    copy.forgetInitializationLocal(count);
    try std.testing.expect(!copy.hasInitializedElement(array, .{ .constant = 0 }));
    try std.testing.expect(source.hasInitializedElement(array, .{ .local = .{ .local = index } }));
}

test "initialization: copied counters retain independent guarded-pop prefixes" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const depth: LocalId = @enumFromInt(1);
    const cursor: LocalId = @enumFromInt(2);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.setSymbolicPrefix(gpa, array, depth, 0, 64);
    try state.copyCounterValue(gpa, cursor, depth);
    const cursor_term: IndexTerm = .{ .local = .{ .local = cursor } };
    for (0..2) |_| {
        try std.testing.expect(try state.assumeComparison(gpa, .{ .lhs = cursor_term, .rhs = .{ .constant = 0 }, .op = .gt }));
        try state.stepCounter(gpa, cursor, -1);
        try std.testing.expect(state.hasInitializedElement(array, cursor_term));
    }
    state.forgetInitializationLocal(depth);
    try std.testing.expect(state.hasInitializedElement(array, cursor_term));
}

test "initialization: guarded unsigned field offsets retain prefix and lower bounds" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const entry: LocalId = @enumFromInt(2);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.setSymbolicPrefix(gpa, array, count, 0, 64);
    const field: IndexTerm = .{ .field = .{ .parent = entry, .name = "length", .is_unsigned = true } };
    try std.testing.expect(try state.assumeComparison(gpa, .{ .lhs = field, .rhs = .{ .local = .{ .local = count } }, .op = .le }));
    try std.testing.expect(try state.assumeComparison(gpa, .{ .lhs = field, .rhs = .{ .constant = 0 }, .op = .ne }));
    const index: IndexTerm = .{ .field = .{ .parent = entry, .name = "length", .offset = -1 } };
    try std.testing.expect(state.provesIndexInBounds(index, 64));
    try std.testing.expect(state.hasInitializedElement(array, index));
    state.forgetInitializationLocal(entry);
    try std.testing.expect(!state.hasInitializedElement(array, index));
}

test "initialization: saturated push paths retain only a capacity-clipped prefix" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const term: IndexTerm = .{ .local = .{ .local = count } };
    var stored: AbstractState = .{};
    defer stored.deinit(gpa);
    try stored.setScalarValue(gpa, count, 0);
    try stored.setSymbolicPrefix(gpa, array, count, 1, 2);
    var saturated: AbstractState = .{};
    defer saturated.deinit(gpa);
    try saturated.setSymbolicPrefix(gpa, array, count, 0, 2);
    try std.testing.expect(try saturated.assumeComparison(gpa, .{ .lhs = term, .rhs = .{ .constant = 2 }, .op = .ge }));
    _ = try join(&stored, &saturated, gpa);
    try std.testing.expect(stored.symbolic_prefixes.values()[0].capped);
    try std.testing.expectEqual(@as(?i8, 1), stored.symbolicPrefixOffset(array, count));
    try stored.stepCounter(gpa, count, 1);
    try std.testing.expect(!stored.provesIndexInBounds(term, 2));
    var entry: AbstractState = .{};
    defer entry.deinit(gpa);
    try entry.setScalarValue(gpa, count, 0);
    try entry.setFixedPrefix(gpa, array, 0);
    _ = try join(&entry, &stored, gpa);
    try std.testing.expect(!entry.hasInitializedElement(array, .{ .constant = 0 }));
    try std.testing.expect(try entry.assumeComparison(gpa, .{ .lhs = term, .rhs = .{ .constant = 0 }, .op = .gt }));
    try std.testing.expect(entry.hasInitializedElement(array, .{ .constant = 0 }));
    try std.testing.expect(!entry.hasInitializedElement(array, .{ .constant = 2 }));
}

// A missing store or an extra increment leaves a real gap at the prefix boundary.
test "initialization: skipped stores and unsupported counter changes revoke proofs" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.setScalarValue(gpa, count, 0);
    try state.setSymbolicPrefix(gpa, array, count, 0, 8);
    try state.stepCounter(gpa, count, 1);
    try std.testing.expectEqual(@as(?i8, -1), state.symbolicPrefixOffset(array, count));
    try std.testing.expect(!state.hasInitializedElement(array, .{ .constant = 0 }));
    try state.stepCounter(gpa, count, 1);
    try std.testing.expectEqual(@as(?i8, null), state.symbolicPrefixOffset(array, count));
    try state.setSymbolicPrefix(gpa, array, count, 0, 8);
    try state.stepCounter(gpa, count, 2);
    try std.testing.expectEqual(@as(?i8, null), state.symbolicPrefixOffset(array, count));
    try std.testing.expectEqual(@as(?u64, null), state.scalarValue(count));
}

// Decrementing a possibly empty count must not manufacture initialized slots.
test "initialization: unguarded pop drops its affine coverage" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.setSymbolicPrefix(gpa, array, count, 0, 8);
    try state.stepCounter(gpa, count, -1);
    try std.testing.expectEqual(@as(?i8, null), state.symbolicPrefixOffset(array, count));
    try std.testing.expect(!state.hasInitializedElement(array, .{ .local = .{ .local = count } }));
}

// Independent branch writes are intersected; neither path fills the other's gap.
test "initialization: joins intersect sparse stores and weaken fixed prefixes" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    var lhs: AbstractState = .{};
    defer lhs.deinit(gpa);
    var rhs: AbstractState = .{};
    defer rhs.deinit(gpa);
    try lhs.setExactElement(gpa, array, 0, true);
    try lhs.setExactElement(gpa, array, 1, true);
    try rhs.setExactElement(gpa, array, 1, true);
    _ = try join(&lhs, &rhs, gpa);
    try std.testing.expectEqual(@as(u64, 0), lhs.fixedPrefix(array));
    try std.testing.expect(!lhs.hasExactElement(array, 0));
    try std.testing.expect(lhs.hasExactElement(array, 1));
    try std.testing.expect(!lhs.hasInitializedPrefix(array, 2));
}

// A dynamic selected read needs a proof that it cannot select an undefined hole.
test "initialization: dynamic holes require exclusion and completion clears holes" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const index: LocalId = @enumFromInt(1);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.markArrayComplete(gpa, array);
    try state.setExactElement(gpa, array, 1, false);
    _ = try state.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = index } },
        .rhs = .{ .constant = 0 },
        .op = .ge,
    });
    try std.testing.expect(!state.hasInitializedElement(array, .{ .local = .{ .local = index } }));
    _ = try state.assumeComparison(gpa, .{
        .lhs = .{ .constant = 1 },
        .rhs = .{ .local = .{ .local = index } },
        .op = .ne,
    });
    try std.testing.expect(state.hasInitializedElement(array, .{ .local = .{ .local = index } }));
    try state.markArrayComplete(gpa, array);
    try std.testing.expect(state.isArrayComplete(array));
    state.forgetInitializationArray(array);
    try std.testing.expect(!state.hasInitializedElement(array, .{ .constant = 2 }));
}

// Reversed conditions and their negated successors retain the same bounded premise.
test "initialization: reversed guards and contradictions" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.setSymbolicPrefix(gpa, array, count, 0, 16);
    try std.testing.expect(try state.assumeComparison(gpa, .{
        .lhs = .{ .constant = 16 },
        .rhs = .{ .local = .{ .local = count } },
        .op = .ne,
    }));
    try std.testing.expect(state.provesLessThan(.{ .local = .{ .local = count } }, .{ .constant = 16 }));
    try std.testing.expect(!try state.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = count } },
        .rhs = .{ .constant = 16 },
        .op = .ge,
    }));
    state.forgetAllComparisons();
    try std.testing.expect(try state.assumeComparison(gpa, .{
        .lhs = .{ .constant = 16 },
        .rhs = .{ .local = .{ .local = count } },
        .op = .le,
    }));
    try std.testing.expect(state.hasInitializedPrefix(array, 16));
    try std.testing.expect(!state.hasInitializedPrefix(array, 17));
}

// Projection drops wholly unobserved initialization maps while retaining Origin rules.
test "initialization: dead coverage keys are projected away" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.setExactElement(gpa, array, 0, true);
    try state.setScalarValue(gpa, count, 0);
    try state.setSymbolicPrefix(gpa, array, count, 0, 8);
    var keep = [_]u8{0};
    var heaps: std.ArrayListUnmanaged(u32) = .empty;
    defer heaps.deinit(gpa);
    var arenas: std.ArrayListUnmanaged(u32) = .empty;
    defer arenas.deinit(gpa);
    try std.testing.expect(!state.projectionIsIdentity(&keep, &keep));
    try state.project(gpa, &keep, &keep, &heaps, &arenas);
    try std.testing.expectEqual(@as(usize, 0), state.exact_elements.count());
    try std.testing.expectEqual(@as(usize, 0), state.fixed_prefixes.count());
    try std.testing.expectEqual(@as(usize, 0), state.symbolic_prefixes.count());
    try std.testing.expectEqual(@as(usize, 0), state.scalar_values.count());
}

// The else successor of count==0 supplies count!=0, not a syntactic count>0.
test "initialization: negated zero guard proves a nonnegative previous slot" {
    const gpa = std.testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.setSymbolicPrefix(gpa, array, count, 0, 16);
    _ = try state.assumeComparison(gpa, .{
        .lhs = .{ .local = .{ .local = count } },
        .rhs = .{ .constant = 0 },
        .op = .ne,
    });
    try std.testing.expect(state.provesCounterPositive(count));
    try std.testing.expect(state.hasInitializedElement(array, .{
        .local = .{ .local = count, .offset = -1 },
    }));
}

test "integer domains: supported endpoints and unbounded widths stay conservative" {
    const domains = [_]IntegerDomain{
        .{ .kind = .unsigned, .bits = 0 },
        .{ .kind = .signed, .bits = 0 },
        .{ .kind = .unsigned, .bits = 1 },
        .{ .kind = .unsigned, .bits = 2 },
        .{ .kind = .signed, .bits = 2 },
        .{ .kind = .unsigned, .bits = 63 },
        .{ .kind = .unsigned, .bits = 64 },
        .{ .kind = .unsigned_unbounded },
        .{},
    };
    var state: AbstractState = .{ .integer_domains = &domains };
    defer state.deinit(std.testing.allocator);
    for ([_]u32{ 0, 1 }) |id| {
        try std.testing.expect(state.provesIndexInBounds(.{ .local = .{ .local = @enumFromInt(id) } }, 1));
    }
    try std.testing.expect(state.provesIndexInBounds(.{ .local = .{ .local = @enumFromInt(2) } }, 2));
    try std.testing.expect(!state.provesIndexInBounds(.{ .local = .{ .local = @enumFromInt(3) } }, 2));
    try std.testing.expect(!state.provesNonNegative(.{ .local = .{ .local = @enumFromInt(4) } }));
    try std.testing.expect(state.provesIndexInBounds(.{ .local = .{ .local = @enumFromInt(5) } }, @as(u64, 1) << 63));
    for ([_]u32{ 6, 7, 8 }) |id| {
        try std.testing.expect(!state.provesIndexInBounds(.{ .local = .{ .local = @enumFromInt(id) } }, std.math.maxInt(u64)));
    }
    try std.testing.expect(state.termBounds(.{ .local = .{ .local = @enumFromInt(7) } }).upper == null);
    try std.testing.expect(state.termBounds(.{ .local = .{ .local = @enumFromInt(8) } }).lower == null);
    try std.testing.expect(!state.provesNonNegative(.{ .local = .{ .local = @enumFromInt(2), .offset = -1 } }));
    try std.testing.expect(state.provesIndexInBounds(.{ .local = .{ .local = @enumFromInt(2), .offset = 1 } }, 3));
}

test "integer domains: widening copies snapshot values and forget mutations" {
    const gpa = std.testing.allocator;
    const domains = [_]IntegerDomain{
        .{ .kind = .unsigned, .bits = 1 },
        .{ .kind = .unsigned, .bits = 64 },
    };
    const source: LocalId = @enumFromInt(0);
    const dest: LocalId = @enumFromInt(1);
    var state: AbstractState = .{ .integer_domains = &domains };
    defer state.deinit(gpa);
    try state.copyCounterValue(gpa, dest, source);
    state.forgetInitializationLocal(source);
    try std.testing.expect(state.provesIndexInBounds(.{ .local = .{ .local = dest } }, 2));
    var cloned = try state.clone(gpa);
    defer cloned.deinit(gpa);
    state.forgetInitializationLocal(dest);
    try std.testing.expect(!state.provesIndexInBounds(.{ .local = .{ .local = dest } }, 2));
    try std.testing.expect(cloned.provesIndexInBounds(.{ .local = .{ .local = dest } }, 2));
    _ = try join(&cloned, &state, gpa);
    try std.testing.expect(!cloned.provesIndexInBounds(.{ .local = .{ .local = dest } }, 2));
    try std.testing.expect(cloned.provesIndexInBounds(.{ .local = .{ .local = source } }, 2));
    var keep = [_]u8{0};
    var heaps: std.ArrayListUnmanaged(u32) = .empty;
    defer heaps.deinit(gpa);
    var arenas: std.ArrayListUnmanaged(u32) = .empty;
    defer arenas.deinit(gpa);
    try cloned.project(gpa, &keep, &keep, &heaps, &arenas);
    try std.testing.expect(cloned.projectionIsIdentity(&keep, &keep));
    try std.testing.expect(cloned.provesIndexInBounds(.{ .local = .{ .local = source } }, 2));
}

test "integer domains: contradictory intervals do not invent finite proofs" {
    const gpa = std.testing.allocator;
    const domains = [_]IntegerDomain{.{ .kind = .unsigned, .bits = 1 }};
    const term: IndexTerm = .{ .local = .{ .local = @enumFromInt(0) } };
    var state: AbstractState = .{ .integer_domains = &domains };
    defer state.deinit(gpa);
    try state.comparisons.append(gpa, .{ .lhs = term, .rhs = .{ .constant = 4 }, .op = .ge });
    try std.testing.expect(!state.provesNonNegative(term));
    try std.testing.expect(!state.provesLessThan(term, .{ .constant = 2 }));
}

test "integer domains: zero equality and guarded endpoint exclusions" {
    const gpa = std.testing.allocator;
    const domains = [_]IntegerDomain{
        .{ .kind = .signed, .bits = 0 },
        .{ .kind = .unsigned, .bits = 1 },
        .{ .kind = .signed, .bits = 64 },
    };
    var state: AbstractState = .{ .integer_domains = &domains };
    defer state.deinit(gpa);
    const zero: IndexTerm = .{ .local = .{ .local = @enumFromInt(0) } };
    const bit: IndexTerm = .{ .local = .{ .local = @enumFromInt(1) } };
    try std.testing.expect(state.provesComparison(.{ .lhs = zero, .rhs = .{ .constant = 0 }, .op = .eq }));
    try std.testing.expect(!state.provesComparison(.{ .lhs = zero, .rhs = .{ .constant = 0 }, .op = .ne }));
    try std.testing.expect(try state.assumeComparison(gpa, .{ .lhs = bit, .rhs = .{ .constant = 0 }, .op = .ne }));
    try std.testing.expect(state.provesComparison(.{ .lhs = bit, .rhs = .{ .constant = 1 }, .op = .eq }));
    try std.testing.expect(!try state.assumeComparison(gpa, .{ .lhs = bit, .rhs = .{ .constant = 1 }, .op = .ne }));
    const signed = state.termBounds(.{ .local = .{ .local = @enumFromInt(2) } });
    try std.testing.expectEqual(@as(?i128, std.math.minInt(i64)), signed.lower);
    try std.testing.expectEqual(@as(?i128, std.math.maxInt(i64)), signed.upper);
}

test "integer domains: reusable scratch follows source context and survives source teardown" {
    const gpa = std.testing.allocator;
    const narrow = [_]IntegerDomain{.{ .kind = .unsigned, .bits = 1 }};
    const wide = [_]IntegerDomain{.{ .kind = .unsigned, .bits = 2 }};
    const term: IndexTerm = .{ .local = .{ .local = @enumFromInt(0) } };
    var scratch: AbstractState = .{};
    defer scratch.deinit(gpa);
    {
        var source: AbstractState = .{ .integer_domains = &narrow };
        defer source.deinit(gpa);
        try source.locals.put(gpa, @enumFromInt(0), .plain);
        try scratch.cloneFrom(&source, gpa);
    }
    try std.testing.expect(scratch.provesIndexInBounds(term, 2));
    {
        var source: AbstractState = .{ .integer_domains = &wide };
        defer source.deinit(gpa);
        try scratch.cloneFrom(&source, gpa);
    }
    try std.testing.expect(!scratch.provesIndexInBounds(term, 2));
    const unknown: AbstractState = .{};
    try scratch.cloneFrom(&unknown, gpa);
    try std.testing.expect(!scratch.provesNonNegative(term));
}

test "integer domains: affine endpoint overflow loses only the unavailable endpoint" {
    const maximum: TermBounds = .{ .lower = std.math.maxInt(i128), .upper = std.math.maxInt(i128) };
    const shifted = maximum.offset(1);
    try std.testing.expect(!boundsProveComparison(shifted, .{ .lower = 0, .upper = 0 }, .ge));
    try std.testing.expect(!boundsProveComparison(shifted, .{ .lower = 2, .upper = 2 }, .lt));
    const lower: TermBounds = .{ .lower = 0 };
    try std.testing.expect(boundsProveComparison(lower.offset(1), .{ .lower = 0, .upper = 0 }, .gt));
}

test "integer domains: wide signed identity contributes neither endpoint" {
    const domains = [_]IntegerDomain{.{ .kind = .signed_unbounded }};
    var state: AbstractState = .{ .integer_domains = &domains };
    defer state.deinit(std.testing.allocator);
    const term: IndexTerm = .{ .local = .{ .local = @enumFromInt(0) } };
    try std.testing.expect(!state.provesNonNegative(term));
    try std.testing.expect(!state.provesLessThan(term, .{ .constant = std.math.maxInt(u64) }));
    try std.testing.expect(state.termBounds(term).lower == null);
    try std.testing.expect(state.termBounds(term).upper == null);
}
