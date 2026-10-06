//! Layer 2 abstract state.
//!
//! Each value carries an `Origin` tagging where its lifetime is bound;
//! the state tracks which arenas are still live.  Use-validity is a
//! lookup, not a borrow-graph traversal.
//!
//! Algorithm: worklist fixed-point over a CFG, with `join` conservatively
//! combining states at merge points.

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
    /// takes-ownership call took it).  Used by transferFieldUse to
    /// fire parent-liveness ONLY for inter-procedural frees —
    /// regular alloc+free in same fn shouldn't propagate to fields
    /// (the field's own tracking handles that, and back-edge state
    /// in loops would otherwise cascade FPs).
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

// ── AbstractState ──────────────────────────────────────────

pub const AbstractState = struct {
    feasible: bool = true,
    booleans: std.AutoArrayHashMapUnmanaged(LocalId, bool) = .empty,

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
        self.booleans.deinit(gpa);
        self.locals.deinit(gpa);
        self.arenas.deinit(gpa);
        self.heaps.deinit(gpa);
        self.fields.deinit(gpa);
        self.out_param_writes.deinit(gpa);
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
        self.booleans.clearRetainingCapacity();
        try self.booleans.ensureTotalCapacity(gpa, src.booleans.count());
        for (src.booleans.keys(), src.booleans.values()) |key, value| {
            self.booleans.putAssumeCapacity(key, value);
        }
        self.locals.clearRetainingCapacity();
        try self.locals.ensureTotalCapacity(gpa, src.locals.count());
        for (src.locals.keys(), src.locals.values()) |k, v| {
            self.locals.putAssumeCapacity(k, v);
        }
        self.arenas.clearRetainingCapacity();
        try self.arenas.ensureTotalCapacity(gpa, src.arenas.count());
        for (src.arenas.keys(), src.arenas.values()) |k, v| {
            self.arenas.putAssumeCapacity(k, v);
        }
        self.heaps.clearRetainingCapacity();
        try self.heaps.ensureTotalCapacity(gpa, src.heaps.count());
        for (src.heaps.keys(), src.heaps.values()) |k, v| {
            self.heaps.putAssumeCapacity(k, v);
        }
        self.fields.clearRetainingCapacity();
        try self.fields.ensureTotalCapacity(gpa, src.fields.count());
        for (src.fields.keys(), src.fields.values()) |k, v| {
            self.fields.putAssumeCapacityContext(k, v, .{});
        }
        self.out_param_writes.clearRetainingCapacity();
        try self.out_param_writes.ensureTotalCapacity(gpa, src.out_param_writes.count());
        for (src.out_param_writes.keys(), src.out_param_writes.values()) |k, v| {
            self.out_param_writes.putAssumeCapacity(k, v);
        }
    }

    /// Join path predicates only when their union is exact, or the predicates
    /// are identical. Distinct resource histories then remain correlated.
    pub fn canMerge(self: *const AbstractState, other: *const AbstractState) bool {
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
        if (different == 0 and only_self == 0 and only_other == 0) return true;
        if (!self.sameResources(other)) return false;
        return (different == 0 and (only_self == 0 or only_other == 0)) or
            (different == 1 and only_self == 0 and only_other == 0);
    }

    fn sameResources(self: *const AbstractState, other: *const AbstractState) bool {
        if (self.locals.count() != other.locals.count() or
            self.arenas.count() != other.arenas.count() or
            self.heaps.count() != other.heaps.count() or
            self.fields.count() != other.fields.count() or
            self.out_param_writes.count() != other.out_param_writes.count()) return false;
        for (self.locals.keys(), self.locals.values()) |key, value| {
            if (!value.eql(other.locals.get(key) orelse return false)) return false;
        }
        for (self.arenas.keys(), self.arenas.values()) |key, value| {
            if (!std.meta.eql(value, other.arenas.get(key) orelse return false)) return false;
        }
        for (self.heaps.keys(), self.heaps.values()) |key, value| {
            if (!std.meta.eql(value, other.heaps.get(key) orelse return false)) return false;
        }
        for (self.fields.keys(), self.fields.values()) |key, value| {
            if (!value.eql(other.fields.get(key) orelse return false)) return false;
        }
        for (self.out_param_writes.keys(), self.out_param_writes.values()) |key, value| {
            if (value != (other.out_param_writes.get(key) orelse return false)) return false;
        }
        return true;
    }
};

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
    var changed = false;
    std.debug.assert(self.feasible);
    std.debug.assert(other.feasible);
    var boolean_index: usize = 0;
    while (boolean_index < self.booleans.count()) {
        const key = self.booleans.keys()[boolean_index];
        if (other.booleans.get(key) != self.booleans.values()[boolean_index]) {
            self.booleans.swapRemoveAt(boolean_index);
            changed = true;
        } else boolean_index += 1;
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
