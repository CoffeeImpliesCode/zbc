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
/// Ordinary reports use the rule and primary source byte. Returned stack
/// cells also carry the physical owner's declaration byte, so distinct
/// owners at one return remain distinct findings. Context compares rule
/// bytes, never message text or a Problem's raw representation.
///
/// The rule id in a key is BORROWED, never copied.  A report's rule id
/// is a `comptime` parameter, so it is a string literal with static
/// lifetime; an adopted one is `Problem.rule_id`, which the module
/// already requires to outlive the findings carrying it, because
/// `Problem.deinit` never frees it.  Both outlive this memo, whose
/// lifetime ends inside the `check` call that owns the list.
pub const Seen = struct {
    const Key = struct { rule_id: []const u8, byte: u32, owner_byte: ?u32 = null };

    keys: std.ArrayHashMapUnmanaged(Key, void, Context, true) = .empty,
    /// Diagnostic paths outlive all replay states, but not this check.
    byte_paths: std.StringHashMapUnmanaged(void) = .empty,
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
            const site_hash = std.hash.Wyhash.hash(
                std.hash_map.hashString(key.rule_id),
                std.mem.asBytes(&key.byte),
            );
            const owner: u64 = if (key.owner_byte) |byte| @as(u64, byte) + 1 else 0;
            return @truncate(std.hash.Wyhash.hash(site_hash, std.mem.asBytes(&owner)));
        }

        pub fn eql(_: Context, a: Key, b: Key, _: usize) bool {
            return a.byte == b.byte and a.owner_byte == b.owner_byte and std.mem.eql(u8, a.rule_id, b.rule_id);
        }
    };

    pub fn init() Seen {
        return .{};
    }

    pub fn deinit(self: *Seen, gpa: std.mem.Allocator) void {
        self.keys.deinit(gpa);
        var paths = self.byte_paths.iterator();
        while (paths.next()) |entry| gpa.free(entry.key_ptr.*);
        self.byte_paths.deinit(gpa);
    }

    const BytePathParts = struct { prefix: []const u8, suffix: []const u8, separator: bool };
    const BytePathContext = struct {
        pub fn hash(_: BytePathContext, parts: BytePathParts) u64 {
            var hasher = std.hash.Wyhash.init(0);
            hasher.update(parts.prefix);
            if (parts.separator) hasher.update(".");
            hasher.update(parts.suffix);
            return hasher.final();
        }

        pub fn eql(_: BytePathContext, parts: BytePathParts, path: []const u8) bool {
            const suffix_start = parts.prefix.len + @intFromBool(parts.separator);
            return path.len == suffix_start + parts.suffix.len and
                std.mem.startsWith(u8, path, parts.prefix) and
                (!parts.separator or path[parts.prefix.len] == '.') and
                std.mem.eql(u8, path[suffix_start..], parts.suffix);
        }
    };

    fn internBytePath(
        self: *Seen,
        gpa: std.mem.Allocator,
        prefix: []const u8,
        suffix: []const u8,
    ) ![]const u8 {
        // A field projected to the root loses its leading separator.
        const tail = if (suffix.len != 0 and suffix[0] == '.') suffix[1..] else suffix;
        const separator = prefix.len != 0 and tail.len != 0 and tail[0] != '[';
        const parts: BytePathParts = .{ .prefix = prefix, .suffix = tail, .separator = separator };
        if (self.byte_paths.getKeyAdapted(parts, BytePathContext{})) |path| return path;
        const suffix_start = try std.math.add(usize, prefix.len, @intFromBool(separator));
        const length = try std.math.add(usize, suffix_start, tail.len);
        const path = try gpa.alloc(u8, length);
        errdefer gpa.free(path);
        @memcpy(path[0..prefix.len], prefix);
        if (separator) path[prefix.len] = '.';
        @memcpy(path[suffix_start..], tail);
        try self.byte_paths.put(gpa, path, {});
        return path;
    }

    /// Record `rule_id` at `byte`.  Returns false when that diagnostic
    /// has already been recorded — the caller's cue to skip building a
    /// message and a note for a finding nobody will read twice.
    ///
    /// Failing to remember a diagnostic is an analysis failure, not a
    /// silent one: reporting without the memo would hand back the same
    /// finding once per path state.
    pub fn record(self: *Seen, gpa: std.mem.Allocator, rule_id: []const u8, byte: u32) !bool {
        try self.adoptExisting(gpa);
        return self.put(gpa, rule_id, byte);
    }

    fn recordOwner(self: *Seen, gpa: std.mem.Allocator, rule_id: []const u8, byte: u32, owner_byte: u32) !bool {
        try self.adoptExisting(gpa);
        return self.putOwner(gpa, rule_id, byte, owner_byte);
    }

    fn adoptExisting(self: *Seen, gpa: std.mem.Allocator) !void {
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
    }

    fn put(self: *Seen, gpa: std.mem.Allocator, rule_id: []const u8, byte: u32) !bool {
        return self.putOwner(gpa, rule_id, byte, null);
    }

    fn putOwner(self: *Seen, gpa: std.mem.Allocator, rule_id: []const u8, byte: u32, owner_byte: ?u32) !bool {
        const slot = try self.keys.getOrPut(gpa, .{ .rule_id = rule_id, .byte = byte, .owner_byte = owner_byte });
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
        .indexed_read => |r| try transferIndexedRead(ctx, state, r, stmt.pos, stmt.end_pos),
        .indexed_write => |w| {
            try transferIndexedWrite(ctx, state, w, stmt.pos);
            try replayIndexedAggregateBytes(ctx, state, w);
        },
        .counter_step => |s| try transferCounterStep(ctx, state, s),
        .field_counter_step => |s| {
            state.facts.forgetLocal(s.parent);
            try state.stepFieldCounter(ctx.gpa, .{ .parent = s.parent, .name = s.name }, s.step);
        },
        .compare_assume => |comparison| {
            const lhs_defined = indexIsDefined(ctx, state, comparison.lhs);
            const operands_defined = lhs_defined and indexIsDefined(ctx, state, comparison.rhs);
            // A successful runtime guard may select a physically written
            // prefix even when the helper count retains strict input
            // obligations. Never expose this relation to the value solver.
            if (comparison.op == .lt and comparison.lhs == .local and comparison.rhs == .local and
                comparison.lhs.local.offset == 0 and comparison.rhs.local.offset == 0 and
                lhs_defined and !operands_defined and
                !localIsProvedUndefined(ctx, state, comparison.rhs.local.local))
            {
                try state.recordDiagnosticIndexBound(ctx.gpa, comparison.lhs.local.local, comparison.rhs.local.local);
            }
            // Bounds constrain existing values, not an uncertain operand.
            // This gate does not require scalar identity for legacy counter
            // or header terms; fixed array lengths are constant terms.
            if (operands_defined) {
                state.feasible = try state.assumeComparison(ctx.gpa, comparison);
            }
        },
        .scaled_index => |certificate| {
            _ = try @import("bounded_prefix.zig").recordScaledIndex(ctx.gpa, state, certificate);
        },
        .array_complete => |complete| {
            const write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
                .array = complete.array,
                .index = .{ .constant = 0 },
                .rhs_kind = .plain,
                .defined = complete.value_defined,
                .inputs = complete.inputs,
                .selected_inputs = complete.selected_inputs,
                .value_has_undefined_origin = complete.value_has_undefined_origin,
                .entire_source_undefined = complete.value_entirely_undefined,
                .value_entirely_undefined = complete.value_entirely_undefined,
                .result_is_computation = true,
            };
            if (!storageInputsAreCovered(ctx, state, &complete.inputs) or
                !indexedRhsIsDefined(ctx, state, write, .plain))
            {
                if (storageInputsMayBeUndefined(ctx, state, &complete.inputs) or
                    indexedRhsReadsUndefined(ctx, state, write, .plain))
                {
                    try transferIndexedWrite(ctx, state, .{
                        .array = complete.array, .index = .{ .constant = 0 },
                        .rhs_kind = .plain, .all_elements = true,
                        .value_has_undefined_origin = true,
                        .entire_source_undefined = complete.value_entirely_undefined,
                        .value_entirely_undefined = complete.value_entirely_undefined,
                        .result_is_computation = true,
                        .selected_inputs = complete.selected_inputs,
                    }, stmt.pos);
                    return;
                }
                try state.unknown_values.put(ctx.gpa, complete.array, {});
            } else {
                _ = state.unknown_values.orderedRemove(complete.array);
                state.forgetUndefinedBytes(complete.array);
                // Completion repairs bytes, not the array's strict origin.
                try state.bindWrittenField(ctx.gpa, .{ .parent = complete.array, .name = "" }, false);
            }
            try state.markArrayComplete(ctx.gpa, complete.array);
        },
        .array_range_complete => |range| try transferArrayRangeComplete(ctx, state, range),
        .array_value => |value| {
            if (value.mask_only) {
                try copyCaptureDiagnosticBytes(ctx, state, value);
                return;
            }
            if (value.diagnostic_only) {
                try copyArrayDiagnosticBytes(ctx, state, value);
                return;
            }
            var may_undefined = exprMayBeUndefined(ctx, state, value.source) or
                valueInputsMayBeUndefined(ctx, state, &value.selected_inputs);
            for (value.inputs) |input| {
                if (input) |local| may_undefined = may_undefined or localIsProvedUndefined(ctx, state, local);
            }
            if (value.layout_change and value.source == .field_copy_of) {
                const field = value.source.field_copy_of;
                may_undefined = may_undefined or fieldValueMayBeUndefined(ctx, state, field.parent, field.name);
            }
            var exact_copy = value.source == .copy_of and !value.whole_payload and
                !ctx.locals[@intFromEnum(value.source.copy_of)].is_pointer and
                localIsArray(ctx, value.source.copy_of) and arrayCopyPreservesExtent(ctx, value.target, value.source.copy_of);
            if (exact_copy) {
                for (value.selected_inputs) |entry| {
                    const selected = entry orelse continue;
                    if (selected == .local and selected.local == value.source.copy_of) continue;
                    if (valueInputsMayBeUndefined(ctx, state, &.{selected})) exact_copy = false;
                }
                for (value.inputs) |entry| {
                    const local = entry orelse continue;
                    if (local != value.source.copy_of and localIsProvedUndefined(ctx, state, local)) exact_copy = false;
                }
            }
            if (exact_copy and value.target != value.source.copy_of) {
                state.forgetUndefinedBytes(value.target);
                try state.copyArrayInitialization(ctx.gpa, value.target, value.source.copy_of);
                try copyUnknownFieldValues(ctx, state, value.target, value.source.copy_of);
                if (!may_undefined) {
                    if (state.locals.getPtr(value.target)) |origin| if (origin.* == .undef) {
                        origin.* = .plain;
                    };
                }
            }
            if (may_undefined) {
                if (value.layout_change)
                    try markPayloadMayBeUndefined(ctx, state, value.target)
                else {
                    if (!exact_copy) state.forgetInitializationArray(value.target);
                    try state.may_undefined_values.put(ctx.gpa, value.target, {});
                }
            }
            // Field-copy abstention revokes certificates, not transported
            // byte witnesses. Materialize the negative mask before returning.
            if (!value.whole_payload and value.source == .field_copy_of and
                !ctx.locals[@intFromEnum(value.source.field_copy_of.parent)].is_pointer)
                try copyArrayDiagnosticBytes(ctx, state, value);
            if (!valueInputsAreDefined(ctx, state, &value.selected_inputs, false)) {
                try state.unknown_values.put(ctx.gpa, value.target, {});
                return;
            }
            for (value.inputs) |input| {
                const local = input orelse continue;
                const covered_array = localIsArray(ctx, local) and arrayHasFullCoverage(ctx, state, local);
                if (state.unknown_values.contains(local) and !covered_array) return;
                if (state.locals.get(local)) |origin| if (origin == .undef and !covered_array) return;
                if (!ctx.locals[@intFromEnum(local)].is_pointer and
                    !state.fieldValueIsDefined(local, "") and !covered_array) return;
                if (ctx.locals[@intFromEnum(local)].is_pointer) return;
            }
            if (value.whole_payload) {
                const covered = switch (value.source) {
                    .copy_of => |source| if (ctx.locals[@intFromEnum(source)].is_pointer)
                        false
                    else if (localIsArray(ctx, source))
                        arrayHasFullCoverage(ctx, state, source) or
                            (!state.locals.contains(source) and !state.unknown_values.contains(source))
                    else
                        !state.unknown_values.contains(source) and state.fieldValueIsDefined(source, ""),
                    .field_copy_of => |field| blk: {
                        if (ctx.locals[@intFromEnum(field.parent)].is_pointer) break :blk false;
                        break :blk state.fieldValueIsDefined(field.parent, field.name);
                    },
                    else => false,
                };
                if (covered) try state.markArrayComplete(ctx.gpa, value.target);
                return;
            }
            switch (value.source) {
                .copy_of => |source| {
                    if (localIsArray(ctx, source) and arrayCopyPreservesExtent(ctx, value.target, source)) {
                        if (state.locals.contains(source)) {
                            if (!exact_copy) try state.copyArrayInitialization(ctx.gpa, value.target, source);
                        } else if (arrayInitializerComplete(ctx, state, value.target, value.source, .plain, true)) {
                            try state.markArrayComplete(ctx.gpa, value.target);
                        }
                    }
                },
                // An opaque call result: every array it was handed must be covered.
                .plain => if (storageInputsAreCovered(ctx, state, &value.inputs)) {
                    try state.markArrayComplete(ctx.gpa, value.target);
                },
                .field_copy_of => |field| {
                    const origin = try originOfInit(ctx, state, value.source, stmt.pos);
                    if (origin != .undef and state.fieldArrayBaseIsDefined(field.parent, field.name)) {
                        try state.markArrayComplete(ctx.gpa, value.target);
                        // Restoring strict coverage must not erase transported holes.
                        try copyArrayDiagnosticBytes(ctx, state, value);
                        // A whole-field default or parameter proof remains a
                        // complete base after an exact undefined overwrite.
                        // Carry its sparse holes, including nested slot holes.
                        for ([_][]const state_mod.FieldKey{ state.fields.keys(), state.unknown_field_values.keys() }) |keys| {
                            for (keys) |key| {
                                if (key.parent != field.parent or key.name.len <= field.name.len or
                                    !std.mem.startsWith(u8, key.name, field.name)) continue;
                                const suffix = key.name[field.name.len..];
                                if (suffix[0] != '[' or state.fieldValueIsDefined(key.parent, key.name)) continue;
                                const index = literalArrayElementIndex(suffix) orelse {
                                    state.forgetInitializationArray(value.target);
                                    break;
                                };
                                if (ctx.locals[@intFromEnum(value.target)].array_extent) |extent| {
                                    if (index >= extent) continue;
                                }
                                try state.setExactElement(ctx.gpa, value.target, index, false);
                            }
                        }
                    }
                    // Partially initialized source fields retain their exact
                    // element coverage. The canonical dependency supplies no
                    // bits; only existing source field facts supply them.
                    if (!state.isArrayComplete(value.target)) {
                        const extent = ctx.locals[@intFromEnum(value.target)].array_extent orelse return;
                        for (state.fields.keys()) |key| {
                            if (key.parent != field.parent or key.name.len <= field.name.len or
                                !std.mem.startsWith(u8, key.name, field.name)) continue;
                            const suffix = key.name[field.name.len..];
                            const index = literalArrayElementIndex(suffix) orelse continue;
                            if (suffix[suffix.len - 1] != ']' or index >= extent) continue;
                            if (state.fieldValueIsDefined(key.parent, key.name))
                                try state.setExactElement(ctx.gpa, value.target, index, true);
                        }
                    }
                },
                else => {},
            }
        },
        .array_prefix => |prefix| {
            if (prefix.diagnostic_only) {
                const extent = prefix.extent orelse ctx.locals[@intFromEnum(prefix.array)].array_extent orelse return;
                const array: state_mod.FieldKey = .{ .parent = prefix.array, .name = prefix.field_array orelse "" };
                const count = prefix.counter_term orelse cfg.IndexTerm{ .local = .{ .local = prefix.count } };
                if (storageInputsMayBeUndefined(ctx, state, &prefix.inputs) or
                    valueInputsMayBeUndefined(ctx, state, &prefix.selected_inputs)) {
                    state.forgetFieldInitialization(array);
                    return;
                }
                if (prefix.preserves_prefix) {
                    const entry: cfg.IndexTerm = if (prefix.entry_count) |local|
                        .{ .local = .{ .local = local } }
                    else
                        count;
                    const entry_array: state_mod.FieldKey = if (prefix.entry_array) |parent|
                        .{ .parent = parent, .name = prefix.field_array orelse "" }
                    else
                        array;
                    const offset = state.termSymbolicPrefixOffset(entry_array, entry);
                    if (!(offset != null and offset.? >= 0) and
                        !state.provesComparison(.{ .lhs = entry, .rhs = .{ .constant = 0 }, .op = .eq })) return;
                }
                try state.unknown_values.put(ctx.gpa, prefix.array, {});
                if (prefix.preserves_prefix) state.forgetEntireUndefinedField(array);
                if (prefix.preserves_prefix) {
                    const entry = if (prefix.entry_count) |local| cfg.IndexTerm{ .local = .{ .local = local } } else count;
                    if (indexIsDefined(ctx, state, entry)) {
                        if (count == .field) {
                            try state.bindFieldValue(ctx.gpa, .{ .parent = count.field.parent, .name = count.field.name }, true);
                            try state.fields.putContext(ctx.gpa, .{ .parent = count.field.parent, .name = count.field.name }, .plain, .{});
                        } else if (count == .local) {
                            _ = state.unknown_values.swapRemove(count.local.local);
                            try state.bindFieldValue(ctx.gpa, .{ .parent = count.local.local, .name = "" }, true);
                        }
                    }
                }
                if (count == .field) state.forgetFieldTermComparisons(.{ .parent = count.field.parent, .name = count.field.name });
                try state.setTermSymbolicPrefix(ctx.gpa, array, count, 0, extent);
                return;
            }
            const extent = ctx.locals[@intFromEnum(prefix.array)].array_extent orelse return;
            if (prefix.seeded_append) {
                // The builder proves the seed-one, capacity-guarded adjacent
                // store/push shape. Actual transfers must have written slot
                // zero, and no undefined store may have poisoned any lane.
                // Unknown stored values do not gain a payload/count proof.
                // The undefined declaration retains MAY for its unwritten
                // suffix. Unplaced undefined overwrites revoke fixed coverage;
                // placed holes are checked below.
                if (prefix.scale != 1 or extent == 0 or state.fixedPrefix(prefix.array) < 1 or
                    localIsProvedUndefined(ctx, state, prefix.count)) return;
                for (state.undefined_elements.keys()) |hole| if (hole.array == prefix.array) return;
                for (state.undefined_field_values.keys()) |key| {
                    if (key.parent == prefix.array and key.name.len != 0 and
                        state.fieldValueMayBeUndefined(prefix.array, key.name)) return;
                }
                var buffer: [128]u8 = undefined;
                const temporary = try std.fmt.bufPrint(&buffer, "[0..${d}:1:0:{d}:0]", .{
                    @intFromEnum(prefix.count), extent,
                });
                const path = try ctx.seen.internBytePath(ctx.gpa, "", temporary);
                try state.bindWrittenField(ctx.gpa, .{ .parent = prefix.array, .name = path }, false);
                try state.diagnostic_index_bounds.put(ctx.gpa, .{
                    .index = prefix.count, .counter = prefix.count, .offset = -1,
                }, {});
                return;
            }
            var certified = storageInputsAreCovered(ctx, state, &prefix.inputs);
            for (prefix.inputs) |input| {
                const local = input orelse continue;
                if (state.unknown_values.contains(local) and
                    !(localIsArray(ctx, local) and arrayHasFullCoverage(ctx, state, local))) certified = false;
            }
            if (!certified) {
                if (storageInputsMayBeUndefined(ctx, state, &prefix.inputs)) return;
                try state.unknown_values.put(ctx.gpa, prefix.array, {});
            }
            // This certificate is emitted only on the helper's successful
            // return of its initialized counter. The returned scalar exists;
            // its bounds and the initialized bytes remain separate facts.
            if (certified) _ = state.unknown_values.swapRemove(prefix.count);
            try state.setScaledSymbolicPrefix(ctx.gpa, prefix.array, prefix.count, prefix.scale, extent);
            // Keep the written region visible when an old undefined base
            // survives alias revocation. This grants no value certificate.
            if (prefix.scale != 0) {
                var buffer: [128]u8 = undefined;
                const temporary = try std.fmt.bufPrint(&buffer, "[0..${d}:{d}:0:{d}:0]", .{
                    @intFromEnum(prefix.count), prefix.scale, extent,
                });
                const path = try ctx.seen.internBytePath(ctx.gpa, "", temporary);
                try state.bindWrittenField(ctx.gpa, .{ .parent = prefix.array, .name = path }, false);
            }
        },
        .array_memset_prefix => |prefix| try transferArrayMemsetPrefix(ctx, state, prefix, stmt.pos),
        .guard_fact => |g| state.feasible = try state.facts.assumeGuard(ctx.gpa, g.guard, g.holds),
        .arena_kill => |k| try transferArenaKill(ctx, state, k, stmt.pos, stmt.end_pos),
        .heap_free => |f| try transferHeapFree(ctx, state, f, stmt.pos, stmt.end_pos),
        .ret => |r| try transferRet(ctx, state, r, stmt.pos, stmt.end_pos),
        .use => |u| try transferUse(ctx, state, u, stmt.pos, stmt.end_pos),
        .pointer_write => |p| {
            const writes_undefined = p.value_has_undefined_origin or
                valueInputsMayBeUndefined(ctx, state, &p.preserve_inputs) or
                valueInputsMayBeUndefined(ctx, state, &p.diagnostic_inputs);
            const preserved_array: ?LocalId = if (p.preserves_complete_array) backing: {
                var array = p.target;
                if (p.payload_only and ctx.locals[@intFromEnum(p.target)].is_slice) {
                    const pointer = state.fields.getContext(.{ .parent = p.target, .name = "ptr" }, .{}) orelse break :backing null;
                    if (!scalarFieldIsDefined(ctx, state, p.target, "ptr") or pointer != .stack)
                        break :backing null;
                    array = pointer.stack;
                }
                // A descriptor is never its payload. Only existing coverage
                // of the identified frame array can survive a defined store.
                if (ctx.locals[@intFromEnum(array)].is_pointer or !localIsArray(ctx, array) or
                    !arrayHasFullCoverage(ctx, state, array) or
                    !valueInputsAreDefined(ctx, state, &p.preserve_inputs, !p.preserve_whole_payload))
                    break :backing null;
                break :backing array;
            } else null;
            try forgetAliasedValueFacts(ctx, state, p.target, p.preserves_diagnostic_base);
            if (writes_undefined) try markPayloadMayBeUndefined(ctx, state, p.target);
            if (!(p.payload_only and ctx.locals[@intFromEnum(p.target)].is_slice))
                try invalidateFieldValueCertificates(ctx, state, p.target);
            if (p.initializes and !writes_undefined and !ctx.locals[@intFromEnum(p.target)].is_pointer and !localIsArray(ctx, p.target))
                state.forgetUndefinedBytes(p.target);
            if (ctx.locals[@intFromEnum(p.target)].tracks_array_payload or tracksScalarValue(ctx, state, p.target)) {
                if (p.initializes and !writes_undefined and !ctx.locals[@intFromEnum(p.target)].is_pointer and !localIsArray(ctx, p.target)) {
                    _ = state.unknown_values.orderedRemove(p.target);
                } else try state.unknown_values.put(ctx.gpa, p.target, {});
            }
            if (state.locals.get(p.target)) |origin| {
                var owner = if (origin == .stack)
                    origin.stack
                else
                    ctx.locals[@intFromEnum(p.target)].frame_borrow_origin;
                if (p.payload_only and ctx.locals[@intFromEnum(p.target)].is_slice) {
                    if (state.fields.getContext(.{ .parent = p.target, .name = "ptr" }, .{})) |pointer| {
                        if (pointer == .stack) owner = pointer.stack;
                    }
                }
                if (owner) |local| {
                    try forgetAliasedValueFacts(ctx, state, local, p.preserves_diagnostic_base);
                    if (writes_undefined) try markPayloadMayBeUndefined(ctx, state, local);
                    if (!writes_undefined and !p.preserves_diagnostic_base) {
                        var buffer: [96]u8 = undefined;
                        const pointer = state.fields.getContext(.{ .parent = p.target, .name = "ptr" }, .{});
                        const scoped_index = if (pointer != null and pointer.? == .stack and pointer.?.stack == local)
                            p.diagnostic_index
                        else
                            null;
                        const path = if (scoped_index) |index| scoped: {
                            const extent = ctx.locals[@intFromEnum(local)].array_extent orelse break :scoped "";
                            const range = state.diagnosticWriteRange(index, extent);
                            if (range.start >= range.end) break :scoped "";
                            break :scoped try std.fmt.bufPrint(&buffer, "[{d}..{d}]", .{ range.start, range.end });
                        } else "";
                        const owned = try ctx.seen.internBytePath(ctx.gpa, "", path);
                        try state.uncertain_byte_writes.putContext(ctx.gpa, .{ .parent = local, .name = owned }, {}, .{});
                    }
                    try invalidateFieldValueCertificates(ctx, state, local);
                    // Preserve field resource origins for lifetime checks, while
                    // revoking every field's initialized-payload certificate.
                    if (ctx.locals[@intFromEnum(local)].tracks_array_payload or tracksScalarValue(ctx, state, local)) {
                        try state.unknown_values.put(ctx.gpa, local, {});
                    }
                }
                if (p.initializes and origin == .undef and !localIsArray(ctx, p.target)) {
                    try state.locals.put(ctx.gpa, p.target, .plain);
                }
            }
            if (preserved_array) |array| {
                // This restores only pre-existing coverage, never a hole.
                try state.markArrayComplete(ctx.gpa, array);
                _ = state.unknown_values.swapRemove(array);
            }
        },
        .reset_capture => |r| {
            const defined = r.value_defined and valueInputsAreDefined(ctx, state, &r.value_inputs, false) and if (r.value_source) |source|
                if (localIsArray(ctx, source))
                    arrayHasFullCoverage(ctx, state, source)
                else if (ctx.locals[@intFromEnum(source)].is_slice) backing: {
                    const pointer = state.fields.getContext(.{ .parent = source, .name = "ptr" }, .{}) orelse break :backing false;
                    if (!scalarFieldIsDefined(ctx, state, source, "ptr")) break :backing false;
                    break :backing switch (pointer) {
                        .stack => |array| localIsArray(ctx, array) and arrayHasFullCoverage(ctx, state, array),
                        .undef => false,
                        else => true,
                    };
                } else
                    localInputIsDefined(ctx, state, source, false)
            else
                true;
            forgetLocalValueFacts(ctx, state, r.local);
            const owner = ctx.locals[@intFromEnum(r.local)].array_element_owner;
            try state.locals.put(ctx.gpa, r.local, if (owner) |array| .{ .stack = array } else .plain);
            // Also clear any tracked FIELD origins for this local —
            // `for (bins) |bin| ctx.allocator.free(bin.path);` frees
            // `bin.path` once per iteration; without clearing the
            // field, iter N+1 sees iter N's freed state and reports
            // a spurious double-free of `bin.path`.
            state.forgetFields(r.local);
            if (!defined) try state.unknown_values.put(ctx.gpa, r.local, {});
        },
        .composite_escape => |c| try transferCompositeEscape(ctx, state, c, stmt.pos, stmt.end_pos),
        .field_assign => |a| try transferFieldAssign(ctx, state, a, stmt.pos),
        .field_heap_free => |f| try transferFieldHeapFree(ctx, state, f, stmt.pos, stmt.end_pos),
        .field_use => |u| try transferFieldUse(ctx, state, u, stmt.pos, stmt.end_pos),
        .out_param_write => |w| try transferOutParamWrite(ctx, state, w, stmt.pos, stmt.end_pos),
        .interior_pointer_destroy => |i| try transferInteriorPointerDestroy(ctx, state, i, stmt.pos, stmt.end_pos),
        .leak_warning => |l| try transferLeakWarning(ctx, l, stmt.pos, stmt.end_pos),
        .partial_union_write => |p| try transferPartialUnionWrite(ctx, p, stmt.pos, stmt.end_pos),
        .lowering_gap => |g| try transferGap(ctx, state, g),
    }
}

/// No input is undefined, or a frame array whose bytes are not all written.
fn storageInputsAreCovered(ctx: Ctx, state: *const AbstractState, inputs: []const ?LocalId) bool {
    for (inputs) |input| {
        const local = input orelse continue;
        const info = ctx.locals[@intFromEnum(local)];
        const covered_array = !info.is_pointer and localIsArray(ctx, local) and
            arrayHasFullCoverage(ctx, state, local);
        if (state.unknown_values.contains(local) and !covered_array) return false;
        if (localIsArray(ctx, local) and !covered_array) return false;
        if (state.locals.get(local)) |origin| {
            if (origin == .undef and !covered_array) return false;
            if (origin == .stack and localIsArray(ctx, origin.stack) and
                !arrayHasFullCoverage(ctx, state, origin.stack)) return false;
        }
        if (ctx.locals[@intFromEnum(local)].frame_borrow_origin) |owner| {
            if (localIsArray(ctx, owner) and !arrayHasFullCoverage(ctx, state, owner)) return false;
        }
        if (info.is_slice) {
            if (!scalarFieldIsDefined(ctx, state, local, "ptr") or
                !scalarFieldIsDefined(ctx, state, local, "len")) return false;
            const pointer = state.fields.getContext(.{ .parent = local, .name = "ptr" }, .{}) orelse return false;
            if (pointer == .stack and localIsArray(ctx, pointer.stack) and
                !arrayHasFullCoverage(ctx, state, pointer.stack)) return false;
        }
    }
    return true;
}

fn storageInputsMayBeUndefined(ctx: Ctx, state: *const AbstractState, inputs: []const ?LocalId) bool {
    for (inputs) |entry| {
        const local = entry orelse continue;
        if (localIsProvedUndefined(ctx, state, local)) return true;
        if (ctx.locals[@intFromEnum(local)].is_pointer and state.fieldValueMayBeUndefined(local, "")) return true;
        if (state.locals.get(local)) |origin| {
            if (origin == .stack and localIsProvedUndefined(ctx, state, origin.stack)) return true;
        }
    }
    return false;
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
    const origin = try originOfInit(ctx, state, d.init_kind, pos);
    const payload_defined = if (tracksScalarValue(ctx, state, d.local))
        scalarValueIsDefined(ctx, state, d.init_kind, d.value_defined, &d.value_inputs)
    else if (state.integer_domains.len != 0 and ctx.locals[@intFromEnum(d.local)].tracks_array_payload)
        d.value_defined and copiedPayloadIsDefined(state, d.init_kind, d.value_defined) and
            valueInputsAreDefined(ctx, state, &d.value_inputs, false)
    else
        copiedPayloadIsDefined(state, d.init_kind, d.value_defined);
    const array_complete = d.array_copy and arrayInitializerComplete(ctx, state, d.local, d.init_kind, origin, payload_defined);
    const may_undefined = d.value_has_undefined_origin or d.value_entirely_undefined or
        bindingMayBeUndefined(ctx, state, d.init_kind, &d.value_inputs);
    const entirely_undefined = bindingIsEntirelyUndefined(ctx, state, d.init_kind,
        d.entire_source_undefined, d.value_entirely_undefined,
        d.result_is_computation, &d.value_inputs);
    forgetLocalValueFacts(ctx, state, d.local);
    try bindBoolean(ctx, state, d.local, d.init_kind);
    const binding_origin: Origin = if (origin == .undef and !may_undefined) .plain else origin;
    try state.locals.put(ctx.gpa, d.local, scalarBindingOrigin(ctx, d.local, binding_origin));
    try seedLocalValueFacts(ctx, state, d.local, d.init_kind, d.integer_value, array_complete);
    if (d.array_copy and d.init_kind == .copy_of and localIsArray(ctx, d.local) and
        localIsArray(ctx, d.init_kind.copy_of) and state.locals.contains(d.init_kind.copy_of) and
        arrayCopyPreservesExtent(ctx, d.local, d.init_kind.copy_of))
    {
        try state.copyArrayInitialization(ctx.gpa, d.local, d.init_kind.copy_of);
    }
    // Clear any stale field state for this local — a fresh decl
    // (e.g. `const source = ...` inside a loop body) creates a new
    // instance; prior-iteration field tracking for the same LocalId
    // is a back-edge artifact that would spuriously fire double-free
    // / UAF on the new instance.
    state.forgetFields(d.local);
    if (may_undefined and !array_complete) try state.may_undefined_values.put(ctx.gpa, d.local, {});
    if ((ctx.locals[@intFromEnum(d.local)].tracks_array_payload or tracksScalarValue(ctx, state, d.local)) and !payload_defined) {
        try state.unknown_values.put(ctx.gpa, d.local, {});
    }
    if (d.init_kind == .copy_of and localIsArray(ctx, d.local) and state.unknown_values.contains(d.init_kind.copy_of)) {
        try state.unknown_values.put(ctx.gpa, d.local, {});
    }
    if (d.init_kind == .copy_of and (ctx.locals[@intFromEnum(d.local)].tracks_array_payload or
        localDiagnosticIsAggregate(ctx, state, d.init_kind.copy_of)))
    {
        try copyUnknownFieldValues(ctx, state, d.local, d.init_kind.copy_of);
    }
    if (entirely_undefined) {
        try state.entire_undefined_values.put(ctx.gpa, d.local, {});
        try state.bindEntireUndefinedField(ctx.gpa, .{ .parent = d.local, .name = "" }, true);
    } else if (binding_origin == .undef) {
        try state.partial_undefined_values.put(ctx.gpa, d.local, {});
    }
    if (d.init_kind == .field_copy_of and (localIsAggregate(ctx, d.local) or
        fieldHasDiagnosticChildren(state, d.init_kind.field_copy_of.parent, d.init_kind.field_copy_of.name))) {
        try copyArrayDiagnosticBytes(ctx, state, .{
            .target = d.local,
            .source = d.init_kind,
            .diagnostic_only = true,
        });
    }
}

fn seedLocalValueFacts(
    ctx: Ctx,
    state: *AbstractState,
    local: LocalId,
    kind: cfg.ExprKind,
    integer_value: ?u64,
    array_complete: bool,
) !void {
    const info = ctx.locals[@intFromEnum(local)];
    if ((info.is_unsigned or tracksIntegerValue(state, local)) and kind == .copy_of) {
        try state.copyCounterValue(ctx.gpa, local, kind.copy_of);
    } else if (info.is_unsigned and kind == .field_copy_of and
        fixedArrayLength(ctx, kind.field_copy_of.parent, kind.field_copy_of.name) == null)
    {
        try state.copyTermCounterValue(ctx.gpa, local, .{ .field = .{
            .parent = kind.field_copy_of.parent, .name = kind.field_copy_of.name, .is_unsigned = true,
        } });
    } else {
        const length_value = if (kind == .field_copy_of)
            fixedArrayLength(ctx, kind.field_copy_of.parent, kind.field_copy_of.name)
        else
            null;
        const value = if (info.is_unsigned)
            integer_value orelse length_value
        else if (tracksIntegerValue(state, local))
            length_value
        else
            null;
        try state.setScalarValue(ctx.gpa, local, value);
    }
    const origin = state.locals.get(local) orelse .plain;
    if (info.is_unsigned and origin != .undef) try state.nonnegative_locals.put(ctx.gpa, local, {});
    if (localIsArray(ctx, local)) {
        if (array_complete) {
            try state.markArrayComplete(ctx.gpa, local);
        } else if (info.array_extent != null) {
            try state.setFixedPrefix(ctx.gpa, local, 0);
        }
    }
}

/// An undefined member overwrite through an element alias can corrupt any
/// slot in its backing array. A defined member store grants no new coverage.
fn invalidateAliasedArrayPayload(ctx: Ctx, state: *AbstractState, parent: LocalId, member: []const u8) !void {
    const info = ctx.locals[@intFromEnum(parent)];
    if (!info.is_pointer) return;
    var owner = info.frame_borrow_origin;
    if (state.locals.get(parent)) |origin| {
        if (origin == .stack) owner = origin.stack;
    }
    const array = owner orelse return;
    if (!localIsArray(ctx, array) and !ctx.locals[@intFromEnum(array)].is_slice and
        !ctx.locals[@intFromEnum(array)].is_pointer) return;
    const may_undefined = state.fieldValueMayBeUndefined(parent, member);
    try forgetAliasedValueFacts(ctx, state, array, false);
    if (may_undefined) {
        if (member.len != 0 and ctx.locals[@intFromEnum(array)].array_extent != null) {
            var buffer: [48]u8 = undefined;
            const range = try std.fmt.bufPrint(&buffer, "[0..{d}]", .{ctx.locals[@intFromEnum(array)].array_extent.?});
            const path = try ctx.seen.internBytePath(ctx.gpa, range, member);
            const key: state_mod.FieldKey = .{ .parent = array, .name = path };
            try state.bindWrittenField(ctx.gpa, key, true);
            try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
        } else try markPayloadMayBeUndefined(ctx, state, array);
    }
    try invalidateFieldValueCertificates(ctx, state, array);
    try state.unknown_values.put(ctx.gpa, array, {});
}

fn markPayloadMayBeUndefined(ctx: Ctx, state: *AbstractState, local: LocalId) !void {
    // This is an authenticated negative effect, not an opaque mutation.
    // It supersedes uncertainty emitted before the precise effect summary.
    var uncertain_index: usize = 0;
    while (uncertain_index < state.uncertain_byte_writes.count()) {
        if (state.uncertain_byte_writes.keys()[uncertain_index].parent == local) {
            _ = state.uncertain_byte_writes.swapRemoveAt(uncertain_index);
        } else uncertain_index += 1;
    }
    const info = ctx.locals[@intFromEnum(local)];
    state.forgetInitializationArray(local);
    if (!info.is_slice) state.forgetWrittenFields(local);
    if (info.is_slice or info.is_pointer) {
        const key: state_mod.FieldKey = .{
            .parent = local,
            .name = if (info.is_slice) "[]" else "",
        };
        try state.bindWrittenField(ctx.gpa, key, true);
        try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
    } else try state.may_undefined_values.put(ctx.gpa, local, {});
    try state.unknown_values.put(ctx.gpa, local, {});
}

fn localIsArray(ctx: Ctx, local: LocalId) bool {
    const info = ctx.locals[@intFromEnum(local)];
    return info.is_array or info.array_extent != null;
}

fn forgetLocalValueFacts(ctx: Ctx, state: *AbstractState, local: LocalId) void {
    state.facts.forgetLocal(local);
    state.forgetInitializationLocal(local);
    if (localIsArray(ctx, local)) state.forgetInitializationArray(local);
}

/// Keep byte-write witnesses when only a value certificate becomes unknown.
fn forgetAliasedValueFacts(ctx: Ctx, state: *AbstractState, local: LocalId, preserve_diagnostic_base: bool) !void {
    state.facts.forgetLocal(local);
    state.forgetInitializationLocal(local);
    _ = state.entire_undefined_values.swapRemove(local);
    if (!preserve_diagnostic_base) state.forgetEntireUndefinedFields(local);
    if ((state.locals.get(local) orelse .plain) == .undef)
        try state.partial_undefined_values.put(ctx.gpa, local, {});
    try state.unknown_field_values.putContext(ctx.gpa, .{ .parent = local, .name = "" }, {}, .{});
    if (localIsArray(ctx, local)) try state.unknown_values.put(ctx.gpa, local, {});
}

/// Unknown writes revoke payload certificates, not physical resource origins.
fn invalidateFieldValueCertificates(ctx: Ctx, state: *AbstractState, local: LocalId) !void {
    const info = ctx.locals[@intFromEnum(local)];
    if (!info.tracks_array_payload and !info.is_slice and !info.is_pointer) return;
    for (state.fields.keys()) |key| {
        if (key.parent == local) try state.unknown_field_values.putContext(ctx.gpa, key, {}, .{});
    }
    if (info.is_slice) {
        try state.unknown_field_values.putContext(ctx.gpa, .{ .parent = local, .name = "len" }, {}, .{});
    }
}

fn literalArrayElementIndex(path: []const u8) ?u64 {
    if (path.len < 3 or path[0] != '[') return null;
    var end: usize = 1;
    while (end < path.len and std.ascii.isDigit(path[end])) : (end += 1) {}
    if (end == 1 or end >= path.len or path[end] != ']') return null;
    return std.fmt.parseInt(u64, path[1..end], 10) catch null;
}

/// Exact slot masks only map between arrays with the same logical extent.
/// Layout-changing casts need a later whole-payload certificate instead.
fn arrayCopyPreservesExtent(ctx: Ctx, target: LocalId, source: LocalId) bool {
    const target_extent = ctx.locals[@intFromEnum(target)].array_extent;
    const source_extent = ctx.locals[@intFromEnum(source)].array_extent;
    if (target_extent) |extent| {
        return if (source_extent) |source_length| source_length == extent else false;
    }
    return source_extent == null;
}

fn arrayInitializerComplete(
    ctx: Ctx,
    state: *const AbstractState,
    target: LocalId,
    kind: ExprKind,
    origin: Origin,
    payload_defined: bool,
) bool {
    const target_extent = ctx.locals[@intFromEnum(target)].array_extent;
    return switch (kind) {
        .copy_of => |source| blk: {
            if (!localIsArray(ctx, source)) break :blk false;
            if (!arrayCopyPreservesExtent(ctx, target, source)) break :blk false;
            if (!state.locals.contains(source)) break :blk true;
            break :blk arrayHasFullCoverage(ctx, state, source);
        },
        .plain, .boolean => payload_defined and target_extent != null and origin != .undef,
        .owned, .arena_init, .heap_alloc, .stack_ref, .borrowed_from, .composite_borrow, .undef, .field_copy_of, .unknown => false,
    };
}

fn arrayHasFullCoverage(ctx: Ctx, state: *const AbstractState, array: LocalId) bool {
    if (undefinedFieldBytesRemain(state, array)) return false;
    if (state.unknown_values.contains(array)) return false;
    return arrayHasWrittenCoverage(ctx, state, array);
}

fn arrayHasWrittenCoverage(ctx: Ctx, state: *const AbstractState, array: LocalId) bool {
    if (ctx.locals[@intFromEnum(array)].array_extent) |extent| {
        return state.hasInitializedPrefix(array, extent);
    }
    return state.isArrayComplete(array);
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
    if (a.rhs_kind == .copy_of and a.rhs_kind.copy_of == a.target) return;
    const origin = try originOfInit(ctx, state, a.rhs_kind, pos);
    const payload_defined = if (tracksScalarValue(ctx, state, a.target))
        scalarValueIsDefined(ctx, state, a.rhs_kind, a.value_defined, &a.value_inputs)
    else if (state.integer_domains.len != 0 and ctx.locals[@intFromEnum(a.target)].tracks_array_payload)
        a.value_defined and copiedPayloadIsDefined(state, a.rhs_kind, a.value_defined) and
            valueInputsAreDefined(ctx, state, &a.value_inputs, false)
    else
        copiedPayloadIsDefined(state, a.rhs_kind, a.value_defined);
    const array_complete = a.array_copy and arrayInitializerComplete(ctx, state, a.target, a.rhs_kind, origin, payload_defined);
    const may_undefined = a.value_has_undefined_origin or a.value_entirely_undefined or
        bindingMayBeUndefined(ctx, state, a.rhs_kind, &a.value_inputs);
    const entirely_undefined = bindingIsEntirelyUndefined(ctx, state, a.rhs_kind,
        a.entire_source_undefined, a.value_entirely_undefined,
        a.result_is_computation, &a.value_inputs);
    forgetLocalValueFacts(ctx, state, a.target);
    try bindBoolean(ctx, state, a.target, a.rhs_kind);
    const binding_origin: Origin = if (origin == .undef and !may_undefined) .plain else origin;
    try state.locals.put(ctx.gpa, a.target, scalarBindingOrigin(ctx, a.target, binding_origin));
    try seedLocalValueFacts(ctx, state, a.target, a.rhs_kind, a.integer_value, array_complete);
    if (a.array_copy and a.rhs_kind == .copy_of and localIsArray(ctx, a.target) and
        localIsArray(ctx, a.rhs_kind.copy_of) and state.locals.contains(a.rhs_kind.copy_of) and
        arrayCopyPreservesExtent(ctx, a.target, a.rhs_kind.copy_of))
    {
        try state.copyArrayInitialization(ctx.gpa, a.target, a.rhs_kind.copy_of);
    }
    // Whole-local reassignment invalidates any tracked field
    // origins for this local — the new value is independent of the
    // old.  Common cases: `&local` passed to a fn (cfg emits an
    // .assign with .unknown to clear .undef; the called fn may
    // also have initialised any field), and `x = foo()` rebinding
    // x.  Stale field state would surface as use-undefined / leak
    // FPs on the new value's fields.
    state.forgetFields(a.target);
    if (may_undefined and !array_complete) try state.may_undefined_values.put(ctx.gpa, a.target, {});
    if ((ctx.locals[@intFromEnum(a.target)].tracks_array_payload or tracksScalarValue(ctx, state, a.target)) and !payload_defined) {
        try state.unknown_values.put(ctx.gpa, a.target, {});
    }
    if (a.rhs_kind == .copy_of and localIsArray(ctx, a.target) and state.unknown_values.contains(a.rhs_kind.copy_of)) {
        try state.unknown_values.put(ctx.gpa, a.target, {});
    }
    if (a.rhs_kind == .copy_of and (ctx.locals[@intFromEnum(a.target)].tracks_array_payload or
        localDiagnosticIsAggregate(ctx, state, a.rhs_kind.copy_of)))
    {
        try copyUnknownFieldValues(ctx, state, a.target, a.rhs_kind.copy_of);
    }
    if (entirely_undefined) {
        try state.entire_undefined_values.put(ctx.gpa, a.target, {});
        try state.bindEntireUndefinedField(ctx.gpa, .{ .parent = a.target, .name = "" }, true);
    } else if (binding_origin == .undef) {
        try state.partial_undefined_values.put(ctx.gpa, a.target, {});
    }
    if (a.rhs_kind == .field_copy_of and (localIsAggregate(ctx, a.target) or
        fieldHasDiagnosticChildren(state, a.rhs_kind.field_copy_of.parent, a.rhs_kind.field_copy_of.name))) {
        try copyArrayDiagnosticBytes(ctx, state, .{
            .target = a.target,
            .source = a.rhs_kind,
            .diagnostic_only = true,
        });
    }
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
    var origin = try originOfInit(ctx, state, r.value_kind, pos);
    const array_source: ?LocalId = switch (r.value_kind) {
        .copy_of => |source| source,
        else => null,
    };
    if (array_source) |source| {
        // A retained strict origin is not an entirely undefined byte witness.
        const entirely_undefined = localIsEntirelyUndefined(ctx, state, source);
        if (origin == .undef and !entirely_undefined) origin = .plain;
        if (localIsArray(ctx, source) and state.locals.contains(source) and entirely_undefined)
            try reportUncoveredArrayUse(ctx, state, source, false, true, pos, end_pos);
    }
    if (r.value_kind == .field_copy_of and origin == .undef and
        !fieldIsEntirelyUndefined(ctx, state, r.value_kind.field_copy_of.parent, r.value_kind.field_copy_of.name))
        origin = .plain;

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
    const diagnostic_undefined = if (r.diagnostic_source) |source|
        localIsEntirelyUndefined(ctx, state, source)
    else
        switch (r.value_kind) {
            .copy_of => |source| localIsEntirelyUndefined(ctx, state, source),
            .field_copy_of => |field| fieldIsEntirelyUndefined(ctx, state, field.parent, field.name),
            else => r.value_has_undefined_origin,
        };
    if ((origin == .undef or r.value_entirely_undefined or diagnostic_undefined) and !r.is_literal_undef and
        config_mod.isEnabled(ctx.config, .use_undefined))
    {
        try report(ctx, "use-undefined", pos, end_pos, .@"error", "returning a value that is still `undefined`", .{});
        return;
    }

    // Physical cell loans do not resolve through the values currently stored
    // in those cells. A complete proof replaces only the coarse stack origin.
    if (config_mod.isEnabled(ctx.config, .stack_escape)) {
        for (r.stack_loans.locals) |local| {
            try reportReturnedStackCell(ctx, local, r.is_borrowed_return_type, pos, end_pos);
        }
        if (legacyStackCell(r.stack_loans, origin)) |local| {
            try reportReturnedStackCell(ctx, local, r.is_borrowed_return_type, pos, end_pos);
        }
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

/// Canonical loans always report. An incomplete proof permits the legacy
/// origin only for independently proved address-value chains. In particular,
/// passing `&local` to a call does not prove its result carries that address.
fn legacyStackCell(loans: cfg.StackLoanProof, origin: Origin) ?LocalId {
    if (loans.complete) return null;
    const local = switch (origin) {
        .stack => |cell| cell,
        else => return null,
    };
    if (std.mem.indexOfScalar(LocalId, loans.legacy_locals, local) == null) return null;
    if (std.mem.indexOfScalar(LocalId, loans.locals, local) != null) return null;
    return local;
}

fn reportReturnedStackCell(
    ctx: Ctx,
    local: LocalId,
    is_borrowed_return_type: bool,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    const name = ctx.locals[@intFromEnum(local)].name;
    if (is_borrowed_return_type) {
        try reportWithIdentity(ctx, "stack-escape", pos, end_pos, .@"error", "returning a pointer to a function-local stack variable `{s}` (escapes its frame)", .{name}, null, ctx.locals[@intFromEnum(local)].decl_pos.byte);
    } else {
        try reportWithIdentity(ctx, "stack-escape", pos, end_pos, .@"error", "returning a value that holds a pointer to function-local stack variable `{s}` (escapes its frame)", .{name}, null, ctx.locals[@intFromEnum(local)].decl_pos.byte);
    }
}

fn copiedPayloadIsDefined(state: *const AbstractState, kind: ExprKind, defined: bool) bool {
    return switch (kind) {
        .stack_ref => true,
        .copy_of, .borrowed_from, .composite_borrow => |source| !state.unknown_values.contains(source),
        .field_copy_of => |field| state.fieldValueIsDefined(field.parent, field.name),
        .undef => false,
        else => defined,
    };
}

fn copyUnknownFieldValues(ctx: Ctx, state: *AbstractState, target: LocalId, source: LocalId) !void {
    if (target == source) return;
    const count = state.unknown_field_values.count();
    var index: usize = 0;
    while (index < count) : (index += 1) {
        const key = state.unknown_field_values.keys()[index];
        if (key.parent == source) try state.unknown_field_values.putContext(ctx.gpa, .{ .parent = target, .name = key.name }, {}, .{});
    }
    const undefined_count = state.undefined_field_values.count();
    index = 0;
    while (index < undefined_count) : (index += 1) {
        const key = state.undefined_field_values.keys()[index];
        if (key.parent == source) try state.undefined_field_values.putContext(ctx.gpa, .{ .parent = target, .name = key.name }, {}, .{});
    }
    const written_count = state.written_fields.count();
    index = 0;
    while (index < written_count) : (index += 1) {
        const key = state.written_fields.keys()[index];
        if (key.parent == source) try state.written_fields.putContext(ctx.gpa, .{ .parent = target, .name = key.name }, {}, .{});
    }
    const uncertain_count = state.uncertain_byte_writes.count();
    index = 0;
    while (index < uncertain_count) : (index += 1) {
        const key = state.uncertain_byte_writes.keys()[index];
        if (key.parent == source) try state.uncertain_byte_writes.putContext(ctx.gpa, .{ .parent = target, .name = key.name }, {}, .{});
    }
    if (state.partial_undefined_values.contains(source))
        try state.partial_undefined_values.put(ctx.gpa, target, {});
    try state.copyEntireUndefinedFields(ctx.gpa, target, source);
}

const ArrayBytePlace = struct { parent: LocalId, path: []const u8 = "" };

fn arrayByteSuffix(ctx: Ctx, place: ArrayBytePlace, key: state_mod.FieldKey) ?[]const u8 {
    if (key.parent != place.parent) return null;
    if (!state_mod.fieldPathPrefix(place.path, key.name)) {
        // Selecting one element narrows a diagnostic range pattern without
        // turning that selection into an initialization certificate.
        for (1..key.name.len + 1) |end| {
            if (end < key.name.len and key.name[end] != '.' and key.name[end] != '[') continue;
            const matched = state_mod.diagnosticFieldPrefix(key.name[0..end], place.path) orelse continue;
            if (matched == place.path.len) return key.name[end..];
        }
        return null;
    }
    if (key.name.len <= place.path.len) return null;
    if (place.path.len == 0 and ctx.locals[@intFromEnum(place.parent)].is_slice and
        (std.mem.eql(u8, key.name, "ptr") or std.mem.eql(u8, key.name, "len"))) return null;
    return key.name[place.path.len..];
}

fn arrayByteKey(ctx: Ctx, target: ArrayBytePlace, suffix: []const u8) !state_mod.FieldKey {
    return .{
        .parent = target.parent,
        .name = try ctx.seen.internBytePath(ctx.gpa, target.path, suffix),
    };
}

fn bindArrayByteRepair(
    ctx: Ctx,
    state: *AbstractState,
    target: ArrayBytePlace,
    suffix: []const u8,
) !void {
    const key = try arrayByteKey(ctx, target, suffix);
    try state.bindWrittenField(ctx.gpa, key, false);
    if (target.path.len != 0) return;
    if (state_mod.diagnosticSymbolicRange(suffix)) |range| {
        if (range.length != suffix.len) return;
        try state.symbolic_prefixes.put(ctx.gpa, .{
            .array = target.parent, .counter = range.counter,
        }, .{
            .scale = range.scale, .offset = range.offset,
            .extent = range.extent, .capped = range.capped,
        });
        return;
    }
    const range = state_mod.diagnosticArrayRange(suffix) orelse return;
    if (range.length != suffix.len) return;
    if (range.range) {
        try state.markArrayRangeComplete(ctx.gpa, target.parent, range.start, range.end);
    } else try state.setExactElement(ctx.gpa, target.parent, range.start, true);
}

fn bindArrayByteHole(
    ctx: Ctx,
    state: *AbstractState,
    target: ArrayBytePlace,
    suffix: []const u8,
) !void {
    const key = try arrayByteKey(ctx, target, suffix);
    try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
    if (target.path.len != 0) return;
    const range = state_mod.diagnosticArrayRange(suffix) orelse return;
    // A descendant hole is not a whole-slot hole that poisons siblings.
    if (range.length != suffix.len) return;
    if (!range.range) try state.setExactElement(ctx.gpa, target.parent, range.start, false);
}

/// A negative base survives selected repairs, but not a whole-scope overwrite.
fn arrayByteHasEntireUndefinedBase(state: *const AbstractState, source: ArrayBytePlace) bool {
    const proof = state.entireUndefinedFieldPrefix(source.parent, source.path) orelse return false;
    for (state.written_fields.keys()) |key| {
        if (key.parent != source.parent) continue;
        const prefix = state_mod.diagnosticFieldPrefix(key.name, source.path) orelse continue;
        if (prefix >= proof) return false;
    }
    for ([_][]const state_mod.FieldKey{
        state.undefined_field_values.keys(), state.unknown_field_values.keys(),
    }) |keys| {
        for (keys) |key| {
            if (key.parent != source.parent) continue;
            const prefix = state_mod.diagnosticFieldPrefix(key.name, source.path) orelse continue;
            if (prefix < proof) continue;
            const exact = state.entireUndefinedFieldPrefix(source.parent, key.name) orelse return false;
            if (exact < state_mod.diagnosticFieldPrefix(key.name, key.name).?) return false;
        }
    }
    return true;
}

fn optionalValueChildPath(value: ArrayBytePlace, path: []const u8, child: []const u8) bool {
    if (value.path.len == 0) return std.mem.eql(u8, path, child);
    return path.len == value.path.len + 1 + child.len and
        std.mem.startsWith(u8, path, value.path) and path[value.path.len] == '.' and
        std.mem.eql(u8, path[value.path.len + 1 ..], child);
}

/// Select an existing ALL byte-base while ignoring only the enclosing tag
/// repair. Payload repairs and unproved mutations still defeat the witness.
fn optionalPayloadIsEntirelyUndefined(ctx: Ctx, state: *const AbstractState, value: ArrayBytePlace) bool {
    if (if (value.path.len == 0)
        localIsEntirelyUndefined(ctx, state, value.parent)
    else
        fieldIsEntirelyUndefined(ctx, state, value.parent, value.path)) return true;
    if (!fieldValueMayBeUndefined(ctx, state, value.parent, value.path)) return false;
    const proof = state.entireUndefinedFieldPrefix(value.parent, value.path) orelse return false;
    for (state.written_fields.keys()) |key| {
        if (key.parent != value.parent) continue;
        if (optionalValueChildPath(value, key.name, cfg.diagnostic_optional_tag)) continue;
        if (state_mod.diagnosticFieldPrefix(key.name, value.path)) |written| {
            if (written >= proof) return false;
        } else if (state_mod.diagnosticFieldPrefix(value.path, key.name) != null) return false;
    }
    for ([_][]const state_mod.FieldKey{
        state.undefined_field_values.keys(), state.unknown_field_values.keys(),
    }) |keys| {
        for (keys) |key| {
            if (key.parent != value.parent) continue;
            if (optionalValueChildPath(value, key.name, cfg.diagnostic_optional_tag)) continue;
            const ancestor = state_mod.diagnosticFieldPrefix(key.name, value.path);
            if (ancestor == null and state_mod.diagnosticFieldPrefix(value.path, key.name) == null) continue;
            if (ancestor != null and ancestor.? < proof) continue;
            const exact = state.entireUndefinedFieldPrefix(value.parent, key.name) orelse return false;
            const scope = state_mod.diagnosticFieldPrefix(key.name, key.name).?;
            if (exact < scope) return false;
        }
    }
    return true;
}

fn captureByteSuffix(ctx: Ctx, source: ArrayBytePlace, key: state_mod.FieldKey, optional_payload: bool) ?[]const u8 {
    // An optional slice capture selects its descriptor, unlike an array-byte
    // copy through a slice, which deliberately excludes ptr/len descriptors.
    const suffix = if (optional_payload and source.path.len == 0 and ctx.locals[@intFromEnum(source.parent)].is_slice)
        if (key.parent == source.parent and key.name.len != 0) key.name else return null
    else
        arrayByteSuffix(ctx, source, key) orelse return null;
    const tail = if (suffix.len != 0 and suffix[0] == '.') suffix[1..] else suffix;
    if (optional_payload and std.mem.eql(u8, tail, cfg.diagnostic_optional_tag)) return null;
    return suffix;
}

/// Immutable by-value captures replay only diagnostic bytes. Positive maps,
/// resource origins, and array initialization certificates are not destinations.
fn copyCaptureDiagnosticBytes(ctx: Ctx, state: *AbstractState, value: @TypeOf(@as(StmtKind, undefined).array_value)) !void {
    var source: ArrayBytePlace = switch (value.source) {
        .copy_of => |parent| .{ .parent = parent },
        .field_copy_of => |field| .{ .parent = field.parent, .path = field.name },
        else => return,
    };
    // An implicit pointer field selection reads the borrowed owner's bytes,
    // not the independently defined pointer header.
    if (source.path.len != 0 and ctx.locals[@intFromEnum(source.parent)].is_pointer) {
        if (state.locals.get(source.parent)) |origin| {
            if (origin == .stack and !ctx.locals[@intFromEnum(origin.stack)].is_pointer)
                source.parent = origin.stack;
        }
    }
    std.debug.assert(value.target_field == null);
    const target: ArrayBytePlace = .{ .parent = value.target };
    if (source.parent == target.parent) return;
    const entire = if (value.optional_payload)
        optionalPayloadIsEntirelyUndefined(ctx, state, source)
    else if (source.path.len == 0)
        localIsEntirelyUndefined(ctx, state, source.parent)
    else
        fieldIsEntirelyUndefined(ctx, state, source.parent, source.path);
    const base_undefined = state.fieldArrayBaseMayBeUndefined(source.parent, source.path);
    const entire_base = base_undefined and arrayByteHasEntireUndefinedBase(state, source);
    state.forgetUndefinedBytes(target.parent);
    state.forgetWrittenFields(target.parent);
    const base = try arrayByteKey(ctx, target, "");
    if (base_undefined) {
        try state.undefined_field_values.putContext(ctx.gpa, base, {}, .{});
        try state.may_undefined_values.put(ctx.gpa, target.parent, {});
    } else try state.written_fields.putContext(ctx.gpa, base, {}, .{});
    if (source.path.len == 0 and localIsArray(ctx, source.parent)) {
        var buffer: [48]u8 = undefined;
        const prefix = state.fixedPrefix(source.parent);
        if (prefix != 0) {
            const suffix = try std.fmt.bufPrint(&buffer, "[0..{d}]", .{prefix});
            try state.written_fields.putContext(ctx.gpa, try arrayByteKey(ctx, target, suffix), {}, .{});
        }
        for (state.exact_elements.keys()) |element| {
            if (element.array != source.parent) continue;
            const suffix = try std.fmt.bufPrint(&buffer, "[{d}]", .{element.index});
            try state.written_fields.putContext(ctx.gpa, try arrayByteKey(ctx, target, suffix), {}, .{});
        }
        for (state.undefined_elements.keys()) |element| {
            if (element.array != source.parent) continue;
            const suffix = try std.fmt.bufPrint(&buffer, "[{d}]", .{element.index});
            try state.undefined_field_values.putContext(ctx.gpa, try arrayByteKey(ctx, target, suffix), {}, .{});
        }
    }
    const written_count = state.written_fields.count();
    for (0..written_count) |index| {
        const key = state.written_fields.keys()[index];
        const suffix = captureByteSuffix(ctx, source, key, value.optional_payload) orelse continue;
        try state.written_fields.putContext(ctx.gpa, try arrayByteKey(ctx, target, suffix), {}, .{});
    }
    const negative_count = state.undefined_field_values.count();
    for (0..negative_count) |index| {
        const key = state.undefined_field_values.keys()[index];
        const suffix = captureByteSuffix(ctx, source, key, value.optional_payload) orelse continue;
        if (!state.fieldValueMayBeUndefined(source.parent, key.name)) continue;
        try state.undefined_field_values.putContext(ctx.gpa, try arrayByteKey(ctx, target, suffix), {}, .{});
    }
    // Physical fields can also retain a proved-undefined origin.
    for (state.fields.keys(), state.fields.values()) |key, origin| {
        if (origin != .undef or !state.fieldValueMayBeUndefined(source.parent, key.name)) continue;
        const suffix = captureByteSuffix(ctx, source, key, value.optional_payload) orelse continue;
        try state.undefined_field_values.putContext(ctx.gpa, try arrayByteKey(ctx, target, suffix), {}, .{});
    }
    const entire_count = state.entire_undefined_fields.count();
    for (0..entire_count) |index| {
        const suffix = captureByteSuffix(ctx, source, state.entire_undefined_fields.keys()[index], value.optional_payload) orelse continue;
        try state.entire_undefined_fields.putContext(ctx.gpa, try arrayByteKey(ctx, target, suffix), {}, .{});
    }
    const uncertain_count = state.uncertain_byte_writes.count();
    for (0..uncertain_count) |index| {
        const key = state.uncertain_byte_writes.keys()[index];
        if (key.parent != source.parent) continue;
        const suffix = if (state_mod.diagnosticFieldPrefix(key.name, source.path) != null)
            ""
        else captureByteSuffix(ctx, source, key, value.optional_payload) orelse continue;
        try state.uncertain_byte_writes.putContext(ctx.gpa, try arrayByteKey(ctx, target, suffix), {}, .{});
    }
    if (entire or entire_base) try state.entire_undefined_fields.putContext(ctx.gpa, base, {}, .{});
    if (entire) {
        try state.entire_undefined_values.put(ctx.gpa, target.parent, {});
    } else try state.partial_undefined_values.put(ctx.gpa, target.parent, {});
    try copyDiagnosticPrefixes(ctx, state, target, source);
}

/// Payload repairs do not write a union tag. Only a whole-root byte witness
/// can defeat a root undefined origin; descendant MAY holes cannot create one.
fn unionTagMayBeUndefined(state: *const AbstractState, local: LocalId) bool {
    const root: state_mod.FieldKey = .{ .parent = local, .name = "" };
    if (state.entire_undefined_values.contains(local)) return true;
    if (state.undefined_field_values.containsContext(root, .{})) return true;
    if (state.fields.getContext(root, .{})) |origin| if (origin == .undef) return true;
    if (state.written_fields.containsContext(root, .{})) return false;
    return (state.locals.get(local) orelse .plain) == .undef or
        state.entire_undefined_fields.containsContext(root, .{});
}

/// Replay byte masks, never resource origins or initialized-value certificates.
/// Sparse intervals and paths make work proportional to observed facts.
fn copyArrayDiagnosticBytes(
    ctx: Ctx,
    state: *AbstractState,
    value: @TypeOf(@as(StmtKind, undefined).array_value),
) !void {
    const source: ArrayBytePlace = switch (value.source) {
        .copy_of => |parent| .{ .parent = parent },
        .field_copy_of => |field| .{ .parent = field.parent, .path = field.name },
        else => return,
    };
    const target: ArrayBytePlace = .{
        .parent = value.target,
        .path = value.target_field orelse "",
    };
    if (source.parent == target.parent and std.mem.eql(u8, source.path, target.path)) return;
    const root_source = source.path.len == 0;
    const root_target = target.path.len == 0;
    // Capture the exact negative guarantee before replacing destination facts.
    // MAY masks alone must never certify an entirely undefined transport.
    const source_entirely_undefined = if (root_source)
        localIsEntirelyUndefined(ctx, state, source.parent)
    else
        fieldIsEntirelyUndefined(ctx, state, source.parent, source.path);
    const source_base_covered = if (root_source)
        state.baseComplete(source.parent) or arrayHasWrittenCoverage(ctx, state, source.parent)
    else
        state.fieldArrayBaseIsDefined(source.parent, source.path);
    const base_undefined = if (source_base_covered)
        false
    else
        state.fieldArrayBaseMayBeUndefined(source.parent, source.path);
    const source_has_entire_base = base_undefined and arrayByteHasEntireUndefinedBase(state, source);
    var partial = root_source and state.partial_undefined_values.contains(source.parent);
    const source_has_value_certificate = if (root_source)
        !state.unknown_values.contains(source.parent)
    else
        state.fieldValueIsDefined(source.parent, source.path);
    // Destination repairs can remove map entries. Freeze only source paths,
    // not the whole state, before replaying into the same unordered ledger.
    var repair_paths: [16][]const u8 = undefined;
    var repair_count: usize = 0;
    var extra_repairs: std.ArrayListUnmanaged([]const u8) = .empty;
    defer extra_repairs.deinit(ctx.gpa);
    for (state.written_fields.keys()) |key| {
        const suffix = arrayByteSuffix(ctx, source, key) orelse continue;
        if (repair_count < repair_paths.len)
            repair_paths[repair_count] = suffix
        else
            try extra_repairs.append(ctx.gpa, suffix);
        repair_count += 1;
    }

    if (root_target) {
        _ = state.may_undefined_values.swapRemove(target.parent);
        _ = state.partial_undefined_values.swapRemove(target.parent);
        _ = state.entire_undefined_values.swapRemove(target.parent);
        if (root_source) {
            try state.copyArrayInitialization(ctx.gpa, target.parent, source.parent);
        } else {
            state.forgetInitializationArray(target.parent);
            if (source_base_covered) try state.markArrayComplete(ctx.gpa, target.parent);
        }
    }
    const base: state_mod.FieldKey = .{ .parent = target.parent, .name = target.path };
    try state.bindWrittenField(ctx.gpa, base, base_undefined);
    if (base_undefined) {
        try state.undefined_field_values.putContext(ctx.gpa, base, {}, .{});
        if (root_target) try state.may_undefined_values.put(ctx.gpa, target.parent, {});
    }

    // Physical root-array coverage is also a field-path byte witness, so an
    // inherited negative base cannot swallow a copied repair.
    if (root_source) {
        var buffer: [48]u8 = undefined;
        const prefix = state.fixedPrefix(source.parent);
        if (prefix != 0) {
            const suffix = try std.fmt.bufPrint(&buffer, "[0..{d}]", .{prefix});
            try bindArrayByteRepair(ctx, state, target, suffix);
            partial = true;
        }
        const count = state.exact_elements.count();
        var index: usize = 0;
        while (index < count) : (index += 1) {
            const element = state.exact_elements.keys()[index];
            if (element.array != source.parent) continue;
            const suffix = try std.fmt.bufPrint(&buffer, "[{d}]", .{element.index});
            try bindArrayByteRepair(ctx, state, target, suffix);
            partial = true;
        }
        var symbolic_buffer: [128]u8 = undefined;
        const symbolic_count = state.symbolic_prefixes.count();
        index = 0;
        while (index < symbolic_count) : (index += 1) {
            const key = state.symbolic_prefixes.keys()[index];
            if (key.array != source.parent) continue;
            const range = state.symbolic_prefixes.values()[index];
            const suffix = try std.fmt.bufPrint(
                &symbolic_buffer, "[0..${d}:{d}:{d}:{d}:{d}]",
                .{ @intFromEnum(key.counter), range.scale, range.offset,
                    range.extent, @intFromBool(range.capped) },
            );
            try bindArrayByteRepair(ctx, state, target, suffix);
            partial = true;
        }
    }
    for (repair_paths[0..@min(repair_count, repair_paths.len)]) |suffix|
        try bindArrayByteRepair(ctx, state, target, suffix);
    for (extra_repairs.items) |suffix|
        try bindArrayByteRepair(ctx, state, target, suffix);
    if (repair_count != 0) partial = true;
    const field_count = state.fields.count();
    var index: usize = 0;
    while (index < field_count) : (index += 1) {
        const key = state.fields.keys()[index];
        const origin = state.fields.values()[index];
        if (origin == .undef or state.unknown_field_values.containsContext(key, .{})) continue;
        const suffix = arrayByteSuffix(ctx, source, key) orelse continue;
        try bindArrayByteRepair(ctx, state, target, suffix);
        partial = true;
    }

    // Holes follow repairs. A broad initialized base must never erase an
    // exact undefined overwrite, including a nested field of one slot.
    const negative_count = state.undefined_field_values.count();
    index = 0;
    while (index < negative_count) : (index += 1) {
        const key = state.undefined_field_values.keys()[index];
        const suffix = arrayByteSuffix(ctx, source, key) orelse continue;
        if (!state.fieldValueMayBeUndefined(source.parent, key.name)) continue;
        try bindArrayByteHole(ctx, state, target, suffix);
    }
    index = 0;
    while (index < field_count) : (index += 1) {
        const key = state.fields.keys()[index];
        if (state.fields.values()[index] != .undef) continue;
        const suffix = arrayByteSuffix(ctx, source, key) orelse continue;
        if (!state.fieldValueMayBeUndefined(source.parent, key.name)) continue;
        try bindArrayByteHole(ctx, state, target, suffix);
    }
    if (root_source) {
        var buffer: [48]u8 = undefined;
        const count = state.undefined_elements.count();
        index = 0;
        while (index < count) : (index += 1) {
            const element = state.undefined_elements.keys()[index];
            if (element.array != source.parent) continue;
            const suffix = try std.fmt.bufPrint(&buffer, "[{d}]", .{element.index});
            // Physical certificates keep their old hole until a strict write.
            // A later exact diagnostic repair nevertheless replaces these bytes.
            if (state.fieldBytesAreWritten(source.parent, suffix) and
                !state.fieldValueMayBeUndefined(source.parent, suffix)) continue;
            try bindArrayByteHole(ctx, state, target, suffix);
        }
    }
    if (partial or !base_undefined)
        try state.partial_undefined_values.put(ctx.gpa, target.parent, {});
    if (value.diagnostic_only or !source_has_value_certificate) {
        if (root_target) {
            try state.unknown_values.put(ctx.gpa, target.parent, {});
        } else try state.unknown_field_values.putContext(ctx.gpa, base, {}, .{});
        for (state.fields.keys()) |key| {
            if (arrayByteSuffix(ctx, target, key) == null) continue;
            try state.unknown_field_values.putContext(ctx.gpa, key, {}, .{});
        }
    }
    // Replay exact negative bases with their copied repair/MAY exceptions.
    // A partially repaired base is not an entirely undefined whole value.
    const entire_count = state.entire_undefined_fields.count();
    if (source_has_entire_base)
        try state.entire_undefined_fields.putContext(ctx.gpa, base, {}, .{});
    index = 0;
    while (index < entire_count) : (index += 1) {
        const key = state.entire_undefined_fields.keys()[index];
        const suffix = arrayByteSuffix(ctx, source, key) orelse continue;
        const copied = try arrayByteKey(ctx, target, suffix);
        try state.entire_undefined_fields.putContext(ctx.gpa, copied, {}, .{});
    }
    const uncertain_count = state.uncertain_byte_writes.count();
    index = 0;
    while (index < uncertain_count) : (index += 1) {
        const key = state.uncertain_byte_writes.keys()[index];
        if (key.parent != source.parent) continue;
        const suffix = if (state_mod.diagnosticFieldPrefix(key.name, source.path) != null)
            ""
        else arrayByteSuffix(ctx, source, key) orelse continue;
        try state.uncertain_byte_writes.putContext(ctx.gpa, try arrayByteKey(ctx, target, suffix), {}, .{});
    }
    // Existing resource-field records stay physical. Certificate revocation
    // is not a new MAY write: keep its exact negative scope only when proved
    // by the corresponding current source scope.
    for (state.fields.keys()) |key| {
        const suffix = arrayByteSuffix(ctx, target, key) orelse continue;
        const source_key = if (root_source)
            state_mod.FieldKey{ .parent = source.parent, .name = suffix }
        else
            try arrayByteKey(ctx, source, suffix);
        if (!source_entirely_undefined and
            !fieldIsEntirelyUndefined(ctx, state, source.parent, source_key.name)) continue;
        try state.entire_undefined_fields.putContext(ctx.gpa, key, {}, .{});
    }
    if (source_entirely_undefined) {
        try state.entire_undefined_fields.putContext(ctx.gpa, base, {}, .{});
        if (root_target) try state.entire_undefined_values.put(ctx.gpa, target.parent, {});
    } else if (!root_target) {
        _ = state.entire_undefined_values.swapRemove(target.parent);
    }
    try copyDiagnosticPrefixes(ctx, state, target, source);
}

fn copyDiagnosticPrefixes(ctx: Ctx, state: *AbstractState, target: ArrayBytePlace, source: ArrayBytePlace) !void {
    const count = state.symbolic_prefixes.count();
    for (0..count) |index| {
        const key = state.symbolic_prefixes.keys()[index];
        if (key.array != source.parent) continue;
        const suffix = arrayByteSuffix(ctx, source, .{ .parent = key.array, .name = key.array_path }) orelse continue;
        const target_array = try arrayByteKey(ctx, target, suffix);
        const source_count: cfg.IndexTerm = if (key.counter_path.len == 0)
            .{ .local = .{ .local = key.counter } }
        else
            .{ .field = .{ .parent = key.counter, .name = key.counter_path, .is_unsigned = true } };
        var target_count = source_count;
        if (key.counter == source.parent and key.counter_path.len != 0) {
            if (arrayByteSuffix(ctx, source, .{ .parent = key.counter, .name = key.counter_path })) |count_suffix| {
                const count_key = try arrayByteKey(ctx, target, count_suffix);
                target_count = .{ .field = .{ .parent = count_key.parent, .name = count_key.name, .is_unsigned = true } };
            }
        }
        try state.copyPrefixValue(ctx.gpa, target_array, target_count,
            .{ .parent = key.array, .name = key.array_path }, source_count);
    }
}

fn fieldAssignmentIsDefined(ctx: Ctx, state: *const AbstractState, assignment: @TypeOf(@as(StmtKind, undefined).field_assign), origin: Origin) bool {
    if (origin == .undef) return false;
    if (assignment.reads_old_value and
        !state.fieldValueIsDefined(assignment.parent, assignment.name)) return false;
    if (!valueInputsAreDefined(ctx, state, &assignment.selected_inputs, false)) return false;
    const target_info = ctx.locals[@intFromEnum(assignment.parent)];
    if (state.integer_domains.len != 0 and target_info.is_slice and std.mem.eql(u8, assignment.name, "len")) {
        // Every header update carries its own source certificate and evaluated
        // bounds, including copies from a saved header scalar.
        if (!assignment.defined) return false;
        for (assignment.inputs) |input| {
            const local = input orelse continue;
            if (assignment.rhs_kind == .field_copy_of and local == assignment.rhs_kind.field_copy_of.parent) continue;
            if (!localInputIsDefined(ctx, state, local, true)) return false;
        }
    }
    switch (assignment.rhs_kind) {
        .copy_of => |source| {
            if (localIsArray(ctx, source)) return arrayHasFullCoverage(ctx, state, source);
            return !state.unknown_values.contains(source);
        },
        .field_copy_of => |source| {
            if (state.integer_domains.len != 0) {
                // This flag certifies supported source shape, not the state
                // of the enclosing object's unrelated payload.
                if (!assignment.defined) return false;
                for (assignment.inputs) |input| {
                    const local = input orelse continue;
                    if (local == source.parent) continue;
                    if (!localInputIsDefined(ctx, state, local, false)) return false;
                }
            }
            return scalarFieldIsDefined(ctx, state, source.parent, source.name);
        },
        else => {},
    }
    if (!assignment.defined) return false;
    for (assignment.inputs) |input| {
        const local = input orelse continue;
        if (state.unknown_values.contains(local)) return false;
        if (state.locals.get(local)) |value| {
            if (value == .undef and !arrayHasFullCoverage(ctx, state, local)) return false;
        }
    }
    return true;
}

/// Diagnostic question: does this store read an operand proved undefined?
fn fieldAssignmentReadsUndefined(ctx: Ctx, state: *const AbstractState, assignment: @TypeOf(@as(StmtKind, undefined).field_assign)) bool {
    if (assignment.value_has_undefined_origin or assignment.entire_value_undefined) return true;
    if (bindingMayBeUndefined(ctx, state, assignment.rhs_kind, &assignment.selected_inputs)) return true;
    if (assignment.reads_old_value and state.fieldValueMayBeUndefined(assignment.parent, assignment.name)) return true;
    for (assignment.inputs) |input| {
        const local = input orelse continue;
        if (assignment.rhs_kind == .stack_ref and local == assignment.rhs_kind.stack_ref) continue;
        if (assignment.rhs_kind == .field_copy_of and local == assignment.rhs_kind.field_copy_of.parent) continue;
        if (localIsProvedUndefined(ctx, state, local)) return true;
    }
    return false;
}

fn fieldValueMayBeUndefined(ctx: Ctx, state: *const AbstractState, parent: LocalId, path: []const u8) bool {
    const info = ctx.locals[@intFromEnum(parent)];
    if (localIsArray(ctx, parent) and (std.mem.eql(u8, path, "len") or std.mem.eql(u8, path, "ptr"))) return false;
    if (localIsArray(ctx, parent)) if (state_mod.diagnosticArrayRange(path)) |element| {
        if (!element.range and state.hasInitializedElement(parent, .{ .constant = element.start })) {
            for (state.undefined_field_values.keys()) |key| {
                if (key.parent != parent or key.name.len == 0) continue;
                if ((state_mod.diagnosticFieldPrefix(key.name, path) != null or
                    state_mod.diagnosticFieldPrefix(path, key.name) != null) and
                    state.fieldValueMayBeUndefined(parent, path)) return true;
            }
            return false;
        }
    };
    if (path.len == 0 and !info.is_pointer and state.entire_undefined_values.contains(parent)) return true;
    if (std.mem.indexOf(u8, path, ".*")) |marker| {
        const header = path[0..marker];
        if (fieldValueMayBeUndefined(ctx, state, parent, header)) return true;
        const pointer = state.fields.getContext(.{ .parent = parent, .name = header }, .{}) orelse return false;
        if (pointer != .stack) return false;
        const suffix = path[marker + 2 ..];
        if (suffix.len == 0) return localIsProvedUndefined(ctx, state, pointer.stack);
        return fieldValueMayBeUndefined(ctx, state, pointer.stack, if (suffix[0] == '.') suffix[1..] else suffix);
    }
    if (info.is_slice and std.mem.eql(u8, path, "[]")) {
        if (localIsProvedUndefined(ctx, state, parent)) return true;
        if (state.undefined_field_values.containsContext(.{ .parent = parent, .name = "[]" }, .{})) return true;
        for (state.undefined_elements.keys()) |hole| if (hole.array == parent) return true;
        if (state.fields.getContext(.{ .parent = parent, .name = "ptr" }, .{})) |pointer| {
            if (pointer == .stack) return localIsProvedUndefined(ctx, state, pointer.stack);
        }
        return false;
    }
    if (path.len == 0 and !info.is_pointer and localIsArray(ctx, parent))
        return localIsProvedUndefined(ctx, state, parent);
    if (state.fieldValueMayBeUndefined(parent, path)) return true;
    if (state.fieldBytesAreWritten(parent, path)) return false;
    if (ctx.locals[@intFromEnum(parent)].is_pointer) {
        const origin = state.locals.get(parent) orelse return false;
        if (origin == .stack) {
            if (path.len == 0 and !ctx.locals[@intFromEnum(origin.stack)].is_pointer and localIsArray(ctx, origin.stack))
                return localIsProvedUndefined(ctx, state, origin.stack);
            if (localIsArray(ctx, origin.stack) and
                (std.mem.eql(u8, path, "len") or std.mem.eql(u8, path, "ptr"))) return false;
            return state.fieldValueMayBeUndefined(origin.stack, path);
        }
    }
    return false;
}

fn undefinedFieldBytesRemain(state: *const AbstractState, local: LocalId) bool {
    for (state.undefined_field_values.keys()) |key| {
        if (key.parent == local and state.fieldValueMayBeUndefined(local, key.name)) return true;
    }
    return false;
}

/// Diagnostic tag bytes use the same written/undefined ledger as other fields.
pub fn optionalTagMayBeUndefined(ctx: Ctx, state: *const AbstractState, local: LocalId) bool {
    return optionalTagBytesMayBeUndefined(ctx, state, local, cfg.diagnostic_optional_tag);
}

fn optionalTagBytesMayBeUndefined(ctx: Ctx, state: *const AbstractState, local: LocalId, path: []const u8) bool {
    const tag: state_mod.FieldKey = .{ .parent = local, .name = path };
    // Joins can discard a tag repair while retaining payload-only negatives.
    // An exact negative tag survives that join; a payload hole is not one.
    if (state.undefined_field_values.containsContext(tag, .{}) and
        state.fieldValueMayBeUndefined(local, path)) return true;
    if (state.fieldBytesAreWritten(local, path)) return false;
    if (path.len > cfg.diagnostic_optional_tag.len) {
        const field = path[0 .. path.len - cfg.diagnostic_optional_tag.len - 1];
        return fieldIsEntirelyUndefined(ctx, state, local, field);
    }
    if (state.partial_undefined_values.contains(local)) return false;
    // A selected tag view must not recurse through localIsProvedUndefined.
    if (ctx.locals[@intFromEnum(local)].diagnostic_tag_only)
        return unionTagMayBeUndefined(state, local);
    return localIsProvedUndefined(ctx, state, local);
}

fn isOptionalTagPath(path: []const u8) bool {
    const tag = cfg.diagnostic_optional_tag;
    return std.mem.endsWith(u8, path, tag) and
        (path.len == tag.len or path[path.len - tag.len - 1] == '.');
}

fn localIsProvedUndefined(ctx: Ctx, state: *const AbstractState, local: LocalId) bool {
    const info = ctx.locals[@intFromEnum(local)];
    if (info.diagnostic_tag_only) {
        if (info.diagnostic_tag_guard) |guard| if (localIsProvedUndefined(ctx, state, guard)) return true;
        if (info.tracks_optional_tag) return optionalTagMayBeUndefined(ctx, state, local);
        return info.diagnostic_tag_may_undefined orelse unionTagMayBeUndefined(state, local);
    }
    if (state.entire_undefined_values.contains(local)) return true;
    if (ctx.locals[@intFromEnum(local)].is_slice)
        return state.fieldValueMayBeUndefined(local, "ptr") or state.fieldValueMayBeUndefined(local, "len");
    if (!ctx.locals[@intFromEnum(local)].is_pointer) {
        if (ctx.locals[@intFromEnum(local)].runtime_fields) |fields| {
            const complete = for (fields) |name| {
                if (fieldValueMayBeUndefined(ctx, state, local, name)) return true;
                if (!state.fieldBytesAreWritten(local, name)) break false;
            } else true;
            if (complete) return false;
        }
    }
    if (!ctx.locals[@intFromEnum(local)].is_pointer and undefinedFieldBytesRemain(state, local)) return true;
    if (!ctx.locals[@intFromEnum(local)].is_pointer and
        (state.isArrayComplete(local) or
            (localIsArray(ctx, local) and arrayHasWrittenCoverage(ctx, state, local)))) return false;
    // Joins can retain MAY from the old strict root after a physical repair.
    // Pointer headers are separate from their written pointee bytes.
    if (state.may_undefined_values.contains(local) and
        (info.is_pointer or !state.fieldBytesAreWritten(local, ""))) return true;
    // Physical transport can replace unknown scalar bytes while retaining
    // the old strict origin. A recorded whole-value repair defeats it here.
    if (state.locals.get(local)) |origin| if (origin == .undef and
        (info.is_pointer or !state.fieldBytesAreWritten(local, ""))) return true;
    if (!ctx.locals[@intFromEnum(local)].is_pointer and state.fieldValueMayBeUndefined(local, "")) return true;
    for (state.undefined_elements.keys()) |hole| if (hole.array == local) return true;
    return false;
}

fn localIsAggregate(ctx: Ctx, local: LocalId) bool {
    const info = ctx.locals[@intFromEnum(local)];
    return !info.is_pointer and (localIsArray(ctx, local) or info.is_slice or
        info.runtime_fields != null or info.tracks_array_payload);
}

fn fieldHasDiagnosticChildren(state: *const AbstractState, parent: LocalId, path: []const u8) bool {
    for ([_][]const state_mod.FieldKey{
        state.written_fields.keys(), state.undefined_field_values.keys(),
        state.entire_undefined_fields.keys(), state.unknown_field_values.keys(),
    }) |keys| {
        for (keys) |key| {
            if (key.parent == parent and key.name.len > path.len and
                state_mod.diagnosticFieldPrefix(path, key.name) != null) return true;
        }
    }
    return false;
}

fn localDiagnosticIsAggregate(ctx: Ctx, state: *const AbstractState, local: LocalId) bool {
    return localIsAggregate(ctx, local) or (!ctx.locals[@intFromEnum(local)].is_pointer and
        fieldHasDiagnosticChildren(state, local, ""));
}

/// Exact ALL proof for whole-value transport and strict result summaries.
/// Selected reads instead use the retained per-byte undefined mask.
fn localIsEntirelyUndefined(ctx: Ctx, state: *const AbstractState, local: LocalId) bool {
    if (state.entire_undefined_values.contains(local)) return true;
    const info = ctx.locals[@intFromEnum(local)];
    if (!info.is_pointer and
        state.entire_undefined_fields.containsContext(.{ .parent = local, .name = "" }, .{}) and
        fieldIsEntirelyUndefined(ctx, state, local, "")) return true;
    // Known record layout can prove that every runtime field is undefined,
    // even when computed constructors established those facts independently.
    if (!info.is_pointer) if (info.runtime_fields) |fields| {
        if (fields.len != 0) {
            var all_undefined = true;
            for (fields) |field| {
                if (!fieldIsEntirelyUndefined(ctx, state, local, field)) {
                    all_undefined = false;
                    break;
                }
            }
            if (all_undefined) return true;
        }
    };
    if ((state.locals.get(local) orelse .plain) != .undef) return false;
    if (state.partial_undefined_values.contains(local)) return false;
    if (!localIsProvedUndefined(ctx, state, local)) return false;
    for (state.written_fields.keys()) |key| if (key.parent == local) return false;
    if (localIsArray(ctx, local)) {
        if (state.baseComplete(local) or state.fixedPrefix(local) != 0) return false;
        for (state.exact_elements.keys()) |key| if (key.array == local) return false;
        for (state.symbolic_prefixes.keys()) |key| if (key.array == local) return false;
    }
    return true;
}

fn fieldIsEntirelyUndefined(ctx: Ctx, state: *const AbstractState, parent: LocalId, path: []const u8) bool {
    if (fixedArrayLength(ctx, parent, path) != null) return false;
    if (state.entire_undefined_values.contains(parent)) return true;
    if (!fieldValueMayBeUndefined(ctx, state, parent, path)) return false;
    const exact = state.entireUndefinedFieldPrefix(parent, path);
    const proof_prefix = exact orelse return false;
    for (state.written_fields.keys()) |key| {
        if (key.parent != parent) continue;
        if (state_mod.diagnosticFieldPrefix(key.name, path)) |written_prefix| {
            if (written_prefix >= proof_prefix) return false;
        } else if (state_mod.diagnosticFieldPrefix(path, key.name) != null) return false;
    }
    for ([_][]const state_mod.FieldKey{
        state.undefined_field_values.keys(), state.unknown_field_values.keys(),
    }) |keys| {
        for (keys) |key| {
            if (key.parent != parent) continue;
            const ancestor = state_mod.diagnosticFieldPrefix(key.name, path);
            if (ancestor == null and state_mod.diagnosticFieldPrefix(path, key.name) == null)
                continue;
            if (ancestor != null and ancestor.? < proof_prefix) continue;
            const mutation_proof = state.entireUndefinedFieldPrefix(parent, key.name);
            const mutation_scope = state_mod.diagnosticFieldPrefix(key.name, key.name).?;
            if (mutation_proof != null and mutation_proof.? >= mutation_scope) continue;
            return false;
        }
    }
    return true;
}

pub fn returnValueIsEntirelyUndefined(ctx: Ctx, state: *const AbstractState, kind: StmtKind) bool {
    if (kind != .ret) return false;
    const ret = kind.ret;
    if (ret.diagnostic_source) |source| return localIsEntirelyUndefined(ctx, state, source);
    return ret.is_literal_undef or bindingIsEntirelyUndefined(ctx, state, ret.value_kind,
        ret.entire_source_undefined, ret.value_entirely_undefined,
        ret.result_is_computation, &ret.value_inputs);
}

/// A proved-undefined operand makes an infallible scalar computation undefined.
/// Opaque calls must not use this rule merely because their arguments are read.
fn bindingIsEntirelyUndefined(
    ctx: Ctx,
    state: *const AbstractState,
    kind: ExprKind,
    entire_source: bool,
    static_entire: bool,
    computation: bool,
    inputs: []const ?cfg.ValueInput,
) bool {
    if (static_entire) return true;
    const origin_entire = switch (kind) {
        .undef => entire_source,
        .copy_of => |local| localIsEntirelyUndefined(ctx, state, local),
        .field_copy_of => |field| fieldIsEntirelyUndefined(ctx, state, field.parent, field.name),
        else => false,
    };
    return origin_entire or (computation and valueInputsAreEntirelyUndefined(ctx, state, inputs));
}

fn valueInputsAreEntirelyUndefined(ctx: Ctx, state: *const AbstractState, inputs: []const ?cfg.ValueInput) bool {
    for (inputs) |entry| switch (entry orelse continue) {
        .local => |local| if (localIsEntirelyUndefined(ctx, state, local)) return true,
        .field => |field| if (fieldIsEntirelyUndefined(ctx, state, field.parent, field.name)) return true,
        .indexed => |indexed| {
            if (indexed.field_array) |path| {
                if (state.hasInitializedFieldElement(indexed.array, path, indexed.index)) continue;
                if (fieldIsEntirelyUndefined(ctx, state, indexed.array, path)) return true;
                const known = resolveIndex(state, indexed.index) orelse continue;
                var buffer: [256]u8 = undefined;
                const selected = std.fmt.bufPrint(&buffer, "{s}[{d}]", .{ path, known }) catch continue;
                if (fieldIsEntirelyUndefined(ctx, state, indexed.array, selected)) return true;
                continue;
            }
            if (localIsEntirelyUndefined(ctx, state, indexed.array)) return true;
            const index = resolveIndex(state, indexed.index) orelse continue;
            var buffer: [32]u8 = undefined;
            const path = std.fmt.bufPrint(&buffer, "[{d}]", .{index}) catch continue;
            if (fieldIsEntirelyUndefined(ctx, state, indexed.array, path)) return true;
        },
    };
    return false;
}

fn bindingMayBeUndefined(ctx: Ctx, state: *const AbstractState, kind: ExprKind, inputs: []const ?cfg.ValueInput) bool {
    if (exprMayBeUndefined(ctx, state, kind)) return true;
    const addressed_owner: ?LocalId = switch (kind) {
        .stack_ref => |owner| owner,
        .composite_borrow, .borrowed_from => |owner| if (!ctx.locals[@intFromEnum(owner)].is_pointer and
            !ctx.locals[@intFromEnum(owner)].is_slice) owner else null,
        else => null,
    };
    for (inputs) |entry| {
        const input = entry orelse continue;
        // Taking an address consumes the address and selector, not the bytes
        // of the place. Certificate dependencies may still demand those bytes.
        if (addressed_owner) |owner| switch (input) {
            .local => |local| if (local == owner) continue,
            .field => |field| if (field.parent == owner) continue,
            .indexed => |indexed| if (indexed.array == owner) continue,
        };
        if (valueInputsMayBeUndefined(ctx, state, &.{input})) return true;
    }
    return false;
}

fn exprMayBeUndefined(ctx: Ctx, state: *const AbstractState, kind: ExprKind) bool {
    return switch (kind) {
        .undef => true,
        .copy_of => |local| localIsProvedUndefined(ctx, state, local),
        .field_copy_of => |field| fixedArrayLength(ctx, field.parent, field.name) == null and
            fieldValueMayBeUndefined(ctx, state, field.parent, field.name),
        else => false,
    };
}

fn valueInputsMayBeUndefined(ctx: Ctx, state: *const AbstractState, inputs: []const ?cfg.ValueInput) bool {
    for (inputs) |entry| switch (entry orelse continue) {
        .local => |local| if (localIsProvedUndefined(ctx, state, local)) return true,
        .field => |field| if (fixedArrayLength(ctx, field.parent, field.name) == null and
            fieldValueMayBeUndefined(ctx, state, field.parent, field.name)) return true,
        .indexed => |indexed| {
            if (indexed.field_array) |path| {
                if (fieldIndexedValueMayBeUndefined(ctx, state, indexed.array, path, indexed.index)) return true;
                continue;
            }
            if (indexed.scaled) |element| {
                if (localIsArray(ctx, indexed.array) and
                    indexIsDefined(ctx, state, .{ .local = .{ .local = element.index } }) and
                    state.hasInitializedScaledElement(indexed.array, element) and
                    !undefinedFieldBytesRemain(state, indexed.array)) continue;
            }
            if (indexedValueMayBeUndefined(ctx, state, indexed.array, indexed.index)) return true;
        },
    };
    return false;
}

fn fieldIndexedValueMayBeUndefined(ctx: Ctx, state: *const AbstractState, array: LocalId, path: []const u8, index: cfg.IndexTerm) bool {
    const correlated = state.hasInitializedFieldElement(array, path, index);
    const written = state.fieldRangeBytesAreWritten(array, path, index) or correlated;
    const selected_index = resolveIndex(state, index);
    const selected_undefined = if (selected_index) |known| blk: {
        var buffer: [256]u8 = undefined;
        const selected = std.fmt.bufPrint(&buffer, "{s}[{d}]", .{ path, known }) catch
            break :blk fieldValueMayBeUndefined(ctx, state, array, path);
        break :blk fieldValueMayBeUndefined(ctx, state, array, selected);
    } else fieldValueMayBeUndefined(ctx, state, array, path);
    return ((selected_index != null and !correlated) or !written) and selected_undefined;
}

fn indexedValueMayBeUndefined(ctx: Ctx, state: *const AbstractState, array: LocalId, index: cfg.IndexTerm) bool {
    const info = ctx.locals[@intFromEnum(array)];
    if (info.is_slice) {
        if (state.fieldValueMayBeUndefined(array, "ptr") or state.fieldValueMayBeUndefined(array, "len")) return true;
        if (!state.hasInitializedElement(array, index)) {
            if (state.undefined_field_values.containsContext(.{ .parent = array, .name = "[]" }, .{})) return true;
            for (state.undefined_elements.keys()) |hole| {
                if (hole.array == array and !state.provesComparison(.{
                    .lhs = index, .rhs = .{ .constant = hole.index }, .op = .ne,
                })) return true;
            }
        }
        const pointer = state.fields.getContext(.{ .parent = array, .name = "ptr" }, .{}) orelse return false;
        return switch (pointer) {
            .stack => |backing| if (state.unknown_field_values.containsContext(.{ .parent = array, .name = "ptr" }, .{}))
                localIsProvedUndefined(ctx, state, backing)
            else
                indexedValueMayBeUndefined(ctx, state, backing, index),
            .undef => true,
            else => false,
        };
    }
    if (!localIsArray(ctx, array)) {
        if (localIsProvedUndefined(ctx, state, array)) return true;
        if (!info.is_pointer or state.hasInitializedElement(array, index)) return false;
        for (state.undefined_elements.keys()) |hole| {
            if (hole.array == array and !state.provesComparison(.{
                .lhs = index, .rhs = .{ .constant = hole.index }, .op = .ne,
            })) return true;
        }
        if (state.fieldValueMayBeUndefined(array, "")) return true;
        if (state.locals.get(array)) |origin| {
            if (origin == .stack and origin.stack != array and localIsArray(ctx, origin.stack))
                return indexedValueMayBeUndefined(ctx, state, origin.stack, index);
        }
        return false;
    }
    if (resolveIndex(state, index)) |known| {
        var buffer: [32]u8 = undefined;
        const path = std.fmt.bufPrint(&buffer, "[{d}]", .{known}) catch unreachable;
        if (state.fieldBytesAreUnknown(array, path)) return false;
        if (state.fieldBytesAreWritten(array, path)) return false;
    }
    if (state.fieldRangeBytesAreWritten(array, "", index)) return false;
    for (state.undefined_field_values.keys()) |key| {
        if (key.parent != array or !state.fieldValueMayBeUndefined(array, key.name)) continue;
        if (state_mod.diagnosticArrayPrefixEnd(key.name)) |bound| {
            if (state.provesComparison(.{
                .lhs = index, .rhs = .{ .constant = bound }, .op = .ge,
            }) or state.provesComparison(.{
                .lhs = index, .rhs = .{ .constant = 0 }, .op = .lt,
            })) continue;
            return true;
        }
        const slot = literalArrayElementIndex(key.name) orelse return true;
        if (!state.provesComparison(.{ .lhs = index, .rhs = .{ .constant = slot }, .op = .ne })) return true;
    }
    for (state.written_fields.keys()) |key| {
        if (key.parent != array) continue;
        if (state_mod.diagnosticArrayPrefixEnd(key.name)) |bound| {
            if (state.provesComparison(.{ .lhs = index, .rhs = .{ .constant = 0 }, .op = .ge }) and
                state.provesComparison(.{ .lhs = index, .rhs = .{ .constant = bound }, .op = .lt })) return false;
            continue;
        }
        const slot = literalArrayElementIndex(key.name) orelse continue;
        if (state.provesComparison(.{ .lhs = index, .rhs = .{ .constant = slot }, .op = .eq }) and
            !state.fieldValueMayBeUndefined(array, key.name)) return false;
    }
    if (arrayHasWrittenCoverage(ctx, state, array)) return false;
    if (state.hasInitializedElement(array, index)) return false;
    for (state.undefined_elements.keys()) |hole| {
        if (hole.array == array and !state.provesComparison(.{
            .lhs = index, .rhs = .{ .constant = hole.index }, .op = .ne,
        })) return true;
    }
    if (state.may_undefined_values.contains(array)) return true;
    return if (state.locals.get(array)) |origin| origin == .undef else false;
}

fn transferFieldAssign(
    ctx: Ctx,
    state: *AbstractState,
    a: @TypeOf(@as(StmtKind, undefined).field_assign),
    pos: cfg.SrcPos,
) !void {
    if (a.diagnostic_only and a.rhs_kind == .unknown) if (a.prefix_entry) |entry| {
        const count: cfg.IndexTerm = .{ .local = .{ .local = entry.count } };
        const offset = state.termSymbolicPrefixOffset(.{ .parent = entry.array, .name = entry.path }, count);
        if ((offset != null and offset.? >= 0) or
            state.provesComparison(.{ .lhs = count, .rhs = .{ .constant = 0 }, .op = .eq })) return;
    };
    if (!a.may_write_only)
        state.forgetFieldInitialization(.{ .parent = a.parent, .name = a.name });
    if (a.may_write_only) {
        if (!fieldAssignmentReadsUndefined(ctx, state, a)) return;
        const key: state_mod.FieldKey = .{ .parent = a.parent, .name = a.name };
        // This is a unioned negative alternative, not an overwrite. In
        // particular, bindWrittenField would erase older holes and repairs.
        try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
        try state.unknown_field_values.putContext(ctx.gpa, key, {}, .{});
        try state.unknown_values.put(ctx.gpa, a.parent, {});
        return;
    }
    if (a.diagnostic_only) {
        const tag_copy = isOptionalTagPath(a.name) and
            a.rhs_kind == .field_copy_of and isOptionalTagPath(a.rhs_kind.field_copy_of.name);
        const may_undefined = if (tag_copy)
            optionalTagBytesMayBeUndefined(ctx, state, a.rhs_kind.field_copy_of.parent, a.rhs_kind.field_copy_of.name)
        else
            fieldAssignmentReadsUndefined(ctx, state, a);
        const key: state_mod.FieldKey = .{ .parent = a.parent, .name = a.name };
        if (isOptionalTagPath(a.name)) {
            const value_path = if (a.name.len == cfg.diagnostic_optional_tag.len)
                ""
            else
                a.name[0 .. a.name.len - cfg.diagnostic_optional_tag.len - 1];
            const value: ArrayBytePlace = .{ .parent = a.parent, .path = value_path };
            const entire_payload = optionalPayloadIsEntirelyUndefined(ctx, state, value);
            const entire_tag = a.entire_value_undefined or (tag_copy and
                fieldIsEntirelyUndefined(ctx, state, a.rhs_kind.field_copy_of.parent, a.rhs_kind.field_copy_of.name));
            // A tag fact changes only negative byte masks, never value,
            // pointer, lifetime, or aliased payload certificates.
            if (may_undefined) {
                // A negative tag cannot repair its ENTIRE undefined owner.
                _ = state.written_fields.swapRemoveContext(key, .{});
                try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
                if (entire_tag) {
                    try state.entire_undefined_fields.putContext(ctx.gpa, key, {}, .{});
                } else {
                    _ = state.entire_undefined_fields.swapRemoveContext(key, .{});
                    _ = state.entire_undefined_values.swapRemove(a.parent);
                }
            } else {
                try state.bindWrittenField(ctx.gpa, key, false);
                _ = state.undefined_field_values.swapRemoveContext(key, .{});
                _ = state.entire_undefined_values.swapRemove(a.parent);
            }
            if (entire_payload) {
                // Retain only a proved ALL byte-base at the actual value
                // prefix. The tag repair still defeats whole-optional ALL.
                const base: state_mod.FieldKey = .{ .parent = a.parent, .name = value_path };
                try state.entire_undefined_fields.putContext(ctx.gpa, base, {}, .{});
            }
            return;
        }
        const aggregate_copy = switch (a.rhs_kind) {
            .copy_of => |source| localDiagnosticIsAggregate(ctx, state, source),
            .field_copy_of => a.aggregate_value,
            else => false,
        };
        if (aggregate_copy) {
            try copyArrayDiagnosticBytes(ctx, state, .{
                .target = a.parent, .target_field = a.name,
                .source = a.rhs_kind, .diagnostic_only = true,
            });
            return;
        }
        if (a.preserve_undefined_descendants) {
            // These are simultaneous snapshot facts, not ordered stores.
            if (may_undefined) {
                _ = state.written_fields.swapRemoveContext(key, .{});
                try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
                if (a.entire_value_undefined)
                    try state.entire_undefined_fields.putContext(ctx.gpa, key, {}, .{})
                else
                    _ = state.entire_undefined_fields.swapRemoveContext(key, .{});
            } else try state.written_fields.putContext(ctx.gpa, key, {}, .{});
            if (a.name.len == 0)
                try state.unknown_values.put(ctx.gpa, a.parent, {})
            else
                try state.unknown_field_values.putContext(ctx.gpa, key, {}, .{});
            if (a.name.len == 0 and a.entire_value_undefined)
                try state.entire_undefined_values.put(ctx.gpa, a.parent, {})
            else if (!a.entire_value_undefined)
                _ = state.entire_undefined_values.swapRemove(a.parent);
            if (!a.entire_value_undefined and (state.locals.get(a.parent) orelse .plain) == .undef)
                try state.partial_undefined_values.put(ctx.gpa, a.parent, {});
            return;
        }
        if (a.name.len == 0 and (!ctx.locals[@intFromEnum(a.parent)].is_pointer or a.whole_value_bytes)) {
            state.forgetUndefinedBytes(a.parent);
            if (localIsArray(ctx, a.parent)) state.forgetInitializationArray(a.parent);
            if (state.locals.getPtr(a.parent)) |origin| {
                if (a.entire_value_undefined and may_undefined and (origin.* == .plain or origin.* == .undef))
                    origin.* = .undef
                else if (origin.* == .undef)
                    origin.* = .plain;
            }
            try state.unknown_values.put(ctx.gpa, a.parent, {});
            if (may_undefined) try state.may_undefined_values.put(ctx.gpa, a.parent, {});
            try state.bindWrittenField(ctx.gpa, key, may_undefined);
        } else {
            const selected: state_mod.FieldKey = .{ .parent = a.parent, .name = a.name };
            try state.unknown_field_values.putContext(ctx.gpa, selected, {}, .{});
            try state.bindWrittenField(ctx.gpa, selected, may_undefined);
            if (may_undefined) {
                try state.undefined_field_values.putContext(ctx.gpa, selected, {}, .{});
            }
            try invalidateAliasedArrayPayload(ctx, state, a.parent, a.name);
        }
        const exact = a.entire_value_undefined and may_undefined;
        try state.bindEntireUndefinedField(ctx.gpa, key, exact);
        if (a.name.len == 0 and (!ctx.locals[@intFromEnum(a.parent)].is_pointer or a.whole_value_bytes) and exact) {
            try state.entire_undefined_values.put(ctx.gpa, a.parent, {});
        } else if (!exact) {
            _ = state.entire_undefined_values.swapRemove(a.parent);
            if ((state.locals.get(a.parent) orelse .plain) == .undef)
                try state.partial_undefined_values.put(ctx.gpa, a.parent, {});
        }
        return;
    }
    if (!a.reads_old_value and a.rhs_kind == .field_copy_of and
        a.rhs_kind.field_copy_of.parent == a.parent and
        std.mem.eql(u8, a.rhs_kind.field_copy_of.name, a.name)) return;
    const entirely_undefined = bindingIsEntirelyUndefined(
        ctx, state, a.rhs_kind, a.entire_source_undefined,
        a.entire_value_undefined, a.result_is_computation, &a.selected_inputs,
    ) or (a.reads_old_value and
        fieldIsEntirelyUndefined(ctx, state, a.parent, a.name));
    var origin = try originOfInit(ctx, state, a.rhs_kind, pos);
    // Retain the selected descriptor scalar at value time. A later source
    // clobber must revoke the relation, not the already copied scalar value.
    var copied_constant: ?u64 = null;
    if (ctx.locals[@intFromEnum(a.parent)].is_slice and std.mem.eql(u8, a.name, "len") and a.rhs_kind == .field_copy_of) {
        const source = a.rhs_kind.field_copy_of;
        for (state.comparisons.items) |premise| {
            if (premise.op != .eq) continue;
            if (premise.lhs == .field and premise.rhs == .constant and
                premise.lhs.field.parent == source.parent and std.mem.eql(u8, premise.lhs.field.name, source.name))
                copied_constant = premise.rhs.constant;
            if (premise.rhs == .field and premise.lhs == .constant and
                premise.rhs.field.parent == source.parent and std.mem.eql(u8, premise.rhs.field.name, source.name))
                copied_constant = premise.lhs.constant;
        }
    }
    state.forgetFieldTermComparisons(.{ .parent = a.parent, .name = a.name });
    const key: state_mod.FieldKey = .{ .parent = a.parent, .name = a.name };
    const defined = !entirely_undefined and
        !(a.interior_view and origin == .stack and localIsArray(ctx, origin.stack)) and
        fieldAssignmentIsDefined(ctx, state, a, origin);
    // MAY taint remains diagnostic-only. Only the separate exact negative
    // proof can tag a plain field as entirely undefined.
    const reads_undefined = entirely_undefined or fieldAssignmentReadsUndefined(ctx, state, a);
    if (entirely_undefined and origin == .plain) origin = .undef;
    if (!entirely_undefined and origin == .undef) origin = .plain;
    try state.bindFieldValue(ctx.gpa, key, defined);
    try state.fields.putContext(ctx.gpa, key, origin, .{});
    try state.bindWrittenField(ctx.gpa, key, reads_undefined);
    if (reads_undefined) try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
    if (!defined) try invalidateAliasedArrayPayload(ctx, state, a.parent, a.name);
    // An aggregate field rebind revokes every descendant descriptor proof.
    var fields = state.fields.iterator();
    while (fields.next()) |entry| {
        const descendant = entry.key_ptr.*;
        if (descendant.parent == a.parent and descendant.name.len > a.name.len and
            std.mem.startsWith(u8, descendant.name, a.name) and descendant.name[a.name.len] == '.')
            try state.bindFieldValue(ctx.gpa, descendant, false);
    }
    if (defined) if (copied_constant) |constant| {
        state.feasible = try state.assumeComparison(ctx.gpa, .{
            .lhs = .{ .field = .{ .parent = a.parent, .name = a.name, .is_unsigned = true } },
            .rhs = .{ .constant = constant },
            .op = .eq,
        });
    };

    if (localIsArray(ctx, a.parent) and origin == .undef) {
        if (literalArrayElementIndex(a.name)) |index| {
            if (ctx.locals[@intFromEnum(a.parent)].array_extent) |extent| {
                if (index < extent) try state.setExactElement(ctx.gpa, a.parent, index, false);
            } else {
                try state.setExactElement(ctx.gpa, a.parent, index, false);
            }
        } else {
            state.forgetInitializationArray(a.parent);
        }
    }

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
    try state.bindEntireUndefinedField(ctx.gpa, key, entirely_undefined);
    if (!entirely_undefined) _ = state.entire_undefined_values.swapRemove(a.parent);
    const aggregate_source = a.aggregate_value or switch (a.rhs_kind) {
        .copy_of => |source| localDiagnosticIsAggregate(ctx, state, source),
        else => false,
    };
    if (aggregate_source and exprMayBeUndefined(ctx, state, a.rhs_kind)) {
        try copyArrayDiagnosticBytes(ctx, state, .{
            .target = a.parent, .target_field = a.name,
            .source = a.rhs_kind, .diagnostic_only = true,
        });
    }

    // A field store never defines its owner or an unwritten sibling.
    // Exact field facts permit selected reads while the whole-object origin
    // stays undefined. Only a complete initialization certificate promotes it.
}

test "field stores define only their selected inline storage" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{.{ .name = "value", .decl_pos = pos0() }};
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const value: LId = @enumFromInt(0);
    try state.locals.put(gpa, value, .undef);
    try transferFieldAssign(ctx, &state, .{
        .parent = value,
        .name = "part.written",
        .rhs_kind = .plain,
        .defined = true,
    }, pos0());
    try testing.expect(scalarFieldIsDefined(ctx, &state, value, "part.written"));
    try testing.expect(!scalarFieldIsDefined(ctx, &state, value, "part.missing"));
    try transferFieldUse(ctx, &state, .{ .parent = value, .name = "part.written" }, pos0(), pos1());
    try testing.expect(problems.items.len == 0);
    try transferFieldUse(ctx, &state, .{ .parent = value, .name = "part.missing" }, pos0(), pos1());
    var reported_missing = false;
    for (problems.items) |problem| {
        if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
            std.mem.indexOf(u8, problem.message, "part.missing") != null) reported_missing = true;
    }
    try testing.expect(reported_missing);
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
    // Whole aggregate transport preserves holes but only rejects an ALL proof.
    const counted_defined = if (u.counted_array) |counted| blk: {
        if (fieldValueMayBeUndefined(ctx, state, u.parent, counted.counter_path)) break :blk false;
        const offset = state.termSymbolicPrefixOffset(.{ .parent = u.parent, .name = counted.array_path },
            .{ .field = .{ .parent = u.parent, .name = counted.counter_path, .is_unsigned = true } }) orelse break :blk false;
        break :blk offset >= 0;
    } else false;
    const reads_undefined = !u.lifetime_only and !counted_defined and if (u.optional_tag_path) |path|
        optionalTagBytesMayBeUndefined(ctx, state, u.parent, path)
    else if (u.aggregate_transport)
        fieldIsEntirelyUndefined(ctx, state, u.parent, u.name)
    else
        fieldValueMayBeUndefined(ctx, state, u.parent, u.name);
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
    // `arr[i].f` on an array or slice owner: the preceding `indexed_read`
    // owns element coverage. An undefined owner root alone does not make
    // an initialized element undefined.
    const element_owner = u.name.len > 0 and u.name[0] == '[' and
        (ctx.locals[@intFromEnum(u.parent)].is_slice or localIsArray(ctx, u.parent));
    if (state.locals.get(u.parent)) |parent_origin| if (!element_owner or parent_origin != .undef) switch (parent_origin) {
        .undef => {
            if (reads_undefined and config_mod.isEnabled(ctx.config, .use_undefined)) {
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
    const origin = state.fields.getContext(key, .{}) orelse .plain;
    const parent_name = ctx.locals[@intFromEnum(u.parent)].name;
    switch (origin) {
        .arena, .arena_borrow => |aid| {
            if (config_mod.isEnabled(ctx.config, .arena_use_after_kill)) {
                if (state.arenas.get(aid)) |st| if (st.state == .dead) {
                    try reportWithNote(ctx, "arena-use-after-kill", pos, end_pos, .@"error", "`{s}{s}{s}` borrows from an arena that was deinit'd", .{ parent_name, pathSep(u.name), u.name }, if (st.killed_at) |ks|
                        .{ .site = ks, .label = "arena deinit'd here" }
                    else
                        null);
                    return;
                };
            }
        },
        .heap => |hid| {
            if (config_mod.isEnabled(ctx.config, .heap_use_after_free)) {
                if (state.heaps.get(hid)) |st| if (st.state == .dead) {
                    try reportWithNote(ctx, "heap-use-after-free", pos, end_pos, .@"error", "use of `{s}{s}{s}` after free", .{ parent_name, pathSep(u.name), u.name }, if (st.killed_at) |ks|
                        .{ .site = ks, .label = "value freed here" }
                    else
                        null);
                    return;
                };
            }
        },
        .undef => {
            if (!reads_undefined or
                !config_mod.isEnabled(ctx.config, .use_undefined)) return;
            try report(ctx, "use-undefined", pos, end_pos, .@"error", "use of `{s}{s}{s}` while still `undefined`", .{ parent_name, pathSep(u.name), u.name });
        },
        .stack => |owner_id| {
            // Field borrows from a stack owner — mirrors the .stack
            // arm in checkOriginAlive.  When the field carries an
            // owner-borrow origin (set via classifyExpr's @borrowed-
            // field route, or via struct-literal unpack of a
            // borrowed-field read), a kill of the owner invalidates
            // this read.
            if (config_mod.isEnabled(ctx.config, .heap_use_after_free)) {
                if (state.locals.get(owner_id)) |owner_origin| switch (owner_origin) {
                    .heap => |hid| {
                        if (state.heaps.get(hid)) |st| if (st.state == .dead) {
                            try reportWithNote(ctx, "heap-use-after-free", pos, end_pos, .@"error", "use of `{s}{s}{s}` (borrow from `{s}`) after free", .{ parent_name, pathSep(u.name), u.name, ctx.locals[@intFromEnum(owner_id)].name }, if (st.killed_at) |ks|
                                .{ .site = ks, .label = "value freed here" }
                            else
                                null);
                            return;
                        };
                    },
                    else => {},
                };
            }
        },
        else => {},
    }
    if (origin != .undef and (!element_owner or u.aggregate_transport) and reads_undefined and
        config_mod.isEnabled(ctx.config, .use_undefined))
    {
        try report(ctx, "use-undefined", pos, end_pos, .@"error", "use of `{s}{s}{s}` without a defined field value", .{ parent_name, pathSep(u.name), u.name });
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
    // ret owns canonical positive reporting. This statement only carries the
    // residual of [legacyStackCell] to value positions inside the aggregate.
    if (c.stack_loans.complete) return;
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
    switch (c.value_kind) {
        .stack_ref, .copy_of => {},
        else => return,
    }
    if (!config_mod.isEnabled(ctx.config, .stack_escape)) return;
    const origin = try originOfInit(ctx, state, c.value_kind, pos);
    const local = legacyStackCell(c.stack_loans, origin) orelse return;
    try reportReturnedStackCell(ctx, local, false, pos, end_pos);
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
    // Borrowing an undefined receiver does not read its payload. Only a
    // proven write may initialize it; a method name supplies no such proof.
    if (u.from_method_call and !ctx.locals[@intFromEnum(u.local)].is_pointer)
    {
        if (origin != .undef)
            try checkOriginAlive(ctx, state, origin, pos, end_pos, ctx.locals[@intFromEnum(u.local)].name);
        return;
    }
    if (localIsArray(ctx, u.local)) {
        const reads_undefined = localIsEntirelyUndefined(ctx, state, u.local);
        if (reads_undefined) try reportUncoveredArrayUse(ctx, state, u.local, false, false, pos, end_pos);
        const read_origin = if (!reads_undefined and origin == .undef) Origin.plain else origin;
        try checkOriginAlive(ctx, state, read_origin, pos, end_pos, ctx.locals[@intFromEnum(u.local)].name);
        return;
    }
    const may_undefined = if (u.tag_only)
        optionalTagMayBeUndefined(ctx, state, u.local)
    else if (u.optional_payload)
        localIsProvedUndefined(ctx, state, u.local)
    else if (localDiagnosticIsAggregate(ctx, state, u.local))
        localIsEntirelyUndefined(ctx, state, u.local)
    else
        localIsProvedUndefined(ctx, state, u.local);
    if (origin != .undef and may_undefined)
        try checkOriginAlive(ctx, state, .undef, pos, end_pos, ctx.locals[@intFromEnum(u.local)].name);
    const read_origin = if (origin == .undef and !may_undefined) Origin.plain else origin;
    try checkOriginAlive(ctx, state, read_origin, pos, end_pos, ctx.locals[@intFromEnum(u.local)].name);
}

fn transferGap(
    ctx: Ctx,
    state: *AbstractState,
    g: @TypeOf(@as(StmtKind, undefined).lowering_gap),
) !void {
    // A gap the builder marked `may_assign_locals = false` is a
    // statement that provably CANNOT write a local: `call-untracked`
    // carries no pointer argument, and `assign-target`'s `arr[i] = X`
    // writes one ELEMENT, not the array.  Collapsing origins for it
    // erases facts the statement never touched, and the flag is the
    // only thing that distinguishes the two claims — reading past it
    // made every gap a claim about locals no gap can support.
    if (!g.may_assign_locals) return;
    for (0..ctx.locals.len) |index| {
        const local: LocalId = @enumFromInt(index);
        if (localIsArray(ctx, local)) {
            // Preserve byte witnesses while revoking their value certificate.
            // An opaque store cannot introduce a proved-undefined byte.
            if (arrayHasWrittenCoverage(ctx, state, local) and !localIsProvedUndefined(ctx, state, local)) {
                try state.markArrayComplete(ctx.gpa, local);
            }
            try state.unknown_values.put(ctx.gpa, local, {});
        }
    }
    for (0..ctx.locals.len) |index| {
        const local: LocalId = @enumFromInt(index);
        if (!ctx.locals[index].is_control_local) state.facts.forgetLocal(local);
        state.forgetInitializationLocal(local);
        // Exact writes and recorded holes survive opaque effects.
    }
    state.forgetAllComparisons();
    // Unknown effects invalidate certificates, but cannot certify a write.
    // Keep undefined origins until a concrete assignment initializes them.
}

fn sliceElementIsDefined(ctx: Ctx, state: *const AbstractState, slice: LocalId, index: cfg.IndexTerm) bool {
    if (indexedValueMayBeUndefined(ctx, state, slice, index)) return false;
    const length: cfg.IndexTerm = .{ .field = .{ .parent = slice, .name = "len", .is_unsigned = true } };
    const pointer = state.fields.getContext(.{ .parent = slice, .name = "ptr" }, .{}) orelse return false;
    if (!scalarFieldIsDefined(ctx, state, slice, "ptr")) return false;
    return switch (pointer) {
        .stack => |backing| indexIsDefined(ctx, state, index) and
            scalarFieldIsDefined(ctx, state, slice, "len") and localIsArray(ctx, backing) and
            !state.unknown_values.contains(backing) and
            state.provesNonNegative(index) and state.provesLessThan(index, length) and
            (arrayHasFullCoverage(ctx, state, backing) or state.hasInitializedElement(backing, index)),
        .undef => false,
        // External initialized bytes have no local holes, and a runtime bounds
        // check is separate from payload definedness: the length certificate
        // only matters when it selects a slot of local storage.
        else => true,
    };
}

fn transferIndexedRead(
    ctx: Ctx,
    state: *AbstractState,
    read: @TypeOf(@as(StmtKind, undefined).indexed_read),
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    const origin = state.locals.get(read.array);
    const info = ctx.locals[@intFromEnum(read.array)];
    if (read.field_array) |path| {
        // A projected index selects bytes, not every hole in the backing field.
        const correlated = state.hasInitializedFieldElement(read.array, path, read.index);
        const written = state.fieldRangeBytesAreWritten(read.array, path, read.index) or correlated;
        const selected_index = resolveIndex(state, read.index);
        const selected_undefined = if (selected_index) |index| blk: {
            var buffer: [256]u8 = undefined;
            const selected = std.fmt.bufPrint(&buffer, "{s}[{d}]", .{ path, index }) catch
                break :blk fieldValueMayBeUndefined(ctx, state, read.array, path);
            break :blk fieldValueMayBeUndefined(ctx, state, read.array, selected);
        } else fieldValueMayBeUndefined(ctx, state, read.array, path);
        if (((selected_index != null and !correlated) or !written) and selected_undefined)
            try checkOriginAlive(ctx, state, .undef, pos, end_pos, info.name);
        if (origin) |root| if (root != .undef)
            try checkOriginAlive(ctx, state, root, pos, end_pos, info.name);
        return;
    }
    if (info.is_slice) {
        const initialized = !indexedValueMayBeUndefined(ctx, state, read.array, read.index);
        const pointer = state.fields.getContext(.{ .parent = read.array, .name = "ptr" }, .{});
        if (!initialized) try checkOriginAlive(ctx, state, .undef, pos, end_pos, info.name);
        if (origin) |root| try checkOriginAlive(ctx, state, root, pos, end_pos, info.name);
        if (pointer) |root| {
            if (root != .undef) try checkOriginAlive(ctx, state, root, pos, end_pos, info.name);
        }
    } else if (localIsArray(ctx, read.array)) {
        // Scaled byte witnesses are diagnostic coverage, not value certificates.
        const scaled_initialized = if (read.scaled) |element|
            indexIsDefined(ctx, state, .{ .local = .{ .local = element.index } }) and
                state.hasInitializedScaledElement(read.array, element)
        else
            false;
        const selected_field = if (read.name) |name| blk: {
            const slot = state_mod.diagnosticArrayRange(name) orelse break :blk false;
            break :blk slot.length < name.len;
        } else false;
        const initialized = (if (selected_field)
            !fieldValueMayBeUndefined(ctx, state, read.array, read.name.?)
        else
            !indexedValueMayBeUndefined(ctx, state, read.array, read.index)) or
            (scaled_initialized and !undefinedFieldBytesRemain(state, read.array));
        try reportUncoveredArrayUse(ctx, state, read.array, initialized, false, pos, end_pos);
        if (origin) |root| {
            const read_origin = if (initialized and root == .undef) Origin.plain else root;
            try checkOriginAlive(ctx, state, read_origin, pos, end_pos, info.name);
        }
    } else if (info.is_pointer) {
        if (indexedValueMayBeUndefined(ctx, state, read.array, read.index))
            try checkOriginAlive(ctx, state, .undef, pos, end_pos, info.name);
        if (origin) |root| if (root != .undef)
            try checkOriginAlive(ctx, state, root, pos, end_pos, info.name);
    } else if (origin) |root| {
        try checkOriginAlive(ctx, state, root, pos, end_pos, info.name);
    }
    if (read.name) |name| try checkIndexedFieldOrigin(ctx, state, read.array, name, pos, end_pos);
}

fn transferIndexedWrite(
    ctx: Ctx,
    state: *AbstractState,
    write: @TypeOf(@as(StmtKind, undefined).indexed_write),
    pos: cfg.SrcPos,
) !void {
    // An indexed store initializes bytes, not the descriptor used to reach
    // them. Undefined slice headers cannot be repaired by writing a slot.
    if (ctx.locals[@intFromEnum(write.array)].is_slice) {
        const name = ctx.locals[@intFromEnum(write.array)].name;
        if (state.locals.get(write.array)) |origin|
            try checkOriginAlive(ctx, state, if (origin == .undef and !localIsProvedUndefined(ctx, state, write.array)) .plain else origin, pos, pos, name);
        // A header seeded `undefined` keeps undefined descriptor-word
        // records while the owner itself reads as initialized.
        for ([_][]const u8{ "ptr", "len" }) |word| {
            const origin = state.fields.getContext(.{ .parent = write.array, .name = word }, .{}) orelse continue;
            if (origin == .undef and state.fieldValueMayBeUndefined(write.array, word))
                try checkOriginAlive(ctx, state, origin, pos, pos, name);
        }
    }
    const rhs_origin = try originOfInit(ctx, state, write.rhs_kind, pos);
    const reads_undefined = indexedRhsReadsUndefined(ctx, state, write, rhs_origin);
    const rhs_entire = bindingIsEntirelyUndefined(ctx, state, write.rhs_kind,
        write.entire_source_undefined, write.value_entirely_undefined,
        write.result_is_computation, write.selected_inputs[0 .. write.certificate_only_input orelse write.selected_inputs.len]);
    const info = ctx.locals[@intFromEnum(write.array)];
    // Retain the initialized byte base when an exact overwrite adds a hole.
    // This witness carries no payload or lifetime certificate.
    if (localIsArray(ctx, write.array) and
        (state.baseComplete(write.array) or arrayHasWrittenCoverage(ctx, state, write.array)))
        try state.written_fields.putContext(ctx.gpa, .{ .parent = write.array, .name = "" }, {}, .{});
    if (!rhs_entire and !info.is_pointer and !info.is_slice) {
        _ = state.entire_undefined_values.swapRemove(write.array);
        if ((state.locals.get(write.array) orelse .plain) == .undef)
            try state.partial_undefined_values.put(ctx.gpa, write.array, {});
    }
    const aggregate_rhs = switch (write.rhs_kind) {
        .copy_of => |source| localDiagnosticIsAggregate(ctx, state, source),
        .field_copy_of => |source| fieldHasDiagnosticChildren(state, source.parent, source.name),
        else => false,
    };
    if (!write.diagnostic_children_follow and !reads_undefined and !rhs_entire and !info.is_pointer and !info.is_slice and
        (resolveIndex(state, write.index) == null or !aggregate_rhs))
    {
        const index = write.diagnostic_index orelse write.index;
        if (index == .unknown or indexIsDefined(ctx, state, index))
            try recordPossibleIndexedWrite(ctx, state, write, index);
    }
    if (write.all_elements and (info.is_pointer or info.is_slice or !localIsArray(ctx, write.array))) {
        try transferFieldAssign(ctx, state, .{
            .parent = write.array,
            .name = if (info.is_slice) "[]" else "",
            .rhs_kind = if (reads_undefined) .undef else .plain,
            .diagnostic_only = true,
            .entire_value_undefined = rhs_entire,
        }, pos);
        return;
    }
    if (write.field_array) |path| {
        const rhs_defined = indexedRhsIsDefined(ctx, state, write, rhs_origin);
        if (!rhs_defined) state.forgetFieldInitialization(.{ .parent = write.array, .name = path });
        state.forgetFieldTermComparisons(.{ .parent = write.array, .name = path });
        if (write.name) |name| {
            const key: state_mod.FieldKey = .{ .parent = write.array, .name = name };
            try state.bindFieldValue(ctx.gpa, key, rhs_defined);
            try state.fields.putContext(ctx.gpa, key, rhs_origin, .{});
            try state.bindWrittenField(ctx.gpa, key, reads_undefined);
            if (reads_undefined)
                try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
            try state.bindEntireUndefinedField(ctx.gpa, key, rhs_entire);
        } else if (!rhs_defined) {
            // An unplaced undefined overwrite can hit any existing slot.
            // Revoke descendants too: a formerly complete element must not
            // override this uncertain array ancestor. Retain lifetime origins.
            for (state.fields.keys()) |key| {
                if (key.parent != write.array or !std.mem.startsWith(u8, key.name, path)) continue;
                if (key.name.len != path.len and key.name[path.len] != '[' and key.name[path.len] != '.') continue;
                try state.unknown_field_values.putContext(ctx.gpa, key, {}, .{});
            }
            try state.unknown_field_values.putContext(ctx.gpa, .{ .parent = write.array, .name = path }, {}, .{});
            if (reads_undefined) {
                try state.bindWrittenField(ctx.gpa, .{ .parent = write.array, .name = path }, true);
                try state.undefined_field_values.putContext(ctx.gpa, .{ .parent = write.array, .name = path }, {}, .{});
            }
            state.forgetEntireUndefinedField(.{ .parent = write.array, .name = path });
        }
        if (write.name == null and rhs_defined and fieldValueMayBeUndefined(ctx, state, write.array, path)) {
            state.forgetEntireUndefinedField(.{ .parent = write.array, .name = path });
            try state.unknown_field_values.putContext(ctx.gpa, .{ .parent = write.array, .name = path }, {}, .{});
        }
        if (!rhs_defined) try invalidateAliasedArrayPayload(ctx, state, write.array, write.name orelse path);
        if (rhs_defined) state.extendTermSymbolicPrefix(.{ .parent = write.array, .name = path }, write.index);
        return;
    }
    if (write.name) |name| {
        const key: state_mod.FieldKey = .{ .parent = write.array, .name = name };
        try state.bindFieldValue(ctx.gpa, key, indexedRhsIsDefined(ctx, state, write, rhs_origin));
        try state.fields.putContext(ctx.gpa, key, rhs_origin, .{});
        try state.bindWrittenField(ctx.gpa, key, reads_undefined);
        if (reads_undefined)
            try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
        try state.bindEntireUndefinedField(ctx.gpa, key, rhs_entire);
    }
    if (write.name == null and !write.all_elements and !info.is_pointer and !info.is_slice) {
        if (resolveIndex(state, write.index)) |index| {
            var buffer: [32]u8 = undefined;
            const temporary = try std.fmt.bufPrint(&buffer, "[{d}]", .{index});
            if (reads_undefined or state.fieldValueMayBeUndefined(write.array, temporary) or
                state.entireUndefinedFieldPrefix(write.array, temporary) != null)
            {
                const path = try ctx.seen.internBytePath(ctx.gpa, "", temporary);
                const key: state_mod.FieldKey = .{ .parent = write.array, .name = path };
                try state.bindWrittenField(ctx.gpa, key, reads_undefined);
                if (!indexedRhsIsDefined(ctx, state, write, rhs_origin))
                    try state.unknown_field_values.putContext(ctx.gpa, key, {}, .{});
                if (reads_undefined) try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
                try state.bindEntireUndefinedField(ctx.gpa, key, rhs_entire);
            }
        } else if (!rhs_entire and localIsProvedUndefined(ctx, state, write.array)) {
            state.forgetEntireUndefinedFields(write.array);
        }
    }
    var rhs_defined = indexedRhsIsDefined(ctx, state, write, rhs_origin);
    if (!rhs_defined and !reads_undefined) {
        // Unproved is not undefined: the slot is written for use-undefined,
        // but the array's payload certificate becomes unknown.
        try state.unknown_values.put(ctx.gpa, write.array, {});
        rhs_defined = true;
    }
    if (!rhs_defined and resolveIndex(state, write.index) == null) {
        if (indexedAggregateSource(ctx, state, write) != null) {
            // Keep the same strict revocation, but replay child negatives
            // below instead of manufacturing a whole-element MAY origin.
            state.forgetInitializationArray(write.array);
            state.forgetWrittenFields(write.array);
            try state.unknown_values.put(ctx.gpa, write.array, {});
        } else try markPayloadMayBeUndefined(ctx, state, write.array);
    }
    const defined = indexIsDefined(ctx, state, write.index) and rhs_defined;
    if (write.all_elements) {
        if (defined) {
            try state.markArrayComplete(ctx.gpa, write.array);
        } else {
            state.forgetInitializationArray(write.array);
            if (reads_undefined) try markPayloadMayBeUndefined(ctx, state, write.array);
        }
        if (rhs_entire) {
            try state.entire_undefined_values.put(ctx.gpa, write.array, {});
            try state.bindEntireUndefinedField(ctx.gpa, .{ .parent = write.array, .name = "" }, true);
        }
        return;
    }
    // A defined store cannot shrink a complete array's coverage, wherever an
    // index we cannot place lands it. The index is checked as a read elsewhere.
    if (rhs_defined and state.baseComplete(write.array) and resolveIndex(state, write.index) == null) return;
    const extent = ctx.locals[@intFromEnum(write.array)].array_extent orelse {
        if (resolveIndex(state, write.index)) |index| {
            try state.setExactElement(ctx.gpa, write.array, index, rhs_defined);
        } else if (!rhs_defined) {
            try markPayloadMayBeUndefined(ctx, state, write.array);
        }
        return;
    };
    const resolved = resolveIndex(state, write.index);
    if (!rhs_defined) {
        if (resolved) |index| {
            if (index < extent) try state.setExactElement(ctx.gpa, write.array, index, false);
        } else {
            state.forgetInitializationArray(write.array);
        }
        return;
    }
    // Unsupported placement cannot create coverage. A defined overwrite also
    // cannot remove prior prefix/sparse coverage merely because we lack a term.
    if (!defined) return;
    if (!state.provesIndexInBounds(write.index, extent)) return;

    const prefix_before = state.fixedPrefix(write.array);
    if (resolved) |index| {
        try state.setExactElement(ctx.gpa, write.array, index, true);
    }
    try extendSymbolicPrefix(ctx, state, write.array, write.index, prefix_before, extent);
}

/// Possible placement suppresses inherited holes, never strict certificates.
fn recordPossibleIndexedWrite(
    ctx: Ctx,
    state: *AbstractState,
    write: @TypeOf(@as(StmtKind, undefined).indexed_write),
    index: cfg.IndexTerm,
) !void {
    var buffer: [96]u8 = undefined;
    if (index == .field and std.mem.eql(u8, index.field.name, "value") and index.field.offset == 0) {
        if (ctx.locals[@intFromEnum(index.field.parent)].enum_value_indices) |indices| {
            const extent = ctx.locals[@intFromEnum(write.array)].array_extent;
            for (indices) |selected| {
                if (extent != null and selected >= extent.?) continue;
                const path = try std.fmt.bufPrint(&buffer, "[{d}]", .{selected});
                const owned = try ctx.seen.internBytePath(ctx.gpa, "", path);
                try state.uncertain_byte_writes.putContext(ctx.gpa, .{ .parent = write.array, .name = owned }, {}, .{});
            }
            return;
        }
    }
    const path = if (resolveIndex(state, index)) |selected| fixed: {
        const suffix = if (write.name) |name|
            if (state_mod.diagnosticArrayRange(name)) |slot| name[slot.length..] else ""
        else "";
        break :fixed try std.fmt.bufPrint(&buffer, "[{d}..{d}]{s}", .{ selected, std.math.add(u64, selected, 1) catch return, suffix });
    } else if (write.name) |name| name else blk: {
        const extent = ctx.locals[@intFromEnum(write.array)].array_extent orelse break :blk "";
        if (write.diagnostic_scaled) |scaled| {
            if (scaled.scale > 1)
                break :blk try std.fmt.bufPrint(&buffer, "[%{d}:{d}:{d}]", .{ scaled.offset, scaled.scale, extent });
        }
        if (write.diagnostic_stride) |stride|
            break :blk try std.fmt.bufPrint(&buffer, "[%{d}:{d}:{d}]", .{ stride.offset, stride.period, extent });
        const range = state.diagnosticWriteRange(index, extent);
        if (range.start >= range.end) return;
        break :blk try std.fmt.bufPrint(&buffer, "[{d}..{d}]", .{ range.start, range.end });
    };
    const owned = try ctx.seen.internBytePath(ctx.gpa, "", path);
    try state.uncertain_byte_writes.putContext(ctx.gpa, .{ .parent = write.array, .name = owned }, {}, .{});
}

/// Diagnostic question: does this store write a value proved undefined?
fn indexedRhsReadsUndefined(
    ctx: Ctx,
    state: *const AbstractState,
    write: @TypeOf(@as(StmtKind, undefined).indexed_write),
    rhs_origin: Origin,
) bool {
    if (write.value_has_undefined_origin or write.value_entirely_undefined) return true;
    if (rhs_origin == .undef and write.rhs_kind != .copy_of and write.rhs_kind != .field_copy_of) return true;
    if (exprMayBeUndefined(ctx, state, write.rhs_kind)) return true;
    for (write.inputs) |input| {
        const local = input orelse continue;
        if (localIsProvedUndefined(ctx, state, local)) return true;
    }
    return valueInputsMayBeUndefined(ctx, state,
        write.selected_inputs[0 .. write.certificate_only_input orelse write.selected_inputs.len]);
}

fn indexedAggregateSource(
    ctx: Ctx,
    state: *const AbstractState,
    write: @TypeOf(@as(StmtKind, undefined).indexed_write),
) ?LocalId {
    if (write.result_is_computation or write.rhs_kind != .copy_of or write.all_elements or
        write.field_array != null or ctx.locals[@intFromEnum(write.array)].array_extent == null) return null;
    const source = write.rhs_kind.copy_of;
    const info = ctx.locals[@intFromEnum(source)];
    if (source == write.array or info.is_pointer or info.is_slice or
        (!localIsArray(ctx, source) and (!info.tracks_array_payload or info.tracks_scalar_value)) or
        localIsEntirelyUndefined(ctx, state, source)) return null;
    return source;
}

/// A whole-element copy transports the source's child masks at its placement.
/// Flattening a partial source to a whole-slot MAY taint loses its siblings.
fn replayIndexedAggregateBytes(
    ctx: Ctx,
    state: *AbstractState,
    write: @TypeOf(@as(StmtKind, undefined).indexed_write),
) !void {
    const source = indexedAggregateSource(ctx, state, write) orelse return;
    const extent = ctx.locals[@intFromEnum(write.array)].array_extent orelse return;
    const resolved = resolveIndex(state, write.index);
    var buffer: [64]u8 = undefined;
    const temporary = if (resolved) |index| fixed: {
        if (index >= extent) return;
        break :fixed try std.fmt.bufPrint(&buffer, "[{d}]", .{index});
    } else unplaced: {
        const range = state.diagnosticWriteRange(write.index, extent);
        if (range.start >= range.end) return;
        break :unplaced try std.fmt.bufPrint(&buffer, "[{d}..{d}]", .{ range.start, range.end });
    };
    const path = try ctx.seen.internBytePath(ctx.gpa, "", temporary);
    try copyArrayDiagnosticBytes(ctx, state, .{
        .target = write.array,
        .target_field = path,
        .source = .{ .copy_of = source },
        .diagnostic_only = true,
    });
    // Replayed holes remain authoritative. Other bytes must not inherit a
    // coarse whole-source MAY taint when a loop join drops repair witnesses.
    try state.uncertain_byte_writes.putContext(ctx.gpa, .{ .parent = write.array, .name = path }, {}, .{});
}

fn transferArrayRangeComplete(
    ctx: Ctx,
    state: *AbstractState,
    range: @TypeOf(@as(StmtKind, undefined).array_range_complete),
) !void {
    const info = ctx.locals[@intFromEnum(range.array)];
    const extent = info.array_extent orelse {
        state.forgetInitializationArray(range.array);
        return;
    };
    if (!info.is_array or info.is_pointer or range.start > range.end or range.end > extent) {
        state.forgetInitializationArray(range.array);
        return;
    }
    if (range.start == range.end) return;
    const write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
        .array = range.array,
        .index = .{ .constant = range.start },
        .rhs_kind = if (range.value_has_undefined_origin) .undef else .plain,
        .defined = range.value_defined,
        .inputs = range.inputs,
        .selected_inputs = range.selected_inputs,
    };
    const covered = storageInputsAreCovered(ctx, state, &range.inputs) and
        indexedRhsIsDefined(ctx, state, write, .plain);
    if (!covered and indexedRhsReadsUndefined(ctx, state, write, .plain)) {
        state.forgetInitializationArray(range.array);
        try state.may_undefined_values.put(ctx.gpa, range.array, {});
    } else {
        if (!covered) try state.unknown_values.put(ctx.gpa, range.array, {});
        try state.markArrayRangeComplete(ctx.gpa, range.array, range.start, range.end);
    }
    // Certificate revocation clears initialization repairs. Replay the exact
    // source bytes afterwards, without restoring any strict certificate.
    if (range.diagnostic_source) |source| {
        try copyCaptureDiagnosticBytes(ctx, state, .{
            .target = range.array, .source = .{ .copy_of = source }, .mask_only = true,
        });
    }
}

fn transferArrayMemsetPrefix(
    ctx: Ctx,
    state: *AbstractState,
    prefix: @TypeOf(@as(StmtKind, undefined).array_memset_prefix),
    pos: cfg.SrcPos,
) !void {
    const info = ctx.locals[@intFromEnum(prefix.array)];
    const extent = info.array_extent orelse {
        state.forgetInitializationArray(prefix.array);
        return;
    };
    if (!info.is_array or info.is_pointer or !indexIsDefined(ctx, state, prefix.count)) {
        state.forgetInitializationArray(prefix.array);
        return;
    }
    switch (prefix.count) {
        .constant => {},
        .local => |term| {
            if (term.offset != 0 or !ctx.locals[@intFromEnum(term.local)].is_unsigned) {
                state.forgetInitializationArray(prefix.array);
                return;
            }
        },
        else => {
            state.forgetInitializationArray(prefix.array);
            return;
        },
    }
    // A successful slice bounds an existing count; it never defines that count.
    state.feasible = try state.assumeComparison(ctx.gpa, .{
        .lhs = prefix.count,
        .rhs = .{ .constant = 0 },
        .op = .ge,
    });
    if (!state.feasible) return;
    state.feasible = try state.assumeComparison(ctx.gpa, .{
        .lhs = prefix.count,
        .rhs = .{ .constant = extent },
        .op = .le,
    });
    if (!state.feasible) return;
    const rhs_origin = try originOfInit(ctx, state, prefix.rhs_kind, pos);
    const write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
        .array = prefix.array,
        .index = prefix.count,
        .rhs_kind = prefix.rhs_kind,
        .defined = prefix.defined,
        .selected_inputs = prefix.selected_inputs,
        .value_has_undefined_origin = prefix.value_has_undefined_origin,
        .entire_source_undefined = prefix.entire_source_undefined,
    };
    if (!indexedRhsIsDefined(ctx, state, write, rhs_origin) or
        !valueInputsAreDefined(ctx, state, &prefix.selected_inputs, false))
    {
        if (prefix.count == .constant and prefix.count.constant == 0) return;
        if (indexedRhsReadsUndefined(ctx, state, write, rhs_origin)) {
            if (prefix.count == .constant) {
                const count = prefix.count.constant;
                if (count == extent) {
                    var whole_write = write;
                    whole_write.all_elements = true;
                    whole_write.value_entirely_undefined = prefix.entire_source_undefined;
                    try transferIndexedWrite(ctx, state, whole_write, pos);
                    return;
                }
                // Keep untouched coverage; this mask poisons only filled lanes.
                var buffer: [48]u8 = undefined;
                const temporary = try std.fmt.bufPrint(&buffer, "[0..{d}]", .{count});
                const path = try ctx.seen.internBytePath(ctx.gpa, "", temporary);
                const key: state_mod.FieldKey = .{ .parent = prefix.array, .name = path };
                try state.bindWrittenField(ctx.gpa, key, true);
                try state.undefined_field_values.putContext(ctx.gpa, key, {}, .{});
                try state.unknown_field_values.putContext(ctx.gpa, key, {}, .{});
                try state.bindEntireUndefinedField(ctx.gpa, key, prefix.entire_source_undefined);
                try state.unknown_values.put(ctx.gpa, prefix.array, {});
                if (!prefix.entire_source_undefined) {
                    _ = state.entire_undefined_values.swapRemove(prefix.array);
                    if ((state.locals.get(prefix.array) orelse .plain) == .undef)
                        try state.partial_undefined_values.put(ctx.gpa, prefix.array, {});
                }
                return;
            }
            state.forgetInitializationArray(prefix.array);
            try state.may_undefined_values.put(ctx.gpa, prefix.array, {});
            return;
        }
        // Unknown stores write bytes without supplying a value certificate.
        try state.unknown_values.put(ctx.gpa, prefix.array, {});
    }
    if (resolveIndex(state, prefix.count)) |count| if (count == 0) return;
    var hole_index: usize = 0;
    while (hole_index < state.undefined_elements.count()) {
        const hole = state.undefined_elements.keys()[hole_index];
        if (hole.array == prefix.array and state.provesLessThan(
            .{ .constant = hole.index },
            prefix.count,
        )) {
            _ = state.undefined_elements.swapRemoveAt(hole_index);
        } else hole_index += 1;
    }
    switch (prefix.count) {
        .constant => |count| {
            if (count != 0) {
                var buffer: [48]u8 = undefined;
                const temporary = try std.fmt.bufPrint(&buffer, "[0..{d}]", .{count});
                if (state.fieldValueMayBeUndefined(prefix.array, temporary)) {
                    const path = try ctx.seen.internBytePath(ctx.gpa, "", temporary);
                    try state.bindWrittenField(ctx.gpa, .{ .parent = prefix.array, .name = path }, false);
                }
            }
            try state.setFixedPrefix(ctx.gpa, prefix.array, @max(state.fixedPrefix(prefix.array), count));
            if (count == extent) try state.markArrayComplete(ctx.gpa, prefix.array);
        },
        .local => |term| {
            if (state.symbolicPrefixOffset(prefix.array, term.local)) |offset| {
                if (offset >= 0) return;
            }
            var buffer: [128]u8 = undefined;
            const temporary = try std.fmt.bufPrint(&buffer, "[0..${d}:1:0:{d}:0]", .{ @intFromEnum(term.local), extent });
            const path = try ctx.seen.internBytePath(ctx.gpa, "", temporary);
            try state.bindWrittenField(ctx.gpa, .{ .parent = prefix.array, .name = path }, false);
            try state.setSymbolicPrefix(ctx.gpa, prefix.array, term.local, 0, extent);
        },
        else => unreachable,
    }
}

fn indexedLocalInputIsDefined(ctx: Ctx, state: *const AbstractState, local: LocalId) bool {
    if (!ctx.locals[@intFromEnum(local)].is_pointer and localIsArray(ctx, local))
        return arrayHasFullCoverage(ctx, state, local);
    if (state.unknown_values.contains(local)) return false;
    if (state.locals.get(local)) |origin| if (origin == .undef) return false;
    // Pointer values carry descriptors, not the initializedness of pointees.
    // A copied by-value aggregate must include every tracked member instead.
    if (!ctx.locals[@intFromEnum(local)].is_pointer and !tracksScalarValue(ctx, state, local) and
        !state.fieldValueIsDefined(local, "")) return false;
    return true;
}

fn indexedRhsIsDefined(
    ctx: Ctx,
    state: *const AbstractState,
    write: @TypeOf(@as(StmtKind, undefined).indexed_write),
    rhs_origin: Origin,
) bool {
    if (!write.defined or write.rhs_kind == .undef or
        write.value_has_undefined_origin or write.value_entirely_undefined) return false;
    if (rhs_origin == .undef) {
        const source = switch (write.rhs_kind) {
            .copy_of => |local| local,
            else => return false,
        };
        if (!localIsArray(ctx, source) or !arrayHasFullCoverage(ctx, state, source)) return false;
    }
    for (write.inputs) |input| {
        const local = input orelse continue;
        if (!indexedLocalInputIsDefined(ctx, state, local)) return false;
    }
    for (write.selected_inputs) |entry| {
        const input = entry orelse continue;
        switch (input) {
            .local => |local| {
                if (!indexedLocalInputIsDefined(ctx, state, local)) return false;
            },
            .field => |field| {
                if (!state.fieldValueIsDefined(field.parent, field.name)) return false;
            },
            .indexed => {
                if (!valueInputsAreDefined(ctx, state, &.{input}, false)) return false;
            },
        }
    }
    return true;
}

fn transferCounterStep(
    ctx: Ctx,
    state: *AbstractState,
    step: @TypeOf(@as(StmtKind, undefined).counter_step),
) !void {
    if (!ctx.locals[@intFromEnum(step.local)].is_unsigned or (step.step != 1 and step.step != -1)) {
        forgetLocalValueFacts(ctx, state, step.local);
        return;
    }
    state.facts.forgetLocal(step.local);
    try state.stepCounter(ctx.gpa, step.local, step.step);
    const origin = state.locals.get(step.local) orelse .plain;
    if (origin != .undef) try state.nonnegative_locals.put(ctx.gpa, step.local, {});
}

fn tracksIntegerValue(state: *const AbstractState, local: LocalId) bool {
    if (state.integer_domains.len == 0) return false;
    const id = @intFromEnum(local);
    std.debug.assert(id < state.integer_domains.len);
    return state.integer_domains[id].kind != .unknown;
}

fn tracksScalarValue(ctx: Ctx, state: *const AbstractState, local: LocalId) bool {
    return ctx.locals[@intFromEnum(local)].tracks_scalar_value or tracksIntegerValue(state, local);
}

/// A return certificate uses the same payload dependencies as element stores.
/// No result type, resource origin, or empty opaque expression creates a value.
pub fn returnValueIsDefined(ctx: Ctx, state: *const AbstractState, returned: cfg.StmtKind) bool {
    const value = returned.ret;
    return value.value_defined and !value.is_literal_undef and
        copiedPayloadIsDefined(state, value.value_kind, true) and
        valueInputsAreDefined(ctx, state, &value.value_inputs, false);
}

pub fn returnValueMayBeUndefined(ctx: Ctx, state: *const AbstractState, returned: cfg.StmtKind) bool {
    const value = returned.ret;
    if (value.diagnostic_source) |source| return localIsProvedUndefined(ctx, state, source);
    return value.value_has_undefined_origin or value.is_literal_undef or
        bindingMayBeUndefined(ctx, state, value.value_kind, &value.value_inputs);
}

fn scalarValueIsDefined(
    ctx: Ctx,
    state: *const AbstractState,
    kind: ExprKind,
    defined: bool,
    inputs: []const ?cfg.ValueInput,
) bool {
    // An empty context has no source type/certificate publication. Explicit
    // scalar flags alone cannot certify a synthetic graph's value.
    if (state.integer_domains.len == 0 or !defined) return false;
    if (kind == .field_copy_of) {
        return scalarFieldIsDefined(ctx, state, kind.field_copy_of.parent, kind.field_copy_of.name) and
            scalarInputsAreDefined(ctx, state, inputs);
    }
    return copiedPayloadIsDefined(state, kind, defined) and scalarInputsAreDefined(ctx, state, inputs);
}

/// Fixed array length is type metadata, not a read of its element payload.
fn fixedArrayLength(ctx: Ctx, parent: LocalId, path: []const u8) ?u64 {
    const info = ctx.locals[@intFromEnum(parent)];
    if (info.is_pointer or !std.mem.eql(u8, path, "len")) return null;
    return info.array_extent;
}

fn scalarFieldIsDefined(ctx: Ctx, state: *const AbstractState, parent: LocalId, path: []const u8) bool {
    if (fixedArrayLength(ctx, parent, path) != null) return true;
    const info = ctx.locals[@intFromEnum(parent)];
    if (info.is_slice and (std.mem.eql(u8, path, "len") or std.mem.eql(u8, path, "ptr"))) {
        // Explicit certificates distinguish defined descriptor bits from
        // the bytes behind them. A ptr certificate additionally identifies
        // the supported zero-offset backing view, not initialized payload.
        if (!state.fields.containsContext(.{ .parent = parent, .name = path }, .{})) return false;
        return state.fieldValueIsDefined(parent, path);
    }
    // A pointer header alone never certifies storage behind it. Exact field
    // stores do, provided the header remains defined and the field's negative
    // or descendant certificates do not invalidate that store.
    if (info.is_pointer) {
        if (state.unknown_values.contains(parent)) return false;
        if (state.locals.get(parent)) |origin| if (origin == .undef) return false;
        if (!state.fields.containsContext(.{ .parent = parent, .name = path }, .{})) return false;
    }
    return state.fieldValueIsDefined(parent, path);
}

/// Evaluate computed scalar dependencies before rebinding their destination.
/// Type endpoints can bound an existing value, but cannot create that value.
fn scalarInputsAreDefined(ctx: Ctx, state: *const AbstractState, inputs: []const ?cfg.ValueInput) bool {
    return valueInputsAreDefined(ctx, state, inputs, true);
}

fn localInputIsDefined(ctx: Ctx, state: *const AbstractState, local: LocalId, scalar_only: bool) bool {
    const info = ctx.locals[@intFromEnum(local)];
    if (!scalar_only and localIsArray(ctx, local)) {
        // Only element coverage certifies array bytes. A header
        // or an old whole-array undef marker does not replace it.
        return !info.is_pointer and !state.unknown_values.contains(local) and arrayHasFullCoverage(ctx, state, local);
    }
    const scalar_source = state.integer_domains.len != 0 and tracksScalarValue(ctx, state, local);
    if (!scalar_source and state.scalarValue(local) == null and
        (scalar_only or !info.tracks_array_payload)) return false;
    if (info.is_pointer or state.unknown_values.contains(local)) return false;
    if (state.locals.get(local)) |origin| if (origin == .undef) return false;
    // A defined root does not repair undefined or uncertain descendants.
    // Scalar selectors retain their narrower field-specific certificates.
    return scalar_only or state.fieldValueIsDefined(local, "");
}

fn valueInputsAreDefined(
    ctx: Ctx,
    state: *const AbstractState,
    inputs: []const ?cfg.ValueInput,
    scalar_only: bool,
) bool {
    for (inputs) |entry| {
        const input = entry orelse continue;
        switch (input) {
            .local => |local| {
                if (!localInputIsDefined(ctx, state, local, scalar_only)) return false;
            },
            .field => |field| {
                if (!scalarFieldIsDefined(ctx, state, field.parent, field.name)) return false;
            },
            .indexed => |indexed| {
                // Field-prefix byte facts do not supply a selected-value certificate.
                if (indexed.field_array != null) return false;
                // Written-but-unproved slots satisfy use-undefined, not certificates.
                if (state.unknown_values.contains(indexed.array)) return false;
                if (indexed.modulo) |modulo| {
                    if (!localIsArray(ctx, indexed.array) or
                        ctx.locals[@intFromEnum(indexed.array)].is_slice) return false;
                    const extent = ctx.locals[@intFromEnum(indexed.array)].array_extent orelse return false;
                    if (!arrayHasFullCoverage(ctx, state, indexed.array) or
                        !moduloIndexInBounds(ctx, state, modulo, extent)) return false;
                    continue;
                }
                if (ctx.locals[@intFromEnum(indexed.array)].is_slice) {
                    if (!sliceElementIsDefined(ctx, state, indexed.array, indexed.index)) return false;
                    continue;
                }
                if (!indexIsDefined(ctx, state, indexed.index)) return false;
                if (!localIsArray(ctx, indexed.array)) return false;
                const extent = ctx.locals[@intFromEnum(indexed.array)].array_extent orelse return false;
                // A complete array needs no bounds proof: a defined selection
                // reads initialized bytes or panics before reading anything.
                if (arrayHasFullCoverage(ctx, state, indexed.array)) continue;
                if (!state.provesIndexInBounds(indexed.index, extent) or
                    !state.hasInitializedElement(indexed.array, indexed.index)) return false;
            },
        }
    }
    return true;
}

/// A remainder is bounded only by its positive divisor. Its input must still
/// exist; a type endpoint or fully written array cannot initialize that input.
fn moduloIndexInBounds(ctx: Ctx, state: *const AbstractState, modulo: cfg.ModuloIndex, extent: u64) bool {
    if (modulo.modulus == 0 or modulo.modulus > extent) return false;
    const input = @intFromEnum(modulo.input);
    if (input >= state.integer_domains.len) return false;
    switch (state.integer_domains[input].kind) {
        .unsigned, .unsigned_unbounded => {},
        else => return false,
    }
    return indexIsDefined(ctx, state, .{ .local = .{ .local = modulo.input } });
}

fn indexIsDefined(ctx: Ctx, state: *const AbstractState, index: cfg.IndexTerm) bool {
    return switch (index) {
        .unknown => false,
        .constant => true,
        .local => |term| !state.unknown_values.contains(term.local) and
            if (state.locals.get(term.local)) |origin| origin != .undef else true,
        .field => |term| scalarFieldIsDefined(ctx, state, term.parent, term.name),
    };
}

fn resolveIndex(state: *const AbstractState, index: cfg.IndexTerm) ?u64 {
    return switch (index) {
        .unknown, .field => null,
        .constant => |value| value,
        .local => |term| blk: {
            const value = state.scalarValue(term.local) orelse break :blk null;
            if (term.offset == 0) break :blk value;
            if (term.offset == 1) break :blk std.math.add(u64, value, 1) catch null;
            if (term.offset == -1) break :blk if (value == 0) null else value - 1;
            break :blk null;
        },
    };
}

fn extendSymbolicPrefix(
    ctx: Ctx,
    state: *AbstractState,
    array: LocalId,
    index: cfg.IndexTerm,
    fixed_prefix_before: u64,
    extent: u64,
) !void {
    const term = switch (index) {
        .local => |local| local,
        else => return,
    };
    if (term.offset < -1 or term.offset > 1) return;

    var reaches_prefix = false;
    if (state.symbolicPrefixOffset(array, term.local)) |offset| {
        reaches_prefix = offset == term.offset;
    }
    if (!reaches_prefix) {
        if (resolveIndex(state, index)) |concrete| {
            reaches_prefix = concrete == fixed_prefix_before;
        }
    }
    if (!reaches_prefix) return;
    const next_offset = term.offset + 1;
    if (next_offset < -1 or next_offset > 1) return;
    try state.setSymbolicPrefix(ctx.gpa, array, term.local, next_offset, extent);
}


fn reportUncoveredArrayUse(
    ctx: Ctx,
    state: *const AbstractState,
    array: LocalId,
    initialized: bool,
    is_return: bool,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    if (initialized or !localIsProvedUndefined(ctx, state, array)) return;
    const origin = state.locals.get(array) orelse return;
    // `checkOriginAlive` emits the existing use-undefined diagnostic
    // for an undefined root.  This path handles holes in a root whose
    // coarse lifetime origin is otherwise plain or resource-bearing.
    if (origin == .undef or !config_mod.isEnabled(ctx.config, .use_undefined)) return;
    if (is_return) {
        try report(ctx, "use-undefined", pos, end_pos, .@"error", "returning a value that is still `undefined`", .{});
    } else {
        try report(ctx, "use-undefined", pos, end_pos, .@"error", "use of `{s}` while still `undefined`", .{ctx.locals[@intFromEnum(array)].name});
    }
}

fn checkIndexedFieldOrigin(
    ctx: Ctx,
    state: *const AbstractState,
    array: LocalId,
    name: []const u8,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    if (name.len > 0 and name[0] == '[') {
        if (std.mem.indexOfScalar(u8, name, ']')) |end| {
            const element_name = name[0 .. end + 1];
            if (!std.mem.eql(u8, name, element_name)) {
                const ancestor = state.fields.getContext(.{ .parent = array, .name = element_name }, .{});
                if (ancestor != null and ancestor.? != .undef)
                    try checkFieldOrigin(ctx, state, array, element_name, pos, end_pos);
            }
        }
    }
    try checkFieldOrigin(ctx, state, array, name, pos, end_pos);
}

fn checkFieldOrigin(
    ctx: Ctx,
    state: *const AbstractState,
    array: LocalId,
    name: []const u8,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
) !void {
    const key: state_mod.FieldKey = .{ .parent = array, .name = name };
    const origin = state.fields.getContext(key, .{}) orelse return;
    // Name the access as written (`arr[0].ptr`), not just the field path.
    // Display-only: an over-long name falls back to the bare path.
    var shown_buf: [256]u8 = undefined;
    const shown = std.fmt.bufPrint(&shown_buf, "{s}{s}{s}", .{ ctx.locals[@intFromEnum(array)].name, pathSep(name), name }) catch name;
    const diagnostic_origin = if (fieldValueMayBeUndefined(ctx, state, array, name)) Origin.undef else
        if (origin == .undef) Origin.plain else origin;
    try checkOriginAlive(ctx, state, diagnostic_origin, pos, end_pos, shown);
    if (diagnostic_origin == .undef and origin != .undef)
        try checkOriginAlive(ctx, state, origin, pos, end_pos, shown);
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
        .stack_ref => |src_local| blk: {
            // Address formation defines a header even when payload is undefined.
            // Resource-backed storage still carries the owner's lifetime.
            const source = state.locals.get(src_local) orelse break :blk .{ .stack = src_local };
            break :blk switch (source) {
                .arena => |id| .{ .arena_borrow = id },
                .arena_borrow, .heap => source,
                else => .{ .stack = src_local },
            };
        },
        .composite_borrow => |src_local| state.locals.get(src_local) orelse .plain,
        .heap_alloc => |info| blk: {
            if (info.allocator_source) |source| {
                const origin = switch (source) {
                    .local => |local| state.locals.get(local),
                    .field => |field| state.fields.getContext(.{ .parent = field.parent, .name = field.name }, .{}),
                    .indexed => null,
                };
                if (origin) |allocator| switch (allocator) {
                    .arena => |id| break :blk .{ .arena_borrow = id },
                    .arena_borrow => break :blk allocator,
                    else => {},
                };
            }
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

const KillSiteNote = struct { site: state_mod.KillSite, label: []const u8 };

fn reportWithNote(
    ctx: Ctx,
    comptime rule_id: []const u8,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
    severity: Severity,
    comptime fmt: []const u8,
    args: anytype,
    kill_site: ?KillSiteNote,
) !void {
    try reportWithIdentity(ctx, rule_id, pos, end_pos, severity, fmt, args, kill_site, null);
}

fn reportWithIdentity(
    ctx: Ctx,
    comptime rule_id: []const u8,
    pos: cfg.SrcPos,
    end_pos: cfg.SrcPos,
    severity: Severity,
    comptime fmt: []const u8,
    args: anytype,
    kill_site: ?KillSiteNote,
    owner_byte: ?u32,
) !void {
    if (!ctx.report_enabled) return;
    // One source operation can be reached through several cleanup paths,
    // and the solver replays the block holding it once per path state.
    // The memo answers "has this already been said" without touching
    // the finding list or the strings below; a new identity costs one
    // insert, an old one one lookup.  The FIRST report still wins, so
    // the finding that lands — and the note it carries — is the one the
    // scan over `ctx.problems` used to keep.
    if (owner_byte) |owner| {
        if (!try ctx.seen.recordOwner(ctx.gpa, rule_id, pos.byte, owner)) return;
    } else if (!try ctx.seen.record(ctx.gpa, rule_id, pos.byte)) return;
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

test "writing gaps clear source booleans but preserve internal outcomes" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "source_flag", .decl_pos = pos0() },
        .{ .name = "control_result", .decl_pos = pos0(), .is_control_local = true },
        .{ .name = "resource", .decl_pos = pos0() },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const source_flag: LId = @enumFromInt(0);
    const control_result: LId = @enumFromInt(1);
    const resource: LId = @enumFromInt(2);
    const resource_heap = @as(HId, @enumFromInt(0));

    try state.facts.bindBoolean(gpa, source_flag, true);
    try state.facts.bindBoolean(gpa, control_result, true);
    try state.locals.put(gpa, resource, .{ .heap = resource_heap });
    try state.heaps.put(gpa, resource_heap, .{ .state = .dead });
    try transferGap(ctx, &state, .{ .note = "unknown call", .may_assign_locals = true });

    try testing.expectEqual(@as(?bool, null), state.facts.boolean(source_flag));
    try testing.expectEqual(@as(?bool, true), state.facts.boolean(control_result));
    try testing.expect(state.locals.get(resource).? == .heap);
    try testing.expectEqual(.dead, state.heaps.get(resource_heap).?.state);
    try transfer(ctx, &state, .{
        .kind = .{ .assume = .{ .not_local = source_flag } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.feasible);
    try transfer(ctx, &state, .{
        .kind = .{ .assume = .{ .not_local = control_result } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(!state.feasible);
    try testing.expect(state.locals.get(resource).? == .heap);
    try testing.expectEqual(.dead, state.heaps.get(resource_heap).?.state);
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
        .stack_loans = .{ .legacy_locals = &.{buf} },
    }, pos0(), pos1());

    try testing.expect(problems.items.len >= 1);
    try testing.expectEqualStrings("stack-escape", problems.items[0].rule_id);
}

test "transferRet: complete empty loans replace only the legacy stack decision" {
    const gpa = testing.allocator;
    for ([_]bool{ true, false }) |complete| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{
            .gpa = gpa,
            .locals = mkLocals(&.{ "alias", "cell" }),
            .problems = &problems,
            .seen = &seen,
            .path = "test",
        };
        const alias: LId = @enumFromInt(0);
        const cell: LId = @enumFromInt(1);
        try state.locals.put(gpa, alias, .{ .stack = cell });
        try transferRet(ctx, &state, .{
            .value_kind = .{ .copy_of = alias },
            .is_borrowed_return_type = true,
            .stack_loans = .{ .complete = complete, .legacy_locals = &.{cell} },
        }, pos0(), pos1());
        try testing.expectEqual(@as(usize, if (complete) 0 else 1), problems.items.len);
    }
}

test "transferRet: physical stack loans preserve arena and heap checks" {
    const gpa = testing.allocator;
    for ([_]bool{ true, false }) |arena| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{
            .gpa = gpa,
            .locals = mkLocals(&.{ "value", "cell" }),
            .problems = &problems,
            .seen = &seen,
            .path = "test",
        };
        const value: LId = @enumFromInt(0);
        const cell: LId = @enumFromInt(1);
        // The cell's contents are irrelevant to an escaping physical address.
        try state.locals.put(gpa, cell, .undef);
        if (arena) {
            const aid: AId = @enumFromInt(0);
            try state.arenas.put(gpa, aid, .{ .state = .live });
            try state.locals.put(gpa, value, .{ .arena = aid });
        } else {
            const hid: HId = @enumFromInt(0);
            try state.heaps.put(gpa, hid, .{ .state = .dead });
            try state.locals.put(gpa, value, .{ .heap = hid });
        }
        try transferRet(ctx, &state, .{
            .value_kind = .{ .copy_of = value },
            .is_borrowed_return_type = true,
            .stack_loans = .{ .complete = arena, .locals = &.{cell} },
        }, pos0(), pos1());
        try testing.expectEqual(@as(usize, 2), problems.items.len);
        try testing.expectEqualStrings("stack-escape", problems.items[0].rule_id);
        try testing.expect(std.mem.indexOf(u8, problems.items[0].message, "`cell`") != null);
        try testing.expectEqualStrings(
            if (arena) "arena-escape" else "heap-use-after-free",
            problems.items[1].rule_id,
        );
    }
}

test "transferRet: undefined value keeps precedence over canonical stack loans" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{
        .gpa = gpa,
        .locals = mkLocals(&.{ "value", "cell" }),
        .problems = &problems,
        .seen = &seen,
        .path = "test",
    };
    const value: LId = @enumFromInt(0);
    const cell: LId = @enumFromInt(1);
    try state.locals.put(gpa, value, .undef);
    try transferRet(ctx, &state, .{
        .value_kind = .{ .copy_of = value },
        .is_borrowed_return_type = true,
        .stack_loans = .{ .complete = true, .locals = &.{cell} },
    }, pos0(), pos1());
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
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
    const loans: cfg.StackLoanProof = .{ .legacy_locals = &.{ inner, src } };
    try transferCompositeEscape(ctx, &state, .{ .value_kind = .{ .composite_borrow = src }, .stack_loans = loans }, pos0(), pos1());
    try transferCompositeEscape(ctx, &state, .{ .value_kind = .{ .borrowed_from = src }, .stack_loans = loans }, pos0(), pos1());
    try testing.expectEqual(@as(usize, 0), problems.items.len);

    // The same source reached through the shapes the producer DOES emit
    // still reports, so the control above is about the narrowing and not
    // about `src` failing to carry a stack origin.
    try transferCompositeEscape(ctx, &state, .{ .value_kind = .{ .stack_ref = src }, .stack_loans = loans }, pos0(), pos1());
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

test "transferFieldUse: disabling undefined checks preserves dead field reports" {
    const gpa = testing.allocator;
    const without_undef: config_mod.Config = .{ .enabled = &enabled_without_use_undefined };
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
        .config = &without_undef,
    };
    const item: LId = @enumFromInt(0);
    const freed: HId = @enumFromInt(0);
    try transferDecl(ctx, &state, .{ .local = item, .init_kind = .undef }, pos0());
    try transferFieldHeapFree(ctx, &state, .{
        .parent = item,
        .name = "buf",
        .fallback_hid = freed,
    }, pos0(), pos1());
    try transferFieldUse(ctx, &state, .{ .parent = item, .name = "buf" }, pos0(), pos1());
    var reported_dead_field = false;
    for (problems.items) |problem| {
        try testing.expect(!std.mem.eql(u8, problem.rule_id, "use-undefined"));
        if (std.mem.eql(u8, problem.rule_id, "heap-use-after-free")) reported_dead_field = true;
    }
    try testing.expect(reported_dead_field);
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
        .{ .kind = .{ .indexed_read = .{ .array = x, .index = .unknown } }, .pos = pos0(), .end_pos = pos1() },
        .{ .kind = .{ .indexed_write = .{ .array = x, .index = .unknown, .rhs_kind = .plain } }, .pos = pos0(), .end_pos = pos1() },
        .{ .kind = .{ .counter_step = .{ .local = x, .step = 1 } }, .pos = pos0(), .end_pos = pos1() },
        .{ .kind = .{ .compare_assume = .{ .lhs = .{ .local = .{ .local = x } }, .rhs = .{ .constant = 0 }, .op = .eq } }, .pos = pos0(), .end_pos = pos1() },
        .{ .kind = .{ .array_complete = .{ .array = x } }, .pos = pos0(), .end_pos = pos1() },
        .{
            .kind = .{ .array_range_complete = .{ .array = x, .start = 0, .end = 1 } },
            .pos = pos0(),
            .end_pos = pos1(),
        },
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

test "indexed transfers keep exact coverage separate from array origin" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "items", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
        .{ .name = "count", .decl_pos = pos0(), .is_unsigned = true },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const items: LId = @enumFromInt(0);
    const count: LId = @enumFromInt(1);

    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = items, .init_kind = .undef } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = count, .init_kind = .plain, .integer_value = 0 } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_write = .{
            .array = items,
            .index = .{ .local = .{ .local = count } },
            .rhs_kind = .plain,
            .defined = true,
        } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .counter_step = .{ .local = count, .step = 1 } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{
            .array = items,
            .index = .{ .local = .{ .local = count, .offset = -1 } },
        } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);

    // A partial transport is silent, without clearing the strict origin.
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = items } },
        .pos = .{ .line = 1, .column = 3, .byte = 2 },
        .end_pos = .{ .line = 1, .column = 4, .byte = 3 },
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try testing.expect(state.locals.get(items).? == .undef);

    // Explicit completion suppresses aggregate undefined without changing
    // the underlying origin.
    try transfer(ctx, &state, .{
        .kind = .{ .array_complete = .{ .array = items } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.locals.get(items).? == .undef);
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = items } },
        .pos = .{ .line = 1, .column = 4, .byte = 3 },
        .end_pos = .{ .line = 1, .column = 5, .byte = 4 },
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);

    // An undefined overwrite must revoke the prior proof for slot zero.
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_write = .{
            .array = items,
            .index = .{ .constant = 0 },
            .rhs_kind = .undef,
            .defined = false,
        } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = items, .index = .{ .constant = 0 } } },
        .pos = .{ .line = 1, .column = 5, .byte = 4 },
        .end_pos = .{ .line = 1, .column = 6, .byte = 5 },
    });
    try testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "compact range completion joins prefixes and exact sparse suffixes" {
    const items: LId = @enumFromInt(0);
    const Step = struct { kind: StmtKind, prefix: u64 };
    const cases = [_]struct { extent: u64, steps: []const Step }{
        .{ .extent = 27, .steps = &.{
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 0 }, .rhs_kind = .plain, .defined = true } }, .prefix = 1 },
            .{ .kind = .{ .array_range_complete = .{ .array = items, .start = 1, .end = 13 } }, .prefix = 13 },
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 13 }, .rhs_kind = .plain, .defined = true } }, .prefix = 14 },
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 14 }, .rhs_kind = .plain, .defined = true } }, .prefix = 15 },
            .{ .kind = .{ .array_range_complete = .{ .array = items, .start = 15, .end = 25 } }, .prefix = 25 },
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 25 }, .rhs_kind = .plain, .defined = true } }, .prefix = 26 },
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 26 }, .rhs_kind = .plain, .defined = true } }, .prefix = 27 },
        } },
        .{ .extent = 9, .steps = &.{
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 0 }, .rhs_kind = .plain, .defined = true } }, .prefix = 1 },
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 1 }, .rhs_kind = .plain, .defined = true } }, .prefix = 2 },
            .{ .kind = .{ .array_range_complete = .{ .array = items, .start = 2, .end = 8 } }, .prefix = 8 },
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 8 }, .rhs_kind = .plain, .defined = true } }, .prefix = 9 },
        } },
        // A range reaching the stored suffix consumes only existing sparse facts.
        .{ .extent = 9, .steps = &.{
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 8 }, .rhs_kind = .plain, .defined = true } }, .prefix = 0 },
            .{ .kind = .{ .array_range_complete = .{ .array = items, .start = 0, .end = 8 } }, .prefix = 9 },
        } },
        // A disconnected range cannot hide the gap or initialize a later suffix.
        .{ .extent = 9, .steps = &.{
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 0 }, .rhs_kind = .plain, .defined = true } }, .prefix = 1 },
            .{ .kind = .{ .array_range_complete = .{ .array = items, .start = 2, .end = 8 } }, .prefix = 1 },
            .{ .kind = .{ .indexed_write = .{ .array = items, .index = .{ .constant = 8 }, .rhs_kind = .plain, .defined = true } }, .prefix = 1 },
        } },
        // The extent is metadata, not a bound on transfer work.
        .{ .extent = std.math.maxInt(u64), .steps = &.{
            .{ .kind = .{ .array_range_complete = .{
                .array = items,
                .start = 0,
                .end = std.math.maxInt(u64),
            } }, .prefix = std.math.maxInt(u64) },
        } },
    };
    const gpa = testing.allocator;
    for (cases) |case| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const locals = [_]LocalInfo{.{
            .name = "items",
            .decl_pos = pos0(),
            .is_array = true,
            .array_extent = case.extent,
        }};
        const ctx: Ctx = .{
            .gpa = gpa,
            .locals = &locals,
            .problems = &problems,
            .seen = &seen,
            .path = "test",
        };
        try transfer(ctx, &state, .{
            .kind = .{ .decl = .{ .local = items, .init_kind = .undef } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        for (case.steps) |step| {
            try transfer(ctx, &state, .{ .kind = step.kind, .pos = pos0(), .end_pos = pos1() });
            try testing.expectEqual(step.prefix, state.fixedPrefix(items));
            try testing.expectEqual(
                step.prefix == case.extent,
                state.hasInitializedPrefix(items, case.extent),
            );
        }
        try testing.expect(state.locals.get(items).? == .undef);
    }
}

test "compact range completion preserves holes outside the written range" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{.{
        .name = "items",
        .decl_pos = pos0(),
        .is_array = true,
        .array_extent = 9,
    }};
    const ctx: Ctx = .{
        .gpa = gpa,
        .locals = &locals,
        .problems = &problems,
        .seen = &seen,
        .path = "test",
    };
    const items: LId = @enumFromInt(0);
    try state.locals.put(gpa, items, .undef);
    try state.markArrayComplete(gpa, items);
    try state.setExactElement(gpa, items, 1, false);
    try state.setExactElement(gpa, items, 4, false);
    try state.setExactElement(gpa, items, 8, false);
    try transfer(ctx, &state, .{
        .kind = .{ .array_range_complete = .{ .array = items, .start = 2, .end = 8 } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(!state.hasExactElement(items, 1));
    try testing.expect(state.hasExactElement(items, 4));
    try testing.expect(!state.hasExactElement(items, 8));
    try testing.expect(!state.hasInitializedPrefix(items, 9));
}

test "compact range completion separates written bytes from strict value certificates" {
    const gpa = testing.allocator;
    const items: LId = @enumFromInt(0);
    const value: LId = @enumFromInt(1);
    for (0..7) |case| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const locals = [_]LocalInfo{
            .{ .name = "items", .decl_pos = pos0(), .is_array = true, .array_extent = 9 },
            .{ .name = "value", .decl_pos = pos0() },
        };
        const ctx: Ctx = .{
            .gpa = gpa,
            .locals = &locals,
            .problems = &problems,
            .seen = &seen,
            .path = "test",
        };
        try state.locals.put(gpa, items, .undef);
        try state.markArrayComplete(gpa, items);
        try state.locals.put(gpa, value, if (case == 0 or case == 2) .undef else .plain);
        var range: @TypeOf(@as(StmtKind, undefined).array_range_complete) = .{
            .array = items,
            .start = 2,
            .end = 8,
        };
        switch (case) {
            0 => range.inputs[0] = value,
            1 => {
                try state.unknown_values.put(gpa, value, {});
                range.inputs[0] = value;
            },
            2 => range.selected_inputs[0] = .{ .local = value },
            3 => {
                try state.bindFieldValue(gpa, .{ .parent = value, .name = "missing" }, false);
                range.selected_inputs[0] = .{ .field = .{ .parent = value, .name = "missing" } };
            },
            4 => {
                try state.setExactElement(gpa, items, 4, false);
                range.selected_inputs[0] = .{
                    .indexed = .{ .array = items, .index = .{ .constant = 4 } },
                };
            },
            5 => range.value_defined = false,
            6 => {
                range.value_defined = false;
                range.value_has_undefined_origin = true;
            },
            else => unreachable,
        }
        try transfer(ctx, &state, .{
            .kind = .{ .array_range_complete = range },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        try testing.expectEqual(case == 1 or case == 3 or case == 5, state.hasExactElement(items, 2));
        try testing.expect(!arrayHasFullCoverage(ctx, &state, items));
        try testing.expectEqual(case == 0 or case == 2 or case == 4 or case == 6, localIsProvedUndefined(ctx, &state, items));
    }
}

test "compact range completion uses initialized dependencies without reading unrelated fields" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "items", .decl_pos = pos0(), .is_array = true, .array_extent = 9 },
        .{ .name = "value", .decl_pos = pos0() },
        .{ .name = "scalar", .decl_pos = pos0(), .tracks_scalar_value = true },
        .{ .name = "source", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
    };
    const ctx: Ctx = .{
        .gpa = gpa,
        .locals = &locals,
        .problems = &problems,
        .seen = &seen,
        .path = "test",
    };
    const items: LId = @enumFromInt(0);
    const value: LId = @enumFromInt(1);
    const scalar: LId = @enumFromInt(2);
    const source: LId = @enumFromInt(3);
    try state.locals.put(gpa, items, .undef);
    try state.locals.put(gpa, value, .plain);
    try state.locals.put(gpa, scalar, .plain);
    try state.locals.put(gpa, source, .undef);
    try state.bindFieldValue(gpa, .{ .parent = value, .name = "missing" }, false);
    try state.fields.putContext(gpa, .{ .parent = value, .name = "initialized" }, .plain, .{});
    try state.setExactElement(gpa, source, 1, true);
    try transfer(ctx, &state, .{
        .kind = .{ .array_range_complete = .{
            .array = items,
            .start = 0,
            .end = 8,
            .inputs = .{ scalar, null, null, null, null, null, null, null },
            .selected_inputs = .{
                .{ .field = .{ .parent = value, .name = "initialized" } },
                .{ .indexed = .{ .array = source, .index = .{ .constant = 1 } } },
                null,
                null,
                null,
                null,
                null,
                null,
            },
        } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.hasInitializedPrefix(items, 8));
    try testing.expect(!state.hasExactElement(items, 8));
    try testing.expect(!state.hasInitializedPrefix(items, 9));
    try testing.expect(!state.fieldValueIsDefined(value, ""));
}

test "compact range completion requires a bounded fixed array range" {
    const gpa = testing.allocator;
    const items: LId = @enumFromInt(0);
    for ([_]struct { extent: ?u64, pointer: bool, start: u64, end: u64 }{
        .{ .extent = 9, .pointer = false, .start = 0, .end = 10 },
        .{ .extent = 9, .pointer = false, .start = 8, .end = 2 },
        .{ .extent = null, .pointer = false, .start = 0, .end = 9 },
        .{ .extent = 9, .pointer = true, .start = 0, .end = 9 },
    }) |case| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const locals = [_]LocalInfo{.{
            .name = "items",
            .decl_pos = pos0(),
            .is_array = true,
            .is_pointer = case.pointer,
            .array_extent = case.extent,
        }};
        const ctx: Ctx = .{
            .gpa = gpa,
            .locals = &locals,
            .problems = &problems,
            .seen = &seen,
            .path = "test",
        };
        try state.locals.put(gpa, items, .undef);
        try transfer(ctx, &state, .{
            .kind = .{ .array_range_complete = .{
                .array = items,
                .start = case.start,
                .end = case.end,
            } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        try testing.expect(!state.hasExactElement(items, 0));
        try testing.expect(!state.hasInitializedPrefix(items, 9));
    }
}

test "partial pointer and field writes do not initialize an array" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "pointer_items", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
        .{ .name = "field_items", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const pointer_items: LId = @enumFromInt(0);
    const field_items: LId = @enumFromInt(1);

    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = pointer_items, .init_kind = .undef } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .pointer_write = .{ .target = pointer_items } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.locals.get(pointer_items).? == .undef);

    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = field_items, .init_kind = .undef } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .field_assign = .{ .parent = field_items, .name = "[0]", .rhs_kind = .plain } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.locals.get(field_items).? == .undef);
}
test "undefined indexed writes revoke initialized coverage on plain arrays" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "items", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const items: LId = @enumFromInt(0);

    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = items, .init_kind = .plain, .value_defined = true } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_write = .{
            .array = items,
            .index = .{ .constant = 0 },
            .rhs_kind = .undef,
            .defined = false,
        } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = items, .index = .{ .constant = 1 } } },
        .pos = .{ .line = 1, .column = 2, .byte = 1 },
        .end_pos = .{ .line = 1, .column = 3, .byte = 2 },
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = items, .index = .{ .constant = 0 } } },
        .pos = .{ .line = 1, .column = 3, .byte = 2 },
        .end_pos = .{ .line = 1, .column = 4, .byte = 3 },
    });
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = items } },
        .pos = .{ .line = 1, .column = 5, .byte = 4 },
        .end_pos = .{ .line = 1, .column = 6, .byte = 5 },
    });

    // Only the selected hole reports; the partial whole-value use is silent.
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
}

test "indexed coverage holes preserve array resource origin" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "items", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const items: LId = @enumFromInt(0);

    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = items, .init_kind = .{ .heap_alloc = .{ .id = @enumFromInt(0) } } } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .array_complete = .{ .array = items } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_write = .{
            .array = items,
            .index = .{ .constant = 0 },
            .rhs_kind = .undef,
            .defined = false,
        } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.locals.get(items).? == .heap);
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = items, .index = .{ .constant = 1 } } },
        .pos = .{ .line = 1, .column = 2, .byte = 1 },
        .end_pos = .{ .line = 1, .column = 3, .byte = 2 },
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = items, .index = .{ .constant = 0 } } },
        .pos = .{ .line = 1, .column = 3, .byte = 2 },
        .end_pos = .{ .line = 1, .column = 4, .byte = 3 },
    });
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
}

test "comparison assumptions use exact unsigned scalar values" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "count", .decl_pos = pos0(), .is_unsigned = true },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const count: LId = @enumFromInt(0);

    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = count, .init_kind = .plain, .integer_value = 0 } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .compare_assume = .{
            .lhs = .{ .local = .{ .local = count } },
            .rhs = .{ .constant = 0 },
            .op = .gt,
        } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(!state.feasible);
    try testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "aliased calls invalidate only exposed coverage and preserve undefined roots" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "items", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
        .{ .name = "alias", .decl_pos = pos0() },
        .{ .name = "undefined_arg", .decl_pos = pos0() },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const items: LId = @enumFromInt(0);
    const alias: LId = @enumFromInt(1);
    const undefined_arg: LId = @enumFromInt(2);

    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = items, .init_kind = .undef } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try state.locals.put(gpa, alias, .{ .stack = items });
    try state.locals.put(gpa, undefined_arg, .undef);
    try transfer(ctx, &state, .{
        .kind = .{ .array_complete = .{ .array = items } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .lowering_gap = .{ .note = "call without an alias", .may_assign_locals = false } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = items, .index = .{ .constant = 1 } } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);

    try transfer(ctx, &state, .{
        .kind = .{ .pointer_write = .{ .target = alias, .initializes = false } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.locals.get(items).? == .undef);
    try testing.expect(state.locals.get(undefined_arg).? == .undef);
    try transfer(ctx, &state, .{
        .kind = .{ .pointer_write = .{ .target = undefined_arg, .initializes = false } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.locals.get(undefined_arg).? == .undef);
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = undefined_arg } },
        .pos = .{ .line = 1, .column = 2, .byte = 1 },
        .end_pos = .{ .line = 1, .column = 3, .byte = 2 },
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = items, .index = .{ .constant = 1 } } },
        .pos = .{ .line = 1, .column = 3, .byte = 2 },
        .end_pos = .{ .line = 1, .column = 4, .byte = 3 },
    });
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
    try testing.expect(!valueInputsAreDefined(ctx, &state, &.{.{ .local = items }}, false));
    try transfer(ctx, &state, .{
        .kind = .{ .array_complete = .{ .array = items } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .lowering_gap = .{ .note = "unknown call may assign", .may_assign_locals = true } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = items, .index = .{ .constant = 1 } } },
        .pos = .{ .line = 1, .column = 5, .byte = 4 },
        .end_pos = .{ .line = 1, .column = 6, .byte = 5 },
    });
    try testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "array copies inherit complete coverage from an undefined-origin source" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
        .{ .name = "decl_copy", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
        .{ .name = "assign_copy", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const source: LId = @enumFromInt(0);
    const decl_copy: LId = @enumFromInt(1);
    const assign_copy: LId = @enumFromInt(2);

    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = source, .init_kind = .undef } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .array_complete = .{ .array = source } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = decl_copy, .init_kind = .{ .copy_of = source } } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = assign_copy, .init_kind = .undef } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .assign = .{ .target = assign_copy, .rhs_kind = .{ .copy_of = source } } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(!localIsProvedUndefined(ctx, &state, decl_copy));
    try testing.expect(!localIsProvedUndefined(ctx, &state, assign_copy));
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = decl_copy, .index = .{ .constant = 0 } } },
        .pos = .{ .line = 1, .column = 2, .byte = 1 },
        .end_pos = .{ .line = 1, .column = 3, .byte = 2 },
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = assign_copy, .index = .{ .constant = 1 } } },
        .pos = .{ .line = 1, .column = 3, .byte = 2 },
        .end_pos = .{ .line = 1, .column = 4, .byte = 3 },
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "certified completion covers whole arrays without a numeric extent" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "items", .decl_pos = pos0(), .is_array = true },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const items: LId = @enumFromInt(0);

    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = items, .init_kind = .undef } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .array_complete = .{ .array = items } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = items, .index = .{ .constant = 0 } } },
        .pos = pos1(),
        .end_pos = .{ .line = 1, .column = 3, .byte = 2 },
    });
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = items } },
        .pos = pos0(),
        .end_pos = pos1(),
    });

    try testing.expectEqual(@as(usize, 0), problems.items.len);
}

// The source parameter has no local state, but its by-value payload is defined.
test "untracked array copies retain computed completion for declaration and assignment" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
        .{ .name = "copy", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const source: LId = @enumFromInt(0);
    const copy: LId = @enumFromInt(1);
    const operations = [_]StmtKind{
        .{ .decl = .{ .local = copy, .init_kind = .{ .copy_of = source } } },
        .{ .assign = .{ .target = copy, .rhs_kind = .{ .copy_of = source } } },
    };
    for (operations) |kind| {
        try transfer(ctx, &state, .{ .kind = kind, .pos = pos0(), .end_pos = pos1() });
        try transfer(ctx, &state, .{
            .kind = .{ .indexed_read = .{ .array = copy, .index = .{ .constant = 1 } } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
    }
    try testing.expectEqual(@as(usize, 0), problems.items.len);

    // A tracked source hole must replace, not inherit, the target's old proof.
    try state.locals.put(gpa, source, .plain);
    try state.markArrayComplete(gpa, source);
    try state.setExactElement(gpa, source, 1, false);
    for (operations) |kind| {
        try transfer(ctx, &state, .{ .kind = kind, .pos = pos0(), .end_pos = pos1() });
        try testing.expect(!state.hasInitializedElement(copy, .{ .constant = 1 }));
        try transfer(ctx, &state, .{
            .kind = .{ .indexed_read = .{ .array = copy, .index = .{ .constant = 1 } } },
            .pos = pos1(),
            .end_pos = .{ .line = 1, .column = 3, .byte = 2 },
        });
    }
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
}

// Unknown pointee writes remove payload proof, not the alias's defined header.
test "stack alias writes revoke aggregate field array completion" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const owner: LId = @enumFromInt(0);
    const alias: LId = @enumFromInt(1);
    const copy: LId = @enumFromInt(2);
    const locals = [_]LocalInfo{
        .{ .name = "owner", .decl_pos = pos0(), .tracks_array_payload = true },
        .{ .name = "alias", .decl_pos = pos0(), .is_pointer = true },
        .{ .name = "copy", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try state.locals.put(gpa, owner, .plain);
    try state.locals.put(gpa, alias, .{ .stack = owner });
    const field: ExprKind = .{ .field_copy_of = .{ .parent = owner, .name = "bytes" } };
    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = copy, .init_kind = field } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .array_value = .{ .target = copy, .source = field } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.isArrayComplete(copy));
    try transfer(ctx, &state, .{
        .kind = .{ .pointer_write = .{ .target = alias } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(state.locals.get(alias).? == .stack);
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = alias } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try transfer(ctx, &state, .{
        .kind = .{ .assign = .{ .target = copy, .rhs_kind = field } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .array_value = .{ .target = copy, .source = field } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = copy, .index = .{ .constant = 1 } } },
        .pos = pos1(),
        .end_pos = .{ .line = 1, .column = 3, .byte = 2 },
    });
    try testing.expect(!arrayHasFullCoverage(ctx, &state, copy));
    try testing.expectEqual(@as(usize, 0), problems.items.len);
}

// Address headers remain defined, while dead resource-backed storage stays dead.
test "stack references preserve resource lifetime without inheriting undefined payload" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const owner: LId = @enumFromInt(0);
    const alias: LId = @enumFromInt(1);
    const locals = [_]LocalInfo{
        .{ .name = "owner", .decl_pos = pos0() },
        .{ .name = "alias", .decl_pos = pos0(), .is_pointer = true, .frame_borrow_origin = owner },
    };
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try state.locals.put(gpa, owner, .undef);
    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = alias, .init_kind = .{ .stack_ref = owner } } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = alias } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    const arena: AId = @enumFromInt(0);
    try state.arenas.put(gpa, arena, .{ .state = .dead });
    const resource_origins = [_]Origin{ .{ .arena = arena }, .{ .arena_borrow = arena } };
    for (resource_origins) |origin| {
        try state.locals.put(gpa, owner, origin);
        try transfer(ctx, &state, .{
            .kind = .{ .decl = .{ .local = alias, .init_kind = .{ .stack_ref = owner } } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        try testing.expect(Origin.eql(.{ .arena_borrow = arena }, state.locals.get(alias).?));
    }
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = alias } },
        .pos = pos1(),
        .end_pos = .{ .line = 1, .column = 3, .byte = 2 },
    });
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("arena-use-after-kill", problems.items[0].rule_id);
    const heap: state_mod.HeapId = @enumFromInt(0);
    try state.locals.put(gpa, owner, .{ .heap = heap });
    try state.heaps.put(gpa, heap, .{ .state = .dead });
    try transfer(ctx, &state, .{
        .kind = .{ .decl = .{ .local = alias, .init_kind = .{ .stack_ref = owner } } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = alias } },
        .pos = .{ .line = 1, .column = 3, .byte = 2 },
        .end_pos = .{ .line = 1, .column = 4, .byte = 3 },
    });
    try testing.expectEqual(@as(usize, 2), problems.items.len);
    try testing.expectEqualStrings("heap-use-after-free", problems.items[1].rule_id);
}

test "integer domains: computed index definedness gates initialized payload reads" {
    const gpa = testing.allocator;
    const domains = [_]state_mod.IntegerDomain{ .{}, .{ .kind = .unsigned, .bits = 1 } };
    const locals = [_]LocalInfo{
        .{ .name = "array", .decl_pos = pos0(), .is_array = true, .array_extent = 2 },
        .{ .name = "index", .decl_pos = pos0(), .is_unsigned = true },
    };
    const array: LocalId = @enumFromInt(0);
    const index: LocalId = @enumFromInt(1);
    for ([_]bool{ false, true }) |defined| {
        var state: AbstractState = .{ .integer_domains = &domains };
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        try state.locals.put(gpa, array, .plain);
        try state.markArrayComplete(gpa, array);
        try transfer(ctx, &state, .{
            .kind = .{ .decl = .{ .local = index, .init_kind = if (defined) .plain else .undef, .value_defined = defined } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        try testing.expectEqual(defined, localInputIsDefined(ctx, &state, index, true));
        try transfer(ctx, &state, .{
            .kind = .{ .use = .{ .local = index } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        try transfer(ctx, &state, .{
            .kind = .{ .indexed_read = .{ .array = array, .index = .{ .local = .{ .local = index } } } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        try testing.expectEqual(@as(usize, if (defined) 0 else 1), problems.items.len);
        if (!defined) try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
    }
}

test "returned stack cells retain distinct physical owners and deduplicate replay" {
    const gpa = testing.allocator;
    const locals = [_]cfg.LocalInfo{
        .{ .name = "x", .decl_pos = .{ .line = 1, .column = 1, .byte = 0 } },
        .{ .name = "y", .decl_pos = .{ .line = 2, .column = 1, .byte = 10 } },
    };
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    for (0..2) |_| {
        try reportReturnedStackCell(ctx, @enumFromInt(0), false, pos0(), pos1());
        try reportReturnedStackCell(ctx, @enumFromInt(1), false, pos0(), pos1());
    }
    try testing.expectEqual(@as(usize, 2), problems.items.len);
    try testing.expectEqual(@as(usize, 2), seen.keys.count());
}

test "successful prefix certificate defines its returned count without filling the tail" {
    const gpa = testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "array", .decl_pos = pos0(), .is_array = true, .array_extent = 4 },
        .{ .name = "count", .decl_pos = pos1(), .is_unsigned = true },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.locals.put(gpa, array, .undef);
    try state.undefined_field_values.putContext(gpa, .{ .parent = array, .name = "" }, {}, .{});
    try state.entire_undefined_fields.putContext(gpa, .{ .parent = array, .name = "" }, {}, .{});
    try state.locals.put(gpa, count, .plain);
    try state.unknown_values.put(gpa, count, {});
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try transfer(ctx, &state, .{
        .kind = .{ .array_prefix = .{ .array = array, .count = count } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try testing.expect(indexIsDefined(ctx, &state, .{ .local = .{ .local = count } }));
    try testing.expect(try state.assumeComparison(gpa, .{ .lhs = .{ .local = .{ .local = count } }, .rhs = .{ .constant = 2 }, .op = .eq }));
    try testing.expect(state.hasInitializedElement(array, .{ .constant = 1 }));
    try testing.expect(!state.hasInitializedElement(array, .{ .constant = 3 }));
    try testing.expect(!indexedValueMayBeUndefined(ctx, &state, array, .{ .constant = 1 }));
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, .{ .constant = 3 }));
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_write = .{
            .array = array, .index = .{ .constant = 1 },
            .rhs_kind = .undef, .defined = false,
        } },
        .pos = pos0(), .end_pos = pos1(),
    });
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, .{ .constant = 1 }));
    try testing.expect(!indexedValueMayBeUndefined(ctx, &state, array, .{ .constant = 0 }));
}

test "nullable OR audit: optional tag masks do not revoke payload certificates" {
    const gpa = testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const optional: LocalId = @enumFromInt(1);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "array", .decl_pos = pos0(), .is_array = true, .array_extent = 1 },
        .{ .name = "optional", .decl_pos = pos1(), .is_slice = true, .tracks_optional_tag = true },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.locals.put(gpa, array, .plain);
    try state.locals.put(gpa, optional, .{ .stack = array });
    try state.markArrayComplete(gpa, array);
    try state.fields.putContext(gpa, .{ .parent = optional, .name = "ptr" }, .{ .stack = array }, .{});
    try state.bindFieldValue(gpa, .{ .parent = optional, .name = "ptr" }, true);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    for ([_]ExprKind{ .undef, .unknown }) |kind| {
        try transfer(ctx, &state, .{
            .kind = .{ .field_assign = .{
                .parent = optional, .name = cfg.diagnostic_optional_tag,
                .rhs_kind = kind, .diagnostic_only = true,
            } },
            .pos = pos0(), .end_pos = pos1(),
        });
        try testing.expectEqual(kind == .undef, optionalTagMayBeUndefined(ctx, &state, optional));
        try testing.expect(state.isArrayComplete(array));
        try testing.expectEqual(@as(usize, 0), state.unknown_field_values.count());
        try testing.expectEqual(Origin{ .stack = array }, state.locals.get(optional).?);
    }
}


test "successful prefix source inputs reject opaque scalars without clearing the count" {
    const gpa = testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const source: LocalId = @enumFromInt(2);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "array", .decl_pos = pos0(), .is_array = true, .array_extent = 4 },
        .{ .name = "count", .decl_pos = pos1(), .is_unsigned = true },
        .{ .name = "source", .decl_pos = pos1(), .tracks_scalar_value = true },
    };
    for ([_]bool{ false, true }) |opaque_source| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        try state.locals.put(gpa, array, .undef);
        try state.undefined_field_values.putContext(gpa, .{ .parent = array, .name = "" }, {}, .{});
        try state.entire_undefined_fields.putContext(gpa, .{ .parent = array, .name = "" }, {}, .{});
        try state.locals.put(gpa, count, .plain);
        try state.locals.put(gpa, source, .plain);
        try state.setScalarValue(gpa, count, 2);
        try state.unknown_values.put(gpa, count, {});
        if (opaque_source) try state.unknown_values.put(gpa, source, {});
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        var inputs: [8]?LocalId = .{null} ** 8;
        inputs[0] = source;
        try transfer(ctx, &state, .{
            .kind = .{ .array_prefix = .{ .array = array, .count = count, .inputs = inputs } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        try testing.expect(state.hasInitializedElement(array, .{ .constant = 1 }));
        try testing.expect(!indexedValueMayBeUndefined(ctx, &state, array, .{ .constant = 1 }));
        try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, .{ .constant = 3 }));
        try testing.expectEqual(!opaque_source, valueInputsAreDefined(ctx, &state, &.{.{
            .indexed = .{ .array = array, .index = .{ .constant = 1 } },
        }}, false));
        try testing.expectEqual(opaque_source, state.unknown_values.contains(count));
    }
}

test "indexed writes require a defined slice descriptor" {
    const gpa = testing.allocator;
    const slice: LocalId = @enumFromInt(0);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "slice", .decl_pos = pos0(), .is_slice = true },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.locals.put(gpa, slice, .undef);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try transferIndexedWrite(ctx, &state, .{
        .array = slice,
        .index = .{ .constant = 0 },
        .rhs_kind = .plain,
        .defined = true,
    }, pos0());
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
    try testing.expect(state.locals.get(slice).? == .undef);
    try testing.expect(!state.isArrayComplete(slice));
}

test "slice initialization separates external descriptor bounds from local coverage" {
    const gpa = testing.allocator;
    const slice: LocalId = @enumFromInt(0);
    const backing: LocalId = @enumFromInt(1);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "slice", .decl_pos = pos0(), .is_slice = true },
        .{ .name = "backing", .decl_pos = pos1(), .is_array = true, .array_extent = 4 },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.locals.put(gpa, slice, .plain);
    try state.locals.put(gpa, backing, .undef);
    try state.fields.putContext(gpa, .{ .parent = slice, .name = "len" }, .plain, .{});
    try state.fields.putContext(gpa, .{ .parent = slice, .name = "ptr" }, .plain, .{});
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try testing.expect(sliceElementIsDefined(ctx, &state, slice, .{ .constant = 0 }));
    try state.fields.putContext(gpa, .{ .parent = slice, .name = "ptr" }, .{ .stack = backing }, .{});
    try testing.expect(!sliceElementIsDefined(ctx, &state, slice, .{ .constant = 0 }));
    _ = try state.assumeComparison(gpa, .{
        .lhs = .{ .field = .{ .parent = slice, .name = "len", .is_unsigned = true } },
        .rhs = .{ .constant = 2 },
        .op = .eq,
    });
    try state.setExactElement(gpa, backing, 0, true);
    try testing.expect(sliceElementIsDefined(ctx, &state, slice, .{ .constant = 0 }));
    try testing.expect(!sliceElementIsDefined(ctx, &state, slice, .{ .constant = 1 }));
    try testing.expect(!sliceElementIsDefined(ctx, &state, slice, .{ .constant = 2 }));
}

test "borrowing a receiver requires a defined pointer header" {
    const gpa = testing.allocator;
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const locals = [_]LocalInfo{.{ .name = "pointer", .decl_pos = pos0(), .is_pointer = true }};
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const pointer: LId = @enumFromInt(0);
    try state.locals.put(gpa, pointer, .undef);
    try transferUse(ctx, &state, .{ .local = pointer, .from_method_call = true }, pos0(), pos1());
    var reported_pointer = false;
    for (problems.items) |problem| {
        if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
            std.mem.indexOf(u8, problem.message, "pointer") != null) reported_pointer = true;
    }
    try testing.expect(reported_pointer);
}

test "pointer field inputs require an exact payload certificate and a defined header" {
    const gpa = testing.allocator;
    const pointer: LocalId = @enumFromInt(0);
    const locals = [_]cfg.LocalInfo{.{ .name = "pointer", .decl_pos = pos0(), .is_pointer = true }};
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const key: state_mod.FieldKey = .{ .parent = pointer, .name = "a" };
    try state.locals.put(gpa, pointer, .plain);
    try testing.expect(!scalarFieldIsDefined(ctx, &state, pointer, "a"));
    try state.fields.putContext(gpa, key, .plain, .{});
    try testing.expect(scalarFieldIsDefined(ctx, &state, pointer, "a"));
    try testing.expect(!scalarFieldIsDefined(ctx, &state, pointer, "b"));
    try state.bindFieldValue(gpa, key, false);
    try state.fields.putContext(gpa, key, .plain, .{});
    try testing.expect(!scalarFieldIsDefined(ctx, &state, pointer, "a"));
    try state.bindFieldValue(gpa, key, true);
    try state.fields.putContext(gpa, key, .plain, .{});
    try state.unknown_values.put(gpa, pointer, {});
    try testing.expect(!scalarFieldIsDefined(ctx, &state, pointer, "a"));
    _ = state.unknown_values.swapRemove(pointer);
    try state.locals.put(gpa, pointer, .undef);
    try testing.expect(!scalarFieldIsDefined(ctx, &state, pointer, "a"));
}

test "undefined diagnostics: unknown field writes initialize bytes without certifying values" {
    const gpa = testing.allocator;
    const locals = [_]LocalInfo{
        .{ .name = "storage", .decl_pos = pos0(), .tracks_array_payload = true },
        .{ .name = "input", .decl_pos = pos0(), .tracks_scalar_value = true },
    };
    const storage: LId = @enumFromInt(0);
    const input: LId = @enumFromInt(1);
    for ([_]bool{ false, true }) |undefined_input| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        try state.locals.put(gpa, storage, .undef);
        try state.locals.put(gpa, input, if (undefined_input) .undef else .plain);
        try state.unknown_values.put(gpa, input, {});
        try transfer(ctx, &state, .{
            .kind = .{ .field_assign = .{
                .parent = storage,
                .name = "index",
                .rhs_kind = .unknown,
                .selected_inputs = .{ .{ .local = input }, null, null, null, null, null, null, null },
            } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        try testing.expect(!state.fieldValueIsDefined(storage, "index"));
        try testing.expectEqual(undefined_input, state.fieldValueMayBeUndefined(storage, "index"));
        try transfer(ctx, &state, .{
            .kind = .{ .field_use = .{ .parent = storage, .name = "index" } },
            .pos = pos1(),
            .end_pos = pos1(),
        });
        try testing.expectEqual(@as(usize, if (undefined_input) 1 else 0), problems.items.len);
    }
}

test "diagnostic-only array transport preserves holes without positive value certificates" {
    const gpa = testing.allocator;
    const source: LId = @enumFromInt(0);
    const destination: LId = @enumFromInt(1);
    const locals = [_]LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .is_array = true, .array_extent = 3, .tracks_array_payload = true },
        .{ .name = "destination", .decl_pos = pos0(), .is_array = true, .array_extent = 3, .tracks_array_payload = true },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try state.locals.put(gpa, source, .undef);
    try state.locals.put(gpa, destination, .undef);
    try transfer(ctx, &state, .{
        .kind = .{ .field_assign = .{ .parent = source, .name = "[0]", .rhs_kind = .unknown } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = source } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    try transfer(ctx, &state, .{
        .kind = .{ .array_value = .{
            .target = destination,
            .source = .{ .copy_of = source },
            .diagnostic_only = true,
        } },
        .pos = pos0(),
        .end_pos = pos1(),
    });
    // Partial transport is silent and does not grant a defined-value certificate.
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try testing.expect(!valueInputsAreDefined(ctx, &state, &.{.{ .local = destination }}, false));
    try testing.expect(!valueInputsAreDefined(ctx, &state, &.{.{
        .indexed = .{ .array = destination, .index = .{ .constant = 0 } },
    }}, false));
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = destination, .index = .{ .constant = 0 } } },
        .pos = pos1(),
        .end_pos = pos1(),
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    const hole_pos: cfg.SrcPos = .{ .line = 3, .column = 5, .byte = 20 };
    try transfer(ctx, &state, .{
        .kind = .{ .indexed_read = .{ .array = destination, .index = .{ .constant = 1 } } },
        .pos = hole_pos,
        .end_pos = hole_pos,
    });
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
    try testing.expectEqual(hole_pos.line, problems.items[0].start.line);
    try testing.expectEqual(hole_pos.column, problems.items[0].start.column);
}

test "returned descriptor prefix: written unknown locations never certify payloads" {
    const gpa = testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const source: LocalId = @enumFromInt(2);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "array", .decl_pos = pos0(), .is_array = true, .array_extent = 4 },
        .{ .name = "count", .decl_pos = pos1(), .is_unsigned = true },
        .{ .name = "source", .decl_pos = pos1(), .is_slice = true },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.locals.put(gpa, array, .undef);
    try state.locals.put(gpa, count, .plain);
    try state.locals.put(gpa, source, .plain);
    try state.unknown_values.put(gpa, source, {});
    try state.unknown_values.put(gpa, count, {});
    try state.setScalarValue(gpa, count, 2);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try transfer(ctx, &state, .{
        .kind = .{ .field_assign = .{ .parent = array, .name = "[0..$1:1:0:4:0]", .rhs_kind = .plain,
            .selected_inputs = .{ .{ .local = source }, null, null, null, null, null, null, null },
            .diagnostic_only = true } },
        .pos = pos0(), .end_pos = pos1(),
    });
    try testing.expect(!indexedValueMayBeUndefined(ctx, &state, array, .{ .constant = 1 }));
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, .{ .constant = 2 }));
    try testing.expect(!state.hasInitializedElement(array, .{ .constant = 1 }));
    try testing.expect(!state.isArrayComplete(array));
    try testing.expect(!state.fieldValueIsDefined(array, "[1]"));
    try testing.expect(state.unknown_values.contains(count));
}

test "returned descriptor prefix: runtime guard stays diagnostic through mutations and joins" {
    const gpa = testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const index: LocalId = @enumFromInt(2);
    const domains = [_]state_mod.IntegerDomain{ .{}, .{ .kind = .unsigned, .bits = 64 }, .{ .kind = .unsigned, .bits = 64 } };
    const locals = [_]cfg.LocalInfo{
        .{ .name = "array", .decl_pos = pos0(), .is_array = true, .array_extent = 4 },
        .{ .name = "count", .decl_pos = pos1(), .is_unsigned = true },
        .{ .name = "index", .decl_pos = pos1(), .is_unsigned = true },
    };
    var state: AbstractState = .{ .integer_domains = &domains };
    defer state.deinit(gpa);
    try state.locals.put(gpa, array, .undef);
    try state.locals.put(gpa, count, .plain);
    try state.locals.put(gpa, index, .plain);
    try state.unknown_values.put(gpa, count, {});
    try state.setScalarValue(gpa, index, 0);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try transfer(ctx, &state, .{
        .kind = .{ .field_assign = .{ .parent = array, .name = "[0..$1:1:0:4:0]", .rhs_kind = .plain, .diagnostic_only = true } },
        .pos = pos0(), .end_pos = pos1(),
    });
    const selected: cfg.IndexTerm = .{ .local = .{ .local = index } };
    const guard: cfg.Stmt = .{
        .kind = .{ .compare_assume = .{ .lhs = selected, .rhs = .{ .local = .{ .local = count } }, .op = .lt } },
        .pos = pos0(), .end_pos = pos1(),
    };
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, selected));
    try transfer(ctx, &state, guard);
    try testing.expect(!indexedValueMayBeUndefined(ctx, &state, array, selected));
    // The observable caller certificate obligations stay strict.
    try testing.expect(!indexIsDefined(ctx, &state, .{ .local = .{ .local = count } }));
    try testing.expect(state.unknown_values.contains(count));
    try testing.expectEqual(@as(usize, 0), state.comparisons.items.len);
    try testing.expect(!state.hasInitializedElement(array, selected));
    try testing.expect(!state.isArrayComplete(array));
    try testing.expect(!state.fieldValueIsDefined(array, "[0]"));

    var joined: AbstractState = .{};
    defer joined.deinit(gpa);
    try joined.cloneFrom(&state, gpa);
    var unguarded: AbstractState = .{};
    defer unguarded.deinit(gpa);
    try unguarded.cloneFrom(&state, gpa);
    unguarded.forgetAllComparisons();
    _ = try state_mod.join(&joined, &unguarded, gpa);
    try testing.expect(indexedValueMayBeUndefined(ctx, &joined, array, selected));

    // An index mutation loses the guard, but not the saved prefix.
    try state.stepCounter(gpa, index, 1);
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, selected));
    try transfer(ctx, &state, guard);
    try testing.expect(!indexedValueMayBeUndefined(ctx, &state, array, selected));

    // A count mutation loses BOTH guard and original prefix. A fresh guard
    // must not turn the enlarged count into a new store witness.
    try state.stepCounter(gpa, count, 1);
    try transfer(ctx, &state, guard);
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, selected));
    try testing.expectEqual(@as(usize, 0), state.written_fields.count());
    try testing.expectEqual(@as(usize, 0), state.diagnostic_index_bounds.count());
}

test "MAY-only field stores union proved poison without granting or erasing byte credit" {
    const gpa = testing.allocator;
    const storage: LId = @enumFromInt(0);
    const input: LId = @enumFromInt(1);
    const locals = [_]LocalInfo{
        .{ .name = "storage", .decl_pos = pos0(), .tracks_array_payload = true },
        .{ .name = "input", .decl_pos = pos0(), .tracks_scalar_value = true },
    };
    const known: state_mod.FieldKey = .{ .parent = storage, .name = "known" };
    const spare: state_mod.FieldKey = .{ .parent = storage, .name = "spare" };
    for ([_]bool{ false, true }) |undefined_input| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        try state.locals.put(gpa, storage, .plain);
        try state.locals.put(gpa, input, if (undefined_input) .undef else .plain);
        try state.unknown_values.put(gpa, input, {});
        try state.bindWrittenField(gpa, known, false);
        try state.undefined_field_values.putContext(gpa, spare, {}, .{});
        try state.fields.putContext(gpa, known, .{ .stack = input }, .{});
        try transfer(ctx, &state, .{
            .kind = .{ .field_assign = .{
                .parent = storage,
                .name = "known",
                .rhs_kind = .unknown,
                .selected_inputs = .{ .{ .local = input }, null, null, null, null, null, null, null },
                .may_write_only = true,
            } },
            .pos = pos0(),
            .end_pos = pos1(),
        });
        try testing.expectEqual(undefined_input, state.fieldValueMayBeUndefined(storage, "known"));
        try testing.expect(state.fieldValueMayBeUndefined(storage, "spare"));
        try testing.expect(state.written_fields.containsContext(known, .{}));
        try testing.expect(!state.written_fields.containsContext(spare, .{}));
        try testing.expect((state.locals.get(storage) orelse unreachable) == .plain);
        const preserved = state.fields.getContext(known, .{}) orelse unreachable;
        try testing.expect(preserved == .stack and preserved.stack == input);
        try testing.expectEqual(undefined_input, state.unknown_values.contains(storage));
    }
}

test "switch capture masks: byte replay preserves positive certificates and origins" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const capture: LocalId = @enumFromInt(1);
    const control: LocalId = @enumFromInt(2);
    const domains = [_]state_mod.IntegerDomain{ .{}, .{ .kind = .unsigned, .bits = 8 }, .{ .kind = .unsigned, .bits = 8 } };
    const locals = [_]LocalInfo{
        .{ .name = "selector", .decl_pos = pos0(), .tracks_array_payload = true },
        .{ .name = "capture", .decl_pos = pos0(), .tracks_scalar_value = true, .is_array = true, .array_extent = 2 },
        .{ .name = "control", .decl_pos = pos0(), .tracks_scalar_value = true },
    };
    for ([_]bool{ false, true }) |unknown_capture| {
        var state: AbstractState = .{ .integer_domains = &domains };
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        try state.locals.put(gpa, source, .plain);
        try state.locals.put(gpa, capture, .plain);
        try state.locals.put(gpa, control, .plain);
        try state.undefined_field_values.putContext(gpa, .{ .parent = source, .name = "a" }, {}, .{});
        try state.entire_undefined_fields.putContext(gpa, .{ .parent = source, .name = "a" }, {}, .{});
        try state.written_fields.putContext(gpa, .{ .parent = source, .name = "a.child" }, {}, .{});
        try state.fields.putContext(gpa, .{ .parent = capture, .name = "existing" }, .plain, .{});
        if (unknown_capture) try state.unknown_values.put(gpa, capture, {});
        try state.unknown_field_values.putContext(gpa, .{ .parent = capture, .name = "uncertified" }, {}, .{});
        try state.unknown_values.put(gpa, control, {});
        try state.setScalarValue(gpa, control, 7);
        try state.markArrayComplete(gpa, capture);
        try state.setExactElement(gpa, capture, 0, true);
        const child_defined = scalarFieldIsDefined(ctx, &state, capture, "child");
        const existing_defined = scalarFieldIsDefined(ctx, &state, capture, "existing");
        const whole_defined = state.fieldValueIsDefined(capture, "");
        const value_defined = localInputIsDefined(ctx, &state, capture, true);
        const control_defined = localInputIsDefined(ctx, &state, control, true);
        const fields_count = state.fields.count();
        const locals_count = state.locals.count();
        const unknown_count = state.unknown_values.count();
        const unknown_fields_count = state.unknown_field_values.count();
        const complete_count = state.complete_arrays.count();
        const exact_count = state.exact_elements.count();
        try transfer(ctx, &state, .{
            .kind = .{ .array_value = .{ .target = capture, .source = .{ .field_copy_of = .{ .parent = source, .name = "a" } }, .mask_only = true } },
            .pos = pos0(), .end_pos = pos1(),
        });
        try testing.expect(!state.fieldValueMayBeUndefined(capture, "child"));
        try testing.expect(state.fieldValueMayBeUndefined(capture, "spare"));
        try testing.expect(!state.entire_undefined_values.contains(capture));
        try testing.expectEqual(child_defined, scalarFieldIsDefined(ctx, &state, capture, "child"));
        try testing.expectEqual(existing_defined, scalarFieldIsDefined(ctx, &state, capture, "existing"));
        try testing.expectEqual(whole_defined, state.fieldValueIsDefined(capture, ""));
        try testing.expectEqual(value_defined, localInputIsDefined(ctx, &state, capture, true));
        try testing.expectEqual(control_defined, localInputIsDefined(ctx, &state, control, true));
        try testing.expectEqual(fields_count, state.fields.count());
        try testing.expectEqual(locals_count, state.locals.count());
        try testing.expectEqual(unknown_count, state.unknown_values.count());
        try testing.expectEqual(unknown_fields_count, state.unknown_field_values.count());
        try testing.expectEqual(complete_count, state.complete_arrays.count());
        try testing.expectEqual(exact_count, state.exact_elements.count());
        try testing.expect(state.locals.get(capture).? == .plain);
        try testing.expectEqual(@as(?u64, 7), state.scalarValue(control));
        try testing.expect(state.isArrayComplete(capture));
    }
}

test "switch tag diagnostics: payload holes are not tag holes and payload repairs do not write tags" {
    const gpa = testing.allocator;
    const selector: LocalId = @enumFromInt(0);
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    try state.locals.put(gpa, selector, .plain);
    try state.undefined_field_values.putContext(gpa, .{ .parent = selector, .name = "a.spare" }, {}, .{});
    try testing.expect(!unionTagMayBeUndefined(&state, selector));
    try state.locals.put(gpa, selector, .undef);
    try state.written_fields.putContext(gpa, .{ .parent = selector, .name = "a.child" }, {}, .{});
    try state.partial_undefined_values.put(gpa, selector, {});
    try testing.expect(unionTagMayBeUndefined(&state, selector));
    try state.undefined_field_values.putContext(gpa, .{ .parent = selector, .name = "" }, {}, .{});
    try state.locals.put(gpa, selector, .plain);
    try testing.expect(unionTagMayBeUndefined(&state, selector));
}


test "counted append prefix: physical last slot does not certify unknown values" {
    const gpa = testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const domains = [_]state_mod.IntegerDomain{ .{}, .{ .kind = .unsigned, .bits = @bitSizeOf(usize) } };
    const locals = [_]cfg.LocalInfo{
        .{ .name = "chain", .decl_pos = pos0(), .is_array = true, .array_extent = 16 },
        .{ .name = "count", .decl_pos = pos1(), .is_unsigned = true, .tracks_scalar_value = true },
    };
    var state: AbstractState = .{ .integer_domains = &domains };
    defer state.deinit(gpa);
    try state.locals.put(gpa, array, .undef);
    try state.locals.put(gpa, count, .plain);
    try state.unknown_values.put(gpa, array, {});
    try state.unknown_values.put(gpa, count, {});
    try state.setExactElement(gpa, array, 0, true);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    const prefix: cfg.Stmt = .{
        .kind = .{ .array_prefix = .{ .array = array, .count = count, .seeded_append = true } },
        .pos = pos0(), .end_pos = pos1(),
    };
    const selected: cfg.IndexTerm = .{ .local = .{ .local = count, .offset = -1 } };
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, selected));
    try transfer(ctx, &state, prefix);
    try testing.expect(!indexedValueMayBeUndefined(ctx, &state, array, selected));
    try testing.expect(state.unknown_values.contains(array));
    try testing.expect(state.unknown_values.contains(count));
    try testing.expect(!indexIsDefined(ctx, &state, selected));
    try testing.expectEqual(@as(?u64, null), state.scalarValue(count));
    try testing.expectEqual(@as(usize, 0), state.comparisons.items.len);
    try testing.expectEqual(@as(usize, 0), state.symbolic_prefixes.count());
    try testing.expect(!state.hasInitializedElement(array, selected));
    try testing.expect(!arrayHasFullCoverage(ctx, &state, array));
    try testing.expect(!state.isArrayComplete(array));
    try testing.expect(!state.fieldValueIsDefined(array, "[1]"));
    const input: cfg.ValueInput = .{ .indexed = .{ .array = array, .index = selected } };
    try testing.expect(!valueInputsAreDefined(ctx, &state, &.{input}, false));
    try testing.expect(!returnValueIsDefined(ctx, &state, .{ .ret = .{
        .value_kind = .plain, .is_borrowed_return_type = false,
        .value_defined = true, .value_inputs = .{input} ++ .{null} ** 7,
    } }));

    var uncertified: AbstractState = .{};
    defer uncertified.deinit(gpa);
    try uncertified.cloneFrom(&state, gpa);
    uncertified.forgetWrittenFields(array);
    uncertified.forgetAllComparisons();
    var joined: AbstractState = .{};
    defer joined.deinit(gpa);
    try joined.cloneFrom(&state, gpa);
    _ = try state_mod.join(&joined, &uncertified, gpa);
    try testing.expect(indexedValueMayBeUndefined(ctx, &joined, array, selected));

    // A sparse undefined overwrite defeats the dynamic physical prefix.
    var hole: AbstractState = .{};
    defer hole.deinit(gpa);
    try hole.cloneFrom(&state, gpa);
    try transferIndexedWrite(ctx, &hole, .{
        .array = array, .index = .{ .constant = 2 }, .rhs_kind = .undef,
    }, pos1());
    try testing.expect(indexedValueMayBeUndefined(ctx, &hole, array, selected));

    // Count+1 without a write removes the witness, not just a scalar bound.
    try transferCounterStep(ctx, &state, .{ .local = count, .step = 1 });
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, selected));
    try testing.expectEqual(@as(usize, 0), state.diagnostic_index_bounds.count());
    try testing.expectEqual(@as(usize, 0), state.written_fields.count());

    var missing: AbstractState = .{ .integer_domains = &domains };
    defer missing.deinit(gpa);
    try missing.locals.put(gpa, array, .undef);
    try missing.locals.put(gpa, count, .plain);
    try transfer(ctx, &missing, prefix);
    try testing.expect(indexedValueMayBeUndefined(ctx, &missing, array, .{ .constant = 0 }));
    try testing.expectEqual(@as(usize, 0), missing.diagnostic_index_bounds.count());
}

test "optional payload ALL corrections: scalar MAY stays MAY through root and field captures" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const capture: LocalId = @enumFromInt(1);
    for ([_]bool{ false, true }) |nested| {
        for ([_]bool{ false, true }) |all| {
            const locals = [_]cfg.LocalInfo{
                .{ .name = "source", .decl_pos = pos0(), .tracks_optional_tag = !nested, .tracks_array_payload = true },
                .{ .name = "capture", .decl_pos = pos1(), .tracks_scalar_value = true },
            };
            var state: AbstractState = .{};
            defer state.deinit(gpa);
            var problems: std.ArrayListUnmanaged(Problem) = .empty;
            defer freeProblems(gpa, &problems);
            var seen = Seen.init();
            defer seen.deinit(gpa);
            const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
            try state.locals.put(gpa, source, .plain);
            try state.locals.put(gpa, capture, .plain);
            const path: []const u8 = if (nested) "value" else "";
            try state.undefined_field_values.putContext(gpa, .{ .parent = source, .name = path }, {}, .{});
            if (all) {
                if (nested)
                    try state.entire_undefined_fields.putContext(gpa, .{ .parent = source, .name = path }, {}, .{})
                else
                    try state.entire_undefined_values.put(gpa, source, {});
            }
            const tag_path: []const u8 = if (nested) "value.$optional-tag" else cfg.diagnostic_optional_tag;
            try transfer(ctx, &state, .{
                .kind = .{ .field_assign = .{
                    .parent = source, .name = tag_path, .rhs_kind = .unknown, .diagnostic_only = true,
                } },
                .pos = pos0(), .end_pos = pos1(),
            });
            const fields_count = state.fields.count();
            const unknown_count = state.unknown_values.count();
            const unknown_fields_count = state.unknown_field_values.count();
            try transfer(ctx, &state, .{
                .kind = .{ .array_value = .{
                    .target = capture,
                    .source = if (nested) .{ .field_copy_of = .{ .parent = source, .name = path } } else .{ .copy_of = source },
                    .mask_only = true, .optional_payload = true,
                } },
                .pos = pos0(), .end_pos = pos1(),
            });
            try testing.expectEqual(all, state.entire_undefined_values.contains(capture));
            try testing.expect(state.fieldValueMayBeUndefined(capture, ""));
            try testing.expect(!fieldHasDiagnosticChildren(&state, capture, ""));
            try testing.expectEqual(Origin.plain, state.locals.get(capture).?);
            try testing.expectEqual(fields_count, state.fields.count());
            try testing.expectEqual(unknown_count, state.unknown_values.count());
            try testing.expectEqual(unknown_fields_count, state.unknown_field_values.count());
            try transfer(ctx, &state, .{
                .kind = .{ .use = .{ .local = capture } }, .pos = pos1(), .end_pos = pos1(),
            });
            try testing.expectEqual(@as(usize, 1), problems.items.len);
            try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
        }
    }
}

test "optional payload ALL corrections: payload repair defeats virtual ALL but keeps selected holes" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const capture: LocalId = @enumFromInt(1);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .tracks_optional_tag = true, .tracks_array_payload = true },
        .{ .name = "capture", .decl_pos = pos1(), .tracks_array_payload = true },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try state.locals.put(gpa, source, .undef);
    try state.locals.put(gpa, capture, .plain);
    try state.entire_undefined_values.put(gpa, source, {});
    try transfer(ctx, &state, .{
        .kind = .{ .field_assign = .{
            .parent = source, .name = cfg.diagnostic_optional_tag, .rhs_kind = .unknown, .diagnostic_only = true,
        } }, .pos = pos0(), .end_pos = pos1(),
    });
    try testing.expect(optionalPayloadIsEntirelyUndefined(ctx, &state, .{ .parent = source }));
    try transfer(ctx, &state, .{
        .kind = .{ .field_assign = .{ .parent = source, .name = "good", .rhs_kind = .plain, .defined = true } },
        .pos = pos0(), .end_pos = pos1(),
    });
    try testing.expect(!optionalPayloadIsEntirelyUndefined(ctx, &state, .{ .parent = source }));
    try transfer(ctx, &state, .{
        .kind = .{ .array_value = .{
            .target = capture, .source = .{ .copy_of = source }, .mask_only = true, .optional_payload = true,
        } }, .pos = pos0(), .end_pos = pos1(),
    });
    try testing.expect(!state.entire_undefined_values.contains(capture));
    try testing.expect(!state.fieldValueMayBeUndefined(capture, "good"));
    try testing.expect(state.fieldValueMayBeUndefined(capture, "bad"));
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = capture } }, .pos = pos0(), .end_pos = pos1(),
    });
    // Partial transport is silent and leaves the selected bad field undefined.
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try transfer(ctx, &state, .{
        .kind = .{ .field_use = .{ .parent = capture, .name = "good" } }, .pos = pos0(), .end_pos = pos1(),
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try transfer(ctx, &state, .{
        .kind = .{ .field_use = .{ .parent = capture, .name = "bad" } }, .pos = pos1(), .end_pos = pos1(),
    });
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
    try testing.expectEqual(pos1().line, problems.items[0].start.line);
    try testing.expectEqual(pos1().column, problems.items[0].start.column);
}

test "optional payload ALL corrections: slice capture keeps descriptor holes without tag bytes" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const capture: LocalId = @enumFromInt(1);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .is_slice = true, .tracks_optional_tag = true },
        .{ .name = "capture", .decl_pos = pos1(), .is_slice = true },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try state.locals.put(gpa, source, .plain);
    try state.locals.put(gpa, capture, .plain);
    try state.undefined_field_values.putContext(gpa, .{ .parent = source, .name = "ptr" }, {}, .{});
    try state.written_fields.putContext(gpa, .{ .parent = source, .name = "len" }, {}, .{});
    try state.written_fields.putContext(gpa, .{ .parent = source, .name = cfg.diagnostic_optional_tag }, {}, .{});
    try transfer(ctx, &state, .{
        .kind = .{ .array_value = .{
            .target = capture, .source = .{ .copy_of = source }, .mask_only = true, .optional_payload = true,
        } }, .pos = pos0(), .end_pos = pos1(),
    });
    try testing.expect(!state.entire_undefined_values.contains(capture));
    try testing.expect(state.fieldValueMayBeUndefined(capture, "ptr"));
    try testing.expect(state.fieldBytesAreWritten(capture, "len"));
    try testing.expect(!state.written_fields.containsContext(.{ .parent = capture, .name = cfg.diagnostic_optional_tag }, .{}));
    try testing.expectEqual(@as(usize, 0), state.fields.count());
    try testing.expectEqual(Origin.plain, state.locals.get(capture).?);
    try transfer(ctx, &state, .{
        .kind = .{ .use = .{ .local = capture } }, .pos = pos0(), .end_pos = pos1(),
    });
    // Partial descriptor transport is silent; only selecting the ptr hole reports.
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try transfer(ctx, &state, .{
        .kind = .{ .field_use = .{ .parent = capture, .name = "len" } }, .pos = pos0(), .end_pos = pos1(),
    });
    try testing.expectEqual(@as(usize, 0), problems.items.len);
    try transfer(ctx, &state, .{
        .kind = .{ .field_use = .{ .parent = capture, .name = "ptr" } }, .pos = pos1(), .end_pos = pos1(),
    });
    try testing.expectEqual(@as(usize, 1), problems.items.len);
    try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
    try testing.expectEqual(pos1().line, problems.items[0].start.line);
    try testing.expectEqual(pos1().column, problems.items[0].start.column);
}


test "constructor mask replay: nested slot holes stay selected through two physical copies" {
    const gpa = testing.allocator;
    const recipe: LocalId = @enumFromInt(0);
    const snapshot: LocalId = @enumFromInt(1);
    const destination: LocalId = @enumFromInt(2);
    const input: LocalId = @enumFromInt(3);
    const locals = [_]LocalInfo{
        .{ .name = "recipe", .decl_pos = pos0(), .tracks_array_payload = true, .is_array = true, .array_extent = 2 },
        .{ .name = "snapshot", .decl_pos = pos0(), .tracks_array_payload = true, .is_array = true, .array_extent = 2 },
        .{ .name = "destination", .decl_pos = pos0(), .tracks_array_payload = true, .is_array = true, .array_extent = 2 },
        .{ .name = "input", .decl_pos = pos0(), .tracks_scalar_value = true },
    };
    for ([_]bool{ false, true }) |undefined_input| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        try state.locals.put(gpa, recipe, .plain);
        try state.locals.put(gpa, snapshot, .plain);
        try state.locals.put(gpa, destination, if (undefined_input) .plain else .undef);
        try state.locals.put(gpa, input, if (undefined_input) .undef else .plain);
        try state.unknown_values.put(gpa, recipe, {});
        // Replay the flattened constructor in producer order: parents first,
        // then leaf stores. Only [0].b consumes the caller input.
        for ([_][]const u8{ "[0]", "[0].a", "[0].b", "[1]", "[1].a", "[1].b" }) |path| {
            var assignment: @TypeOf(@as(StmtKind, undefined).field_assign) = .{
                .parent = recipe, .name = path, .rhs_kind = .unknown, .diagnostic_only = true,
            };
            if (std.mem.eql(u8, path, "[0].b")) assignment.selected_inputs[0] = .{ .local = input };
            try transferFieldAssign(ctx, &state, assignment, pos0());
        }
        try testing.expectEqual(undefined_input, state.fieldValueMayBeUndefined(recipe, "[0].b"));
        try testing.expect(!state.fieldValueMayBeUndefined(recipe, "[0].a"));
        for ([_]struct { target: LocalId, source: LocalId }{
            .{ .target = snapshot, .source = recipe },
            .{ .target = destination, .source = snapshot },
        }) |copy| {
            try copyArrayDiagnosticBytes(ctx, &state, .{
                .target = copy.target, .source = .{ .copy_of = copy.source }, .diagnostic_only = true,
            });
            try testing.expect(!state.undefined_elements.contains(.{ .array = copy.target, .index = 0 }));
            try testing.expect(!state.fieldValueMayBeUndefined(copy.target, "[0].a"));
            try testing.expectEqual(undefined_input, state.fieldValueMayBeUndefined(copy.target, "[0].b"));
            try testing.expect(!state.fieldValueMayBeUndefined(copy.target, "[1].b"));
            try testing.expect(state.unknown_values.contains(copy.target));
            try testing.expect(!state.fieldValueIsDefined(copy.target, "[0].a"));
        }
        for ([_][]const u8{ "[0].a", "[0].b", "[1].b" }, 0..) |path, ordinal| {
            const position: cfg.SrcPos = .{ .line = 1, .column = @intCast(ordinal + 1), .byte = @intCast(ordinal) };
            try transferIndexedRead(ctx, &state, .{
                .array = destination,
                .index = .{ .constant = if (ordinal == 2) 1 else 0 },
                .name = path,
            }, position, position);
        }
        try testing.expectEqual(@as(usize, @intFromBool(undefined_input)), problems.items.len);
        if (undefined_input) {
            try testing.expectEqualStrings("use-undefined", problems.items[0].rule_id);
            try testing.expectEqual(@as(u32, 2), problems.items[0].start.column);
        }
    }
}

test "constructor mask replay: a whole slot hole still reaches every selected field" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const destination: LocalId = @enumFromInt(1);
    const locals = [_]LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .tracks_array_payload = true, .is_array = true, .array_extent = 2 },
        .{ .name = "destination", .decl_pos = pos0(), .tracks_array_payload = true, .is_array = true, .array_extent = 2 },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try state.locals.put(gpa, source, .plain);
    try state.locals.put(gpa, destination, .plain);
    try state.undefined_field_values.putContext(gpa, .{ .parent = source, .name = "[0]" }, {}, .{});
    try copyArrayDiagnosticBytes(ctx, &state, .{
        .target = destination, .source = .{ .copy_of = source }, .diagnostic_only = true,
    });
    try testing.expect(state.undefined_elements.contains(.{ .array = destination, .index = 0 }));
    try testing.expect(state.fieldValueMayBeUndefined(destination, "[0].a"));
    try testing.expect(state.fieldValueMayBeUndefined(destination, "[0].b"));
    try testing.expect(!state.fieldValueMayBeUndefined(destination, "[1].b"));
}

test "counted append prefix: undefined declaration seed is not an append poison" {
    const gpa = testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const count: LocalId = @enumFromInt(1);
    const domains = [_]state_mod.IntegerDomain{
        .{}, .{ .kind = .unsigned, .bits = @bitSizeOf(usize) },
    };
    const locals = [_]cfg.LocalInfo{
        .{ .name = "chain", .decl_pos = pos0(), .is_array = true,
            .array_extent = 16, .tracks_array_payload = true },
        .{ .name = "count", .decl_pos = pos1(), .is_unsigned = true,
            .tracks_scalar_value = true },
    };
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{
        .gpa = gpa, .locals = &locals, .problems = &problems,
        .seen = &seen, .path = "test",
    };
    var state: AbstractState = .{ .integer_domains = &domains };
    defer state.deinit(gpa);
    try transferDecl(ctx, &state, .{
        .local = array, .init_kind = .undef, .value_defined = false,
    }, pos0());
    try state.locals.put(gpa, count, .plain);
    try state.unknown_values.put(gpa, count, {});
    const prefix: cfg.Stmt = .{
        .kind = .{ .array_prefix = .{
            .array = array, .count = count, .seeded_append = true,
        } },
        .pos = pos0(), .end_pos = pos1(),
    };
    const selected: cfg.IndexTerm = .{ .local = .{ .local = count, .offset = -1 } };

    // The declaration alone cannot establish even the physical seed.
    try transfer(ctx, &state, prefix);
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, selected));
    try testing.expectEqual(@as(usize, 0), state.diagnostic_index_bounds.count());
    try transferIndexedWrite(ctx, &state, .{
        .array = array, .index = .{ .constant = 0 }, .rhs_kind = .unknown,
    }, pos0());
    try testing.expectEqual(@as(u64, 1), state.fixedPrefix(array));
    try testing.expect(state.may_undefined_values.contains(array));
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, selected));
    try transfer(ctx, &state, prefix);
    try testing.expect(!indexedValueMayBeUndefined(ctx, &state, array, selected));
    try testing.expect(state.may_undefined_values.contains(array));
    try testing.expect(state.unknown_values.contains(array));
    try testing.expect(state.unknown_values.contains(count));
    try testing.expect(!indexIsDefined(ctx, &state, selected));
    try testing.expectEqual(@as(?u64, null), state.scalarValue(count));
    try testing.expectEqual(@as(usize, 0), state.comparisons.items.len);
    try testing.expectEqual(@as(usize, 0), state.symbolic_prefixes.count());
    try testing.expect(!state.hasInitializedElement(array, selected));
    try testing.expect(!arrayHasFullCoverage(ctx, &state, array));
    try testing.expect(!state.isArrayComplete(array));
    const input: cfg.ValueInput = .{ .indexed = .{ .array = array, .index = selected } };
    try testing.expect(!returnValueIsDefined(ctx, &state, .{ .ret = .{
        .value_kind = .plain, .is_borrowed_return_type = false,
        .value_defined = true,
        .value_inputs = .{input} ++ .{null} ** 7,
    } }));

    for ([_]cfg.IndexTerm{ .{ .constant = 2 }, .unknown }) |index| {
        var poisoned: AbstractState = .{};
        defer poisoned.deinit(gpa);
        try poisoned.cloneFrom(&state, gpa);
        try transferIndexedWrite(ctx, &poisoned, .{
            .array = array, .index = index, .rhs_kind = .undef,
        }, pos1());
        try transfer(ctx, &poisoned, prefix);
        try testing.expect(indexedValueMayBeUndefined(ctx, &poisoned, array, selected));
    }
    try transferCounterStep(ctx, &state, .{ .local = count, .step = 1 });
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, array, selected));
    try testing.expectEqual(@as(usize, 0), state.diagnostic_index_bounds.count());
}


test "pointee transport corrections: mask replay respects repairs without strict certificates" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const target: LocalId = @enumFromInt(1);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .is_array = true, .array_extent = 2, .tracks_array_payload = true },
        .{ .name = "target", .decl_pos = pos0(), .is_array = true, .array_extent = 2, .tracks_array_payload = true },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try state.locals.put(gpa, source, .plain);
    try state.locals.put(gpa, target, .plain);
    try state.unknown_values.put(gpa, source, {});
    try state.undefined_elements.put(gpa, .{ .array = source, .index = 0 }, {});
    try state.undefined_elements.put(gpa, .{ .array = source, .index = 1 }, {});
    try transferFieldAssign(ctx, &state, .{
        .parent = source, .name = "[0]", .rhs_kind = .unknown, .diagnostic_only = true,
    }, pos0());
    try copyArrayDiagnosticBytes(ctx, &state, .{
        .target = target, .source = .{ .copy_of = source }, .diagnostic_only = true,
    });
    try testing.expect(!indexedValueMayBeUndefined(ctx, &state, target, .{ .constant = 0 }));
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, target, .{ .constant = 1 }));
    try testing.expect(state.undefined_elements.contains(.{ .array = source, .index = 0 }));
    const selected: cfg.ValueInput = .{ .indexed = .{ .array = target, .index = .{ .constant = 0 } } };
    try testing.expect(!returnValueIsDefined(ctx, &state, .{ .ret = .{
        .value_kind = .plain, .is_borrowed_return_type = false, .value_defined = true,
        .value_inputs = .{selected} ++ .{null} ** 7,
    } }));
}

test "pointee transport corrections: unknown array snapshot poison keeps disjoint slots silent" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const target: LocalId = @enumFromInt(1);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .is_array = true, .array_extent = 2, .tracks_array_payload = true },
        .{ .name = "target", .decl_pos = pos0(), .is_array = true, .array_extent = 2, .tracks_array_payload = true },
    };
    var state: AbstractState = .{};
    defer state.deinit(gpa);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer freeProblems(gpa, &problems);
    var seen = Seen.init();
    defer seen.deinit(gpa);
    const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
    try state.locals.put(gpa, source, .plain);
    try state.locals.put(gpa, target, .plain);
    try state.unknown_values.put(gpa, source, {});
    try transferFieldAssign(ctx, &state, .{
        .parent = source, .name = "[1]", .rhs_kind = .undef,
        .diagnostic_only = true, .entire_value_undefined = true,
    }, pos0());
    try copyArrayDiagnosticBytes(ctx, &state, .{
        .target = target, .source = .{ .copy_of = source }, .diagnostic_only = true,
    });
    try testing.expect(!indexedValueMayBeUndefined(ctx, &state, target, .{ .constant = 0 }));
    try testing.expect(indexedValueMayBeUndefined(ctx, &state, target, .{ .constant = 1 }));
    try testing.expect(state.unknown_values.contains(target));
}

test "certified array completion: only a value certificate retires prior byte holes" {
    const gpa = testing.allocator;
    const array: LocalId = @enumFromInt(0);
    const owner: LocalId = @enumFromInt(1);
    const locals = [_]LocalInfo{
        .{ .name = "array", .decl_pos = pos0(), .is_array = true, .array_extent = 2, .tracks_array_payload = true },
        .{ .name = "owner", .decl_pos = pos0() },
    };
    for ([_]bool{ false, true }) |certified| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        try transferDecl(ctx, &state, .{ .local = array, .init_kind = .undef, .value_defined = false }, pos0());
        try state.undefined_field_values.putContext(gpa, .{ .parent = array, .name = "[0].b" }, {}, .{});
        try state.fields.putContext(gpa, .{ .parent = array, .name = "[1].ptr" }, .{ .stack = owner }, .{});
        try transfer(ctx, &state, .{
            .kind = .{ .array_complete = .{ .array = array, .value_defined = certified } },
            .pos = pos0(), .end_pos = pos1(),
        });
        try testing.expectEqual(!certified, state.fieldValueMayBeUndefined(array, "[0].b"));
        try testing.expectEqual(!certified, state.unknown_values.contains(array));
        try testing.expectEqual(@as(Origin, .{ .stack = owner }), state.fields.getContext(.{ .parent = array, .name = "[1].ptr" }, .{}).?);
        const selected: cfg.ValueInput = .{ .indexed = .{ .array = array, .index = .{ .constant = 0 } } };
        try testing.expectEqual(certified, returnValueIsDefined(ctx, &state, .{ .ret = .{
            .value_kind = .plain, .is_borrowed_return_type = false, .value_defined = true,
            .value_inputs = .{selected} ++ .{null} ** 7,
        } }));
    }
}

test "optional selection followup: tag ALL stores and copies do not survive repaired joins" {
    const gpa = testing.allocator;
    const owner: LocalId = @enumFromInt(0);
    const copied: LocalId = @enumFromInt(1);
    for ([_]bool{ false, true }) |nested| {
        const locals = [_]cfg.LocalInfo{
            .{ .name = "owner", .decl_pos = pos0(), .tracks_array_payload = true, .tracks_optional_tag = !nested },
            .{ .name = "copied", .decl_pos = pos1(), .tracks_array_payload = true, .tracks_optional_tag = true },
        };
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        const path: []const u8 = if (nested) "value" else "";
        const tag_path: []const u8 = if (nested) "value.$optional-tag" else cfg.diagnostic_optional_tag;
        var negative: AbstractState = .{};
        defer negative.deinit(gpa);
        try negative.locals.put(gpa, owner, .plain);
        try negative.undefined_field_values.putContext(gpa, .{ .parent = owner, .name = path }, {}, .{});
        try negative.entire_undefined_fields.putContext(gpa, .{ .parent = owner, .name = path }, {}, .{});
        if (!nested) try negative.entire_undefined_values.put(gpa, owner, {});
        try transferFieldAssign(ctx, &negative, .{
            .parent = owner, .name = tag_path, .rhs_kind = .undef,
            .diagnostic_only = true, .entire_value_undefined = true,
        }, pos0());
        try testing.expect(fieldIsEntirelyUndefined(ctx, &negative, owner, path));
        try testing.expect(fieldIsEntirelyUndefined(ctx, &negative, owner, tag_path));
        try transferDecl(ctx, &negative, .{
            .local = copied,
            .init_kind = if (nested) .{ .field_copy_of = .{ .parent = owner, .name = path } } else .{ .copy_of = owner },
        }, pos1());
        try transferFieldAssign(ctx, &negative, .{
            .parent = copied, .name = cfg.diagnostic_optional_tag,
            .rhs_kind = .{ .field_copy_of = .{ .parent = owner, .name = tag_path } },
            .diagnostic_only = true,
        }, pos1());
        try testing.expect(localIsEntirelyUndefined(ctx, &negative, copied));
        try testing.expect(optionalTagMayBeUndefined(ctx, &negative, copied));

        var repaired: AbstractState = .{};
        defer repaired.deinit(gpa);
        try repaired.cloneFrom(&negative, gpa);
        try transferFieldAssign(ctx, &repaired, .{
            .parent = owner, .name = tag_path, .rhs_kind = .unknown, .diagnostic_only = true,
        }, pos1());
        try testing.expect(!fieldIsEntirelyUndefined(ctx, &repaired, owner, path));
        try testing.expect(!optionalTagBytesMayBeUndefined(ctx, &repaired, owner, tag_path));
        try testing.expect(optionalPayloadIsEntirelyUndefined(ctx, &repaired, .{ .parent = owner, .path = path }));
        for ([_]bool{ false, true }) |reverse| {
            var joined: AbstractState = .{};
            defer joined.deinit(gpa);
            try joined.cloneFrom(if (reverse) &repaired else &negative, gpa);
            _ = try state_mod.join(&joined, if (reverse) &negative else &repaired, gpa);
            try testing.expect(optionalTagBytesMayBeUndefined(ctx, &joined, owner, tag_path));
            try testing.expect(!fieldIsEntirelyUndefined(ctx, &joined, owner, path));
            try testing.expect(!fieldIsEntirelyUndefined(ctx, &joined, owner, tag_path));
            try testing.expect(optionalPayloadIsEntirelyUndefined(ctx, &joined, .{ .parent = owner, .path = path }));
            try transferDecl(ctx, &joined, .{
                .local = copied,
                .init_kind = if (nested) .{ .field_copy_of = .{ .parent = owner, .name = path } } else .{ .copy_of = owner },
            }, pos1());
            try transferFieldAssign(ctx, &joined, .{
                .parent = copied, .name = cfg.diagnostic_optional_tag,
                .rhs_kind = .{ .field_copy_of = .{ .parent = owner, .name = tag_path } },
                .diagnostic_only = true,
            }, pos1());
            try testing.expect(optionalTagMayBeUndefined(ctx, &joined, copied));
            try testing.expect(!localIsEntirelyUndefined(ctx, &joined, copied));
        }
    }
}

test "optional selection followup: optional tag selector snapshots do not certify payloads" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const selector: LocalId = @enumFromInt(1);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .tracks_array_payload = true, .tracks_optional_tag = true },
        .{ .name = "selector", .decl_pos = pos1(), .tracks_scalar_value = true, .tracks_optional_tag = true, .diagnostic_tag_only = true },
    };
    for ([_]bool{ false, true }) |tag_undefined| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        try state.locals.put(gpa, source, .plain);
        try state.locals.put(gpa, selector, .plain);
        try state.undefined_field_values.putContext(gpa, .{ .parent = source, .name = "" }, {}, .{});
        try state.entire_undefined_fields.putContext(gpa, .{ .parent = source, .name = "" }, {}, .{});
        try state.entire_undefined_values.put(gpa, source, {});
        try transferFieldAssign(ctx, &state, .{
            .parent = source, .name = cfg.diagnostic_optional_tag,
            .rhs_kind = if (tag_undefined) .undef else .unknown,
            .diagnostic_only = true, .entire_value_undefined = tag_undefined,
        }, pos0());
        try transferAssign(ctx, &state, .{
            .target = selector, .rhs_kind = .{ .copy_of = source }, .value_defined = false,
        }, pos1());
        const selector_origin = state.locals.get(selector).?;
        const fields_count = state.fields.count();
        const unknown_count = state.unknown_values.count();
        const unknown_fields_count = state.unknown_field_values.count();
        try testing.expectEqual(tag_undefined, localIsProvedUndefined(ctx, &state, selector));
        try testing.expect(!localInputIsDefined(ctx, &state, selector, true));
        try transferFieldAssign(ctx, &state, .{
            .parent = source, .name = cfg.diagnostic_optional_tag,
            .rhs_kind = if (tag_undefined) .unknown else .undef,
            .diagnostic_only = true, .entire_value_undefined = !tag_undefined,
        }, pos1());
        try testing.expectEqual(!tag_undefined, optionalTagMayBeUndefined(ctx, &state, source));
        try testing.expectEqual(tag_undefined, localIsProvedUndefined(ctx, &state, selector));
        try testing.expectEqual(selector_origin, state.locals.get(selector).?);
        try testing.expectEqual(fields_count, state.fields.count());
        try testing.expectEqual(unknown_count, state.unknown_values.count());
        try testing.expectEqual(unknown_fields_count, state.unknown_field_values.count());
        try testing.expect(!localInputIsDefined(ctx, &state, selector, true));
    }
}

test "diagnostic scalar transport: unknown overwrite retires holes without certifying its strict origin" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const target: LocalId = @enumFromInt(1);
    const locals = [_]cfg.LocalInfo{
        .{ .name = "source", .decl_pos = pos0(), .tracks_scalar_value = true },
        .{ .name = "target", .decl_pos = pos1(), .tracks_scalar_value = true },
    };
    for ([_]bool{ false, true }) |poison| {
        var state: AbstractState = .{};
        defer state.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        try state.locals.put(gpa, source, if (poison) .undef else .plain);
        try state.unknown_values.put(gpa, source, {});
        try state.locals.put(gpa, target, .undef);
        try state.entire_undefined_values.put(gpa, target, {});
        try copyArrayDiagnosticBytes(ctx, &state, .{
            .target = target, .source = .{ .copy_of = source }, .diagnostic_only = true,
        });
        try testing.expect(state.locals.get(target).? == .undef);
        try testing.expect(state.unknown_values.contains(target));
        try testing.expect(!localInputIsDefined(ctx, &state, target, false));
        try testing.expectEqual(poison, localIsProvedUndefined(ctx, &state, target));
        try testing.expectEqual(poison, localIsEntirelyUndefined(ctx, &state, target));
        try transfer(ctx, &state, .{
            .kind = .{ .ret = .{ .value_kind = .{ .copy_of = target }, .is_borrowed_return_type = false } },
            .pos = pos1(), .end_pos = pos1(),
        });
        try testing.expectEqual(@as(usize, if (poison) 1 else 0), problems.items.len);
    }
}

test "diagnostic scalar transport: joins retain UNKNOWN repairs and actual poison separately" {
    const gpa = testing.allocator;
    const source: LocalId = @enumFromInt(0);
    const target: LocalId = @enumFromInt(1);
    for ([_]enum { repaired_both, one_unwritten, undefined_pointer_header }{ .repaired_both, .one_unwritten, .undefined_pointer_header }) |scenario| {
        const locals = [_]cfg.LocalInfo{
            .{ .name = "source", .decl_pos = pos0(), .tracks_scalar_value = true },
            .{ .name = "target", .decl_pos = pos1(), .tracks_scalar_value = true,
                .is_pointer = scenario == .undefined_pointer_header },
        };
        var left: AbstractState = .{};
        defer left.deinit(gpa);
        var right: AbstractState = .{};
        defer right.deinit(gpa);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer freeProblems(gpa, &problems);
        var seen = Seen.init();
        defer seen.deinit(gpa);
        const ctx: Ctx = .{ .gpa = gpa, .locals = &locals, .problems = &problems, .seen = &seen, .path = "test" };
        try left.locals.put(gpa, source, .plain);
        try left.unknown_values.put(gpa, source, {});
        try left.locals.put(gpa, target, .undef);
        try right.cloneFrom(&left, gpa);
        try copyArrayDiagnosticBytes(ctx, &left, .{
            .target = target, .source = .{ .copy_of = source }, .diagnostic_only = true,
        });
        if (scenario != .one_unwritten) try copyArrayDiagnosticBytes(ctx, &right, .{
            .target = target, .source = .{ .copy_of = source }, .diagnostic_only = true,
        });
        _ = try state_mod.join(&left, &right, gpa);
        _ = try state_mod.join(&left, &right, gpa);
        try testing.expect(left.locals.get(target).? == .undef);
        try testing.expect(left.unknown_values.contains(target));
        try testing.expect(!localInputIsDefined(ctx, &left, target, false));
        try testing.expectEqual(scenario != .repaired_both, localIsProvedUndefined(ctx, &left, target));
        try transfer(ctx, &left, .{
            .kind = .{ .use = .{ .local = target } }, .pos = pos1(), .end_pos = pos1(),
        });
        try testing.expectEqual(@as(usize, if (scenario == .repaired_both) 0 else 1), problems.items.len);
    }
}
