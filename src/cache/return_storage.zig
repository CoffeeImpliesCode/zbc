//! Parameter-relative returned STORAGE, not scalar value dependencies.
//! Returned-storage results and path bytes belong to the root cache until deinit.
//! Expression-loan frames and results borrow one caller-owned scratch arena.
//! Static tag-name storage is independent of the selecting enum. Canonical
//! allocator freshness discharges deep storage only for address-free pointees;
//! a fresh outer allocation cannot erase pointer payload loans.
//! Private cell effects retain constructor/call bindings only for one query.
//! Their ordered normal/error walks share the mutation walker and work meter;
//! only caller-independent, complete symbolic returns enter the root memo.
//! A completed lexical-name index shares each immutable binding-table scan;
//! individual lookups still resolve exact declaration scope and use horizons.

const std = @import("std");
const builtin = @import("builtin");
const Ast = std.zig.Ast;
const FileCache = @import("file_cache.zig").FileCache;
const TypeResolver = @import("../type_resolver.zig").TypeResolver;
const fn_summary = @import("../model/fn_summary.zig");
const call_summary = @import("call_summary.zig");
const storage_alias = @import("storage_alias.zig");

const tokens = @import("../ast/tokens.zig");
const bindings_mod = @import("../model/local_bindings.zig");
const grow = @import("grow_analysis.zig");
const budget = @import("../budget.zig");
const Iterator = @import("type_engine").AstIterator;

/// Source, model, semantic-query, allocation, cancellation and budget failures
/// propagate unchanged. Failed walks publish no answer and remain retryable.
pub const Error = call_summary.Error;
pub const Projection = enum { cell_address, pointer_value, payload_value };
pub const Storage = enum { backing_storage, inline_storage, payload_storage };

/// A positive borrow, in the declaring function's formal coordinates.
/// Payload storage is the pointee carried IN a copied value, never its cell.
pub const Alternative = struct {
    owner: fn_summary.ParamPath,
    projection: Projection,
    storage: Storage,
    /// Field of an aggregate result carrying this borrow; "" is the result.
    result_path: []const u8 = "",
};

pub const ReturnedStorage = struct {
    /// False forbids general negative conclusions, including an empty set.
    complete: bool = false,
    alternatives: []const Alternative = &.{},
    /// Exact, unmodified formal slice forwarding. This certifies the outer
    /// selector only; it does not certify the selected elements' pointees.
    direct_formal_loan: bool = false,
    /// Exact load through an unmodified formal. Consumers must resolve the
    /// actual cell's payload; neither this nor `direct_formal_loan` proves safety.
    direct_formal_load: ?enum { element, dereference } = null,
};

const AllocationRequirement = struct { allocator: fn_summary.ParamPath, source: ?Source = null };
const SymbolicStorage = struct {
    storage: ReturnedStorage = .{},
    allocations: []const AllocationRequirement = &.{},
};

const Key = struct {
    declaration: @import("file_cache.zig").DeclKey,
    context: TypeResolver.ActualTypeID,
};
const KeyContext = struct {
    pub fn hash(_: KeyContext, key: Key) u64 {
        var h = std.hash.Wyhash.init(0);
        const tree = @intFromPtr(key.declaration.tree);
        h.update(std.mem.asBytes(&tree));
        h.update(std.mem.asBytes(&key.declaration.module));
        h.update(std.mem.asBytes(&key.declaration.declaration));
        const context_hash = key.context.hash64();
        h.update(std.mem.asBytes(&context_hash));
        return h.final();
    }
    pub fn eql(_: KeyContext, a: Key, b: Key) bool {
        return a.declaration.tree == b.declaration.tree and
            a.declaration.module == b.declaration.module and
            a.declaration.declaration == b.declaration.declaration and
            a.context.eql(b.context);
    }
};

const FormalKey = struct { function: Key, parameter: u32 };
const no_prune = std.math.maxInt(usize);
/// Frame depth at which every returned-storage walk gives up.
const depth_limit: u32 = 64;
const BindingLookup = struct { table: usize, name: usize, name_len: usize, token: Ast.TokenIndex };
const BindingIndex = std.StringHashMapUnmanaged(std.ArrayListUnmanaged(*const bindings_mod.Binding));

/// A whole-callee effect verdict. `callEffectAt(.whole)` answers for the call,
/// its canonical callee, the caller's contextual view and the caller's
/// declaration, and for nothing else: not the demanded cell, not the horizon.
const WholeEffect = struct {
    cache: *FileCache,
    declaration: Ast.Node.Index,
    resolution: TypeResolver.ResolutionFrame,
    actual: FileCache.ActualCallSummary,
    effect: ?call_summary.Effect,
};

/// Finished proofs shared by the queries of one function session. Contextual
/// entries include their exact frame, actual invocation and horizon; type
/// lookups are context-free. Failed or externally cycle-dependent proofs are
/// never published. Session scratch storage outlives every query.
const Memo = struct {
    binding_lookups: std.AutoHashMapUnmanaged(BindingLookup, ?*const bindings_mod.Binding) = .empty,
    binding_indexes: std.AutoHashMapUnmanaged(usize, BindingIndex) = .empty,
    whole_effects: std.AutoArrayHashMapUnmanaged(Ast.Node.Index, std.ArrayListUnmanaged(WholeEffect)) = .empty,
    address_free: std.HashMapUnmanaged(TypeResolver.ActualType, bool, TypeContext, 80) = .empty,
    address_narrow: std.HashMapUnmanaged(TypeResolver.ActualType, bool, TypeContext, 80) = .empty,
    deposit_free: std.HashMapUnmanaged(TypeResolver.ActualType, bool, TypeContext, 80) = .empty,
    source_cells: std.AutoArrayHashMapUnmanaged(Ast.Node.Index, std.ArrayListUnmanaged(CellAnswer)) = .empty,
    invalidations: std.AutoArrayHashMapUnmanaged(Ast.Node.Index, std.ArrayListUnmanaged(InvalidationAnswer)) = .empty,
    address_bits: std.AutoArrayHashMapUnmanaged(Ast.Node.Index, std.ArrayListUnmanaged(AddressBitsAnswer)) = .empty,
    invocations: std.AutoArrayHashMapUnmanaged(NodeKey, std.ArrayListUnmanaged(Frame)) = .empty,
    formal_failures: std.HashMapUnmanaged(FormalKey, std.ArrayListUnmanaged(FileCache.ActualCallSummary), FormalKeyContext, 80) = .empty,
    loop_windows: std.AutoArrayHashMapUnmanaged(NodeKey, []const LoopWindow) = .empty,
    rebinding_indexes: std.AutoArrayHashMapUnmanaged(NodeKey, RebindingIndex) = .empty,
    cell_types: std.AutoArrayHashMapUnmanaged(NodeKey, std.ArrayListUnmanaged(CellTypeAnswer)) = .empty,
};

/// One finished `sourceCell`: the same node under a structurally equal frame,
/// the same expected type and the same selected formal gives the same cell.
const CellAnswer = struct {
    frame: Frame,
    expected: ?TypeResolver.ActualType,
    selected_formal: ?u32,
    cell: ?SourceCell,
};

const CellTypeAnswer = struct { resolution: TypeResolver.ResolutionFrame, path: []const u8, ty: TypeResolver.ActualType };
const InvalidationAnswer = struct { frame: Frame, invalidated: bool };
const AddressBitsAnswer = struct { frame: Frame, selected_formal: ?u32, bits: bool };

const TypeContext = struct {
    pub fn hash(_: TypeContext, value: TypeResolver.ActualType) u64 {
        return value.hash64();
    }
    pub fn eql(_: TypeContext, a: TypeResolver.ActualType, b: TypeResolver.ActualType) bool {
        return a.eql(b);
    }
};
const MutationKey = struct { tree: *const Ast, body: Ast.Node.Index, domain: Domain };
const MutationSet = struct { mutations: []const Ast.Node.Index, caught: []const Ast.Node.Index, complete: bool, ordered: bool };
const NodeKey = struct { tree: *const Ast, node: Ast.Node.Index };
/// Return-only walks stop at a return's value and at nested functions.
/// Height preserves their existing depth cutoffs when an empty subtree skips.
const ReturnShape = struct { contains_return: bool, height: u32 };
const LoopWindow = struct { first: Ast.TokenIndex, last: Ast.TokenIndex };
const RebindingIndex = std.StringHashMapUnmanaged(std.ArrayListUnmanaged(Ast.TokenIndex));
const FormalKeyContext = struct {
    pub fn hash(_: FormalKeyContext, key: FormalKey) u64 {
        return KeyContext.hash(.{}, key.function) ^ std.hash.Wyhash.hash(key.parameter, "formal");
    }
    pub fn eql(_: FormalKeyContext, a: FormalKey, b: FormalKey) bool {
        return a.parameter == b.parameter and KeyContext.eql(.{}, a.function, b.function);
    }
};

/// Only grow_state.owner's instance is used. Keys borrow the canonical
/// resolver arena, which outlives this state; ALL path bytes are owned here.
pub const State = struct {
    memo: ?std.heap.ArenaAllocator = null,
    sets: std.HashMapUnmanaged(Key, SymbolicStorage, KeyContext, 80) = .empty,
    active: std.HashMapUnmanaged(Key, void, KeyContext, 80) = .empty,
    tables: std.HashMapUnmanaged(Key, bool, KeyContext, 80) = .empty,
    formal_certificates: std.HashMapUnmanaged(FormalKey, void, FormalKeyContext, 80) = .empty,
    formal_active: std.HashMapUnmanaged(FormalKey, void, FormalKeyContext, 80) = .empty,
    /// Syntax-only facts of one body: they depend on nothing else.
    mutation_sets: std.AutoHashMapUnmanaged(MutationKey, MutationSet) = .empty,
    return_shapes: std.AutoHashMapUnmanaged(NodeKey, ReturnShape) = .empty,

    pub fn deinit(self: *State, gpa: std.mem.Allocator) void {
        self.mutation_sets.deinit(gpa);
        self.return_shapes.deinit(gpa);
        self.sets.deinit(gpa);
        self.active.deinit(gpa);
        self.tables.deinit(gpa);
        self.formal_certificates.deinit(gpa);
        self.formal_active.deinit(gpa);
        if (self.memo) |*arena| arena.deinit();
        self.memo = null;
    }

    fn allocator(self: *State, gpa: std.mem.Allocator) std.mem.Allocator {
        if (self.memo == null) self.memo = std.heap.ArenaAllocator.init(gpa);
        return self.memo.?.allocator();
    }
};

/// Canonical identity/declaration/type queries each cost one semantic edge:
/// those existing queries enforce their own internal bounds. All AST nodes,
/// edges, lexical-binding candidates and helper edges use the SAME caller
/// meter. Only a root entry with no meter seeds one allowance; helpers never do.
pub fn returnedStorageAt(
    cache: *FileCache,
    token: Ast.TokenIndex,
    context: storage_alias.QueryContext,
) Error!ReturnedStorage {
    var root_remaining: u32 = call_summary.actual_query_work_limit;
    const remaining = context.remaining orelse &root_remaining;
    const state = try grow.growStateAlloc(cache);
    const root = state.owner;
    const resolver = if (context.frame) |f| f.resolver else root.zls orelse return .{};
    var scratch = std.heap.ArenaAllocator.init(root.gpa);
    defer scratch.deinit();
    var memo: Memo = .{};
    var query: Query = .{
        .root = root,
        .state = &root.return_storage_state,
        .resolver = resolver,
        .remaining = remaining,
        .scratch = &scratch,
        .memo = &memo,
        .entry_tree = cache.tree,
        .entry_token = token,
    };
    try query.charge();
    const actual = (try cache.actualCallSummaryAt(token, context.frame)) orelse {
        return .{};
    };
    return returnedStorageResolved(&query, cache, actual, context, null, null);
}

/// Private handoff: canonical actual binding and caller frame are already
/// resolved. Nested consumers share their arena, source index, and work meter.
///
/// `providers` null requires every allocator the callee draws from to be an
/// external contract, else the answer is incomplete. A non-null list is for a
/// consumer that walks values itself: an allocator requirement whose actual is
/// not proved external is handed back instead of making the answer incomplete,
/// and the consumer borrows that actual header and the stores that could have
/// replaced it, so a provider holding a frame address becomes a loan.
fn returnedStorageResolved(query: *Query, cache: *FileCache, actual: FileCache.ActualCallSummary, context: storage_alias.QueryContext, caller: ?Frame, providers: ?*std.ArrayListUnmanaged(AllocationRequirement)) Error!ReturnedStorage {
    const symbolic = try query.body(cache, actual, 0);
    var answer = symbolic.storage;
    var needs_caller = false;
    for (symbolic.allocations) |requirement| {
        try query.charge();
        needs_caller = needs_caller or requirement.allocator.path.len != 0;
    }
    for (answer.alternatives) |alternative| {
        try query.charge();
        needs_caller = needs_caller or (alternative.owner.path.len != 0 and alternative.projection != .cell_address) or
            (alternative.projection == .payload_value and alternative.owner.path.len == 0);
    }
    const caller_frame = if (needs_caller) (if (caller) |frame| frame else try query.callerFrame(cache, query.entry_token, context.frame)) else null;
    for (symbolic.allocations) |requirement| {
        try query.charge();
        var buffer: [2]Ast.Node.Index = undefined;
        const argument = (try actual.callArgumentFor(cache, &buffer, requirement.allocator.param)) orelse {
            answer.complete = false;
            continue;
        };
        var allocator_cache = cache;
        var allocator_node = argument;
        var allocator_frame = context.frame;
        var resolved = true;
        if (requirement.allocator.path.len != 0) source: {
            const frame = caller_frame orelse {
                resolved = false;
                break :source;
            };
            const source = (try query.sourceAt(frame, argument, requirement.allocator.path, 0)) orelse {
                resolved = false;
                break :source;
            };
            allocator_cache = source.frame.cache;
            allocator_node = source.node;
            allocator_frame = source.frame.resolution;
        }
        if (resolved and try @import("fresh_storage.zig").allocatorOriginIsExternal(allocator_cache, allocator_node, .{
            .claim = .{ .first = allocator_cache.tree.firstToken(allocator_node), .last = allocator_cache.tree.lastToken(allocator_node) },
            .depth = 0,
            .remaining = query.remaining,
            .frame = allocator_frame,
        }, 0)) continue;
        if (providers) |list| try list.append(query.scratch.allocator(), requirement) else answer.complete = false;
    }
    if (caller_frame) |frame| {
        var kept: ?std.ArrayListUnmanaged(Alternative) = null;
        for (answer.alternatives, 0..) |alternative, index| {
            try query.charge();
            var buffer: [2]Ast.Node.Index = undefined;
            const mapped = (try mappedStorageAt(cache, actual, alternative, &buffer)) orelse {
                answer.complete = false;
                if (kept) |*items| try items.append(query.scratch.allocator(), alternative);
                continue;
            };
            // A symbolic aggregate can carry encoded caller bits. Bind that
            // channel before retaining it; plain incoming scalar copies do
            // not borrow this caller's parameter header.
            if (alternative.projection == .payload_value and mapped.path.len == 0) {
                if (try query.nodeType(frame, mapped.node)) |ty| {
                    if (try query.addressless(frame, mapped.node, ty, 0)) {
                        if (kept == null) {
                            kept = std.ArrayListUnmanaged(Alternative).empty;
                            try kept.?.appendSlice(query.scratch.allocator(), answer.alternatives[0..index]);
                        }
                        continue;
                    }
                }
            }
            var source: Output = .{};
            const cell = try query.sourceCell(frame, mapped.node, null, 0);
            // An inline-storage pointer designates the actual's own cell at the
            // path, not a pointer value stored there; its content proves nothing.
            if (alternative.projection != .cell_address and alternative.storage != .inline_storage and cell != null and cell.?.binding.origin != .param and mapped.path.len != 0) {
                try query.projectExpression(frame, mapped.node, mapped.path, .value, alternative.result_path, &source, 0);
                for (source.allocations.items) |requirement| {
                    try query.charge();
                    if (requirement.allocator.path.len != 0) source.complete = false;
                }
                if (!source.complete) answer.complete = false;
                // Provider-backed memory is still part of the actual's
                // retained graph: its owner may free it at this boundary.
                if (source.complete and source.items.items.len == 0 and source.allocations.items.len == 0) {
                    if (kept == null) {
                        kept = std.ArrayListUnmanaged(Alternative).empty;
                        try kept.?.appendSlice(query.scratch.allocator(), answer.alternatives[0..index]);
                    }
                    continue;
                }
            }
            if (kept) |*items| try items.append(query.scratch.allocator(), alternative);
        }
        // Returned paths retain the root cache lifetime, never scratch.
        if (kept) |items| answer.alternatives = try query.state.allocator(query.root.gpa).dupe(Alternative, items.items);
    }
    return answer;
}

/// A positive selected-channel certificate, not returned-value completeness or
/// physical disjointness from another actual argument's preexisting storage.
/// Unknown transfers abstain; only successful certificates are memoized.
pub fn formalNonRetentionAt(
    cache: *FileCache,
    token: Ast.TokenIndex,
    parameter: u32,
    context: storage_alias.QueryContext,
) Error!bool {
    var root_remaining: u32 = call_summary.actual_query_work_limit;
    const root = (try grow.growStateAlloc(cache)).owner;
    const resolver = if (context.frame) |frame| frame.resolver else root.zls orelse return false;
    var scratch = std.heap.ArenaAllocator.init(root.gpa);
    defer scratch.deinit();
    var memo: Memo = .{};
    var query: Query = .{
        .root = root,
        .state = &root.return_storage_state,
        .resolver = resolver,
        .remaining = context.remaining orelse &root_remaining,
        .scratch = &scratch,
        .memo = &memo,
        .entry_tree = cache.tree,
        .entry_token = token,
    };
    try query.charge();
    const actual = (try cache.actualCallSummaryAt(token, context.frame)) orelse return false;
    return query.formalBody(cache, actual, parameter, 0);
}

/// The mapped node belongs to the call's caller tree, NOT the callee tree.
/// Selection is storage, not value dependency; payload-mode consumers must
/// still ask reachable-storage aliasing rather than certifying a TABLE cell.
pub fn mappedStorageAt(
    cache: *FileCache,
    actual: FileCache.ActualCallSummary,
    alternative: Alternative,
    buffer: *[2]Ast.Node.Index,
) Error!?storage_alias.StorageSelection {
    const argument = (try actual.callArgumentFor(cache, buffer, alternative.owner.param)) orelse return null;
    return .{ .node = argument, .path = alternative.owner.path };
}

/// Outcome domain shared by returned-storage and expression-loan queries.
pub const Domain = enum { normal, failure };

pub const ExpressionLoanOptions = struct {
    cache: *FileCache,
    body: Ast.Node.Index,
    /// All query snapshots remain owned by this caller's arena.
    scratch: *std.heap.ArenaAllocator,
    context: storage_alias.QueryContext = .{},
};
pub const ExpressionLoanRequest = struct {
    selection: storage_alias.StorageSelection,
    horizon: Ast.TokenIndex,
    domain: Domain = .normal,
};
pub const ExpressionLoan = struct {
    pub const Origin = enum { frame_cell, retained_value };
    pub const Derivation = enum { direct_address, propagated };
    binding_token: Ast.TokenIndex,
    origin: Origin,
    derivation: Derivation,
    scalar_cell: bool = false,
    /// A possible argument/event dependency is not a positive escape witness.
    /// Keep it for conservative storage queries, but do not report it as a bug.
    proved: bool = true,
};
pub const ExpressionLoans = struct {
    complete: bool = false,
    loans: []const ExpressionLoan = &.{},
};

const SourceEvent = struct {
    node: Ast.Node.Index,
    direct: bool,
    loop_start: Ast.TokenIndex = 0,
    loop_end: Ast.TokenIndex = 0,
};
const ExpressionFrame = struct { frame: Frame, events: []const SourceEvent, complete: bool };

/// One caller-owned arena/session per function. No result memo: snapshots and
/// load horizons remain explicit, and later results never overwrite old loans.
/// Only pure lookups that cannot depend on either are shared between requests.
pub const ExpressionLoanQuery = struct {
    options: ExpressionLoanOptions,
    remaining: u32 = call_summary.actual_query_work_limit,
    frames: [2]?ExpressionFrame = .{ null, null },
    memo: Memo = .{},

    pub fn init(options: ExpressionLoanOptions) ExpressionLoanQuery {
        return .{ .options = options };
    }

    pub fn expressionLoansAt(self: *ExpressionLoanQuery, request: ExpressionLoanRequest) Error!ExpressionLoans {
        const cache = self.options.cache;
        const root = (try grow.growStateAlloc(cache)).owner;
        const resolver = if (self.options.context.frame) |frame| frame.resolver else cache.zls orelse return .{};
        var query: Query = .{
            .root = root,
            .state = &root.return_storage_state,
            .resolver = resolver,
            .remaining = self.options.context.remaining orelse &self.remaining,
            .scratch = self.options.scratch,
            .memo = &self.memo,
            .entry_tree = cache.tree,
            .entry_token = cache.tree.firstToken(request.selection.node),
        };
        try query.charge();
        const domain: usize = @intFromEnum(request.domain);
        if (self.frames[domain] == null) {
            var events: std.ArrayListUnmanaged(SourceEvent) = .empty;
            query.source_events = &events;
            query.source_domain = request.domain;
            var frame = (try query.callerFrame(cache, cache.tree.firstToken(self.options.body), self.options.context.frame)) orelse return .{};
            query.source_events = null;
            if (frame.body != self.options.body) return .{};
            frame.domain = request.domain;
            self.frames[domain] = .{ .frame = frame, .events = events.items, .complete = frame.mutations_complete };
        }
        const prepared = self.frames[domain].?;
        var frame = prepared.frame;
        frame.return_token = request.horizon;
        var walk: ExpressionWalk = .{
            .cache = cache,
            .bindings = frame.bindings,
            .query = &query,
            .frame = frame,
            .events = prepared.events,
            .complete = prepared.complete,
            .load_token = request.horizon,
        };
        try walk.borrow(request.selection.node, request.selection.path, false, 0);
        return .{ .complete = walk.complete, .loans = walk.loans.items };
    }
};

/// These builtins compute values or metadata; none deposits into an operand.
fn valueBuiltin(name: []const u8) bool {
    const names = [_][]const u8{
        "@tagName", "@as", "@field", "@ptrCast", "@alignCast", "@constCast",
        "@volatileCast", "@fieldParentPtr", "@intCast", "@truncate", "@bitCast",
        "@intFromEnum", "@enumFromInt", "@intFromPtr", "@ptrFromInt",
        "@sizeOf", "@bitSizeOf", "@alignOf", "@offsetOf", "@bitOffsetOf", "@typeInfo",
        "@TypeOf", "@branchHint", "@setEvalBranchQuota", "@inComptime",
        "@splat", "@ctz", "@clz", "@popCount",
        "@addWithOverflow", "@subWithOverflow", "@mulWithOverflow", "@shlWithOverflow",
    };
    for (names) |known| if (std.mem.eql(u8, name, known)) return true;
    return false;
}

/// Assignment tags whose node data is a `node_and_node` target/value pair.
fn hasAssignOperands(tag: Ast.Node.Tag) bool {
    return switch (tag) {
        .assign,
        .assign_mul,
        .assign_div,
        .assign_mod,
        .assign_add,
        .assign_sub,
        .assign_shl,
        .assign_shl_sat,
        .assign_shr,
        .assign_bit_and,
        .assign_bit_xor,
        .assign_bit_or,
        .assign_mul_wrap,
        .assign_add_wrap,
        .assign_sub_wrap,
        .assign_mul_sat,
        .assign_add_sat,
        .assign_sub_sat,
        => true,
        else => false,
    };
}

const ExpressionWalk = struct {
    cache: *FileCache,
    bindings: bindings_mod.LocalBindings,
    query: *Query,
    frame: Frame,
    events: []const SourceEvent,
    complete: bool = true,
    loans: std.ArrayListUnmanaged(ExpressionLoan) = .empty,
    retained: bool = false,
    excluded: []const []const u8 = &.{},
    // Referenced payloads are read now; copied aggregates freeze this horizon
    // at the copy expression before following their initializer.
    load_token: Ast.TokenIndex = 0,
    payload_load: bool = false,
    element_unknown: bool = false,
    capture_load: ?CaptureLoad = null,
    capture_source: bool = false,
    /// Event-argument walks already completed in this request. A walk only
    /// adds loans and clears completeness, so repeating one under identical
    /// state changes nothing; see `effectArguments`.
    effect_walks: std.AutoArrayHashMapUnmanaged(Ast.Node.Index, std.ArrayListUnmanaged(EffectWalk)) = .empty,
    /// Finished `clearedFields` scans, by binding and use horizon.
    cleared_walks: std.AutoArrayHashMapUnmanaged(ClearedKey, std.ArrayListUnmanaged(ClearedWalk)) = .empty,
    // Propagation/selection composes a loan even when its final pointee is a
    // scalar. Only a bare address of a proven scalar local is a direct escape.
    derived_origin: bool = false,
    speculative: bool = false,

    fn covered(paths: []const []const u8, path: []const u8) bool {
        if (path.len == 0) return false;
        for (paths) |prefix| {
            if (std.mem.eql(u8, path, prefix) or
                (std.mem.startsWith(u8, path, prefix) and path.len > prefix.len and path[prefix.len] == '.'))
                return true;
        }
        return false;
    }

    fn bindingPath(self: *ExpressionWalk, node: Ast.Node.Index, binding: *const bindings_mod.Binding) Error!?[]const u8 {
        if (self.cache.tree.nodeTag(node) == .identifier) {
            const token = self.cache.tree.nodeMainToken(node);
            const lexical = try self.bindingAt(self.cache.tree.tokenSlice(token), token);
            if (lexical != null and lexical.?.name_token == binding.name_token) return "";
        }
        const cell = (try self.query.sourceCell(self.frame, node, null, 0)) orelse return null;
        if (cell.frame.cache.tree != self.cache.tree or cell.binding.name_token != binding.name_token) return null;
        return cell.path;
    }

    const ElementTarget = struct { base: Ast.Node.Index, path: []const u8 };

    fn elementTarget(self: *ExpressionWalk, node: Ast.Node.Index, depth: u8) Error!?ElementTarget {
        try self.charge();
        if (depth >= depth_limit) return self.query.depthExhausted(depth);
        const tree = self.cache.tree;
        if (tree.nodeTag(node) == .array_access)
            return .{ .base = tree.nodeData(node).node_and_node[0], .path = "" };
        if (tree.nodeTag(node) == .field_access) {
            const field = tree.nodeData(node).node_and_token;
            var target = (try self.elementTarget(field[0], depth + 1)) orelse return null;
            target.path = try self.join(target.path, tree.tokenSlice(field[1]));
            return target;
        }
        return null;
    }

    fn bindingAt(self: *ExpressionWalk, name: []const u8, token: Ast.TokenIndex) Error!?*const bindings_mod.Binding {
        return self.query.lookupBinding(self.bindings, name, token);
    }

    fn castOperand(self: *ExpressionWalk, node: Ast.Node.Index) Error!?Ast.Node.Index {
        const tree = self.cache.tree;
        switch (tree.nodeTag(node)) {
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {},
            else => return null,
        }
        const name = tree.tokenSlice(tree.nodeMainToken(node));
        if (!std.mem.eql(u8, name, "@as") and !std.mem.eql(u8, name, "@ptrCast") and
            !std.mem.eql(u8, name, "@alignCast") and !std.mem.eql(u8, name, "@constCast") and
            !std.mem.eql(u8, name, "@volatileCast") and !std.mem.eql(u8, name, "@bitCast")) return null;
        var children = Iterator.init(tree, node);
        var operand: ?Ast.Node.Index = null;
        while (children.next(tree)) |child| {
            try self.charge();
            operand = child;
        }
        return operand;
    }

    // Indexing, slicing and implicit field dereference address the backing
    // object of a reference, not the stack cell holding its pointer/header.
    fn backingBorrow(self: *ExpressionWalk, node: Ast.Node.Index, path: []const u8, depth: u8) Error!void {
        try self.charge();
        const ty = (try self.query.nodeType(self.frame, node)) orelse {
            self.complete = false;
            return;
        };
        const size = try self.query.pointerSize(ty);
        if (size != null) {
            if (path.len != 0 and size == .one) {
                var cell = (try self.query.sourceCell(self.frame, node, null, depth + 1)) orelse {
                    self.complete = false;
                    return;
                };
                cell.path = try self.join(cell.path, path);
                const selected = (try self.query.cellType(cell, depth + 1)) orelse {
                    self.complete = false;
                    return;
                };
                if (try self.query.pointerSize(selected) == null)
                    return self.cellBorrow(node, path, depth + 1);
            }
            return self.borrow(node, path, false, depth + 1);
        }
        return self.borrow(node, path, true, depth + 1);
    }

    /// The pointer a selected lvalue is reached through when the cell walk
    /// attributed that selection to the frame binding holding the pointer
    /// itself: the address then lies in the pointee, so the pointer's value
    /// carries it. A selection that really resolved to another binding (a
    /// pointer to a local) keeps its physical cell.
    fn pointeeCell(self: *ExpressionWalk, node: Ast.Node.Index, path: []const u8, cell_binding: *const bindings_mod.Binding) Error!?Ast.Node.Index {
        const pointer = switch (try self.pointerBoundary(node, path)) {
            .pointer => |value| value,
            .inline_storage => return null,
            .unknown => {
                self.complete = false;
                self.speculative = true;
                return null;
            },
        };
        const tree = self.cache.tree;
        var root = pointer;
        for (0..64) |_| {
            try self.charge();
            switch (tree.nodeTag(root)) {
                .identifier => {
                    const token = tree.nodeMainToken(root);
                    const binding = (try self.bindingAt(tree.tokenSlice(token), token)) orelse return null;
                    return if (binding.name_token == cell_binding.name_token) pointer else null;
                },
                .field_access, .grouped_expression, .unwrap_optional => root = tree.nodeData(root).node_and_token[0],
                .array_access => root = tree.nodeData(root).node_and_node[0],
                .deref => root = tree.nodeData(root).node,
                else => return null,
            }
        }
        return null;
    }

    const PointerBoundary = union(enum) { unknown, inline_storage, pointer: Ast.Node.Index };

    /// A selected cell is inline only after every accessed base type resolves.
    /// Unknown type queries must not turn a possible pointee into a frame cell.
    fn pointerBoundary(self: *ExpressionWalk, node: Ast.Node.Index, path: []const u8) Error!PointerBoundary {
        const tree = self.cache.tree;
        var current = node;
        var selected = path.len != 0;
        for (0..64) |_| {
            try self.charge();
            if (selected) {
                const ty = (try self.query.nodeType(self.frame, current)) orelse return .unknown;
                const actual = (try self.query.canonicalType(ty)) orelse return .unknown;
                if (self.query.resolver.typeTag(actual) == null) return .unknown;
                if (try self.query.pointerSize(ty) == .one) return .{ .pointer = current };
            }
            switch (tree.nodeTag(current)) {
                .identifier => return .inline_storage,
                .field_access => {
                    current = tree.nodeData(current).node_and_token[0];
                    selected = true;
                },
                .array_access => {
                    const base = tree.nodeData(current).node_and_node[0];
                    const ty = (try self.query.nodeType(self.frame, base)) orelse return .unknown;
                    const actual = (try self.query.canonicalType(ty)) orelse return .unknown;
                    if (self.query.resolver.typeTag(actual) == null) return .unknown;
                    if (try self.query.pointerSize(ty) != null) return .{ .pointer = base };
                    current = base;
                    selected = true;
                },
                .deref => return .{ .pointer = tree.nodeData(current).node },
                .grouped_expression, .unwrap_optional => {
                    current = tree.nodeData(current).node_and_token[0];
                    selected = true;
                },
                else => return .unknown,
            }
        }
        return .unknown;
    }

    fn selectedFrameCell(self: *ExpressionWalk, binding: *const bindings_mod.Binding, node: Ast.Node.Index, path: []const u8, depth: u8) Error!void {
        if (path.len == 0) return self.frameCell(binding, node);
        var prefix: usize = 0;
        while (prefix < path.len) {
            try self.charge();
            const ty = (try self.query.cellType(.{
                .frame = self.frame, .binding = binding, .node = node,
                .path = if (prefix == 0) "" else path[0 .. prefix - 1],
            }, depth + 1)) orelse {
                self.complete = false;
                return;
            };
            if (try self.query.pointerSize(ty) != null)
                return self.borrow(node, if (prefix == 0) "" else path[0 .. prefix - 1], false, depth + 1);
            // A field slot stays inline only when its parent is an aggregate.
            const tag = self.query.resolver.typeTag(ty) orelse {
                self.complete = false;
                return;
            };
            if (tag != .@"struct" and tag != .@"union") {
                self.complete = false;
                return;
            }
            const dot = std.mem.indexOfScalarPos(u8, path, prefix, '.') orelse break;
            prefix = dot + 1;
        }
        return self.frameCell(binding, node);
    }

    /// Physical selected cells and stored pointer payloads are different
    /// demands. A selector never turns an address carried IN a field into
    /// the address OF the aggregate which carries it.
    fn cellBorrow(self: *ExpressionWalk, node: Ast.Node.Index, path: []const u8, depth: u8) Error!void {
        try self.charge();
        if (depth >= depth_limit) return self.query.depthExhausted(depth);
        if (try self.enterDemand(.cell, node, path, "")) return;
        defer self.leaveDemand();
        const saved_speculative = self.speculative;
        defer self.speculative = saved_speculative;
        const tree = self.cache.tree;
        switch (tree.nodeTag(node)) {
            .grouped_expression, .unwrap_optional => return self.cellBorrow(tree.nodeData(node).node_and_token[0], path, depth + 1),
            .@"try" => return self.cellBorrow(tree.nodeData(node).node, path, depth + 1),
            .@"return", .@"break", .@"continue" => return,
            .@"catch", .@"orelse" => {
                self.complete = false;
                const pair = tree.nodeData(node).node_and_node;
                try self.cellBorrow(pair[0], path, depth + 1);
                return self.cellBorrow(pair[1], path, depth + 1);
            },
            .@"switch", .switch_comma => {
                self.complete = false;
                const selection = tree.fullSwitch(node) orelse return;
                // Only prong values can supply the selected physical address.
                for (selection.ast.cases) |case_node| {
                    try self.charge();
                    const prong = tree.fullSwitchCase(case_node) orelse continue;
                    try self.cellBorrow(prong.ast.target_expr, path, depth + 1);
                }
                return;
            },
            .address_of => {
                const value = tree.nodeData(node).node;
                if (tree.nodeTag(value) == .identifier) {
                    const token = tree.nodeMainToken(value);
                    const binding = (try self.bindingAt(tree.tokenSlice(token), token)) orelse {
                        if (try self.query.globalCellAddress(self.frame, value)) return;
                        self.complete = false;
                        return;
                    };
                    return self.selectedFrameCell(binding, value, path, depth + 1);
                }
            },
            .identifier => {
                if (tree.tokenTag(tree.nodeMainToken(node)) == .keyword_unreachable) return;
                const ty = (try self.query.nodeType(self.frame, node)) orelse {
                    self.complete = false;
                    return;
                };
                if (try self.query.pointerSize(ty) != .one) {
                    const token = tree.nodeMainToken(node);
                    const binding = (try self.bindingAt(tree.tokenSlice(token), token)) orelse {
                        self.complete = false;
                        return;
                    };
                    return self.selectedFrameCell(binding, node, path, depth + 1);
                }
            },
            else => {},
        }
        if (try self.query.sourceCell(self.frame, node, null, depth + 1)) |cell| {
            if (cell.frame.cache != self.cache or cell.frame.declaration != self.frame.declaration) {
                self.complete = false;
                return;
            }
            if (cell.binding.origin != .param) {
                if (try self.pointeeCell(node, path, cell.binding)) |pointer| return self.borrow(pointer, "", false, depth + 1);
                return self.frameCell(cell.binding, cell.node);
            }
            if (try self.query.cellType(cell, depth + 1)) |ty| {
                if (try self.query.pointerSize(ty) == null) {
                    if (try self.pointeeCell(node, path, cell.binding)) |pointer| return self.borrow(pointer, "", false, depth + 1);
                    return self.frameCell(cell.binding, cell.node);
                }
            }
            // An incoming reference points outside this invocation; taking
            // the address of the formal's own header is a different source.
            if (try self.query.sourceAt(self.frame, node, "", depth + 1)) |source| {
                if (source.frame.cache == self.cache and source.frame.declaration == self.frame.declaration and
                    source.node != node and tree.nodeTag(source.node) == .address_of)
                    return self.cellBorrow(source.node, path, depth + 1);
                return;
            }
            self.complete = false;
            return;
        }
        if (try self.query.sourceAt(self.frame, node, "", depth + 1)) |source| {
            if (source.frame.cache == self.cache and source.frame.declaration == self.frame.declaration and source.node != node)
                return self.cellBorrow(source.node, path, depth + 1);
        }
        self.complete = false;
    }

    /// Collected source events preserve before-RHS and loop horizons. Null
    /// kills need exhaustive direct stores; all overlapping unknown effects
    /// poison negative conclusions, without erasing physical positives.
    ///
    /// Every identifier load of a mutable local scans all earlier events, and
    /// each event can cost a transitive call-effect proof. The scan is a pure
    /// function of the binding, the horizon and the walk state; a finished
    /// scan is replayed from its answer. `cleared` and `poisoned` must be
    /// empty on entry.
    fn clearedFields(self: *ExpressionWalk, binding: *const bindings_mod.Binding, use_token: Ast.TokenIndex, cleared: *std.ArrayList([]const u8), poisoned: *bool, depth: u8) Error!void {
        std.debug.assert(cleared.items.len == 0 and !poisoned.*);
        const entry = self.walkState();
        const walks = try self.cleared_walks.getOrPut(self.query.scratch.allocator(), .{ .binding_token = binding.name_token, .use_token = use_token });
        if (!walks.found_existing) walks.value_ptr.* = .empty;
        for (walks.value_ptr.items) |known| {
            try self.charge();
            if (!known.state.matches(entry)) continue;
            try cleared.appendSlice(self.query.scratch.allocator(), known.cleared);
            poisoned.* = known.poisoned;
            self.element_unknown = known.element_unknown_exit;
            return;
        }
        const attempt = self.query.beginAttempt();
        try self.clearedFieldsScan(binding, use_token, cleared, poisoned, depth);
        if (!self.query.endAttempt(attempt)) return;
        const finished = self.cleared_walks.getPtr(.{ .binding_token = binding.name_token, .use_token = use_token }).?;
        try finished.append(self.query.scratch.allocator(), .{
            .state = entry,
            .cleared = try self.query.scratch.allocator().dupe([]const u8, cleared.items),
            .poisoned = poisoned.*,
            .element_unknown_exit = self.element_unknown,
        });
    }

    fn clearedFieldsScan(self: *ExpressionWalk, binding: *const bindings_mod.Binding, use_token: Ast.TokenIndex, cleared: *std.ArrayList([]const u8), poisoned: *bool, depth: u8) Error!void {
        const tree = self.cache.tree;
        for (self.events) |event| {
            try self.charge();
            const horizon = if (event.loop_start < use_token and event.loop_end >= use_token) event.loop_end + 1 else use_token;
            if (tree.lastToken(event.node) <= binding.rhs_last or tree.firstToken(event.node) >= horizon) continue;
            if (tree.nodeTag(event.node) == .address_of) {
                if ((try self.bindingPath(tree.nodeData(event.node).node, binding)) != null) poisoned.* = true;
                continue;
            }
            if (tree.nodeTag(event.node) == .assign) {
                if (tree.lastToken(event.node) >= horizon) continue;
                const pair = tree.nodeData(event.node).node_and_node;
                if (try self.bindingPath(pair[0], binding)) |path| {
                    if (path.len != 0 and event.direct and try self.fieldClearAllowed(pair[0]) and tree.nodeTag(pair[1]) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(pair[1])), "null")) {
                        try cleared.append(self.query.scratch.allocator(), path);
                    } else poisoned.* = true;
                } else if ((try self.query.sourceCell(self.frame, pair[0], null, depth + 1)) == null and
                    !(tree.nodeTag(pair[0]) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(pair[0])), "_")))
                {
                    // A rebound/reinterpreted/opaque alias can restore any
                    // killed field. Never treat failed location resolution
                    // as storage disjointness.
                    poisoned.* = true;
                    self.complete = false;
                    const saved = self.excluded;
                    self.excluded = &.{};
                    defer self.excluded = saved;
                    try self.borrow(pair[1], "", false, depth + 1);
                }
                continue;
            }
            var buffer: [2]Ast.Node.Index = undefined;
            if (TypeResolver.CallOperands.full(tree, &buffer, event.node)) |call| {
                var at_call = self.frame;
                at_call.return_token = tree.firstToken(event.node);
                const actual = try self.query.effectCall(at_call, event.node, call, depth + 1);
                const selected: SourceCell = .{ .frame = self.frame, .binding = binding, .node = self.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse {
                    poisoned.* = true;
                    self.complete = false;
                    continue;
                }, .path = "" };
                var effects: Output = .{};
                if (actual != null) {
                    try self.query.callEffectsResolved(at_call, event.node, call, actual, selected, self.frame.domain, "", &effects, depth + 1, null);
                    if (!effects.complete or effects.items.items.len != 0) {
                        poisoned.* = true;
                        if (try self.swapsWithin(at_call, call, actual.?, binding)) continue;
                        self.complete = false;
                        try self.effectArguments(event.node, call, depth + 1);
                    }
                } else {
                    var unknown_reaches = false;
                    for (call.ast.params) |argument| {
                        if (try self.query.nodeType(at_call, argument)) |ty| {
                            if (try self.query.addressFree(ty, 0)) continue;
                        }
                        const cell = try self.query.sourceCell(at_call, argument, null, 0);
                        if (cell == null or cell.?.binding.name_token == binding.name_token) unknown_reaches = true;
                    }
                    if (tree.nodeTag(call.ast.fn_expr) == .field_access) {
                        const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
                        const cell = try self.query.sourceCell(at_call, receiver, null, 0);
                        if (cell == null or cell.?.binding.name_token == binding.name_token) unknown_reaches = true;
                    }
                    if (unknown_reaches) {
                        poisoned.* = true;
                        self.complete = false;
                        try self.effectArguments(event.node, call, depth + 1);
                    }
                }
            } else {
                const tag = tree.nodeTag(event.node);
                if (tag != .builtin_call and tag != .builtin_call_two and tag != .builtin_call_comma and tag != .builtin_call_two_comma) {
                    poisoned.* = true;
                    self.complete = false;
                    continue;
                }
                const args = tree.builtinCallParams(&buffer, event.node) orelse {
                    poisoned.* = true;
                    self.complete = false;
                    continue;
                };
                for (args) |argument| {
                    const cell = try self.query.sourceCell(self.frame, argument, null, 0);
                    if (cell != null and cell.?.binding.name_token == binding.name_token) {
                        poisoned.* = true;
                        self.complete = false;
                    }
                }
            }
        }
    }

    /// The toolchain's `std.mem.swap(T, a, b)` exchanges the contents of its two
    /// pointees and stores nothing else, never either pointer. When both
    /// pointees are cells of `binding`'s own storage, the call only permutes
    /// what that storage already holds, so no new loan can reach it.
    fn swapsWithin(self: *ExpressionWalk, at_call: Frame, call: TypeResolver.CallOperands, canonical: FileCache.ActualCallSummary, binding: *const bindings_mod.Binding) Error!bool {
        const callee = canonical.callee;
        const name = callee.fn_token + 1;
        if (call.ast.params.len != 3 or name >= callee.tree.tokens.len or callee.tree.tokenTag(name) != .identifier or
            !std.mem.eql(u8, callee.tree.tokenSlice(name), "swap")) return false;
        if (!try self.query.resolver.declaredInToolchainFile(callee.handle, "/std/mem.zig")) return false;
        for (call.ast.params[1..3]) |argument| {
            try self.charge();
            const cell = (try self.query.sourceCell(at_call, argument, null, 0)) orelse return false;
            if (cell.frame.cache.tree != self.cache.tree or cell.binding.name_token != binding.name_token) return false;
        }
        return true;
    }

    fn effectArguments(self: *ExpressionWalk, node: Ast.Node.Index, call: TypeResolver.CallOperands, depth: u8) Error!void {
        const saved_frame = self.frame;
        const saved_load = self.load_token;
        const saved_retained = self.retained;
        const saved_derived = self.derived_origin;
        const saved_speculative = self.speculative;
        self.speculative = true;
        defer self.speculative = saved_speculative;
        defer {
            self.frame = saved_frame;
            self.load_token = saved_load;
            self.retained = saved_retained;
            self.derived_origin = saved_derived;
        }
        self.load_token = self.cache.tree.firstToken(node);
        self.frame.return_token = self.load_token;
        self.retained = true;
        self.derived_origin = true;
        // Unresolved borrows replay every earlier event, and each event's
        // arguments can be unresolved again: without memory this is
        // exponential in the event count. Loans only grow and completeness
        // only falls, so a finished walk under the same frame, horizon and
        // flags has nothing left to add. Failed walks are never recorded.
        // An entry made while incomplete cannot answer a complete walk (and
        // vice versa): `complete` also steers the independence shortcut.
        const entry = self.walkState();
        const walks = try self.effect_walks.getOrPut(self.query.scratch.allocator(), node);
        if (!walks.found_existing) walks.value_ptr.* = .empty;
        for (walks.value_ptr.items) |known| {
            try self.charge();
            if (known.state.matches(entry)) {
                self.element_unknown = known.element_unknown_exit;
                return;
            }
        }
        const attempt = self.query.beginAttempt();
        const actual = try self.query.effectCall(self.frame, node, call, depth + 1);
        if (actual) |canonical| {
            // Mutation uncertainty does not make every input a retained value.
            // Reuse the selected-formal certificate: it covers both returned
            // storage and outward stores, including transitive scalar copies.
            // An unknown certificate keeps the existing conservative channel.
            const function = canonical.callee.reference.actual_type.data.function;
            for (function.parameters, 0..) |_, index| {
                try self.charge();
                var buffer: [2]Ast.Node.Index = undefined;
                const argument = (try canonical.callArgumentFor(self.cache, &buffer, @intCast(index))) orelse {
                    self.complete = false;
                    // Failed argument mapping is not a separation proof.
                    for (call.ast.params) |unknown| try self.borrow(unknown, "", false, depth + 1);
                    if (self.cache.tree.nodeTag(call.ast.fn_expr) == .field_access) {
                        const receiver = self.cache.tree.nodeData(call.ast.fn_expr).node_and_token[0];
                        try self.receiverBorrow(self.frame, null, receiver, depth + 1);
                    }
                    continue;
                };
                if (try self.query.formalBody(self.cache, canonical, @intCast(index), depth + 1)) continue;
                if (index == 0 and canonical.argument_offset == 1)
                    try self.receiverBorrow(self.frame, actual, argument, depth + 1)
                else
                    try self.borrow(argument, "", false, depth + 1);
            }
        } else {
            for (call.ast.params) |argument| try self.borrow(argument, "", false, depth + 1);
            if (self.cache.tree.nodeTag(call.ast.fn_expr) == .field_access) {
                const receiver = self.cache.tree.nodeData(call.ast.fn_expr).node_and_token[0];
                try self.receiverBorrow(self.frame, null, receiver, depth + 1);
            }
        }
        if (!self.query.endAttempt(attempt)) return;
        // The map may have grown during the walk; look the list up again.
        const finished = self.effect_walks.getPtr(node).?;
        try finished.append(self.query.scratch.allocator(), .{ .state = entry, .element_unknown_exit = self.element_unknown });
    }

    /// `x.allocator()` of a standard-library allocator type builds
    /// `.{ .ptr = x, .vtable = <constant> }`: no storage but the receiver's.
    fn sdkAllocatorHeader(self: *ExpressionWalk, canonical: FileCache.ActualCallSummary) Error!bool {
        const callee = canonical.callee;
        const tree = callee.tree;
        const name = callee.fn_token + 1;
        if (canonical.argument_offset != 1 or name >= tree.tokens.len or tree.tokenTag(name) != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(name), "allocator")) return false;
        const files = [_][]const u8{ "/std/heap/ArenaAllocator.zig", "/std/heap/FixedBufferAllocator.zig", "/std/heap/debug_allocator.zig" };
        for (files) |suffix| {
            try self.charge();
            if (try self.query.resolver.declaredInToolchainFile(callee.handle, suffix)) return true;
        }
        return false;
    }

    /// A std `Allocator` allocation call whose elements hold no address returns
    /// provider memory: only the provider argument can lend it storage. Copied
    /// elements (`dupe`) must also be narrow, since a copy keeps address bits.
    fn allocationBorrow(self: *ExpressionWalk, canonical: FileCache.ActualCallSummary, node: Ast.Node.Index, depth: u8) Error!bool {
        const tree = self.cache.tree;
        const primitive = (try @import("fresh_storage.zig").allocatorPrimitive(self.cache, canonical, .{
            .claim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) },
            .depth = 0,
            .remaining = self.query.remaining,
            .frame = self.frame.resolution,
        })) orelse return false;
        if (primitive.operation != .allocate) return false;
        const result = (try self.query.nodeType(self.frame, node)) orelse return false;
        const element = (try self.query.allocationPointee(result)) orelse return false;
        if (primitive.copies_elements) {
            if (!try self.query.addressNarrow(element, 0)) return false;
        } else if (!try self.query.addressFree(element, 0)) return false;
        var buffer: [2]Ast.Node.Index = undefined;
        const provider = (try canonical.callArgumentFor(self.cache, &buffer, primitive.allocator_parameter)) orelse return false;
        try self.borrow(provider, "", false, depth + 1);
        return true;
    }

    /// The call's returned storage. An allocator the callee draws from that is
    /// not a proved external contract (a field of a formal aggregate) is
    /// borrowed as the actual header it is, with the stores that could have put
    /// a frame-backed provider there. Memory such a provider hands out is owned
    /// by the provider: it reaches this frame only through an address the
    /// header itself carries, so the result is complete either way.
    fn returnedWithProviders(self: *ExpressionWalk, canonical: FileCache.ActualCallSummary, at_call: Frame, depth: u8) Error!ReturnedStorage {
        var providers: std.ArrayListUnmanaged(AllocationRequirement) = .empty;
        var returned = try returnedStorageResolved(self.query, self.cache, canonical, .{ .remaining = self.query.remaining, .frame = self.frame.resolution }, at_call, &providers);
        if (providers.items.len == 0) return returned;
        const saved = self.excluded;
        defer self.excluded = saved;
        self.excluded = &.{};
        for (providers.items) |requirement| {
            try self.charge();
            var buffer: [2]Ast.Node.Index = undefined;
            const argument = (try canonical.callArgumentFor(self.cache, &buffer, requirement.allocator.param)) orelse {
                returned.complete = false;
                continue;
            };
            try self.borrow(argument, requirement.allocator.path, false, depth + 1);
        }
        try self.providerStores(depth + 1);
        return returned;
    }

    /// A receiver passed by implicit address whose physical cell is already a
    /// loan is not also retained as a copied value. Reachable storage stays borrowed.
    fn receiverBorrow(self: *ExpressionWalk, caller: Frame, actual: ?FileCache.ActualCallSummary, receiver: Ast.Node.Index, depth: u8) Error!void {
        if (actual) |canonical| {
            if (canonical.argument_offset == 1) {
                if (try self.query.actualArgumentSource(caller, canonical, 0, receiver, null, depth + 1)) |source| {
                    if (source.cell) |cell| {
                        if (cell.frame.cache == self.cache and cell.frame.declaration == self.frame.declaration and
                            cell.frame.invocation == self.frame.invocation and self.loaned(cell.binding.name_token, .frame_cell))
                        {
                            const saved = self.retained;
                            self.retained = false;
                            defer self.retained = saved;
                            return self.borrow(receiver, "", false, depth + 1);
                        }
                    }
                }
            }
        }
        try self.borrow(receiver, "", false, depth + 1);
    }

    fn loaned(self: *ExpressionWalk, token: Ast.TokenIndex, origin: ExpressionLoan.Origin) bool {
        for (self.loans.items) |loan| {
            if (loan.binding_token == token and loan.origin == origin) return true;
        }
        return false;
    }

    /// Select this block's lexical break values, not unrelated nested labels.
    /// Each value is evaluated at its own inner horizon. A root block token
    /// precedes declarations and stores inside it and is not a load boundary.
    fn blockBorrow(self: *ExpressionWalk, node: Ast.Node.Index, path: []const u8, location: bool, depth: u8) Error!void {
        const tree = self.cache.tree;
        const main = tree.nodeMainToken(node);
        const tags = tree.tokens.items(.tag);
        if (main < 2 or tags[main - 1] != .colon or tags[main - 2] != .identifier) {
            self.complete = false;
            return;
        }
        const label = tree.tokenSlice(main - 2);
        var count: usize = 0;
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            try self.blockBreaks(child, label, path, location, &count, depth + 1);
        if (count == 0) self.complete = false;
    }

    fn blockBreaks(self: *ExpressionWalk, node: Ast.Node.Index, label: []const u8, path: []const u8, location: bool, count: *usize, depth: u8) Error!void {
        try self.charge();
        if (depth >= depth_limit) return self.query.depthExhausted(depth);
        const tree = self.cache.tree;
        switch (tree.nodeTag(node)) {
            .fn_decl, .@"defer", .@"errdefer", .@"return" => return,
            .@"break" => {
                const data = tree.nodeData(node).opt_token_and_opt_node;
                const target = data[0].unwrap() orelse return;
                if (!std.mem.eql(u8, tree.tokenSlice(target), label)) return;
                count.* += 1;
                const value = data[1].unwrap() orelse {
                    self.complete = false;
                    return;
                };
                const saved_frame = self.frame;
                const saved_load = self.load_token;
                const saved_derived = self.derived_origin;
                defer {
                    self.frame = saved_frame;
                    self.load_token = saved_load;
                    self.derived_origin = saved_derived;
                }
                self.load_token = tree.firstToken(value);
                self.frame.return_token = self.load_token;
                self.derived_origin = true;
                return self.borrow(value, path, location, depth + 1);
            },
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                const main = tree.nodeMainToken(node);
                const tags = tree.tokens.items(.tag);
                if (main >= 2 and tags[main - 1] == .colon and tags[main - 2] == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(main - 2), label)) return;
            },
            .@"if", .if_simple => {
                const conditional = tree.fullIf(node).?;
                const known = try self.frame.resolution.boolValueOfNode(conditional.ast.cond_expr);
                if (known == null or known.?) try self.blockBreaks(conditional.ast.then_expr, label, path, location, count, depth + 1);
                if (known == null or !known.?) {
                    if (conditional.ast.else_expr.unwrap()) |other|
                        try self.blockBreaks(other, label, path, location, count, depth + 1);
                }
                return;
            },
            else => {},
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            try self.blockBreaks(child, label, path, location, count, depth + 1);
    }

    fn fieldClearAllowed(self: *ExpressionWalk, destination: Ast.Node.Index) Error!bool {
        var cell = (try self.query.sourceCell(self.frame, destination, null, 0)) orelse return false;
        const path = cell.path;
        cell.path = "";
        var segments = std.mem.splitScalar(u8, path, '.');
        while (segments.next()) |segment| {
            const ty = (try self.query.cellType(cell, 0)) orelse return false;
            if (self.query.resolver.typeTag(ty) != .@"struct") return false;
            cell.path = try self.join(cell.path, segment);
        }
        return true;
    }

    fn frameCell(self: *ExpressionWalk, binding: *const bindings_mod.Binding, node: Ast.Node.Index) Error!void {
        if (try self.query.explicitComptimeCell(self.frame, binding)) {
            const ty = try self.query.nodeType(self.frame, node);
            if (ty == null or !try self.query.staticCellPayload(ty.?, 0)) {
                self.complete = false;
                try self.replayEvents(null, 0);
            }
            return;
        }
        var scalar = false;
        if (try self.query.nodeType(self.frame, node)) |ty| {
            if (try self.query.canonicalType(ty)) |value| {
                if (self.query.resolver.typeTag(value)) |tag| {
                    scalar = switch (tag) {
                        .int, .float, .comptime_int, .comptime_float, .bool, .@"enum", .error_set => true,
                        else => false,
                    };
                } else self.complete = false;
            } else self.complete = false;
        } else self.complete = false;
        try self.add(binding.name_token, .frame_cell, scalar);
    }

    fn writtenEffects(self: *ExpressionWalk, reference: Ast.Node.Index, binding: *const bindings_mod.Binding, use_token: Ast.TokenIndex, path: []const u8, depth: u8) Error!void {
        const tree = self.cache.tree;
        const start = if (binding.origin == .param) binding.name_token else binding.rhs_last;
        for (self.events) |event| {
            try self.charge();
            const horizon = if (event.loop_start < use_token and event.loop_end >= use_token) event.loop_end + 1 else use_token;
            if (tree.firstToken(event.node) <= start or tree.lastToken(event.node) >= horizon) continue;
            const tag = tree.nodeTag(event.node);
            if (tag == .assign or tag == .address_of) continue;
            var at_effect = self.frame;
            at_effect.return_token = tree.firstToken(event.node);
            var cell = (try self.query.sourceCell(at_effect, reference, null, depth + 1)) orelse {
                self.complete = false;
                continue;
            };
            cell.path = try self.join(cell.path, path);
            var effects: Output = .{};
            var buffer: [2]Ast.Node.Index = undefined;
            const call = TypeResolver.CallOperands.full(tree, &buffer, event.node);
            var permutation = false;
            if (call) |operands| {
                const actual = try self.query.effectCall(at_effect, event.node, operands, depth + 1);
                try self.query.callEffectsResolved(at_effect, event.node, operands, actual, cell, self.frame.domain, "", &effects, depth + 1, null);
                if (actual) |canonical|
                    try self.copiedCallEffects(at_effect, canonical, cell, depth + 1);
                if (actual) |canonical| permutation = try self.swapsWithin(at_effect, operands, canonical, binding);
            } else {
                at_effect.mutations = try self.query.scratch.allocator().dupe(Ast.Node.Index, &.{event.node});
                try self.query.effectsFor(at_effect, cell, horizon, self.frame.domain, "", &effects, depth + 1);
            }
            // A scalar copy separates the source header from the destination,
            // but can still copy encoded addresses carried by its elements.
            if (effects.complete and effects.items.items.len == 0) {
                if (tree.builtinCallParams(&buffer, event.node)) |arguments| {
                    if (arguments.len == 2 and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(event.node)), "@memcpy")) {
                        const target = try self.query.sourceCell(at_effect, arguments[0], null, depth + 1);
                        if (target != null and try self.query.cellsOverlap(target.?, cell)) {
                            const saved = self.frame;
                            const saved_load = self.load_token;
                            self.frame = at_effect;
                            self.load_token = at_effect.return_token;
                            defer {
                                self.frame = saved;
                                self.load_token = saved_load;
                            }
                            try self.elementBorrow(arguments[1], "", "", depth + 1);
                        }
                    }
                }
            }
            if (!permutation and (!effects.complete or effects.items.items.len != 0)) {
                self.complete = false;
                const saved_speculative = self.speculative;
                self.speculative = true;
                defer self.speculative = saved_speculative;
                const saved = self.frame;
                const saved_load = self.load_token;
                self.frame.return_token = tree.firstToken(event.node);
                self.load_token = self.frame.return_token;
                defer {
                    self.frame = saved;
                    self.load_token = saved_load;
                }
                if (call) |operands| {
                    try self.effectArguments(event.node, operands, depth + 1);
                } else if (tree.builtinCallParams(&buffer, event.node)) |arguments| {
                    const name = tree.tokenSlice(tree.nodeMainToken(event.node));
                    if (arguments.len == 2 and (std.mem.eql(u8, name, "@memcpy") or std.mem.eql(u8, name, "@memset"))) {
                        if (std.mem.eql(u8, name, "@memcpy"))
                            try self.elementBorrow(arguments[1], "", "", depth + 1)
                        else
                            try self.borrow(arguments[1], "", false, depth + 1);
                    } else for (arguments) |argument| try self.borrow(argument, "", false, depth + 1);
                } else if (hasAssignOperands(tag)) {
                    try self.borrow(tree.nodeData(event.node).node_and_node[1], "", false, depth + 1);
                }
            }
        }
    }
    /// Reuse actual copy sources discovered by the existing effect scan.
    /// Do not traverse the callee a second time for each loaded field.
    fn copiedCallEffects(self: *ExpressionWalk, caller: Frame, actual: FileCache.ActualCallSummary, cell: SourceCell, depth: u8) Error!void {
        const count = self.query.copied_payloads.items.len;
        var index: usize = 0;
        while (index < count) : (index += 1) {
            try self.charge();
            const copied = self.query.copied_payloads.items[index];
            if (!Query.sameCellRoot(copied.cell, cell) or !std.mem.eql(u8, copied.cell.path, cell.path)) continue;
            var active = copied.frame.invocation;
            var matches = false;
            while (active) |invocation| : (active = invocation.caller.invocation) {
                if (sameActual(invocation.actual, actual) and sameFrame(invocation.caller, caller)) {
                    matches = true;
                    break;
                }
            }
            if (!matches) continue;
            try self.borrowActualSource(copied.source, copied.path, copied.element, depth + 1);
        }
    }

    /// A proved store's RHS is evaluated in its actual invocation. Follow its
    /// formal-to-actual mapping, rather than treating every call argument as
    /// stored. Foreign frame cells are checked when that function is analyzed.
    fn borrowActualSource(self: *ExpressionWalk, source: Source, path: []const u8, element: bool, depth: u8) Error!void {
        try self.charge();
        if (depth >= depth_limit) {
            self.complete = false;
            return;
        }
        if (source.frame.cache == self.cache and source.frame.declaration == self.frame.declaration and
            sameInvocation(source.frame.invocation, self.frame.invocation))
        {
            const saved_frame = self.frame;
            const saved_load = self.load_token;
            self.frame = source.frame;
            self.load_token = source.frame.return_token;
            defer {
                self.frame = saved_frame;
                self.load_token = saved_load;
            }
            if (element) return self.elementBorrow(source.node, path, "", depth + 1);
            return self.borrow(source.node, path, false, depth + 1);
        }
        const tree = source.frame.cache.tree;
        const node = source.node;
        if (try self.query.sourceAt(source.frame, node, path, depth + 1)) |mapped| {
            if (mapped.frame.cache != source.frame.cache or mapped.frame.declaration != source.frame.declaration or
                mapped.node != node or !sameInvocation(mapped.frame.invocation, source.frame.invocation))
                return self.borrowActualSource(mapped, "", element, depth + 1);
        }
        if (path.len != 0) {
            self.complete = false;
            return;
        }
        if (try self.query.nodeType(source.frame, node)) |ty|
            if (try self.query.addressless(source.frame, node, ty, 0)) return;
        switch (tree.nodeTag(node)) {
            .number_literal, .char_literal, .string_literal, .multiline_string_literal, .enum_literal, .error_value => return,
            // The foreign cell belongs to the callee, not this function.
            .address_of => return,
            .identifier, .field_access, .array_access, .deref => {
                self.complete = false;
                return;
            },
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &buffer, node) != null) {
            self.complete = false;
            return;
        }
        if (tree.builtinCallParams(&buffer, node)) |arguments| {
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            // Only value casts forward operand bits; type operands and other
            // metadata computations never establish an address dependency.
            for ([_][]const u8{
                "@as", "@ptrCast", "@alignCast", "@constCast", "@volatileCast",
                "@intCast", "@truncate", "@bitCast", "@intFromEnum",
                "@enumFromInt", "@intFromPtr", "@ptrFromInt",
            }) |cast| {
                if (!std.mem.eql(u8, name, cast)) continue;
                if (arguments.len == 0) break;
                return self.borrowActualSource(.{ .frame = source.frame, .node = arguments[arguments.len - 1] }, "", element, depth + 1);
            }
            self.complete = false;
            return;
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            try self.borrowActualSource(.{ .frame = source.frame, .node = child }, "", element, depth + 1);
    }

    const CaptureMode = enum { value, dereference, element };
    const CaptureLoad = struct { mode: CaptureMode, horizon: Ast.TokenIndex };

    /// Every mutable input a borrow walk reads. `frame` carries the return
    /// horizon in `return_token`. Two walks with equal state and equal
    /// arguments do identical work.
    const WalkState = struct {
        frame: Frame,
        excluded: []const []const u8,
        load_token: Ast.TokenIndex,
        payload_load: bool,
        capture_load: ?CaptureLoad,
        capture_source: bool,
        complete: bool,
        element_unknown: bool,
        retained: bool,
        derived_origin: bool,
        speculative: bool,

        fn matches(a: WalkState, b: WalkState) bool {
            if (a.load_token != b.load_token or a.payload_load != b.payload_load or a.complete != b.complete or
                a.element_unknown != b.element_unknown or a.retained != b.retained or a.speculative != b.speculative or
                a.derived_origin != b.derived_origin or a.capture_source != b.capture_source or !std.meta.eql(a.capture_load, b.capture_load) or
                a.excluded.len != b.excluded.len or !sameFrame(a.frame, b.frame)) return false;
            for (a.excluded, b.excluded) |left, right| {
                if (!std.mem.eql(u8, left, right)) return false;
            }
            return true;
        }
    };
    const EffectWalk = struct { state: WalkState, element_unknown_exit: bool };
    const ClearedKey = struct { binding_token: Ast.TokenIndex, use_token: Ast.TokenIndex };
    const ClearedWalk = struct { state: WalkState, cleared: []const []const u8, poisoned: bool, element_unknown_exit: bool };

    fn walkState(self: *const ExpressionWalk) WalkState {
        return .{
            .frame = self.frame,
            .excluded = self.excluded,
            .load_token = self.load_token,
            .payload_load = self.payload_load,
            .capture_load = self.capture_load,
            .capture_source = self.capture_source,
            .complete = self.complete,
            .element_unknown = self.element_unknown,
            .retained = self.retained,
            .derived_origin = self.derived_origin,
            .speculative = self.speculative,
        };
    }

    fn captureBorrow(self: *ExpressionWalk, binding: *const bindings_mod.Binding, path: []const u8, mode: CaptureMode, depth: u8) Error!void {
        const saved_origin = self.derived_origin;
        self.derived_origin = true;
        defer self.derived_origin = saved_origin;
        const saved_capture_source = self.capture_source;
        self.capture_source = true;
        defer self.capture_source = saved_capture_source;
        try self.captureBorrowSource(binding, path, mode, depth);
        // Only an unresolved source needs a synthetic capture coordinate.
        // A known literal/header forwards its actual physical loans instead.
        if (!self.complete) try self.add(binding.name_token, .retained_value, false);
    }

    fn captureBorrowSource(self: *ExpressionWalk, binding: *const bindings_mod.Binding, path: []const u8, mode: CaptureMode, depth: u8) Error!void {
        const rhs = self.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse {
            self.complete = false;
            return;
        };
        const saved = self.load_token;
        const saved_frame = self.frame;
        defer {
            self.load_token = saved;
            self.frame = saved_frame;
        }
        const pointer_capture = binding.name_token != 0 and self.cache.tree.tokenTag(binding.name_token - 1) == .asterisk;
        if (!pointer_capture) {
            self.load_token = binding.rhs_last + 1;
            self.frame.return_token = self.load_token;
        }
        const ty = if (try self.query.nodeType(self.frame, rhs)) |value| try self.query.canonicalType(value) else null;
        const optional = if (ty) |value| self.query.resolver.typeTag(value) == .optional else false;
        if (optional) {
            if (pointer_capture) {
                if (mode == .value and path.len == 0) return self.cellBorrow(rhs, "", depth + 1);
                return switch (mode) {
                    .value, .dereference => self.borrow(rhs, path, false, depth + 1),
                    .element => self.elementBorrow(rhs, "", path, depth + 1),
                };
            }
            return switch (mode) {
                .value => self.borrow(rhs, path, false, depth + 1),
                .dereference => self.dereferenceBorrow(rhs, path, depth + 1),
                .element => self.elementBorrow(rhs, "", path, depth + 1),
            };
        }
        // `|*element|` addresses an element cell of the iterable's storage: the
        // local array itself, but only the referent of a slice or pointer.
        if (pointer_capture and mode == .value and path.len == 0) return self.backingBorrow(rhs, "", depth + 1);
        const saved_capture = self.capture_load;
        defer self.capture_load = saved_capture;
        self.capture_load = if (!pointer_capture and mode != .value) .{ .mode = mode, .horizon = saved } else null;
        return self.elementBorrow(rhs, "", path, depth + 1);
    }

    fn capturedElement(self: *ExpressionWalk, node: Ast.Node.Index, path: []const u8, depth: u8) Error!void {
        const capture = self.capture_load orelse return self.borrow(node, path, false, depth + 1);
        self.capture_load = null;
        defer self.capture_load = capture;
        return self.frozenCaptureLoad(node, path, capture.mode, self.load_token, capture.horizon, depth + 1);
    }

    fn frozenCaptureLoad(self: *ExpressionWalk, node: Ast.Node.Index, path: []const u8, mode: CaptureMode, copy_horizon: Ast.TokenIndex, read_horizon: Ast.TokenIndex, depth: u8) Error!void {
        try self.charge();
        if (depth >= depth_limit) return self.query.depthExhausted(depth);
        const tree = self.cache.tree;
        const saved_frame = self.frame;
        const saved_load = self.load_token;
        defer {
            self.frame = saved_frame;
            self.load_token = saved_load;
        }
        self.frame.return_token = copy_horizon;
        self.load_token = copy_horizon;
        if (try self.query.sourceAt(self.frame, node, "", depth + 1)) |source| {
            if (source.frame.cache == self.cache and source.frame.declaration == self.frame.declaration and source.node != node)
                return self.frozenCaptureLoad(source.node, path, mode, source.frame.return_token, read_horizon, depth + 1);
        }
        if (tree.nodeTag(node) == .field_access) {
            const field = tree.nodeData(node).node_and_token;
            return self.frozenCaptureSelection(field[0], tree.tokenSlice(field[1]), path, mode, copy_horizon, read_horizon, depth + 1);
        }
        if (tree.nodeTag(node) == .identifier) {
            const token = tree.nodeMainToken(node);
            if (try self.bindingAt(tree.tokenSlice(token), token)) |binding| {
                if (binding.origin != .param and binding.origin != .loop_capture) {
                    const initializer = self.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse {
                        self.complete = false;
                        return;
                    };
                    try self.frozenCaptureLoad(initializer, path, mode, tree.firstToken(initializer), read_horizon, depth + 1);
                    for (self.events) |event| {
                        try self.charge();
                        if (tree.nodeTag(event.node) != .assign or tree.lastToken(event.node) >= copy_horizon or tree.firstToken(event.node) <= binding.rhs_last) continue;
                        const pair = tree.nodeData(event.node).node_and_node;
                        if (tree.nodeTag(pair[0]) != .identifier) continue;
                        if (try self.bindingPath(pair[0], binding)) |target| {
                            if (target.len == 0) try self.frozenCaptureLoad(pair[1], path, mode, tree.firstToken(event.node), read_horizon, depth + 1);
                        }
                    }
                    return;
                }
            }
        }
        switch (tree.nodeTag(node)) {
            .grouped_expression, .unwrap_optional => return self.frozenCaptureLoad(tree.nodeData(node).node_and_token[0], path, mode, copy_horizon, read_horizon, depth + 1),
            .@"try" => return self.frozenCaptureLoad(tree.nodeData(node).node, path, mode, copy_horizon, read_horizon, depth + 1),
            .@"if", .if_simple => {
                const conditional = tree.fullIf(node).?;
                try self.frozenCaptureLoad(conditional.ast.then_expr, path, mode, copy_horizon, read_horizon, depth + 1);
                if (conditional.ast.else_expr.unwrap()) |other| try self.frozenCaptureLoad(other, path, mode, copy_horizon, read_horizon, depth + 1) else self.complete = false;
                return;
            },
            .@"catch", .@"orelse" => {
                const pair = tree.nodeData(node).node_and_node;
                try self.frozenCaptureLoad(pair[0], path, mode, copy_horizon, read_horizon, depth + 1);
                return self.frozenCaptureLoad(pair[1], path, mode, copy_horizon, read_horizon, depth + 1);
            },
            else => {},
        }
        self.load_token = read_horizon;
        self.frame.return_token = read_horizon;
        return switch (mode) {
            .value => self.borrow(node, path, false, depth + 1),
            .dereference => self.dereferenceBorrow(node, path, depth + 1),
            .element => self.elementBorrow(node, "", path, depth + 1),
        };
    }

    fn frozenCaptureSelection(self: *ExpressionWalk, node: Ast.Node.Index, selection: []const u8, path: []const u8, mode: CaptureMode, copy_horizon: Ast.TokenIndex, read_horizon: Ast.TokenIndex, depth: u8) Error!void {
        try self.charge();
        if (depth >= depth_limit) return self.query.depthExhausted(depth);
        if (selection.len == 0) return self.frozenCaptureLoad(node, path, mode, copy_horizon, read_horizon, depth + 1);
        const tree = self.cache.tree;
        const saved = self.frame;
        defer self.frame = saved;
        self.frame.return_token = copy_horizon;
        if (try self.query.sourceAt(self.frame, node, selection, depth + 1)) |source| {
            if (source.frame.cache == self.cache and source.frame.declaration == self.frame.declaration)
                return self.frozenCaptureLoad(source.node, path, mode, source.frame.return_token, read_horizon, depth + 1);
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullStructInit(&buffer, node)) |literal| {
            const dot = std.mem.indexOfScalar(u8, selection, '.');
            const head = if (dot) |at| selection[0..at] else selection;
            const tail = if (dot) |at| selection[at + 1 ..] else "";
            var found = false;
            for (literal.ast.fields) |field| {
                try self.charge();
                const first = tree.firstToken(field);
                const tags = tree.tokens.items(.tag);
                if (first < 3 or tags[first - 1] != .equal or tags[first - 2] != .identifier or tags[first - 3] != .period) {
                    self.complete = false;
                    continue;
                }
                if (!std.mem.eql(u8, tree.tokenSlice(first - 2), head)) continue;
                found = true;
                try self.frozenCaptureSelection(field, tail, path, mode, copy_horizon, read_horizon, depth + 1);
            }
            if (!found) self.complete = false;
            return;
        }
        switch (tree.nodeTag(node)) {
            .field_access => {
                const field = tree.nodeData(node).node_and_token;
                return self.frozenCaptureSelection(field[0], try self.join(tree.tokenSlice(field[1]), selection), path, mode, copy_horizon, read_horizon, depth + 1);
            },
            .grouped_expression, .unwrap_optional => return self.frozenCaptureSelection(tree.nodeData(node).node_and_token[0], selection, path, mode, copy_horizon, read_horizon, depth + 1),
            .@"try" => return self.frozenCaptureSelection(tree.nodeData(node).node, selection, path, mode, copy_horizon, read_horizon, depth + 1),
            .@"if", .if_simple => {
                const conditional = tree.fullIf(node).?;
                try self.frozenCaptureSelection(conditional.ast.then_expr, selection, path, mode, copy_horizon, read_horizon, depth + 1);
                if (conditional.ast.else_expr.unwrap()) |other| try self.frozenCaptureSelection(other, selection, path, mode, copy_horizon, read_horizon, depth + 1) else self.complete = false;
                return;
            },
            .@"catch", .@"orelse" => {
                const pair = tree.nodeData(node).node_and_node;
                try self.frozenCaptureSelection(pair[0], selection, path, mode, copy_horizon, read_horizon, depth + 1);
                return self.frozenCaptureSelection(pair[1], selection, path, mode, copy_horizon, read_horizon, depth + 1);
            },
            .identifier => {
                var selected = (try self.query.sourceCell(self.frame, node, null, depth + 1)) orelse {
                    self.complete = false;
                    return;
                };
                selected.path = try self.join(selected.path, selection);
                if (selected.frame.cache != self.cache or selected.frame.declaration != self.frame.declaration or selected.binding.origin == .param or selected.binding.origin == .loop_capture) {
                    self.complete = false;
                    return;
                }
                const initializer = self.cache.nodeForExactSpan(selected.binding.rhs_first, selected.binding.rhs_last) orelse {
                    self.complete = false;
                    return;
                };
                try self.frozenCaptureSelection(initializer, selected.path, path, mode, tree.firstToken(initializer), read_horizon, depth + 1);
                for (self.events) |event| {
                    try self.charge();
                    if (tree.nodeTag(event.node) != .assign or tree.lastToken(event.node) >= copy_horizon or tree.firstToken(event.node) <= selected.binding.rhs_last) continue;
                    const pair = tree.nodeData(event.node).node_and_node;
                    var before = self.frame;
                    before.return_token = tree.firstToken(event.node);
                    const target = (try self.query.sourceCell(before, pair[0], null, depth + 1)) orelse {
                        self.complete = false;
                        continue;
                    };
                    if (!try self.query.cellsOverlap(target, selected)) continue;
                    if (!Query.sameCellRoot(target, selected) or !Query.pathContains(target.path, selected.path)) {
                        self.complete = false;
                        continue;
                    }
                    const tail = if (target.path.len == selected.path.len) "" else selected.path[target.path.len + @intFromBool(target.path.len != 0) ..];
                    try self.frozenCaptureSelection(pair[1], tail, path, mode, before.return_token, read_horizon, depth + 1);
                }
                return;
            },
            else => {
                self.complete = false;
                return;
            },
        }
    }

    fn unresolvedBorrow(self: *ExpressionWalk, reference: ?Ast.Node.Index, depth: u8) Error!void {
        self.complete = false;
        const saved = self.speculative;
        self.speculative = true;
        defer self.speculative = saved;
        const selected = if (reference) |node| try self.query.globalDeclaration(self.frame, node, depth + 1) else null;
        try self.replayEvents(selected, depth);
    }

    /// Stores that could have replaced an allocator header held in storage this
    /// invocation did not create, through a formal or an alias of one. Unlike
    /// `unresolvedBorrow` the call's result is understood, so only a store whose
    /// target cannot be resolved, or a call that may deposit pointers anywhere,
    /// makes the answer incomplete.
    fn providerStores(self: *ExpressionWalk, depth: u8) Error!void {
        try self.replayEvents(null, depth);
    }

    /// Every earlier event that could have stored one of this frame's addresses
    /// into storage reachable from elsewhere: an assignment to a formal's
    /// storage or to an unresolvable target stores its right-hand side, and a
    /// call that may deposit pointers stores any of its actuals.
    fn replayEvents(self: *ExpressionWalk, selected: ?Ast.Node.Index, depth: u8) Error!void {
        const saved_origin = self.derived_origin;
        self.derived_origin = true;
        defer self.derived_origin = saved_origin;
        const tree = self.cache.tree;
        for (self.events) |event| {
            try self.charge();
            const horizon = if (event.loop_start < self.load_token and event.loop_end >= self.load_token) event.loop_end + 1 else self.load_token;
            if (tree.lastToken(event.node) >= horizon) continue;
            const saved = self.frame;
            const saved_load = self.load_token;
            self.load_token = tree.firstToken(event.node);
            self.frame.return_token = self.load_token;
            defer {
                self.frame = saved;
                self.load_token = saved_load;
            }
            if (tree.nodeTag(event.node) == .assign) {
                const pair = tree.nodeData(event.node).node_and_node;
                if (selected) |declared| {
                    if (try self.query.globalDeclaration(self.frame, pair[0], depth + 1)) |target| {
                        if (target != declared) continue;
                    }
                }
                const cell = try self.query.sourceCell(self.frame, pair[0], null, depth + 1);
                if (cell == null) self.complete = false;
                if (cell == null or cell.?.binding.origin == .param) try self.borrow(pair[1], "", false, depth + 1);
            } else {
                var buffer: [2]Ast.Node.Index = undefined;
                if (TypeResolver.CallOperands.full(tree, &buffer, event.node)) |call| {
                    // A call that cannot store a pointer anywhere gave nothing
                    // an unknown result could have acquired from its arguments.
                    if (try self.query.eventCannotDeposit(self.frame, event.node, call, depth + 1)) continue;
                    self.complete = false;
                    try self.effectArguments(event.node, call, depth + 1);
                }
            }
        }
    }

    /// A header capture does not authenticate an incoming pointee. Accept a
    /// later payload only after a matching direct store in a block that
    /// necessarily executes that store before this read. Branch-only stores
    /// still contribute loans, but cannot close the incoming source channel.
    fn capturedStoreCoversRead(self: *ExpressionWalk, binding: *const bindings_mod.Binding, path: []const u8, horizon: Ast.TokenIndex) Error!bool {
        const tree = self.cache.tree;
        for (self.events) |event| {
            try self.charge();
            if (tree.nodeTag(event.node) != .assign or tree.lastToken(event.node) >= horizon) continue;
            const destination = tree.nodeData(event.node).node_and_node[0];
            const target = (try self.bindingPath(destination, binding)) orelse continue;
            if (!std.mem.eql(u8, target, path) or (target.len == 0 and tree.nodeTag(destination) == .identifier)) continue;
            for (tree.nodes.items(.tag), 0..) |tag, raw| {
                switch (tag) {
                    .block, .block_semicolon, .block_two, .block_two_semicolon => {},
                    else => continue,
                }
                try self.charge();
                const block: Ast.Node.Index = @enumFromInt(raw);
                if (tree.firstToken(block) > tree.firstToken(event.node) or tree.lastToken(block) < horizon) continue;
                var statements = Iterator.init(tree, block);
                var stored = false;
                while (statements.next(tree)) |statement| {
                    try self.charge();
                    if (statement == event.node) stored = true;
                    if (tree.firstToken(statement) <= horizon and tree.lastToken(statement) >= horizon)
                        if (stored) return true;
                }
            }
        }
        return false;
    }

    fn writtenBorrow(self: *ExpressionWalk, reference: Ast.Node.Index, binding: *const bindings_mod.Binding, use_token: Ast.TokenIndex, path: []const u8, dereference_root: bool, depth: u8) Error!void {
        try self.writtenEffects(reference, binding, use_token, path, depth + 1);
        const tree = self.cache.tree;
        for (self.events) |event| {
            try self.charge();
            if (tree.nodeTag(event.node) != .assign) continue;
            const pair = tree.nodeData(event.node).node_and_node;
            const start = if (binding.origin == .param) binding.name_token else binding.rhs_last;
            // This store has not completed while its own RHS is being read.
            const horizon = if (self.load_token != tree.firstToken(pair[1]) and event.loop_start < use_token and event.loop_end >= use_token) event.loop_end + 1 else use_token;
            if (tree.firstToken(event.node) <= start or tree.lastToken(event.node) >= horizon) continue;
            if (try self.bindingPath(pair[0], binding)) |target| {
                if (covered(self.excluded, target)) continue;
                const selected: ?[]const u8 = if (target.len == 0) path else if (path.len == 0 or std.mem.eql(u8, path, target)) "" else if (Query.pathContains(target, path)) path[target.len + 1 ..] else if (Query.pathContains(path, target)) "" else null;
                if (selected) |tail| {
                    const saved = self.excluded;
                    self.excluded = &.{};
                    defer self.excluded = saved;
                    const saved_load = self.load_token;
                    const saved_frame = self.frame;
                    self.load_token = tree.firstToken(pair[1]);
                    self.frame.return_token = self.load_token;
                    defer {
                        self.load_token = saved_load;
                        self.frame = saved_frame;
                    }
                    if (dereference_root and target.len == 0 and tree.nodeTag(pair[0]) == .identifier)
                        try self.dereferenceBorrow(pair[1], tail, depth + 1)
                    else
                        try self.borrow(pair[1], tail, false, depth + 1);
                }
            }
        }
    }

    /// Payload writes never establish the addressed outer array cell. Join
    /// every possible element, including syntactically later loop iterations.
    fn writtenElementBorrow(self: *ExpressionWalk, reference: Ast.Node.Index, binding: *const bindings_mod.Binding, use_token: Ast.TokenIndex, array_path: []const u8, path: []const u8, depth: u8) Error!void {
        try self.writtenEffects(reference, binding, use_token, array_path, depth + 1);
        const tree = self.cache.tree;
        for (self.events) |event| {
            try self.charge();
            if (tree.nodeTag(event.node) != .assign) continue;
            const pair = tree.nodeData(event.node).node_and_node;
            const start = if (binding.origin == .param) binding.name_token else binding.rhs_last;
            // Keep other loop writes, not the active RHS's own replacement.
            const horizon = if (self.load_token != tree.firstToken(pair[1]) and event.loop_start < use_token and event.loop_end >= use_token) event.loop_end + 1 else use_token;
            if (tree.firstToken(event.node) <= start or tree.lastToken(event.node) >= horizon) continue;
            const element = try self.elementTarget(pair[0], depth + 1);
            const target_node = if (element) |target| target.base else pair[0];
            if (try self.bindingPath(target_node, binding)) |target| {
                const selected: ?[]const u8 = if (target.len == 0) array_path else if (std.mem.eql(u8, array_path, target)) "" else if (Query.pathContains(target, array_path)) array_path[target.len + 1 ..] else if (Query.pathContains(array_path, target)) "" else null;
                if (selected) |tail| {
                    const saved = self.excluded;
                    self.excluded = &.{};
                    defer self.excluded = saved;
                    const saved_load = self.load_token;
                    const saved_frame = self.frame;
                    self.load_token = tree.firstToken(pair[1]);
                    self.frame.return_token = self.load_token;
                    defer {
                        self.load_token = saved_load;
                        self.frame = saved_frame;
                    }
                    if (element) |store| {
                        const selection = try self.join(tail, path);
                        const payload: ?[]const u8 = if (store.path.len == 0) selection else if (selection.len == 0 or std.mem.eql(u8, selection, store.path)) "" else if (Query.pathContains(store.path, selection)) selection[store.path.len + 1 ..] else if (Query.pathContains(selection, store.path)) "" else null;
                        if (payload) |selected_payload| try self.borrow(pair[1], selected_payload, false, depth + 1);
                    } else try self.elementBorrow(pair[1], tail, path, depth + 1);
                }
            }
        }
    }

    fn add(self: *ExpressionWalk, token: Ast.TokenIndex, origin: ExpressionLoan.Origin, scalar: bool) Error!void {
        try self.charge();
        const loan: ExpressionLoan = .{ .binding_token = token, .origin = origin, .derivation = if (self.derived_origin) .propagated else .direct_address, .scalar_cell = scalar, .proved = !self.speculative };
        if (origin == .retained_value) self.complete = false;
        for (self.loans.items) |*old| {
            if (old.binding_token != loan.binding_token or old.origin != loan.origin) continue;
            if (loan.derivation == .propagated) old.derivation = .propagated;
            old.scalar_cell = old.scalar_cell and loan.scalar_cell;
            old.proved = old.proved or loan.proved;
            return;
        }
        try self.loans.append(self.query.scratch.allocator(), loan);
    }

    const BorrowKind = enum { value, location, cell, dereference, element };

    /// One demand an `ExpressionWalk` is answering. A loop-carried cursor
    /// (`current = node.parent`, where `node` was read through `current`)
    /// makes a demand's answer depend on itself: the same node, selection and
    /// walk inputs return through the loop's own stores. Such a repeat adds
    /// nothing a frame still on the stack will not add when it finishes.
    const BorrowDemand = struct {
        kind: BorrowKind,
        node: Ast.Node.Index,
        path: []const u8,
        /// `elementBorrow`'s payload path; empty for every other kind.
        payload: []const u8,
        state: WalkState,
    };

    /// Register a demand, or cut it when the same demand is already being
    /// answered. "Same" is the node, the kind and every walk input, with
    /// selections that extend one another at a segment boundary counting as
    /// equal: a cursor rebound through a recursive type grows its selection
    /// (`next`, `next.next`, ...) on every trip around the loop, so exact
    /// equality would never fire. A cut answers incompletely and counts as a
    /// cycle prune. A registered demand must be released with `leaveDemand`.
    ///
    /// Unlike a `Query` cycle prune, a cut does not stop the enclosing
    /// `effect_walks`/`cleared_walks` attempts from being recorded. A walk
    /// only adds loans and clears completeness, and the frame the cut matched
    /// is still running: it adds everything the cut skipped when it finishes.
    /// The cut also cleared `complete` for the rest of the walk, so a replay
    /// can never turn the answer complete. Refusing to record those attempts
    /// would re-walk every simple path through a loop's events, which is
    /// exponential in their number.
    fn enterDemand(self: *ExpressionWalk, kind: BorrowKind, node: Ast.Node.Index, path: []const u8, payload: []const u8) Error!bool {
        const query = self.query;
        const entry = self.walkState();
        for (query.active_borrows.items) |active| {
            if (active.kind != kind or active.node != node or !Query.pathsNest(active.path, path) or
                !Query.pathsNest(active.payload, payload) or !active.state.matches(entry)) continue;
            query.prunes += 1;
            self.complete = false;
            return true;
        }
        try query.active_borrows.append(query.scratch.allocator(), .{ .kind = kind, .node = node, .path = path, .payload = payload, .state = entry });
        return false;
    }

    fn leaveDemand(self: *ExpressionWalk) void {
        self.query.active_borrows.items.len -= 1;
    }

    fn charge(self: *ExpressionWalk) Error!void {
        try self.query.charge();
    }

    fn join(self: *ExpressionWalk, first: []const u8, last: []const u8) error{OutOfMemory}![]const u8 {
        if (first.len == 0) return last;
        if (last.len == 0) return first;
        return std.fmt.allocPrint(self.query.scratch.allocator(), "{s}.{s}", .{ first, last });
    }

    fn defaultBorrow(self: *ExpressionWalk, field: Query.DefaultFieldSource, path: []const u8, element: bool, depth: u8) Error!void {
        if (field.source.frame.cache == self.cache) {
            if (element) return self.elementBorrow(field.source.node, path, "", depth + 1);
            return self.borrow(field.source.node, path, false, depth + 1);
        }
        // A foreign default is never decoded with this caller's token table.
        // Complete symbolic independence is useful; unresolved globals may
        // still have acquired this caller's storage through earlier effects.
        var output: Output = .{};
        try self.query.projectExpression(field.source.frame, field.source.node, path, .value, "", &output, depth + 1);
        if (!output.complete or output.items.items.len != 0 or output.allocations.items.len != 0)
            return self.unresolvedBorrow(null, depth + 1);
    }

    /// An empty path selects the whole value; otherwise it selects only the
    /// returned field. Location mode follows the cell addressed by a pointer,
    /// rather than confusing the array's by-value contents with its address.
    fn borrow(
        self: *ExpressionWalk,
        node: Ast.Node.Index,
        path: []const u8,
        location: bool,
        depth: u8,
    ) Error!void {
        try self.charge();
        if (depth >= depth_limit) return self.query.depthExhausted(depth);
        if (try self.enterDemand(if (location) .location else .value, node, path, "")) return;
        defer self.leaveDemand();
        const tree = self.cache.tree;
        if (tree.nodeTag(node) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "undefined")) {
            self.complete = false;
            return;
        }
        const saved_origin = self.derived_origin;
        defer self.derived_origin = saved_origin;
        if (!location and covered(self.excluded, path)) return;
        if (!location and path.len == 0) {
            if (try self.query.nodeType(self.frame, node)) |ty| {
                // Storage proof only: undefined/read diagnostics still run.
                if (try self.query.addressless(self.frame, node, ty, 0)) return;
            }
        }
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                const name = tree.tokenSlice(token);
                if (std.mem.eql(u8, name, "null") or std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false")) return;
                const binding = (try self.bindingAt(name, token)) orelse {
                    if (location and try self.query.globalCellAddress(self.frame, node)) return;
                    return self.unresolvedBorrow(node, depth + 1);
                };
                const use_token = if (self.payload_load) self.load_token else token;
                if (binding.origin == .param) {
                    // An external receiver can acquire this invocation's local
                    // storage through outward field stores before the call.
                    if (!location) {
                        try self.writtenBorrow(node, binding, use_token, path, false, depth + 1);
                    }
                    return;
                }
                if (binding.origin == .loop_capture) {
                    if (location) self.complete = false;
                    if (location) return self.frameCell(binding, node);
                    return self.captureBorrow(binding, path, .value, depth + 1);
                }
                // Location mode follows the local cell, not its initializer.
                // Do not turn a direct scalar address into a derived loan.
                // Unknown types retain the possible borrow; arrays retain
                // their backing-storage loan, including slice coercions.
                if (location) {
                    try self.frameCell(binding, node);
                    return;
                }
                if (self.retained) try self.add(binding.name_token, .retained_value, false);
                self.derived_origin = true;
                const initializer = self.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse {
                    self.complete = false;
                    return;
                };
                const saved = self.excluded;
                defer self.excluded = saved;
                if (!location and !binding.is_const) {
                    var cleared: std.ArrayList([]const u8) = .empty;
                    var poisoned = false;
                    try self.clearedFields(binding, use_token, &cleared, &poisoned, depth + 1);
                    if (!poisoned and cleared.items.len != 0) {
                        try cleared.appendSlice(self.query.scratch.allocator(), saved);
                        self.excluded = cleared.items;
                        if (covered(self.excluded, path)) return;
                    }
                    try self.writtenBorrow(node, binding, use_token, path, false, depth + 1);
                }
                const saved_load = self.payload_load;
                const saved_horizon = self.load_token;
                const saved_frame = self.frame;
                self.load_token = tree.firstToken(initializer);
                self.frame.return_token = self.load_token;
                defer self.frame = saved_frame;
                defer self.load_token = saved_horizon;
                self.payload_load = false;
                defer self.payload_load = saved_load;
                return self.borrow(initializer, path, location, depth + 1);
            },
            .address_of => {
                if (!location and path.len != 0) return self.dereferenceBorrow(node, path, depth + 1);
                const value = tree.nodeData(node).node;
                if (tree.nodeTag(value) == .identifier) {
                    const token = tree.nodeMainToken(value);
                    if (try self.bindingAt(tree.tokenSlice(token), token)) |binding| {
                        if (binding.origin == .param) return self.frameCell(binding, value);
                    }
                }
                return self.borrow(value, path, true, depth + 1);
            },
            .deref => {
                const pointer = tree.nodeData(node).node;
                self.derived_origin = true;
                if (location) return self.backingBorrow(pointer, path, depth + 1);
                return self.dereferenceBorrow(pointer, path, depth + 1);
            },
            .@"try" => return self.borrow(tree.nodeData(node).node, path, location, depth + 1),
            .grouped_expression, .unwrap_optional => return self.borrow(tree.nodeData(node).node_and_token[0], path, location, depth + 1),
            .field_access => {
                const access = tree.nodeData(node).node_and_token;
                self.derived_origin = true;
                if (location)
                    return self.cellBorrow(access[0], try self.join(tree.tokenSlice(access[1]), path), depth + 1);
                const selected = try self.join(tree.tokenSlice(access[1]), path);
                if (try self.query.nodeType(self.frame, access[0])) |ty| {
                    if (try self.query.pointerSize(ty) == .one)
                        return self.dereferenceBorrow(access[0], selected, depth + 1);
                    if (try self.query.pointerSize(ty) == .slice and std.mem.eql(u8, tree.tokenSlice(access[1]), "ptr"))
                        return self.borrow(access[0], path, false, depth + 1);
                } else self.complete = false;
                return self.borrow(access[0], selected, false, depth + 1);
            },
            .array_access => {
                const base = tree.nodeData(node).node_and_node[0];
                self.derived_origin = true;
                if (location) return self.backingBorrow(base, path, depth + 1);
                return self.elementBorrow(base, "", path, depth + 1);
            },
            .slice_open, .slice, .slice_sentinel => {
                const slice = tree.fullSlice(node).?;
                self.derived_origin = true;
                return self.backingBorrow(slice.ast.sliced, path, depth + 1);
            },
            .@"if", .if_simple => {
                self.derived_origin = true;
                const conditional = tree.fullIf(node).?;
                const known = try self.frame.resolution.boolValueOfNode(conditional.ast.cond_expr);
                if (known) |condition| {
                    if (condition) return self.borrow(conditional.ast.then_expr, path, location, depth + 1);
                    if (conditional.ast.else_expr.unwrap()) |other| return self.borrow(other, path, location, depth + 1);
                    self.complete = false;
                    return;
                }
                try self.borrow(conditional.ast.then_expr, path, location, depth + 1);
                if (conditional.ast.else_expr.unwrap()) |other|
                    return self.borrow(other, path, location, depth + 1);
                self.complete = false;
                return;
            },
            .@"catch", .@"orelse" => {
                self.derived_origin = true;
                const pair = tree.nodeData(node).node_and_node;
                try self.borrow(pair[0], path, location, depth + 1);
                return self.borrow(pair[1], path, location, depth + 1);
            },
            .block, .block_semicolon, .block_two, .block_two_semicolon => return self.blockBorrow(node, path, location, depth + 1),
            else => {},
        }

        var call_buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &call_buffer, node)) |call| {
            if (location) self.complete = false;
            self.derived_origin = true;
            const token = call.queryToken(tree, node);
            const actual = try self.cache.actualCallSummaryAt(token, self.frame.resolution);
            var at_call = self.frame;
            at_call.return_token = tree.firstToken(node);
            // An authenticated SDK allocation of address-free elements is memory
            // its provider owns. The only storage it can borrow is the provider's,
            // so earlier effects on unrelated arguments cannot reach the result.
            if (!location) {
                if (actual) |canonical| {
                    if (try self.allocationBorrow(canonical, node, depth)) return;
                }
            }
            // Demand the selected storage before scanning unrelated siblings.
            // Unknown selection or provider provenance still needs the full walk.
            if (path.len != 0) {
                if (actual) |canonical| {
                    // An authenticated SDK list constructor allocates its selected
                    // slice from an external allocator; no frame cell backs it.
                    const fresh = @import("fresh_storage.zig");
                    const range: FileCache.TokenRange = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) };
                    const constructor: fresh.FreshWalk = .{
                        .claim = .{ .first = range.first, .last = range.last },
                        .depth = 0,
                        .remaining = self.query.remaining,
                        .frame = self.frame.resolution,
                    };
                    if (try fresh.standardListConstructor(self.cache, range, constructor) and
                        try fresh.listConstructorProjection(self.cache, canonical, &.{path}, self.query.remaining)) return;
                    if (try self.query.sourceAt(at_call, node, path, depth + 1)) |source| {
                        if (source.cell) |cell| {
                            if (cell.frame.cache == self.cache and cell.frame.declaration == self.frame.declaration and
                                cell.frame.invocation == self.frame.invocation)
                            {
                                // An implicit address names the actual header,
                                // not the storage carried by its initializer.
                                try self.cellBorrow(cell.node, cell.path, depth + 1);
                                return;
                            }
                        }
                        if (source.frame.cache == self.cache and source.frame.declaration == self.frame.declaration and
                            source.frame.invocation == self.frame.invocation and source.node != node)
                        {
                            const saved_frame = self.frame;
                            const saved_excluded = self.excluded;
                            self.frame = source.frame;
                            self.excluded = &.{};
                            defer {
                                self.frame = saved_frame;
                                self.excluded = saved_excluded;
                            }
                            return self.borrow(source.node, "", location, depth + 1);
                        }
                    }
                    var selected: Output = .{};
                    try self.query.selectedCallStorage(at_call, node, canonical, path, &selected, depth + 1);
                    if (selected.complete and selected.items.items.len == 0) {
                        var independent = true;
                        const before = self.loans.items.len;
                        for (selected.allocations.items) |requirement| {
                            const source = requirement.source orelse {
                                independent = false;
                                continue;
                            };
                            if (source.frame.cache != self.cache or source.frame.declaration != self.frame.declaration) {
                                independent = false;
                                continue;
                            }
                            if (!try @import("fresh_storage.zig").allocatorOriginIsExternal(source.frame.cache, source.node, .{
                                .claim = .{ .first = tree.firstToken(source.node), .last = tree.lastToken(source.node) },
                                .depth = 0,
                                .remaining = self.query.remaining,
                                .frame = source.frame.resolution,
                            }, 0)) independent = false;
                            try self.borrow(source.node, "", false, depth + 1);
                        }
                        if (independent and self.complete and self.loans.items.len == before) return;
                    }
                }
            }
            const returned = if (actual) |canonical| try self.returnedWithProviders(canonical, at_call, depth) else ReturnedStorage{};
            var mapped_complete = (returned.complete or returned.direct_formal_load != null) and actual != null;
            var matched_load = false;
            if (actual) |canonical| {
                for (returned.alternatives) |alternative| {
                    try self.charge();
                    if (covered(self.excluded, alternative.result_path)) continue;
                    var selected_path = alternative.owner.path;
                    if (path.len != 0 and alternative.result_path.len != 0) {
                        if (std.mem.eql(u8, path, alternative.result_path)) {
                            // The exact returned borrow is selected.
                        } else if (std.mem.startsWith(u8, path, alternative.result_path) and
                            path.len > alternative.result_path.len and path[alternative.result_path.len] == '.')
                        {
                            selected_path = try self.join(selected_path, path[alternative.result_path.len + 1 ..]);
                        } else if (!(std.mem.startsWith(u8, alternative.result_path, path) and
                            alternative.result_path.len > path.len and alternative.result_path[path.len] == '.'))
                            continue;
                    } else if (path.len != 0) {
                        selected_path = try self.join(selected_path, path);
                    }
                    var argument_buffer: [2]Ast.Node.Index = undefined;
                    const mapped = (try mappedStorageAt(self.cache, canonical, alternative, &argument_buffer)) orelse {
                        mapped_complete = false;
                        continue;
                    };
                    const argument = mapped.node;
                    const saved = self.excluded;
                    self.excluded = &.{};
                    defer self.excluded = saved;
                    const saved_unknown = self.element_unknown;
                    self.element_unknown = false;
                    defer self.element_unknown = self.element_unknown or saved_unknown;
                    if (returned.direct_formal_load) |load| {
                        matched_load = true;
                        const saved_load = self.load_token;
                        self.load_token = tree.firstToken(node);
                        defer self.load_token = saved_load;
                        switch (load) {
                            .element => try self.elementBorrow(argument, "", selected_path, depth + 1),
                            .dereference => try self.dereferenceBorrow(argument, selected_path, depth + 1),
                        }
                        // The exact selector proves a negative only when the
                        // actual payload traversal handled every selected arm.
                        mapped_complete = mapped_complete and !self.element_unknown;
                    } else {
                        if (alternative.projection == .cell_address) {
                            if (alternative.storage == .inline_storage)
                                try self.cellBorrow(argument, selected_path, depth + 1)
                            else
                                try self.backingBorrow(argument, selected_path, depth + 1);
                        } else {
                            if (alternative.projection == .pointer_value and alternative.storage == .inline_storage and
                                alternative.owner.path.len == 0 and selected_path.len == 0)
                            {
                                if (try self.query.actualArgumentSource(at_call, canonical, alternative.owner.param, argument, null, depth + 1)) |source| {
                                    if (source.cell) |cell| {
                                        if (cell.frame.cache == self.cache and cell.frame.declaration == self.frame.declaration and
                                            cell.frame.invocation == self.frame.invocation)
                                        {
                                            try self.cellBorrow(cell.node, cell.path, depth + 1);
                                            continue;
                                        }
                                    }
                                }
                            }
                            // A slice of an inline array field points at that cell of
                            // the actual, not at a pointer value stored inside it.
                            if (alternative.projection == .pointer_value and alternative.storage == .inline_storage and
                                alternative.owner.path.len != 0)
                            {
                                try self.cellBorrow(argument, selected_path, depth + 1);
                                continue;
                            }
                            try self.borrow(argument, selected_path, false, depth + 1);
                        }
                    }
                }
                if (returned.direct_formal_load != null and !matched_load) {
                    var argument_buffer: [2]Ast.Node.Index = undefined;
                    if (returned.alternatives.len != 0) {
                        if (try mappedStorageAt(self.cache, canonical, returned.alternatives[0], &argument_buffer)) |mapped| {
                            const saved_load = self.load_token;
                            self.load_token = tree.firstToken(node);
                            defer self.load_token = saved_load;
                            switch (returned.direct_formal_load.?) {
                                .element => try self.elementBorrow(mapped.node, "", "", depth + 1),
                                .dereference => try self.dereferenceBorrow(mapped.node, "", depth + 1),
                            }
                        }
                    }
                    self.element_unknown = true;
                    self.complete = false;
                    return;
                }
            }
            if (mapped_complete) return;

            const saved_retained = self.retained;
            self.retained = true;
            defer self.retained = saved_retained;
            // Unknown is not a safety certificate. Keep known argument storage
            // unless the existing producer proves this call makes fresh storage.
            if (try @import("fresh_storage.zig").freshStorageAt(self.cache, .{
                .claim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) },
                .depth = 0,
                .remaining = self.query.remaining,
                .frame = self.frame.resolution,
            })) return;
            self.complete = false;
            const saved_speculative = self.speculative;
            self.speculative = true;
            defer self.speculative = saved_speculative;
            const saved = self.excluded;
            self.excluded = &.{};
            defer self.excluded = saved;
            // A selected formal certificate does not detach an actual from
            // storage already reachable through self. Check that channel first.
            if (actual) |canonical| {
                if (canonical.argument_offset == 1) {
                    var receiver_buffer: [2]Ast.Node.Index = undefined;
                    if (try canonical.callArgumentFor(self.cache, &receiver_buffer, 0)) |receiver| {
                        try self.receiverBorrow(at_call, actual, receiver, depth + 1);
                    }
                }
            }
            if ((actual == null or actual.?.argument_offset == null) and tree.nodeTag(call.ast.fn_expr) == .field_access) {
                const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
                try self.receiverBorrow(at_call, actual, receiver, depth + 1);
            }
            for (call.ast.params, 0..) |argument, index| {
                if (actual) |canonical| {
                    if (canonical.argument_offset) |offset| {
                        const parameter: u32 = @intCast(index + offset);
                        if (try self.query.formalBody(self.cache, canonical, parameter, depth + 1)) continue;
                    }
                }
                try self.borrow(argument, "", false, depth + 1);
            }
            // An SDK allocator accessor returns a header over its receiver alone;
            // the receiver's own contents and earlier effects were walked above.
            if (actual) |canonical| {
                if (try self.sdkAllocatorHeader(canonical)) return;
            }
            try self.unresolvedBorrow(null, depth + 1);
            return;
        }
        var struct_buffer: [2]Ast.Node.Index = undefined;
        if (try self.query.arrayLiteral(self.frame, node, &struct_buffer)) |literal| {
            if (!literal.complete or (location and literal.elements.len != 0)) self.complete = false;
            self.derived_origin = true;
            var element_path = path;
            if (!location and path.len != 0) {
                const actual = if (try self.query.nodeType(self.frame, node)) |value| try self.query.canonicalType(value) else null;
                if (actual != null and self.query.isTuple(actual.?)) {
                    // Unknown tuple selectors cannot erase component loans.
                    self.complete = false;
                    element_path = "";
                }
            }
            // The literal is a temporary: its elements are copied INTO it, so
            // even when its own cell is demanded they contribute their values.
            for (literal.elements) |element| try self.borrow(element, element_path, false, depth + 1);
            return;
        }
        if (tree.fullStructInit(&struct_buffer, node)) |literal| {
            if (location) self.complete = false;
            var selected = path.len == 0;
            self.derived_origin = true;
            for (literal.ast.fields) |field| {
                try self.charge();
                const first = tree.firstToken(field);
                const tags = tree.tokens.items(.tag);
                if (first < 3 or tags[first - 1] != .equal or tags[first - 2] != .identifier or tags[first - 3] != .period) {
                    self.complete = false;
                    try self.borrow(field, "", false, depth + 1);
                    continue;
                }
                const name = tree.tokenSlice(first - 2);
                const tail = if (std.mem.indexOfScalar(u8, path, '.')) |dot| path[dot + 1 ..] else "";
                const head = if (std.mem.indexOfScalar(u8, path, '.')) |dot| path[0..dot] else path;
                if (path.len != 0 and !std.mem.eql(u8, head, name)) continue;
                selected = true;
                if (covered(self.excluded, name)) continue;
                const saved = self.excluded;
                var nested: std.ArrayList([]const u8) = .empty;
                for (saved) |excluded| {
                    if (std.mem.startsWith(u8, excluded, name) and excluded.len > name.len and excluded[name.len] == '.')
                        try nested.append(self.query.scratch.allocator(), excluded[name.len + 1 ..]);
                }
                self.excluded = nested.items;
                defer self.excluded = saved;
                try self.borrow(field, tail, false, depth + 1);
            }
            const defaults = try self.query.literalDefaults(self.frame, node, literal.ast.fields, depth + 1);
            if (!defaults.complete) self.complete = false;
            const dot = std.mem.indexOfScalar(u8, path, '.');
            const head = if (dot) |at| path[0..at] else path;
            const tail = if (dot) |at| path[at + 1 ..] else "";
            for (defaults.fields.items) |field| {
                if (path.len != 0 and !std.mem.eql(u8, head, field.name)) continue;
                selected = true;
                if (!covered(self.excluded, field.name)) try self.defaultBorrow(field, tail, false, depth + 1);
            }
            if (!selected) self.complete = false;
            return;
        }
        switch (tree.nodeTag(node)) {
            .number_literal, .char_literal, .string_literal, .multiline_string_literal, .enum_literal, .error_value => {
                if (path.len != 0) self.complete = false;
                return;
            },
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "@tagName")) return;
                if (try self.castOperand(node)) |operand| {
                    self.derived_origin = true;
                    return self.borrow(operand, path, location, depth + 1);
                }
            },
            else => {},
        }
        self.complete = false;
        self.derived_origin = true;
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| try self.borrow(child, path, location, depth + 1);
    }

    /// Cancel one actual address layer for a proven callee cell load. Opaque
    /// expressions still retain their possible argument storage.
    fn dereferenceBorrow(
        self: *ExpressionWalk,
        node: Ast.Node.Index,
        path: []const u8,
        depth: u8,
    ) Error!void {
        try self.charge();
        if (depth >= depth_limit) return self.query.depthExhausted(depth);
        if (try self.enterDemand(.dereference, node, path, "")) return;
        defer self.leaveDemand();
        const tree = self.cache.tree;
        const saved_origin = self.derived_origin;
        self.derived_origin = true;
        defer self.derived_origin = saved_origin;
        if (try self.castOperand(node)) |operand| {
            if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@ptrCast") and
                (try self.query.sourceCell(self.frame, node, null, depth + 1)) == null)
            {
                self.complete = false;
                return;
            }
            return self.dereferenceBorrow(operand, path, depth + 1);
        }
        var call_buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &call_buffer, node)) |call| {
            try self.charge();
            const actual = try self.cache.actualCallSummaryAt(call.queryToken(tree, node), self.frame.resolution);
            if (actual) |canonical| {
                if (try self.query.pointerReturnSource(self.frame, node, call, canonical, path, depth + 1)) |source|
                    return self.dereferenceBorrow(source.node, path, depth + 1);
            }
            self.complete = false;
            return self.borrow(node, path, false, depth + 1);
        }
        switch (tree.nodeTag(node)) {
            .address_of => {
                const saved = self.payload_load;
                self.payload_load = true;
                defer self.payload_load = saved;
                return self.borrow(tree.nodeData(node).node, path, false, depth + 1);
            },
            .grouped_expression, .unwrap_optional => return self.dereferenceBorrow(tree.nodeData(node).node_and_token[0], path, depth + 1),
            .@"try" => return self.dereferenceBorrow(tree.nodeData(node).node, path, depth + 1),
            .identifier => {
                const token = tree.nodeMainToken(node);
                const name = tree.tokenSlice(token);
                if (std.mem.eql(u8, name, "null") or std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false")) return;
                const binding = (try self.bindingAt(name, token)) orelse {
                    if (try self.query.sourceAt(self.frame, node, "", depth + 1)) |source| {
                        if (source.frame.cache == self.cache and source.frame.declaration == self.frame.declaration and source.node != node)
                            return self.dereferenceBorrow(source.node, path, depth + 1);
                    }
                    // No authenticated pointee: header declaration identity
                    // cannot exclude any storage reached by this load.
                    self.complete = false;
                    return;
                };
                if (binding.origin == .param) {
                    if (self.capture_source and !try self.capturedStoreCoversRead(binding, path, @max(token, self.load_token)))
                        self.complete = false;
                    try self.writtenBorrow(node, binding, @max(token, self.load_token), path, true, depth + 1);
                    return;
                }
                if (binding.origin == .loop_capture) return self.captureBorrow(binding, path, .dereference, depth + 1);
                try self.writtenBorrow(node, binding, self.load_token, path, true, depth + 1);
                const initializer = self.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse {
                    self.complete = false;
                    return;
                };
                return self.dereferenceBorrow(initializer, path, depth + 1);
            },
            .@"if", .if_simple => {
                const conditional = tree.fullIf(node).?;
                const known = try self.frame.resolution.boolValueOfNode(conditional.ast.cond_expr);
                if (known) |condition| {
                    if (condition) return self.dereferenceBorrow(conditional.ast.then_expr, path, depth + 1);
                    if (conditional.ast.else_expr.unwrap()) |other| return self.dereferenceBorrow(other, path, depth + 1);
                    self.complete = false;
                    return;
                }
                try self.dereferenceBorrow(conditional.ast.then_expr, path, depth + 1);
                if (conditional.ast.else_expr.unwrap()) |other|
                    return self.dereferenceBorrow(other, path, depth + 1);
                self.complete = false;
                return;
            },
            .@"catch", .@"orelse" => {
                const pair = tree.nodeData(node).node_and_node;
                try self.dereferenceBorrow(pair[0], path, depth + 1);
                return self.dereferenceBorrow(pair[1], path, depth + 1);
            },
            else => return self.borrow(node, path, false, depth + 1),
        }
    }

    /// Element reads copy payloads, not cell addresses. An outer slice borrowing
    /// an array does not establish a borrow for a pointer stored in that array.
    fn elementBorrow(
        self: *ExpressionWalk,
        node: Ast.Node.Index,
        array_path: []const u8,
        path: []const u8,
        depth: u8,
    ) Error!void {
        try self.charge();
        if (depth >= depth_limit) return self.query.depthExhausted(depth);
        if (try self.enterDemand(.element, node, path, array_path)) return;
        defer self.leaveDemand();
        const tree = self.cache.tree;
        const saved_origin = self.derived_origin;
        self.derived_origin = true;
        defer self.derived_origin = saved_origin;
        if (try self.castOperand(node)) |operand| {
            if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@bitCast"))
                return self.borrow(operand, try self.join(array_path, path), false, depth + 1);
            if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@ptrCast") and
                (try self.query.sourceCell(self.frame, node, null, depth + 1)) == null)
            {
                self.complete = false;
                return;
            }
            return self.elementBorrow(operand, array_path, path, depth + 1);
        }
        const node_type = if (try self.query.nodeType(self.frame, node)) |ty| try self.query.canonicalType(ty) else null;
        if (node_type) |ty| {
            if (try self.query.pointerSize(ty) == .one) {
                const child = if (self.query.resolver.childType(ty)) |pointee| try self.query.canonicalType(pointee) else null;
                if (child) |pointee| {
                    if (self.query.resolver.typeTag(pointee)) |tag| {
                        if (tag != .array and tag != .@"struct")
                            return self.dereferenceBorrow(node, try self.join(array_path, path), depth + 1);
                    } else self.complete = false;
                } else self.complete = false;
            }
        } else self.complete = false;
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                const name = tree.tokenSlice(token);
                if (std.mem.eql(u8, name, "null") or std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false")) return;
                const binding = (try self.bindingAt(name, token)) orelse {
                    if (try self.query.sourceAt(self.frame, node, "", depth + 1)) |source| {
                        if (source.frame.cache == self.cache and source.frame.declaration == self.frame.declaration and source.node != node)
                            return self.elementBorrow(source.node, array_path, path, depth + 1);
                    }
                    self.complete = false;
                    return;
                };
                if (binding.origin == .param) {
                    // A slice/header formal is not proof of its element
                    // payload, even when the capture copied that header.
                    if (self.capture_source) self.complete = false;
                    try self.writtenElementBorrow(node, binding, @max(token, self.load_token), array_path, path, depth + 1);
                    return;
                }
                if (binding.origin == .loop_capture) return self.captureBorrow(binding, try self.join(array_path, path), .element, depth + 1);
                const initializer = self.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse {
                    self.complete = false;
                    return;
                };
                try self.writtenElementBorrow(node, binding, self.load_token, array_path, path, depth + 1);
                const saved_token = self.load_token;
                defer self.load_token = saved_token;
                // An array/record identifier copies its contents. A pointer or
                // slice identifier keeps referring to the original payload.
                if (node_type) |ty| {
                    if (try self.query.pointerSize(ty) == null)
                        self.load_token = tree.firstToken(initializer);
                }
                return self.elementBorrow(initializer, array_path, path, depth + 1);
            },
            .field_access => {
                const access = tree.nodeData(node).node_and_token;
                return self.elementBorrow(access[0], try self.join(tree.tokenSlice(access[1]), array_path), path, depth + 1);
            },
            .address_of, .deref, .@"try" => return self.elementBorrow(tree.nodeData(node).node, array_path, path, depth + 1),
            .grouped_expression, .unwrap_optional => return self.elementBorrow(tree.nodeData(node).node_and_token[0], array_path, path, depth + 1),
            .slice_open, .slice, .slice_sentinel => return self.elementBorrow(tree.fullSlice(node).?.ast.sliced, array_path, path, depth + 1),
            .@"if", .if_simple => {
                const conditional = tree.fullIf(node).?;
                const known = try self.frame.resolution.boolValueOfNode(conditional.ast.cond_expr);
                if (known) |condition| {
                    if (condition) return self.elementBorrow(conditional.ast.then_expr, array_path, path, depth + 1);
                    if (conditional.ast.else_expr.unwrap()) |other| return self.elementBorrow(other, array_path, path, depth + 1);
                    self.complete = false;
                    return;
                }
                try self.elementBorrow(conditional.ast.then_expr, array_path, path, depth + 1);
                if (conditional.ast.else_expr.unwrap()) |other|
                    return self.elementBorrow(other, array_path, path, depth + 1);
                self.complete = false;
                return;
            },
            .@"catch", .@"orelse" => {
                const pair = tree.nodeData(node).node_and_node;
                try self.elementBorrow(pair[0], array_path, path, depth + 1);
                return self.elementBorrow(pair[1], array_path, path, depth + 1);
            },
            else => {},
        }
        var struct_buffer: [2]Ast.Node.Index = undefined;
        if (try self.query.arrayLiteral(self.frame, node, &struct_buffer)) |literal| {
            if (!literal.complete) self.complete = false;
            const selected = try self.join(array_path, path);
            for (literal.elements) |element| try self.capturedElement(element, selected, depth + 1);
            return;
        }
        if (tree.fullStructInit(&struct_buffer, node)) |literal| {
            const dot = std.mem.indexOfScalar(u8, array_path, '.');
            const head = if (dot) |at| array_path[0..at] else array_path;
            const tail = if (dot) |at| array_path[at + 1 ..] else "";
            var selected_field = array_path.len == 0;
            for (literal.ast.fields) |field| {
                try self.charge();
                const first = tree.firstToken(field);
                const tags = tree.tokens.items(.tag);
                if (first < 3 or tags[first - 1] != .equal or tags[first - 2] != .identifier or tags[first - 3] != .period) {
                    self.complete = false;
                    try self.borrow(field, "", false, depth + 1);
                    continue;
                }
                const name = tree.tokenSlice(first - 2);
                if (array_path.len != 0 and !std.mem.eql(u8, head, name)) continue;
                selected_field = true;
                try self.elementBorrow(field, tail, path, depth + 1);
            }
            const defaults = try self.query.literalDefaults(self.frame, node, literal.ast.fields, depth + 1);
            if (!defaults.complete) self.complete = false;
            for (defaults.fields.items) |field| {
                if (array_path.len != 0 and !std.mem.eql(u8, head, field.name)) continue;
                selected_field = true;
                if (field.source.frame.cache == self.cache)
                    try self.elementBorrow(field.source.node, tail, path, depth + 1)
                else
                    try self.defaultBorrow(field, try self.join(tail, path), true, depth + 1);
            }
            if (!selected_field) self.complete = false;
            return;
        }
        var call_buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &call_buffer, node)) |call| {
            const token = call.queryToken(tree, node);
            const actual = try self.cache.actualCallSummaryAt(token, self.frame.resolution);
            var at_call = self.frame;
            at_call.return_token = tree.firstToken(node);
            if (actual) |canonical| {
                if (node_type) |ty| {
                    if ((try self.query.pointerSize(ty)) != null) {
                        if (try self.query.pointerReturnSource(at_call, node, call, canonical, array_path, depth + 1)) |source|
                            return self.elementBorrow(source.node, array_path, path, depth + 1);
                    }
                }
            }
            const returned = if (actual) |canonical| try self.returnedWithProviders(canonical, at_call, depth) else ReturnedStorage{};
            const selected = try self.join(array_path, path);
            const copied_array = if (node_type) |ty| self.query.resolver.typeTag(ty) == .array else false;
            // A direct formal slice loan proves which payload is copied even
            // when the slice's reachable pointee storage is not complete.
            // This certificate does not apply to the slice's outer address.
            var mapped_complete = (returned.complete or returned.direct_formal_loan) and actual != null;
            if (actual) |canonical| {
                for (returned.alternatives) |alternative| {
                    try self.charge();
                    if (covered(self.excluded, alternative.result_path)) continue;
                    var owner_path = alternative.owner.path;
                    if (selected.len != 0 and alternative.result_path.len != 0) {
                        if (std.mem.eql(u8, selected, alternative.result_path)) {
                            // This field carries the selected element payload.
                        } else if (std.mem.startsWith(u8, selected, alternative.result_path) and
                            selected.len > alternative.result_path.len and selected[alternative.result_path.len] == '.')
                        {
                            owner_path = try self.join(owner_path, selected[alternative.result_path.len + 1 ..]);
                        } else if (!(std.mem.startsWith(u8, alternative.result_path, selected) and
                            alternative.result_path.len > selected.len and alternative.result_path[selected.len] == '.'))
                            continue;
                    } else if (selected.len != 0) {
                        owner_path = try self.join(owner_path, selected);
                    }
                    var argument_buffer: [2]Ast.Node.Index = undefined;
                    const mapped = (try mappedStorageAt(self.cache, canonical, alternative, &argument_buffer)) orelse {
                        mapped_complete = false;
                        continue;
                    };
                    const argument = mapped.node;
                    const saved = self.excluded;
                    self.excluded = &.{};
                    defer self.excluded = saved;
                    if (alternative.projection == .cell_address) {
                        if (alternative.storage == .inline_storage)
                            try self.cellBorrow(argument, owner_path, depth + 1)
                        else
                            try self.backingBorrow(argument, owner_path, depth + 1);
                    } else if (!returned.direct_formal_loan and copied_array and
                        (alternative.storage == .backing_storage or
                            (alternative.projection == .pointer_value and alternative.storage == .inline_storage)))
                    {
                        // A by-value array carries an inline formal pointer,
                        // not a load through it. A pointer-to-array result still
                        // selects its pointee payload, not the outer array cell.
                        try self.borrow(argument, owner_path, false, depth + 1);
                    } else {
                        try self.elementBorrow(argument, owner_path, "", depth + 1);
                    }
                }
            }
            if (mapped_complete) return;
            if (try @import("fresh_storage.zig").freshStorageAt(self.cache, .{
                .claim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) },
                .depth = 0,
                .remaining = self.query.remaining,
                .frame = self.frame.resolution,
            })) return;
            self.complete = false;
            if (node_type) |ty| {
                // An unknown scalar array child is still unknown, but cannot
                // carry the physical argument cell as its storage origin.
                if (self.query.resolver.typeTag(ty) == .array) {
                    if (self.query.resolver.childType(ty)) |child| {
                        if (path.len == 0 and array_path.len == 0 and try self.query.addressFree(child, 0)) {
                            self.element_unknown = true;
                            return;
                        }
                    }
                }
            }
            const saved = self.excluded;
            self.excluded = &.{};
            defer self.excluded = saved;
            const saved_retained = self.retained;
            self.retained = true;
            defer self.retained = saved_retained;
            if (actual) |canonical| {
                if (canonical.argument_offset == 1) {
                    var argument_buffer: [2]Ast.Node.Index = undefined;
                    if (try canonical.callArgumentFor(self.cache, &argument_buffer, 0)) |receiver| {
                        try self.borrow(receiver, "", false, depth + 1);
                    }
                }
            }
            if ((actual == null or actual.?.argument_offset == null) and tree.nodeTag(call.ast.fn_expr) == .field_access) {
                const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
                try self.borrow(receiver, "", false, depth + 1);
            }
            for (call.ast.params, 0..) |argument, index| {
                if (actual) |canonical| {
                    if (canonical.argument_offset) |offset| {
                        const parameter: u32 = @intCast(index + offset);
                        if (try self.query.formalBody(self.cache, canonical, parameter, depth + 1)) continue;
                    }
                }
                // An unknown result may retain any actual argument storage,
                // not only payloads with the same shape as the selected field.
                try self.borrow(argument, "", false, depth + 1);
            }
        }
        self.element_unknown = true;
        self.complete = false;
        return;
    }
};

const Mode = enum { value, location, coordinate, address_bits };
const Output = struct {
    complete: bool = true,
    /// An enclosing scan already holds alternatives this one cannot see.
    seeded: bool = false,
    items: std.ArrayListUnmanaged(Alternative) = .empty,
    allocations: std.ArrayListUnmanaged(AllocationRequirement) = .empty,
};
const Frame = struct {
    cache: *FileCache,
    declaration: Ast.Node.Index,
    body: Ast.Node.Index,
    // Borrow immutable item/arena storage, not a relocatable cache-map slot.
    bindings: bindings_mod.LocalBindings,
    resolution: TypeResolver.ResolutionFrame,
    mutations: []const Ast.Node.Index = &.{},
    mutations_ordered: bool = false,
    caught_errors: []const Ast.Node.Index = &.{},
    return_token: Ast.TokenIndex = 0,
    invocation: ?*const Invocation = null,
    projected_return: ?ProjectedReturn = null,
    domain: Domain = .normal,
    source_return: ?*SourceReturn = null,
    mutations_complete: bool = true,
    // Unbound declaration summaries preserve caller-supplied scalar bits.
    // A concrete caller's incoming bits do not borrow its own frame cells.
    symbolic: bool = false,
};

// Invocation bindings and source locations are query-local. They never enter
// the declaration memo: an allocator's actual origin belongs to its caller.
const Invocation = struct { caller: Frame, actual: FileCache.ActualCallSummary };
const Source = struct { frame: Frame, node: Ast.Node.Index, cell: ?SourceCell = null };

// Structural frame identity for memo keys. Frames are rebuilt per query, so
// pointer identity would never repeat; everything an answer can read is
// compared instead. Invocation chains bind formals to actuals and compare
// recursively. A frame bound to a projected return compares that selector.
fn sameType(a: ?TypeResolver.ActualType, b: ?TypeResolver.ActualType) bool {
    return if (a) |left| if (b) |right| left.eql(right) else false else b == null;
}

fn sameResolution(a: TypeResolver.ResolutionFrame, b: TypeResolver.ResolutionFrame) bool {
    return a.resolver == b.resolver and a.handle.eql(b.handle) and
        sameType(a.actual_type, b.actual_type) and sameType(a.container_type, b.container_type);
}

fn sameFrame(a: Frame, b: Frame) bool {
    if (a.cache != b.cache or a.declaration != b.declaration or a.body != b.body or
        a.return_token != b.return_token or a.domain != b.domain or a.symbolic != b.symbolic or
        a.source_return != b.source_return or a.mutations_complete != b.mutations_complete or
        a.mutations.ptr != b.mutations.ptr or a.mutations.len != b.mutations.len or
        a.caught_errors.ptr != b.caught_errors.ptr or a.caught_errors.len != b.caught_errors.len or
        !sameResolution(a.resolution, b.resolution)) return false;
    if (a.projected_return) |left| {
        const right = b.projected_return orelse return false;
        if (left.mode != right.mode or !std.mem.eql(u8, left.path, right.path) or
            !std.mem.eql(u8, left.result_path, right.result_path)) return false;
    } else if (b.projected_return != null) return false;
    return sameInvocation(a.invocation, b.invocation);
}

fn sameInvocation(a: ?*const Invocation, b: ?*const Invocation) bool {
    if (a == b) return true;
    const left = a orelse return false;
    const right = b orelse return false;
    return sameActual(left.actual, right.actual) and sameFrame(left.caller, right.caller);
}

fn sameActual(a: FileCache.ActualCallSummary, b: FileCache.ActualCallSummary) bool {
    const left = a.callee;
    const right = b.callee;
    if (left.call_node != right.call_node or left.tree != right.tree or left.fn_token != right.fn_token or
        left.declaration != right.declaration or !left.handle.eql(right.handle) or
        a.argument_offset != b.argument_offset or
        left.reference.fn_token != right.reference.fn_token or left.reference.tree != right.reference.tree or
        !left.reference.actual_type.eql(right.reference.actual_type)) return false;
    if (left.caller_frame) |frame| {
        return if (right.caller_frame) |other| sameResolution(frame, other) else false;
    }
    return right.caller_frame == null;
}
const SourceReturn = struct { source: ?Source = null };
const ProjectedReturn = struct { path: []const u8, mode: Mode, result_path: []const u8 };
const SourceCell = struct {
    frame: Frame,
    binding: *const bindings_mod.Binding,
    node: Ast.Node.Index,
    path: []const u8,
};
const EffectDemand = struct {
    function: Key,
    cell: SourceCell,
    horizon: Ast.TokenIndex,
    domain: Domain,
};
// A cycle-free call-effect scan for one demanded cell, reusable verbatim
// where frame, call, cell, domain and result coordinate agree.
const CallEffectCertificate = struct {
    frame: Frame,
    node: Ast.Node.Index,
    cell: SourceCell,
    domain: Domain,
    result_path: []const u8,
    selected_formal: ?u32,
    seeded: bool,
    complete: bool,
    items: []const Alternative,
    allocations: []const AllocationRequirement,
    copies: []const CopiedPayload,
};

const CopiedPayload = struct {
    frame: Frame,
    cell: SourceCell,
    source: Source,
    path: []const u8 = "",
    element: bool = true,
};
const EffectCertificate = struct {
    frame: Frame,
    cell: SourceCell,
    horizon: Ast.TokenIndex,
    domain: Domain,
    result_path: []const u8,
    selected_formal: ?u32,
    seeded: bool,
    complete: bool,
    items: []const Alternative,
    allocations: []const AllocationRequirement,
    writes: []const SourceCell,
    copies: []const CopiedPayload,
};

const Query = struct {
    root: *FileCache,
    state: *State,
    resolver: *TypeResolver,
    remaining: *u32,
    scratch: *std.heap.ArenaAllocator,
    memo: *Memo,
    entry_tree: *const Ast,
    entry_token: Ast.TokenIndex,
    selected_formal: ?u32 = null,
    active_effects: std.ArrayListUnmanaged(EffectDemand) = .empty,
    // Source locations can depend on themselves through earlier aliased
    // stores (for example, hash-map header metadata). Cut that dependency
    // before it repeats every path to the depth cap.
    active_sources: std.ArrayListUnmanaged(SourceDemand) = .empty,
    active_scalar_cells: std.ArrayListUnmanaged(ScalarDemand) = .empty,
    copied_payloads: std.ArrayListUnmanaged(CopiedPayload) = .empty,
    /// ExpressionWalk demands being answered, outermost first.
    active_borrows: std.ArrayListUnmanaged(ExpressionWalk.BorrowDemand) = .empty,
    call_effect_certificates: std.AutoArrayHashMapUnmanaged(Ast.Node.Index, std.ArrayListUnmanaged(CallEffectCertificate)) = .empty,
    effect_certificates: std.AutoArrayHashMapUnmanaged(Ast.Node.Index, std.ArrayListUnmanaged(EffectCertificate)) = .empty,
    // Counts abandoned cycles; a scan that abandoned none is context-free.
    prunes: u32 = 0,
    // Counts reads of `written_cells`. An answer that never read it is
    // independent of which cells earlier scans wrote.
    written_reads: u32 = 0,
    // Counts depth cut-offs. A cut-off answer is shallower than the question
    // asked, so it is never published to a memo; see `Attempt`.
    cutoffs: u32 = 0,
    /// `depositFree` walks being answered, outermost first, and the number of
    /// times a walk closed on one of them.
    deposit_open: std.ArrayListUnmanaged(TypeResolver.ActualType) = .empty,
    deposit_cycles: u32 = 0,
    // Lowest `active_effects` index a cycle prune has matched since the
    // enclosing attempt began; zero when the cycle lies outside the stack.
    prune_floor: usize = no_prune,
    // A source cycle can be memoized only by an attempt enclosing its root.
    source_prune_floor: usize = no_prune,
    scalar_prune_floor: usize = no_prune,
    written_cells: std.ArrayListUnmanaged(SourceCell) = .empty,
    source_events: ?*std.ArrayListUnmanaged(SourceEvent) = null,
    source_direct: bool = true,
    source_loop_start: Ast.TokenIndex = 0,
    source_loop_end: Ast.TokenIndex = 0,
    source_domain: Domain = .normal,
    mutation_errdefer: bool = false,
    mutation_ordered: bool = true,
    const SourceDemand = struct {
        frame: Frame,
        node: Ast.Node.Index,
        path: []const u8,
        selected_formal: ?u32,
    };
    const ScalarDemand = struct {
        frame: Frame,
        reader: ?Frame,
        binding_token: Ast.TokenIndex,
        path: []const u8,
        selected_formal: ?u32,
    };

    /// One computation that may be published to a memo. It qualifies only if
    /// it met no depth cut-off and abandoned no cycle through a frame older
    /// than itself: a cycle closed entirely inside the computation is its own
    /// deterministic outcome, while one through an outer frame answers for
    /// that caller's stack alone.
    const Attempt = struct { cutoffs: u32, floor: usize, start: usize, source_floor: usize, source_start: usize, scalar_floor: usize, scalar_start: usize };

    fn beginAttempt(self: *Query) Attempt {
        const attempt: Attempt = .{
            .cutoffs = self.cutoffs,
            .floor = self.prune_floor,
            .start = self.active_effects.items.len,
            .source_floor = self.source_prune_floor,
            .source_start = self.active_sources.items.len,
            .scalar_floor = self.scalar_prune_floor,
            .scalar_start = self.active_scalar_cells.items.len,
        };
        self.prune_floor = no_prune;
        self.source_prune_floor = no_prune;
        self.scalar_prune_floor = no_prune;
        return attempt;
    }

    /// True when the finished computation may be published. Prunes still
    /// count against every enclosing attempt.
    fn endAttempt(self: *Query, attempt: Attempt) bool {
        const clean = self.cutoffs == attempt.cutoffs and self.prune_floor >= attempt.start and
            self.source_prune_floor >= attempt.source_start and self.scalar_prune_floor >= attempt.scalar_start;
        self.prune_floor = @min(attempt.floor, self.prune_floor);
        self.source_prune_floor = @min(attempt.source_floor, self.source_prune_floor);
        self.scalar_prune_floor = @min(attempt.scalar_floor, self.scalar_prune_floor);
        return clean;
    }

    /// Index a table once, then charge only same-spelling candidates. The
    /// scope and declaration-token rules are exactly `LocalBindings.findAt`;
    /// an interrupted index is never published.
    fn lookupBinding(self: *Query, bindings: bindings_mod.LocalBindings, name: []const u8, token: Ast.TokenIndex) Error!?*const bindings_mod.Binding {
        const key: BindingLookup = .{ .table = @intFromPtr(bindings.items.ptr), .name = @intFromPtr(name.ptr), .name_len = name.len, .token = token };
        if (self.memo.binding_lookups.get(key)) |known| {
            try self.charge();
            return known;
        }
        var index = self.memo.binding_indexes.get(key.table);
        if (index == null) {
            var built: BindingIndex = .empty;
            for (bindings.items) |*binding| {
                try self.charge();
                const entry = try built.getOrPut(self.scratch.allocator(), binding.name);
                if (!entry.found_existing) entry.value_ptr.* = .empty;
                try entry.value_ptr.append(self.scratch.allocator(), binding);
            }
            try self.memo.binding_indexes.put(self.scratch.allocator(), key.table, built);
            index = built;
        }
        var found: ?*const bindings_mod.Binding = null;
        if (index.?.get(name)) |candidates| {
            for (candidates.items) |binding| {
                try self.charge();
                if (binding.name_token > token or token < binding.scope_open or token > binding.scope_close) continue;
                if (found == null or binding.name_token > found.?.name_token) found = binding;
            }
        }
        try self.memo.binding_lookups.put(self.scratch.allocator(), key, found);
        return found;
    }

    fn charge(self: *Query) Error!void {
        if (self.remaining.* == 0) {
            return self.exhausted(.return_storage_work, call_summary.actual_query_work_limit, call_summary.actual_query_work_limit);
        }
        self.remaining.* -= 1;
    }

    /// A frame-depth cap tripped. The walk gives up, so the CLI must be able
    /// to say which cap it was and where the query started.
    fn depthExhausted(self: *Query, depth: u32) budget.BudgetError {
        // The bound is checked before use, so a tripped bound reached itself;
        // a frame that skipped past it is still reported at the bound.
        return self.exhausted(.return_storage_depth, depth_limit, @min(depth, depth_limit));
    }

    /// Record `limit` against the query's entry site, then return the error
    /// every caller already propagates.
    fn exhausted(self: *Query, limit: budget.Limit, cap: u32, reached: u32) budget.BudgetError {
        const pos = budget.lineCol(self.entry_tree.source, self.entry_tree.tokenStart(self.entry_token));
        var name: budget.NameBuf = .{};
        if (tokens.enclosingFnDecl(self.entry_tree, self.entry_token)) |decl| {
            var buffer: [1]Ast.Node.Index = undefined;
            if (tokens.fnProto(self.entry_tree, &buffer, decl)) |proto| {
                if (proto.name_token) |t| name.set(self.entry_tree.tokenSlice(t));
            }
        }
        return budget.fail(.{
            .limit = limit,
            .limit_value = cap,
            .reached = reached,
            .byte = self.entry_tree.tokenStart(self.entry_token),
            .line = pos.line,
            .column = pos.column,
            .function = name,
        });
    }

    fn formalBody(self: *Query, caller: *FileCache, actual: FileCache.ActualCallSummary, parameter: u32, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return false;
        }
        const callee = actual.callee;
        const key: FormalKey = .{
            .function = .{
                .declaration = .{ .tree = callee.tree, .module = callee.handle.module, .declaration = callee.declaration },
                .context = callee.reference.actual_type,
            },
            .parameter = parameter,
        };
        if (self.state.formal_certificates.contains(key)) return true;
        if (self.memo.formal_failures.get(key)) |failed| {
            for (failed.items) |known| {
                try self.charge();
                if (sameActual(known, actual)) return false;
            }
        }
        if (self.state.formal_active.contains(key)) {
            self.prunes += 1;
            self.prune_floor = 0;
            return false;
        }
        try self.state.formal_active.put(self.root.gpa, key, {});
        defer _ = self.state.formal_active.remove(key);
        try self.charge();
        const cache = (try actual.declaringCache(caller)) orelse return false;
        const body_node = tokens.bodyOf(cache.tree, callee.declaration) orelse return false;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(cache.tree, &buffer, callee.declaration) orelse return false;
        var frame: Frame = .{
            .cache = cache,
            .declaration = callee.declaration,
            .body = body_node,
            .bindings = (try cache.localBindings(proto, body_node)).*,
            .resolution = self.resolver.frameForFunction(callee.reference),
            .return_token = cache.tree.lastToken(body_node),
            .symbolic = true,
        };
        var parameter_count: u32 = 0;
        var parameters = proto.iterate(cache.tree);
        while (parameters.next() != null) {
            try self.charge();
            parameter_count += 1;
        }
        if (parameter >= parameter_count) return false;
        const fresh = @import("fresh_storage.zig");
        if (try fresh.allocatorPrimitive(cache, actual, .{
            .claim = .{ .first = cache.tree.firstToken(body_node), .last = cache.tree.lastToken(body_node) },
            .depth = 0,
            .remaining = self.remaining,
            .frame = frame.resolution,
        })) |primitive| {
            if (primitive.operation == .allocate and parameter != primitive.allocator_parameter) {
                if (try self.allocationPointee(callee.reference.actual_type.data.function.return_value.*)) |child| {
                    // Byte/scalar copying does not copy a source header's
                    // storage channel. Pointer-bearing element copies abstain.
                    if (try self.addressFree(child, 0)) {
                        try self.state.formal_certificates.put(self.root.gpa, key, {});
                        return true;
                    }
                }
            }
        }
        const mutations = try self.bodyMutations(cache.tree, body_node, .normal, false);
        var output: Output = .{ .complete = mutations.complete };
        frame.mutations = mutations.mutations;
        frame.mutations_ordered = mutations.ordered;
        const previous = self.selected_formal;
        self.selected_formal = parameter;
        defer self.selected_formal = previous;
        var returns: usize = 0;
        const attempt = self.beginAttempt();
        const prunes = self.prunes;
        const reads = self.written_reads;
        self.scan(frame, body_node, &output, &returns, depth + 1) catch |err| {
            _ = self.endAttempt(attempt);
            return err;
        };
        const clean = self.endAttempt(attempt) and self.prunes == prunes and self.written_reads == reads;
        if (!output.complete or output.items.items.len != 0) {
            // Repeated unknown channels are still unknown, not certificates.
            // Remember only a completed source scan in this exact actual
            // context; errors, abandoned cycles and depth cutoffs never enter.
            if (clean) {
                const failed = try self.memo.formal_failures.getOrPut(self.scratch.allocator(), key);
                if (!failed.found_existing) failed.value_ptr.* = .empty;
                try failed.value_ptr.append(self.scratch.allocator(), actual);
            }
            return false;
        }
        try self.state.formal_certificates.put(self.root.gpa, key, {});
        return true;
    }

    fn body(self: *Query, caller: *FileCache, actual: FileCache.ActualCallSummary, depth: u32) Error!SymbolicStorage {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return .{};
        }
        const callee = actual.callee;
        const key: Key = .{
            .declaration = .{ .tree = callee.tree, .module = callee.handle.module, .declaration = callee.declaration },
            .context = callee.reference.actual_type,
        };
        if (self.state.sets.get(key)) |answer| {
            return answer;
        }
        if (self.state.active.contains(key)) {
            self.prunes += 1;
            self.prune_floor = 0;
            return .{};
        }
        try self.state.active.put(self.root.gpa, key, {});
        defer _ = self.state.active.remove(key);
        try self.charge();
        const cache = (try actual.declaringCache(caller)) orelse {
            return .{};
        };
        const body_node = tokens.bodyOf(cache.tree, callee.declaration) orelse {
            return .{};
        };
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(cache.tree, &buffer, callee.declaration) orelse {
            return .{};
        };
        const resolution = self.resolver.frameForFunction(callee.reference);
        var frame: Frame = .{
            .cache = cache,
            .declaration = callee.declaration,
            .body = body_node,
            .bindings = (try cache.localBindings(proto, body_node)).*,
            .resolution = resolution,
            .symbolic = true,
        };
        const mutations = try self.bodyMutations(cache.tree, body_node, .normal, true);
        frame.mutations = mutations.mutations;
        frame.mutations_ordered = mutations.ordered;
        frame.caught_errors = mutations.caught;
        frame.mutations_complete = mutations.complete;
        try self.charge();
        const declared = try self.resolver.normalizedType(callee.reference.actual_type.data.function.return_value.*);
        if (declared) |result_type| {
            // The instantiated callable, not its unresolved generic syntax,
            // supplies this shape. Explicit address-bit conversions still
            // require origin tracing rather than a scalar safety conclusion.
            const attempt = self.beginAttempt();
            const independent = mutations.complete and try self.addressFree(result_type, 0) and !try self.returnedAddressBits(frame, body_node, 0);
            const clean = self.endAttempt(attempt);
            if (independent and clean) {
                const copied: SymbolicStorage = .{ .storage = .{ .complete = true } };
                try self.state.sets.put(self.root.gpa, key, copied);
                return copied;
            }
        }
        var output: Output = .{ .complete = mutations.complete };
        var returns: usize = 0;
        const prunes = self.prunes;
        const reads = self.written_reads;
        const attempt = self.beginAttempt();
        try self.scan(frame, body_node, &output, &returns, depth);
        // Whether the scan ran undisturbed by a cut-off, an abandoned cycle or
        // cells earlier scans wrote: only then is its answer the callee's own.
        const own = self.endAttempt(attempt) and self.prunes == prunes and self.written_reads == reads;
        if (returns == 0) output.complete = false;
        // SDK table coordinates are the canonical receiver, not the private
        // header layout reached through ptrCast(metadata). This is declaration
        // and instantiated-container identity, never a getter-name opcode.
        if (try self.tableContainer(frame.resolution)) {
            for (output.items.items) |*item| {
                try self.charge();
                if (item.owner.param == 0 and item.storage == .backing_storage and item.projection != .payload_value)
                    item.owner.path = "";
            }
        }
        const arena = self.state.allocator(self.root.gpa);
        const owned = try arena.alloc(Alternative, output.items.items.len);
        for (owned, output.items.items) |*dest, src| {
            dest.* = src;
            dest.owner.path = try arena.dupe(u8, src.owner.path);
            dest.result_path = try arena.dupe(u8, src.result_path);
        }
        var answer: ReturnedStorage = .{ .complete = output.complete, .alternatives = owned };
        try self.directFormalSelection(frame, &answer);
        const allocations = try arena.alloc(AllocationRequirement, output.allocations.items.len);
        for (allocations, output.allocations.items) |*dest, src| {
            dest.* = src;
            dest.source = null;
            dest.allocator.path = try arena.dupe(u8, src.allocator.path);
        }
        const symbolic: SymbolicStorage = .{ .storage = answer, .allocations = allocations };
        // An incomplete answer is no certificate, but one the callee's own body
        // produced is the same every time: keep it so its body is scanned once.
        if (answer.complete or own) try self.state.sets.put(self.root.gpa, key, symbolic);
        return symbolic;
    }
    /// Certify a real producer selector, not completeness of deep storage.
    /// Additional statements or return arms have no exact-selector certificate.
    fn directFormalSelection(self: *Query, frame: Frame, answer: *ReturnedStorage) Error!void {
        if (answer.alternatives.len == 0) return;
        var statements = Iterator.init(frame.cache.tree, frame.body);
        try self.charge();
        const statement = statements.next(frame.cache.tree) orelse return;
        try self.charge();
        if (statements.next(frame.cache.tree) != null) return;
        const tree = frame.cache.tree;
        if (tree.nodeTag(statement) != .@"return") return;
        const selected = tree.nodeData(statement).opt_node.unwrap() orelse return;
        var formal = selected;
        switch (tree.nodeTag(selected)) {
            .identifier => {},
            .array_access => {
                const access = tree.nodeData(selected).node_and_node;
                // An index expression could mutate the actual payload before
                // the load. A literal has no such effect.
                if (tree.nodeTag(access[1]) != .number_literal) return;
                formal = access[0];
            },
            .deref => formal = tree.nodeData(selected).node,
            else => return,
        }
        if (tree.nodeTag(formal) != .identifier) return;
        const path = (try self.syntaxPath(frame, formal, 0)) orelse return;
        if (path.binding.origin != .param or try self.rebound(frame, path.binding, tree.lastToken(statement), &.{}))
            return;
        const alternative = answer.alternatives[0];
        if (tree.nodeTag(selected) == .array_access) {
            for (answer.alternatives) |item| {
                try self.charge();
                if (item.owner.param != alternative.owner.param or
                    !std.mem.eql(u8, item.owner.path, item.result_path) or
                    item.projection != .payload_value or item.storage != .payload_storage) return;
            }
        } else if (answer.alternatives.len != 1 or alternative.owner.path.len != 0 or alternative.result_path.len != 0) return;
        const ty = (try self.nodeType(frame, formal)) orelse return;
        const size = try self.pointerSize(ty);
        switch (tree.nodeTag(selected)) {
            .identifier => {
                if (size == .slice and alternative.projection == .pointer_value and
                    alternative.storage == .backing_storage) answer.direct_formal_loan = true;
            },
            .array_access => {
                if (size != null and alternative.projection == .payload_value and
                    alternative.storage == .payload_storage) answer.direct_formal_load = .element;
            },
            .deref => {
                if (size == .one and alternative.projection == .payload_value and
                    alternative.storage == .payload_storage) answer.direct_formal_load = .dereference;
            },
            else => unreachable,
        }
    }

    fn scan(self: *Query, frame: Frame, node: Ast.Node.Index, output: *Output, returns: *usize, depth: u32) Error!void {
        if (self.selected_formal != null and (!output.complete or output.items.items.len != 0)) return;
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            output.complete = false;
            return;
        }
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) == .fn_decl) return;
        // The mutation walk already visited this syntax. Only return-channel
        // scans can skip its empty subtrees; formal retention still examines
        // stores and calls, and a potentially deep subtree keeps its cutoff.
        if (self.selected_formal == null) {
            if (self.state.return_shapes.get(.{ .tree = tree, .node = node })) |shape|
                if (!shape.contains_return and shape.height < depth_limit - depth) return;
        }
        if (self.selected_formal != null) {
            if (tree.nodeTag(node) == .assign) {
                const data = tree.nodeData(node).node_and_node;
                const destination = try self.syntaxPath(frame, data[0], 0);
                const local_cell = tree.nodeTag(data[0]) == .identifier and destination != null and destination.?.binding.origin != .param;
                if (!local_cell) {
                    // A local pointer/header can already alias outward storage.
                    // Only a direct lexical-cell replacement is private here.
                    var at_store = frame;
                    at_store.return_token = tree.firstToken(node);
                    try self.expression(at_store, data[1], .value, "", output, depth + 1);
                }
            }
            var call_buffer: [2]Ast.Node.Index = undefined;
            const ordinary_call = TypeResolver.CallOperands.full(tree, &call_buffer, node) != null;
            if (ordinary_call) {
                try self.call(frame, node, .value, "", output, depth + 1);
            }
            switch (tree.nodeTag(node)) {
                .@"asm", .asm_simple => output.complete = false,
                .assign_destructure => output.complete = false,
                .assign_add,
                .assign_sub,
                .assign_mul,
                .assign_div,
                .assign_mod,
                .assign_bit_and,
                .assign_bit_or,
                .assign_bit_xor,
                .assign_shl,
                .assign_shr,
                .assign_shl_sat,
                .assign_mul_wrap,
                .assign_add_wrap,
                .assign_sub_wrap,
                .assign_mul_sat,
                .assign_add_sat,
                .assign_sub_sat,
                => {
                    const operands = tree.nodeData(node).node_and_node;
                    const destination = try self.nodeType(frame, operands[0]);
                    if (destination == null or !try self.addressFree(destination.?, 0) or
                        try self.hasAddressBits(frame, operands[1], 0))
                        output.complete = false;
                },
                .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => builtin: {
                    // @call follows its actual callee above, never a pure
                    // builtin exemption. Missing callee proofs stay incomplete.
                    if (ordinary_call) break :builtin;
                    const name = tree.tokenSlice(tree.nodeMainToken(node));
                    if (std.mem.eql(u8, name, "@memcpy") or std.mem.eql(u8, name, "@memset")) {
                        var buffer: [2]Ast.Node.Index = undefined;
                        const arguments = tree.builtinCallParams(&buffer, node) orelse {
                            output.complete = false;
                            return;
                        };
                        if (arguments.len != 2) {
                            output.complete = false;
                            return;
                        }
                        const destination = (try self.nodeType(frame, arguments[0])) orelse {
                            output.complete = false;
                            return;
                        };
                        const element = self.resolver.childType(destination) orelse {
                            output.complete = false;
                            return;
                        };
                        const scalar_copy = std.mem.eql(u8, name, "@memcpy") and
                            try self.scalarParameterMemory(frame, arguments[1], 0);
                        if (!try self.addressFree(element, 0) or
                            (!scalar_copy and try self.hasAddressBits(frame, arguments[1], 0))) {
                            output.complete = false;
                            try self.expression(frame, arguments[1], .value, "", output, depth + 1);
                        }
                    } else if (!valueBuiltin(name)) output.complete = false;
                },
                else => {},
            }
            if (!output.complete or output.items.items.len != 0) return;
        }
        if (tree.nodeTag(node) == .@"return") {
            returns.* += 1;
            const value = tree.nodeData(node).opt_node.unwrap() orelse return;
            var at_return = frame;
            at_return.return_token = tree.lastToken(node);
            if (frame.source_return) |returned| {
                at_return.source_return = null;
                returned.source = if (returns.* == 1) .{ .frame = at_return, .node = value } else null;
                return;
            }
            if (frame.projected_return) |path| {
                try self.projectExpression(at_return, value, path.path, path.mode, path.result_path, output, depth + 1);
            } else {
                try self.expression(at_return, value, .value, "", output, depth + 1);
            }
            if (self.selected_formal != null)
                try self.scan(at_return, value, output, returns, depth + 1);
            return;
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            try self.charge();
            try self.scan(frame, child, output, returns, depth + 1);
        }
    }

    /// Mutating nodes and caught-error continuations of one body, in source
    /// order. The walk reads only the tree, so a finished answer is shared by
    /// every query of this file; an aborted walk publishes nothing. Event
    /// collection needs the ordered walk of its own caller and is not cached.
    fn bodyMutations(self: *Query, tree: *const Ast, body_node: Ast.Node.Index, domain: Domain, want_caught: bool) Error!MutationSet {
        // Caught continuations are syntax of the same walk, not another
        // traversal. Cached metadata always carries them; callers that only
        // want mutation nodes simply do not consume this second list.
        const key: MutationKey = .{ .tree = tree, .body = body_node, .domain = domain };
        if (self.source_events == null) {
            try self.charge();
            if (self.state.mutation_sets.get(key)) |known| return known;
        }
        var mutations: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        var caught: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        const previous_errdefer = self.mutation_errdefer;
        const previous_ordered = self.mutation_ordered;
        self.mutation_ordered = true;
        defer self.mutation_ordered = previous_ordered;
        self.mutation_errdefer = false;
        defer self.mutation_errdefer = previous_errdefer;
        const complete = try self.collectMutationsDomain(tree, body_node, &mutations, if (want_caught or self.source_events == null) &caught else null, domain, 0);
        const answer: MutationSet = .{ .mutations = mutations.items, .caught = caught.items, .complete = complete, .ordered = complete and self.mutation_ordered };
        if (self.source_events != null) return answer;
        const arena = self.state.allocator(self.root.gpa);
        const owned: MutationSet = .{
            .mutations = try arena.dupe(Ast.Node.Index, answer.mutations),
            .caught = try arena.dupe(Ast.Node.Index, answer.caught),
            .complete = complete,
            .ordered = answer.ordered,
        };
        try self.state.mutation_sets.put(self.root.gpa, key, owned);
        // Normal and failure mutation syntax differs only at errdefer. A
        // finished walk without one answers both domains with the same owned
        // lists. Partial walks never establish that absence.
        if (complete and !self.mutation_errdefer) {
            var other = key;
            other.domain = if (domain == .normal) .failure else .normal;
            try self.state.mutation_sets.put(self.root.gpa, other, owned);
        }
        return owned;
    }

    fn collectMutationsDomain(self: *Query, tree: *const Ast, node: Ast.Node.Index, result: *std.ArrayListUnmanaged(Ast.Node.Index), caught: ?*std.ArrayListUnmanaged(Ast.Node.Index), domain: Domain, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return false;
        }
        if (tree.nodeTag(node) == .fn_decl) {
            try self.state.return_shapes.put(self.root.gpa, .{ .tree = tree, .node = node }, .{ .contains_return = false, .height = 0 });
            return true;
        }
        // Explicit comptime scopes cannot mutate runtime cells. Their returned
        // values still go through the separate storage/source scans.
        if (tree.nodeTag(node) == .@"comptime") return true;
        if (tree.nodeTag(node) == .@"errdefer") {
            self.mutation_errdefer = true;
            if (domain == .normal) return true;
        }
        if (tree.nodeTag(node) == .@"catch") {
            if (caught) |continuations| try continuations.append(self.scratch.allocator(), tree.nodeData(node).node_and_node[0]);
        }
        const saved_direct = self.source_direct;
        const saved_loop_start = self.source_loop_start;
        const saved_loop_end = self.source_loop_end;
        defer {
            self.source_direct = saved_direct;
            self.source_loop_start = saved_loop_start;
            self.source_loop_end = saved_loop_end;
        }
        if (self.source_events != null and (tree.fullWhile(node) != null or tree.fullFor(node) != null)) {
            self.source_loop_start = tree.firstToken(node);
            self.source_loop_end = tree.lastToken(node);
        }
        const previous_count = result.items.len;
        var complete = true;
        switch (tree.nodeTag(node)) {
            .assign,
            .assign_add,
            .assign_sub,
            .assign_mul,
            .assign_div,
            .assign_mod,
            .assign_bit_and,
            .assign_bit_or,
            .assign_bit_xor,
            .assign_shl,
            .assign_shr,
            .assign_shl_sat,
            .assign_mul_wrap,
            .assign_add_wrap,
            .assign_sub_wrap,
            .assign_mul_sat,
            .assign_add_sat,
            .assign_sub_sat,
            => try result.append(self.scratch.allocator(), node),
            .call,
            .call_one,
            .call_comma,
            .call_one_comma,
            .builtin_call,
            .builtin_call_two,
            .builtin_call_comma,
            .builtin_call_two_comma,
            => try result.append(self.scratch.allocator(), node),
            .assign_destructure, .@"asm", .asm_simple => {
                if (self.source_events == null) return false;
                try result.append(self.scratch.allocator(), node);
                complete = false;
            },
            else => {},
        }
        // Record a token-order certificate during the already charged syntax
        // walk. Unordered or partial lists retain the full horizon scan.
        if (result.items.len != previous_count and previous_count != 0)
            self.mutation_ordered = self.mutation_ordered and
                tree.firstToken(result.items[previous_count - 1]) <= tree.firstToken(node);
        if (self.source_events) |events| {
            if (result.items.len != previous_count or tree.nodeTag(node) == .address_of) {
                try events.append(self.scratch.allocator(), .{
                    .node = node,
                    .direct = self.source_direct,
                    .loop_start = self.source_loop_start,
                    .loop_end = self.source_loop_end,
                });
            }
            self.source_direct = self.source_direct and
                tree.fullIf(node) == null and tree.fullWhile(node) == null and
                tree.fullFor(node) == null and tree.fullSwitch(node) == null and
                switch (tree.nodeTag(node)) {
                    .@"defer", .@"errdefer", .@"catch", .@"orelse", .bool_and, .bool_or => false,
                    else => true,
                };
        }
        var shape: ReturnShape = .{ .contains_return = tree.nodeTag(node) == .@"return", .height = 0 };
        var shape_complete = true;
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            try self.charge();
            if (!try self.collectMutationsDomain(tree, child, result, caught, domain, depth + 1)) complete = false;
            if (tree.nodeTag(node) != .@"return") {
                if (self.state.return_shapes.get(.{ .tree = tree, .node = child })) |child_shape| {
                    shape.contains_return = shape.contains_return or child_shape.contains_return;
                    shape.height = @max(shape.height, child_shape.height + 1);
                } else {
                    // Comptime/errdefer and abandoned mutation subtrees have
                    // no return index; their absence is not an empty proof.
                    shape_complete = false;
                }
            }
        }
        if (shape_complete)
            try self.state.return_shapes.put(self.root.gpa, .{ .tree = tree, .node = node }, shape);
        return complete;
    }

    fn tableContainer(self: *Query, resolution: TypeResolver.ResolutionFrame) Error!bool {
        const actual = resolution.container_type orelse return false;
        if (actual.data != .container) return false;
        const container = actual.data.container;
        if (container.scope_handle.scope == .root) return false;
        const tree = &container.scope_handle.handle.document.tree;
        const node = container.scope_handle.toNode();
        const key: Key = .{
            .declaration = .{ .tree = tree, .module = container.scope_handle.handle.module, .declaration = node },
            .context = actual,
        };
        try self.charge();
        if (self.state.tables.get(key)) |known| return known;
        try self.charge();
        const hash_map = try self.resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/hash_map.zig");
        try self.charge();
        const array_map = try self.resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/array_hash_map.zig");
        if (!hash_map and !array_map) {
            try self.state.tables.put(self.root.gpa, key, false);
            return false;
        }
        const constructor = tokens.enclosingFnDecl(tree, tree.firstToken(node)) orelse return false;
        var top_level = false;
        for (tree.rootDecls()) |decl| {
            try self.charge();
            if (decl == constructor) {
                top_level = true;
                break;
            }
        }
        if (!top_level) {
            try self.state.tables.put(self.root.gpa, key, false);
            return false;
        }
        const body_node = tokens.bodyOf(tree, constructor) orelse return false;
        const is_table = try self.directReturnedContainer(tree, body_node, node, 0);
        try self.state.tables.put(self.root.gpa, key, is_table);
        return is_table;
    }

    /// A map's literal is returned by its type constructor. Nested iterator,
    /// entry and header literals in that returned struct are NOT table roots.
    fn directReturnedContainer(self: *Query, tree: *const Ast, node: Ast.Node.Index, selected: Ast.Node.Index, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return false;
        }
        if (tree.nodeTag(node) == .fn_decl) return false;
        if (tree.nodeTag(node) == .@"return") {
            const result = tree.nodeData(node).opt_node.unwrap() orelse return false;
            return result == selected;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullContainerDecl(&buffer, node) != null) return false;
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            try self.charge();
            if (try self.directReturnedContainer(tree, child, selected, depth + 1)) return true;
        }
        return false;
    }

    fn pointerSize(self: *Query, initial: TypeResolver.ActualType) Error!?std.builtin.Type.Pointer.Size {
        var ty = initial;
        for (0..32) |_| {
            try self.charge();
            ty = (try self.canonicalType(ty)) orelse return null;
            if (self.resolver.pointerSize(ty)) |size| return size;
            if (self.resolver.typeTag(ty) != .optional) return null;
            ty = self.resolver.childType(ty) orelse return null;
        }
        return null;
    }

    /// Statements may consume addresses without returning them. Check only
    /// each returned value, with the body's complete mutation evidence and
    /// its load horizon; scalar stores and opaque writes stay conservative.
    fn returnedAddressBits(self: *Query, frame: Frame, node: Ast.Node.Index, depth: u32) Error!bool {
        try self.charge();
        if (depth >= depth_limit) {
            self.cutoffs += 1;
            return true;
        }
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) == .fn_decl) return false;
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullContainerDecl(&buffer, node) != null) return false;
        if (self.state.return_shapes.get(.{ .tree = tree, .node = node })) |shape|
            if (!shape.contains_return and shape.height < depth_limit - depth) return false;
        if (tree.nodeTag(node) == .@"return") {
            const value = tree.nodeData(node).opt_node.unwrap() orelse return false;
            var at_return = frame;
            at_return.return_token = tree.lastToken(node);
            return self.hasAddressBits(at_return, value, depth + 1);
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            if (try self.returnedAddressBits(frame, child, depth + 1)) return true;
        }
        return false;
    }

    /// Whether `node`'s value can encode an address. A value whose type is
    /// narrower than a pointer cannot (see `narrowValue`); everything else is
    /// answered by the structural walk.
    fn hasAddressBits(self: *Query, frame: Frame, node: Ast.Node.Index, depth: u32) Error!bool {
        const known = try self.memo.address_bits.getOrPut(self.scratch.allocator(), node);
        if (!known.found_existing) known.value_ptr.* = .empty;
        for (known.value_ptr.items) |entry| {
            if (entry.selected_formal == self.selected_formal and sameFrame(entry.frame, frame)) {
                try self.charge();
                return entry.bits;
            }
        }
        const attempt = self.beginAttempt();
        const bits = if (try self.narrowValue(frame, node)) false else try self.hasAddressBitsWalk(frame, node, depth);
        if (self.endAttempt(attempt)) {
            // Nested calls can grow the map; reacquire the finished bucket.
            const finished = self.memo.address_bits.getPtr(node).?;
            try finished.append(self.scratch.allocator(), .{ .frame = frame, .selected_formal = self.selected_formal, .bits = bits });
        }
        return bits;
    }

    /// A value of narrow type holds no address, even when computed from one:
    /// no encoding of a stack address fits in fewer bits than a pointer.
    /// `@intFromPtr`/`@ptrFromInt` inside the expression keep the walk, because
    /// an aggregate of narrow parts can still be assembled into an address.
    fn narrowValue(self: *Query, frame: Frame, node: Ast.Node.Index) Error!bool {
        const ty = (try self.nodeType(frame, node)) orelse return false;
        if (!try self.addressNarrow(ty, 0)) return false;
        const tree = frame.cache.tree;
        const tags = tree.tokens.items(.tag);
        var token = tree.firstToken(node);
        const last = tree.lastToken(node);
        while (token <= last) : (token += 1) {
            if (tags[token] != .builtin) continue;
            const name = tree.tokenSlice(token);
            if (std.mem.eql(u8, name, "@intFromPtr") or std.mem.eql(u8, name, "@ptrFromInt")) return false;
        }
        return true;
    }

    /// The bytes read by a memory copy, not the address of their header.
    fn memoryAddressBits(self: *Query, frame: Frame, node: Ast.Node.Index, depth: u32) Error!bool {
        try self.charge();
        if (depth >= depth_limit) {
            self.cutoffs += 1;
            return true;
        }
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .address_of => return self.hasAddressBits(frame, tree.nodeData(node).node, depth + 1),
            .grouped_expression => return self.memoryAddressBits(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            .slice, .slice_open, .slice_sentinel => return self.memoryAddressBits(frame, tree.fullSlice(node).?.ast.sliced, depth + 1),
            else => {},
        }
        if (try self.sourceAt(frame, node, "", depth + 1)) |source| {
            if (source.frame.cache != frame.cache or source.node != node or
                !sameInvocation(source.frame.invocation, frame.invocation))
                return self.memoryAddressBits(source.frame, source.node, depth + 1);
        }
        const ty = (try self.nodeType(frame, node)) orelse return true;
        if (try self.pointerSize(ty) != null) return true;
        return self.hasAddressBits(frame, node, depth + 1);
    }

    /// Copying an unbound formal's scalar pointee bytes does not copy its
    /// pointer/header. This is a header-nonretention proof only; actual stores
    /// still trace their payload, including encoded bytes, in `effectsFor`.
    /// Reinterpretations and unknown producers get no such credit.
    fn scalarParameterMemory(self: *Query, frame: Frame, node: Ast.Node.Index, depth: u32) Error!bool {
        try self.charge();
        if (depth >= depth_limit or frame.invocation != null) return false;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .grouped_expression => return self.scalarParameterMemory(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            .slice, .slice_open, .slice_sentinel => return self.scalarParameterMemory(frame, tree.fullSlice(node).?.ast.sliced, depth + 1),
            .identifier => {
                const token = tree.nodeMainToken(node);
                const binding = (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) orelse return false;
                if (binding.origin != .param) {
                    if (!binding.is_const) return false;
                    const initial = frame.cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse return false;
                    return self.scalarParameterMemory(frame, initial, depth + 1);
                }
            },
            .field_access => {
                const path = (try self.syntaxPath(frame, node, depth + 1)) orelse return false;
                if (path.binding.origin != .param) return false;
            },
            else => return false,
        }
        const ty = (try self.nodeType(frame, node)) orelse return false;
        if (try self.pointerSize(ty) == null) return false;
        const child = self.resolver.childType(ty) orelse return false;
        return self.addressFree(child, 0);
    }

    /// `node` provably encodes no address: its type holds none, and either the
    /// type is narrow or no address bits reach the value.
    fn addressless(self: *Query, frame: Frame, node: Ast.Node.Index, ty: TypeResolver.ActualType, depth: u32) Error!bool {
        return try self.addressFree(ty, 0) and !try self.hasAddressBits(frame, node, depth);
    }

    /// Close a local scalar dependency graph by joining its initializer and
    /// every reaching store. A loop edge adds no encoded source of its own.
    /// Unknown effects stay unknown; a result that leaned on an older open
    /// graph cannot enter any memo until that graph itself closes.
    /// Loop syntax is immutable and only windows inside this function can
    /// contain its reads. Index it once, retaining AST order for nested loops.
    fn bodyLoopWindows(self: *Query, frame: Frame) Error![]const LoopWindow {
        const key: NodeKey = .{ .tree = frame.cache.tree, .node = frame.body };
        if (self.memo.loop_windows.get(key)) |known| {
            try self.charge();
            return known;
        }
        const tree = frame.cache.tree;
        const body_first = tree.firstToken(frame.body);
        const body_last = tree.lastToken(frame.body);
        var windows: std.ArrayListUnmanaged(LoopWindow) = .empty;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            switch (tag) {
                .while_simple, .while_cont, .@"while", .for_simple, .@"for" => {},
                else => continue,
            }
            try self.charge();
            const loop: Ast.Node.Index = @enumFromInt(raw);
            const first = tree.firstToken(loop);
            const last = tree.lastToken(loop);
            if (first >= body_first and last <= body_last)
                try windows.append(self.scratch.allocator(), .{ .first = first, .last = last });
        }
        try self.memo.loop_windows.put(self.scratch.allocator(), key, windows.items);
        return windows.items;
    }

    fn scalarCellBits(self: *Query, frame: Frame, node: Ast.Node.Index, binding: *const bindings_mod.Binding, path: []const u8, reader: ?Frame, depth: u32) Error!bool {
        try self.charge();
        if (depth >= depth_limit or !frame.mutations_complete) {
            self.cutoffs += 1;
            return true;
        }
        const tree = frame.cache.tree;
        var selected = frame;
        // A store inside a loop also reads earlier iterations' later stores.
        // Widen that read to the loop boundary, not to unrelated later code.
        for (try self.bodyLoopWindows(frame)) |loop| {
            try self.charge();
            const first = loop.first;
            const last = loop.last;
            if (first <= binding.name_token or first > frame.return_token or last < frame.return_token) continue;

            selected.return_token = @max(selected.return_token, last + 1);
        }
        var current = reader;
        if (current) |*read| {
            if (!read.mutations_complete) return true;
            const source = read.cache.tree;
            for (try self.bodyLoopWindows(read.*)) |loop| {
                try self.charge();
                const first = loop.first;
                const last = loop.last;
                if (first < source.firstToken(read.body) or first > read.return_token or last < read.return_token) continue;
                read.return_token = @max(read.return_token, last + 1);
            }
        }
        for (self.active_scalar_cells.items, 0..) |active, index| {
            try self.charge();
            if (active.reader) |read| {
                if (current == null or !sameFrame(read, current.?)) continue;
            } else if (current != null) continue;
            if (active.binding_token == binding.name_token and active.selected_formal == self.selected_formal and std.mem.eql(u8, active.path, path) and
                sameFrame(active.frame, selected))
            {
                self.scalar_prune_floor = @min(self.scalar_prune_floor, index);
                return false;
            }
        }
        try self.active_scalar_cells.append(self.scratch.allocator(), .{
            .frame = selected,
            .reader = current,
            .binding_token = binding.name_token,
            .path = path,
            .selected_formal = self.selected_formal,
        });
        defer self.active_scalar_cells.items.len -= 1;
        const initial = frame.cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse return true;
        var before = selected;
        before.mutations = &.{};
        before.return_token = binding.rhs_first;
        var origins: Output = .{};
        try self.projectExpression(before, initial, path, .value, "", &origins, depth + 1);
        if (!origins.complete or origins.items.items.len != 0 or origins.allocations.items.len != 0) return true;
        try self.effectsFor(selected, .{ .frame = selected, .node = node, .binding = binding, .path = path }, selected.return_token, selected.domain, "", &origins, depth + 1);
        if (current) |read| {
            if (!sameFrameBody(read, selected) or !sameInvocation(read.invocation, selected.invocation)) {
                // The actual pointee can also receive stores in the callee
                // executing this read. Its caller's pre-call contents alone
                // are never a proof of the value now being returned.
                try self.effectsFor(read, .{ .frame = selected, .node = node, .binding = binding, .path = path }, read.return_token, read.domain, "", &origins, depth + 1);
            }
        }
        return !origins.complete or origins.items.items.len != 0 or origins.allocations.items.len != 0;
    }

    fn hasAddressBitsWalk(self: *Query, frame: Frame, node: Ast.Node.Index, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return true;
        }
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .address_of => return true,
            .@"if", .if_simple => {
                const conditional = tree.fullIf(node).?;
                if (try frame.resolution.boolValueOfNode(conditional.ast.cond_expr)) |known| {
                    if (known) return self.hasAddressBits(frame, conditional.ast.then_expr, depth + 1);
                    if (conditional.ast.else_expr.unwrap()) |other|
                        return self.hasAddressBits(frame, other, depth + 1);
                    // A known false guard with no else executes no branch.
                    return false;
                }
                // An unknown guard selects either branch; the guard itself is a
                // bool and encodes no address.
                if (try self.hasAddressBits(frame, conditional.ast.then_expr, depth + 1)) return true;
                if (conditional.ast.else_expr.unwrap()) |other|
                    return self.hasAddressBits(frame, other, depth + 1);
                return false;
            },
            .field_access => {
                const ty = (try self.nodeType(frame, node)) orelse return true;
                if (!try self.addressFree(ty, 0)) return true;
                // A slice length is a count, never a converted address.
                const access = tree.nodeData(node).node_and_token;
                if (std.mem.eql(u8, tree.tokenSlice(access[1]), "len")) {
                    if (try self.nodeType(frame, access[0])) |base| {
                        if (try self.pointerSize(base) == .slice) return false;
                    }
                }
                // Close a mutable scalar field's graph in its actual lexical
                // cell. Pointer headers do not establish pointee contents.
                if (try self.sourceCell(frame, node, null, depth + 1)) |cell| {
                    if (cell.binding.origin != .param and cell.binding.origin != .loop_capture) {
                        if (try self.cellType(cell, depth + 1)) |cell_type| {
                            if (try self.addressFree(cell_type, 0)) {
                                var at_read = frame;
                                at_read.return_token = @max(at_read.return_token, tree.firstToken(node));
                                return self.scalarCellBits(cell.frame, cell.node, cell.binding, cell.path, at_read, depth + 1);
                            }
                        }
                    }
                }
                const source = (try self.sourceAt(frame, node, "", depth + 1)) orelse return true;
                if (source.frame.cache.tree == tree and source.node == node) return true;
                return self.hasAddressBits(source.frame, source.node, depth + 1);
            },
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "@intFromPtr") or std.mem.eql(u8, name, "@ptrFromInt")) return true;
                // Cast type operands are metadata, not value dependencies.
                // Preserve the copied operand, including explicit encodings.
                if (std.mem.eql(u8, name, "@as") or std.mem.eql(u8, name, "@intCast") or
                    std.mem.eql(u8, name, "@truncate") or std.mem.eql(u8, name, "@bitCast") or
                    std.mem.eql(u8, name, "@intFromEnum") or std.mem.eql(u8, name, "@enumFromInt"))
                {
                    var buffer: [2]Ast.Node.Index = undefined;
                    const arguments = tree.builtinCallParams(&buffer, node) orelse return true;
                    if (arguments.len == 0) return true;
                    return self.hasAddressBits(frame, arguments[arguments.len - 1], depth + 1);
                }
                if (std.mem.eql(u8, name, "@sizeOf") or std.mem.eql(u8, name, "@bitSizeOf") or
                    std.mem.eql(u8, name, "@alignOf") or std.mem.eql(u8, name, "@inComptime") or
                    std.mem.eql(u8, name, "@setEvalBranchQuota")) return false;
                if (std.mem.eql(u8, name, "@ptrCast")) {
                    var buffer: [2]Ast.Node.Index = undefined;
                    const arguments = tree.builtinCallParams(&buffer, node) orelse return true;
                    if (arguments.len == 0) return true;
                    const source = (try self.nodeType(frame, arguments[arguments.len - 1])) orelse return true;
                    if (self.resolver.childType(source)) |child| {
                        if (!try self.addressFree(child, 0)) return true;
                    }
                }
            },
            .identifier => {
                const token = tree.nodeMainToken(node);
                // `null`, `true`, `false` and `undefined` are constants, not storage.
                for ([_][]const u8{ "null", "true", "false", "undefined" }) |constant| {
                    if (std.mem.eql(u8, tree.tokenSlice(token), constant)) return false;
                }
                if (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) |binding| {
                    if (binding.origin == .param and try self.invalidated(frame, node)) return true;
                    if (binding.origin == .param) {
                        if (frame.invocation != null) {
                            const source = (try self.actualSource(frame, binding, "", depth + 1)) orelse return true;
                            return self.hasAddressBits(source.frame, source.node, depth + 1);
                        }
                        if (!frame.symbolic) return false;
                        // A symbolic wide scalar can carry an encoded actual
                        // address. Keep its channel until the caller is bound.
                        const ty = (try self.nodeType(frame, node)) orelse return true;
                        return !try self.addressNarrow(ty, 0);
                    }
                    if (!binding.is_const) {
                        const ty = (try self.nodeType(frame, node)) orelse return true;
                        if (try self.addressFree(ty, 0)) return self.scalarCellBits(frame, node, binding, "", null, depth + 1);
                        if (try self.invalidated(frame, node)) return true;
                    }
                    const rhs = frame.cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse return true;
                    if (rhs == node) return true;
                    return self.hasAddressBits(frame, rhs, depth + 1);
                }
                const selected = try self.globalDeclaration(frame, node, depth + 1) orelse return true;
                const variable = tree.fullVarDecl(selected).?;
                if (tree.tokenTag(variable.ast.mut_token) == .keyword_const) {
                    // Local stores cannot replace this immutable global cell.
                    const initializer = variable.ast.init_node.unwrap() orelse return true;
                    return self.hasAddressBits(frame, initializer, depth + 1);
                }
                for (frame.mutations) |write| {
                    try self.charge();
                    if (tree.lastToken(write) >= frame.return_token) continue;
                    if (tree.nodeTag(write) != .assign) continue;
                    const pair = tree.nodeData(write).node_and_node;
                    if (try self.globalDeclaration(frame, pair[0], depth + 1)) |target| {
                        if (target != selected) continue;
                    } else {
                        if (try self.hasAddressBits(frame, pair[1], depth + 1)) return true;
                        continue;
                    }
                    var before = frame;
                    before.return_token = tree.firstToken(write);
                    if (try self.hasAddressBits(before, pair[1], depth + 1)) return true;
                }
                const initializer = variable.ast.init_node.unwrap() orelse return true;
                return self.hasAddressBits(frame, initializer, depth + 1);
            },
            else => {},
        }
        var call_buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &call_buffer, node)) |call_node| {
            // Follow returned scalar bits in the actual invocation, rather
            // than confusing consumed input addresses with returned storage.
            // Caller bindings matter: identity(@intFromPtr(&local)) must
            // retain the address even though its formal is an integer.
            // Opaque callees cannot supply this proof.
            const actual = (try frame.cache.actualCallSummaryAt(call_node.queryToken(tree, node), frame.resolution)) orelse return true;
            const symbolic = try self.body(frame.cache, actual, depth + 1);
            if (symbolic.storage.complete and symbolic.storage.alternatives.len == 0 and
                symbolic.allocations.len == 0) return false;
            var active = frame.invocation;
            while (active) |invocation| : (active = invocation.caller.invocation) {
                try self.charge();
                const ancestor = invocation.actual.callee;
                if (ancestor.tree == actual.callee.tree and ancestor.declaration == actual.callee.declaration and
                    ancestor.reference.actual_type.eql(actual.callee.reference.actual_type))
                {
                    // Recursive actual-value dependence is not a scalar proof.
                    self.cutoffs += 1;
                    return true;
                }
            }
            var at_call = frame;
            at_call.return_token = tree.firstToken(node);
            const callee_frame = (try self.invocationFrame(at_call, actual)) orelse return true;
            return self.returnedAddressBits(callee_frame, callee_frame.body, depth + 1);
        }
        var literal_buffer: [2]Ast.Node.Index = undefined;
        if (try self.arrayLiteral(frame, node, &literal_buffer)) |literal| {
            if (!literal.complete) return true;
            for (literal.elements) |element|
                if (try self.hasAddressBits(frame, element, depth + 1)) return true;
            return false;
        }
        if (tree.fullStructInit(&literal_buffer, node)) |literal| {
            const defaults = try self.literalDefaults(frame, node, literal.ast.fields, depth + 1);
            if (!defaults.complete) return true;
            for (defaults.fields.items) |default_field| {
                if (try self.hasAddressBits(default_field.source.frame, default_field.source.node, depth + 1)) return true;
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            try self.charge();
            if (try self.hasAddressBits(frame, child, depth + 1)) return true;
        }
        return false;
    }
    const SyntaxPath = struct { binding: *const bindings_mod.Binding, path: []const u8 };

    fn syntaxPath(self: *Query, frame: Frame, node: Ast.Node.Index, depth: u32) Error!?SyntaxPath {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return null;
        }
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                const binding = (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) orelse return null;
                return .{ .binding = binding, .path = "" };
            },
            .field_access => {
                const data = tree.nodeData(node).node_and_token;
                var root = (try self.syntaxPath(frame, data[0], depth + 1)) orelse return null;
                root.path = try self.join(root.path, tree.tokenSlice(data[1]));
                return root;
            },
            .@"try", .address_of => return self.syntaxPath(frame, tree.nodeData(node).node, depth + 1),
            .grouped_expression, .unwrap_optional => return self.syntaxPath(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            else => return null,
        }
    }

    /// Whether a write between the binding and the load can replace this
    /// path. Depends on the node and the frame's mutations and horizon only.
    fn invalidated(self: *Query, frame: Frame, node: Ast.Node.Index) Error!bool {
        const known = try self.memo.invalidations.getOrPut(self.scratch.allocator(), node);
        if (!known.found_existing) known.value_ptr.* = .empty;
        for (known.value_ptr.items) |entry| {
            if (sameFrame(entry.frame, frame)) {
                try self.charge();
                return entry.invalidated;
            }
        }
        const attempt = self.beginAttempt();
        const answer = try self.invalidatedWalk(frame, node);
        if (self.endAttempt(attempt)) {
            const finished = self.memo.invalidations.getPtr(node).?;
            try finished.append(self.scratch.allocator(), .{ .frame = frame, .invalidated = answer });
        }
        return answer;
    }

    /// The plain `name = value` writes that make `invalidated` true for an
    /// identifier read, when they are the only ones and all precede the read.
    /// Null when any other write could reach the read: a compound or field
    /// store, a destructure, or a write at or after the horizon (a loop may
    /// carry it back to the read).
    fn plainRewrites(self: *Query, frame: Frame, node: Ast.Node.Index) Error!?[]const Ast.Node.Index {
        if (!frame.mutations_complete) return null;
        const tree = frame.cache.tree;
        const token = tree.nodeMainToken(node);
        const binding = (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) orelse return null;
        if (binding.is_const or binding.origin == .param) return null;
        // A local whose address is taken, or that is a method receiver, can be
        // written by a callee without any visible store to its name.
        const roots = try frame.cache.escapeRoots(frame.body);
        for (roots.addressed) |name| {
            try self.charge();
            if (std.mem.eql(u8, name, binding.name)) return null;
        }
        var writes: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        for (frame.mutations) |write| {
            try self.charge();
            const first = tree.firstToken(write);
            switch (tree.nodeTag(write)) {
                .call, .call_one, .call_comma, .call_one_comma => {
                    if (first <= binding.name_token or first > binding.scope_close) continue;
                    var buffer: [1]Ast.Node.Index = undefined;
                    const full = tree.fullCall(&buffer, write) orelse return null;
                    const root = tokens.rootIdentifier(tree, full.ast.fn_expr) orelse continue;
                    const named = tree.tokenSlice(tree.nodeMainToken(root));
                    if (tree.nodeTag(full.ast.fn_expr) == .field_access and std.mem.eql(u8, named, binding.name)) return null;
                    continue;
                },
                .builtin_call,
                .builtin_call_two,
                .builtin_call_comma,
                .builtin_call_two_comma,
                => continue,
                else => {},
            }
            if (first <= binding.name_token or first > binding.scope_close) continue;
            if (!hasAssignOperands(tree.nodeTag(write))) return null;
            const target = tree.nodeData(write).node_and_node[0];
            const changed = (try self.syntaxPath(frame, target, 0)) orelse continue;
            if (changed.binding.name_token != binding.name_token) continue;
            if (tree.nodeTag(write) == .assign and tree.nodeTag(target) == .identifier and changed.path.len == 0 and first < frame.return_token) {
                // Inside a loop declared after the local, the value written may
                // depend on what the previous iteration wrote.
                if (try self.loopStartAround(tree, binding, first)) |start| {
                    if (!try self.loopInvariant(frame, start, tree.nodeData(write).node_and_node[1])) return null;
                }
                try writes.append(self.scratch.allocator(), write);
                continue;
            }
            return null;
        }
        if (writes.items.len == 0) return null;
        return writes.items;
    }

    /// First token of the outermost loop that holds `token` and starts after
    /// the local `binding` was declared, if any.
    fn loopStartAround(self: *Query, tree: *const Ast, binding: *const bindings_mod.Binding, token: Ast.TokenIndex) Error!?Ast.TokenIndex {
        var outermost: ?Ast.TokenIndex = null;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            switch (tag) {
                .while_simple, .while_cont, .@"while", .for_simple, .@"for" => {},
                else => continue,
            }
            try self.charge();
            const node: Ast.Node.Index = @enumFromInt(raw);
            const first = tree.firstToken(node);
            if (first <= binding.name_token or first > token or tree.lastToken(node) < token) continue;
            if (outermost == null or first < outermost.?) outermost = first;
        }
        return outermost;
    }

    /// Whether `value` reads only values that do not change from one
    /// iteration of the loop starting at `loop_start` to the next: parameters,
    /// constants declared before the loop, and names that are no local at all.
    fn loopInvariant(self: *Query, frame: Frame, loop_start: Ast.TokenIndex, value: Ast.Node.Index) Error!bool {
        const tree = frame.cache.tree;
        const tags = tree.tokens.items(.tag);
        var token = tree.firstToken(value);
        const last = tree.lastToken(value);
        while (token <= last) : (token += 1) {
            if (tags[token] != .identifier) continue;
            if (token != 0 and tags[token - 1] == .period) continue;
            try self.charge();
            const named = (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) orelse continue;
            if (named.origin == .param) continue;
            if (named.is_const and named.origin != .loop_capture and named.name_token < loop_start) continue;
            return false;
        }
        return true;
    }

    fn invalidatedWalk(self: *Query, frame: Frame, node: Ast.Node.Index) Error!bool {
        const selected = (try self.syntaxPath(frame, node, 0)) orelse return false;
        return self.invalidatedPath(frame, selected);
    }

    fn invalidatedPath(self: *Query, frame: Frame, selected: SyntaxPath) Error!bool {
        const tree = frame.cache.tree;
        for (frame.mutations) |write| {
            try self.charge();
            switch (tree.nodeTag(write)) {
                .call,
                .call_one,
                .call_comma,
                .call_one_comma,
                .builtin_call,
                .builtin_call_two,
                .builtin_call_comma,
                .builtin_call_two_comma,
                => continue,
                else => {},
            }
            const token = tree.firstToken(write);
            if (token <= selected.binding.name_token or token >= frame.return_token) continue;
            // A write without a target/value pair (destructuring, inline
            // assembly) may change the selected path.
            if (!hasAssignOperands(tree.nodeTag(write))) return true;
            const target = tree.nodeData(write).node_and_node[0];
            const changed = (try self.syntaxPath(frame, target, 0)) orelse continue;
            if (selected.binding.name_token != changed.binding.name_token) continue;
            if (tree.nodeTag(write) == .assign_add or tree.nodeTag(write) == .assign_sub) {
                const target_type = try self.nodeType(frame, target);
                const offset_type = try self.nodeType(frame, tree.nodeData(write).node_and_node[1]);
                if (target_type != null and offset_type != null and try self.pointerSize(target_type.?) != null and
                    try self.addressFree(offset_type.?, 0)) continue;
            }
            if (changed.path.len == 0 or std.mem.eql(u8, selected.path, changed.path) or
                (std.mem.startsWith(u8, selected.path, changed.path) and selected.path.len > changed.path.len and selected.path[changed.path.len] == '.')) return true;
        }
        return false;
    }

    fn nodeType(self: *Query, frame: Frame, node: Ast.Node.Index) Error!?TypeResolver.ActualType {
        try self.charge();
        return try frame.resolution.typeOfNode(node);
    }

    fn canonicalType(self: *Query, value: TypeResolver.ActualType) Error!?TypeResolver.ActualType {
        if (value.is_type_val) return value;
        try self.charge();
        return try self.resolver.normalizedType(value);
    }

    /// A tuple is either an anonymous tuple or an interned `struct { T, ... }`.
    fn isTuple(self: *Query, ty: TypeResolver.ActualType) bool {
        if (ty.data == .tuple) return true;
        const index = ty.ipIndex() orelse return false;
        return self.resolver.ctx.ip.indexToKey(index) == .tuple_type;
    }

    /// `&.{}` coerced to a slice is a zero-length array: it addresses no
    /// storage. The expected type comes from the address, not the anonymous
    /// literal, which the resolver cannot type on its own.
    fn emptySliceLiteral(self: *Query, frame: Frame, address: Ast.Node.Index, operand: Ast.Node.Index) Error!bool {
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = frame.cache.tree.fullStructInit(&buffer, operand) orelse return false;
        if (literal.ast.fields.len != 0 or literal.ast.type_expr != .none) return false;
        try self.charge();
        const expected = (try frame.resolution.expectedTypeOfNode(address)) orelse return false;
        const ty = (try self.canonicalType(expected)) orelse return false;
        return (try self.pointerSize(ty)) == .slice;
    }

    /// An address-free element loaded from a call's typed result copies scalar
    /// bits. The callee's own coverage of that container adds no loan to it.
    fn scalarCallElement(self: *Query, frame: Frame, node: Ast.Node.Index, base: Ast.Node.Index) Error!bool {
        switch (frame.cache.tree.nodeTag(base)) {
            .call, .call_one, .call_comma, .call_one_comma => {},
            else => return false,
        }
        const element = (try self.nodeType(frame, node)) orelse return false;
        return self.addressFree(element, 0);
    }

    /// Every declared field must be checked. One borrowed sibling prevents
    /// an aggregate's copied-value proof, even when its first field is scalar.
    fn addressFree(self: *Query, value: TypeResolver.ActualType, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 32) {
            self.cutoffs += 1;
            return false;
        }
        // A pure function of the type; only a full-depth answer is shared.
        if (self.memo.address_free.get(value)) |known| return known;
        const cutoffs = self.cutoffs;
        const answer = try self.addressFreeWalk(value, depth);
        if (self.cutoffs == cutoffs) try self.memo.address_free.put(self.scratch.allocator(), value, answer);
        return answer;
    }

    fn addressFreeWalk(self: *Query, value: TypeResolver.ActualType, depth: u32) Error!bool {
        const ty = (try self.canonicalType(value)) orelse return false;
        const tag = self.resolver.typeTag(ty) orelse return false;
        switch (tag) {
            .int, .float, .comptime_int, .comptime_float, .bool, .@"enum", .void, .noreturn, .null, .error_set => return true,
            .optional, .error_union, .array, .vector => {
                const child = self.resolver.childType(ty) orelse return false;
                return self.addressFree(child, depth + 1);
            },
            .@"struct" => {
                if (ty.data != .container) return false;
                const container = ty.data.container;
                const field_frame = self.resolver.frameForContainer(container);
                const tree = &container.scope_handle.handle.document.tree;
                var buffer: [2]Ast.Node.Index = undefined;
                const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return false;
                for (declaration.ast.members) |member| {
                    try self.charge();
                    const container_field = tree.fullContainerField(member) orelse continue;
                    const node = container_field.ast.type_expr.unwrap() orelse return false;
                    try self.charge();
                    const field_type = (try field_frame.typeOfNode(node)) orelse return false;
                    if (!try self.addressFree(field_type, depth + 1)) return false;
                }
                return true;
            },
            else => return false,
        }
    }

    /// Every value of `value` is narrower than a pointer, so no address (not
    /// even its low bits reassembled elsewhere) fits in it. Aggregates are
    /// never narrow: several narrow parts can jointly hold an address.
    fn addressNarrow(self: *Query, value: TypeResolver.ActualType, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 32) {
            self.cutoffs += 1;
            return false;
        }
        if (self.memo.address_narrow.get(value)) |known| return known;
        const cutoffs = self.cutoffs;
        const answer = try self.addressNarrowWalk(value, depth);
        if (self.cutoffs == cutoffs) try self.memo.address_narrow.put(self.scratch.allocator(), value, answer);
        return answer;
    }

    fn addressNarrowWalk(self: *Query, value: TypeResolver.ActualType, depth: u32) Error!bool {
        const ty = (try self.canonicalType(value)) orelse return false;
        const tag = self.resolver.typeTag(ty) orelse return false;
        switch (tag) {
            .bool, .error_set => return true,
            .int => return self.integerNarrow(ty.ipIndex() orelse return false),
            .float => {
                const index = ty.ipIndex() orelse return false;
                return self.resolver.ctx.ip.floatBits(index, builtin.target) < builtin.target.ptrBitWidth();
            },
            .optional, .error_union => {
                const child = self.resolver.childType(ty) orelse return false;
                return self.addressNarrow(child, depth + 1);
            },
            .@"enum" => {
                if (ty.ipIndex()) |index| {
                    const ip = &self.resolver.ctx.ip;
                    return switch (ip.indexToKey(index)) {
                        .enum_type => |enum_index| self.integerNarrow(ip.getEnum(enum_index).tag_type),
                        else => false,
                    };
                }
                if (ty.data != .container) return false;
                // An exhaustive enum's declared tags can be much narrower than
                // its ABI tag type (for example enum(u64) { a = 1, b = 2 }).
                // The canonical range refuses non-exhaustive or unknown tags.
                try self.charge();
                if (try self.resolver.enumIntegerRangeOfType(ty)) |range| {
                    const shift: u7 = @intCast(builtin.target.ptrBitWidth() - 1);
                    const bound = @as(i128, 1) << shift;
                    if (range.min > -bound and range.max < bound) return true;
                }
                const container = ty.data.container;
                const tree = &container.scope_handle.handle.document.tree;
                var buffer: [2]Ast.Node.Index = undefined;
                const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return false;
                // An enum without an explicit tag type has a tag just wide
                // enough for its fields: far narrower than a pointer.
                const tag_node = declaration.ast.arg.unwrap() orelse return true;
                try self.charge();
                const tag_type = (try self.resolver.frameForContainer(container).typeOfNode(tag_node)) orelse return false;
                const canonical = (try self.canonicalType(tag_type)) orelse return false;
                if (self.resolver.typeTag(canonical) != .int) return false;
                return self.integerNarrow(canonical.ipIndex() orelse return false);
            },
            else => return false,
        }
    }

    fn integerNarrow(self: *Query, index: anytype) bool {
        const ip = &self.resolver.ctx.ip;
        if (ip.zigTypeTag(index) != .int) return false;
        return ip.intInfo(index, builtin.target).bits < builtin.target.ptrBitWidth();
    }

    fn payload(self: *Query, value: TypeResolver.ActualType, source: Alternative, known_loan: bool, output: *Output, depth: u32) Error!void {
        try self.charge();
        if (depth >= 32) {
            output.complete = false;
            return;
        }
        const ty = (try self.canonicalType(value)) orelse {
            output.complete = false;
            return;
        };
        if (try self.addressFree(ty, 0)) return;
        const tag = self.resolver.typeTag(ty) orelse {
            output.complete = false;
            return;
        };
        if (tag == .pointer) {
            var item = source;
            item.projection = .payload_value;
            item.storage = .payload_storage;
            // A formal payload selector names the loan, not its carrier cell.
            // Only an address-free pointee closes all reachable storage.
            // Loads through a carrier have no such loan-origin certificate.
            const child = self.resolver.childType(ty);
            if (!known_loan or child == null or !try self.addressFree(child.?, 0))
                output.complete = false;
            try self.add(output, item);
            return;
        }
        if (tag == .optional or tag == .array) {
            const child = self.resolver.childType(ty) orelse {
                output.complete = false;
                return;
            };
            return self.payload(child, source, known_loan, output, depth + 1);
        }
        if (ty.data == .tuple) {
            // Positional selectors stay unknown; component loans do not.
            output.complete = false;
            for (ty.data.tuple) |element|
                try self.payload(element, source, known_loan, output, depth + 1);
            return;
        }
        if (tag != .@"struct" or ty.data != .container) {
            output.complete = false;
            return;
        }
        const container = ty.data.container;
        const field_frame = self.resolver.frameForContainer(container);
        const tree = &container.scope_handle.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse {
            output.complete = false;
            return;
        };
        for (declaration.ast.members) |member| {
            try self.charge();
            const container_field = tree.fullContainerField(member) orelse continue;
            const node = container_field.ast.type_expr.unwrap() orelse {
                output.complete = false;
                continue;
            };
            try self.charge();
            const ty_field = (try field_frame.typeOfNode(node)) orelse {
                output.complete = false;
                continue;
            };
            var projected = source;
            const name = tree.tokenSlice(container_field.ast.main_token);
            projected.owner.path = try self.join(source.owner.path, name);
            projected.result_path = try self.join(source.result_path, name);
            try self.payload(ty_field, projected, known_loan, output, depth + 1);
        }
    }

    fn join(self: *Query, left: []const u8, right: []const u8) Error![]const u8 {
        if (left.len == 0) return right;
        if (right.len == 0) return left;
        return std.fmt.allocPrint(self.scratch.allocator(), "{s}.{s}", .{ left, right });
    }

    fn add(self: *Query, output: *Output, alternative: Alternative) Error!void {
        for (output.items.items) |existing| {
            try self.charge();
            if (existing.owner.param == alternative.owner.param and existing.projection == alternative.projection and
                existing.storage == alternative.storage and std.mem.eql(u8, existing.owner.path, alternative.owner.path) and
                std.mem.eql(u8, existing.result_path, alternative.result_path)) return;
        }
        try output.items.append(self.scratch.allocator(), alternative);
    }

    /// Rebinding questions repeatedly inspect the same immutable write index.
    /// Group its non-declaration writes by name once; lexical binding identity
    /// and the exact use horizon are still checked by each question.
    fn rebindingWrites(self: *Query, frame: Frame, name: []const u8) Error![]const Ast.TokenIndex {
        const key: NodeKey = .{ .tree = frame.cache.tree, .node = frame.body };
        if (self.memo.rebinding_indexes.get(key)) |known| {
            try self.charge();
            return if (known.get(name)) |writes| writes.items else &.{};
        }
        const roots = try frame.cache.escapeRoots(frame.body);
        var index: RebindingIndex = .empty;
        for (roots.writes) |write| {
            try self.charge();
            if (write.declares) continue;
            const entry = try index.getOrPut(self.scratch.allocator(), write.name);
            if (!entry.found_existing) entry.value_ptr.* = .empty;
            try entry.value_ptr.append(self.scratch.allocator(), write.token);
        }
        try self.memo.rebinding_indexes.put(self.scratch.allocator(), key, index);
        return if (index.get(name)) |writes| writes.items else &.{};
    }

    /// `covered` lists plain whole-name writes the caller already folded into
    /// its answer (see `plainRewrites`); they do not count as rebinding.
    fn rebound(self: *Query, frame: Frame, binding: *const bindings_mod.Binding, use_token: Ast.TokenIndex, covered: []const Ast.Node.Index) Error!bool {
        try self.charge();
        write: for (try self.rebindingWrites(frame, binding.name)) |token| {
            try self.charge();
            if (token <= binding.name_token or token >= @max(use_token, frame.return_token)) continue;
            for (covered) |node| if (frame.cache.tree.firstToken(node) == token) continue :write;
            const target = frame.bindings.findAt(binding.name, token) orelse return true;
            if (target.name_token == binding.name_token) return true;
        }
        return false;
    }

    /// A local aggregate may contain positively rooted pointer writes even
    /// when its initializer or loop coverage remains unknown. Retain those
    /// borrows, but do not mistake collecting writes for proving every cell.
    fn assignedOrigins(self: *Query, frame: Frame, binding: *const bindings_mod.Binding, result_path: []const u8, covered: []const Ast.Node.Index, output: *Output, depth: u32) Error!void {
        const tree = frame.cache.tree;
        for (frame.mutations) |write| {
            try self.charge();
            if (tree.nodeTag(write) != .assign) continue;
            if (std.mem.indexOfScalar(Ast.Node.Index, covered, write) != null) continue;
            const token = tree.firstToken(write);
            if (token <= binding.name_token or token >= frame.return_token) continue;
            const data = tree.nodeData(write).node_and_node;
            var target = data[0];
            for (0..64) |_| {
                try self.charge();
                if (tree.nodeTag(target) != .array_access) break;
                target = tree.nodeData(target).node_and_node[0];
            }
            const destination = (try self.syntaxPath(frame, target, 0)) orelse continue;
            if (destination.binding.name_token != binding.name_token) continue;
            var at_write = frame;
            at_write.return_token = token;
            var source: Output = .{};
            const field_path = try self.join(result_path, destination.path);
            try self.expression(at_write, data[1], .value, field_path, &source, depth + 1);
            if (source.items.items.len != 0 or source.allocations.items.len != 0 or !source.complete) output.complete = false;
            for (source.items.items) |item| try self.add(output, item);
        }
    }

    /// Select an explicit initializer field without inspecting unrelated
    /// pointer-bearing siblings. Omitted/default/computed fields abstain.
    fn projectedSource(self: *Query, frame: Frame, initial: Ast.Node.Index, path: []const u8, depth: u32) Error!?Ast.Node.Index {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return null;
        }
        if (path.len == 0) return initial;
        const tree = frame.cache.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = tree.fullStructInit(&buffer, initial) orelse {
            return null;
        };
        const dot = std.mem.indexOfScalar(u8, path, '.');
        const head = path[0 .. dot orelse path.len];
        const tail = if (dot) |index| path[index + 1 ..] else "";
        for (literal.ast.fields) |field_node| {
            try self.charge();
            const first = tree.firstToken(field_node);
            if (first < 3 or tree.tokenTag(first - 1) != .equal or tree.tokenTag(first - 2) != .identifier or
                tree.tokenTag(first - 3) != .period)
            {
                return null;
            }
            if (std.mem.eql(u8, tree.tokenSlice(first - 2), head))
                return self.projectedSource(frame, field_node, tail, depth + 1);
        }
        return null;
    }
    fn callerFrame(self: *Query, cache: *FileCache, token: Ast.TokenIndex, context: ?TypeResolver.ResolutionFrame) Error!?Frame {
        try self.charge();
        const declaration = tokens.enclosingFnDecl(cache.tree, token) orelse return null;
        const body_node = tokens.bodyOf(cache.tree, declaration) orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(cache.tree, &buffer, declaration) orelse return null;
        var resolution = context orelse self.resolver.resolutionFrame();
        if (resolution.actual_type == null) {
            try self.charge();
            const value = (try resolution.resolveValueOfNode(declaration)) orelse return null;
            if (value.is_type_val or value.data != .function) return null;
            const function = value.data.function;
            if (function.fn_token != proto.ast.fn_token or &function.handle.document.tree != cache.tree or
                function.handle.module != cache.module_id) return null;
            resolution = self.resolver.frameForFunction(.{
                .tree = cache.tree,
                .fn_token = proto.ast.fn_token,
                .handle = function.handle,
                .actual_type = value,
            });
        }
        const mutations = try self.bodyMutations(cache.tree, body_node, self.source_domain, true);
        const mutations_complete = mutations.complete;
        if (!mutations_complete and self.source_events == null) return null;
        return .{
            .cache = cache,
            .declaration = declaration,
            .body = body_node,
            .bindings = (try cache.localBindings(proto, body_node)).*,
            .resolution = resolution,
            .mutations = mutations.mutations,
            .mutations_ordered = mutations.ordered,
            .caught_errors = mutations.caught,
            .return_token = token,
            .mutations_complete = mutations_complete,
        };
    }

    fn invocationFrame(self: *Query, caller: Frame, actual: FileCache.ActualCallSummary) Error!?Frame {
        try self.charge();
        // Rebuilds of the same actual invocation must share its immutable
        // frame. Besides avoiding body work, this keeps location memo keys
        // stable without merging different arguments or load horizons.
        const key: NodeKey = .{ .tree = caller.cache.tree, .node = actual.callee.call_node };
        if (self.memo.invocations.get(key)) |known_list| {
            for (known_list.items) |known| {
                try self.charge();
                const invocation = known.invocation.?;
                if (sameActual(invocation.actual, actual) and sameFrame(invocation.caller, caller)) return known;
            }
        }
        const cache = (try actual.declaringCache(caller.cache)) orelse return null;
        const body_node = tokens.bodyOf(cache.tree, actual.callee.declaration) orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(cache.tree, &buffer, actual.callee.declaration) orelse return null;
        const invocation = try self.scratch.allocator().create(Invocation);
        invocation.* = .{ .caller = caller, .actual = actual };
        const mutations = try self.bodyMutations(cache.tree, body_node, caller.domain, true);
        if (!mutations.complete) return null;
        const frame: Frame = .{
            .cache = cache,
            .declaration = actual.callee.declaration,
            .body = body_node,
            .bindings = (try cache.localBindings(proto, body_node)).*,
            .resolution = self.resolver.frameForFunction(actual.callee.reference),
            .mutations = mutations.mutations,
            .mutations_ordered = mutations.ordered,
            .caught_errors = mutations.caught,
            .invocation = invocation,
            .domain = caller.domain,
        };
        // Recursive frame construction may grow the map; obtain its bucket
        // only after that work, rather than retaining a movable map pointer.
        const known = try self.memo.invocations.getOrPut(self.scratch.allocator(), key);
        if (!known.found_existing) known.value_ptr.* = .empty;
        try known.value_ptr.append(self.scratch.allocator(), frame);
        return frame;
    }

    fn actualSource(self: *Query, frame: Frame, binding: *const bindings_mod.Binding, path: []const u8, depth: u32) Error!?Source {
        const invocation = frame.invocation orelse return null;
        const parameter = (try self.formalIndex(frame, binding)) orelse return null;
        var buffer: [2]Ast.Node.Index = undefined;
        try self.charge();
        const argument = (try invocation.actual.callArgumentFor(invocation.caller.cache, &buffer, parameter)) orelse return null;
        if (path.len == 0) {
            const source = (try self.actualArgumentSource(invocation.caller, invocation.actual, parameter, argument, .{ .frame = frame, .binding = binding }, depth)) orelse return null;
            if (source.cell != null) return source;
        }
        return self.sourceAt(invocation.caller, argument, path, depth + 1);
    }

    /// A one-pointer formal can receive the address of an aggregate actual.
    /// Keep the optional formal guard before locating its physical header.
    fn actualArgumentSource(self: *Query, caller: Frame, actual_call: FileCache.ActualCallSummary, parameter: u32, argument: Ast.Node.Index, guard: ?struct { frame: Frame, binding: *const bindings_mod.Binding }, depth: u32) Error!?Source {
        const parameters = actual_call.callee.reference.actual_type.data.function.parameters;
        if (parameter >= parameters.len) return null;
        const formal = (try self.canonicalType(parameters[parameter].type)) orelse return null;
        if (self.resolver.pointerSize(formal) == .one) {
            const child = (try self.canonicalType(self.resolver.childType(formal) orelse return null)) orelse return null;
            if (try self.nodeType(caller, argument)) |actual_type| {
                if (try self.canonicalType(actual_type)) |actual| {
                    if (actual.eql(child)) {
                        if (guard) |bound|
                            if (try self.rebound(bound.frame, bound.binding, bound.frame.return_token, &.{})) return null;
                        const cell = (try self.sourceCell(caller, argument, null, depth + 1)) orelse return null;
                        return .{ .frame = cell.frame, .node = cell.node, .cell = cell };
                    }
                }
            }
        }
        return .{ .frame = caller, .node = argument };
    }

    /// Project the actual returned value in its bound invocation frame. This
    /// is a storage proof, not SDK header freshness: allocator dependencies,
    /// mutations, unknown alternatives and errors remain in the same output.
    fn selectedCallStorage(self: *Query, caller: Frame, node: Ast.Node.Index, actual: FileCache.ActualCallSummary, path: []const u8, output: *Output, depth: u32) Error!void {
        try self.charge();
        if (depth >= depth_limit) return self.depthExhausted(depth);
        var at_call = caller;
        at_call.return_token = caller.cache.tree.firstToken(node);
        var callee = (try self.invocationFrame(at_call, actual)) orelse {
            output.complete = false;
            return;
        };
        callee.projected_return = .{ .path = path, .mode = .value, .result_path = "" };
        var returns: usize = 0;
        try self.scan(callee, callee.body, output, &returns, depth + 1);
        if (returns == 0) output.complete = false;
    }

    /// A forwarded pointer denotes its actual cell, not the argument's header
    /// address after a load. Keep the invocation frame for the effect proof:
    /// a callee which writes a local pointer into that cell is not a negative.
    fn pointerReturnSource(self: *Query, frame: Frame, node: Ast.Node.Index, call_operands: TypeResolver.CallOperands, actual: FileCache.ActualCallSummary, path: []const u8, depth: u32) Error!?Source {
        try self.charge();
        if (depth >= depth_limit) return self.depthExhausted(depth);
        const tree = frame.cache.tree;
        if (try @import("fresh_storage.zig").allocatorPrimitive(frame.cache, actual, .{
            .claim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) },
            .depth = 0,
            .remaining = self.remaining,
            .frame = frame.resolution,
        })) |_| return null;
        var caller = frame;
        caller.return_token = tree.firstToken(node);
        var callee = (try self.invocationFrame(caller, actual)) orelse return null;
        var returned: SourceReturn = .{};
        callee.source_return = &returned;
        var count: usize = 0;
        var unused: Output = .{};
        const selected_formal = self.selected_formal;
        self.selected_formal = null;
        defer self.selected_formal = selected_formal;
        try self.scan(callee, callee.body, &unused, &count, depth + 1);
        callee.source_return = null;
        const result = returned.source orelse return null;
        const source = (try self.sourceAt(result.frame, result.node, "", depth + 1)) orelse return null;
        if (source.frame.cache != frame.cache or source.frame.declaration != frame.declaration or
            source.frame.invocation != frame.invocation) return null;
        var cell = (try self.sourceCell(source.frame, source.node, null, depth + 1)) orelse return null;
        cell.path = try self.join(cell.path, path);
        var effects: Output = .{};
        try self.callEffectsResolved(caller, node, call_operands, actual, cell, frame.domain, "", &effects, depth + 1, callee);
        if (!effects.complete) return null;
        return source;
    }

    /// Select a const declaration from an authenticated type container, not a
    /// same-spelled stored field or a runtime object's pointer header.
    fn containerConstantSource(self: *Query, frame: Frame, base: Ast.Node.Index, name: []const u8, path: []const u8, depth: u32) Error!?Source {
        try self.charge();
        const owner = (try frame.resolution.resolveValueOfNode(base)) orelse return null;
        if (!owner.is_type_val or owner.data != .container) return null;
        const declaration = (try owner.lookupSymbol(&self.resolver.analyser, name)) orelse return null;
        if (!declaration.isConst()) return null;
        const declared = switch (declaration.decl) {
            .ast_node => |node| node,
            else => return null,
        };
        const tree = &declaration.handle.document.tree;
        const variable = tree.fullVarDecl(declared) orelse return null;
        const initial = variable.ast.init_node.unwrap() orelse return null;
        const resolution = self.resolver.frameForContainer(owner.data.container);
        if (!resolution.handle.eql(declaration.handle)) return null;
        const cache = if (tree == frame.cache.tree and declaration.handle.module == frame.cache.module_id)
            frame.cache
        else
            &(try grow.sourceDocument(frame.cache, declaration.handle, resolution.resolver.ctx)).cache;
        var source_frame = frame;
        source_frame.cache = cache;
        source_frame.declaration = owner.data.container.scope_handle.toNode();
        source_frame.body = source_frame.declaration;
        source_frame.bindings.items = &.{};
        source_frame.bindings.tree = tree;
        source_frame.resolution = resolution;
        source_frame.invocation = null;
        source_frame.source_return = null;
        source_frame.projected_return = null;
        source_frame.mutations = &.{};
        source_frame.caught_errors = &.{};
        source_frame.return_token = tree.lastToken(initial) + 1;
        return self.sourceAt(source_frame, initial, path, depth + 1);
    }

    /// Resolve one immutable source value, preserving its declaring frame.
    /// A multi-return constructor has no unique function-table source.
    fn sourceAt(self: *Query, frame: Frame, node: Ast.Node.Index, path: []const u8, depth: u32) Error!?Source {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return null;
        }
        for (self.active_sources.items, 0..) |active, index| {
            try self.charge();
            if (active.node != node or active.selected_formal != self.selected_formal or
                !std.mem.eql(u8, active.path, path) or !sameFrame(active.frame, frame)) continue;
            self.prunes += 1;
            self.source_prune_floor = @min(self.source_prune_floor, index);
            return null;
        }
        try self.active_sources.append(self.scratch.allocator(), .{ .frame = frame, .node = node, .path = path, .selected_formal = self.selected_formal });
        defer self.active_sources.items.len -= 1;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .@"try", .deref => return self.sourceAt(frame, tree.nodeData(node).node, path, depth + 1),
            .address_of => {
                // An immutable address names the lexical destination even if
                // its contents change. Only a pointee projection needs those
                // contents; stripping the address loses the writable root.
                if (path.len == 0) {
                    const cell = if (try self.nodeType(frame, node) != null)
                        try self.sourceCell(frame, node, null, depth + 1)
                    else
                        null;
                    return .{ .frame = frame, .node = node, .cell = cell };
                }
                return self.sourceAt(frame, tree.nodeData(node).node, path, depth + 1);
            },
            .grouped_expression, .unwrap_optional => return self.sourceAt(frame, tree.nodeData(node).node_and_token[0], path, depth + 1),
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                // Pointer casts preserve an authenticated physical address;
                // they do not authenticate a reinterpreted payload or write.
                if (path.len == 0 and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@ptrCast")) {
                    var buffer: [2]Ast.Node.Index = undefined;
                    if (tree.builtinCallParams(&buffer, node)) |arguments| {
                        if (arguments.len == 1) {
                            if (try self.nodeType(frame, node)) |ty| {
                                if (try self.pointerSize(ty) == .one) {
                                    if (try self.sourceAt(frame, arguments[0], "", depth + 1)) |source|
                                        if (source.cell != null) return source;
                                }
                            }
                        }
                    }
                }
            },
            .field_access => {
                if (path.len == 0) {
                    try self.charge();
                    switch (try frame.resolution.functionReference(node)) {
                        .function => return .{ .frame = frame, .node = node },
                        .unknown, .not_callable => {},
                    }
                }
                const field_node = tree.nodeData(node).node_and_token;
                if (try self.containerConstantSource(frame, field_node[0], tree.tokenSlice(field_node[1]), path, depth + 1)) |source|
                    return source;
                return self.sourceAt(frame, field_node[0], try self.join(tree.tokenSlice(field_node[1]), path), depth + 1);
            },
            .identifier => {
                const token = tree.nodeMainToken(node);
                if (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) |binding| {
                    if (binding.origin == .param) {
                        if (frame.invocation != null) return self.actualSource(frame, binding, path, depth + 1);
                        return if (path.len == 0) .{ .frame = frame, .node = node } else null;
                    }
                    if (try self.rebound(frame, binding, token, &.{})) {
                        return null;
                    }
                    if (path.len != 0) {
                        if (try self.nodeType(frame, node)) |ty| {
                            if (try self.pointerSize(ty) == .one) {
                                // A typed immutable pointer alias selects the
                                // actual lexical parent, including a checked
                                // fieldParentPtr. Project from that cell, not
                                // from the pointer-producing builtin syntax.
                                if (try self.sourceCell(frame, node, ty, depth + 1)) |cell| {
                                    const lexical: SourceCell = .{ .frame = frame, .binding = binding, .node = node, .path = "" };
                                    if (!sameCellRoot(lexical, cell) or cell.path.len != 0)
                                        return self.sourceAt(cell.frame, cell.node, try self.join(cell.path, path), depth + 1);
                                }
                            }
                        }
                    }
                    const selected: SourceCell = .{ .frame = frame, .binding = binding, .node = node, .path = path };
                    const horizon = if (frame.return_token != 0) frame.return_token else token;
                    // Authenticate a mutable source only after checking the
                    // calls before this use as well as its direct writes.
                    if (!binding.is_const) {
                        var effects: Output = .{};
                        try self.effectsFor(frame, selected, horizon, frame.domain, "", &effects, depth + 1);
                        if (!effects.complete) {
                            return null;
                        }
                    }
                    self.written_reads += 1;
                    for (self.written_cells.items) |written| {
                        try self.charge();
                        if (try self.cellsOverlap(selected, written)) {
                            return null;
                        }
                    }
                    for (frame.mutations) |write| {
                        try self.charge();
                        const at = tree.firstToken(write);
                        if (frame.mutations_ordered and at >= horizon) break;
                        if (tree.nodeTag(write) != .assign or at <= binding.rhs_last or at >= horizon) continue;
                        // A discard evaluates its RHS but has no destination.
                        // Its enclosing assignment starts before this call's
                        // token and must not invalidate an actual receiver.
                        const destination = tree.nodeData(write).node_and_node[0];
                        if (tree.nodeTag(destination) == .identifier and
                            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(destination)), "_")) continue;
                        const target = (try self.sourceCell(frame, destination, null, depth + 1)) orelse {
                            return null;
                        };
                        if (try self.cellsOverlap(selected, target)) {
                            return null;
                        }
                    }
                    const initial = frame.cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse {
                        return null;
                    };
                    if (initial == node) {
                        return null;
                    }
                    var at_copy = frame;
                    if (try self.nodeType(frame, node)) |ty| {
                        // Values freeze their fields when copied. References
                        // retain the current pointee-load horizon.
                        if (try self.pointerSize(ty) == null)
                            at_copy.return_token = tree.firstToken(initial);
                    }
                    return self.sourceAt(at_copy, initial, path, depth + 1);
                }
                try self.charge();
                const declaration = (try self.resolver.analyser.lookupSymbolGlobal(frame.resolution.handle, tree.tokenSlice(token), tree.tokenStart(token))) orelse return null;
                if (&declaration.handle.document.tree != tree or declaration.handle.module != frame.cache.module_id) return null;
                const declared = switch (declaration.decl) {
                    .ast_node => |value| value,
                    else => return null,
                };
                const variable = tree.fullVarDecl(declared) orelse {
                    if (path.len == 0) return .{ .frame = frame, .node = node };
                    return null;
                };
                if (tree.tokenTag(variable.ast.mut_token) != .keyword_const) return null;
                return self.sourceAt(frame, variable.ast.init_node.unwrap() orelse return null, path, depth + 1);
            },
            .call, .call_one, .call_comma, .call_one_comma => {
                if (path.len == 0) return .{ .frame = frame, .node = node };
                var buffer: [2]Ast.Node.Index = undefined;
                const call_node = TypeResolver.CallOperands.full(tree, &buffer, node) orelse return null;
                try self.charge();
                const actual = (try frame.cache.actualCallSummaryAt(call_node.queryToken(tree, node), frame.resolution)) orelse return null;
                var caller = frame;
                caller.return_token = tree.firstToken(node);
                var callee = (try self.invocationFrame(caller, actual)) orelse return null;
                var returned: SourceReturn = .{};
                callee.source_return = &returned;
                var count: usize = 0;
                var unused: Output = .{};
                const selected_formal = self.selected_formal;
                self.selected_formal = null;
                self.scan(callee, callee.body, &unused, &count, depth + 1) catch |err| {
                    self.selected_formal = selected_formal;
                    return err;
                };
                self.selected_formal = selected_formal;
                const source = returned.source orelse return null;
                return self.sourceAt(source.frame, source.node, path, depth + 1);
            },
            else => {},
        }
        if (path.len == 0) return .{ .frame = frame, .node = node };
        // Resolve each stored field value before selecting its child. A
        // constructor may store an address to an immutable function table;
        // that address is not another nested struct literal.
        const dot = std.mem.indexOfScalar(u8, path, '.');
        const head = path[0 .. dot orelse path.len];
        const tail = if (dot) |index| path[index + 1 ..] else "";
        const selected = (try self.projectedSource(frame, node, head, depth + 1)) orelse return null;
        return self.sourceAt(frame, selected, tail, depth + 1);
    }

    fn projectExpression(self: *Query, frame: Frame, node: Ast.Node.Index, path: []const u8, mode: Mode, result_path: []const u8, output: *Output, depth: u32) Error!void {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            output.complete = false;
            return;
        }
        if (path.len == 0) return self.expression(frame, node, mode, result_path, output, depth + 1);
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .@"try" => return self.projectExpression(frame, tree.nodeData(node).node, path, mode, result_path, output, depth + 1),
            .grouped_expression, .unwrap_optional => return self.projectExpression(frame, tree.nodeData(node).node_and_token[0], path, mode, result_path, output, depth + 1),
            .error_value => return,
            .@"if", .if_simple => {
                const conditional = tree.fullIf(node).?;
                try self.charge();
                const known = try frame.resolution.boolValueOfNode(conditional.ast.cond_expr);
                if (known == null or known.?) try self.projectExpression(frame, conditional.ast.then_expr, path, mode, result_path, output, depth + 1);
                if (known == null or !known.?) {
                    if (conditional.ast.else_expr.unwrap()) |other| {
                        try self.projectExpression(frame, other, path, mode, result_path, output, depth + 1);
                    } else output.complete = false;
                }
                return;
            },
            else => {},
        }
        if (try self.sourceCell(frame, node, null, depth + 1)) |located| {
            var cell = located;
            cell.path = try self.join(cell.path, path);
            if (cell.binding.origin != .param and cell.path.len != 0)
                return self.backingForCell(cell, self.cellHorizon(frame, cell, node), mode, result_path, output, depth + 1);
        }
        if (try self.sourceAt(frame, node, path, depth + 1)) |source|
            return self.expression(source.frame, source.node, mode, result_path, output, depth + 1);
        var literal_buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullStructInit(&literal_buffer, node)) |literal| {
            const defaults = try self.literalDefaults(frame, node, literal.ast.fields, depth + 1);
            if (!defaults.complete) output.complete = false;
            const dot = std.mem.indexOfScalar(u8, path, '.');
            const head = path[0 .. dot orelse path.len];
            const tail = if (dot) |index| path[index + 1 ..] else "";
            for (defaults.fields.items) |field_source| {
                try self.charge();
                if (std.mem.eql(u8, field_source.name, head))
                    return self.projectExpression(field_source.source.frame, field_source.source.node, tail, mode, result_path, output, depth + 1);
            }
        }
        var call_buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &call_buffer, node)) |call_node| {
            try self.charge();
            const actual = (try frame.cache.actualCallSummaryAt(call_node.queryToken(tree, node), frame.resolution)) orelse {
                output.complete = false;
                return;
            };
            var caller = frame;
            caller.return_token = tree.firstToken(node);
            var callee = (try self.invocationFrame(caller, actual)) orelse {
                output.complete = false;
                return;
            };
            callee.projected_return = .{ .path = path, .mode = mode, .result_path = result_path };
            var returns: usize = 0;
            try self.scan(callee, callee.body, output, &returns, depth + 1);
            if (returns == 0) output.complete = false;
            return;
        }
        // No unique source does not erase positive formal coordinates.
        var parent: Output = .{};
        try self.expression(frame, node, .coordinate, result_path, &parent, depth + 1);
        if (!parent.complete) output.complete = false;
        if (parent.allocations.items.len != 0) output.complete = false;
        for (parent.items.items) |item| {
            var selected = item;
            selected.owner.path = try self.join(item.owner.path, path);
            selected.projection = .pointer_value;
            selected.storage = .backing_storage;
            try self.add(output, selected);
        }
        if (parent.items.items.len == 0) output.complete = false;
    }
    fn cellHorizon(self: *Query, frame: Frame, cell: SourceCell, use_node: Ast.Node.Index) Ast.TokenIndex {
        _ = self;
        return if (frame.cache.tree == cell.frame.cache.tree and frame.declaration == cell.frame.declaration)
            @max(frame.return_token, frame.cache.tree.firstToken(use_node))
        else
            cell.frame.return_token;
    }

    fn sameCellRoot(a: SourceCell, b: SourceCell) bool {
        if (a.frame.cache.tree != b.frame.cache.tree or a.frame.cache.module_id != b.frame.cache.module_id or
            a.frame.declaration != b.frame.declaration or a.binding.name_token != b.binding.name_token) return false;
        const left = a.frame.resolution.actual_type;
        const right = b.frame.resolution.actual_type;
        return if (left) |value| if (right) |other| value.eql(other) else false else right == null;
    }

    fn pathContains(parent: []const u8, child: []const u8) bool {
        return parent.len == 0 or std.mem.eql(u8, parent, child) or
            (std.mem.startsWith(u8, child, parent) and child.len > parent.len and child[parent.len] == '.');
    }

    /// One selection extends the other at a segment boundary, at its start
    /// or at its end. Equal selections nest; an empty selection nests with all.
    fn pathsNest(a: []const u8, b: []const u8) bool {
        const short = if (a.len <= b.len) a else b;
        const long = if (a.len <= b.len) b else a;
        if (pathContains(short, long)) return true;
        return std.mem.endsWith(u8, long, short) and long[long.len - short.len - 1] == '.';
    }

    fn cellsOverlap(self: *Query, a: SourceCell, b: SourceCell) Error!bool {
        if (!sameCellRoot(a, b)) return false;
        if (pathContains(a.path, b.path) or pathContains(b.path, a.path)) return true;
        // Distinct spellings prove disjoint storage only at a typed struct
        // boundary. Union members and unresolved paths can share header bytes.
        var left = std.mem.splitScalar(u8, a.path, '.');
        var right = std.mem.splitScalar(u8, b.path, '.');
        var parent = a;
        parent.path = "";
        while (left.next()) |segment| {
            try self.charge();
            const other = right.next() orelse return true;
            if (!std.mem.eql(u8, segment, other)) {
                const ty = (try self.cellType(parent, 0)) orelse return true;
                return self.resolver.typeTag(ty) != .@"struct";
            }
            parent.path = try self.join(parent.path, segment);
        }
        return true;
    }

    /// Locations, not copied header origins. Pointer aliases and invocation
    /// formals resolve back to the actual lexical cell before comparing paths.
    fn sourceCell(self: *Query, frame: Frame, node: Ast.Node.Index, expected: ?TypeResolver.ActualType, depth: u32) Error!?SourceCell {
        // A bound invocation names its caller by address. Reuse locations
        // only within that same invocation, never an equivalent rebuilt one.
        const known = try self.memo.source_cells.getOrPut(self.scratch.allocator(), node);
        if (!known.found_existing) known.value_ptr.* = .empty;
        for (known.value_ptr.items) |entry| {
            if (entry.selected_formal == self.selected_formal and entry.frame.invocation == frame.invocation and
                sameType(entry.expected, expected) and sameFrame(entry.frame, frame))
            {
                try self.charge();
                return entry.cell;
            }
        }
        // Resolving a location reads only the tree, the frame and the type
        // resolver, unless it falls through to `sourceAt`, which also reads
        // the cells earlier scans wrote. Those answers are not shared.
        const attempt = self.beginAttempt();
        const reads = self.written_reads;
        const answer = try self.sourceCellWalk(frame, node, expected, depth);
        if (self.endAttempt(attempt) and self.written_reads == reads) {
            const finished = self.memo.source_cells.getPtr(node).?;
            try finished.append(self.scratch.allocator(), .{ .frame = frame, .expected = expected, .selected_formal = self.selected_formal, .cell = answer });
        }
        return answer;
    }

    fn sourceCellWalk(self: *Query, frame: Frame, node: Ast.Node.Index, expected: ?TypeResolver.ActualType, depth: u32) Error!?SourceCell {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return null;
        }
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .address_of => {
                const operand = tree.nodeData(node).node;
                if (tree.nodeTag(operand) == .identifier) {
                    const token = tree.nodeMainToken(operand);
                    const binding = (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) orelse return null;
                    return .{ .frame = frame, .binding = binding, .node = operand, .path = "" };
                }
                return self.sourceCell(frame, operand, null, depth + 1);
            },
            .deref, .@"try" => return self.sourceCell(frame, tree.nodeData(node).node, expected, depth + 1),
            .grouped_expression, .unwrap_optional => return self.sourceCell(frame, tree.nodeData(node).node_and_token[0], expected, depth + 1),
            .field_access => {
                const field_node = tree.nodeData(node).node_and_token;
                // Dereferencing a pointer-valued base follows the stored
                // address. The final field itself remains a lexical cell:
                // assigning a pointer field replaces its header, not pointee.
                if (try self.nodeType(frame, field_node[0])) |ty| {
                    if (try self.pointerSize(ty) == .one) {
                        // A receiver formal denotes its actual lexical cell,
                        // not the aggregate constructor copied into that cell.
                        // Authenticate the pointee before extending its path;
                        // pointer-valued fields still need their stored source.
                        const pointee = (try self.canonicalType(self.resolver.childType(ty) orelse return null)) orelse return null;
                        var located = try self.sourceCell(frame, field_node[0], ty, depth + 1);
                        if (located) |cell| {
                            const actual_type = try self.cellType(cell, depth + 1);
                            if (actual_type == null or !actual_type.?.eql(pointee)) located = null;
                        }
                        var cell = located orelse blk: {
                            const source = (try self.sourceAt(frame, field_node[0], "", depth + 1)) orelse return null;
                            break :blk (try self.sourceCell(source.frame, source.node, ty, depth + 1)) orelse return null;
                        };
                        cell.path = try self.join(cell.path, tree.tokenSlice(field_node[1]));
                        return cell;
                    }
                }
                var cell = (try self.sourceCell(frame, field_node[0], null, depth + 1)) orelse return null;
                cell.path = try self.join(cell.path, tree.tokenSlice(field_node[1]));
                return cell;
            },
            .slice_open, .slice, .slice_sentinel => return self.sourceCell(frame, tree.fullSlice(node).?.ast.sliced, null, depth + 1),
            .array_access => return self.sourceCell(frame, tree.nodeData(node).node_and_node[0], null, depth + 1),
            .identifier => {
                const token = tree.nodeMainToken(node);
                const binding = (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) orelse return null;
                if (binding.origin == .param) {
                    if (frame.invocation) |invocation| {
                        const parameter = (try self.formalIndex(frame, binding)) orelse return null;
                        var buffer: [2]Ast.Node.Index = undefined;
                        try self.charge();
                        const actual = (try invocation.actual.callArgumentFor(invocation.caller.cache, &buffer, parameter)) orelse return null;
                        return self.sourceCell(invocation.caller, actual, null, depth + 1);
                    }
                    return .{ .frame = frame, .binding = binding, .node = node, .path = "" };
                }
                const ty = (try self.nodeType(frame, node)) orelse return null;
                if (try self.pointerSize(ty) != null) {
                    if (try self.rebound(frame, binding, token, &.{})) return null;
                    const initial = frame.cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse return null;
                    return self.sourceCell(frame, initial, ty, depth + 1);
                }
                return .{ .frame = frame, .binding = binding, .node = node, .path = "" };
            },
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                var buffer: [2]Ast.Node.Index = undefined;
                const arguments = tree.builtinCallParams(&buffer, node) orelse return null;
                if (std.mem.eql(u8, name, "@fieldParentPtr")) {
                    if (arguments.len != 2) return null;
                    try self.charge();
                    const field_name = (try frame.resolution.stringValueOfNode(arguments[0])) orelse return null;
                    var child = (try self.sourceCell(frame, arguments[1], null, depth + 1)) orelse return null;
                    const last_dot = std.mem.lastIndexOfScalar(u8, child.path, '.');
                    const actual_field = child.path[(if (last_dot) |dot| dot + 1 else 0)..];
                    if (!std.mem.eql(u8, field_name, actual_field)) return null;
                    const result_type = expected orelse (try self.nodeType(frame, node)) orelse return null;
                    const parent_type = (try self.canonicalType(result_type)) orelse return null;
                    if (self.resolver.pointerSize(parent_type) != .one) return null;
                    const parent = (try self.canonicalType(self.resolver.childType(parent_type) orelse return null)) orelse return null;
                    if (parent.data != .container) return null;
                    const container = parent.data.container;
                    const owner_tree = &container.scope_handle.handle.document.tree;
                    const field_frame = self.resolver.frameForContainer(container);
                    var container_buffer: [2]Ast.Node.Index = undefined;
                    const declaration = owner_tree.fullContainerDecl(&container_buffer, container.scope_handle.toNode()) orelse return null;
                    const child_pointer = (try self.nodeType(frame, arguments[1])) orelse return null;
                    if (self.resolver.pointerSize(child_pointer) != .one) return null;
                    const child_type = (try self.canonicalType(self.resolver.childType(child_pointer) orelse return null)) orelse return null;
                    var verified = false;
                    for (declaration.ast.members) |member| {
                        try self.charge();
                        const field_node = owner_tree.fullContainerField(member) orelse continue;
                        if (!std.mem.eql(u8, owner_tree.tokenSlice(field_node.ast.main_token), field_name)) continue;
                        try self.charge();
                        const declared = (try field_frame.typeOfNode(field_node.ast.type_expr.unwrap() orelse return null)) orelse return null;
                        const normalized = (try self.canonicalType(declared)) orelse return null;
                        verified = normalized.eql(child_type);
                        break;
                    }
                    if (!verified) return null;
                    child.path = child.path[0 .. last_dot orelse 0];
                    // The actual parent's container must agree, not just its
                    // field spelling and the child's type.
                    const actual_parent = (try self.cellType(child, depth + 1)) orelse return null;
                    if (!actual_parent.eql(parent)) return null;
                    return child;
                }
                if (std.mem.eql(u8, name, "@as") or std.mem.eql(u8, name, "@alignCast") or
                    std.mem.eql(u8, name, "@constCast") or std.mem.eql(u8, name, "@ptrCast"))
                {
                    if (arguments.len == 0) return null;
                    if (std.mem.eql(u8, name, "@ptrCast")) {
                        const destination = expected orelse (try self.nodeType(frame, node)) orelse return null;
                        const source = (try self.nodeType(frame, arguments[arguments.len - 1])) orelse return null;
                        const destination_child = (try self.canonicalType(self.resolver.childType(destination) orelse return null)) orelse return null;
                        const source_child = (try self.canonicalType(self.resolver.childType(source) orelse return null)) orelse return null;
                        // A byte/union reinterpretation cannot preserve a
                        // typed field path as a disjoint header location.
                        if (!destination_child.eql(source_child)) return null;
                    }
                    return self.sourceCell(frame, arguments[arguments.len - 1], expected, depth + 1);
                }
            },
            else => {},
        }
        return null;
    }

    const DefaultFieldSource = struct { name: []const u8, source: Source };
    const LiteralDefaults = struct {
        complete: bool = true,
        fields: std.ArrayListUnmanaged(DefaultFieldSource) = .empty,
    };

    const ArrayLiteral = struct { elements: []const Ast.Node.Index, complete: bool };

    fn literalType(self: *Query, frame: Frame, node: Ast.Node.Index) Error!?TypeResolver.ActualType {
        if (try self.nodeType(frame, node)) |value|
            if (try self.canonicalType(value)) |ty| return ty;
        try self.charge();
        var expected = (try frame.resolution.expectedTypeOfNode(node)) orelse return null;
        // An anonymous literal expected as `?T` or `E!T` is initialising the `T`
        // payload: the wrapper adds no field, default or element of its own.
        for (0..8) |_| {
            const wrapped = (try self.canonicalType(expected)) orelse return null;
            const wrapper = self.resolver.typeTag(wrapped) orelse return wrapped;
            if (wrapper != .optional and wrapper != .error_union) return wrapped;
            expected = self.resolver.childType(wrapped) orelse return null;
        }
        return null;
    }

    /// Zig can encode an array literal as a struct-init AST node. Its
    /// instantiated type and exact element count, not that tag, prove shape.
    fn arrayLiteral(self: *Query, frame: Frame, node: Ast.Node.Index, buffer: *[2]Ast.Node.Index) Error!?ArrayLiteral {
        const tree = frame.cache.tree;
        if (tree.fullArrayInit(buffer, node)) |array|
            return .{ .elements = array.ast.elements, .complete = true };
        // Native array syntax already identifies element payloads. Only an
        // ambiguous struct initializer needs a resolved array shape.
        const structure = tree.fullStructInit(buffer, node) orelse return null;
        const elements = structure.ast.fields;
        var ty = (try self.literalType(frame, node)) orelse return null;
        if (self.resolver.typeTag(ty) != .array and structure.ast.type_expr.unwrap() == null) {
            // Context can select array semantics for an inferred dot literal.
            try self.charge();
            if (try frame.resolution.expectedTypeOfNode(node)) |expected| {
                if (try self.canonicalType(expected)) |value| {
                    if (self.resolver.typeTag(value) == .array) ty = value;
                }
            }
        }
        if (self.resolver.typeTag(ty) != .array) return null;
        try self.charge();
        const count: ?u64 = switch (ty.data) {
            .array => |info| info.elem_count,
            .ip_index => switch (self.resolver.ctx.ip.indexToKey(ty.ipIndex() orelse return .{ .elements = elements, .complete = false })) {
                .array_type => |info| info.len,
                else => null,
            },
            else => null,
        };
        return .{ .elements = elements, .complete = if (count) |length| length == elements.len else false };
    }

    /// Omitted fields are values too. Their AST and resolver belong to the
    /// declaring container, never to a coincidentally same-spelled local.
    fn literalDefaults(self: *Query, frame: Frame, node: Ast.Node.Index, explicit: []const Ast.Node.Index, depth: u32) Error!LiteralDefaults {
        try self.charge();
        var result: LiteralDefaults = .{};
        if (depth >= depth_limit) return self.depthExhausted(depth);
        const ty = try self.literalType(frame, node);
        if (ty == null or ty.?.data != .container or self.resolver.typeTag(ty.?) != .@"struct") {
            result.complete = false;
            return result;
        }
        const container = ty.?.data.container;
        const resolution = self.resolver.frameForContainer(container);
        const owner_tree = &resolution.handle.document.tree;
        const owner_cache = if (owner_tree == frame.cache.tree and resolution.handle.module == frame.cache.module_id)
            frame.cache
        else
            &(try grow.sourceDocument(frame.cache, resolution.handle, resolution.resolver.ctx)).cache;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = owner_tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse {
            result.complete = false;
            return result;
        };
        for (declaration.ast.members) |member| {
            try self.charge();
            const container_field = owner_tree.fullContainerField(member) orelse continue;
            if (container_field.ast.tuple_like) {
                result.complete = false;
                continue;
            }
            const name = owner_tree.tokenSlice(container_field.ast.main_token);
            var supplied = false;
            for (explicit) |value| {
                try self.charge();
                const first = frame.cache.tree.firstToken(value);
                const tags = frame.cache.tree.tokens.items(.tag);
                if (first >= 3 and tags[first - 1] == .equal and tags[first - 2] == .identifier and tags[first - 3] == .period and
                    std.mem.eql(u8, frame.cache.tree.tokenSlice(first - 2), name))
                {
                    supplied = true;
                    break;
                }
            }
            if (supplied) continue;
            const value = container_field.ast.value_expr.unwrap() orelse {
                result.complete = false;
                continue;
            };
            var source_frame = frame;
            source_frame.cache = owner_cache;
            source_frame.declaration = container.scope_handle.toNode();
            source_frame.body = source_frame.declaration;
            source_frame.bindings.items = &.{};
            source_frame.bindings.tree = owner_tree;
            source_frame.resolution = resolution;
            source_frame.invocation = null;
            source_frame.source_return = null;
            source_frame.mutations = &.{};
            source_frame.caught_errors = &.{};
            source_frame.return_token = owner_tree.lastToken(source_frame.body) + 1;
            try result.fields.append(self.scratch.allocator(), .{ .name = name, .source = .{ .frame = source_frame, .node = value } });
        }
        return result;
    }

    /// Field-type selection uses only this node's contextual type and path,
    /// not its runtime contents or load horizon. Repeated alias/effect demands
    /// therefore share one typed selection in the same canonical resolution.
    fn cellType(self: *Query, cell: SourceCell, depth: u32) Error!?TypeResolver.ActualType {
        if (depth >= 64) return self.cellTypeWalk(cell, depth);
        const key: NodeKey = .{ .tree = cell.frame.cache.tree, .node = cell.node };
        if (self.memo.cell_types.get(key)) |known_list| {
            for (known_list.items) |known| {
                if (sameResolution(known.resolution, cell.frame.resolution) and std.mem.eql(u8, known.path, cell.path)) {
                    try self.charge();
                    return known.ty;
                }
            }
        }
        const answer = (try self.cellTypeWalk(cell, depth)) orelse return null;
        const known = try self.memo.cell_types.getOrPut(self.scratch.allocator(), key);
        if (!known.found_existing) known.value_ptr.* = .empty;
        try known.value_ptr.append(self.scratch.allocator(), .{ .resolution = cell.frame.resolution, .path = cell.path, .ty = answer });
        return answer;
    }

    fn cellTypeWalk(self: *Query, cell: SourceCell, depth: u32) Error!?TypeResolver.ActualType {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return null;
        }
        var ty = (try self.nodeType(cell.frame, cell.node)) orelse return null;
        ty = (try self.canonicalType(ty)) orelse return null;
        if (cell.path.len != 0 and self.resolver.pointerSize(ty) == .one)
            ty = (try self.canonicalType(self.resolver.childType(ty) orelse return null)) orelse return null;
        var segments = std.mem.tokenizeScalar(u8, cell.path, '.');
        while (segments.next()) |segment| {
            try self.charge();
            if (ty.data != .container) return null;
            const container = ty.data.container;
            const tree = &container.scope_handle.handle.document.tree;
            const resolution = self.resolver.frameForContainer(container);
            var buffer: [2]Ast.Node.Index = undefined;
            const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return null;
            var field_type: ?TypeResolver.ActualType = null;
            for (declaration.ast.members) |member| {
                try self.charge();
                const field_node = tree.fullContainerField(member) orelse continue;
                if (!std.mem.eql(u8, tree.tokenSlice(field_node.ast.main_token), segment)) continue;
                try self.charge();
                field_type = try resolution.typeOfNode(field_node.ast.type_expr.unwrap() orelse return null);
                break;
            }
            ty = (try self.canonicalType(field_type orelse return null)) orelse return null;
        }
        return ty;
    }

    /// Scalar writes cannot hide pointer storage behind union/byte aliases.
    /// A scalar descendant must cross only authenticated struct fields until
    /// it reaches a wholly address-free subtree. RHS origins remain separate.
    fn scalarWritePreservesStorage(self: *Query, target: SourceCell, demand: SourceCell) Error!bool {
        const ty = (try self.cellType(demand, 0)) orelse return false;
        if (try self.addressFree(ty, 0)) return true;
        if (!pathContains(demand.path, target.path) or std.mem.eql(u8, demand.path, target.path)) return false;
        var parent = demand;
        const suffix = target.path[demand.path.len + @intFromBool(demand.path.len != 0) ..];
        var segments = std.mem.tokenizeScalar(u8, suffix, '.');
        while (segments.next()) |segment| {
            try self.charge();
            const parent_type = (try self.cellType(parent, 0)) orelse return false;
            if (try self.addressFree(parent_type, 0)) return true;
            if (self.resolver.typeTag(parent_type) != .@"struct") return false;
            parent.path = try self.join(parent.path, segment);
        }
        return true;
    }

    /// Repeated loads of one physical cell ask the same instantiated body
    /// about its writes up to the same horizon. A cycle-free scan that never
    /// read earlier writes can be replayed, including its write/copy evidence.
    fn effectsFor(self: *Query, frame: Frame, cell: SourceCell, horizon: Ast.TokenIndex, domain: Domain, result_path: []const u8, output: *Output, depth: u32) Error!void {
        // Ordered source-event collection and mutable source-return slots are
        // not set-valued effects; their scans must still run in source order.
        if (self.source_events != null or frame.source_return != null or cell.frame.source_return != null or depth >= 64)
            return self.effectsForScan(frame, cell, horizon, domain, result_path, output, depth);
        const seeded = output.seeded or output.items.items.len != 0;
        if (self.effect_certificates.get(frame.body)) |known_list| {
            try self.charge();
            for (known_list.items) |known| {
                if (known.horizon != horizon or known.domain != domain or known.seeded != seeded or
                    known.selected_formal != self.selected_formal or !sameFrame(known.frame, frame) or
                    !sameFrame(known.cell.frame, cell.frame) or !sameCellRoot(known.cell, cell) or
                    known.cell.node != cell.node or !std.mem.eql(u8, known.cell.path, cell.path) or
                    !std.mem.eql(u8, known.result_path, result_path)) continue;
                if (!known.complete) output.complete = false;
                for (known.items) |item| try self.add(output, item);
                try output.allocations.appendSlice(self.scratch.allocator(), known.allocations);
                try self.written_cells.appendSlice(self.scratch.allocator(), known.writes);
                try self.copied_payloads.appendSlice(self.scratch.allocator(), known.copies);
                return;
            }
        }
        const writes = self.written_cells.items.len;
        const copies = self.copied_payloads.items.len;
        const reads = self.written_reads;
        const prunes = self.prunes;
        const attempt = self.beginAttempt();
        var local: Output = .{ .seeded = seeded };
        self.effectsForScan(frame, cell, horizon, domain, result_path, &local, depth) catch |err| {
            _ = self.endAttempt(attempt);
            return err;
        };
        const clean = self.endAttempt(attempt) and self.prunes == prunes and self.written_reads == reads;
        if (!local.complete) output.complete = false;
        for (local.items.items) |item| try self.add(output, item);
        try output.allocations.appendSlice(self.scratch.allocator(), local.allocations.items);
        if (!clean) return;
        const known = try self.effect_certificates.getOrPut(self.scratch.allocator(), frame.body);
        if (!known.found_existing) known.value_ptr.* = .empty;
        try known.value_ptr.append(self.scratch.allocator(), .{
            .frame = frame,
            .cell = cell,
            .horizon = horizon,
            .domain = domain,
            .result_path = result_path,
            .selected_formal = self.selected_formal,
            .seeded = seeded,
            .complete = local.complete,
            .items = local.items.items,
            .allocations = local.allocations.items,
            .writes = try self.scratch.allocator().dupe(SourceCell, self.written_cells.items[writes..]),
            .copies = try self.scratch.allocator().dupe(CopiedPayload, self.copied_payloads.items[copies..]),
        });
    }

    fn effectsForScan(self: *Query, frame: Frame, cell: SourceCell, horizon: Ast.TokenIndex, domain: Domain, result_path: []const u8, output: *Output, depth: u32) Error!void {
        try self.charge();
        if (depth >= 64) {
            self.prunes += 1;
            self.cutoffs += 1;
            self.prune_floor = 0;
            output.complete = false;
            return;
        }
        const key: Key = .{
            .declaration = .{ .tree = frame.cache.tree, .module = frame.cache.module_id, .declaration = frame.declaration },
            .context = frame.resolution.actual_type orelse {
                output.complete = false;
                return;
            },
        };
        for (self.active_effects.items, 0..) |active, index| {
            try self.charge();
            if (KeyContext.eql(.{}, active.function, key) and sameCellRoot(active.cell, cell) and
                std.mem.eql(u8, active.cell.path, cell.path) and active.horizon == horizon and active.domain == domain)
            {
                self.prunes += 1;
                self.prune_floor = @min(self.prune_floor, index);
                output.complete = false;
                return;
            }
        }
        try self.active_effects.append(self.scratch.allocator(), .{ .function = key, .cell = cell, .horizon = horizon, .domain = domain });
        defer self.active_effects.items.len -= 1;
        const tree = frame.cache.tree;
        for (frame.mutations) |effect| {
            try self.charge();
            const token = tree.firstToken(effect);
            if (token >= horizon) {
                if (frame.mutations_ordered) break;
                continue;
            }
            if (frame.cache.tree == cell.frame.cache.tree and frame.declaration == cell.frame.declaration and token <= cell.binding.rhs_last) continue;
            var at_effect = frame;
            at_effect.return_token = token;
            at_effect.domain = domain;
            if (tree.nodeTag(effect) == .assign) {
                const data = tree.nodeData(effect).node_and_node;
                if (tree.nodeTag(data[0]) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(data[0])), "_")) continue;
                const target = (try self.sourceCell(at_effect, data[0], null, depth + 1)) orelse {
                    // An unresolved destination may alias the demanded cell.
                    output.complete = false;
                    continue;
                };
                if (try self.scalarAllocationPayloadStore(at_effect, data[0], data[1], target, depth + 1)) continue;
                try self.written_cells.append(self.scratch.allocator(), target);
                if (!try self.cellsOverlap(target, cell)) continue;
                if (!pathContains(target.path, cell.path) and !pathContains(cell.path, target.path))
                    output.complete = false;
                const target_type = (try self.cellType(target, 0)) orelse {
                    output.complete = false;
                    continue;
                };
                if (try self.addressFree(target_type, 0) and !try self.scalarWritePreservesStorage(target, cell)) output.complete = false;
                const suffix = if (pathContains(target.path, cell.path) and target.path.len < cell.path.len)
                    cell.path[target.path.len + @intFromBool(target.path.len != 0) ..]
                else
                    "";
                if (frame.invocation != null and pathContains(target.path, cell.path)) {
                    try self.copied_payloads.append(self.scratch.allocator(), .{
                        .frame = at_effect,
                        .cell = cell,
                        .source = .{ .frame = at_effect, .node = data[1] },
                        .path = suffix,
                        .element = false,
                    });
                }
                try self.projectExpression(at_effect, data[1], suffix, .value, result_path, output, depth + 1);
                // Branch overwrites keep the prior origin. They cannot prove
                // a borrowed initializer detached on every path.
                if (cell.binding.origin != .param and (output.seeded or output.items.items.len != 0)) output.complete = false;
                continue;
            }
            var buffer: [2]Ast.Node.Index = undefined;
            if (TypeResolver.CallOperands.full(tree, &buffer, effect)) |call_node| {
                try self.callEffects(at_effect, effect, call_node, cell, domain, result_path, output, depth + 1);
                continue;
            }
            if (tree.builtinCallParams(&buffer, effect)) |arguments| {
                const name = tree.tokenSlice(tree.nodeMainToken(effect));
                if (std.mem.eql(u8, name, "@call")) {
                    output.complete = false;
                    continue;
                }
                if (std.mem.eql(u8, name, "@memcpy") or std.mem.eql(u8, name, "@memset")) {
                    if (arguments.len != 2) {
                        output.complete = false;
                        continue;
                    }
                    const target = try self.sourceCell(at_effect, arguments[0], null, depth + 1);
                    if (target != null and !try self.cellsOverlap(target.?, cell)) continue;
                    if (target != null and !pathContains(target.?.path, cell.path) and
                        !pathContains(cell.path, target.?.path))
                        output.complete = false;
                    const fresh = target == null and try self.allocationDestination(at_effect, arguments[0], output, depth + 1);
                    if (target == null and !fresh) output.complete = false;
                    const ty = (try self.nodeType(at_effect, arguments[0])) orelse {
                        output.complete = false;
                        continue;
                    };
                    const element = self.resolver.childType(ty) orelse {
                        output.complete = false;
                        continue;
                    };
                    // Address-free bytes stored into a new allocation reach
                    // no existing cell and carry no origin.
                    if (fresh and try self.addressFree(element, 0)) continue;
                    // A slice or many-pointer header stores through its pointee,
                    // not into its own cell. Address-free bytes carry no origin.
                    if (target != null and try self.addressFree(element, 0)) {
                        if (try self.cellType(target.?, 0)) |header| {
                            const size = try self.pointerSize(header);
                            if (size == .slice or size == .many) continue;
                        }
                    }
                    const scalar_safe = target != null and try self.scalarWritePreservesStorage(target.?, cell);
                    if (scalar_safe and std.mem.eql(u8, name, "@memcpy") and
                        try self.memoryAddressBits(at_effect, arguments[1], depth + 1)) {
                        output.complete = false;
                        if (try self.sourceAt(at_effect, arguments[1], "", depth + 1)) |source|
                            try self.copied_payloads.append(self.scratch.allocator(), .{ .frame = at_effect, .cell = cell, .source = source });
                    }
                    if (!try self.addressFree(element, 0) or !scalar_safe) {
                        output.complete = false;
                        try self.expression(at_effect, arguments[1], .value, result_path, output, depth + 1);
                    }
                } else {
                    // Casts and metadata builtins do not write through their
                    // operands. Other builtins get no mutable-reach credit.
                    for (arguments) |argument| {
                        try self.charge();
                        const target = try self.sourceCell(at_effect, argument, null, depth + 1);
                        if (target != null and try self.cellsOverlap(target.?, cell)) {
                            if (!valueBuiltin(name)) output.complete = false;
                        }
                    }
                }
                continue;
            }
            if (!hasAssignOperands(tree.nodeTag(effect))) {
                // Destructuring, inline assembly and the like have no
                // target/value pair to project.
                output.complete = false;
                continue;
            }
            const target = (try self.sourceCell(at_effect, tree.nodeData(effect).node_and_node[0], null, depth + 1)) orelse {
                output.complete = false;
                continue;
            };
            if (try self.cellsOverlap(target, cell)) {
                if (!pathContains(target.path, cell.path) and !pathContains(cell.path, target.path))
                    output.complete = false;
                const ty = (try self.nodeType(at_effect, tree.nodeData(effect).node_and_node[0])) orelse {
                    output.complete = false;
                    continue;
                };
                if (!try self.addressFree(ty, 0) or !try self.scalarWritePreservesStorage(target, cell) or try self.hasAddressBits(at_effect, tree.nodeData(effect).node_and_node[1], depth + 1)) output.complete = false;
            }
        }
    }

    /// A missing lexical location is disjoint only when this actual source
    /// is a new canonical allocation. Remap and copied headers do not qualify.
    /// Provider requirements remain symbolic until the outer actual boundary.
    fn allocationDestination(self: *Query, frame: Frame, node: Ast.Node.Index, output: *Output, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return false;
        }
        const source = (try self.sourceAt(frame, node, "", depth + 1)) orelse return false;
        if (source.frame.cache.tree != frame.cache.tree or source.node != node or
            source.frame.invocation != frame.invocation)
            return self.allocationDestination(source.frame, source.node, output, depth + 1);
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .@"try" => return self.allocationDestination(frame, tree.nodeData(node).node, output, depth + 1),
            .grouped_expression, .unwrap_optional => return self.allocationDestination(frame, tree.nodeData(node).node_and_token[0], output, depth + 1),
            .slice_open, .slice, .slice_sentinel => return self.allocationDestination(frame, tree.fullSlice(node).?.ast.sliced, output, depth + 1),
            .@"orelse", .@"catch" => {
                const operands = tree.nodeData(node).node_and_node;
                if (tree.nodeTag(operands[1]) != .@"return" and
                    !(tree.firstToken(operands[1]) == tree.lastToken(operands[1]) and
                        tree.tokenTag(tree.firstToken(operands[1])) == .keyword_unreachable)) return false;
                return self.allocationDestination(frame, operands[0], output, depth + 1);
            },
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (!std.mem.eql(u8, name, "@as") and !std.mem.eql(u8, name, "@alignCast") and
                    !std.mem.eql(u8, name, "@ptrCast") and !std.mem.eql(u8, name, "@constCast")) return false;
                var buffer: [2]Ast.Node.Index = undefined;
                const arguments = tree.builtinCallParams(&buffer, node) orelse return false;
                if (arguments.len == 0) return false;
                return self.allocationDestination(frame, arguments[arguments.len - 1], output, depth + 1);
            },
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const call_node = TypeResolver.CallOperands.full(tree, &buffer, node) orelse return false;
        try self.charge();
        const actual = (try frame.cache.actualCallSummaryAt(call_node.queryToken(tree, node), frame.resolution)) orelse return false;
        const primitive = (try @import("fresh_storage.zig").allocatorPrimitive(frame.cache, actual, .{
            .claim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) },
            .depth = 0,
            .remaining = self.remaining,
            .frame = frame.resolution,
        })) orelse return false;
        if (primitive.operation != .allocate) return false;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const allocator = (try actual.callArgumentFor(frame.cache, &argument_buffer, primitive.allocator_parameter)) orelse return false;
        var origin: Output = .{};
        try self.allocationOrigin(frame, allocator, &origin, 0);
        if (!origin.complete) return false;
        for (origin.allocations.items) |requirement| {
            try self.charge();
            try output.allocations.append(self.scratch.allocator(), requirement);
        }
        return true;
    }

    /// An ordinary typed index write into authenticated fresh scalar backing
    /// cannot replace its descriptor. Reinterpreted byte aliases, unknown
    /// backing, and encoded scalar values still use the full origin walk.
    fn scalarAllocationPayloadStore(self: *Query, frame: Frame, target_node: Ast.Node.Index, value_node: Ast.Node.Index, target: SourceCell, depth: u32) Error!bool {
        const tree = frame.cache.tree;
        if (tree.nodeTag(target_node) != .array_access) return false;
        const base = tree.nodeData(target_node).node_and_node[0];
        const base_type = (try self.nodeType(frame, base)) orelse return false;
        const size = try self.pointerSize(base_type);
        if (size != .slice and size != .many) return false;
        const lexical = (try self.syntaxPath(frame, base, depth + 1)) orelse return false;
        if (target.frame.cache != frame.cache or target.frame.declaration != frame.declaration or
            target.binding.name_token != lexical.binding.name_token or !std.mem.eql(u8, target.path, lexical.path)) return false;
        const element = (try self.nodeType(frame, target_node)) orelse return false;
        if (!try self.addressFree(element, 0) or try self.hasAddressBits(frame, value_node, depth + 1)) return false;
        var before = frame;
        before.mutations = &.{};
        before.return_token = lexical.binding.name_token;
        var origin: Output = .{};
        return self.allocationDestination(before, base, &origin, depth + 1);
    }

    /// Canonical lexical cell plus ordered field projection, demanded at a
    /// specific use. Branch writes join positive origins and stay incomplete;
    /// opaque calls never erase a previously captured backing alternative.
    fn localBackingAt(self: *Query, frame: Frame, selected_node: Ast.Node.Index, use_node: Ast.Node.Index, mode: Mode, result_path: []const u8, output: *Output, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            return false;
        }
        if (mode == .location) return false;
        const tree = frame.cache.tree;
        if (tree.nodeTag(selected_node) == .field_access) {
            const access = tree.nodeData(selected_node).node_and_token;
            if (std.mem.eql(u8, tree.tokenSlice(access[1]), "ptr")) {
                if (try self.nodeType(frame, access[0])) |base_type| {
                    // A slice's built-in pointer selector is handled by field;
                    // it is not a declared child field for cellType to chase.
                    if (try self.pointerSize(base_type) == .slice) return false;
                }
            }
        }
        const cell = (try self.sourceCell(frame, selected_node, null, depth + 1)) orelse return false;
        if (cell.path.len == 0) return false;
        if (cell.binding.origin == .param) {
            if (mode != .value or !try self.invalidated(frame, selected_node)) return false;
            if (tree.nodeTag(selected_node) != .field_access) return false;
            const access = tree.nodeData(selected_node).node_and_token;
            var before_writes = frame;
            before_writes.mutations = &.{};
            before_writes.return_token = 0;
            try self.field(before_writes, selected_node, access[0], tree.tokenSlice(access[1]), mode, result_path, output, depth + 1);
            try self.effectsFor(frame, cell, self.cellHorizon(frame, cell, use_node), frame.domain, result_path, output, depth + 1);
            return true;
        }
        try self.backingForCell(cell, self.cellHorizon(frame, cell, use_node), mode, result_path, output, depth + 1);
        return true;
    }

    fn backingForCell(self: *Query, cell: SourceCell, horizon: Ast.TokenIndex, mode: Mode, result_path: []const u8, output: *Output, depth: u32) Error!void {
        try self.charge();
        const tree = cell.frame.cache.tree;
        const initial = cell.frame.cache.nodeForExactSpan(cell.binding.rhsFirstAfterTry(tree.tokens.items(.tag)), cell.binding.rhs_last) orelse {
            output.complete = false;
            return;
        };
        var at_initial = cell.frame;
        at_initial.return_token = cell.binding.name_token;
        try self.projectExpression(at_initial, initial, cell.path, mode, result_path, output, depth + 1);
        try self.effectsFor(cell.frame, cell, horizon, cell.frame.domain, result_path, output, depth + 1);
    }
    fn effectCall(self: *Query, frame: Frame, node: Ast.Node.Index, call_node: TypeResolver.CallOperands, depth: u32) Error!?FileCache.ActualCallSummary {
        try self.charge();
        if (try frame.cache.actualCallSummaryAt(call_node.queryToken(frame.cache.tree, node), frame.resolution)) |actual| return actual;
        // A type-only dynamic target is insufficient. Trace the actual
        // constructor's selected field to an immutable source function value.
        const source = (try self.sourceAt(frame, call_node.ast.fn_expr, "", depth + 1)) orelse return null;
        try self.charge();
        const reference = switch (try source.frame.resolution.functionReference(source.node)) {
            .function => |value| value,
            .unknown, .not_callable => return null,
        };
        const function = reference.actual_type.data.function;
        const name = function.name orelse return null;
        try self.charge();
        const declared = (try self.resolver.analyser.lookupSymbolGlobal(reference.handle, name, reference.tree.tokenStart(reference.fn_token))) orelse return null;
        if (!declared.handle.eql(reference.handle)) return null;
        const declaration = switch (declared.decl) {
            .ast_node => |value| value,
            else => return null,
        };
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(reference.tree, &proto_buffer, declaration) orelse return null;
        if (proto.ast.fn_token != reference.fn_token) return null;
        const actual: FileCache.ActualCallSummary = .{
            .callee = .{
                .call_node = node,
                .tree = reference.tree,
                .fn_token = reference.fn_token,
                .handle = reference.handle,
                .declaration = declaration,
                .reference = reference,
                .caller_frame = frame.resolution,
            },
            .summary = null,
            .argument_offset = null,
            .read_only = null,
        };
        // Mapping still belongs to the original dynamic CALL's typed view.
        // No source-local argument list or assumed receiver offset is used.
        for (function.parameters, 0..) |_, index| {
            try self.charge();
            var argument_buffer: [2]Ast.Node.Index = undefined;
            if (try actual.callArgumentFor(frame.cache, &argument_buffer, @intCast(index)) == null) return null;
        }
        return actual;
    }

    fn callEffects(self: *Query, frame: Frame, node: Ast.Node.Index, call_node: TypeResolver.CallOperands, cell: SourceCell, domain: Domain, result_path: []const u8, output: *Output, depth: u32) Error!void {
        try self.charge();
        const actual = try self.effectCall(frame, node, call_node, depth + 1);
        return self.callEffectsResolved(frame, node, call_node, actual, cell, domain, result_path, output, depth, null);
    }

    fn sameFrameBody(a: Frame, b: Frame) bool {
        if (a.cache.tree != b.cache.tree or a.cache.module_id != b.cache.module_id or a.declaration != b.declaration or
            a.return_token != b.return_token or a.domain != b.domain or
            a.mutations.ptr != b.mutations.ptr or a.mutations.len != b.mutations.len or
            a.caught_errors.ptr != b.caught_errors.ptr or a.caught_errors.len != b.caught_errors.len) return false;
        const left = a.resolution.actual_type;
        const right = b.resolution.actual_type;
        return if (left) |value| if (right) |other| value.eql(other) else false else right == null;
    }

    /// One call's effects on one demanded cell. Nested demands of the same
    /// cell reach the same call through several consumers and field paths;
    /// a scan that abandoned no cycle (and met no depth cut-off) answers all
    /// of them identically. Invocation frames bind formals to actuals, so
    /// they match only structurally equal invocation chains, never by address.
    fn callEffectsResolved(self: *Query, frame: Frame, node: Ast.Node.Index, call_node: TypeResolver.CallOperands, actual: ?FileCache.ActualCallSummary, cell: SourceCell, domain: Domain, result_path: []const u8, output: *Output, depth: u32, prepared: ?Frame) Error!void {
        if (prepared != null) return self.callEffectsScan(frame, node, call_node, actual, cell, domain, result_path, output, depth, prepared);
        // What the scan can read of the caller's output is whether an enclosing
        // scan already holds alternatives (`Output.seeded`); everything else
        // it writes is a set union and a monotone `complete`. So the scan runs
        // into its own output, is certified for that one bit, and is folded in.
        const seeded = output.seeded or output.items.items.len != 0;
        if (self.call_effect_certificates.get(node)) |known_list| {
            try self.charge();
            for (known_list.items) |known| {
                // Reuse a finished empty whole-cell certificate, but never
                // broaden a cold field demand just to seek one. A whole-cell
                // walk can spend the allowance on unrelated sibling payloads.
                const empty_whole = actual != null and cell.path.len != 0 and
                    known.cell.path.len == 0 and known.result_path.len == 0 and
                    known.complete and known.items.len == 0 and known.allocations.len == 0;
                if (known.domain == domain and known.seeded == seeded and known.selected_formal == self.selected_formal and
                    sameFrameBody(known.frame, frame) and sameInvocation(known.frame.invocation, frame.invocation) and
                    sameCellRoot(known.cell, cell) and sameInvocation(known.cell.frame.invocation, cell.frame.invocation) and
                    (empty_whole or (std.mem.eql(u8, known.cell.path, cell.path) and std.mem.eql(u8, known.result_path, result_path))))
                {
                    if (!known.complete) output.complete = false;
                    for (known.items) |item| try self.add(output, item);
                    for (known.allocations) |requirement| try output.allocations.append(self.scratch.allocator(), requirement);
                    try self.copied_payloads.appendSlice(self.scratch.allocator(), known.copies);
                    return;
                }
            }
        }
        const prunes = self.prunes;
        const attempt = self.beginAttempt();
        const copies = self.copied_payloads.items.len;
        var local: Output = .{ .seeded = seeded };
        try self.callEffectsScan(frame, node, call_node, actual, cell, domain, result_path, &local, depth, null);
        const clean = self.endAttempt(attempt);
        if (!local.complete) output.complete = false;
        for (local.items.items) |item| try self.add(output, item);
        try output.allocations.appendSlice(self.scratch.allocator(), local.allocations.items);
        const bound = frame.invocation != null or cell.frame.invocation != null;
        if (if (bound) clean else self.prunes == prunes) {
            const known = try self.call_effect_certificates.getOrPut(self.scratch.allocator(), node);
            if (!known.found_existing) known.value_ptr.* = .empty;
            try known.value_ptr.append(self.scratch.allocator(), .{
                .frame = frame,
                .node = node,
                .cell = cell,
                .domain = domain,
                .result_path = result_path,
                .selected_formal = self.selected_formal,
                .seeded = seeded,
                .complete = local.complete,
                .items = local.items.items,
                .allocations = local.allocations.items,
                .copies = try self.scratch.allocator().dupe(CopiedPayload, self.copied_payloads.items[copies..]),
            });
        }
    }

    /// The call's whole-callee effect verdict. It does not depend on the
    /// demanded cell, so every cell and horizon asked about this call shares
    /// one proof; a failed proof (budget, cancellation) is never recorded.
    fn wholeEffect(self: *Query, frame: Frame, node: Ast.Node.Index, call_node: TypeResolver.CallOperands, canonical: FileCache.ActualCallSummary) Error!?call_summary.Effect {
        const known = try self.memo.whole_effects.getOrPut(self.scratch.allocator(), node);
        if (!known.found_existing) known.value_ptr.* = .empty;
        for (known.value_ptr.items) |entry| {
            if (entry.cache == frame.cache and entry.declaration == frame.declaration and
                sameResolution(entry.resolution, frame.resolution) and sameActual(entry.actual, canonical))
            {
                try self.charge();
                return entry.effect;
            }
        }
        const effect = try call_summary.callEffectAt(frame.cache, call_node.queryToken(frame.cache.tree, node), .{ .whole = canonical.callee }, .{
            .frame = frame.resolution,
            .remaining = self.remaining,
            .declaration = frame.declaration,
        });
        const finished = self.memo.whole_effects.getPtr(node).?;
        try finished.append(self.scratch.allocator(), .{ .cache = frame.cache, .declaration = frame.declaration, .resolution = frame.resolution, .actual = canonical, .effect = effect });
        return effect;
    }

    /// `&local` or `local[a..b]` of a pointer-free local other than the root of
    /// `cell`. Through it a callee reaches only that local's scalar bytes.
    fn privateLocal(self: *Query, frame: Frame, argument: Ast.Node.Index, cell: SourceCell) Error!bool {
        try self.charge();
        const tree = frame.cache.tree;
        var operand = argument;
        switch (tree.nodeTag(argument)) {
            .address_of => operand = tree.nodeData(argument).node,
            .slice_open, .slice, .slice_sentinel => operand = tree.fullSlice(argument).?.ast.sliced,
            else => return false,
        }
        if (tree.nodeTag(operand) != .identifier) return false;
        const token = tree.nodeMainToken(operand);
        const binding = (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) orelse return false;
        if (binding.origin == .loop_capture or binding.name_token == cell.binding.name_token) return false;
        const ty = (try self.nodeType(frame, operand)) orelse return false;
        return self.addressFree(ty, 0);
    }

    /// Implicit one-pointer argument coercion addresses the actual header.
    /// An authenticated private scalar header cannot reach another cell.
    fn privateActual(self: *Query, frame: Frame, argument: Ast.Node.Index, formal: TypeResolver.ActualType, cell: SourceCell) Error!bool {
        if (try self.privateLocal(frame, argument, cell)) return true;
        const parameter = (try self.canonicalType(formal)) orelse return false;
        if (try self.pointerSize(parameter) != .one) return false;
        const child = (try self.canonicalType(self.resolver.childType(parameter) orelse return false)) orelse return false;
        if (!try self.addressFree(child, 0)) return false;
        const argument_type = (try self.canonicalType((try self.nodeType(frame, argument)) orelse return false)) orelse return false;
        if (!argument_type.eql(child)) return false;
        const actual = (try self.sourceCell(frame, argument, null, 0)) orelse return false;
        if (actual.binding.origin == .param or actual.binding.origin == .loop_capture) return false;
        return !try self.cellsOverlap(actual, cell);
    }

    /// Type-only certificate that none of the selected formals exposes a
    /// writable destination or an address-valued scalar. Pointer destinations,
    /// including scalar pointees that can receive encoded bits, need body proof.
    fn formalsCannotDeposit(self: *Query, function: anytype, formals: []const u32) Error!bool {
        for (formals) |formal| {
            try self.charge();
            const parameter_type = function.parameters[formal].type;
            if (try self.addressFree(parameter_type, 0)) return false;
            if (!try self.depositFree(parameter_type, 0)) return false;
        }
        return true;
    }

    /// A type-only no-deposit proof. Every pointer needs a body-level proof:
    /// pointer-free pointees can still receive encoded addresses, and a
    /// callee can cast away pointer qualifiers before a store.
    ///
    /// The property is universal over the finite set of types reachable from
    /// `value`, so a type met again inside its own open walk (`union { rest:
    /// []const Self }`) adds no new pointer: the open walk already checks
    /// every pointer it reaches. Only a cut-off, never a cycle, is unknown.
    fn depositFree(self: *Query, value: TypeResolver.ActualType, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 16) {
            self.cutoffs += 1;
            return false;
        }
        if (self.memo.deposit_free.get(value)) |known| return known;
        for (self.deposit_open.items) |open| {
            try self.charge();
            if (open.eql(value)) {
                self.deposit_cycles += 1;
                return true;
            }
        }
        try self.deposit_open.append(self.scratch.allocator(), value);
        errdefer self.deposit_open.items.len -= 1;
        const cutoffs = self.cutoffs;
        const cycles = self.deposit_cycles;
        const answer = try self.depositFreeWalk(value, depth);
        const outermost = self.deposit_open.items.len == 1;
        // A positive answer that leaned on an open walk is valid only once that
        // walk finishes positive; a negative one never leaned on an assumption.
        if (self.cutoffs == cutoffs and (!answer or outermost or self.deposit_cycles == cycles))
            try self.memo.deposit_free.put(self.scratch.allocator(), value, answer);
        self.deposit_open.items.len -= 1;
        return answer;
    }

    fn depositFreeWalk(self: *Query, value: TypeResolver.ActualType, depth: u32) Error!bool {
        const ty = (try self.canonicalType(value)) orelse return false;
        const tag = self.resolver.typeTag(ty) orelse return false;
        switch (tag) {
            .int, .float, .bool, .@"enum", .void, .noreturn, .null, .error_set, .comptime_int, .comptime_float => return true,
            .optional, .array, .vector, .error_union => {
                const child = self.resolver.childType(ty) orelse return false;
                return self.depositFree(child, depth + 1);
            },
            // Pointer-free pointees can still receive encoded addresses.
            // Const can be cast away, so only the canonical body effect,
            // not the pointer's shape, proves that no deposit occurs.
            .pointer => return false,
            .@"struct", .@"union" => {
                if (ty.data != .container) return false;
                const container = ty.data.container;
                const field_frame = self.resolver.frameForContainer(container);
                const tree = &container.scope_handle.handle.document.tree;
                var buffer: [2]Ast.Node.Index = undefined;
                const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return false;
                for (declaration.ast.members) |member| {
                    try self.charge();
                    const container_field = tree.fullContainerField(member) orelse continue;
                    const node = container_field.ast.type_expr.unwrap() orelse return false;
                    try self.charge();
                    const field_type = (try field_frame.typeOfNode(node)) orelse return false;
                    if (!try self.depositFree(field_type, depth + 1)) return false;
                }
                return true;
            },
            else => return false,
        }
    }

    /// The resolved call stores no pointer into any caller-visible memory:
    /// scalar formals receive no address bits and every mutable pointer
    /// reachable from the other formals targets pointer-free storage.
    fn eventCannotDeposit(self: *Query, frame: Frame, node: Ast.Node.Index, call_node: TypeResolver.CallOperands, depth: u32) Error!bool {
        const actual = (try frame.cache.actualCallSummaryAt(call_node.queryToken(frame.cache.tree, node), frame.resolution)) orelse return false;
        const function = switch (actual.callee.reference.actual_type.data) {
            .function => |function| function,
            else => return false,
        };
        // A callee whose whole body only reads, through any formal or global,
        // stores nothing anywhere.
        if (try self.wholeEffect(frame, node, call_node, actual) == .read_only) return true;
        for (function.parameters, 0..) |parameter, index| {
            try self.charge();
            if (try self.addressFree(parameter.type, 0)) {
                var buffer: [2]Ast.Node.Index = undefined;
                const argument = (try actual.callArgumentFor(frame.cache, &buffer, @intCast(index))) orelse return false;
                if (try self.hasAddressBits(frame, argument, depth + 1)) return false;
                continue;
            }
            if (!try self.depositFree(parameter.type, 0)) return false;
        }
        return true;
    }

    fn callEffectsScan(self: *Query, frame: Frame, node: Ast.Node.Index, call_node: TypeResolver.CallOperands, actual: ?FileCache.ActualCallSummary, cell: SourceCell, domain: Domain, result_path: []const u8, output: *Output, depth: u32, prepared: ?Frame) Error!void {
        var reaches = false;
        if (actual) |canonical| {
            const function = canonical.callee.reference.actual_type.data.function;
            // Read the declared meta-type in this canonical callable's frame.
            // Its instantiated return_value can instead be the returned
            // container type itself, which is not the universe `type`.
            var proto_buffer: [1]Ast.Node.Index = undefined;
            if (tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration)) |proto| {
                if (proto.ast.return_type.unwrap()) |returned| {
                    const resolution = self.resolver.frameForFunction(canonical.callee.reference);
                    try self.charge();
                    if (try resolution.resolveValueOfNode(returned)) |result|
                        if (result.is_type_val and self.resolver.typeTag(result) == .type) return;
                }
            }
            // Type arguments cannot carry physical storage. This is the same
            // exclusion as the formal walk below, without first traversing a
            // metadata helper's otherwise irrelevant mutation body.
            var types_only = true;
            for (function.parameters) |parameter| {
                try self.charge();
                if (self.resolver.typeTag(parameter.type) != .type) {
                    types_only = false;
                    break;
                }
            }
            if (types_only) return;
            // Readonly calls need no actual payload projection. In particular,
            // do not load unknown actual cells merely to exclude a known
            // readonly call: that work can recursively rescan those cells.
            if (try self.wholeEffect(frame, node, call_node, canonical) == .read_only) return;
            var reaching: std.ArrayListUnmanaged(u32) = .empty;
            for (function.parameters, 0..) |parameter, index| {
                try self.charge();
                if (try self.canonicalType(parameter.type)) |declared|
                    if (self.resolver.typeTag(declared) == .type) continue;
                var buffer: [2]Ast.Node.Index = undefined;
                const argument = (try canonical.callArgumentFor(frame.cache, &buffer, @intCast(index))) orelse {
                    output.complete = false;
                    continue;
                };
                if (try self.addressFree(parameter.type, 0) and !try self.hasAddressBits(frame, argument, depth + 1)) continue;
                // A pointer to another pointer-free local lets the callee write
                // scalars into that local only; it names no storage of `cell`.
                if (try self.privateActual(frame, argument, parameter.type, cell)) continue;
                // Different lexical roots are not a reachable-storage
                // separation proof: aggregates can carry this cell's
                // address. Inspect the body instead of skipping it.
                try reaching.append(self.scratch.allocator(), @intCast(index));
                reaches = true;
            }
            if (!reaches) return;
            // The formals that could carry the cell are never written through
            // and nothing outside the formals is written: the call cannot
            // store into `cell` (it may still write its other, private actuals).
            if (try self.formalsCannotDeposit(function, reaching.items)) return;
            if (prepared == null) {
                const fresh = @import("fresh_storage.zig");
                if (try fresh.allocatorPrimitive(frame.cache, canonical, .{
                    .claim = .{ .first = frame.cache.tree.firstToken(node), .last = frame.cache.tree.lastToken(node) },
                    .depth = 0,
                    .remaining = self.remaining,
                    .frame = frame.resolution,
                })) |_| return;
            }
            var callee = if (prepared) |value| value else (try self.invocationFrame(frame, canonical)) orelse {
                output.complete = false;
                return;
            };
            callee.domain = domain;
            try self.effectsFor(callee, cell, callee.cache.tree.lastToken(callee.body), domain, result_path, output, depth + 1);
            if (domain == .normal) {
                for (frame.caught_errors) |caught| {
                    try self.charge();
                    const tree = frame.cache.tree;
                    if (tree.firstToken(node) < tree.firstToken(caught) or tree.lastToken(node) > tree.lastToken(caught)) continue;
                    var failure_caller = frame;
                    failure_caller.domain = .failure;
                    const failure = (try self.invocationFrame(failure_caller, canonical)) orelse {
                        output.complete = false;
                        break;
                    };
                    // Error-only cleanup is queried separately. It contributes
                    // to a normal caller only where an error is caught.
                    try self.effectsFor(failure, cell, failure.cache.tree.lastToken(failure.body), .failure, result_path, output, depth + 1);
                    break;
                }
            }
        } else {
            for (call_node.ast.params) |argument| {
                try self.charge();
                const ty = try self.nodeType(frame, argument);
                if (ty != null and try self.addressless(frame, argument, ty.?, depth + 1)) continue;
                // A copied wrapper can retain this cell through any pointer
                // field. Its own lexical root is not a reachability proof.
                output.complete = false;
            }
            // The unresolved receiver may be absent from explicit operands.
            if (frame.cache.tree.nodeTag(call_node.ast.fn_expr) == .field_access) {
                const receiver = frame.cache.tree.nodeData(call_node.ast.fn_expr).node_and_token[0];
                const ty = try self.nodeType(frame, receiver);
                if (ty == null or !try self.addressless(frame, receiver, ty.?, depth + 1)) output.complete = false;
            }
        }
    }

    /// Resolve physical global header identity with the same caller scope used
    /// by sourceAt. Distinct header declarations do not alias one another.
    fn globalDeclaration(self: *Query, frame: Frame, node: Ast.Node.Index, depth: u32) Error!?Ast.Node.Index {
        try self.charge();
        if (depth >= depth_limit) return self.depthExhausted(depth);
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .grouped_expression, .unwrap_optional => return self.globalDeclaration(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            .field_access, .array_access => {
                const base = if (tree.nodeTag(node) == .field_access) tree.nodeData(node).node_and_token[0] else tree.nodeData(node).node_and_node[0];
                const ty = if (try self.nodeType(frame, base)) |value| try self.canonicalType(value) else null;
                const value = ty orelse return null;
                // Only inline aggregate headers inherit a physical root.
                // Pointer and slice element/field writes can alias elsewhere.
                if (try self.pointerSize(value) != null) return null;
                const tag = self.resolver.typeTag(value) orelse return null;
                if (tree.nodeTag(node) == .array_access) {
                    if (tag != .array) return null;
                } else if (tag != .@"struct" and tag != .@"union") return null;
                return self.globalDeclaration(frame, base, depth + 1);
            },
            .identifier => {},
            else => return null,
        }
        const token = tree.nodeMainToken(node);
        const declaration = (try self.resolver.analyser.lookupSymbolGlobal(
            frame.resolution.handle,
            tree.tokenSlice(token),
            tree.tokenStart(token),
        )) orelse return null;
        if (&declaration.handle.document.tree != tree or declaration.handle.module != frame.cache.module_id) return null;
        const declared = switch (declaration.decl) {
            .ast_node => |value| value,
            else => return null,
        };
        if (tree.fullVarDecl(declared) == null or tokens.enclosingFnDecl(tree, tree.firstToken(declared)) != null) return null;
        return declared;
    }

    /// Static cells can hold callbacks without lending data storage. Other
    /// pointer payloads can reach mutable cells whose contents are runtime;
    /// a static outer address alone does not certify those deep pointees.
    fn staticCellPayload(self: *Query, value: TypeResolver.ActualType, depth: u32) Error!bool {
        try self.charge();
        if (depth >= depth_limit) return self.depthExhausted(depth);
        const ty = (try self.canonicalType(value)) orelse return false;
        const tag = self.resolver.typeTag(ty) orelse return false;
        switch (tag) {
            .pointer => {
                const child = (try self.canonicalType(self.resolver.childType(ty) orelse return false)) orelse return false;
                return self.resolver.typeTag(child) == .@"fn";
            },
            .optional, .array, .vector => {
                const child = self.resolver.childType(ty) orelse return false;
                return self.staticCellPayload(child, depth + 1);
            },
            .@"struct" => {
                if (ty.data != .container) return false;
                const container = ty.data.container;
                const field_frame = self.resolver.frameForContainer(container);
                const tree = &container.scope_handle.handle.document.tree;
                var buffer: [2]Ast.Node.Index = undefined;
                const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return false;
                for (declaration.ast.members) |member| {
                    try self.charge();
                    const container_field = tree.fullContainerField(member) orelse continue;
                    const node = container_field.ast.type_expr.unwrap() orelse return false;
                    const field_type = (try field_frame.typeOfNode(node)) orelse return false;
                    if (!try self.staticCellPayload(field_type, depth + 1)) return false;
                }
                return true;
            },
            else => return self.addressFree(ty, depth + 1),
        }
    }

    /// A comptime initializer gives an immutable local static storage. A
    /// runtime `var` still has a frame cell even if its initial value is
    /// computed at comptime; do not confuse the value with its storage.
    fn explicitComptimeCell(self: *Query, frame: Frame, binding: *const bindings_mod.Binding) Error!bool {
        try self.charge();
        if (!binding.is_const or binding.origin == .param or binding.origin == .loop_capture) return false;
        const tree = frame.cache.tree;
        var initializer = frame.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
        for (0..depth_limit) |_| {
            try self.charge();
            if (tree.nodeTag(initializer) != .grouped_expression)
                return tree.nodeTag(initializer) == .@"comptime";
            initializer = tree.nodeData(initializer).node_and_token[0];
        }
        return false;
    }

    fn globalCellAddress(self: *Query, frame: Frame, node: Ast.Node.Index) Error!bool {
        try self.charge();
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) != .identifier) return false;
        const token = tree.nodeMainToken(node);
        if (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) |binding| {
            if (!try self.explicitComptimeCell(frame, binding)) return false;
            if (self.selected_formal != null) return true;
            const ty = (try self.nodeType(frame, node)) orelse return false;
            return self.staticCellPayload(ty, 0);
        }
        const declaration = (try self.resolver.analyser.lookupSymbolGlobal(
            frame.resolution.handle,
            tree.tokenSlice(token),
            tree.tokenStart(token),
        )) orelse return false;
        if (&declaration.handle.document.tree != tree or
            declaration.handle.module != frame.cache.module_id) return false;
        const declared = switch (declaration.decl) {
            .ast_node => |value| value,
            else => return false,
        };
        const variable = tree.fullVarDecl(declared) orelse return false;
        // Immutable static cells carry no selected invocation channel. A
        // complete deep-storage answer additionally requires payloads that
        // cannot reach mutable pointer-bearing data.
        if (tree.tokenTag(variable.ast.mut_token) == .keyword_const and
            tokens.enclosingFnDecl(tree, tree.firstToken(declared)) == null)
        {
            if (self.selected_formal != null) return true;
            const ty = (try self.nodeType(frame, node)) orelse return false;
            return self.staticCellPayload(ty, 0);
        }
        for (tree.rootDecls()) |member| {
            try self.charge();
            if (member != declared) continue;
            const ty = (try self.nodeType(frame, node)) orelse return false;
            return self.addressFree(ty, 0);
        }
        return false;
    }

    /// A fresh one-object allocation acquires its graph from a dominating
    /// whole-pointee store, not from the pointer header's initializedness.
    /// Later effects must be resolved separately; this certificate refuses
    /// them rather than treating a fresh outer address as a deep proof.
    fn initializedAllocation(
        self: *Query,
        frame: Frame,
        node: Ast.Node.Index,
        binding: *const bindings_mod.Binding,
        result_path: []const u8,
        output: *Output,
        depth: u32,
    ) Error!bool {
        if (!binding.is_const) return false;
        switch (binding.origin) {
            .call, .method_call, .try_call, .try_method_call => {},
            else => return false,
        }
        const tree = frame.cache.tree;
        if (binding.scope_open != tree.nodeMainToken(frame.body)) return false;
        const ty = (try self.nodeType(frame, node)) orelse return false;
        if (try self.pointerSize(ty) != .one) return false;
        const initial = frame.cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse return false;
        var store: ?Ast.Node.Index = null;
        var statements = Iterator.init(tree, frame.body);
        while (statements.next(tree)) |statement| {
            try self.charge();
            if (tree.nodeTag(statement) != .assign or tree.lastToken(statement) >= frame.return_token) continue;
            const operands = tree.nodeData(statement).node_and_node;
            if (tree.nodeTag(operands[0]) != .deref) continue;
            const pointer = tree.nodeData(operands[0]).node;
            if (tree.nodeTag(pointer) != .identifier) continue;
            const token = tree.nodeMainToken(pointer);
            const destination = (try self.lookupBinding(frame.bindings, tree.tokenSlice(token), token)) orelse continue;
            if (destination.name_token == binding.name_token) store = statement;
        }
        const initialized = store orelse return false;
        for (frame.mutations) |mutation| {
            try self.charge();
            const token = tree.firstToken(mutation);
            if (token > tree.lastToken(initialized) and token < frame.return_token) return false;
        }
        var provider: Output = .{};
        if (!try self.allocationDestination(frame, initial, &provider, depth + 1)) return false;
        var at_store = frame;
        at_store.return_token = tree.firstToken(initialized);
        try self.expression(at_store, tree.nodeData(initialized).node_and_node[1], .value, result_path, output, depth + 1);
        try output.allocations.appendSlice(self.scratch.allocator(), provider.allocations.items);
        return true;
    }

    fn expression(self: *Query, frame: Frame, node: Ast.Node.Index, mode: Mode, result_path: []const u8, output: *Output, depth: u32) Error!void {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            output.complete = false;
            return;
        }
        const tree = frame.cache.tree;
        const tag = tree.nodeTag(node);
        if (tag == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "undefined")) {
            output.complete = false;
            return;
        }
        if (mode == .value) {
            if (try self.nodeType(frame, node)) |ty| {
                if (try self.addressless(frame, node, ty, 0)) return;
            }
        }
        if (tag == .field_access and try self.localBackingAt(frame, node, node, mode, result_path, output, depth + 1)) return;
        var covered: []const Ast.Node.Index = &.{};
        if (try self.invalidated(frame, node)) {
            // A local rewritten whole holds its initializer or one of the
            // values written, so those are the origins; anything else stays
            // unknown.
            covered = (if (tag == .identifier and mode != .location) try self.plainRewrites(frame, node) else null) orelse {
                output.complete = false;
                return;
            };
            for (covered) |write| {
                var at_write = frame;
                at_write.return_token = tree.firstToken(write);
                try self.expression(at_write, tree.nodeData(write).node_and_node[1], mode, result_path, output, depth + 1);
            }
        }
        switch (tag) {
            .@"orelse", .@"catch" => {
                const pair = tree.nodeData(node).node_and_node;
                try self.expression(frame, pair[0], mode, result_path, output, depth + 1);
                if (tree.nodeTag(pair[1]) == .@"return" or
                    (tree.firstToken(pair[1]) == tree.lastToken(pair[1]) and tree.tokenTag(tree.firstToken(pair[1])) == .keyword_unreachable)) return;
                try self.expression(frame, pair[1], mode, result_path, output, depth + 1);
            },
            .@"try" => return self.expression(frame, tree.nodeData(node).node, mode, result_path, output, depth + 1),
            .deref => {
                if (mode != .value) return self.expression(frame, tree.nodeData(node).node, if (mode == .location) .value else mode, result_path, output, depth + 1);
                var source: Output = .{};
                try self.expression(frame, tree.nodeData(node).node, .value, result_path, &source, depth + 1);
                if (!source.complete) output.complete = false;
                if (source.allocations.items.len != 0) output.complete = false;
                const ty = (try self.nodeType(frame, node)) orelse {
                    output.complete = false;
                    return;
                };
                for (source.items.items) |item| try self.payload(ty, item, false, output, 0);
            },
            .grouped_expression, .unwrap_optional => return self.expression(frame, tree.nodeData(node).node_and_token[0], mode, result_path, output, depth + 1),
            // Authenticated globals and explicit-comptime immutable locals
            // have static storage; a runtime local header remains unknown.
            .address_of => {
                var value = tree.nodeData(node).node;
                var peeled: u32 = 0;
                while (peeled < 64) : (peeled += 1) {
                    try self.charge();
                    switch (tree.nodeTag(value)) {
                        .grouped_expression, .unwrap_optional => value = tree.nodeData(value).node_and_token[0],
                        .@"try" => value = tree.nodeData(value).node,
                        else => break,
                    }
                }
                if (peeled == 64) {
                    output.complete = false;
                    return;
                }
                switch (tree.nodeTag(value)) {
                    .identifier => {
                        if (mode == .value and try self.globalCellAddress(frame, value)) return;
                        output.complete = false;
                        return;
                    },
                    .call, .call_one, .call_comma, .call_one_comma => {
                        // An address of a parameter/local header or a temporary
                        // result is not the address held IN that value.
                        output.complete = false;
                        return;
                    },
                    else => {},
                }
                if (try self.emptySliceLiteral(frame, node, value)) return;
                var operand: Output = .{};
                try self.expression(frame, tree.nodeData(node).node, .location, result_path, &operand, depth + 1);
                if (!operand.complete) output.complete = false;
                if (operand.allocations.items.len != 0) output.complete = false;
                for (operand.items.items) |item| {
                    var address = item;
                    address.projection = .cell_address;
                    try self.add(output, address);
                }
            },
            .identifier => {
                const token = tree.nodeMainToken(node);
                const name = tree.tokenSlice(token);
                if (std.mem.eql(u8, name, "null")) return;
                const binding = (try self.lookupBinding(frame.bindings, name, token)) orelse {
                    output.complete = false;
                    return;
                };
                if (mode == .value and try self.initializedAllocation(frame, node, binding, result_path, output, depth + 1)) return;
                if (try self.rebound(frame, binding, token, covered)) {
                    output.complete = false;
                    return;
                }
                if (binding.origin == .param) {
                    const parameter = (try self.formalIndex(frame, binding)) orelse {
                        output.complete = false;
                        return;
                    };
                    if (frame.invocation) |invocation| {
                        var argument_buffer: [2]Ast.Node.Index = undefined;
                        try self.charge();
                        const argument = (try invocation.actual.callArgumentFor(invocation.caller.cache, &argument_buffer, parameter)) orelse {
                            output.complete = false;
                            return;
                        };
                        return self.expression(invocation.caller, argument, mode, result_path, output, depth + 1);
                    }
                    if (self.selected_formal) |selected| {
                        if (parameter != selected) return;
                    }
                    const ty = (try self.nodeType(frame, node)) orelse {
                        output.complete = false;
                        return;
                    };
                    const size = try self.pointerSize(ty);
                    if (mode == .address_bits and size == null) {
                        output.complete = false;
                        return;
                    }
                    if (mode == .location and size == null) {
                        output.complete = false;
                        return;
                    }
                    if (mode == .value and size == null) {
                        if (try self.addressFree(ty, 0) and !try self.addressNarrow(ty, 0)) {
                            try self.add(output, .{
                                .owner = .{ .param = parameter, .path = "" },
                                .result_path = result_path,
                                .projection = .payload_value,
                                .storage = .payload_storage,
                            });
                            return;
                        }
                        return self.payload(ty, .{
                            .owner = .{ .param = parameter, .path = "" },
                            .result_path = result_path,
                            .projection = .payload_value,
                            .storage = .payload_storage,
                        }, true, output, 0);
                    }
                    if (mode == .value) {
                        const canonical = try self.canonicalType(ty);
                        const child = if (canonical) |pointer| self.resolver.childType(pointer) else null;
                        if (child == null or !try self.addressFree(child.?, 0)) output.complete = false;
                    }
                    try self.add(output, .{
                        .owner = .{ .param = parameter, .path = "" },
                        .result_path = result_path,
                        .projection = if (mode == .location) .cell_address else .pointer_value,
                        .storage = if (size == .slice or size == .many or size == .c) .backing_storage else .inline_storage,
                    });
                    return;
                }
                if (!binding.is_const and mode != .location)
                    try self.assignedOrigins(frame, binding, result_path, covered, output, depth + 1);
                if (mode == .location) {
                    const ty = (try self.nodeType(frame, node)) orelse {
                        output.complete = false;
                        return;
                    };
                    if (try self.pointerSize(ty) == null) {
                        output.complete = false;
                        return;
                    }
                }
                const rhs = frame.cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse {
                    output.complete = false;
                    return;
                };
                if (rhs == node) {
                    output.complete = false;
                    return;
                }
                if (binding.origin == .loop_capture) {
                    const rhs_type = try self.nodeType(frame, rhs);
                    const pointer_capture = binding.name_token != 0 and tree.tokenTag(binding.name_token - 1) == .asterisk;
                    if (pointer_capture and mode == .value and rhs_type != null and self.resolver.typeTag(rhs_type.?) != .optional) {
                        // `|*element|` is the address of an element cell of the
                        // iterable's storage, exactly as `&iterable[index]` is.
                        const ty = rhs_type.?;
                        const size = self.resolver.pointerSize(ty);
                        var iterable: Output = .{};
                        try self.expression(frame, rhs, if (size != null) .coordinate else .location, result_path, &iterable, depth + 1);
                        if (!iterable.complete or iterable.allocations.items.len != 0 or iterable.items.items.len == 0) output.complete = false;
                        for (iterable.items.items) |original| {
                            var item = original;
                            const known_address = item.projection == .cell_address;
                            item.projection = .cell_address;
                            if (item.storage != .payload_storage) {
                                item.storage = if (size == .slice or size == .many or size == .c)
                                    .backing_storage
                                else if (self.resolver.typeTag(ty) == .array)
                                    .inline_storage
                                else if (size == .one and item.owner.path.len != 0 and !known_address)
                                    .backing_storage
                                else
                                    item.storage;
                            }
                            try self.add(output, item);
                        }
                        return;
                    }
                    if (rhs_type == null or self.resolver.typeTag(rhs_type.?) != .optional) {
                        // A by-value loop element copies its pointer payload;
                        // the iterable's allocation is not the element pointee.
                        var iterable: Output = .{};
                        try self.expression(frame, rhs, .value, result_path, &iterable, depth + 1);
                        output.complete = false;
                        for (iterable.items.items) |original| {
                            var item = original;
                            item.projection = .payload_value;
                            item.storage = .payload_storage;
                            try self.add(output, item);
                        }
                        return;
                    }
                }
                var at_initializer = frame;
                at_initializer.return_token = binding.rhs_last;
                return self.expression(at_initializer, rhs, mode, result_path, output, depth + 1);
            },
            .field_access => {
                const access = tree.nodeData(node).node_and_token;
                try self.field(frame, node, access[0], tree.tokenSlice(access[1]), mode, result_path, output, depth + 1);
            },
            .array_access => {
                const access = tree.nodeData(node).node_and_node;
                if (mode == .value and try self.scalarCallElement(frame, node, access[0])) return;
                const base = access[0];
                const ty = (try self.nodeType(frame, base)) orelse {
                    output.complete = false;
                    return;
                };
                const size = self.resolver.pointerSize(ty);
                var parent: Output = .{};
                const base_mode: Mode = if (mode == .location) (if (size != null) .coordinate else .location) else .value;
                try self.expression(frame, base, base_mode, result_path, &parent, depth + 1);
                if (!parent.complete) output.complete = false;
                if (parent.allocations.items.len != 0) output.complete = false;
                if (mode == .location and parent.items.items.len == 0) output.complete = false;
                for (parent.items.items) |original| {
                    var item = original;
                    if (mode == .location) {
                        const known_address = item.projection == .cell_address;
                        item.projection = .cell_address;
                        if (item.storage != .payload_storage) {
                            item.storage = if (size == .slice or size == .many or size == .c)
                                .backing_storage
                            else if (self.resolver.typeTag(ty) == .array)
                                .inline_storage
                            else if (size == .one and item.owner.path.len != 0 and !known_address)
                                .backing_storage
                            else
                                item.storage;
                        }
                    } else {
                        const result_type = (try self.nodeType(frame, node)) orelse {
                            output.complete = false;
                            continue;
                        };
                        try self.payload(result_type, item, false, output, 0);
                        continue;
                    }
                    try self.add(output, item);
                }
            },
            .slice_open, .slice, .slice_sentinel => {
                const slice = tree.fullSlice(node).?;
                var parent: Output = .{};
                // Inline arrays lend their coordinates. A slice/pointer
                // instead copies its current header, including prior rewrites.
                const sliced_type = (try self.nodeType(frame, slice.ast.sliced)) orelse {
                    output.complete = false;
                    return;
                };
                const base_mode: Mode = if (self.resolver.typeTag(sliced_type) == .array) .coordinate else .value;
                try self.expression(frame, slice.ast.sliced, base_mode, result_path, &parent, depth + 1);
                if (parent.items.items.len == 0 and parent.complete)
                    try self.expression(frame, slice.ast.sliced, .location, result_path, &parent, depth + 1);
                if (!parent.complete) output.complete = false;
                for (parent.allocations.items) |requirement| {
                    try self.charge();
                    try output.allocations.append(self.scratch.allocator(), requirement);
                }
                const ty = (try self.nodeType(frame, slice.ast.sliced)) orelse {
                    output.complete = false;
                    return;
                };
                for (parent.items.items) |original| {
                    var item = original;
                    if (item.storage != .payload_storage) {
                        item.projection = .pointer_value;
                        item.storage = if (self.resolver.typeTag(ty) == .array) .inline_storage else .backing_storage;
                    }
                    try self.add(output, item);
                }
            },
            .call, .call_one, .call_comma, .call_one_comma => try self.call(frame, node, mode, result_path, output, depth + 1),
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "@call")) return self.call(frame, node, mode, result_path, output, depth + 1);
                if (std.mem.eql(u8, name, "@field")) {
                    var arguments = Iterator.init(tree, node);
                    const base = arguments.next(tree) orelse {
                        output.complete = false;
                        return;
                    };
                    try self.charge();
                    const name_node = arguments.next(tree) orelse {
                        output.complete = false;
                        return;
                    };
                    try self.charge();
                    if (arguments.next(tree) != null) {
                        output.complete = false;
                        return;
                    }
                    try self.charge();
                    const field_name = (try frame.resolution.stringValueOfNode(name_node)) orelse {
                        output.complete = false;
                        return;
                    };
                    return self.field(frame, node, base, field_name, mode, result_path, output, depth + 1);
                }
                // Zig owns the tag-name bytes for the program lifetime. The
                // value selects static storage; it does not lend its enum cell.
                if (mode == .value and std.mem.eql(u8, name, "@tagName")) return;
                if (mode == .value and (std.mem.eql(u8, name, "@inComptime") or
                    std.mem.eql(u8, name, "@setEvalBranchQuota"))) return;
                if (mode == .value and std.mem.eql(u8, name, "@splat")) {
                    var buffer: [2]Ast.Node.Index = undefined;
                    const arguments = tree.builtinCallParams(&buffer, node) orelse {
                        output.complete = false;
                        return;
                    };
                    if (arguments.len != 1) {
                        output.complete = false;
                        return;
                    }
                    return self.expression(frame, arguments[0], .value, result_path, output, depth + 1);
                }
                const cast = std.mem.eql(u8, name, "@ptrCast") or std.mem.eql(u8, name, "@alignCast") or
                    std.mem.eql(u8, name, "@constCast") or std.mem.eql(u8, name, "@volatileCast") or
                    std.mem.eql(u8, name, "@as");
                const bits = std.mem.eql(u8, name, "@intFromPtr") or std.mem.eql(u8, name, "@ptrFromInt");
                if (!cast and !bits and mode == .value and valueBuiltin(name)) {
                    var buffer: [2]Ast.Node.Index = undefined;
                    const arguments = tree.builtinCallParams(&buffer, node) orelse {
                        output.complete = false;
                        return;
                    };
                    for (arguments) |argument| {
                        if (try frame.resolution.resolveValueOfNode(argument)) |value|
                            if (value.is_type_val) continue;
                        try self.expression(frame, argument, .value, result_path, output, depth + 1);
                    }
                    return;
                }
                if (!cast and !bits) {
                    output.complete = false;
                    return;
                }
                var children = Iterator.init(tree, node);
                var last: ?Ast.Node.Index = null;
                while (children.next(tree)) |child| {
                    try self.charge();
                    last = child;
                }
                const operand = last orelse {
                    output.complete = false;
                    return;
                };
                var operand_result: Output = .{};
                try self.expression(frame, operand, if (bits) .address_bits else mode, result_path, &operand_result, depth + 1);
                if (!operand_result.complete or (bits and operand_result.items.items.len == 0)) output.complete = false;
                for (operand_result.allocations.items) |requirement| {
                    try self.charge();
                    try output.allocations.append(self.scratch.allocator(), requirement);
                }
                for (operand_result.items.items) |item| try self.add(output, item);
            },
            .add, .sub, .mul, .bit_or, .bit_and, .bit_xor, .shl, .shr => {
                if (mode == .location or mode == .coordinate) {
                    const result_type = (try self.nodeType(frame, node)) orelse {
                        output.complete = false;
                        return;
                    };
                    if (try self.pointerSize(result_type) == null) {
                        output.complete = false;
                        return;
                    }
                }
                var children = Iterator.init(tree, node);
                while (children.next(tree)) |child| {
                    try self.charge();
                    // Numeric offsets contribute no storage; pointer-to-int
                    // operands retain their canonical source path.
                    if (tree.nodeTag(child) == .number_literal) continue;
                    if (try self.nodeType(frame, child)) |ty| {
                        if (try self.addressless(frame, child, ty, 0)) continue;
                    }
                    try self.expression(frame, child, if (mode == .address_bits) .address_bits else .value, result_path, output, depth + 1);
                }
            },
            .@"if", .if_simple => {
                const conditional = tree.fullIf(node).?;
                try self.charge();
                const known = try frame.resolution.boolValueOfNode(conditional.ast.cond_expr);
                if (known) |condition| {
                    if (condition) return self.expression(frame, conditional.ast.then_expr, mode, result_path, output, depth + 1);
                    if (conditional.ast.else_expr.unwrap()) |other|
                        return self.expression(frame, other, mode, result_path, output, depth + 1);
                    output.complete = false;
                    return;
                }
                try self.expression(frame, conditional.ast.then_expr, mode, result_path, output, depth + 1);
                if (conditional.ast.else_expr.unwrap()) |other| {
                    try self.expression(frame, other, mode, result_path, output, depth + 1);
                } else output.complete = false;
            },
            // A switch yields one prong's value, so its storage is the union of
            // its prongs. A labeled switch can loop back with `continue`, and a
            // payload capture binds storage this walk does not follow: both
            // stay unknown. Prongs that never produce a value contribute none.
            .@"switch", .switch_comma => {
                const selection = tree.fullSwitch(node) orelse {
                    output.complete = false;
                    return;
                };
                if (selection.label_token != null) output.complete = false;
                for (selection.ast.cases) |case_node| {
                    try self.charge();
                    const prong = tree.fullSwitchCase(case_node) orelse {
                        output.complete = false;
                        continue;
                    };
                    const target = prong.ast.target_expr;
                    if (tree.nodeTag(target) == .@"return" or
                        (tree.firstToken(target) == tree.lastToken(target) and tree.tokenTag(tree.firstToken(target)) == .keyword_unreachable)) continue;
                    if (prong.payload_token != null) output.complete = false;
                    try self.expression(frame, target, mode, result_path, output, depth + 1);
                }
            },
            .number_literal, .char_literal, .enum_literal, .error_value => {},
            // The bytes of a string literal are static constant memory: its
            // value borrows no storage. Its own cell has no stable address.
            .string_literal, .multiline_string_literal => {
                if (mode == .location) output.complete = false;
            },
            else => {
                var buffer: [2]Ast.Node.Index = undefined;
                if (try self.arrayLiteral(frame, node, &buffer)) |literal| {
                    if (!literal.complete or (mode == .location and literal.elements.len != 0)) output.complete = false;
                    // Element payloads carry loans, not positional field paths.
                    for (literal.elements) |element| {
                        try self.charge();
                        try self.expression(frame, element, .value, result_path, output, depth + 1);
                    }
                } else if (tree.fullStructInit(&buffer, node)) |literal| {
                    const defaults = try self.literalDefaults(frame, node, literal.ast.fields, depth + 1);
                    if (!defaults.complete) output.complete = false;
                    for (defaults.fields.items) |default_field| {
                        const path = try self.join(result_path, default_field.name);
                        try self.expression(default_field.source.frame, default_field.source.node, .value, path, output, depth + 1);
                    }
                    for (literal.ast.fields) |member_node| {
                        try self.charge();
                        const first = tree.firstToken(member_node);
                        const tags = tree.tokens.items(.tag);
                        if (first < 3 or tags[first - 1] != .equal or tags[first - 2] != .identifier or tags[first - 3] != .period) {
                            output.complete = false;
                            continue;
                        }
                        const path = try self.join(result_path, tree.tokenSlice(first - 2));
                        try self.expression(frame, member_node, .value, path, output, depth + 1);
                    }
                } else output.complete = false;
            },
        }
    }

    fn field(self: *Query, frame: Frame, node: Ast.Node.Index, base: Ast.Node.Index, name: []const u8, mode: Mode, result_path: []const u8, output: *Output, depth: u32) Error!void {
        var parent: Output = .{};
        try self.expression(frame, base, if (mode == .location) .location else .coordinate, result_path, &parent, depth + 1);
        if (!parent.complete) output.complete = false;
        for (parent.allocations.items) |requirement| {
            try self.charge();
            try output.allocations.append(self.scratch.allocator(), requirement);
        }
        const ty = try self.nodeType(frame, node);
        if (ty == null and mode != .coordinate and mode != .location) output.complete = false;
        const base_type = try self.nodeType(frame, base);
        const slice_pointer = if (base_type) |value| self.resolver.pointerSize(value) == .slice and std.mem.eql(u8, name, "ptr") else false;
        for (parent.items.items) |original| {
            var item = original;
            if (item.result_path.len != result_path.len) {
                if (mode == .location) {
                    output.complete = false;
                    continue;
                }
                const selected = try self.join(result_path, name);
                if (!std.mem.eql(u8, item.result_path, selected) and
                    !(std.mem.startsWith(u8, item.result_path, selected) and item.result_path.len > selected.len and item.result_path[selected.len] == '.')) continue;
                item.result_path = if (item.result_path.len == selected.len) result_path else try self.join(result_path, item.result_path[selected.len + 1 ..]);
            } else {
                if (!slice_pointer) item.owner.path = try self.join(item.owner.path, name);
                if (mode == .coordinate) {
                    if (ty) |field_type| {
                        if (try self.pointerSize(field_type) != null) {
                            // Selecting a stored pointer copies its payload;
                            // it does not address the enclosing carrier cell.
                            item.projection = .pointer_value;
                            item.storage = .backing_storage;
                        }
                    }
                }
                if (mode == .value or mode == .address_bits) {
                    const field_type = ty orelse {
                        output.complete = false;
                        continue;
                    };
                    const field_size = try self.pointerSize(field_type);
                    if (mode == .address_bits and field_size == null) {
                        output.complete = false;
                        continue;
                    }
                    if (mode == .value and field_size == null and try self.addressFree(field_type, 0) and
                        !try self.addressNarrow(field_type, 0))
                    {
                        // Copied wide scalar fields can contain encoded actual
                        // addresses. Numeric origin proofs, not shape alone,
                        // may remove their caller-bound payload channel.
                        item.projection = .payload_value;
                        item.storage = .payload_storage;
                        try self.add(output, item);
                        continue;
                    }
                    if ((mode == .value and field_size == null) or field_size == .one) {
                        try self.payload(field_type, item, true, output, 0);
                        continue;
                    }
                    item.projection = .pointer_value;
                    item.storage = .backing_storage;
                }
            }
            try self.add(output, item);
        }
    }

    fn formalIndex(self: *Query, frame: Frame, binding: *const bindings_mod.Binding) Error!?u32 {
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(frame.cache.tree, &buffer, frame.declaration) orelse return null;
        var parameters = proto.iterate(frame.cache.tree);
        var index: u32 = 0;
        while (parameters.next()) |parameter| : (index += 1) {
            try self.charge();
            if (parameter.name_token) |name| {
                if (name == binding.name_token) return index;
            }
        }
        return null;
    }

    fn allocationOrigin(self: *Query, frame: Frame, allocator: Ast.Node.Index, output: *Output, depth: u32) Error!void {
        try self.charge();
        if (depth >= 64) {
            self.cutoffs += 1;
            output.complete = false;
            return;
        }
        // Bind only the provider actually used at this allocation. A formal
        // field overwritten in the body cannot reuse its caller's old value.
        if (try self.invalidated(frame, allocator)) {
            output.complete = false;
            return;
        }
        if (try self.sourceAt(frame, allocator, "", depth + 1)) |source| {
            if (source.frame.cache.tree != frame.cache.tree or source.node != allocator or source.frame.invocation != frame.invocation) {
                const start = output.allocations.items.len;
                try self.allocationOrigin(source.frame, source.node, output, depth + 1);
                for (output.allocations.items[start..]) |*requirement| {
                    if (requirement.source == null) requirement.source = source;
                }
                return;
            }
        }
        const walk: @import("fresh_storage.zig").FreshWalk = .{
            .claim = .{ .first = frame.cache.tree.firstToken(allocator), .last = frame.cache.tree.lastToken(allocator) },
            .depth = 0,
            .remaining = self.remaining,
            .frame = frame.resolution,
        };
        if (try self.syntaxPath(frame, allocator, 0)) |path| {
            if (path.binding.origin == .param) {
                const parameter = (try self.formalIndex(frame, path.binding)) orelse {
                    output.complete = false;
                    return;
                };
                if (self.selected_formal) |selected| {
                    if (selected == parameter) output.complete = false;
                } else {
                    try output.allocations.append(self.scratch.allocator(), .{ .allocator = .{ .param = parameter, .path = path.path } });
                }
                return;
            }
        }
        if (!try @import("fresh_storage.zig").allocatorOriginIsExternal(frame.cache, allocator, walk, 0))
            output.complete = false;
    }

    fn allocationPointee(self: *Query, initial: TypeResolver.ActualType) Error!?TypeResolver.ActualType {
        var ty = initial;
        for (0..32) |_| {
            try self.charge();
            ty = (try self.canonicalType(ty)) orelse return null;
            const tag = self.resolver.typeTag(ty) orelse return null;
            switch (tag) {
                .optional, .error_union => ty = self.resolver.childType(ty) orelse return null,
                .pointer => return self.resolver.childType(ty),
                else => return null,
            }
        }
        return null;
    }

    /// A symbolic field has no unique value node, but its provider coordinate
    /// still names the same formal field. Keep that requirement symbolic until
    /// an actual caller supplies its provider; never treat it as independent.
    fn allocationProjectionOrigin(self: *Query, frame: Frame, allocator: Ast.Node.Index, path: []const u8, output: *Output, depth: u32) Error!void {
        if (path.len == 0) return self.allocationOrigin(frame, allocator, output, depth);
        if (try self.sourceAt(frame, allocator, path, depth + 1)) |source|
            return self.allocationOrigin(source.frame, source.node, output, depth + 1);
        var projected = (try self.syntaxPath(frame, allocator, depth + 1)) orelse {
            output.complete = false;
            return;
        };
        if (frame.invocation != null or projected.binding.origin != .param) {
            output.complete = false;
            return;
        }
        projected.path = try self.join(projected.path, path);
        if (try self.invalidatedPath(frame, projected)) {
            output.complete = false;
            return;
        }
        const parameter = (try self.formalIndex(frame, projected.binding)) orelse {
            output.complete = false;
            return;
        };
        if (self.selected_formal) |selected| {
            if (selected == parameter) output.complete = false;
        } else {
            try output.allocations.append(self.scratch.allocator(), .{ .allocator = .{ .param = parameter, .path = projected.path } });
        }
    }

    fn call(self: *Query, frame: Frame, node: Ast.Node.Index, _: Mode, result_path: []const u8, output: *Output, depth: u32) Error!void {
        var buffer: [2]Ast.Node.Index = undefined;
        const ast_call = TypeResolver.CallOperands.full(frame.cache.tree, &buffer, node) orelse {
            output.complete = false;
            return;
        };
        try self.charge();
        const actual = (try frame.cache.actualCallSummaryAt(ast_call.queryToken(frame.cache.tree, node), frame.resolution)) orelse {
            output.complete = false;
            return;
        };
        const fresh = @import("fresh_storage.zig");
        const walk: fresh.FreshWalk = .{
            .claim = .{ .first = frame.cache.tree.firstToken(node), .last = frame.cache.tree.lastToken(node) },
            .depth = 0,
            .remaining = self.remaining,
            .frame = frame.resolution,
        };
        if (try fresh.allocatorPrimitive(frame.cache, actual, walk)) |primitive| {
            if (primitive.operation == .allocate) {
                if (try self.nodeType(frame, node)) |ty| {
                    if (try self.allocationPointee(ty)) |child| {
                        if (try self.addressFree(child, 0)) {
                            var allocator_buffer: [2]Ast.Node.Index = undefined;
                            const allocator = (try actual.callArgumentFor(frame.cache, &allocator_buffer, primitive.allocator_parameter)) orelse {
                                output.complete = false;
                                return;
                            };
                            try self.allocationOrigin(frame, allocator, output, depth + 1);
                            return;
                        }
                    }
                }
            }
            if (primitive.operation == .replace) {
                var previous_buffer: [2]Ast.Node.Index = undefined;
                const previous = (try actual.callArgumentFor(frame.cache, &previous_buffer, primitive.previous_parameter orelse {
                    output.complete = false;
                    return;
                })) orelse {
                    output.complete = false;
                    return;
                };
                // Remap's successful value may still carry the old backing.
                // Allocator identity never clears that positive alternative.
                return self.expression(frame, previous, .value, result_path, output, depth + 1);
            }
        }
        if (self.selected_formal != null) {
            // A read-only call with an independent returned value cannot keep
            // any input address. Both proofs are required: an empty return
            // alone says nothing about outward stores or unknown effects.
            if (try self.wholeEffect(frame, node, ast_call, actual) == .read_only) {
                const independent = independent: {
                    const selected = self.selected_formal;
                    self.selected_formal = null;
                    defer self.selected_formal = selected;
                    const returned = try self.body(frame.cache, actual, depth + 1);
                    break :independent returned.storage.complete and returned.storage.alternatives.len == 0 and
                        returned.allocations.len == 0;
                };
                if (independent) return;
            }
            // Demand only the selected channel. Unknown deep result storage
            // from other actuals cannot reintroduce this formal after a proved
            // detach. Each tainted canonical formal still needs its own proof.
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(actual.callee.tree, &proto_buffer, actual.callee.declaration) orelse {
                output.complete = false;
                return;
            };
            var parameters = proto.iterate(actual.callee.tree);
            var parameter: u32 = 0;
            while (parameters.next() != null) : (parameter += 1) {
                try self.charge();
                const formals = actual.callee.reference.actual_type.data.function.parameters;
                if (parameter >= formals.len) {
                    output.complete = false;
                    return;
                }
                const formal = formals[parameter];
                if (try self.canonicalType(formal.type)) |declared|
                    if (self.resolver.typeTag(declared) == .type) continue;
                var argument_buffer: [2]Ast.Node.Index = undefined;
                const argument = (try actual.callArgumentFor(frame.cache, &argument_buffer, parameter)) orelse {
                    output.complete = false;
                    return;
                };
                var channel: Output = .{};
                var at_call = frame;
                at_call.return_token = frame.cache.tree.firstToken(node);
                try self.expression(at_call, argument, .value, "", &channel, depth + 1);
                if (!channel.complete) output.complete = false;
                if (channel.items.items.len != 0 and !try self.formalBody(frame.cache, actual, parameter, depth + 1))
                    output.complete = false;
                if (!output.complete) return;
            }
            return;
        }
        const selected = self.selected_formal;
        self.selected_formal = null;
        const symbolic = self.body(frame.cache, actual, depth) catch |err| {
            self.selected_formal = selected;
            return err;
        };
        self.selected_formal = selected;
        const returned = symbolic.storage;
        for (symbolic.allocations) |requirement| {
            try self.charge();
            var allocator_buffer: [2]Ast.Node.Index = undefined;
            const allocator = (try actual.callArgumentFor(frame.cache, &allocator_buffer, requirement.allocator.param)) orelse {
                output.complete = false;
                continue;
            };
            try self.allocationProjectionOrigin(frame, allocator, requirement.allocator.path, output, depth + 1);
        }
        if (!returned.complete) output.complete = false;
        for (returned.alternatives) |alternative| {
            try self.charge();
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const mapped = (try mappedStorageAt(frame.cache, actual, alternative, &argument_buffer)) orelse {
                output.complete = false;
                continue;
            };
            // Project an actual private source cell before copying formal
            // coordinates. This binds allocator requirements at the caller.
            if (alternative.projection != .cell_address and mapped.path.len != 0) {
                var at_call = frame;
                at_call.return_token = frame.cache.tree.firstToken(node);
                if (try self.sourceCell(at_call, mapped.node, null, depth + 1)) |cell| {
                    if (cell.binding.origin != .param) {
                        try self.projectExpression(at_call, mapped.node, mapped.path, .value, try self.join(result_path, alternative.result_path), output, depth + 1);
                        continue;
                    }
                }
            }
            var arguments: Output = .{};
            try self.expression(frame, mapped.node, .coordinate, result_path, &arguments, depth + 1);
            if (!arguments.complete) output.complete = false;
            if (arguments.allocations.items.len != 0) output.complete = false;
            for (arguments.items.items) |item| {
                var translated = item;
                var suffix = mapped.path;
                const argument_selector = if (item.result_path.len == result_path.len) "" else item.result_path[result_path.len + @intFromBool(result_path.len != 0) ..];
                if (argument_selector.len != 0) {
                    if (!std.mem.eql(u8, suffix, argument_selector) and
                        !(std.mem.startsWith(u8, suffix, argument_selector) and suffix.len > argument_selector.len and suffix[argument_selector.len] == '.')) continue;
                    suffix = if (suffix.len == argument_selector.len) "" else suffix[argument_selector.len + 1 ..];
                }
                translated.owner.path = try self.join(item.owner.path, suffix);
                translated.result_path = try self.join(result_path, alternative.result_path);
                const rooted_payload = argument_selector.len != 0 and
                    alternative.storage == .payload_storage and item.storage != .payload_storage;
                translated.projection = if (rooted_payload) item.projection else alternative.projection;
                // A constructed aggregate's field selector selects its source;
                // it is not another field to append to the source's owner path.
                // Incomplete construction coverage still remains incomplete.
                translated.storage = if (alternative.storage == .inline_storage or rooted_payload)
                    item.storage
                else if (item.storage == .payload_storage)
                    .payload_storage
                else
                    alternative.storage;
                try self.add(output, translated);
            }
        }
    }
};

test "returned storage distinguishes a backing cell from an inline sibling cell" {
    const source: [:0]const u8 =
        \\const Box = struct {
        \\    slots: []u32, scratch: [4]u32,
        \\    fn backing(self: *Box) *u32 { return &self.slots[0]; }
        \\    fn inlineCell(self: *Box) *u32 { return &self.scratch[0]; }
        \\};
        \\fn use(box: *Box) void { _ = box.backing(); _ = box.inlineCell(); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var remaining: u32 = 50_000;
    const backing = try returnedStorageAt(typed.cache, callNamed(typed.tree(), "backing").?, .{ .remaining = &remaining });
    const inline_cell = try returnedStorageAt(typed.cache, callNamed(typed.tree(), "inlineCell").?, .{ .remaining = &remaining });
    try std.testing.expect(backing.complete and inline_cell.complete);
    try std.testing.expectEqual(@as(usize, 1), backing.alternatives.len);
    try std.testing.expectEqual(@as(usize, 1), inline_cell.alternatives.len);
    try std.testing.expectEqual(Projection.cell_address, backing.alternatives[0].projection);
    try std.testing.expectEqual(Storage.backing_storage, backing.alternatives[0].storage);
    try std.testing.expectEqualStrings("slots", backing.alternatives[0].owner.path);
    try std.testing.expectEqual(Storage.inline_storage, inline_cell.alternatives[0].storage);
    try std.testing.expectEqualStrings("scratch", inline_cell.alternatives[0].owner.path);
}

// Typed consumer regressions query the same canonical callee token as real
// callers. A field-call's identifier token is not its call-index coordinate.
// Each query has its own shared semantic-work allowance.

/// A document the type engine can resolve in, so a call edge inside one body
/// really names the declaration another body spells.
const Typed = struct {
    const engine = @import("type_engine");

    context: engine.TypeContext,
    resolver: engine.TypeResolver,
    cache: *FileCache,

    fn init(gpa: std.mem.Allocator, source: [:0]const u8) !*Typed {
        const self = try gpa.create(Typed);
        errdefer gpa.destroy(self);
        try self.context.init(gpa, std.testing.io);
        errdefer self.context.deinit();
        try self.resolver.init(&self.context, gpa, "/zbc-call-summary-test.zig", source);
        errdefer self.resolver.deinit();
        self.cache = try gpa.create(FileCache);
        errdefer gpa.destroy(self.cache);
        self.cache.* = FileCache.init(gpa, self.tree());
        self.cache.setZls(&self.resolver);
        return self;
    }

    fn deinit(self: *Typed, gpa: std.mem.Allocator) void {
        self.cache.deinit();
        gpa.destroy(self.cache);
        self.resolver.deinit();
        self.context.deinit();
        gpa.destroy(self);
    }

    fn tree(self: *Typed) *const Ast {
        return &self.resolver.handle.document.tree;
    }
};

fn callNamed(tree: *const Ast, name: []const u8) ?Ast.TokenIndex {
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), name)) continue;
        return call.queryToken(tree, node);
    }
    return null;
}

/// The call whose OWN FIRST ARGUMENT is written exactly as `argument`.  The
/// callee's name is deliberately not part of this lookup: an SDK accessor is
/// read by what it is handed, never by the getter vocabulary a consumer writes.
fn callTaking(tree: *const Ast, argument: []const u8) ?Ast.TokenIndex {
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        if (call.ast.params.len == 0) continue;
        if (!std.mem.eql(u8, tree.getNodeSource(call.ast.params[0]), argument)) continue;
        return call.queryToken(tree, node);
    }
    return null;
}

/// The meter's whole allowance, spelled once and read from the same constant
/// the root cache meters every consumer query with.
const work_limit: u32 = call_summary.actual_query_work_limit;

/// One consumer query on its own meter: an answer is paid for out of the
/// caller's allowance, and the meter is read back so a query that spent
/// nothing is never mistaken for one that proved something.  The result and
/// its path bytes belong to the root cache, so it outlives this call.
fn returnedStorageOf(cache: *FileCache, token: Ast.TokenIndex) !ReturnedStorage {
    var remaining: u32 = work_limit;
    const returned = try returnedStorageAt(cache, token, .{ .remaining = &remaining });
    try std.testing.expect(remaining < work_limit);
    return returned;
}

fn actualOf(cache: *FileCache, token: Ast.TokenIndex) !FileCache.ActualCallSummary {
    return (try cache.actualCallSummaryAt(token, null)) orelse error.TestExpectedCallee;
}

/// One alternative named the way a consumer reads it: by owner, projection,
/// storage and the field of the RESULT that carries it.  The set is searched
/// by owner, so no answer depends on the order its alternatives came out in.
fn expectAlternative(
    returned: ReturnedStorage,
    owner: fn_summary.ParamPath,
    projection: Projection,
    storage: Storage,
    result_path: []const u8,
) !Alternative {
    for (returned.alternatives) |alternative| {
        if (alternative.owner.param != owner.param) continue;
        if (!std.mem.eql(u8, alternative.owner.path, owner.path)) continue;
        try std.testing.expectEqual(projection, alternative.projection);
        try std.testing.expectEqual(storage, alternative.storage);
        try std.testing.expectEqualStrings(result_path, alternative.result_path);
        return alternative;
    }
    return error.TestExpectedAlternative;
}

fn expectOnlyAlternative(
    returned: ReturnedStorage,
    owner: fn_summary.ParamPath,
    projection: Projection,
    storage: Storage,
    result_path: []const u8,
) !Alternative {
    try std.testing.expect(returned.complete);
    try std.testing.expectEqual(@as(usize, 1), returned.alternatives.len);
    return expectAlternative(returned, owner, projection, storage, result_path);
}

fn expectNoAlternative(returned: ReturnedStorage, param: u32, path: []const u8) !void {
    for (returned.alternatives) |alternative| {
        if (alternative.owner.param != param) continue;
        if (!std.mem.eql(u8, alternative.owner.path, path)) continue;
        return error.TestUnexpectedAlternative;
    }
}

fn expectNoStorage(returned: ReturnedStorage, storage: Storage) !void {
    for (returned.alternatives) |alternative| {
        if (alternative.storage == storage) return error.TestUnexpectedStorage;
    }
}

/// UNKNOWN: incomplete and empty.  No conclusion may be drawn from it, and
/// none may be drawn from the absence of alternatives either.
fn expectUnknown(returned: ReturnedStorage) !void {
    try std.testing.expect(!returned.complete);
    try std.testing.expectEqual(@as(usize, 0), returned.alternatives.len);
}

/// Complete and empty: the returned value carries no storage at all, so a
/// consumer may conclude that nothing was lent to it.
fn expectNoBorrow(returned: ReturnedStorage) !void {
    try std.testing.expect(returned.complete);
    try std.testing.expectEqual(@as(usize, 0), returned.alternatives.len);
}

/// The caller-side coordinate of one alternative: the argument the callee's
/// formal was handed, carrying the owner's own path.  The node belongs to the
/// caller's tree.
fn expectMapping(
    cache: *FileCache,
    actual: FileCache.ActualCallSummary,
    alternative: Alternative,
    expression: []const u8,
    path: []const u8,
) !void {
    var buffer: [2]Ast.Node.Index = undefined;
    const mapped = (try mappedStorageAt(cache, actual, alternative, &buffer)) orelse
        return error.TestExpectedMapping;
    const tree = cache.tree;
    try std.testing.expectEqualStrings(
        expression,
        tree.getNodeSource(mapped.node),
    );
    try std.testing.expectEqualStrings(path, mapped.path);
}

test "an address into an inline field maps onto the receiver this call site handed it" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    scratch: [4]u32,
        \\    fn inlineCell(self: *Slots) *u32 { return &self.scratch[0]; }
        \\};
        \\const Holder = struct { grid: Slots };
        \\fn run(holder: *Holder) void { _ = holder.grid.inlineCell(); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    const token = callNamed(typed.tree(), "inlineCell") orelse return error.TestExpectedCall;
    const alternative = try expectOnlyAlternative(
        try returnedStorageOf(cache, token),
        .{ .param = 0, .path = "scratch" },
        .cell_address,
        .inline_storage,
        "",
    );
    // The consumer can carry that answer onto its own storage: the receiver
    // EXPRESSION this call site wrote, and the inline field inside it.
    try expectMapping(cache, try actualOf(cache, token), alternative, "holder.grid", "scratch");
}

test "a slice header copied out of a field carries that field's own storage" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    scratch: [4]u32,
        \\    fn view(self: *Slots, index: usize) []u32 { return self.slots[index .. index + 1]; }
        \\    fn inlineView(self: *Slots) []u32 { return self.scratch[0 .. 1]; }
        \\};
        \\fn run(grid: *Slots) void {
        \\    _ = grid.view(1);
        \\    _ = grid.inlineView();
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    // A returned slice is a copied header, not an address: it names the
    // allocation its field names, whether that field is a slice or an inline
    // array.
    _ = try expectOnlyAlternative(
        try returnedStorageOf(cache, callNamed(typed.tree(), "view") orelse return error.TestExpectedCall),
        .{ .param = 0, .path = "slots" },
        .pointer_value,
        .backing_storage,
        "",
    );
    _ = try expectOnlyAlternative(
        try returnedStorageOf(cache, callNamed(typed.tree(), "inlineView") orelse return error.TestExpectedCall),
        .{ .param = 0, .path = "scratch" },
        .pointer_value,
        .inline_storage,
        "",
    );
}

/// The owner and storage kind one answer reports, without pinning how the
/// callee's own return type spells the projection.
fn expectOwnerStorage(
    returned: ReturnedStorage,
    owner: fn_summary.ParamPath,
    storage: Storage,
) !Alternative {
    for (returned.alternatives) |alternative| {
        if (alternative.owner.param != owner.param) continue;
        if (!std.mem.eql(u8, alternative.owner.path, owner.path)) continue;
        try std.testing.expectEqual(storage, alternative.storage);
        return alternative;
    }
    return error.TestExpectedAlternative;
}

test "a helper that returns its pointer formal inherits the storage of the argument it was handed" {
    const source: [:0]const u8 =
        \\const Box = struct {
        \\    slots: []u32,
        \\    scratch: [4]u32,
        \\    fn identity(x: *u32) *u32 { return x; }
        \\    fn borrowed(self: *Box) *u32 { return identity(&self.slots[0]); }
        \\    fn inlined(self: *Box) *u32 { return identity(&self.scratch[0]); }
        \\};
        \\fn run(box: *Box) void {
        \\    _ = box.borrowed();
        \\    _ = box.inlined();
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    // `identity`'s own formal is a pointer, which says nothing about what it
    // was handed: the answer follows the ARGUMENT, so a cell in a field's
    // allocation keeps that allocation.
    const borrowed = try returnedStorageOf(cache, callNamed(typed.tree(), "borrowed") orelse return error.TestExpectedCall);
    try std.testing.expect(borrowed.complete);
    try std.testing.expectEqual(@as(usize, 1), borrowed.alternatives.len);
    _ = try expectOwnerStorage(borrowed, .{ .param = 0, .path = "slots" }, .backing_storage);
    try expectNoStorage(borrowed, .inline_storage);
    // The same helper handed an inline cell leaves it inline.
    const inlined = try returnedStorageOf(cache, callNamed(typed.tree(), "inlined") orelse return error.TestExpectedCall);
    try std.testing.expect(inlined.complete);
    try std.testing.expectEqual(@as(usize, 1), inlined.alternatives.len);
    _ = try expectOwnerStorage(inlined, .{ .param = 0, .path = "scratch" }, .inline_storage);
    try expectNoStorage(inlined, .backing_storage);
}

test "a copied aggregate names every direct and nested pointer loan" {
    const source: [:0]const u8 =
        \\const Inner = struct { data: *u32 };
        \\const Payload = struct { direct: *u32, value: Inner };
        \\const Pair = struct { first: *u32, second: *u32 };
        \\fn borrow(payload: Payload) Payload { return payload; }
        \\fn copyPair(pair: Pair) Pair { return pair; }
        \\fn run(borrowed: Payload, pair: Pair) void {
        \\    _ = borrow(borrowed);
        \\    _ = copyPair(pair);
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    // Copied loans retain the formal field and the result field that carry
    // them, including fields nested inside another copied aggregate.
    const payload = try returnedStorageOf(cache, callNamed(typed.tree(), "borrow") orelse return error.TestExpectedCall);
    try std.testing.expectEqual(@as(usize, 2), payload.alternatives.len);
    _ = try expectAlternative(
        payload,
        .{ .param = 0, .path = "direct" },
        .payload_value,
        .payload_storage,
        "direct",
    );
    _ = try expectAlternative(
        payload,
        .{ .param = 0, .path = "value.data" },
        .payload_value,
        .payload_storage,
        "value.data",
    );
    try expectNoStorage(payload, .backing_storage);
    try expectNoStorage(payload, .inline_storage);
    // Every direct sibling loan is represented and its pointee is address-free.
    const pair = try returnedStorageOf(cache, callNamed(typed.tree(), "copyPair") orelse return error.TestExpectedCall);
    try std.testing.expectEqual(@as(usize, 2), pair.alternatives.len);
    _ = try expectAlternative(pair, .{ .param = 0, .path = "first" }, .payload_value, .payload_storage, "first");
    _ = try expectAlternative(pair, .{ .param = 0, .path = "second" }, .payload_value, .payload_storage, "second");
    try expectNoStorage(pair, .backing_storage);
}

test "an aggregate literal of two direct borrows is complete and names both" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []u32, scratch: [4]u32 };
        \\const Pair = struct { backed: *u32, inlined: *u32 };
        \\fn pair(box: *Box) Pair {
        \\    return .{ .backed = &box.slots[0], .inlined = &box.scratch[0] };
        \\}
        \\fn run(box: *Box) void { _ = pair(box); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const returned = try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "pair") orelse return error.TestExpectedCall,
    );
    // Each field of the literal is a direct borrow, named by the field of the
    // RESULT that carries it, and there is nothing left to conclude.
    try std.testing.expect(returned.complete);
    try std.testing.expectEqual(@as(usize, 2), returned.alternatives.len);
    _ = try expectAlternative(
        returned,
        .{ .param = 0, .path = "slots" },
        .cell_address,
        .backing_storage,
        "backed",
    );
    _ = try expectAlternative(
        returned,
        .{ .param = 0, .path = "scratch" },
        .cell_address,
        .inline_storage,
        "inlined",
    );
}

test "a scalar copied out of a formal is complete and borrows nothing" {
    const source: [:0]const u8 =
        \\const Count = struct { value: u32 };
        \\fn scale(count: u32) u32 { return count; }
        \\fn pack(count: u32) Count { return .{ .value = count }; }
        \\fn run(count: u32) void {
        \\    _ = scale(count);
        \\    _ = pack(count);
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    // A by-value copy of an address-free formal reaches nothing at all, and
    // the answer says so outright instead of staying quiet about it.
    try expectNoBorrow(try returnedStorageOf(
        cache,
        callNamed(typed.tree(), "scale") orelse return error.TestExpectedCall,
    ));
    try expectNoBorrow(try returnedStorageOf(
        cache,
        callNamed(typed.tree(), "pack") orelse return error.TestExpectedCall,
    ));
}

test "a helper's nested field and a borrowed sibling are both named across a plain rebinding" {
    const source: [:0]const u8 =
        \\const Inner = struct { items: []u32 };
        \\const Outer = struct { inner: Inner, spare: []u32 };
        \\fn itemsOf(inner: *Inner) []u32 { return inner.items; }
        \\fn gather(outer: *Outer) []u32 {
        \\    if (outer.inner.items.len == 0) {
        \\        return outer.spare;
        \\    } else if (outer.spare.len == 0) {
        \\        return itemsOf(&outer.inner);
        \\    } else {
        \\        var moved = itemsOf(&outer.inner);
        \\        moved = outer.spare;
        \\        return moved;
        \\    }
        \\}
        \\fn run(state: *Outer) void { _ = gather(state); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const token = callNamed(typed.tree(), "gather") orelse return error.TestExpectedCall;
    const actual = try actualOf(typed.cache, token);
    const returned = try returnedStorageOf(typed.cache, token);
    // Every alias the body can hand back is represented, in the callee's own
    // formal coordinates: the field a helper reaches, and the sibling this
    // aggregate already holds. The plain rebinding contributes its value to
    // the union without leaving anything unaccounted for.
    try std.testing.expect(returned.complete);
    try std.testing.expectEqual(@as(usize, 2), returned.alternatives.len);
    const nested = try expectAlternative(
        returned,
        .{ .param = 0, .path = "inner.items" },
        .pointer_value,
        .backing_storage,
        "",
    );
    const sibling = try expectAlternative(
        returned,
        .{ .param = 0, .path = "spare" },
        .pointer_value,
        .backing_storage,
        "",
    );
    try expectMapping(typed.cache, actual, nested, "state", "inner.items");
    try expectMapping(typed.cache, actual, sibling, "state", "spare");
    // The aggregate itself is never named: only the field that carries it.
    try expectNoAlternative(returned, 0, "inner");
}

const rewrite_source: [:0]const u8 =
    \\const Chain = struct { lead: []const u8, other: []const u8, buffers: [][]const u8 };
    \\fn merged(chain: Chain, flag: bool) []const u8 {
    \\    var storage = chain.lead;
    \\    if (flag) storage = chain.lead;
    \\    return storage;
    \\}
    \\fn either(chain: Chain, flag: bool) []const u8 {
    \\    var storage = chain.lead;
    \\    if (flag) storage = chain.other;
    \\    return storage;
    \\}
    \\fn looped(chain: Chain, count: usize) []const u8 {
    \\    var storage = chain.lead;
    \\    var index: usize = 0;
    \\    while (index < count) : (index += 1) storage = chain.other;
    \\    return storage;
    \\}
    \\fn carried(chain: Chain, flag: bool) []const u8 {
    \\    var storage = chain.lead;
    \\    storage = chain.lead;
    \\    while (true) {
    \\        if (flag) return storage;
    \\        storage = chain.other;
    \\    }
    \\}
    \\fn selfFed(chain: Chain) []const u8 {
    \\    var storage = chain.lead;
    \\    storage = storage[1..];
    \\    return storage;
    \\}
    \\fn rotate(x: []const u8, y: []const u8, z: []const u8, count: usize) []const u8 {
    \\    var a = x;
    \\    var b = y;
    \\    var c = z;
    \\    var index: usize = 0;
    \\    while (index < count) : (index += 1) {
    \\        a = b;
    \\        b = c;
    \\        c = a;
    \\    }
    \\    return a;
    \\}
    \\fn store(slot: *[]const u8, value: []const u8) void { slot.* = value; }
    \\fn addressed(chain: Chain, flag: bool) []const u8 {
    \\    var storage = chain.lead;
    \\    if (flag) storage = chain.lead;
    \\    store(&storage, chain.other);
    \\    return storage;
    \\}
    \\fn useAll(chain: Chain, flag: bool) void {
    \\    _ = rotate(chain.lead, chain.other, chain.lead, 2);
    \\    _ = addressed(chain, flag);
    \\    _ = merged(chain, flag);
    \\    _ = either(chain, flag);
    \\    _ = looped(chain, 1);
    \\    _ = carried(chain, flag);
    \\    _ = selfFed(chain);
    \\}
;

const RewriteAnswer = struct { complete: bool, lead: bool, other: bool, alternatives: usize };

fn rewriteAnswer(callee: []const u8) !RewriteAnswer {
    const typed = try Typed.init(std.testing.allocator, rewrite_source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const token = callNamed(typed.tree(), callee) orelse return error.TestExpectedCall;
    const returned = try returnedStorageOf(typed.cache, token);
    var answer: RewriteAnswer = .{ .complete = returned.complete, .lead = false, .other = false, .alternatives = returned.alternatives.len };
    for (returned.alternatives) |alternative| {
        if (alternative.owner.param != 0) continue;
        if (std.mem.eql(u8, alternative.owner.path, "lead")) answer.lead = true;
        if (std.mem.eql(u8, alternative.owner.path, "other")) answer.other = true;
    }
    return answer;
}

test "a local rewritten whole by plain writes before the read holds only the values written" {
    // Writing the same field again adds no origin: the sibling field that
    // points at a local buffer is never named.
    const merged = try rewriteAnswer("merged");
    try std.testing.expect(merged.complete);
    try std.testing.expect(merged.lead and !merged.other);
    try std.testing.expectEqual(@as(usize, 1), merged.alternatives);
    // A rewrite from another field names that field too, and nothing else.
    const either = try rewriteAnswer("either");
    try std.testing.expect(either.complete);
    try std.testing.expect(either.lead and either.other);
    try std.testing.expectEqual(@as(usize, 2), either.alternatives);
    const looped = try rewriteAnswer("looped");
    try std.testing.expect(looped.complete);
    try std.testing.expect(looped.lead and looped.other);
    try std.testing.expectEqual(@as(usize, 2), looped.alternatives);
}

test "a rewrite a loop carries back, one fed by the local itself, or a local a callee can store into stays unknown" {
    // The write after the read reaches it through the loop: it is not before
    // the read, so the answer must not claim to have seen every write.
    try std.testing.expect(!(try rewriteAnswer("carried")).complete);
    try std.testing.expect(!(try rewriteAnswer("selfFed")).complete);
    // A callee holding the local's address can store into it unseen.
    try std.testing.expect(!(try rewriteAnswer("addressed")).complete);
    // Loop writes that feed one another: the last value rotated in is not
    // among the ones written before it lexically.
    try std.testing.expect(!(try rewriteAnswer("rotate")).complete);
}

test "an aggregate result names the borrow under the field of the result that carries it" {
    const source: [:0]const u8 =
        \\const Inner = struct { items: []u32 };
        \\const Pair = struct { first: []u32, second: []u32 };
        \\fn itemsOf(inner: *Inner) []u32 { return inner.items; }
        \\fn gather(inner: *Inner, spare: []u32) Pair {
        \\    return .{ .first = itemsOf(inner), .second = spare };
        \\}
        \\fn firstOf(inner: *Inner, spare: []u32) []u32 { return gather(inner, spare).first; }
        \\fn run(inner: *Inner, spare: []u32) void { _ = firstOf(inner, spare); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    const gathered = try returnedStorageOf(
        cache,
        callNamed(typed.tree(), "gather") orelse return error.TestExpectedCall,
    );
    // The aggregate hands back both borrows, each under the RESULT field that
    // carries it rather than under a field of a formal.
    try std.testing.expect(gathered.complete);
    try std.testing.expectEqual(@as(usize, 2), gathered.alternatives.len);
    _ = try expectAlternative(
        gathered,
        .{ .param = 0, .path = "items" },
        .pointer_value,
        .backing_storage,
        "first",
    );
    _ = try expectAlternative(
        gathered,
        .{ .param = 1, .path = "" },
        .pointer_value,
        .backing_storage,
        "second",
    );
    // A caller that selects ONE of those fields reads that field's owner
    // alone, and the result path it travelled is already consumed.
    _ = try expectOnlyAlternative(
        try returnedStorageOf(cache, callNamed(typed.tree(), "firstOf") orelse return error.TestExpectedCall),
        .{ .param = 0, .path = "items" },
        .pointer_value,
        .backing_storage,
        "",
    );
}

test "storage a callee copied into its own frame cannot be named relative to a formal" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    scratch: [4]u32,
        \\    fn copied(self: *Slots) *u32 {
        \\        const copy = self.scratch;
        \\        return &copy[0];
        \\    }
        \\};
        \\fn run(grid: *Slots) void { _ = grid.copied(); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    // `copy` is the callee's own frame storage: the answer is not the formal's
    // cell, and no private origin may be invented for it either.
    try expectUnknown(try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "copied") orelse return error.TestExpectedCall,
    ));
}

test "unknown integer bits do not prove a reconstructed pointer independent" {
    const source: [:0]const u8 =
        \\const Cell = struct { address: usize };
        \\fn load(cell: *Cell) *u32 { return @ptrFromInt(cell.address); }
        \\fn run(cell: *Cell) void { _ = load(cell); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    // The integer source does not identify the returned pointer's allocation.
    try expectUnknown(try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "load") orelse return error.TestExpectedCall,
    ));
}

test "a bodyless declaration returns no storage at all" {
    const source: [:0]const u8 =
        \\extern "c" fn fill(bytes: []u8) void;
        \\fn run(bytes: []u8) void { fill(bytes); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    // A record of a declaration is still an identity; the absence of a body
    // is never a promise that nothing was lent.
    try expectUnknown(try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "fill") orelse return error.TestExpectedCall,
    ));
}

test "a cycle in the return path is unknown rather than an error" {
    const source: [:0]const u8 =
        \\const Node = struct { items: []u32 };
        \\fn ping(node: *Node) []u32 { return pong(node); }
        \\fn pong(node: *Node) []u32 { return ping(node); }
        \\fn run(entry: *Node) void { _ = entry.ping(); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    // The recursion is cut, not reported as a resource failure: a caller
    // still has no answer, and no part of one either.
    try expectUnknown(try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "ping") orelse return error.TestExpectedCall,
    ));
}

test "an owner lands on the caller's own argument expression" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    fn view(self: *Slots, index: usize) []u32 { return self.slots[index .. index + 1]; }
        \\};
        \\fn run(grid: *Slots) void { _ = grid.view(1); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    const token = callNamed(typed.tree(), "view") orelse return error.TestExpectedCall;
    const alternative = try expectOnlyAlternative(
        try returnedStorageOf(cache, token),
        .{ .param = 0, .path = "slots" },
        .pointer_value,
        .backing_storage,
        "",
    );
    // The consumer's own question is answerable: formal zero of the getter is
    // the receiver this call site handed it, and the owner's path rides along.
    try expectMapping(cache, try actualOf(cache, token), alternative, "grid", "slots");
}

test "an owner reached through the caller's receiver keeps that receiver's own coordinate" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    fn view(self: *Slots, index: usize) []u32 { return self.slots[index .. index + 1]; }
        \\};
        \\const Holder = struct { grid: Slots };
        \\fn run(holder: *Holder) void { _ = holder.grid.view(2); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    const token = callNamed(typed.tree(), "view") orelse return error.TestExpectedCall;
    const alternative = try expectOnlyAlternative(
        try returnedStorageOf(cache, token),
        .{ .param = 0, .path = "slots" },
        .pointer_value,
        .backing_storage,
        "",
    );
    // The mapped node is the receiver EXPRESSION the call site wrote, so the
    // caller's own storage is `holder.grid.slots`, not some formal of the
    // getter.
    try expectMapping(cache, try actualOf(cache, token), alternative, "holder.grid", "slots");
}

test "a forwarded method return preserves its argument storage through the canonical call token" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    fn view(self: *Slots) []u32 { return self.slots; }
        \\};
        \\fn forwarded(grid: *Slots) []u32 { return grid.view(); }
        \\fn run(grid: *Slots) void { _ = forwarded(grid); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const token = callNamed(typed.tree(), "forwarded") orelse return error.TestExpectedCall;
    const alternative = try expectOnlyAlternative(
        try returnedStorageOf(cache, token),
        .{ .param = 0, .path = "slots" },
        .pointer_value,
        .backing_storage,
        "",
    );
    try expectMapping(cache, try actualOf(cache, token), alternative, "grid", "slots");
}

test "canonical builtin calls preserve generic tuple arguments and forwarded storage" {
    const source: [:0]const u8 =
        \\const Box = struct { scratch: [4]u32 };
        \\fn identity(comptime T: type, value: T) T { return value; }
        \\fn forwarded(box: *Box) *u32 {
        \\    return @call(.auto, identity, .{ *u32, &box.scratch[0] });
        \\}
        \\fn run(box: *Box) void { _ = @call(.auto, forwarded, .{box}); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const token = callNamed(typed.tree(), "forwarded") orelse return error.TestExpectedCall;
    try std.testing.expectEqualStrings("@call", typed.tree().tokenSlice(token));
    const alternative = try expectOnlyAlternative(
        try returnedStorageOf(cache, token),
        .{ .param = 0, .path = "scratch" },
        .pointer_value,
        .inline_storage,
        "",
    );
    try expectMapping(cache, try actualOf(cache, token), alternative, "box", "scratch");
    const identity_token = callNamed(typed.tree(), "identity") orelse return error.TestExpectedCall;
    const actual = try actualOf(cache, identity_token);
    const identity_returned = try returnedStorageOf(cache, identity_token);
    try std.testing.expect(identity_returned.complete);
    try std.testing.expectEqual(@as(usize, 1), identity_returned.alternatives.len);
    const identity_alternative = identity_returned.alternatives[0];
    try std.testing.expectEqual(@as(u32, 1), identity_alternative.owner.param);
    try expectMapping(cache, actual, identity_alternative, "&box.scratch[0]", "");
}

test "canonical generic builtin calls forward backing slice storage" {
    const source: [:0]const u8 =
        \\fn identity(comptime T: type, value: T) T { return value; }
        \\fn forwarded(values: []u32) []u32 {
        \\    return @call(.auto, identity, .{ []u32, values });
        \\}
        \\fn use(values: []u32) void { _ = @call(.auto, forwarded, .{values}); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const identity_token = callNamed(typed.tree(), "identity").?;
    const alternative = try expectOnlyAlternative(
        try returnedStorageOf(typed.cache, identity_token),
        .{ .param = 1, .path = "" },
        .pointer_value,
        .backing_storage,
        "",
    );
    try expectMapping(typed.cache, try actualOf(typed.cache, identity_token), alternative, "values", "");
    _ = try expectOnlyAlternative(
        try returnedStorageOf(typed.cache, callNamed(typed.tree(), "forwarded").?),
        .{ .param = 0, .path = "" },
        .pointer_value,
        .backing_storage,
        "",
    );
}

test "instantiated factory builtin calls retain their backing slice context" {
    const source: [:0]const u8 =
        \\fn Factory(comptime T: type) type {
        \\    return struct {
        \\        fn identity(value: []T) []T { return value; }
        \\    };
        \\}
        \\const U32 = Factory(u32);
        \\fn forwarded(values: []u32) []u32 {
        \\    return @call(.auto, U32.identity, .{values});
        \\}
        \\fn use(values: []u32) void { _ = forwarded(values); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    _ = try expectOnlyAlternative(
        try returnedStorageOf(typed.cache, callNamed(typed.tree(), "forwarded").?),
        .{ .param = 0, .path = "" },
        .pointer_value,
        .backing_storage,
        "",
    );
}

test "exact formal selectors do not claim deep storage completeness" {
    const source: [:0]const u8 =
        \\fn loan(values: []*u8) []*u8 { return values; }
        \\fn element(values: []*u8) *u8 { return values[0]; }
        \\fn dereference(value: **u8) *u8 { return value.*; }
        \\extern fn opaqueLoan(values: []*u8) []*u8;
        \\fn mixed(values: []*u8, choose: bool) []*u8 {
        \\    return if (choose) values else opaqueLoan(values);
        \\}
        \\fn cast(values: []*u8) []*u8 { return @ptrCast(values); }
        \\fn use(values: []*u8, value: **u8, choose: bool) void {
        \\    _ = loan(values);
        \\    _ = element(values);
        \\    _ = dereference(value);
        \\    _ = mixed(values, choose);
        \\    _ = cast(values);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const loan = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "loan").?);
    try std.testing.expect(!loan.complete);
    try std.testing.expect(loan.direct_formal_loan);
    try std.testing.expect(loan.direct_formal_load == null);
    const element = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "element").?);
    try std.testing.expect(!element.complete);
    try std.testing.expect(element.direct_formal_load == .element);
    const dereference = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "dereference").?);
    try std.testing.expect(!dereference.complete);
    try std.testing.expect(dereference.direct_formal_load == .dereference);
    for ([_][]const u8{ "mixed", "cast" }) |name| {
        const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), name).?);
        try std.testing.expect(!returned.direct_formal_loan);
        try std.testing.expect(returned.direct_formal_load == null);
    }
}

test "a dynamic builtin argument tuple has no canonical call index or pure answer" {
    const source: [:0]const u8 =
        \\fn identity(value: *u32) *u32 { return value; }
        \\fn dynamic(arguments: struct { *u32 }) *u32 {
        \\    return @call(.auto, identity, arguments);
        \\}
        \\fn run(arguments: struct { *u32 }) void { _ = dynamic(arguments); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    try std.testing.expect(callNamed(typed.tree(), "identity") == null);
    const returned = try returnedStorageOf(cache, callNamed(typed.tree(), "dynamic") orelse return error.TestExpectedCall);
    try std.testing.expect(!returned.complete);
    const index = try cache.getCallIndex();
    for (typed.tree().nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        try std.testing.expect(!index.by_callee_token.contains(typed.tree().nodeMainToken(node)));
    }
}

test "a real SDK map hands back a pointer into the table this call site handed it" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Map = std.AutoHashMap(u32, u32);
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    var entries = Map.init(gpa);
        \\    defer entries.deinit();
        \\    try entries.put(1, 2);
        \\    _ = entries.getPtr(3);
        \\    _ = entries.getPtrAdapted(@as(u32, 4), std.hash_map.AutoContext(u32){});
        \\    _ = entries.get(5);
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    typed.cache.module_id = typed.resolver.handle.module;
    const cache = typed.cache;
    // Each accessor is found by the argument it is handed, never by a getter
    // name this query might have learned.  Both name a declaration written in
    // the toolchain's own hash map, not a spelling this file owns.
    const pointer_token = callTaking(typed.tree(), "3") orelse return error.TestExpectedCall;
    const pointer = try actualOf(cache, pointer_token);
    try std.testing.expect(pointer.callee.tree != typed.tree());
    try std.testing.expect(try typed.resolver.declaredInToolchainFile(pointer.callee.handle, "/std/hash_map.zig"));
    // The pointer it returns addresses a cell of the map itself, so the owner
    // is that receiver and the whole of its storage: nothing of the private
    // header layout the compiler walks to reach it leaks into the answer.
    const pointer_storage = try expectOnlyAlternative(
        try returnedStorageOf(cache, pointer_token),
        .{ .param = 0, .path = "" },
        .cell_address,
        .backing_storage,
        "",
    );
    try expectMapping(cache, pointer, pointer_storage, "entries", "");
    // The adapted accessor answers with the same cell of the same map.
    const adapted_token = callTaking(typed.tree(), "@as(u32, 4)") orelse return error.TestExpectedCall;
    const adapted = try actualOf(cache, adapted_token);
    try std.testing.expect(adapted.callee.tree != typed.tree());
    try std.testing.expect(try typed.resolver.declaredInToolchainFile(adapted.callee.handle, "/std/hash_map.zig"));
    _ = try expectOnlyAlternative(
        try returnedStorageOf(cache, adapted_token),
        .{ .param = 0, .path = "" },
        .cell_address,
        .backing_storage,
        "",
    );
    // A copied value, by contrast, is answered outright: the `u32` this map
    // copies is address-free, so nothing was lent to the caller.
    const copied_token = callTaking(typed.tree(), "5") orelse return error.TestExpectedCall;
    const copied = try actualOf(cache, copied_token);
    try std.testing.expect(copied.callee.tree != typed.tree());
    try std.testing.expect(try typed.resolver.declaredInToolchainFile(copied.callee.handle, "/std/hash_map.zig"));
    try expectNoBorrow(try returnedStorageOf(cache, copied_token));
}

test "a copied pointer element carries an unknown pointee rather than its table cell" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []*u32 };
        \\fn copied(box: *Box) *u32 { return box.slots[0]; }
        \\fn use(box: *Box) void { _ = copied(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const result = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copied").?);
    try std.testing.expect(!result.complete);
    _ = try expectAlternative(result, .{ .param = 0, .path = "slots" }, .payload_value, .payload_storage, "");
    try expectNoStorage(result, .backing_storage);
    try expectNoStorage(result, .inline_storage);
}

test "assigned aggregate pointers remain visible without claiming full array coverage" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []u32 };
        \\const View = struct { pointers: [2][*]u32 };
        \\fn view(box: *Box) View {
        \\    var result: View = .{ .pointers = undefined };
        \\    var pointer: [*]u32 = box.slots.ptr;
        \\    for ([_]usize{ 0, 1 }) |index| {
        \\        result.pointers[index] = pointer;
        \\        pointer += 1;
        \\    }
        \\    return result;
        \\}
        \\fn use(box: *Box) void { _ = view(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const result = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "view").?);
    try std.testing.expect(!result.complete);
    _ = try expectAlternative(result, .{ .param = 0, .path = "slots" }, .pointer_value, .backing_storage, "pointers");
}

test "returned storage exhaustion keeps its named origin and shared allowance" {
    const source: [:0]const u8 =
        \\fn borrowed(bytes: []u32) *u32 { return &bytes[0]; }
        \\fn use(bytes: []u32) void { _ = borrowed(bytes); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    budget.clear();
    defer budget.clear();
    var remaining: u32 = 0;
    const token = callNamed(typed.tree(), "borrowed").?;
    try std.testing.expectError(error.AnalysisBudgetExceeded, returnedStorageAt(typed.cache, token, .{ .remaining = &remaining }));
    try std.testing.expectEqual(@as(u32, 0), remaining);
    const diagnostic = budget.take() orelse return error.TestExpectedBudget;
    try std.testing.expectEqual(budget.Limit.return_storage_work, diagnostic.limit);
    try std.testing.expectEqual(call_summary.actual_query_work_limit, diagnostic.limit_value);
}

test "an undefined pointer is unknown rather than a completed copied value" {
    const source: [:0]const u8 =
        \\fn unknown(bytes: []u32) *u32 { _ = bytes; return undefined; }
        \\fn use(bytes: []u32) void { _ = unknown(bytes); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectUnknown(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "unknown").?));
}

test "a canonical constant condition excludes only its unreachable pointer return" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []u32, address: usize };
        \\fn selected(box: *Box) *u32 {
        \\    return if (true) &box.slots[0] else @ptrFromInt(box.address);
        \\}
        \\fn use(box: *Box) void { _ = selected(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    _ = try expectOnlyAlternative(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "selected").?), .{ .param = 0, .path = "slots" }, .cell_address, .backing_storage, "");
}

test "a pointer field copy is a pointee and indexing its array addresses a backing cell" {
    const source: [:0]const u8 =
        \\const Box = struct { pointer: *u32, slots: *[4]u32, scratch: [4]u32 };
        \\fn copied(box: *Box) *u32 { return box.pointer; }
        \\fn cell(box: *Box) *u32 { return &box.slots[0]; }
        \\fn inlineAlias(box: *Box) *u32 {
        \\    const view = &box.scratch;
        \\    return &view[0];
        \\}
        \\fn use(box: *Box) void { _ = copied(box); _ = cell(box); _ = inlineAlias(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const copied = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copied").?);
    _ = try expectAlternative(copied, .{ .param = 0, .path = "pointer" }, .payload_value, .payload_storage, "");
    _ = try expectOnlyAlternative(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "cell").?), .{ .param = 0, .path = "slots" }, .cell_address, .backing_storage, "");
    _ = try expectOnlyAlternative(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "inlineAlias").?), .{ .param = 0, .path = "scratch" }, .cell_address, .inline_storage, "");
}

test "mapping a returned aggregate pointer consumes its formal field selector" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []u32 };
        \\const View = struct { pointers: [2][*]u32 };
        \\fn assembled(box: *Box) View {
        \\    var result: View = .{ .pointers = undefined };
        \\    var pointer: [*]u32 = box.slots.ptr;
        \\    for ([_]usize{ 0, 1 }) |index| {
        \\        result.pointers[index] = pointer;
        \\        pointer += 1;
        \\    }
        \\    return result;
        \\}
        \\fn projected(view: View) []u32 { return view.pointers[0][0..1]; }
        \\fn borrowed(box: *Box) []u32 { return projected(assembled(box)); }
        \\fn use(box: *Box) void { _ = borrowed(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "borrowed").?);
    try std.testing.expect(!returned.complete);
    _ = try expectAlternative(returned, .{ .param = 0, .path = "slots" }, .pointer_value, .backing_storage, "");
    for (returned.alternatives) |alternative|
        try std.testing.expect(!std.mem.endsWith(u8, alternative.owner.path, ".pointers"));
}

test "a declared scalar result remains a copied value across an undefined zero-size branch" {
    const source: [:0]const u8 =
        \\fn copied(comptime V: type, value: V) V {
        \\    return if (@sizeOf(V) == 0) undefined else value;
        \\}
        \\fn use() void { _ = copied(u32, @as(u32, 5)); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copied").?);
    try std.testing.expect(returned.complete);
    try std.testing.expectEqual(@as(usize, 0), returned.alternatives.len);
}

test "a real SDK array map pointer return is never classified as a copied scalar" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Map = std.array_hash_map.Auto(u32, u32);
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    var entries: Map = .empty;
        \\    defer entries.deinit(gpa);
        \\    try entries.put(gpa, 1, 2);
        \\    _ = entries.getPtr(3);
        \\    _ = entries.get(4);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    typed.cache.module_id = typed.resolver.handle.module;
    const pointer_token = callTaking(typed.tree(), "3") orelse return error.TestExpectedCall;
    const actual = try actualOf(typed.cache, pointer_token);
    try std.testing.expect(actual.callee.tree != typed.tree());
    try std.testing.expect(try typed.resolver.declaredInToolchainFile(actual.callee.handle, "/std/array_hash_map.zig"));
    const pointer = try returnedStorageOf(typed.cache, pointer_token);
    // Unknown coverage still requires a borrow. It must not become the
    // completed-empty answer that lets copied address-free values stay quiet.
    try std.testing.expect(!pointer.complete or pointer.alternatives.len != 0);
    for (pointer.alternatives) |alternative| {
        try std.testing.expectEqual(Projection.cell_address, alternative.projection);
        try std.testing.expectEqual(Storage.backing_storage, alternative.storage);
    }
    const copied = try returnedStorageOf(typed.cache, callTaking(typed.tree(), "4") orelse return error.TestExpectedCall);
    try std.testing.expect(copied.complete);
    try std.testing.expectEqual(@as(usize, 0), copied.alternatives.len);
}

test "returned selected effects avoid cold whole-cell walks and retain selected encodings" {
    const gpa = std.testing.allocator;
    var out: std.Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    try out.writer.writeAll("const Box = struct { selected: usize, sibling: usize };\nfn change(box: *Box, pointer: *u32) void {\n");
    for (0..60) |_| try out.writer.writeAll("box.sibling = @intFromPtr(pointer);\n");
    try out.writer.writeAll(
        \\box.selected = 1;
        \\}
        \\fn poison(box: *Box, pointer: *u32) void { box.selected = @intFromPtr(pointer); }
        \\fn hash(pointer: *u32) usize {
        \\    var box: Box = .{ .selected = 0, .sibling = 0 };
        \\    change(&box, pointer);
        \\    return box.selected;
        \\}
        \\fn encoded(pointer: *u32) usize {
        \\    var box: Box = .{ .selected = 0, .sibling = 0 };
        \\    poison(&box, pointer);
        \\    return box.selected;
        \\}
        \\fn use(pointer: *u32) void { _ = hash(pointer); _ = encoded(pointer); }
    );
    const source = try gpa.dupeZ(u8, out.written());
    defer gpa.free(source);
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    budget.clear();
    defer budget.clear();
    var remaining: u32 = 4000;
    const copied = try returnedStorageAt(typed.cache, callNamed(typed.tree(), "hash").?, .{ .remaining = &remaining });
    try std.testing.expect(copied.complete);
    try std.testing.expectEqual(@as(usize, 0), copied.alternatives.len);
    const encoded = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "encoded").?);
    try std.testing.expect(!encoded.complete or encoded.alternatives.len != 0);
    try std.testing.expect(budget.peek() == null);
}

test "returned storage indexes repeated binding lookups without erasing encoded addresses" {
    const gpa = std.testing.allocator;
    const Sum = struct {
        fn write(writer: *std.Io.Writer, first: usize, count: usize) anyerror!void {
            if (count == 1) return writer.print("a{d}", .{first});
            try writer.writeByte('(');
            try write(writer, first, count / 2);
            try writer.writeAll(" +% ");
            try write(writer, first + count / 2, count - count / 2);
            try writer.writeByte(')');
        }
    };
    var out: std.Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    try out.writer.writeAll("fn hash() usize {\n");
    for (0..320) |index| try out.writer.print("const a{d}: usize = {d};\n", .{ index, index });
    try out.writer.writeAll("return ");
    try Sum.write(&out.writer, 0, 320);
    try out.writer.writeAll(";\n}\nfn encoded(pointer: *u32) usize { return @intFromPtr(pointer); }\nfn use(pointer: *u32) void { _ = hash(); _ = encoded(pointer); }\n");
    const source = try gpa.dupeZ(u8, out.written());
    defer gpa.free(source);
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    budget.clear();
    defer budget.clear();
    const copied = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "hash").?);
    try std.testing.expect(copied.complete);
    try std.testing.expectEqual(@as(usize, 0), copied.alternatives.len);
    const encoded = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "encoded").?);
    try std.testing.expect(!encoded.complete or encoded.alternatives.len != 0);
    try std.testing.expect(budget.peek() == null);
}

test "explicitly encoded address bits are not discharged by their scalar return type" {
    const source: [:0]const u8 =
        \\fn encoded(pointer: *u32) usize { return @intFromPtr(pointer); }
        \\fn use(pointer: *u32) void { _ = encoded(pointer); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "encoded").?);
    try std.testing.expect(!returned.complete or returned.alternatives.len != 0);
}

test "array child values are classified through their canonical types" {
    const source: [:0]const u8 =
        \\fn scalar(values: [2]u32) [2]u32 { return values; }
        \\fn pointers(values: [2]*u32) [2]*u32 { return values; }
        \\fn use(scalars: [2]u32, addresses: [2]*u32) void {
        \\    _ = scalar(scalars);
        \\    _ = pointers(addresses);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "scalar").?));
    const pointer_array = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "pointers").?);
    _ = try expectAlternative(pointer_array, .{ .param = 0, .path = "" }, .payload_value, .payload_storage, "");
}

test "array result preserves a direct pointer loan rather than loading its pointee" {
    const source: [:0]const u8 =
        \\fn wrap(value: *[2]u8) [1]*[2]u8 { return .{value}; }
        \\fn addressed(values: []u8) [1]*u8 { return .{&values[0]}; }
        \\fn copy(values: [1]*[2]u8) [1]*[2]u8 { return values; }
        \\fn use(value: *[2]u8, values: []u8, pointers: [1]*[2]u8) void {
        \\    _ = wrap(value);
        \\    _ = addressed(values);
        \\    _ = copy(pointers);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const direct = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "wrap").?);
    try std.testing.expect(direct.complete);
    _ = try expectOnlyAlternative(direct, .{ .param = 0, .path = "" }, .pointer_value, .inline_storage, "");
    try std.testing.expect(!direct.direct_formal_loan);
    try std.testing.expect(direct.direct_formal_load == null);
    const addressed = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "addressed").?);
    try std.testing.expect(addressed.complete);
    _ = try expectOnlyAlternative(addressed, .{ .param = 0, .path = "" }, .cell_address, .backing_storage, "");
    const copied = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copy").?);
    try std.testing.expect(copied.complete);
    _ = try expectOnlyAlternative(copied, .{ .param = 0, .path = "" }, .payload_value, .payload_storage, "");
}

test "formal pointer loans require address-free pointees on every reachable arm" {
    const source: [:0]const u8 =
        \\const Deep = struct { borrowed: *u8 };
        \\const View = struct { selected: *[2]u8, borrowed: *u8 };
        \\const DeepView = struct { selected: *[2]u8, carrier: *Deep, nested: **u8 };
        \\fn known(value: *[2]u8) *[2]u8 { return value; }
        \\fn nested(value: **u8) **u8 { return value; }
        \\fn deep(value: *Deep) *Deep { return value; }
        \\fn copied(value: View) View { return value; }
        \\fn copiedDeep(value: DeepView) DeepView { return value; }
        \\fn array(value: *[2]u8, borrowed: *u8) [1]View {
        \\    return .{.{ .selected = value, .borrowed = borrowed }};
        \\}
        \\extern fn opaqueLoan(value: *[2]u8) *[2]u8;
        \\fn mixed(value: *[2]u8, choose: bool) *[2]u8 {
        \\    return if (choose) value else opaqueLoan(value);
        \\}
        \\fn use(value: *[2]u8, pointer: **u8, carrier: *Deep, view: View, deep_view: DeepView, choose: bool) void {
        \\    _ = known(value);
        \\    _ = nested(pointer);
        \\    _ = deep(carrier);
        \\    _ = copied(view);
        \\    _ = copiedDeep(deep_view);
        \\    _ = array(value, view.borrowed);
        \\    _ = mixed(value, choose);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const known = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "known").?);
    _ = try expectOnlyAlternative(known, .{ .param = 0, .path = "" }, .pointer_value, .inline_storage, "");
    const nested = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "nested").?);
    try std.testing.expect(!nested.complete);
    _ = try expectAlternative(nested, .{ .param = 0, .path = "" }, .pointer_value, .inline_storage, "");
    const deep = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "deep").?);
    try std.testing.expect(!deep.complete);
    _ = try expectAlternative(deep, .{ .param = 0, .path = "" }, .pointer_value, .inline_storage, "");
    const copied = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copied").?);
    try std.testing.expect(copied.complete);
    _ = try expectAlternative(copied, .{ .param = 0, .path = "selected" }, .payload_value, .payload_storage, "selected");
    _ = try expectAlternative(copied, .{ .param = 0, .path = "borrowed" }, .payload_value, .payload_storage, "borrowed");
    const copied_deep = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copiedDeep").?);
    try std.testing.expect(!copied_deep.complete);
    _ = try expectAlternative(copied_deep, .{ .param = 0, .path = "selected" }, .payload_value, .payload_storage, "selected");
    _ = try expectAlternative(copied_deep, .{ .param = 0, .path = "carrier" }, .payload_value, .payload_storage, "carrier");
    _ = try expectAlternative(copied_deep, .{ .param = 0, .path = "nested" }, .payload_value, .payload_storage, "nested");
    const array = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "array").?);
    try std.testing.expect(array.complete);
    _ = try expectAlternative(array, .{ .param = 0, .path = "" }, .pointer_value, .inline_storage, "selected");
    _ = try expectAlternative(array, .{ .param = 1, .path = "" }, .pointer_value, .inline_storage, "borrowed");
    const mixed = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "mixed").?);
    try std.testing.expect(!mixed.complete);
    _ = try expectAlternative(mixed, .{ .param = 0, .path = "" }, .pointer_value, .inline_storage, "");
}

test "a failed returned-storage walk retires its visiting key and can be retried" {
    const source: [:0]const u8 =
        \\fn borrowed(bytes: []u32) []u32 { return bytes; }
        \\fn use(bytes: []u32) void { _ = borrowed(bytes); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    budget.clear();
    defer budget.clear();
    const token = callNamed(typed.tree(), "borrowed").?;
    var remaining: u32 = 3;
    try std.testing.expectError(error.AnalysisBudgetExceeded, returnedStorageAt(
        typed.cache,
        token,
        .{ .remaining = &remaining },
    ));
    _ = try expectOnlyAlternative(
        try returnedStorageOf(typed.cache, token),
        .{ .param = 0, .path = "" },
        .pointer_value,
        .backing_storage,
        "",
    );
}

fn allocationFailureReturnedStorage(gpa: std.mem.Allocator, typed: *Typed) !void {
    // Toolchain discovery and the semantic context are already valid. Each
    // attempt owns a fresh cache so prior memo entries cannot bypass a failing
    // query allocation, and that cache retires before the resolver/context.
    var cache = FileCache.init(gpa, typed.tree());
    defer cache.deinit();
    cache.setZls(&typed.resolver);
    cache.module_id = typed.resolver.handle.module;
    const token = callNamed(typed.tree(), "borrowed").?;
    const returned = try returnedStorageOf(&cache, token);
    _ = try expectOnlyAlternative(
        returned,
        .{ .param = 0, .path = "bytes" },
        .pointer_value,
        .backing_storage,
        "",
    );
}

test "returned-storage allocation failures release scratch and owned memo storage" {
    const source: [:0]const u8 =
        \\const Box = struct { bytes: []u32 };
        \\fn borrowed(box: *Box) []u32 { return box.bytes; }
        \\fn use(box: *Box) void { _ = borrowed(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        allocationFailureReturnedStorage,
        .{typed},
    );
}

test "reading a byte and copying a pointer-free array return no borrowed storage" {
    const source: [:0]const u8 =
        \\fn byte(bytes: []const u8) u8 { return bytes[0]; }
        \\fn array(bytes: *const [2]u8) [2]u8 { return bytes.*; }
        \\fn use(bytes: []const u8, pair: *const [2]u8) void {
        \\    _ = byte(bytes);
        \\    _ = array(pair);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "byte").?));
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "array").?));
}

test "excluded returned-storage sources fail without a negative memo and can be retried" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{
        .sub_path = "remote.zig",
        .data = "pub fn view(bytes: []const u8) []const u8 { return bytes; }",
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    const remote = try std.fs.path.join(gpa, &.{ directory, "remote.zig" });
    defer gpa.free(remote);
    var context: Typed.engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory}, .excludes = &.{remote} };
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, path,
        \\const remote = @import("remote.zig");
        \\fn use(bytes: []const u8) void { _ = remote.view(bytes); }
    );
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.module_id = resolver.handle.module;
    const token = callNamed(cache.tree, "view").?;
    try std.testing.expectError(error.SourceExcluded, returnedStorageAt(&cache, token, .{}));
    try std.testing.expect(!cache.actual_callees.contains(token));
    context.store.source_policy = .{ .roots = &.{directory} };
    _ = try expectOnlyAlternative(
        try returnedStorageOf(&cache, token),
        .{ .param = 0, .path = "" },
        .pointer_value,
        .backing_storage,
        "",
    );
}

test "returned vtable addresses distinguish explicit comptime and global constants from runtime cells" {
    const source: [:0]const u8 =
        \\const VTable = struct { draw: *const fn (*u32) void };
        \\fn draw(pointer: *u32) void { pointer.* += 1; }
        \\const global: VTable = .{ .draw = draw };
        \\fn explicit() *const VTable {
        \\    const vtable: VTable = comptime .{ .draw = draw };
        \\    return &vtable;
        \\}
        \\fn staticGlobal() *const VTable { return &global; }
        \\fn runtime(callback: *const fn (*u32) void) *const VTable {
        \\    const vtable: VTable = .{ .draw = callback };
        \\    return &vtable;
        \\}
        \\fn use(callback: *const fn (*u32) void) void {
        \\    _ = explicit();
        \\    _ = staticGlobal();
        \\    _ = runtime(callback);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "explicit").?));
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "staticGlobal").?));
    try expectUnknown(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "runtime").?));
}

test "static outer cells do not certify mutable deep pointer payloads" {
    const source: [:0]const u8 =
        \\const Holder = struct { slot: **u32 };
        \\var slot: *u32 = undefined;
        \\const global: Holder = .{ .slot = &slot };
        \\fn explicit() *const Holder {
        \\    const holder: Holder = comptime .{ .slot = &slot };
        \\    return &holder;
        \\}
        \\fn staticGlobal() *const Holder { return &global; }
        \\fn use() void { _ = explicit(); _ = staticGlobal(); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectUnknown(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "explicit").?));
    try expectUnknown(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "staticGlobal").?));
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const Holder = struct { slot: **u32 };
        \\var slot: *u32 = undefined;
        \\fn leak() *const Holder {
        \\    var value: u32 = 1;
        \\    slot = &value;
        \\    const holder: Holder = comptime .{ .slot = &slot };
        \\    return &holder;
        \\}
    );
}

test "borrow consumer treats explicit comptime and global vtables as static but preserves runtime cells" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const VTable = struct { draw: *const fn (*u32) void };
        \\const View = struct { ptr: *u32, vtable: *const VTable };
        \\fn draw(pointer: *u32) void { pointer.* += 1; }
        \\fn make(ptr: *u32) View {
        \\    const vtable: VTable = comptime .{ .draw = draw };
        \\    return .{ .ptr = ptr, .vtable = &vtable };
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const VTable = struct { draw: *const fn (*u32) void };
        \\const View = struct { ptr: *u32, vtable: *const VTable };
        \\fn draw(pointer: *u32) void { pointer.* += 1; }
        \\const vtable: VTable = .{ .draw = draw };
        \\fn make(ptr: *u32) View { return .{ .ptr = ptr, .vtable = &vtable }; }
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const VTable = struct { draw: *const fn (*u32) void };
        \\const View = struct { ptr: *u32, vtable: *const VTable };
        \\fn make(ptr: *u32, callback: *const fn (*u32) void) View {
        \\    const vtable: VTable = .{ .draw = callback };
        \\    return .{ .ptr = ptr, .vtable = &vtable };
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const VTable = struct { draw: *const fn (*u32) void };
        \\const View = struct { ptr: *u32, vtable: *const VTable };
        \\fn draw(pointer: *u32) void { pointer.* += 1; }
        \\fn make(ptr: *u32, callback: *const fn (*u32) void) View {
        \\    var vtable: VTable = comptime .{ .draw = draw };
        \\    vtable.draw = callback;
        \\    return .{ .ptr = ptr, .vtable = &vtable };
        \\}
    );
}

test "borrow consumer treats tag names as static and preserves a copied sibling loan" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const Tag = enum { first, second };
        \\fn reason(input: []const Tag) []const u8 { return @tagName(input[0]); }
        \\fn detect() []const u8 {
        \\    var tags: [1]Tag = .{.first};
        \\    return reason(&tags);
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const Tag = enum { first, second };
        \\const Result = struct { reason: []const u8, bytes: []const u8 };
        \\fn mixed(tag: Tag, input: []const u8) Result {
        \\    return .{ .reason = @tagName(tag), .bytes = input };
        \\}
        \\fn detect() Result {
        \\    var bytes: [2]u8 = .{1, 2};
        \\    return mixed(.first, &bytes);
        \\}
    );
}

test "borrow consumer distinguishes allocated bytes from copied pointer payloads" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn bytes(gpa: std.mem.Allocator, input: []const u8) ![]u8 {
        \\    return gpa.dupe(u8, input);
        \\}
        \\fn detect(gpa: std.mem.Allocator) ![]u8 {
        \\    var input: [2]u8 = .{1, 2};
        \\    return bytes(gpa, &input);
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const std = @import("std");
        \\fn pointers(gpa: std.mem.Allocator, input: []const *u8) ![]*u8 {
        \\    return gpa.dupe(*u8, input);
        \\}
        \\fn detect(gpa: std.mem.Allocator) ![]*u8 {
        \\    var input: [2]u8 = .{1, 2};
        \\    const cells = [_]*u8{&input[0]};
        \\    return pointers(gpa, &cells);
        \\}
    );
}

test "selected formal retention distinguishes scalar copies headers outward stores and cycles" {
    const source: [:0]const u8 =
        \\var saved: []const u8 = "";
        \\fn scalar(input: []const u8) u8 { return input[0]; }
        \\fn header(input: []const u8) []const u8 { return input; }
        \\fn store(input: []const u8) u8 { saved = input; return input[0]; }
        \\fn cycle(input: []const u8) u8 { return cycle(input); }
        \\extern fn opaqueRead(input: []const u8) u8;
        \\fn use(input: []const u8) void {
        \\    _ = scalar(input);
        \\    _ = header(input);
        \\    _ = store(input);
        \\    _ = cycle(input);
        \\    _ = opaqueRead(input);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.expect(try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "scalar").?, 0, .{}));
    for ([_][]const u8{ "header", "store", "cycle", "opaqueRead" }) |name| {
        try std.testing.expect(!try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), name).?, 0, .{}));
    }
}

test "selected formal certificates do not certify unrelated deep returned storage" {
    const source: [:0]const u8 =
        \\const Model = struct { nested: **u8 };
        \\fn model(receiver: *Model, input: []const u8) *Model {
        \\    _ = input.len;
        \\    return receiver;
        \\}
        \\fn use(receiver: *Model, input: []const u8) void { _ = model(receiver, input); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const token = callNamed(typed.tree(), "model").?;
    try std.testing.expect(try formalNonRetentionAt(typed.cache, token, 1, .{}));
    try std.testing.expect(!try formalNonRetentionAt(typed.cache, token, 0, .{}));
    try std.testing.expect(!(try returnedStorageOf(typed.cache, token)).complete);
}

test "failed selected formal queries retire active certificates without negative publication" {
    const source: [:0]const u8 =
        \\fn scalar(input: []const u8) u8 { return input[0]; }
        \\fn use(input: []const u8) void { _ = scalar(input); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    budget.clear();
    defer budget.clear();
    var remaining: u32 = 3;
    const token = callNamed(typed.tree(), "scalar").?;
    try std.testing.expectError(error.AnalysisBudgetExceeded, formalNonRetentionAt(typed.cache, token, 0, .{ .remaining = &remaining }));
    try std.testing.expect(try formalNonRetentionAt(typed.cache, token, 0, .{}));
}

test "borrow consumer discharges only selected input and preserves receiver alias storage" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const Model = struct { nested: **u8 };
        \\fn model(receiver: *Model, input: []const u8) *Model {
        \\    _ = input.len;
        \\    return receiver;
        \\}
        \\fn detect(receiver: *Model) *Model {
        \\    var input: [2]u8 = .{1, 2};
        \\    return model(receiver, &input);
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const Model = struct { bytes: []const u8 };
        \\fn model(receiver: *Model, input: []const u8) *Model {
        \\    _ = input.len;
        \\    return receiver;
        \\}
        \\fn detect() *Model {
        \\    var input: [2]u8 = .{1, 2};
        \\    var receiver: Model = .{ .bytes = &input };
        \\    return model(&receiver, &input);
        \\}
    );
}

test "allocator requirements are instantiated for each actual caller" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\fn copy(gpa: std.mem.Allocator, input: []const u8) ![]u8 { return gpa.dupe(u8, input); }
        \\fn heap(input: []const u8) void { _ = copy(std.heap.page_allocator, input); }
        \\fn stack(input: []const u8) void {
        \\    var backing: [128]u8 = undefined;
        \\    var fixed = std.heap.FixedBufferAllocator.init(&backing);
        \\    _ = copy(fixed.allocator(), input);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var tokens_found: [2]Ast.TokenIndex = undefined;
    var count: usize = 0;
    for (0..typed.tree().nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = typed.tree().fullCall(&buffer, node) orelse continue;
        const name = typed.tree().tokenSlice(typed.tree().lastToken(call.ast.fn_expr));
        if (!std.mem.eql(u8, name, "copy")) continue;
        tokens_found[count] = @import("fresh_storage.zig").calleeQueryToken(typed.tree(), call);
        count += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), count);
    const first = @min(tokens_found[0], tokens_found[1]);
    const second = @max(tokens_found[0], tokens_found[1]);
    try std.testing.expect((try returnedStorageOf(typed.cache, first)).complete);
    try std.testing.expect(!(try returnedStorageOf(typed.cache, second)).complete);
    try std.testing.expect((try returnedStorageOf(typed.cache, first)).complete);
}

test "aggregate allocator requirements bind actual providers rather than formal fields" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Packet = struct { bytes: []u8 };
        \\const Source = struct {
        \\    gpa: std.mem.Allocator, bytes: []const u8,
        \\    fn copy(self: Source) !Packet {
        \\        return .{ .bytes = try self.gpa.dupe(u8, self.bytes) };
        \\    }
        \\};
        \\fn heap(gpa: std.mem.Allocator, input: []const u8) void {
        \\    const source: Source = .{ .gpa = gpa, .bytes = input };
        \\    _ = source.copy();
        \\}
        \\fn stack(input: []const u8) void {
        \\    var backing: [128]u8 = undefined;
        \\    var fixed = std.heap.FixedBufferAllocator.init(&backing);
        \\    const source: Source = .{ .gpa = fixed.allocator(), .bytes = input };
        \\    _ = source.copy();
        \\}
        \\fn unbound(source: Source) void { _ = source.copy(); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var calls: [3]Ast.TokenIndex = undefined;
    var count: usize = 0;
    for (0..typed.tree().nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = typed.tree().fullCall(&buffer, node) orelse continue;
        const name = typed.tree().tokenSlice(typed.tree().lastToken(call.ast.fn_expr));
        if (!std.mem.eql(u8, name, "copy")) continue;
        try std.testing.expect(count < calls.len);
        calls[count] = @import("fresh_storage.zig").calleeQueryToken(typed.tree(), call);
        count += 1;
    }
    try std.testing.expectEqual(calls.len, count);
    std.mem.sort(Ast.TokenIndex, &calls, {}, std.sort.asc(Ast.TokenIndex));
    try expectNoBorrow(try returnedStorageOf(typed.cache, calls[0]));
    try std.testing.expect(!(try returnedStorageOf(typed.cache, calls[1])).complete);
    try std.testing.expect(!(try returnedStorageOf(typed.cache, calls[2])).complete);
    try expectNoBorrow(try returnedStorageOf(typed.cache, calls[0]));
}

test "borrow consumer retains Writer owned-slice stack transfers" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const std = @import("std");
        \\fn detect(gpa: std.mem.Allocator) ![]u8 {
        \\    var backing: [8]u8 = undefined;
        \\    var writer = std.Io.Writer.Allocating.initOwnedSlice(gpa, &backing);
        \\    return writer.toOwnedSlice();
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const std = @import("std");
        \\fn detect() ![]u8 {
        \\    var backing: [128]u8 = undefined;
        \\    var fixed = std.heap.FixedBufferAllocator.init(&backing);
        \\    var writer = std.Io.Writer.Allocating.init(fixed.allocator());
        \\    try writer.writer.writeAll("copied");
        \\    return writer.toOwnedSlice();
        \\}
    );
}

test "local backing projection does not inherit a pointer-bearing reader sibling" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Writer = struct { buffer: []u8, reader: []const []const u8 };
        \\fn bytes(gpa: std.mem.Allocator, reader: []const []const u8) ![]u8 {
        \\    const writer: Writer = .{ .buffer = try gpa.dupe(u8, reader[0]), .reader = reader };
        \\    return writer.buffer;
        \\}
        \\fn use(gpa: std.mem.Allocator, reader: []const []const u8) void { _ = bytes(gpa, reader); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?));
}

test "ordered local backing writes preserve borrowed alternatives" {
    const source: [:0]const u8 =
        \\const Writer = struct { buffer: []const u8 };
        \\fn bytes(first: []const u8, second: []const u8, choose: bool) []const u8 {
        \\    var writer: Writer = .{ .buffer = first };
        \\    if (choose) writer.buffer = second;
        \\    return writer.buffer;
        \\}
        \\fn use(first: []const u8, second: []const u8, choose: bool) void { _ = bytes(first, second, choose); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?);
    try std.testing.expect(!returned.complete);
    _ = try expectAlternative(returned, .{ .param = 0, .path = "" }, .pointer_value, .backing_storage, "");
    _ = try expectAlternative(returned, .{ .param = 1, .path = "" }, .pointer_value, .backing_storage, "");
}

test "selected formal coordinates include unnamed generic parameters" {
    const source: [:0]const u8 =
        \\fn copied(comptime _: type, input: []const u8) u8 { return input[0]; }
        \\fn borrowed(comptime _: type, input: []const u8) []const u8 { return input; }
        \\fn use(input: []const u8) void {
        \\    _ = copied(u8, input);
        \\    _ = borrowed(u8, input);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.expect(try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "copied").?, 1, .{}));
    try std.testing.expect(!try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "borrowed").?, 1, .{}));
    _ = try expectOnlyAlternative(
        try returnedStorageOf(typed.cache, callNamed(typed.tree(), "borrowed").?),
        .{ .param = 1, .path = "" },
        .pointer_value,
        .backing_storage,
        "",
    );
}

test "typed local allocating writer copies reader bytes rather than its storage" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn copy(gpa: std.mem.Allocator, reader: []const u8) ![]u8 {
        \\    var writer = std.Io.Writer.Allocating.init(gpa);
        \\    try writer.writer.writeAll(reader);
        \\    return writer.toOwnedSlice();
        \\}
        \\fn detect(gpa: std.mem.Allocator) ![]u8 {
        \\    var input: [2]u8 = .{1, 2};
        \\    return copy(gpa, &input);
        \\}
    );
}

test "module cell address proves returned array independence without certifying global pointer payloads" {
    const source: [:0]const u8 =
        \\var cell: u8 = 1;
        \\var saved: *u8 = &cell;
        \\fn detached(_: [1]*u8) [1]*u8 { return .{&cell}; }
        \\fn retained(input: [1]*u8) [1]*u8 {
        \\    saved = input[0];
        \\    return .{saved};
        \\}
        \\fn use(input: [1]*u8) void { _ = detached(input); _ = retained(input); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "detached").?));
    try std.testing.expect(try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "detached").?, 0, .{}));
    try std.testing.expect(!try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "retained").?, 0, .{}));
}

test "selected formal certificate abstains on inline assembly outward effects" {
    const source: [:0]const u8 =
        \\var saved: [*]const u8 = undefined;
        \\fn capture(input: []const u8) void {
        \\    asm volatile ("movq %[src], %[dst]"
        \\        : [dst] "=m" (saved)
        \\        : [src] "r" (input.ptr)
        \\    );
        \\}
        \\fn use(input: []const u8) void { capture(input); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.expect(!try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "capture").?, 0, .{}));
}

test "constructor projection binds its actual allocator without borrowing reader siblings" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Cell = struct {
        \\    buffer: []u8, reader: []const []const u8,
        \\    fn init(gpa: std.mem.Allocator, reader: []const []const u8) !Cell {
        \\        return .{ .buffer = try gpa.dupe(u8, reader[0]), .reader = reader };
        \\    }
        \\};
        \\fn bytes(gpa: std.mem.Allocator, reader: []const []const u8) ![]u8 {
        \\    const cell = try Cell.init(gpa, reader);
        \\    return cell.buffer;
        \\}
        \\fn use(gpa: std.mem.Allocator, reader: []const []const u8) void { _ = bytes(gpa, reader); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?));
}

test "private canonical vtable writes preserve both backing loans" {
    const source: [:0]const u8 =
        \\const Ops = struct { store: *const fn (*Cell, []const u8) void };
        \\const Cell = struct {
        \\    buffer: []const u8, ops: *const Ops,
        \\    fn init(first: []const u8) Cell { return .{ .buffer = first, .ops = &operations }; }
        \\};
        \\const operations: Ops = .{ .store = store };
        \\fn store(cell: *Cell, second: []const u8) void { cell.buffer = second; }
        \\fn invoke(cell: *Cell, second: []const u8) void { cell.ops.store(cell, second); }
        \\fn bytes(first: []const u8, second: []const u8) []const u8 {
        \\    var cell = Cell.init(first);
        \\    invoke(&cell, second);
        \\    return cell.buffer;
        \\}
        \\fn use(first: []const u8, second: []const u8) void { _ = bytes(first, second); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?);
    try std.testing.expect(!returned.complete);
    _ = try expectAlternative(returned, .{ .param = 0, .path = "" }, .pointer_value, .backing_storage, "");
    _ = try expectAlternative(returned, .{ .param = 1, .path = "" }, .pointer_value, .backing_storage, "");
}

test "private normal effects exclude error-only cleanup" {
    const source: [:0]const u8 =
        \\const Cell = struct { buffer: []const u8 };
        \\fn edit(cell: *Cell, second: []const u8, fail: bool) !void {
        \\    errdefer cell.buffer = second;
        \\    if (fail) return error.Failed;
        \\}
        \\fn bytes(first: []const u8, second: []const u8, fail: bool) ![]const u8 {
        \\    var cell: Cell = .{ .buffer = first };
        \\    try edit(&cell, second, fail);
        \\    return cell.buffer;
        \\}
        \\fn use(first: []const u8, second: []const u8, fail: bool) void { _ = bytes(first, second, fail); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    _ = try expectOnlyAlternative(
        try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?),
        .{ .param = 0, .path = "" },
        .pointer_value,
        .backing_storage,
        "",
    );
}

test "caught private failures retain error-only cleanup loans" {
    const source: [:0]const u8 =
        \\const Cell = struct { buffer: []const u8 };
        \\fn edit(cell: *Cell, second: []const u8, fail: bool) !void {
        \\    errdefer cell.buffer = second;
        \\    if (fail) return error.Failed;
        \\}
        \\fn bytes(first: []const u8, second: []const u8, fail: bool) []const u8 {
        \\    var cell: Cell = .{ .buffer = first };
        \\    edit(&cell, second, fail) catch {};
        \\    return cell.buffer;
        \\}
        \\fn use(first: []const u8, second: []const u8, fail: bool) void { _ = bytes(first, second, fail); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?);
    try std.testing.expect(!returned.complete);
    _ = try expectAlternative(returned, .{ .param = 0, .path = "" }, .pointer_value, .backing_storage, "");
    _ = try expectAlternative(returned, .{ .param = 1, .path = "" }, .pointer_value, .backing_storage, "");
}

test "private backing effects inspect pointer-bearing aggregate actuals" {
    const source: [:0]const u8 =
        \\const Cell = struct { buffer: []const u8 };
        \\const View = struct { cell: *Cell };
        \\fn mutate(view: View, input: []const u8) void { view.cell.buffer = input; }
        \\fn bytes(first: []const u8, input: []const u8) []const u8 {
        \\    var cell: Cell = .{ .buffer = first };
        \\    const view: View = .{ .cell = &cell };
        \\    mutate(view, input);
        \\    return cell.buffer;
        \\}
        \\fn use(first: []const u8, input: []const u8) void { _ = bytes(first, input); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?);
    try std.testing.expect(!returned.complete);
    _ = try expectAlternative(returned, .{ .param = 0, .path = "" }, .pointer_value, .backing_storage, "");
    _ = try expectAlternative(returned, .{ .param = 1, .path = "" }, .pointer_value, .backing_storage, "");
}

test "private backing writes follow a const pointer alias to a nested cell" {
    const source: [:0]const u8 =
        \\const Cell = struct { buffer: []const u8 };
        \\const Outer = struct { cell: Cell };
        \\fn store(cell: *Cell, input: []const u8) void { cell.buffer = input; }
        \\fn bytes(first: []const u8, input: []const u8) []const u8 {
        \\    var outer: Outer = .{ .cell = .{ .buffer = first } };
        \\    const alias = &outer.cell;
        \\    store(alias, input);
        \\    return outer.cell.buffer;
        \\}
        \\fn use(first: []const u8, input: []const u8) void { _ = bytes(first, input); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?);
    try std.testing.expect(!returned.complete);
    _ = try expectAlternative(returned, .{ .param = 0, .path = "" }, .pointer_value, .backing_storage, "");
    _ = try expectAlternative(returned, .{ .param = 1, .path = "" }, .pointer_value, .backing_storage, "");
}

test "mutable callback tables do not authenticate their obsolete initializer" {
    const source: [:0]const u8 =
        \\const Ops = struct { store: *const fn (*Cell, []const u8) void };
        \\const Cell = struct { buffer: []const u8, ops: Ops };
        \\fn noop(_: *Cell, _: []const u8) void {}
        \\fn retain(cell: *Cell, input: []const u8) void { cell.buffer = input; }
        \\fn change(ops: *Ops) void { ops.store = retain; }
        \\fn bytes(input: []const u8) []const u8 {
        \\    var cell: Cell = .{ .buffer = &.{}, .ops = .{ .store = noop } };
        \\    change(&cell.ops);
        \\    cell.ops.store(&cell, input);
        \\    return cell.buffer;
        \\}
        \\fn use(input: []const u8) void { _ = bytes(input); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.expect(!(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?)).complete);
}

test "replaced formal allocator fields do not bind the caller old provider" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Cell = struct { allocator: std.mem.Allocator };
        \\fn make(cell: *Cell, input: []u8) ?[*]u8 {
        \\    var fixed = std.heap.FixedBufferAllocator.init(input);
        \\    cell.allocator = fixed.allocator();
        \\    return cell.allocator.rawAlloc(1, .of(u8), @returnAddress());
        \\}
        \\fn use(cell: *Cell, input: []u8) void { _ = make(cell, input); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.expect(!(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "make").?)).complete);
}

test "selected formal byte copies do not retain headers but pointer copies do" {
    const source: [:0]const u8 =
        \\fn bytes(destination: []u8, input: []const u8) void { @memcpy(destination, input); }
        \\fn pointers(destination: []*u8, input: []const *u8) void { @memcpy(destination, input); }
        \\fn use(destination: []u8, input: []const u8, cells: []*u8, pointers_in: []const *u8) void {
        \\    bytes(destination, input);
        \\    pointers(cells, pointers_in);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.expect(try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "bytes").?, 1, .{}));
    try std.testing.expect(!try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "pointers").?, 1, .{}));
}

test "actual allocating writer byte transfer has complete independent returned storage" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\fn copy(gpa: std.mem.Allocator, reader: []const u8) ![]u8 {
        \\    var writer = std.Io.Writer.Allocating.init(gpa);
        \\    try writer.writer.writeAll(reader);
        \\    return writer.toOwnedSlice();
        \\}
        \\fn use(gpa: std.mem.Allocator, reader: []const u8) void { _ = copy(gpa, reader); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copy").?));
}

test "overlapping union and reinterpreted scalar stores cannot certify backing headers" {
    // Scalar writes need a real typed location, not a scalar-only exemption.
    const source: [:0]const u8 =
        \\const Slot = union { buffer: []const u8, count: usize };
        \\const Cell = struct { slot: Slot };
        \\fn unionEdit(cell: *Cell, input: []const u8) void { cell.slot.count += input.len; }
        \\fn unionBytes(first: []const u8, input: []const u8) []const u8 {
        \\    var cell: Cell = .{ .slot = .{ .buffer = first } };
        \\    unionEdit(&cell, input);
        \\    return cell.slot.buffer;
        \\}
        \\const Header = struct { buffer: []const u8 };
        \\fn castEdit(cell: *Header, input: []const u8) void {
        \\    const raw: *usize = @ptrCast(&cell.buffer);
        \\    raw.* = input.len;
        \\}
        \\fn castBytes(first: []const u8, input: []const u8) []const u8 {
        \\    var cell: Header = .{ .buffer = first };
        \\    castEdit(&cell, input);
        \\    return cell.buffer;
        \\}
        \\fn copyEdit(cell: *Header, input: []const u8) void {
        \\    const raw: *[@sizeOf([]const u8)]u8 = @ptrCast(&cell.buffer);
        \\    @memcpy(raw, input[0..@sizeOf([]const u8)]);
        \\}
        \\fn copyBytes(first: []const u8, input: []const u8) []const u8 {
        \\    var cell: Header = .{ .buffer = first };
        \\    copyEdit(&cell, input);
        \\    return cell.buffer;
        \\}
        \\fn use(first: []const u8, input: []const u8) void {
        \\    _ = unionBytes(first, input);
        \\    _ = castBytes(first, input);
        \\    _ = copyBytes(first, input);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    for ([_][]const u8{ "unionBytes", "castBytes", "copyBytes" }) |name| {
        const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), name).?);
        try std.testing.expect(!returned.complete);
        _ = try expectAlternative(returned, .{ .param = 0, .path = "" }, .pointer_value, .backing_storage, "");
    }
}

test "byte copies and fills distinguish union header overlap from struct siblings" {
    // Identical byte writes affect pointer representation only in the union.
    const source: [:0]const u8 =
        \\const byte: u8 = 1;
        \\const Slot = extern union { pointer: *const u8, bytes: [@sizeOf(*const u8)]u8 };
        \\const Separate = struct { pointer: *const u8, bytes: [@sizeOf(*const u8)]u8 };
        \\fn unionCopy(input: *const u8) *const u8 {
        \\    var cell: Slot = .{ .pointer = &byte };
        \\    const raw: [*]const u8 = @ptrCast(&input);
        \\    @memcpy(cell.bytes[0..], raw[0..@sizeOf(*const u8)]);
        \\    return cell.pointer;
        \\}
        \\fn structCopy(input: *const u8) *const u8 {
        \\    var cell: Separate = .{ .pointer = &byte, .bytes = undefined };
        \\    const raw: [*]const u8 = @ptrCast(&input);
        \\    @memcpy(cell.bytes[0..], raw[0..@sizeOf(*const u8)]);
        \\    return cell.pointer;
        \\}
        \\fn unionFill(input: *const u8) *const u8 {
        \\    var cell: Slot = .{ .pointer = input };
        \\    @memset(cell.bytes[0..], 0);
        \\    return cell.pointer;
        \\}
        \\fn structFill(input: *const u8) *const u8 {
        \\    var cell: Separate = .{ .pointer = input, .bytes = undefined };
        \\    @memset(cell.bytes[0..], 0);
        \\    return cell.pointer;
        \\}
        \\fn use(input: *const u8) void {
        \\    _ = unionCopy(input);
        \\    _ = structCopy(input);
        \\    _ = unionFill(input);
        \\    _ = structFill(input);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const union_copy = callNamed(typed.tree(), "unionCopy").?;
    try std.testing.expect(!(try returnedStorageOf(typed.cache, union_copy)).complete);
    try std.testing.expect(!try formalNonRetentionAt(typed.cache, union_copy, 0, .{}));
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "structCopy").?));
    const union_fill = callNamed(typed.tree(), "unionFill").?;
    const filled = try returnedStorageOf(typed.cache, union_fill);
    try std.testing.expect(!filled.complete);
    _ = try expectAlternative(filled, .{ .param = 0, .path = "" }, .pointer_value, .inline_storage, "");
    try std.testing.expect(!try formalNonRetentionAt(typed.cache, union_fill, 0, .{}));
    _ = try expectOnlyAlternative(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "structFill").?), .{ .param = 0, .path = "" }, .pointer_value, .inline_storage, "");
}

test "typed parent-pointer provider projection keeps actual constructor requirements" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Child = struct { buffer: []u8 };
        \\const Parent = struct {
        \\    allocator: std.mem.Allocator, child: Child,
        \\    fn init(allocator: std.mem.Allocator) Parent {
        \\        return .{ .allocator = allocator, .child = .{ .buffer = &.{} } };
        \\    }
        \\};
        \\fn fill(child: *Child) !void {
        \\    const parent: *Parent = @fieldParentPtr("child", child);
        \\    parent.child.buffer = try parent.allocator.alloc(u8, 8);
        \\}
        \\fn bytes(allocator: std.mem.Allocator) ![]u8 {
        \\    var parent = Parent.init(allocator);
        \\    try fill(&parent.child);
        \\    return parent.child.buffer;
        \\}
        \\fn heap(allocator: std.mem.Allocator) void { _ = bytes(allocator); }
        \\fn stack() void {
        \\    var backing: [128]u8 = undefined;
        \\    var fixed = std.heap.FixedBufferAllocator.init(&backing);
        \\    _ = bytes(fixed.allocator());
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var calls: [2]Ast.TokenIndex = undefined;
    var count: usize = 0;
    for (0..typed.tree().nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [2]Ast.Node.Index = undefined;
        const call_node = TypeResolver.CallOperands.full(typed.tree(), &buffer, node) orelse continue;
        if (!std.mem.eql(u8, typed.tree().getNodeSource(call_node.ast.fn_expr), "bytes")) continue;
        try std.testing.expect(count < calls.len);
        calls[count] = call_node.queryToken(typed.tree(), node);
        count += 1;
    }
    try std.testing.expectEqual(calls.len, count);
    std.mem.sort(Ast.TokenIndex, &calls, {}, std.sort.asc(Ast.TokenIndex));
    try expectNoBorrow(try returnedStorageOf(typed.cache, calls[0]));
    try std.testing.expect(!(try returnedStorageOf(typed.cache, calls[1])).complete);
}

test "canonical type selection does not enter recursive runtime cell effects" {
    const source: [:0]const u8 =
        \\fn Factory(comptime T: type, comptime normalize: bool) type {
        \\    if (normalize) return Factory(T, false);
        \\    return struct { value: T };
        \\}
        \\const Cell = struct { buffer: []const u8 };
        \\fn touch(cell: *Cell) void { _ = Factory(u8, true); _ = cell; }
        \\fn bytes(input: []const u8) []const u8 {
        \\    var cell: Cell = .{ .buffer = input };
        \\    touch(&cell);
        \\    return cell.buffer;
        \\}
        \\fn use(input: []const u8) void { _ = bytes(input); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    _ = try expectOnlyAlternative(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "bytes").?), .{ .param = 0, .path = "" }, .pointer_value, .backing_storage, "");
}

const ExpressionLoanTestSite = struct {
    body: Ast.Node.Index,
    node: Ast.Node.Index,
    horizon: Ast.TokenIndex,
};

fn expressionLoanTestSite(
    tree: *const Ast,
    function_name: []const u8,
    expression: []const u8,
    occurrence: usize,
) !ExpressionLoanTestSite {
    var body: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .fn_decl) continue;
        const declaration: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration) orelse continue;
        const name = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name), function_name)) continue;
        body = tokens.bodyOf(tree, declaration);
        break;
    }
    const function_body = body orelse return error.TestExpectedFunction;
    var previous: ?Ast.TokenIndex = null;
    var found: ?Ast.Node.Index = null;
    for (0..occurrence + 1) |_| {
        var selected: ?Ast.Node.Index = null;
        for (tree.nodes.items(.tag), 0..) |_, raw| {
            const node: Ast.Node.Index = @enumFromInt(raw);
            const first = tree.firstToken(node);
            if (first < tree.firstToken(function_body) or tree.lastToken(node) > tree.lastToken(function_body)) continue;
            if (previous) |last| if (first <= last) continue;
            if (!std.mem.eql(u8, tree.getNodeSource(node), expression)) continue;
            if (selected == null or first < tree.firstToken(selected.?)) selected = node;
        }
        const node = selected orelse return error.TestExpectedExpression;
        previous = tree.firstToken(node);
        found = node;
    }
    return .{ .body = function_body, .node = found.?, .horizon = previous.? };
}

fn expressionLoanTestBinding(
    cache: *FileCache,
    site: ExpressionLoanTestSite,
    name: []const u8,
) !Ast.TokenIndex {
    for (cache.tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .fn_decl) continue;
        const declaration: Ast.Node.Index = @enumFromInt(raw);
        if (tokens.bodyOf(cache.tree, declaration) != site.body) continue;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(cache.tree, &buffer, declaration) orelse continue;
        const bindings = (try cache.localBindings(proto, site.body)).*;
        return (bindings.findAt(name, site.horizon) orelse return error.TestExpectedBinding).name_token;
    }
    return error.TestExpectedFunction;
}

fn expectExpressionLoan(answer: ExpressionLoans, expected: ExpressionLoan) !void {
    for (answer.loans) |loan| {
        if (loan.binding_token != expected.binding_token or loan.origin != expected.origin) continue;
        try std.testing.expectEqual(expected.derivation, loan.derivation);
        try std.testing.expectEqual(expected.scalar_cell, loan.scalar_cell);
        return;
    }
    return error.TestExpectedExpressionLoan;
}

fn expectNoExpressionLoan(answer: ExpressionLoans, binding_token: Ast.TokenIndex) !void {
    for (answer.loans) |loan| {
        if (loan.binding_token == binding_token) return error.TestUnexpectedExpressionLoan;
    }
}

test "out parameter map constructors complete within returned storage allowance" {
    const bytes = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, "test/fixtures/missing_errdefer_on_out_param.zig", std.testing.allocator, .limited(4096));
    defer std.testing.allocator.free(bytes);
    const source = try std.testing.allocator.dupeZ(u8, bytes);
    defer std.testing.allocator.free(source);
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    defer budget.clear();
    inline for (.{ .{ "initBuggy", 2 }, .{ "initFixed", 4 } }) |case| {
        budget.clear();
        const site = try expressionLoanTestSite(typed.tree(), case[0], "result", case[1]);
        var remaining: u32 = work_limit;
        var query = ExpressionLoanQuery.init(.{
            .cache = typed.cache,
            .body = site.body,
            .scratch = &arena,
            .context = .{ .frame = typed.resolver.resolutionFrame(), .remaining = &remaining },
        });
        _ = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expect(work_limit - remaining < 35_000);
        try std.testing.expect(budget.peek() == null);
    }
    const testing = @import("../testing.zig");
    const borrow = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig");
    const leak = @import("../rules/errdefer/missing_errdefer_on_out_param.zig");
    try testing.expectNoFireTyped(borrow.check, source);
    var findings = try testing.runRuleTyped(std.testing.allocator, leak.check, source);
    defer testing.freeProblems(std.testing.allocator, &findings);
    try std.testing.expectEqual(@as(usize, 2), findings.items.len);
    for (findings.items, 0..) |finding, index| {
        try std.testing.expectEqualStrings("missing-errdefer-on-out-param", finding.rule_id);
        try std.testing.expectEqual(@as(u32, 15) + @as(u32, @intCast(index)), finding.start.line);
        try std.testing.expectEqual(if (index == 0) @as(u32, 31) else @as(u32, 27), finding.start.column);
        try std.testing.expectEqual(if (index == 0) @as(u32, 50) else @as(u32, 46), finding.end.column);
    }
}

test "canonical expression loans distinguish complete empty values from unknown pointers" {
    const source: [:0]const u8 =
        \\extern fn opaqueValue() *u8;
        \\fn scalar() u32 { const count: u32 = 3; return count + 1; }
        \\fn external(bytes: []const u8) []const u8 { return bytes; }
        \\fn staticBytes() []const u8 { return "safe"; }
        \\fn absent() ?*u8 { return null; }
        \\fn undefinedPointer() *u8 { return undefined; }
        \\fn reconstructed(bits: usize) *u8 { return @ptrFromInt(bits); }
        \\fn unknownCall() *u8 { return opaqueValue(); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const cases = .{
        .{ "scalar", "count + 1", true },
        .{ "external", "bytes", true },
        .{ "staticBytes", "\"safe\"", true },
        .{ "absent", "null", true },
        .{ "undefinedPointer", "undefined", false },
        .{ "reconstructed", "@ptrFromInt(bits)", false },
        .{ "unknownCall", "opaqueValue()", false },
    };
    inline for (cases) |case| {
        const site = try expressionLoanTestSite(typed.tree(), case[0], case[1], 0);
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "" }, .horizon = site.horizon, .domain = .normal });
        try std.testing.expectEqual(case[2], answer.complete);
        try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
    }
}

test "canonical expression loans distinguish finite wide enum results from opaque address results" {
    const source: [:0]const u8 =
        \\const Object = enum(u64) { integer = 1, floating = 2 };
        \\const Open = enum(u64) { integer = 1, _ };
        \\extern fn selectObject(values: *const [2]Object) ?Object;
        \\extern fn selectAddress(values: *const [2]Object) ?*const Object;
        \\extern fn selectBits(values: *const [2]Object) Open;
        \\fn safe() ?Object {
        \\    const args: [2]Object = .{ .integer, .floating };
        \\    return selectObject(&args);
        \\}
        \\fn unsafe() ?*const Object {
        \\    const args: [2]Object = .{ .integer, .floating };
        \\    return selectAddress(&args);
        \\}
        \\fn unknownBits() Open {
        \\    const args: [2]Object = .{ .integer, .floating };
        \\    return selectBits(&args);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{
        .{ "safe", "selectObject(&args)", true },
        .{ "unsafe", "selectAddress(&args)", false },
        .{ "unknownBits", "selectBits(&args)", false },
    }) |case| {
        const site = try expressionLoanTestSite(typed.tree(), case[0], case[1], 0);
        const token = try expressionLoanTestBinding(typed.cache, site, "args");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        if (case[2]) {
            try std.testing.expect(answer.complete);
            try expectNoExpressionLoan(answer, token);
        } else {
            try std.testing.expect(!answer.complete);
            try std.testing.expect(answer.loans.len != 0);
        }
    }
}

test "borrow consumer accepts finite wide enum results but rejects opaque pointer aliases" {
    const testing = @import("../testing.zig");
    const borrow = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig");
    try testing.expectNoFireTyped(borrow.check,
        \\const Object = enum(u64) { integer = 1, floating = 2 };
        \\extern fn join(values: *const [2]Object) ?Object;
        \\fn safe() ?Object {
        \\    const args: [2]Object = .{ .integer, .floating };
        \\    return join(&args);
        \\}
    );
    try testing.expectFiresTyped(borrow.check, "borrowed-slice-into-stack-buffer-returned",
        \\const Object = enum(u64) { integer = 1, floating = 2 };
        \\extern fn lookup(values: *const [2]Object) ?*const Object;
        \\fn unsafe() ?*const Object {
        \\    const args: [2]Object = .{ .integer, .floating };
        \\    return lookup(&args);
        \\}
    );
}

test "canonical expression loans discard synchronous scalar outparam dependencies but retain encoded addresses" {
    const source: [:0]const u8 =
        \\const Kind = enum { integer, floating };
        \\fn scalar(kind: *Kind, value: u64) !u64 { kind.* = .integer; return value; }
        \\fn encode(value: *u8) usize { return @intFromPtr(value); }
        \\fn safe(value: u64) !struct { kind: Kind, word: u64 } {
        \\    var kind: Kind = .floating;
        \\    const word = try scalar(&kind, value);
        \\    return .{ .kind = kind, .word = word };
        \\}
        \\fn unsafe() usize {
        \\    var local: u8 = 1;
        \\    return encode(&local);
        \\}
        \\fn identity(bits: usize) usize { return bits; }
        \\fn forwarded() usize {
        \\    var local: u8 = 1;
        \\    return identity(@intFromPtr(&local));
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const safe = try expressionLoanTestSite(typed.tree(), "safe", ".{ .kind = kind, .word = word }", 0);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = safe.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = safe.node }, .horizon = safe.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
    const unsafe = try expressionLoanTestSite(typed.tree(), "unsafe", "encode(&local)", 0);
    var control = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = unsafe.body, .scratch = &arena, .context = .{} });
    const loan = try control.expressionLoansAt(.{ .selection = .{ .node = unsafe.node }, .horizon = unsafe.horizon });
    try std.testing.expect(loan.loans.len != 0);
    const forwarded = try expressionLoanTestSite(typed.tree(), "forwarded", "identity(@intFromPtr(&local))", 0);
    var forwarding = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = forwarded.body, .scratch = &arena, .context = .{} });
    const encoded = try forwarding.expressionLoansAt(.{ .selection = .{ .node = forwarded.node }, .horizon = forwarded.horizon });
    try std.testing.expect(encoded.loans.len != 0);
}

test "canonical scalar proofs preserve address bits written through outparams and indexed stores" {
    const source: [:0]const u8 =
        \\fn set(bits: *usize, pointer: *u8) void { bits.* = @intFromPtr(pointer); }
        \\fn outparam() usize {
        \\    var local: u8 = 1;
        \\    var bits: usize = 0;
        \\    set(&bits, &local);
        \\    return bits + 0;
        \\}
        \\fn indexed() usize {
        \\    var local: u8 = 1;
        \\    var bits: [1]usize = .{0};
        \\    bits[0] = @intFromPtr(&local);
        \\    return bits[0] + 0;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{ .{ "outparam", "bits + 0" }, .{ "indexed", "bits[0] + 0" } }) |case| {
        const site = try expressionLoanTestSite(typed.tree(), case[0], case[1], 0);
        const local = try expressionLoanTestBinding(typed.cache, site, "local");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        var found = false;
        for (answer.loans) |loan| {
            if (loan.binding_token == local and loan.origin == .frame_cell) found = true;
        }
        try std.testing.expect(found);
    }
}

test "canonical scalar memcpy retains encoded actual byte payloads without their source headers" {
    const source: [:0]const u8 =
        \\const Bytes = [@sizeOf(usize)]u8;
        \\fn copy(destination: []u8, input: []const u8) void { @memcpy(destination, input); }
        \\fn encoded() usize {
        \\    var local: u8 = 1;
        \\    const bits: Bytes = @bitCast(@intFromPtr(&local));
        \\    var output: Bytes = @splat(0);
        \\    copy(&output, &bits);
        \\    return @bitCast(output);
        \\}
        \\fn numeric() usize {
        \\    const bits: Bytes = @bitCast(@as(usize, 7));
        \\    var output: Bytes = @splat(0);
        \\    copy(&output, &bits);
        \\    return @bitCast(output);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{ "encoded", "numeric" }) |name| {
        const site = try expressionLoanTestSite(typed.tree(), name, "@bitCast(output)", 0);
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        if (comptime std.mem.eql(u8, name, "encoded")) {
            const local = try expressionLoanTestBinding(typed.cache, site, "local");
            var found = false;
            for (answer.loans) |loan|
                if (loan.binding_token == local and loan.origin == .frame_cell) {
                    found = true;
                };
            try std.testing.expect(found);
        } else {
            for (answer.loans) |loan|
                try std.testing.expect(loan.origin != .frame_cell);
        }
    }
}

test "canonical expression loans retain dynamically called encoded outparam stores" {
    const source: [:0]const u8 =
        \\fn encoded(writer: *const fn (*usize, *u8) void) usize {
        \\    var local: u8 = 1;
        \\    var bits: usize = 0;
        \\    @call(.auto, writer, .{ &bits, &local });
        \\    return bits + 0;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "encoded", "bits + 0", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.binding_token == local and loan.origin == .frame_cell) return;
    }
    return error.TestExpectedLoan;
}

test "formal nonretention distinguishes called type metadata from runtime retention" {
    const source: [:0]const u8 =
        \\fn copy(comptime T: type, pointer: *T) T { return pointer.*; }
        \\fn keep(comptime T: type, pointer: *T) *T { return pointer; }
        \\fn scalar(pointer: *u8) u8 { return @call(.auto, copy, .{ u8, pointer }); }
        \\fn retained(pointer: *u8) *u8 { return @call(.auto, keep, .{ u8, pointer }); }
        \\pub fn main() void {
        \\    var local: u8 = 1;
        \\    _ = scalar(&local);
        \\    _ = retained(&local);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.expect(try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "scalar").?, 0, .{}));
    try std.testing.expect(!try formalNonRetentionAt(typed.cache, callNamed(typed.tree(), "retained").?, 0, .{}));
}

test "canonical scalar field copies preserve encoded actual payloads and discard numeric copies" {
    const source: [:0]const u8 =
        \\const Value = struct { words: [1]usize, label: []const u8 = "" };
        \\fn copy(value: Value) Value { return .{ .words = value.words }; }
        \\const Defaults = struct { const initial: Value = .{ .words = .{42} }; };
        \\fn numeric() Value {
        \\    const value = Defaults.initial;
        \\    return copy(value);
        \\}
        \\fn encoded() Value {
        \\    var local: u8 = 1;
        \\    const value: Value = .{ .words = .{@intFromPtr(&local)} };
        \\    return copy(value);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const numeric = try expressionLoanTestSite(typed.tree(), "numeric", "copy(value)", 0);
    var numeric_query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = numeric.body, .scratch = &arena, .context = .{} });
    const copied = try numeric_query.expressionLoansAt(.{ .selection = .{ .node = numeric.node }, .horizon = numeric.horizon });
    try std.testing.expect(copied.complete);
    try std.testing.expectEqual(@as(usize, 0), copied.loans.len);
    const encoded = try expressionLoanTestSite(typed.tree(), "encoded", "copy(value)", 0);
    const local = try expressionLoanTestBinding(typed.cache, encoded, "local");
    var encoded_query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = encoded.body, .scratch = &arena, .context = .{} });
    const retained = try encoded_query.expressionLoansAt(.{ .selection = .{ .node = encoded.node }, .horizon = encoded.horizon });
    for (retained.loans) |loan| {
        if (loan.binding_token == local and loan.origin == .frame_cell) return;
    }
    return error.TestExpectedLoan;
}

test "canonical scalar field reads retain actual callee encoded stores" {
    const source: [:0]const u8 =
        \\const Box = struct { bits: usize = 0 };
        \\fn write(box: *Box, pointer: *u8) usize {
        \\    box.bits = @intFromPtr(pointer);
        \\    return box.bits;
        \\}
        \\fn encoded() usize {
        \\    var local: u8 = 1;
        \\    var box: Box = .{};
        \\    return write(&box, &local);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "encoded", "write(&box, &local)", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.binding_token == local and loan.origin == .frame_cell) return;
    }
    return error.TestExpectedLoan;
}

test "canonical scalar dependency closure preserves encoded loop seeds and cuts numeric recurrences" {
    const source: [:0]const u8 =
        \\fn numeric(count: u8) usize {
        \\    var value: usize = 0;
        \\    var index: u8 = 0;
        \\    while (index < count) : (index += 1) value += index;
        \\    return value + 0;
        \\}
        \\fn encoded(count: u8) usize {
        \\    var local: u8 = 1;
        \\    var value: usize = @intFromPtr(&local);
        \\    var index: u8 = 0;
        \\    while (index < count) : (index += 1) value += index;
        \\    return value + 0;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const numeric = try expressionLoanTestSite(typed.tree(), "numeric", "value + 0", 0);
    var numeric_query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = numeric.body, .scratch = &arena, .context = .{} });
    const copied = try numeric_query.expressionLoansAt(.{ .selection = .{ .node = numeric.node }, .horizon = numeric.horizon });
    try std.testing.expect(copied.complete);
    try std.testing.expectEqual(@as(usize, 0), copied.loans.len);
    const encoded = try expressionLoanTestSite(typed.tree(), "encoded", "value + 0", 0);
    const local = try expressionLoanTestBinding(typed.cache, encoded, "local");
    var encoded_query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = encoded.body, .scratch = &arena, .context = .{} });
    const retained = try encoded_query.expressionLoansAt(.{ .selection = .{ .node = encoded.node }, .horizon = encoded.horizon });
    for (retained.loans) |loan| {
        if (loan.binding_token == local and loan.origin == .frame_cell) return;
    }
    return error.TestExpectedLoan;
}

test "borrow consumer distinguishes copied CPU feature bitsets from retained feature slices" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn riscvCpu(comptime arch: std.Target.Cpu.Arch) std.Target.Cpu {
        \\    const model = std.Target.Cpu.Model.generic(arch);
        \\    var cpu = model.toCpu(arch);
        \\    const features = [_]std.Target.riscv.Feature{ .m, .a, .f, .d };
        \\    cpu.features.addFeatureSet(std.Target.riscv.featureSet(&features));
        \\    cpu.features.populateDependencies(arch.allFeaturesList());
        \\    return cpu;
        \\}
        \\pub fn main() void { _ = riscvCpu(.riscv64); }
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const std = @import("std");
        \\const Cpu = struct { features: []const std.Target.riscv.Feature };
        \\pub fn detect() Cpu {
        \\    var features = [_]std.Target.riscv.Feature{ .m, .a, .f, .d };
        \\    return .{ .features = &features };
        \\}
    );
}

test "canonical expression loans separate direct scalar addresses from propagated addresses" {
    const source: [:0]const u8 =
        \\fn direct() *u32 { var cell: u32 = 1; return &cell; }
        \\fn propagated() *u32 { var cell: u32 = 1; const alias = &cell; return alias; }
        \\fn parameterCell(pointer: *u32) *const *u32 { return &pointer; }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const cases = .{
        .{ "direct", "&cell", "cell", true, true },
        .{ "propagated", "alias", "cell", false, true },
        .{ "parameterCell", "&pointer", "pointer", true, false },
    };
    inline for (cases) |case| {
        const site = try expressionLoanTestSite(typed.tree(), case[0], case[1], 0);
        const token = try expressionLoanTestBinding(typed.cache, site, case[2]);
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expect(answer.complete);
        try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
        try expectExpressionLoan(answer, .{
            .binding_token = token,
            .origin = .frame_cell,
            .derivation = if (case[3]) .direct_address else .propagated,
            .scalar_cell = case[4],
        });
        if (!case[3]) try expectNoExpressionLoan(answer, try expressionLoanTestBinding(typed.cache, site, "alias"));
    }
}

test "canonical expression loans retain every nested backing origin beside an unknown sibling" {
    const source: [:0]const u8 =
        \\const Inner = struct { bytes: []const u8 };
        \\const View = struct { first: []const u8, nested: Inner, repeated: []const u8, unknown: ?*u8 };
        \\fn known() View {
        \\    var first: [2]u8 = .{ 1, 2 };
        \\    var second: [2]u8 = .{ 3, 4 };
        \\    return .{ .first = &first, .nested = .{ .bytes = &second }, .repeated = &first, .unknown = null };
        \\}
        \\fn partial() View {
        \\    var first: [2]u8 = .{ 1, 2 };
        \\    var second: [2]u8 = .{ 3, 4 };
        \\    return .{ .first = &first, .nested = .{ .bytes = &second }, .repeated = &first, .unknown = undefined };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const cases = .{
        .{ "known", ".{ .first = &first, .nested = .{ .bytes = &second }, .repeated = &first, .unknown = null }", true },
        .{ "partial", ".{ .first = &first, .nested = .{ .bytes = &second }, .repeated = &first, .unknown = undefined }", false },
    };
    inline for (cases) |case| {
        const site = try expressionLoanTestSite(typed.tree(), case[0], case[1], 0);
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expectEqual(case[2], answer.complete);
        try std.testing.expectEqual(@as(usize, 2), answer.loans.len);
        inline for (.{ "first", "second" }) |name| {
            try expectExpressionLoan(answer, .{
                .binding_token = try expressionLoanTestBinding(typed.cache, site, name),
                .origin = .frame_cell,
                .derivation = .propagated,
            });
        }
    }
}

test "canonical expression loans never promote provisional retained values to physical frame cells" {
    const source: [:0]const u8 =
        \\const View = extern struct { pointer: *u8 };
        \\extern fn opaqueValue(value: View) View;
        \\fn external(pointer: *u8) View {
        \\    const value: View = .{ .pointer = pointer };
        \\    return opaqueValue(value);
        \\}
        \\fn physical() View {
        \\    var cell: u8 = 1;
        \\    const value: View = .{ .pointer = &cell };
        \\    return opaqueValue(value);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{ "external", "physical" }) |name| {
        const site = try expressionLoanTestSite(typed.tree(), name, "opaqueValue(value)", 0);
        const value_token = try expressionLoanTestBinding(typed.cache, site, "value");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expect(!answer.complete);
        try expectExpressionLoan(answer, .{ .binding_token = value_token, .origin = .retained_value, .derivation = .propagated });
        for (answer.loans) |loan| {
            if (loan.binding_token == value_token) try std.testing.expectEqual(.retained_value, loan.origin);
        }
        if (comptime std.mem.eql(u8, name, "physical")) {
            try std.testing.expectEqual(@as(usize, 2), answer.loans.len);
            try expectExpressionLoan(answer, .{
                .binding_token = try expressionLoanTestBinding(typed.cache, site, "cell"),
                .origin = .frame_cell,
                .derivation = .propagated,
                .scalar_cell = true,
            });
        } else {
            try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
        }
    }
}

test "canonical expression loans select nested payloads without borrowing unknown siblings" {
    const source: [:0]const u8 =
        \\const Inner = struct { bytes: []const u8 };
        \\const View = struct { selected: Inner, sibling: []const u8, external: []const u8, unknown: ?*u8 };
        \\fn view(external: []const u8) View {
        \\    var first: [2]u8 = .{ 1, 2 };
        \\    var second: [2]u8 = .{ 3, 4 };
        \\    const result: View = .{ .selected = .{ .bytes = &first }, .sibling = &second, .external = external, .unknown = undefined };
        \\    return result;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "result", 0);
    const first = try expressionLoanTestBinding(typed.cache, site, "first");
    const second = try expressionLoanTestBinding(typed.cache, site, "second");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const whole = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!whole.complete);
    try std.testing.expectEqual(@as(usize, 2), whole.loans.len);
    try expectExpressionLoan(whole, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated });
    try expectExpressionLoan(whole, .{ .binding_token = second, .origin = .frame_cell, .derivation = .propagated });
    const selected = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "selected.bytes" }, .horizon = site.horizon });
    try std.testing.expect(selected.complete);
    try std.testing.expectEqual(@as(usize, 1), selected.loans.len);
    try expectExpressionLoan(selected, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated });
    try expectNoExpressionLoan(selected, second);
    const external = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "external" }, .horizon = site.horizon });
    try std.testing.expect(external.complete);
    try std.testing.expectEqual(@as(usize, 0), external.loans.len);
    const unknown = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "unknown" }, .horizon = site.horizon });
    try std.testing.expect(!unknown.complete);
    try std.testing.expectEqual(@as(usize, 0), unknown.loans.len);
    try std.testing.expectEqual(@as(usize, 2), whole.loans.len);
    try expectExpressionLoan(whole, .{ .binding_token = second, .origin = .frame_cell, .derivation = .propagated });
}

test "canonical expression loans preserve exact tokens for same-spelling sibling locals" {
    const source: [:0]const u8 =
        \\fn selected(choose: bool) *u8 {
        \\    if (choose) {
        \\        var cell: u8 = 1;
        \\        return &cell;
        \\    } else {
        \\        var cell: u8 = 2;
        \\        return &cell;
        \\    }
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const first_site = try expressionLoanTestSite(typed.tree(), "selected", "&cell", 0);
    const second_site = try expressionLoanTestSite(typed.tree(), "selected", "&cell", 1);
    const first = try expressionLoanTestBinding(typed.cache, first_site, "cell");
    const second = try expressionLoanTestBinding(typed.cache, second_site, "cell");
    try std.testing.expect(first != second);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = first_site.body, .scratch = &arena, .context = .{} });
    const first_answer = try query.expressionLoansAt(.{ .selection = .{ .node = first_site.node }, .horizon = first_site.horizon });
    const second_answer = try query.expressionLoansAt(.{ .selection = .{ .node = second_site.node }, .horizon = second_site.horizon });
    try std.testing.expect(first_answer.complete and second_answer.complete);
    try std.testing.expectEqual(@as(usize, 1), first_answer.loans.len);
    try std.testing.expectEqual(@as(usize, 1), second_answer.loans.len);
    try expectExpressionLoan(first_answer, .{ .binding_token = first, .origin = .frame_cell, .derivation = .direct_address, .scalar_cell = true });
    try expectExpressionLoan(second_answer, .{ .binding_token = second, .origin = .frame_cell, .derivation = .direct_address, .scalar_cell = true });
    try expectNoExpressionLoan(first_answer, second);
    try expectNoExpressionLoan(second_answer, first);
}

test "canonical expression loans freeze copied payloads but observe live alias late writes" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: ?*u8 };
        \\const Pair = struct { snapshot: Cell, live: Cell };
        \\fn view() Pair {
        \\    var first: u8 = 1;
        \\    var second: u8 = 2;
        \\    var cell: Cell = .{ .pointer = &first };
        \\    const snapshot = cell;
        \\    const alias = &cell;
        \\    cell.pointer = &second;
        \\    const result: Pair = .{ .snapshot = snapshot, .live = alias.* };
        \\    return result;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "result", 0);
    const first = try expressionLoanTestBinding(typed.cache, site, "first");
    const second = try expressionLoanTestBinding(typed.cache, site, "second");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const snapshot = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "snapshot.pointer" }, .horizon = site.horizon });
    try std.testing.expect(snapshot.complete);
    try std.testing.expectEqual(@as(usize, 1), snapshot.loans.len);
    try expectExpressionLoan(snapshot, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(snapshot, second);
    const live = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "live.pointer" }, .horizon = site.horizon });
    try std.testing.expect(live.complete);
    try expectExpressionLoan(live, .{ .binding_token = second, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(live, try expressionLoanTestBinding(typed.cache, site, "cell"));
    try expectExpressionLoan(snapshot, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(snapshot, second);
}

test "canonical expression loans certify completed null stores without erasing conditional loans" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: ?*u8 };
        \\fn cleared() Cell {
        \\    var local: u8 = 1;
        \\    var cell: Cell = .{ .pointer = &local };
        \\    cell.pointer = null;
        \\    return cell;
        \\}
        \\fn conditional(choose: bool) Cell {
        \\    var local: u8 = 1;
        \\    var cell: Cell = .{ .pointer = &local };
        \\    if (choose) cell.pointer = null;
        \\    return cell;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{ "cleared", "conditional" }) |name| {
        const site = try expressionLoanTestSite(typed.tree(), name, "cell", 1);
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "pointer" }, .horizon = site.horizon });
        if (comptime std.mem.eql(u8, name, "cleared")) {
            try std.testing.expect(answer.complete);
            try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
        } else {
            try expectExpressionLoan(answer, .{
                .binding_token = try expressionLoanTestBinding(typed.cache, site, "local"),
                .origin = .frame_cell,
                .derivation = .propagated,
                .scalar_cell = true,
            });
        }
    }
}

test "canonical expression loans join incomplete alternatives independently of arm order" {
    const source: [:0]const u8 =
        \\fn first(choose: bool) *u8 { var cell: u8 = 1; return if (choose) &cell else undefined; }
        \\fn last(choose: bool) *u8 { var cell: u8 = 1; return if (choose) undefined else &cell; }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const cases = .{
        .{ "first", "if (choose) &cell else undefined" },
        .{ "last", "if (choose) undefined else &cell" },
    };
    inline for (cases) |case| {
        const site = try expressionLoanTestSite(typed.tree(), case[0], case[1], 0);
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expect(!answer.complete);
        try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
        try expectExpressionLoan(answer, .{
            .binding_token = try expressionLoanTestBinding(typed.cache, site, "cell"),
            .origin = .frame_cell,
            .derivation = .propagated,
            .scalar_cell = true,
        });
    }
}

test "canonical expression loans separate selected element payloads from outer array cells" {
    const source: [:0]const u8 =
        \\fn element(values: []const *u8) *u8 { return values[0]; }
        \\fn view() *u8 {
        \\    var first: u8 = 1;
        \\    var second: u8 = 2;
        \\    var values: [2]*u8 = .{ &first, &second };
        \\    _ = &values[0];
        \\    return element(&values);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const payload_site = try expressionLoanTestSite(typed.tree(), "view", "element(&values)", 0);
    const cell_site = try expressionLoanTestSite(typed.tree(), "view", "&values[0]", 0);
    const values = try expressionLoanTestBinding(typed.cache, payload_site, "values");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = payload_site.body, .scratch = &arena, .context = .{} });
    const payload = try query.expressionLoansAt(.{ .selection = .{ .node = payload_site.node }, .horizon = payload_site.horizon });
    try std.testing.expect(payload.complete);
    try std.testing.expectEqual(@as(usize, 2), payload.loans.len);
    inline for (.{ "first", "second" }) |name| {
        try expectExpressionLoan(payload, .{
            .binding_token = try expressionLoanTestBinding(typed.cache, payload_site, name),
            .origin = .frame_cell,
            .derivation = .propagated,
            .scalar_cell = true,
        });
    }
    try expectNoExpressionLoan(payload, values);
    const cell = try query.expressionLoansAt(.{ .selection = .{ .node = cell_site.node }, .horizon = cell_site.horizon });
    try std.testing.expect(cell.complete);
    try std.testing.expectEqual(@as(usize, 1), cell.loans.len);
    try expectExpressionLoan(cell, .{ .binding_token = values, .origin = .frame_cell, .derivation = .propagated });
}

test "canonical expression loans retain failure-only writes only in the failure domain" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: ?*u8 };
        \\fn view(fail: bool) !Cell {
        \\    var normal: u8 = 1;
        \\    var cleanup: u8 = 2;
        \\    var cell: Cell = .{ .pointer = null };
        \\    errdefer cell.pointer = &cleanup;
        \\    cell.pointer = &normal;
        \\    if (fail) return error.Failed;
        \\    return cell;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "cell", 2);
    const normal_token = try expressionLoanTestBinding(typed.cache, site, "normal");
    const cleanup_token = try expressionLoanTestBinding(typed.cache, site, "cleanup");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const normal = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "pointer" }, .horizon = site.horizon, .domain = .normal });
    try std.testing.expect(normal.complete);
    try expectExpressionLoan(normal, .{ .binding_token = normal_token, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(normal, cleanup_token);
    const failure = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "pointer" }, .horizon = site.horizon, .domain = .failure });
    try expectExpressionLoan(failure, .{ .binding_token = cleanup_token, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(normal, cleanup_token);
}

test "canonical expression loans propagate shared work exhaustion and permit semantic retry" {
    const source: [:0]const u8 =
        \\fn identity(value: *u8) *u8 { return value; }
        \\fn view() *u8 { var cell: u8 = 1; return identity(&cell); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    budget.clear();
    defer budget.clear();
    const site = try expressionLoanTestSite(typed.tree(), "view", "identity(&cell)", 0);
    const cell = try expressionLoanTestBinding(typed.cache, site, "cell");
    var remaining: u32 = 1;
    var query = ExpressionLoanQuery.init(.{
        .cache = typed.cache,
        .body = site.body,
        .scratch = &arena,
        .context = .{ .frame = typed.resolver.resolutionFrame(), .remaining = &remaining },
    });
    const request: ExpressionLoanRequest = .{ .selection = .{ .node = site.node }, .horizon = site.horizon };
    try std.testing.expectError(error.AnalysisBudgetExceeded, query.expressionLoansAt(request));
    try std.testing.expectEqual(@as(u32, 0), remaining);
    remaining = work_limit;
    const answer = try query.expressionLoansAt(request);
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = cell, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    remaining = 0;
    try std.testing.expectError(error.AnalysisBudgetExceeded, query.expressionLoansAt(request));
    try std.testing.expectEqual(@as(u32, 0), remaining);
    try expectExpressionLoan(answer, .{ .binding_token = cell, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans replay unresolved event arguments once per horizon" {
    // Every unresolved argument replays all earlier events, and each event's
    // own unresolved argument replays the events before it. Without a record
    // of finished replays the work doubles with each call.
    const source: [:0]const u8 =
        \\fn view(a: u32) u32 {
        \\    const t0 = ext(Missing, a);
        \\    const t1 = ext(Missing, a);
        \\    const t2 = ext(Missing, a);
        \\    const t3 = ext(Missing, a);
        \\    const t4 = ext(Missing, a);
        \\    const t5 = ext(Missing, a);
        \\    const t6 = ext(Missing, a);
        \\    const t7 = ext(Missing, a);
        \\    const t8 = ext(Missing, a);
        \\    const t9 = ext(Missing, a);
        \\    const t10 = ext(Missing, a);
        \\    const t11 = ext(Missing, a);
        \\    const t12 = ext(Missing, a);
        \\    const t13 = ext(Missing, a);
        \\    const t14 = ext(Missing, a);
        \\    const t15 = ext(Missing, a);
        \\    const t16 = ext(Missing, a);
        \\    return ext(Missing, a) + t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    budget.clear();
    defer budget.clear();
    const site = try expressionLoanTestSite(typed.tree(), "view", "ext(Missing, a) + t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16", 0);
    var remaining: u32 = work_limit;
    var query = ExpressionLoanQuery.init(.{
        .cache = typed.cache,
        .body = site.body,
        .scratch = &arena,
        .context = .{ .frame = typed.resolver.resolutionFrame(), .remaining = &remaining },
    });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    // An unresolved callee can never certify an empty loan set.
    try std.testing.expect(!answer.complete);
    try std.testing.expect(remaining > 0);
}

fn allocationFailureExpressionLoans(gpa: std.mem.Allocator, typed: *Typed) !void {
    var cache = FileCache.init(gpa, typed.tree());
    defer cache.deinit();
    cache.setZls(&typed.resolver);
    cache.module_id = typed.resolver.handle.module;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "result", 0);
    const first = try expressionLoanTestBinding(&cache, site, "first");
    const second = try expressionLoanTestBinding(&cache, site, "second");
    var query = ExpressionLoanQuery.init(.{ .cache = &cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 2), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated });
    try expectExpressionLoan(answer, .{ .binding_token = second, .origin = .frame_cell, .derivation = .propagated });
    const selected = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "second" }, .horizon = site.horizon });
    try std.testing.expect(selected.complete);
    try std.testing.expectEqual(@as(usize, 1), selected.loans.len);
    try expectExpressionLoan(selected, .{ .binding_token = second, .origin = .frame_cell, .derivation = .propagated });
    try expectExpressionLoan(answer, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated });
}

test "canonical expression loans propagate allocation failures and release query scratch" {
    const source: [:0]const u8 =
        \\const Pair = struct { first: []const u8, second: []const u8 };
        \\fn view() Pair {
        \\    var first: [2]u8 = .{ 1, 2 };
        \\    var second: [2]u8 = .{ 3, 4 };
        \\    const result: Pair = .{ .first = &first, .second = &second };
        \\    return result;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, allocationFailureExpressionLoans, .{typed});
}

test "canonical expression loans propagate excluded sources without publishing a negative answer" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{
        .sub_path = "remote.zig",
        .data = "pub fn identity(bytes: []const u8) []const u8 { return bytes; }",
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    const remote = try std.fs.path.join(gpa, &.{ directory, "remote.zig" });
    defer gpa.free(remote);
    var context: Typed.engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory}, .excludes = &.{remote} };
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, path,
        \\const remote = @import("remote.zig");
        \\fn view() []const u8 { var bytes: [2]u8 = .{ 1, 2 }; return remote.identity(&bytes); }
    );
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.module_id = resolver.handle.module;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const site = try expressionLoanTestSite(cache.tree, "view", "remote.identity(&bytes)", 0);
    const bytes = try expressionLoanTestBinding(&cache, site, "bytes");
    var query = ExpressionLoanQuery.init(.{ .cache = &cache, .body = site.body, .scratch = &arena, .context = .{} });
    const request: ExpressionLoanRequest = .{ .selection = .{ .node = site.node }, .horizon = site.horizon };
    try std.testing.expectError(error.SourceExcluded, query.expressionLoansAt(request));
    context.store.source_policy = .{ .roots = &.{directory} };
    const answer = try query.expressionLoansAt(request);
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = bytes, .origin = .frame_cell, .derivation = .propagated });
}

test "canonical expression loans load external payloads through implicit pointer base fields" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\fn view(external: *u8) *u8 {
        \\    const cell: Cell = .{ .pointer = external };
        \\    const alias = &cell;
        \\    return alias.pointer;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "alias.pointer", 0);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
}

test "canonical expression loans name implicit field pointees rather than pointer base headers" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\fn view() *u8 {
        \\    var local: u8 = 1;
        \\    const cell: Cell = .{ .pointer = &local };
        \\    const alias = &cell;
        \\    return alias.pointer;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "alias.pointer", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const cell = try expressionLoanTestBinding(typed.cache, site, "cell");
    const alias = try expressionLoanTestBinding(typed.cache, site, "alias");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(answer, cell);
    try expectNoExpressionLoan(answer, alias);
}

test "canonical expression loans distinguish copied fields from implicit alias late loads" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\const Pair = struct { snapshot: *u8, live: *u8 };
        \\fn view() Pair {
        \\    var first: u8 = 1;
        \\    var second: u8 = 2;
        \\    var cell: Cell = .{ .pointer = &first };
        \\    const frozen = cell;
        \\    const alias = &cell;
        \\    cell.pointer = &second;
        \\    return .{ .snapshot = frozen.pointer, .live = alias.pointer };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const snapshot_site = try expressionLoanTestSite(typed.tree(), "view", "frozen.pointer", 0);
    const live_site = try expressionLoanTestSite(typed.tree(), "view", "alias.pointer", 0);
    const first = try expressionLoanTestBinding(typed.cache, snapshot_site, "first");
    const second = try expressionLoanTestBinding(typed.cache, live_site, "second");
    const cell = try expressionLoanTestBinding(typed.cache, live_site, "cell");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = snapshot_site.body, .scratch = &arena, .context = .{} });
    const snapshot = try query.expressionLoansAt(.{ .selection = .{ .node = snapshot_site.node }, .horizon = snapshot_site.horizon });
    try std.testing.expect(snapshot.complete);
    try std.testing.expectEqual(@as(usize, 1), snapshot.loans.len);
    try expectExpressionLoan(snapshot, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(snapshot, second);
    const live = try query.expressionLoansAt(.{ .selection = .{ .node = live_site.node }, .horizon = live_site.horizon });
    try std.testing.expect(live.complete);
    try expectExpressionLoan(live, .{ .binding_token = second, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(live, cell);
    try expectExpressionLoan(snapshot, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(snapshot, second);
}

test "canonical expression loans cancel forwarded cell addresses when loading external payloads" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\fn identity(value: *const Cell) *const Cell { return value; }
        \\fn view(external: *u8) Cell {
        \\    const cell: Cell = .{ .pointer = external };
        \\    return identity(&cell).*;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "identity(&cell).*", 0);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
}

test "canonical expression loans retain local payloads after forwarded cell dereferences" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\fn identity(value: *const Cell) *const Cell { return value; }
        \\fn view() Cell {
        \\    var local: u8 = 1;
        \\    const cell: Cell = .{ .pointer = &local };
        \\    return identity(&cell).*;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "identity(&cell).*", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const cell = try expressionLoanTestBinding(typed.cache, site, "cell");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(answer, cell);
}

fn expressionLoanTestReturnedBlock(
    tree: *const Ast,
    inner: ExpressionLoanTestSite,
) !ExpressionLoanTestSite {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .@"return") continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(node) < tree.firstToken(inner.body) or tree.lastToken(node) > tree.lastToken(inner.body)) continue;
        const value = tree.nodeData(node).opt_node.unwrap() orelse continue;
        if (tree.firstToken(value) > tree.firstToken(inner.node) or tree.lastToken(value) < tree.lastToken(inner.node)) continue;
        return .{ .body = inner.body, .node = value, .horizon = tree.firstToken(value) };
    }
    return error.TestExpectedReturnedBlock;
}

test "canonical expression loans evaluate block local addresses at the inner break horizon" {
    const source: [:0]const u8 =
        \\fn view() *u8 {
        \\    return result: {
        \\        var cell: u8 = 1;
        \\        break :result &cell;
        \\    };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const inner = try expressionLoanTestSite(typed.tree(), "view", "&cell", 0);
    const cell = try expressionLoanTestBinding(typed.cache, inner, "cell");
    const block = try expressionLoanTestReturnedBlock(typed.tree(), inner);
    try std.testing.expect(block.horizon < cell);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = block.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = block.node }, .horizon = block.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = cell, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans observe block internal field writes before the selected break" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: ?*u8 };
        \\fn view() Cell {
        \\    var local: u8 = 1;
        \\    return result: {
        \\        var cell: Cell = .{ .pointer = null };
        \\        cell.pointer = &local;
        \\        break :result cell;
        \\    };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const inner = try expressionLoanTestSite(typed.tree(), "view", "cell", 1);
    const block = try expressionLoanTestReturnedBlock(typed.tree(), inner);
    const local = try expressionLoanTestBinding(typed.cache, inner, "local");
    const cell = try expressionLoanTestBinding(typed.cache, inner, "cell");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = block.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = block.node, .path = "pointer" }, .horizon = block.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(answer, cell);
}

test "canonical expression loans preserve block copy snapshots before later field writes" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: ?*u8 };
        \\fn view() Cell {
        \\    var first: u8 = 1;
        \\    var second: u8 = 2;
        \\    return result: {
        \\        var cell: Cell = .{ .pointer = &first };
        \\        const frozen = cell;
        \\        cell.pointer = &second;
        \\        break :result frozen;
        \\    };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const inner = try expressionLoanTestSite(typed.tree(), "view", "frozen", 0);
    const block = try expressionLoanTestReturnedBlock(typed.tree(), inner);
    const first = try expressionLoanTestBinding(typed.cache, inner, "first");
    const second = try expressionLoanTestBinding(typed.cache, inner, "second");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = block.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = block.node, .path = "pointer" }, .horizon = block.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(answer, second);
}

test "canonical expression loans load block pointer aliases after late field writes" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: ?*u8 };
        \\fn view() Cell {
        \\    var first: u8 = 1;
        \\    var second: u8 = 2;
        \\    return result: {
        \\        var cell: Cell = .{ .pointer = &first };
        \\        const alias = &cell;
        \\        cell.pointer = &second;
        \\        break :result alias.*;
        \\    };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const inner = try expressionLoanTestSite(typed.tree(), "view", "alias.*", 0);
    const block = try expressionLoanTestReturnedBlock(typed.tree(), inner);
    const second = try expressionLoanTestBinding(typed.cache, inner, "second");
    const cell = try expressionLoanTestBinding(typed.cache, inner, "cell");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = block.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = block.node, .path = "pointer" }, .horizon = block.horizon });
    try std.testing.expect(answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = second, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(answer, cell);
}

test "canonical expression loans preserve block positives beside unknown break alternatives" {
    const source: [:0]const u8 =
        \\fn earlyHole(choose: bool) *u8 {
        \\    return result: {
        \\        var cell: u8 = 1;
        \\        if (choose) break :result undefined;
        \\        break :result &cell;
        \\    };
        \\}
        \\fn lateHole(choose: bool) *u8 {
        \\    return result: {
        \\        var cell: u8 = 1;
        \\        if (choose) break :result &cell;
        \\        break :result undefined;
        \\    };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{ "earlyHole", "lateHole" }) |name| {
        const inner = try expressionLoanTestSite(typed.tree(), name, "&cell", 0);
        const block = try expressionLoanTestReturnedBlock(typed.tree(), inner);
        const cell = try expressionLoanTestBinding(typed.cache, inner, "cell");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = block.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = block.node }, .horizon = block.horizon });
        try std.testing.expect(!answer.complete);
        try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
        try expectExpressionLoan(answer, .{ .binding_token = cell, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    }
}

test "canonical expression loans separate block error cleanup from normal field writes" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: ?*u8 };
        \\fn view(fail: bool) !Cell {
        \\    var normal: u8 = 1;
        \\    var cleanup: u8 = 2;
        \\    return result: {
        \\        var cell: Cell = .{ .pointer = null };
        \\        errdefer cell.pointer = &cleanup;
        \\        cell.pointer = &normal;
        \\        if (fail) return error.Failed;
        \\        break :result cell;
        \\    };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const inner = try expressionLoanTestSite(typed.tree(), "view", "cell", 2);
    const block = try expressionLoanTestReturnedBlock(typed.tree(), inner);
    const normal_token = try expressionLoanTestBinding(typed.cache, inner, "normal");
    const cleanup_token = try expressionLoanTestBinding(typed.cache, inner, "cleanup");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = block.body, .scratch = &arena, .context = .{} });
    const normal = try query.expressionLoansAt(.{ .selection = .{ .node = block.node, .path = "pointer" }, .horizon = block.horizon, .domain = .normal });
    try std.testing.expect(normal.complete);
    try expectExpressionLoan(normal, .{ .binding_token = normal_token, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(normal, cleanup_token);
    const failure = try query.expressionLoansAt(.{ .selection = .{ .node = block.node, .path = "pointer" }, .horizon = block.horizon, .domain = .failure });
    try expectExpressionLoan(failure, .{ .binding_token = cleanup_token, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(normal, cleanup_token);
}

test "canonical expression loans use supplied frames for slice aliases without cache resolvers" {
    const source: [:0]const u8 =
        \\fn view(external: []const u8) []const u8 {
        \\    const local = external;
        \\    return local[0..];
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "local[0..]", 0);
    const resolver = typed.cache.zls.?;
    const frame = resolver.resolutionFrame();
    typed.cache.zls = null;
    defer typed.cache.zls = resolver;
    var query = ExpressionLoanQuery.init(.{
        .cache = typed.cache,
        .body = site.body,
        .scratch = &arena,
        .context = .{ .frame = frame },
    });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
}

test "canonical expression loans use supplied frames for external element payloads without cache resolvers" {
    const source: [:0]const u8 =
        \\fn view(external: *u8) *u8 {
        \\    const values: [1]*u8 = .{external};
        \\    const alias = &values;
        \\    return alias[0];
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "alias[0]", 0);
    const resolver = typed.cache.zls.?;
    const frame = resolver.resolutionFrame();
    typed.cache.zls = null;
    defer typed.cache.zls = resolver;
    var query = ExpressionLoanQuery.init(.{
        .cache = typed.cache,
        .body = site.body,
        .scratch = &arena,
        .context = .{ .frame = frame },
    });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
}

test "canonical expression loans select external payloads through nested pointer fields" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\const Holder = struct { link: *const Cell };
        \\fn view(external: *u8) *u8 {
        \\    const cell: Cell = .{ .pointer = external };
        \\    const holder: Holder = .{ .link = &cell };
        \\    return holder.link.pointer;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const base = try expressionLoanTestSite(typed.tree(), "view", "holder", 0);
    const field = try expressionLoanTestSite(typed.tree(), "view", "holder.link.pointer", 0);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = base.body, .scratch = &arena, .context = .{} });
    const selected = try query.expressionLoansAt(.{ .selection = .{ .node = base.node, .path = "link.pointer" }, .horizon = base.horizon });
    try std.testing.expect(selected.complete);
    try std.testing.expectEqual(@as(usize, 0), selected.loans.len);
    const accessed = try query.expressionLoansAt(.{ .selection = .{ .node = field.node }, .horizon = field.horizon });
    try std.testing.expect(accessed.complete);
    try std.testing.expectEqual(@as(usize, 0), accessed.loans.len);
}

test "canonical expression loans select nested local pointees without borrowing intermediate headers" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\const Holder = struct { link: *const Cell };
        \\fn view() *u8 {
        \\    var local: u8 = 1;
        \\    const cell: Cell = .{ .pointer = &local };
        \\    const holder: Holder = .{ .link = &cell };
        \\    return holder.link.pointer;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const base = try expressionLoanTestSite(typed.tree(), "view", "holder", 0);
    const field = try expressionLoanTestSite(typed.tree(), "view", "holder.link.pointer", 0);
    const local = try expressionLoanTestBinding(typed.cache, base, "local");
    const cell = try expressionLoanTestBinding(typed.cache, base, "cell");
    const holder = try expressionLoanTestBinding(typed.cache, base, "holder");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = base.body, .scratch = &arena, .context = .{} });
    const selected = try query.expressionLoansAt(.{ .selection = .{ .node = base.node, .path = "link.pointer" }, .horizon = base.horizon });
    try std.testing.expect(selected.complete);
    try std.testing.expectEqual(@as(usize, 1), selected.loans.len);
    try expectExpressionLoan(selected, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(selected, cell);
    try expectNoExpressionLoan(selected, holder);
    const accessed = try query.expressionLoansAt(.{ .selection = .{ .node = field.node }, .horizon = field.horizon });
    try std.testing.expect(accessed.complete);
    try std.testing.expectEqual(@as(usize, 1), accessed.loans.len);
    try expectExpressionLoan(accessed, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(accessed, cell);
    try expectNoExpressionLoan(accessed, holder);
}

test "canonical expression loans distinguish helper inline cell addresses from external backing addresses" {
    const source: [:0]const u8 =
        \\const Box = struct { scratch: [2]u8, external: []u8 };
        \\fn inlineCell(box: *Box) *u8 { return &box.scratch[0]; }
        \\fn backed(box: *Box) *u8 { return &box.external[0]; }
        \\fn view(external: []u8) *u8 {
        \\    var box: Box = .{ .scratch = .{ 1, 2 }, .external = external };
        \\    _ = inlineCell(&box);
        \\    return backed(&box);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    _ = try expectOnlyAlternative(
        try returnedStorageOf(typed.cache, callNamed(typed.tree(), "inlineCell").?),
        .{ .param = 0, .path = "scratch" },
        .cell_address,
        .inline_storage,
        "",
    );
    _ = try expectOnlyAlternative(
        try returnedStorageOf(typed.cache, callNamed(typed.tree(), "backed").?),
        .{ .param = 0, .path = "external" },
        .cell_address,
        .backing_storage,
        "",
    );
    const inline_site = try expressionLoanTestSite(typed.tree(), "view", "inlineCell(&box)", 0);
    const backed_site = try expressionLoanTestSite(typed.tree(), "view", "backed(&box)", 0);
    const box = try expressionLoanTestBinding(typed.cache, inline_site, "box");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = inline_site.body, .scratch = &arena, .context = .{} });
    const inline_cell = try query.expressionLoansAt(.{ .selection = .{ .node = inline_site.node }, .horizon = inline_site.horizon });
    try std.testing.expect(inline_cell.complete);
    try std.testing.expectEqual(@as(usize, 1), inline_cell.loans.len);
    try expectExpressionLoan(inline_cell, .{ .binding_token = box, .origin = .frame_cell, .derivation = .propagated });
    const backing = try query.expressionLoansAt(.{ .selection = .{ .node = backed_site.node }, .horizon = backed_site.horizon });
    try std.testing.expect(backing.complete);
    try std.testing.expectEqual(@as(usize, 0), backing.loans.len);
    try expectExpressionLoan(inline_cell, .{ .binding_token = box, .origin = .frame_cell, .derivation = .propagated });
}

test "canonical expression loans load mapped helper pointer fields rather than actual cell headers" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\fn get(cell: *const Cell) *const Cell { return cell; }
        \\fn externalView(external: *u8) *u8 {
        \\    const cell: Cell = .{ .pointer = external };
        \\    return get(&cell).pointer;
        \\}
        \\fn localView() *u8 {
        \\    var local: u8 = 1;
        \\    const cell: Cell = .{ .pointer = &local };
        \\    return get(&cell).pointer;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{ "externalView", "localView" }) |name| {
        const site = try expressionLoanTestSite(typed.tree(), name, "get(&cell).pointer", 0);
        const cell = try expressionLoanTestBinding(typed.cache, site, "cell");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expect(answer.complete);
        try expectNoExpressionLoan(answer, cell);
        if (comptime std.mem.eql(u8, name, "externalView")) {
            try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
        } else {
            try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
            try expectExpressionLoan(answer, .{
                .binding_token = try expressionLoanTestBinding(typed.cache, site, "local"),
                .origin = .frame_cell,
                .derivation = .propagated,
                .scalar_cell = true,
            });
        }
    }
}

test "canonical expression loans load builtin forwarded cell payloads without borrowing cell headers" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\fn identity(cell: *const Cell) *const Cell { return cell; }
        \\fn externalView(external: *u8) Cell {
        \\    const cell: Cell = .{ .pointer = external };
        \\    return @call(.auto, identity, .{&cell}).*;
        \\}
        \\fn localView() Cell {
        \\    var local: u8 = 1;
        \\    const cell: Cell = .{ .pointer = &local };
        \\    return @call(.auto, identity, .{&cell}).*;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{ "externalView", "localView" }) |name| {
        const site = try expressionLoanTestSite(typed.tree(), name, "@call(.auto, identity, .{&cell}).*", 0);
        const cell = try expressionLoanTestBinding(typed.cache, site, "cell");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expect(answer.complete);
        try expectNoExpressionLoan(answer, cell);
        if (comptime std.mem.eql(u8, name, "externalView")) {
            try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
        } else {
            try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
            try expectExpressionLoan(answer, .{
                .binding_token = try expressionLoanTestBinding(typed.cache, site, "local"),
                .origin = .frame_cell,
                .derivation = .propagated,
                .scalar_cell = true,
            });
        }
    }
}

test "canonical expression loans freeze forwarded copies but retain ordinary and generic live loads" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: *u8 };
        \\const Pair = struct { snapshot: *u8, live: *u8 };
        \\fn identity(cell: *Cell) *Cell { return cell; }
        \\fn genericIdentity(comptime T: type, value: T) T { return value; }
        \\fn ordinary() Pair {
        \\    var first: u8 = 1;
        \\    var second: u8 = 2;
        \\    var cell: Cell = .{ .pointer = &first };
        \\    const snapshot = identity(&cell).*;
        \\    const live = @call(.auto, identity, .{&cell});
        \\    cell.pointer = &second;
        \\    return .{ .snapshot = snapshot.pointer, .live = live.pointer };
        \\}
        \\fn generic() Pair {
        \\    var first: u8 = 1;
        \\    var second: u8 = 2;
        \\    var cell: Cell = .{ .pointer = &first };
        \\    const snapshot = @call(.auto, genericIdentity, .{ *Cell, &cell }).*;
        \\    const live = genericIdentity(*Cell, &cell);
        \\    cell.pointer = &second;
        \\    return .{ .snapshot = snapshot.pointer, .live = live.pointer };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{ "ordinary", "generic" }) |name| {
        const snapshot_site = try expressionLoanTestSite(typed.tree(), name, "snapshot.pointer", 0);
        const live_site = try expressionLoanTestSite(typed.tree(), name, "live.pointer", 0);
        const first = try expressionLoanTestBinding(typed.cache, snapshot_site, "first");
        const second = try expressionLoanTestBinding(typed.cache, live_site, "second");
        const cell = try expressionLoanTestBinding(typed.cache, live_site, "cell");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = snapshot_site.body, .scratch = &arena, .context = .{} });
        const snapshot = try query.expressionLoansAt(.{ .selection = .{ .node = snapshot_site.node }, .horizon = snapshot_site.horizon });
        try std.testing.expect(snapshot.complete);
        try std.testing.expectEqual(@as(usize, 1), snapshot.loans.len);
        try expectExpressionLoan(snapshot, .{ .binding_token = first, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
        try expectNoExpressionLoan(snapshot, second);
        try expectNoExpressionLoan(snapshot, cell);
        const live = try query.expressionLoansAt(.{ .selection = .{ .node = live_site.node }, .horizon = live_site.horizon });
        try std.testing.expect(live.complete);
        try expectExpressionLoan(live, .{ .binding_token = second, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
        try expectNoExpressionLoan(live, cell);
        try expectNoExpressionLoan(snapshot, second);
    }
}

test "canonical expression loans keep unsupported named element selectors incomplete" {
    const source: [:0]const u8 =
        \\const Item = struct { pointer: *u8 };
        \\fn element(values: []const Item) Item { return values[0]; }
        \\fn view() Item {
        \\    var local: u8 = 1;
        \\    const values = [1]Item{Item{ .pointer = &local }};
        \\    return element(&values);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "element(&values)", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const selected = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "pointer" }, .horizon = site.horizon });
    try std.testing.expect(selected.complete);
    try std.testing.expectEqual(@as(usize, 1), selected.loans.len);
    try expectExpressionLoan(selected, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    // This query-only path does not alter the valid typed source. A missing
    // selector is an unknown projection, not a completed empty payload.
    const unsupported = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "missing" }, .horizon = site.horizon });
    try std.testing.expect(!unsupported.complete);
    try expectExpressionLoan(selected, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans retain tuple element pointees beside unsupported selectors" {
    const source: [:0]const u8 =
        \\const Item = struct { *u8 };
        \\fn element(values: []const Item) Item { return values[0]; }
        \\fn view() Item {
        \\    var local: u8 = 1;
        \\    const values = [1]Item{Item{&local}};
        \\    return element(&values);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "element(&values)", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const values = try expressionLoanTestBinding(typed.cache, site, "values");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node, .path = "missing" }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(answer, values);
}

test "canonical expression loans retain unresolved loop capture values by exact capture tokens" {
    const source: [:0]const u8 =
        \\fn view(input: []*u8) *u8 {
        \\    for (input) |item| {
        \\        return item;
        \\    }
        \\    return undefined;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "item", 0);
    const item = try expressionLoanTestBinding(typed.cache, site, "item");
    const input = try expressionLoanTestBinding(typed.cache, site, "input");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = item, .origin = .retained_value, .derivation = .propagated });
    try expectNoExpressionLoan(answer, input);
}

test "canonical expression loans keep loop capture cell addresses physical but incomplete" {
    const source: [:0]const u8 =
        \\fn view(input: []*u8) *const *u8 {
        \\    for (input) |item| {
        \\        return &item;
        \\    }
        \\    return undefined;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "&item", 0);
    const item = try expressionLoanTestBinding(typed.cache, site, "item");
    const input = try expressionLoanTestBinding(typed.cache, site, "input");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try expectExpressionLoan(answer, .{ .binding_token = item, .origin = .frame_cell, .derivation = .direct_address });
    try expectNoExpressionLoan(answer, input);
}

test "canonical expression loans keep forwarded union representation writes incomplete and physical" {
    const source: [:0]const u8 =
        \\const Slot = extern union { pointer: ?*u8, bits: usize, bytes: [@sizeOf(usize)]u8 };
        \\fn compound(slot: *Slot, pointer: *u8) *Slot {
        \\    slot.bits |= @intFromPtr(pointer);
        \\    return slot;
        \\}
        \\fn overwrite(slot: *Slot, pointer: *u8) *Slot {
        \\    slot.bits = @intFromPtr(pointer);
        \\    return slot;
        \\}
        \\fn copyBytes(slot: *Slot, pointer: *u8) *Slot {
        \\    const bits: [@sizeOf(usize)]u8 = @bitCast(@intFromPtr(pointer));
        \\    @memcpy(&slot.bytes, &bits);
        \\    return slot;
        \\}
        \\fn compoundView() *u8 {
        \\    var local: u8 = 1;
        \\    var slot: Slot = .{ .pointer = null };
        \\    return compound(&slot, &local).pointer.?;
        \\}
        \\fn overwriteView() *u8 {
        \\    var local: u8 = 1;
        \\    var slot: Slot = .{ .pointer = null };
        \\    return overwrite(&slot, &local).pointer.?;
        \\}
        \\fn bytesView() *u8 {
        \\    var local: u8 = 1;
        \\    var slot: Slot = .{ .pointer = null };
        \\    return copyBytes(&slot, &local).pointer.?;
        \\}
        \\fn compoundWhole() Slot {
        \\    var local: u8 = 1;
        \\    var slot: Slot = .{ .pointer = null };
        \\    return compound(&slot, &local).*;
        \\}
        \\fn overwriteWhole() Slot {
        \\    var local: u8 = 1;
        \\    var slot: Slot = .{ .pointer = null };
        \\    return overwrite(&slot, &local).*;
        \\}
        \\fn bytesWhole() Slot {
        \\    var local: u8 = 1;
        \\    var slot: Slot = .{ .pointer = null };
        \\    return copyBytes(&slot, &local).*;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const cases = .{
        .{ "compoundView", "compound(&slot, &local).pointer.?" },
        .{ "overwriteView", "overwrite(&slot, &local).pointer.?" },
        .{ "bytesView", "copyBytes(&slot, &local).pointer.?" },
        .{ "compoundWhole", "compound(&slot, &local).*" },
        .{ "overwriteWhole", "overwrite(&slot, &local).*" },
        .{ "bytesWhole", "copyBytes(&slot, &local).*" },
    };
    inline for (cases) |case| {
        const site = try expressionLoanTestSite(typed.tree(), case[0], case[1], 0);
        const local = try expressionLoanTestBinding(typed.cache, site, "local");
        const slot = try expressionLoanTestBinding(typed.cache, site, "slot");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expect(!answer.complete);
        var physical = false;
        for (answer.loans) |loan| {
            if (loan.origin != .frame_cell) continue;
            if (loan.binding_token == local or loan.binding_token == slot) physical = true;
        }
        try std.testing.expect(physical);
    }
}

test "canonical expression loans retain physical pointees stored through output parameters" {
    const source: [:0]const u8 =
        \\fn view(out: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    out.* = &local;
        \\    return out.*;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "out.*", 1);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans retain physical pointees installed by output setters" {
    const source: [:0]const u8 =
        \\fn set(out: **u8, pointer: *u8) void { out.* = pointer; }
        \\fn view(out: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    set(out, &local);
        \\    return out.*;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "out.*", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans retain late output setter writes through const parameter aliases" {
    const source: [:0]const u8 =
        \\fn set(out: **u8, pointer: *u8) void { out.* = pointer; }
        \\fn view(out: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    const alias = out;
        \\    set(alias, &local);
        \\    return alias.*;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "alias.*", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans preserve physical channels through forwarded aggregate callbacks" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: ?*u8 };
        \\const View = struct { cell: *Cell, pointer: *u8 };
        \\fn wrapper(value: View, callback: *const fn (View) void) Cell {
        \\    callback(value);
        \\    return value.cell.*;
        \\}
        \\fn view(callback: *const fn (View) void) Cell {
        \\    var local: u8 = 1;
        \\    var cell: Cell = .{ .pointer = null };
        \\    return wrapper(.{ .cell = &cell, .pointer = &local }, callback);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "wrapper(.{ .cell = &cell, .pointer = &local }, callback)", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const cell = try expressionLoanTestBinding(typed.cache, site, "cell");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    var physical = false;
    for (answer.loans) |loan| {
        if (loan.origin != .frame_cell) continue;
        if (loan.binding_token == local or loan.binding_token == cell) physical = true;
    }
    try std.testing.expect(physical);
}

test "canonical expression loans preserve nested encoded pointer effect channels" {
    const source: [:0]const u8 =
        \\const Cell = struct { pointer: ?*u8 };
        \\fn writeRaw(rawcell: usize, rawpointer: usize) void {
        \\    const cell: *Cell = @ptrFromInt(rawcell);
        \\    const pointer: *u8 = @ptrFromInt(rawpointer);
        \\    cell.pointer = pointer;
        \\}
        \\fn wrapper(rawcell: usize, rawpointer: usize) Cell {
        \\    writeRaw(rawcell, rawpointer);
        \\    const cell: *Cell = @ptrFromInt(rawcell);
        \\    return cell.*;
        \\}
        \\fn view() Cell {
        \\    var local: u8 = 1;
        \\    var cell: Cell = .{ .pointer = null };
        \\    return wrapper(@intFromPtr(&cell), @intFromPtr(&local));
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "wrapper(@intFromPtr(&cell), @intFromPtr(&local))", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const cell = try expressionLoanTestBinding(typed.cache, site, "cell");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    var physical = false;
    for (answer.loans) |loan| {
        if (loan.origin != .frame_cell) continue;
        if (loan.binding_token == local or loan.binding_token == cell) physical = true;
    }
    try std.testing.expect(physical);
}

test "canonical expression loans retain physical local writes into global pointer cells" {
    const source: [:0]const u8 =
        \\var saved: *u8 = undefined;
        \\fn view() *u8 {
        \\    var local: u8 = 1;
        \\    saved = &local;
        \\    return saved;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "saved", 1);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans prove local pointees in literal loop captures" {
    const source: [:0]const u8 =
        \\fn view() *u8 {
        \\    var local: u8 = 1;
        \\    const values = [_]*u8{&local};
        \\    for (values) |item| {
        \\        return item;
        \\    }
        \\    return undefined;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "item", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const item = try expressionLoanTestBinding(typed.cache, site, "item");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(answer, item);
}

test "canonical expression loans evaluate omitted typed aggregate pointer defaults truthfully" {
    const source: [:0]const u8 =
        \\const Unknown = struct { pointer: ?*u8 = undefined };
        \\const Safe = struct { pointer: ?*u8 = null };
        \\fn inferred() Unknown { return .{}; }
        \\fn named() Unknown { return Unknown{}; }
        \\fn safe() Safe { return Safe{}; }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const cases = .{
        .{ "inferred", ".{}", false },
        .{ "named", "Unknown{}", false },
        .{ "safe", "Safe{}", true },
    };
    inline for (cases) |case| {
        const site = try expressionLoanTestSite(typed.tree(), case[0], case[1], 0);
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expectEqual(case[2], answer.complete);
        try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
    }
}

test "canonical expression loans retain descendant stores when returning containing aggregate fields" {
    const source: [:0]const u8 =
        \\const Inner = struct { pointer: ?*u8 };
        \\const Outer = struct { inner: Inner };
        \\fn view() Inner {
        \\    var local: u8 = 1;
        \\    var outer: Outer = .{ .inner = .{ .pointer = null } };
        \\    outer.inner.pointer = &local;
        \\    return outer.inner;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "outer.inner", 1);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans retain pointer cell memcpy output pointees" {
    const source: [:0]const u8 =
        \\fn view(out: []*u8) *u8 {
        \\    var local: u8 = 1;
        \\    const cells = [_]*u8{&local};
        \\    @memcpy(out[0..1], &cells);
        \\    return out[0];
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "out[0]", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans load loop captured output pointers after live stores" {
    const source: [:0]const u8 =
        \\fn view(out: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    const values = [_]**u8{out};
        \\    for (values) |item| {
        \\        out.* = &local;
        \\        return item.*;
        \\    }
        \\    return undefined;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "item.*", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const out = try expressionLoanTestBinding(typed.cache, site, "out");
    const item = try expressionLoanTestBinding(typed.cache, site, "item");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    for (answer.loans) |loan| {
        if (loan.origin != .frame_cell) continue;
        try std.testing.expect(loan.binding_token != out and loan.binding_token != item);
    }
}

test "canonical expression loans load loop captured local pointer payloads without header loans" {
    const source: [:0]const u8 =
        \\fn view() *u8 {
        \\    var local: u8 = 1;
        \\    var header: *u8 = &local;
        \\    const values = [_]**u8{&header};
        \\    for (values) |item| {
        \\        return item.*;
        \\    }
        \\    return undefined;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "item.*", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const header = try expressionLoanTestBinding(typed.cache, site, "header");
    const item = try expressionLoanTestBinding(typed.cache, site, "item");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    for (answer.loans) |loan| {
        if (loan.origin != .frame_cell) continue;
        try std.testing.expect(loan.binding_token != header and loan.binding_token != item);
    }
}

test "canonical expression loans retain descendant stores inside selected array element aggregates" {
    const source: [:0]const u8 =
        \\const Inner = struct { pointer: ?*u8 };
        \\const Outer = struct { inner: Inner };
        \\fn view() Inner {
        \\    var local: u8 = 1;
        \\    var values: [1]Outer = .{.{ .inner = .{ .pointer = null } }};
        \\    values[0].inner.pointer = &local;
        \\    return values[0].inner;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "values[0].inner", 1);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans exclude unrelated global pointer stores from static global views" {
    const source: [:0]const u8 =
        \\var saved: []const u8 = "static";
        \\var other: ?*u8 = null;
        \\fn view() []const u8 {
        \\    var local: u8 = 1;
        \\    other = &local;
        \\    return saved;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "saved", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.origin == .frame_cell) try std.testing.expect(loan.binding_token != local);
    }
}

test "canonical expression loans retain local address bits written into scalar global cells" {
    const source: [:0]const u8 =
        \\var saved: usize = 0;
        \\fn view() usize {
        \\    var local: u8 = 1;
        \\    saved = @intFromPtr(&local);
        \\    return saved;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "saved", 1);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans retain optional pointer capture backing cells without capture headers" {
    const source: [:0]const u8 =
        \\fn view() *[1]u8 {
        \\    var maybe: ?[1]u8 = [_]u8{1};
        \\    if (maybe) |*payload| {
        \\        return payload;
        \\    }
        \\    return undefined;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "payload", 0);
    const maybe = try expressionLoanTestBinding(typed.cache, site, "maybe");
    const payload = try expressionLoanTestBinding(typed.cache, site, "payload");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = maybe, .origin = .frame_cell, .derivation = .propagated });
    for (answer.loans) |loan| {
        if (loan.origin == .frame_cell) try std.testing.expect(loan.binding_token != payload);
    }
}

test "canonical expression loans preserve exact value capture origins in multiple iterator loops" {
    const source: [:0]const u8 =
        \\fn view() *u8 {
        \\    var local: u8 = 1;
        \\    const values = [_]*u8{&local};
        \\    for (values, 0..) |item, index| {
        \\        _ = index;
        \\        return item;
        \\    }
        \\    return undefined;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "item", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const item = try expressionLoanTestBinding(typed.cache, site, "item");
    const index = try expressionLoanTestBinding(typed.cache, site, "index");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    try expectNoExpressionLoan(answer, item);
    try expectNoExpressionLoan(answer, index);
}

test "canonical expression loans retain local address bits through scalar compound stores" {
    const source: [:0]const u8 =
        \\fn view() usize {
        \\    var local: u8 = 1;
        \\    var bits: usize = 0;
        \\    bits |= @intFromPtr(&local);
        \\    return bits;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "bits", 1);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans name by value parameter field addresses as physical cells" {
    const source: [:0]const u8 =
        \\const S = struct { bytes: [1]u8 };
        \\fn view(value: S) *const [1]u8 { return &value.bytes; }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "&value.bytes", 0);
    const value = try expressionLoanTestBinding(typed.cache, site, "value");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expectEqual(@as(usize, 1), answer.loans.len);
    try std.testing.expectEqual(value, answer.loans[0].binding_token);
    try std.testing.expectEqual(.frame_cell, answer.loans[0].origin);
    try std.testing.expect(!answer.loans[0].scalar_cell);
}

test "canonical expression loans do not borrow incoming pointer parameter headers for field addresses" {
    const source: [:0]const u8 =
        \\const S = struct { bytes: [1]u8 };
        \\fn view(value: *const S) *const [1]u8 { return &value.bytes; }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "&value.bytes", 0);
    const value = try expressionLoanTestBinding(typed.cache, site, "value");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.origin == .frame_cell) try std.testing.expect(loan.binding_token != value);
    }
}

test "canonical expression loans freeze loop input pointer values before later pointer rebinding" {
    const source: [:0]const u8 =
        \\fn view(incoming: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    var header: *u8 = &local;
        \\    var current: **u8 = incoming;
        \\    const values = [_]**u8{current};
        \\    current = &header;
        \\    for (values) |item| {
        \\        return item.*;
        \\    }
        \\    unreachable;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "item.*", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const header = try expressionLoanTestBinding(typed.cache, site, "header");
    const current = try expressionLoanTestBinding(typed.cache, site, "current");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    for (answer.loans) |loan| {
        if (loan.origin != .frame_cell) continue;
        try std.testing.expect(loan.binding_token != local and loan.binding_token != header and loan.binding_token != current);
    }
}

test "canonical expression loans exclude distinct global inline field stores from static global views" {
    const source: [:0]const u8 =
        \\const Holder = struct { bytes: []const u8 };
        \\var saved: []const u8 = "static";
        \\var other: Holder = .{ .bytes = "" };
        \\fn view() []const u8 {
        \\    var local: [1]u8 = .{1};
        \\    other.bytes = &local;
        \\    return saved;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "saved", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.origin == .frame_cell) try std.testing.expect(loan.binding_token != local);
    }
}

test "canonical expression loans exclude distinct global array stores from static global views" {
    const source: [:0]const u8 =
        \\var saved: []const u8 = "static";
        \\var other: [1][]const u8 = .{""};
        \\fn view() []const u8 {
        \\    var local: [1]u8 = .{1};
        \\    other[0] = &local;
        \\    return saved;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "saved", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.origin == .frame_cell) try std.testing.expect(loan.binding_token != local);
    }
}

test "canonical expression loans freeze stored selected pointer fields before live captured pointee loads" {
    const source: [:0]const u8 =
        \\const State = struct { pointer: **u8 };
        \\fn view(out: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    var state: State = .{ .pointer = out };
        \\    state.pointer = out;
        \\    const values = [_]**u8{state.pointer};
        \\    for (values) |item| {
        \\        out.* = &local;
        \\        return item.*;
        \\    }
        \\    unreachable;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "item.*", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans keep selected field capture pointees unknown without a proved store" {
    const sources = [_][:0]const u8{
        \\const State = struct { pointer: **u8 };
        \\fn view(out: **u8, condition: bool) *u8 {
        \\    var local: u8 = 1;
        \\    var state: State = .{ .pointer = out };
        \\    state.pointer = out;
        \\    const values = [_]**u8{state.pointer};
        \\    for (values) |item| {
        \\        _ = condition;
        \\        _ = &local;
        \\        return item.*;
        \\    }
        \\    unreachable;
        \\}
        ,
        \\const State = struct { pointer: **u8 };
        \\fn view(out: **u8, condition: bool) *u8 {
        \\    var local: u8 = 1;
        \\    var state: State = .{ .pointer = out };
        \\    state.pointer = out;
        \\    const values = [_]**u8{state.pointer};
        \\    for (values) |item| {
        \\        if (condition) out.* = &local;
        \\        return item.*;
        \\    }
        \\    unreachable;
        \\}
        ,
    };
    for (sources, 0..) |source, index| {
        const typed = try Typed.init(std.testing.allocator, source);
        defer typed.deinit(std.testing.allocator);
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const site = try expressionLoanTestSite(typed.tree(), "view", "item.*", 0);
        const local = try expressionLoanTestBinding(typed.cache, site, "local");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        try std.testing.expect(!answer.complete);
        if (index == 0)
            try expectNoExpressionLoan(answer, local)
        else
            try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
    }
}

test "canonical expression loans freeze selected field capture inputs before later field rebinding" {
    const source: [:0]const u8 =
        \\const State = struct { pointer: **u8 };
        \\fn view(incoming: **u8) *u8 {
        \\    var local: u8 = 1;
        \\    var header: *u8 = &local;
        \\    var state: State = .{ .pointer = incoming };
        \\    state.pointer = incoming;
        \\    const values = [_]**u8{state.pointer};
        \\    state.pointer = &header;
        \\    for (values) |item| {
        \\        return item.*;
        \\    }
        \\    unreachable;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "item.*", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    const header = try expressionLoanTestBinding(typed.cache, site, "header");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    for (answer.loans) |loan| {
        if (loan.origin != .frame_cell) continue;
        try std.testing.expect(loan.binding_token != local and loan.binding_token != header);
    }
}

test "canonical expression loans retain writes through global inline pointer field aliases" {
    const source: [:0]const u8 =
        \\const Holder = struct { pointer: *u8 };
        \\var other: Holder = .{ .pointer = undefined };
        \\const saved: **u8 = &other.pointer;
        \\fn view() *u8 {
        \\    var local: u8 = 1;
        \\    other.pointer = &local;
        \\    return saved.*;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "view", "saved.*", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = true });
}

test "canonical expression loans cut a loop-carried cursor that rebinds itself" {
    // `current` is rebound from `next`, which was read through `current`: the
    // demand on `next` returns to itself through the loop's own store. Without
    // a cut the walk recurses to its depth cap.
    const source: [:0]const u8 =
        \\const Node = struct { next: ?*Node };
        \\fn last(start: *Node) *Node {
        \\    var current = start;
        \\    while (current.next) |next| {
        \\        current = next;
        \\    }
        \\    return current;
        \\}
        \\fn view() *Node {
        \\    var local: Node = .{ .next = null };
        \\    var current: *Node = &local;
        \\    while (current.next) |next| {
        \\        current = next;
        \\    }
        \\    return current;
        \\}
        \\fn walk(start: *Node) *Node {
        \\    var current = start;
        \\    while (true) {
        \\        const node = step(current) orelse return current;
        \\        current = node;
        \\    }
        \\}
        \\fn step(node: *Node) ?*Node {
        \\    return node.next;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    budget.clear();
    defer budget.clear();
    inline for (.{ "last", "view", "walk" }) |name| {
        // The returned `current` is the third mention in `last` and `view`
        // (loop condition, rebinding target, return) but the second in `walk`.
        const site = try expressionLoanTestSite(typed.tree(), name, "current", if (comptime std.mem.eql(u8, name, "walk")) 1 else 2);
        var remaining: u32 = work_limit;
        var query = ExpressionLoanQuery.init(.{
            .cache = typed.cache,
            .body = site.body,
            .scratch = &arena,
            .context = .{ .frame = typed.resolver.resolutionFrame(), .remaining = &remaining },
        });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        // The cut answers incompletely, and the loop costs a few repeats of
        // the cycle instead of every frame up to the depth cap.
        try std.testing.expect(!answer.complete);
        try std.testing.expect(work_limit - remaining < 1_000);
        try std.testing.expect(budget.peek() == null);
        if (comptime std.mem.eql(u8, name, "view")) {
            const local = try expressionLoanTestBinding(typed.cache, site, "local");
            try expectExpressionLoan(answer, .{ .binding_token = local, .origin = .frame_cell, .derivation = .propagated, .scalar_cell = false });
        }
    }
}

test "canonical expression loans walk a loop's unresolved events once, not once per path" {
    // Each event's argument is `cur`, which the loop rebinds from the last
    // event, so every event depends on every other one. Walking each simple
    // path through them costs more than the whole allowance at three events.
    const source: [:0]const u8 =
        \\fn view(input: []const u8) []const u8 {
        \\    var cur: []const u8 = input;
        \\    var n: usize = 0;
        \\    while (n < 10) : (n += 1) {
        \\        const e0 = ext(Missing, cur);
        \\        const e1 = ext(Missing, cur);
        \\        const e2 = ext(Missing, cur);
        \\        const e3 = ext(Missing, cur);
        \\        const e4 = ext(Missing, cur);
        \\        const e5 = ext(Missing, cur);
        \\        cur = e5;
        \\    }
        \\    return cur;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    budget.clear();
    defer budget.clear();
    const site = try expressionLoanTestSite(typed.tree(), "view", "cur", 7);
    var remaining: u32 = work_limit;
    var query = ExpressionLoanQuery.init(.{
        .cache = typed.cache,
        .body = site.body,
        .scratch = &arena,
        .context = .{ .frame = typed.resolver.resolutionFrame(), .remaining = &remaining },
    });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    try std.testing.expect(work_limit - remaining < work_limit / 5);
    try std.testing.expect(budget.peek() == null);
}

test "returned-storage depth cap records a labelled diagnostic" {
    const source: [:0]const u8 = "fn view(p: *u8) *u8 { return " ++ "(" ** 70 ++ "p" ++ ")" ** 70 ++ "; }";
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    budget.clear();
    defer budget.clear();
    const site = try expressionLoanTestSite(typed.tree(), "view", "(" ** 70 ++ "p" ++ ")" ** 70, 0);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    try std.testing.expectError(error.AnalysisBudgetExceeded, query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon }));
    const diagnostic = budget.take() orelse return error.TestExpectedBudget;
    try std.testing.expectEqual(budget.Limit.return_storage_depth, diagnostic.limit);
    try std.testing.expectEqual(depth_limit, diagnostic.limit_value);
    try std.testing.expectEqual(depth_limit, diagnostic.reached);
    try std.testing.expectEqualStrings("view", diagnostic.function.slice());
    try std.testing.expectEqual(@as(u32, 1), diagnostic.line);
    try std.testing.expect(diagnostic.column > 1);
}

test "borrow cycle cuts treat selections that extend one another as the same demand" {
    try std.testing.expect(Query.pathsNest("", "next"));
    try std.testing.expect(Query.pathsNest("next", "next"));
    try std.testing.expect(Query.pathsNest("next", "next.next"));
    try std.testing.expect(Query.pathsNest("next.next", "next"));
    try std.testing.expect(Query.pathsNest("parent", "next.parent"));
    try std.testing.expect(!Query.pathsNest("next", "nextra"));
    try std.testing.expect(!Query.pathsNest("parent", "xparent"));
    try std.testing.expect(!Query.pathsNest("left", "right"));
    try std.testing.expect(!Query.pathsNest("left.left", "left.right"));
}

const stack_precision_source: [:0]const u8 =
    \\const std = @import("std");
    \\const Index = enum(u32) { _ };
    \\const Call = struct { params: []const Index };
    \\fn view(buffer: *[1]Index, node: Index) ?Call {
    \\    buffer[0] = node;
    \\    return .{ .params = buffer };
    \\}
    \\fn scalarElement(node: Index) ?Index {
    \\    var buffer: [1]Index = undefined;
    \\    const call = view(&buffer, node) orelse return null;
    \\    return call.params[0];
    \\}
    \\fn leakView(node: Index) []const Index {
    \\    var buffer: [1]Index = undefined;
    \\    const call = view(&buffer, node) orelse return &.{};
    \\    return call.params;
    \\}
    \\const Tree = struct { source: []const u8, tokens: []const u32 };
    \\const Proto = struct { name_token: ?u32, params: []const u32 };
    \\fn fullProto(tree: Tree, buffer: *[1]u32, node: u32) ?Proto {
    \\    _ = tree;
    \\    buffer[0] = node;
    \\    return .{ .name_token = node, .params = buffer };
    \\}
    \\fn tokenSlice(tree: Tree, token: u32) []const u8 { return tree.source[token..]; }
    \\fn fnName(tree: *const Tree, declaration: u32) []const u8 {
    \\    var buffer: [1]u32 = undefined;
    \\    const proto = fullProto(tree.*, &buffer, declaration) orelse return "?";
    \\    return tokenSlice(tree.*, proto.name_token orelse return "?");
    \\}
    \\const Sink = struct { slice: []const u8 };
    \\fn stash(sink: *Sink, buf: *[4]u8) void { sink.slice = buf; }
    \\fn leakViaSink(sink: *Sink) []const u8 {
    \\    var buf: [4]u8 = undefined;
    \\    stash(sink, &buf);
    \\    return sink.slice;
    \\}
    \\const Selection = struct { arena: std.heap.ArenaAllocator };
    \\fn fill(path: []const u8, out: *[64]u8) usize {
    \\    @memcpy(out[0..path.len], path);
    \\    return path.len;
    \\}
    \\fn canonical(self: *Selection, path: []const u8) ![]const u8 {
    \\    var buffer: [64]u8 = undefined;
    \\    const len = fill(path, &buffer);
    \\    return self.arena.allocator().dupe(u8, buffer[0..len]);
    \\}
    \\fn leakFixed() ![]u8 {
    \\    var backing: [32]u8 = undefined;
    \\    var fixed = std.heap.FixedBufferAllocator.init(&backing);
    \\    return fixed.allocator().dupe(u8, "abc");
    \\}
    \\const Document = struct { tree: u32 };
    \\const Handle = struct { document: *Document, module: u32 };
    \\const Store = struct { handle: Handle, value: ?u32 = null };
    \\fn treeOfCopy(store: *const Store) *const u32 {
    \\    const copy = store.handle;
    \\    return &copy.document.tree;
    \\}
    \\fn inlineMember(store: *const Store) *const u32 {
    \\    var copy = store.handle;
    \\    _ = &copy;
    \\    return &copy.module;
    \\}
    \\fn throughLocalPointer() *const u32 {
    \\    var document: Document = .{ .tree = 1 };
    \\    const copy: Handle = .{ .document = &document, .module = 0 };
    \\    return &copy.document.tree;
    \\}
    \\fn valueOrNull(store: *Store) ?*const u32 {
    \\    return if (store.value) |*value| value else null;
    \\}
    \\const Model = struct {
    \\    types: []const u32,
    \\    fn findQualified(self: *const Model, path: []const []const u8) ?*const u32 {
    \\        if (path.len == 0) return null;
    \\        for (self.types) |*candidate| {
    \\            if (candidate.* == path.len) return candidate;
    \\        }
    \\        return null;
    \\    }
    \\};
    \\fn identity(path: []const []const u8) []const []const u8 { return path; }
    \\fn splitPath(out: *[4][]const u8, name: []const u8) usize {
    \\    out[0] = name;
    \\    return 1;
    \\}
    \\fn find(model: *const Model, name: []const u8) ?*const u32 {
    \\    var segments: [4][]const u8 = undefined;
    \\    const count = splitPath(&segments, name);
    \\    return model.findQualified(segments[0..count]);
    \\}
    \\fn leakPath(name: []const u8) []const []const u8 {
    \\    var segments: [4][]const u8 = undefined;
    \\    const count = splitPath(&segments, name);
    \\    return identity(segments[0..count]);
    \\}
    \\const Workspace = struct { used: u32 = 0 };
    \\const Query = struct {
    \\    workspace: *Workspace,
    \\    remaining: u32,
    \\    fn survives(self: *Query, boundary: u32) !bool {
    \\        self.workspace.used += boundary;
    \\        return self.workspace.used > self.remaining;
    \\    }
    \\    fn handle(self: *Query) *Workspace { return self.workspace; }
    \\};
    \\fn survivesHandoff(remaining: u32, boundary: u32) !bool {
    \\    var local_workspace: Workspace = .{};
    \\    var query: Query = .{ .workspace = &local_workspace, .remaining = remaining };
    \\    return query.survives(boundary);
    \\}
    \\fn leakHandoff() *Workspace {
    \\    var local_workspace: Workspace = .{};
    \\    var query: Query = .{ .workspace = &local_workspace, .remaining = 1 };
    \\    return query.handle();
    \\}
    \\fn wideBits() usize {
    \\    var local: u8 = 1;
    \\    return @intFromPtr(&local);
    \\}
;

/// Whether the expression's canonical loans include a frame cell of `local`.
fn stackPrecisionLoan(function: []const u8, expression: []const u8, local: []const u8) !bool {
    const typed = try Typed.init(std.testing.allocator, stack_precision_source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), function, expression, 0);
    const binding = try expressionLoanTestBinding(typed.cache, site, local);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.binding_token == binding and loan.origin == .frame_cell) return true;
    }
    return false;
}

test "canonical expression loans: an element read from a call-filled view carries no stack address" {
    try std.testing.expect(!try stackPrecisionLoan("scalarElement", "call.params[0]", "buffer"));
    try std.testing.expect(try stackPrecisionLoan("leakView", "call.params", "buffer"));
}

test "canonical expression loans: a scalar result of a call over a local-holding struct carries no stack address" {
    try std.testing.expect(!try stackPrecisionLoan("survivesHandoff", "query.survives(boundary)", "local_workspace"));
    try std.testing.expect(try stackPrecisionLoan("leakHandoff", "query.handle()", "local_workspace"));
}

const rewrite_stack_source: [:0]const u8 =
    \\const Chain = struct { lead: []const u8, suffixes: [][]const u8 };
    \\fn mint(chain: Chain, flag: bool) []const u8 {
    \\    var storage = chain.lead;
    \\    if (flag) storage = chain.lead;
    \\    return storage;
    \\}
    \\fn leakMint(chain: Chain, flag: bool) [][]const u8 {
    \\    var storage = chain.suffixes;
    \\    if (flag) storage = chain.suffixes;
    \\    return storage;
    \\}
    \\fn resolve(name: []const u8, flag: bool) []const u8 {
    \\    var suffixes: [4][]const u8 = undefined;
    \\    const chain: Chain = .{ .lead = name, .suffixes = suffixes[0..1] };
    \\    return mint(chain, flag);
    \\}
    \\fn leak(name: []const u8, flag: bool) [][]const u8 {
    \\    var suffixes: [4][]const u8 = undefined;
    \\    const chain: Chain = .{ .lead = name, .suffixes = suffixes[0..1] };
    \\    return leakMint(chain, flag);
    \\}
;

/// Whether the expression's canonical loans include a frame cell of `local`.
fn rewriteStackLoan(function: []const u8, expression: []const u8, local: []const u8) !bool {
    const typed = try Typed.init(std.testing.allocator, rewrite_stack_source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), function, expression, 0);
    const binding = try expressionLoanTestBinding(typed.cache, site, local);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.binding_token == binding and loan.origin == .frame_cell) return true;
    }
    return false;
}

test "canonical expression loans: a by-value struct result rewritten from one field carries only that field" {
    // The result is the field that names the caller's data; the sibling field
    // that points at the local buffer is not part of it.
    try std.testing.expect(!try rewriteStackLoan("resolve", "mint(chain, flag)", "suffixes"));
    try std.testing.expect(try rewriteStackLoan("leak", "leakMint(chain, flag)", "suffixes"));
}

const iterator_cost_source: [:0]const u8 =
    \\const std = @import("std");
    \\fn parseTriple(text: []const u8) !usize {
    \\    var it = std.mem.splitScalar(u8, text, '.');
    \\    const major = try std.fmt.parseUnsigned(usize, it.next() orelse return error.InvalidVersion, 10);
    \\    const minor = try std.fmt.parseUnsigned(usize, it.next() orelse return error.InvalidVersion, 10);
    \\    const patch = try std.fmt.parseUnsigned(usize, it.next() orelse return error.InvalidVersion, 10);
    \\    return major + minor + patch;
    \\}
    \\fn tailAfterPair(text: []const u8) ![]const u8 {
    \\    var it = std.mem.splitScalar(u8, text, '.');
    \\    _ = try std.fmt.parseUnsigned(usize, it.next() orelse return error.InvalidVersion, 10);
    \\    _ = try std.fmt.parseUnsigned(usize, it.next() orelse return error.InvalidVersion, 10);
    \\    return it.rest();
    \\}
    \\fn leakTail(text: []const u8) ![]const u8 {
    \\    var buffer: [65]u8 = undefined;
    \\    const count = @min(text.len, buffer.len);
    \\    @memcpy(buffer[0..count], text[0..count]);
    \\    return try tailAfterPair(buffer[0..count]);
    \\}
;

test "canonical expression loans: repeated iterator steps feeding a tiny callee stay well inside the work budget" {
    const typed = try Typed.init(std.testing.allocator, iterator_cost_source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "parseTriple", "major + minor + patch", 0);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    _ = answer;
    // Guard against regressions to whole-scan cost (41490 units before the
    // memoized effect, cell, and ordered-mutation scans; 26625 measured after).
    // 60% of the budget keeps headroom for the cold whole-effect demand.
    const used = work_limit - query.remaining;
    const bound = work_limit * 3 / 5;
    if (used >= bound)
        std.debug.print("iterator scalar-copy loan work: {d}; strict bound: {d}\n", .{ used, bound });
    try std.testing.expect(used < bound);
}

test "canonical expression loans: a tail iterator over a local buffer still carries that buffer after repeated steps" {
    const typed = try Typed.init(std.testing.allocator, iterator_cost_source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "leakTail", "tailAfterPair(buffer[0..count])", 0);
    const binding = try expressionLoanTestBinding(typed.cache, site, "buffer");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.binding_token == binding and loan.origin == .frame_cell) return;
    }
    return error.TestExpectedLoan;
}

test "canonical expression loans: a token index from a call-filled prototype selects only the tree" {
    try std.testing.expect(!try stackPrecisionLoan("fnName", "tokenSlice(tree.*, proto.name_token orelse return \"?\")", "buffer"));
    try std.testing.expect(try stackPrecisionLoan("leakViaSink", "sink.slice", "buf"));
}

test "canonical expression loans: a copied allocation from an external receiver does not borrow the filled buffer" {
    try std.testing.expect(!try stackPrecisionLoan("canonical", "self.arena.allocator().dupe(u8, buffer[0..len])", "buffer"));
    try std.testing.expect(try stackPrecisionLoan("leakFixed", "fixed.allocator().dupe(u8, \"abc\")", "fixed"));
}

test "canonical expression loans: an address through a pointer member is not a cell of the holder" {
    try std.testing.expect(!try stackPrecisionLoan("treeOfCopy", "&copy.document.tree", "copy"));
    try std.testing.expect(try stackPrecisionLoan("inlineMember", "&copy.module", "copy"));
    try std.testing.expect(try stackPrecisionLoan("throughLocalPointer", "&copy.document.tree", "document"));
    try std.testing.expect(!try stackPrecisionLoan("valueOrNull", "if (store.value) |*value| value else null", "store"));
}

test "canonical expression loans: a pointer loop capture addresses the iterable's elements" {
    try std.testing.expect(!try stackPrecisionLoan("find", "model.findQualified(segments[0..count])", "segments"));
    try std.testing.expect(try stackPrecisionLoan("leakPath", "identity(segments[0..count])", "segments"));
}

test "canonical expression loans: address bits in a pointer-wide integer stay borrowed" {
    try std.testing.expect(try stackPrecisionLoan("wideBits", "@intFromPtr(&local)", "local"));
}

// ── Stack-escape flow precision ──────────────────────────────────────────────

const stack_flow_source: [:0]const u8 =
    \\const std = @import("std");
    \\
    \\// A recursive parameter type is not an unbounded reach for stores.
    \\const Atom = union(enum) { text: []const u8, capture: u8, opt: []const Atom };
    \\const Match = struct { start: u32, end: u32, captures: [4]?u32 = @splat(null) };
    \\fn matchSlice(atoms: []const Atom, t: *u32, captures: *[4]?u32) bool {
    \\    for (atoms) |a| switch (a) {
    \\        .capture => |slot| {
    \\            captures[slot] = t.*;
    \\            t.* += 1;
    \\        },
    \\        else => return false,
    \\    };
    \\    return true;
    \\}
    \\fn matchAt(atoms: []const Atom, pos: u32) ?Match {
    \\    var m: Match = .{ .start = pos, .end = pos };
    \\    var t: u32 = pos;
    \\    if (matchSlice(atoms, &t, &m.captures)) {
    \\        m.end = t - 1;
    \\        return m;
    \\    }
    \\    return null;
    \\}
    \\const Tree = struct { kids: []const Tree, sink: *?*const u32 };
    \\fn plant(tree: *const Tree, slot: *u32) void {
    \\    tree.sink.* = slot;
    \\}
    \\fn leakTree(tree: *const Tree) ?*const u32 {
    \\    var slot: u32 = 0;
    \\    plant(tree, &slot);
    \\    return tree.sink.*;
    \\}
    \\const Cell = union(enum) { leaf: u32, link: *const u32, more: []Cell };
    \\fn stash(cells: []Cell, slot: *u32) void {
    \\    cells[0] = .{ .link = slot };
    \\}
    \\fn leakCells(cells: []Cell) Cell {
    \\    var slot: u32 = 0;
    \\    stash(cells, &slot);
    \\    return cells[0];
    \\}
    \\
    \\// A switch yields one prong's value.
    \\const Tag = enum { a, b, c };
    \\fn lexeme(tag: Tag) ?[]const u8 {
    \\    return switch (tag) {
    \\        .a => null,
    \\        .b => "b",
    \\        .c => "c",
    \\    };
    \\}
    \\const Source = struct { text: []const u8 };
    \\fn sliceOf(source: Source, tag: Tag, start: u32) []const u8 {
    \\    if (lexeme(tag)) |text| return text;
    \\    return source.text[start..];
    \\}
    \\const Proto = struct { params: []const u32 };
    \\const ProtoIter = struct {
    \\    proto: *const Proto,
    \\    index: u32,
    \\    fn next(it: *ProtoIter) ?u32 {
    \\        if (it.index >= it.proto.params.len) return null;
    \\        const token = it.proto.params[it.index];
    \\        it.index += 1;
    \\        return token;
    \\    }
    \\};
    \\fn firstName(source: Source, tag: Tag, proto: Proto) []const u8 {
    \\    var it: ProtoIter = .{ .proto = &proto, .index = 0 };
    \\    const token = it.next() orelse return "";
    \\    return sliceOf(source, tag, token);
    \\}
    \\fn pickBuf(tag: Tag, other: []const u8) []const u8 {
    \\    var buf: [4]u8 = undefined;
    \\    return switch (tag) { .a => other, .b => buf[0..], .c => "c" };
    \\}
    \\fn pickSafe(tag: Tag, other: []const u8) []const u8 {
    \\    var buf: [4]u8 = undefined;
    \\    _ = &buf;
    \\    return switch (tag) { .a => other, .b => "b", .c => "c" };
    \\}
    \\
    \\// An address-free value built by an analysable callee holds no address.
    \\const Param = struct { name_token: ?u32, type_expr: ?u32 };
    \\const Syntax = struct {
    \\    tokens: []const u32,
    \\    fn first(tree: *const Syntax, node: u32) u32 {
    \\        return tree.tokens[node];
    \\    }
    \\};
    \\const Signature = struct { params: []const u32 };
    \\fn fullSignature(tree: *const Syntax, buffer: *[1]u32, node: u32) ?Signature {
    \\    _ = tree;
    \\    buffer[0] = node;
    \\    return .{ .params = buffer };
    \\}
    \\const ParamIter = struct {
    \\    tree: *const Syntax,
    \\    params: []const u32,
    \\    param_i: u32,
    \\    fn init(signature: *const Signature, tree: *const Syntax) ParamIter {
    \\        return .{ .tree = tree, .params = signature.params, .param_i = 0 };
    \\    }
    \\    fn next(it: *ParamIter) ?Param {
    \\        if (it.param_i >= it.params.len) return null;
    \\        const param_type = it.params[it.param_i];
    \\        it.param_i += 1;
    \\        return .{ .name_token = it.tree.first(param_type) - 1, .type_expr = param_type };
    \\    }
    \\};
    \\fn getParam(tree: *const Syntax, node: u32, index: u16) ?Param {
    \\    var buffer: [1]u32 = undefined;
    \\    const func = fullSignature(tree, &buffer, node).?;
    \\    var i: u16 = 0;
    \\    var it: ParamIter = .init(&func, tree);
    \\    while (it.next()) |param| : (i += 1) {
    \\        if (index == i) return param;
    \\    }
    \\    return null;
    \\}
    \\const Slot = struct { target: *const u32 };
    \\const SlotIter = struct {
    \\    slots: []const Slot,
    \\    index: u32,
    \\    fn next(it: *SlotIter) ?Slot {
    \\        if (it.index >= it.slots.len) return null;
    \\        const slot = it.slots[it.index];
    \\        it.index += 1;
    \\        return slot;
    \\    }
    \\};
    \\fn slotAt(want: u32) ?Slot {
    \\    var value: u32 = 7;
    \\    const all = [_]Slot{.{ .target = &value }};
    \\    var it: SlotIter = .{ .slots = &all, .index = 0 };
    \\    var i: u32 = 0;
    \\    while (it.next()) |slot| : (i += 1) {
    \\        if (i == want) return slot;
    \\    }
    \\    return null;
    \\}
    \\
    \\// `|*element|` addresses the referent of a slice, the cell of an array.
    \\const Info = struct { name: []const u8, parent: ?u32 };
    \\const Model = struct { types: []const Info };
    \\const Resolved = struct { info: *const Info };
    \\fn lookup(model: *const Model, wanted: []const u8) ?Resolved {
    \\    const view = model.types;
    \\    for (view) |*candidate| {
    \\        if (std.mem.eql(u8, candidate.name, wanted)) return .{ .info = candidate };
    \\    }
    \\    return null;
    \\}
    \\fn lookupLocal(wanted: []const u8) ?Resolved {
    \\    const local = [_]Info{.{ .name = "a", .parent = null }};
    \\    for (local) |*candidate| {
    \\        if (std.mem.eql(u8, candidate.name, wanted)) return .{ .info = candidate };
    \\    }
    \\    return null;
    \\}
    \\
    \\// An address-of literal holds copies of its elements.
    \\const Escaper = struct {
    \\    out: *std.Io.Writer,
    \\    fn drain(self: *Escaper, data: []const []const u8, splat: usize) std.Io.Writer.Error!usize {
    \\        const out = self.out;
    \\        for (data, 0..) |vec, i| {
    \\            const index = std.mem.findAny(u8, vec, "$}\\") orelse continue;
    \\            if (i != 0) {
    \\                return try out.writeSplat(data[0..i], splat);
    \\            }
    \\            const unescaped = vec[index];
    \\            try out.writeAll(&.{ '\\', unescaped });
    \\            return 1;
    \\        }
    \\        return 0;
    \\    }
    \\};
    \\fn leakLiteral() []const *const u8 {
    \\    var local: u8 = 0;
    \\    return &.{&local};
    \\}
    \\
    \\// join and concat return fresh provider memory, never their inputs.
    \\const Cache = struct {
    \\    gpa: std.mem.Allocator,
    \\    fn rootFor(cache: *Cache, from: []const u8, name: []const u8) ![]u8 {
    \\        const dir = std.fs.path.dirname(from) orelse return error.None;
    \\        return try std.fs.path.join(cache.gpa, &.{ dir, name });
    \\    }
    \\    fn concatFor(cache: *Cache, from: []const u8, name: []const u8) ![]u8 {
    \\        const dir = std.fs.path.dirname(from) orelse return error.None;
    \\        return try std.mem.concat(cache.gpa, u8, &.{ dir, name });
    \\    }
    \\};
    \\fn joinLocal(a: []const u8, b: []const u8) ![]u8 {
    \\    var backing: [64]u8 = undefined;
    \\    var fixed = std.heap.FixedBufferAllocator.init(&backing);
    \\    return std.fs.path.join(fixed.allocator(), &.{ a, b });
    \\}
    \\
    \\// std.mem.swap only permutes what its two pointees hold.
    \\const Segments = struct { names: [4][]const u8, len: usize };
    \\fn reversed(source: []const u8) Segments {
    \\    var path: Segments = .{ .names = undefined, .len = 2 };
    \\    path.names[0] = source[0..1];
    \\    path.names[1] = source[1..2];
    \\    std.mem.swap([]const u8, &path.names[0], &path.names[1]);
    \\    return path;
    \\}
    \\fn reversedLocal(source: []const u8) Segments {
    \\    var buf: [2]u8 = undefined;
    \\    var path: Segments = .{ .names = undefined, .len = 2 };
    \\    path.names[0] = source[0..1];
    \\    path.names[1] = buf[0..];
    \\    std.mem.swap([]const u8, &path.names[0], &path.names[1]);
    \\    return path;
    \\}
;

/// The first token declaring local `name` (`const name` / `var name`) in the body:
/// a local declared after the expression, which lexical lookup at its horizon misses.
fn stackFlowBinding(tree: *const Ast, site: ExpressionLoanTestSite, name: []const u8) !Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    var token = tree.firstToken(site.body) + 1;
    while (token <= tree.lastToken(site.body)) : (token += 1) {
        if (tags[token] != .identifier or !std.mem.eql(u8, tree.tokenSlice(token), name)) continue;
        if (tags[token - 1] == .keyword_const or tags[token - 1] == .keyword_var) return token;
    }
    return error.TestExpectedBinding;
}

/// Whether the canonical loans of `expression` (the `occurrence`th node with
/// that source in `function`) include a frame cell of `local`.
fn stackFlowLoan(function: []const u8, expression: []const u8, occurrence: usize, local: []const u8) !bool {
    const typed = try Typed.init(std.testing.allocator, stack_flow_source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), function, expression, occurrence);
    const binding = expressionLoanTestBinding(typed.cache, site, local) catch try stackFlowBinding(typed.tree(), site, local);
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    for (answer.loans) |loan| {
        if (loan.binding_token == binding and loan.origin == .frame_cell) return true;
    }
    return false;
}

test "canonical expression loans: a recursive parameter type is not an unbounded reach for stores" {
    try std.testing.expect(!try stackFlowLoan("matchAt", "m", 2, "m"));
    try std.testing.expect(!try stackFlowLoan("matchAt", "m", 2, "t"));
    try std.testing.expect(try stackFlowLoan("leakTree", "tree.sink.*", 0, "slot"));
    try std.testing.expect(try stackFlowLoan("leakCells", "cells[0]", 0, "slot"));
}

test "canonical expression loans: a switch of constants returns no storage" {
    try std.testing.expect(!try stackFlowLoan("firstName", "sliceOf(source, tag, token)", 0, "proto"));
    try std.testing.expect(!try stackFlowLoan("pickSafe", "switch (tag) { .a => other, .b => \"b\", .c => \"c\" }", 0, "buf"));
    try std.testing.expect(try stackFlowLoan("pickBuf", "switch (tag) { .a => other, .b => buf[0..], .c => \"c\" }", 0, "buf"));
}

test "canonical expression loans: an index struct built by an analysable callee holds no address" {
    try std.testing.expect(!try stackFlowLoan("getParam", "param", 0, "func"));
    try std.testing.expect(!try stackFlowLoan("getParam", "param", 0, "buffer"));
    try std.testing.expect(try stackFlowLoan("slotAt", "slot", 0, "value"));
}

test "canonical expression loans: a pointer capture over a slice local addresses its referent" {
    try std.testing.expect(!try stackFlowLoan("lookup", ".{ .info = candidate }", 0, "view"));
    try std.testing.expect(try stackFlowLoan("lookupLocal", ".{ .info = candidate }", 0, "local"));
}

test "canonical expression loans: an address-of literal borrows its elements' values, not their cells" {
    try std.testing.expect(!try stackFlowLoan("drain", "try out.writeSplat(data[0..i], splat)", 0, "unescaped"));
    try std.testing.expect(try stackFlowLoan("leakLiteral", "&.{&local}", 0, "local"));
}

test "canonical expression loans: join and concat results are provider memory, not their inputs" {
    try std.testing.expect(!try stackFlowLoan("rootFor", "try std.fs.path.join(cache.gpa, &.{ dir, name })", 0, "dir"));
    try std.testing.expect(!try stackFlowLoan("concatFor", "try std.mem.concat(cache.gpa, u8, &.{ dir, name })", 0, "dir"));
    try std.testing.expect(try stackFlowLoan("joinLocal", "std.fs.path.join(fixed.allocator(), &.{ a, b })", 0, "fixed"));
}

test "canonical expression loans: a swap inside one binding adds no loan to it" {
    try std.testing.expect(!try stackFlowLoan("reversed", "path", 0, "path"));
}

test "canonical expression loans do not retain scalar mutation helper receiver cells" {
    const source: [:0]const u8 =
        \\const Index = struct { items: []u32, count: usize = 0 };
        \\fn append(index: *Index, kinds: []u8) void {
        \\    index.items[index.count] = 1;
        \\    kinds[index.count] = 2;
        \\    index.count += 1;
        \\}
        \\fn safe(items: []u32, kinds: []u8) []u32 {
        \\    var index: Index = .{ .items = items };
        \\    append(&index, kinds);
        \\    return index.items;
        \\}
        \\const Holder = struct { pointer: ?*Index = null };
        \\fn retain(holder: *Holder, index: *Index) void { holder.pointer = index; }
        \\fn unsafe(items: []u32) *Index {
        \\    var index: Index = .{ .items = items };
        \\    var holder: Holder = .{};
        \\    retain(&holder, &index);
        \\    return holder.pointer.?;
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    inline for (.{ .{ "safe", "index.items", false }, .{ "unsafe", "holder.pointer.?", true } }) |case| {
        const site = try expressionLoanTestSite(typed.tree(), case[0], case[1], 0);
        const token = try expressionLoanTestBinding(typed.cache, site, "index");
        var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
        const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
        if (case[2]) {
            try expectExpressionLoan(answer, .{ .binding_token = token, .origin = .frame_cell, .derivation = .propagated });
        } else {
            try expectNoExpressionLoan(answer, token);
        }
    }
}

test "borrow consumer distinguishes scalar inline copies from retained pointer payloads" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const Pending = struct { inline_values: [2]u64 = undefined, owned: []u64 = &.{} };
        \\fn expand(values: []u64) []u64 { values[0] = 7; return values[0..1]; }
        \\pub fn detect() Pending {
        \\    var values: [2]u64 = undefined;
        \\    const expanded = expand(&values);
        \\    var pending: Pending = .{};
        \\    @memcpy(pending.inline_values[0..expanded.len], expanded);
        \\    return pending;
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const Pending = struct { inline_values: [1]*u8 = undefined };
        \\pub fn detect() Pending {
        \\    var value: u8 = 1;
        \\    const values = [_]*u8{&value};
        \\    var pending: Pending = .{};
        \\    @memcpy(&pending.inline_values, &values);
        \\    return pending;
        \\}
    );
}

test "scalar inline memcpy retains encoded element addresses without retaining source headers" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const Pending = struct { words: [1]usize = .{0}, other: []const u8 = "" };
        \\pub fn detect() Pending {
        \\    var local: u8 = 1;
        \\    const words = [_]usize{@intFromPtr(&local)};
        \\    var pending: Pending = .{};
        \\    @memcpy(&pending.words, &words);
        \\    return pending;
        \\}
    );
}

test "borrow consumer does not retain scalar ArrayList appendSlice source cells" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn extract(out: []u32) usize { out[0] = 1; return 1; }
        \\pub fn detect(allocator: std.mem.Allocator) ![]u32 {
        \\    var list = std.ArrayList(u32).empty;
        \\    errdefer list.deinit(allocator);
        \\    var indexes: [8]u32 = undefined;
        \\    const count = extract(&indexes);
        \\    try list.appendSlice(allocator, indexes[0..count]);
        \\    return list.toOwnedSlice(allocator);
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const std = @import("std");
        \\pub fn detect(allocator: std.mem.Allocator) ![]*u8 {
        \\    var list = std.ArrayList(*u8).empty;
        \\    errdefer list.deinit(allocator);
        \\    var local: u8 = 1;
        \\    const values = [_]*u8{&local};
        \\    try list.appendSlice(allocator, &values);
        \\    return list.toOwnedSlice(allocator);
        \\}
    );
}

test "borrow consumer distinguishes allocated string copies from borrowed source pointers" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Value = struct { typ: u8, obj: *anyopaque };
        \\const TypedSlice = struct { ref: *anyopaque, slice: []u8 };
        \\const Store = struct {
        \\    allocator: std.mem.Allocator,
        \\    fn createTyped(self: *Store, size: usize) ![]u8 { return self.allocator.alloc(u8, size); }
        \\    fn allocSlice(self: *Store, size: usize) !TypedSlice {
        \\        const bytes = try self.createTyped(size);
        \\        return .{ .ref = @ptrCast(bytes.ptr), .slice = bytes };
        \\    }
        \\};
        \\fn storeString(store: *Store, bytes: []const u8) !Value {
        \\    const alloc = try store.allocSlice(bytes.len + 1);
        \\    @memcpy(alloc.slice[0..bytes.len], bytes);
        \\    alloc.slice[bytes.len] = 0;
        \\    return .{ .typ = 1, .obj = @ptrCast(alloc.slice.ptr) };
        \\}
        \\pub fn detect(store: *Store) !Value {
        \\    var buf: [65]u8 = undefined;
        \\    buf[0] = '4';
        \\    buf[1] = '2';
        \\    return storeString(store, buf[0..2]);
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const Value = struct { typ: u8, obj: *anyopaque };
        \\fn storeString(bytes: []u8) Value { return .{ .typ = 1, .obj = @ptrCast(bytes.ptr) }; }
        \\pub fn detect() Value {
        \\    var buf: [2]u8 = .{ '4', '2' };
        \\    return storeString(&buf);
        \\}
    );
}

test "borrow consumer does not retain local cursors when appending scalar token copies" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Cursor = struct { src: []const u8, offset: usize = 0, line: u16 = 1, col: u16 = 1 };
        \\const Token = struct { start: u32, end: u32, line: u16, col: u16 };
        \\fn token(start: *const Cursor, end: *const Cursor) Token {
        \\    return .{ .start = @intCast(start.offset), .end = @intCast(end.offset), .line = start.line, .col = end.col };
        \\}
        \\fn lex(c: *Cursor) !Token {
        \\    const start = c.*;
        \\    if (c.offset < c.src.len) c.offset += 1;
        \\    return token(&start, c);
        \\}
        \\pub fn detect(allocator: std.mem.Allocator, src: []const u8) ![]Token {
        \\    var list = std.ArrayList(Token).empty;
        \\    errdefer list.deinit(allocator);
        \\    var c: Cursor = .{ .src = src };
        \\    const tok = try lex(&c);
        \\    try list.append(allocator, tok);
        \\    return list.toOwnedSlice(allocator);
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const std = @import("std");
        \\const Cursor = struct { offset: usize = 0 };
        \\const Token = struct { cursor: *Cursor };
        \\fn lex(c: *Cursor) Token { c.offset += 1; return .{ .cursor = c }; }
        \\pub fn detect(allocator: std.mem.Allocator) ![]Token {
        \\    var list = std.ArrayList(Token).empty;
        \\    errdefer list.deinit(allocator);
        \\    var c: Cursor = .{};
        \\    try list.append(allocator, lex(&c));
        \\    return list.toOwnedSlice(allocator);
        \\}
    );
}

test "borrow consumer separates staged deep byte copies from retained source headers" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owned = struct { allocator: std.mem.Allocator, bytes: []u8 };
        \\const Builder = struct {
        \\    allocator: std.mem.Allocator,
        \\    staged: []u8 = &.{},
        \\    fn init(allocator: std.mem.Allocator) Builder { return .{ .allocator = allocator }; }
        \\    fn addSectionData(self: *Builder, bytes: []const u8) !void {
        \\        self.staged = try self.allocator.dupe(u8, bytes);
        \\    }
        \\    fn publish(self: *Builder) !Owned {
        \\        return .{ .allocator = self.allocator, .bytes = try self.allocator.dupe(u8, self.staged) };
        \\    }
        \\    fn deinit(self: *Builder) void { if (self.staged.len != 0) self.allocator.free(self.staged); }
        \\};
        \\pub fn detect(allocator: std.mem.Allocator) !Owned {
        \\    const text_bytes = [_]u8{ 1, 2, 3 };
        \\    var builder = Builder.init(allocator);
        \\    defer builder.deinit();
        \\    try builder.addSectionData(&text_bytes);
        \\    return builder.publish();
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const Owned = struct { bytes: []const u8 };
        \\const Builder = struct {
        \\    staged: []const u8 = &.{},
        \\    fn addSectionData(self: *Builder, bytes: []const u8) void { self.staged = bytes; }
        \\    fn publish(self: *Builder) Owned { return .{ .bytes = self.staged }; }
        \\};
        \\pub fn detect() Owned {
        \\    const text_bytes = [_]u8{ 1, 2, 3 };
        \\    var builder: Builder = .{};
        \\    builder.addSectionData(&text_bytes);
        \\    return builder.publish();
        \\}
    );
}

test "borrow consumer keeps external image pins independent of by value handle cells" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    const declarations =
        \\const std = @import("std");
        \\const Image = struct { active: std.atomic.Value(u32) = .init(0), owner: *Owner };
        \\const Pin = struct { owner: *Owner, image: *Image };
        \\const Owner = struct {
        \\    fn pin(self: *Owner, handle: Handle) Pin {
        \\        _ = handle.image.active.fetchAdd(1, .monotonic);
        \\        return .{ .owner = self, .image = handle.image };
        \\    }
        \\};
        \\const Handle = struct {
        \\    owner: *Owner,
        \\    image: *Image,
        \\    fn fromImage(image: *Image) Handle { return .{ .owner = image.owner, .image = image }; }
        \\    fn pin(self: Handle) Pin { return self.owner.pin(self); }
        \\};
        \\
    ;
    try testing.expectNoFireTyped(check, declarations ++
        \\pub fn detect(image: *Image) Pin {
        \\    const handle = Handle.fromImage(image);
        \\    return handle.pin();
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned", declarations ++
        \\pub fn detect(owner: *Owner) Pin {
        \\    var image: Image = .{ .owner = owner };
        \\    const handle = Handle.fromImage(&image);
        \\    return handle.pin();
        \\}
    );
}

test "borrow consumer does not retain receiver addresses for copied inline pointer slots" {
    const testing = @import("../testing.zig");
    const check = @import("../rules/borrow/borrowed_slice_into_stack_buffer_returned.zig").check;
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Path = struct {
        \\    root: []const u8,
        \\    segments: [2][]const u8 = .{ "", "" },
        \\    len: usize = 0,
        \\    fn push(self: *Path, segment: []const u8) void {
        \\        self.segments[self.len] = segment;
        \\        self.len += 1;
        \\    }
        \\};
        \\pub fn detect(first: []const u8, second: []const u8) Path {
        \\    var path: Path = .{ .root = first };
        \\    path.push(first);
        \\    path.push(second);
        \\    std.mem.swap([]const u8, &path.segments[0], &path.segments[1]);
        \\    return path;
        \\}
    );
    try testing.expectFiresTyped(check, "borrowed-slice-into-stack-buffer-returned",
        \\const Path = struct {
        \\    segments: [1][]const u8 = .{""},
        \\    fn push(self: *Path, segment: []const u8) void { self.segments[0] = segment; }
        \\};
        \\pub fn detect() Path {
        \\    const text_bytes = [_]u8{1};
        \\    var path: Path = .{};
        \\    path.push(&text_bytes);
        \\    return path;
        \\}
    );
}

test "canonical expression loans separate proved aliases from speculative call arguments" {
    const source: [:0]const u8 =
        \\extern fn opaqueValue(pointer: *const u8) *const u8;
        \\fn identity(pointer: *const u8) *const u8 { return pointer; }
        \\const Pair = struct { known: *const u8, unknown: *const u8 };
        \\fn select() Pair {
        \\    var first: u8 = 1;
        \\    var second: u8 = 2;
        \\    return .{ .known = identity(&first), .unknown = opaqueValue(&second) };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "select", ".{ .known = identity(&first), .unknown = opaqueValue(&second) }", 0);
    const first = try expressionLoanTestBinding(typed.cache, site, "first");
    const second = try expressionLoanTestBinding(typed.cache, site, "second");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    try std.testing.expect(!answer.complete);
    var proved_first = false;
    var speculative_second = false;
    for (answer.loans) |loan| {
        if (loan.origin != .frame_cell) continue;
        if (loan.binding_token == first and loan.proved) proved_first = true;
        if (loan.binding_token == second) {
            try std.testing.expect(!loan.proved);
            speculative_second = true;
        }
    }
    try std.testing.expect(proved_first and speculative_second);
}

test "canonical expression loan proof upgrades do not depend on speculative walk order" {
    const source: [:0]const u8 =
        \\extern fn opaqueValue(pointer: *const u8) *const u8;
        \\const Pair = struct { unknown: *const u8, known: *const u8 };
        \\fn select() Pair {
        \\    var local: u8 = 1;
        \\    return .{ .unknown = opaqueValue(&local), .known = &local };
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const site = try expressionLoanTestSite(typed.tree(), "select", ".{ .unknown = opaqueValue(&local), .known = &local }", 0);
    const local = try expressionLoanTestBinding(typed.cache, site, "local");
    var query = ExpressionLoanQuery.init(.{ .cache = typed.cache, .body = site.body, .scratch = &arena, .context = .{} });
    const answer = try query.expressionLoansAt(.{ .selection = .{ .node = site.node }, .horizon = site.horizon });
    var proved = false;
    for (answer.loans) |loan|
        if (loan.origin == .frame_cell and loan.binding_token == local and loan.proved) {
            proved = true;
        };
    try std.testing.expect(proved);
}
