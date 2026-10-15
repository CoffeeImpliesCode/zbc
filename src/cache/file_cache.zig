//! Per-file shared state for pattern detectors.
//!
//! Both `FileModel` (per-file TypeTable + FnTable) and `LocalBindings`
//! (per-fn binding-origin tracker) are expensive to build but identical
//! for every consumer.  Before this cache, ARCHITECTURE.md claimed they
//! were "built ONCE per file" but the code rebuilt them inside every
//! rule that needed them — for an N-fn file with 13 LocalBindings-using
//! rules, that was 13N builds.
//!
//! The cache materializes each at most once per file:
//!   - `fileModel()` lazily builds (and caches) the FileModel on first
//!     call.
//!   - `localBindings(proto, body)` returns a cached LocalBindings if
//!     present; builds + stores otherwise.  Keyed by the body's node
//!     index.
//!   - Imported ownership folds publish immutable scalar answers for all
//!     completed foreign bodies, including non-taking bodies. Repeated
//!     method queries reuse by-value summaries with caller-owned field paths.
//!     Failed folds or publication allocations remain retryable.
//!
//! The cache is per-file, owned by lib.zig, deinit'd at the end of each
//! file's analysis.  Threading: main.zig's worker pool processes one
//! file per thread; no cross-thread sharing.

const std = @import("std");
const Ast = std.zig.Ast;

const file_model = @import("../model/file_model.zig");
const local_bindings = @import("../model/local_bindings.zig");
const fn_summary = @import("../model/fn_summary.zig");
const tokens = @import("../ast/tokens.zig");
const numeric_nodes = @import("../model/numeric_nodes.zig");
const zls_resolver_mod = @import("../type_resolver.zig");
const project_cache_mod = @import("project_cache.zig");
const SourcePolicy = @import("type_engine").SourcePolicy;
const cfg_builder_mod = @import("../flow/cfg_builder.zig");
const cfg_mod = @import("../flow/cfg.zig");
const grow_analysis_mod = @import("grow_analysis.zig");
const worklist_mod = @import("../flow/worklist.zig");
const comptime_fill_mod = @import("../flow/comptime_fill.zig");
const config_mod = @import("../config.zig");
const problem_mod = @import("../problem.zig");
const call_summary_mod = @import("call_summary.zig");
const fresh_storage_mod = @import("fresh_storage.zig");
const return_storage_mod = @import("return_storage.zig");
const storage_alias_mod = @import("storage_alias.zig");
const engine = @import("type_engine");
const budget_mod = @import("../budget.zig");
const TypeResolver = zls_resolver_mod.TypeResolver;

/// The module this cache's own names are written in.  A document is
/// opened in the module that declared it, and that module — not the
/// reader's — is what its names mean, so the id is part of the key of
/// every declaration-scoped memo here.
pub const ModuleId = engine.ModuleId;

/// A declaration, addressed by the tree and module it was read in
/// plus its own node.  The same source compiled into two environments
/// is two declarations here, and an answer about one says nothing
/// about the other.
pub const DeclKey = struct {
    tree: *const Ast,
    module: ModuleId,
    declaration: Ast.Node.Index,
};

/// A source document, addressed the same way a declaration is.  Used
/// where the key names the FILE rather than a declaration in it.
pub const DocumentKey = struct {
    tree: *const Ast,
    module: ModuleId,
};

/// Resource failures while a source document is being opened.  Named
/// rather than inferred: the open is mutually recursive with the fold
/// that reads the document it opens, so reading each other's inferred
/// set is a dependency loop.
pub const OpenError = error{OutOfMemory};

/// What BUILDING this file's own model can fail at — `OutOfMemory`,
/// `InvalidSyntax`, `SourceTooWide`, `TooManyTypes`.
///
/// DERIVED from `file_model.buildWithPath`'s own return type rather than
/// written out, because that set is what a summary actually reads: every
/// `summaryOfFn` models its document before it reads one.  Naming the
/// members by hand here is a second copy of a set that changes when the
/// model builder changes, and a stale copy is a compile error at the call
/// site rather than a wrong answer — which is the good kind of drift, but
/// still an edit the reader would have to make for no reason.
pub const ModelError = @typeInfo(@typeInfo(@TypeOf(file_model.buildWithPath)).@"fn".return_type.?).error_union.error_set;

/// Model, source-load, semantic-query, resource, and cancellation failures over
/// the whole summary fold. Cleanup walks also reject ranges that do not fit TokenIndex.
pub const SummaryError = ModelError || engine.SourceLoadError || std.Io.Cancelable || error{ OutOfMemory, AnalysisBudgetExceeded, SourceTooWide, UnsupportedScheme };

/// A function whose summary work exhausted an analysis budget.
pub const SummaryFailure = struct {
    fn_decl: Ast.Node.Index,
    /// Null when the walk that gave up recorded no limit.
    budget: ?budget_mod.Diagnostic,
};

/// Tracks the roots `resolveTransitiveTakesCollecting` gave up on. With no
/// sink every error propagates, which is the strict `resolveTransitiveTakes`.
const RootFailures = struct {
    sink: ?*std.ArrayListUnmanaged(SummaryFailure),
    failed: std.DynamicBitSetUnmanaged = .{},

    fn init(gpa: std.mem.Allocator, node_count: usize, sink: ?*std.ArrayListUnmanaged(SummaryFailure)) !RootFailures {
        if (sink == null) return .{ .sink = null };
        return .{ .sink = sink, .failed = try .initEmpty(gpa, node_count) };
    }

    fn deinit(self: *RootFailures, gpa: std.mem.Allocator) void {
        self.failed.deinit(gpa);
    }

    fn skipped(self: *const RootFailures, fn_decl: Ast.Node.Index) bool {
        return self.sink != null and self.failed.isSet(@intFromEnum(fn_decl));
    }

    /// Record a budget failure of `fn_decl`; return any other error.
    ///
    /// The root stays failed: its summary is withdrawn and every later lookup
    /// re-raises the failure recorded here (`FileCache.failed_roots`).  A
    /// later phase can give up after earlier ones already published facts,
    /// and a summary that holds only part of its fold must not be read as
    /// the whole of it.
    fn note(self: *RootFailures, cache: *FileCache, fn_decl: Ast.Node.Index, err: anyerror) anyerror!void {
        const sink = self.sink orelse return err;
        if (err != error.AnalysisBudgetExceeded) return err;
        const diagnostic = budget_mod.take();
        try cache.failRoot(fn_decl, diagnostic);
        try sink.append(cache.gpa, .{ .fn_decl = fn_decl, .budget = diagnostic });
        self.failed.set(@intFromEnum(fn_decl));
    }
};

/// Passes one transitive fixpoint phase needs to settle.  One more pass is
/// allowed past it, only to confirm that nothing moves any more.
const max_fixpoint_rounds: u32 = 16;

/// A fixpoint that still moves after `max_fixpoint_rounds` passes has not been
/// reached, and the summaries it was filling hold part of their fold.  That is
/// an exhausted budget, not a smaller answer.
fn fixpointUnsettled() budget_mod.BudgetError {
    return budget_mod.fail(.{
        .limit = .transitive_fixpoint_rounds,
        .limit_value = max_fixpoint_rounds,
        .reached = max_fixpoint_rounds,
    });
}

/// Raise again a failure a root recorded earlier.  A root that recorded
/// nothing raises the bare error, exactly as it did the first time.
fn reraiseRootFailure(recorded: ?budget_mod.Diagnostic) budget_mod.BudgetError {
    const diagnostic = recorded orelse return error.AnalysisBudgetExceeded;
    return budget_mod.fail(diagnostic);
}

const CleanupDemand = union(enum) {
    all,
    one: u32,
    many: []const u32,

    fn contains(self: CleanupDemand, parameter: u32) bool {
        return switch (self) {
            .all => true,
            .one => |selected| selected == parameter,
            .many => |selected| std.mem.indexOfScalar(u32, selected, parameter) != null,
        };
    }

    fn eql(a: CleanupDemand, b: CleanupDemand) bool {
        if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
        return switch (a) {
            .all => true,
            .one => |selected| selected == b.one,
            .many => |selected| std.mem.eql(u32, selected, b.many),
        };
    }
};

const CleanupKey = struct {
    declaration: DeclKey,
    context: TypeResolver.ActualTypeID,
    /// Recursive edges retain only the formals actually handed storage
    /// from the enclosing demand. A published MANY slice owns its indices.
    demand: CleanupDemand = .all,
};

const CleanupKeyContext = struct {
    pub fn hash(_: CleanupKeyContext, key: CleanupKey) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const tree = @intFromPtr(key.declaration.tree);
        hasher.update(std.mem.asBytes(&tree));
        hasher.update(std.mem.asBytes(&key.declaration.module));
        hasher.update(std.mem.asBytes(&key.declaration.declaration));
        const context = key.context.hash64();
        hasher.update(std.mem.asBytes(&context));
        const demand_tag = std.meta.activeTag(key.demand);
        hasher.update(std.mem.asBytes(&demand_tag));
        switch (key.demand) {
            .all => {},
            .one => |parameter| hasher.update(std.mem.asBytes(&parameter)),
            .many => |parameters| hasher.update(std.mem.sliceAsBytes(parameters)),
        }
        return hasher.final();
    }

    pub fn eql(_: CleanupKeyContext, a: CleanupKey, b: CleanupKey) bool {
        return a.declaration.tree == b.declaration.tree and
            a.declaration.module == b.declaration.module and
            a.declaration.declaration == b.declaration.declaration and
            a.context.eql(b.context) and CleanupDemand.eql(a.demand, b.demand);
    }
};

/// Root output proofs depend on the reached callee and the caller's actual
/// instantiation. Nested lexical snapshots are deliberately never memoized.
const ParameterWriteKey = struct {
    call_node: Ast.Node.Index,
    parameter_index: u32,
    callee_context: TypeResolver.ActualTypeID,
    caller_context: ?TypeResolver.ActualTypeID,
};

const ParameterWriteKeyContext = struct {
    pub fn hash(_: ParameterWriteKeyContext, key: ParameterWriteKey) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&key.call_node));
        hasher.update(std.mem.asBytes(&key.parameter_index));
        const callee = key.callee_context.hash64();
        hasher.update(std.mem.asBytes(&callee));
        const has_caller = key.caller_context != null;
        hasher.update(std.mem.asBytes(&has_caller));
        if (key.caller_context) |context| {
            const caller = context.hash64();
            hasher.update(std.mem.asBytes(&caller));
        }
        return hasher.final();
    }

    pub fn eql(_: ParameterWriteKeyContext, a: ParameterWriteKey, b: ParameterWriteKey) bool {
        if (a.call_node != b.call_node or a.parameter_index != b.parameter_index or
            !a.callee_context.eql(b.callee_context)) return false;
        if (a.caller_context) |context| return context.eql(b.caller_context orelse return false);
        return b.caller_context == null;
    }
};

const CleanupBudget = struct {
    queries: u32 = 0,
    depth: u32 = 0,
    remaining: u32 = 50_000,
    initiating_cache: ?*FileCache = null,
    initiating_node: ?Ast.Node.Index = null,
    initiating_tree: ?*const Ast = null,
};

/// AST snapshots outlive replay memo entries. Temporary caches and their
/// borrowed cleanup demands do not, so retain only the raw tree and node.
const ReplayFailureSite = struct {
    tree: *const Ast,
    node: Ast.Node.Index,
};

threadlocal var replay_failure_site: ?ReplayFailureSite = null;

const ReplayFailureKey = struct {
    callee: CleanupKey,
    remaining: u32,
    depth: u32,
};

const ReplayFailureKeyContext = struct {
    pub fn hash(_: ReplayFailureKeyContext, key: ReplayFailureKey) u64 {
        var hasher = std.hash.Wyhash.init(CleanupKeyContext.hash(.{}, key.callee));
        hasher.update(std.mem.asBytes(&key.remaining));
        hasher.update(std.mem.asBytes(&key.depth));
        return hasher.final();
    }

    pub fn eql(_: ReplayFailureKeyContext, a: ReplayFailureKey, b: ReplayFailureKey) bool {
        return a.remaining == b.remaining and a.depth == b.depth and
            CleanupKeyContext.eql(.{}, a.callee, b.callee);
    }
};

const ReplayFailure = struct {
    site: ReplayFailureSite,
    diagnostic: budget_mod.Diagnostic,
    remaining: u32,
    memo_entries: usize,
    exhausted_entries: usize,
};

// Every cache on one worker shares the outer semantic query's allowance,
// including caches opened for admitted foreign declarations.
threadlocal var cleanup_budget: CleanupBudget = .{};

// Temporary source-only witness. It observes the existing allowance without
// changing keys, admission, publication, or the error reported to callers.
const CleanupProbeDemand = struct {
    tag: std.meta.Tag(CleanupDemand),
    indices: [16]u32 = undefined,
    count: usize = 0,

    fn init(demand: CleanupDemand) CleanupProbeDemand {
        var result: CleanupProbeDemand = .{ .tag = std.meta.activeTag(demand) };
        switch (demand) {
            .all => {},
            .one => |index| {
                result.indices[0] = index;
                result.count = 1;
            },
            .many => |indices| {
                result.count = indices.len;
                const count = @min(indices.len, result.indices.len);
                @memcpy(result.indices[0..count], indices[0..count]);
            },
        }
        return result;
    }
};

const CleanupProbeKey = struct {
    declaration: DeclKey,
    context: TypeResolver.ActualTypeID,
    demand: CleanupProbeDemand,

    fn init(key: CleanupKey) CleanupProbeKey {
        return .{
            .declaration = key.declaration,
            .context = key.context,
            .demand = CleanupProbeDemand.init(key.demand),
        };
    }
};

const CleanupProbeOwner = struct {
    formal: u32,
    parameter: u32,
    argument: Ast.Node.Index,
    path: [64]u8 = undefined,
    path_len: usize,
    path_total: usize,

    fn init(formal: u32, argument: Ast.Node.Index, owner: fn_summary.ParamPath) CleanupProbeOwner {
        var result: CleanupProbeOwner = .{
            .formal = formal,
            .parameter = owner.param,
            .argument = argument,
            .path_len = @min(owner.path.len, 64),
            .path_total = owner.path.len,
        };
        @memcpy(result.path[0..result.path_len], owner.path[0..result.path_len]);
        return result;
    }
};

const CleanupProbeEdge = struct {
    key: CleanupProbeKey,
    declaring: ?*FileCache = null,
    kind: enum { call, argument_check, field_context },
    field: ?[]const u8 = null,
    owners: [16]CleanupProbeOwner = undefined,
    owner_count: usize = 0,
};

const CleanupProbeRow = struct {
    cache: *FileCache,
    tree: *const Ast,
    node: Ast.Node.Index,
    frame: ?TypeResolver.ResolutionFrame,
    demand: CleanupProbeDemand,
    edge: ?CleanupProbeEdge,
    cache_hits: u32 = 0,
    visiting_hits: u32 = 0,
    last_hit: ?CleanupProbeKey = null,
};

threadlocal var cleanup_probe_stack: [64]CleanupProbeRow = undefined;
threadlocal var cleanup_probe_edge: ?CleanupProbeEdge = null;
threadlocal var cleanup_probe_owners: [16]CleanupProbeOwner = undefined;
threadlocal var cleanup_probe_owner_count: usize = 0;
var cleanup_probe_dumped: std.atomic.Value(bool) = .init(false);

fn cleanupProbeHit(key: CleanupKey, visiting: bool) void {
    if (cleanup_budget.depth == 0) return;
    const row = &cleanup_probe_stack[cleanup_budget.depth - 1];
    if (visiting) row.visiting_hits +|= 1 else row.cache_hits +|= 1;
    row.last_hit = CleanupProbeKey.init(key);
}

fn cleanupProbeRow(cache: *FileCache, node: Ast.Node.Index) CleanupProbeRow {
    return .{
        .cache = cache,
        .tree = cache.tree,
        .node = node,
        .frame = cache.cleanup_frame,
        .demand = CleanupProbeDemand.init(cache.cleanup_demand),
        .edge = cleanup_probe_edge,
    };
}

fn cleanupProbeName(tree: *const Ast, declaration: Ast.Node.Index) []const u8 {
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return "?";
    return tree.tokenSlice(proto.name_token orelse return "?");
}

fn cleanupProbeFormalCount(tree: *const Ast, declaration: Ast.Node.Index) ?u32 {
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
    var parameters = proto.iterate(tree);
    for (0..65) |count| {
        if (parameters.next() == null) return @intCast(count);
    }
    return null;
}

fn cleanupProbeTarget(row: *const CleanupProbeRow) bool {
    const tree = row.tree;
    const declaration = row.cache.enclosingFunctionAt(tree, tree.nodeMainToken(row.node)) orelse return false;
    const name = cleanupProbeName(tree, declaration);
    // Names select diagnostic output only. They never select an analysis answer.
    return (std.mem.endsWith(u8, row.cache.file_path, "/grow_analysis.zig") and
        std.mem.eql(u8, name, "isStandardSliceComparison")) or
        (std.mem.endsWith(u8, row.cache.file_path, "/file_cache.zig") and
            std.mem.eql(u8, name, "importModel"));
}

fn cleanupProbePrintDemand(demand: *const CleanupProbeDemand) void {
    std.debug.print(" demand={s} selected={any} selected_total={d}", .{
        @tagName(demand.tag),
        demand.indices[0..@min(demand.count, demand.indices.len)],
        demand.count,
    });
}

fn cleanupProbePrintKey(label: []const u8, key: *const CleanupProbeKey) void {
    const tree = key.declaration.tree;
    const token = tree.nodeMainToken(key.declaration.declaration);
    const byte = tree.tokens.items(.start)[token];
    const lc = budget_mod.lineCol(tree.source, byte);
    const name = cleanupProbeName(tree, key.declaration.declaration);
    std.debug.print(" {s}_tree=0x{x} module={any} decl={d} name={s} decl_loc={d}:{d} context=0x{x} context_tag={s} formals={d}", .{
        label,                                                                              @intFromPtr(tree),           key.declaration.module,
        @intFromEnum(key.declaration.declaration),                                          name[0..@min(name.len, 64)], lc.line,
        lc.column,                                                                          key.context.hash64(),        @tagName(key.context.data),
        if (key.context.data == .function) key.context.data.function.parameters.len else 0,
    });
    cleanupProbePrintDemand(&key.demand);
    if (key.context.data == .function) {
        const parameters = key.context.data.function.parameters;
        for (parameters[0..@min(parameters.len, 16)], 0..) |parameter, index| {
            std.debug.print(" formal{d}_type=0x{x}:{s}", .{
                index, parameter.type.hash64(), @tagName(parameter.type.data),
            });
        }
    }
}

fn cleanupProbePrintRow(index: usize, row: *const CleanupProbeRow) void {
    const cache = row.cache;
    const tree = row.tree;
    const token = tree.nodeMainToken(row.node);
    const lc = budget_mod.lineCol(tree.source, tree.tokens.items(.start)[token]);
    const declaration = cache.enclosingFunctionAt(tree, token);
    const name = if (declaration) |decl| cleanupProbeName(tree, decl) else "?";
    std.debug.print("ZBC_CLEANUP_STACK row={d} cache=0x{x} tree=0x{x} module={any} path={s} node={d} tag={s} loc={d}:{d} caller_decl={any} caller={s} caller_context={?x} cache_hits={d} visiting_hits={d}", .{
        index,                                              @intFromPtr(cache),                                              @intFromPtr(tree),                cache.module_id,
        cache.file_path[0..@min(cache.file_path.len, 160)], @intFromEnum(row.node),                                          @tagName(tree.nodeTag(row.node)), lc.line,
        lc.column,                                          if (declaration) |decl| @as(?u32, @intFromEnum(decl)) else null, name[0..@min(name.len, 64)],      if (row.frame) |frame| if (frame.actual_type) |actual| @as(?u64, actual.hash64()) else null else null,
        row.cache_hits,                                     row.visiting_hits,
    });
    cleanupProbePrintDemand(&row.demand);
    std.debug.print(" caller_formals={any}", .{
        if (declaration) |decl| cleanupProbeFormalCount(tree, decl) else null,
    });
    if (row.frame) |frame| {
        if (frame.actual_type) |actual| {
            if (declaration) |decl| {
                const caller_key: CleanupProbeKey = .{
                    .declaration = .{ .tree = tree, .module = frame.handle.module, .declaration = decl },
                    .context = actual,
                    .demand = row.demand,
                };
                cleanupProbePrintKey("caller", &caller_key);
            }
        }
    }
    if (row.edge) |*edge| {
        std.debug.print(" edge={s} callee_cache={?x}", .{
            @tagName(edge.kind),
            if (edge.declaring) |declaring| @as(?usize, @intFromPtr(declaring)) else null,
        });
        if (edge.declaring) |declaring| {
            std.debug.print(" callee_path={s}", .{
                declaring.file_path[0..@min(declaring.file_path.len, 160)],
            });
        }
        if (edge.field) |field| {
            std.debug.print(" stored_field={s} stored_field_total={d}", .{
                field[0..@min(field.len, 64)], field.len,
            });
        }
        cleanupProbePrintKey("callee", &edge.key);
        // Equality is the engine's full identity equality, not hash equality.
        for (cleanup_probe_stack[0..@min(index, cleanup_budget.depth)], 0..) |*previous, previous_index| {
            const b = edge.key;
            if (previous.edge) |previous_edge| {
                const a = previous_edge.key;
                if (a.declaration.tree == b.declaration.tree and
                    a.declaration.module == b.declaration.module and
                    a.declaration.declaration == b.declaration.declaration)
                {
                    std.debug.print(" same_decl_edge_row={d} context_equal={} prior_demand={s}", .{
                        previous_index, a.context.eql(b.context), @tagName(a.demand.tag),
                    });
                }
            }
            if (previous.frame) |frame| {
                if (frame.actual_type) |actual| {
                    const previous_decl = previous.cache.enclosingFunctionAt(
                        previous.tree,
                        previous.tree.nodeMainToken(previous.node),
                    );
                    if (previous.tree == b.declaration.tree and
                        frame.handle.module == b.declaration.module and
                        previous_decl == b.declaration.declaration)
                    {
                        std.debug.print(" same_decl_caller_row={d} context_equal={} prior_demand={s}", .{
                            previous_index, actual.eql(b.context), @tagName(previous.demand.tag),
                        });
                    }
                }
            }
        }
        std.debug.print(" owners_total={d}\n", .{edge.owner_count});
        for (edge.owners[0..@min(edge.owner_count, edge.owners.len)]) |*owner| {
            std.debug.print("ZBC_CLEANUP_STACK owner row={d} formal={d} caller_parameter={d} argument={d} path={s} path_total={d}\n", .{
                index,                         owner.formal,     owner.parameter, @intFromEnum(owner.argument),
                owner.path[0..owner.path_len], owner.path_total,
            });
        }
    } else std.debug.print("\n", .{});
    if (row.last_hit) |*hit| {
        std.debug.print("ZBC_CLEANUP_STACK last_hit row={d}", .{index});
        cleanupProbePrintKey("hit", hit);
        std.debug.print("\n", .{});
    }
}

fn cleanupProbeFailure(cache: *FileCache, tree: *const Ast, node: Ast.Node.Index, limit: budget_mod.Limit) void {
    if (cleanup_probe_dumped.load(.monotonic)) return;
    var failed = cleanupProbeRow(cache, node);
    failed.tree = tree;
    var targeted = cleanupProbeTarget(&failed);
    for (cleanup_probe_stack[0..cleanup_budget.depth]) |*row| {
        targeted = targeted or cleanupProbeTarget(row);
    }
    if (!targeted) return;
    if (cleanup_probe_dumped.swap(true, .monotonic)) return;
    std.debug.print("ZBC_CLEANUP_STACK first_failure limit={s} depth={d} remaining={d} rows_cap=64 indices_cap=16 path_cap=64\n", .{
        @tagName(limit), cleanup_budget.depth, cleanup_budget.remaining,
    });
    for (cleanup_probe_stack[0..cleanup_budget.depth], 0..) |*row, index| {
        cleanupProbePrintRow(index, row);
    }
    std.debug.print("ZBC_CLEANUP_STACK rejected_edge\n", .{});
    cleanupProbePrintRow(cleanup_budget.depth, &failed);
}

pub const FileCache = struct {
    gpa: std.mem.Allocator,
    tree: *const Ast,
    /// Arena for FnSummary variable-length fields and nested strings.
    /// Local summaries and owned foreign-summary copies live here; lazy
    /// until the first summary needs it.
    summary_arena: ?std.heap.ArenaAllocator = null,
    file_model: ?file_model.FileModel = null,
    bindings: std.AutoHashMapUnmanaged(u32, local_bindings.LocalBindings) = .empty,
    summaries: std.AutoHashMapUnmanaged(u32, fn_summary.FnSummary) = .empty,
    /// Set when `resolveTransitiveTakes` ran every phase.  Roots it gave up on
    /// are listed in `failed_roots`; they stay failed, so the pass is final.
    transitive_resolved: bool = false,
    /// Roots whose summary fold gave up on a budget, keyed by body node like
    /// `summaries`, each with the failure it recorded.  A failed root has no
    /// summary: a lookup raises the recorded failure instead of recomputing
    /// the body-only answer and presenting it as the finished one.
    failed_roots: std.AutoHashMapUnmanaged(u32, ?budget_mod.Diagnostic) = .empty,
    /// Bodies being inferred. A recursive edge reads only the conservative
    /// cheap entry and cannot turn an unfinished cleanup walk into a proof.
    summary_visiting: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Declaration facts do not force a normal/error cleanup graph walk.
    resolved_declarations: std.HashMapUnmanaged(CleanupKey, fn_summary.FnSummary, CleanupKeyContext, 80) = .empty,
    resolved_declaration_visiting: std.HashMapUnmanaged(CleanupKey, void, CleanupKeyContext, 80) = .empty,
    /// Contextual outcomes use the complete instantiated callee identity.
    cleanup_summaries: std.HashMapUnmanaged(CleanupKey, fn_summary.FnSummary, CleanupKeyContext, 80) = .empty,
    cleanup_visiting: std.HashMapUnmanaged(CleanupKey, void, CleanupKeyContext, 80) = .empty,
    /// Successful scalar receiver footprints, keyed by full instantiated
    /// declaration identity and selected formal. Abstentions are not cached.
    method_scalar_reads: std.HashMapUnmanaged(CleanupKey, []const []const u8, CleanupKeyContext, 80) = .empty,
    method_scalar_reads_visiting: std.HashMapUnmanaged(CleanupKey, void, CleanupKeyContext, 80) = .empty,
    /// Diagnostic-only unproved positive writes; null means unrestricted reach.
    diagnostic_output_touches: std.HashMapUnmanaged(CleanupKey, ?[]const []const u8, CleanupKeyContext, 80) = .empty,
    diagnostic_output_touches_visiting: std.HashMapUnmanaged(CleanupKey, void, CleanupKeyContext, 80) = .empty,
    store_value_visiting: std.HashMapUnmanaged(CleanupKey, void, CleanupKeyContext, 80) = .empty,
    cleanup_frame: ?TypeResolver.ResolutionFrame = null,
    /// Complete source-defined return values, under defined runtime formals.
    /// Actual type identity separates generic instantiations; a declaration
    /// already on the stack cannot publish a recursive certificate.
    return_defined_summaries: std.HashMapUnmanaged(CleanupKey, ReturnValueVerdict, CleanupKeyContext, 80) = .empty,
    /// Caller-selected negative facts, never strict return certificates.
    diagnostic_return_summaries: std.HashMapUnmanaged(ReturnCallKey, ReturnValueVerdict, ReturnCallKeyContext, 80) = .empty,
    /// Borrowed only while lowering a caller-selected diagnostic replay.
    diagnostic_actual_integers: []const DiagnosticIntegerBinding = &.{},
    return_defined_visiting: std.AutoHashMapUnmanaged(DeclKey, void) = .empty,
    /// Failed standalone replays, never verdicts. Exact initial allowances
    /// and unchanged memo state are required; active outer proofs do not reuse.
    return_replay_failures: std.HashMapUnmanaged(ReplayFailureKey, ReplayFailure, ReplayFailureKeyContext, 80) = .empty,
    return_replay_syntax: std.AutoHashMapUnmanaged(DeclKey, ReturnReplaySyntax) = .empty,
    /// Completed identity queries, without argument or cleanup summaries.
    return_calls: std.HashMapUnmanaged(ReturnCallKey, ?ActualCallSummary, ReturnCallKeyContext, 80) = .empty,
    /// Eligibility is not a verdict. A later settled replay takes precedence.
    return_diagnostic_seeds: std.HashMapUnmanaged(CleanupKey, bool, CleanupKeyContext, 80) = .empty,
    return_source_eligibility: std.HashMapUnmanaged(ReturnSourceKey, SourceEligibility, ReturnSourceKeyContext, 80) = .empty,
    return_source_visiting: std.HashMapUnmanaged(ReturnSourceKey, void, ReturnSourceKeyContext, 80) = .empty,
    return_defined_mode: bool = false,
    array_source_visiting: std.AutoHashMapUnmanaged(DeclKey, void) = .empty,
    cleanup_demand: CleanupDemand = .all,
    /// Nested foreign walks publish contextual memo entries on the original
    /// caller, whose resolver owns the complete instantiated identity.
    cleanup_origin: ?*FileCache = null,
    /// Syntactic writes are context-independent and indexed once per body.
    retained_writes: std.AutoHashMapUnmanaged(u32, []const fn_summary.ParamPath) = .empty,
    /// Optional ZLS-backed type resolver.  When set, type-shaped
    /// questions (param container name, field type) prefer ZLS over
    /// the token-walk fallback — handles cross-module types, generic
    /// instantiations, and pointer/optional chains uniformly instead
    /// of via fragile token-pattern proxies.
    zls: ?*zls_resolver_mod.TypeResolver = null,
    /// Optional ProjectCache for cross-file lookups through imports
    /// permitted by its SourcePolicy. Exact root const bindings select
    /// the module or imported type; the cache loads those models lazily.
    project: ?*project_cache_mod.ProjectCache = null,
    /// Absolute path of the file this cache analyses. Used as the source
    /// path for import resolution. An empty path disables cross-file lookup.
    file_path: []const u8 = "",
    /// Metadata-only extent queries, including unsupported or inaccessible
    /// literals. Each AST node is queried once for this immutable sweep.
    embedded_file_lengths: std.AutoHashMapUnmanaged(Ast.Node.Index, ?u64) = .empty,
    /// Result cache for cross-file method lookups. Key = gpa-owned
    /// `"type-path\x00method-name"`; null means searched, not found.
    /// The full type path keeps same-named types in separate imports
    /// distinct and avoids repeating a per-file import walk.
    method_lookup_cache: std.StringHashMapUnmanaged(?ResolvedMethod) = .empty,
    /// Receiver-field writes and releases of imported methods, keyed by
    /// the same exact type path and method name. Nested path text lives in
    /// `summary_arena`, so by-value summaries outlive the foreign tree.
    cross_file_fields: std.StringHashMapUnmanaged(fn_summary.FieldEffects) = .empty,
    /// Completed cross-file method answers, keyed only after import admission.
    /// Scalar facts are copied; field paths borrow this cache's summary arena.
    foreign_method_summaries: std.AutoHashMapUnmanaged(ForeignBodyKey, fn_summary.FnSummary) = .empty,
    /// Completed same-file ownership folds, including null answers. One foreign
    /// fold publishes every body it resolved, without retaining its FileCache.
    foreign_takes: std.AutoHashMapUnmanaged(ForeignBodyKey, ?u32) = .empty,
    /// The file-level `const` declarations, keyed by the name each one
    /// owns.  Lazy: built on the first `fileConstInitializer` call and
    /// reused for the rest of this file's analysis.  Keys borrow the
    /// source, which outlives the cache.
    root_consts: ?std.StringHashMapUnmanaged(?Ast.Node.Index) = null,
    /// Lazily-built sorted table of byte offsets where each source line
    /// starts.  Shared across all function analyses in this file so
    /// cfg_builder's buildLineOffsets() runs at most once per file.
    line_offsets: []const u32 = &.{},

    /// The module this document's own names are written in.  It is set
    /// when the document is opened, because a document is opened in the
    /// module that DECLARED it — that module, not the reader's, is what
    /// its names mean — and it is part of the key of every
    /// declaration-scoped memo below.
    module_id: ModuleId = .unscoped,
    /// The one grow fold this root cache shares with every source
    /// document it opens.  Sharing it is what lets a cycle that crosses
    /// documents be recognised: each end asks the same set what is
    /// being computed right now, instead of opening a second analysis of
    /// a file that is already on the stack.  Null until the first grow
    /// question is asked; the ROOT cache owns the one instance and hands
    /// it to every document it opens.
    grow_state: ?*grow_analysis_mod.GrowState = null,
    /// True for a document opened to answer a demand query, false for
    /// the file under analysis.  A cache with its own Phase 8 loop reads
    /// live summaries on purpose and converges on them itself, so folding
    /// a declaration underneath it would answer a question it is already
    /// asking.
    grow_on_demand: bool = false,
    /// Resolved callee identity, one entry per callee token, published
    /// only by a resolution that ran to the end.  A contextual (frame)
    /// query never publishes here: its answer belongs to the frame it
    /// was asked in, not to this document's token-only context.
    actual_callees: std.AutoHashMapUnmanaged(Ast.TokenIndex, ?ActualCallee) = .empty,
    /// Preservation is conditional on caller-owned definedness facts, never
    /// an initialization certificate. Failed queries remain retryable.
    preserving_writes: std.HashMapUnmanaged(
        PreservingCallKey,
        ?PreservingCallWrite,
        PreservingCallKeyContext,
        80,
    ) = .empty,
    preserving_visiting: std.HashMapUnmanaged(
        PreservingCallKey,
        void,
        PreservingCallKeyContext,
        80,
    ) = .empty,
    /// Completed actual-context source event plans share traversal only.
    /// Formal/path effect witnesses remain scoped to their semantic queries.
    /// Owned event/use buffers borrow this immutable snapshot and the original
    /// resolver's identity arena; cache teardown precedes resolver teardown.
    effect_source_plans: std.HashMapUnmanaged(
        call_summary_mod.SourcePlanKey,
        call_summary_mod.SourcePlan,
        call_summary_mod.SourcePlanKeyContext,
        80,
    ) = .empty,
    /// Complete binding-qualified write syntax per immutable body. Actual
    /// context and formal/path affect origin answers, not this source index.
    effect_binding_writes: std.AutoHashMapUnmanaged(u32, call_summary_mod.BindingWriteIndex) = .empty,
    /// Direct grow effects per body, computed once and reused by every
    /// round that folds it.  The canonical collector reads only the
    /// immutable AST, the proto, the body and the bindings — never a
    /// callee's summary — so the answer cannot change between rounds.
    direct_effects: std.AutoHashMapUnmanaged(u32, fn_summary.GrowEffects) = .empty,
    /// Fresh-storage verdicts, keyed by the claim together with the
    /// complete instantiated identity it was asked in.
    fresh_storage: std.HashMapUnmanaged(fresh_storage_mod.FreshKey, bool, fresh_storage_mod.FreshKeyContext, 80) = .empty,
    /// Declarations whose fresh-storage walk is running right now.
    /// Meeting one again is a cycle, and a cycle proves nothing.
    fresh_visiting: std.AutoHashMapUnmanaged(DeclKey, void) = .empty,
    /// Storage-alias syntax indexes and completed answers for this tree.
    alias_state: storage_alias_mod.FileState = .{},
    /// Returned-storage summaries share the grow owner's canonical resolver
    /// identities. Only that owner's state is queried; paths live until deinit.
    return_storage_state: return_storage_mod.State = .{},
    /// Completed call-effect witness sets for this root, shared by every
    /// root `callEffectAt` of one file analysis. Only the root cache owns it;
    /// documents opened for demand queries reach it through `grow_state`.
    effects_state: call_summary_mod.State = .{},
    /// Parameters this file proved cannot carry an address, keyed by
    /// `(fn_token, parameter)`.  Both answers are kept — a parameter
    /// that is a narrow scalar and one that is not are both complete
    /// readings — and only a question that RAN TO THE END is filed.
    scalar_params: std.AutoHashMapUnmanaged(u64, bool) = .empty,
    /// This toolchain's own `std/array_list.zig`, or the record that this
    /// session has no toolchain to read.  Cached so the answer is sought
    /// once per file rather than once per claim.
    std_list_tree: StdListTree = .unknown,
    /// Every call node in this file, keyed by the token naming its
    /// callee.  Built once; shared by every question that must know
    /// whether a token has a call behind it at all.
    call_index: ?*CallIndex = null,
    /// The calls whose callee this file's OWN declarations resolve to,
    /// per enclosing declaration.  Memoised per declaration so a helper
    /// consulted from several sites is resolved once.
    closed_local_calls: std.AutoHashMapUnmanaged(Ast.Node.Index, ?[]Ast.Node.Index) = .empty,
    /// Every syntactic use of an identifier token, per token.  A
    /// question that must know every place a name is REFERENCED cannot
    /// ask the resolver for it: the resolver answers about values, and a
    /// reference can be one without ever being called directly.
    syntax_uses: std.AutoHashMapUnmanaged(Ast.TokenIndex, []SyntaxUse) = .empty,
    /// The escape index of each fn body: which roots this body takes the
    /// address of, and what it writes to which name.  Built once per body
    /// and owned for the snapshot's lifetime, so every walk of that body
    /// — the first and every child query — reads one table.
    escape_roots: std.AutoHashMapUnmanaged(u32, *EscapeRootIndex) = .empty,
    /// Every `&` operand in this file, keyed by the token naming the
    /// root it addresses.  Lazy: one whole-file pass answers every
    /// body's question about every token, so a body walked repeatedly
    /// reads a table instead of re-walking the file's node array.
    address_uses: ?AddressUseMap = null,
    /// Completed in-place address proofs also invalidate failed replay stamps.
    address_proof_generation: usize = 0,
    /// Successful root certificates only; failures and abstentions are retried.
    definite_parameter_writes: std.HashMapUnmanaged(ParameterWriteKey, void, ParameterWriteKeyContext, 80) = .empty,
    /// `(first << 32) | last` → lowest node with exactly that token span.
    /// Built on the first `nodeForExactSpan` question; null until then.
    exact_spans: ?std.AutoHashMapUnmanaged(u64, Ast.Node.Index) = null,
    /// Tree-only fill scope material and exact visibility queries, shared by
    /// ordinary lowering and return replay. No type/value certificate.
    fill_lexical_index: comptime_fill_mod.LexicalIndex = .{},

    const ForeignBodyKey = struct {
        tree: *const Ast,
        module: ModuleId,
        body: u32,
    };

    const ReturnCallKey = struct {
        token: Ast.TokenIndex,
        resolver: *TypeResolver,
        tree: *const Ast,
        module: ModuleId,
        callable: ?TypeResolver.ActualTypeID,
        container: ?TypeResolver.ActualTypeID,
    };

    const ReturnCallKeyContext = struct {
        pub fn hash(_: ReturnCallKeyContext, key: ReturnCallKey) u64 {
            var hasher = std.hash.Wyhash.init(0);
            hasher.update(std.mem.asBytes(&key.token));
            const resolver = @intFromPtr(key.resolver);
            const tree = @intFromPtr(key.tree);
            hasher.update(std.mem.asBytes(&resolver));
            hasher.update(std.mem.asBytes(&tree));
            hasher.update(std.mem.asBytes(&key.module));
            // Syntax distributes node queries without recursively hashing
            // their entire generic binding closure. Context collisions still
            // require full structural equality below; no key loses a field.
            inline for (.{ key.callable, key.container }) |context| {
                const present = context != null;
                hasher.update(std.mem.asBytes(&present));
            }
            return hasher.final();
        }

        pub fn eql(_: ReturnCallKeyContext, a: ReturnCallKey, b: ReturnCallKey) bool {
            if (a.token != b.token or a.resolver != b.resolver or
                a.tree != b.tree or a.module != b.module) return false;
            if (a.callable) |context| {
                if (!context.eql(b.callable orelse return false)) return false;
            } else if (b.callable != null) return false;
            if (a.container) |context| {
                if (!context.eql(b.container orelse return false)) return false;
            } else if (b.container != null) return false;
            return true;
        }
    };

    const ReturnValueVerdict = struct {
        defined: bool,
        may_undefined: bool,
        all_undefined: bool,
        stores: std.ArrayListUnmanaged(worklist_mod.UndefinedParameterStore) = .empty,
        bytes: std.ArrayListUnmanaged(worklist_mod.UndefinedReturnBytes) = .empty,
    };

    pub const DiagnosticIntegerBinding = struct {
        parameter_byte: u32,
        value: u64,
    };

    const DiagnosticReplay = struct {
        key: ReturnCallKey,
        integers: []const DiagnosticIntegerBinding,
    };

    const ReturnReplaySyntax = struct {
        has_defer: bool = false,
    };

    /// A source is only permission to ask the settled replay, never a mask.
    /// Cycle-dependent absences are not published as completed answers.
    const SourceEligibility = enum {
        absent,
        present,
        cycle,

        fn merge(a: SourceEligibility, b: SourceEligibility) SourceEligibility {
            if (a == .present or b == .present) return .present;
            if (a == .cycle or b == .cycle) return .cycle;
            return .absent;
        }
    };

    const ReturnSourceKey = struct {
        frame: ReturnCallKey,
        node: Ast.Node.Index,
        returns: bool,
        stores: bool = false,
        mutation_root: ?Ast.Node.Index = null,
    };

    const ReturnSourceKeyContext = struct {
        pub fn hash(_: ReturnSourceKeyContext, key: ReturnSourceKey) u64 {
            var hasher = std.hash.Wyhash.init((ReturnCallKeyContext{}).hash(key.frame));
            hasher.update(std.mem.asBytes(&key.node));
            hasher.update(std.mem.asBytes(&key.returns));
            hasher.update(std.mem.asBytes(&key.stores));
            const rooted = key.mutation_root != null;
            hasher.update(std.mem.asBytes(&rooted));
            if (key.mutation_root) |root| hasher.update(std.mem.asBytes(&root));
            return hasher.final();
        }

        pub fn eql(_: ReturnSourceKeyContext, a: ReturnSourceKey, b: ReturnSourceKey) bool {
            return a.node == b.node and a.returns == b.returns and a.stores == b.stores and
                a.mutation_root == b.mutation_root and (ReturnCallKeyContext{}).eql(a.frame, b.frame);
        }
    };

    pub fn init(gpa: std.mem.Allocator, tree: *const Ast) FileCache {
        return .{ .gpa = gpa, .tree = tree };
    }

    fn enclosingFunctionAt(self: *FileCache, tree: *const Ast, token: Ast.TokenIndex) ?Ast.Node.Index {
        if (tree == self.tree) {
            if (self.zls) |resolver| {
                return resolver.enclosingFunctionAt(token) catch tokens.enclosingFnDecl(tree, token);
            }
        }
        return tokens.enclosingFnDecl(tree, token);
    }

    /// Bind the resolver for this cache's exact source document and module.
    /// Bind before semantic queries. A cache already assigned to a module
    /// cannot be rebound to another instance of the same physical source.
    /// Detaching the resolver does not change the document's identity.
    pub fn setZls(self: *FileCache, zls: ?*zls_resolver_mod.TypeResolver) void {
        if (zls) |resolver| {
            std.debug.assert(self.tree == &resolver.handle.document.tree);
            std.debug.assert(self.module_id == .unscoped or self.module_id == resolver.handle.module);
            self.module_id = resolver.handle.module;
        }
        self.zls = zls;
    }

    /// Byte count of an exact relative literal @embedFile, without reading
    /// its contents or borrowing a named module's source document. Unsupported
    /// shapes and policy refusals are unknown; I/O errors propagate uncached.
    pub fn embeddedFileLength(self: *FileCache, node: Ast.Node.Index) engine.SourceLoadError!?u64 {
        if (self.embedded_file_lengths.get(node)) |length| return length;
        const length = try self.readEmbeddedFileLength(node);
        try self.embedded_file_lengths.put(self.gpa, node, length);
        return length;
    }

    fn readEmbeddedFileLength(self: *FileCache, node: Ast.Node.Index) engine.SourceLoadError!?u64 {
        const resolver = self.zls orelse return null;
        // Only this cache's defining source selects the directory. A resolver
        // handle or a module root may describe a different source document.
        if (!std.fs.path.isAbsolute(self.file_path)) return null;
        const directory = std.fs.path.dirname(self.file_path) orelse return null;
        var buffer: [2]Ast.Node.Index = undefined;
        const args = self.tree.builtinCallParams(&buffer, node) orelse return null;
        if (args.len != 1 or !std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(node)), "@embedFile"))
            return null;
        if (self.tree.nodeTag(args[0]) != .string_literal) return null;
        const literal = std.zig.string_literal.parseAlloc(self.gpa, self.tree.tokenSlice(self.tree.nodeMainToken(args[0]))) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InvalidLiteral => return null,
        };
        defer self.gpa.free(literal);
        if (literal.len == 0 or std.fs.path.isAbsolute(literal) or std.mem.indexOfScalar(u8, literal, 0) != null)
            return null;
        // Join only: folding link/.. before the OS resolves it selects a
        // different file and can incorrectly bring it inside the policy.
        const joined = try std.fs.path.join(self.gpa, &.{ directory, literal });
        defer self.gpa.free(joined);
        const store = &resolver.ctx.store;
        // Reject lexical exclusions before resolving any path. "." and ".."
        // are traversal syntax, not dot-prefixed directories; leave their
        // meaning to the OS and admit roots only by the canonical target.
        if (store.source_policy.excludesPath(joined)) return null;
        var components = std.mem.tokenizeAny(u8, literal, "/\\");
        while (components.next()) |component| {
            if (std.mem.eql(u8, component, ".") or std.mem.eql(u8, component, "..")) continue;
            if (store.source_policy.excludesPath(component)) return null;
        }
        const canonical = try store.canonical_paths.resolve(store.allocator, store.io, joined);
        if (!store.source_policy.allowsAbsolutePath(canonical)) return null;
        const file = try std.Io.Dir.cwd().openFile(store.io, canonical, .{ .path_only = true });
        defer file.close(store.io);
        const stat = try file.stat(store.io);
        return if (stat.kind == .file) stat.size else null;
    }

    /// Compile-time element count of `node`'s type when it resolves to a
    /// fixed-size array `[N]T` (or single-pointer to one).  Returns null when
    /// the type engine is unavailable (token-only mode) or the type is a
    /// runtime slice / non-array.  A non-null result is an exact, compiler-
    /// guaranteed bound — safe to use for slice in-bounds reasoning.
    pub fn fixedArrayLenOf(self: *FileCache, node: std.zig.Ast.Node.Index) ?u64 {
        const z = self.zls orelse return null;
        return z.fixedArrayLen(node) catch null;
    }

    /// Comptime-known non-negative value of `node`, or null when not
    /// comptime-resolvable / engine unavailable.  A comptime index can't cause a
    /// runtime underflow/OOB (it would be a compile error), so a non-null result
    /// means the access is comptime-verified safe.
    pub fn comptimeIntValueOf(self: *FileCache, node: std.zig.Ast.Node.Index) ?u64 {
        const z = self.zls orelse return null;
        return z.comptimeIntValue(node) catch null;
    }

    /// For a type-name reference node `T`: whether `T` denotes a pointer/
    /// optional type (true), a value type (false), or couldn't resolve (null).
    /// Null when the type engine is unavailable.
    pub fn typeRefIsPointerLike(self: *FileCache, node: std.zig.Ast.Node.Index) ?bool {
        const z = self.zls orelse return null;
        return z.typeRefIsPointerLike(node) catch null;
    }

    /// Signedness + bit-width of `node`'s integer type, or null when the type
    /// engine is unavailable / the type isn't an integer.
    pub fn intInfoOf(self: *FileCache, node: std.zig.Ast.Node.Index) ?zls_resolver_mod.TypeResolver.IntInfo {
        const z = self.zls orelse return null;
        return z.intInfo(node) catch null;
    }

    /// `intInfoOf` for a node whose type is `?T`: the payload integer a cast
    /// into it produces.  Null when the type engine is unavailable, the type
    /// is not an optional, or its payload is not an integer.
    pub fn optionalPayloadIntInfoOf(self: *FileCache, node: std.zig.Ast.Node.Index) ?zls_resolver_mod.TypeResolver.IntInfo {
        const z = self.zls orelse return null;
        return z.optionalPayloadIntInfo(node) catch null;
    }

    /// Whether `node`'s type resolves to a floating-point type, or
    /// null when the type engine is unavailable or did not resolve the
    /// type at all — an unresolved type is not a proved non-`float`.
    /// Floats are not containers, so `typeNameOfNode` can't report them
    /// — use this instead.
    pub fn isFloatType(self: *FileCache, node: std.zig.Ast.Node.Index) ?bool {
        const z = self.zls orelse return null;
        return z.isFloatType(node) catch null;
    }

    /// For `x.ptr` (x a slice): whether x's element is byte-sized (align 1) —
    /// true=byte slice, false=wider element, null=unresolved/unknown.  Null
    /// when the type engine is unavailable.
    pub fn sourcePtrElemByteSized(self: *FileCache, node: std.zig.Ast.Node.Index) ?bool {
        const z = self.zls orelse return null;
        return z.sourcePtrElemByteSized(node) catch null;
    }

    /// Container type name of `node`'s resolved type (pointer/optional/array
    /// unwrapped), e.g. "Allocator" for a `std.mem.Allocator` value, or null
    /// when the type engine is unavailable / the type doesn't resolve.
    pub fn typeNameOfNode(self: *FileCache, node: std.zig.Ast.Node.Index) ?[]const u8 {
        const z = self.zls orelse return null;
        return z.typeNameOfNode(node) catch null;
    }
    /// The value the file-level `const name` was written with, or null
    /// when the file declares no such name, when that declaration has
    /// no initializer, or when the name is declared TWICE — neither
    /// declaration is then a proof, so the name is dropped rather than
    /// answered with the first one found.
    ///
    /// Building the table can fail, and a table that cannot be built is
    /// an incomplete file rather than a file with no constants in it,
    /// so that is an error and not an answer.
    pub fn fileConstInitializer(self: *FileCache, name: []const u8) !?Ast.Node.Index {
        const entry = (try self.rootConsts()).get(name) orelse return null;
        return entry;
    }

    /// The file-level `const` declarations, built once per file.
    fn rootConsts(self: *FileCache) !*const std.StringHashMapUnmanaged(?Ast.Node.Index) {
        if (self.root_consts == null) {
            var table: std.StringHashMapUnmanaged(?Ast.Node.Index) = .{};
            errdefer table.deinit(self.gpa);
            for (self.tree.rootDecls()) |node| {
                const decl = self.tree.fullVarDecl(node) orelse continue;
                if (self.tree.tokenTag(decl.ast.mut_token) != .keyword_const) continue;
                const gop = try table.getOrPut(self.gpa, self.tree.tokenSlice(decl.ast.mut_token + 1));
                // A name declared twice is dropped, and stays dropped:
                // a third declaration cannot make either of the first
                // two a proof.  A `const X: T;` with no initializer is
                // a declaration too — it binds the name without
                // declaring a value this file can read — so it is
                // recorded as null rather than skipped, and a later
                // declaration of the same name finds it already taken
                // instead of answering in its place.
                gop.value_ptr.* = if (gop.found_existing) null else decl.ast.init_node.unwrap();
            }
            self.root_consts = table;
        }
        return &self.root_consts.?;
    }

    pub fn setProject(
        self: *FileCache,
        project: ?*project_cache_mod.ProjectCache,
        file_path: []const u8,
    ) void {
        self.project = project;
        self.file_path = file_path;
    }

    /// Resolve a local type or a type reached through an exact root const
    /// binding. Bare imported types require a const that selects the type;
    /// module imports require their qualified alias path.
    pub fn findTypeAcrossImports(
        self: *FileCache,
        name: []const u8,
    ) ?*const file_model.TypeInfo {
        return if (self.resolvedTypeAcrossImports(name)) |resolved| resolved.info else null;
    }

    /// Resolve a type and retain its owning model and source path. Qualified
    /// paths start with the exact root const that binds their import. Bare
    /// imported names resolve only through a const that explicitly selects
    /// a type.
    pub fn resolvedTypeAcrossImports(
        self: *FileCache,
        name: []const u8,
    ) ?ResolvedType {
        const model = self.fileModel() catch return null;
        if (findTypeInModelPath(model, name)) |ti| {
            return .{ .model = model, .info = ti, .path = self.file_path, .module = self.module_id };
        }
        const pc = self.project orelse return null;
        if (self.file_path.len == 0) return null;
        return resolvedTypeViaImports(pc, self.tree, self.file_path, name, 4, self.module_id);
    }

    /// Resolve an imported type from exact alias and type segments. A single
    /// segment is accepted only when a root const of that name selects a type.
    pub fn importedTypeAcrossImports(
        self: *FileCache,
        segments: []const []const u8,
    ) ?ResolvedType {
        const pc = self.project orelse return null;
        if (self.file_path.len == 0) return null;
        return resolvedTypePathViaImports(
            pc,
            self.tree,
            self.file_path,
            segments,
            4,
            self.module_id,
        );
    }

    /// Resolve a local nested type path or an exact import-alias path.
    pub fn resolvedTypePathAcrossImports(
        self: *FileCache,
        name: []const u8,
    ) ?ResolvedType {
        return self.resolvedTypeAcrossImports(name);
    }

    /// Resolve a dotted path in the declaration scope of `owner`. Local
    /// nested declarations win; imports use that document's root bindings.
    pub fn typePathInOwnerScope(
        self: *FileCache,
        owner: ResolvedType,
        name: []const u8,
    ) ?ResolvedType {
        var segments: [max_type_path_segments][]const u8 = undefined;
        const count = splitTypePath(&segments, name);
        if (count == 0) return null;
        if (owner.model.findTypeInScope(segments[0], owner.info)) |info| {
            return walkTypePath(.{
                .model = owner.model,
                .info = info,
                .path = owner.path,
                .module = owner.module,
            }, segments[1..count]);
        }
        const pc = self.project orelse return null;
        if (owner.path.len == 0) return null;
        return resolvedTypePathViaImports(pc, owner.model.tree, owner.path, segments[0..count], 4, owner.module);
    }

    /// Resolve a type in the lexical scope that declared `owner`, then
    /// through that document's exact root import bindings.
    pub fn typeInOwnerScope(
        self: *FileCache,
        owner: ResolvedType,
        name: []const u8,
    ) ?ResolvedType {
        if (owner.model.findTypeInScope(name, owner.info)) |found| {
            return .{ .model = owner.model, .info = found, .path = owner.path, .module = owner.module };
        }
        return self.findTypeAcrossImportsFrom(owner, name);
    }

    /// Resolve the type declared by a field in its owner's lexical scope.
    pub fn fieldType(
        self: *FileCache,
        owner: ResolvedType,
        field_name: []const u8,
    ) ?ResolvedType {
        const found = owner.model.fieldType(owner.info.qualified_name, field_name) orelse return null;
        if (owner.model.findTypeInScope(found, owner.info)) |info| {
            return .{ .model = owner.model, .info = info, .path = owner.path, .module = owner.module };
        }
        return self.findTypeAcrossImportsFrom(owner, found);
    }

    /// Resolve a name in the file and lexical scope that own `owner`.
    fn findTypeAcrossImportsFrom(self: *FileCache, owner: ResolvedType, name: []const u8) ?ResolvedType {
        var segments: [max_type_path_segments][]const u8 = undefined;
        const count = splitTypePath(&segments, name);
        if (count == 0) return null;
        if (count == 1) {
            if (owner.model.findTypeInScope(segments[0], owner.info)) |info| {
                return .{ .model = owner.model, .info = info, .path = owner.path, .module = owner.module };
            }
        }
        if (findTypeInModelPath(owner.model, name)) |info| {
            return .{ .model = owner.model, .info = info, .path = owner.path, .module = owner.module };
        }
        const pc = self.project orelse return null;
        if (owner.path.len == 0) return null;
        return resolvedTypeViaImports(pc, owner.model.tree, owner.path, name, 4, owner.module);
    }

    /// Resolved cross-file method lookup result. When foreign, both fields
    /// borrow the model and tree owned by this FileCache's ProjectCache;
    /// keep that cache alive while using them. Local results borrow this
    /// FileCache's tree and model.
    pub const ResolvedMethod = struct {
        tree: *const Ast,
        method: *const file_model.MethodInfo,
    };

    /// The declaration a call's callee expression REACHES: the call node
    /// itself, the tree and `fn` token of the declaration it names, the
    /// document handle that declaration was read through, the
    /// declaration node itself, and the complete instantiated reference
    /// the engine resolved — which is what distinguishes two
    /// instantiations of one generic declaration.
    ///
    /// `caller_frame` is the contextual view the CALL was reached in.
    /// It is not the frame the callee's own body is read in: the
    /// bindings a caller instantiates are the ones its own arguments
    /// were resolved against.
    pub const ActualCallee = struct {
        call_node: Ast.Node.Index,
        tree: *const Ast,
        fn_token: Ast.TokenIndex,
        handle: engine.DocumentStore.Handle,
        declaration: Ast.Node.Index,
        reference: TypeResolver.FunctionReference,
        caller_frame: ?TypeResolver.ResolutionFrame,
    };

    /// The canonical record of one call: what it reaches, the summary of
    /// the body it reaches, the argument offset its receiver sits at, and
    /// the whole-body read-only verdict a demand query has already
    /// folded — which stays null until one has, because "this body writes
    /// nothing" and "this body has not been looked at" are different
    /// answers.
    pub const ActualCallSummary = call_summary_mod.ActualCallSummary;

    /// A half-open token span `[first, last]`, inclusive.  Spans name a
    /// position in ONE tree, so a span from a foreign document is only
    /// meaningful beside that document's own tree.
    pub const TokenRange = struct {
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    };

    /// A type this cache resolved, together with the document it was
    /// read from and the module it was read in. Token ranges in `info`
    /// belong to `model.tree`, not the requesting file's tree.
    ///
    /// These fields are borrowed: local results require this FileCache
    /// to stay alive, and imported results require its ProjectCache to
    /// stay alive. Do not retain this value past either owner.
    pub const ResolvedType = struct {
        model: *const file_model.FileModel,
        info: *const file_model.TypeInfo,
        path: []const u8,
        module: ModuleId,
    };

    /// This toolchain's own `std/array_list.zig`, or the record that this
    /// session has no toolchain to read.
    pub const StdListTree = union(enum) {
        unknown,
        absent,
        known: *const Ast,
    };

    /// Every call node in this file, keyed by the token naming its callee.
    /// A question that must know whether a token has a call behind it at
    /// all asks here rather than re-deriving it from the token shape: a
    /// token with no call node behind it is a type application or a
    /// spelled name, not something that runs.
    pub const CallIndex = struct {
        by_callee_token: std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index) = .empty,

        fn deinit(self: *CallIndex, gpa: std.mem.Allocator) void {
            self.by_callee_token.deinit(gpa);
            gpa.destroy(self);
        }
    };

    /// One place an identifier token is REFERENCED.  The resolver answers
    /// about values, so it cannot enumerate every syntactic use of a
    /// name; a question that must know them all asks here.
    pub const SyntaxUse = struct {
        node: Ast.Node.Index,
    };

    /// One write to a name inside a fn body: the declaration that binds
    /// it (`declares`), the value written, and whether the write is
    /// unconditional within its statement list.  A plain assignment to
    /// a name can only follow the declaration that binds it, which is
    /// what lets the roots be collected before the targets are read.
    pub const EscapeWrite = struct {
        name: []const u8,
        type_node: ?Ast.Node.Index,
        init: Ast.Node.Index,
        token: Ast.TokenIndex,
        unconditional: bool,
        declares: bool,
    };

    /// What one fn body does to storage by name: the roots it takes the
    /// address of, and the writes it makes.  Borrowed from the cache,
    /// which builds it once per body and owns it for the snapshot's
    /// lifetime, so every walk of that body reads one table.
    pub const EscapeRootIndex = struct {
        addressed: []const []const u8,
        writes: []const EscapeWrite,
    };

    /// Look up a local type or the type reached through the exact import
    /// path in `type_name`. Imported module names require their root alias
    /// prefix; bare names require a root const that selects that type.
    /// Returns the owning tree alongside MethodInfo for cross-file callers.
    ///
    /// Results are cached by the complete type path and method name, so
    /// separate aliases to same-named types remain distinct.
    pub fn findMethodAcrossImports(
        self: *FileCache,
        type_name: []const u8,
        method_name: []const u8,
    ) ?ResolvedMethod {
        // Fast path: type lives in the current file — no traversal.
        const model = self.fileModel() catch return null;
        if (findTypeInModelPath(model, type_name)) |ti| {
            if (ti.findMethod(method_name)) |m| return .{ .tree = self.tree, .method = m };
        }
        const pc = self.project orelse return null;
        if (self.file_path.len == 0) return null;

        // Build the cache key.  On OOM, fall through to uncached lookup.
        const key = std.fmt.allocPrint(
            self.gpa,
            "{s}\x00{s}",
            .{ type_name, method_name },
        ) catch return findMethodCrossFile(self, pc, type_name, method_name);

        // Cache hit — free the key we just built and return the stored result.
        if (self.method_lookup_cache.get(key)) |cached| {
            self.gpa.free(key);
            return cached;
        }

        // Cache miss — run the expensive @import traversal.
        const result = findMethodCrossFile(self, pc, type_name, method_name);

        // Store the result (key now owned by the map on success).
        self.method_lookup_cache.put(self.gpa, key, result) catch self.gpa.free(key);
        return result;
    }

    /// Resolve a cross-file method only through the exact import path named
    /// by `type_name`. A missed path is unresolved; project-global name
    /// matching cannot establish that this file imports a declaration.
    fn findMethodCrossFile(
        self: *FileCache,
        pc: *project_cache_mod.ProjectCache,
        type_name: []const u8,
        method_name: []const u8,
    ) ?ResolvedMethod {
        return findMethodViaImports(
            pc,
            self.tree,
            self.file_path,
            type_name,
            method_name,
            4,
            self.module_id,
        );
    }

    // ── AST and syntax helpers ────────────────────────────────────────

    /// The one node whose token span is EXACTLY `[first, last]`.
    /// Candidates are pre-filtered on their main token before the
    /// expensive firstToken/lastToken walk, since for every node
    /// `firstToken(n) <= main_token(n) <= lastToken(n)`.
    ///
    /// Exact, not enclosing: a question about an expression must not be
    /// answered by a larger expression that happens to contain it.
    pub fn nodeForExactSpan(
        self: *FileCache,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) ?Ast.Node.Index {
        if (first > last) return null;
        if (self.exact_spans == null) self.exact_spans = self.buildExactSpans() catch null;
        // An index that could not be built answers by the scan it replaces.
        const spans = self.exact_spans orelse return self.scanExactSpan(first, last);
        return spans.get((@as(u64, first) << 32) | last);
    }

    /// The spelling this file dispatches on for the type of the expression
    /// spanning exactly `[first, last]`: its own name for a declaration it
    /// owns, `<alias>.<name>` for one reached through an import, and null
    /// when the type engine is unavailable, could not answer, or the
    /// declaration is not nameable from this file.  A foreign declaration's
    /// leaf name is never substituted for an unrelated local declaration.
    pub fn typeReferenceOfExpr(
        self: *FileCache,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) !?[]const u8 {
        const resolver = self.zls orelse return null;
        const node = self.nodeForExactSpan(first, last) orelse return null;
        return resolver.typeReferenceOfNode(node);
    }

    fn buildExactSpans(self: *FileCache) !std.AutoHashMapUnmanaged(u64, Ast.Node.Index) {
        const tree = self.tree;
        var spans: std.AutoHashMapUnmanaged(u64, Ast.Node.Index) = .empty;
        errdefer spans.deinit(self.gpa);
        try spans.ensureTotalCapacity(self.gpa, @intCast(tree.nodes.len));
        var idx: u32 = 1;
        while (idx < tree.nodes.len) : (idx += 1) {
            const node: Ast.Node.Index = @enumFromInt(idx);
            const key = (@as(u64, tree.firstToken(node)) << 32) | tree.lastToken(node);
            // Ascending node order: the first insert is the lowest node, as the scan returned.
            const slot = spans.getOrPutAssumeCapacity(key);
            if (!slot.found_existing) slot.value_ptr.* = node;
        }
        return spans;
    }

    fn scanExactSpan(self: *FileCache, first: Ast.TokenIndex, last: Ast.TokenIndex) ?Ast.Node.Index {
        const tree = self.tree;
        const main_toks = tree.nodes.items(.main_token);
        var idx: u32 = 1;
        while (idx < tree.nodes.len) : (idx += 1) {
            const mt = main_toks[idx];
            if (mt < first or mt > last) continue;
            const node: Ast.Node.Index = @enumFromInt(idx);
            if (tree.firstToken(node) != first or tree.lastToken(node) != last) continue;
            return node;
        }
        return null;
    }

    /// Every node whose main token is `token` — every place this file
    /// REFERENCES that identifier.  Built once per token and borrowed
    /// for the cache's lifetime.
    ///
    /// The resolver cannot answer this: it speaks about values, and a
    /// name can be referenced without ever being called directly.  What
    /// is here is the SYNTACTIC use set, which is what a question about
    /// references needs and what a question about a resolved callee must
    /// not be answered from.
    pub fn syntaxUsesAt(self: *FileCache, token: Ast.TokenIndex) ![]const SyntaxUse {
        if (self.syntax_uses.get(token)) |uses| return uses;
        const tree = self.tree;
        var uses: std.ArrayListUnmanaged(SyntaxUse) = .empty;
        errdefer uses.deinit(self.gpa);
        const main_toks = tree.nodes.items(.main_token);
        var idx: u32 = 1;
        while (idx < tree.nodes.len) : (idx += 1) {
            if (main_toks[idx] != token) continue;
            const node: Ast.Node.Index = @enumFromInt(idx);
            try uses.append(self.gpa, .{ .node = node });
        }
        const owned = try uses.toOwnedSlice(self.gpa);
        try self.syntax_uses.put(self.gpa, token, owned);
        return owned;
    }

    /// Every call node in this file, keyed by the token naming its
    /// callee, built once.  A question that must know whether a token has
    /// a call behind it at all asks here rather than re-deriving it from
    /// the token shape: a token with no call node behind it is a type
    /// application or a spelled name, not something that runs.
    pub fn getCallIndex(self: *FileCache) error{OutOfMemory}!*const CallIndex {
        if (self.call_index == null) {
            // Heap-allocated: the index's own table is filled after the
            // pointer is stored, and a `self`-relative pointer into this
            // struct would move with it.
            const index = try self.gpa.create(CallIndex);
            errdefer self.gpa.destroy(index);
            index.* = .{};
            errdefer index.by_callee_token.deinit(self.gpa);
            const tree = self.tree;
            var buf: [2]Ast.Node.Index = undefined;
            for (tree.nodes.items(.tag), 0..) |_, raw| {
                const node: Ast.Node.Index = @enumFromInt(raw);
                const call = TypeResolver.CallOperands.full(tree, &buf, node) orelse continue;
                try index.by_callee_token.put(self.gpa, call.queryToken(tree, node), node);
            }
            self.call_index = index;
        }
        return self.call_index.?;
    }

    /// Every call site in this file that REACHES `declaration`, or null
    /// when that census cannot be closed.
    ///
    /// The question is the CALLERS of a body, so the scan is over the
    /// whole file and never over the declaration's own body: a call the
    /// body MAKES is not a caller of it, and for a leaf body there is none.
    ///
    /// Each call is bound to the DECLARATION its callee resolves to, never
    /// to the spelling of its name: an alias reaches the declaration it
    /// aliases, a method spelled `recv.grow(..)` reaches the same body, and
    /// a same-named declaration elsewhere does not.
    ///
    /// An unresolved direct identifier or member call with a different name
    /// is unrelated only when the complete reference walk proves this private
    /// function and its owning namespace do not escape. A renamed callable
    /// needs a function-value escape; reflection through an opaque helper
    /// needs a namespace escape. Both prevent closing this census.
    ///
    /// Unknown references with this body's name, indirect callee expressions,
    /// and unknown reflective targets still refuse. Resolved calls always use
    /// declaration identity, not spelling.
    ///
    /// Reflective function values are bound to the same exact declaration.
    /// An export of another helper is not an escape of this body; an unknown
    /// reflective target still prevents closing the census.
    ///
    /// Memoised per declaration, so a helper consulted from several sites
    /// is resolved once rather than once per site and per recursion level.
    /// The slice is borrowed and filed in the cache's own allocator, so
    /// it outlives every caller.
    pub fn closedLocalCalls(self: *FileCache, fn_decl: Ast.Node.Index) SummaryError!?[]Ast.Node.Index {
        if (self.closed_local_calls.get(fn_decl)) |memoized| return memoized;
        // The memo stores null as "refused", so a refusal is as
        // memoised as an answer and is asked once.
        const calls = try self.buildClosedLocalCalls(fn_decl);
        errdefer if (calls) |owned| self.gpa.free(owned);
        try self.closed_local_calls.put(self.gpa, fn_decl, calls);
        return calls;
    }

    /// Build the declaration-bound caller set. Refusals after a collected
    /// call still release the partially built list.
    fn buildClosedLocalCalls(self: *FileCache, fn_decl: Ast.Node.Index) SummaryError!?[]Ast.Node.Index {
        const tree = self.tree;
        const resolver = self.zls orelse return null;
        const frame = resolver.resolutionFrame();
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, fn_decl) orelse return null;
        if (proto.visib_token != null) return null;
        if (proto.extern_export_inline_token) |modifier| {
            switch (tree.tokenTag(modifier)) {
                .keyword_extern, .keyword_export => return null,
                else => {},
            }
        }
        if (try self.writesReflectiveEntryPoint(frame, proto.ast.fn_token)) return null;
        const call_index = try self.getCallIndex();
        var calls: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        defer calls.deinit(self.gpa);
        var namespace_closed: ?bool = null;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            switch (tag) {
                .call, .call_comma, .call_one, .call_one_comma,
                .identifier, .field_access, .enum_literal,
                => {},
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(@enumFromInt(raw))), "@call")) continue;
                },
                else => continue,
            }
            // Namespace/self-relative references are interpreted where they
            // are written, not in this document's root namespace.
            const source_node: Ast.Node.Index = @enumFromInt(raw);
            var source_frame = frame;
            if (raw != 0) {
                if (try resolver.enclosingFunctionAt(tree.firstToken(source_node))) |owner| {
                    switch (try frame.functionReference(owner)) {
                        .function => |reference| source_frame = resolver.frameForFunction(reference),
                        else => {},
                    }
                }
            }
            switch (tag) {
                .call, .call_comma, .call_one, .call_one_comma => {},
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    const node: Ast.Node.Index = @enumFromInt(raw);
                    if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@call")) continue;
                },
                .identifier, .field_access, .enum_literal => {
                    // A function value outside its callee expression can
                    // escape. Resolve the declaration, not its leaf name.
                    const use_node: Ast.Node.Index = @enumFromInt(raw);
                    if (call_index.by_callee_token.get(tree.nodeMainToken(use_node))) |call_node| {
                        var call_buffer: [2]Ast.Node.Index = undefined;
                        const call = TypeResolver.CallOperands.full(tree, &call_buffer, call_node).?;
                        if (call.ast.fn_expr == use_node) continue;
                    }
                    const escaped = try source_frame.functionReference(use_node);
                    switch (escaped) {
                        .function => |reference| {
                            if (reference.tree == tree and reference.handle.module == self.module_id and
                                reference.fn_token == proto.ast.fn_token) return null;
                        },
                        .unknown => {
                            const name_token = if (tag == .field_access)
                                tree.nodeData(use_node).node_and_token[1]
                            else
                                tree.nodeMainToken(use_node);
                            const target_name = proto.name_token orelse return null;
                            if (self.closedCallerNamesEqual(name_token, target_name) orelse return null) return null;
                        },
                        .not_callable => {},
                    }
                    continue;
                },
                else => continue,
            }
            // Node 0 is not a node in Zig's AST.
            if (raw == 0) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            // Census identity does not require one concrete argument frame:
            // an inline tuple call can reach this declaration in many frames.
            // Numeric proofs must still resolve every actual iteration.
            const reference = switch (try source_frame.functionReferenceOfCall(node)) {
                .function => |found| found,
                .unknown => blk: {
                    var call_buffer: [2]Ast.Node.Index = undefined;
                    const call = TypeResolver.CallOperands.full(tree, &call_buffer, node) orelse return null;
                    switch (try source_frame.functionReference(call.ast.fn_expr)) {
                        .function => |found| break :blk found,
                        else => {},
                    }
                    if (try self.isFunctionPointerParameterCall(node)) continue;
                    const name_token = switch (tree.nodeTag(call.ast.fn_expr)) {
                        // A contextual declaration literal still selects a
                        // named namespace member. It cannot rename this
                        // private declaration unless a function value escaped,
                        // which the independent reference walk refuses.
                        .identifier, .enum_literal => tree.nodeMainToken(call.ast.fn_expr),
                        .field_access => tree.nodeData(call.ast.fn_expr).node_and_token[1],
                        else => return null,
                    };
                    const target_name = proto.name_token orelse return null;
                    if (!(self.closedCallerNamesEqual(name_token, target_name) orelse return null)) {
                        if (namespace_closed == null)
                            namespace_closed = !try self.privateNamespaceEscapes(frame, fn_decl);
                        if (namespace_closed.?) continue;
                    }
                    return null;
                },
                .not_callable => return null,
            };
            // Another document's callee is not a caller of this
            // declaration; among this file's own declarations only the
            // one carrying this body is.
            if (reference.tree != tree or reference.handle.module != self.module_id) continue;
            if (reference.fn_token != proto.ast.fn_token) continue;
            try calls.append(self.gpa, node);
        }
        return try calls.toOwnedSlice(self.gpa);
    }

    /// Unknown uses are unrelated only when their decoded names differ.
    /// A quoted spelling is not a new declaration, and a malformed name
    /// cannot close the census. Resolved uses still require declaration identity.
    fn closedCallerNamesEqual(self: *FileCache, left: Ast.TokenIndex, right: Ast.TokenIndex) ?bool {
        var names: [2][]const u8 = undefined;
        for ([_]Ast.TokenIndex{ left, right }, 0..) |token, index| {
            const raw = self.tree.tokenSlice(token);
            if (!std.mem.startsWith(u8, raw, "@\"")) {
                names[index] = raw;
                continue;
            }
            if (raw.len < 3 or raw[raw.len - 1] != '"') return null;
            names[index] = raw[2 .. raw.len - 1];
        }
        if (std.mem.indexOfScalar(u8, names[0], '\\') == null and
            std.mem.indexOfScalar(u8, names[1], '\\') == null)
            return std.mem.eql(u8, names[0], names[1]);
        var readers: [2]CallerNameReader = .{ .{ .raw = names[0] }, .{ .raw = names[1] } };
        var equal = true;
        while (true) {
            const a = readers[0].next() catch return null;
            const b = readers[1].next() catch return null;
            if (a == null and b == null) return equal;
            if (a) |left_byte| {
                if (b) |right_byte| {
                    equal = equal and left_byte == right_byte;
                } else equal = false;
            } else if (b != null) equal = false;
        }
    }

    /// Decode one identifier byte at a time without allocating a copied name.
    const CallerNameReader = struct {
        raw: []const u8,
        index: usize = 0,
        encoded: [4]u8 = undefined,
        encoded_index: usize = 0,
        encoded_len: usize = 0,

        fn next(self: *CallerNameReader) error{InvalidLiteral}!?u8 {
            if (self.encoded_index < self.encoded_len) {
                const byte = self.encoded[self.encoded_index];
                self.encoded_index += 1;
                return byte;
            }
            if (self.index == self.raw.len) return null;
            const byte = self.raw[self.index];
            if (byte != '\\') {
                if (byte == '\n' or byte == '"') return error.InvalidLiteral;
                self.index += 1;
                return byte;
            }
            const unicode = self.index + 1 < self.raw.len and self.raw[self.index + 1] == 'u';
            const scalar = switch (std.zig.string_literal.parseEscapeSequence(self.raw, &self.index)) {
                .success => |value| value,
                .failure => return error.InvalidLiteral,
            };
            if (!unicode) return @as(u8, @intCast(scalar));
            self.encoded_len = std.unicode.utf8Encode(scalar, &self.encoded) catch return error.InvalidLiteral;
            self.encoded_index = 1;
            return self.encoded[0];
        }
    };

    /// A helper can reflect a method after receiving its namespace or an
    /// instance's type, without spelling that method in this document.
    /// Only direct member projections keep the owner local. The declaration's
    /// own container literal creates the namespace; returning it transfers it.
    fn privateNamespaceEscapes(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        fn_decl: Ast.Node.Index,
    ) SummaryError!bool {
        const tree = self.tree;
        const function = (try frame.resolveValueOfNode(fn_decl)) orelse return true;
        if (function.data != .function) return true;
        const owner = function.data.function.container_type.*;
        if (owner.data != .container) return true;
        const owner_scope = owner.data.container.scope_handle;
        // A private module declaration cannot be reflected from another
        // document, even when that document imports/receives its namespace.
        // This census separately refuses all local function-value escapes
        // and unresolved reflection before relying on this privacy boundary.
        if (owner_scope.scope == .root) return false;
        const owner_token = tree.firstToken(owner_scope.toNode());
        var local_owner = (try frame.resolver.enclosingFunctionAt(owner_token)) != null;
        if (!local_owner) for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .test_decl) continue;
            const test_node: Ast.Node.Index = @enumFromInt(raw);
            if (tree.firstToken(test_node) <= owner_token and owner_token <= tree.lastToken(test_node)) {
                local_owner = true;
                break;
            }
        };
        if (!local_owner) return false;
        // An inline literal can be passed as a type without an identifier
        // use. A namespace member can also escape through its outer container.
        // Require a const statement in a local block, not a container member.
        var owner_binding: ?Ast.Node.Index = null;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            switch (tag) {
                .global_var_decl, .local_var_decl, .aligned_var_decl, .simple_var_decl => {},
                else => continue,
            }
            const declaration = tree.fullVarDecl(@enumFromInt(raw)).?;
            if (declaration.ast.init_node.unwrap() != owner_scope.toNode()) continue;
            if (tree.tokenTag(declaration.ast.mut_token) != .keyword_const) return true;
            owner_binding = @enumFromInt(raw);
            break;
        }
        const binding = owner_binding orelse return true;
        var bound_literal = false;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            switch (tag) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => {},
                else => continue,
            }
            var buffer: [2]Ast.Node.Index = undefined;
            const statements = tree.blockStatements(&buffer, @enumFromInt(raw)).?;
            if (std.mem.indexOfScalar(Ast.Node.Index, statements, binding) != null) {
                bound_literal = true;
                break;
            }
        }
        if (!bound_literal) return true;
        var projections = try std.DynamicBitSetUnmanaged.initEmpty(self.gpa, tree.nodes.len);
        defer projections.deinit(self.gpa);
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .field_access) continue;
            var receiver = tree.nodeData(@enumFromInt(raw)).node_and_token[0];
            while (true) {
                projections.set(@intFromEnum(receiver));
                if (tree.nodeTag(receiver) != .grouped_expression) break;
                receiver = tree.nodeData(receiver).node_and_token[0];
            }
        }
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            var node: Ast.Node.Index = @enumFromInt(raw);
            switch (tag) {
                .identifier, .field_access, .address_of, .deref,
                .call, .call_comma, .call_one, .call_one_comma,
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma,
                => {},
                .@"return" => node = tree.nodeData(node).opt_node.unwrap() orelse continue,
                else => continue,
            }
            if (projections.isSet(@intFromEnum(node))) continue;
            const namespace = (try frame.containerOfNode(node)) orelse continue;
            if (namespace.scope_handle.scope == owner_scope.scope and
                namespace.scope_handle.handle.eql(owner_scope.handle)) return true;
        }
        return false;
    }

    /// A caller-supplied function pointer is unrelated only after the census
    /// also rejects every escape of the private target. Do not generalize this
    /// to opaque receivers, aliases, anytype parameters or unknown functions.
    fn isFunctionPointerParameterCall(self: *FileCache, node: Ast.Node.Index) SummaryError!bool {
        const tree = self.tree;
        const resolver = self.zls orelse return false;
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &call_buffer, node) orelse return false;
        if (tree.nodeTag(call.ast.fn_expr) != .identifier) return false;
        const name_token = tree.nodeMainToken(call.ast.fn_expr);
        const function = (try resolver.enclosingFunctionAt(name_token)) orelse return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, function) orelse return false;
        const body = tokens.bodyOf(tree, function) orelse return false;
        const bindings = try self.localBindings(proto, body);
        const binding = bindings.findAt(tree.tokenSlice(name_token), name_token) orelse return false;
        if (binding.origin != .param) return false;
        var parameters = proto.iterate(tree);
        while (parameters.next()) |parameter| {
            if (parameter.name_token != binding.name_token) continue;
            const type_node = parameter.type_expr orelse return false;
            const pointer = tree.fullPtrType(type_node) orelse return false;
            if (pointer.size != .one) return false;
            var function_buffer: [1]Ast.Node.Index = undefined;
            return tree.fullFnProto(&function_buffer, pointer.ast.child_type) != null;
        }
        return false;
    }

    /// A reflective target can escape without an identifier use of this body.
    /// Resolve its actual declaration rather than refusing unrelated exports.
    fn writesReflectiveEntryPoint(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        fn_token: Ast.TokenIndex,
    ) SummaryError!bool {
        const tree = self.tree;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            switch (tag) {
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
                else => continue,
            }
            const node: Ast.Node.Index = @enumFromInt(raw);
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            var target = node;
            if (std.mem.eql(u8, name, "@export")) {
                var buffer: [2]Ast.Node.Index = undefined;
                const parameters = tree.builtinCallParams(&buffer, node) orelse return true;
                if (parameters.len != 2) return true;
                target = parameters[0];
            } else if (!std.mem.eql(u8, name, "@field")) {
                continue;
            }
            switch (try frame.functionReference(target)) {
                .function => |reference| {
                    if (reference.tree == tree and reference.handle.module == self.module_id and
                        reference.fn_token == fn_token) return true;
                },
                .unknown => return true,
                .not_callable => {},
            }
        }
        return false;
    }

    // ── Address uses ─────────────────────────────────────────────────

    /// One `&` operand in this file: the expression the address is of,
    /// and whether that address can act as a WRITE. An instance-method
    /// call `x.method(..)` also takes the address of its receiver `x`
    /// implicitly; that receiver is filed the same way, with `receiver`
    /// set, and is reported when source proves complete or exact field stores.
    ///
    /// Possible mutation is not initialization. `definite_write` proves the
    /// complete pointee; `fields` proves only those inline projections.
    pub const ComputedStoreBase = struct {
        source: ?WholeStoreSource = null,
        computations: u8 = 0,
        original_alternative: bool = false,
        opaque_alternative: bool = false,

        pub fn equal(a: ComputedStoreBase, b: ComputedStoreBase) bool {
            return WholeStoreSource.equal(a.source, b.source) and a.computations == b.computations and
                a.original_alternative == b.original_alternative and a.opaque_alternative == b.opaque_alternative;
        }
    };

    pub const WrittenRead = struct {
        argument: Ast.Node.Index,
        tree: *const Ast,
        node: Ast.Node.Index,
        identity_projection: bool = false,
        /// Original pointee bytes require a current caller backing, not pointer identity.
        pointee_read: bool = false,
        base_read: ?u3 = null,
        relative_path: ?[]const u8 = null,
        index: ?u64 = null,
        is_array: bool = false,
        array_extent: ?u64 = null,
        value_type: ?TypeResolver.ActualType = null,
        output_read: bool = false,
        /// Select one runtime-indexed element from the immutable output COW base.
        output_index_read: bool = false,
        output_prefix: ?[]const u8 = null,
        output_base: ?ComputedStoreBase = null,
    };

    /// Authenticated value identity, not an initialized-value certificate.
    /// Bits name independently proved originating-caller written_inputs slots.
    pub const WholeStoreSource = struct {
        sources: u8 = 0,
        projections: u8 = 0,
        opaque_alternative: bool = true,

        fn merge(a: WholeStoreSource, b: WholeStoreSource) WholeStoreSource {
            return .{ .sources = a.sources | b.sources, .projections = a.projections | b.projections, .opaque_alternative = a.opaque_alternative or b.opaque_alternative };
        }

        fn equal(a: ?WholeStoreSource, b: ?WholeStoreSource) bool {
            if (a == null or b == null) return a == null and b == null;
            return a.?.sources == b.?.sources and a.?.projections == b.?.projections and a.?.opaque_alternative == b.?.opaque_alternative;
        }
    };

    /// Slots in the bounded, deduplicated caller-input and projected-read tables.
    /// This recipe describes byte dependencies, never a value certificate.
    pub const WrittenDependencies = struct {
        inputs: u8 = 0,
        reads: u8 = 0,

        fn merge(self: *WrittenDependencies, other: WrittenDependencies) void {
            self.inputs |= other.inputs;
            self.reads |= other.reads;
        }

        fn eql(self: WrittenDependencies, other: WrittenDependencies) bool {
            return self.inputs == other.inputs and self.reads == other.reads;
        }

        fn isEmpty(self: WrittenDependencies) bool {
            return self.inputs == 0 and self.reads == 0;
        }
    };
    pub const ComputedStoreWrite = struct {
        path: []const u8,
        parent: ?u7 = null,
        array_index: ?u64 = null,
        dependencies: WrittenDependencies = .{},
        source: ?WholeStoreSource = null,
        literal_undefined: bool = false,
        literal_may_undefined: bool = false,
        opaque_alternative: bool = false,
        is_array: bool = false,
        array_extent: ?u64 = null,
    };

    /// One immutable COW result. Its base is an older result set, and its
    /// ordered component writes replace only the paths they name.
    pub const ComputedStoreValue = struct {
        whole_value: bool = false,
        base_source: ?WholeStoreSource = null,
        base_computations: u8 = 0,
        base_original_alternative: bool = false,
        base_opaque_alternative: bool = false,
        writes: []const ComputedStoreWrite = &.{},
        is_array: bool = false,
        array_extent: ?u64 = null,
        output_prefix: ?[]const u8 = null,
    };

    /// Proof-local staging pool. Templates and writes remain inline scratch
    /// until the root proof succeeds. Publication copies only reachable write
    /// slices into the summary arena, once per immutable result.
    const ComputedStoreBuilders = struct {
        values: [8]?ComputedStoreValue = .{null} ** 8,
        expanded_alternatives: [8]u8 = @splat(0),
        write_offsets: [8]usize = undefined,
        write_counts: [8]usize = undefined,
        writes: [128]ComputedStoreWrite = undefined,
        count: usize = 0,
        write_count: usize = 0,
        overflow: bool = false,

        fn sourceAlternativeCount(source: ?WholeStoreSource, write: ?ComputedStoreWrite) u16 {
            var count: u16 = 0;
            if (source) |identity| {
                count += @intCast(@popCount(identity.sources));
                count += @intCast(@popCount(identity.projections));
            }
            const source_opaque = if (source) |identity| identity.opaque_alternative else false;
            const write_opaque = if (write) |component| component.opaque_alternative else false;
            if (source_opaque or write_opaque) count += 1;
            if (if (write) |component| component.literal_undefined or component.literal_may_undefined else false) count += 1;
            return if (count == 0) 1 else count;
        }

        fn alternativeCount(self: *const ComputedStoreBuilders, base: ComputedStoreBase) ?u8 {
            var count: u16 = 0;
            if (base.source) |source| {
                count += @intCast(@popCount(source.sources));
                count += @intCast(@popCount(source.projections));
                if (source.opaque_alternative) count += 1;
            }
            if (base.original_alternative) count += 1;
            if (base.opaque_alternative) count += 1;
            var handles = base.computations;
            while (handles != 0) {
                const index: usize = @intCast(@ctz(handles));
                if (index >= self.count) return null;
                count += self.expanded_alternatives[index];
                handles &= handles - 1;
            }
            if (count == 0 or count > 8) return null;
            return @intCast(count);
        }

        fn add(
            self: *ComputedStoreBuilders,
            value: ComputedStoreValue,
        ) ?u8 {
            for (self.values[0..self.count], 0..) |entry, index| {
                const previous = entry orelse continue;
                if (previous.whole_value != value.whole_value or
                    !WholeStoreSource.equal(previous.base_source, value.base_source) or
                    previous.base_computations != value.base_computations or
                    previous.base_original_alternative != value.base_original_alternative or
                    previous.base_opaque_alternative != value.base_opaque_alternative or
                    previous.is_array != value.is_array or previous.array_extent != value.array_extent or
                    previous.writes.len != value.writes.len) continue;
                if (previous.output_prefix) |prefix| {
                    if (value.output_prefix == null or !std.mem.eql(u8, prefix, value.output_prefix.?)) continue;
                } else if (value.output_prefix != null) continue;
                var same = true;
                for (previous.writes, value.writes) |old, new| {
                    if (!std.mem.eql(u8, old.path, new.path) or old.parent != new.parent or
                        old.array_index != new.array_index or !old.dependencies.eql(new.dependencies) or
                        !WholeStoreSource.equal(old.source, new.source) or
                        old.literal_undefined != new.literal_undefined or
                        old.literal_may_undefined != new.literal_may_undefined or
                        old.opaque_alternative != new.opaque_alternative or
                        old.is_array != new.is_array or old.array_extent != new.array_extent)
                    {
                        same = false;
                        break;
                    }
                }
                if (same) return @as(u8, 1) << @intCast(index);
            }
            if (self.overflow) return null;
            if (self.count == self.values.len or value.writes.len == 0 or
                value.writes.len > self.writes.len - self.write_count)
            {
                self.overflow = true;
                return null;
            }
            const handle_mask: u8 = if (self.count == 0) 0 else (@as(u8, 1) << @intCast(self.count)) - 1;
            if (value.whole_value) {
                if (value.base_source != null or value.base_computations != 0 or
                    value.base_original_alternative or value.base_opaque_alternative)
                {
                    self.overflow = true;
                    return null;
                }
            } else if (value.base_computations & ~handle_mask != 0) {
                self.overflow = true;
                return null;
            }

            const base: ComputedStoreBase = .{
                .source = value.base_source,
                .computations = value.base_computations,
                .original_alternative = value.base_original_alternative,
                .opaque_alternative = value.base_opaque_alternative,
            };
            var alternatives: u16 = if (value.whole_value) 1 else self.alternativeCount(base) orelse {
                self.overflow = true;
                return null;
            };
            for (value.writes) |write| {
                const choices = sourceAlternativeCount(write.source, write);
                if (alternatives > 8 / choices) {
                    self.overflow = true;
                    return null;
                }
                alternatives *= choices;
            }

            const index = self.count;
            const first = self.write_count;
            const last = first + value.writes.len;
            @memcpy(self.writes[first..last], value.writes);
            self.write_offsets[index] = first;
            self.write_counts[index] = value.writes.len;
            self.values[index] = .{
                .whole_value = value.whole_value,
                .base_source = value.base_source,
                .base_computations = value.base_computations,
                .base_original_alternative = value.base_original_alternative,
                .base_opaque_alternative = value.base_opaque_alternative,
                .writes = self.writes[first..last],
                .is_array = value.is_array,
                .array_extent = value.array_extent,
                .output_prefix = value.output_prefix,
            };
            self.expanded_alternatives[index] = @intCast(alternatives);
            self.write_count = last;
            self.count += 1;
            return @as(u8, 1) << @intCast(index);
        }

        fn markReachable(
            self: *const ComputedStoreBuilders,
            handles: u8,
            reachable: *u8,
        ) bool {
            var pending = handles;
            while (pending != 0) {
                const index: usize = @intCast(@ctz(pending));
                const bit = @as(u8, 1) << @intCast(index);
                pending &= pending - 1;
                if (reachable.* & bit != 0) continue;
                if (index >= self.count) return false;
                reachable.* |= bit;
                pending |= self.values[index].?.base_computations;
            }
            return true;
        }

        fn publish(
            self: *const ComputedStoreBuilders,
            owner: *FileCache,
            root: ComputedStoreBase,
            include_root: bool,
            reads: *const [8]?WrittenRead,
            selected_reads: u8,
            use: *AddressUse,
        ) !bool {
            use.written_computations = .{null} ** 8;
            if (self.overflow or (include_root and self.alternativeCount(root) == null)) return false;
            var reachable: u8 = 0;
            var pending_reads = selected_reads;
            if (include_root) {
                if (!self.markReachable(root.computations, &reachable)) return false;
                if (root.source) |source| pending_reads |= source.projections;
            }
            var examined_nodes: u8 = 0;
            var examined_reads: u8 = 0;
            while (true) {
                var nodes = reachable & ~examined_nodes;
                var requested = pending_reads & ~examined_reads;
                if (nodes == 0 and requested == 0) break;
                while (nodes != 0) {
                    const index: usize = @intCast(@ctz(nodes));
                    const bit = @as(u8, 1) << @intCast(index);
                    nodes &= nodes - 1;
                    examined_nodes |= bit;
                    const node = self.values[index] orelse return false;
                    if (node.base_source) |source| pending_reads |= source.projections;
                    for (node.writes) |write| {
                        pending_reads |= write.dependencies.reads;
                        if (write.source) |source| pending_reads |= source.projections;
                    }
                }
                requested |= pending_reads & ~examined_reads;
                while (requested != 0) {
                    const index: usize = @intCast(@ctz(requested));
                    const bit = @as(u8, 1) << @intCast(index);
                    requested &= requested - 1;
                    examined_reads |= bit;
                    const entry = reads[index] orelse return false;
                    const read_base = entry.output_base orelse continue;
                    if (self.alternativeCount(read_base) == null or
                        !self.markReachable(read_base.computations, &reachable)) return false;
                    if (read_base.source) |source| pending_reads |= source.projections;
                }
            }
            var handles = reachable;
            while (handles != 0) {
                const index: usize = @intCast(@ctz(handles));
                handles &= handles - 1;
                const value = self.values[index] orelse return false;
                const first = self.write_offsets[index];
                const last = first + self.write_counts[index];
                if (owner.summary_arena == null) owner.summary_arena = std.heap.ArenaAllocator.init(owner.gpa);
                const writes = try owner.summary_arena.?.allocator().dupe(
                    ComputedStoreWrite,
                    self.writes[first..last],
                );
                var published = value;
                published.writes = writes;
                use.written_computations[index] = published;
            }
            return true;
        }
    };

    /// Passive changed-continue alternatives. Proof snapshots borrow this
    /// bounded sink; they never copy another binding or coverage payload.
    const WrittenMayStores = struct {
        fields: [128][]const u8 = undefined,
        dependencies: [128]WrittenDependencies = undefined,
        literal_may_undefined: [128]bool = @splat(false),
        count: usize = 0,

        fn add(self: *WrittenMayStores, path: []const u8, recipe: WrittenDependencies) bool {
            for (self.fields[0..self.count], self.dependencies[0..self.count]) |field, *dependencies| {
                if (!std.mem.eql(u8, field, path)) continue;
                dependencies.merge(recipe);
                return true;
            }
            if (self.count == self.fields.len) return false;
            self.fields[self.count] = path;
            self.dependencies[self.count] = recipe;
            self.literal_may_undefined[self.count] = false;
            self.count += 1;
            return true;
        }

        fn addLiteral(self: *WrittenMayStores, path: []const u8) bool {
            if (!self.add(path, .{})) return false;
            for (self.fields[0..self.count], self.literal_may_undefined[0..self.count]) |field, *literal| {
                if (std.mem.eql(u8, field, path)) {
                    literal.* = true;
                    return true;
                }
            }
            unreachable;
        }
    };

    pub const AddressUse = struct {
        operand: Ast.Node.Index,
        may_write: bool,
        definite_write: bool = false,
        location_written: bool = false,
        /// The successful source paths were completely traversed, even when
        /// they prove only partial/conditional writes. False means UNKNOWN,
        /// not a witnessed no-store alternative.
        location_store_coverage_known: bool = false,
        whole_source: ?WholeStoreSource = null,
        written_computations: [8]?ComputedStoreValue = .{null} ** 8,
        location_computed_sources: u8 = 0,
        location_computed_original_alternative: bool = false,
        location_computed_opaque_alternative: bool = false,
        location_computed_complete: bool = true,
        physical_store_only: bool = false,
        /// Exact physical C scalar destination; never a whole-array certificate.
        location_element_index: ?u64 = null,
        location_value_type: ?TypeResolver.ActualType = null,
        /// Definite physical writes, separate from initialized-value proofs.
        location_fields: [128][]const u8 = undefined,
        location_field_dependencies: [128]WrittenDependencies = undefined,
        /// Independently authenticated exact field sources; never dependency identities.
        location_field_sources: [128]?WholeStoreSource = .{null} ** 128,
        location_field_count: usize = 0,
        may_written_stores: WrittenMayStores = .{},
        written_inputs: [8]?Ast.Node.Index = .{null} ** 8,
        written_reads: [8]?WrittenRead = .{null} ** 8,
        undefined_fields: [128][]const u8 = undefined,
        undefined_field_count: usize = 0,
        /// Exact source-proven paths, independent of complete-pointee credit.
        fields: [128][]const u8 = undefined,
        field_count: usize = 0,
        /// A boolean-return certificate applies only to this result arm.
        success_bool: ?bool = null,
        call_node: ?Ast.Node.Index = null,
        address_node: Ast.Node.Index,
        proof_queried: bool = false,
        /// The address is the implicit one of a method-call receiver. An
        /// unproven receiver is not an address use at all: a method name
        /// and a possible write say nothing about its storage.
        receiver: bool = false,
    };
    const AddressUseMap = std.AutoHashMapUnmanaged(Ast.TokenIndex, AddressUse);

    /// What this file does with the address of the name at
    /// `operand_token`, or null when nothing here takes that name's
    /// address.  `&x` and `&x.field` are both filed under `x`, by the
    /// same `tokens.rootIdentifier` the escape index uses, so the two
    /// readers cannot disagree about whose address is being taken.
    ///
    /// MAY_WRITE is true exactly when the address reaches an ARGUMENT
    /// POSITION of something that writes memory: an ordinary call —
    /// whose arguments are every child of the call node except the
    /// callee itself, so `(&f)()` is a call THROUGH the address and not
    /// a write to `f` — or one of `@memcpy` / `@memset` /
    /// `@atomicStore` / `@atomicRmw` / `@cmpxchgStrong` /
    /// `@cmpxchgWeak`, whose every child is an operand.  A builtin that
    /// only inspects an address (`@intFromPtr`) is deliberately not on
    /// that list, and a bare `fn_decl` boundary stops the question: an
    /// argument position in an ENCLOSING call says nothing about what a
    /// nested function does with the name it merely closed over.
    ///
    /// Anything else is a false: `const p = &x`, `_ = &x`,
    /// `arr[i] = &x`, `&x` stored in a struct — the address is formed
    /// and the storage is untouched, which is what a caller asking
    /// "can this be an out-parameter write?" must be told.
    ///
    /// Bounded like every other walk of this file's nodes: one frame
    /// per AST level, one visit per node, each reported through the
    /// budget module rather than as a bare error.
    pub fn addressUseAt(
        self: *FileCache,
        operand_token: Ast.TokenIndex,
    ) SummaryError!?AddressUse {
        if (self.address_uses == null) self.address_uses = try self.buildAddressUses();
        const use = self.address_uses.?.get(operand_token) orelse return null;
        if (use.proof_queried) return use;
        var proved = use;
        const positive = try self.definiteAddressWrite(&proved);
        if (!positive and use.receiver) return null;
        // A completed no-store or conditional-store query still carries
        // diagnostic facts. Do not replace them with the raw call mapping.
        proved.proof_queried = true;
        self.address_uses.?.getPtr(operand_token).?.* = proved;
        self.address_proof_generation += 1;
        return proved;
    }

    /// Raw possible-write mapping; no must-write or returned-value credit.
    pub fn possibleAddressUseAt(self: *FileCache, token: Ast.TokenIndex) SummaryError!?AddressUse {
        if (self.address_uses == null) self.address_uses = try self.buildAddressUses();
        return self.address_uses.?.get(token);
    }

    pub fn undefinedAddressUseAt(self: *FileCache, token: Ast.TokenIndex, success_bool: ?bool) anyerror!?AddressUse {
        if (self.address_uses == null) self.address_uses = try self.buildAddressUses();
        var use = self.address_uses.?.get(token) orelse return null;
        use.definite_write = false;
        use.location_written = false;
        use.whole_source = null;
        use.location_field_count = 0;
        use.field_count = 0;
        use.may_written_stores.count = 0;
        use.written_inputs = .{null} ** 8;
        use.written_reads = .{null} ** 8;
        use.success_bool = success_bool;
        try self.populateUndefinedAddressStores(&use);
        return if (use.undefined_field_count != 0) use else null;
    }

    /// A result-conditioned certificate is deliberately separate from the
    /// unconditional token memo. False, unknown, and opaque results do not
    /// inherit stores proved only on true returns.
    pub fn addressUseOnBooleanAt(self: *FileCache, operand_token: Ast.TokenIndex, expected: bool) SummaryError!?AddressUse {
        if (self.address_uses == null) self.address_uses = try self.buildAddressUses();
        var use = self.address_uses.?.get(operand_token) orelse return null;
        use.definite_write = false;
        use.field_count = 0;
        use.location_written = false;
        use.whole_source = null;
        use.location_field_count = 0;
        use.location_field_sources = .{null} ** 128;
        use.written_inputs = .{null} ** 8;
        use.written_reads = .{null} ** 8;
        use.success_bool = expected;
        if (!try self.definiteAddressWrite(&use)) return null;
        return use;
    }


    /// Query an explicit pointer actual only after the consumer authenticates a
    /// current local backing. This reuses the same must-store proof as address-of
    /// arguments; it does not infer pointee identity from a pointer type.
    pub fn pointerArgumentStoreUseAt(
        self: *FileCache,
        call_node: Ast.Node.Index,
        argument: Ast.Node.Index,
        success_bool: ?bool,
    ) SummaryError!?AddressUse {
        var use: AddressUse = .{
            .address_node = argument,
            .operand = if (self.tree.fullSlice(argument)) |slice| slice.ast.sliced else argument,
            .call_node = call_node,
            .may_write = true,
            .success_bool = success_bool,
            .physical_store_only = true,
        };
        if (!try self.definiteAddressWrite(&use)) return null;
        if (self.tree.fullSlice(argument) != null and use.location_element_index == null) return null;
        use.proof_queried = true;
        return use;
    }

    /// Exact scalar reads through an implicit pointer receiver. These paths
    /// do not certify stores or reads of the receiver's remaining fields.
    pub const MethodScalarReads = struct {
        receiver: Ast.Node.Index,
        fields: [128][]const u8 = undefined,
        field_count: usize = 0,
    };

    /// A by-value aggregate transports bytes; a source-proven scalar selection
    /// in its callee reads only the corresponding actual bytes.
    pub fn valueScalarReadsAt(self: *FileCache, call_token: Ast.TokenIndex, frame: ?TypeResolver.ResolutionFrame, argument: Ast.Node.Index) SummaryError!?MethodScalarReads {
        const canonical = (try self.actualCallSummaryAt(call_token, frame)) orelse return null;
        const call_node = canonical.callee.call_node;
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        try self.enterNormalCleanup(call_node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanup(call_node);
        return self.scalarReadsForUse(.{ .operand = argument, .address_node = argument, .call_node = call_node, .may_write = false }, call_node, canonical, true);
    }

    /// Overlay only writes whose positive byte effect is not source-proven.
    /// Source-proven copies, negative writes and loop recipes retain their
    /// existing masks; this query never grants an initialization certificate.
    pub fn diagnosticOutputTouchesAt(self: *FileCache, call_token: Ast.TokenIndex, frame: ?TypeResolver.ResolutionFrame, argument: Ast.Node.Index) SummaryError!?MethodScalarReads {
        const canonical = (try self.actualCallSummaryAt(call_token, frame)) orelse return null;
        const tree = canonical.callee.tree;
        const body = tokens.bodyOf(tree, canonical.callee.declaration) orelse return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return null;
        var parameters = proto.iterate(tree);
        var parameter_index: u32 = 0;
        var name: ?[]const u8 = null;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            const actual = (try canonical.callArgumentFor(self, &argument_buffer, parameter_index)) orelse continue;
            if (actual != argument) continue;
            name = tree.tokenSlice(parameter.name_token orelse return null);
            break;
        }
        var key = resolvedCleanupKey(canonical.callee.reference, canonical.callee.declaration);
        key.demand = .{ .one = parameter_index };
        if (self.diagnostic_output_touches.get(key)) |cached| {
            const paths = cached orelse return null;
            var result: MethodScalarReads = .{ .receiver = argument, .field_count = paths.len };
            @memcpy(result.fields[0..paths.len], paths);
            return result;
        }
        if (self.diagnostic_output_touches_visiting.contains(key)) return null;
        try self.diagnostic_output_touches_visiting.put(self.gpa, key, {});
        defer _ = self.diagnostic_output_touches_visiting.remove(key);
        const declaring = (try canonical.declaringCache(self)) orelse return null;
        const resolver = declaring.zls orelse return null;
        const formal_types = canonical.callee.reference.actual_type.data.function.parameters;
        if (parameter_index >= formal_types.len) return null;
        const formal_type = (try resolver.normalizedType(formal_types[parameter_index].type)) orelse return null;
        if (resolver.pointerSize(formal_type) == null) switch (resolver.typeTag(formal_type) orelse return null) {
            .@"struct", .@"union", .array, .vector => {},
            else => return .{ .receiver = argument },
        };
        const read_only = switch (formal_type.data) {
            .pointer => |pointer| pointer.is_const,
            .ip_index => switch (resolver.ctx.ip.indexToKey(formal_type.ipIndex() orelse return null)) {
                .pointer_type => |pointer| pointer.flags.is_const,
                else => false,
            },
            else => false,
        };
        if (read_only) return .{ .receiver = argument };
        // Build the callee's bindings now; the context names them by body and
        // reacquires them at each use, because the nested touch queries below
        // can grow `declaring.bindings` and move every borrowed entry.
        _ = try declaring.localBindings(proto, body);
        const context: DiagnosticTouchContext = .{
            .declaring = declaring,
            .frame = resolver.frameForFunction(canonical.callee.reference),
            .body = body,
        };
        var result: MethodScalarReads = .{ .receiver = argument };
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        // These whole-body proofs bind every write and its value dependencies.
        // Their caller byte effects retain old-hole and poisoned-input witnesses.
        if ((try self.preservingParameterBody(canonical, canonical.callee.call_node, parameter_index, false)) != null or
            (try self.preservingParameterBody(canonical, canonical.callee.call_node, parameter_index, true)) != null)
            return result;
        if (!try self.collectDiagnosticOutputTouches(tree, body, name orelse return null, &result, context, 0)) {
            try self.diagnostic_output_touches.put(self.gpa, key, null);
            return null;
        }
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        const paths = try self.summary_arena.?.allocator().dupe([]const u8, result.fields[0..result.field_count]);
        try self.diagnostic_output_touches.put(self.gpa, key, paths);
        return result;
    }

    fn diagnosticOutputPath(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, name: []const u8, depth: u32) SummaryError!?struct { path: []const u8, precise: bool = true } {
        if (depth == 64) return null;
        switch (tree.nodeTag(node)) {
            .identifier => return if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name)) .{ .path = "" } else null,
            .deref => {
                const base = tree.nodeData(node).node;
                if (tree.nodeTag(base) != .identifier) return null;
                return self.diagnosticOutputPath(tree, base, name, depth + 1);
            },
            .address_of => return self.diagnosticOutputPath(tree, tree.nodeData(node).node, name, depth + 1),
            .grouped_expression => return self.diagnosticOutputPath(tree, tree.nodeData(node).node_and_token[0], name, depth + 1),
            .array_access => {
                const base, const subscript = tree.nodeData(node).node_and_node;
                const prefix = (try self.diagnosticOutputPath(tree, base, name, depth + 1)) orelse return null;
                if (!prefix.precise) return prefix;
                if (tree.nodeTag(subscript) != .number_literal) return .{ .path = prefix.path, .precise = false };
                const index = std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(subscript)), 0) catch return .{ .path = prefix.path, .precise = false };
                if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
                return .{ .path = try std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}[{d}]", .{ prefix.path, index }) };
            },
            .field_access => {
                const base, const selector = tree.nodeData(node).node_and_token;
                const prefix = (try self.diagnosticOutputPath(tree, base, name, depth + 1)) orelse return null;
                if (!prefix.precise) return prefix;
                if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
                return .{ .path = try std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}{s}{s}", .{ prefix.path, if (prefix.path.len == 0) "" else ".", tree.tokenSlice(selector) }) };
            },
            else => return null,
        }
    }

    const DiagnosticTouchContext = struct {
        declaring: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        /// Key of a `declaring.bindings` entry built before the walk. Entries
        /// are only removed at cache teardown, but the table can rehash.
        body: Ast.Node.Index,

        fn bindings(context: DiagnosticTouchContext) *const local_bindings.LocalBindings {
            return context.declaring.bindings.getPtr(@intFromEnum(context.body)).?;
        }
    };

    const DiagnosticTouchPath = struct { path: []const u8, precise: bool = true };

    /// A copied scalar cannot write its source. Aggregate values can still
    /// transport borrowed pointers; their constructor leaves retain that reach.
    fn diagnosticBorrowedTouchPath(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, name: []const u8, context: DiagnosticTouchContext, depth: u32) SummaryError!?DiagnosticTouchPath {
        // Forming an address selects a location, even when its stored value is
        // scalar. Passing that scalar value itself still supplies no address.
        if (tree.nodeTag(node) == .address_of)
            return self.diagnosticTouchPath(tree, tree.nodeData(node).node, name, context, depth + 1);
        if (tree.nodeTag(node) == .grouped_expression)
            return self.diagnosticBorrowedTouchPath(tree, tree.nodeData(node).node_and_token[0], name, context, depth + 1);
        if (try context.frame.typeOfNode(node)) |actual| {
            if (try context.frame.resolver.normalizedType(actual)) |normalized| {
                if (context.frame.resolver.pointerSize(normalized) == null) switch (context.frame.resolver.typeTag(normalized) orelse return null) {
                    .@"struct", .@"union", .array, .vector => {},
                    else => return self.diagnosticEncodedTouchPath(tree, node, name, context, depth),
                };
            }
        }
        return self.diagnosticTouchPath(tree, node, name, context, depth);
    }

    /// Only explicit pointer encodings supply scalar address reach. Ordinary
    /// scalar loads, parameters and field selections never infer such a loan.
    fn diagnosticEncodedTouchPath(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, name: []const u8, context: DiagnosticTouchContext, depth: u32) SummaryError!?DiagnosticTouchPath {
        if (depth == 64) return .{ .path = "", .precise = false };
        try self.chargeNormalCleanupAt(tree, node);
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.builtinCallParams(&buffer, node)) |arguments| {
            const builtin = tree.tokenSlice(tree.nodeMainToken(node));
            if (arguments.len == 1 and std.mem.eql(u8, builtin, "@intFromPtr")) {
                if ((try self.diagnosticBorrowedTouchPath(tree, arguments[0], name, context, depth + 1)) != null)
                    return .{ .path = "", .precise = false };
                return null;
            }
            if (arguments.len != 0 and (std.mem.eql(u8, builtin, "@as") or
                std.mem.eql(u8, builtin, "@bitCast") or std.mem.eql(u8, builtin, "@intCast") or
                std.mem.eql(u8, builtin, "@truncate")))
                return self.diagnosticEncodedTouchPath(tree, arguments[arguments.len - 1], name, context, depth + 1);
            return null;
        }
        if (tree.nodeTag(node) == .identifier) {
            const token = tree.nodeMainToken(node);
            const binding = (context.bindings().findAt(tree.tokenSlice(token), token) orelse return null).*;
            if (binding.origin == .param or binding.origin == .loop_capture) return null;
            var base: ?DiagnosticTouchPath = null;
            if (context.declaring.nodeForExactSpan(binding.rhs_first, binding.rhs_last)) |rhs| {
                base = try self.diagnosticEncodedTouchPath(tree, rhs, name, context, depth + 1);
            }
            if (!binding.is_const)
                try self.diagnosticReboundTouches(tree, context.body, binding.name_token, token, name, context, &base, depth + 1);
            return base;
        }
        if (tree.nodeTag(node) == .grouped_expression)
            return self.diagnosticEncodedTouchPath(tree, tree.nodeData(node).node_and_token[0], name, context, depth + 1);
        switch (tree.nodeTag(node)) {
            .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor,
            .add_wrap, .sub_wrap, .mul_wrap, .add_sat, .sub_sat, .mul_sat, .shl_sat,
            => {
                var children = engine.AstIterator.init(tree, node);
                while (children.next(tree)) |child|
                    if ((try self.diagnosticEncodedTouchPath(tree, child, name, context, depth + 1)) != null)
                        return .{ .path = "", .precise = false };
            },
            else => {},
        }
        return null;
    }

    /// Follow local pointer copies and pointer captures for possible opaque
    /// writes. This is reachability only, never a current-pointee certificate.
    /// Rebindings are unioned so an alias cannot hide a reachable opaque call.
    fn diagnosticTouchPath(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, name: []const u8, context: DiagnosticTouchContext, depth: u32) SummaryError!?DiagnosticTouchPath {
        if (depth == 64) return .{ .path = "", .precise = false };
        try self.chargeNormalCleanupAt(tree, node);
        const root = tokens.rootIdentifier(tree, node) orelse {
            // A cast or returned pointer can hide a formal root. Keep possible
            // reach, without inventing a precise projection.
            var children = engine.AstIterator.init(tree, node);
            while (children.next(tree)) |child|
                if ((try self.diagnosticBorrowedTouchPath(tree, child, name, context, depth + 1)) != null)
                    return .{ .path = "", .precise = false };
            return null;
        };
        const token = tree.nodeMainToken(root);
        const root_name = tree.tokenSlice(token);
        const binding = (context.bindings().findAt(root_name, token) orelse return null).*;
        if (binding.origin == .param) {
            if (!std.mem.eql(u8, root_name, name)) return null;
            const path = (try self.diagnosticOutputPath(tree, node, name, 0)) orelse
                return .{ .path = "", .precise = false };
            return .{ .path = path.path, .precise = path.precise };
        }
        if (try context.frame.typeOfNode(root)) |actual| {
            if (try context.frame.resolver.normalizedType(actual)) |normalized| {
                if (context.frame.resolver.pointerSize(normalized) == null) switch (context.frame.resolver.typeTag(normalized) orelse return null) {
                    .@"struct", .@"union", .array, .vector => {},
                    else => return null,
                };
            }
        }
        if (binding.origin == .loop_capture and
            (binding.name_token == 0 or tree.tokenTag(binding.name_token - 1) != .asterisk)) return null;
        var base: ?DiagnosticTouchPath = null;
        if (context.declaring.nodeForExactSpan(binding.rhs_first, binding.rhs_last)) |rhs| {
            if (try self.diagnosticBorrowedTouchPath(tree, rhs, name, context, depth + 1)) |path|
                base = .{ .path = path.path, .precise = path.precise };
        }
        if (!binding.is_const)
            try self.diagnosticReboundTouches(tree, context.body, binding.name_token, token, name, context, &base, depth + 1);
        const source = base orelse return null;
        if (binding.origin == .loop_capture or !source.precise) return .{ .path = source.path, .precise = false };
        const relative = (try self.diagnosticOutputPath(tree, node, root_name, 0)) orelse
            return .{ .path = source.path, .precise = false };
        if (relative.path.len == 0) return .{ .path = source.path, .precise = relative.precise };
        if (source.path.len == 0) return .{ .path = relative.path, .precise = relative.precise };
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        return .{
            .path = try std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}{s}{s}",
                .{ source.path, if (relative.path[0] == '[') "" else ".", relative.path }),
            .precise = relative.precise,
        };
    }

    fn diagnosticReboundTouches(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, binding_token: Ast.TokenIndex, use_token: Ast.TokenIndex, name: []const u8, context: DiagnosticTouchContext, base: *?DiagnosticTouchPath, depth: u32) SummaryError!void {
        if (depth == 64) {
            base.* = .{ .path = "", .precise = false };
            return;
        }
        try self.chargeNormalCleanupAt(tree, node);
        if (tree.nodeTag(node) == .fn_decl or tree.firstToken(node) >= use_token) return;
        if (tree.nodeTag(node) == .assign) {
            const target, const value = tree.nodeData(node).node_and_node;
            if (tree.nodeTag(target) == .identifier) {
                const token = tree.nodeMainToken(target);
                const binding = context.bindings().findAt(tree.tokenSlice(token), token);
                if (binding != null and binding.?.name_token == binding_token)
                    if (try self.diagnosticBorrowedTouchPath(tree, value, name, context, depth + 1)) |path| {
                        if (base.*) |prior| {
                            if (!std.mem.eql(u8, prior.path, path.path)) base.* = .{ .path = "", .precise = false };
                        } else base.* = path;
                    };
            }
        }
        var children = engine.AstIterator.init(tree, node);
        while (children.next(tree)) |child|
            try self.diagnosticReboundTouches(tree, child, binding_token, use_token, name, context, base, depth + 1);
    }

    fn appendDiagnosticTouch(result: *MethodScalarReads, path: []const u8) bool {
        for (result.fields[0..result.field_count]) |old|
            if (std.mem.eql(u8, old, path)) return true;
        if (result.field_count == result.fields.len) return false;
        result.fields[result.field_count] = path;
        result.field_count += 1;
        return true;
    }

    /// Local induction variables and scalar-counter dereferences already have
    /// source-proven loop recipes. A record member or a free runtime parameter
    /// does not identify the byte that a write will replace.
    fn diagnosticUnprovedIndex(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, context: DiagnosticTouchContext, depth: u32) SummaryError!bool {
        if (depth == 64) return true;
        try self.chargeNormalCleanupAt(tree, node);
        switch (tree.nodeTag(node)) {
            .field_access => return true,
            .identifier => {
                const token = tree.nodeMainToken(node);
                const binding = (context.bindings().findAt(tree.tokenSlice(token), token) orelse return true).*;
                if (!binding.is_const and
                    try self.diagnosticIndexRebound(tree, context.body, binding.name_token, token, context, depth + 1)) return true;
                switch (binding.origin) {
                    .param => return true,
                    .literal, .loop_capture => return false,
                    else => {
                        if (diagnosticCountdownIndex(tree, context.body, binding.name, token, 0)) return false;
                        const value = context.declaring.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return true;
                        return self.diagnosticUnprovedIndex(tree, value, context, depth + 1);
                    },
                }
            },
            .deref, .number_literal => return false,
            else => {
                var children = engine.AstIterator.init(tree, node);
                while (children.next(tree)) |child|
                    if (try self.diagnosticUnprovedIndex(tree, child, context, depth + 1)) return true;
                return false;
            },
        }
    }

    fn diagnosticIndexRebound(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, binding_token: Ast.TokenIndex, use_token: Ast.TokenIndex, context: DiagnosticTouchContext, depth: u32) SummaryError!bool {
        if (depth == 64) return true;
        try self.chargeNormalCleanupAt(tree, node);
        if (tree.nodeTag(node) == .fn_decl or tree.firstToken(node) >= use_token) return false;
        switch (tree.nodeTag(node)) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
            .assign_shl, .assign_shr, .assign_bit_and, .assign_bit_or, .assign_bit_xor,
            .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap,
            .assign_add_sat, .assign_sub_sat, .assign_mul_sat, .assign_shl_sat,
            => {
                const target, const value = tree.nodeData(node).node_and_node;
                if (tree.nodeTag(target) == .identifier) {
                    const token = tree.nodeMainToken(target);
                    const binding = context.bindings().findAt(tree.tokenSlice(token), token);
                    if (binding != null and binding.?.name_token == binding_token and
                        try self.diagnosticUnprovedIndex(tree, value, context, depth + 1)) return true;
                }
            },
            else => {},
        }
        var children = engine.AstIterator.init(tree, node);
        while (children.next(tree)) |child|
            if (try self.diagnosticIndexRebound(tree, child, binding_token, use_token, context, depth + 1)) return true;
        return false;
    }

    /// A decrement-before-store countdown places writes in a visible prefix,
    /// even when an early exit prevents an initialization certificate.
    fn diagnosticCountdownIndex(tree: *const Ast, node: Ast.Node.Index, name: []const u8, use_token: Ast.TokenIndex, depth: u32) bool {
        if (depth == 64 or tree.nodeTag(node) == .fn_decl) return false;
        if (tree.fullWhile(node)) |loop| {
            if (tree.firstToken(loop.ast.then_expr) <= use_token and tree.lastToken(loop.ast.then_expr) >= use_token and
                tree.nodeTag(loop.ast.cond_expr) == .greater_than)
            {
                const index, const zero = tree.nodeData(loop.ast.cond_expr).node_and_node;
                if (tree.nodeTag(index) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(index)), name) and
                    tree.nodeTag(zero) == .number_literal and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(zero)), "0"))
                {
                    var statements = engine.AstIterator.init(tree, loop.ast.then_expr);
                    if (statements.next(tree)) |step| if (tree.nodeTag(step) == .assign_sub) {
                        const target, const one = tree.nodeData(step).node_and_node;
                        if (tree.nodeTag(target) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(target)), name) and
                            tree.nodeTag(one) == .number_literal and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(one)), "1"))
                            return true;
                    };
                }
            }
        }
        var children = engine.AstIterator.init(tree, node);
        while (children.next(tree)) |child|
            if (diagnosticCountdownIndex(tree, child, name, use_token, depth + 1)) return true;
        return false;
    }

    fn diagnosticOpaqueValue(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, context: DiagnosticTouchContext, depth: u32) SummaryError!bool {
        if (depth == 64) return true;
        var call_buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &call_buffer, node)) |call| {
            const canonical = (try context.declaring.actualCallSummaryAt(call.queryToken(tree, node), context.frame)) orelse return true;
            if (tokens.bodyOf(canonical.callee.tree, canonical.callee.declaration) == null) return true;
            // Reaching a source body is not itself a usable value recipe.
            // Explicit negative returns remain represented by source replay.
            return try context.declaring.diagnosticReturnSeed(canonical, context.frame) != .present;
        }
        if (tree.nodeTag(node) == .identifier) {
            const token = tree.nodeMainToken(node);
            const spelling = tree.tokenSlice(token);
            for ([_][]const u8{ "undefined", "null", "true", "false" }) |literal|
                if (std.mem.eql(u8, spelling, literal)) return false;
            const binding = (context.bindings().findAt(spelling, token) orelse return true).*;
            if (binding.origin == .param or binding.origin == .loop_capture) return false;
            const value = context.declaring.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return true;
            return self.diagnosticOpaqueValue(tree, value, context, depth + 1);
        }
        if (tree.builtinCallParams(&call_buffer, node) != null) return true;
        var children = engine.AstIterator.init(tree, node);
        while (children.next(tree)) |child|
            if (try self.diagnosticOpaqueValue(tree, child, context, depth + 1)) return true;
        return false;
    }

    fn collectDiagnosticOutputTouches(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, name: []const u8, result: *MethodScalarReads, context: DiagnosticTouchContext, depth: u32) SummaryError!bool {
        if (depth == 64) return false;
        try self.chargeNormalCleanupAt(tree, node);
        const tag = tree.nodeTag(node);
        const assignment = switch (tag) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
            .assign_shl, .assign_shr, .assign_bit_and, .assign_bit_or, .assign_bit_xor,
            .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap,
            .assign_add_sat, .assign_sub_sat, .assign_mul_sat, .assign_shl_sat,
            => true,
            else => false,
        };
        if (assignment) {
            const target, const value = tree.nodeData(node).node_and_node;
            if (tree.nodeTag(target) != .identifier) {
                if (try self.diagnosticTouchPath(tree, target, name, context, 0)) |path| {
                    const literal_undefined = tree.nodeTag(value) == .identifier and
                        std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(value)), "undefined");
                    var unproved_index = false;
                    var targets = engine.AstIterator.init(tree, target);
                    if (tree.nodeTag(target) == .array_access) {
                        unproved_index = try self.diagnosticUnprovedIndex(tree, tree.nodeData(target).node_and_node[1], context, 0);
                    }
                    while (targets.next(tree)) |child| {
                        if (tree.nodeTag(child) != .array_access) continue;
                        unproved_index = unproved_index or try self.diagnosticUnprovedIndex(tree, tree.nodeData(child).node_and_node[1], context, 0);
                    }
                    const opaque_value = try self.diagnosticOpaqueValue(tree, value, context, 0);
                    const mutable_value = if (tree.nodeTag(value) == .identifier) mutable: {
                        const token = tree.nodeMainToken(value);
                        const binding = context.bindings().findAt(tree.tokenSlice(token), token) orelse break :mutable false;
                        break :mutable binding.origin != .param and !binding.is_const;
                    } else false;
                    const selected_value = tree.nodeTag(value) == .array_access;
                    if (tag == .assign and !literal_undefined and (unproved_index or opaque_value or (path.precise and (mutable_value or selected_value))))
                        if (!appendDiagnosticTouch(result, path.path)) return false;
                    return self.collectDiagnosticOutputTouches(tree, value, name, result, context, depth + 1);
                }
            }
            // Storing an exposed pointer into other storage escapes its source.
            // The subsequent opaque mutation cannot retain old byte witnesses.
            if (tree.nodeTag(target) != .identifier)
                if ((try self.diagnosticBorrowedTouchPath(tree, value, name, context, 0)) != null)
                    if (!appendDiagnosticTouch(result, "")) return false;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &buffer, node)) |call| {
            const receiver: ?Ast.Node.Index = if (tree.nodeTag(call.ast.fn_expr) == .field_access)
                tree.nodeData(call.ast.fn_expr).node_and_token[0] else null;
            for (0..call.ast.params.len + @as(usize, @intFromBool(receiver != null))) |ordinal| {
                const argument = if (ordinal < call.ast.params.len) call.ast.params[ordinal] else receiver.?;
                const path = (try self.diagnosticBorrowedTouchPath(tree, argument, name, context, 0)) orelse continue;
                const touches = try context.declaring.diagnosticOutputTouchesAt(call.queryToken(tree, node), context.frame, argument);
                const paths = if (touches) |*scope| scope.fields[0..scope.field_count] else {
                    // An opaque callee can recover the enclosing object from
                    // a field address. Unknown scope is not a leaf-only write.
                    if (!appendDiagnosticTouch(result, "")) return false;
                    continue;
                };
                for (paths) |child| {
                    if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
                    const selected = if (!path.precise or child.len == 0) path.path else if (path.path.len == 0) child else
                        try std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}{s}{s}",
                            .{ path.path, if (child[0] == '[') "" else ".", child });
                    if (!appendDiagnosticTouch(result, selected)) return false;
                }
            }
            return true;
        }
        if (tree.builtinCallParams(&buffer, node)) |arguments| {
            const builtin = tree.tokenSlice(tree.nodeMainToken(node));
            for ([_][]const u8{ "@memcpy", "@memset", "@atomicStore", "@atomicRmw", "@cmpxchgStrong", "@cmpxchgWeak" }) |writer| {
                if (!std.mem.eql(u8, builtin, writer)) continue;
                // No independent bulk/atomic byte recipe was published here.
                // A reachable destination abstains instead of claiming empty.
                for (arguments) |argument|
                    if ((try self.diagnosticTouchPath(tree, argument, name, context, 0)) != null) return false;
            }
        }
        if (tag == .field_access or tag == .array_access or tag == .deref or tag == .address_of) {
            if (tokens.rootIdentifier(tree, node)) |root|
                if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(root)), name)) return true;
        }
        var children = engine.AstIterator.init(tree, node);
        while (children.next(tree)) |child|
            if (!try self.collectDiagnosticOutputTouches(tree, child, name, result, context, depth + 1)) return false;
        return true;
    }

    /// Reuse the raw method-address mapping even when it proves no write.
    /// Every formal occurrence must select inline scalar bytes, a fixed-array
    /// element, or scalar dereference. Unknown pointees supply no byte fact.
    /// Calls, escapes and unsupported bodies abstain.
    pub fn methodScalarReadsAt(self: *FileCache, operand_token: Ast.TokenIndex) SummaryError!?MethodScalarReads {
        if (self.address_uses == null) self.address_uses = try self.buildAddressUses();
        const use = self.address_uses.?.get(operand_token) orelse return null;
        if (!use.receiver) return null;
        const call_node = use.call_node orelse return null;
        _ = self.zls orelse return null;
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        try self.enterNormalCleanup(call_node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanup(call_node);
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.tree, &call_buffer, call_node) orelse return null;
        const canonical = (try self.actualCallSummaryAt(call.queryToken(self.tree, call_node), self.cleanup_frame)) orelse return null;
        return self.scalarReadsForUse(use, call_node, canonical, false);
    }

    fn scalarReadsForUse(self: *FileCache, use: AddressUse, call_node: Ast.Node.Index, canonical: ActualCallSummary, by_value: bool) SummaryError!?MethodScalarReads {
        const resolver = self.zls orelse return null;
        var call_buffer: [2]Ast.Node.Index = undefined;
        const tree = canonical.callee.tree;
        if (tree.nodeTag(canonical.callee.declaration) != .fn_decl) return null;
        const body = tokens.bodyOf(tree, canonical.callee.declaration) orelse return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return null;
        var parameters = proto.iterate(tree);
        var parameter_index: u32 = 0;
        var parameter_token: ?Ast.TokenIndex = null;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            const argument = (try canonical.callArgumentFor(self, &call_buffer, parameter_index)) orelse continue;
            if (argument != use.operand) continue;
            parameter_token = parameter.name_token orelse return null;
            break;
        }
        const name = tree.tokenSlice(parameter_token orelse return null);
        const formal_types = canonical.callee.reference.actual_type.data.function.parameters;
        if (parameter_index >= formal_types.len) return null;
        const formal = (try resolver.normalizedType(formal_types[parameter_index].type)) orelse return null;
        const pointee = if (by_value) formal else pointer: {
            if (resolver.pointerSize(formal) != .one) return null;
            break :pointer (try resolver.normalizedType(resolver.childType(formal) orelse return null)) orelse return null;
        };
        const value_tag = resolver.typeTag(pointee) orelse return null;
        if (value_tag != .@"struct" and !(by_value and value_tag == .array)) return null;

        // The caller path must also stay in inline storage. Pointer-valued
        // places need alias/payload facts this field-only certificate lacks.
        const caller_frame = canonical.callee.caller_frame orelse resolver.resolutionFrame();
        var receiver_node = use.operand;
        var receiver_depth: usize = 0;
        while (true) {
            try self.chargeNormalCleanup(call_node);
            const actual = (try caller_frame.typeOfNode(receiver_node)) orelse return null;
            const normalized = (try resolver.normalizedType(actual)) orelse return null;
            if (resolver.typeTag(normalized) != .@"struct" and
                !(by_value and resolver.typeTag(normalized) == .array)) return null;
            switch (self.tree.nodeTag(receiver_node)) {
                .identifier => break,
                .field_access => {
                    if (receiver_depth == 128) return null;
                    receiver_depth += 1;
                    const base, const selector = self.tree.nodeData(receiver_node).node_and_token;
                    if (std.mem.startsWith(u8, self.tree.tokenSlice(selector), "@\"")) return null;
                    receiver_node = base;
                },
                else => return null,
            }
        }

        var key = resolvedCleanupKey(canonical.callee.reference, canonical.callee.declaration);
        key.demand = .{ .one = parameter_index };
        if (self.method_scalar_reads.get(key)) |fields| {
            var cached: MethodScalarReads = .{ .receiver = use.operand, .field_count = fields.len };
            @memcpy(cached.fields[0..fields.len], fields);
            return cached;
        }
        if (self.method_scalar_reads_visiting.contains(key)) return null;
        try self.method_scalar_reads_visiting.put(self.gpa, key, {});
        defer _ = self.method_scalar_reads_visiting.remove(key);

        var result: MethodScalarReads = .{ .receiver = use.operand };
        var occurrences: usize = 0;
        var frames: [FileCache.max_address_use_frames]engine.AstIterator = undefined;
        frames[0] = engine.AstIterator.init(tree, body);
        var depth: usize = 1;
        while (depth != 0) {
            const node = frames[depth - 1].next(tree) orelse {
                depth -= 1;
                continue;
            };
            try self.chargeNormalCleanup(call_node);
            const tag = tree.nodeTag(node);
            if (tag == .field_access or tag == .array_access or tag == .deref) {
                const root = tokens.rootIdentifier(tree, node) orelse return null;
                if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(root)), name)) {
                    const path = (try self.methodScalarReadPath(tree, node, pointee, call_node)) orelse return null;
                    occurrences += 1;
                    var present = false;
                    for (result.fields[0..result.field_count]) |field| {
                        if (std.mem.eql(u8, field, path)) {
                            present = true;
                            break;
                        }
                    }
                    if (!present) {
                        if (result.field_count == result.fields.len) return null;
                        result.fields[result.field_count] = path;
                        result.field_count += 1;
                    }
                    continue;
                }
            }
            switch (tag) {
                .identifier => if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name)) return null,
                .block,
                .block_semicolon,
                .block_two,
                .block_two_semicolon,
                .@"return",
                .field_access,
                .grouped_expression,
                .number_literal,
                .char_literal,
                .enum_literal,
                .bool_not,
                .negation,
                .bit_not,
                .add,
                .sub,
                .mul,
                .div,
                .mod,
                .equal_equal,
                .bang_equal,
                .less_than,
                .less_or_equal,
                .greater_than,
                .greater_or_equal,
                .bool_and,
                .bool_or,
                => {},
                .if_simple, .@"if" => {
                    const branch = tree.fullIf(node) orelse return null;
                    if (branch.payload_token != null) return null;
                },
                .assign => {
                    const lhs = tree.nodeData(node).node_and_node[0];
                    if (!by_value or tree.nodeTag(lhs) != .identifier or
                        !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(lhs)), "_")) return null;
                },
                else => return null,
            }
            if (depth == frames.len) return null;
            frames[depth] = engine.AstIterator.init(tree, node);
            depth += 1;
        }
        // Includes declarations/captures the AST iterator does not expose as
        // identifier expressions. Such an occurrence cannot escape the proof.
        var token = tree.firstToken(body);
        const last = tree.lastToken(body);
        while (token <= last) : (token += 1) {
            try self.chargeNormalCleanup(call_node);
            if (tree.tokenTag(token) != .identifier or !std.mem.eql(u8, tree.tokenSlice(token), name)) continue;
            if (occurrences == 0) return null;
            occurrences -= 1;
        }
        if (occurrences != 0 or result.field_count == 0) return null;
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        const fields = try self.summary_arena.?.allocator().dupe([]const u8, result.fields[0..result.field_count]);
        try self.method_scalar_reads.put(self.gpa, key, fields);
        return result;
    }

    fn methodScalarReadPath(
        self: *FileCache,
        tree: *const Ast,
        node: Ast.Node.Index,
        pointee: TypeResolver.ActualType,
        call_node: Ast.Node.Index,
    ) SummaryError!?[]const u8 {
        const resolver = self.zls orelse return null;
        var selectors: [128]Ast.TokenIndex = undefined;
        var count: usize = 0;
        var current = node;
        const pointer_header = tree.nodeTag(current) == .deref;
        var selected_index: ?u64 = null;
        if (pointer_header) {
            current = tree.nodeData(current).node;
        } else if (tree.nodeTag(current) == .array_access) {
            const base, const index = tree.nodeData(current).node_and_node;
            if (tree.nodeTag(index) != .number_literal) return null;
            selected_index = std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(index)), 0) catch return null;
            current = base;
        }
        while (tree.nodeTag(current) == .field_access) {
            if (count == selectors.len) return null;
            const base, const selector = tree.nodeData(current).node_and_token;
            selectors[count] = selector;
            count += 1;
            current = base;
        }
        if (tree.nodeTag(current) != .identifier or (count == 0 and selected_index == null)) return null;
        var actual = pointee;
        var path: ?[]const u8 = null;
        while (count != 0) {
            count -= 1;
            try self.chargeNormalCleanup(call_node);
            const owner = (try resolver.normalizedType(actual)) orelse return null;
            if (resolver.typeTag(owner) != .@"struct" or owner.data != .container) return null;
            const container = owner.data.container.scope_handle;
            const field_tree = &container.handle.document.tree;
            var buffer: [2]Ast.Node.Index = undefined;
            const declaration = field_tree.fullContainerDecl(&buffer, container.toNode()) orelse return null;
            const field_name = tree.tokenSlice(selectors[count]);
            // Quoted components need the consumer's field-name codec. Until
            // that representation is shared, do not issue a mismatched key.
            if (std.mem.startsWith(u8, field_name, "@\"")) return null;
            var selected: ?TypeResolver.ActualType = null;
            const frame = resolver.frameForContainer(owner.data.container);
            for (declaration.ast.members) |member| {
                const field = field_tree.fullContainerField(member) orelse continue;
                if (!std.mem.eql(u8, field_tree.tokenSlice(field.ast.main_token), field_name)) continue;
                if (field.ast.tuple_like) return null;
                selected = try frame.typeOfNode(field.ast.type_expr.unwrap() orelse return null);
                break;
            }
            actual = selected orelse return null;
            path = if (path) |prefix| joined: {
                if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
                break :joined try std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}.{s}", .{ prefix, field_name });
            } else field_name;
        }
        var scalar = (try resolver.normalizedType(actual)) orelse return null;
        if (pointer_header) {
            if (resolver.pointerSize(scalar) != .one) return null;
            const pointee_value = (try resolver.normalizedType(resolver.childType(scalar) orelse return null)) orelse return null;
            switch (resolver.typeTag(pointee_value) orelse return null) {
                .int, .comptime_int, .float, .comptime_float, .bool, .@"enum" => {
                    if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
                    return try std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}.*", .{path orelse return null});
                },
                // A partial aggregate pointee is transported, not selected.
                else => return path,
            }
        }
        if (selected_index) |index| {
            if (resolver.typeTag(scalar) != .array) return null;
            scalar = (try resolver.normalizedType(resolver.childType(scalar) orelse return null)) orelse return null;
            if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
            path = try std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}[{d}]", .{ path orelse "", index });
        }
        switch (resolver.typeTag(scalar) orelse return null) {
            .int, .comptime_int, .float, .comptime_float, .bool, .@"enum" => return path,
            else => return null,
        }
    }

    /// Prove the actual callee's returned value with the ordinary CFG transfer
    /// and solver. This is conditional on all runtime formal values being
    /// defined: consumers must retain their actual value dependencies.
    pub fn callResultDefinedAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) anyerror!bool {
        return self.callResultValueAt(token, caller_frame, false, null);
    }

    pub fn callResultFieldMayBeUndefinedAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
        field: []const u8,
    ) anyerror!bool {
        const verdict = (try self.diagnosticReturnVerdictAt(token, caller_frame)) orelse return false;
        for (verdict.bytes.items) |mask| {
            if (mask.mayBeUndefined(field)) return true;
        }
        return false;
    }

    /// Whole-value undefined origin requires every reached return to retain
    /// it. A partial aggregate or an unknown alternative is not `.undef`.
    pub fn callResultIsUndefinedAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) anyerror!bool {
        const verdict = (try self.diagnosticReturnVerdictAt(token, caller_frame)) orelse return false;
        return verdict.all_undefined;
    }

    /// Borrowed negative byte masks from the existing settled replay.
    /// They convey no value, payload, or lifetime certificate.
    pub fn callResultUndefinedBytesAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) anyerror![]const worklist_mod.UndefinedReturnBytes {
        const verdict = (try self.diagnosticReturnVerdictAt(token, caller_frame)) orelse return &.{};
        return if (verdict.may_undefined) verdict.bytes.items else &.{};
    }

    fn returnReplaySyntax(self: *FileCache, callee: ActualCallee) SummaryError!ReturnReplaySyntax {
        const origin = self.cleanup_origin orelse self;
        const key = resolvedCleanupKey(callee.reference, callee.declaration).declaration;
        if (origin.return_replay_syntax.get(key)) |syntax| return syntax;
        const body = tokens.bodyOf(callee.tree, callee.declaration) orelse return .{};
        var syntax: ReturnReplaySyntax = .{};
        var token = callee.tree.firstToken(body);
        const last = callee.tree.lastToken(body);
        while (token <= last) : (token += 1) {
            try self.chargeNormalCleanupAt(callee.tree, body);
            switch (callee.tree.tokenTag(token)) {
                .keyword_defer, .keyword_errdefer => {
                    syntax.has_defer = true;
                    break;
                },
                else => {},
            }
        }
        try origin.return_replay_syntax.put(origin.gpa, key, syntax);
        return syntax;
    }

    pub fn callResultMayBeUndefinedAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) anyerror!bool {
        return if (try self.diagnosticReturnVerdictAt(token, caller_frame)) |verdict| verdict.may_undefined else false;
    }

    /// Select only discriminant bytes; payload verdicts remain unchanged.
    pub fn callResultTagMayBeUndefinedAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) anyerror!bool {
        const verdict = (try self.diagnosticReturnVerdictAt(token, caller_frame)) orelse return false;
        for (verdict.bytes.items) |mask| if (mask.tag_may_undefined) return true;
        return false;
    }

    /// Identity-only record shared with return-value dependency lowering.
    /// This does not add an argument, effect, or definedness certificate.
    pub fn returnCallAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) SummaryError!?ActualCallSummary {
        const frame = caller_frame orelse (self.zls orelse return null).resolutionFrame();
        std.debug.assert(&frame.handle.document.tree == self.tree);
        const key: ReturnCallKey = .{
            .token = token,
            .resolver = frame.resolver,
            .tree = self.tree,
            .module = frame.handle.module,
            .callable = frame.actual_type,
            .container = frame.container_type,
        };
        if (self.return_calls.get(key)) |record| return record;
        const callee = callee: {
            // An explicit ordinary frame asks the same query as null.
            // Reuse only a completed token memo; contextual frames stay separate.
            if (self.zls) |resolver| {
                if (frame.resolver == resolver and frame.handle.eql(resolver.handle) and
                    frame.actual_type == null and frame.container_type == null)
                {
                    if (self.actual_callees.get(token)) |cached| break :callee cached;
                }
            }
            break :callee try grow_analysis_mod.actualCalleeOf(self, token, caller_frame);
        };
        var record: ?ActualCallSummary = if (callee) |actual| .{
            .callee = actual,
            .summary = null,
            .argument_offset = null,
            .read_only = null,
        } else null;
        if (record) |*actual| actual.callee.caller_frame = caller_frame;
        try self.return_calls.put(self.gpa, key, record);
        return record;
    }

    fn diagnosticReturnVerdictAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) anyerror!?*const ReturnValueVerdict {
        const canonical = (try self.returnCallAt(token, caller_frame)) orelse return null;
        const origin = self.cleanup_origin orelse self;
        const key = resolvedCleanupKey(canonical.callee.reference, canonical.callee.declaration);
        // A positive replay can retain uncertified scratch dependencies.
        // It does not authorize a negative result that the source gate rejects.
        if (origin.return_defined_summaries.getPtr(key)) |verdict| {
            if (!verdict.may_undefined) return verdict;
        }
        // Eligibility, generic replay and actual-selected replay spend one
        // query allowance. Selection must not refresh a spent cleanup budget.
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        if (try self.diagnosticReturnSeed(canonical, caller_frame) != .present) return null;
        // Seed resolution can rehash the map: borrow its verdict only now.
        if (!origin.return_defined_summaries.contains(key))
            _ = try self.callResultValueAt(token, caller_frame, true, &canonical);
        const generic = origin.return_defined_summaries.getPtr(key) orelse return null;
        if (!generic.may_undefined) return generic;
        const frame = caller_frame orelse (self.zls orelse return null).resolutionFrame();
        const actual_key: ReturnCallKey = .{
            .token = token, .resolver = frame.resolver, .tree = self.tree,
            .module = frame.handle.module, .callable = frame.actual_type, .container = frame.container_type,
        };
        if (origin.diagnostic_return_summaries.getPtr(actual_key)) |verdict| return verdict;
        var integers: std.ArrayListUnmanaged(DiagnosticIntegerBinding) = .empty;
        defer integers.deinit(origin.gpa);
        try self.collectDiagnosticActualIntegers(canonical, frame, &integers);
        if (integers.items.len == 0) return origin.return_defined_summaries.getPtr(key);
        _ = try self.replayCallResultValueAt(token, caller_frame, true, &canonical, .{
            .key = actual_key, .integers = integers.items,
        });
        // An unfinished selected replay proves neither the generic path nor
        // safety for this actual call. Its result remains silent UNKNOWN.
        return origin.diagnostic_return_summaries.getPtr(actual_key);
    }

    fn collectDiagnosticActualIntegers(
        self: *FileCache,
        canonical: ActualCallSummary,
        frame: TypeResolver.ResolutionFrame,
        integers: *std.ArrayListUnmanaged(DiagnosticIntegerBinding),
    ) anyerror!void {
        const tree = canonical.callee.tree;
        const declaring = (try canonical.declaringCache(self)) orelse return;
        const resolver = declaring.zls orelse return;
        const formals = canonical.callee.reference.actual_type.data.function.parameters;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return;
        const body = tokens.bodyOf(tree, canonical.callee.declaration) orelse return;
        var parameters = proto.iterate(tree);
        var ordinal: u32 = 0;
        while (parameters.next()) |parameter| : (ordinal += 1) {
            const name_token = parameter.name_token orelse continue;
            if (ordinal >= formals.len) break;
            const formal = (try resolver.normalizedType(formals[ordinal].type)) orelse continue;
            const tag = resolver.typeTag(formal) orelse continue;
            if (tag != .int and tag != .comptime_int) continue;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try canonical.callArgumentFor(self, &argument_buffer, ordinal)) orelse continue;
            const stable = (try self.diagnosticStableIntegerActual(argument, canonical.callee.call_node)) orelse continue;
            const actual_type = (try frame.typeOfNode(argument)) orelse continue;
            const normalized_actual = (try frame.resolver.normalizedType(actual_type)) orelse continue;
            const actual_tag = frame.resolver.typeTag(normalized_actual) orelse continue;
            if (actual_tag != .int and actual_tag != .comptime_int) continue;
            if (tag == .int) {
                const index = formal.ipIndex() orelse continue;
                const info = resolver.ctx.ip.intInfo(index, @import("builtin").target);
                const digits = info.bits - @intFromBool(info.signedness == .signed and info.bits != 0);
                if (digits < 64 and stable >= (@as(u64, 1) << @intCast(digits))) continue;
            }
            // The immutable source expression is the value proof. Resolution
            // must authenticate the scalar type, not invent an IP value for a
            // typed const alias. Cross-check a value when one is available.
            if (try frame.resolveValueOfNode(argument)) |actual| {
                if (actual.is_type_val) continue;
                if (actual.ipIndex()) |index| switch (frame.resolver.ctx.ip.indexToKey(index)) {
                    .int_u64_value => |known| if (known.int != stable) continue,
                    .int_i64_value => |known| if (known.int < 0 or @as(u64, @intCast(known.int)) != stable) continue,
                    else => {},
                };
            }
            // Reuse the body's lexical escape census. Discarding an address
            // does not mutate a formal; every non-discarded scalar alias makes
            // the caller constant unavailable for this replay.
            const roots = try declaring.escapeRoots(body);
            const escaped = for (roots.addressed) |name| {
                if (std.mem.eql(u8, name, tree.tokenSlice(name_token))) break true;
            } else false;
            if (escaped) continue;
            try integers.append((self.cleanup_origin orelse self).gpa, .{
                .parameter_byte = tree.tokenStart(name_token), .value = stable,
            });
        }
    }

    fn diagnosticStableIntegerActual(self: *FileCache, node: Ast.Node.Index, call_node: Ast.Node.Index) SummaryError!?u64 {
        var evaluator = comptime_fill_mod.Resolver.init(self.gpa, self.tree, self, null);
        defer evaluator.deinit();
        const span: comptime_fill_mod.TokenSpan = .{ .first = self.tree.firstToken(node), .last = self.tree.lastToken(node) };
        const function = self.enclosingFunctionAt(self.tree, span.first) orelse return evaluator.comptimeIntTokens(span, 0);
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buffer, function) orelse return null;
        const body = tokens.bodyOf(self.tree, function) orelse return null;
        const roots = try self.escapeRoots(body);
        const bindings = try self.localBindings(proto, body);
        return self.diagnosticIntegerTokens(&evaluator, bindings, roots.addressed, span, call_node, 0);
    }

    /// Same scalar arithmetic and caps as the fill evaluator, but immutable
    /// aliases are selected by this body's declaration/scope identity. A
    /// same-spelled binding in a sibling function cannot decline or vouch for it.
    fn diagnosticIntegerTokens(
        self: *FileCache,
        evaluator: *const comptime_fill_mod.Resolver,
        bindings: *const local_bindings.LocalBindings,
        escaped: []const []const u8,
        span: comptime_fill_mod.TokenSpan,
        call_node: Ast.Node.Index,
        depth: u32,
    ) SummaryError!?u64 {
        if (depth > 6 or span.first > span.last or span.last >= self.tree.tokens.len or
            span.last - span.first + 1 > 32) return null;
        try self.normalCleanupStorageWork(call_node, span.last - span.first + 1);
        var expression: DiagnosticIntegerEval = .{
            .cache = self, .evaluator = evaluator, .bindings = bindings,
            .escaped = escaped, .call_node = call_node,
            .pos = span.first, .end = span.last, .depth = depth,
        };
        const value = (try expression.expr()) orelse return null;
        return if (expression.pos > expression.end) value else null;
    }

    const DiagnosticIntegerEval = struct {
        cache: *FileCache,
        evaluator: *const comptime_fill_mod.Resolver,
        bindings: *const local_bindings.LocalBindings,
        escaped: []const []const u8,
        call_node: Ast.Node.Index,
        pos: Ast.TokenIndex,
        end: Ast.TokenIndex,
        depth: u32,

        fn expr(self: *DiagnosticIntegerEval) SummaryError!?u64 {
            var value = (try self.term()) orelse return null;
            while (self.pos <= self.end) {
                const tag = self.cache.tree.tokenTag(self.pos);
                if (tag != .plus and tag != .minus) break;
                self.pos += 1;
                const rhs = (try self.term()) orelse return null;
                value = if (tag == .plus)
                    std.math.add(u64, value, rhs) catch return null
                else
                    std.math.sub(u64, value, rhs) catch return null;
            }
            return value;
        }

        fn term(self: *DiagnosticIntegerEval) SummaryError!?u64 {
            var value = (try self.factor()) orelse return null;
            while (self.pos <= self.end and self.cache.tree.tokenTag(self.pos) == .asterisk) {
                self.pos += 1;
                const rhs = (try self.factor()) orelse return null;
                value = std.math.mul(u64, value, rhs) catch return null;
            }
            return value;
        }

        fn factor(self: *DiagnosticIntegerEval) SummaryError!?u64 {
            if (self.pos > self.end) return null;
            const tree = self.cache.tree;
            const token = self.pos;
            switch (tree.tokenTag(token)) {
                .number_literal => {
                    self.pos += 1;
                    return self.evaluator.comptimeIntTokens(.{ .first = token, .last = token }, self.depth);
                },
                .identifier => {
                    self.pos += 1;
                    const name = tree.tokenSlice(token);
                    for (self.escaped) |root| if (std.mem.eql(u8, root, name)) return null;
                    const span: comptime_fill_mod.TokenSpan = if (self.bindings.findAt(name, token)) |binding| local: {
                        if (!binding.is_const or binding.origin == .param or binding.origin == .loop_capture or
                            binding.name_token == 0 or tree.tokenTag(binding.name_token - 1) != .keyword_const or
                            binding.rhs_last >= token) return null;
                        break :local .{ .first = binding.rhs_first, .last = binding.rhs_last };
                    } else global: {
                        // This is the existing scope-indexed immutable lookup,
                        // never a spelling-only scan across foreign declarations.
                        const declaration = self.evaluator.visibleConstDecl(token, name) orelse return null;
                        break :global declaration.spans.?.init;
                    };
                    return self.cache.diagnosticIntegerTokens(
                        self.evaluator, self.bindings, self.escaped, span, self.call_node, self.depth + 1,
                    );
                },
                .l_paren => {
                    if (self.depth == 6) return null;
                    self.pos += 1;
                    self.depth += 1;
                    defer self.depth -= 1;
                    const value = (try self.expr()) orelse return null;
                    if (self.pos > self.end or tree.tokenTag(self.pos) != .r_paren) return null;
                    self.pos += 1;
                    return value;
                },
                else => return null,
            }
        }
    };

    fn diagnosticReturnSeed(
        self: *FileCache,
        canonical: ActualCallSummary,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) SummaryError!SourceEligibility {
        const origin = self.cleanup_origin orelse self;
        const key = resolvedCleanupKey(canonical.callee.reference, canonical.callee.declaration);
        if (origin.return_diagnostic_seeds.get(key)) |seed| return if (seed) .present else .absent;
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        // A root has explored the entire reachable dependency closure. If
        // every leaf is absent, its remaining back edges add no source.
        // Nested cycles still depend on unfinished ancestors and stay open.
        const root_query = origin.return_source_visiting.count() == 0;
        var seed = try self.computeDiagnosticReturnSeed(canonical, caller_frame);
        if (root_query and seed == .cycle) seed = .absent;
        if (seed != .cycle) try origin.return_diagnostic_seeds.put(origin.gpa, key, seed == .present);
        return seed;
    }

    fn computeDiagnosticReturnSeed(
        self: *FileCache,
        canonical: ActualCallSummary,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) SummaryError!SourceEligibility {
        const resolver = if (caller_frame) |frame| frame.resolver else self.zls orelse return .absent;
        const declared = canonical.callee.reference.actual_type.data.function.return_value.*;
        if (try resolver.normalizedType(declared)) |result| {
            if (resolver.typeTag(result)) |tag| switch (tag) {
                .type, .void, .noreturn => return .absent,
                else => {},
            };
        }
        const body = tokens.bodyOf(canonical.callee.tree, canonical.callee.declaration) orelse return .absent;
        return self.returnSourceEligibility(resolver.frameForFunction(canonical.callee.reference), body, true);
    }

    fn returnSourceEligibility(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
        returns: bool,
    ) SummaryError!SourceEligibility {
        return self.sourceEligibility(frame, node, returns, false);
    }

    fn sourceEligibility(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
        returns: bool,
        stores: bool,
    ) SummaryError!SourceEligibility {
        const origin = self.cleanup_origin orelse self;
        const tree = &frame.handle.document.tree;
        const key: ReturnSourceKey = .{
            .frame = .{
                .token = tree.nodeMainToken(node),
                .resolver = frame.resolver,
                .tree = tree,
                .module = frame.handle.module,
                .callable = frame.actual_type,
                .container = frame.container_type,
            },
            .node = node,
            .returns = returns,
            .stores = stores,
        };
        if (origin.return_source_eligibility.get(key)) |answer| return answer;
        if (origin.return_source_visiting.contains(key)) return .cycle;
        try self.enterNormalCleanupAt(tree, node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanupAt(tree, node);
        try origin.return_source_visiting.put(origin.gpa, key, {});
        defer _ = origin.return_source_visiting.remove(key);
        const answer = if (stores)
            try self.storeSourceEligibilityUncached(frame, node, returns)
        else
            try self.returnSourceEligibilityUncached(frame, node, returns);
        if (answer != .cycle) try origin.return_source_eligibility.put(origin.gpa, key, answer);
        return answer;
    }

    /// Store eligibility is independent of return eligibility: void helpers
    /// can write undefined. Parameters and pointees remain unknown.
    fn storeSourceEligibilityUncached(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
        effects: bool,
    ) SummaryError!SourceEligibility {
        const tree = &frame.handle.document.tree;
        const tag = tree.nodeTag(node);
        if (tag == .fn_decl) return .absent;
        if (tree.fullIf(node)) |branch| {
            var answer: SourceEligibility = .absent;
            if (effects) answer = try self.sourceEligibility(frame, branch.ast.cond_expr, true, true);
            if (answer == .present) return answer;
            if (try frame.boolValueOfNode(branch.ast.cond_expr)) |condition| {
                if (condition) return answer.merge(try self.sourceEligibility(frame, branch.ast.then_expr, effects, true));
                const other = branch.ast.else_expr.unwrap() orelse return answer;
                return answer.merge(try self.sourceEligibility(frame, other, effects, true));
            }
            answer = answer.merge(try self.sourceEligibility(frame, branch.ast.then_expr, effects, true));
            if (answer == .present) return answer;
            if (branch.ast.else_expr.unwrap()) |other|
                answer = answer.merge(try self.sourceEligibility(frame, other, effects, true));
            return answer;
        }
        if (!effects) {
            const known = try self.returnSourceEligibility(frame, node, false);
            if (known == .present) return known;
            if (tag == .identifier) {
                const token = tree.nodeMainToken(node);
                const declaration = (try frame.resolver.analyser.lookupSymbolGlobal(
                    frame.handle, tree.tokenSlice(token), tree.tokenStart(token),
                )) orelse return known;
                const declared = switch (declaration.decl) {
                    .ast_node => |value| value,
                    else => return known,
                };
                const owner_tree = &declaration.handle.document.tree;
                const variable = owner_tree.fullVarDecl(declared) orelse return known;
                const initial = variable.ast.init_node.unwrap() orelse return known;
                // A local mutable initializer is a possible source only;
                // settled replay still decides its value at the later store.
                if (!declaration.isConst()) {
                    const actual = frame.actual_type orelse return known;
                    if (actual.data != .function or !declaration.handle.eql(frame.handle)) return known;
                    const function = actual.data.function;
                    const function_decl = (try frame.resolver.analyser.lookupSymbolGlobal(
                        frame.handle, function.name orelse return known, tree.tokenStart(function.fn_token),
                    )) orelse return known;
                    const function_node = switch (function_decl.decl) {
                        .ast_node => |value| value,
                        else => return known,
                    };
                    const body = tokens.bodyOf(tree, function_node) orelse return known;
                    if (owner_tree.firstToken(declared) < tree.firstToken(body) or
                        owner_tree.lastToken(declared) > tree.lastToken(body)) return known;
                }
                const owner: TypeResolver.ResolutionFrame = .{
                    .resolver = frame.resolver,
                    .handle = declaration.handle,
                    .container_type = declaration.container_type orelse
                        if (declaration.handle.eql(frame.handle)) frame.container_type else null,
                    .actual_type = if (declaration.handle.eql(frame.handle)) frame.actual_type else null,
                };
                return known.merge(try self.sourceEligibility(owner, initial, false, true));
            }
            if (tag == .field_access or tag == .array_access) {
                const base = if (tag == .field_access)
                    tree.nodeData(node).node_and_token[0]
                else
                    tree.nodeData(node).node_and_node[0];
                const ty = (try frame.typeOfNode(base)) orelse return known;
                const type_tag = frame.resolver.typeTag(ty) orelse return known;
                if (type_tag != .@"struct" and type_tag != .@"union" and type_tag != .array) return known;
                return known.merge(try self.sourceEligibility(frame, base, false, true));
            }
            var value_buffer: [2]Ast.Node.Index = undefined;
            if (tree.builtinCallParams(&value_buffer, node)) |arguments| {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (arguments.len == 2 and std.mem.eql(u8, name, "@as"))
                    return known.merge(try self.sourceEligibility(frame, arguments[1], false, true));
                if (arguments.len == 1 and
                    (std.mem.eql(u8, name, "@intCast") or std.mem.eql(u8, name, "@floatCast") or
                        std.mem.eql(u8, name, "@bitCast") or std.mem.eql(u8, name, "@truncate")))
                    return known.merge(try self.sourceEligibility(frame, arguments[0], false, true));
                return known;
            }
            switch (tag) {
                .grouped_expression, .@"try", .@"catch", .@"orelse",
                .add, .sub, .mul, .div, .mod, .add_wrap, .sub_wrap, .mul_wrap,
                .add_sat, .sub_sat, .mul_sat, .bit_and, .bit_or, .bit_xor,
                .array_init, .array_init_comma, .array_init_one, .array_init_one_comma,
                .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma,
                .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma,
                .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma,
                => {},
                else => return known,
            }
            var children = engine.AstIterator.init(tree, node);
            var answer = known;
            while (children.next(tree)) |child| {
                answer = answer.merge(try self.sourceEligibility(frame, child, false, true));
                if (answer == .present) return answer;
            }
            return answer;
        }
        if (tree.fullVarDecl(node)) |variable| {
            const initial = variable.ast.init_node.unwrap() orelse return .absent;
            return self.sourceEligibility(frame, initial, true, true);
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.builtinCallParams(&buffer, node)) |arguments| {
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            var answer: SourceEligibility = .absent;
            if (arguments.len == 2 and
                (std.mem.eql(u8, name, "@memset") or std.mem.eql(u8, name, "@memcpy")))
            {
                var source = arguments[1];
                if (std.mem.eql(u8, name, "@memcpy")) {
                    while (tree.nodeTag(source) == .grouped_expression)
                        source = tree.nodeData(source).node_and_token[0];
                    if (tree.nodeTag(source) == .address_of) {
                        const payload = tree.nodeData(source).node;
                        if (try frame.typeOfNode(payload)) |ty| {
                            if (frame.resolver.typeTag(ty) == .array) source = payload;
                        }
                    }
                }
                // The copy reads an addressed array's payload, not its defined
                // pointer header. This grants replay eligibility, not a mask
                // or initialization certificate.
                answer = try self.sourceEligibility(frame, source, false, true);
            }
            for (arguments) |argument| {
                answer = answer.merge(try self.sourceEligibility(frame, argument, true, true));
                if (answer == .present) return answer;
            }
            return answer;
        }
        if (TypeResolver.CallOperands.full(tree, &buffer, node)) |call| {
            const declaring = if (tree == self.tree and frame.handle.module == self.module_id)
                self
            else
                &(try grow_analysis_mod.sourceDocument(self, frame.handle, frame.resolver.ctx)).cache;
            var answer = try self.sourceEligibility(frame, call.ast.fn_expr, true, true);
            if (answer == .present) return answer;
            if (try declaring.returnCallAt(call.queryToken(tree, node), frame)) |canonical| {
                const callee = canonical.callee;
                if (tokens.bodyOf(callee.tree, callee.declaration)) |body|
                    answer = answer.merge(try self.sourceEligibility(frame.resolver.frameForFunction(callee.reference), body, true, true));
            }
            // Unknown effects are not a source. Known effects in actual
            // arguments are still reached before the outer call.
            for (call.ast.params) |argument| {
                answer = answer.merge(try self.sourceEligibility(frame, argument, true, true));
                if (answer == .present) return answer;
            }
            return answer;
        }
        switch (tag) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
            .assign_bit_and, .assign_bit_or, .assign_bit_xor,
            .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap,
            .assign_add_sat, .assign_sub_sat, .assign_mul_sat,
            => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                var answer = try self.sourceEligibility(frame, rhs, false, true);
                if (answer == .present) return answer;
                answer = answer.merge(try self.sourceEligibility(frame, lhs, true, true));
                return answer.merge(try self.sourceEligibility(frame, rhs, true, true));
            },
            .block, .block_semicolon, .block_two, .block_two_semicolon,
            .@"while", .while_simple, .while_cont, .@"for", .for_simple,
            .@"switch", .switch_comma, .switch_case, .switch_case_inline,
            .switch_case_one, .switch_case_inline_one,
            .@"return", .@"break", .@"defer", .@"errdefer",
            .grouped_expression, .@"try", .@"catch", .@"orelse",
            .add, .sub, .mul, .div, .mod, .add_wrap, .sub_wrap, .mul_wrap,
            .add_sat, .sub_sat, .mul_sat, .bit_and, .bit_or, .bit_xor,
            .field_access, .array_access, .deref, .address_of,
            .array_init, .array_init_comma, .array_init_one, .array_init_one_comma,
            .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma,
            .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma,
            .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma,
            => {},
            else => return .absent,
        }
        var children = engine.AstIterator.init(tree, node);
        var answer: SourceEligibility = .absent;
        while (children.next(tree)) |child| {
            answer = answer.merge(try self.sourceEligibility(frame, child, true, true));
            if (answer == .present) return answer;
        }
        return answer;
    }

    /// A clean mutable return needs only sources that can reach its storage.
    /// Escapes and unsupported uses retain the existing whole-body demand.
    fn mutableReturnSourceEligibility(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        body: Ast.Node.Index,
        root: Ast.Node.Index,
    ) SummaryError!SourceEligibility {
        const origin = self.cleanup_origin orelse self;
        const tree = &frame.handle.document.tree;
        const key: ReturnSourceKey = .{
            .frame = .{
                .token = tree.nodeMainToken(body),
                .resolver = frame.resolver,
                .tree = tree,
                .module = frame.handle.module,
                .callable = frame.actual_type,
                .container = frame.container_type,
            },
            .node = body,
            .returns = true,
            .stores = true,
            .mutation_root = root,
        };
        if (origin.return_source_eligibility.get(key)) |answer| return answer;
        if (origin.return_source_visiting.contains(key)) return .cycle;
        try origin.return_source_visiting.put(origin.gpa, key, {});
        defer _ = origin.return_source_visiting.remove(key);
        const answer = (try self.mutableReturnSources(frame, body, root, .value)) orelse
            try self.sourceEligibility(frame, body, true, true);
        if (answer != .cycle) try origin.return_source_eligibility.put(origin.gpa, key, answer);
        return answer;
    }

    const MutableReturnUse = enum { value, target, escape };

    /// The spelling is only a cheap candidate filter. A match is accepted only
    /// for the exact lexical declaration, including shadowed and quoted names.
    fn mutableReturnIdentifier(
        frame: TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
        root: Ast.Node.Index,
    ) SummaryError!?bool {
        const tree = &frame.handle.document.tree;
        if (tree.nodeTag(node) != .identifier) return false;
        const token = tree.nodeMainToken(node);
        const name = tree.tokenSlice(token);
        const variable = tree.fullVarDecl(root) orelse return null;
        const root_name = tree.tokenSlice(variable.ast.mut_token + 1);
        if (!std.mem.eql(u8, name, root_name) and
            !std.mem.startsWith(u8, name, "@\"") and !std.mem.startsWith(u8, root_name, "@\"")) return false;
        const declaration = (try frame.resolver.analyser.lookupSymbolGlobal(
            frame.handle, name, tree.tokenStart(token),
        )) orelse return null;
        return declaration.handle.eql(frame.handle) and switch (declaration.decl) {
            .ast_node => |declared| declared == root,
            else => false,
        };
    }

    fn mutableReturnTarget(
        frame: TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
        root: Ast.Node.Index,
    ) SummaryError!?bool {
        const tree = &frame.handle.document.tree;
        var base = node;
        while (true) switch (tree.nodeTag(base)) {
            .field_access => base = tree.nodeData(base).node_and_token[0],
            .array_access => base = tree.nodeData(base).node_and_node[0],
            .grouped_expression => base = tree.nodeData(base).node_and_token[0],
            .identifier => return mutableReturnIdentifier(frame, base, root),
            else => return false,
        };
    }

    /// Null means an alias, exposure, or unsupported root use: do not publish
    /// an absence from this walk. The caller falls back to whole-body sources.
    fn mutableReturnSources(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
        root: Ast.Node.Index,
        use: MutableReturnUse,
    ) SummaryError!?SourceEligibility {
        const tree = &frame.handle.document.tree;
        try self.enterNormalCleanupAt(tree, node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanupAt(tree, node);
        const tag = tree.nodeTag(node);
        if (tag == .identifier) {
            // The assignment already authenticated this target's base.
            if (use == .target) return .absent;
            const matches = (try mutableReturnIdentifier(frame, node, root)) orelse return null;
            return if (matches and use == .escape) null else .absent;
        }
        if (tree.fullIf(node)) |branch| {
            var answer = (try self.mutableReturnSources(frame, branch.ast.cond_expr, root, use)) orelse return null;
            if (answer == .present) return answer;
            if (try frame.boolValueOfNode(branch.ast.cond_expr)) |condition| {
                if (condition)
                    return answer.merge((try self.mutableReturnSources(frame, branch.ast.then_expr, root, use)) orelse return null);
                const other = branch.ast.else_expr.unwrap() orelse return answer;
                return answer.merge((try self.mutableReturnSources(frame, other, root, use)) orelse return null);
            }
            answer = answer.merge((try self.mutableReturnSources(frame, branch.ast.then_expr, root, use)) orelse return null);
            if (answer == .present) return answer;
            if (branch.ast.else_expr.unwrap()) |other|
                answer = answer.merge((try self.mutableReturnSources(frame, other, root, use)) orelse return null);
            return answer;
        }
        switch (tag) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
            .assign_bit_and, .assign_bit_or, .assign_bit_xor,
            .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap,
            .assign_add_sat, .assign_sub_sat, .assign_mul_sat,
            => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                const rooted = (try mutableReturnTarget(frame, lhs, root)) orelse return null;
                var answer: SourceEligibility = if (rooted)
                    try self.sourceEligibility(frame, rhs, false, true)
                else
                    .absent;
                if (answer == .present) return answer;
                answer = answer.merge((try self.mutableReturnSources(frame, lhs, root, if (rooted) .target else .escape)) orelse return null);
                return answer.merge((try self.mutableReturnSources(frame, rhs, root, .escape)) orelse return null);
            },
            .field_access, .grouped_expression => {
                return self.mutableReturnSources(frame, tree.nodeData(node).node_and_token[0], root, use);
            },
            .array_access => {
                const base, const index = tree.nodeData(node).node_and_node;
                const answer = (try self.mutableReturnSources(frame, base, root, use)) orelse return null;
                if (answer == .present) return answer;
                return answer.merge((try self.mutableReturnSources(frame, index, root, .escape)) orelse return null);
            },
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &buffer, node)) |call| {
            var answer = (try self.mutableReturnSources(frame, call.ast.fn_expr, root, .escape)) orelse return null;
            if (answer == .present) return answer;
            for (call.ast.params) |argument| {
                answer = answer.merge((try self.mutableReturnSources(frame, argument, root, .escape)) orelse return null);
                if (answer == .present) return answer;
            }
            return answer;
        }
        const child_use: MutableReturnUse = switch (tag) {
            .block, .block_semicolon, .block_two, .block_two_semicolon,
            .@"while", .while_simple, .while_cont,
            .@"switch", .switch_comma, .switch_case, .switch_case_inline,
            .switch_case_one, .switch_case_inline_one,
            .@"return", .@"break", .@"defer", .@"errdefer",
            .@"try", .@"catch", .@"orelse",
            .add, .sub, .mul, .div, .mod, .add_wrap, .sub_wrap, .mul_wrap,
            .add_sat, .sub_sat, .mul_sat, .bit_and, .bit_or, .bit_xor,
            .bool_and, .bool_or, .bool_not, .equal_equal, .bang_equal,
            .less_than, .less_or_equal, .greater_than, .greater_or_equal,
            => if (use == .target) .escape else use,
            else => .escape,
        };
        var children = engine.AstIterator.init(tree, node);
        var answer: SourceEligibility = .absent;
        while (children.next(tree)) |child| {
            answer = answer.merge((try self.mutableReturnSources(frame, child, root, child_use)) orelse return null);
            if (answer == .present) return answer;
        }
        return answer;
    }

    fn returnSourceEligibilityUncached(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
        returns: bool,
    ) SummaryError!SourceEligibility {
        const tree = &frame.handle.document.tree;
        const tag = tree.nodeTag(node);
        if (tag == .fn_decl) return .absent;
        if (tag == .@"return") {
            const value = tree.nodeData(node).opt_node.unwrap() orelse return .absent;
            return self.returnSourceEligibility(frame, value, false);
        }
        if (tree.fullIf(node)) |branch| {
            if (try frame.boolValueOfNode(branch.ast.cond_expr)) |condition| {
                if (condition) return self.returnSourceEligibility(frame, branch.ast.then_expr, returns);
                const other = branch.ast.else_expr.unwrap() orelse return .absent;
                return self.returnSourceEligibility(frame, other, returns);
            }
            var answer = try self.returnSourceEligibility(frame, branch.ast.then_expr, returns);
            if (answer == .present) return answer;
            if (branch.ast.else_expr.unwrap()) |other|
                answer = answer.merge(try self.returnSourceEligibility(frame, other, returns));
            return answer;
        }
        if (tree.fullSwitch(node)) |selection| {
            var answer: SourceEligibility = .absent;
            for (selection.ast.cases) |case_node| {
                try self.chargeNormalCleanupAt(tree, case_node);
                const prong = tree.fullSwitchCase(case_node) orelse continue;
                answer = answer.merge(try self.returnSourceEligibility(frame, prong.ast.target_expr, returns));
                if (answer == .present) return answer;
            }
            return answer;
        }
        if (returns) {
            // Visit only the control skeleton that can contain value returns.
            // Do not descend into statements' initializers, operands or calls.
            switch (tag) {
                .block, .block_semicolon, .block_two, .block_two_semicolon,
                .@"while", .while_simple, .while_cont, .@"for", .for_simple,
                .@"switch", .switch_comma, .switch_case, .switch_case_inline,
                .switch_case_one, .switch_case_inline_one, .@"catch", .@"orelse",
                => {},
                else => return .absent,
            }
            var children = engine.AstIterator.init(tree, node);
            var answer: SourceEligibility = .absent;
            while (children.next(tree)) |child| {
                answer = answer.merge(try self.returnSourceEligibility(frame, child, true));
                if (answer == .present) return answer;
            }
            return answer;
        }
        if (tag == .identifier) {
            const token = tree.nodeMainToken(node);
            if (std.mem.eql(u8, tree.tokenSlice(token), "undefined")) return .present;
            const declaration = (try frame.resolver.analyser.lookupSymbolGlobal(
                frame.handle, tree.tokenSlice(token), tree.tokenStart(token),
            )) orelse return .absent;
            const declared = switch (declaration.decl) {
                .ast_node => |value| value,
                .optional_payload => |capture| {
                    if (!declaration.handle.eql(frame.handle)) return .absent;
                    // Admission only: settled replay selects these payload
                    // bytes and decides MAY/ALL without a positive proof.
                    return self.returnSourceEligibility(frame, capture.condition, false);
                },
                else => return .absent,
            };
            const owner_tree = &declaration.handle.document.tree;
            const variable = owner_tree.fullVarDecl(declared) orelse return .absent;
            const initial = variable.ast.init_node.unwrap() orelse return .absent;
            var mutable_body: ?Ast.Node.Index = null;
            if (!declaration.isConst()) {
                if (!declaration.handle.eql(frame.handle)) return .absent;
                if (try frame.enclosingFunctionAt(owner_tree.nodeMainToken(declared))) |local_function| {
                    const reached_function = (try frame.enclosingFunctionAt(token)) orelse return .absent;
                    if (local_function != reached_function) return .absent;
                    mutable_body = tokens.bodyOf(tree, local_function);
                }
            }
            const owner: TypeResolver.ResolutionFrame = .{
                .resolver = frame.resolver,
                .handle = declaration.handle,
                .container_type = declaration.container_type orelse
                    if (declaration.handle.eql(frame.handle)) frame.container_type else null,
                .actual_type = if (declaration.handle.eql(frame.handle)) frame.actual_type else null,
            };
            const initial_source = try self.returnSourceEligibility(owner, initial, false);
            if (initial_source == .present) return initial_source;
            // Later writes can introduce a source into local storage. This
            // only admits replay; settled states must still prove its bytes.
            if (mutable_body) |body|
                return initial_source.merge(try self.mutableReturnSourceEligibility(frame, body, declared));
            return initial_source;
        }
        if (tag == .field_access) {
            const base, const selector = tree.nodeData(node).node_and_token;
            const owner = (try frame.resolveValueOfNode(base)) orelse return .absent;
            if (owner.is_type_val and owner.data == .container) {
                const declaration = (try owner.lookupSymbol(&frame.resolver.analyser, tree.tokenSlice(selector))) orelse return .absent;
                if (!declaration.isConst()) return .absent;
                const declared = switch (declaration.decl) {
                    .ast_node => |value| value,
                    else => return .absent,
                };
                const owner_tree = &declaration.handle.document.tree;
                const variable = owner_tree.fullVarDecl(declared) orelse return .absent;
                const initial = variable.ast.init_node.unwrap() orelse return .absent;
                return self.returnSourceEligibility(frame.resolver.frameForContainer(owner.data.container), initial, false);
            }
            // An inline immutable value can contain a hole. A pointer cannot
            // authenticate the bytes of its pointee.
            const ty = (try frame.typeOfNode(base)) orelse return .absent;
            if (frame.resolver.typeTag(ty) != .@"struct" and
                frame.resolver.typeTag(ty) != .@"union") return .absent;
            return self.returnSourceEligibility(frame, base, false);
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.builtinCallParams(&buffer, node)) |arguments| {
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            // Only value casts forward bytes; type/metadata operands cannot
            // make a call eligible for negative runtime-byte replay.
            if (arguments.len == 2 and std.mem.eql(u8, name, "@as"))
                return self.returnSourceEligibility(frame, arguments[1], false);
            if (arguments.len == 1 and
                (std.mem.eql(u8, name, "@intCast") or std.mem.eql(u8, name, "@floatCast") or
                    std.mem.eql(u8, name, "@bitCast") or std.mem.eql(u8, name, "@truncate") or
                    std.mem.eql(u8, name, "@splat")))
                return self.returnSourceEligibility(frame, arguments[0], false);
            return .absent;
        }
        if (TypeResolver.CallOperands.full(tree, &buffer, node)) |call| {
            const declaring = if (tree == self.tree and frame.handle.module == self.module_id)
                self
            else
                &(try grow_analysis_mod.sourceDocument(self, frame.handle, frame.resolver.ctx)).cache;
            const canonical = (try declaring.returnCallAt(call.queryToken(tree, node), frame)) orelse return .absent;
            return self.diagnosticReturnSeed(canonical, frame);
        }
        if (tree.fullStructInit(&buffer, node)) |literal| {
            var answer: SourceEligibility = .absent;
            for (literal.ast.fields) |value| {
                answer = answer.merge(try self.returnSourceEligibility(frame, value, false));
                if (answer == .present) return answer;
            }
            const ty = if (literal.ast.type_expr == .none)
                (try frame.expectedTypeOfNode(node)) orelse return answer
            else
                (try frame.typeOfNode(node)) orelse return answer;
            var actual = (try frame.resolver.normalizedType(ty)) orelse return answer;
            while (frame.resolver.typeTag(actual) == .optional or
                frame.resolver.typeTag(actual) == .error_union)
            {
                try self.chargeNormalCleanupAt(tree, node);
                actual = (try frame.resolver.normalizedType(frame.resolver.childType(actual) orelse return answer)) orelse return answer;
            }
            if (actual.data != .container) return answer;
            const owner = frame.resolver.frameForContainer(actual.data.container);
            const owner_tree = &owner.handle.document.tree;
            // `literal.ast.fields` may borrow `buffer`; the container needs its own.
            var container_buffer: [2]Ast.Node.Index = undefined;
            const container = owner_tree.fullContainerDecl(&container_buffer, actual.data.container.scope_handle.toNode()) orelse return answer;
            for (container.ast.members) |member| {
                try self.chargeNormalCleanupAt(owner_tree, member);
                const field = owner_tree.fullContainerField(member) orelse continue;
                const initial = field.ast.value_expr.unwrap() orelse continue;
                var supplied = false;
                for (literal.ast.fields) |value| {
                    try self.chargeNormalCleanupAt(tree, value);
                    const first = tree.firstToken(value);
                    if (first >= 3 and tree.tokenTag(first - 1) == .equal and
                        tree.tokenTag(first - 2) == .identifier and tree.tokenTag(first - 3) == .period and
                        std.mem.eql(u8, tree.tokenSlice(first - 2), owner_tree.tokenSlice(field.ast.main_token)))
                    {
                        supplied = true;
                        break;
                    }
                }
                if (supplied) continue;
                answer = answer.merge(try self.returnSourceEligibility(owner, initial, false));
                if (answer == .present) return answer;
            }
            return answer;
        }
        // Value operands only. Addresses, pointees, unknown builtins and
        // mutable declarations are intentionally not negative sources.
        switch (tag) {
            .grouped_expression, .@"try", .@"catch", .@"orelse",
            .add, .sub, .mul, .div, .mod, .add_wrap, .sub_wrap, .mul_wrap,
            .add_sat, .sub_sat, .mul_sat, .bit_and, .bit_or, .bit_xor,
            .array_mult,
            .array_init, .array_init_comma, .array_init_one, .array_init_one_comma,
            .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma,
            => {},
            else => return .absent,
        }
        var children = engine.AstIterator.init(tree, node);
        var answer: SourceEligibility = .absent;
        while (children.next(tree)) |child| {
            answer = answer.merge(try self.returnSourceEligibility(frame, child, false));
            if (answer == .present) return answer;
        }
        return answer;
    }

    fn replayFailureIdle(self: *FileCache) bool {
        return self.summary_visiting.count() == 0 and
            self.resolved_declaration_visiting.count() == 0 and
            self.cleanup_visiting.count() == 0 and
            self.method_scalar_reads_visiting.count() == 0 and
            self.store_value_visiting.count() == 0 and
            self.return_defined_visiting.count() == 0 and
            self.return_source_visiting.count() == 0 and
            self.array_source_visiting.count() == 0 and
            self.fresh_visiting.count() == 0 and
            self.preserving_visiting.count() == 0 and
            self.return_storage_state.active.count() == 0 and
            self.return_storage_state.formal_active.count() == 0 and
            self.cleanup_demand == .all;
    }

    fn replayFailureMemoAllowed(self: *FileCache, declaring: *FileCache) bool {
        if (cleanup_budget.depth != 0 or !self.replayFailureIdle() or
            !declaring.replayFailureIdle()) return false;
        const root = if (self.grow_state) |state| state.owner else self;
        const effects = &root.effects_state;
        if (effects.queries != 0 or effects.depth != 0 or effects.remaining != null or
            effects.global_walk != null or effects.active.count() != 0) return false;
        // A scoped effect answer may have depended on an outer unfinished
        // proof. It must not be transported to another scope by a failure.
        var scoped = effects.scoped.valueIterator();
        while (scoped.next()) |entry| {
            if (entry.epoch == effects.epoch) return false;
        }
        if (self.grow_state) |state| {
            if (state.queries != 0 or state.open != 0 or state.active.count() != 0) return false;
            var documents = state.documents.valueIterator();
            while (documents.next()) |document| {
                if (!document.*.cache.replayFailureIdle()) return false;
            }
        }
        return true;
    }

    /// Completed memo tables are monotone. Count all tables, including new
    /// ones added to these states, but not failures (which prove no fact).
    fn replayMemoTableEntries(state: anytype) usize {
        var total: usize = 0;
        inline for (std.meta.fields(@TypeOf(state.*))) |field| {
            if (comptime std.mem.eql(u8, field.name, "return_replay_failures") or
                std.mem.eql(u8, field.name, "exhausted") or
                // Canonical resolution does not spend the cleanup allowance.
                std.mem.eql(u8, field.name, "return_calls") or
                std.mem.eql(u8, field.name, "actual_callees")) continue;
            if (comptime @typeInfo(field.type) == .@"struct") {
                if (comptime @hasDecl(field.type, "count")) {
                    total += @field(state.*, field.name).count();
                }
            }
        }
        return total;
    }

    fn replayFileMemoEntries(self: *FileCache) usize {
        return replayMemoTableEntries(self) +
            replayMemoTableEntries(&self.alias_state) +
            replayMemoTableEntries(&self.return_storage_state) +
            replayMemoTableEntries(&self.effects_state) +
            self.effects_state.verdict_count +
            self.address_proof_generation + @intFromBool(self.transitive_resolved) +
            (if (self.address_uses) |uses| uses.count() else 0) +
            (if (self.exact_spans) |spans| spans.count() else 0);
    }

    fn replayMemoEntries(self: *FileCache, declaring: *FileCache) usize {
        var total = self.replayFileMemoEntries();
        var has_declaring = declaring == self;
        if (self.grow_state) |state| {
            total += replayMemoTableEntries(state);
            var documents = state.documents.valueIterator();
            while (documents.next()) |document| {
                const cache = &document.*.cache;
                if (cache != self) total += cache.replayFileMemoEntries();
                has_declaring = has_declaring or cache == declaring;
            }
        }
        if (!has_declaring) total += declaring.replayFileMemoEntries();
        return total;
    }

    fn replayFileExhaustedEntries(self: *FileCache) usize {
        return self.alias_state.exhausted.count() + self.effects_state.exhausted.count();
    }

    /// Failure caches can shorten a nested walk too. Keep their stamp separate
    /// so removing a failure and adding a completed fact cannot cancel out.
    fn replayExhaustedEntries(self: *FileCache, declaring: *FileCache) usize {
        var total = self.replayFileExhaustedEntries();
        var has_declaring = declaring == self;
        if (self.grow_state) |state| {
            var documents = state.documents.valueIterator();
            while (documents.next()) |document| {
                const cache = &document.*.cache;
                if (cache != self) total += cache.replayFileExhaustedEntries();
                has_declaring = has_declaring or cache == declaring;
            }
        }
        if (!has_declaring) total += declaring.replayFileExhaustedEntries();
        return total;
    }

    fn callResultValueAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
        diagnostic: bool,
        resolved: ?*const ActualCallSummary,
    ) anyerror!bool {
        return self.replayCallResultValueAt(token, caller_frame, diagnostic, resolved, null);
    }

    fn replayCallResultValueAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
        diagnostic: bool,
        resolved: ?*const ActualCallSummary,
        selected: ?DiagnosticReplay,
    ) anyerror!bool {
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        const canonical = if (resolved) |actual| actual.* else (try self.returnCallAt(token, caller_frame)) orelse return false;
        const origin = self.cleanup_origin orelse self;
        const callee = canonical.callee;
        const key = resolvedCleanupKey(callee.reference, callee.declaration);
        if (selected) |actual| {
            if (origin.diagnostic_return_summaries.get(actual.key)) |verdict| return verdict.may_undefined;
        } else if (origin.return_defined_summaries.get(key)) |verdict|
            return if (diagnostic) verdict.may_undefined else verdict.defined;
        if (origin.return_defined_visiting.contains(key.declaration)) return false;
        const declaring = (try canonical.declaringCache(self)) orelse return false;
        const body = tokens.bodyOf(callee.tree, callee.declaration) orelse return false;
        const failure_key: ReplayFailureKey = .{
            .callee = key,
            .remaining = cleanup_budget.remaining,
            .depth = cleanup_budget.depth,
        };
        const can_memo_failure = selected == null and origin.replayFailureMemoAllowed(declaring);
        const memo_entries = if (can_memo_failure) origin.replayMemoEntries(declaring) else 0;
        const exhausted_entries = if (can_memo_failure) origin.replayExhaustedEntries(declaring) else 0;
        if (can_memo_failure) {
            if (origin.return_replay_failures.get(failure_key)) |failed| {
                if (failed.memo_entries == memo_entries and failed.exhausted_entries == exhausted_entries) {
                    // Preserve the first diagnostic and the raw inner site:
                    // reusing a walk must not move its failure into another file.
                    try declaring.enterNormalCleanup(body);
                    defer declaring.leaveNormalCleanup();
                    cleanup_budget.remaining = failed.remaining;
                    if (replay_failure_site == null) replay_failure_site = failed.site;
                    return budget_mod.fail(failed.diagnostic);
                }
                _ = origin.return_replay_failures.remove(failure_key);
            }
        }
        const guard = if (can_memo_failure) call_summary_mod.PendingGuard.begin() else null;
        const saved_failure_site = replay_failure_site;
        if (can_memo_failure) replay_failure_site = null;
        defer {
            if (guard) |pending| _ = pending.end();
            if (can_memo_failure) replay_failure_site = saved_failure_site;
        }
        errdefer |err| {
            if (can_memo_failure and err == error.AnalysisBudgetExceeded) {
                if (budget_mod.peek()) |failure| {
                    if ((failure.limit == .normal_cleanup_nodes or failure.limit == .normal_cleanup_depth) and
                        origin.replayFailureMemoAllowed(declaring) and
                        origin.replayMemoEntries(declaring) == memo_entries and
                        origin.replayExhaustedEntries(declaring) == exhausted_entries)
                    {
                        if (replay_failure_site) |site| {
                            origin.return_replay_failures.put(origin.gpa, failure_key, .{
                                .site = site,
                                .diagnostic = failure,
                                .remaining = cleanup_budget.remaining,
                                .memo_entries = memo_entries,
                                .exhausted_entries = exhausted_entries,
                            }) catch {};
                        }
                    }
                }
            }
        }
        try declaring.enterNormalCleanup(body);
        defer declaring.leaveNormalCleanup();
        try origin.return_defined_visiting.put(origin.gpa, key.declaration, {});
        defer _ = origin.return_defined_visiting.remove(key.declaration);
        // Deferred mutation remains uncertified. Diagnostic return snapshots
        // still retain bytes evaluated before those actions run.
        const has_defer = (try self.returnReplaySyntax(callee)).has_defer;
        // CFG node IDs belong to the declaring document, not the caller.
        // Keep the callee's actual bindings, but lower with its own resolver.
        const resolver = declaring.zls orelse return false;
        const saved_frame = declaring.cleanup_frame;
        const saved_origin = declaring.cleanup_origin;
        const saved_mode = declaring.return_defined_mode;
        const saved_integers = declaring.diagnostic_actual_integers;
        declaring.diagnostic_actual_integers = if (selected) |actual| actual.integers else &.{};
        defer declaring.diagnostic_actual_integers = saved_integers;
        declaring.cleanup_frame = resolver.frameForFunction(callee.reference);
        declaring.cleanup_origin = origin;
        declaring.return_defined_mode = true;
        defer declaring.cleanup_frame = saved_frame;
        defer declaring.cleanup_origin = saved_origin;
        defer declaring.return_defined_mode = saved_mode;
        var graph = (try cfg_builder_mod.lowerFunctionFullWithZls(
            origin.gpa,
            callee.tree,
            callee.declaration,
            &config_mod.Default,
            declaring,
            resolver,
        )) orelse return false;
        defer graph.deinit(origin.gpa);
        if (selected) |actual| for (graph.blocks) |*block| {
            for (block.stmts) |*statement| {
                if (statement.kind != .decl) continue;
                const local = graph.locals[@intFromEnum(statement.kind.decl.local)];
                for (actual.integers) |binding| if (local.decl_pos.byte == binding.parameter_byte) {
                    statement.kind.decl.integer_value = binding.value;
                    break;
                };
            }
        };
        var problems: std.ArrayListUnmanaged(problem_mod.Problem) = .empty;
        defer {
            for (problems.items) |*problem| problem.deinit(origin.gpa);
            problems.deinit(origin.gpa);
        }
        var defined = true;
        var undefined_value = false;
        var all_undefined = true;
        const parameters = callee.reference.actual_type.data.function.parameters;
        const parameter_locals = try origin.gpa.alloc(?cfg_mod.LocalId, parameters.len);
        defer origin.gpa.free(parameter_locals);
        @memset(parameter_locals, null);
        var parameter_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(callee.tree, &parameter_buffer, callee.declaration) orelse return false;
        var iterator = proto.iterate(callee.tree);
        var ordinal: usize = 0;
        while (iterator.next()) |parameter| : (ordinal += 1) {
            if (ordinal >= parameter_locals.len) break;
            const name = parameter.name_token orelse continue;
            const byte = callee.tree.tokens.items(.start)[name];
            for (graph.locals, 0..) |local, local_index| {
                if (local.decl_pos.byte == byte and (local.is_pointer or local.is_slice)) {
                    parameter_locals[ordinal] = @enumFromInt(local_index);
                    break;
                }
            }
        }
        var stores: std.ArrayListUnmanaged(worklist_mod.UndefinedParameterStore) = .empty;
        var bytes: std.ArrayListUnmanaged(worklist_mod.UndefinedReturnBytes) = .empty;
        errdefer {
            for (bytes.items) |*mask| mask.deinit(origin.gpa);
            bytes.deinit(origin.gpa);
        }
        errdefer {
            for (stores.items) |store| origin.gpa.free(store.path);
            stores.deinit(origin.gpa);
        }
        try worklist_mod.check(origin.gpa, &graph, .{
            .path = budget_mod.documentForTree(callee.tree),
            .return_defined = &defined,
            .return_undefined = &undefined_value,
            .return_all_undefined = &all_undefined,
            .return_bytes = &bytes,
            .parameter_stores = .{ .locals = parameter_locals, .stores = &stores },
            .summary_cache = declaring,
        }, &problems);
        if (has_defer) defined = false;
        const verdict: ReturnValueVerdict = .{
            .defined = selected == null and defined,
            .may_undefined = undefined_value,
            .all_undefined = all_undefined,
            .stores = stores,
            .bytes = bytes,
        };
        if (selected) |actual|
            try origin.diagnostic_return_summaries.put(origin.gpa, actual.key, verdict)
        else
            try origin.return_defined_summaries.put(origin.gpa, key, verdict);
        return if (diagnostic) undefined_value else defined;
    }

    /// A source-proven value dependency, never an initialization certificate.
    /// Projection fields borrow the canonical callee document. Index operands
    /// are mapped into the caller tree, just like the root argument.
    pub const ArrayReturnSource = struct {
        pub const Projection = union(enum) {
            field: []const u8,
            deref,
            index: Ast.Node.Index,
        };
        argument: Ast.Node.Index,
        projections: [64]Projection = undefined,
        projection_count: usize = 0,
    };

    /// Project a selected result through source-defined returns. A mutating
    /// tail return qualifies only when definite stores cover the returned field.
    /// Formal-rooted projections and canonical forwarding calls qualify.
    /// This proves a post-call source, not initializedness, and memoizes no abstention.
    /// An exhausted analysis budget is not an abstention: it propagates.
    pub fn arrayReturnSourceAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
        result_fields: []const []const u8,
    ) SummaryError!?ArrayReturnSource {
        return self.arrayReturnSourceFor(token, caller_frame, result_fields, false);
    }

    /// Locate returned storage for negative byte facts only. This does not
    /// certify the value or require a write to the selected return field.
    pub fn arrayDiagnosticReturnSourceAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
        result_fields: []const []const u8,
    ) SummaryError!?ArrayReturnSource {
        return self.arrayReturnSourceFor(token, caller_frame, result_fields, true);
    }

    fn arrayReturnSourceFor(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
        result_fields: []const []const u8,
        diagnostic: bool,
    ) SummaryError!?ArrayReturnSource {
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        const source = (try self.arrayReturnSourceCallFor(token, caller_frame, diagnostic)) orelse return null;
        var result: ArrayReturnSource = .{ .argument = source.argument };
        if (source.projection_count + result_fields.len > result.projections.len) return null;
        for (source.projections[0..source.projection_count]) |projection| {
            result.projections[result.projection_count] = switch (projection) {
                .field => |field| .{ .field = field },
                .deref => .deref,
                .index => |index| .{ .index = index },
                .address => return null,
            };
            result.projection_count += 1;
        }
        for (result_fields) |field| {
            result.projections[result.projection_count] = .{ .field = field };
            result.projection_count += 1;
        }
        return result;
    }

    /// Addresses exist only while substituting helper arguments. A following
    /// dereference consumes the address; no address escapes the public proof.
    const ArraySource = struct {
        const Projection = union(enum) {
            field: []const u8,
            deref,
            address,
            index: Ast.Node.Index,
        };
        argument: Ast.Node.Index,
        projections: [64]Projection = undefined,
        projection_count: usize = 0,

        fn append(source: *ArraySource, projection: Projection) bool {
            if (projection == .deref and source.projection_count != 0 and
                source.projections[source.projection_count - 1] == .address)
            {
                source.projection_count -= 1;
                return true;
            }
            if (source.projection_count == source.projections.len) return false;
            source.projections[source.projection_count] = projection;
            source.projection_count += 1;
            return true;
        }
    };

    fn arrayReturnSourceCall(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) SummaryError!?ArraySource {
        return self.arrayReturnSourceCallFor(token, caller_frame, false);
    }

    fn arrayReturnSourceCallFor(
        self: *FileCache,
        token: Ast.TokenIndex,
        caller_frame: ?TypeResolver.ResolutionFrame,
        diagnostic: bool,
    ) SummaryError!?ArraySource {
        const canonical = (try self.returnCallAt(token, caller_frame)) orelse return null;
        const declaring = (try canonical.declaringCache(self)) orelse return null;
        const origin = self.cleanup_origin orelse self;
        const declaration = resolvedCleanupKey(canonical.callee.reference, canonical.callee.declaration).declaration;
        if (origin.array_source_visiting.contains(declaration)) return null;
        try origin.array_source_visiting.put(origin.gpa, declaration, {});
        defer _ = origin.array_source_visiting.remove(declaration);
        try self.enterNormalCleanup(canonical.callee.call_node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanup(canonical.callee.call_node);
        const tree = canonical.callee.tree;
        if (tree.nodeTag(canonical.callee.declaration) != .fn_decl) return null;
        const body = tree.nodeData(canonical.callee.declaration).node_and_node[1];
        switch (tree.nodeTag(body)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {},
            else => return null,
        }
        var statements = engine.AstIterator.init(tree, body);
        var statement = statements.next(tree) orelse return null;
        var mutating = false;
        while (statements.next(tree)) |next| {
            mutating = true;
            statement = next;
        }
        if (tree.nodeTag(statement) != .@"return") return null;
        const returned = tree.nodeData(statement).opt_node.unwrap() orelse return null;
        const source = (try self.arrayReturnSourceExpression(canonical, returned)) orelse return null;
        if (!mutating or diagnostic) return source;
        // Mutation coverage needs the real receiver offset; forwarding does
        // not need a body-effect summary.
        const store_canonical = (try self.actualCallSummaryAt(token, caller_frame)) orelse return null;
        // Only a formal-rooted inline field can be related to a mutating
        // caller-visible store. The same must-write proof rejects early
        // returns, missing switch arms and unknown invalidating operations.
        const root = tokens.rootIdentifier(tree, returned) orelse return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return null;
        var parameters = proto.iterate(tree);
        var parameter_index: u32 = 0;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            const name_token = parameter.name_token orelse continue;
            const name = tree.tokenSlice(name_token);
            if (!std.mem.eql(u8, name, tree.tokenSlice(tree.nodeMainToken(root)))) continue;
            var caller: ?DefiniteStoreProof = null;
            const chain = [1]StoreVisit{.{ .tree = tree, .declaration = canonical.callee.declaration }};
            const coverage = (try self.definiteParameterStore(store_canonical, store_canonical.callee.call_node, parameter_index, &caller, &chain)) orelse return null;
            const proof: DefiniteStoreProof = .{
                .tree = tree,
                .frame = (declaring.zls orelse return null).frameForFunction(canonical.callee.reference),
                .call_node = canonical.callee.call_node,
                .call_tree = self.tree,
            };
            const field = (try storeFieldIndex(&proof, name, coverage.field_names[0..coverage.field_count], returned)) orelse return null;
            if (!coverage.covered[field]) return null;
            return source;
        }
        return null;
    }

    fn arrayReturnSourceExpression(
        self: *FileCache,
        canonical: ActualCallSummary,
        node: Ast.Node.Index,
    ) SummaryError!?ArraySource {
        // Walk callee nodes with their own cache and instantiated body frame.
        const declaring = (try canonical.declaringCache(self)) orelse return null;
        try declaring.enterNormalCleanup(node);
        defer declaring.leaveNormalCleanup();
        try declaring.chargeNormalCleanup(node);
        const tree = canonical.callee.tree;
        const resolver = declaring.zls orelse return null;
        const frame = resolver.frameForFunction(canonical.callee.reference);
        const value_type = (try frame.typeOfNode(node)) orelse return null;
        _ = (try resolver.normalizedType(value_type)) orelse return null;
        switch (tree.nodeTag(node)) {
            .identifier => return .{
                .argument = (try self.valueSourceFormalArgument(canonical, node)) orelse return null,
            },
            .grouped_expression => return self.arrayReturnSourceExpression(
                canonical,
                tree.nodeData(node).node_and_token[0],
            ),
            .field_access => {
                const root, const field_token = tree.nodeData(node).node_and_token;
                var source = (try self.arrayReturnSourceExpression(canonical, root)) orelse return null;
                const root_type = (try frame.typeOfNode(root)) orelse return null;
                const normalized = (try resolver.normalizedType(root_type)) orelse return null;
                if (resolver.typeTag(normalized) == .pointer and !source.append(.deref)) return null;
                if (!source.append(.{ .field = tree.tokenSlice(field_token) })) return null;
                return source;
            },
            .deref, .address_of => {
                var source = (try self.arrayReturnSourceExpression(canonical, tree.nodeData(node).node)) orelse return null;
                if (!source.append(if (tree.nodeTag(node) == .deref) .deref else .address)) return null;
                return source;
            },
            .array_access => {
                const root, const index = tree.nodeData(node).node_and_node;
                var source = (try self.arrayReturnSourceExpression(canonical, root)) orelse return null;
                const actual_index = (try self.valueSourceFormalArgument(canonical, index)) orelse return null;
                if (!source.append(.{ .index = actual_index })) return null;
                return source;
            },
            else => {
                var call_buffer: [2]Ast.Node.Index = undefined;
                const call = TypeResolver.CallOperands.full(tree, &call_buffer, node) orelse return null;
                // A sole return is not enough if evaluating an unused actual
                // can mutate storage. Admit only inert argument expressions.
                if (!try declaring.arraySourceInertExpression(call.ast.fn_expr)) return null;
                for (call.ast.params) |argument| {
                    if (!try declaring.arraySourceInertExpression(argument)) return null;
                }
                const nested = (try declaring.arrayReturnSourceCall(call.queryToken(tree, node), frame)) orelse return null;
                var source = (try self.arrayReturnSourceExpression(canonical, nested.argument)) orelse return null;
                for (nested.projections[0..nested.projection_count]) |projection| {
                    const mapped: ArraySource.Projection = switch (projection) {
                        .index => |index| .{
                            .index = (try self.valueSourceFormalArgument(canonical, index)) orelse return null,
                        },
                        else => projection,
                    };
                    if (!source.append(mapped)) return null;
                }
                return source;
            },
        }
    }

    fn arraySourceInertExpression(self: *FileCache, node: Ast.Node.Index) SummaryError!bool {
        try self.enterNormalCleanup(node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanup(node);
        const tree = self.tree;
        return switch (tree.nodeTag(node)) {
            .identifier, .number_literal, .string_literal, .char_literal, .enum_literal => true,
            .grouped_expression, .field_access => self.arraySourceInertExpression(tree.nodeData(node).node_and_token[0]),
            .deref, .address_of => self.arraySourceInertExpression(tree.nodeData(node).node),
            .array_access => blk: {
                const root, const index = tree.nodeData(node).node_and_node;
                break :blk try self.arraySourceInertExpression(root) and
                    try self.arraySourceInertExpression(index);
            },
            else => false,
        };
    }

    fn valueSourceFormalArgument(
        self: *FileCache,
        canonical: ActualCallSummary,
        node: Ast.Node.Index,
    ) SummaryError!?Ast.Node.Index {
        const tree = canonical.callee.tree;
        if (tree.nodeTag(node) != .identifier) return null;
        const name = tree.tokenSlice(tree.nodeMainToken(node));
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return null;
        const declaring = (try canonical.declaringCache(self)) orelse return null;
        var parameters = proto.iterate(tree);
        var index: u32 = 0;
        while (parameters.next()) |parameter| : (index += 1) {
            try declaring.chargeNormalCleanup(node);
            const name_token = parameter.name_token orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(name_token), name)) continue;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            return try canonical.callArgumentFor(self, &argument_buffer, index);
        }
        return null;
    }

    pub fn populateUndefinedAddressStores(self: *FileCache, use: *AddressUse) anyerror!void {
        if (!use.may_write or use.definite_write) return;
        const call_node = use.call_node orelse return;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.tree, &buffer, call_node) orelse return;
        const token = call.queryToken(self.tree, call_node);
        const canonical = (try self.returnCallAt(token, self.cleanup_frame)) orelse return;
        const origin = self.cleanup_origin orelse self;
        const key = resolvedCleanupKey(canonical.callee.reference, canonical.callee.declaration);
        if (!origin.return_defined_summaries.contains(key)) {
            self.beginNormalCleanup();
            defer self.endNormalCleanup();
            const body = tokens.bodyOf(canonical.callee.tree, canonical.callee.declaration) orelse return;
            const resolver = if (canonical.callee.caller_frame) |frame| frame.resolver else self.zls orelse return;
            const seed = try self.sourceEligibility(resolver.frameForFunction(canonical.callee.reference), body, true, true);
            if (seed != .present) return;
            _ = try self.callResultValueAt(token, canonical.callee.caller_frame, true, &canonical);
        }
        const verdict = origin.return_defined_summaries.get(key) orelse return;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration) orelse return;
        var parameters = proto.iterate(canonical.callee.tree);
        var parameter: u32 = 0;
        while (parameters.next() != null) : (parameter += 1) {
            const argument = (try canonical.callArgumentFor(self, &buffer, parameter)) orelse continue;
            if (argument != use.address_node) continue;
            for (verdict.stores.items) |store| {
                if (store.parameter != parameter or use.undefined_field_count == use.undefined_fields.len) continue;
                if (use.success_bool) |wanted| {
                    if (store.on_boolean) |returned| if (returned != wanted) continue;
                }
                use.undefined_fields[use.undefined_field_count] = store.path;
                use.undefined_field_count += 1;
            }
        }
    }

    /// A pointer value passed directly is not an address-of expression.
    /// Apply only proved-undefined stores; this grants no write certificate.
    pub fn pointerArgumentUndefinedUseAt(
        self: *FileCache,
        call_node: Ast.Node.Index,
        argument: Ast.Node.Index,
        success_bool: ?bool,
    ) anyerror!?AddressUse {
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.tree, &buffer, call_node) orelse return null;
        const canonical = (try self.actualCallSummaryAt(call.queryToken(self.tree, call_node), self.cleanup_frame)) orelse return null;
        const declaring = (try canonical.declaringCache(self)) orelse return null;
        const summary = try declaring.summaryOfFn(canonical.callee.declaration);
        var selected: ?u32 = null;
        for (summary.written_paths) |path| {
            const actual = (try canonical.callArgumentFor(self, &buffer, path.param)) orelse continue;
            if (actual == argument) { selected = path.param; break; }
        }
        if (selected == null) return null;
        var use: AddressUse = .{
            .address_node = argument,
            .operand = argument,
            .call_node = call_node,
            .may_write = true,
            .success_bool = success_bool,
        };
        try self.populateUndefinedAddressStores(&use);
        return if (use.undefined_field_count != 0) use else null;
    }

    fn directCElementTarget(
        self: *FileCache,
        canonical: ActualCallSummary,
        parameter: u32,
        actual: Ast.Node.Index,
    ) SummaryError!?struct { index: u64, value_type: TypeResolver.ActualType } {
        const resolver = self.zls orelse return null;
        const formals = canonical.callee.reference.actual_type.data.function.parameters;
        if (parameter >= formals.len) return null;
        const pointer = (try resolver.normalizedType(formals[parameter].type)) orelse return null;
        if (resolver.pointerSize(pointer) != .c) return null;
        const pointee = (try resolver.normalizedType(resolver.childType(pointer) orelse return null)) orelse return null;
        const frame = canonical.callee.caller_frame orelse resolver.resolutionFrame();
        var proof: DefiniteStoreProof = .{ .tree = self.tree, .frame = frame, .call_node = canonical.callee.call_node, .call_tree = self.tree };
        var root = actual;
        var index: u64 = 0;
        var stop: ?u64 = null;
        if (self.tree.nodeTag(actual) == .address_of) {
            root = self.tree.nodeData(actual).node;
        } else if (self.tree.fullSlice(actual)) |slice| {
            root = slice.ast.sliced;
            index = (try definiteStoreInteger(&proof, slice.ast.start)) orelse return null;
            if (slice.ast.end.unwrap()) |end| stop = (try definiteStoreInteger(&proof, end)) orelse return null;
        } else return null;
        if (self.tree.nodeTag(root) != .identifier) return null;
        const raw = (try frame.typeOfNode(root)) orelse return null;
        const array = (try resolver.normalizedType(raw)) orelse return null;
        if (resolver.typeTag(array) != .array) return null;
        const extent = (try definiteStoreArrayCount(&proof, root)) orelse return null;
        if (index >= extent or (stop != null and (stop.? > extent or index >= stop.?))) return null;
        const element = (try resolver.normalizedType(resolver.childType(array) orelse return null)) orelse return null;
        if (!element.eql(pointee)) return null;
        return .{ .index = index, .value_type = element };
    }

    /// Fail closed unless an exact argument reaches a source declaration with
    /// a straight-line complete store. Mutation summaries are may-effects and
    /// cannot establish this must-effect. No declaration spelling is trusted.
    ///
    /// The argument is `&x`, `&x.field`, or the implicit receiver `x` /
    /// `x.field` of an instance call. A callee statement `[try] other(..)`
    /// that hands its own pointer on is followed into `other`'s body, so a
    /// wrapper credits exactly the stores its delegate proves. Only the
    /// success path is credited: an error return is not a store.
    fn definiteAddressWrite(self: *FileCache, use: *AddressUse) SummaryError!bool {
        use.may_written_stores.count = 0;
        if (!use.may_write) return false;
        switch (self.tree.nodeTag(use.operand)) {
            .identifier => {},
            // One field of a named holder. A deeper path would need a
            // path-keyed fact the consumer does not carry.
            .field_access => if (self.tree.nodeTag(self.tree.nodeData(use.operand).node_and_token[0]) != .identifier) return false,
            else => return false,
        }
        const call_node = use.call_node orelse return false;
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        try self.enterNormalCleanup(call_node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanup(call_node);
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.tree, &call_buffer, call_node) orelse return false;
        const canonical = (try self.actualCallSummaryAt(call.queryToken(self.tree, call_node), self.cleanup_frame)) orelse return false;
        if (use.success_bool != null) {
            const resolver = self.zls orelse return false;
            const frame = canonical.callee.caller_frame orelse resolver.resolutionFrame();
            if ((try frame.isBoolType(call_node)) != true) return false;
        }
        const tree = canonical.callee.tree;
        if (tree.nodeTag(canonical.callee.declaration) != .fn_decl) return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return false;
        var parameters = proto.iterate(tree);
        var parameter_index: u32 = 0;
        var selected = false;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            const argument = (try canonical.callArgumentFor(self, &call_buffer, parameter_index)) orelse continue;
            if (argument == use.address_node) {
                _ = parameter.name_token orelse return false;
                selected = true;
                break;
            }
        }
        if (!selected) return false;
        if (use.receiver) {
            // A pointer receiver passes its own value on; only a by-value
            // place has its address taken implicitly.
            const resolver = self.zls orelse return false;
            const caller_frame = canonical.callee.caller_frame orelse resolver.resolutionFrame();
            const receiver_type = (try caller_frame.typeOfNode(use.address_node)) orelse return false;
            const normalized = (try resolver.normalizedType(receiver_type)) orelse return false;
            if ((resolver.typeTag(normalized) orelse return false) == .pointer) return false;
        }
        var caller_proof: ?DefiniteStoreProof = null;
        const chain = [1]StoreVisit{.{ .tree = tree, .declaration = canonical.callee.declaration }};
        const proved_coverage = try self.definiteParameterStoreOnSuccess(canonical, call_node, parameter_index, &caller_proof, &chain, use.success_bool);
        if (proved_coverage) |coverage| {
            use.definite_write = coverage.complete;
            for (coverage.field_names[0..coverage.field_count], coverage.covered[0..coverage.field_count]) |path, covered| {
                if (!covered) continue;
                use.fields[use.field_count] = path;
                use.field_count += 1;
            }
            if (use.definite_write and !use.physical_store_only) {
                use.location_store_coverage_known = true;
                return true;
            }
        }
        // Partial value certification can still omit definitely written fields.
        // Preserve its certificates and credit only the remaining physical writes.
        use.may_written_stores.count = 0;
        const c_element = try self.directCElementTarget(canonical, parameter_index, use.address_node);
        if (c_element) |target| {
            use.location_element_index = target.index;
            use.location_value_type = target.value_type;
        }
        const written = (try self.parameterStoreCoverage(canonical, call_node, parameter_index, &caller_proof, &chain, use.success_bool, &use.written_inputs, &use.written_reads, &use.may_written_stores, use, c_element != null)) orelse
            return use.field_count != 0 or use.may_written_stores.count != 0;
        use.location_store_coverage_known = written.effects_known;
        use.location_written = written.complete;
        use.whole_source = if (written.complete) written.whole_source else null;
        for (written.field_names[0..written.field_count], written.covered[0..written.field_count], 0..) |path, covered, slot| {
            if (!covered) continue;
            const certified = for (use.fields[0..use.field_count]) |field| {
                if (std.mem.eql(u8, path, field)) break true;
            } else false;
            if (certified and !use.physical_store_only) continue;
            use.location_fields[use.location_field_count] = path;
            use.location_field_sources[use.location_field_count] = use.location_field_sources[slot];
            use.location_field_dependencies[use.location_field_count] = written.written_dependencies[slot];
            use.location_field_count += 1;
        }
        return use.field_count != 0 or use.location_written or use.location_field_count != 0;
    }

    /// Nested callees followed from one wrapper body. Deeper chains abstain.
    const max_store_call_depth = 4;

    /// A callee body on the proof's current call chain; a revisit abstains.
    const StoreVisit = struct { tree: *const Ast, declaration: Ast.Node.Index };

    pub const PreservingCallWrite = struct {
        dependencies: [8]?Ast.Node.Index = .{null} ** 8,
        whole_payload: bool = false,
    };

    const PreservingCallKey = struct {
        declaration: DeclKey,
        callable: TypeResolver.ActualType,
        caller_resolver: *TypeResolver,
        caller_tree: *const Ast,
        caller_module: ModuleId,
        caller_actual: ?TypeResolver.ActualType,
        caller_container: ?TypeResolver.ActualType,
        call_node: Ast.Node.Index,
        parameter: u32,
    };

    const PreservingCallKeyContext = struct {
        pub fn hash(_: PreservingCallKeyContext, key: PreservingCallKey) u64 {
            var hasher = std.hash.Wyhash.init(0);
            std.hash.autoHash(&hasher, key.declaration);
            std.hash.autoHash(&hasher, key.callable.hash64());
            std.hash.autoHash(&hasher, key.caller_resolver);
            std.hash.autoHash(&hasher, key.caller_tree);
            std.hash.autoHash(&hasher, key.caller_module);
            for ([_]?TypeResolver.ActualType{ key.caller_actual, key.caller_container }) |ty| {
                std.hash.autoHash(&hasher, ty != null);
                if (ty) |actual| std.hash.autoHash(&hasher, actual.hash64());
            }
            std.hash.autoHash(&hasher, key.call_node);
            std.hash.autoHash(&hasher, key.parameter);
            return hasher.final();
        }

        fn sameType(a: ?TypeResolver.ActualType, b: ?TypeResolver.ActualType) bool {
            if ((a == null) != (b == null)) return false;
            return if (a) |actual| actual.eql(b.?) else true;
        }

        pub fn eql(_: PreservingCallKeyContext, a: PreservingCallKey, b: PreservingCallKey) bool {
            return a.declaration.tree == b.declaration.tree and
                a.declaration.module == b.declaration.module and
                a.declaration.declaration == b.declaration.declaration and
                a.callable.eql(b.callable) and a.caller_resolver == b.caller_resolver and
                a.caller_tree == b.caller_tree and a.caller_module == b.caller_module and
                sameType(a.caller_actual, b.caller_actual) and
                sameType(a.caller_container, b.caller_container) and
                a.call_node == b.call_node and a.parameter == b.parameter;
        }
    };

    /// Prove that every supported write keeps already-defined selected
    /// storage defined when all returned caller expressions are defined.
    pub fn preservingCallParameterWrite(
        self: *FileCache,
        call_node: Ast.Node.Index,
        parameter_index: u32,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) SummaryError!?PreservingCallWrite {
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        try self.enterNormalCleanup(call_node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanup(call_node);
        const resolver = if (caller_frame) |frame| frame.resolver else self.zls orelse return null;
        const caller = caller_frame orelse resolver.resolutionFrame();
        if (&caller.handle.document.tree != self.tree or caller.handle.module != self.module_id)
            return null;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.tree, &buffer, call_node) orelse return null;
        const canonical = (try self.actualCallSummaryAt(
            call.queryToken(self.tree, call_node),
            caller_frame,
        )) orelse return null;
        if (canonical.callee.call_node != call_node) return null;
        const key: PreservingCallKey = .{
            .declaration = .{
                .tree = canonical.callee.tree,
                .module = canonical.callee.handle.module,
                .declaration = canonical.callee.declaration,
            },
            .callable = canonical.callee.reference.actual_type,
            .caller_resolver = resolver,
            .caller_tree = &caller.handle.document.tree,
            .caller_module = caller.handle.module,
            .caller_actual = caller.actual_type,
            .caller_container = caller.container_type,
            .call_node = call_node,
            .parameter = parameter_index,
        };
        if (self.preserving_writes.get(key)) |answer| return answer;
        if (self.preserving_visiting.contains(key)) return null;
        try self.preserving_visiting.put(self.gpa, key, {});
        defer _ = self.preserving_visiting.remove(key);
        const answer = try self.preservingParameterBody(canonical, call_node, parameter_index, false);
        try self.preserving_writes.put(self.gpa, key, answer);
        return answer;
    }

    /// A negative-only source recipe for optional-array insertion. The
    /// hypothetical formal value is never a caller value certificate.
    pub fn diagnosticWholePayloadWriteInputs(
        self: *FileCache,
        call_node: Ast.Node.Index,
        parameter_index: u32,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) SummaryError!?PreservingCallWrite {
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.tree, &buffer, call_node) orelse return null;
        const canonical = (try self.actualCallSummaryAt(call.queryToken(self.tree, call_node), caller_frame)) orelse return null;
        return self.preservingParameterBody(canonical, call_node, parameter_index, true);
    }

    fn preservingParameterBody(
        self: *FileCache,
        canonical: ActualCallSummary,
        call_node: Ast.Node.Index,
        parameter_index: u32,
        diagnostic: bool,
    ) SummaryError!?PreservingCallWrite {
        const tree = canonical.callee.tree;
        if (tree.nodeTag(canonical.callee.declaration) != .fn_decl) return null;
        const declaring = (try canonical.declaringCache(self)) orelse return null;
        const resolver = declaring.zls orelse return null;
        const frame = resolver.frameForFunction(canonical.callee.reference);
        const types = canonical.callee.reference.actual_type.data.function.parameters;
        if (parameter_index >= types.len) return null;
        const pointer = (try frame.resolver.normalizedType(types[parameter_index].type)) orelse
            return null;
        if (frame.resolver.pointerSize(pointer) != .one) return null;
        const child = frame.resolver.childType(pointer) orelse return null;
        const pointee = (try frame.resolver.normalizedType(child)) orelse return null;
        const whole_payload = (frame.resolver.typeTag(pointee) orelse return null) == .array;
        if (diagnostic and !whole_payload) return null;
        if (whole_payload) {
            const element = frame.resolver.childType(pointee) orelse return null;
            const actual_element = (try frame.resolver.normalizedType(element)) orelse return null;
            if (frame.resolver.typeTag(actual_element) != .optional) return null;
        } else {
            switch (frame.resolver.typeTag(pointee) orelse return null) {
                .int, .comptime_int, .float, .comptime_float, .bool, .@"enum" => {},
                else => return null,
            }
        }
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse
            return null;
        var proof: DefiniteStoreProof = .{
            .tree = tree,
            .frame = frame,
            .call_node = call_node,
            .call_tree = self.tree,
        };
        var result: PreservingCallWrite = .{ .whole_payload = whole_payload };
        var dependency_count: usize = 0;
        var selected_token: ?Ast.TokenIndex = null;
        var parameters = proto.iterate(tree);
        var index: u32 = 0;
        while (parameters.next()) |parameter| : (index += 1) {
            try self.chargeNormalCleanup(call_node);
            if (index >= types.len) return null;
            const token = parameter.name_token orelse return null;
            if (index == parameter_index) {
                selected_token = token;
                if (!proof.bind(token, .undefined_value)) return null;
                continue;
            }
            const actual_type = (try frame.resolver.normalizedType(types[index].type)) orelse
                return null;
            switch (frame.resolver.typeTag(actual_type) orelse return null) {
                .int, .comptime_int, .float, .comptime_float, .bool, .@"enum" => {},
                .@"struct" => {
                    if (!whole_payload or (!diagnostic and !try self.preservingWholeArgument(
                        canonical,
                        index,
                        actual_type,
                    ))) return null;
                },
                .undefined => if (!diagnostic) return null,
                else => return null,
            }
            if (dependency_count == result.dependencies.len) return null;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            result.dependencies[dependency_count] = (try canonical.callArgumentFor(
                self,
                &argument_buffer,
                index,
            )) orelse return null;
            dependency_count += 1;
            if (!proof.bind(token, .defined)) return null;
        }
        if (index != types.len) return null;
        proof.parameter_count = proof.binding_count;
        const selected = selected_token orelse return null;
        if (whole_payload) {
            var stored_parameter: Ast.TokenIndex = undefined;
            if (!try declaring.preservingOptionalArrayBody(
                &proof,
                canonical.callee.declaration,
                selected,
                if (diagnostic) &stored_parameter else null,
            )) return null;
            if (diagnostic) {
                result.dependencies = .{null} ** 8;
                var selected_parameters = proto.iterate(tree);
                var selected_index: u32 = 0;
                while (selected_parameters.next()) |parameter| : (selected_index += 1) {
                    if (parameter.name_token != stored_parameter) continue;
                    var argument_buffer: [2]Ast.Node.Index = undefined;
                    result.dependencies[0] = try canonical.callArgumentFor(self, &argument_buffer, selected_index);
                    break;
                }
            }
            return result;
        }
        // This premise is discharged by the caller's prior whole-array fact.
        // No consumer may turn it into an initializer certificate.
        if (!proof.setStorePointee(selected, .defined)) return null;
        const name = tree.tokenSlice(selected);
        const body = tokens.bodyOf(tree, canonical.callee.declaration) orelse return null;
        var statements = engine.AstIterator.init(tree, body);
        var wrote = false;
        while (statements.next(tree)) |statement| {
            try self.chargeNormalCleanup(call_node);
            if (tree.fullVarDecl(statement)) |variable| {
                const value = variable.ast.init_node.unwrap() orelse return null;
                const local_name = tree.tokenSlice(variable.ast.mut_token + 1);
                if (proof.findIndex(local_name) != null) return null;
                if (try definiteStoreKind(&proof, value) != .scalar) return null;
                const verdict = try declaring.preservingStoreValue(&proof, name, value);
                if (verdict == .unknown or
                    !proof.bind(variable.ast.mut_token + 1, verdict)) return null;
                continue;
            }
            if (tree.nodeTag(statement) == .@"return") {
                if (tree.nodeData(statement).opt_node.unwrap()) |value| {
                    if (tree.nodeTag(value) != .error_value and
                        try declaring.preservingStoreValue(&proof, name, value) != .defined)
                        return null;
                }
                break;
            }
            switch (tree.nodeTag(statement)) {
                .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod, .assign_shl, .assign_shr, .assign_bit_and, .assign_bit_or, .assign_bit_xor, .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap, .assign_add_sat, .assign_sub_sat, .assign_mul_sat, .assign_shl_sat => {},
                else => return null,
            }
            const lhs, const rhs = tree.nodeData(statement).node_and_node;
            const verdict = try declaring.preservingStoreValue(&proof, name, rhs);
            if (verdict == .unknown) return null;
            if (tree.nodeTag(lhs) == .identifier) {
                const binding_index = proof.findIndex(tree.tokenSlice(tree.nodeMainToken(lhs))) orelse
                    return null;
                if (binding_index < proof.parameter_count or tree.nodeTag(statement) != .assign)
                    return null;
                proof.bindings[binding_index].value = verdict;
                continue;
            }
            if (tree.nodeTag(lhs) != .deref or verdict != .defined) return null;
            const base = tree.nodeData(lhs).node;
            if (tree.nodeTag(base) != .identifier or
                !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(base)), name)) return null;
            if (!proof.setStorePointee(selected, .defined)) return null;
            wrote = true;
        }
        return if (wrote) result else null;
    }

    /// The value evaluator owns scalar/call semantics. This guard only
    /// excludes pointer transport, which would escape the selected storage.
    fn preservingStoreValue(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        selected_name: []const u8,
        value: Ast.Node.Index,
    ) SummaryError!DefiniteStoreValue {
        if (!try self.preservingValueHasNoEscape(proof, selected_name, value, 0))
            return .unknown;
        // Keep the catch/try node: the value evaluator must select only the
        // successful payload and prove that its fallback exits without a store.
        return self.definiteStoreValue(proof, value, 0);
    }

    fn preservingValueHasNoEscape(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        selected_name: []const u8,
        node: Ast.Node.Index,
        depth: u32,
    ) SummaryError!bool {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        if (depth == 64)
            return self.cleanupBudgetFailureAt(proof.call_tree, .normal_cleanup_depth, 64, proof.call_node);
        const tree = proof.tree;
        switch (tree.nodeTag(node)) {
            .address_of => return false,
            .identifier => return !std.mem.eql(
                u8,
                tree.tokenSlice(tree.nodeMainToken(node)),
                selected_name,
            ),
            .deref => {
                const base = tree.nodeData(node).node;
                if (tree.nodeTag(base) == .identifier and std.mem.eql(
                    u8,
                    tree.tokenSlice(tree.nodeMainToken(base)),
                    selected_name,
                )) return true;
            },
            else => {},
        }
        var children = engine.AstIterator.init(tree, node);
        while (children.next(tree)) |child| {
            if (!try self.preservingValueHasNoEscape(
                proof,
                selected_name,
                child,
                depth + 1,
            )) return false;
        }
        return true;
    }

    /// A whole-value premise needs a complete actual constructor. Omissions,
    /// nested aggregates and pointer-bearing fields need another certificate.
    fn preservingWholeArgument(
        self: *FileCache,
        canonical: ActualCallSummary,
        parameter: u32,
        ty: TypeResolver.ActualType,
    ) SummaryError!bool {
        if (ty.data != .container) return false;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const actual = (try canonical.callArgumentFor(self, &argument_buffer, parameter)) orelse
            return false;
        var literal_buffer: [2]Ast.Node.Index = undefined;
        const literal = self.tree.fullStructInit(&literal_buffer, actual) orelse return false;
        const resolver = if (canonical.callee.caller_frame) |frame|
            frame.resolver
        else
            self.zls orelse return false;
        const field_frame = resolver.frameForContainer(ty.data.container);
        const field_tree = &field_frame.handle.document.tree;
        var container_buffer: [2]Ast.Node.Index = undefined;
        const container = field_tree.fullContainerDecl(
            &container_buffer,
            ty.data.container.scope_handle.toNode(),
        ) orelse return false;
        var field_count: usize = 0;
        for (container.ast.members) |member| {
            try self.chargeNormalCleanup(canonical.callee.call_node);
            const field = field_tree.fullContainerField(member) orelse continue;
            if (field.ast.tuple_like or field.comptime_token != null) return false;
            const field_type_node = field.ast.type_expr.unwrap() orelse return false;
            const field_type = (try field_frame.typeOfNode(field_type_node)) orelse return false;
            const normalized = (try resolver.normalizedType(field_type)) orelse return false;
            switch (resolver.typeTag(normalized) orelse return false) {
                .int, .comptime_int, .float, .comptime_float, .bool, .@"enum" => {},
                else => return false,
            }
            const name = field_tree.tokenSlice(field.ast.main_token);
            var matches: usize = 0;
            for (literal.ast.fields) |value| {
                try self.chargeNormalCleanup(canonical.callee.call_node);
                const first = self.tree.firstToken(value);
                if (first >= 3 and self.tree.tokenTag(first - 1) == .equal and
                    self.tree.tokenTag(first - 2) == .identifier and
                    std.mem.eql(u8, self.tree.tokenSlice(first - 2), name)) matches += 1;
            }
            if (matches != 1) return false;
            field_count += 1;
        }
        return field_count == literal.ast.fields.len;
    }

    /// The loop writes only one captured optional slot, or returns without
    /// writing. Its input is precisely the already-initialized fixed array.
    fn preservingOptionalArrayBody(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        declaration: Ast.Node.Index,
        selected: Ast.TokenIndex,
        stored_parameter: ?*Ast.TokenIndex,
    ) SummaryError!bool {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        const tree = proof.tree;
        const body = tokens.bodyOf(tree, declaration) orelse return false;
        var body_buffer: [2]Ast.Node.Index = undefined;
        const statements = tree.blockStatements(&body_buffer, body) orelse return false;
        if (statements.len != 2 or !preservingEmptyOrErrorReturn(tree, statements[1]))
            return false;
        const loop = tree.fullFor(statements[0]) orelse return false;
        if (loop.label_token != null or loop.inline_token != null or
            loop.ast.else_expr != .none or loop.ast.inputs.len != 1) return false;
        const input = loop.ast.inputs[0];
        const selected_name = tree.tokenSlice(selected);
        if (tree.nodeTag(input) != .identifier or !std.mem.eql(
            u8,
            tree.tokenSlice(tree.nodeMainToken(input)),
            selected_name,
        )) return false;
        const capture = loop.payload_token;
        if (tree.tokenTag(capture) != .asterisk or
            tree.tokenTag(capture + 1) != .identifier or
            tree.tokenTag(capture + 2) != .pipe) return false;
        const capture_name = tree.tokenSlice(capture + 1);
        if (proof.findIndex(capture_name) != null) return false;
        var loop_buffer: [2]Ast.Node.Index = undefined;
        const loop_statements = tree.blockStatements(
            &loop_buffer,
            loop.ast.then_expr,
        ) orelse return false;
        if (loop_statements.len != 1) return false;
        const branch = tree.fullIf(loop_statements[0]) orelse return false;
        if (branch.payload_token != null or branch.error_token != null or
            branch.ast.else_expr != .none) return false;
        if (tree.nodeTag(branch.ast.cond_expr) != .equal_equal) return false;
        const left, const right = tree.nodeData(branch.ast.cond_expr).node_and_node;
        if (!(preservingCapturedSlot(tree, left, capture_name) and
            preservingNull(tree, right)) and
            !(preservingCapturedSlot(tree, right, capture_name) and
                preservingNull(tree, left))) return false;
        var branch_buffer: [2]Ast.Node.Index = undefined;
        const branch_statements = tree.blockStatements(
            &branch_buffer,
            branch.ast.then_expr,
        ) orelse return false;
        if (branch_statements.len != 2 or tree.nodeTag(branch_statements[0]) != .assign or
            tree.nodeTag(branch_statements[1]) != .@"return" or
            tree.nodeData(branch_statements[1]).opt_node != .none) return false;
        const target, const value = tree.nodeData(branch_statements[0]).node_and_node;
        if (!preservingCapturedSlot(tree, target, capture_name)) return false;
        // Only a caller-premised formal supplies the whole payload. A local
        // struct literal could hide an omitted undefined default.
        if (tree.nodeTag(value) != .identifier) return false;
        const value_index = proof.findIndex(tree.tokenSlice(tree.nodeMainToken(value))) orelse
            return false;
        if (value_index >= proof.parameter_count) return false;
        if (stored_parameter) |output| output.* = proof.bindings[value_index].token;
        if (!try self.preservingValueHasNoEscape(proof, capture_name, value, 0)) return false;
        return try self.preservingStoreValue(proof, selected_name, value) == .defined;
    }

    fn preservingCapturedSlot(tree: *const Ast, node: Ast.Node.Index, name: []const u8) bool {
        if (tree.nodeTag(node) != .deref) return false;
        const base = tree.nodeData(node).node;
        return tree.nodeTag(base) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(base)), name);
    }

    fn preservingNull(tree: *const Ast, node: Ast.Node.Index) bool {
        return tree.nodeTag(node) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "null");
    }

    fn preservingEmptyOrErrorReturn(tree: *const Ast, node: Ast.Node.Index) bool {
        if (tree.nodeTag(node) != .@"return") return false;
        const value = tree.nodeData(node).opt_node.unwrap() orelse return true;
        return tree.nodeTag(value) == .error_value;
    }

    /// Stores through a pointer formal intersected across successful exits.
    /// A partial certificate covers only its listed fields.
    const StoreCoverage = struct {
        pointee: TypeResolver.ActualType,
        field_count: usize = 0,
        field_names: [128][]const u8 = undefined,
        covered: [128]bool = @splat(false),
        written_dependencies: [128]WrittenDependencies = @splat(.{}),
        whole_dependencies: WrittenDependencies = .{},
        computed_sources: u8 = 0,
        computed_original_alternative: bool = true,
        computed_opaque_alternative: bool = false,
        computed_overflow: bool = false,
        complete: bool = false,
        effects_known: bool = true,
        whole_source: ?WholeStoreSource = null,
    };

    /// Include parent fields and nested inline-struct fields. Pointer and array
    /// payloads remain single fields; following them would credit other storage.
    fn storeCoverageFields(
        self: *FileCache,
        pointee: TypeResolver.ActualType,
        fields: *[128][]const u8,
        defaults: *[128]?Ast.Node.Index,
        coverage: *StoreCoverage,
        call_tree: *const Ast,
        call_node: Ast.Node.Index,
    ) SummaryError!bool {
        return self.storeCoverageFieldsAt(pointee, "", fields, defaults, coverage, call_tree, call_node, false);
    }

    fn storeCoverageFieldsAt(
        self: *FileCache,
        actual: TypeResolver.ActualType,
        prefix: []const u8,
        fields: *[128][]const u8,
        defaults: *[128]?Ast.Node.Index,
        coverage: *StoreCoverage,
        call_tree: *const Ast,
        call_node: Ast.Node.Index,
        physical: bool,
    ) SummaryError!bool {
        try self.chargeNormalCleanupAt(call_tree, call_node);
        const resolver = self.zls orelse return false;
        const normalized = (try resolver.normalizedType(actual)) orelse return physical;
        if (physical and resolver.typeTag(normalized) == .array) {
            const count = definiteStoreArrayTypeCount(resolver, normalized) orelse return false;
            if (count > fields.len - coverage.field_count) return false;
            const child = resolver.childType(normalized) orelse return false;
            if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
            for (0..@as(usize, @intCast(count))) |element| {
                const path = try std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}[{d}]", .{ prefix, element });
                const index = coverage.field_count;
                fields[index] = path;
                coverage.field_names[index] = path;
                defaults[index] = null;
                coverage.field_count += 1;
                if (!try self.storeCoverageFieldsAt(child, path, fields, defaults, coverage, call_tree, call_node, true)) return false;
            }
            return true;
        }
        if (resolver.typeTag(normalized) != .@"struct") return true;
        if (normalized.data != .container) return false;
        const container = normalized.data.container.scope_handle;
        const tree = &container.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = tree.fullContainerDecl(&buffer, container.toNode()) orelse return false;
        const frame = resolver.frameForContainer(normalized.data.container);
        for (declaration.ast.members) |member| {
            const field = tree.fullContainerField(member) orelse continue;
            if (field.ast.tuple_like or coverage.field_count == fields.len) return false;
            const name = tree.tokenSlice(field.ast.main_token);
            const path = if (prefix.len == 0) name else path: {
                if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
                break :path try std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}.{s}", .{ prefix, name });
            };
            const index = coverage.field_count;
            fields[index] = path;
            coverage.field_names[index] = path;
            defaults[index] = field.ast.value_expr.unwrap();
            coverage.field_count += 1;
            const type_node = field.ast.type_expr.unwrap() orelse {
                if (physical) continue;
                return false;
            };
            const child = (try frame.typeOfNode(type_node)) orelse {
                if (physical) continue;
                return false;
            };
            // Recursive inline values cannot form a finite Zig type. The
            // existing field bound also caps this source-directed traversal.
            if (!try self.storeCoverageFieldsAt(child, path, fields, defaults, coverage, call_tree, call_node, physical)) return false;
        }
        return true;
    }

    fn storeFieldIndex(proof: *const DefiniteStoreProof, name: []const u8, fields: []const []const u8, lhs: Ast.Node.Index) SummaryError!?usize {
        const tree = proof.tree;
        if (tree.nodeTag(lhs) != .field_access and tree.nodeTag(lhs) != .array_access) return null;
        const root = tokens.rootIdentifier(tree, lhs) orelse return null;
        if (!std.mem.eql(u8, proof.formalName(tree.tokenSlice(tree.nodeMainToken(root))), name)) return null;
        for (fields, 0..) |path, index| {
            var current = lhs;
            var end = path.len;
            while (tree.nodeTag(current) == .field_access or tree.nodeTag(current) == .array_access) {
                if (tree.nodeTag(current) == .array_access) {
                    const base, const subscript = tree.nodeData(current).node_and_node;
                    const element = (try definiteStoreInteger(proof, subscript)) orelse break;
                    if (end == 0 or path[end - 1] != ']') break;
                    const start = std.mem.lastIndexOfScalar(u8, path[0..end], '[') orelse break;
                    const expected = std.fmt.parseInt(u64, path[start + 1 .. end - 1], 10) catch break;
                    if (element != expected) break;
                    current = base;
                    end = start;
                    if (end == 0) {
                        if (current == root) return index;
                        break;
                    }
                    continue;
                }
                const base, const token = tree.nodeData(current).node_and_token;
                const start = if (std.mem.lastIndexOfScalar(u8, path[0..end], '.')) |dot| dot + 1 else 0;
                if (!std.mem.eql(u8, tree.tokenSlice(token), path[start..end])) break;
                current = base;
                if (start == 0) {
                    if (current == root) return index;
                    break;
                }
                end = start - 1;
            }
        }
        return null;
    }

    fn coverStoreField(coverage: *StoreCoverage, index: usize) void {
        const path = coverage.field_names[index];
        for (coverage.field_names[0..coverage.field_count], coverage.covered[0..coverage.field_count]) |candidate, *covered| {
            if (std.mem.eql(u8, candidate, path) or
                (candidate.len > path.len and candidate[path.len] == '.' and std.mem.startsWith(u8, candidate, path))) covered.* = true;
        }
        refreshStoreCoverage(coverage);
    }

    fn refreshStoreCoverage(coverage: *StoreCoverage) void {
        var index = coverage.field_count;
        while (index != 0) {
            index -= 1;
            const path = coverage.field_names[index];
            var children = false;
            var complete = true;
            var descendant_dependencies: WrittenDependencies = .{};
            for (coverage.field_names[index + 1 .. coverage.field_count], coverage.covered[index + 1 .. coverage.field_count], coverage.written_dependencies[index + 1 .. coverage.field_count]) |candidate, covered, dependencies| {
                if (candidate.len <= path.len or candidate[path.len] != '.' or !std.mem.startsWith(u8, candidate, path)) continue;
                children = true;
                complete = complete and covered;
                descendant_dependencies.merge(dependencies);
            }
            if (children) {
                coverage.covered[index] = complete;
                coverage.written_dependencies[index] = descendant_dependencies;
            }
        }
        if (coverage.field_count == 0) return;
        coverage.complete = true;
        coverage.whole_dependencies = .{};
        for (coverage.covered[0..coverage.field_count], coverage.written_dependencies[0..coverage.field_count]) |covered, dependencies| {
            coverage.complete = coverage.complete and covered;
            if (covered) coverage.whole_dependencies.merge(dependencies);
        }
    }

    fn recordWrittenStoreField(coverage: *StoreCoverage, index: usize, dependencies: WrittenDependencies) void {
        const path = coverage.field_names[index];
        for (coverage.field_names[0..coverage.field_count], coverage.written_dependencies[0..coverage.field_count]) |candidate, *recipe| {
            if (std.mem.eql(u8, candidate, path) or
                (candidate.len > path.len and candidate[path.len] == '.' and std.mem.startsWith(u8, candidate, path)))
                recipe.* = dependencies;
        }
        refreshStoreCoverage(coverage);
    }

    /// Which part of the proof's own pointee a nested actual designates.
    const StoreTarget = union(enum) { whole, field: usize, unknown_field };

    /// Calls unwrapped through `try` or an error-exiting catch.
    fn storeCall(tree: *const Ast, node: Ast.Node.Index) ?Ast.Node.Index {
        var current = node;
        while (true) {
            if (tree.nodeTag(current) == .@"try") {
                current = tree.nodeData(current).node;
                continue;
            }
            if (tree.nodeTag(current) == .@"catch") {
                const call, const fallback = tree.nodeData(current).node_and_node;
                if (tree.nodeTag(fallback) != .unreachable_literal) {
                    if (tree.nodeTag(fallback) != .@"return") return null;
                    const value = tree.nodeData(fallback).opt_node.unwrap() orelse return null;
                    if (tree.nodeTag(value) != .error_value) {
                        const token = tree.nodeMainToken(current);
                        if (tree.tokenTag(token + 1) != .pipe or tree.tokenTag(token + 2) != .identifier or
                            tree.tokenTag(token + 3) != .pipe or tree.nodeTag(value) != .identifier or
                            !std.mem.eql(u8, tree.tokenSlice(token + 2), tree.tokenSlice(tree.nodeMainToken(value)))) return null;
                    }
                }
                current = call;
                continue;
            }
            break;
        }
        return switch (tree.nodeTag(current)) {
            .call, .call_one, .call_comma, .call_one_comma => current,
            else => null,
        };
    }

    /// The type fixes this count. Slice values with runtime lengths abstain.
    fn definiteStoreArrayCount(proof: *const DefiniteStoreProof, node: Ast.Node.Index) SummaryError!?u64 {
        const resolver = proof.frame.resolver;
        var ty = (try proof.frame.typeOfNode(node)) orelse return null;
        if (resolver.pointerSize(ty)) |size| {
            if (size != .one) return null;
            ty = (try resolver.normalizedType(resolver.childType(ty) orelse return null)) orelse return null;
        }
        return definiteStoreArrayTypeCount(resolver, ty);
    }

    fn definiteStoreArrayTypeCount(resolver: *TypeResolver, ty: TypeResolver.ActualType) ?u64 {
        return switch (ty.data) {
            .array => |array| array.elem_count,
            .ip_index => switch (resolver.ctx.ip.indexToKey(ty.ipIndex() orelse return null)) {
                .array_type => |array| array.len,
                else => null,
            },
            else => null,
        };
    }

    fn definiteStoreInteger(proof: *const DefiniteStoreProof, node: Ast.Node.Index) SummaryError!?u64 {
        return proof.frame.resolver.analyser.resolveIntegerLiteral(u64, .{
            .node_handle = .of(node, proof.frame.handle),
            .container_type = proof.frame.container_type,
        });
    }

    fn storeNames(tree: *const Ast, node: Ast.Node.Index, name: []const u8) bool {
        return tree.nodeTag(node) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name);
    }

    /// One unconditional store per iteration. Control flow, aliases and
    /// additional side effects need the ordinary body proof, not a loop guess.
    fn definiteStoreLoop(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        canonical: ActualCallSummary,
        call_node: Ast.Node.Index,
        name: []const u8,
        fields: []const []const u8,
        node: Ast.Node.Index,
        visiting: []const StoreVisit,
        coverage: *StoreCoverage,
    ) SummaryError!bool {
        _ = fields;
        try self.chargeNormalCleanup(call_node);
        const tree = proof.tree;
        const loop = tree.fullFor(node) orelse return false;
        if (loop.label_token != null or loop.ast.else_expr != .none or
            loop.ast.inputs.len == 0 or loop.ast.inputs.len > 2) return false;
        var body = loop.ast.then_expr;
        switch (tree.nodeTag(body)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                var statements = engine.AstIterator.init(tree, body);
                body = statements.next(tree) orelse return false;
                if (statements.next(tree) != null) return false;
            },
            else => {},
        }
        var lexical = proof.*;
        var capture = loop.payload_token;
        const pointer_capture = tree.tokenTag(capture) == .asterisk;
        if (pointer_capture) capture += 1;
        if (tree.tokenTag(capture) != .identifier) return false;
        const capture_name = tree.tokenSlice(capture);
        const input = loop.ast.inputs[0];
        const whole_capture = storeNames(tree, input, name) and pointer_capture;
        // A capture of the output points at undefined bytes until its store.
        if (!lexical.bind(capture, if (whole_capture) .undefined_value else .defined)) return false;
        var index_name: ?[]const u8 = null;
        if (loop.ast.inputs.len == 2) {
            const range = loop.ast.inputs[1];
            if (tree.nodeTag(range) != .for_range) return false;
            const start, const end = tree.nodeData(range).node_and_opt_node;
            if (end != .none or try definiteStoreInteger(proof, start) != 0) return false;
            if (tree.tokenTag(capture + 1) != .comma or tree.tokenTag(capture + 2) != .identifier) return false;
            index_name = tree.tokenSlice(capture + 2);
            if (!lexical.bind(capture + 2, .defined)) return false;
        }
        if (whole_capture) {
            if (tree.nodeTag(body) != .assign) return false;
            const lhs, const rhs = tree.nodeData(body).node_and_node;
            if (tree.nodeTag(lhs) != .deref or !storeNames(tree, tree.nodeData(lhs).node, capture_name)) return false;
            lexical.written_dependencies = .{};
            if (try self.definiteStoreValue(&lexical, rhs, 0) != .defined) return false;
            coverage.whole_dependencies = lexical.written_dependencies;
            coverage.complete = true;
            return true;
        }
        if (pointer_capture or index_name == null) return false;
        const count = (try definiteStoreArrayCount(proof, input)) orelse return false;
        if (count == 0 or try self.definiteStoreValue(proof, input, 0) != .defined) return false;
        const output_count = switch (coverage.pointee.data) {
            .array => |array| array.elem_count,
            .ip_index => switch (proof.frame.resolver.ctx.ip.indexToKey(coverage.pointee.ipIndex() orelse return false)) {
                .array_type => |array| array.len,
                else => return false,
            },
            else => return false,
        };
        const nested_call = storeCall(tree, body) orelse return false;
        const declaring = (try canonical.declaringCache(self)) orelse return false;
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &call_buffer, nested_call) orelse return false;
        const nested = (try declaring.actualCallSummaryAt(call.queryToken(tree, nested_call), proof.frame)) orelse return false;
        if (nested.callee.tree.nodeTag(nested.callee.declaration) != .fn_decl or visiting.len > max_store_call_depth) return false;
        for (visiting) |seen| {
            if (seen.tree == nested.callee.tree and seen.declaration == nested.callee.declaration) return false;
        }
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(nested.callee.tree, &proto_buffer, nested.callee.declaration) orelse return false;
        var parameters = proto.iterate(nested.callee.tree);
        var parameter_index: u32 = 0;
        var output_parameter: ?u32 = null;
        var width: u64 = 0;
        while (parameters.next() != null) : (parameter_index += 1) {
            const argument = (try nested.callArgumentFor(declaring, &call_buffer, parameter_index)) orelse return false;
            if (tree.fullSlice(argument)) |chunk| {
                const tail = tree.fullSlice(chunk.ast.sliced) orelse return false;
                if (!storeNames(tree, tail.ast.sliced, name) or tail.ast.end != .none or
                    tail.ast.sentinel != .none or chunk.ast.sentinel != .none) return false;
                if (try definiteStoreInteger(proof, chunk.ast.start) != 0) return false;
                const chunk_end = chunk.ast.end.unwrap() orelse return false;
                width = (try definiteStoreInteger(proof, chunk_end)) orelse return false;
                if (tree.nodeTag(tail.ast.start) != .mul) return false;
                const left, const right = tree.nodeData(tail.ast.start).node_and_node;
                const stride = if (storeNames(tree, right, index_name.?))
                    try definiteStoreInteger(proof, left)
                else if (storeNames(tree, left, index_name.?))
                    try definiteStoreInteger(proof, right)
                else
                    null;
                if (width == 0 or stride != width or output_parameter != null) return false;
                output_parameter = parameter_index;
            } else if (try self.definiteStoreValue(&lexical, argument, 0) != .defined) {
                return false;
            }
        }
        const selected = output_parameter orelse return false;
        if ((std.math.mul(u64, count, width) catch return false) != output_count) return false;
        var chain: [max_store_call_depth + 1]StoreVisit = undefined;
        @memcpy(chain[0..visiting.len], visiting);
        chain[visiting.len] = .{ .tree = nested.callee.tree, .declaration = nested.callee.declaration };
        var caller: ?DefiniteStoreProof = lexical;
        const written = (try declaring.definiteParameterStore(nested, nested_call, selected, &caller, chain[0 .. visiting.len + 1])) orelse return false;
        if (!written.complete) return false;
        coverage.whole_dependencies = written.whole_dependencies;
        coverage.complete = true;
        return true;
    }

    /// A success-only certificate for an actual output argument. C-pointer
    /// actuals must match the formal storage extent; slice bounds and the
    /// accepted success edge remain the builder's responsibility.
    pub fn definiteCallParameterWrite(self: *FileCache, call_node: Ast.Node.Index, parameter_index: u32) SummaryError!bool {
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        try self.enterNormalCleanup(call_node);
        defer self.leaveNormalCleanup();
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.tree, &call_buffer, call_node) orelse return false;
        const canonical = (try self.actualCallSummaryAt(call.queryToken(self.tree, call_node), null)) orelse return false;
        const key: ParameterWriteKey = .{
            .call_node = call_node,
            .parameter_index = parameter_index,
            .callee_context = canonical.callee.reference.actual_type,
            .caller_context = if (canonical.callee.caller_frame) |frame| frame.actual_type else null,
        };
        if (self.definite_parameter_writes.contains(key)) return true;
        var caller: ?DefiniteStoreProof = null;
        const chain = [1]StoreVisit{.{ .tree = canonical.callee.tree, .declaration = canonical.callee.declaration }};
        const stored = (try self.definiteParameterStore(canonical, call_node, parameter_index, &caller, &chain)) orelse return false;
        if (!stored.complete) return false;
        try self.definite_parameter_writes.put(self.gpa, key, {});
        return true;
    }

    /// Successful exits of `canonical` as seen through pointer-like formal
    /// number `parameter_index`. `caller` holds the lexical state of whoever
    /// supplied the actuals, built on first need. Null is an
    /// abstention; partial coverage is a proof of exactly the stores it lists.
    fn definiteParameterStore(
        self: *FileCache,
        canonical: ActualCallSummary,
        call_node: Ast.Node.Index,
        parameter_index: u32,
        caller: *?DefiniteStoreProof,
        visiting: []const StoreVisit,
    ) SummaryError!?StoreCoverage {
        return self.definiteParameterStoreOnSuccess(canonical, call_node, parameter_index, caller, visiting, null);
    }

    fn definiteParameterStoreOnSuccess(
        self: *FileCache,
        canonical: ActualCallSummary,
        call_node: Ast.Node.Index,
        parameter_index: u32,
        caller: *?DefiniteStoreProof,
        visiting: []const StoreVisit,
        success_bool: ?bool,
    ) SummaryError!?StoreCoverage {
        return self.parameterStoreCoverage(canonical, call_node, parameter_index, caller, visiting, success_bool, null, null, null, null, false);
    }

    fn parameterStoreCoverage(
        self: *FileCache,
        canonical: ActualCallSummary,
        call_node: Ast.Node.Index,
        parameter_index: u32,
        caller: *?DefiniteStoreProof,
        visiting: []const StoreVisit,
        success_bool: ?bool,
        written_inputs: ?*[8]?Ast.Node.Index,
        written_reads: ?*[8]?WrittenRead,
        may_written_stores: ?*WrittenMayStores,
        computed_use: ?*AddressUse,
        physical_c_element: bool,
    ) SummaryError!?StoreCoverage {
        try self.chargeNormalCleanup(call_node);
        const tree = canonical.callee.tree;
        if (tree.nodeTag(canonical.callee.declaration) != .fn_decl) return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return null;
        var parameters = proto.iterate(tree);
        var index: u32 = 0;
        var parameter_token: ?Ast.TokenIndex = null;
        while (parameters.next()) |parameter| : (index += 1) {
            if (index != parameter_index) continue;
            parameter_token = parameter.name_token orelse return null;
            break;
        }
        const declaring = (try canonical.declaringCache(self)) orelse return null;
        const resolver = declaring.zls orelse return null;
        const frame = resolver.frameForFunction(canonical.callee.reference);
        const formal_types = canonical.callee.reference.actual_type.data.function.parameters;
        if (parameter_index >= formal_types.len) return null;
        const pointer = (try resolver.normalizedType(formal_types[parameter_index].type)) orelse return null;
        const pointer_size = resolver.pointerSize(pointer) orelse return null;
        if (pointer_size != .one and pointer_size != .c and pointer_size != .slice) return null;
        const child = resolver.childType(pointer) orelse return null;
        const pointee = (try resolver.normalizedType(child)) orelse return null;
        // Authenticated physical C element recipes bypass this gate.
        // All certificates retain the extent check.
        if (pointer_size == .c and !physical_c_element) {
            // A scalar C pointee is not the whole storage of *[N]T actuals,
            // including constant slices. Enforce extent before any caller can
            // publish or memoize the successful-store certificate.
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try canonical.callArgumentFor(self, &argument_buffer, parameter_index)) orelse return null;
            const caller_frame = canonical.callee.caller_frame orelse
                (self.zls orelse return null).resolutionFrame();
            const actual_type = (try caller_frame.typeOfNode(argument)) orelse return null;
            const actual = (try resolver.normalizedType(actual_type)) orelse return null;
            if (resolver.pointerSize(actual) == null) return null;
            const actual_child = resolver.childType(actual) orelse return null;
            const actual_pointee = (try resolver.normalizedType(actual_child)) orelse return null;
            if (!pointee.eql(actual_pointee)) return null;
        }
        var fields: [128][]const u8 = undefined;
        var defaults: [128]?Ast.Node.Index = @splat(null);
        var coverage: StoreCoverage = .{ .pointee = pointee };
        const inputs = written_inputs orelse if (caller.*) |parent| parent.written_inputs else null;
        const reads = written_reads orelse if (caller.*) |parent| parent.written_reads else null;
        const fields_known = if (inputs != null)
            try self.storeCoverageFieldsAt(pointee, "", &fields, &defaults, &coverage, self.tree, call_node, true)
        else try self.storeCoverageFields(pointee, &fields, &defaults, &coverage, self.tree, call_node);
        if (!fields_known) return null;
        const name = tree.tokenSlice(parameter_token orelse return null);
        const body = tree.nodeData(canonical.callee.declaration).node_and_node[1];
        switch (tree.nodeTag(body)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {},
            else => return null,
        }
        var dependencies_complete = true;
        var local_templates: ComputedStoreBuilders = .{};
        const templates = if (computed_use != null) &local_templates else
            if (caller.*) |parent| parent.computed_templates else null;
        var output_argument_buffer: [2]Ast.Node.Index = undefined;
        const output_actual = if (caller.* != null or written_inputs != null)
            try canonical.callArgumentFor(self, &output_argument_buffer, parameter_index)
        else
            null;
        const identity_output = if (caller.*) |parent| parent.identity_output orelse output_actual else output_actual;
        var identity_output_prefix: ?[]const u8 = if (written_inputs != null) "" else null;
        if (caller.*) |parent| {
            identity_output_prefix = if (output_actual) |actual|
                try self.outputArgumentPrefix(&parent, actual)
            else
                null;
        }
        const identity_inputs = if (caller.*) |parent| parent.identity_inputs orelse written_inputs else written_inputs;
        const identity_tree = if (caller.*) |parent| parent.identity_tree orelse
            (if (written_inputs != null) self.tree else null) else
            (if (written_inputs != null) self.tree else null);
        var proof: DefiniteStoreProof = .{
            .tree = tree,
            .frame = frame,
            .canonical = canonical,
            .caller = caller,
            .caller_cache = self,
            .identity_inputs = identity_inputs,
            .identity_tree = identity_tree,
            .identity_input_boundary = written_inputs != null,
            .identity_output = identity_output,
            .identity_output_prefix = identity_output_prefix,
            .call_node = call_node,
            .call_tree = self.tree,
            .written_inputs = inputs,
            .written_reads = reads,
            .written_input_boundary = written_inputs != null,
            .may_written_stores = may_written_stores,
            .computed_templates = templates,
            .written_dependencies_complete = if (written_inputs != null) &dependencies_complete else
                if (caller.*) |parent| parent.written_dependencies_complete else null,
        };
        const context: StoreBodyContext = .{
            .canonical = canonical,
            .call_node = call_node,
            .call_tree = self.tree,
            .name = name,
            .fields = fields[0..coverage.field_count],
            .defaults = defaults[0..coverage.field_count],
            .visiting = visiting,
            .success_bool = success_bool,
        };
        proof.out_name = name;
        proof.out_fields = context.fields;
        proof.out_coverage = &coverage;
        if (templates != null and computed_use == null) if (caller.*) |parent| {
            if (parent.out_name) |parent_name| if (parent.out_coverage) |prior| {
                var argument_buffer: [2]Ast.Node.Index = undefined;
                const actual = (try canonical.callArgumentFor(self, &argument_buffer, parameter_index)) orelse return null;
                const target = try storeTarget(&parent, parent_name, parent.out_fields, actual);
                if (target != null and target.? == .whole and prior.pointee.eql(coverage.pointee)) {
                    coverage.whole_source = prior.whole_source;
                    coverage.computed_sources = prior.computed_sources;
                    coverage.computed_original_alternative = prior.computed_original_alternative;
                    coverage.computed_opaque_alternative = prior.computed_opaque_alternative;
                    coverage.computed_overflow = prior.computed_overflow;
                }
            };
        };
        var exits: ?StoreCoverage = null;
        const falls_through = try self.definiteStoreBody(&context, &proof, body, &coverage, &exits);
        // An unavailable byte recipe revokes value/identity credit, not a
        // source-proved must-store. Resource failures still propagate above.
        if (proof.written_dependencies_complete) |complete| if (!complete.*) {
            if (may_written_stores) |stores| {
                for (coverage.field_names[0..coverage.field_count], coverage.written_dependencies[0..coverage.field_count]) |path, recipe| {
                    if (!recipe.isEmpty()) _ = stores.add(path, recipe);
                }
                if (exits) |final| {
                    for (final.field_names[0..final.field_count], final.written_dependencies[0..final.field_count]) |path, recipe| {
                        if (!recipe.isEmpty()) _ = stores.add(path, recipe);
                    }
                }
            }
            if (proof.written_inputs == null) return null;
            coverage.computed_overflow = true;
            if (exits) |*final| final.computed_overflow = true;
        };
        if (falls_through orelse return null) intersectStoreExit(&exits, coverage);
        if (computed_use) |use| {
            const final = exits orelse return null;
            const root = computedCoverageBase(&final);
            var selected_reads: u8 = if (final.field_count == 0) final.whole_dependencies.reads else 0;
            for (final.covered[0..final.field_count], final.written_dependencies[0..final.field_count]) |covered, recipe| {
                if (covered) selected_reads |= recipe.reads;
            }
            for (use.may_written_stores.dependencies[0..use.may_written_stores.count]) |recipe| {
                selected_reads |= recipe.reads;
            }
            // A conditional source effect needs both its computed output and
            // its untouched entry alternative, even without must-store credit.
            var consume_root = final.complete or
                (root.original_alternative and (root.computations != 0 or root.opaque_alternative));
            if (!final.complete) {
                for (final.field_names[0..final.field_count], final.covered[0..final.field_count], 0..) |path, covered, slot| {
                    if (!covered) continue;
                    var memo: [8]?ComputedFieldRecipe = @splat(null);
                    const recipe = computedFieldRecipe(&local_templates, root, path, &memo);
                    consume_root = consume_root or recipe.needs_root;
                    if (!recipe.needs_root) {
                        use.location_field_sources[slot] = recipe.source;
                        selected_reads |= recipe.source.projections;
                    }
                }
                if (consume_root) {
                    @memset(use.location_field_sources[0..final.field_count], null);
                }
            }
            const published = !final.computed_overflow and
                try local_templates.publish(self, root, consume_root, reads.?, selected_reads, use);
            use.location_computed_complete = published;
            use.location_computed_sources = if (published and consume_root) root.computations else 0;
            use.location_computed_original_alternative = published and consume_root and root.original_alternative;
            use.location_computed_opaque_alternative = published and consume_root and root.opaque_alternative;
            if (!published) {
                for (final.field_names[0..final.field_count], final.written_dependencies[0..final.field_count]) |path, dependencies| {
                    if (!dependencies.isEmpty()) _ = use.may_written_stores.add(path, dependencies);
                    if (computedFieldLiteralMay(&local_templates, root.computations, path))
                        _ = use.may_written_stores.addLiteral(path);
                }
            }
        }
        return exits;
    }

    const StoreBodyContext = struct {
        canonical: ActualCallSummary,
        call_node: Ast.Node.Index,
        call_tree: *const Ast,
        name: []const u8,
        fields: []const []const u8,
        defaults: []const ?Ast.Node.Index,
        visiting: []const StoreVisit,
        success_bool: ?bool,
        returning: bool = false,
        value_label: ?Ast.TokenIndex = null,
        loop_proof: ?*const DefiniteStoreProof = null,
        loop_coverage: ?*const StoreCoverage = null,
        loop_body: ?Ast.Node.Index = null,
        loop_node: ?Ast.Node.Index = null,
    };

    fn intersectStoreCoverage(target: *StoreCoverage, other: StoreCoverage) void {
        if (target.whole_source != null or other.whole_source != null)
            target.whole_source = WholeStoreSource.merge(target.whole_source orelse .{}, other.whole_source orelse .{});
        target.complete = target.complete and other.complete;
        target.whole_dependencies.merge(other.whole_dependencies);
        target.computed_sources |= other.computed_sources;
        target.computed_original_alternative = target.computed_original_alternative or other.computed_original_alternative;
        target.computed_opaque_alternative = target.computed_opaque_alternative or other.computed_opaque_alternative;
        target.computed_overflow = target.computed_overflow or other.computed_overflow;
        target.effects_known = target.effects_known and other.effects_known;
        for (target.covered[0..target.field_count], other.covered[0..other.field_count], target.written_dependencies[0..target.field_count], other.written_dependencies[0..other.field_count]) |*mine, theirs, *dependencies, incoming| {
            mine.* = mine.* and theirs;
            dependencies.merge(incoming);
        }
    }

    fn intersectStoreExit(exits: *?StoreCoverage, coverage: StoreCoverage) void {
        if (exits.*) |*prior| intersectStoreCoverage(prior, coverage) else exits.* = coverage;
    }

    /// Only bindings visible before a branch survive its lexical scope.
    /// A disagreement cannot establish a defined source on the merged path.
    fn mergeStoreProof(target: *DefiniteStoreProof, other: *const DefiniteStoreProof, count: usize) bool {
        target.binding_count = count;
        target.written_dependencies.merge(other.written_dependencies);
        for (target.bindings[0..count], other.bindings[0..count]) |*mine, theirs| {
            mine.written_dependencies.merge(theirs.written_dependencies);
            if (theirs.aggregate_source) |source| {
                mine.aggregate_source = if (mine.aggregate_source) |current|
                    WholeStoreSource.merge(current, source)
                else
                    source;
            }
            mine.value_nonidentity = mine.value_nonidentity or theirs.value_nonidentity;
            mine.computed_sources |= theirs.computed_sources;
            mine.computed_original_alternative = mine.computed_original_alternative or theirs.computed_original_alternative;
            mine.computed_opaque_alternative = mine.computed_opaque_alternative or theirs.computed_opaque_alternative;
            if (mine.value != theirs.value) mine.value = .undefined_value;
            mine.complete_value = mine.complete_value and theirs.complete_value;
            mine.literal_undefined = mine.literal_undefined and theirs.literal_undefined;
            mine.literal_may_undefined = mine.literal_may_undefined or theirs.literal_may_undefined;
            if (mine.formal_alias != theirs.formal_alias) mine.formal_alias = null;
            if (mine.aggregate_source != null or theirs.aggregate_source != null)
                mine.aggregate_source = WholeStoreSource.merge(mine.aggregate_source orelse .{}, theirs.aggregate_source orelse .{});
        }
        for (target.pointees[0..target.pointee_count]) |*pointee| {
            const name = target.tree.tokenSlice(pointee.token);
            const theirs = other.findStorePointeeEntry(name);
            if (pointee.value != (if (theirs) |entry| entry.value else .unknown))
                pointee.value = .unknown;
            pointee.computed = mergeComputedPointeeState(
                pointee.computed, if (theirs) |entry| entry.computed else null,
            );
        }
        for (other.pointees[0..other.pointee_count]) |pointee| {
            const name = other.tree.tokenSlice(pointee.token);
            if (target.findStorePointee(name) == null) {
                if (!target.setStorePointee(pointee.token, .unknown)) return false;
                target.pointees[target.pointee_count - 1].computed =
                    mergeComputedPointeeState(null, pointee.computed);
            }
        }
        for (target.field_facts[0..target.field_fact_count]) |*fact| {
            const name = target.tree.tokenSlice(fact.token);
            if (other.findStoreFieldFact(name, fact.path)) |theirs| {
                fact.written_dependencies.merge(theirs.written_dependencies);
                if (fact.value != theirs.value) fact.value = .unknown;
            } else {
                fact.value = .unknown;
            }
        }
        for (other.field_facts[0..other.field_fact_count]) |fact| {
            if (!fact.fallback_recipe) continue;
            if (!recordComputedFallbackFact(target, fact.token, fact.path, fact.written_dependencies, fact.fallback_literal_may)) return false;
        }
        return true;
    }

    /// A by-value union payload copies part of an already defined selector.
    /// Its complete-value certificate does not initialize storage behind pointers.
    fn bindStoreSwitchPayload(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        condition: Ast.Node.Index,
        case: Ast.full.SwitchCase,
    ) SummaryError!bool {
        const capture = case.payload_token orelse return true;
        const tree = proof.tree;
        if (tree.tokenTag(capture) != .identifier or
            tree.tokenTag(capture + 1) != .pipe or case.ast.values.len != 1) return false;
        const variant = case.ast.values[0];
        if (tree.nodeTag(variant) != .enum_literal) return false;
        const value_type = (try proof.frame.typeOfNode(condition)) orelse return false;
        const resolver = proof.frame.resolver;
        const actual = (try resolver.normalizedType(value_type)) orelse return false;
        if (resolver.typeTag(actual) != .@"union" or actual.data != .container) return false;
        const owner = resolver.frameForContainer(actual.data.container);
        const owner_tree = &owner.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = owner_tree.fullContainerDecl(&buffer, actual.data.container.scope_handle.toNode()) orelse return false;
        const wanted = tree.tokenSlice(tree.nodeMainToken(variant));
        for (declaration.ast.members) |member| {
            try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
            const field = owner_tree.fullContainerField(member) orelse continue;
            if (!std.mem.eql(u8, owner_tree.tokenSlice(field.ast.main_token), wanted)) continue;
            const type_node = field.ast.type_expr.unwrap() orelse return false;
            const field_type = (try owner.typeOfNode(type_node)) orelse return false;
            const payload_type = (try resolver.normalizedType(field_type)) orelse return false;
            switch (resolver.typeTag(payload_type) orelse return false) {
                .int, .comptime_int, .float, .comptime_float, .bool, .@"enum",
                .@"struct", .@"union", .pointer, .optional, .array, .vector, .error_union, .error_set => {},
                else => return false,
            }
            if (!proof.bind(capture, .defined)) return false;
            proof.bindings[proof.binding_count - 1].complete_value = true;
            return true;
        }
        return false;
    }

    fn passiveStoreExpression(self: *FileCache, proof: *const DefiniteStoreProof, node: Ast.Node.Index, depth: u32) SummaryError!bool {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        if (depth >= 64) return self.cleanupBudgetFailureAt(proof.call_tree, .normal_cleanup_depth, 64, proof.call_node);
        switch (proof.tree.nodeTag(node)) {
            .identifier, .number_literal, .char_literal, .enum_literal,
            .grouped_expression, .array_access, .field_access,
            .negation, .bit_not, .bool_not, .add, .sub, .mul, .div, .mod,
            .bit_and, .bit_or, .bit_xor, .shl, .shr,
            .equal_equal, .bang_equal, .less_than, .greater_than,
            .less_or_equal, .greater_or_equal, .bool_and, .bool_or,
            => {},
            else => return false,
        }
        var children = engine.AstIterator.init(proof.tree, node);
        while (children.next(proof.tree)) |child| {
            if (!try self.passiveStoreExpression(proof, child, depth + 1)) return false;
        }
        return true;
    }

    /// One source/control-authenticated resume, not a loop fixed point:
    /// the first if arm changes scalar locals, clears its boolean selector,
    /// then continues. The next iteration skips that arm and runs a passive
    /// field-store suffix ending in a void return. Calls, aliases, extra
    /// control flow and mutated source storage are outside this evidence.
    fn recordContinueMayStores(
        self: *FileCache,
        context: *const StoreBodyContext,
        proof: *const DefiniteStoreProof,
        before: *const DefiniteStoreProof,
        continued: Ast.Node.Index,
    ) SummaryError!void {
        const stores = proof.may_written_stores orelse return;
        if (!proof.written_input_boundary or context.success_bool != null) return;
        const tree = proof.tree;
        const body = context.loop_body orelse return;
        const loop_node = context.loop_node orelse return;
        const function_body = tokens.bodyOf(tree, context.canonical.callee.declaration) orelse return;
        var prefix = engine.AstIterator.init(tree, function_body);
        var reached_loop = false;
        while (prefix.next(tree)) |statement| {
            if (statement == loop_node) {
                reached_loop = true;
                break;
            }
            if (tree.fullVarDecl(statement)) |variable| {
                const initial = variable.ast.init_node.unwrap() orelse return;
                if (try definiteStoreKind(proof, initial) != .scalar or
                    !try self.passiveStoreExpression(proof, initial, 0)) return;
            } else if (tree.nodeTag(statement) == .assign) {
                const lhs, const rhs = tree.nodeData(statement).node_and_node;
                if (tree.nodeTag(lhs) != .identifier or
                    try definiteStoreKind(proof, lhs) != .scalar or
                    proof.findIndex(tree.tokenSlice(tree.nodeMainToken(lhs))) == null or
                    !try self.passiveStoreExpression(proof, rhs, 0)) return;
            } else return;
        }
        if (!reached_loop) return;
        switch (tree.nodeTag(body)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {},
            else => return,
        }
        var statements = engine.AstIterator.init(tree, body);
        const first = statements.next(tree) orelse return;
        const branch = tree.fullIf(first) orelse return;
        if (branch.payload_token != null or branch.error_token != null or
            branch.ast.else_expr != .none or tree.nodeTag(branch.ast.cond_expr) != .identifier) return;
        if ((try proof.frame.isBoolType(branch.ast.cond_expr)) != true) return;
        const selector_name = tree.tokenSlice(tree.nodeMainToken(branch.ast.cond_expr));
        const selector = before.findIndex(selector_name) orelse return;
        if (before.bindings[selector].formal_alias != null) return;
        switch (tree.nodeTag(branch.ast.then_expr)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {},
            else => return,
        }
        var arm = engine.AstIterator.init(tree, branch.ast.then_expr);
        var selector_false = false;
        var found_continue = false;
        while (arm.next(tree)) |statement| {
            try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
            if (statement == continued) {
                if (arm.next(tree) != null) return;
                found_continue = true;
                break;
            }
            if (tree.nodeTag(statement) != .assign) return;
            const lhs, const rhs = tree.nodeData(statement).node_and_node;
            if (tree.nodeTag(lhs) != .identifier or
                try definiteStoreKind(proof, lhs) != .scalar or
                !try self.passiveStoreExpression(proof, rhs, 0)) return;
            const assigned = before.findIndex(tree.tokenSlice(tree.nodeMainToken(lhs))) orelse return;
            if (before.bindings[assigned].formal_alias != null) return;
            if (assigned == selector) {
                selector_false = tree.nodeTag(rhs) == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(rhs)), "false");
            }
        }
        if (!found_continue or !selector_false) return;

        var recipes: [128]WrittenDependencies = @splat(.{});
        var returned = false;
        while (statements.next(tree)) |statement| {
            try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
            if (tree.nodeTag(statement) == .@"return") {
                if (tree.nodeData(statement).opt_node != .none or statements.next(tree) != null) return;
                returned = true;
                break;
            }
            if (tree.nodeTag(statement) != .assign) return;
            const lhs, const rhs = tree.nodeData(statement).node_and_node;
            if (try definiteStoreKind(proof, lhs) != .scalar) return;
            const field = (try storeFieldIndex(proof, context.name, context.fields, lhs)) orelse return;
            var recipe: WrittenDependencies = .{};
            switch (tree.nodeTag(rhs)) {
                .number_literal, .char_literal, .enum_literal => {},
                .identifier => {
                    const name = tree.tokenSlice(tree.nodeMainToken(rhs));
                    if (!std.mem.eql(u8, name, "true") and !std.mem.eql(u8, name, "false") and
                        !std.mem.eql(u8, name, "null"))
                    {
                        const binding = proof.findIndex(name) orelse return;
                        if (binding >= before.binding_count or
                            proof.bindings[binding].token != before.bindings[binding].token or
                            proof.bindings[binding].formal_alias != null or
                            try definiteStoreKind(proof, rhs) != .scalar) return;
                        // Only a saved source lineage changed by this resume
                        // contributes an alternative; old/global inputs do not.
                        if (!proof.bindings[binding].written_dependencies.eql(before.bindings[binding].written_dependencies))
                            recipe = proof.bindings[binding].written_dependencies;
                    }
                },
                else => return,
            }
            // A later unconditional scalar overwrite replaces its source.
            recipes[field] = recipe;
        }
        if (!returned) return;
        for (context.fields, recipes[0..context.fields.len]) |path, recipe| {
            if (recipe.inputs == 0 and recipe.reads == 0) continue;
            if (!stores.add(path, recipe)) return;
        }
    }

    /// `true` falls through; `false` exits. Null is an unsupported proof.
    /// Branches carry independent lexical state and coverage. Their successful
    /// returns join the exit meet, not the continuing statement's state.
    fn definiteStoreBody(
        self: *FileCache,
        context: *const StoreBodyContext,
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        coverage: *StoreCoverage,
        exits: *?StoreCoverage,
    ) SummaryError!?bool {
        try self.chargeNormalCleanupAt(context.call_tree, context.call_node);
        try self.enterNormalCleanupAt(context.call_tree, context.call_node);
        defer self.leaveNormalCleanup();
        const tree = proof.tree;
        proof.out_coverage = coverage;
        switch (tree.nodeTag(node)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                const count = proof.binding_count;
                var nested_context = context.*;
                const first = tree.firstToken(node);
                if (tree.tokenTag(first) == .identifier and tree.tokenTag(first + 1) == .colon) {
                    if (!context.returning) return null;
                    nested_context.value_label = first;
                    nested_context.returning = false;
                }
                var statements = engine.AstIterator.init(tree, node);
                while (statements.next(tree)) |statement| {
                    const continuing = (try self.definiteStoreBody(&nested_context, proof, statement, coverage, exits)) orelse return null;
                    if (!continuing) {
                        proof.binding_count = count;
                        return false;
                    }
                }
                proof.binding_count = count;
                return if (context.returning) null else true;
            },
            .@"return" => {
                if (tree.nodeData(node).opt_node.unwrap()) |value| {
                    var returning_context = context.*;
                    returning_context.returning = true;
                    returning_context.value_label = null;
                    return self.definiteStoreBody(&returning_context, proof, value, coverage, exits);
                }
                if (context.success_bool != null) return null;
                intersectStoreExit(exits, coverage.*);
                return false;
            },
            .@"break" => {
                if (context.value_label == null) return null;
                const label, const value = tree.nodeData(node).opt_token_and_opt_node;
                const wanted = context.value_label orelse return null;
                const actual = label.unwrap() orelse return null;
                if (!std.mem.eql(u8, tree.tokenSlice(wanted), tree.tokenSlice(actual))) return null;
                var returning_context = context.*;
                returning_context.returning = true;
                returning_context.value_label = null;
                return self.definiteStoreBody(&returning_context, proof, value.unwrap() orelse return null, coverage, exits);
            },
            .unreachable_literal, .error_value => {
                if (tree.nodeTag(node) == .error_value and !context.returning) return null;
                return false;
            },
            .@"continue" => {
                const before = context.loop_proof orelse return null;
                const initial = context.loop_coverage orelse return null;
                if (tree.lastToken(node) != tree.nodeMainToken(node) or
                    coverage.complete != initial.complete or coverage.field_count != initial.field_count or
                    !std.mem.eql(bool, coverage.covered[0..coverage.field_count], initial.covered[0..initial.field_count]) or
                    !WholeStoreSource.equal(coverage.whole_source, initial.whole_source)) return null;
                if (!coverage.whole_dependencies.eql(initial.whole_dependencies)) return null;
                if (coverage.computed_sources != initial.computed_sources or
                    coverage.computed_original_alternative != initial.computed_original_alternative or
                    coverage.computed_opaque_alternative != initial.computed_opaque_alternative or
                    coverage.computed_overflow != initial.computed_overflow) return null;
                for (coverage.written_dependencies[0..coverage.field_count], initial.written_dependencies[0..initial.field_count]) |current, original| {
                    if (!current.eql(original)) return null;
                }
                for (before.bindings[0..before.binding_count], proof.bindings[0..before.binding_count]) |original, current| {
                    if (original.value != current.value or original.complete_value != current.complete_value or
                        original.formal_alias != current.formal_alias or
                        !WholeStoreSource.equal(original.aggregate_source, current.aggregate_source) or
                        original.value_nonidentity != current.value_nonidentity or
                        !original.written_dependencies.eql(current.written_dependencies) or
                        original.computed_sources != current.computed_sources or
                        original.literal_undefined != current.literal_undefined or
                        original.literal_may_undefined != current.literal_may_undefined or
                        original.computed_original_alternative != current.computed_original_alternative or
                        original.computed_opaque_alternative != current.computed_opaque_alternative)
                    {
                        try self.recordContinueMayStores(context, proof, before, node);
                        return null;
                    }
                }
                if (before.pointee_count != proof.pointee_count) return null;
                for (before.pointees[0..before.pointee_count]) |original| {
                    const name = tree.tokenSlice(original.token);
                    const current = proof.findStorePointeeEntry(name) orelse return null;
                    if (current.value != original.value or
                        !ComputedPointeeState.equal(original.computed, current.computed)) return null;
                }
                if (before.field_fact_count != proof.field_fact_count) return null;
                for (before.field_facts[0..before.field_fact_count]) |original| {
                    const name = tree.tokenSlice(original.token);
                    const current = proof.findStoreFieldFact(name, original.path) orelse return null;
                    if (current.value != original.value or
                        !current.written_dependencies.eql(original.written_dependencies) or
                        current.fallback_recipe != original.fallback_recipe or
                        current.fallback_literal_may != original.fallback_literal_may) return null;
                }
                return false;
            },
            else => {},
        }
        if (tree.fullIf(node)) |branch| {
            if (branch.payload_token != null or branch.error_token != null) return null;
            const collecting = proof.collect_written_inputs;
            proof.collect_written_inputs = false;
            const condition = self.definiteStoreValue(proof, branch.ast.cond_expr, 0);
            proof.collect_written_inputs = collecting;
            if (try condition != .defined) return null;
            const count = proof.binding_count;
            var then_proof = proof.*;
            var then_coverage = coverage.*;
            const then_continues = (try self.definiteStoreBody(context, &then_proof, branch.ast.then_expr, &then_coverage, exits)) orelse return null;
            var else_proof = proof.*;
            var else_coverage = coverage.*;
            const else_continues = if (branch.ast.else_expr.unwrap()) |otherwise|
                (try self.definiteStoreBody(context, &else_proof, otherwise, &else_coverage, exits)) orelse return null
            else if (context.returning) return null else true;
            if (then_continues and else_continues) {
                if (!mergeStoreProof(&then_proof, &else_proof, count)) return null;
                intersectStoreCoverage(&then_coverage, else_coverage);
            }
            if (then_continues) {
                proof.* = then_proof;
                coverage.* = then_coverage;
            } else if (else_continues) {
                proof.* = else_proof;
                coverage.* = else_coverage;
            }
            proof.binding_count = count;
            proof.out_coverage = coverage;
            return then_continues or else_continues;
        }
        if (tree.fullSwitch(node)) |selection| {
            if (selection.label_token != null or selection.ast.cases.len == 0 or
                try self.definiteStoreValue(proof, selection.ast.condition, 0) != .defined) return null;
            const count = proof.binding_count;
            var continuing_proof: ?DefiniteStoreProof = null;
            var continuing_coverage: ?StoreCoverage = null;
            for (selection.ast.cases) |case_node| {
                const case = tree.fullSwitchCase(case_node) orelse return null;
                var arm_proof = proof.*;
                var arm_coverage = coverage.*;
                if (!try self.bindStoreSwitchPayload(&arm_proof, selection.ast.condition, case)) return null;
                const continuing = (try self.definiteStoreBody(context, &arm_proof, case.ast.target_expr, &arm_coverage, exits)) orelse return null;
                if (!continuing) continue;
                arm_proof.binding_count = count;
                if (continuing_proof) |*prior| {
                    if (!mergeStoreProof(prior, &arm_proof, count)) return null;
                    intersectStoreCoverage(&continuing_coverage.?, arm_coverage);
                } else {
                    continuing_proof = arm_proof;
                    continuing_coverage = arm_coverage;
                }
            }
            if (continuing_proof) |state| {
                proof.* = state;
                coverage.* = continuing_coverage.?;
                proof.out_coverage = coverage;
                return true;
            }
            return false;
        }
        if (tree.fullWhile(node)) |loop| {
            if (context.returning or loop.label_token != null or loop.payload_token != null or loop.error_token != null or
                loop.ast.else_expr != .none or loop.ast.cont_expr != .none or
                tree.nodeTag(loop.ast.cond_expr) != .identifier or
                !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(loop.ast.cond_expr)), "true")) return null;
            const before = proof.*;
            const initial = coverage.*;
            var looping_context = context.*;
            looping_context.loop_proof = &before;
            looping_context.loop_coverage = &initial;
            looping_context.loop_body = loop.ast.then_expr;
            looping_context.loop_node = node;
            const continuing = (try self.definiteStoreBody(&looping_context, proof, loop.ast.then_expr, coverage, exits)) orelse return null;
            // A body fallthrough also restarts the loop; only proven
            // terminating paths and unchanged bare continues are supported.
            if (continuing) return null;
            return false;
        }
        if (tree.fullFor(node) != null) {
            if (context.returning or !try self.definiteStoreLoop(proof, context.canonical, context.call_node, context.name, context.fields, node, context.visiting, coverage)) return null;
            return true;
        }
        if (context.returning) {
            if (context.success_bool) |wanted| {
                if (tree.nodeTag(node) == .identifier) {
                    const value = tree.tokenSlice(tree.nodeMainToken(node));
                    if ((std.mem.eql(u8, value, "true") and !wanted) or
                        (std.mem.eql(u8, value, "false") and wanted)) return false;
                }
            }
            if (storeCall(tree, node)) |nested_call| {
                if (!try self.definiteNestedStore(proof, context.canonical, context.call_node, context.name, context.fields, nested_call, context.visiting, coverage, true) and proof.written_inputs == null) return null;
            } else if (try self.definiteStoreValue(proof, node, 0) != .defined) return null;
            intersectStoreExit(exits, coverage.*);
            return false;
        }
        if (tree.fullVarDecl(node)) |declaration| {
            if (std.mem.eql(u8, tree.tokenSlice(declaration.ast.mut_token + 1), context.name)) return null;
            const value = declaration.ast.init_node.unwrap() orelse return null;
            const alias = try self.definiteStoreFormalAlias(proof, value);
            proof.written_dependencies = .{};
            const evaluated = try self.definiteStoreValueWithComputed(proof, value, 0);
            const verdict = evaluated.value;
            if (verdict == .unknown or !proof.bind(declaration.ast.mut_token + 1, verdict)) return null;
            const binding = &proof.bindings[proof.binding_count - 1];
            binding.written_dependencies = proof.written_dependencies;
            binding.aggregate_source = evaluated.computed.source;
            binding.computed_sources = evaluated.computed.computations;
            binding.computed_original_alternative = evaluated.computed.original_alternative;
            binding.computed_opaque_alternative = evaluated.computed.opaque_alternative;
            binding.value_nonidentity = evaluated.computed.value_nonidentity;
            binding.literal_undefined = evaluated.literal_undefined;
            binding.literal_may_undefined = evaluated.literal_may_undefined;
            binding.complete_value =
                verdict == .defined and try definiteStoreKind(proof, value) == .aggregate;
            binding.formal_alias = alias;
            copyComputedFallbackFacts(proof, evaluated.computed.fallback_token, binding.token);
            return true;
        }
        if (tree.nodeTag(node) != .assign) {
            if (storeCall(tree, node)) |nested_call| {
                if (!try self.definiteNestedStore(proof, context.canonical, context.call_node, context.name, context.fields, nested_call, context.visiting, coverage, node != nested_call)) {
                    if (proof.written_inputs == null) return null;
                    try self.unprovedStoreCallOutputs(proof, nested_call);
                    try self.definiteStoreEscapes(proof, nested_call, 0);
                }
                return true;
            }
            var builtin_buffer: [2]Ast.Node.Index = undefined;
            const arguments = tree.builtinCallParams(&builtin_buffer, node) orelse return null;
            const builtin = std.zig.BuiltinFn.list.get(tree.tokenSlice(tree.nodeMainToken(node))) orelse return null;
            if (builtin.tag != .set_float_mode or arguments.len != 1 or tree.nodeTag(arguments[0]) != .enum_literal or
                std.meta.stringToEnum(std.builtin.FloatMode, tree.tokenSlice(tree.lastToken(arguments[0]))) == null) return null;
            return true;
        }
        const lhs, const rhs = tree.nodeData(node).node_and_node;
        proof.written_dependencies = .{};
        const evaluated = try self.definiteStoreValueWithComputed(proof, rhs, 0);
        const verdict = evaluated.value;
        if (verdict == .unknown) return null;
        if (tree.nodeTag(lhs) == .identifier) {
            const token = tree.nodeMainToken(lhs);
            if (std.mem.eql(u8, tree.tokenSlice(token), "_")) return true;
            const binding = proof.find(tree.tokenSlice(token)) orelse return null;
            // Rebinding a copied pointer destroys its exact formal identity.
            if (binding.formal_alias != null) return null;
            proof.invalidateStoreFields(tree.tokenSlice(token));
            binding.complete_value = false;
            binding.value = verdict;
            binding.written_dependencies = proof.written_dependencies;
            binding.aggregate_source = evaluated.computed.source;
            binding.computed_sources = evaluated.computed.computations;
            binding.computed_original_alternative = evaluated.computed.original_alternative;
            binding.computed_opaque_alternative = evaluated.computed.opaque_alternative;
            binding.value_nonidentity = evaluated.computed.value_nonidentity;
            binding.literal_undefined = evaluated.literal_undefined;
            binding.literal_may_undefined = evaluated.literal_may_undefined;
            copyComputedFallbackFacts(proof, evaluated.computed.fallback_token, binding.token);
            return true;
        }
        // Nested coverage joins require no-poison must certificates. Without
        // a kill mask, returning partial coverage after a poison could retain
        // an earlier wrapper write. Such helpers must abstain in full.
        if (verdict != .defined) return null;
        if (tree.nodeTag(lhs) == .deref) {
            const base = tree.nodeData(lhs).node;
            if (tree.nodeTag(base) != .identifier) return null;
            const base_name = tree.tokenSlice(tree.nodeMainToken(base));
            if (proof.find(base_name)) |binding| {
                if (binding.formal_alias == null) return null;
            }
            if (!std.mem.eql(u8, proof.formalName(base_name), context.name)) {
                // The RHS already has a complete defined-value proof. A
                // defined aggregate store cannot poison this other output.
                if (!(try self.definiteStoreOtherFormal(proof, base) orelse false)) return null;
                if (proof.computed_templates != null) {
                    if (!try self.recordOtherPointeeStore(proof, lhs, rhs, evaluated)) return null;
                } else if (!proof.setStorePointee(tree.nodeMainToken(base), .defined)) return null;
                return true;
            }
            coverage.whole_dependencies = proof.written_dependencies;
            setComputedStoreWholeReplacement(proof, coverage, evaluated);
            if (proof.computed_templates) |builders| {
                for (coverage.field_names[0..coverage.field_count], coverage.written_dependencies[0..coverage.field_count]) |path, *dependencies| {
                    dependencies.* = computedFieldDependencies(builders, coverage.computed_sources, path);
                }
            } else {
                @memset(coverage.written_dependencies[0..coverage.field_count], proof.written_dependencies);
            }
            if (proof.written_inputs != null) {
                if (proof.computed_templates == null) {
                    coverage.whole_source = null;
                    switch (proof.frame.resolver.typeTag(coverage.pointee) orelse return null) {
                        .@"struct", .@"union", .array, .vector => {
                            coverage.whole_source = .{};
                            if (try wholeStoreType(proof, rhs)) |source_type| {
                                if (source_type.eql(coverage.pointee)) coverage.whole_source = evaluated.computed.source orelse WholeStoreSource{};
                            }
                        },
                        else => {}, // Scalars retain their separate dependency recipe.
                    }
                }
                @memset(coverage.covered[0..coverage.field_count], true);
                coverage.complete = true;
                if (!proof.setStorePointee(tree.nodeMainToken(base), .defined)) return null;
                return true;
            }
            var literal_buffer: [2]Ast.Node.Index = undefined;
            if (tree.fullStructInit(&literal_buffer, rhs)) |literal| {
                if (coverage.field_count != 0) {
                    @memset(coverage.covered[0..coverage.field_count], false);
                    for (context.fields, 0..) |field_name, field_index| {
                        if (std.mem.indexOfScalar(u8, field_name, '.') != null) continue;
                        var supplied = false;
                        for (literal.ast.fields) |value| {
                            const first = tree.firstToken(value);
                            if (first >= 3 and tree.tokenTag(first - 1) == .equal and
                                std.mem.eql(u8, tree.tokenSlice(first - 2), field_name)) supplied = true;
                        }
                        if (!supplied) {
                            const default_value = context.defaults[field_index] orelse return null;
                            const default_frame = proof.frame.resolver.frameForContainer(coverage.pointee.data.container);
                            var default_proof: DefiniteStoreProof = .{
                                .tree = &default_frame.handle.document.tree,
                                .frame = default_frame,
                                .call_node = context.call_node,
                                .call_tree = context.call_tree,
                            };
                            if (try self.definiteStoreValue(&default_proof, default_value, 1) != .defined) return null;
                        }
                        coverStoreField(coverage, field_index);
                    }
                }
            } else @memset(coverage.covered[0..coverage.field_count], true);
            coverage.complete = true;
            if (!proof.setStorePointee(tree.nodeMainToken(base), .defined)) return null;
            return true;
        }
        if (tree.nodeTag(lhs) == .field_access or
            (tree.nodeTag(lhs) == .array_access and proof.written_inputs != null))
        {
            const field_root = tokens.rootIdentifier(tree, lhs) orelse return null;
            if (proof.computed_templates != null and
                !std.mem.eql(u8, proof.formalName(tree.tokenSlice(tree.nodeMainToken(field_root))), context.name) and
                (try self.definiteStoreOtherFormal(proof, field_root) orelse false))
                return try self.recordOtherPointeeStore(proof, lhs, rhs, evaluated);
            if (proof.find(tree.tokenSlice(tree.nodeMainToken(field_root)))) |binding| {
                if (proof.computed_templates == null or binding.formal_alias != null) return null;
                const resolver = proof.frame.resolver;
                const actual = (try proof.frame.typeOfNode(field_root)) orelse return null;
                const ty = (try resolver.normalizedType(actual)) orelse return null;
                var fields: [128][]const u8 = undefined;
                var defaults: [128]?Ast.Node.Index = @splat(null);
                var mapped: StoreCoverage = .{ .pointee = ty };
                if (!try self.storeCoverageFields(ty, &fields, &defaults, &mapped, proof.call_tree, proof.call_node)) return null;
                const selected = (try storeFieldIndex(proof, tree.tokenSlice(tree.nodeMainToken(field_root)), fields[0..mapped.field_count], lhs)) orelse return null;
                const path = fields[selected];
                const base_state: ComputedStoreBase = .{
                    .source = binding.aggregate_source,
                    .computations = binding.computed_sources,
                    .original_alternative = binding.computed_original_alternative,
                    .opaque_alternative = binding.computed_opaque_alternative,
                };
                if (!proof.setStoreField(tree.nodeMainToken(field_root), path, verdict, proof.written_dependencies)) return null;
                const write = try self.computedStoreWriteForValue(
                    proof, path, rhs, evaluated, proof.written_dependencies, false, null, null,
                );
                if (appendComputedFieldStoreWrite(proof, base_state, write, evaluated.computed, fields[0..mapped.field_count])) |result| {
                    binding.aggregate_source = result.source;
                    binding.computed_sources = result.computations;
                    binding.computed_original_alternative = result.original_alternative;
                    binding.computed_opaque_alternative = result.opaque_alternative;
                } else {
                    binding.computed_opaque_alternative = true;
                    _ = recordComputedFallbackFact(proof, binding.token, path, write.dependencies, write.literal_undefined or write.literal_may_undefined);
                }
                binding.value_nonidentity = true;
                return true;
            }
            if (try storeFieldIndex(proof, context.name, context.fields, lhs)) |index| {
                const prior_base = computedCoverageBase(coverage);
                // A selected overwrite is not a whole-parent identity.
                if (coverage.whole_source != null) coverage.whole_source = .{};
                coverStoreField(coverage, index);
                recordWrittenStoreField(coverage, index, proof.written_dependencies);
                if (proof.computed_templates != null) {
                    const write = try self.computedStoreWriteForValue(
                        proof, context.fields[index], rhs, evaluated, proof.written_dependencies, false, null, null,
                    );
                    if (appendComputedFieldStoreWrite(proof, prior_base, write, evaluated.computed, context.fields)) |result| {
                        coverage.whole_source = result.source;
                        coverage.computed_sources = result.computations;
                        coverage.computed_original_alternative = result.original_alternative;
                        coverage.computed_opaque_alternative = result.opaque_alternative;
                    } else {
                        coverage.computed_overflow = true;
                        if (write.literal_undefined or write.literal_may_undefined) {
                            if (proof.may_written_stores) |stores| _ = stores.addLiteral(context.fields[index]);
                        }
                    }
                }
                if (coverage.complete) {
                    const root = tokens.rootIdentifier(tree, lhs) orelse return null;
                    if (!proof.setStorePointee(tree.nodeMainToken(root), .defined)) return null;
                }
                return true;
            }
            const root = tokens.rootIdentifier(tree, lhs) orelse return null;
            return self.definiteStoreOtherFormal(proof, root);
        }
        if (tree.nodeTag(lhs) == .array_access) {
            const base, const index = tree.nodeData(lhs).node_and_node;
            const root = tokens.rootIdentifier(tree, base) orelse return null;
            if (!(try self.definiteStoreOtherFormal(proof, root) orelse false) or
                try self.definiteStoreValue(proof, index, 0) != .defined) return null;
            // Typed physical recipes retain intrinsic poison as a selected byte
            // write. The strict scalar RHS admission below remains unchanged.
            if (proof.computed_templates != null and
                !std.mem.eql(u8, proof.formalName(tree.tokenSlice(tree.nodeMainToken(root))), context.name))
                return try self.recordOtherPointeeStore(proof, lhs, rhs, evaluated);
            const actual = (try proof.frame.typeOfNode(rhs)) orelse return null;
            const normalized = (try proof.frame.resolver.normalizedType(actual)) orelse return null;
            switch (proof.frame.resolver.typeTag(normalized) orelse return null) {
                .int, .float, .comptime_int, .comptime_float, .bool, .@"enum", .enum_literal => {},
                else => return null,
            }
            // One known scalar element cannot poison an earlier certificate,
            // but does not establish initialization of the entire array.
            return true;
        }
        return null;
    }

    fn wholeStoreType(proof: *const DefiniteStoreProof, node: Ast.Node.Index) SummaryError!?TypeResolver.ActualType {
        const actual = (try proof.frame.typeOfNode(node)) orelse return null;
        const normalized = (try proof.frame.resolver.normalizedType(actual)) orelse return null;
        switch (proof.frame.resolver.typeTag(normalized) orelse return null) {
            .@"struct", .@"union", .array, .vector => return normalized,
            else => return null,
        }
    }

    fn storeProjectionType(proof: *const DefiniteStoreProof, node: Ast.Node.Index) SummaryError!?TypeResolver.ActualType {
        const actual = (try proof.frame.typeOfNode(node)) orelse return null;
        return proof.frame.resolver.normalizedType(actual);
    }

    fn passiveWholeStorePlace(self: *FileCache, proof: *const DefiniteStoreProof, node: Ast.Node.Index, depth: u32) SummaryError!bool {
        try self.chargeNormalCleanupAt(proof.tree, node);
        if (depth == 64) return self.cleanupBudgetFailureAt(proof.tree, .normal_cleanup_depth, 64, node);
        switch (proof.tree.nodeTag(node)) {
            .identifier => return !std.mem.eql(u8, proof.tree.tokenSlice(proof.tree.nodeMainToken(node)), "undefined"),
            .grouped_expression => return self.passiveWholeStorePlace(proof, proof.tree.nodeData(node).node_and_token[0], depth + 1),
            .field_access => {
                const owner = proof.tree.nodeData(node).node_and_token[0];
                const owner_type = (try wholeStoreType(proof, owner)) orelse return false;
                const tag = proof.frame.resolver.typeTag(owner_type) orelse return false;
                if (tag != .@"struct" and tag != .@"union") return false;
                return self.passiveWholeStorePlace(proof, owner, depth + 1);
            },
            else => return false,
        }
    }

    /// Follow syntactic by-value identities into the original caller's AST.
    /// Dependency masks are neither consulted nor used as copying authority.
    fn wholeStoreSource(self: *FileCache, proof: *DefiniteStoreProof, node: Ast.Node.Index, depth: u32) SummaryError!?WholeStoreSource {
        const inputs = proof.identity_inputs orelse return null;
        _ = proof.identity_tree orelse return null;
        try self.chargeNormalCleanupAt(proof.tree, node);
        if (depth == 64) return self.cleanupBudgetFailureAt(proof.tree, .normal_cleanup_depth, 64, node);
        if (proof.tree.nodeTag(node) == .field_access) {
            if (try wholeStoreType(proof, node) != null)
                return self.wholeStoreFieldSource(proof, node, depth + 1);
            if (!try self.passiveWholeStorePlace(proof, node, depth + 1)) return null;
            const path = (try self.storeProjectionPath(proof.tree, node)) orelse return null;
            const root = tokens.rootIdentifier(proof.tree, node) orelse return null;
            const base = (try self.wholeStoreSource(proof, root, depth + 1)) orelse return null;
            const source = (try self.wholeStoreFieldSourceProjection(proof, base, path, node)) orelse return null;
            return if (source.sources != 0 or source.projections != 0) source else null;
        }
        if (try wholeStoreType(proof, node) == null) {
            if (!proof.identity_leaf) return null;
            var literal_buffer: [2]Ast.Node.Index = undefined;
            if (proof.tree.fullStructInit(&literal_buffer, node) == null and
                proof.tree.fullArrayInit(&literal_buffer, node) == null) return null;
            const expected = (try proof.frame.expectedTypeOfNode(node)) orelse return null;
            const actual = (try proof.frame.resolver.normalizedType(expected)) orelse return null;
            switch (proof.frame.resolver.typeTag(actual) orelse return null) {
                .@"struct", .@"union", .array, .vector => {},
                else => return null,
            }
        }
        if (proof.identity_leaf) {
            // Only an exact caller argument slot proves whole-value identity.
            for (inputs, 0..) |*entry, index| {
                if (entry.* == node) return .{ .sources = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
            }
            for (inputs, 0..) |*entry, index| {
                if (entry.* != null) continue;
                entry.* = node;
                return .{ .sources = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
            }
            return wholeStoreSourceOverflow(proof);
        }
        if (!try self.passiveWholeStorePlace(proof, node, depth)) return WholeStoreSource{};
        if (proof.tree.nodeTag(node) == .grouped_expression)
            return self.wholeStoreSource(proof, proof.tree.nodeData(node).node_and_token[0], depth + 1);
        if (proof.tree.nodeTag(node) == .field_access)
            return self.wholeStoreFieldSource(proof, node, depth + 1);
        if (proof.tree.nodeTag(node) != .identifier) return WholeStoreSource{};
        const name = proof.tree.tokenSlice(proof.tree.nodeMainToken(node));
        if (proof.findIndex(name)) |binding| {
            const source = proof.bindings[binding].aggregate_source;
            const is_formal = binding < proof.parameter_count and proof.bindings[binding].formal_alias == null;
            if (source) |identity| return identity;
            if (!is_formal) return WholeStoreSource{};
            // A formal without a recipe must still map through the actual call
            // edge; its local binding is not a source identity.
        }
        const canonical = proof.canonical orelse return WholeStoreSource{};
        const caller_cache = proof.caller_cache orelse return WholeStoreSource{};
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(proof.tree, &proto_buffer, canonical.callee.declaration) orelse return WholeStoreSource{};
        var parameters = proto.iterate(proof.tree);
        var parameter_index: u32 = 0;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            const token = parameter.name_token orelse continue;
            if (!std.mem.eql(u8, name, proof.tree.tokenSlice(token))) continue;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const actual = (try canonical.callArgumentFor(caller_cache, &argument_buffer, parameter_index)) orelse return WholeStoreSource{};
            if (proof.identity_input_boundary) {
                const resolver = caller_cache.zls orelse return WholeStoreSource{};
                var leaf: DefiniteStoreProof = .{
                    .tree = originTree(proof),
                    .frame = canonical.callee.caller_frame orelse resolver.resolutionFrame(),
                    .call_node = actual,
                    .call_tree = caller_cache.tree,
                    .identity_inputs = inputs,
                    .identity_tree = originTree(proof),
                    .identity_input_boundary = true,
                    .identity_leaf = true,
                    .written_inputs = proof.written_inputs,
                    .written_reads = proof.written_reads,
                };
                return caller_cache.wholeStoreSource(&leaf, actual, depth + 1);
            }
            const caller = proof.caller orelse return WholeStoreSource{};
            if (caller.*) |*parent| {
                // The origin table is shared, but each AST node stays paired with
                // the cache that owns it. Do not copy identities from dependencies.
                parent.identity_inputs = inputs;
                parent.identity_tree = originTree(proof);
                return caller_cache.wholeStoreSource(parent, actual, depth + 1);
            }
            return WholeStoreSource{};
        }
        return WholeStoreSource{};
    }

    fn originTree(proof: *const DefiniteStoreProof) *const Ast {
        return proof.identity_tree orelse proof.tree;
    }

    fn wholeStoreSourceOverflow(proof: *DefiniteStoreProof) WholeStoreSource {
        if (proof.written_dependencies_complete) |complete| complete.* = false;
        return .{};
    }

    fn storeProjectionPath(self: *FileCache, tree: *const Ast, node: Ast.Node.Index) SummaryError!?[]const u8 {
        var fields: [32][]const u8 = undefined;
        var count: usize = 0;
        var current = node;
        while (true) {
            switch (tree.nodeTag(current)) {
                .grouped_expression => current = tree.nodeData(current).node_and_token[0],
                .field_access => {
                    const base, const field = tree.nodeData(current).node_and_token;
                    const raw = tree.tokenSlice(field);
                    // Quoted identifiers need decoded field names. Until the
                    // resolver supplies one, abstain rather than store a raw path.
                    if (std.mem.startsWith(u8, raw, "@\"")) return null;
                    if (count == fields.len) return null;
                    fields[count] = raw;
                    count += 1;
                    current = base;
                },
                else => break,
            }
        }
        if (count == 0) return "";
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        const arena = self.summary_arena.?.allocator();
        var path: []const u8 = "";
        while (count != 0) {
            count -= 1;
            path = if (path.len == 0)
                try arena.dupe(u8, fields[count])
            else
                try std.fmt.allocPrint(arena, "{s}.{s}", .{ path, fields[count] });
        }
        return path;
    }

    fn appendStoreProjectionPath(self: *FileCache, prefix: []const u8, suffix: []const u8) SummaryError![]const u8 {
        if (suffix.len == 0) return prefix;
        if (prefix.len == 0) return suffix;
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        return std.fmt.allocPrint(self.summary_arena.?.allocator(), "{s}.{s}", .{ prefix, suffix });
    }

    fn addIdentityProjectionRead(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        argument: Ast.Node.Index,
        relative_path: []const u8,
        source_node: Ast.Node.Index,
    ) SummaryError!?WholeStoreSource {
        _ = self;
        const reads = proof.written_reads orelse {
            if (proof.written_inputs != null) return wholeStoreSourceOverflow(proof);
            return WholeStoreSource{};
        };
        const source_type = try storeProjectionType(proof, source_node) orelse return WholeStoreSource{};
        const is_array = proof.frame.resolver.typeTag(source_type) == .array;
        const extent = if (is_array) try definiteStoreArrayCount(proof, source_node) else null;
        var slot: ?usize = null;
        for (reads, 0..) |*entry, index| {
            if (entry.*) |read| {
                if (read.identity_projection and !read.output_read and read.argument == argument and
                    read.relative_path != null and std.mem.eql(u8, read.relative_path.?, relative_path)) {
                    slot = index;
                    break;
                }
            } else if (slot == null) slot = index;
        }
        const index = slot orelse return wholeStoreSourceOverflow(proof);
        const existing = reads[index];
        if (existing == null) reads[index] = .{
            .argument = argument,
            .tree = originTree(proof),
            .node = argument,
            .identity_projection = true,
            .relative_path = relative_path,
            .is_array = is_array,
            .array_extent = extent,
            .value_type = source_type,
        } else if (!existing.?.identity_projection or existing.?.output_read) return WholeStoreSource{};
        return .{ .projections = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
    }

    fn wholeStoreFieldSourceProjection(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        base: WholeStoreSource,
        suffix: []const u8,
        source_node: Ast.Node.Index,
    ) SummaryError!?WholeStoreSource {
        if (suffix.len == 0) return base;
        var result: WholeStoreSource = .{ .opaque_alternative = base.opaque_alternative };
        var sources = base.sources;
        while (sources != 0) {
            const index: usize = @intCast(@ctz(sources));
            sources &= sources - 1;
            const argument = (proof.identity_inputs orelse return WholeStoreSource{})[index] orelse return wholeStoreSourceOverflow(proof);
            const projected = (try self.addIdentityProjectionRead(proof, argument, suffix, source_node)) orelse return WholeStoreSource{};
            result.projections |= projected.projections;
        }
        var projections = base.projections;
        while (projections != 0) {
            const index: usize = @intCast(@ctz(projections));
            projections &= projections - 1;
            const reads = proof.written_reads orelse return wholeStoreSourceOverflow(proof);
            const prior = reads[index] orelse return wholeStoreSourceOverflow(proof);
            if (prior.output_read) {
                const output_prefix = try self.appendStoreProjectionPath(prior.output_prefix orelse "", suffix);
                const projected = (try self.addOutputProjectionRead(proof, prior, output_prefix, source_node)) orelse return WholeStoreSource{};
                result.projections |= projected.projections;
            } else {
                const path = try self.appendStoreProjectionPath(prior.relative_path orelse "", suffix);
                const projected = (try self.addIdentityProjectionRead(proof, prior.argument, path, source_node)) orelse return WholeStoreSource{};
                result.projections |= projected.projections;
            }
        }
        return result;
    }

    fn addOutputProjectionRead(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        prior: WrittenRead,
        output_prefix: []const u8,
        source_node: Ast.Node.Index,
    ) SummaryError!?WholeStoreSource {
        _ = self;
        const reads = proof.written_reads orelse {
            if (proof.written_inputs != null) return wholeStoreSourceOverflow(proof);
            return WholeStoreSource{};
        };
        const value_type = try wholeStoreType(proof, source_node) orelse return WholeStoreSource{};
        const is_array = proof.frame.resolver.typeTag(value_type) == .array;
        const extent = if (is_array) try definiteStoreArrayCount(proof, source_node) else null;
        var slot: ?usize = null;
        for (reads, 0..) |entry, index| {
            if (entry) |read| {
                if (read.output_read and read.argument == prior.argument and read.output_base != null and
                    prior.output_base != null and ComputedStoreBase.equal(read.output_base.?, prior.output_base.?) and read.output_prefix != null and
                    std.mem.eql(u8, read.output_prefix.?, output_prefix)) {
                    slot = index;
                    break;
                }
            } else if (slot == null) slot = index;
        }
        const index = slot orelse return wholeStoreSourceOverflow(proof);
        if (reads[index] == null) reads[index] = .{
            .argument = prior.argument,
            .tree = prior.tree,
            .node = prior.node,
            .identity_projection = true,
            .relative_path = "",
            .value_type = value_type,
            .is_array = is_array,
            .array_extent = extent,
            .output_read = true,
            .output_prefix = output_prefix,
            .output_base = prior.output_base,
        };
        return .{ .projections = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
    }

    /// Exact aggregate field/array source recipes. This function creates only
    /// identity slots; dependency masks never authorize a copy.
    fn wholeStoreFieldSource(self: *FileCache, proof: *DefiniteStoreProof, node: Ast.Node.Index, depth: u32) SummaryError!?WholeStoreSource {
        try self.chargeNormalCleanupAt(proof.tree, node);
        if (depth == 64) return self.cleanupBudgetFailureAt(proof.tree, .normal_cleanup_depth, 64, node);
        if (proof.tree.nodeTag(node) == .grouped_expression)
            return self.wholeStoreFieldSource(proof, proof.tree.nodeData(node).node_and_token[0], depth + 1);
        if (proof.computed_templates != null and proof.tree.nodeTag(node) == .array_access) {
            const base, const index_node = proof.tree.nodeData(node).node_and_node;
            if (proof.tree.nodeTag(base) == .identifier) {
                const actual = (try proof.frame.typeOfNode(base)) orelse return null;
                const array = (try proof.frame.resolver.normalizedType(actual)) orelse return null;
                if (proof.frame.resolver.typeTag(array) == .array) {
                    const name = proof.tree.tokenSlice(proof.tree.nodeMainToken(base));
                    if (proof.findIndex(name)) |binding_index| {
                        const bound = proof.bindings[binding_index];
                        const index = try definiteStoreInteger(proof, index_node);
                        const extent = (try definiteStoreArrayCount(proof, base)) orelse return null;
                        if (index != null and index.? >= extent) return null;
                        const child_raw = (try proof.frame.typeOfNode(node)) orelse return null;
                        const child = (try proof.frame.resolver.normalizedType(child_raw)) orelse return null;
                        const path = if (index) |selected| blk: {
                            if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
                            break :blk try std.fmt.allocPrint(self.summary_arena.?.allocator(), "[{d}]", .{selected});
                        } else "";
                        const source = try self.computedPointeeReadSource(proof, base, path, child, .{
                            .source = bound.aggregate_source,
                            .computations = bound.computed_sources,
                            .original_alternative = bound.computed_original_alternative,
                            .opaque_alternative = bound.computed_opaque_alternative,
                        }, index == null);
                        proof.written_dependencies.reads |= source.projections;
                        return source;
                    }
                }
            }
        }
        // Modified whole pointees carry exact byte sources, never certificates.
        if (proof.tree.nodeTag(node) == .deref) {
            const base = proof.tree.nodeData(node).node;
            if (proof.tree.nodeTag(base) == .identifier) {
                const name = proof.tree.tokenSlice(proof.tree.nodeMainToken(base));
                if (proof.findStorePointeeEntry(name)) |entry| if (entry.computed) |state| {
                    const actual = (try proof.frame.typeOfNode(node)) orelse return null;
                    const value_type = (try proof.frame.resolver.normalizedType(actual)) orelse return null;
                    const source = try self.computedPointeeReadSource(
                        proof, node, "", value_type, state.base, false,
                    );
                    // Computed scalar consumers read these selected bytes as dependencies.
                    proof.written_dependencies.reads |= source.projections;
                    return source;
                };
            }
        }
        const source_type = (try wholeStoreType(proof, node)) orelse {
            if (proof.tree.nodeTag(node) != .field_access) return null;
            return self.wholeStoreSource(proof, node, depth + 1);
        };
        const path = (try self.storeProjectionPath(proof.tree, node)) orelse return WholeStoreSource{};
        const root = tokens.rootIdentifier(proof.tree, node) orelse return WholeStoreSource{};
        const root_name = proof.tree.tokenSlice(proof.tree.nodeMainToken(root));
        // Output pointee reads use only the authenticated output formal and
        // its applicable COW base; arbitrary pointer pointees remain opaque.
        if (proof.out_name) |out_name| {
            if (std.mem.eql(u8, proof.formalName(root_name), out_name) and
                (proof.tree.nodeTag(node) == .deref or proof.tree.nodeTag(node) == .field_access))
                return self.outputStoreReadSource(proof, node, path, source_type, depth + 1);
        }
        if (proof.tree.nodeTag(node) == .deref)
            return self.aggregateStoreReadSource(proof, node, source_type, depth + 1);
        if (!try self.passiveWholeStorePlace(proof, node, depth)) return WholeStoreSource{};
        if (path.len == 0) return self.wholeStoreSource(proof, node, depth + 1);
        if (proof.identity_leaf) {
            return self.addIdentityProjectionRead(proof, node, "", node);
        }
        if (proof.findIndex(root_name)) |binding| {
            if (proof.bindings[binding].aggregate_source) |base|
                return self.wholeStoreFieldSourceProjection(proof, base, path, node);
            const is_formal = binding < proof.parameter_count and proof.bindings[binding].formal_alias == null;
            if (!is_formal) return WholeStoreSource{};
        }
        const base = (try self.wholeStoreSource(proof, root, depth + 1)) orelse return null;
        return self.wholeStoreFieldSourceProjection(proof, base, path, node);
    }

    fn mergeComputedPointeeState(
        first: ?ComputedPointeeState,
        second: ?ComputedPointeeState,
    ) ?ComputedPointeeState {
        const witness = first orelse second orelse return null;
        const left = if (first) |state| state.base else ComputedStoreBase{ .source = witness.original };
        const right = if (second) |state| state.base else ComputedStoreBase{ .source = witness.original };
        return .{
            .original = witness.original,
            .base = .{
                .source = if (left.source != null or right.source != null)
                    WholeStoreSource.merge(
                        left.source orelse .{ .opaque_alternative = false },
                        right.source orelse .{ .opaque_alternative = false },
                    ) else null,
                .computations = left.computations | right.computations,
                .opaque_alternative = left.opaque_alternative or right.opaque_alternative,
            },
        };
    }

    /// Reserve an exact original-pointee read; lowering must authenticate its backing.
    fn originalPointeeReadSource(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        root: Ast.Node.Index,
        pointee: TypeResolver.ActualType,
    ) SummaryError!WholeStoreSource {
        const argument = (try self.originatingWrittenArgument(proof, root, 0)) orelse
            return WholeStoreSource{};
        const reads = proof.written_reads orelse return wholeStoreSourceOverflow(proof);
        var slot: ?usize = null;
        for (reads, 0..) |entry, index| {
            if (entry) |prior| {
                if (prior.pointee_read and prior.argument == argument and
                    prior.value_type != null and prior.value_type.?.eql(pointee))
                    return .{ .projections = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
            } else if (slot == null) slot = index;
        }
        const index = slot orelse return wholeStoreSourceOverflow(proof);
        const is_array = proof.frame.resolver.typeTag(pointee) == .array;
        reads[index] = .{
            .argument = argument,
            .tree = originTree(proof),
            .node = argument,
            .pointee_read = true,
            .relative_path = "",
            .value_type = pointee,
            .is_array = is_array,
            .array_extent = if (is_array) try definiteStoreArrayCount(proof, root) else null,
        };
        return .{ .projections = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
    }

    const ScalarOutputAlias = struct { same: bool, selected_token: Ast.TokenIndex };

    /// C scalar bookkeeping is clipped to two authenticated scalar variables
    /// in the same caller body. Array extents, casts, fields and unresolved
    /// pointer aliases do not acquire whole-pointee credit through this path.
    fn scalarOutputAlias(
        self: *FileCache,
        proof: *const DefiniteStoreProof,
        name: []const u8,
        child: TypeResolver.ActualType,
    ) SummaryError!?ScalarOutputAlias {
        const canonical = proof.canonical orelse return null;
        const output_name = proof.out_name orelse return null;
        const caller_cache = proof.caller_cache orelse self;
        const caller_tree = caller_cache.tree;
        const caller_frame = canonical.callee.caller_frame orelse
            (caller_cache.zls orelse return null).resolutionFrame();
        if (&caller_frame.handle.document.tree != caller_tree or
            caller_frame.handle.module != caller_cache.module_id) return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(proof.tree, &proto_buffer, canonical.callee.declaration) orelse return null;
        var parameters = proto.iterate(proof.tree);
        var ordinal: u32 = 0;
        var selected_token: ?Ast.TokenIndex = null;
        var output: ?Ast.Node.Index = null;
        var other: ?Ast.Node.Index = null;
        while (parameters.next()) |parameter| : (ordinal += 1) {
            const token = parameter.name_token orelse continue;
            const parameter_name = proof.tree.tokenSlice(token);
            if (!std.mem.eql(u8, parameter_name, output_name) and !std.mem.eql(u8, parameter_name, name)) continue;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try canonical.callArgumentFor(caller_cache, &argument_buffer, ordinal)) orelse return null;
            if (std.mem.eql(u8, parameter_name, output_name)) {
                selected_token = token;
                output = argument;
            } else other = argument;
        }
        const arguments = [2]Ast.Node.Index{ output orelse return null, other orelse return null };
        var declarations: [2]Ast.TokenIndex = undefined;
        var body_node: ?Ast.Node.Index = null;
        for (arguments, 0..) |argument, index| {
            if (caller_tree.nodeTag(argument) != .address_of) return null;
            const operand = caller_tree.nodeData(argument).node;
            if (caller_tree.nodeTag(operand) != .identifier) return null;
            const ty = (try caller_frame.typeOfNode(operand)) orelse return null;
            const normalized = (try caller_frame.resolver.normalizedType(ty)) orelse return null;
            if (!normalized.eql(child)) return null;
            const token = caller_tree.nodeMainToken(operand);
            const function = caller_cache.enclosingFunctionAt(caller_tree, token) orelse return null;
            var caller_proto_buffer: [1]Ast.Node.Index = undefined;
            const caller_proto = tokens.fnProto(caller_tree, &caller_proto_buffer, function) orelse return null;
            const body = tokens.bodyOf(caller_tree, function) orelse return null;
            if (body_node != null and body_node.? != body) return null;
            body_node = body;
            const bindings = try caller_cache.localBindings(caller_proto, body);
            const binding = bindings.findAt(caller_tree.tokenSlice(token), token) orelse return null;
            if (binding.is_const or binding.origin == .param or binding.origin == .loop_capture or
                binding.name_token == 0 or caller_tree.tokenTag(binding.name_token - 1) != .keyword_var) return null;
            declarations[index] = binding.name_token;
        }
        return .{ .same = declarations[0] == declarations[1], .selected_token = selected_token orelse return null };
    }

    /// Compose non-output formal stores into the same bounded immutable COW pool.
    fn recordOtherPointeeStore(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        lhs: Ast.Node.Index,
        rhs: Ast.Node.Index,
        evaluated: DefiniteStoreResult,
    ) SummaryError!bool {
        const tree = proof.tree;
        const root = tokens.rootIdentifier(tree, lhs) orelse return false;
        const name = proof.formalName(tree.tokenSlice(tree.nodeMainToken(root)));
        const resolver = proof.frame.resolver;
        const actual = (try proof.frame.typeOfNode(root)) orelse return false;
        const pointer = (try resolver.normalizedType(actual)) orelse return false;
        const size = resolver.pointerSize(pointer) orelse return false;
        if (size != .one and (size != .c or proof.written_inputs == null)) return false;
        const child = (try resolver.normalizedType(resolver.childType(pointer) orelse return false)) orelse return false;
        const scalar_alias: ?ScalarOutputAlias = if (size == .c) relation: {
            switch (resolver.typeTag(child) orelse return false) {
                .int, .float, .bool, .@"enum" => {},
                else => return false,
            }
            if (tree.nodeTag(lhs) != .deref) return false;
            break :relation (try self.scalarOutputAlias(proof, name, child)) orelse return false;
        } else null;
        switch (resolver.typeTag(child) orelse return false) {
            .@"struct", .@"union", .array, .vector => {},
            .int, .float, .bool, .@"enum" => {
                if (tree.nodeTag(lhs) != .deref) return false;
            },
            else => {
                // Every resolved runtime whole-pointee value uses the same byte
                // recipe. Selected writes still require an aggregate layout.
                if (tree.nodeTag(lhs) != .deref) return false;
            },
        }
        const previous = proof.findStorePointeeEntry(name);
        const state: ComputedPointeeState = if (previous) |entry|
            entry.computed orelse .{ .original = .{}, .base = .{ .opaque_alternative = true } }
        else blk: {
            const original = try self.originalPointeeReadSource(proof, root, child);
            break :blk .{ .original = original, .base = .{ .source = original } };
        };
        var fields: [128][]const u8 = undefined;
        var defaults: [128]?Ast.Node.Index = @splat(null);
        var mapped: StoreCoverage = .{ .pointee = child };
        if (!try self.storeCoverageFields(child, &fields, &defaults, &mapped, proof.call_tree, proof.call_node)) return false;
        var path: []const u8 = "";
        var array_index: ?u64 = null;
        switch (tree.nodeTag(lhs)) {
            .deref => {},
            .field_access => {
                const index = (try storeFieldIndex(proof, name, fields[0..mapped.field_count], lhs)) orelse return false;
                path = fields[index];
            },
            .array_access => {
                const base, const index = tree.nodeData(lhs).node_and_node;
                const extent = (try definiteStoreArrayCount(proof, base)) orelse return false;
                array_index = (try definiteStoreInteger(proof, index)) orelse return false;
                if (array_index.? >= extent) return false;
                path = (try self.storeProjectionPath(tree, base)) orelse return false;
            },
            else => return false,
        }
        var write = try self.computedStoreWriteForValue(
            proof, path, rhs, evaluated, proof.written_dependencies, false, null, array_index,
        );
        const child_tag = resolver.typeTag(child);
        var boxed_optional = false;
        if (tree.nodeTag(lhs) == .deref and
            (child_tag == .optional or child_tag == .error_union))
        {
            if (try proof.frame.typeOfNode(rhs)) |source_actual| {
                if (try resolver.normalizedType(source_actual)) |source_type| {
                    const source_tag = resolver.typeTag(source_type);
                    // Intrinsic undefined initializes the whole wrapper, not a
                    // success payload; only actual boxing repairs the tag.
                    boxed_optional = child_tag == .optional and source_tag != null and
                        source_tag != .optional and source_tag != .undefined;
                    if (child_tag == .error_union and source_tag != .error_union and
                        source_tag != null and source_tag != .error_set and write.literal_undefined)
                    {
                        // A success payload hole is not an entirely undefined wrapper.
                        write.literal_undefined = false;
                        write.literal_may_undefined = true;
                    }
                }
            }
        }
        var composed: ComputedStoreBase = if (array_index != null)
            .{ .computations = appendComputedStoreWrite(proof, state.base, write) orelse return false }
        else appendComputedFieldStoreWrite(
            proof, state.base, write, evaluated.computed, fields[0..mapped.field_count],
        ) orelse return false;
        if (boxed_optional) {
            // Boxing keeps the tag defined even when its payload bytes are undefined.
            // This repairs the negative ledger only, never a value certificate.
            composed = .{ .computations = appendComputedStoreWrite(proof, composed, .{
                .path = "$optional-tag",
            }) orelse return false };
        }
        // This recipe transports byte diagnostics only. It grants no pointee certificate.
        if (!proof.setStorePointee(tree.nodeMainToken(root), .unknown)) return false;
        for (proof.pointees[0..proof.pointee_count]) |*entry| {
            if (std.mem.eql(u8, tree.tokenSlice(entry.token), name)) {
                entry.computed = .{ .original = state.original, .base = composed };
                if (scalar_alias) |relation| if (relation.same) {
                    const coverage = proof.out_coverage orelse return false;
                    if (!coverage.pointee.eql(child)) return false;
                    coverage.whole_dependencies = proof.written_dependencies;
                    coverage.whole_source = composed.source;
                    coverage.computed_sources = composed.computations;
                    coverage.computed_original_alternative = composed.original_alternative;
                    coverage.computed_opaque_alternative = composed.opaque_alternative;
                    @memset(coverage.covered[0..coverage.field_count], true);
                    coverage.complete = true;
                    const current = entry.computed;
                    if (!proof.setStorePointee(relation.selected_token, .unknown)) return false;
                    for (proof.pointees[0..proof.pointee_count]) |*selected| {
                        if (std.mem.eql(u8, tree.tokenSlice(selected.token), proof.out_name.?))
                            selected.computed = current;
                    }
                };
                return true;
            }
        }
        unreachable;
    }

    fn computedPointeeReadSource(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        prefix: []const u8,
        source_type: TypeResolver.ActualType,
        base: ComputedStoreBase,
        output_index_read: bool,
    ) SummaryError!WholeStoreSource {
        _ = self;
        const reads = proof.written_reads orelse return wholeStoreSourceOverflow(proof);
        var slot: ?usize = null;
        for (reads, 0..) |entry, index| {
            if (entry) |prior| {
                if (prior.output_read and prior.output_index_read == output_index_read and
                    prior.tree == proof.tree and prior.node == node and
                    prior.output_base != null and ComputedStoreBase.equal(prior.output_base.?, base) and
                    prior.output_prefix != null and std.mem.eql(u8, prior.output_prefix.?, prefix))
                    return .{ .projections = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
            } else if (slot == null) slot = index;
        }
        const index = slot orelse return wholeStoreSourceOverflow(proof);
        const is_array = proof.frame.resolver.typeTag(source_type) == .array;
        reads[index] = .{
            .argument = node,
            .tree = proof.tree,
            .node = node,
            .identity_projection = true,
            .relative_path = "",
            .value_type = source_type,
            .is_array = is_array,
            .array_extent = if (is_array) try definiteStoreArrayCount(proof, node) else null,
            .output_read = true,
            .output_index_read = output_index_read,
            .output_prefix = prefix,
            .output_base = base,
        };
        return .{ .projections = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
    }

    fn aggregateStoreReadSource(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        source_type: TypeResolver.ActualType,
        depth: u32,
    ) SummaryError!?WholeStoreSource {
        try self.chargeNormalCleanupAt(proof.tree, node);
        if (depth >= 64) return self.cleanupBudgetFailureAt(proof.tree, .normal_cleanup_depth, 64, node);
        const base = proof.tree.nodeData(node).node;
        if (proof.tree.nodeTag(base) != .identifier) return WholeStoreSource{};
        const name = proof.formalName(proof.tree.tokenSlice(proof.tree.nodeMainToken(base)));
        // Modified non-output pointees use their exact COW state, never the
        // original caller identity. Untracked whole stores still abstain.
        if (proof.findStorePointeeEntry(name)) |entry| {
            if (entry.computed) |state|
                return try self.computedPointeeReadSource(proof, node, "", source_type, state.base, false);
            return WholeStoreSource{};
        }
        const raw = (try proof.frame.typeOfNode(base)) orelse return WholeStoreSource{};
        const pointer = (try proof.frame.resolver.normalizedType(raw)) orelse return WholeStoreSource{};
        if (proof.frame.resolver.pointerSize(pointer) != .one) return WholeStoreSource{};
        const raw_child = proof.frame.resolver.childType(pointer) orelse return WholeStoreSource{};
        const child = (try proof.frame.resolver.normalizedType(raw_child)) orelse return WholeStoreSource{};
        if (!child.eql(source_type)) return WholeStoreSource{};
        const origin = (try self.originatingWrittenArgument(proof, base, depth + 1)) orelse return WholeStoreSource{};
        const saved_projection = proof.read_projection;
        defer proof.read_projection = saved_projection;
        proof.read_projection = node;
        if (!try proof.recordWrittenRead(origin)) return wholeStoreSourceOverflow(proof);
        const reads = proof.written_reads orelse return WholeStoreSource{};
        // Match the exact authenticated AST read just registered. A singleton
        // dependency is not an identity premise and is never consulted here.
        for (reads, 0..) |entry, index| if (entry) |selected| {
            if (selected.argument == origin and selected.tree == proof.tree and selected.node == node and
                selected.value_type != null and selected.value_type.?.eql(source_type))
                return .{ .projections = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
        };
        return WholeStoreSource{};
    }

    fn outputArgumentPrefix(
        self: *FileCache,
        caller: *const DefiniteStoreProof,
        argument: Ast.Node.Index,
    ) SummaryError!?[]const u8 {
        var node = argument;
        while (self.tree.nodeTag(node) == .grouped_expression)
            node = self.tree.nodeData(node).node_and_token[0];
        if (self.tree.nodeTag(node) == .address_of)
            return self.storeProjectionPath(self.tree, self.tree.nodeData(node).node);
        if (self.tree.nodeTag(node) != .identifier) return null;
        const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
        if (caller.out_name) |out_name| {
            if (std.mem.eql(u8, caller.formalName(name), out_name)) return "";
        }
        if (caller.findIndex(name)) |binding| {
            if (caller.bindings[binding].formal_alias) |alias| {
                if (caller.out_name) |out_name| {
                    if (std.mem.eql(u8, self.tree.tokenSlice(alias), out_name)) return "";
                }
            }
        }
        return null;
    }

    fn outputStoreReadSource(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        path: []const u8,
        source_type: TypeResolver.ActualType,
        depth: u32,
    ) SummaryError!?WholeStoreSource {
        try self.chargeNormalCleanupAt(proof.tree, node);
        if (depth == 64) return self.cleanupBudgetFailureAt(proof.tree, .normal_cleanup_depth, 64, node);
        const argument = proof.identity_output orelse return WholeStoreSource{};
        const coverage = proof.out_coverage orelse return WholeStoreSource{};
        const builders = proof.computed_templates orelse return WholeStoreSource{};
        var base = computedCoverageBase(coverage);
        var prefix = path;
        var current = proof;
        var memo: [8]?u8 = .{null} ** 8;
        while (current.caller) |caller_link| {
            if (caller_link.*) |*parent| {
                const parent_coverage = parent.out_coverage orelse break;
                const root_prefix = current.identity_output_prefix orelse return WholeStoreSource{};
                memo = .{null} ** 8;
                base = rebaseComputedStoreBase(current, base, computedCoverageBase(parent_coverage), root_prefix, parent.out_fields, builders.count, &memo) orelse return WholeStoreSource{};
                prefix = (try self.mapOutputReadPrefix(parent.out_fields, root_prefix, prefix)) orelse return WholeStoreSource{};
                current = parent;
            } else break;
        }
        const reads = proof.written_reads orelse return wholeStoreSourceOverflow(proof);
        var slot: ?usize = null;
        for (reads, 0..) |entry, index| {
            if (entry) |read| {
                if (read.output_read and read.argument == argument and read.output_prefix != null and
                    std.mem.eql(u8, read.output_prefix.?, prefix) and read.value_type != null and
                    read.value_type.?.eql(source_type) and read.output_base != null and
                    ComputedStoreBase.equal(read.output_base.?, base)) {
                    slot = index;
                    break;
                }
            } else if (slot == null) slot = index;
        }
        const index = slot orelse return wholeStoreSourceOverflow(proof);
        if (reads[index] == null) reads[index] = .{
            .argument = argument,
            .tree = originTree(proof),
            .node = argument,
            .identity_projection = true,
            .relative_path = "",
            .value_type = source_type,
            .is_array = proof.frame.resolver.typeTag(source_type) == .array,
            .array_extent = if (proof.frame.resolver.typeTag(source_type) == .array) try definiteStoreArrayCount(proof, node) else null,
            .output_read = true,
            .output_prefix = prefix,
            .output_base = base,
        };
        return .{ .projections = @as(u8, 1) << @intCast(index), .opaque_alternative = false };
    }

    fn mapOutputReadPrefix(self: *FileCache, fields: []const []const u8, prefix: []const u8, suffix: []const u8) SummaryError!?[]const u8 {
        const path = try self.appendStoreProjectionPath(prefix, suffix);
        if (path.len == 0) return path;
        for (fields) |candidate| {
            if (std.mem.eql(u8, candidate, path) or
                (candidate.len > path.len and candidate[path.len] == '.' and std.mem.startsWith(u8, candidate, path))) return path;
        }
        return null;
    }


    /// Only a direct copy of a pointer formal retains its exact identity.
    /// Rebinding and escaping that local make the body proof abstain.
    fn definiteStoreFormalAlias(self: *FileCache, proof: *DefiniteStoreProof, node: Ast.Node.Index) SummaryError!?Ast.TokenIndex {
        if (proof.tree.nodeTag(node) != .identifier) return null;
        const name = proof.tree.tokenSlice(proof.tree.nodeMainToken(node));
        if (proof.findIndex(name)) |index| {
            if (proof.bindings[index].formal_alias) |alias| return alias;
            if (index >= proof.parameter_count) return null;
        }
        const canonical = proof.canonical orelse return null;
        const resolver = proof.frame.resolver;
        const actual = (try proof.frame.typeOfNode(node)) orelse return null;
        const normalized = (try resolver.normalizedType(actual)) orelse return null;
        const size = resolver.pointerSize(normalized) orelse return null;
        if (size != .one and size != .c) return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(proof.tree, &buffer, canonical.callee.declaration) orelse return null;
        var parameters = proto.iterate(proof.tree);
        while (parameters.next()) |parameter| {
            try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
            const token = parameter.name_token orelse continue;
            if (std.mem.eql(u8, proof.tree.tokenSlice(token), name)) return token;
        }
        return null;
    }

    /// Defined stores to another formal cannot poison this output through an
    /// alias. Unknown values and pointers without exact formal identity abstain.
    fn definiteStoreOtherFormal(self: *FileCache, proof: *DefiniteStoreProof, root: Ast.Node.Index) SummaryError!?bool {
        const canonical = proof.canonical orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(proof.tree, &buffer, canonical.callee.declaration) orelse return null;
        const root_name = proof.tree.tokenSlice(proof.tree.nodeMainToken(root));
        if (proof.find(root_name)) |binding| {
            if (binding.formal_alias == null) return null;
        }
        const name = proof.formalName(root_name);
        var parameters = proto.iterate(proof.tree);
        while (parameters.next()) |parameter| {
            try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
            const token = parameter.name_token orelse continue;
            if (std.mem.eql(u8, proof.tree.tokenSlice(token), name)) return true;
        }
        return null;
    }

    /// A callee statement `[try] nested(..)` that passes the proof's pointer
    /// on, whole or as one field. The nested body is proved against the same
    /// rules; its coverage joins the wrapper's. A call that never receives the
    /// pointer, a revisit, a depth overrun or any unproven delegate abstains
    /// (false). `try` makes the error return leave the statement, so only the
    /// success path is credited.
    fn definiteNestedStore(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        canonical: ActualCallSummary,
        call_node: Ast.Node.Index,
        name: []const u8,
        fields: []const []const u8,
        nested_call: Ast.Node.Index,
        visiting: []const StoreVisit,
        coverage: *StoreCoverage,
        selected_success: bool,
    ) SummaryError!bool {
        if (visiting.len > max_store_call_depth) return false;
        const declaring = (try canonical.declaringCache(self)) orelse return false;
        try declaring.enterNormalCleanup(nested_call);
        defer declaring.leaveNormalCleanup();
        try declaring.chargeNormalCleanup(nested_call);
        const tree = proof.tree;
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &call_buffer, nested_call) orelse return false;
        const nested = (try declaring.actualCallSummaryAt(call.queryToken(tree, nested_call), proof.frame)) orelse return false;
        if (nested.callee.tree.nodeTag(nested.callee.declaration) != .fn_decl) return false;
        if (!selected_success) {
            const result = (try proof.frame.typeOfNode(nested_call)) orelse return false;
            const normalized = (try proof.frame.resolver.normalizedType(result)) orelse return false;
            if (proof.frame.resolver.typeTag(normalized) == .error_union) return false;
        }
        for (visiting) |seen| {
            if (seen.tree == nested.callee.tree and seen.declaration == nested.callee.declaration) return false;
        }
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(nested.callee.tree, &proto_buffer, nested.callee.declaration) orelse return false;
        // The wrapper's own lexical state at this call evaluates the actuals.
        var state: ?DefiniteStoreProof = proof.*;
        var matched: ?struct { index: u32, target: StoreTarget } = null;
        var parameters = proto.iterate(nested.callee.tree);
        var parameter_index: u32 = 0;
        while (parameters.next() != null) : (parameter_index += 1) {
            try self.chargeNormalCleanup(call_node);
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try nested.callArgumentFor(declaring, &argument_buffer, parameter_index)) orelse return false;
            // An ignored actual can still mutate a dependency while it runs.
            if (try self.definiteStoreValue(&state.?, argument, 1) == .unknown) return false;
            if (try storeTarget(proof, name, fields, argument)) |target| {
                if (matched != null) return false;
                matched = .{ .index = parameter_index, .target = target };
            }
        }
        const delegate = matched orelse {
            if (try self.definiteStoreCallValue(proof, nested_call, 0, selected_success) != .unknown) return true;
            var pointer_formal = false;
            for (nested.callee.reference.actual_type.data.function.parameters) |formal| {
                const ty = (try proof.frame.resolver.normalizedType(formal.type)) orelse return false;
                pointer_formal = pointer_formal or proof.frame.resolver.pointerSize(ty) != null;
            }
            if (!pointer_formal) return false;
            return declaring.definiteStoreCallEffects(proof, nested, &state, 0);
        };
        var chain: [max_store_call_depth + 1]StoreVisit = undefined;
        @memcpy(chain[0..visiting.len], visiting);
        chain[visiting.len] = .{ .tree = nested.callee.tree, .declaration = nested.callee.declaration };
        const stored = (try declaring.definiteParameterStore(nested, nested_call, delegate.index, &state, chain[0 ..visiting.len + 1])) orelse return false;
        coverage.effects_known = coverage.effects_known and stored.effects_known;
        switch (delegate.target) {
            .unknown_field => return false,
            .whole => {
                if (!stored.pointee.eql(coverage.pointee) or stored.field_count != coverage.field_count) return false;
                for (coverage.covered[0..coverage.field_count], stored.covered[0..coverage.field_count], coverage.written_dependencies[0..coverage.field_count], stored.written_dependencies[0..stored.field_count]) |*mine, theirs, *dependencies, incoming| {
                    mine.* = mine.* or theirs or stored.complete;
                    if (theirs or stored.complete) dependencies.* = incoming;
                }
                if (stored.complete) coverage.whole_dependencies = stored.whole_dependencies;
                if (proof.computed_templates != null) {
                    coverage.whole_source = stored.whole_source;
                    coverage.computed_sources = stored.computed_sources;
                    coverage.computed_original_alternative = stored.computed_original_alternative;
                    coverage.computed_opaque_alternative = stored.computed_opaque_alternative;
                    coverage.computed_overflow = coverage.computed_overflow or stored.computed_overflow;
                }
                coverage.complete = coverage.complete or stored.complete;
                if (stored.complete) coverage.whole_source = stored.whole_source
                else if (coverage.whole_source != null) coverage.whole_source = .{};
            },
            .field => |field_index| {
                if (coverage.whole_source != null) coverage.whole_source = .{};
                if (field_index >= coverage.field_count) return false;
                if (stored.complete) {
                    coverStoreField(coverage, field_index);
                    recordWrittenStoreField(coverage, field_index, stored.whole_dependencies);
                }
                const prefix = coverage.field_names[field_index];
                if (proof.computed_templates) |builders| {
                    const parent_base = computedCoverageBase(coverage);
                    var memo: [8]?u8 = .{null} ** 8;
                    const rebased = rebaseComputedStoreBase(proof, computedCoverageBase(&stored), parent_base, prefix, coverage.field_names[0..coverage.field_count], builders.count, &memo);
                    if (rebased) |base| {
                        coverage.whole_source = base.source;
                        coverage.computed_sources = base.computations;
                        coverage.computed_original_alternative = base.original_alternative;
                        coverage.computed_opaque_alternative = base.opaque_alternative;
                    } else {
                        builders.overflow = true;
                        coverage.computed_overflow = true;
                    }
                }
                for (stored.field_names[0..stored.field_count], stored.covered[0..stored.field_count], stored.written_dependencies[0..stored.field_count]) |suffix, written, dependencies| {
                    if (!written) continue;
                    for (coverage.field_names[0..coverage.field_count], coverage.covered[0..coverage.field_count], coverage.written_dependencies[0..coverage.field_count]) |candidate, *covered, *recipe| {
                        if (candidate.len == prefix.len + 1 + suffix.len and
                            candidate[prefix.len] == '.' and std.mem.startsWith(u8, candidate, prefix) and
                            std.mem.eql(u8, candidate[prefix.len + 1 ..], suffix)) {
                            covered.* = true;
                            recipe.* = dependencies;
                        }
                    }
                }
            },
        }
        refreshStoreCoverage(coverage);
        // An address handed to the delegate may change the wrapper's locals.
        try self.definiteStoreEscapes(proof, nested_call, 0);
        return true;
    }

    /// Which part of the pointer `name` (or of its pointee) `argument` hands
    /// on: itself or `&name.*`, `&name.field`, or the by-value `name.field` an
    /// instance call takes the address of. Anything else is not that storage.
    fn storeTarget(
        proof: *const DefiniteStoreProof,
        name: []const u8,
        fields: []const []const u8,
        argument: Ast.Node.Index,
    ) SummaryError!?StoreTarget {
        const tree = proof.tree;
        var node = argument;
        const addressed = tree.nodeTag(node) == .address_of;
        if (addressed) node = tree.nodeData(node).node;
        switch (tree.nodeTag(node)) {
            .identifier => {
                if (addressed or !std.mem.eql(u8, proof.formalName(tree.tokenSlice(tree.nodeMainToken(node))), name)) return null;
                return .whole;
            },
            .deref => {
                const base = tree.nodeData(node).node;
                if (!addressed or tree.nodeTag(base) != .identifier or
                    !std.mem.eql(u8, proof.formalName(tree.tokenSlice(tree.nodeMainToken(base))), name)) return null;
                return .whole;
            },
            .field_access => {
                const root = tokens.rootIdentifier(tree, node) orelse return null;
                if (!std.mem.eql(u8, proof.formalName(tree.tokenSlice(tree.nodeMainToken(root))), name)) return null;
                if (!addressed) {
                    // A pointer-typed field hands on its value, not its slot.
                    const resolver = proof.frame.resolver;
                    const field_type = (try proof.frame.typeOfNode(node)) orelse return .unknown_field;
                    const normalized = (try resolver.normalizedType(field_type)) orelse return .unknown_field;
                    if ((resolver.typeTag(normalized) orelse return .unknown_field) == .pointer) return null;
                }
                if (try storeFieldIndex(proof, name, fields, node)) |field_index| return .{ .field = field_index };
                return .unknown_field;
            },
            else => return null,
        }
    }

    const DefiniteStoreValue = enum { defined, undefined_value, unknown };
    const ComputedStoreState = struct {
        source: ?WholeStoreSource = null,
        computations: u8 = 0,
        original_alternative: bool = false,
        opaque_alternative: bool = false,
        value_nonidentity: bool = false,
        literal_undefined: bool = false,
        literal_may_undefined: bool = false,
        fallback_token: ?Ast.TokenIndex = null,


        fn merge(self: *ComputedStoreState, other: ComputedStoreState) void {
            if (other.source) |source| {
                self.source = if (self.source) |current|
                    WholeStoreSource.merge(current, source)
                else
                    source;
            }
            self.computations |= other.computations;
            self.original_alternative = self.original_alternative or other.original_alternative;
            self.opaque_alternative = self.opaque_alternative or other.opaque_alternative;
            self.value_nonidentity = self.value_nonidentity or other.value_nonidentity;
            self.literal_undefined = self.literal_undefined and other.literal_undefined;
            self.literal_may_undefined = self.literal_may_undefined or other.literal_may_undefined;
        }

    };

    const DefiniteStoreResult = struct {
        value: DefiniteStoreValue,
        raw_value: DefiniteStoreValue,
        literal_undefined: bool = false,
        literal_may_undefined: bool = false,
        computed: ComputedStoreState = .{},
    };

    const ComputedPointeeState = struct {
        original: WholeStoreSource,
        base: ComputedStoreBase,

        fn equal(first: ?ComputedPointeeState, second: ?ComputedPointeeState) bool {
            if (first == null or second == null) return first == null and second == null;
            return WholeStoreSource.equal(first.?.original, second.?.original) and
                ComputedStoreBase.equal(first.?.base, second.?.base);
        }
    };

    /// Ephemeral lexical facts for this proof, not another call summary.
    /// A binding holds the value at this statement, never its initializer's
    /// stale dependencies. Unsupported caller statements clear local facts.
    const DefiniteStoreProof = struct {
        tree: *const Ast,
        frame: TypeResolver.ResolutionFrame,
        canonical: ?ActualCallSummary = null,
        caller: ?*?DefiniteStoreProof = null,
        /// Owns the tree of `canonical.callee.call_node` and of `caller`.
        /// Formal-to-actual mapping must use it, never the callee's cache.
        caller_cache: ?*FileCache = null,
        call_node: Ast.Node.Index,
        /// `call_node` remains the originating caller site through nested proofs.
        call_tree: *const Ast,
        out_name: ?[]const u8 = null,
        out_fields: []const []const u8 = &.{},
        out_coverage: ?*StoreCoverage = null,
        written_inputs: ?*[8]?Ast.Node.Index = null,
        written_reads: ?*[8]?WrittenRead = null,
        /// Only this formal-to-actual edge owns originating-caller AST slots.
        /// Inherited table pointers never establish a second slot namespace.
        written_input_boundary: bool = false,
        may_written_stores: ?*WrittenMayStores = null,
        written_dependencies: WrittenDependencies = .{},
        written_dependencies_complete: ?*bool = null,
        identity_inputs: ?*[8]?Ast.Node.Index = null,
        identity_tree: ?*const Ast = null,
        identity_input_boundary: bool = false,
        /// Original destination actual; never used as the call_node's AST owner.
        identity_output: ?Ast.Node.Index = null,
        identity_output_prefix: ?[]const u8 = null,
        identity_leaf: bool = false,
        read_projection: ?Ast.Node.Index = null,
        collect_written_inputs: bool = true,
        computed_templates: ?*ComputedStoreBuilders = null,
        computed_result: ComputedStoreState = .{},

        bindings: [128]struct {
            token: Ast.TokenIndex,
            value: DefiniteStoreValue,
            written_dependencies: WrittenDependencies = .{},
            computed_sources: u8 = 0,
            computed_original_alternative: bool = false,
            computed_opaque_alternative: bool = false,
            /// Complete source-proven aggregates, never arbitrary literals.
            complete_value: bool = false,
            /// Immutable integer-overflow builtins produce two scalar slots.
            overflow_tuple: bool = false,
            formal_alias: ?Ast.TokenIndex = null,
            aggregate_source: ?WholeStoreSource = null,
            value_nonidentity: bool = false,
            literal_undefined: bool = false,
            literal_may_undefined: bool = false,
        } = undefined,
        binding_count: usize = 0,

        parameter_count: usize = 0,
        pointees: [128]struct {
            token: Ast.TokenIndex,
            value: DefiniteStoreValue,
            computed: ?ComputedPointeeState = null,
        } = undefined,
        pointee_count: usize = 0,
        field_facts: [128]struct {
            token: Ast.TokenIndex,
            path: []const u8,
            value: DefiniteStoreValue,
            written_dependencies: WrittenDependencies = .{},
            fallback_literal_may: bool = false,
            fallback_recipe: bool = false,
        } = undefined,
        field_fact_count: usize = 0,

        fn recordWrittenRead(proof: *DefiniteStoreProof, argument: Ast.Node.Index) SummaryError!bool {
            if (!proof.collect_written_inputs) return true;
            const reads = proof.written_reads orelse return false;
            const node = proof.read_projection orelse return false;
            for (reads, 0..) |*entry, slot| {
                if (entry.*) |read| {
                    if (read.argument != argument or read.tree != proof.tree or read.node != node) continue;
                } else {
                    const actual = (try proof.frame.typeOfNode(node)) orelse return false;
                    const ty = (try proof.frame.resolver.normalizedType(actual)) orelse return false;
                    const is_array = proof.frame.resolver.typeTag(ty) == .array;
                    entry.* = .{
                        .argument = argument,
                        .tree = proof.tree,
                        .node = node,
                        .value_type = ty,
                        .is_array = is_array,
                        .array_extent = if (is_array) try definiteStoreArrayCount(proof, node) else null,
                    };
                }
                proof.written_dependencies.reads |= @as(u8, 1) << @intCast(slot);
                return true;
            }
            if (proof.written_dependencies_complete) |complete| complete.* = false;
            return false;
        }

        fn findStoreFieldFact(proof: *const DefiniteStoreProof, name: []const u8, path: []const u8) ?*const @TypeOf(proof.field_facts[0]) {
            const binding = proof.findIndex(name) orelse return null;
            const token = proof.bindings[binding].token;
            for (proof.field_facts[0..proof.field_fact_count]) |*fact| {
                if (fact.token == token and std.mem.eql(u8, fact.path, path)) return fact;
            }
            return null;
        }

        fn findStoreField(proof: *const DefiniteStoreProof, name: []const u8, path: []const u8) ?DefiniteStoreValue {
            const fact = proof.findStoreFieldFact(name, path) orelse return null;
            return fact.value;
        }

        fn setStoreField(proof: *DefiniteStoreProof, token: Ast.TokenIndex, path: []const u8, value: DefiniteStoreValue, dependencies: WrittenDependencies) bool {
            const binding = proof.findIndex(proof.tree.tokenSlice(token)) orelse return false;
            proof.bindings[binding].aggregate_source = null;
            const root = proof.bindings[binding].token;
            proof.bindings[binding].literal_undefined = false;
            proof.bindings[binding].literal_may_undefined = false;
            proof.bindings[binding].value_nonidentity = true;
            for (proof.field_facts[0..proof.field_fact_count]) |*fact| {
                if (fact.token == root and std.mem.eql(u8, fact.path, path)) {
                    fact.value = value;
                    fact.written_dependencies = dependencies;
                    fact.fallback_recipe = false;
                    fact.fallback_literal_may = false;
                    return true;
                }
            }
            if (proof.field_fact_count == proof.field_facts.len) return false;
            proof.field_facts[proof.field_fact_count] = .{ .token = root, .path = path, .value = value, .written_dependencies = dependencies };
            proof.field_fact_count += 1;
            return true;
        }

        fn weakenLiteralStoreBinding(proof: *DefiniteStoreProof, index: usize) void {
            const binding = &proof.bindings[index];
            if (index < proof.parameter_count or binding.token == 0 or
                proof.tree.tokenTag(binding.token - 1) != .keyword_var) return;
            binding.literal_may_undefined = binding.literal_may_undefined or binding.literal_undefined;
            binding.literal_undefined = false;
        }

        fn invalidateStoreFields(proof: *DefiniteStoreProof, name: []const u8) void {
            const binding = proof.findIndex(name) orelse return;
            proof.bindings[binding].aggregate_source = null;
            proof.weakenLiteralStoreBinding(binding);
            const token = proof.bindings[binding].token;
            for (proof.field_facts[0..proof.field_fact_count]) |*fact| {
                if (fact.token == token) {
                    fact.value = .unknown;
                    fact.written_dependencies = .{};
                    fact.fallback_recipe = false;
                    fact.fallback_literal_may = false;
                }
            }
        }

        fn invalidateAllStoreFields(proof: *DefiniteStoreProof) void {
            for (proof.bindings[0..proof.binding_count], 0..) |*binding, index| {
                binding.aggregate_source = null;
                proof.weakenLiteralStoreBinding(index);
            }
            for (proof.field_facts[0..proof.field_fact_count]) |*fact| {
                fact.value = .unknown;
                fact.written_dependencies = .{};
                fact.fallback_recipe = false;
                fact.fallback_literal_may = false;
            }
        }

        fn formalName(proof: *const DefiniteStoreProof, name: []const u8) []const u8 {
            if (proof.findIndex(name)) |index| {
                if (proof.bindings[index].formal_alias) |token| return proof.tree.tokenSlice(token);
            }
            return name;
        }

        fn findStorePointeeEntry(
            proof: *const DefiniteStoreProof,
            name: []const u8,
        ) ?*const @TypeOf(proof.pointees[0]) {
            const formal = proof.formalName(name);
            for (proof.pointees[0..proof.pointee_count]) |*entry| {
                if (std.mem.eql(u8, proof.tree.tokenSlice(entry.token), formal)) return entry;
            }
            return null;
        }

        fn findStorePointee(proof: *const DefiniteStoreProof, name: []const u8) ?DefiniteStoreValue {
            if (proof.findIndex(name)) |index| {
                if (index >= proof.parameter_count and proof.bindings[index].formal_alias == null) return .unknown;
            }
            const formal = proof.formalName(name);
            for (proof.pointees[0..proof.pointee_count]) |pointee| {
                if (std.mem.eql(u8, proof.tree.tokenSlice(pointee.token), formal)) return pointee.value;
            }
            return null;
        }

        fn setStorePointee(proof: *DefiniteStoreProof, token: Ast.TokenIndex, value: DefiniteStoreValue) bool {
            const original = proof.tree.tokenSlice(token);
            var root = token;
            if (proof.findIndex(original)) |index| {
                if (proof.bindings[index].formal_alias) |alias| {
                    root = alias;
                } else if (index >= proof.parameter_count) return false;
            }
            const name = proof.tree.tokenSlice(root);
            for (proof.pointees[0..proof.pointee_count]) |*pointee| {
                if (std.mem.eql(u8, proof.tree.tokenSlice(pointee.token), name)) {
                    pointee.value = value;
                    pointee.computed = null;
                    return true;
                }
            }
            if (proof.pointee_count == proof.pointees.len) return false;
            proof.pointees[proof.pointee_count] = .{ .token = root, .value = value };
            proof.pointee_count += 1;
            return true;
        }

        fn invalidateStorePointees(proof: *DefiniteStoreProof) void {
            // Revoke identity even in physical mode, before its early return.
            for (proof.bindings[0..proof.binding_count]) |*binding| binding.aggregate_source = null;
            if (proof.out_coverage) |coverage| {
                if (coverage.whole_source != null) coverage.whole_source = .{};
            }
            for (proof.pointees[0..proof.pointee_count]) |*pointee| {
                pointee.value = .unknown;
                if (pointee.computed) |*state| {
                    // An uncertain effect may replace the bytes, but cannot erase
                    // the prior negative alternative or grant a positive identity.
                    state.original = .{};
                    state.base.opaque_alternative = true;
                }
            }
            if (proof.written_inputs != null) return;
            if (proof.out_coverage) |coverage| {
                coverage.complete = false;
                @memset(coverage.covered[0..coverage.field_count], false);
            }
        }

        fn bind(proof: *DefiniteStoreProof, token: Ast.TokenIndex, value: DefiniteStoreValue) bool {
            if (proof.binding_count == proof.bindings.len) return false;
            for (proof.field_facts[0..proof.field_fact_count]) |*fact| {
                if (fact.token == token) {
                    fact.value = .unknown;
                    fact.written_dependencies = .{};
                    fact.fallback_recipe = false;
                    fact.fallback_literal_may = false;
                }
            }
            proof.bindings[proof.binding_count] = .{
                .token = token, .value = value,
                .written_dependencies = proof.written_dependencies,
            };
            proof.binding_count += 1;
            return true;
        }

        fn findIndex(proof: *const DefiniteStoreProof, name: []const u8) ?usize {
            var index = proof.binding_count;
            while (index != 0) {
                index -= 1;
                if (std.mem.eql(u8, proof.tree.tokenSlice(proof.bindings[index].token), name)) return index;
            }
            return null;
        }

        fn overflowTupleBinding(proof: *const DefiniteStoreProof, node: Ast.Node.Index) ?usize {
            if (proof.tree.nodeTag(node) != .identifier) return null;
            const binding = proof.findIndex(proof.tree.tokenSlice(proof.tree.nodeMainToken(node))) orelse return null;
            return if (proof.bindings[binding].overflow_tuple) binding else null;
        }

        fn find(proof: *DefiniteStoreProof, name: []const u8) ?*@TypeOf(proof.bindings[0]) {
            const index = proof.findIndex(name) orelse return null;
            return &proof.bindings[index];
        }
    };

    /// Build the caller's exact lexical values before this call. A nested
    /// call horizon is unsupported rather than flattened across branches.
    fn definiteStoreCaller(
        self: *FileCache,
        call_node: Ast.Node.Index,
        caller_frame: ?TypeResolver.ResolutionFrame,
    ) SummaryError!?DefiniteStoreProof {
        const tree = self.tree;
        const resolver = self.zls orelse return null;
        const declaration = self.enclosingFunctionAt(tree, tree.nodeMainToken(call_node)) orelse return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return null;
        const body = tokens.bodyOf(tree, declaration) orelse return null;
        var proof: DefiniteStoreProof = .{
            .tree = tree,
            .frame = caller_frame orelse resolver.resolutionFrame(),
            .call_node = call_node,
            .call_tree = self.tree,
        };
        var parameters = proto.iterate(tree);
        while (parameters.next()) |parameter| {
            if (parameter.name_token) |token| {
                if (!proof.bind(token, .defined)) return null;
            }
        }
        proof.parameter_count = proof.binding_count;
        // An initialized parameter header does not define its entry pointee.
        // Only explicit stores or addressed payloads establish that premise.
        var statements = engine.AstIterator.init(tree, body);
        const horizon = tree.firstToken(call_node);
        while (statements.next(tree)) |statement| {
            try self.chargeNormalCleanup(call_node);
            if (tree.firstToken(statement) <= horizon and horizon <= tree.lastToken(statement)) {
                // The call may be the exact condition or a statement RHS.
                // Sibling operands and branch-local facts remain unsupported.
                var root = statement;
                if (tree.fullVarDecl(root)) |variable| root = variable.ast.init_node.unwrap() orelse return null;
                if (tree.nodeTag(root) == .assign) root = tree.nodeData(root).node_and_node[1];
                if (tree.fullIf(root)) |branch| root = branch.ast.cond_expr;
                while (tree.nodeTag(root) == .@"try" or tree.nodeTag(root) == .@"catch" or
                    tree.nodeTag(root) == .bool_not or tree.nodeTag(root) == .grouped_expression)
                {
                    root = switch (tree.nodeTag(root)) {
                        .@"try", .bool_not => tree.nodeData(root).node,
                        .@"catch" => tree.nodeData(root).node_and_node[0],
                        else => tree.nodeData(root).node_and_token[0],
                    };
                }
                if (root != call_node) return null;
                return proof;
            }
            if (tree.firstToken(statement) > horizon) return null;
            if (tree.fullVarDecl(statement)) |variable| {
                const value = variable.ast.init_node.unwrap() orelse return null;
                const literal_undefined = try self.literalStoreUndefined(&proof, value, 0);
                const literal_may_undefined = literal_undefined or try self.literalStoreMayUndefined(&proof, value, 0);
                const verdict = try self.definiteStoreValue(&proof, value, 0);
                if (verdict == .unknown) {
                    for (proof.bindings[proof.parameter_count..proof.binding_count], proof.parameter_count..) |*binding, index| {
                        binding.value = .undefined_value;
                        binding.complete_value = false;
                        proof.weakenLiteralStoreBinding(index);
                        binding.written_dependencies = .{};
                    }
                    proof.invalidateAllStoreFields();
                    proof.invalidateStorePointees();
                }
                if (!proof.bind(variable.ast.mut_token + 1, verdict)) return null;
                proof.bindings[proof.binding_count - 1].literal_undefined = literal_undefined;
                proof.bindings[proof.binding_count - 1].literal_may_undefined = literal_may_undefined;
                proof.bindings[proof.binding_count - 1].complete_value =
                    verdict == .defined and try definiteStoreKind(&proof, value) == .aggregate;
                continue;
            }
            switch (tree.nodeTag(statement)) {
                .assign_add,
                .assign_sub,
                .assign_mul,
                .assign_div,
                .assign_add_wrap,
                .assign_sub_wrap,
                .assign_mul_wrap,
                .assign_add_sat,
                .assign_sub_sat,
                .assign_mul_sat,
                .assign_bit_and,
                .assign_bit_or,
                .assign_bit_xor,
                .assign_shl,
                .assign_shr,
                .assign_shl_sat,
                .assign_mod,
                => {
                    const lhs, const rhs = tree.nodeData(statement).node_and_node;
                    if (tree.nodeTag(lhs) == .identifier) {
                        const name = tree.tokenSlice(tree.nodeMainToken(lhs));
                        const left = try self.definiteStoreValue(&proof, lhs, 0);
                        const right = try self.definiteStoreValue(&proof, rhs, 0);
                        if (proof.find(name)) |binding| {
                            binding.value = if (left == .unknown or right == .unknown) .unknown else if (left == .defined and right == .defined) .defined else .undefined_value;
                            if (binding.value != .unknown) continue;
                        }
                    }
                },
                else => {},
            }
            if (tree.nodeTag(statement) == .assign) {
                const lhs, const rhs = tree.nodeData(statement).node_and_node;
                const literal_undefined = try self.literalStoreUndefined(&proof, rhs, 0);
                const literal_may_undefined = literal_undefined or try self.literalStoreMayUndefined(&proof, rhs, 0);
                const verdict = try self.definiteStoreValue(&proof, rhs, 0);
                if (tree.nodeTag(lhs) == .identifier and verdict != .unknown) {
                    if (proof.find(tree.tokenSlice(tree.nodeMainToken(lhs)))) |binding| {
                        proof.invalidateStoreFields(tree.tokenSlice(tree.nodeMainToken(lhs)));
                        binding.value = verdict;
                        binding.complete_value = false;
                        binding.literal_undefined = literal_undefined;
                        binding.literal_may_undefined = literal_may_undefined;
                        continue;
                    }
                }
                if (tree.nodeTag(lhs) == .deref and verdict != .unknown) {
                    const base = tree.nodeData(lhs).node;
                    if (tree.nodeTag(base) == .identifier and
                        proof.setStorePointee(tree.nodeMainToken(base), verdict)) continue;
                }
            }
            if (storeCall(tree, statement)) |call| {
                if (try self.definiteStoreCallValue(&proof, call, 0, statement != call) != .unknown) continue;
            }
            var builtin_buffer: [2]Ast.Node.Index = undefined;
            if (tree.builtinCallParams(&builtin_buffer, statement)) |arguments| {
                const builtin = std.zig.BuiltinFn.list.get(tree.tokenSlice(tree.nodeMainToken(statement)));
                if (builtin != null and builtin.?.tag == .set_float_mode and arguments.len == 1 and
                    tree.nodeTag(arguments[0]) == .enum_literal) continue;
            }
            for (proof.bindings[proof.parameter_count..proof.binding_count], proof.parameter_count..) |*binding, index| {
                binding.value = .undefined_value;
                binding.complete_value = false;
                proof.weakenLiteralStoreBinding(index);
                binding.written_dependencies = .{};
            }
            proof.invalidateAllStoreFields();
            proof.invalidateStorePointees();
            try self.definiteStoreEscapes(&proof, statement, 0);
        }
        return null;
    }

    /// An opaque delegated pointer effect supplies UNKNOWN, not an authenticated
    /// unchanged alternative. Later exact source stores still overlay this base.
    fn unprovedStoreCallOutputs(self: *FileCache, proof: *DefiniteStoreProof, node: Ast.Node.Index) SummaryError!void {
        if (proof.written_inputs == null) return;
        const coverage = proof.out_coverage orelse return;
        const output = proof.out_name orelse return;
        const declaring = if (proof.canonical) |owner|
            (try owner.declaringCache(self)) orelse return
        else self;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(proof.tree, &buffer, node) orelse return;
        const canonical = try declaring.actualCallSummaryAt(call.queryToken(proof.tree, node), proof.frame);
        const count = if (canonical) |actual|
            actual.callee.reference.actual_type.data.function.parameters.len
        else call.ast.params.len;
        for (0..count) |ordinal| {
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = if (canonical) |actual|
                (try actual.callArgumentFor(declaring, &argument_buffer, @intCast(ordinal))) orelse continue
            else call.ast.params[ordinal];
            const operand = if (proof.tree.nodeTag(argument) == .address_of)
                proof.tree.nodeData(argument).node
            else argument;
            const root = tokens.rootIdentifier(proof.tree, operand) orelse continue;
            const name = proof.tree.tokenSlice(proof.tree.nodeMainToken(root));
            if (!std.mem.eql(u8, proof.formalName(name), output)) continue;
            const raw = (try proof.frame.typeOfNode(argument)) orelse continue;
            const ty = (try proof.frame.resolver.normalizedType(raw)) orelse continue;
            if (proof.frame.resolver.pointerSize(ty) == null) continue;
            if (try declaring.callEffectAt(call.queryToken(proof.tree, node), .{
                .parameter = .{ .param = @intCast(ordinal), .read_only_only = true },
            }, .{ .frame = proof.frame })) |effect| if (effect == .read_only) continue;
            coverage.effects_known = false;
            const selected = try self.diagnosticOutputPath(proof.tree, argument, name, 0);
            const path = if (selected) |place| place.path else "";
            coverage.whole_dependencies = .{};
            for (coverage.field_names[0..coverage.field_count], coverage.written_dependencies[0..coverage.field_count]) |field, *dependencies| {
                if (storeEffectReachesPath(path, field)) dependencies.* = .{};
            }
            if (proof.may_written_stores) |stores| {
                var index: usize = 0;
                while (index < stores.count) {
                    if (!storeEffectReachesPath(path, stores.fields[index]) and stores.fields[index].len != 0) {
                        index += 1;
                        continue;
                    }
                    stores.count -= 1;
                    stores.fields[index] = stores.fields[stores.count];
                    stores.dependencies[index] = stores.dependencies[stores.count];
                    stores.literal_may_undefined[index] = stores.literal_may_undefined[stores.count];
                }
            }
            const base: ComputedStoreBase = .{
                .source = coverage.whole_source,
                .computations = coverage.computed_sources,
                .original_alternative = coverage.computed_original_alternative,
                .opaque_alternative = coverage.computed_opaque_alternative,
            };
            const write: ComputedStoreWrite = .{ .path = path, .opaque_alternative = true };
            const unknown: ComputedStoreState = .{ .opaque_alternative = true, .value_nonidentity = true };
            const updated = appendComputedFieldStoreWrite(
                proof, base, write, unknown, coverage.field_names[0..coverage.field_count],
            ) orelse {
                coverage.computed_overflow = true;
                if (path.len == 0) {
                    coverage.whole_source = null;
                    coverage.computed_sources = 0;
                    coverage.computed_original_alternative = false;
                    coverage.computed_opaque_alternative = true;
                }
                continue;
            };
            coverage.whole_source = updated.source;
            coverage.computed_sources = updated.computations;
            coverage.computed_original_alternative = updated.original_alternative;
            coverage.computed_opaque_alternative = updated.opaque_alternative;
            for (proof.pointees[0..proof.pointee_count]) |*pointee| {
                if (!std.mem.eql(u8, proof.tree.tokenSlice(pointee.token), output)) continue;
                pointee.value = .unknown;
                pointee.computed = .{ .original = .{}, .base = updated };
            }
        }
    }

    fn storeEffectReachesPath(effect: []const u8, path: []const u8) bool {
        return effect.len == 0 or std.mem.eql(u8, effect, path) or
            (path.len > effect.len and std.mem.startsWith(u8, path, effect) and
                (path[effect.len] == '.' or path[effect.len] == '['));
    }

    fn definiteStoreEscapes(self: *FileCache, proof: *DefiniteStoreProof, node: Ast.Node.Index, depth: u32) SummaryError!void {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        if (depth == 64) return self.cleanupBudgetFailureAt(proof.call_tree, .normal_cleanup_depth, 64, proof.call_node);
        if (proof.tree.nodeTag(node) == .address_of) {
            if (tokens.rootIdentifier(proof.tree, proof.tree.nodeData(node).node)) |root| {
                const name = proof.tree.tokenSlice(proof.tree.nodeMainToken(root));
                const prior_source = if (proof.find(name)) |binding| binding.aggregate_source else null;
                proof.invalidateStoreFields(name);
                if (proof.find(name)) |binding| {
                    binding.value = .undefined_value;
                    binding.complete_value = false;
                    binding.formal_alias = null;
                    binding.written_dependencies = .{};
                    const header = proof.tree.nodeTag(proof.tree.nodeData(node).node) == .identifier;
                    const raw = if (proof.computed_templates != null or header) try proof.frame.typeOfNode(root) else null;
                    const ty = if (raw) |actual| try proof.frame.resolver.normalizedType(actual) else null;
                    if (header and ty != null) switch (proof.frame.resolver.typeTag(ty.?) orelse .@"struct") {
                        .int, .float, .bool, .@"enum", .pointer => {
                            // Failure to certify an addressed scalar is not a
                            // surviving source-negative witness. Its actual
                            // caller byte snapshot remains the diagnostic input.
                            binding.literal_undefined = false;
                            binding.literal_may_undefined = false;
                            binding.computed_sources = 0;
                            binding.computed_original_alternative = false;
                            binding.computed_opaque_alternative = true;
                            binding.value_nonidentity = true;
                        },
                        else => {},
                    };
                    if (ty != null and proof.frame.resolver.typeTag(ty.?) == .array) {
                        // An opaque call may write; it cannot erase prior poison.
                        binding.aggregate_source = prior_source;
                        binding.computed_opaque_alternative = true;
                    }
                }
            }
        }
        var children = engine.AstIterator.init(proof.tree, node);
        while (children.next(proof.tree)) |child| try self.definiteStoreEscapes(proof, child, depth + 1);
    }
    fn setStoreFieldNode(self: *FileCache, proof: *DefiniteStoreProof, node: Ast.Node.Index, value: DefiniteStoreValue, dependencies: WrittenDependencies) SummaryError!bool {
        const root = tokens.rootIdentifier(proof.tree, node) orelse return false;
        const token = proof.tree.nodeMainToken(root);
        const name = proof.tree.tokenSlice(token);
        if (proof.findIndex(name) == null) return false;
        const resolver = proof.frame.resolver;
        var ty = (try proof.frame.typeOfNode(root)) orelse return false;
        if (resolver.pointerSize(ty) != null) ty = resolver.childType(ty) orelse return false;
        ty = (try resolver.normalizedType(ty)) orelse return false;
        var fields: [128][]const u8 = undefined;
        var defaults: [128]?Ast.Node.Index = @splat(null);
        var coverage: StoreCoverage = .{ .pointee = ty };
        if (!try self.storeCoverageFields(ty, &fields, &defaults, &coverage, proof.call_tree, proof.call_node)) return false;
        const index = (try storeFieldIndex(proof, name, fields[0..coverage.field_count], node)) orelse return false;
        return proof.setStoreField(token, fields[index], value, dependencies);
    }

    /// A C scalar store changes one authenticated local array element, never its extent.
    fn localCElementCallEffect(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        canonical: ActualCallSummary,
        state: *?DefiniteStoreProof,
        parameter: u32,
        pointer: TypeResolver.ActualType,
        actual: Ast.Node.Index,
        chain: []const StoreVisit,
    ) SummaryError!?bool {
        if (proof.written_inputs == null or proof.computed_templates == null or
            proof.frame.resolver.pointerSize(pointer) != .c) return null;
        const tree = proof.tree;
        var root = actual;
        var index: u64 = 0;
        if (tree.nodeTag(actual) == .address_of) {
            root = tree.nodeData(actual).node;
        } else if (tree.fullSlice(actual)) |slice| {
            root = slice.ast.sliced;
            index = (try definiteStoreInteger(proof, slice.ast.start)) orelse return null;
            if (slice.ast.end.unwrap()) |end| {
                const stop = (try definiteStoreInteger(proof, end)) orelse return null;
                if (index >= stop) return null;
            }
        } else return null;
        if (tree.nodeTag(root) != .identifier) return null;
        const name = tree.tokenSlice(tree.nodeMainToken(root));
        const binding = proof.find(name) orelse return null;
        if (binding.formal_alias != null) return null;
        const raw = (try proof.frame.typeOfNode(root)) orelse return null;
        const array = (try proof.frame.resolver.normalizedType(raw)) orelse return null;
        if (proof.frame.resolver.typeTag(array) != .array) return null;
        const extent = (try definiteStoreArrayCount(proof, root)) orelse return null;
        if (index >= extent) return null;
        const element_raw = proof.frame.resolver.childType(array) orelse return null;
        const element = (try proof.frame.resolver.normalizedType(element_raw)) orelse return null;
        const pointee_raw = proof.frame.resolver.childType(pointer) orelse return null;
        const pointee = (try proof.frame.resolver.normalizedType(pointee_raw)) orelse return null;
        if (!element.eql(pointee)) return null;
        const stored = (try self.parameterStoreCoverage(
            canonical, canonical.callee.call_node, parameter, state, chain, null, null, null, null, null, true,
        )) orelse return false;
        if (!stored.complete) return false;
        const source = try self.computedPointeeReadSource(proof, root, "", element, computedCoverageBase(&stored), false);
        const base: ComputedStoreBase = .{
            .source = binding.aggregate_source,
            .computations = binding.computed_sources,
            .original_alternative = binding.computed_original_alternative,
            .opaque_alternative = binding.computed_opaque_alternative,
        };
        const handle = appendComputedStoreWrite(proof, base, .{
            .path = "", .array_index = index, .source = source,
        }) orelse return false;
        binding.aggregate_source = null;
        binding.computed_sources = handle;
        binding.computed_original_alternative = false;
        binding.computed_opaque_alternative = false;
        binding.literal_undefined = false;
        binding.literal_may_undefined = false;
        binding.value_nonidentity = true;
        return true;
    }

    /// Apply only callee-certified stores to exact caller places. A partial
    /// struct store records its fields, not an initialized whole object.
    fn definiteStoreCallEffects(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        canonical: ActualCallSummary,
        state: *?DefiniteStoreProof,
        depth: u32,
    ) SummaryError!bool {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        if (depth >= 64) return self.cleanupBudgetFailureAt(proof.call_tree, .normal_cleanup_depth, 64, proof.call_node);
        const resolver = proof.frame.resolver;
        const formals = canonical.callee.reference.actual_type.data.function.parameters;
        const tree = canonical.callee.tree;
        const chain = [1]StoreVisit{.{ .tree = tree, .declaration = canonical.callee.declaration }};
        var buffer: [2]Ast.Node.Index = undefined;
        for (formals, 0..) |formal, raw| {
            const ty = (try resolver.normalizedType(formal.type)) orelse return false;
            if (resolver.pointerSize(ty) == null) continue;
            const parameter: u32 = @intCast(raw);
            const actual = (try canonical.callArgumentFor(self, &buffer, parameter)) orelse return false;
            if (try self.localCElementCallEffect(proof, canonical, state, parameter, ty, actual, &chain)) |applied| {
                if (!applied) {
                    try self.definiteStoreEscapes(proof, actual, 0);
                    return false;
                }
                continue;
            }
            const addressed = proof.tree.nodeTag(actual) == .address_of;
            const operand = if (addressed) proof.tree.nodeData(actual).node else actual;
            const root = tokens.rootIdentifier(proof.tree, operand) orelse return false;
            const token = proof.tree.nodeMainToken(root);
            const name = proof.tree.tokenSlice(token);
            // This proof keeps the outer diagnostic site. The nested store
            // must instead enter with its actual caller document's call node.
            const coverage = (try self.definiteParameterStore(canonical, canonical.callee.call_node, parameter, state, &chain)) orelse {
                try self.definiteStoreEscapes(proof, actual, 0);
                return false;
            };
            if (addressed and proof.tree.nodeTag(operand) == .identifier) {
                proof.invalidateStoreFields(name);
                const binding = proof.find(name) orelse continue;
                binding.value = if (coverage.complete) .defined else .undefined_value;
                binding.complete_value = coverage.complete;
                if (coverage.complete) binding.written_dependencies = coverage.whole_dependencies;
                for (coverage.field_names[0..coverage.field_count], coverage.covered[0..coverage.field_count], coverage.written_dependencies[0..coverage.field_count]) |path, written, dependencies| {
                    if (written and !proof.setStoreField(token, path, .defined, dependencies)) return false;
                }
                binding.aggregate_source = if (coverage.complete) coverage.whole_source else null;
                if (coverage.complete and proof.written_inputs != null and
                    proof.computed_templates != null and binding.formal_alias == null)
                {
                    switch (resolver.typeTag(coverage.pointee) orelse .@"struct") {
                        .int, .float, .bool, .@"enum" => {
                            // The nested store replaced this local's bytes.
                            // Carry its current recipe, not the declaration's
                            // obsolete literal witness or a value certificate.
                            const base: ComputedStoreBase = if (coverage.computed_overflow)
                                .{ .opaque_alternative = true }
                            else computedCoverageBase(&coverage);
                            const source = try self.computedPointeeReadSource(
                                proof, operand, "", coverage.pointee, base, false,
                            );
                            binding.written_dependencies = .{ .reads = source.projections };
                            binding.aggregate_source = source;
                            binding.literal_undefined = false;
                            binding.literal_may_undefined = false;
                            binding.computed_sources = 0;
                            binding.computed_original_alternative = false;
                            binding.computed_opaque_alternative = source.opaque_alternative;
                            binding.value_nonidentity = true;
                        },
                        else => {},
                    }
                }
            } else if (addressed and proof.tree.nodeTag(operand) == .field_access) {
                if (coverage.complete and !try self.setStoreFieldNode(proof, operand, .defined, coverage.whole_dependencies)) return false;
            } else if (!addressed and proof.tree.nodeTag(operand) == .identifier) {
                const prior = proof.findStorePointee(name);
                if (coverage.complete or (prior orelse .unknown) == .defined) {
                    if (!proof.setStorePointee(token, .defined)) return false;
                }
            } else {
                // A slice or indexed pointer does not designate all of its
                // root's storage. Never promote its root to complete.
                try self.definiteStoreEscapes(proof, actual, 0);
            }
        }
        return true;
    }

    const DefiniteStoreKind = enum { scalar, aggregate, unresolved };

    /// A scalar value is defined exactly when its dependencies are. An
    /// aggregate or pointer value is a whole other proof: only a parameter
    /// the caller supplied is trusted to be fully defined, never a local
    /// whose initializer could still hide an undefined member. A type that
    /// does not resolve, or is neither, proves nothing.
    fn definiteStoreKind(proof: *const DefiniteStoreProof, node: Ast.Node.Index) SummaryError!DefiniteStoreKind {
        // Inferred aggregate literals have an expected type, not a standalone
        // expression type. Their value/default proof must already succeed
        // before this classification can publish a complete binding.
        var buffer: [2]Ast.Node.Index = undefined;
        if (proof.tree.fullStructInit(&buffer, node) != null or
            proof.tree.fullArrayInit(&buffer, node) != null) return .aggregate;
        if (proof.overflowTupleBinding(node) != null) return .aggregate;
        if (proof.tree.nodeTag(node) == .array_access) {
            const base, const index = proof.tree.nodeData(node).node_and_node;
            if (proof.overflowTupleBinding(base) != null) {
                const slot = (try definiteStoreInteger(proof, index)) orelse return .unresolved;
                return if (slot < 2) .scalar else .unresolved;
            }
        }
        const ty = (try proof.frame.typeOfNode(node)) orelse return .unresolved;
        const actual = (try proof.frame.resolver.normalizedType(ty)) orelse return .unresolved;
        return switch (proof.frame.resolver.typeTag(actual) orelse return .unresolved) {
            .int, .comptime_int, .float, .comptime_float, .bool, .@"enum" => .scalar,
            .@"struct", .@"union", .pointer, .optional, .array, .vector, .error_union, .error_set => .aggregate,
            else => .unresolved,
        };
    }
    fn definiteStoreCallReturnAllowed(proof: *const DefiniteStoreProof, node: Ast.Node.Index) SummaryError!bool {
        if (try definiteStoreKind(proof, node) == .scalar) return true;
        // The strict scalar proof still declines aggregate returns. Physical
        // transport can retain an optional's existing immutable result recipe.
        if (proof.written_inputs == null or proof.computed_templates == null) return false;
        const ty = (try proof.frame.typeOfNode(node)) orelse return false;
        const normalized = (try proof.frame.resolver.normalizedType(ty)) orelse return false;
        return proof.frame.resolver.typeTag(normalized) == .optional;
    }

    /// Evaluate a resolved scalar or physical optional-return body in its caller's lexical state.
    /// Calls with unsupported effects never preserve local dependency facts.
    fn definiteStoreCallValue(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        depth: u32,
        selected_success: bool,
    ) SummaryError!DefiniteStoreValue {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        if (depth >= 64) return self.cleanupBudgetFailureAt(proof.call_tree, .normal_cleanup_depth, 64, proof.call_node);
        const declaring = if (proof.canonical) |canonical|
            (try canonical.declaringCache(self)) orelse return .unknown
        else
            self;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(proof.tree, &buffer, node) orelse return .unknown;
        const canonical = (try declaring.actualCallSummaryAt(call.queryToken(proof.tree, node), proof.frame)) orelse {
            try self.unprovedStoreCallOutputs(proof, node);
            return .unknown;
        };
        const tree = canonical.callee.tree;
        if (tree.nodeTag(canonical.callee.declaration) != .fn_decl) {
            try self.unprovedStoreCallOutputs(proof, node);
            return .unknown;
        }
        if (!selected_success) {
            const result_type = (try proof.frame.typeOfNode(node)) orelse return .unknown;
            const normalized = (try proof.frame.resolver.normalizedType(result_type)) orelse return .unknown;
            if (proof.frame.resolver.typeTag(normalized) == .error_union) return .unknown;
        }
        const value_key = resolvedCleanupKey(canonical.callee.reference, canonical.callee.declaration);
        if (self.store_value_visiting.contains(value_key)) return .unknown;
        try self.store_value_visiting.put(self.gpa, value_key, {});
        defer _ = self.store_value_visiting.remove(value_key);
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return .unknown;
        var state: ?DefiniteStoreProof = proof.*;
        const callee_cache = (try canonical.declaringCache(declaring)) orelse return .unknown;
        const callee_resolver = callee_cache.zls orelse return .unknown;
        var callee: DefiniteStoreProof = .{
            .tree = tree,
            .frame = callee_resolver.frameForFunction(canonical.callee.reference),
            .canonical = canonical,
            .caller = &state,
            .caller_cache = declaring,
            .call_node = proof.call_node,
            .call_tree = proof.call_tree,
            .written_inputs = proof.written_inputs,
            .written_reads = proof.written_reads,
            .written_dependencies_complete = proof.written_dependencies_complete,
            .computed_templates = proof.computed_templates,
            .identity_inputs = proof.identity_inputs,
            .identity_tree = proof.identity_tree,
        };
        var parameters = proto.iterate(tree);
        var parameter_index: u32 = 0;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            const token = parameter.name_token orelse continue;
            const actual = (try canonical.callArgumentFor(declaring, &buffer, parameter_index)) orelse return .unknown;
            const aggregate_source = try declaring.wholeStoreSource(&state.?, actual, depth + 1);
            callee.written_dependencies = .{};
            const literal_undefined = proof.computed_templates != null and
                try declaring.literalStoreUndefined(&state.?, actual, depth + 1);
            const literal_may_undefined = literal_undefined or (proof.computed_templates != null and
                try declaring.literalStoreMayUndefined(&state.?, actual, depth + 1));
            const verdict = try self.definiteCallerStoreValue(&callee, declaring, &state.?, actual, depth + 1);
            if (verdict == .unknown or !callee.bind(token, verdict)) return .unknown;
            callee.bindings[callee.binding_count - 1].literal_undefined = literal_undefined;
            callee.bindings[callee.binding_count - 1].literal_may_undefined = literal_may_undefined;
            callee.bindings[callee.binding_count - 1].aggregate_source = aggregate_source;
        }
        callee.parameter_count = callee.binding_count;
        const body = tokens.bodyOf(tree, canonical.callee.declaration) orelse return .unknown;
        var result: DefiniteStoreValue = .defined;
        var result_dependencies: WrittenDependencies = .{};
        var result_literal_all = true;
        var result_literal_may = false;
        var result_computed: ComputedStoreState = .{};
        var result_value_seen = false;
        var statements = engine.AstIterator.init(tree, body);
        while (statements.next(tree)) |statement| {
            try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
            if (tree.fullIf(statement)) |branch| {
                if (branch.payload_token != null or branch.error_token != null or
                    branch.ast.else_expr != .none or tree.nodeTag(branch.ast.then_expr) != .@"return") return .unknown;
                if (try declaring.definiteStoreValue(&callee, branch.ast.cond_expr, depth + 1) != .defined) return .unknown;
                // Only literal booleans select a path. A runtime lexical const
                // may depend on storage changed since its initializer.
                const condition: ?bool = if (tree.nodeTag(branch.ast.cond_expr) == .identifier) blk: {
                    const name = tree.tokenSlice(tree.nodeMainToken(branch.ast.cond_expr));
                    break :blk if (std.mem.eql(u8, name, "true")) true else if (std.mem.eql(u8, name, "false")) false else null;
                } else null;
                if (condition == false) continue;
                const value = tree.nodeData(branch.ast.then_expr).opt_node.unwrap() orelse return .unknown;
                if (tree.nodeTag(value) == .error_value) {
                    // An error arm has no successful scalar result.
                    if (condition == true) return .unknown;
                    continue;
                }
                if (!try definiteStoreCallReturnAllowed(&callee, value)) return .unknown;
                var returned_state = callee;
                returned_state.written_dependencies = .{};
                const evaluated = try declaring.definiteStoreValueWithComputed(&returned_state, value, depth + 1);
                const verdict = evaluated.value;
                result_literal_all = result_literal_all and evaluated.literal_undefined;
                result_literal_may = result_literal_may or evaluated.literal_may_undefined;
                var returned_computed = evaluated.computed;
                if (returned_computed.source == null and returned_computed.computations == 0 and
                    !returned_computed.original_alternative and !returned_computed.opaque_alternative)
                    returned_computed.opaque_alternative = true;
                if (result_value_seen) result_computed.merge(returned_computed) else result_computed = returned_computed;
                result_value_seen = true;
                result_dependencies.merge(returned_state.written_dependencies);
                if (verdict == .unknown) return .unknown;
                if (verdict != .defined) result = .undefined_value;
                if (condition == true) break;
                continue;
            }
            if (tree.nodeTag(statement) == .@"return") {
                if (tree.nodeData(statement).opt_node.unwrap()) |value| {
                    if (tree.nodeTag(value) == .error_value or
                        !try definiteStoreCallReturnAllowed(&callee, value)) return .unknown;
                    callee.written_dependencies = .{};
                    const evaluated = try declaring.definiteStoreValueWithComputed(&callee, value, depth + 1);
                    const verdict = evaluated.value;
                    result_literal_all = result_literal_all and evaluated.literal_undefined;
                    result_literal_may = result_literal_may or evaluated.literal_may_undefined;
                    var returned_computed = evaluated.computed;
                    if (returned_computed.source == null and returned_computed.computations == 0 and
                        !returned_computed.original_alternative and !returned_computed.opaque_alternative)
                        returned_computed.opaque_alternative = true;
                    if (result_value_seen) result_computed.merge(returned_computed) else result_computed = returned_computed;
                    result_value_seen = true;
                    result_dependencies.merge(callee.written_dependencies);
                    if (verdict == .unknown) return .unknown;
                    if (verdict != .defined) result = .undefined_value;
                }
                break;
            }
            if (tree.fullVarDecl(statement)) |variable| {
                const value = variable.ast.init_node.unwrap() orelse return .unknown;
                callee.written_dependencies = .{};
                const evaluated = try declaring.definiteStoreValueWithComputed(&callee, value, depth + 1);
                const verdict = evaluated.value;
                if (verdict == .unknown or !callee.bind(variable.ast.mut_token + 1, verdict)) return .unknown;
                callee.bindings[callee.binding_count - 1].literal_undefined = evaluated.literal_undefined;
                callee.bindings[callee.binding_count - 1].literal_may_undefined = evaluated.literal_may_undefined;
                callee.bindings[callee.binding_count - 1].aggregate_source = evaluated.computed.source;
                callee.bindings[callee.binding_count - 1].computed_sources = evaluated.computed.computations;
                callee.bindings[callee.binding_count - 1].computed_original_alternative = evaluated.computed.original_alternative;
                callee.bindings[callee.binding_count - 1].computed_opaque_alternative = evaluated.computed.opaque_alternative;
                callee.bindings[callee.binding_count - 1].value_nonidentity = evaluated.computed.value_nonidentity;
                callee.bindings[callee.binding_count - 1].complete_value =
                    verdict == .defined and try definiteStoreKind(&callee, value) == .aggregate;
                if (tree.tokenTag(variable.ast.mut_token) == .keyword_const) {
                    var tuple_buffer: [2]Ast.Node.Index = undefined;
                    if (tree.builtinCallParams(&tuple_buffer, value)) |arguments| {
                        const builtin = std.zig.BuiltinFn.list.get(tree.tokenSlice(tree.nodeMainToken(value))) orelse return .unknown;
                        if (arguments.len == 2 and (builtin.tag == .add_with_overflow or
                            builtin.tag == .sub_with_overflow or builtin.tag == .mul_with_overflow))
                        {
                            callee.bindings[callee.binding_count - 1].complete_value = verdict == .defined;
                            callee.bindings[callee.binding_count - 1].overflow_tuple = true;
                        }
                    }
                }
                continue;
            }
            if (tree.nodeTag(statement) == .assign) {
                const lhs, const rhs = tree.nodeData(statement).node_and_node;
                callee.written_dependencies = .{};
                const evaluated = try declaring.definiteStoreValueWithComputed(&callee, rhs, depth + 1);
                const verdict = evaluated.value;
                if (verdict == .unknown) return .unknown;
                if (tree.nodeTag(lhs) == .identifier) {
                    const name = tree.tokenSlice(tree.nodeMainToken(lhs));
                    if (std.mem.eql(u8, name, "_")) continue;
                    const binding = callee.find(name) orelse return .unknown;
                    callee.invalidateStoreFields(name);
                    binding.complete_value = false;
                    binding.value = verdict;
                    binding.written_dependencies = callee.written_dependencies;
                    binding.literal_undefined = evaluated.literal_undefined;
                    binding.literal_may_undefined = evaluated.literal_may_undefined;
                    binding.aggregate_source = evaluated.computed.source;
                    binding.computed_sources = evaluated.computed.computations;
                    binding.computed_original_alternative = evaluated.computed.original_alternative;
                    binding.computed_opaque_alternative = evaluated.computed.opaque_alternative;
                    binding.value_nonidentity = evaluated.computed.value_nonidentity;
                    continue;
                }
                // Only an explicit formal's inline fields or pointee may be
                // changed. Global stores and aliases remain unsupported.
                if (tree.nodeTag(lhs) == .field_access) {
                    const root = tokens.rootIdentifier(tree, lhs) orelse return .unknown;
                    const index = callee.findIndex(tree.tokenSlice(tree.nodeMainToken(root))) orelse return .unknown;
                    if (index >= callee.parameter_count or verdict != .defined or
                        !try declaring.setStoreFieldNode(&callee, lhs, verdict, callee.written_dependencies)) return .unknown;
                    continue;
                }
                if (tree.nodeTag(lhs) != .deref) return .unknown;
                const base = tree.nodeData(lhs).node;
                if (tree.nodeTag(base) != .identifier) return .unknown;
                const index = callee.findIndex(tree.tokenSlice(tree.nodeMainToken(base))) orelse return .unknown;
                if (index >= callee.parameter_count or
                    !callee.setStorePointee(tree.nodeMainToken(base), verdict)) return .unknown;
                continue;
            }
            if (storeCall(tree, statement)) |nested| {
                if (try declaring.definiteStoreCallValue(&callee, nested, depth + 1, statement != nested) == .unknown) return .unknown;
                continue;
            }
            var builtin_buffer: [2]Ast.Node.Index = undefined;
            const arguments = tree.builtinCallParams(&builtin_buffer, statement) orelse return .unknown;
            const builtin = std.zig.BuiltinFn.list.get(tree.tokenSlice(tree.nodeMainToken(statement))) orelse return .unknown;
            if (builtin.tag != .set_float_mode or arguments.len != 1 or tree.nodeTag(arguments[0]) != .enum_literal) return .unknown;
        }
        // Argument evaluation can mutate caller locals too. Preserve its exact
        // post-evaluation facts before applying the callee's own stores.
        proof.* = state.?;
        proof.written_dependencies.merge(result_dependencies);
        if (!try declaring.definiteStoreCallEffects(proof, canonical, &state, depth)) return .unknown;
        proof.computed_result = result_computed;
        proof.computed_result.literal_undefined = result_value_seen and result_literal_all;
        proof.computed_result.literal_may_undefined = result_literal_may;
        return result;
    }

    fn originatingWrittenArgument(
        self: *FileCache,
        proof: *const DefiniteStoreProof,
        node: Ast.Node.Index,
        depth: u32,
    ) SummaryError!?Ast.Node.Index {
        if (depth >= 64) return null;
        try self.chargeNormalCleanupAt(proof.tree, node);
        var selected = node;
        if (proof.tree.nodeTag(selected) == .address_of) selected = proof.tree.nodeData(selected).node;
        if (proof.tree.nodeTag(selected) != .identifier) return null;
        const name = proof.formalName(proof.tree.tokenSlice(proof.tree.nodeMainToken(selected)));
        const canonical = proof.canonical orelse return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(proof.tree, &proto_buffer, canonical.callee.declaration) orelse return null;
        var parameters = proto.iterate(proof.tree);
        var index: u32 = 0;
        while (parameters.next()) |parameter| : (index += 1) {
            const token = parameter.name_token orelse continue;
            if (!std.mem.eql(u8, proof.tree.tokenSlice(token), name)) continue;
            var buffer: [2]Ast.Node.Index = undefined;
            const caller_cache = proof.caller_cache orelse self;
            const argument = (try canonical.callArgumentFor(caller_cache, &buffer, index)) orelse return null;
            if (proof.written_input_boundary) return argument;
            const caller_slot = proof.caller orelse return null;
            const caller = if (caller_slot.*) |*state| state else return null;
            return caller_cache.originatingWrittenArgument(caller, argument, depth + 1);
        }
        return null;
    }

    fn definiteStoreDeref(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        base: Ast.Node.Index,
        depth: u32,
    ) SummaryError!DefiniteStoreValue {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        if (depth >= 64) return self.cleanupBudgetFailureAt(proof.call_tree, .normal_cleanup_depth, 64, proof.call_node);
        const tree = proof.tree;
        if (tree.nodeTag(base) != .identifier) return .unknown;
        const name = proof.formalName(tree.tokenSlice(tree.nodeMainToken(base)));
        if (proof.collect_written_inputs) if (proof.out_name) |output| {
            if (std.mem.eql(u8, name, output)) if (proof.out_coverage) |coverage| {
                if (coverage.complete) {
                    proof.written_dependencies.merge(coverage.whole_dependencies);
                } else if (proof.written_reads != null) {
                    _ = try self.definiteStoreValueInner(proof, base, depth + 1);
                }
            };
        };
        if (proof.findStorePointee(name)) |value| return value;
        if (proof.out_name) |output| {
            if (std.mem.eql(u8, name, output)) {
                const coverage = proof.out_coverage orelse return .undefined_value;
                return if (coverage.complete) .defined else .undefined_value;
            }
        }
        if (proof.canonical) |canonical| {
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return .unknown;
            var parameters = proto.iterate(tree);
            var index: u32 = 0;
            while (parameters.next()) |parameter| : (index += 1) {
                const token = parameter.name_token orelse continue;
                if (!std.mem.eql(u8, name, tree.tokenSlice(token))) continue;
                var buffer: [2]Ast.Node.Index = undefined;
                const caller_cache = proof.caller_cache orelse self;
                const argument = (try canonical.callArgumentFor(caller_cache, &buffer, index)) orelse return .unknown;
                if (proof.written_reads != null) {
                    const origin = try self.originatingWrittenArgument(proof, base, depth + 1);
                    if (origin) |actual|
                        return if (try proof.recordWrittenRead(actual)) .defined else .unknown;
                }
                const caller = proof.caller orelse return .unknown;
                if (caller.* == null) caller.* = try caller_cache.definiteStoreCaller(proof.call_node, canonical.callee.caller_frame);
                const state = if (caller.*) |*value| value else return .undefined_value;
                if (state.tree.nodeTag(argument) == .address_of)
                    return self.definiteCallerStoreValue(proof, caller_cache, state, state.tree.nodeData(argument).node, depth + 1);
                if (index == 0 and canonical.argument_offset == 1) {
                    const actual_type = (try state.frame.typeOfNode(argument)) orelse return .unknown;
                    const actual = (try state.frame.resolver.normalizedType(actual_type)) orelse return .unknown;
                    // An instance method takes the address of its by-value
                    // receiver place. Its value proof, not a pointer header,
                    // establishes the payload read through the receiver.
                    if (state.frame.resolver.pointerSize(actual) == null)
                        return caller_cache.definiteStoreValue(state, argument, depth + 1);
                }
                if (state.tree.fullSlice(argument)) |slice| {
                    const header = try caller_cache.definiteStoreValue(state, argument, depth + 1);
                    if (header != .defined) return header;
                    return caller_cache.definiteStoreProjectionBase(state, slice.ast.sliced, depth + 1);
                }
                if (state.tree.nodeTag(argument) == .identifier)
                    return caller_cache.definiteStoreDeref(state, argument, depth + 1);
                return .undefined_value;
            }
        }
        return .undefined_value;
    }

    /// Indexing and implicit pointer fields read storage, not a pointer header.
    /// A by-value aggregate still uses its ordinary complete-value premise.
    fn definiteStoreProjectionBase(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        base: Ast.Node.Index,
        depth: u32,
    ) SummaryError!DefiniteStoreValue {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        if (depth >= 64) return self.cleanupBudgetFailureAt(proof.call_tree, .normal_cleanup_depth, 64, proof.call_node);
        if (proof.overflowTupleBinding(base) != null)
            return self.definiteStoreValue(proof, base, depth + 1);
        const ty = (try proof.frame.typeOfNode(base)) orelse return .unknown;
        const actual = (try proof.frame.resolver.normalizedType(ty)) orelse return .unknown;
        if (proof.frame.resolver.pointerSize(actual) == null)
            return self.definiteStoreValue(proof, base, depth + 1);
        if (proof.tree.fullSlice(base)) |slice| {
            const header = try self.definiteStoreValue(proof, base, depth + 1);
            if (header != .defined) return header;
            return self.definiteStoreProjectionBase(proof, slice.ast.sliced, depth + 1);
        }
        if (proof.tree.nodeTag(base) == .address_of)
            return self.definiteStoreValue(proof, proof.tree.nodeData(base).node, depth + 1);
        // Evaluate formal actuals first, including ignored arguments that can
        // mutate the payload. Header definedness itself never proves storage.
        if (try self.definiteStoreValue(proof, base, depth + 1) == .unknown) return .unknown;
        return self.definiteStoreDeref(proof, base, depth + 1);
    }

    /// Aggregate completeness includes omitted values in the actual declaring
    /// container. An inferred literal needs its canonical expected type; syntax
    /// alone cannot establish that no undefined default was omitted.
    fn definiteStoreAggregateValue(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        depth: u32,
    ) SummaryError!DefiniteStoreValue {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        const tree = proof.tree;
        const resolver = proof.frame.resolver;
        var buffer: [2]Ast.Node.Index = undefined;
        const structure = tree.fullStructInit(&buffer, node);
        const array = if (structure == null) tree.fullArrayInit(&buffer, node) else null;
        const values = if (structure) |literal| literal.ast.fields else if (array) |literal| literal.ast.elements else return .unknown;
        const type_expr = if (structure) |literal| literal.ast.type_expr else array.?.ast.type_expr;
        var actual = if (type_expr == .none)
            (try proof.frame.expectedTypeOfNode(node)) orelse return .unknown
        else
            (try proof.frame.typeOfNode(node)) orelse return .unknown;
        // Optional/error wrappers add no omitted aggregate field. Use the
        // existing recursion bound rather than a separate wrapper limit.
        var type_depth = depth;
        while (true) {
            actual = (try resolver.normalizedType(actual)) orelse return .unknown;
            const tag = resolver.typeTag(actual) orelse return .unknown;
            if (tag != .optional and tag != .error_union) break;
            try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
            type_depth += 1;
            if (type_depth == 64) return self.cleanupBudgetFailureAt(proof.call_tree, .normal_cleanup_depth, 64, proof.call_node);
            actual = resolver.childType(actual) orelse return .unknown;
        }
        const tag = resolver.typeTag(actual) orelse return .unknown;
        if (tag != .array and tag != .@"struct") return .unknown;
        var array_extent: ?u64 = null;
        if (tag == .array) {
            const count: u64 = switch (actual.data) {
                .array => |info| blk: {
                    if (info.sentinel != .none) return .unknown;
                    break :blk info.elem_count orelse return .unknown;
                },
                .ip_index => switch (resolver.ctx.ip.indexToKey(actual.ipIndex() orelse return .unknown)) {
                    .array_type => |info| blk: {
                        if (info.sentinel != .none) return .unknown;
                        break :blk info.len;
                    },
                    else => return .unknown,
                },
                else => return .unknown,
            };
            if (count != values.len) return .unknown;
            array_extent = count;
        } else if (structure == null or actual.data != .container) return .unknown;

        // Evaluate explicit payloads once, in source order. The physical
        // recipe borrows only the resulting source/dependency facts.
        const collect_recipe = proof.computed_templates != null and values.len <= 128;
        if (proof.computed_templates != null and values.len > 128) {
            proof.computed_templates.?.overflow = true;
            proof.computed_result = .{ .opaque_alternative = true, .value_nonidentity = true };
        }
        var evaluated_values: [128]DefiniteStoreResult = undefined;
        var value_dependencies: [128]WrittenDependencies = undefined;
        var result: DefiniteStoreValue = .defined;
        for (values, 0..) |value, index| {
            var verdict: DefiniteStoreValue = undefined;
            if (collect_recipe) {
                const saved_dependencies = proof.written_dependencies;
                proof.written_dependencies = .{};
                const evaluated = try self.definiteStoreValueWithComputed(proof, value, depth + 1);
                const dependencies = proof.written_dependencies;
                proof.written_dependencies = saved_dependencies;
                proof.written_dependencies.merge(dependencies);
                evaluated_values[index] = evaluated;
                value_dependencies[index] = dependencies;
                verdict = evaluated.value;
            } else {
                verdict = try self.definiteStoreValue(proof, value, depth + 1);
            }
            if (verdict == .unknown) return .unknown;
            if (verdict == .undefined_value) result = .undefined_value;
        }
        if (tag == .array) {
            if (collect_recipe) {
                var writes: [128]ComputedStoreWrite = undefined;
                var write_count: usize = 0;
                for (values, 0..) |value, index| {
                    const component = try self.computedStoreWriteForValue(
                        proof,
                        "",
                        value,
                        evaluated_values[index],
                        value_dependencies[index],
                        true,
                        array_extent,
                        @intCast(index),
                    );
                    if (!appendComputedComponent(proof, tree.nodeMainToken(node), &writes, &write_count, component, evaluated_values[index].computed)) break;
                }
                setComputedStoreConstructor(proof, node, writes[0..write_count], true, array_extent);
            }
            return result;
        }

        const frame = resolver.frameForContainer(actual.data.container);
        const owner_tree = &frame.handle.document.tree;
        var declaration_buffer: [2]Ast.Node.Index = undefined;
        const declaration = owner_tree.fullContainerDecl(&declaration_buffer, actual.data.container.scope_handle.toNode()) orelse return .unknown;
        if (values.len > proof.bindings.len) return .unknown;
        var supplied: [128]bool = @splat(false);
        var writes: [128]ComputedStoreWrite = undefined;
        var write_count: usize = 0;
        var field_count: usize = 0;
        for (declaration.ast.members) |member| {
            try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
            const field = owner_tree.fullContainerField(member) orelse continue;
            if (field.ast.tuple_like or field_count == supplied.len) return .unknown;
            field_count += 1;
            const field_type_node = field.ast.type_expr.unwrap() orelse return .unknown;
            const field_type = (try frame.typeOfNode(field_type_node)) orelse return .unknown;
            _ = (try resolver.normalizedType(field_type)) orelse return .unknown;
            const name = owner_tree.tokenSlice(field.ast.main_token);
            var explicit_index: ?usize = null;
            for (values, 0..) |value, index| {
                try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
                const first = tree.firstToken(value);
                if (first < 3 or tree.tokenTag(first - 1) != .equal or
                    tree.tokenTag(first - 2) != .identifier or tree.tokenTag(first - 3) != .period or
                    !std.mem.eql(u8, tree.tokenSlice(first - 2), name)) continue;
                if (explicit_index != null or supplied[index]) return .unknown;
                supplied[index] = true;
                explicit_index = index;
            }
            if (explicit_index) |index| {
                if (collect_recipe) {
                    const component = try self.computedStoreWriteForValue(
                        proof,
                        name,
                        values[index],
                        evaluated_values[index],
                        value_dependencies[index],
                        false,
                        null,
                        null,
                    );
                    _ = appendComputedComponent(proof, tree.nodeMainToken(node), &writes, &write_count, component, evaluated_values[index].computed);
                }
                continue;
            }
            const default = field.ast.value_expr.unwrap() orelse return .unknown;
            var default_proof: DefiniteStoreProof = .{
                .tree = owner_tree,
                .frame = frame,
                .call_node = proof.call_node,
                .call_tree = proof.call_tree,
                .computed_templates = proof.computed_templates,
            };
            const default_evaluated = if (collect_recipe)
                try self.definiteStoreValueWithComputed(&default_proof, default, depth + 1)
            else
                null;
            const verdict = if (default_evaluated) |evaluated|
                evaluated.value
            else
                try self.definiteStoreValue(&default_proof, default, depth + 1);
            if (verdict == .unknown) return .unknown;
            if (verdict == .undefined_value) result = .undefined_value;
            if (collect_recipe) {
                const component = try self.computedStoreWriteForValue(
                    &default_proof,
                    name,
                    default,
                    default_evaluated.?,
                    default_proof.written_dependencies,
                    false,
                    null,
                    null,
                );
                _ = appendComputedComponent(proof, tree.nodeMainToken(node), &writes, &write_count, component, default_evaluated.?.computed);
            }
        }
        for (supplied[0..values.len]) |matched| {
            if (!matched) return .unknown;
        }
        if (collect_recipe) setComputedStoreConstructor(proof, node, writes[0..write_count], false, null);
        return result;
    }

    /// A namespace header does not establish the value of one of its members.
    fn definiteStoreNamespaceValue(self: *FileCache, proof: *DefiniteStoreProof, node: Ast.Node.Index, depth: u32) SummaryError!?DefiniteStoreValue {
        const base, const selector = proof.tree.nodeData(node).node_and_token;
        const resolver = proof.frame.resolver;
        var namespace = (try proof.frame.resolveValueOfNode(base)) orelse return null;
        if (!namespace.is_type_val) return null;
        namespace = (try resolver.normalizedType(namespace)) orelse return .unknown;
        if (namespace.data != .container) return .unknown;
        const owner = resolver.frameForContainer(namespace.data.container);
        const tree = &owner.handle.document.tree;
        const container_node = namespace.data.container.scope_handle.toNode();
        var buffer: [2]Ast.Node.Index = undefined;
        const members = if (tree.fullContainerDecl(&buffer, container_node)) |container|
            container.ast.members
        else if (tree.nodeTag(container_node) == .root)
            tree.rootDecls()
        else
            return .unknown;
        const wanted = proof.tree.tokenSlice(selector);
        for (members) |member| {
            try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
            var initializer: ?Ast.Node.Index = null;
            if (tree.fullVarDecl(member)) |declaration| {
                if (!std.mem.eql(u8, tree.tokenSlice(declaration.ast.mut_token + 1), wanted)) continue;
                if (tree.tokenTag(declaration.ast.mut_token) != .keyword_const) return .unknown;
                initializer = declaration.ast.init_node.unwrap() orelse return .unknown;
            } else if (tree.fullContainerField(member)) |field| {
                if (!std.mem.eql(u8, tree.tokenSlice(field.ast.main_token), wanted)) continue;
                if (resolver.typeTag(namespace) != .@"enum") return .unknown;
                initializer = field.ast.value_expr.unwrap();
                if (initializer == null) return .defined;
            } else {
                var proto_buffer: [1]Ast.Node.Index = undefined;
                const proto = tokens.fnProto(tree, &proto_buffer, member) orelse continue;
                const token = proto.name_token orelse continue;
                if (std.mem.eql(u8, tree.tokenSlice(token), wanted)) return .defined;
                continue;
            }
            var member_proof: DefiniteStoreProof = .{
                .tree = tree,
                .frame = owner,
                .call_node = proof.call_node,
                .call_tree = proof.call_tree,
            };
            return try self.definiteStoreValue(&member_proof, initializer.?, depth + 1);
        }
        return .unknown;
    }

    fn definiteCallerStoreValue(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        caller_cache: *FileCache,
        caller: *DefiniteStoreProof,
        node: Ast.Node.Index,
        depth: u32,
    ) SummaryError!DefiniteStoreValue {
        _ = self;
        const saved = caller.written_dependencies;
        const collecting = caller.collect_written_inputs;
        caller.written_dependencies = .{};
        caller.collect_written_inputs = collecting and proof.collect_written_inputs;
        defer {
            caller.written_dependencies = saved;
            caller.collect_written_inputs = collecting;
        }
        const value = try caller_cache.definiteStoreValue(caller, node, depth);
        if (proof.collect_written_inputs) proof.written_dependencies.merge(caller.written_dependencies);
        return value;
    }

    /// Pure scalar expressions distinguish an undefined dependency from an
    /// unsupported effect. Only exact canonical actuals define callee formals.
    fn definiteStoreValue(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        depth: u32,
    ) SummaryError!DefiniteStoreValue {
        return (try self.definiteStoreValueWithComputed(proof, node, depth)).value;
    }

    fn literalStoreUndefined(self: *FileCache, proof: *const DefiniteStoreProof, node: Ast.Node.Index, depth: u32) SummaryError!bool {
        return self.literalStoreUndefinedMode(proof, node, depth, false);
    }

    fn literalStoreMayUndefined(self: *FileCache, proof: *const DefiniteStoreProof, node: Ast.Node.Index, depth: u32) SummaryError!bool {
        return self.literalStoreUndefinedMode(proof, node, depth, true);
    }

    /// A failed strict certificate is not a poison witness. Only explicit
    /// literal syntax or a saved, scoped literal witness can answer true.
    const LiteralStoreBox = struct {
        kind: enum { optional_payload, error_payload, unsupported_payload },
        value_node: Ast.Node.Index,
    };

    fn literalStoreBoxing(proof: *const DefiniteStoreProof, node: Ast.Node.Index) SummaryError!?LiteralStoreBox {
        const tree = proof.tree;
        var value_node = node;
        while (tree.nodeTag(value_node) == .grouped_expression)
            value_node = tree.nodeData(value_node).node_and_token[0];
        if (tree.nodeTag(value_node) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(value_node)), "undefined")) return null;
        const actual_raw = (try proof.frame.typeOfNode(node)) orelse return null;
        const actual = (try proof.frame.resolver.normalizedType(actual_raw)) orelse return null;
        const expected_raw = (try proof.frame.expectedTypeOfNode(node)) orelse actual_raw;
        const expected = (try proof.frame.resolver.normalizedType(expected_raw)) orelse return null;
        // Interned and structural wrappers use the same semantic queries.
        const expected_tag = proof.frame.resolver.typeTag(expected) orelse return null;
        const actual_tag = proof.frame.resolver.typeTag(actual) orelse return null;
        const wrapper = switch (expected_tag) {
            .optional, .error_union => expected,
            else => switch (actual_tag) {
                .optional, .error_union => actual,
                else => return null,
            },
        };
        var value_type = actual;
        if (actual.eql(wrapper)) {
            var buffer: [2]Ast.Node.Index = undefined;
            const arguments = tree.builtinCallParams(&buffer, node) orelse return null;
            const builtin = std.zig.BuiltinFn.list.get(tree.tokenSlice(tree.nodeMainToken(node))) orelse return null;
            if (builtin.tag != .as or arguments.len != 2) return null;
            value_node = arguments[1];
            while (tree.nodeTag(value_node) == .grouped_expression)
                value_node = tree.nodeData(value_node).node_and_token[0];
            // Expected-type resolution can type this literal as the wrapper.
            if (tree.nodeTag(value_node) == .identifier and
                std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(value_node)), "undefined")) return null;
            const value_raw = (try proof.frame.typeOfNode(value_node)) orelse return null;
            value_type = (try proof.frame.resolver.normalizedType(value_raw)) orelse return null;
            // An identity cast does not construct or repair a wrapper tag.
            if (value_type.eql(wrapper)) return null;
        }
        const wrapper_tag = proof.frame.resolver.typeTag(wrapper) orelse return null;
        const payload = proof.frame.resolver.childType(wrapper) orelse return null;
        const child = (try proof.frame.resolver.normalizedType(payload)) orelse return null;
        if (!value_type.eql(child)) return .{ .kind = .unsupported_payload, .value_node = value_node };
        return .{
            .kind = switch (wrapper_tag) {
                .optional => .optional_payload,
                .error_union => .error_payload,
                else => unreachable,
            },
            .value_node = value_node,
        };
    }

    fn literalStoreUndefinedMode(self: *FileCache, proof: *const DefiniteStoreProof, node: Ast.Node.Index, depth: u32, may: bool) SummaryError!bool {
        const literal = try self.literalStoreUndefinedValueMode(proof, node, depth, may);
        if (!literal or may) return literal;
        return try literalStoreBoxing(proof, node) == null;
    }

    fn literalStoreUndefinedValueMode(
        self: *FileCache,
        proof: *const DefiniteStoreProof,
        node: Ast.Node.Index,
        depth: u32,
        may: bool,
    ) SummaryError!bool {
        try self.chargeNormalCleanupAt(proof.tree, node);
        if (depth >= 64) return self.cleanupBudgetFailureAt(proof.tree, .normal_cleanup_depth, 64, node);
        const tree = proof.tree;
        switch (tree.nodeTag(node)) {
            .identifier => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "undefined")) return true;
                const binding = &proof.bindings[proof.findIndex(name) orelse return false];
                return binding.literal_undefined or (may and binding.literal_may_undefined);
            },
            .grouped_expression => return self.literalStoreUndefinedMode(proof, tree.nodeData(node).node_and_token[0], depth + 1, may),
            .bool_not, .negation, .bit_not => return self.literalStoreUndefinedMode(proof, tree.nodeData(node).node, depth + 1, may),
            .@"if" => {
                const branch = tree.fullIf(node) orelse return false;
                if (!try self.literalStorePassive(proof, branch.ast.cond_expr, depth + 1)) return false;
                if (try proof.frame.boolValueOfNode(branch.ast.cond_expr)) |condition| {
                    const selected = if (condition) branch.ast.then_expr else branch.ast.else_expr.unwrap() orelse return false;
                    return self.literalStoreUndefinedMode(proof, selected, depth + 1, may);
                }
                const otherwise = branch.ast.else_expr.unwrap() orelse return false;
                const left = try self.literalStoreUndefinedMode(proof, branch.ast.then_expr, depth + 1, may);
                if (may and left) return true;
                if (!may and !left) return false;
                return self.literalStoreUndefinedMode(proof, otherwise, depth + 1, may);
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                const first = literalStoreBuiltinFirst(tree, node) orelse return false;
                var buffer: [2]Ast.Node.Index = undefined;
                const arguments = tree.builtinCallParams(&buffer, node) orelse return false;
                if (arguments.len <= first) return false;
                for (arguments[first..]) |argument| if (!try self.literalStorePassive(proof, argument, depth + 1)) return false;
                for (arguments[first..]) |argument| if (try self.literalStoreUndefinedMode(proof, argument, depth + 1, may)) return true;
                return false;
            },
            .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor,
            .add_wrap, .sub_wrap, .mul_wrap, .add_sat, .sub_sat, .mul_sat, .shl_sat,
            .equal_equal, .bang_equal, .less_than, .less_or_equal, .greater_than, .greater_or_equal => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                if (!try self.literalStorePassive(proof, lhs, depth + 1) or
                    !try self.literalStorePassive(proof, rhs, depth + 1)) return false;
                return try self.literalStoreUndefinedMode(proof, lhs, depth + 1, may) or
                    try self.literalStoreUndefinedMode(proof, rhs, depth + 1, may);
            },
            else => return false,
        }
    }

    /// Reject runtime calls before consulting saved flags: an earlier effect
    /// could have repaired the very source the passive probe would read.
    fn literalStoreBuiltinFirst(tree: *const Ast, node: Ast.Node.Index) ?usize {
        const builtin = std.zig.BuiltinFn.list.get(tree.tokenSlice(tree.nodeMainToken(node))) orelse return null;
        return switch (builtin.tag) {
            .as => 1,
            .int_cast, .float_cast, .bit_cast, .float_from_int, .int_from_float, .truncate,
            .int_from_bool, .int_from_enum, .enum_from_int, .int_from_ptr, .ptr_from_int,
            .abs, .sqrt, .byte_swap, .bit_reverse, .clz, .ctz, .pop_count,
            .min, .max, .div_exact, .div_floor, .div_trunc, .mod, .rem,
            .floor, .ceil, .trunc, .round, .sin, .cos, .tan, .exp, .exp2, .log, .log2, .log10 => 0,
            else => null,
        };
    }

    fn literalStorePassive(self: *FileCache, proof: *const DefiniteStoreProof, node: Ast.Node.Index, depth: u32) SummaryError!bool {
        try self.chargeNormalCleanupAt(proof.tree, node);
        if (depth >= 64) return self.cleanupBudgetFailureAt(proof.tree, .normal_cleanup_depth, 64, node);
        const tree = proof.tree;
        switch (tree.nodeTag(node)) {
            .identifier, .number_literal, .char_literal, .string_literal, .enum_literal => return true,
            .grouped_expression => return self.literalStorePassive(proof, tree.nodeData(node).node_and_token[0], depth + 1),
            .bool_not, .negation, .bit_not, .deref => return self.literalStorePassive(proof, tree.nodeData(node).node, depth + 1),
            .field_access => return self.literalStorePassive(proof, tree.nodeData(node).node_and_token[0], depth + 1),
            .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor,
            .add_wrap, .sub_wrap, .mul_wrap, .add_sat, .sub_sat, .mul_sat, .shl_sat,
            .equal_equal, .bang_equal, .less_than, .less_or_equal, .greater_than, .greater_or_equal,
            .bool_and, .bool_or, .array_access => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                return try self.literalStorePassive(proof, lhs, depth + 1) and
                    try self.literalStorePassive(proof, rhs, depth + 1);
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                const first = literalStoreBuiltinFirst(tree, node) orelse return false;
                var buffer: [2]Ast.Node.Index = undefined;
                const arguments = tree.builtinCallParams(&buffer, node) orelse return false;
                if (arguments.len <= first) return false;
                for (arguments[first..]) |argument| if (!try self.literalStorePassive(proof, argument, depth + 1)) return false;
                return true;
            },
            else => return false,
        }
    }

    fn definiteStoreValueWithComputed(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        depth: u32,
    ) SummaryError!DefiniteStoreResult {
        const saved = proof.computed_result;
        defer proof.computed_result = saved;
        proof.computed_result = .{};
        const source_before = if (proof.computed_templates != null)
            try self.wholeStoreFieldSource(proof, node, depth)
        else
            null;
        const literal_undefined = proof.computed_templates != null and
            try self.literalStoreUndefined(proof, node, depth);
        const literal_may_undefined = literal_undefined or (proof.computed_templates != null and
            try self.literalStoreMayUndefined(proof, node, depth));
        const raw = try self.definiteStoreValueInner(proof, node, depth);
        const boxing = if (proof.computed_templates != null and
            (literal_may_undefined or proof.computed_result.literal_undefined or proof.computed_result.literal_may_undefined))
            try literalStoreBoxing(proof, node)
        else null;
        if (boxing) |boxed| {
            const returned_payload_all = proof.computed_result.literal_undefined;
            proof.computed_result.literal_undefined = false;
            proof.computed_result.literal_may_undefined = true;
            if (boxed.kind == .optional_payload) {
                const payload_all = returned_payload_all or try self.literalStoreUndefinedValueMode(proof, boxed.value_node, depth, false);
                const payload_may = payload_all or literal_may_undefined or proof.computed_result.literal_may_undefined;
                const writes = [_]ComputedStoreWrite{
                    .{ .path = "", .literal_undefined = payload_all, .literal_may_undefined = payload_may, .opaque_alternative = !payload_all },
                    .{ .path = "$optional-tag" },
                };
                if (proof.computed_templates.?.add(.{ .whole_value = true, .writes = &writes })) |handle| {
                    proof.computed_result = .{ .computations = handle, .value_nonidentity = true, .literal_may_undefined = true };
                } else {
                    proof.computed_result = .{ .opaque_alternative = true, .value_nonidentity = true, .literal_may_undefined = true };
                }
            }
        }
        if (literal_undefined and proof.computed_templates != null and proof.computed_result.computations == 0) {
            var actual = try proof.frame.expectedTypeOfNode(node);
            if (actual == null) actual = try proof.frame.typeOfNode(node);
            if (actual) |ty| if (try proof.frame.resolver.normalizedType(ty)) |normalized| {
                const tag = proof.frame.resolver.typeTag(normalized);
                if (tag == .@"struct" or tag == .array or tag == .optional or tag == .error_union) {
                    const write = [_]ComputedStoreWrite{.{ .path = "", .literal_undefined = true }};
                    const extent = if (tag == .array) definiteStoreArrayTypeCount(proof.frame.resolver, normalized) else null;
                    if (proof.computed_templates.?.add(.{
                        .whole_value = true, .writes = &write,
                        .is_array = tag == .array, .array_extent = extent,
                    })) |handle| {
                        proof.computed_result = .{ .computations = handle, .value_nonidentity = true };
                    } else {
                        const token = proof.tree.nodeMainToken(node);
                        _ = recordComputedFallbackFact(proof, token, "", .{}, true);
                        proof.computed_result.fallback_token = token;
                    }
                }
            };
        }
        if (proof.computed_result.source == null and proof.computed_result.computations == 0 and
            !proof.computed_result.original_alternative and !proof.computed_result.value_nonidentity)
            proof.computed_result.source = source_before;
        if (proof.computed_templates != null and proof.computed_result.source == null and
            proof.computed_result.computations == 0 and !proof.computed_result.original_alternative and
            raw != .defined and !literal_undefined)
            proof.computed_result.opaque_alternative = true;
        return .{
            .value = if (proof.written_inputs != null) .defined else raw,
            .raw_value = raw,
            .literal_undefined = boxing == null and (literal_undefined or proof.computed_result.literal_undefined),
            .literal_may_undefined = literal_may_undefined or proof.computed_result.literal_may_undefined,
            .computed = proof.computed_result,
        };
    }


    fn computedStoreWriteForValue(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        path: []const u8,
        node: Ast.Node.Index,
        evaluated: DefiniteStoreResult,
        dependencies: WrittenDependencies,
        is_array: bool,
        array_extent: ?u64,
        array_index: ?u64,
    ) SummaryError!ComputedStoreWrite {
        _ = self;
        _ = proof;
        _ = node;
        const source = evaluated.computed.source;
        const literal_undefined = source == null and evaluated.literal_undefined;
        return .{
            .path = path,
            .array_index = array_index,
            .dependencies = dependencies,
            .source = source,
            .literal_undefined = literal_undefined,
            .literal_may_undefined = source == null and evaluated.literal_may_undefined,
            .opaque_alternative = source == null and !literal_undefined and
                (evaluated.raw_value != .defined or evaluated.computed.computations != 0 or
                    evaluated.computed.opaque_alternative),
            .is_array = is_array,
            .array_extent = array_extent,
        };
    }
    fn appendComputedComponent(
        proof: *DefiniteStoreProof,
        constructor_token: Ast.TokenIndex,
        writes: *[128]ComputedStoreWrite,
        count: *usize,
        component: ComputedStoreWrite,
        state: ComputedStoreState,
    ) bool {
        const builders = proof.computed_templates orelse return false;
        if (count.* == writes.len) {
            builders.overflow = true;
            return false;
        }
        const parent = count.*;
        writes[parent] = component;
        count.* += 1;
        if (state.fallback_token != null and component.array_index == null) {
            const token = state.fallback_token.?;
            writes[parent].dependencies = .{};
            const fact_count = proof.field_fact_count;
            for (0..fact_count) |index| {
                const fact = proof.field_facts[index];
                if (fact.token != token or !fact.fallback_recipe) continue;
                const path = if (fact.path.len == 0)
                    component.path
                else
                    computedMappedPrefix(proof.out_fields, component.path, fact.path) orelse continue;
                if (!recordComputedFallbackFact(proof, constructor_token, path, fact.written_dependencies, fact.fallback_literal_may)) break;
            }
        }
        if (state.computations == 0) return true;
        if (@popCount(state.computations) != 1 or state.source != null or
            state.original_alternative or state.opaque_alternative)
        {
            builders.overflow = true;
            return false;
        }
        const child_index: usize = @intCast(@ctz(state.computations));
        const child = builders.values[child_index] orelse {
            builders.overflow = true;
            return false;
        };
        if (!child.whole_value or child.writes.len > writes.len - count.*) {
            builders.overflow = true;
            return false;
        }
        writes[parent].dependencies = .{};
        writes[parent].literal_undefined = false;
        writes[parent].literal_may_undefined = false;
        writes[parent].is_array = child.is_array;
        writes[parent].array_extent = child.array_extent;
        if (child.is_array and child.array_extent != null and child.array_extent.? != 0) {
            var entirely_literal = child.writes.len == child.array_extent.?;
            for (child.writes) |write| {
                entirely_literal = entirely_literal and write.parent == null and
                    write.array_index != null and write.literal_undefined;
            }
            if (entirely_literal) {
                writes[parent].literal_undefined = true;
                writes[parent].opaque_alternative = false;
            }
        }
        const offset = count.*;
        for (child.writes, 0..) |write, index| {
            writes[offset + index] = write;
            writes[offset + index].parent = if (write.parent) |relative|
                @intCast(offset + relative)
            else
                @intCast(parent);
        }
        count.* += child.writes.len;
        return true;
    }

    fn setComputedStoreConstructor(
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        writes: []const ComputedStoreWrite,
        is_array: bool,
        array_extent: ?u64,
    ) void {
        const builders = proof.computed_templates orelse return;
        const handle = builders.add(.{
            .whole_value = true,
            .writes = writes,
            .is_array = is_array,
            .array_extent = array_extent,
        }) orelse {
            const token = proof.tree.nodeMainToken(node);
            for (writes, 0..) |write, index| {
                if (write.array_index != null) continue;
                if (write.dependencies.isEmpty() and !write.literal_undefined and !write.literal_may_undefined) continue;
                if (write.parent == null) {
                    if (write.path.len != 0 and !recordComputedFallbackFact(proof, token, write.path, write.dependencies, write.literal_undefined or write.literal_may_undefined)) break;
                    continue;
                }
                // Borrow the authenticated mapped path; do not allocate or
                // taint the entire parent with one flattened child's recipe.
                for (proof.out_fields) |path| {
                    if (!computedWriteMatchesPath(writes, index, path)) continue;
                    if (!recordComputedFallbackFact(proof, token, path, write.dependencies, write.literal_undefined or write.literal_may_undefined)) break;
                }
            }
            proof.computed_result = .{
                .opaque_alternative = true,
                .value_nonidentity = true,
                .fallback_token = token,
            };
            return;
        };
        proof.computed_result = .{
            .computations = handle,
            .value_nonidentity = true,
        };
    }

    fn recordComputedFallbackFact(
        proof: *DefiniteStoreProof,
        token: Ast.TokenIndex,
        path: []const u8,
        dependencies: WrittenDependencies,
        literal_may: bool,
    ) bool {
        for (proof.field_facts[0..proof.field_fact_count]) |*fact| {
            if (fact.token != token or !std.mem.eql(u8, fact.path, path)) continue;
            fact.written_dependencies.merge(dependencies);
            fact.fallback_literal_may = fact.fallback_literal_may or literal_may;
            fact.fallback_recipe = true;
            return true;
        }
        if (proof.field_fact_count == proof.field_facts.len) return false;
        proof.field_facts[proof.field_fact_count] = .{
            .token = token,
            .path = path,
            .value = .unknown,
            .written_dependencies = dependencies,
            .fallback_literal_may = literal_may,
            .fallback_recipe = true,
        };
        proof.field_fact_count += 1;
        return true;
    }

    fn copyComputedFallbackFacts(proof: *DefiniteStoreProof, source: ?Ast.TokenIndex, destination: Ast.TokenIndex) void {
        const token = source orelse return;
        if (token == destination) return;
        const count = proof.field_fact_count;
        for (0..count) |index| {
            const fact = proof.field_facts[index];
            if (fact.token != token) continue;
            if (!recordComputedFallbackFact(proof, destination, fact.path, fact.written_dependencies, fact.fallback_literal_may)) return;
        }
    }

    fn setComputedStoreWholeReplacement(
        proof: *DefiniteStoreProof,
        coverage: *StoreCoverage,
        evaluated: DefiniteStoreResult,
    ) void {
        const builders = proof.computed_templates orelse return;
        if (evaluated.computed.fallback_token) |token| {
            coverage.computed_overflow = true;
            if (proof.may_written_stores) |stores| {
                for (proof.field_facts[0..proof.field_fact_count]) |fact| {
                    if (fact.token != token or !fact.fallback_recipe) continue;
                    for (coverage.field_names[0..coverage.field_count]) |path| {
                        if (fact.path.len != 0 and !std.mem.eql(u8, path, fact.path)) continue;
                        if (!fact.written_dependencies.isEmpty()) _ = stores.add(path, fact.written_dependencies);
                        if (fact.fallback_literal_may) _ = stores.addLiteral(path);
                    }
                }
            }
        }
        var state = evaluated.computed;
        const scalar = if (proof.frame.resolver.typeTag(coverage.pointee)) |tag| switch (tag) {
            .@"struct", .@"union", .array, .vector, .optional, .error_union => false,
            else => true,
        } else false;
        if (scalar and state.source == null and state.computations == 0 and
            !state.original_alternative and !evaluated.literal_undefined and
            !evaluated.literal_may_undefined and !proof.written_dependencies.isEmpty())
        {
            const write = [_]ComputedStoreWrite{.{
                .path = "", .dependencies = proof.written_dependencies,
                .opaque_alternative = state.opaque_alternative,
            }};
            if (builders.add(.{ .whole_value = true, .writes = &write })) |handle| {
                state = .{ .computations = handle, .value_nonidentity = true };
            } else {
                coverage.computed_overflow = true;
            }
        }
        if (state.source == null and state.computations == 0 and
            !state.original_alternative and !state.opaque_alternative)
        {
            if (evaluated.literal_undefined or evaluated.literal_may_undefined) {
                const write = [_]ComputedStoreWrite{.{
                    .path = "",
                    .literal_undefined = evaluated.literal_undefined,
                    .literal_may_undefined = evaluated.literal_may_undefined,
                    .opaque_alternative = !evaluated.literal_undefined,
                }};
                if (builders.add(.{ .whole_value = true, .writes = &write })) |handle| {
                    state = .{ .computations = handle, .value_nonidentity = true };
                } else {
                    state.opaque_alternative = true;
                    state.value_nonidentity = true;
                    coverage.computed_overflow = true;
                    if (proof.may_written_stores) |stores| {
                        for (coverage.field_names[0..coverage.field_count]) |path| _ = stores.addLiteral(path);
                    }
                }
            } else {
                state.opaque_alternative = true;
                state.value_nonidentity = true;
            }
        }
        coverage.whole_source = state.source;
        coverage.computed_sources = state.computations;
        coverage.computed_original_alternative = state.original_alternative;
        coverage.computed_opaque_alternative = state.opaque_alternative;
    }

    fn computedWriteMatchesPath(writes: []const ComputedStoreWrite, index: usize, path: []const u8) bool {
        const write = writes[index];
        if (write.array_index != null) return false;
        if (!std.mem.endsWith(u8, path, write.path)) return false;
        const leading = path.len - write.path.len;
        if (write.parent) |parent| {
            if (parent >= index or leading == 0 or path[leading - 1] != '.') return false;
            return computedWriteMatchesPath(writes, parent, path[0 .. leading - 1]);
        }
        return leading == 0;
    }

    fn computedWriteMatchesLeaf(writes: []const ComputedStoreWrite, index: usize, path: []const u8, leaf: []const u8) bool {
        const write = writes[index];
        if (write.array_index != null or !std.mem.endsWith(u8, path, leaf)) return false;
        const leading = path.len - leaf.len;
        if (write.parent) |parent| {
            if (parent >= index or leading == 0 or path[leading - 1] != '.') return false;
            return computedWriteMatchesPath(writes, parent, path[0 .. leading - 1]);
        }
        return leading == 0;
    }

    fn computedWriteOverlapsField(writes: []const ComputedStoreWrite, index: usize, path: []const u8) bool {
        const effective = if (writes[index].array_index != null)
            writes[index].parent orelse return true
        else
            index;
        if (effective >= writes.len) return true;
        var ancestor = path;
        while (true) {
            if (computedWriteMatchesPath(writes, effective, ancestor)) return true;
            if (ancestor.len == 0) break;
            ancestor = if (std.mem.lastIndexOfScalar(u8, ancestor, '.')) |dot| ancestor[0..dot] else "";
        }
        var descendant = effective;
        while (true) {
            if (computedWriteMatchesPath(writes, descendant, path)) return true;
            var leaf = writes[descendant].path;
            while (std.mem.lastIndexOfScalar(u8, leaf, '.')) |dot| {
                leaf = leaf[0..dot];
                if (computedWriteMatchesLeaf(writes, descendant, path, leaf)) return true;
            }
            const parent = writes[descendant].parent orelse break;
            if (parent >= descendant) return true;
            descendant = parent;
        }
        return false;
    }

    const ComputedFieldRecipe = struct {
        source: WholeStoreSource = .{},
        needs_root: bool = true,
    };

    /// Identity only: dependency bits do not authorize a physical copy.
    /// Memoize each immutable result once for this selected physical path.
    fn computedFieldRecipe(
        builders: *const ComputedStoreBuilders,
        base: ComputedStoreBase,
        path: []const u8,
        memo: *[8]?ComputedFieldRecipe,
    ) ComputedFieldRecipe {
        var result: ?ComputedFieldRecipe = if (base.source != null or base.original_alternative or base.opaque_alternative)
            ComputedFieldRecipe{}
        else
            null;
        var remaining = base.computations;
        while (remaining != 0) {
            const index: usize = @intCast(@ctz(remaining));
            remaining &= remaining - 1;
            var arm = memo[index];
            if (arm == null) {
                if (index < builders.count) if (builders.values[index]) |node| {
                    const relative: ?[]const u8 = if (node.output_prefix) |prefix| blk: {
                        if (std.mem.eql(u8, path, prefix)) break :blk "";
                        if (path.len <= prefix.len or path[prefix.len] != '.' or
                            !std.mem.startsWith(u8, path, prefix)) break :blk null;
                        break :blk path[prefix.len + 1 ..];
                    } else path;
                    if (relative) |selected| {
                        var write_index = node.writes.len;
                        while (write_index != 0) {
                            write_index -= 1;
                            const write = node.writes[write_index];
                            if (!computedWriteOverlapsField(node.writes, write_index, selected)) continue;
                            arm = ComputedFieldRecipe{};
                            if (computedWriteMatchesPath(node.writes, write_index, selected)) {
                                const source = write.source orelse WholeStoreSource{};
                                arm.?.source = source;
                                arm.?.source.opaque_alternative = source.opaque_alternative or write.opaque_alternative or
                                    write.literal_undefined or write.literal_may_undefined;
                                arm.?.needs_root = write.literal_undefined or write.literal_may_undefined or write.opaque_alternative or
                                    (write.source != null and source.sources == 0 and source.projections == 0);
                            }
                            break;
                        }
                    }
                    if (arm == null and !node.whole_value) arm = computedFieldRecipe(builders, .{
                        .source = node.base_source,
                        .computations = node.base_computations,
                        .original_alternative = node.base_original_alternative,
                        .opaque_alternative = node.base_opaque_alternative,
                    }, path, memo);
                };
                if (arm == null) arm = ComputedFieldRecipe{};
                memo[index] = arm;
            }
            result = if (result) |prior| .{
                .source = WholeStoreSource.merge(prior.source, arm.?.source),
                .needs_root = prior.needs_root or arm.?.needs_root,
            } else arm.?;
        }
        return result orelse ComputedFieldRecipe{};
    }

    fn computedFieldDependencies(
        builders: *const ComputedStoreBuilders,
        handles: u8,
        path: []const u8,
    ) WrittenDependencies {
        var result: WrittenDependencies = .{};
        var remaining = handles;
        while (remaining != 0) {
            const index: usize = @intCast(@ctz(remaining));
            remaining &= remaining - 1;
            if (index >= builders.count) continue;
            const node = builders.values[index] orelse continue;
            var arm = computedFieldDependencies(builders, node.base_computations, path);
            const relative = if (node.output_prefix) |prefix| blk: {
                if (path.len <= prefix.len or path[prefix.len] != '.' or
                    !std.mem.startsWith(u8, path, prefix)) break :blk null;
                break :blk path[prefix.len + 1 ..];
            } else path;
            if (relative) |selected| {
                for (node.writes, 0..) |write, write_index| {
                    if (computedWriteMatchesPath(node.writes, write_index, selected)) arm = write.dependencies;
                }
            }
            result.merge(arm);
        }
        return result;
    }

    fn computedFieldLiteralMay(
        builders: *const ComputedStoreBuilders,
        handles: u8,
        path: []const u8,
    ) bool {
        var result = false;
        var remaining = handles;
        while (remaining != 0) {
            const index: usize = @intCast(@ctz(remaining));
            remaining &= remaining - 1;
            if (index >= builders.count) continue;
            const node = builders.values[index] orelse continue;
            var arm = computedFieldLiteralMay(builders, node.base_computations, path);
            const relative: ?[]const u8 = if (node.output_prefix) |prefix| blk: {
                if (path.len <= prefix.len or path[prefix.len] != '.' or
                    !std.mem.startsWith(u8, path, prefix)) break :blk null;
                break :blk path[prefix.len + 1 ..];
            } else path;
            if (relative) |selected| {
                for (node.writes, 0..) |write, write_index| {
                    const whole = write.parent == null and write.array_index == null and write.path.len == 0;
                    if (!whole and !computedWriteMatchesPath(node.writes, write_index, selected)) continue;
                    if (write.literal_undefined or write.literal_may_undefined) {
                        arm = true;
                    } else if (!write.opaque_alternative and write.source == null and write.dependencies.isEmpty()) {
                        arm = false;
                    }
                }
            }
            result = result or arm;
        }
        return result;
    }

    fn appendComputedFieldStoreWrite(
        proof: *DefiniteStoreProof,
        base: ComputedStoreBase,
        write: ComputedStoreWrite,
        state: ComputedStoreState,
        fields: []const []const u8,
    ) ?ComputedStoreBase {
        const builders = proof.computed_templates orelse return null;
        if (state.computations == 0) return .{
            .computations = appendComputedStoreWrite(proof, base, write) orelse return null,
        };
        var memo: [8]?u8 = @splat(null);
        return rebaseComputedStoreBase(proof, .{
            .source = state.source,
            .computations = state.computations,
            .original_alternative = state.original_alternative,
            .opaque_alternative = state.opaque_alternative,
        }, base, write.path, fields, builders.count, &memo);
    }

    fn appendComputedStoreWrite(
        proof: *DefiniteStoreProof,
        base: ComputedStoreBase,
        write: ComputedStoreWrite,
    ) ?u8 {
        const builders = proof.computed_templates orelse return null;
        const writes = [_]ComputedStoreWrite{write};
        return builders.add(.{
            .whole_value = false,
            .base_source = base.source,
            .base_computations = base.computations,
            .base_original_alternative = base.original_alternative,
            .base_opaque_alternative = base.opaque_alternative,
            .writes = &writes,
        });
    }

    fn computedCoverageBase(coverage: *const StoreCoverage) ComputedStoreBase {
        return .{
            .source = coverage.whole_source,
            .computations = coverage.computed_sources,
            .original_alternative = coverage.computed_original_alternative,
            .opaque_alternative = coverage.computed_opaque_alternative,
        };
    }

    fn computedMappedPrefix(fields: []const []const u8, prefix: []const u8, suffix: []const u8) ?[]const u8 {
        for (fields) |candidate| {
            if (candidate.len == prefix.len + 1 + suffix.len and
                std.mem.startsWith(u8, candidate, prefix) and candidate[prefix.len] == '.' and
                std.mem.eql(u8, candidate[prefix.len + 1 ..], suffix)) return candidate;
        }
        return null;
    }

    fn rebaseComputedStoreBase(
        proof: *DefiniteStoreProof,
        selected: ComputedStoreBase,
        parent_base: ComputedStoreBase,
        prefix: []const u8,
        fields: []const []const u8,
        original_count: usize,
        memo: *[8]?u8,
    ) ?ComputedStoreBase {
        const builders = proof.computed_templates orelse return null;
        var result: ComputedStoreBase = .{};
        if (selected.original_alternative) result = parent_base;
        if (selected.source != null or selected.opaque_alternative) {
            const write: ComputedStoreWrite = .{
                .path = prefix,
                .source = selected.source,
                .opaque_alternative = selected.opaque_alternative,
            };
            result.computations |= appendComputedStoreWrite(proof, parent_base, write) orelse return null;
        }
        var handles = selected.computations;
        while (handles != 0) {
            const index: usize = @intCast(@ctz(handles));
            handles &= handles - 1;
            if (index >= original_count) return null;
            if (memo[index]) |rebased| {
                result.computations |= rebased;
                continue;
            }
            const node = builders.values[index] orelse return null;
            const mapped_prefix = if (node.output_prefix) |suffix|
                computedMappedPrefix(fields, prefix, suffix) orelse return null
            else
                prefix;
            var writes: [128]ComputedStoreWrite = undefined;
            var write_count: usize = 0;
            var base = parent_base;
            if (node.whole_value) {
                if (node.writes.len >= writes.len) return null;
                writes[0] = .{ .path = mapped_prefix, .opaque_alternative = true, .is_array = node.is_array, .array_extent = node.array_extent };
                write_count = 1;
                for (node.writes, 0..) |write, offset| {
                    writes[write_count + offset] = write;
                    writes[write_count + offset].parent = if (write.parent) |relative| relative + 1 else 0;
                }
                write_count += node.writes.len;
            } else {
                const node_base: ComputedStoreBase = .{
                    .source = node.base_source,
                    .computations = node.base_computations,
                    .original_alternative = node.base_original_alternative,
                    .opaque_alternative = node.base_opaque_alternative,
                };
                base = rebaseComputedStoreBase(proof, node_base, parent_base, prefix, fields, original_count, memo) orelse return null;
                write_count = 0;
            }
            const rebased = builders.add(.{
                .whole_value = false,
                .base_source = base.source,
                .base_computations = base.computations,
                .base_original_alternative = base.original_alternative,
                .base_opaque_alternative = base.opaque_alternative,
                .writes = if (node.whole_value) writes[0..write_count] else node.writes,
                .output_prefix = if (node.whole_value) null else mapped_prefix,
            }) orelse return null;
            memo[index] = rebased;
            result.computations |= rebased;
        }
        if (builders.alternativeCount(result) == null) return null;
        return result;
    }

    fn definiteStoreValueInner(
        self: *FileCache,
        proof: *DefiniteStoreProof,
        node: Ast.Node.Index,
        depth: u32,
    ) SummaryError!DefiniteStoreValue {
        try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
        if (depth == 64) return self.cleanupBudgetFailureAt(proof.call_tree, .normal_cleanup_depth, 64, proof.call_node);
        const tree = proof.tree;
        switch (tree.nodeTag(node)) {
            .number_literal, .string_literal, .char_literal, .enum_literal => return .defined,
            .identifier => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "undefined")) return .undefined_value;
                if (std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false") or std.mem.eql(u8, name, "null")) return .defined;
                if ((try proof.frame.resolveValueOfNode(node))) |value| {
                    if (value.is_type_val) return .defined;
                    if (value.ipIndex()) |index| {
                        switch (proof.frame.resolver.ctx.ip.indexToKey(index)) {
                            .int_u64_value, .int_i64_value, .int_big_value => return .defined,
                            else => {},
                        }
                    }
                }
                if (proof.overflowTupleBinding(node)) |binding| {
                    if (proof.collect_written_inputs)
                        proof.written_dependencies.merge(proof.bindings[binding].written_dependencies);
                    return proof.bindings[binding].value;
                }
                const kind = try definiteStoreKind(proof, node);
                if (kind == .unresolved) return .undefined_value;
                if (proof.findIndex(name)) |binding| {
                    if (proof.collect_written_inputs)
                        proof.written_dependencies.merge(proof.bindings[binding].written_dependencies);
                    const ty = (try proof.frame.typeOfNode(node)) orelse return .undefined_value;
                    const normalized = (try proof.frame.resolver.normalizedType(ty)) orelse return .undefined_value;
                    const is_aggregate = kind == .aggregate or
                        proof.frame.resolver.typeTag(normalized) == .optional or
                        proof.frame.resolver.typeTag(normalized) == .error_union or
                        proof.frame.resolver.typeTag(normalized) == .array or
                        proof.frame.resolver.typeTag(normalized) == .vector or
                        proof.frame.resolver.pointerSize(normalized) == .slice;
                    if (is_aggregate and proof.computed_templates != null) {
                        const bound = proof.bindings[binding];
                        var computed: ComputedStoreState = .{
                            .source = bound.aggregate_source,
                            .computations = bound.computed_sources,
                            .original_alternative = bound.computed_original_alternative,
                            .opaque_alternative = bound.computed_opaque_alternative,
                            .value_nonidentity = bound.value_nonidentity,
                        };
                        if (computed.source == null and computed.computations == 0 and
                            !computed.original_alternative and !computed.opaque_alternative)
                        {
                            if (binding < proof.parameter_count) {
                                computed.source = try self.wholeStoreSource(proof, node, depth);
                                computed.opaque_alternative = computed.source == null;
                            } else {
                                computed.opaque_alternative = true;
                            }
                        }
                        proof.computed_result = computed;
                        for (proof.field_facts[0..proof.field_fact_count]) |fact| {
                            if (fact.token == bound.token and fact.fallback_recipe) {
                                proof.computed_result.fallback_token = bound.token;
                                break;
                            }
                        }
                    }
                    if (kind == .scalar or binding < proof.parameter_count or proof.bindings[binding].complete_value or
                        proof.frame.resolver.typeTag(normalized) == .array or
                        proof.frame.resolver.typeTag(normalized) == .vector or
                        proof.frame.resolver.pointerSize(normalized) == .slice) return proof.bindings[binding].value;
                    return .undefined_value;
                }
                const canonical = proof.canonical orelse return .undefined_value;
                var proto_buffer: [1]Ast.Node.Index = undefined;
                const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return .undefined_value;
                var parameters = proto.iterate(tree);
                var index: u32 = 0;
                while (parameters.next()) |parameter| : (index += 1) {
                    const formal_name = parameter.name_token orelse continue;
                    if (!std.mem.eql(u8, name, tree.tokenSlice(formal_name))) continue;
                    var argument_buffer: [2]Ast.Node.Index = undefined;
                    const caller_cache = proof.caller_cache orelse self;
                    const argument = (try canonical.callArgumentFor(caller_cache, &argument_buffer, index)) orelse return .undefined_value;
                    if (proof.written_input_boundary and proof.written_reads != null and proof.read_projection != null) {
                        return if (try proof.recordWrittenRead(argument)) .defined else .unknown;
                    }
                    if (proof.written_input_boundary) if (proof.written_inputs) |inputs| {
                        if (!proof.collect_written_inputs) return .defined;
                        for (inputs, 0..) |*entry, slot| {
                            if (entry.* != null and entry.* != argument) continue;
                            entry.* = argument;
                            proof.written_dependencies.inputs |= @as(u8, 1) << @intCast(slot);
                            return .defined;
                        }
                        if (proof.written_dependencies_complete) |complete| complete.* = false;
                        return .undefined_value;
                    };
                    const caller_slot = proof.caller.?;
                    if (caller_slot.* == null) {
                        var caller = (try caller_cache.definiteStoreCaller(proof.call_node, canonical.callee.caller_frame)) orelse return .undefined_value;
                        // An ignored argument can still mutate a dependency
                        // during evaluation. Do not certify that call.
                        var actual_parameters = proto.iterate(tree);
                        var actual_index: u32 = 0;
                        while (actual_parameters.next() != null) : (actual_index += 1) {
                            const actual = (try canonical.callArgumentFor(caller_cache, &argument_buffer, actual_index)) orelse return .undefined_value;
                            if (try caller_cache.definiteStoreValue(&caller, actual, depth + 1) == .unknown) return .unknown;
                        }
                        caller_slot.* = caller;
                    }
                    return self.definiteCallerStoreValue(proof, caller_cache, &caller_slot.*.?, argument, depth + 1);
                }
                return .undefined_value;
            },
            .grouped_expression => return self.definiteStoreValue(proof, tree.nodeData(node).node_and_token[0], depth + 1),
            .negation, .bit_not, .bool_not => return self.definiteStoreValue(proof, tree.nodeData(node).node, depth + 1),
            .@"try" => {
                const call = storeCall(tree, node) orelse return .unknown;
                return self.definiteStoreCallValue(proof, call, depth + 1, true);
            },
            .@"catch" => {
                const call = storeCall(tree, node) orelse return .unknown;
                return self.definiteStoreCallValue(proof, call, depth + 1, true);
            },
            .deref => {
                const saved = proof.read_projection;
                if (saved == null) proof.read_projection = node;
                defer proof.read_projection = saved;
                return self.definiteStoreDeref(proof, tree.nodeData(node).node, depth + 1);
            },
            .call, .call_one, .call_comma, .call_one_comma => return self.definiteStoreCallValue(proof, node, depth + 1, false),
            .if_simple, .@"if" => {
                const branch = tree.fullIf(node) orelse return .unknown;
                if (branch.payload_token != null) return .unknown;
                // A pure selector does not initialize either alternative.
                // Certify the result only when both alternatives are defined;
                // diagnostics for an undefined selector remain independent.
                if (try self.definiteStoreValue(proof, branch.ast.cond_expr, depth + 1) == .unknown) return .unknown;
                const other = branch.ast.else_expr.unwrap() orelse return .unknown;
                const original_count = proof.binding_count;
                const output = proof.out_coverage;
                var left_coverage: ?StoreCoverage = if (output) |coverage| coverage.* else null;
                var right_coverage = left_coverage;
                var left_proof = proof.*;
                var right_proof = proof.*;
                left_proof.out_coverage = if (left_coverage) |*coverage| coverage else null;
                right_proof.out_coverage = if (right_coverage) |*coverage| coverage else null;
                const left_result = try self.definiteStoreValueWithComputed(&left_proof, branch.ast.then_expr, depth + 1);
                const right_result = try self.definiteStoreValueWithComputed(&right_proof, other, depth + 1);
                const left = left_result.value;
                const right = right_result.value;
                if (!mergeStoreProof(&left_proof, &right_proof, original_count)) return .unknown;
                proof.* = left_proof;
                proof.out_coverage = output;
                var left_computed = left_result.computed;
                var right_computed = right_result.computed;
                left_computed.literal_undefined = left_result.literal_undefined;
                right_computed.literal_undefined = right_result.literal_undefined;
                left_computed.literal_may_undefined = left_result.literal_may_undefined;
                right_computed.literal_may_undefined = right_result.literal_may_undefined;
                if (proof.computed_templates != null and try definiteStoreKind(proof, node) == .aggregate) {
                    if (left_result.literal_undefined and left_computed.computations == 0) {
                        const write = [_]ComputedStoreWrite{.{ .path = "", .literal_undefined = true }};
                        left_computed.computations = proof.computed_templates.?.add(.{ .whole_value = true, .writes = &write }) orelse 0;
                    }
                    if (right_result.literal_undefined and right_computed.computations == 0) {
                        const write = [_]ComputedStoreWrite{.{ .path = "", .literal_undefined = true }};
                        right_computed.computations = proof.computed_templates.?.add(.{ .whole_value = true, .writes = &write }) orelse 0;
                    }
                }
                proof.computed_result = left_computed;
                proof.computed_result.merge(right_computed);
                if (left_computed.fallback_token != null or right_computed.fallback_token != null) {
                    const token = tree.nodeMainToken(node);
                    copyComputedFallbackFacts(proof, left_computed.fallback_token, token);
                    copyComputedFallbackFacts(proof, right_computed.fallback_token, token);
                    proof.computed_result.fallback_token = token;
                }
                if (output) |coverage| {
                    coverage.* = left_coverage.?;
                    intersectStoreCoverage(coverage, right_coverage.?);
                }
                if (left == .unknown or right == .unknown) return .unknown;
                return if (left == .defined and right == .defined) .defined else .undefined_value;
            },
            .array_access, .array_mult => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                if (tree.nodeTag(node) == .array_access and proof.overflowTupleBinding(lhs) != null and
                    try definiteStoreKind(proof, node) != .scalar) return .unknown;
                const left = blk: {
                    const saved = proof.read_projection;
                    if (saved == null) proof.read_projection = node;
                    defer proof.read_projection = saved;
                    break :blk try self.definiteStoreProjectionBase(proof, lhs, depth + 1);
                };
                const right = try self.definiteStoreValue(proof, rhs, depth + 1);
                if (left == .unknown or right == .unknown) return .unknown;
                return if (left == .defined and right == .defined) .defined else .undefined_value;
            },
            .slice, .slice_open, .slice_sentinel => {
                const slice = tree.fullSlice(node) orelse return .unknown;
                var base = try self.definiteStoreValue(proof, slice.ast.sliced, depth + 1);
                if (base == .undefined_value) {
                    const actual = (try proof.frame.typeOfNode(slice.ast.sliced)) orelse return .unknown;
                    // Taking a slice of array storage constructs a descriptor;
                    // it does not read or initialize the array's contents.
                    if (proof.frame.resolver.typeTag(actual) == .array) base = .defined;
                }
                const start = try self.definiteStoreValue(proof, slice.ast.start, depth + 1);
                if (base == .unknown or start == .unknown) return .unknown;
                var verdict: DefiniteStoreValue = if (base == .defined and start == .defined) .defined else .undefined_value;
                if (slice.ast.end.unwrap()) |end| {
                    const value = try self.definiteStoreValue(proof, end, depth + 1);
                    if (value == .unknown) return .unknown;
                    if (value != .defined) verdict = .undefined_value;
                }
                if (slice.ast.sentinel.unwrap()) |sentinel| {
                    const value = try self.definiteStoreValue(proof, sentinel, depth + 1);
                    if (value == .unknown) return .unknown;
                    if (value != .defined) verdict = .undefined_value;
                }
                return verdict;
            },
            .address_of => {
                var operand = tree.nodeData(node).node;
                while (tree.nodeTag(operand) == .field_access) {
                    try self.chargeNormalCleanupAt(proof.call_tree, proof.call_node);
                    operand = tree.nodeData(operand).node_and_token[0];
                }
                if (tree.nodeTag(operand) != .identifier) return .unknown;
                return .undefined_value;
            },
            .add,
            .sub,
            .mul,
            .div,
            .mod,
            .shl,
            .shr,
            .bit_and,
            .bit_or,
            .bit_xor,
            .add_wrap,
            .sub_wrap,
            .mul_wrap,
            .add_sat,
            .sub_sat,
            .mul_sat,
            .shl_sat,
            .equal_equal,
            .bang_equal,
            .less_than,
            .less_or_equal,
            .greater_than,
            .greater_or_equal,
            => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                const left = try self.definiteStoreValue(proof, lhs, depth + 1);
                const right = try self.definiteStoreValue(proof, rhs, depth + 1);
                if (left == .unknown or right == .unknown) return .unknown;
                return if (left == .defined and right == .defined) .defined else .undefined_value;
            },
            .bool_and, .bool_or => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                const left = try self.definiteStoreValue(proof, lhs, depth + 1);
                if (left == .unknown) return .unknown;
                const literal: ?bool = if (tree.nodeTag(lhs) == .identifier) blk: {
                    const name = tree.tokenSlice(tree.nodeMainToken(lhs));
                    break :blk if (std.mem.eql(u8, name, "true")) true else if (std.mem.eql(u8, name, "false")) false else null;
                } else null;
                if (literal) |value| {
                    const skipped = if (tree.nodeTag(node) == .bool_and) !value else value;
                    if (skipped) return left;
                    return self.definiteStoreValue(proof, rhs, depth + 1);
                }
                // The RHS can be skipped. Intersect its effects with that path.
                const count = proof.binding_count;
                const output = proof.out_coverage;
                var taken_coverage: ?StoreCoverage = if (output) |coverage| coverage.* else null;
                var taken = proof.*;
                taken.out_coverage = if (taken_coverage) |*coverage| coverage else null;
                const right = try self.definiteStoreValue(&taken, rhs, depth + 1);
                if (!mergeStoreProof(proof, &taken, count)) return .unknown;
                if (output) |coverage| intersectStoreCoverage(coverage, taken_coverage.?);
                if (right == .unknown) return .unknown;
                return if (left == .defined and right == .defined) .defined else .undefined_value;
            },
            .field_access => {
                if (try self.definiteStoreNamespaceValue(proof, node, depth)) |value| return value;
                if ((try definiteStoreKind(proof, node)) == .unresolved) return .unknown;
                const root = tokens.rootIdentifier(tree, node) orelse return .unknown;
                const name = tree.tokenSlice(tree.nodeMainToken(root));
                if (proof.out_name) |output| {
                    if (std.mem.eql(u8, proof.formalName(name), output) and
                        (proof.findIndex(name) == null or proof.bindings[proof.findIndex(name).?].formal_alias != null))
                    {
                        if (try storeFieldIndex(proof, output, proof.out_fields, node)) |index| {
                            const coverage = proof.out_coverage orelse return .undefined_value;
                            if (proof.collect_written_inputs) {
                                if (coverage.covered[index]) {
                                    proof.written_dependencies.merge(coverage.written_dependencies[index]);
                                } else if (proof.written_reads != null) {
                                    const saved = proof.read_projection;
                                    if (saved == null) proof.read_projection = node;
                                    defer proof.read_projection = saved;
                                    _ = try self.definiteStoreValueInner(proof, root, depth + 1);
                                }
                            }
                            return if (coverage.covered[index]) .defined else .undefined_value;
                        }
                    }
                }
                for (proof.field_facts[0..proof.field_fact_count]) |fact| {
                    const one = [1][]const u8{fact.path};
                    if (try storeFieldIndex(proof, name, &one, node) != null) {
                        if (proof.findStoreFieldFact(name, fact.path)) |stored| {
                            if (proof.collect_written_inputs)
                                proof.written_dependencies.merge(stored.written_dependencies);
                            return stored.value;
                        }
                    }
                }
                const saved = proof.read_projection;
                if (saved == null) proof.read_projection = node;
                defer proof.read_projection = saved;
                const base, const selector = tree.nodeData(node).node_and_token;
                const base_type = (try proof.frame.typeOfNode(base)) orelse return .unknown;
                const actual = (try proof.frame.resolver.normalizedType(base_type)) orelse return .unknown;
                const size = proof.frame.resolver.pointerSize(actual);
                if (size == .slice and (std.mem.eql(u8, tree.tokenSlice(selector), "len") or
                    std.mem.eql(u8, tree.tokenSlice(selector), "ptr")))
                    return self.definiteStoreValue(proof, base, depth + 1);
                return self.definiteStoreProjectionBase(proof, base, depth + 1);
            },
            .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma, .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma, .array_init, .array_init_comma, .array_init_one, .array_init_one_comma, .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma => {
                return self.definiteStoreAggregateValue(proof, node, depth);
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                const builtin = std.zig.BuiltinFn.list.get(tree.tokenSlice(tree.nodeMainToken(node))) orelse return .unknown;
                if (builtin.tag == .add_with_overflow or builtin.tag == .sub_with_overflow or
                    builtin.tag == .mul_with_overflow)
                {
                    var overflow_buffer: [2]Ast.Node.Index = undefined;
                    const arguments = tree.builtinCallParams(&overflow_buffer, node) orelse return .unknown;
                    if (arguments.len != 2) return .unknown;
                    const left = try self.definiteStoreValue(proof, arguments[0], depth + 1);
                    const right = try self.definiteStoreValue(proof, arguments[1], depth + 1);
                    if (left == .unknown or right == .unknown) return .unknown;
                    return if (left == .defined and right == .defined) .defined else .undefined_value;
                }
                const first: usize = switch (builtin.tag) {
                    .splat, .int_cast, .float_cast, .bit_cast, .float_from_int, .int_from_float, .abs, .sqrt, .byte_swap, .bit_reverse, .clz, .ctz, .pop_count, .truncate, .int_from_bool, .int_from_enum, .enum_from_int, .min, .max, .div_exact, .div_floor, .div_trunc, .mod, .rem, .floor, .ceil, .trunc, .round, .sin, .cos, .tan, .exp, .exp2, .log, .log2, .log10 => 0,
                    .as, .mul_add => 1,
                    else => return .unknown,
                };
                var buffer: [2]Ast.Node.Index = undefined;
                const arguments = tree.builtinCallParams(&buffer, node) orelse return .unknown;
                if (arguments.len <= first) return .unknown;
                var verdict: DefiniteStoreValue = .defined;
                for (arguments[first..]) |argument| {
                    const value = try self.definiteStoreValue(proof, argument, depth + 1);
                    if (value == .unknown) return .unknown;
                    if (value != .defined) verdict = .undefined_value;
                }
                return verdict;
            },
            else => return .unknown,
        }
    }

    /// Nesting depth of the whole-file address-use walk.  Bounded
    /// because the walk keeps one frame per AST level; named so the
    /// check and the reported diagnostic cannot drift apart.
    const max_address_use_frames = 256;

    /// `identifier` or `identifier.field.field…`: the named place an instance
    /// call implicitly takes the address of. Anything computed has no
    /// root name, so no storage this file can say anything about.
    fn receiverRoot(tree: *const Ast, node: Ast.Node.Index) ?Ast.Node.Index {
        var current = node;
        while (true) switch (tree.nodeTag(current)) {
            .identifier => return current,
            .field_access => current = tree.nodeData(current).node_and_token[0],
            else => return null,
        };
    }

    /// The `&` operand of an `address_of` node and whether it sits in
    /// an argument position.  BUILT INSTEAD OF COMPUTED PER QUERY: a
    /// body walk asks about every identifier token it passes, and
    /// answering each one by descending the whole file again would be
    /// quadratic in the file's size.
    ///
    /// File every instance-call receiver as a candidate address use. Its
    /// initializer can return an incomplete aggregate without spelling
    /// `undefined` in this function. The demand query proves actual stores.
    fn buildAddressUses(self: *FileCache) error{ OutOfMemory, AnalysisBudgetExceeded }!AddressUseMap {
        const Iterator = engine.AstIterator;
        const Frame = struct {
            children: Iterator,
            in_argument: bool,
            call_children: bool,
            first_child: bool = true,
            call_node: ?Ast.Node.Index = null,
            function: ?Ast.Node.Index = null,
        };
        var result: AddressUseMap = .empty;
        errdefer result.deinit(self.gpa);
        // The node budget for this walk is the whole-file AST node
        // count, and both numbers the node diagnostic reports — the
        // bound in force and the value the counter reached — are that
        // count in the `u32` the diagnostic schema uses.  Convert it
        // once, here where the walk starts, so both come from a
        // checked ceiling instead of two unchecked narrowings: a tree
        // with more than `maxInt(u32)` nodes cannot be described by
        // that schema at all — it needs more source than the `u32`
        // byte offsets `std.zig.Ast` addresses a file with — so the
        // count saturates at `maxInt(u32)` and the walk gives up
        // naming that ceiling as both bound and reached value.
        const node_budget = std.math.cast(u32, self.tree.nodes.len) orelse
            return budget_mod.fail(.{
                .limit = .address_use_nodes,
                .limit_value = std.math.maxInt(u32),
                .reached = std.math.maxInt(u32),
                .document = budget_mod.documentForTree(self.tree),
            });
        var frames: [FileCache.max_address_use_frames]Frame = undefined;
        // A `.root` node's children live in its `extra_range`; the plain
        // `node` payload other nodes carry is not present on `.root`.
        frames[0] = .{
            .children = .{ .sub_range = .{
                .items = self.tree.nodeData(.root).extra_range,
            } },
            .in_argument = false,
            .call_children = false,
        };
        var depth: usize = 1;
        var visited: usize = 0;
        while (depth != 0) {
            const frame = &frames[depth - 1];
            const node = frame.children.next(self.tree) orelse {
                depth -= 1;
                continue;
            };
            if (visited == self.tree.nodes.len) {
                // The counter has caught the budget exactly, so the
                // observed count and the limit in force are one
                // number, already checked above.
                return self.addressUseFailure(.address_use_nodes, node_budget, node_budget, node);
            }
            visited += 1;
            // An argument is a CHILD of its call, but the FIRST child
            // of a call node is the callee.  So a node is in argument
            // position when its parent was already in one, or when its
            // parent is a call and this is not that call's first child.
            const in_argument = frame.in_argument or (frame.call_children and !frame.first_child);
            frame.first_child = false;
            const tag = self.tree.nodeTag(node);
            if (tag == .address_of) {
                if (tokens.rootIdentifier(self.tree, self.tree.nodeData(node).node)) |operand| {
                    try result.put(self.gpa, self.tree.nodeMainToken(operand), .{
                        .operand = self.tree.nodeData(node).node,
                        .may_write = in_argument,
                        .address_node = node,
                        .call_node = frame.call_node,
                    });
                }
            }
            if (frame.function != null) {
                var call_buffer: [1]Ast.Node.Index = undefined;
                if (self.tree.fullCall(&call_buffer, node)) |call| {
                    if (self.tree.nodeTag(call.ast.fn_expr) == .field_access) {
                        const receiver = self.tree.nodeData(call.ast.fn_expr).node_and_token[0];
                        if (receiverRoot(self.tree, receiver)) |root| {
                            const slot = try result.getOrPut(self.gpa, self.tree.nodeMainToken(root));
                            if (!slot.found_existing) slot.value_ptr.* = .{
                                .operand = receiver,
                                .may_write = true,
                                .address_node = receiver,
                                .call_node = node,
                                .receiver = true,
                            };
                        }
                    }
                }
            }
            if (depth == frames.len) {
                return self.addressUseFailure(.address_use_depth, @intCast(frames.len), @intCast(depth), node);
            }
            frames[depth] = .{
                .children = Iterator.init(self.tree, node),
                // A nested `fn` body is a separate world: what the
                // enclosing call does with an argument says nothing
                // about a name the nested body merely closes over.
                .in_argument = tag != .fn_decl and (in_argument or self.builtinWritesMemory(node)),
                .call_children = switch (tag) {
                    .call, .call_one, .call_comma, .call_one_comma => true,
                    else => false,
                },
                .call_node = switch (tag) {
                    .call, .call_one, .call_comma, .call_one_comma => node,
                    .fn_decl => null,
                    else => frame.call_node,
                },
                .function = switch (tag) {
                    .fn_decl, .test_decl => node,
                    else => frame.function,
                },
            };
            depth += 1;
        }
        return result;
    }

    /// Describe an address-use walk that ran out of budget.  Anchors on
    /// the node the walk was about to descend into, and names the
    /// enclosing function when the node sits inside one.  Line/column
    /// come from a direct scan rather than `getLineOffsets` so reporting
    /// a failure can never itself fail to allocate.
    fn addressUseFailure(
        self: *FileCache,
        limit: budget_mod.Limit,
        limit_value: u32,
        reached: u32,
        node: Ast.Node.Index,
    ) budget_mod.BudgetError {
        const token = self.tree.nodeMainToken(node);
        const byte = self.tree.tokens.items(.start)[token];
        const line_col = budget_mod.lineCol(self.tree.source, byte);
        var name: budget_mod.NameBuf = .{};
        if (self.enclosingFunctionAt(self.tree, token)) |decl| {
            var buffer: [1]Ast.Node.Index = undefined;
            if (tokens.fnProto(self.tree, &buffer, decl)) |proto| {
                if (proto.name_token) |name_tok| name.set(self.tree.tokenSlice(name_tok));
            }
        }
        return budget_mod.fail(.{
            .limit = limit,
            .limit_value = limit_value,
            .reached = reached,
            .byte = byte,
            .document = budget_mod.documentForTree(self.tree),
            .line = line_col.line,
            .column = line_col.column,
            .function = name,
        });
    }

    /// True for the builtins whose ARGUMENTS are themselves write
    /// positions — every child of one of these is an operand it stores
    /// through, where a call node's first child is its callee and the
    /// rest are its arguments.
    fn builtinWritesMemory(self: *const FileCache, node: Ast.Node.Index) bool {
        switch (self.tree.nodeTag(node)) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => return false,
        }
        const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
        for ([_][]const u8{ "@memcpy", "@memset", "@atomicStore", "@atomicRmw", "@cmpxchgStrong", "@cmpxchgWeak" }) |writer| {
            if (std.mem.eql(u8, name, writer)) return true;
        }
        return false;
    }

    /// Is `token` evaluated at RUNTIME inside `declaration`?
    ///
    /// A subscript, cast or arithmetic node that exists only in a
    /// COMPTIME position cannot produce a runtime finding: the compiler
    /// has already evaluated it, and nothing the program does later
    /// reaches it.  Three shapes put a position in that world, and all
    /// three are syntax — the type engine says nothing about them:
    ///
    ///   - inside a `comptime { … }` block (or `comptime label: { … }`),
    ///     every statement of which is evaluated at comptime;
    ///   - inside a function all of whose parameters are `comptime`, so
    ///     the whole body is evaluated at comptime;
    ///   - inside a type-introspection builtin's parentheses
    ///     (`@sizeOf`, `@TypeOf`, `@offsetOf`, …), whose argument is a
    ///     type and never read at runtime.
    ///
    /// A token in none of them IS runtime: an ordinary statement, even
    /// one whose value the compiler could fold, is written to run.
    pub fn isRuntimeUse(
        self: *FileCache,
        declaration: Ast.Node.Index,
        token: Ast.TokenIndex,
    ) !bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var buf: [1]Ast.Node.Index = undefined;
        if (tokens.fnProto(tree, &buf, declaration)) |proto| {
            // A function whose every parameter is `comptime` is only
            // callable at comptime; its body is evaluated by the
            // compiler, not by the program.
            if (proto.ast.params.len != 0) {
                var all_comptime = true;
                var it = proto.iterate(tree);
                while (it.next()) |param| {
                    const cn = param.comptime_noalias orelse {
                        all_comptime = false;
                        break;
                    };
                    if (tags[cn] != .keyword_comptime) {
                        all_comptime = false;
                        break;
                    }
                }
                if (all_comptime) return false;
            }
        }
        if ((try comptimeBlockEnclosing(tree, token)) != null) return false;
        if (comptimeOnlyBuiltinArgument(tree, token)) return false;
        return true;
    }

    pub fn deinit(self: *FileCache) void {
        if (self.line_offsets.len > 0) self.gpa.free(self.line_offsets);
        if (self.file_model) |*m| m.deinit();
        if (self.summary_arena) |*a| a.deinit();
        if (self.exact_spans) |*spans| spans.deinit(self.gpa);
        self.fill_lexical_index.deinit(self.gpa);
        var it = self.bindings.valueIterator();
        while (it.next()) |b| b.deinit();
        self.bindings.deinit(self.gpa);
        self.summaries.deinit(self.gpa);
        self.failed_roots.deinit(self.gpa);
        self.summary_visiting.deinit(self.gpa);
        self.resolved_declarations.deinit(self.gpa);
        self.resolved_declaration_visiting.deinit(self.gpa);
        self.cleanup_summaries.deinit(self.gpa);
        self.cleanup_visiting.deinit(self.gpa);
        inline for (.{ &self.return_defined_summaries, &self.diagnostic_return_summaries }) |verdicts| {
            var return_verdicts = verdicts.valueIterator();
            while (return_verdicts.next()) |verdict| {
                for (verdict.stores.items) |store| self.gpa.free(store.path);
                verdict.stores.deinit(self.gpa);
                for (verdict.bytes.items) |*mask| mask.deinit(self.gpa);
                verdict.bytes.deinit(self.gpa);
            }
            verdicts.deinit(self.gpa);
        }
        self.return_defined_visiting.deinit(self.gpa);
        self.return_replay_failures.deinit(self.gpa);
        self.return_replay_syntax.deinit(self.gpa);
        self.return_calls.deinit(self.gpa);
        self.return_diagnostic_seeds.deinit(self.gpa);
        self.return_source_eligibility.deinit(self.gpa);
        self.return_source_visiting.deinit(self.gpa);
        self.array_source_visiting.deinit(self.gpa);
        self.method_scalar_reads.deinit(self.gpa);
        self.method_scalar_reads_visiting.deinit(self.gpa);
        self.diagnostic_output_touches.deinit(self.gpa);
        self.diagnostic_output_touches_visiting.deinit(self.gpa);
        self.store_value_visiting.deinit(self.gpa);
        self.retained_writes.deinit(self.gpa);
        var mit = self.method_lookup_cache.iterator();
        while (mit.next()) |e| self.gpa.free(e.key_ptr.*);
        self.method_lookup_cache.deinit(self.gpa);
        self.embedded_file_lengths.deinit(self.gpa);
        var cfit = self.cross_file_fields.iterator();
        while (cfit.next()) |e| self.gpa.free(e.key_ptr.*);
        self.cross_file_fields.deinit(self.gpa);
        self.foreign_method_summaries.deinit(self.gpa);
        self.foreign_takes.deinit(self.gpa);
        if (self.root_consts) |*t| t.deinit(self.gpa);
        if (self.call_index) |index| index.deinit(self.gpa);
        var cit = self.closed_local_calls.valueIterator();
        while (cit.next()) |entry| if (entry.*) |calls| self.gpa.free(calls);
        self.closed_local_calls.deinit(self.gpa);
        var sit = self.syntax_uses.valueIterator();
        while (sit.next()) |entry| self.gpa.free(entry.*);
        self.syntax_uses.deinit(self.gpa);
        var eit = self.escape_roots.valueIterator();
        while (eit.next()) |entry| {
            self.gpa.free(entry.*.addressed);
            self.gpa.free(entry.*.writes);
            self.gpa.destroy(entry.*);
        }
        self.escape_roots.deinit(self.gpa);
        if (self.address_uses) |*uses| uses.deinit(self.gpa);
        self.definite_parameter_writes.deinit(self.gpa);
        self.actual_callees.deinit(self.gpa);
        self.preserving_writes.deinit(self.gpa);
        self.preserving_visiting.deinit(self.gpa);
        var source_plans = self.effect_source_plans.valueIterator();
        while (source_plans.next()) |plan| plan.deinit(self.gpa);
        self.effect_source_plans.deinit(self.gpa);
        var binding_writes = self.effect_binding_writes.valueIterator();
        while (binding_writes.next()) |index| index.deinit(self.gpa);
        self.effect_binding_writes.deinit(self.gpa);
        self.direct_effects.deinit(self.gpa);
        self.fresh_storage.deinit(self.gpa);
        self.fresh_visiting.deinit(self.gpa);
        self.scalar_params.deinit(self.gpa);
        self.effects_state.deinit(self.gpa);
        self.return_storage_state.deinit(self.gpa);
        self.alias_state.deinit(self.gpa);
        // The ROOT cache owns the one grow state, and it tears down every
        // document it opened with it.  A document opened to answer a
        // demand query borrows the root's state and tears down none of
        // it, which is what lets a fold cross a document boundary.
        if (self.grow_state) |state| {
            if (!self.grow_on_demand) state.deinit(self.gpa);
            self.grow_state = null;
        }
    }

    /// Lazily build (and cache) the FileModel for this file.
    pub fn fileModel(self: *FileCache) !*const file_model.FileModel {
        if (self.file_model == null) {
            const fp: ?[]const u8 = if (self.file_path.len > 0) self.file_path else null;
            self.file_model = try file_model.buildWithPath(self.gpa, self.tree, fp);
        }
        return &self.file_model.?;
    }

    /// Lazily build (and cache) the line offset table for this file.
    /// Called once per file; subsequent calls return the cached slice.
    /// Refuse `SourceTooWide` before scanning, allocation, or cached lookup.
    pub fn getLineOffsets(self: *FileCache) ![]const u32 {
        if (!SourcePolicy.admitsSourceLength(self.tree.source.len)) return error.SourceTooWide;
        if (self.line_offsets.len > 0) return self.line_offsets;
        self.line_offsets = try cfg_builder_mod.buildLineOffsets(self.gpa, self.tree.source);
        return self.line_offsets;
    }

    /// Lazily build (and cache) LocalBindings for the given fn body.
    /// Keyed by body node — rules processing the same fn share one
    /// build. The returned pointer is borrowed until another body's
    /// bindings grow the map. Its arena-backed items stay valid until
    /// cache teardown; reacquire the table after reentrant queries.
    pub fn localBindings(
        self: *FileCache,
        proto: Ast.full.FnProto,
        body: Ast.Node.Index,
    ) !*const local_bindings.LocalBindings {
        const key = @intFromEnum(body);
        if (self.bindings.getPtr(key)) |bindings| return bindings;
        // Build privately: a failed build must not publish an undefined
        // arena that retry or cache teardown would read.
        var built = try local_bindings.build(self.gpa, self.tree, proto, body);
        errdefer built.deinit();
        const gop = try self.bindings.getOrPut(self.gpa, key);
        std.debug.assert(!gop.found_existing);
        gop.value_ptr.* = built;
        return gop.value_ptr;
    }

    /// Lazily infer (and cache) the behavioral summary for the given
    /// fn body.  Same caching contract as localBindings.  Body-only
    /// inference — for the deep fields (may_free_fields /
    /// result_heap_fields / heap_allocates_self), use `summaryOfFn`.
    fn summaryOf(
        self: *FileCache,
        proto: Ast.full.FnProto,
        body: Ast.Node.Index,
    ) !*const fn_summary.FnSummary {
        const key = @intFromEnum(body);
        const gop = try self.summaries.getOrPut(self.gpa, key);
        if (!gop.found_existing) {
            gop.value_ptr.* = fn_summary.inferFromBody(self.tree, proto, body);
        }
        return gop.value_ptr;
    }

    /// The parameter's complete declared container path, with pointer and
    /// optional qualifiers removed. Preserve its root import alias and
    /// nested type segments: a foreign leaf name alone proves no binding.
    /// Non-path expressions are resolved by the type engine when available.
    pub fn paramContainerName(
        self: *FileCache,
        proto: Ast.full.FnProto,
        idx: u32,
    ) !?[]const u8 {
        var i: u32 = 0;
        var it = proto.iterate(self.tree);
        while (it.next()) |p| : (i += 1) {
            if (i != idx) continue;
            const type_node = p.type_expr orelse return null;
            // A declared identifier path is already exact. Do not reduce
            // `namespace.Type` to the unrelated bare `Type`.
            if (typeNameFromTypeNode(self.tree, type_node)) |name| return name;
            const z = self.zls orelse return null;
            return z.typeNameOfNode(type_node) catch null;
        }
        return null;
    }

    /// Filter may_free_fields entries — an entry survives only when:
    ///   - param's type is locally declared
    ///   - field is not pointer-typed
    ///   - field's declared type is locally declared
    ///   - the field-type's method (the one recorded in ff.method)
    ///     exists AND has takes_ownership_of != null (the method
    ///     actually consumes its receiver — not just that it
    ///     exists).  Without this check value-typed fields whose type
    ///     has a non-consuming deinit get treated as freed when they
    ///     shouldn't.
    fn filterMayFreeFields(
        self: *FileCache,
        arena: std.mem.Allocator,
        model: *const file_model.FileModel,
        tree: *const Ast,
        proto: Ast.full.FnProto,
        raw: []const fn_summary.FieldFree,
    ) ![]const fn_summary.FieldFree {
        _ = tree;
        if (raw.len == 0) return &.{};
        var out: std.ArrayListUnmanaged(fn_summary.FieldFree) = .empty;
        for (raw) |ff| {
            const param_ty = (try self.paramContainerName(proto, ff.param)) orelse continue;
            if (!model.hasType(param_ty)) continue;
            const deepest_path = walkFieldPath(model, param_ty, ff.field) orelse continue;
            // Resolve the cleanup method on the deepest field's TYPE and
            // decide whether to keep this field-free.  Keep iff the
            // callee takes ownership OR is cleanup-named (deinit/close/…),
            // in which case we presume it consumes its receiver even
            // without an explicit takes signal — recovers external-stdlib
            // deinit cases (e.g. HashMap.deinit) pure inference can't see.
            //
            // The field's type may be local (including a nested type) or
            // imported. Resolve its complete spelling locally first;
            // otherwise the exact root import alias path proves which
            // foreign declaration owns the cleanup method.
            const keep: bool = blk: {
                if (findTypeInModelPath(model, deepest_path.qualified_name)) |ti| {
                    if (!ti.hasMethod(ff.method)) break :blk false;
                    const summary = (try self.summaryByMethod(deepest_path.qualified_name, ff.method)) orelse break :blk false;
                    break :blk summary.takes_ownership_of != null or
                        fn_summary.isReceiverCleanupMethodName(ff.method);
                }
                const foreign = (try self.summaryByMethodCrossFile(deepest_path.qualified_name, ff.method)) orelse break :blk false;
                break :blk foreign.takes_ownership_of != null or
                    fn_summary.isReceiverCleanupMethodName(ff.method);
            };
            if (!keep) continue;
            try out.append(arena, ff);
        }
        return out.toOwnedSlice(arena);
    }

    /// Fixed-point pass: for every fn in the file, propagate
    /// `takes_ownership_of` transitively across `<param>.<method>()`
    /// chains.  When `method`'s summary takes its receiver (arg 0),
    /// the outer fn takes `<param>`.  Iterates until no new takes
    /// are inferred (bounded by `max_iters` to guard against
    /// pathological cases).
    ///
    /// Direct chain (`<param>.<method>()`) only.  Multi-segment
    /// `<param>.<field>.<method>()` chains are tracked via
    /// `may_free_fields` and resolved separately.
    ///
    /// Idempotent.  Call once per file before any consumer reads
    /// summaries that depend on transitive ownership.
    // Explicit `anyerror` error set (not inferred) breaks an
    // inferred-error-set dependency loop: resolveTransitiveTakes ->
    // propagateTransitiveTakesOne -> summaryByMethodCrossFile (which now
    // re-enters resolveTransitiveTakes on a project-less foreign cache).
    pub fn resolveTransitiveTakes(self: *FileCache) anyerror!void {
        return self.resolveTransitiveTakesInto(null);
    }

    /// `resolveTransitiveTakes` that survives analysis-budget exhaustion.
    /// A function whose summary work exhausts a budget is appended to
    /// `failures` and left out of every later phase; the pass continues
    /// with the next function. Every other error propagates.
    ///
    /// The failed function's summary is never published as complete: its
    /// entry is withdrawn, and every later lookup of it raises the failure
    /// it recorded (`failed_roots`).  A function that reads a failed one
    /// fails with it, so a partial fold never reaches a caller as a finished
    /// one.  A fixpoint still moving after `max_fixpoint_rounds` passes is a
    /// failure of the whole pass and propagates out of it.
    pub fn resolveTransitiveTakesCollecting(
        self: *FileCache,
        failures: *std.ArrayListUnmanaged(SummaryFailure),
    ) anyerror!void {
        return self.resolveTransitiveTakesInto(failures);
    }

    fn resolveTransitiveTakesInto(self: *FileCache, failures: ?*std.ArrayListUnmanaged(SummaryFailure)) anyerror!void {
        // One finished pass is final. A repeat would only redo failed roots.
        if (self.transitive_resolved) return;
        const model = try self.fileModel();
        var roots = try RootFailures.init(self.gpa, self.tree.nodes.len, failures);
        defer roots.deinit(self.gpa);
        // Phase 1a: pre-warm summaries for every fn.
        for (model.fns) |fi| {
            if (self.summaryOfFn(fi.fn_decl)) |_| {} else |err| try roots.note(self, fi.fn_decl, err);
        }
        for (model.types) |ti| {
            for (ti.methods) |m| {
                if (self.summaryOfFn(m.fn_decl)) |_| {} else |err| try roots.note(self, m.fn_decl, err);
            }
        }

        // Phase 1b: seed takes_ownership_of via direct R8b inference.
        // Done explicitly here (not in inferFromBody) so the seed is
        // only applied when transitive resolution is requested —
        // pattern rules that don't go through this path get the
        // conservative .unknown / null defaults.
        const seedFn = struct {
            fn run(self2: *FileCache, fn_decl: Ast.Node.Index) !void {
                var pbuf: [1]Ast.Node.Index = undefined;
                const proto = tokens.fnProto(self2.tree, &pbuf, fn_decl) orelse return;
                const body = tokens.bodyOf(self2.tree, fn_decl) orelse return;
                if (fn_summary.inferDirectTakes(self2.tree, proto, body)) |idx| {
                    const key = @intFromEnum(body);
                    if (self2.summaries.getPtr(key)) |entry| {
                        if (entry.takes_ownership_of == null) {
                            entry.takes_ownership_of = idx;
                        }
                    }
                }
            }
        }.run;
        for (model.fns) |fi| try seedFn(self, fi.fn_decl);
        for (model.types) |ti| {
            for (ti.methods) |m| try seedFn(self, m.fn_decl);
        }
        // Phase 2: fixed-point R10 Case A propagation.
        var iters: u32 = 0;
        while (iters <= max_fixpoint_rounds) : (iters += 1) {
            var changed = false;
            for (model.fns) |fi| {
                if (roots.skipped(fi.fn_decl)) continue;
                const took = self.propagateTransitiveTakesOne(fi.fn_decl, null) catch |err| {
                    try roots.note(self, fi.fn_decl, err);
                    continue;
                };
                if (took) changed = true;
            }
            for (model.types) |ti| {
                for (ti.methods) |m| {
                    if (roots.skipped(m.fn_decl)) continue;
                    const took = self.propagateTransitiveTakesOne(m.fn_decl, ti.qualified_name) catch |err| {
                        try roots.note(self, m.fn_decl, err);
                        continue;
                    };
                    if (took) changed = true;
                }
            }
            if (!changed) break;
            if (iters == max_fixpoint_rounds) return fixpointUnsettled();
        }

        // Phase 3: filter may_free_fields per fn.  Done here (not in
        // summaryOfFn) because the filter consults OTHER fn summaries
        // — moving it inside summaryOfFn creates a comptime dep cycle.
        // Filter requires Phase 2 to be done so the called methods'
        // takes_ownership_of reflects the transitive analysis.
        for (model.fns) |fi| {
            if (roots.skipped(fi.fn_decl)) continue;
            self.filterMayFreeFieldsOne(fi.fn_decl) catch |err| try roots.note(self, fi.fn_decl, err);
        }
        for (model.types) |ti| {
            for (ti.methods) |m| {
                if (roots.skipped(m.fn_decl)) continue;
                self.filterMayFreeFieldsOne(m.fn_decl) catch |err| try roots.note(self, m.fn_decl, err);
            }
        }

        // Phase 4: fixed-point R7 inference — propagate
        // `returns = .borrowed_from(N)` across delegating wrappers.
        // A fn whose body returns a delegating call to another fn
        // that's inferred borrowed_from inherits the borrowed_from
        // with the local param index.  Skipped when the fn's returns
        // is already known (preserves .heap / .owned / explicit
        // borrowed_from).
        iters = 0;
        while (iters <= max_fixpoint_rounds) : (iters += 1) {
            var changed = false;
            for (model.fns) |fi| {
                if (roots.skipped(fi.fn_decl)) continue;
                const set = self.inferDelegatorBorrowOne(fi.fn_decl) catch |err| {
                    try roots.note(self, fi.fn_decl, err);
                    continue;
                };
                if (set) changed = true;
            }
            for (model.types) |ti| {
                for (ti.methods) |m| {
                    if (roots.skipped(m.fn_decl)) continue;
                    const set = self.inferDelegatorBorrowOne(m.fn_decl) catch |err| {
                        try roots.note(self, m.fn_decl, err);
                        continue;
                    };
                    if (set) changed = true;
                }
            }
            if (!changed) break;
            if (iters == max_fixpoint_rounds) return fixpointUnsettled();
        }

        // Phases 5-7: propagate the transitive EFFECT flags
        // (may_grow_collections / may_invoke_gc / may_run_on_any_thread) to a
        // fixed point.  Direct detection is done in `inferFromBody`; this
        // propagates one call-hop at a time.  Each effect considers BOTH
        // same-file bare calls (`foo()`) AND same-file/cross-file method
        // calls (`recv.method()`).  The cross-file leg (#20) inherits the
        // foreign method's direct effect via `summaryByMethodCrossFile`.
        inline for ([_]Effect{ .grow, .gc, .thread }) |eff| {
            iters = 0;
            while (iters <= max_fixpoint_rounds) : (iters += 1) {
                var changed = false;
                for (model.fns) |fi| {
                    if (roots.skipped(fi.fn_decl)) continue;
                    const grew = self.propagateEffectOne(fi.fn_decl, null, eff) catch |err| {
                        try roots.note(self, fi.fn_decl, err);
                        continue;
                    };
                    if (grew) changed = true;
                }
                for (model.types) |ti| {
                    for (ti.methods) |m| {
                        if (roots.skipped(m.fn_decl)) continue;
                        const grew = self.propagateEffectOne(m.fn_decl, ti.qualified_name, eff) catch |err| {
                            try roots.note(self, m.fn_decl, err);
                            continue;
                        };
                        if (grew) changed = true;
                    }
                }
                if (!changed) break;
                if (iters == max_fixpoint_rounds) return fixpointUnsettled();
            }
        }
        self.transitive_resolved = true;
    }

    /// A transitive boolean effect tracked by `propagateEffectOne`.
    const Effect = enum { grow, gc, thread };

    fn readEffect(s: *const fn_summary.FnSummary, comptime e: Effect) bool {
        return switch (e) {
            .grow => s.may_grow_collections,
            .gc => s.may_invoke_gc,
            .thread => s.may_run_on_any_thread,
        };
    }
    fn writeEffect(s: *fn_summary.FnSummary, comptime e: Effect) void {
        switch (e) {
            .grow => s.may_grow_collections = true,
            .gc => s.may_invoke_gc = true,
            .thread => s.may_run_on_any_thread = true,
        }
    }

    /// Propagate one transitive EFFECT flag into `fn_decl` from its
    /// callees.  Considers same-file bare calls (`foo()` -> summaryByName)
    /// AND same-file/cross-file method calls (`recv.method()` ->
    /// summaryByMethod / summaryByMethodCrossFile).  `receiver_type` is the
    /// enclosing type for methods (so `self.method()` resolves), null for
    /// free fns.  Returns true iff this call set the flag.
    fn propagateEffectOne(
        self: *FileCache,
        fn_decl: Ast.Node.Index,
        receiver_type: ?[]const u8,
        comptime e: Effect,
    ) !bool {
        const s_ptr = try self.summaryOfFn(fn_decl);
        if (readEffect(s_ptr, e)) return false;

        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const body = tokens.bodyOf(tree, fn_decl) orelse return false;
        const first = tree.firstToken(body);
        const last = tree.lastToken(body);

        var pbuf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &pbuf, fn_decl);

        var t = first;
        while (t + 1 <= last) : (t += 1) {
            if (tags[t] == .keyword_fn) {
                t = tokens.skipNestedFn(tags, t, last);
                continue;
            }
            if (tags[t] != .identifier) continue;
            if (tags[t + 1] != .l_paren) continue;

            const is_method = t > first and tags[t - 1] == .period;
            const has_effect: bool = blk: {
                if (!is_method) {
                    // Bare call -> same-file free fn (unchanged behavior).
                    if (try self.summaryByName(tree.tokenSlice(t))) |cs| break :blk readEffect(cs, e);
                    break :blk false;
                }
                // Method call `recv.method(` — recv is two tokens back.
                if (t < first + 2 or tags[t - 2] != .identifier) break :blk false;
                const method = tree.tokenSlice(t);
                const recv = tree.tokenSlice(t - 2);
                const recv_type: ?[]const u8 = rt: {
                    if (proto) |p| {
                        if (paramIndexFor(tree, p, recv)) |pi| {
                            if (try self.paramContainerName(p, pi)) |tn| break :rt tn;
                        }
                    }
                    if (std.mem.eql(u8, recv, "self") or std.mem.eql(u8, recv, "this")) break :rt receiver_type;
                    break :rt null;
                };
                const tn = recv_type orelse break :blk false;
                if (try self.summaryByMethod(tn, method)) |cs| break :blk readEffect(cs, e);
                if (try self.summaryByMethodCrossFile(tn, method)) |cs| break :blk readEffect(&cs, e);
                break :blk false;
            };
            if (has_effect) {
                const key = @intFromEnum(body);
                if (self.summaries.getPtr(key)) |entry| {
                    writeEffect(entry, e);
                    return true;
                }
            }
        }
        return false;
    }

    /// Apply R7 delegator-borrow inference to one fn.  Returns true
    /// iff this call set/updated the fn's `returns` field.
    fn inferDelegatorBorrowOne(self: *FileCache, fn_decl: Ast.Node.Index) !bool {
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &buf, fn_decl) orelse return false;
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return false;

        const s_ptr = try self.summaryOfFn(fn_decl);
        // Only fill when returns hasn't been determined yet.
        switch (s_ptr.returns) {
            .unknown => {},
            else => return false,
        }

        const idx = try self.inferDelegatorBorrow(proto, body) orelse return false;
        const key = @intFromEnum(body);
        if (self.summaries.getPtr(key)) |entry| {
            entry.returns = .{ .borrowed_from = idx };
            return true;
        }
        return false;
    }

    /// R7 delegator-borrow inference.  Tries the single-return shape
    /// first; falls back to multi-return.  Returns the borrowed param
    /// index when inference fires.
    fn inferDelegatorBorrow(
        self: *FileCache,
        proto: Ast.full.FnProto,
        body: Ast.Node.Index,
    ) !?u32 {
        if (fn_summary.singleReturnExpr(self.tree, body)) |re| {
            if (try self.tryInferFromReturnExpr(proto, re)) |idx| return idx;
        }
        return try self.inferDelegatorBorrowMultiReturn(proto, body);
    }

    /// Try every R7 shape on a single return expression.
    fn tryInferFromReturnExpr(
        self: *FileCache,
        proto: Ast.full.FnProto,
        return_expr: Ast.Node.Index,
    ) !?u32 {
        // Extends-storage form (struct literal carrying a param).
        if (fn_summary.inferReturnStructLiteralBorrowsParam(self.tree, proto, return_expr)) |idx| {
            return idx;
        }
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = self.tree.fullCall(&buf, return_expr) orelse return null;
        if (try self.inferMethodStyle(proto, return_expr)) |idx| return idx;
        return try self.inferNamespaceStyle(proto, call_full);
    }

    /// `return <param>.<chain>.<method>(args);` shape.  Fires when
    /// `<method>` is `borrowed_from(self)` (target_idx 0).
    fn inferMethodStyle(
        self: *FileCache,
        proto: Ast.full.FnProto,
        return_expr: Ast.Node.Index,
    ) !?u32 {
        const tree = self.tree;
        const first = tree.firstToken(return_expr);
        const last = tree.lastToken(return_expr);
        const tags = tree.tokens.items(.tag);

        if (tags[first] != .identifier) return null;
        if (first + 1 > last or tags[first + 1] != .period) return null;

        const head_name = tree.tokenSlice(first);
        const param_idx = fn_summary.paramIndex(tree, proto, head_name) orelse return null;

        var k: Ast.TokenIndex = first + 1;
        var method_tok: Ast.TokenIndex = 0;
        while (k + 1 <= last and tags[k] == .period and tags[k + 1] == .identifier) {
            method_tok = k + 1;
            k += 2;
            if (k > last) break;
            if (tags[k] == .l_paren) break;
            if (tags[k] != .period) {
                method_tok = 0;
                break;
            }
        }
        if (method_tok == 0) return null;
        if (k > last or tags[k] != .l_paren) return null;

        const method_name = tree.tokenSlice(method_tok);
        // The receiver's declared type decides the callee. A parameter whose
        // type cannot be resolved, or a method that type does not declare,
        // proves nothing: a same-named top-level fn is another declaration.
        const type_name = (try self.paramContainerName(proto, param_idx)) orelse return null;
        const model = try self.fileModel();
        var owner = self.resolvedTypeAcrossImports(type_name) orelse return null;
        var field_tok = first + 2;
        while (field_tok < method_tok) : (field_tok += 2) {
            owner = self.fieldType(owner, tree.tokenSlice(field_tok)) orelse return null;
        }
        // Foreign methods carry no borrowed-return summary in this cache.
        if (owner.model != model) return null;
        const method = owner.info.findMethod(method_name) orelse return null;
        const returns = (try self.summaryOfFn(method.fn_decl)).returns;
        if (returns == .borrowed_from and returns.borrowed_from == 0) return param_idx;
        return null;
    }

    /// Resolve a namespace or lexical function declaration before propagating
    /// its borrowed argument. A leaf name is not a dispatch identity: a
    /// qualified callee dispatches on its namespace type only, and a bare
    /// callee on the nearest enclosing declaration scope, then the file root.
    fn inferNamespaceStyle(
        self: *FileCache,
        proto: Ast.full.FnProto,
        call_full: Ast.full.Call,
    ) !?u32 {
        const tree = self.tree;
        const callee = call_full.ast.fn_expr;
        const method_tok = switch (tree.nodeTag(callee)) {
            .identifier => tree.nodeMainToken(callee),
            .field_access => tree.nodeData(callee).node_and_token[1],
            else => return null,
        };
        const method_name = tree.tokenSlice(method_tok);
        const model = try self.fileModel();
        const scope = model.containingTypeAtToken(proto.ast.fn_token);
        const returns = result: {
            if (tree.nodeTag(callee) == .field_access) {
                const recv = tree.nodeData(callee).node_and_token[0];
                const type_name = typeNameFromTypeNode(tree, recv) orelse return null;
                const owner = (if (scope) |s|
                    model.resolveTypeNameInScope(type_name, s)
                else
                    findTypeInModelPath(model, type_name)) orelse return null;
                const method = owner.findMethod(method_name) orelse return null;
                break :result (try self.summaryOfFn(method.fn_decl)).returns;
            }
            var walk: ?*const file_model.TypeInfo = scope;
            while (walk) |owner| {
                if (owner.findMethod(method_name)) |method| {
                    break :result (try self.summaryOfFn(method.fn_decl)).returns;
                }
                walk = if (owner.parent) |parent| &model.types[parent] else null;
            }
            const summary = (try self.summaryByName(method_name)) orelse return null;
            break :result summary.returns;
        };
        const idx_resolved = switch (returns) {
            .borrowed_from => |idx| idx,
            else => return null,
        };
        const args = call_full.ast.params;
        if (idx_resolved >= args.len) return null;
        const arg = args[idx_resolved];
        if (tree.nodeTag(arg) != .identifier) return null;
        const arg_name = tree.tokenSlice(tree.nodeMainToken(arg));
        return fn_summary.paramIndex(tree, proto, arg_name);
    }

    /// Multi-return-stmt variant: walk every `return EXPR;` whose
    /// token range lies within `body`, infer per-return, and return
    /// `borrowed_from(N)` only when at least one return matched AND
    /// every matched return agreed on the same N.  Non-borrow shapes
    /// (literals / null / undefined / `&.{}`) are skipped.
    fn inferDelegatorBorrowMultiReturn(
        self: *FileCache,
        proto: Ast.full.FnProto,
        body: Ast.Node.Index,
    ) !?u32 {
        const tree = self.tree;
        const body_first = tree.firstToken(body);
        const body_last = tree.lastToken(body);

        var found: ?u32 = null;
        var any_match = false;

        var node_idx: u32 = 1;
        while (node_idx < tree.nodes.len) : (node_idx += 1) {
            const node: Ast.Node.Index = @enumFromInt(node_idx);
            if (tree.nodeTag(node) != .@"return") continue;
            const ft = tree.firstToken(node);
            const lt = tree.lastToken(node);
            if (ft < body_first or lt > body_last) continue;

            const value = tree.nodeData(node).opt_node.unwrap() orelse continue;
            if (fn_summary.isNonBorrowReturnValue(tree, value)) continue;

            const idx = try self.tryInferFromReturnExpr(proto, value) orelse return null;
            if (found) |existing| if (existing != idx) return null;
            found = idx;
            any_match = true;
        }
        if (!any_match) return null;
        return found.?;
    }

    /// Apply filterMayFreeFields to one fn's summary in-place.
    fn filterMayFreeFieldsOne(self: *FileCache, fn_decl: Ast.Node.Index) !void {
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &buf, fn_decl) orelse return;
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return;
        const key = @intFromEnum(body);
        const fields = (self.summaries.get(key) orelse return).may_free_fields;
        if (fields.len == 0) return;
        const model = try self.fileModel();
        if (self.summary_arena == null) {
            self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        }
        const a = self.summary_arena.?.allocator();
        const filtered = try self.filterMayFreeFields(a, model, self.tree, proto, fields);
        self.summaries.getPtr(key).?.may_free_fields = filtered;
    }

    /// Returns true iff the fn's summary's `takes_ownership_of` was
    /// updated by this call.  Scans body for `<param>.<method>()`
    /// chains; when method's cached summary takes arg 0, the outer
    /// fn takes the param.
    fn propagateTransitiveTakesOne(
        self: *FileCache,
        fn_decl: Ast.Node.Index,
        receiver_type: ?[]const u8,
    ) !bool {
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &buf, fn_decl) orelse return false;
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return false;

        // If we already know a takes for this fn, no work to do.
        const s_ptr = try self.summaryOfFn(fn_decl);
        if (s_ptr.takes_ownership_of != null) return false;

        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const first = tree.firstToken(body);
        const last = tree.lastToken(body);

        var t = first;
        while (t + 3 <= last) : (t += 1) {
            if (tags[t] == .keyword_fn) {
                t = tokens.skipNestedFn(tags, t, last);
                continue;
            }
            if (tags[t] != .identifier) continue;
            if (tags[t + 1] != .period) continue;
            if (tags[t + 2] != .identifier) continue;
            if (tags[t + 3] != .l_paren) continue;
            // Reject longer chains (`a.b.c(` shouldn't match at `b.c(`).
            if (t > first and tags[t - 1] == .period) continue;

            const param_name = tree.tokenSlice(t);
            const pi = paramIndexFor(tree, proto, param_name) orelse continue;
            const method = tree.tokenSlice(t + 2);

            // Look up callee summary on PARAM's declared type — that's
            // the receiver of `<param>.<method>(`.  Typed paths only:
            // bare-name lookup is omitted because it can match the same
            // method name on a completely different type and propagate
            // ownership where none exists.  ZLS-resolved type first
            // (precise), then the enclosing struct's type (provably
            // correct for self-receiver), then cross-file variants of
            // both.
            const param_type = try self.paramContainerName(proto, pi);
            const callee_takes: ?u32 = blk: {
                if (param_type) |tn| {
                    if (try self.summaryByMethod(tn, method)) |s| {
                        break :blk s.takes_ownership_of;
                    }
                }
                if (receiver_type) |rt| {
                    if (try self.summaryByMethod(rt, method)) |s| {
                        break :blk s.takes_ownership_of;
                    }
                }
                // Cross-file fallback: callee lives in an @import'd file.
                // Direct-takes inference only — no transitive resolution
                // for foreign bodies.
                if (param_type) |tn| {
                    if (try self.summaryByMethodCrossFile(tn, method)) |xf| {
                        break :blk xf.takes_ownership_of;
                    }
                }
                if (receiver_type) |rt| {
                    if (try self.summaryByMethodCrossFile(rt, method)) |xf| {
                        break :blk xf.takes_ownership_of;
                    }
                }
                break :blk null;
            };
            if (callee_takes) |idx| {
                if (idx == 0) {
                    // Mutate the cached entry in place.
                    const key = @intFromEnum(body);
                    if (self.summaries.getPtr(key)) |entry| {
                        entry.takes_ownership_of = pi;
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /// Look up the FnSummary for a top-level fn named `name`.
    /// Replaces the old `db.lookup(name)` query for the intra-file
    /// (same-file) path.  Returns null when no top-level fn matches.
    pub fn summaryByName(
        self: *FileCache,
        name: []const u8,
    ) !?*const fn_summary.FnSummary {
        const model = try self.fileModel();
        const fi = model.findFn(name) orelse return null;
        return try self.summaryOfFn(fi.fn_decl);
    }

    /// Look up the FnSummary for a method `method_name` on `type_name`.
    /// Replaces the old `db.lookupTyped(type, name)` query for the
    /// intra-file path.  Returns null when the type or method isn't
    /// declared in this file.
    pub fn summaryByMethod(
        self: *FileCache,
        type_name: []const u8,
        method_name: []const u8,
    ) !?*const fn_summary.FnSummary {
        const model = try self.fileModel();
        const ti = findTypeInModelPath(model, type_name) orelse return null;
        const m = ti.findMethod(method_name) orelse return null;
        return try self.summaryOfFn(m.fn_decl);
    }

    /// Look up a method summary in the import named by `type_name`.
    /// Qualified names start with the exact root import alias
    /// (`namespace.Type`); a bare name works only for a root const that
    /// directly selects its imported type. No project-wide leaf-name
    /// search can establish that this file imports a declaration.
    ///
    /// Returns an owned-by-value summary. Foreign variable-length fields
    /// are copied into this cache's `summary_arena`; direct effects and
    /// transitive takes within the foreign file retain their existing
    /// inference bounds.
    ///
    /// Use case: detecting that a callee defined in another file takes
    /// ownership of its first parameter (e.g. `bun.destroy(ptr)` where
    /// `destroy` lives in `bun.zig`).
    pub fn summaryByMethodCrossFile(
        self: *FileCache,
        type_name: []const u8,
        method_name: []const u8,
    ) !?fn_summary.FnSummary {
        const rm = self.findMethodAcrossImports(type_name, method_name) orelse return null;
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(rm.tree, &buf, rm.method.fn_decl) orelse return null;
        const body = tokens.bodyOf(rm.tree, rm.method.fn_decl) orelse return null;
        const key: ForeignBodyKey = .{
            .tree = rm.tree,
            .module = self.module_id,
            .body = @intFromEnum(body),
        };
        if (self.foreign_method_summaries.get(key)) |cached| return cached;
        var summary: fn_summary.FnSummary = .{};
        // Cross-file effect flags (#20) include the foreign method's direct
        // body effects. A foreign method that delegates a grow or GC effect
        // is outside this one-file summary bound.
        const direct = fn_summary.inferFromBody(rm.tree, proto, body);
        summary.takes_ownership_of = direct.takes_ownership_of;
        summary.may_grow_collections = direct.may_grow_collections;
        summary.may_invoke_gc = direct.may_invoke_gc;
        summary.may_run_on_any_thread = direct.may_run_on_any_thread;

        // Follow ownership delegation only within the resolved foreign file.
        // A project-less cache prevents recursive cross-file summaries.
        if (summary.takes_ownership_of == null) {
            summary.takes_ownership_of = try self.foreignOwnership(rm, key);
        }

        const effects = try self.foreignFieldEffects(type_name, method_name);
        summary.freed_paths = effects.freed_paths;
        summary.written_paths = effects.written_paths;
        try self.foreign_method_summaries.put(self.gpa, key, summary);
        return summary;
    }

    fn foreignOwnership(self: *FileCache, rm: ResolvedMethod, key: ForeignBodyKey) !?u32 {
        // getPtr distinguishes a completed negative answer from a cache miss.
        if (self.foreign_takes.getPtr(key)) |completed| return completed.*;

        // Keep the original one-file inference bound. No temporary summary
        // slices, bindings or model pointers escape this project-less cache.
        var foreign = FileCache.init(self.gpa, rm.tree);
        defer foreign.deinit();
        try foreign.resolveTransitiveTakes();
        const takes = (try foreign.summaryOfFn(rm.method.fn_decl)).takes_ownership_of;

        // Reserve after the complete fold, before publishing any answers.
        // A failed allocation leaves this document unpublished and retryable;
        // the remaining inserts cannot fail or expose a partial completion.
        try self.foreign_takes.ensureUnusedCapacity(self.gpa, foreign.summaries.count());
        var summaries = foreign.summaries.iterator();
        while (summaries.next()) |entry| {
            self.foreign_takes.putAssumeCapacity(.{
                .tree = rm.tree,
                .module = key.module,
                .body = entry.key_ptr.*,
            }, entry.value_ptr.takes_ownership_of);
        }
        return takes;
    }

    /// The receiver-field paths (`freed_paths` / `written_paths`) of the
    /// method `type_name.method_name` resolves to, or the EMPTY pair when
    /// nothing resolves or the declaration spells out nothing.
    ///
    /// `inferFieldEffects` over the RESOLVED DECLARATION is the one
    /// authoritative source, and it is the same reading `summaryOfFn`
    /// makes for a declaration in this file — a foreign summary must
    /// not differ from a local one in what it claims about the same
    /// body, or which of the two a caller believes depends on where
    /// the type happens to be declared.  There is therefore no second
    /// list to reconcile with this one and none to double-count.
    /// The per-file memo stores exactly what the declaration said, so
    /// repeated summaries reuse these paths rather than copying a second
    /// set.
    ///
    /// The slices live in `summary_arena`, which outlives the analysis,
    /// so the value may be copied into a summary handed back by value.
    fn foreignFieldEffects(
        self: *FileCache,
        type_name: []const u8,
        method_name: []const u8,
    ) !fn_summary.FieldEffects {
        const key = try std.fmt.allocPrint(
            self.gpa,
            "{s}\x00{s}",
            .{ type_name, method_name },
        );
        defer self.gpa.free(key);
        if (self.cross_file_fields.get(key)) |eff| return eff;

        var eff: fn_summary.FieldEffects = .{};
        if (self.findMethodAcrossImports(type_name, method_name)) |rm| {
            var pbuf: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(rm.tree, &pbuf, rm.method.fn_decl) orelse return eff;
            const body = tokens.bodyOf(rm.tree, rm.method.fn_decl) orelse return eff;
            if (self.summary_arena == null) {
                self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
            }
            const a = self.summary_arena.?.allocator();
            const bindings = try local_bindings.build(a, rm.tree, proto, body);
            eff = try fn_summary.inferFieldEffects(a, rm.tree, proto, &bindings, body);
            try ownEffectPathTexts(a, eff.freed_paths);
            try ownEffectPathTexts(a, eff.written_paths);
        }

        const owned_key = self.gpa.dupe(u8, key) catch return eff;
        self.cross_file_fields.put(self.gpa, owned_key, eff) catch self.gpa.free(owned_key);
        return eff;
    }

    /// True iff any method on the file's type `type_name` has a
    /// body that allocates a heap instance of the type itself
    /// (`<x>.create(<type_name>)` or `<x>.create(Self)`).
    ///
    /// Composes FileModel + summaryOfFn — runs FnSummary inference
    /// across the type's methods, short-circuits on first hit.
    /// True iff `type_name`'s body declares a method named
    /// `method_name`.  Thin wrapper over FileModel.findType +
    /// TypeInfo.hasMethod for callers that only hold a FileCache
    /// (no direct model).
    pub fn typeHasMethod(
        self: *FileCache,
        type_name: []const u8,
        method_name: []const u8,
    ) !bool {
        const model = try self.fileModel();
        const ti = model.findType(type_name) orelse return false;
        return ti.hasMethod(method_name);
    }

    /// Signedness + bit-width of the integer-typed expression spanning exactly
    /// [start_tok, end_tok] (e.g. a `-` operand).  Null when the type engine is
    /// unavailable, no node matches the span, or the type isn't an integer.
    pub fn intInfoOfExpr(
        self: *FileCache,
        start_tok: Ast.TokenIndex,
        end_tok: Ast.TokenIndex,
    ) ?zls_resolver_mod.TypeResolver.IntInfo {
        const zls = self.zls orelse return null;
        const tree = self.tree;
        const main_toks = tree.nodes.items(.main_token);
        var idx: u32 = 1;
        while (idx < tree.nodes.len) : (idx += 1) {
            const mt = main_toks[idx];
            if (mt < start_tok or mt > end_tok) continue;
            const node: Ast.Node.Index = @enumFromInt(idx);
            if (tree.firstToken(node) != start_tok or tree.lastToken(node) != end_tok) continue;
            return zls.intInfo(node) catch null;
        }
        return null;
    }

    pub fn anyMethodAllocatesSelf(
        self: *FileCache,
        type_name: []const u8,
    ) !bool {
        const model = try self.fileModel();
        const ti = model.findType(type_name) orelse return false;
        for (ti.methods) |m| {
            const s = try self.summaryOfFn(m.fn_decl);
            if (s.heap_allocates_self) return true;
        }
        return false;
    }

    /// For the named receiver param in `proto`, determine whether its
    /// declared type (in this file) has any method that self-destructs —
    /// i.e. `takes_ownership_of == 0` (calls `.destroy(this)` /
    /// `.free(self)` etc. on the receiver itself).
    ///
    /// Returns:
    ///   null  — type name unresolvable or declared outside this file;
    ///           caller should be conservative (don't suppress).
    ///   true  — type IS locally declared AND has a self-freeing method.
    ///   false — type IS locally declared AND has NO self-freeing method
    ///           (safe to suppress publish-then-touch-self findings).
    pub fn receiverTypeHasSelfDestructor(
        self: *FileCache,
        proto: Ast.full.FnProto,
        param_name: []const u8,
    ) !?bool {
        const idx = paramIndexFor(self.tree, proto, param_name) orelse return null;
        const type_name = (try self.paramContainerName(proto, idx)) orelse return null;
        const model = try self.fileModel();
        const ti = model.findType(type_name) orelse return null;
        for (ti.methods) |m| {
            const s = try self.summaryOfFn(m.fn_decl);
            if (s.takes_ownership_of) |tidx| {
                if (tidx == 0) return true;
            }
        }
        return false;
    }

    // ── Queries that live in a sibling and borrow this cache ─────────
    //
    // Each of these asks a question whose LOGIC belongs to the module
    // named, not to the cache that holds the per-file state.  They are
    // here so a consumer holding only a `FileCache` can ask without
    // re-deriving which module owns the answer — and so the cache stays
    // the one thing every module reads.

    /// The canonical record of the call at `token`: what it reaches, the
    /// summary of the body it reaches, its receiver's argument offset,
    /// and the whole-body read-only verdict a demand query has already
    /// folded.  A null verdict means the fold has not run, NOT that the
    /// body writes nothing.
    pub fn actualCallSummaryAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        frame: ?TypeResolver.ResolutionFrame,
    ) call_summary_mod.Error!?call_summary_mod.ActualCallSummary {
        return call_summary_mod.actualCallSummaryAt(self, token, frame);
    }

    /// What the call at `token` does to the storage `selection` names —
    /// storage rooted at a formal of the callee and a path from it, or
    /// the storage the call reaches that no formal names.
    ///
    /// `context` carries the caller's own contextual view and, when this
    /// runs inside another query, that query's counter, so the whole
    /// recursive walk spends one allowance.  A root call passes `.{}`.
    pub fn callEffectAt(
        self: *FileCache,
        token: Ast.TokenIndex,
        selection: call_summary_mod.EffectSelection,
        context: call_summary_mod.QueryContext,
    ) call_summary_mod.Error!?call_summary_mod.Effect {
        return call_summary_mod.callEffectAt(self, token, selection, context);
    }

    /// Does the initializer `claim` name provably build storage this
    /// expression laid out, rather than hand back a header somebody else
    /// is holding?  Refused for an unknown identity or provenance.
    pub fn provesFreshStorage(
        self: *FileCache,
        claim: fn_summary.FreshClaim,
        remaining: ?*u32,
    ) SummaryError!bool {
        return fresh_storage_mod.provesFreshStorage(self, claim, remaining);
    }

    /// The body this cache owns that reads declarations of `handle`,
    /// opened once per document and released only by the root cache that
    /// owns the grow state it shares.
    pub fn sourceDocument(
        self: *FileCache,
        handle: engine.DocumentStore.Handle,
    ) OpenError!*grow_analysis_mod.SourceDocument {
        return grow_analysis_mod.sourceDocument(self, handle, self.zls.?.ctx);
    }

    /// The grow state this root cache shares with every document it
    /// opens, created on first use.
    pub fn growStateAlloc(self: *FileCache) error{OutOfMemory}!*grow_analysis_mod.GrowState {
        return grow_analysis_mod.growStateAlloc(self);
    }

    // ── Type queries ─────────────────────────────────────────────────

    /// Signedness + bit-width of the integer type `node` is COERCED to
    /// when it has no type of its own — a conversion such as `@intCast(x)`
    /// takes the type of the context it is written in, so a cast in
    /// argument position is read against the parameter it is passed as
    /// rather than against itself.  Null when the type engine is
    /// unavailable or could not answer.
    pub fn coercedIntInfoOf(
        self: *FileCache,
        node: Ast.Node.Index,
    ) ?zls_resolver_mod.TypeResolver.IntInfo {
        const z = self.zls orelse return null;
        return z.contextIntInfo(node) catch null;
    }

    /// True when the expression spanning exactly `[start_tok, end_tok]`
    /// resolves to an enum type, false when it resolves to something
    /// that is not one, and null when the type engine could not answer
    /// at all — an unresolved expression is not a proved non-enum.
    pub fn isEnumTypeOfExpr(
        self: *FileCache,
        start_tok: Ast.TokenIndex,
        end_tok: Ast.TokenIndex,
    ) ?bool {
        const zls = self.zls orelse return null;
        const node = self.nodeForExactSpan(start_tok, end_tok) orelse return null;
        return zls.isEnumType(node) catch null;
    }

    /// The name of the `index`-th formal of `proto`, borrowed from the
    /// source.  Null when the parameter does not exist.
    pub fn paramNameFor(
        self: *FileCache,
        proto: Ast.full.FnProto,
        index: u32,
    ) ?[]const u8 {
        var position: u32 = 0;
        var it = proto.iterate(self.tree);
        while (it.next()) |param| : (position += 1) {
            if (position != index) continue;
            const name_token = param.name_token orelse return null;
            return self.tree.tokenSlice(name_token);
        }
        return null;
    }

    /// Legacy facts of the exact instantiated declaration, without demanding
    /// cleanup outcomes. Outcome consumers use summaryOfResolvedMethod.
    pub fn summaryOfResolvedDeclaration(
        self: *FileCache,
        callee: ActualCallee,
    ) SummaryError!?fn_summary.FnSummary {
        const origin = self.cleanup_origin orelse self;
        const key = resolvedCleanupKey(callee.reference, callee.declaration);
        if (origin.resolved_declarations.get(key)) |summary| return summary;
        if (origin.resolved_declaration_visiting.contains(key)) return null;
        const record: ActualCallSummary = .{
            .callee = callee,
            .summary = null,
            .argument_offset = null,
            .read_only = null,
        };
        const declaring = (try record.declaringCache(self)) orelse return null;
        const resolver = if (callee.caller_frame) |frame| frame.resolver else self.zls orelse return null;
        return origin.contextualDeclarationSummary(declaring, resolver, callee.reference, callee.declaration);
    }

    fn contextualDeclarationSummary(
        self: *FileCache,
        declaring: *FileCache,
        resolver: *TypeResolver,
        reference: TypeResolver.FunctionReference,
        declaration: Ast.Node.Index,
    ) SummaryError!?fn_summary.FnSummary {
        const key = resolvedCleanupKey(reference, declaration);
        if (self.resolved_declarations.get(key)) |summary| return summary;
        if (self.resolved_declaration_visiting.contains(key)) return null;
        const body = tokens.bodyOf(reference.tree, declaration) orelse return null;
        try self.resolved_declaration_visiting.put(self.gpa, key, {});
        defer _ = self.resolved_declaration_visiting.remove(key);
        const saved_frame = declaring.cleanup_frame;
        const saved_origin = declaring.cleanup_origin;
        declaring.cleanup_frame = resolver.frameForFunction(reference);
        declaring.cleanup_origin = self;
        defer declaring.cleanup_frame = saved_frame;
        defer declaring.cleanup_origin = saved_origin;
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        const arena = self.summary_arena.?.allocator();
        if (declaring.failed_roots.get(@intFromEnum(body))) |recorded| return reraiseRootFailure(recorded);
        const local = declaring.summaries.get(@intFromEnum(body));
        var summary = if (local != null and local.?._resolved) cloned: {
            // These exits belong to the default declaration frame, not this
            // actual call. Drop them before cloning their dead payloads.
            var metadata = local.?;
            setCleanupOutcomes(&metadata, .{});
            try declaring.chargeCleanupStorageClone(metadata, declaring.tree, body);
            break :cloned try cloneFnSummary(arena, metadata);
        } else (try self.summaryOfDeclaration(.{
            .tree = reference.tree,
            .module = reference.handle.module,
            .fn_decl = declaration,
        })) orelse return null;
        // A declaration's default frame cannot authenticate this call's exits.
        setCleanupOutcomes(&summary, .{});
        const model = try declaring.fileModel();
        const containing_type: ?[]const u8 = if (model.containingTypeOf(declaration)) |owner| owner.name else null;
        summary.heap_allocates_self = try fn_summary.inferHeapAllocatesSelf(declaring, body, containing_type);
        summary._resolved = true;
        try self.resolved_declarations.put(self.gpa, key, summary);
        return summary;
    }

    /// A summary of the exact instantiated declaration reached by one call.
    /// Foreign payloads are cloned into this receiving cache's arena before
    /// publication. A cycle publishes no partial positive certificate.
    pub fn summaryOfResolvedMethod(
        self: *FileCache,
        callee: ActualCallee,
    ) SummaryError!?fn_summary.FnSummary {
        return self.resolvedMethodCleanup(callee, .all);
    }

    fn resolvedMethodCleanup(
        self: *FileCache,
        callee: ActualCallee,
        demand: CleanupDemand,
    ) SummaryError!?fn_summary.FnSummary {
        const origin = self.cleanup_origin orelse self;
        var key = resolvedCleanupKey(callee.reference, callee.declaration);
        key.demand = demand;
        if (origin.cleanup_summaries.get(key)) |summary| {
            cleanupProbeHit(key, false);
            return summary;
        }
        if (origin.cleanup_visiting.contains(key)) {
            cleanupProbeHit(key, true);
            return null;
        }
        self.beginNormalCleanup();
        defer self.endNormalCleanup();
        const saved_probe_edge = cleanup_probe_edge;
        cleanup_probe_edge = .{ .key = CleanupProbeKey.init(key), .kind = .call };
        cleanup_probe_edge.?.owner_count = cleanup_probe_owner_count;
        const probe_owner_count = @min(cleanup_probe_owner_count, cleanup_probe_owners.len);
        @memcpy(cleanup_probe_edge.?.owners[0..probe_owner_count], cleanup_probe_owners[0..probe_owner_count]);
        defer cleanup_probe_edge = saved_probe_edge;
        try self.enterNormalCleanup(callee.call_node);
        defer self.leaveNormalCleanup();
        // Only the interprocedural entry owns this edge; AST children record
        // their installed caller frame rather than inheriting a false call.
        cleanup_probe_edge = null;
        // A value-only handover carries no owned allocation into this body.
        // Its declaration facts remain available, but its global/opaque
        // behavior remains UNKNOWN rather than an empty purity certificate.
        if (demand == .all and !try self.cleanupCallCanOwn(callee))
            return self.summaryOfResolvedDeclaration(callee);
        const record: ActualCallSummary = .{
            .callee = callee,
            .summary = null,
            .argument_offset = null,
            .read_only = null,
        };
        const declaring = (try record.declaringCache(self)) orelse return null;
        cleanup_probe_stack[cleanup_budget.depth - 1].edge.?.declaring = declaring;
        const resolver = if (callee.caller_frame) |frame| frame.resolver else self.zls orelse return null;
        return origin.contextualCleanupSummary(declaring, resolver, callee.reference, callee.declaration, demand);
    }

    fn contextualCleanupSummary(
        self: *FileCache,
        declaring: *FileCache,
        resolver: *TypeResolver,
        reference: TypeResolver.FunctionReference,
        declaration: Ast.Node.Index,
        demand: CleanupDemand,
    ) SummaryError!?fn_summary.FnSummary {
        const body = tokens.bodyOf(reference.tree, declaration) orelse return null;
        var key = resolvedCleanupKey(reference, declaration);
        key.demand = demand;
        if (self.cleanup_summaries.get(key)) |summary| {
            cleanupProbeHit(key, false);
            return summary;
        }
        if (self.cleanup_visiting.contains(key)) {
            cleanupProbeHit(key, true);
            return null;
        }
        try self.cleanup_visiting.put(self.gpa, key, {});
        defer _ = self.cleanup_visiting.remove(key);
        const saved_frame = declaring.cleanup_frame;
        const saved_origin = declaring.cleanup_origin;
        const saved_demand = declaring.cleanup_demand;
        declaring.cleanup_frame = resolver.frameForFunction(reference);
        declaring.cleanup_origin = self;
        declaring.cleanup_demand = demand;
        defer declaring.cleanup_frame = saved_frame;
        defer declaring.cleanup_origin = saved_origin;
        defer declaring.cleanup_demand = saved_demand;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(reference.tree, &proto_buffer, declaration) orelse return null;
        var summary = (try self.contextualDeclarationSummary(declaring, resolver, reference, declaration)) orelse return null;
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        const arena = self.summary_arena.?.allocator();
        const bindings = (try declaring.localBindings(proto, body)).*;
        const outcomes = try fn_summary.inferNormalSuccessCleanup(declaring, arena, proto, &bindings, body);
        setCleanupOutcomes(&summary, outcomes);
        if (demand == .many) key.demand = .{ .many = try arena.dupe(u32, demand.many) };
        try self.cleanup_summaries.put(self.gpa, key, summary);
        return summary;
    }

    /// Declaration-only legacy facts. With no actual call frame this query
    /// cannot establish contextual normal/error cleanup or retained ownership.
    fn summaryOfDeclaration(self: *FileCache, declared: ResolvedFnDecl) SummaryError!?fn_summary.FnSummary {
        if (declared.tree.errors.len != 0) return error.InvalidSyntax;
        _ = try fn_summary.checkedTokenCount(declared.tree.source.len, declared.tree.tokens.len);
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(declared.tree, &buffer, declared.fn_decl) orelse return null;
        const body = tokens.bodyOf(declared.tree, declared.fn_decl) orelse return null;
        var summary = fn_summary.inferFromBody(declared.tree, proto, body);
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        const arena = self.summary_arena.?.allocator();
        const bindings = try local_bindings.build(arena, declared.tree, proto, body);
        summary.may_free_fields = try fn_summary.inferMayFreeFields(arena, declared.tree, proto, body);
        summary.result_heap_fields = try fn_summary.inferResultHeapFields(arena, declared.tree, body);
        const fields = try fn_summary.inferFieldEffects(arena, declared.tree, proto, &bindings, body);
        summary.freed_paths = fields.freed_paths;
        summary.written_paths = fields.written_paths;
        // Growth and new cleanup outcomes retain their UNKNOWN defaults.
        setCleanupOutcomes(&summary, .{});
        const charge_cache = cleanup_budget.initiating_cache orelse self;
        const charge_node = cleanup_budget.initiating_node orelse @as(Ast.Node.Index, @enumFromInt(0));
        const charge_tree = cleanup_budget.initiating_tree orelse self.tree;
        try charge_cache.chargeCleanupStorageClone(summary, charge_tree, charge_node);
        return try cloneFnSummary(arena, summary);
    }

    /// The FnSummary for `<qualifier>.<name>` where `qualifier` names a
    /// module-level declaration of THIS file.  Used for a qualified call
    /// whose receiver names no container type, so the method-name route
    /// cannot be taken — the name must reach the module it actually
    /// imports before it means anything.
    pub fn summaryByQualifiedName(
        self: *FileCache,
        qualifier: []const u8,
        name: []const u8,
    ) SummaryError!?fn_summary.FnSummary {
        // The qualifier is resolved to the module it REALLY imports, and
        // the name is read from the tree that module was parsed from —
        // never from the spelling, which is all the call site wrote.
        const module_tree = (try self.qualifierModule(qualifier)) orelse return null;
        if (module_tree == self.tree) {
            const summary = (try self.summaryByName(name)) orelse return null;
            return summary.*;
        }
        const declared = moduleFnDecl(module_tree, name, .unscoped) orelse return null;
        return self.summaryOfDeclaration(declared);
    }

    /// The tree a call qualifier's module really declares, opened through
    /// the same project cache every other cross-file read goes through,
    /// or null when the qualifier names no `@import` declaration of this
    /// file or the module it names is not one this session can read.
    ///
    /// Null is not a clean bill of health: a qualifier this file does not
    /// bind, and a module this project cannot reach, both leave the callee
    /// unreadable, and the caller charges that.
    pub fn qualifierModule(self: *FileCache, qualifier: []const u8) !?*const Ast {
        const entry = (try self.rootConsts()).get(qualifier) orelse return null;
        const import_node = entry orelse return null;
        const pc = self.project orelse return null;
        const first = self.tree.firstToken(import_node);
        const last = self.tree.lastToken(import_node);
        const literal = tokens.importLiteralFromTokens(self.tree, first, last) orelse return null;
        const model = if (project_cache_mod.isRelativeImport(literal))
            pc.modelForRelativeImport(self.file_path, literal) catch return null
        else
            pc.modelForModuleImport(self.file_path, literal) catch null;
        return if (model) |found| found.tree else null;
    }

    // ── Escape analysis ──────────────────────────────────────────────

    /// This body's escape index: which roots it takes the address of, and
    /// what it writes to which name.  Built once per body and owned for
    /// the snapshot's lifetime, so every walk of that body — the first
    /// and every child query — reads one table instead of re-walking the
    /// file's node array.
    ///
    /// A root here is the name an `&` operand BELONGS to, reached by
    /// the same `tokens.rootIdentifier` `addressUseAt` keys on, so the
    /// two readers agree on whose address a node takes.  They answer
    /// different questions and so differ on `_ = &x`: that address
    /// escapes nothing, so it is not a root here, while it is still an
    /// address `addressUseAt` reports — with `may_write` false, since
    /// discarding an address stores nothing.
    ///
    /// The roots are collected before the targets: a plain assignment to
    /// a name can only FOLLOW the declaration that binds it, so by the
    /// time a write is read the root set already holds exactly the entries
    /// an earlier pass would have finished adding — while the targets,
    /// which each depend on the bindings recorded before them, keep the
    /// order the source wrote them in.
    pub fn escapeRoots(self: *FileCache, body: Ast.Node.Index) error{OutOfMemory}!*const EscapeRootIndex {
        const key = @intFromEnum(body);
        if (self.escape_roots.get(key)) |borrowed| return borrowed;
        const tree = self.tree;
        const first = tree.firstToken(body);
        const last = tree.lastToken(body);
        var addressed: std.ArrayListUnmanaged([]const u8) = .empty;
        errdefer addressed.deinit(self.gpa);
        var writes: std.ArrayListUnmanaged(EscapeWrite) = .empty;
        errdefer writes.deinit(self.gpa);
        // Sparse, so nothing is pre-sized: the lists grow to what the
        // body actually holds of these tags.
        var statement_buf: [2]Ast.Node.Index = undefined;
        const statements = bodyStatements(tree, body, &statement_buf);
        var cursor: usize = 0;
        for (tree.nodes.items(.tag), 0..) |tag, raw_node| {
            const node: Ast.Node.Index = @enumFromInt(raw_node);
            if (!numeric_nodes.isIndexedTag(tag)) continue;
            const node_first = tree.firstToken(node);
            if (node_first < first or tree.lastToken(node) > last) continue;
            while (cursor < statements.len and @intFromEnum(statements[cursor]) < @intFromEnum(node)) cursor += 1;
            const unconditional = cursor < statements.len and statements[cursor] == node;
            switch (tag) {
                .address_of => {
                    if (addressIsDiscarded(tree, node)) continue;
                    const root = tokens.rootIdentifier(tree, tree.nodeData(node).node) orelse continue;
                    try addressed.append(self.gpa, tree.tokenSlice(tree.nodeMainToken(root)));
                },
                .simple_var_decl, .local_var_decl, .aligned_var_decl => {
                    const decl = tree.fullVarDecl(node) orelse continue;
                    const init_node = decl.ast.init_node.unwrap() orelse identifierNodeAt(tree, decl.ast.mut_token + 1);
                    if (init_node == null) continue;
                    try writes.append(self.gpa, .{
                        .name = tree.tokenSlice(decl.ast.mut_token + 1),
                        .type_node = decl.ast.type_node.unwrap(),
                        .init = init_node.?,
                        .token = node_first,
                        .unconditional = unconditional,
                        .declares = true,
                    });
                },
                .assign => {
                    const data = tree.nodeData(node).node_and_node;
                    if (tree.nodeTag(data[0]) != .identifier) continue;
                    try writes.append(self.gpa, .{
                        .name = tree.tokenSlice(tree.nodeMainToken(data[0])),
                        .type_node = null,
                        .init = data[1],
                        .token = node_first,
                        .unconditional = unconditional,
                        .declares = false,
                    });
                },
                else => {},
            }
        }
        const owned = try self.gpa.create(EscapeRootIndex);
        errdefer self.gpa.destroy(owned);
        owned.addressed = addressed.toOwnedSlice(self.gpa) catch |err| return err;
        owned.writes = writes.toOwnedSlice(self.gpa) catch |err| return err;
        try self.escape_roots.put(self.gpa, key, owned);
        return owned;
    }

    /// True iff any function (top-level or method) in this file
    /// DIRECTLY calls `.destroy(param0)` or `.free(param0)` —
    /// i.e. inferDirectTakes returns 0 for its body.
    ///
    /// Deliberately bypasses the cached summaries (which may carry
    /// transitive takes_ownership_of from resolveTransitiveTakes) to
    /// check only for literal single-hop self-destruction.
    ///
    /// Used as a file-level fallback when the receiver type can't be
    /// resolved (file-level struct, or `this` bound via `@fieldParentPtr`
    /// rather than as a direct parameter): if NO function in the whole
    /// file directly self-destructs its first param, nothing in the
    /// file is individually heap-managed, so publish-then-touch-self
    /// findings are safe to suppress.
    pub fn fileHasDirectSelfDestructor(self: *FileCache) !bool {
        const model = try self.fileModel();
        var buf: [1]Ast.Node.Index = undefined;

        for (model.fns) |fi| {
            const proto = tokens.fnProto(self.tree, &buf, fi.fn_decl) orelse continue;
            const body = tokens.bodyOf(self.tree, fi.fn_decl) orelse continue;
            if (fn_summary.inferDirectTakes(self.tree, proto, body)) |idx| {
                if (idx == 0) return true;
            }
        }
        for (model.types) |ti| {
            for (ti.methods) |m| {
                const proto = tokens.fnProto(self.tree, &buf, m.fn_decl) orelse continue;
                const body = tokens.bodyOf(self.tree, m.fn_decl) orelse continue;
                if (fn_summary.inferDirectTakes(self.tree, proto, body)) |idx| {
                    if (idx == 0) return true;
                }
            }
        }
        return false;
    }

    pub fn beginNormalCleanup(self: *FileCache) void {
        if (cleanup_budget.queries == 0) {
            cleanup_budget = .{};
            call_summary_mod.openScope(self);
        }
        cleanup_budget.queries += 1;
    }

    pub fn endNormalCleanup(self: *FileCache) void {
        std.debug.assert(cleanup_budget.queries != 0);
        cleanup_budget.queries -= 1;
        if (cleanup_budget.queries == 0) call_summary_mod.closeScope(self);
    }

    pub fn enterNormalCleanup(self: *FileCache, node: Ast.Node.Index) SummaryError!void {
        return self.enterNormalCleanupAt(self.tree, node);
    }

    fn enterNormalCleanupAt(self: *FileCache, tree: *const Ast, node: Ast.Node.Index) SummaryError!void {
        if (cleanup_budget.initiating_cache == null) {
            cleanup_budget.initiating_cache = self;
            cleanup_budget.initiating_node = node;
            cleanup_budget.initiating_tree = tree;
        }
        if (cleanup_budget.depth == 64) return self.cleanupBudgetFailureAt(tree, .normal_cleanup_depth, 64, node);
        cleanup_probe_stack[cleanup_budget.depth] = cleanupProbeRow(self, node);
        cleanup_probe_stack[cleanup_budget.depth].tree = tree;
        cleanup_budget.depth += 1;
    }

    pub fn leaveNormalCleanup(_: *FileCache) void {
        std.debug.assert(cleanup_budget.depth != 0);
        cleanup_budget.depth -= 1;
    }

    pub fn chargeNormalCleanup(self: *FileCache, node: Ast.Node.Index) SummaryError!void {
        return self.chargeNormalCleanupAt(self.tree, node);
    }

    /// Source scans can visit admitted declarations outside this cache.
    /// The budget is shared, but each node keeps its owning document.
    pub fn chargeNormalCleanupAt(self: *FileCache, tree: *const Ast, node: Ast.Node.Index) SummaryError!void {
        if (cleanup_budget.remaining == 0)
            return self.cleanupBudgetFailureAt(tree, .normal_cleanup_nodes, 50_000, node);
        cleanup_budget.remaining -= 1;
    }

    /// Charge alternative copies and products before allocating their state.
    pub fn normalCleanupStorageWork(self: *FileCache, node: Ast.Node.Index, units: usize) SummaryError!void {
        return self.normalCleanupStorageWorkAt(self.tree, node, units);
    }

    fn normalCleanupStorageWorkAt(self: *FileCache, tree: *const Ast, node: Ast.Node.Index, units: usize) SummaryError!void {
        if (units > cleanup_budget.remaining)
            return self.cleanupBudgetFailureAt(tree, .normal_cleanup_nodes, 50_000, node);
        cleanup_budget.remaining -= @intCast(units);
    }

    /// Production clone callers preflight before any summary allocation.
    /// Ordinary declaration clones outside cleanup do not spend this scope.
    fn chargeCleanupStorageClone(self: *FileCache, summary: fn_summary.FnSummary, tree: *const Ast, node: Ast.Node.Index) SummaryError!void {
        if (cleanup_budget.queries == 0) return;
        inline for (.{ "normal_success_storage_outcomes", "error_storage_outcomes" }) |name| {
            const outcomes = @field(summary, name);
            try self.normalCleanupStorageWorkAt(tree, node, outcomes.len);
            for (outcomes) |outcome| {
                try self.normalCleanupStorageWorkAt(tree, node, outcome.operations.len);
                for (outcome.operations) |operation| {
                    try self.normalCleanupStorageWorkAt(tree, node, operation.path.path.len);
                    if (operation.allocator) |allocator|
                        try self.normalCleanupStorageWorkAt(tree, node, allocator.path.len);
                }
            }
        }
    }

    fn cleanupBudgetFailure(self: *FileCache, limit: budget_mod.Limit, cap: u32, node: Ast.Node.Index) budget_mod.BudgetError {
        return self.cleanupBudgetFailureAt(self.tree, limit, cap, node);
    }

    fn cleanupBudgetFailureAt(self: *FileCache, tree: *const Ast, limit: budget_mod.Limit, cap: u32, node: Ast.Node.Index) budget_mod.BudgetError {
        if (replay_failure_site == null) replay_failure_site = .{ .tree = tree, .node = node };
        cleanupProbeFailure(self, tree, node, limit);
        if (cleanup_budget.initiating_cache) |origin| {
            const initiating_tree = cleanup_budget.initiating_tree.?;
            if (origin != self or initiating_tree != tree or cleanup_budget.initiating_node.? != node)
                return origin.cleanupBudgetFailureAt(initiating_tree, limit, cap, cleanup_budget.initiating_node.?);
        }
        const token = tree.nodeMainToken(node);
        const byte = tree.tokens.items(.start)[token];
        const lc = budget_mod.lineCol(tree.source, byte);
        var name: budget_mod.NameBuf = .{};
        if (self.enclosingFunctionAt(tree, token)) |declaration| {
            var buffer: [1]Ast.Node.Index = undefined;
            if (tokens.fnProto(tree, &buffer, declaration)) |proto| {
                if (proto.name_token) |name_token| name.set(tree.tokenSlice(name_token));
            }
        }
        return budget_mod.fail(.{
            .limit = limit,
            .limit_value = cap,
            .reached = cap,
            .byte = byte,
            .document = budget_mod.documentForTree(tree),
            .line = lc.line,
            .column = lc.column,
            .function = name,
        });
    }

    pub fn normalCleanupReturnKind(self: *FileCache, node: Ast.Node.Index) SummaryError!?bool {
        if (self.tree.nodeTag(node) == .error_value) return true;
        const frame = self.cleanup_frame orelse (self.zls orelse return null).resolutionFrame();
        const ty = (try frame.typeOfNode(node)) orelse return null;
        const tag = frame.resolver.typeTag(ty) orelse return null;
        return switch (tag) {
            .error_set => true,
            .error_union => null,
            else => false,
        };
    }

    pub fn normalCleanupCondition(self: *FileCache, node: Ast.Node.Index) SummaryError!?bool {
        const frame = self.cleanup_frame orelse (self.zls orelse return null).resolutionFrame();
        return frame.boolValueOfNode(node);
    }

    /// Cleanup versions require a canonical new backing allocation, not an
    /// independent provider lifetime. Replay retains the allocator provenance.
    pub fn normalCleanupFresh(self: *FileCache, node: Ast.Node.Index) SummaryError!bool {
        return (try self.cleanupFreshAllocatorNode(node)) != null;
    }

    /// Empty syntax proves a descriptor value only in its actual slice type.
    pub fn normalCleanupStaticEmpty(self: *FileCache, lhs: Ast.Node.Index, rhs: Ast.Node.Index) SummaryError!bool {
        try self.normalCleanupStorageWork(rhs, @as(usize, self.tree.lastToken(rhs) - self.tree.firstToken(rhs)) + 1);
        if (!fn_summary.isStaticEmptyDescriptor(self.tree, rhs)) return false;
        const frame = self.cleanup_frame orelse (self.zls orelse return false).resolutionFrame();
        const ty = (try frame.typeOfNode(lhs)) orelse return false;
        const pointer = cleanupPointerTraits(frame.resolver, ty) orelse return false;
        return pointer.size == .slice and !pointer.has_sentinel;
    }

    fn cleanupPointerTraits(resolver: *TypeResolver, ty: TypeResolver.ActualType) ?struct {
        size: std.builtin.Type.Pointer.Size,
        has_sentinel: bool,
    } {
        return switch (ty.data) {
            .pointer => |info| .{ .size = info.size, .has_sentinel = info.sentinel != .none },
            .ip_index => switch (resolver.ctx.ip.indexToKey(ty.ipIndex() orelse return null)) {
                .pointer_type => |info| .{ .size = info.flags.size, .has_sentinel = info.sentinel != .none },
                else => null,
            },
            else => null,
        };
    }

    /// Identify the allocation's allocator in this function's formal paths.
    /// A copied local allocator can carry an earlier field value, so refuse
    /// that projection rather than authenticate the current field instead.
    pub fn normalCleanupAllocator(self: *FileCache, node: Ast.Node.Index) SummaryError!?fn_summary.ParamPath {
        const allocator = (try self.cleanupFreshAllocatorNode(node)) orelse return null;
        const token = self.tree.firstToken(allocator);
        const declaration = self.enclosingFunctionAt(self.tree, token) orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &buffer, declaration) orelse return null;
        const body = tokens.bodyOf(self.tree, declaration) orelse return null;
        const bindings = (try self.localBindings(proto, body)).*;
        if (!try self.cleanupDirectFormal(&bindings, allocator)) return null;
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        try self.normalCleanupStorageWork(allocator, bindings.items.len);
        const owner = try fn_summary.ownerOfExpr(self.summary_arena.?.allocator(), self.tree, proto, &bindings, token, self.tree.lastToken(allocator), 0);
        return if (owner == .param) owner.param else null;
    }

    fn cleanupDirectFormal(self: *FileCache, bindings: *const local_bindings.LocalBindings, node: Ast.Node.Index) SummaryError!bool {
        var first = self.tree.firstToken(node);
        const last = self.tree.lastToken(node);
        try self.normalCleanupStorageWork(node, @as(usize, last - first) + 1);
        while (first <= last and (self.tree.tokenTag(first) == .ampersand or
            self.tree.tokenTag(first) == .keyword_try)) first += 1;
        if (first > last or self.tree.tokenTag(first) != .identifier) return false;
        try self.normalCleanupStorageWork(node, bindings.items.len);
        const binding = bindings.findAt(self.tree.tokenSlice(first), first) orelse return false;
        return binding.origin == .param;
    }

    fn cleanupFreshAllocatorNode(self: *FileCache, node: Ast.Node.Index) SummaryError!?Ast.Node.Index {
        const frame = self.cleanup_frame orelse (self.zls orelse return null).resolutionFrame();
        var expression = node;
        while (true) {
            try self.chargeNormalCleanup(expression);
            switch (self.tree.nodeTag(expression)) {
                .@"try" => {
                    expression = self.tree.nodeData(expression).node;
                    continue;
                },
                .grouped_expression => {
                    expression = self.tree.nodeData(expression).node_and_token[0];
                    continue;
                },
                .identifier => {
                    const token = self.tree.nodeMainToken(expression);
                    const declaration = self.enclosingFunctionAt(self.tree, token) orelse return null;
                    var proto_buffer: [1]Ast.Node.Index = undefined;
                    const proto = tokens.fnProto(self.tree, &proto_buffer, declaration) orelse return null;
                    const body = tokens.bodyOf(self.tree, declaration) orelse return null;
                    const bindings = (try self.localBindings(proto, body)).*;
                    try self.normalCleanupStorageWork(expression, bindings.items.len);
                    const binding = bindings.findAt(self.tree.tokenSlice(token), token) orelse return null;
                    if (!binding.is_const or binding.origin == .param or binding.origin == .loop_capture or
                        binding.rhs_first >= token) return null;
                    expression = self.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return null;
                    continue;
                },
                else => {},
            }
            var call_buffer: [1]Ast.Node.Index = undefined;
            const call = self.tree.fullCall(&call_buffer, expression) orelse return null;
            const actual = (try self.actualCallSummaryAt(fresh_storage_mod.calleeQueryToken(self.tree, call), frame)) orelse return null;
            const primitive = (try fresh_storage_mod.allocatorPrimitive(self, actual, .{
                .claim = .{ .first = self.tree.firstToken(expression), .last = self.tree.lastToken(expression) },
                .depth = 0,
                .remaining = &cleanup_budget.remaining,
                .frame = frame,
            })) orelse return null;
            if (primitive.operation != .allocate) return null;
            var receiver_buffer: [2]Ast.Node.Index = undefined;
            return actual.callArgumentFor(self, &receiver_buffer, primitive.allocator_parameter);
        }
    }

    fn cleanupCallCanOwn(self: *FileCache, callee: ActualCallee) SummaryError!bool {
        const frame = callee.caller_frame orelse (self.zls orelse return true).resolutionFrame();
        var buffer: [2]Ast.Node.Index = undefined;
        const arguments = (try frame.callArgumentsOf(&buffer, callee.call_node)) orelse return true;
        if (arguments.receiver) |receiver| {
            if (try self.cleanupParameterCanOwn(callee, frame, receiver, 0, true)) return true;
        }
        for (arguments.arguments, 0..) |argument, index| {
            const parameter: u32 = @intCast(index + @intFromBool(arguments.receiver != null));
            if (try self.cleanupParameterCanOwn(callee, frame, argument, parameter, false)) return true;
        }
        return false;
    }

    fn cleanupParameterCanOwn(
        self: *FileCache,
        callee: ActualCallee,
        frame: TypeResolver.ResolutionFrame,
        argument: Ast.Node.Index,
        parameter: u32,
        receiver: bool,
    ) SummaryError!bool {
        // Method coercion can address a field whose by-value type is scalar.
        // Only an actual by-value formal can discard that addressability.
        if (receiver) {
            const parameters = callee.reference.actual_type.data.function.parameters;
            if (parameter >= parameters.len) return true;
            const formal = (try frame.resolver.normalizedType(parameters[parameter].type)) orelse return true;
            if (frame.resolver.typeTag(formal) == .pointer) return true;
        }
        return self.cleanupArgumentCanOwn(frame, argument);
    }

    fn cleanupArgumentCanOwn(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        argument: Ast.Node.Index,
    ) SummaryError!bool {
        try self.enterNormalCleanup(argument);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanup(argument);
        const tree = &frame.handle.document.tree;
        switch (tree.nodeTag(argument)) {
            .char_literal, .number_literal, .enum_literal, .string_literal, .multiline_string_literal => return false,
            .grouped_expression => return self.cleanupArgumentCanOwn(frame, tree.nodeData(argument).node_and_token[0]),
            else => {},
        }
        // Literal tuple/array slots are the actual values handed over. The
        // aggregate's type may remain unresolved while its scalar leaves are
        // already known, so do not let that erase their by-value proof.
        var literal_buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullArrayInit(&literal_buffer, argument)) |literal| {
            if (literal.ast.type_expr == .none) {
                for (literal.ast.elements) |element| {
                    if (try self.cleanupArgumentCanOwn(frame, element)) return true;
                }
                return false;
            }
        }
        const ty = (try frame.typeOfNode(argument)) orelse return true;
        if (try self.cleanupTypeAddressFree(frame, ty, argument, 0)) return false;
        // A bound format string is static bytes, not caller-owned storage.
        if ((try frame.stringValueOfNode(argument)) != null) return false;
        return true;
    }

    fn cleanupTypeAddressFree(
        self: *FileCache,
        frame: TypeResolver.ResolutionFrame,
        ty: TypeResolver.ActualType,
        node: Ast.Node.Index,
        depth: u8,
    ) SummaryError!bool {
        if (depth > @import("../model/type_query.zig").max_element_depth) return false;
        try self.chargeNormalCleanup(node);
        const actual = (try frame.resolver.normalizedType(ty)) orelse return false;
        switch (actual.data) {
            .tuple => |elements| {
                for (elements) |element| {
                    if (!try self.cleanupTypeAddressFree(frame, element, node, depth + 1)) return false;
                }
                return true;
            },
            .array => |array| return self.cleanupTypeAddressFree(frame, array.elem_ty.*, node, depth + 1),
            .optional => |payload| return self.cleanupTypeAddressFree(frame, payload.*, node, depth + 1),
            .error_union => |value| return self.cleanupTypeAddressFree(frame, value.payload.*, node, depth + 1),
            else => {},
        }
        switch (frame.resolver.typeTag(actual) orelse return false) {
            .error_set, .noreturn, .type => return true,
            else => {},
        }
        return fresh_storage_mod.actualTypeAddressFree(frame, actual, depth, &cleanup_budget.remaining) catch |err| switch (err) {
            error.AnalysisBudgetExceeded => return self.cleanupBudgetFailure(.normal_cleanup_nodes, 50_000, node),
            else => return err,
        };
    }

    /// Authenticated effects of one call in its caller's formal coordinates.
    pub const NormalCleanupCall = struct {
        definite_paths: []const fn_summary.ParamPath = &.{},
        definite_fields: []const fn_summary.FieldFree = &.{},
        may_paths: []const fn_summary.ParamPath = &.{},
        may_fields: []const fn_summary.FieldFree = &.{},
        complete: bool = false,
        error_definite_paths: []const fn_summary.ParamPath = &.{},
        error_definite_fields: []const fn_summary.FieldFree = &.{},
        error_may_paths: []const fn_summary.ParamPath = &.{},
        error_may_fields: []const fn_summary.FieldFree = &.{},
        error_complete: bool = false,
        storage_outcomes: []const fn_summary.StorageOutcome = &.{},
        error_storage_outcomes: []const fn_summary.StorageOutcome = &.{},
        storage_complete: bool = false,
        error_storage_complete: bool = false,
        release_argument: ?Ast.Node.Index = null,
        /// Only canonical SDK free of a nonsentinel slice ignores zero length.
        sdk_empty_slice_noop: bool = false,
        can_normal: bool = true,
        can_error: bool = true,
        returns_error: ?bool = null,
    };

    pub fn normalCleanupCall(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        node: Ast.Node.Index,
    ) SummaryError!NormalCleanupCall {
        const tree = self.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse return .{};
        const token = call.queryToken(tree, node);
        const frame = self.cleanup_frame orelse (self.zls orelse return .{}).resolutionFrame();
        const resolver = frame.resolver;
        const callee = (try grow_analysis_mod.resolveActualCallee(self, token, frame)) orelse return .{};
        const actual: ActualCallSummary = .{
            .callee = callee,
            .summary = null,
            .argument_offset = null,
            .read_only = null,
        };
        const caller_frame = callee.caller_frame orelse frame;
        const result_type = (try caller_frame.typeOfNode(node)) orelse return .{};
        const result_tag = resolver.typeTag(result_type) orelse return .{};
        const can_normal = result_tag != .noreturn and result_tag != .error_set;
        const can_error = result_tag == .error_union or result_tag == .error_set;
        const returns_error: ?bool = if (result_tag == .error_union) null else result_tag == .error_set;
        const unknown: NormalCleanupCall = .{
            .can_normal = can_normal,
            .can_error = can_error,
            .returns_error = returns_error,
        };
        // A noreturn call has no normal or error exit on which cleanup can
        // hand storage back. Traversing its panic/abort implementation cannot
        // contribute to either certificate and needlessly follows dead exits.
        if (result_tag == .noreturn) return unknown;
        if (try resolver.declaredInToolchainFile(callee.handle, "/std/mem/Allocator.zig")) {
            var pbuf: [1]Ast.Node.Index = undefined;
            const declaration = tokens.fnProto(callee.tree, &pbuf, callee.declaration) orelse return unknown;
            const name = callee.tree.tokenSlice(declaration.name_token orelse return unknown);
            const is_free = std.mem.eql(u8, name, "free");
            const is_destroy = std.mem.eql(u8, name, "destroy");
            if (!is_free and !is_destroy) {
                const primitive = (try fresh_storage_mod.allocatorPrimitive(self, actual, .{
                    .claim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) },
                    .depth = 0,
                    .remaining = &cleanup_budget.remaining,
                    .frame = frame,
                })) orelse return unknown;
                if (primitive.operation != .allocate) return unknown;
                const receiver = (try actual.callArgumentFor(self, &buffer, primitive.allocator_parameter)) orelse return unknown;
                if ((try caller_frame.isStdAllocator(receiver)) != true) return unknown;
                // Allocation creates local storage. It neither releases nor
                // replaces a caller-owned version on either exit.
                var allocation = unknown;
                allocation.complete = true;
                allocation.error_complete = true;
                allocation.storage_complete = true;
                allocation.error_storage_complete = true;
                return allocation;
            }
            var parameters = declaration.iterate(callee.tree);
            _ = parameters.next() orelse return unknown;
            const memory = parameters.next() orelse return unknown;
            if (parameters.next() != null or memory.anytype_ellipsis3 == null) return unknown;
            const return_node = declaration.ast.return_type.unwrap() orelse return unknown;
            const declaration_frame = resolver.frameForFunction(callee.reference);
            const sdk_return_type = (try declaration_frame.typeOfNode(return_node)) orelse return unknown;
            if (resolver.typeTag(sdk_return_type) != .void) return unknown;
            const receiver = (try actual.callArgumentFor(self, &buffer, 0)) orelse return unknown;
            if ((try caller_frame.isStdAllocator(receiver)) != true) return unknown;
            const argument = (try actual.callArgumentFor(self, &buffer, 1)) orelse return unknown;
            const ty = (try caller_frame.typeOfNode(argument)) orelse return unknown;
            const expected: std.builtin.Type.Pointer.Size = if (is_free) .slice else .one;
            const pointer = cleanupPointerTraits(resolver, ty) orelse return unknown;
            if (pointer.size != expected) return unknown;
            const owner = try fn_summary.ownerOfExpr(arena, tree, proto, bindings, tree.firstToken(argument), tree.lastToken(argument), 0);
            var release = unknown;
            release.can_normal = true;
            release.can_error = false;
            release.returns_error = false;
            release.error_complete = true;
            release.storage_complete = true;
            release.error_storage_complete = true;
            release.release_argument = argument;
            release.sdk_empty_slice_noop = is_free and !pointer.has_sentinel;
            if (owner != .param or !self.cleanup_demand.contains(owner.param.param)) {
                release.complete = try self.normalCleanupFresh(argument);
                return release;
            }
            try self.normalCleanupStorageWork(node, 2);
            const paths = try arena.alloc(fn_summary.ParamPath, 1);
            paths[0] = owner.param;
            const operations = try arena.alloc(fn_summary.StorageOperation, 1);
            operations[0] = .{
                .path = owner.param,
                .kind = .release_current,
                .sdk_empty_slice_noop = release.sdk_empty_slice_noop,
            };
            const outcomes = try arena.alloc(fn_summary.StorageOutcome, 1);
            outcomes[0] = .{ .operations = operations };
            release.definite_paths = paths;
            release.may_paths = paths;
            release.complete = true;
            release.storage_outcomes = outcomes;
            return release;
        }
        // Demand only callee formals handed possible owned storage from the
        // caller's selected roots. Other formals, globals and opaque calls
        // stay incomplete; they do not seed unrelated ownership traversals.
        const arguments = (try caller_frame.callArgumentsOf(&buffer, node)) orelse return unknown;
        const count = arguments.arguments.len + @intFromBool(arguments.receiver != null);
        var selected_buffer: [16]u32 = undefined;
        var selected: []u32 = &selected_buffer;
        var selected_len: usize = 0;
        var read_only_count: usize = 0;
        const effect_context: call_summary_mod.QueryContext = .{
            .frame = caller_frame,
            .remaining = &cleanup_budget.remaining,
            .declaration = self.enclosingFunctionAt(tree, token),
        };
        const saved_probe_owners = cleanup_probe_owners;
        const saved_probe_owner_count = cleanup_probe_owner_count;
        cleanup_probe_owner_count = 0;
        defer cleanup_probe_owners = saved_probe_owners;
        defer cleanup_probe_owner_count = saved_probe_owner_count;
        for (0..count) |index| {
            const parameter: u32 = @intCast(index);
            const argument = (try actual.callArgumentFor(self, &buffer, parameter)) orelse return unknown;
            const owner = try fn_summary.ownerOfExpr(arena, tree, proto, bindings, tree.firstToken(argument), tree.lastToken(argument), 0);
            if (owner != .param or !self.cleanup_demand.contains(owner.param.param)) continue;
            const can_own = can_own: {
                var candidate_key = resolvedCleanupKey(callee.reference, callee.declaration);
                candidate_key.demand = .{ .one = parameter };
                const saved_edge = cleanup_probe_edge;
                cleanup_probe_edge = .{
                    .key = CleanupProbeKey.init(candidate_key),
                    .kind = .argument_check,
                    .owner_count = 1,
                };
                cleanup_probe_edge.?.owners[0] = CleanupProbeOwner.init(parameter, argument, owner.param);
                defer cleanup_probe_edge = saved_edge;
                break :can_own try self.cleanupParameterCanOwn(
                    callee,
                    caller_frame,
                    argument,
                    parameter,
                    arguments.receiver != null and index == 0,
                );
            };
            if (!can_own) continue;
            if (selected_len == selected.len) {
                const expanded = try arena.alloc(u32, count);
                @memcpy(expanded[0..selected_len], selected[0..selected_len]);
                selected = expanded;
            }
            selected[selected_len] = parameter;
            if (selected_len < cleanup_probe_owners.len) {
                cleanup_probe_owners[selected_len] = CleanupProbeOwner.init(parameter, argument, owner.param);
            }
            cleanup_probe_owner_count = selected_len + 1;
            selected_len += 1;
        }
        if (selected_len == 0) return unknown;
        var demand: CleanupDemand = if (selected_len == 1)
            .{ .one = selected[0] }
        else
            .{ .many = selected[0..selected_len] };
        const origin = self.cleanup_origin orelse self;
        var key = resolvedCleanupKey(callee.reference, callee.declaration);
        key.demand = demand;
        // A completed exact ownership demand already authenticates both exit
        // domains. Do not spend a general-effect walk before reusing it.
        if (origin.cleanup_summaries.get(key)) |summary| {
            cleanupProbeHit(key, false);
            return self.mapNormalCleanupSummary(arena, proto, bindings, actual, summary, unknown);
        }
        const candidate_len = selected_len;
        selected_len = 0;
        for (selected[0..candidate_len], 0..) |parameter, index| {
            // Address-bearing storage can own an allocation even when its
            // header is passed by value. Unknown/global reach still demands
            // the cleanup body; read-only is not a no-capture certificate.
            const effect = try self.callEffectAt(token, .{
                .parameter = .{ .param = parameter, .read_only_only = true },
            }, effect_context);
            if (effect == .read_only) {
                read_only_count += 1;
                continue;
            }
            selected[selected_len] = parameter;
            if (selected_len < cleanup_probe_owners.len and index < cleanup_probe_owners.len)
                cleanup_probe_owners[selected_len] = cleanup_probe_owners[index];
            selected_len += 1;
        }
        cleanup_probe_owner_count = selected_len;
        if (selected_len == 0) {
            if (count != 0 and read_only_count == count and
                try self.callEffectAt(token, .unrooted, effect_context) == .read_only)
            {
                var pure = unknown;
                pure.complete = true;
                pure.error_complete = true;
                pure.storage_complete = true;
                pure.error_storage_complete = true;
                return pure;
            }
            return unknown;
        }
        demand = if (selected_len == 1)
            .{ .one = selected[0] }
        else
            .{ .many = selected[0..selected_len] };
        const summary = (try self.resolvedMethodCleanup(callee, demand)) orelse return unknown;
        return self.mapNormalCleanupSummary(arena, proto, bindings, actual, summary, unknown);
    }

    /// Outcomes remain canonical; caller ownership/alias projection does not.
    fn mapNormalCleanupSummary(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        actual: ActualCallSummary,
        summary: fn_summary.FnSummary,
        exits: NormalCleanupCall,
    ) SummaryError!NormalCleanupCall {
        var definite_paths: std.ArrayListUnmanaged(fn_summary.ParamPath) = .empty;
        defer definite_paths.deinit(arena);
        var definite_fields: std.ArrayListUnmanaged(fn_summary.FieldFree) = .empty;
        defer definite_fields.deinit(arena);
        var may_paths: std.ArrayListUnmanaged(fn_summary.ParamPath) = .empty;
        defer may_paths.deinit(arena);
        var may_fields: std.ArrayListUnmanaged(fn_summary.FieldFree) = .empty;
        defer may_fields.deinit(arena);
        var error_definite_paths: std.ArrayListUnmanaged(fn_summary.ParamPath) = .empty;
        defer error_definite_paths.deinit(arena);
        var error_definite_fields: std.ArrayListUnmanaged(fn_summary.FieldFree) = .empty;
        defer error_definite_fields.deinit(arena);
        var error_may_paths: std.ArrayListUnmanaged(fn_summary.ParamPath) = .empty;
        defer error_may_paths.deinit(arena);
        var error_may_fields: std.ArrayListUnmanaged(fn_summary.FieldFree) = .empty;
        defer error_may_fields.deinit(arena);
        var normal_complete = summary.normal_success_effects_complete;
        var error_complete = summary.error_effects_complete;
        var storage_complete = summary.normal_success_storage_effects_complete;
        var error_storage_complete = summary.error_storage_effects_complete;
        const storage_outcomes = try self.mapStorageOutcomes(arena, proto, bindings, actual, summary.normal_success_storage_outcomes, &storage_complete);
        const error_storage_outcomes = try self.mapStorageOutcomes(arena, proto, bindings, actual, summary.error_storage_outcomes, &error_storage_complete);
        try self.mapNormalPaths(arena, proto, bindings, actual, summary.normal_success_definite_freed_paths, &definite_paths, &definite_fields, &normal_complete);
        try self.mapNormalPaths(arena, proto, bindings, actual, summary.normal_success_may_freed_paths, &may_paths, &may_fields, &normal_complete);
        try self.mapNormalFields(arena, proto, bindings, actual, summary.normal_success_definite_free_fields, &definite_fields, &normal_complete);
        try self.mapNormalFields(arena, proto, bindings, actual, summary.normal_success_may_free_fields, &may_fields, &normal_complete);
        try self.mapNormalPaths(arena, proto, bindings, actual, summary.error_definite_freed_paths, &error_definite_paths, &error_definite_fields, &error_complete);
        try self.mapNormalPaths(arena, proto, bindings, actual, summary.error_may_freed_paths, &error_may_paths, &error_may_fields, &error_complete);
        try self.mapNormalFields(arena, proto, bindings, actual, summary.error_definite_free_fields, &error_definite_fields, &error_complete);
        try self.mapNormalFields(arena, proto, bindings, actual, summary.error_may_free_fields, &error_may_fields, &error_complete);
        const owned_definite_paths = try definite_paths.toOwnedSlice(arena);
        errdefer arena.free(owned_definite_paths);
        const owned_definite_fields = try definite_fields.toOwnedSlice(arena);
        errdefer arena.free(owned_definite_fields);
        const owned_may_paths = try may_paths.toOwnedSlice(arena);
        errdefer arena.free(owned_may_paths);
        const owned_may_fields = try may_fields.toOwnedSlice(arena);
        errdefer arena.free(owned_may_fields);
        const owned_error_definite_paths = try error_definite_paths.toOwnedSlice(arena);
        errdefer arena.free(owned_error_definite_paths);
        const owned_error_definite_fields = try error_definite_fields.toOwnedSlice(arena);
        errdefer arena.free(owned_error_definite_fields);
        const owned_error_may_paths = try error_may_paths.toOwnedSlice(arena);
        errdefer arena.free(owned_error_may_paths);
        const owned_error_may_fields = try error_may_fields.toOwnedSlice(arena);
        return .{
            .definite_paths = owned_definite_paths,
            .definite_fields = owned_definite_fields,
            .may_paths = owned_may_paths,
            .may_fields = owned_may_fields,
            .complete = normal_complete,
            .error_definite_paths = owned_error_definite_paths,
            .error_definite_fields = owned_error_definite_fields,
            .error_may_paths = owned_error_may_paths,
            .error_may_fields = owned_error_may_fields,
            .error_complete = error_complete,
            .storage_outcomes = storage_outcomes,
            .error_storage_outcomes = error_storage_outcomes,
            .storage_complete = storage_complete,
            .error_storage_complete = error_storage_complete,
            .can_normal = exits.can_normal,
            .can_error = exits.can_error,
            .returns_error = exits.returns_error,
        };
    }

    /// Storage operations retain their identity meaning even when a method's
    /// whole receiver maps to a caller field. Do not project them to FieldFree.
    fn mapStorageOutcomes(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        call: ActualCallSummary,
        outcomes: []const fn_summary.StorageOutcome,
        complete: *bool,
    ) SummaryError![]const fn_summary.StorageOutcome {
        const node = call.callee.call_node;
        try self.normalCleanupStorageWork(node, outcomes.len);
        const mapped = try arena.alloc(fn_summary.StorageOutcome, outcomes.len);
        for (outcomes, mapped) |outcome, *destination| {
            try self.normalCleanupStorageWork(node, outcome.operations.len);
            const operations = try arena.alloc(fn_summary.StorageOperation, outcome.operations.len);
            var operation_count: usize = 0;
            for (outcome.operations, 0..) |operation, source_index| {
                const path = (try self.mapStoragePath(arena, proto, bindings, call, operation.path)) orelse {
                    complete.* = false;
                    continue;
                };
                const allocator = if (operation.allocator) |source_allocator|
                    try self.mapStoragePath(arena, proto, bindings, call, source_allocator)
                else
                    null;
                if (operation.kind == .replace and operation.replacement == .fresh_heap and allocator == null) complete.* = false;
                if (operation.allocator != null and allocator == null) complete.* = false;
                // Distinct formal histories cannot share one caller ledger:
                // their relative replacement ordinals would name other cells.
                if (operation_count == source_index) {
                    for (operations[0..operation_count], 0..) |previous, index| {
                        const source = outcome.operations[index].path;
                        try self.normalCleanupStorageWork(node, 1 +
                            @min(previous.path.path.len, path.path.len) +
                            @min(source.path.len, operation.path.path.len));
                        if ((previous.kind == .replace or operation.kind == .replace) and
                            previous.path.param == path.param and std.mem.eql(u8, previous.path.path, path.path) and
                            (source.param != operation.path.param or !std.mem.eql(u8, source.path, operation.path.path)))
                            complete.* = false;
                    }
                }
                operations[operation_count] = .{
                    .path = path,
                    .allocator = allocator,
                    .kind = operation.kind,
                    .replacement = operation.replacement,
                    .sdk_empty_slice_noop = operation.sdk_empty_slice_noop,
                    .version = operation.version,
                    .identity_proved = operation.identity_proved,
                };
                operation_count += 1;
            }
            destination.* = .{ .operations = operations[0..operation_count] };
        }
        return mapped;
    }

    fn mapStoragePath(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        call: ActualCallSummary,
        path: fn_summary.ParamPath,
    ) SummaryError!?fn_summary.ParamPath {
        var buffer: [2]Ast.Node.Index = undefined;
        const argument = (try call.callArgumentFor(self, &buffer, path.param)) orelse return null;
        // Local value aliases are snapshots, not unversioned receiver access.
        // The legacy mapper still retains their observed release as MAY.
        if (!try self.cleanupDirectFormal(bindings, argument)) return null;
        try self.normalCleanupStorageWork(argument, bindings.items.len);
        const owner = try fn_summary.ownerOfExpr(arena, self.tree, proto, bindings, self.tree.firstToken(argument), self.tree.lastToken(argument), 0);
        if (owner != .param) return null;
        try self.normalCleanupStorageWork(argument, owner.param.path.len);
        try self.normalCleanupStorageWork(argument, path.path.len);
        if (owner.param.path.len != 0 and path.path.len != 0)
            try self.normalCleanupStorageWork(argument, 1);
        return .{
            .param = owner.param.param,
            .path = try fn_summary.joinPath(arena, owner.param.path, path.path),
        };
    }

    fn mapNormalPaths(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        call: ActualCallSummary,
        paths: []const fn_summary.ParamPath,
        out: *std.ArrayListUnmanaged(fn_summary.ParamPath),
        fields: *std.ArrayListUnmanaged(fn_summary.FieldFree),
        complete: *bool,
    ) SummaryError!void {
        for (paths) |path| {
            var buffer: [2]Ast.Node.Index = undefined;
            const argument = (try call.callArgumentFor(self, &buffer, path.param)) orelse {
                complete.* = false;
                continue;
            };
            const owner = try fn_summary.ownerOfExpr(arena, self.tree, proto, bindings, self.tree.firstToken(argument), self.tree.lastToken(argument), 0);
            if (owner != .param) {
                complete.* = false;
                continue;
            }
            // A method consuming the whole value handed as its receiver
            // releases that receiver field, not its parent's allocation.
            if (path.param == 0 and path.path.len == 0 and owner.param.path.len != 0) {
                var receiver_buffer: [2]Ast.Node.Index = undefined;
                const receiver = (try call.callArgumentFor(self, &receiver_buffer, 0)) orelse {
                    complete.* = false;
                    continue;
                };
                var call_buffer: [2]Ast.Node.Index = undefined;
                const invocation = TypeResolver.CallOperands.full(self.tree, &call_buffer, call.callee.call_node) orelse {
                    complete.* = false;
                    continue;
                };
                if (invocation.implicit_receiver and self.tree.nodeTag(invocation.ast.fn_expr) == .field_access and
                    self.tree.nodeData(invocation.ast.fn_expr).node_and_token[0] == receiver)
                {
                    var proto_buffer: [1]Ast.Node.Index = undefined;
                    const declared = tokens.fnProto(call.callee.tree, &proto_buffer, call.callee.declaration) orelse {
                        complete.* = false;
                        continue;
                    };
                    const name_token = declared.name_token orelse {
                        complete.* = false;
                        continue;
                    };
                    try fields.append(arena, .{
                        .param = owner.param.param,
                        .field = owner.param.path,
                        .method = try arena.dupe(u8, call.callee.tree.tokenSlice(name_token)),
                    });
                    continue;
                }
            }
            try out.append(arena, .{
                .param = owner.param.param,
                .path = try fn_summary.joinPath(arena, owner.param.path, path.path),
            });
        }
    }

    fn mapNormalFields(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        call: ActualCallSummary,
        fields: []const fn_summary.FieldFree,
        out: *std.ArrayListUnmanaged(fn_summary.FieldFree),
        complete: *bool,
    ) SummaryError!void {
        for (fields) |field| {
            var buffer: [2]Ast.Node.Index = undefined;
            const argument = (try call.callArgumentFor(self, &buffer, field.param)) orelse {
                complete.* = false;
                continue;
            };
            const owner = try fn_summary.ownerOfExpr(arena, self.tree, proto, bindings, self.tree.firstToken(argument), self.tree.lastToken(argument), 0);
            if (owner != .param) {
                complete.* = false;
                continue;
            }
            try out.append(arena, .{
                .param = owner.param.param,
                .field = try fn_summary.joinPath(arena, owner.param.path, field.field),
                .method = try arena.dupe(u8, field.method),
            });
        }
    }

    /// Retention requires a typed destination and that exact owner's cleanup.
    pub fn retainedStorageAt(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        node: Ast.Node.Index,
    ) SummaryError![]const u32 {
        const frame = self.cleanup_frame orelse (self.zls orelse return &.{}).resolutionFrame();
        var retained: std.ArrayListUnmanaged(u32) = .empty;
        const tag = self.tree.nodeTag(node);
        if (tag == .assign) {
            const pair = self.tree.nodeData(node).node_and_node;
            if (self.tree.nodeTag(pair[0]) != .field_access) return &.{};
            const access = self.tree.nodeData(pair[0]).node_and_token;
            const target = try fn_summary.ownerOfExpr(arena, self.tree, proto, bindings, self.tree.firstToken(access[0]), self.tree.lastToken(access[0]), 0);
            if (target != .param or target.param.path.len != 0) return &.{};
            const container = (try frame.containerOfNode(access[0])) orelse return &.{};
            if (!try self.uniqueRetainedFieldWrite(arena, proto, bindings, node, target.param.param, self.tree.tokenSlice(access[1]))) return &.{};
            try self.retainStoredFormal(arena, proto, bindings, container, self.tree.tokenSlice(access[1]), pair[1], &retained);
        } else if (tag == .@"return") {
            const value = self.tree.nodeData(node).opt_node.unwrap() orelse return &.{};
            const return_type = proto.ast.return_type.unwrap() orelse return &.{};
            const container = (try frame.containerOfNode(return_type)) orelse return &.{};
            const literal_node = (try self.returnedAggregate(bindings, value)) orelse return &.{};
            var literal_buffer: [2]Ast.Node.Index = undefined;
            const literal = self.tree.fullStructInit(&literal_buffer, literal_node) orelse return &.{};
            for (literal.ast.fields) |field_value| {
                const value_first = self.tree.firstToken(field_value);
                if (value_first < 3 or self.tree.tokenTag(value_first - 1) != .equal or
                    self.tree.tokenTag(value_first - 2) != .identifier or
                    self.tree.tokenTag(value_first - 3) != .period) continue;
                try self.retainStoredFormal(arena, proto, bindings, container, self.tree.tokenSlice(value_first - 2), field_value, &retained);
            }
        }
        std.mem.sort(u32, retained.items, {}, std.sort.asc(u32));
        return retained.toOwnedSlice(arena);
    }

    fn uniqueRetainedFieldWrite(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        store: Ast.Node.Index,
        parameter: u32,
        field: []const u8,
    ) SummaryError!bool {
        const declaration = self.enclosingFunctionAt(self.tree, self.tree.nodeMainToken(store)) orelse return false;
        const body = tokens.bodyOf(self.tree, declaration) orelse return false;
        const key = @intFromEnum(body);
        const writes = self.retained_writes.get(key) orelse blk: {
            if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
            const owned_arena = self.summary_arena.?.allocator();
            var out: std.ArrayListUnmanaged(fn_summary.ParamPath) = .empty;
            try self.collectRetainedWrites(owned_arena, proto, bindings, body, &out);
            const complete = try out.toOwnedSlice(owned_arena);
            try self.retained_writes.put(self.gpa, key, complete);
            break :blk complete;
        };
        _ = arena;
        var count: usize = 0;
        for (writes) |write| {
            if (write.param == std.math.maxInt(u32)) return false;
            if (write.param != parameter) continue;
            if (write.path.len == 0) return false;
            if (std.mem.eql(u8, write.path, field)) count += 1;
        }
        return count == 1;
    }

    fn collectRetainedWrites(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        node: Ast.Node.Index,
        writes: *std.ArrayListUnmanaged(fn_summary.ParamPath),
    ) SummaryError!void {
        try self.enterNormalCleanup(node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanup(node);
        const tag = self.tree.nodeTag(node);
        var container_buffer: [2]Ast.Node.Index = undefined;
        if (tag == .fn_decl or self.tree.fullContainerDecl(&container_buffer, node) != null) return;
        switch (tag) {
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
            => {
                const target = self.tree.nodeData(node).node_and_node[0];
                if (self.tree.nodeTag(target) == .identifier and
                    std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(target)), "_")) return;
                const owner = try fn_summary.ownerOfExpr(arena, self.tree, proto, bindings, self.tree.firstToken(target), self.tree.lastToken(target), 0);
                try writes.append(arena, if (owner == .param) owner.param else .{ .param = std.math.maxInt(u32), .path = "" });
            },
            else => {},
        }
        var children = engine.AstIterator.init(self.tree, node);
        while (children.next(self.tree)) |child| try self.collectRetainedWrites(arena, proto, bindings, child, writes);
    }

    fn returnedAggregate(
        self: *FileCache,
        bindings: *const local_bindings.LocalBindings,
        node: Ast.Node.Index,
    ) SummaryError!?Ast.Node.Index {
        try self.enterNormalCleanup(node);
        defer self.leaveNormalCleanup();
        try self.chargeNormalCleanup(node);
        var buffer: [2]Ast.Node.Index = undefined;
        if (self.tree.fullStructInit(&buffer, node) != null) return node;
        if (self.tree.nodeTag(node) != .identifier) return null;
        const token = self.tree.nodeMainToken(node);
        const binding = bindings.findAt(self.tree.tokenSlice(token), token) orelse return null;
        if (!binding.is_const or binding.rhs_first >= token) return null;
        const initializer = self.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return null;
        return try self.returnedAggregate(bindings, initializer);
    }

    fn retainStoredFormal(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        container: TypeResolver.ActualType.Data.Container,
        field: []const u8,
        value: Ast.Node.Index,
        retained: *std.ArrayListUnmanaged(u32),
    ) SummaryError!void {
        const origin = try fn_summary.ownerOfExpr(arena, self.tree, proto, bindings, self.tree.firstToken(value), self.tree.lastToken(value), 0);
        if (origin != .param or origin.param.path.len != 0) return;
        if (!self.cleanup_demand.contains(origin.param.param)) return;
        const frame = self.cleanup_frame orelse (self.zls orelse return).resolutionFrame();
        const source_type = (try frame.typeOfNode(value)) orelse return;
        const source_tag = frame.resolver.typeTag(source_type) orelse return;
        const nonnull = source_tag != .optional;
        const field_released = released: {
            const saved_owners = cleanup_probe_owners;
            const saved_owner_count = cleanup_probe_owner_count;
            cleanup_probe_owners[0] = CleanupProbeOwner.init(0, value, origin.param);
            cleanup_probe_owner_count = 1;
            defer cleanup_probe_owners = saved_owners;
            defer cleanup_probe_owner_count = saved_owner_count;
            break :released try self.ownerFieldReleased(arena, container, field, nonnull);
        };
        if (!field_released) return;
        for (retained.items) |existing| if (existing == origin.param.param) return;
        try retained.append(arena, origin.param.param);
    }

    fn ownerFieldReleased(
        self: *FileCache,
        arena: std.mem.Allocator,
        container: TypeResolver.ActualType.Data.Container,
        field: []const u8,
        nonnull: bool,
    ) SummaryError!bool {
        const resolver = if (self.cleanup_frame) |frame| frame.resolver else self.zls orelse return false;
        const owner_frame = resolver.frameForContainer(container);
        const owner_tree = &owner_frame.handle.document.tree;
        const owner_cache = if (owner_tree == self.tree and owner_frame.handle.module == self.module_id)
            self
        else
            &(try grow_analysis_mod.sourceDocument(self, owner_frame.handle, owner_frame.resolver.ctx)).cache;
        var container_buffer: [2]Ast.Node.Index = undefined;
        const declared = owner_tree.fullContainerDecl(&container_buffer, container.scope_handle.toNode()) orelse return false;
        var declared_field = false;
        for (declared.ast.members) |member| {
            try owner_cache.chargeNormalCleanup(member);
            if (owner_tree.fullContainerField(member) == null) continue;
            if (std.mem.eql(u8, owner_tree.tokenSlice(owner_tree.nodeMainToken(member)), field)) {
                declared_field = true;
                break;
            }
        }
        if (!declared_field) return false;
        for (declared.ast.members) |member| {
            try owner_cache.chargeNormalCleanup(member);
            if (owner_tree.nodeTag(member) != .fn_decl) continue;
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const method = tokens.fnProto(owner_tree, &proto_buffer, member) orelse continue;
            var formals = method.iterate(owner_tree);
            const receiver = formals.next() orelse continue;
            const receiver_type = receiver.type_expr orelse continue;
            const actual_receiver = (try owner_frame.containerOfNode(receiver_type)) orelse continue;
            const owner_type: TypeResolver.ActualType = .{ .data = .{ .container = container }, .is_type_val = true };
            const receiver_owner: TypeResolver.ActualType = .{ .data = .{ .container = actual_receiver }, .is_type_val = true };
            if (!receiver_owner.eql(owner_type)) continue;
            // This node is the declaration itself, not a callable expression.
            // Resolve its actual function value in the same typed owner frame.
            const callable = (try owner_frame.resolveValueOfNode(member)) orelse continue;
            if (callable.is_type_val or callable.data != .function) continue;
            const function = callable.data.function;
            if (!function.handle.eql(owner_frame.handle) or
                function.fn_token != method.ast.fn_token or
                !function.container_type.*.eql(owner_type)) continue;
            const reference: TypeResolver.FunctionReference = .{
                .tree = owner_tree,
                .fn_token = function.fn_token,
                .handle = function.handle,
                .actual_type = callable,
            };
            const origin = self.cleanup_origin orelse self;
            var probe_key = resolvedCleanupKey(reference, member);
            probe_key.demand = .{ .one = 0 };
            const saved_probe_edge = cleanup_probe_edge;
            cleanup_probe_edge = .{
                .key = CleanupProbeKey.init(probe_key),
                .declaring = owner_cache,
                .kind = .field_context,
                .field = field,
                .owner_count = cleanup_probe_owner_count,
            };
            const probe_owner_count = @min(cleanup_probe_owner_count, cleanup_probe_owners.len);
            @memcpy(cleanup_probe_edge.?.owners[0..probe_owner_count], cleanup_probe_owners[0..probe_owner_count]);
            defer cleanup_probe_edge = saved_probe_edge;
            const summary = (try origin.contextualCleanupSummary(owner_cache, resolver, reference, member, .{ .one = 0 })) orelse continue;
            for (summary.normal_success_definite_freed_paths) |path| {
                if (path.param == 0 and std.mem.eql(u8, path.path, field)) return true;
            }
            for (summary.normal_success_definite_free_fields) |path| {
                if (path.param == 0 and std.mem.eql(u8, path.field, field)) return true;
            }
            if (!nonnull) continue;
            // A sole unwrap proves cleanup for a stored nonnull value only;
            // it is deliberately not an unconditional field-death fact.
            const method_body = tokens.bodyOf(owner_tree, member) orelse continue;
            var block_buffer: [2]Ast.Node.Index = undefined;
            const statements = owner_tree.blockStatements(&block_buffer, method_body) orelse continue;
            if (statements.len != 1) continue;
            const branch = owner_tree.fullIf(statements[0]) orelse continue;
            if (branch.payload_token == null or branch.error_token != null or branch.ast.else_expr != .none) continue;
            const branch_bindings = try local_bindings.build(arena, owner_tree, method, method_body);
            const condition = try fn_summary.ownerOfExpr(arena, owner_tree, method, &branch_bindings, owner_tree.firstToken(branch.ast.cond_expr), owner_tree.lastToken(branch.ast.cond_expr), 0);
            if (condition != .param or condition.param.param != 0 or !std.mem.eql(u8, condition.param.path, field)) continue;
            const condition_type = (try owner_frame.typeOfNode(branch.ast.cond_expr)) orelse continue;
            if (resolver.typeTag(condition_type) != .optional) continue;
            const saved_frame = owner_cache.cleanup_frame;
            const saved_origin = owner_cache.cleanup_origin;
            const saved_demand = owner_cache.cleanup_demand;
            owner_cache.cleanup_frame = resolver.frameForFunction(reference);
            owner_cache.cleanup_origin = origin;
            owner_cache.cleanup_demand = .{ .one = 0 };
            defer owner_cache.cleanup_frame = saved_frame;
            defer owner_cache.cleanup_origin = saved_origin;
            defer owner_cache.cleanup_demand = saved_demand;
            const cleanup = try fn_summary.inferNormalSuccessCleanup(owner_cache, arena, method, &branch_bindings, branch.ast.then_expr);
            for (cleanup.definite_freed_paths) |path| {
                if (path.param == 0 and std.mem.eql(u8, path.path, field)) return true;
            }
            for (cleanup.definite_free_fields) |path| {
                if (path.param == 0 and std.mem.eql(u8, path.field, field)) return true;
            }
        }
        return false;
    }

    /// Withdraw the summary of a root whose fold gave up and remember the
    /// failure, so no lookup reads the part it computed as the whole of it.
    fn failRoot(
        self: *FileCache,
        fn_decl: Ast.Node.Index,
        diagnostic: ?budget_mod.Diagnostic,
    ) error{OutOfMemory}!void {
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return;
        const key = @intFromEnum(body);
        try self.failed_roots.put(self.gpa, key, diagnostic);
        _ = self.summaries.remove(key);
    }

    /// Like summaryOf but also fills the deep inference fields that
    /// require allocation (`may_free_fields`, `result_heap_fields`)
    /// and the contextual field (`heap_allocates_self`).  Slice
    /// storage lives in the cache's `summary_arena`.
    pub fn summaryOfFn(
        self: *FileCache,
        fn_decl: Ast.Node.Index,
    ) SummaryError!*const fn_summary.FnSummary {
        // Resolve proto + body via lexer helpers.
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse {
            // Caller passed a non-fn_decl node — return a sentinel
            // .unknown summary.  Cache by fn_decl index so we don't
            // recompute.
            const key = @intFromEnum(fn_decl) | 0x8000_0000;
            const gop = try self.summaries.getOrPut(self.gpa, key);
            if (!gop.found_existing) gop.value_ptr.* = .{};
            return gop.value_ptr;
        };
        const body = tokens.bodyOf(self.tree, fn_decl) orelse {
            const key = @intFromEnum(fn_decl) | 0x8000_0000;
            const gop = try self.summaries.getOrPut(self.gpa, key);
            if (!gop.found_existing) gop.value_ptr.* = .{};
            return gop.value_ptr;
        };

        const key = @intFromEnum(body);
        // A root whose fold gave up stays failed: its partial summary was
        // withdrawn, and recomputing it here would publish the body-only
        // answer as the finished one.
        if (self.failed_roots.get(key)) |recorded| return reraiseRootFailure(recorded);
        const gop = try self.summaries.getOrPut(self.gpa, key);
        if (gop.found_existing and gop.value_ptr._resolved) {
            // Already resolved; preserves any R10 transitive
            // mutations from prior `resolveTransitiveTakes` passes.
            return gop.value_ptr;
        }

        // Start from the cheap body-only summary, or upgrade an
        // existing (cheap-only) entry in place.
        var s = if (gop.found_existing) gop.value_ptr.* else fn_summary.inferFromBody(self.tree, proto, body);
        if (!gop.found_existing) gop.value_ptr.* = s;
        if (self.summary_visiting.contains(key)) return self.summaries.getPtr(key).?;
        errdefer _ = self.summaries.remove(key);
        try self.summary_visiting.put(self.gpa, key, {});
        defer _ = self.summary_visiting.remove(key);

        // Lazy-init the summary arena.
        if (self.summary_arena == null) {
            self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        }
        const a = self.summary_arena.?.allocator();

        s.may_free_fields = try fn_summary.inferMayFreeFields(a, self.tree, proto, body);
        s.result_heap_fields = try fn_summary.inferResultHeapFields(a, self.tree, body);
        // `freed_paths` / `written_paths`: the receiver-field releases
        // and writes this body spells out.  `receiverFreedFields` reads
        // them to answer "which fields of THIS receiver does the callee
        // release", so an allocator-routed release —
        // `self.gpa.destroy(self.first)` — names `first` rather than
        // leaving the call site with nothing to say.  Built from a real
        // `LocalBindings` so a store through an alias is attributed to
        // the storage the alias names.
        {
            const bindings = try local_bindings.build(a, self.tree, proto, body);
            const eff = try fn_summary.inferFieldEffects(a, self.tree, proto, &bindings, body);
            s.freed_paths = eff.freed_paths;
            s.written_paths = eff.written_paths;
            const normal = try fn_summary.inferNormalSuccessCleanup(self, a, proto, &bindings, body);
            setCleanupOutcomes(&s, normal);
        }

        // Containing-type lookup → heap_allocates_self.
        const model = try self.fileModel();
        const ct: ?[]const u8 = if (model.containingTypeOf(fn_decl)) |ti| ti.name else null;
        s.heap_allocates_self = try fn_summary.inferHeapAllocatesSelf(self, body, ct);

        // NOTE: may_free_fields here is the RAW body-only inference.
        // resolveTransitiveTakes filters it as a finalization pass,
        // since the filter needs to consult OTHER summaries (creating
        // a comptime-dependency cycle if done inside summaryOfFn).

        s._resolved = true;
        // Storage-provenance queries can rehash the summary map.
        const completed = self.summaries.getPtr(key).?;
        completed.* = s;
        return completed;
    }
};
fn resolvedCleanupKey(reference: TypeResolver.FunctionReference, declaration: Ast.Node.Index) CleanupKey {
    return .{
        .declaration = .{ .tree = reference.tree, .module = reference.handle.module, .declaration = declaration },
        .context = reference.actual_type,
    };
}

fn setCleanupOutcomes(summary: *fn_summary.FnSummary, outcomes: fn_summary.NormalSuccessEffects) void {
    summary.normal_success_definite_freed_paths = outcomes.definite_freed_paths;
    summary.normal_success_may_freed_paths = outcomes.may_freed_paths;
    summary.normal_success_definite_free_fields = outcomes.definite_free_fields;
    summary.normal_success_may_free_fields = outcomes.may_free_fields;
    summary.normal_success_effects_complete = outcomes.complete;
    summary.normal_success_storage_outcomes = outcomes.storage_outcomes;
    summary.normal_success_storage_effects_complete = outcomes.storage_effects_complete;
    summary.retained_owned_params = outcomes.retained_owned_params;
    summary.error_definite_freed_paths = outcomes.error_definite_freed_paths;
    summary.error_may_freed_paths = outcomes.error_may_freed_paths;
    summary.error_definite_free_fields = outcomes.error_definite_free_fields;
    summary.error_may_free_fields = outcomes.error_may_free_fields;
    summary.error_effects_complete = outcomes.error_complete;
    summary.error_storage_outcomes = outcomes.error_storage_outcomes;
    summary.error_storage_effects_complete = outcomes.error_storage_effects_complete;
}

fn copySummaryText(arena: std.mem.Allocator, text: []const u8) error{OutOfMemory}![]const u8 {
    if (text.len == 0) return "";
    return try arena.dupe(u8, text);
}

/// `inferFieldEffects` allocates its path arrays in the supplied arena;
/// only their path text borrows the source tree.
fn ownEffectPathTexts(arena: std.mem.Allocator, paths: []const fn_summary.ParamPath) error{OutOfMemory}!void {
    for (@constCast(paths)) |*path| path.path = try copySummaryText(arena, path.path);
}

/// Copy every variable-length member of a summary into the receiving
/// cache's arena. Several entries contain slices borrowed from the
/// foreign AST, so copying only the outer arrays is not sufficient.
fn cloneFnSummary(
    arena: std.mem.Allocator,
    source: fn_summary.FnSummary,
) error{OutOfMemory}!fn_summary.FnSummary {
    var result = source;

    inline for (.{ "normal_success_definite_freed_paths", "normal_success_may_freed_paths", "error_definite_freed_paths", "error_may_freed_paths" }) |name| {
        const paths = try arena.dupe(fn_summary.ParamPath, @field(source, name));
        for (paths) |*path| path.path = try copySummaryText(arena, path.path);
        @field(result, name) = paths;
    }
    inline for (.{ "normal_success_definite_free_fields", "normal_success_may_free_fields", "error_definite_free_fields", "error_may_free_fields" }) |name| {
        const fields = try arena.dupe(fn_summary.FieldFree, @field(source, name));
        for (fields) |*field| {
            field.field = try copySummaryText(arena, field.field);
            field.method = try copySummaryText(arena, field.method);
        }
        @field(result, name) = fields;
    }
    result.retained_owned_params = try arena.dupe(u32, source.retained_owned_params);
    inline for (.{ "normal_success_storage_outcomes", "error_storage_outcomes" }) |name| {
        const outcomes = try arena.dupe(fn_summary.StorageOutcome, @field(source, name));
        for (outcomes) |*outcome| {
            const operations = try arena.dupe(fn_summary.StorageOperation, outcome.operations);
            for (operations) |*operation| {
                operation.path.path = try copySummaryText(arena, operation.path.path);
                if (operation.allocator) |*allocator|
                    allocator.path = try copySummaryText(arena, allocator.path);
            }
            outcome.operations = operations;
        }
        @field(result, name) = outcomes;
    }

    if (source.may_free_fields.len == 0) {
        result.may_free_fields = &.{};
    } else {
        const fields = try arena.dupe(fn_summary.FieldFree, source.may_free_fields);
        for (fields) |*field| {
            field.field = try copySummaryText(arena, field.field);
            field.method = try copySummaryText(arena, field.method);
        }
        result.may_free_fields = fields;
    }

    if (source.freed_paths.len == 0) {
        result.freed_paths = &.{};
    } else {
        const paths = try arena.dupe(fn_summary.ParamPath, source.freed_paths);
        for (paths) |*path| path.path = try copySummaryText(arena, path.path);
        result.freed_paths = paths;
    }

    if (source.written_paths.len == 0) {
        result.written_paths = &.{};
    } else {
        const paths = try arena.dupe(fn_summary.ParamPath, source.written_paths);
        for (paths) |*path| path.path = try copySummaryText(arena, path.path);
        result.written_paths = paths;
    }

    if (source.result_heap_fields.len == 0) {
        result.result_heap_fields = &.{};
    } else {
        const fields = try arena.dupe([]const u8, source.result_heap_fields);
        for (fields) |*field| field.* = try copySummaryText(arena, field.*);
        result.result_heap_fields = fields;
    }

    if (source.grow_paths.len == 0) {
        result.grow_paths = &.{};
    } else {
        const paths = try arena.dupe(fn_summary.GrowPath, source.grow_paths);
        for (paths) |*path| path.field = try copySummaryText(arena, path.field);
        result.grow_paths = paths;
    }

    result.unplaced_args = if (source.unplaced_args.len == 0)
        &.{}
    else
        try arena.dupe(u32, source.unplaced_args);
    return result;
}

/// How many `{` regions deep the comptime-scope walk will look.  Past
/// the bound the walk did not finish, and a partial reading of where a
/// token sits is not a reading of it.
const max_fill_scope_depth: usize = 64;

/// How far back from a token the search for its enclosing builtin's `(`
/// will reach before giving up.
const max_comptime_builtin_depth: usize = 256;

/// Built-ins whose argument is a TYPE, evaluated at comptime and never
/// read at runtime.  Each name includes its leading `@`.
const comptime_only_builtins = [_][]const u8{
    "@TypeOf",   "@sizeOf",      "@alignOf",        "@bitSizeOf",
    "@typeInfo", "@typeName",    "@hasField",       "@hasDecl",
    "@offsetOf", "@bitOffsetOf", "@fieldParentPtr",
};

/// The `{` of the innermost `comptime` block — `comptime { … }` or
/// `comptime label: { … }` — enclosing `token`, or null when there is
/// none.  Every statement of such a block is evaluated at comptime.  A nest
/// deeper than the walk reads is an exhausted bound, not "no block".
fn comptimeBlockEnclosing(tree: *const Ast, token: Ast.TokenIndex) budget_mod.BudgetError!?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    var regions: [max_fill_scope_depth]Ast.TokenIndex = undefined;
    const region_len = openBraceStack(tags, token, &regions) orelse
        return tokenBudgetFailure(tree, token, .comptime_scope_depth, max_fill_scope_depth);
    var i = region_len;
    while (i > 0) {
        i -= 1;
        const brace = regions[i];
        if (brace == 0) continue;
        if (tags[brace - 1] == .keyword_comptime) return brace;
        if (brace >= 3 and tags[brace - 3] == .keyword_comptime and
            tags[brace - 2] == .identifier and tags[brace - 1] == .colon) return brace;
    }
    return null;
}

/// Record that a bounded walk over `tree` gave up at `token` — line, column
/// and enclosing function included — and return the error callers propagate.
pub fn tokenBudgetFailure(
    tree: *const Ast,
    token: Ast.TokenIndex,
    limit: budget_mod.Limit,
    cap: u32,
) budget_mod.BudgetError {
    const byte = tree.tokens.items(.start)[token];
    const position = budget_mod.lineCol(tree.source, byte);
    var name: budget_mod.NameBuf = .{};
    if (tokens.enclosingFnDecl(tree, token)) |declaration| {
        var buffer: [1]Ast.Node.Index = undefined;
        if (tokens.fnProto(tree, &buffer, declaration)) |proto| {
            if (proto.name_token) |name_token| name.set(tree.tokenSlice(name_token));
        }
    }
    return budget_mod.fail(.{
        .limit = limit,
        .limit_value = cap,
        .reached = cap,
        .byte = byte,
        .document = budget_mod.documentForTree(tree),
        .line = position.line,
        .column = position.column,
        .function = name,
    });
}

/// The open `{` tokens enclosing `token`, innermost LAST.  Bounded: when
/// more than `max_fill_scope_depth` regions are open AT `token`, the walk
/// did not finish, which is not an answer.  A region nested deeper than the
/// bound earlier in the file and already closed does not matter: its depth
/// is counted, not stored, and the stack below the bound stays intact.
fn openBraceStack(
    tags: []const std.zig.Token.Tag,
    token: Ast.TokenIndex,
    regions: *[max_fill_scope_depth]Ast.TokenIndex,
) ?usize {
    var depth: usize = 0;
    var t: Ast.TokenIndex = 0;
    while (t < token) : (t += 1) {
        switch (tags[t]) {
            .l_brace => {
                if (depth < max_fill_scope_depth) regions[depth] = t;
                depth += 1;
            },
            .r_brace => {
                if (depth > 0) depth -= 1;
            },
            else => {},
        }
    }
    if (depth > max_fill_scope_depth) return null;
    return depth;
}

/// Is `token` written inside the parentheses of a built-in whose
/// argument is a TYPE, evaluated at comptime and never read at runtime?
///
/// `@sizeOf`, `@TypeOf`, `@offsetOf` and the rest answer a question
/// about a type; the expression inside them is never a runtime value,
/// so a subscript or a cast written there is not a runtime one.
fn comptimeOnlyBuiltinArgument(tree: *const Ast, token: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    // Walk back over this buildin's argument to its `(`.  Bounded: an
    // argument list this tool cannot close is one it cannot classify.
    var open: ?Ast.TokenIndex = null;
    var scanned: usize = 0;
    var t = token;
    while (t > 0 and scanned < max_comptime_builtin_depth) : (scanned += 1) {
        t -= 1;
        switch (tags[t]) {
            .l_paren => {
                open = t;
                break;
            },
            // A closing paren steps back over the group it closes; a
            // separator or a brace ends the search.
            .r_paren, .comma, .semicolon, .l_brace, .r_brace => break,
            else => {},
        }
    }
    const paren = open orelse return false;
    if (paren == 0) return false;
    if (tags[paren - 1] != .builtin) return false;
    const name = tree.tokenSlice(paren - 1);
    inline for (comptime_only_builtins) |candidate| {
        if (std.mem.eql(u8, name, candidate)) return true;
    }
    return false;
}

/// The statements of one block node, in source order.  `buf` backs the
/// one- and two-statement shapes, which the node table stores inline.
fn bodyStatements(
    tree: *const Ast,
    block_node: Ast.Node.Index,
    buf: *[2]Ast.Node.Index,
) []const Ast.Node.Index {
    return switch (tree.nodeTag(block_node)) {
        .block, .block_semicolon => tree.extraDataSlice(tree.nodeData(block_node).extra_range, Ast.Node.Index),
        .block_two, .block_two_semicolon => blk: {
            const data = tree.nodeData(block_node);
            buf[0] = data.opt_node_and_opt_node[0].unwrap() orelse break :blk &.{};
            if (data.opt_node_and_opt_node[1].unwrap()) |second| {
                buf[1] = second;
                break :blk buf[0..2];
            }
            break :blk buf[0..1];
        },
        else => &.{},
    };
}

/// A node standing for the bare name spelled at `name_token`.  Used
/// where a value is required but the declaration has none: `var x: T;`
/// binds `x` to `undefined`, and the name itself is the only expression
/// in the declaration — so reading it here names the same absence an
/// absent initializer names, rather than inventing one.
fn identifierNodeAt(tree: *const Ast, name_token: Ast.TokenIndex) ?Ast.Node.Index {
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeMainToken(node) != name_token) continue;
        return node;
    }
    return null;
}

/// Recognize a direct `_ = &x` at a statement boundary.  Other contexts
/// remain escaped: the prefix excludes struct fields and field
/// assignments, where the address is not discarded but stored.
fn addressIsDiscarded(tree: *const Ast, node: Ast.Node.Index) bool {
    const amp = tree.firstToken(node);
    if (amp < 3 or tree.tokenTag(amp - 1) != .equal) return false;
    if (tree.tokenTag(amp - 2) != .identifier) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(amp - 2), "_")) return false;
    return switch (tree.tokenTag(amp - 3)) {
        .semicolon, .l_brace, .r_brace => true,
        else => false,
    };
}

/// The token range of the initializer of the file-level declaration
/// `name` is written with, or null when this file declares no such name
/// or that declaration has no initializer.
///
/// A file-level `const name` OWNS its name: what it aliases is what
/// that name means, so a reader that wants the type behind `const List =
/// std.ArrayList(u32);` follows the declaration rather than resolving
/// the spelling.
pub fn rootDeclInitRange(tree: *const Ast, name: []const u8) ?FileCache.TokenRange {
    for (tree.rootDecls()) |node| {
        const decl = tree.fullVarDecl(node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(decl.ast.mut_token + 1), name)) continue;
        const value = decl.ast.init_node.unwrap() orelse return null;
        return .{ .first = tree.firstToken(value), .last = tree.lastToken(value) };
    }
    return null;
}

/// Resolve a name in `proto`'s param list to its 0-indexed position.
pub fn paramIndexFor(tree: *const Ast, proto: Ast.full.FnProto, name: []const u8) ?u32 {
    var idx: u32 = 0;
    var it = proto.iterate(tree);
    while (it.next()) |p| : (idx += 1) {
        const name_tok = p.name_token orelse continue;
        if (std.mem.eql(u8, tree.tokenSlice(name_tok), name)) return idx;
    }
    return null;
}

/// A `fn` declaration addressed the way a resolved one is: the tree it
/// was read from, the module it was read in, and its own node.  Token
/// indices belong to `tree`, so the two travel together and a reader
/// cannot take one without the other.
pub const ResolvedFnDecl = struct {
    tree: *const Ast,
    module: ModuleId,
    fn_decl: Ast.Node.Index,
};

/// The `fn` declaration `name` names at the top level of `tree`, or
/// null when this tree declares no such fn or declares it more than
/// once.  Two declarations of one name are a duplicate the compiler
/// rejects, and nothing here may pick one of them.
///
/// Read from the tree the qualifier's module was PARSED FROM, never from
/// the spelling at the call site — which is all the call site wrote.
pub fn moduleFnDecl(tree: *const Ast, name: []const u8, module: ModuleId) ?ResolvedFnDecl {
    var buf: [1]Ast.Node.Index = undefined;
    var found: ?ResolvedFnDecl = null;
    var it = tokens.iterFnDecls(tree);
    while (it.next(&buf)) |entry| {
        if (!std.mem.eql(u8, tree.tokenSlice(entry.name_token), name)) continue;
        if (found != null) return null;
        found = .{ .tree = tree, .module = module, .fn_decl = entry.node };
    }
    return found;
}

/// Read a complete container path from a type expression without invoking
/// the type engine. Strip only leading pointer/optional/const qualifiers.
/// The borrowed source slice retains the exact import alias and every nested
/// segment. Non-path types (including slices and generic calls) return null.
fn typeNameFromTypeNode(tree: *const Ast, type_node: Ast.Node.Index) ?[]const u8 {
    const first = tree.firstToken(type_node);
    const last = tree.lastToken(type_node);
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .asterisk, .keyword_const => continue,
            .l_bracket => return null,
            .identifier => break,
            else => return null,
        }
    }
    if (t > last) return null;
    const name_first = t;
    var expecting_ident = true;
    while (t <= last) : (t += 1) {
        const tag = tags[t];
        if (expecting_ident) {
            if (tag == .identifier) {
                expecting_ident = false;
            } else return null;
        } else {
            if (tag == .period) expecting_ident = true else return null;
        }
    }
    if (expecting_ident) return null;
    const starts = tree.tokens.items(.start);
    return tree.source[starts[name_first] .. starts[last] + tree.tokenSlice(last).len];
}

/// The declared type path at the end of a `param.field.path` chain.
/// The spelling is borrowed from the owner model and retains an exact
/// import alias when the leaf type is foreign.
const FieldPathEnd = struct {
    qualified_name: []const u8,
};

/// Walk a dotted field path through locally resolved container types.
/// Return the deepest field's complete declared type path. Intermediate
/// foreign or otherwise unresolved types cannot establish the next field.
fn walkFieldPath(
    model: *const file_model.FileModel,
    outer_type: []const u8,
    path: []const u8,
) ?FieldPathEnd {
    var it = std.mem.splitScalar(u8, path, '.');
    var cur_outer: []const u8 = outer_type;
    var last_result: ?FieldPathEnd = null;
    while (it.next()) |segment| {
        // The declared type NAME with `*`/`?`/`const`/`align(…)` stripped —
        // the same shape `resolveFieldTypeQualified` reads.  A field whose
        // type names nothing walkable (a slice, an array, an unresolved
        // shape) has no type name this question could go on with.
        const declared = model.fieldType(cur_outer, segment) orelse return null;
        const end = FieldPathEnd{ .qualified_name = declared };
        last_result = end;
        // The next segment needs a type in this model. A dotted name
        // may be a local nested type; otherwise it belongs to an import
        // whose fields require that module's own model.
        if (it.peek() == null) break;
        if (findTypeInModelPath(model, end.qualified_name) == null) return null;
        cur_outer = end.qualified_name;
    }
    return last_result;
}

/// The longest dotted type path this cache follows.  A longer path is
/// not a name it reasons about.
const max_type_path_segments = 8;

/// The identifier segments a dotted type path is written as, borrowed
/// from `name`.  Returns 0 for an empty segment or a path longer than
/// `out` can hold — a path this walk cannot name in full is not a path
/// it answers for.
fn splitTypePath(out: *[max_type_path_segments][]const u8, name: []const u8) usize {
    var count: usize = 0;
    var segments = std.mem.splitScalar(u8, name, '.');
    while (segments.next()) |segment| {
        const trimmed = std.mem.trim(u8, segment, " \t\r\n");
        if (trimmed.len == 0) return 0;
        if (count == max_type_path_segments) return 0;
        out[count] = trimmed;
        count += 1;
    }
    return count;
}

/// The declarations a dotted type path reaches, starting from what its
/// head segment resolved to.  Every later segment must be a type
/// declared DIRECTLY inside the type the previous segment reached — the
/// enclosing index, not the name alone, is what places it — so a
/// name reused in an unrelated scope cannot answer for this one.
/// Anything else ends the walk with no answer.
fn walkTypePath(head: ?FileCache.ResolvedType, rest: []const []const u8) ?FileCache.ResolvedType {
    var current = head orelse return null;
    for (rest) |segment| {
        const types = current.model.types;
        var enclosing: ?u32 = null;
        for (types, 0..) |*candidate, i| {
            if (candidate == current.info) {
                enclosing = @intCast(i);
                break;
            }
        }
        const outer_index = enclosing orelse return null;
        var next: ?FileCache.ResolvedType = null;
        for (types) |*candidate| {
            const parent = candidate.parent orelse continue;
            if (parent != outer_index) continue;
            if (!std.mem.eql(u8, candidate.name, segment)) continue;
            next = .{
                .model = current.model,
                .info = candidate,
                .path = current.path,
                .module = current.module,
            };
            break;
        }
        current = next orelse return null;
    }
    return current;
}

const ImportExpr = struct {
    path: []const u8,
    selected_type: ?[]const u8 = null,
};

/// Accept only an import initializer or a direct type selection from it.
/// An arbitrary expression containing `@import` does not bind a namespace.
fn importExprInNode(tree: *const Ast, node: Ast.Node.Index) ?ImportExpr {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(node);
    const last = tree.lastToken(node);
    if (first > last or tags[first] != .builtin) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(first), "@import")) return null;
    const open = first + 1;
    if (open > last or tags[open] != .l_paren) return null;
    const close = tokens.matchParen(tags, open, last) orelse return null;
    const path = tokens.importLiteralFromTokens(tree, first, close) orelse return null;
    if (close == last) return .{ .path = path };
    if (close + 2 != last or tags[close + 1] != .period or tags[close + 2] != .identifier) return null;
    return .{ .path = path, .selected_type = tree.tokenSlice(close + 2) };
}

fn importModel(
    pc: *project_cache_mod.ProjectCache,
    from_path: []const u8,
    import_path: []const u8,
) ?*const file_model.FileModel {
    if (project_cache_mod.isRelativeImport(import_path)) {
        return pc.modelForRelativeImport(from_path, import_path) catch null;
    }
    return pc.modelForModuleImport(from_path, import_path) catch null;
}

const BoundImport = struct {
    model: *const file_model.FileModel,
    selected_type: ?*const file_model.TypeInfo,
};

fn findTypeInModelPath(
    model: *const file_model.FileModel,
    name: []const u8,
) ?*const file_model.TypeInfo {
    var segments: [max_type_path_segments][]const u8 = undefined;
    const count = splitTypePath(&segments, name);
    if (count == 0) return null;
    return model.findQualifiedType(segments[0..count]);
}

fn boundImportForInitializer(
    pc: *project_cache_mod.ProjectCache,
    tree: *const Ast,
    from_path: []const u8,
    initializer: Ast.Node.Index,
) ?BoundImport {
    const expr = importExprInNode(tree, initializer) orelse return null;
    const model = importModel(pc, from_path, expr.path) orelse return null;
    const selected_type = if (expr.selected_type) |name|
        findTypeInModelPath(model, name) orelse return null
    else
        null;
    return .{ .model = model, .selected_type = selected_type };
}

/// Resolve only the root const named by the first path segment. A module
/// import binds a namespace; a selected import binds that exact type.
fn modelForBoundImport(
    pc: *project_cache_mod.ProjectCache,
    tree: *const Ast,
    from_path: []const u8,
    alias: []const u8,
) ?BoundImport {
    var found = false;
    var result: ?BoundImport = null;
    for (tree.rootDecls()) |node| {
        const decl = tree.fullVarDecl(node) orelse continue;
        if (tree.tokenTag(decl.ast.mut_token) != .keyword_const) continue;
        const name_token = decl.ast.mut_token + 1;
        if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), alias)) continue;
        if (found) return null;
        found = true;
        const init = decl.ast.init_node.unwrap() orelse return null;
        result = boundImportForInitializer(pc, tree, from_path, init);
    }
    return result;
}

fn resolvedTypeViaImports(
    pc: *project_cache_mod.ProjectCache,
    tree: *const Ast,
    from_path: []const u8,
    name: []const u8,
    depth_left: u32,
    module: ModuleId,
) ?FileCache.ResolvedType {
    var segments: [max_type_path_segments][]const u8 = undefined;
    const count = splitTypePath(&segments, name);
    if (count == 0) return null;
    return resolvedTypePathViaImports(pc, tree, from_path, segments[0..count], depth_left, module);
}

/// Resolve a segment path only through the exact root const it names.
/// A bare type is valid only when that const directly selects the type;
/// a module namespace can contribute a member only after its alias prefix.
fn resolvedTypePathViaImports(
    pc: *project_cache_mod.ProjectCache,
    tree: *const Ast,
    from_path: []const u8,
    segments: []const []const u8,
    depth_left: u32,
    module: ModuleId,
) ?FileCache.ResolvedType {
    if (depth_left == 0 or segments.len == 0) return null;
    const bound = modelForBoundImport(pc, tree, from_path, segments[0]) orelse return null;
    const entry: *const project_cache_mod.ProjectCache.Entry =
        @fieldParentPtr("model", bound.model);

    if (segments.len == 1) {
        const selected = bound.selected_type orelse return null;
        return .{
            .model = bound.model,
            .info = selected,
            .path = entry.abs_path,
            .module = module,
        };
    }

    const head = if (bound.selected_type) |selected| FileCache.ResolvedType{
        .model = bound.model,
        .info = selected,
        .path = entry.abs_path,
        .module = module,
    } else if (findTypeInModelPath(bound.model, segments[1])) |local| FileCache.ResolvedType{
        .model = bound.model,
        .info = local,
        .path = entry.abs_path,
        .module = module,
    } else resolvedTypePathViaImports(
        pc,
        bound.model.tree,
        entry.abs_path,
        segments[1..2],
        depth_left - 1,
        module,
    ) orelse return null;
    const rest = if (bound.selected_type != null) segments[1..] else segments[2..];
    return walkTypePath(head, rest);
}

fn findMethodViaImports(
    pc: *project_cache_mod.ProjectCache,
    tree: *const Ast,
    from_path: []const u8,
    type_name: []const u8,
    method_name: []const u8,
    depth_left: u32,
    module: ModuleId,
) ?FileCache.ResolvedMethod {
    const resolved = resolvedTypeViaImports(pc, tree, from_path, type_name, depth_left, module) orelse return null;
    const method = resolved.info.findMethod(method_name) orelse return null;
    return .{ .tree = resolved.model.tree, .method = method };
}

// ── Tests ──────────────────────────────────────────────────

test "FileCache: line offsets refuse source width before allocation or scanning" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "", .zig);
    defer tree.deinit(gpa);
    const original_source = tree.source;
    defer tree.source = original_source;
    for ([_]usize{ SourcePolicy.max_source_bytes, std.math.maxInt(usize) }) |length| {
        // Forge metadata only; the admission guard must not read this pointer.
        tree.source.ptr = @ptrFromInt(1);
        tree.source.len = length;
        var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = 0 });
        var cache = FileCache.init(failing.allocator(), &tree);
        defer cache.deinit();
        try std.testing.expectError(error.SourceTooWide, cache.getLineOffsets());
        try std.testing.expect(!failing.has_induced_failure);
        try std.testing.expectEqual(@as(usize, 0), cache.line_offsets.len);
    }
}

test "FileCache: line offset refusal leaves admitted retry cacheable" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "\n\n", .zig);
    defer tree.deinit(gpa);
    const original_source = tree.source;
    defer tree.source = original_source;
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();

    tree.source.ptr = @ptrFromInt(1);
    tree.source.len = SourcePolicy.max_source_bytes;
    try std.testing.expectError(error.SourceTooWide, cache.getLineOffsets());
    tree.source = original_source;
    const offsets = try cache.getLineOffsets();
    try std.testing.expectEqualSlices(u32, &.{ 0, 1, 2 }, offsets);
    try std.testing.expectEqual(offsets.ptr, (try cache.getLineOffsets()).ptr);

    // A cached table is not admission for a different source length.
    tree.source.ptr = @ptrFromInt(1);
    tree.source.len = SourcePolicy.max_source_bytes;
    try std.testing.expectError(error.SourceTooWide, cache.getLineOffsets());
}

test "FileCache: failed localBindings builds permit clean teardown and retry" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\fn foo(x: u32) void {
        \\    const first = x;
        \\    {
        \\        const second = first;
        \\        _ = second;
        \\    }
        \\}
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(&tree);
    const foo = fns.next(&proto_buf).?;

    for ([_]bool{ false, true }) |retry_after_failure| {
        var fail_index: usize = 0;
        while (true) : (fail_index += 1) {
            var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = fail_index });
            var cache = FileCache.init(failing.allocator(), &tree);
            defer cache.deinit();
            const bindings = cache.localBindings(foo.proto, foo.body) catch |err| {
                try std.testing.expectEqual(error.OutOfMemory, err);
                try std.testing.expect(failing.has_induced_failure);
                if (retry_after_failure) {
                    failing.fail_index = std.math.maxInt(usize);
                    const retried = try cache.localBindings(foo.proto, foo.body);
                    try std.testing.expectEqual(local_bindings.OriginKind.param, std.meta.activeTag(retried.find("x").?.origin));
                    try std.testing.expectEqualStrings("x", retried.find("first").?.origin.alias);
                    try std.testing.expectEqualStrings("first", retried.find("second").?.origin.alias);
                }
                continue;
            };
            try std.testing.expectEqual(local_bindings.OriginKind.param, std.meta.activeTag(bindings.find("x").?.origin));
            try std.testing.expectEqualStrings("x", bindings.find("first").?.origin.alias);
            try std.testing.expectEqualStrings("first", bindings.find("second").?.origin.alias);
            break;
        }
    }
}

test "FileCache: local binding items survive bindings map growth" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\fn first(initial: u32) void { const saved = initial; _ = saved; }
        \\fn second(two: u32) void { const second_alias = two; _ = second_alias; }
        \\fn third(three: u32) void { const third_alias = three; _ = third_alias; }
        \\fn fourth(four: u32) void { const fourth_alias = four; _ = fourth_alias; }
        \\fn fifth(five: u32) void { const fifth_alias = five; _ = fifth_alias; }
        \\fn sixth(six: u32) void { const sixth_alias = six; _ = sixth_alias; }
        \\fn seventh(seven: u32) void { const seventh_alias = seven; _ = seventh_alias; }
        \\fn eighth(eight: u32) void { const eighth_alias = eight; _ = eighth_alias; }
        \\fn ninth(nine: u32) void { const ninth_alias = nine; _ = ninth_alias; }
        \\fn tenth(ten: u32) void { const tenth_alias = ten; _ = tenth_alias; }
        \\fn eleventh(eleven: u32) void { const eleventh_alias = eleven; _ = eleventh_alias; }
        \\fn twelfth(twelve: u32) void { const twelfth_alias = twelve; _ = twelfth_alias; }
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(&tree);
    const first = fns.next(&proto_buf).?;
    const first_bindings = try cache.localBindings(first.proto, first.body);
    const initial = first_bindings.find("initial").?;
    const saved = first_bindings.find("saved").?;
    var last = first_bindings;
    while (fns.next(&proto_buf)) |function| {
        last = try cache.localBindings(function.proto, function.body);
    }
    try std.testing.expectEqualStrings("twelve", last.find("twelfth_alias").?.origin.alias);
    try std.testing.expect(last.find("initial") == null);
    try std.testing.expectEqualStrings("initial", initial.name);
    try std.testing.expectEqual(local_bindings.OriginKind.param, std.meta.activeTag(initial.origin));
    try std.testing.expectEqualStrings("saved", saved.name);
    try std.testing.expectEqualStrings("initial", saved.origin.alias);
    const reacquired = try cache.localBindings(first.proto, first.body);
    try std.testing.expectEqualStrings("initial", reacquired.find("saved").?.origin.alias);
    try std.testing.expect(reacquired.find("twelfth_alias") == null);
}

test "FileCache: resolveTransitiveTakes chains via .destroy(self) seed" {
    const gpa = std.testing.allocator;
    // A real consuming chain: kill calls .destroy(self) directly
    // (R8b infers takes=0), wrapper/outer propagate via R10 Case A.
    const src: [:0]const u8 =
        \\const T = struct {
        \\    pub fn kill(self: *T, gpa: std.mem.Allocator) void {
        \\        gpa.destroy(self);
        \\    }
        \\    pub fn wrapper(self: *T, gpa: std.mem.Allocator) void {
        \\        self.kill(gpa);
        \\    }
        \\    pub fn outer(self: *T, gpa: std.mem.Allocator) void {
        \\        self.wrapper(gpa);
        \\    }
        \\};
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();

    try cache.resolveTransitiveTakes();

    // `kill` directly takes self via gpa.destroy(self) (R8b direct).
    const kill_s = (try cache.summaryByMethod("T", "kill")).?;
    try std.testing.expectEqual(@as(?u32, 0), kill_s.takes_ownership_of);
    // `wrapper` calls `self.kill(gpa)` — kill takes 0, so wrapper takes self.
    const wrapper_s = (try cache.summaryByMethod("T", "wrapper")).?;
    try std.testing.expectEqual(@as(?u32, 0), wrapper_s.takes_ownership_of);
    // `outer` calls `self.wrapper(gpa)` — third-level chain.
    const outer_s = (try cache.summaryByMethod("T", "outer")).?;
    try std.testing.expectEqual(@as(?u32, 0), outer_s.takes_ownership_of);
}

test "FileCache: anyMethodAllocatesSelf detects type with heap factory method" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const std = @import("std");
        \\const Foo = struct {
        \\    x: u32,
        \\    pub fn create(alloc: std.mem.Allocator) !*Foo {
        \\        return try alloc.create(Foo);
        \\    }
        \\    pub fn deinit(self: *Foo) void { _ = self; }
        \\};
        \\const Bar = struct {
        \\    pub fn deinit(self: *Bar) void { _ = self; }
        \\};
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-heap-factory-test.zig" });
    defer gpa.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, src);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);

    try std.testing.expect(try cache.anyMethodAllocatesSelf("Foo"));
    try std.testing.expect(!try cache.anyMethodAllocatesSelf("Bar"));
    try std.testing.expect(!try cache.anyMethodAllocatesSelf("Missing"));
}

test "FileCache: summaryOfFn fills deep fields (heap_allocates_self + result_heap_fields)" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const std = @import("std");
        \\const Foo = struct {
        \\    bytes: []u8,
        \\    pub fn init(self_alloc: std.mem.Allocator) !*Foo {
        \\        const f = try self_alloc.create(Foo);
        \\        f.* = .{ .bytes = try self_alloc.alloc(u8, 16) };
        \\        return f;
        \\    }
        \\};
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-heap-summary-test.zig" });
    defer gpa.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, src);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);

    // Find the init fn_decl.
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const s = try cache.summaryOfFn(node);
        // Body has gpa.create(Foo) on a fn inside Foo → heap_allocates_self.
        try std.testing.expect(s.heap_allocates_self);
        try std.testing.expect(s.allocates);
        break;
    }
}

test "FileCache: summaryOf caches per body, classifies alloc as heap" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\fn alloc_one(gpa: std.mem.Allocator) ![]u8 {
        \\    return try gpa.alloc(u8, 1);
        \\}
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();

    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(&tree);
    const f = fns.next(&proto_buf).?;
    const a = try cache.summaryOf(f.proto, f.body);
    const b = try cache.summaryOf(f.proto, f.body);
    try std.testing.expect(a == b);
    try std.testing.expect(a.returns == .heap);
    try std.testing.expect(a.allocates);
}

// ── Cross-file call-graph tests ──────────────────────────────────────

test "FileCache: summaryByMethodCrossFile finds direct takes in imported file" {
    // Verifies that a method defined in an @import'd file is discovered
    // and its `takes_ownership_of` is inferred via inferDirectTakes.
    const gpa = std.testing.allocator;
    const tio = std.testing.io;

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // `destroyer.zig` — defines a type whose `kill` directly frees self.
    try tmp.dir.writeFile(tio, .{
        .sub_path = "destroyer.zig",
        .data =
        \\pub const Node = struct {
        \\    pub fn kill(self: *Node, gpa: std.mem.Allocator) void {
        \\        gpa.destroy(self);
        \\    }
        \\};
        ,
    });

    // A second import declares the same leaf name. The qualified alias must
    // select the declaration whose method actually frees its receiver.
    try tmp.dir.writeFile(tio, .{
        .sub_path = "observer.zig",
        .data =
        \\pub const Node = struct {
        \\    pub fn kill(self: *Node) void { _ = self; }
        \\};
        ,
    });
    // `consumer.zig` imports both modules; their `Node` declarations must
    // remain distinct at lookup time.
    try tmp.dir.writeFile(tio, .{ .sub_path = "consumer.zig", .data =
        \\const destroyer = @import("./destroyer.zig");
        \\const observer = @import("./observer.zig");
        \\const SelectedNode = @import("./destroyer.zig").Node;
        \\pub fn useNode(n: *destroyer.Node, o: *observer.Node) void {
        \\    _ = n;
        \\    _ = o;
        \\}
    });

    const fixture_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(fixture_root);
    const from_path = try std.fs.path.join(gpa, &.{ fixture_root, "consumer.zig" });
    defer gpa.free(from_path);

    const consumer_src: [:0]const u8 =
        \\const destroyer = @import("./destroyer.zig");
        \\const observer = @import("./observer.zig");
        \\const SelectedNode = @import("./destroyer.zig").Node;
        \\pub fn useNode(n: *destroyer.Node, o: *observer.Node) void { _ = n; _ = o; }
    ;
    var consumer_tree = try Ast.parse(gpa, consumer_src, .zig);
    defer consumer_tree.deinit(gpa);

    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{fixture_root} });
    defer pc.deinit();

    var cache = FileCache.init(gpa, &consumer_tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    const destroyed = (try cache.summaryByMethodCrossFile("destroyer.Node", "kill")) orelse
        return error.CrossFileResolutionFailed;
    try std.testing.expectEqual(@as(?u32, 0), destroyed.takes_ownership_of);
    const observed = (try cache.summaryByMethodCrossFile("observer.Node", "kill")) orelse
        return error.CrossFileResolutionFailed;
    try std.testing.expectEqual(@as(?u32, null), observed.takes_ownership_of);
    const selected = (try cache.summaryByMethodCrossFile("SelectedNode", "kill")) orelse
        return error.CrossFileResolutionFailed;
    try std.testing.expectEqual(@as(?u32, 0), selected.takes_ownership_of);
    if (try cache.summaryByMethodCrossFile("Node", "kill")) |_| {
        return error.TestUnexpectedResult;
    }
}

test "FileCache: foreign ownership and field summaries survive allocation failure and retry" {
    // Read genuine delegated ownership, non-taking methods and owned field
    // paths through the consumer API, including after an interrupted fold.
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{
        .sub_path = "owners.zig",
        .data =
        \\const std = @import("std");
        \\pub const Node = struct {
        \\    payload: []u8,
        \\    pub fn observe(self: *Node) void { _ = self; }
        \\    pub fn kill(self: *Node, gpa: std.mem.Allocator) void { gpa.destroy(self); }
        \\    pub fn delegated(self: *Node, gpa: std.mem.Allocator) void { self.kill(gpa); }
        \\    pub fn release(self: *Node, gpa: std.mem.Allocator) void { gpa.free(self.payload); }
        \\};
        ,
    });
    const src: [:0]const u8 =
        \\const owners = @import("./owners.zig");
        \\const Selected = @import("./owners.zig").Node;
        \\fn use(node: *owners.Node) void { _ = node; }
    ;
    try tmp.dir.writeFile(io, .{ .sub_path = "consumer.zig", .data = src });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const path = try std.fs.path.join(gpa, &.{ root, "consumer.zig" });
    defer gpa.free(path);
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var project = project_cache_mod.ProjectCache.init(gpa, io, .{ .roots = &.{root} });
    defer project.deinit();

    const readSummaries = struct {
        fn run(cache: *FileCache) !void {
            for (0..2) |_| {
                const observed = (try cache.summaryByMethodCrossFile("owners.Node", "observe")) orelse
                    return error.CrossFileResolutionFailed;
                try std.testing.expectEqual(@as(?u32, null), observed.takes_ownership_of);
                const delegated = (try cache.summaryByMethodCrossFile("Selected", "delegated")) orelse
                    return error.CrossFileResolutionFailed;
                try std.testing.expectEqual(@as(?u32, 0), delegated.takes_ownership_of);
                const released = (try cache.summaryByMethodCrossFile("owners.Node", "release")) orelse
                    return error.CrossFileResolutionFailed;
                try std.testing.expectEqual(@as(?u32, null), released.takes_ownership_of);
                var found_payload = false;
                for (released.freed_paths) |field| {
                    if (field.param == 0 and std.mem.eql(u8, field.path, "payload")) {
                        found_payload = true;
                    }
                }
                try std.testing.expect(found_payload);
            }
        }
    }.run;

    var fail_offset: usize = 0;
    while (true) : (fail_offset += 1) {
        var failing: std.testing.FailingAllocator = .init(gpa, .{});
        var cache = FileCache.init(failing.allocator(), &tree);
        defer cache.deinit();
        cache.setProject(&project, path);
        // Admit and resolve the declarations before testing summary failures.
        _ = cache.findMethodAcrossImports("owners.Node", "observe") orelse
            return error.CrossFileResolutionFailed;
        _ = cache.findMethodAcrossImports("Selected", "delegated") orelse
            return error.CrossFileResolutionFailed;
        _ = cache.findMethodAcrossImports("owners.Node", "release") orelse
            return error.CrossFileResolutionFailed;
        failing.fail_index = failing.alloc_index + fail_offset;
        readSummaries(&cache) catch |err| {
            try std.testing.expectEqual(error.OutOfMemory, err);
            try std.testing.expect(failing.has_induced_failure);
            failing.fail_index = std.math.maxInt(usize);
            try readSummaries(&cache);
            continue;
        };
        if (!failing.has_induced_failure) break;
    }
}

test "FileCache: resolved foreign summaries own nested effect data" {
    const gpa = std.testing.allocator;
    const foreign_src: [:0]const u8 =
        \\const std = @import("std");
        \\const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\pub const Thing = struct {
        \\    payload: []u8,
        \\    enabled: bool,
        \\    inner: Inner,
        \\    pub fn release(self: *Thing, gpa: std.mem.Allocator) void {
        \\        self.inner.deinit();
        \\        gpa.free(self.payload);
        \\        self.enabled = false;
        \\    }
        \\    pub fn build(gpa: std.mem.Allocator) !Thing {
        \\        return .{ .payload = try gpa.alloc(u8, 2), .enabled = true, .inner = .{} };
        \\    }
        \\};
    ;
    const caller_src: [:0]const u8 = "";
    var caller_tree = try Ast.parse(gpa, caller_src, .zig);
    defer caller_tree.deinit(gpa);
    var cache = FileCache.init(gpa, &caller_tree);
    defer cache.deinit();

    const summaries = blk: {
        var foreign_tree = try Ast.parse(gpa, foreign_src, .zig);
        defer foreign_tree.deinit(gpa);
        var foreign_cache = FileCache.init(gpa, &foreign_tree);
        defer foreign_cache.deinit();

        const model = try foreign_cache.fileModel();
        const thing = model.findType("Thing") orelse return error.TestUnexpectedResult;
        const release = thing.findMethod("release") orelse return error.TestUnexpectedResult;
        const build = thing.findMethod("build") orelse return error.TestUnexpectedResult;
        const release_summary = (try cache.summaryOfDeclaration(.{
            .tree = &foreign_tree,
            .module = .unscoped,
            .fn_decl = release.fn_decl,
        })) orelse return error.TestUnexpectedResult;
        const build_summary = (try cache.summaryOfDeclaration(.{
            .tree = &foreign_tree,
            .module = .unscoped,
            .fn_decl = build.fn_decl,
        })) orelse return error.TestUnexpectedResult;
        break :blk .{ .release = release_summary, .build = build_summary };
    };

    var freed_payload = false;
    for (summaries.release.freed_paths) |path| {
        if (path.param == 0 and std.mem.eql(u8, path.path, "payload")) freed_payload = true;
    }
    try std.testing.expect(freed_payload);

    var wrote_enabled = false;
    for (summaries.release.written_paths) |path| {
        if (path.param == 0 and std.mem.eql(u8, path.path, "enabled")) wrote_enabled = true;
    }
    try std.testing.expect(wrote_enabled);

    var freed_inner = false;
    for (summaries.release.may_free_fields) |field| {
        if (field.param == 0 and
            std.mem.eql(u8, field.field, "inner") and
            std.mem.eql(u8, field.method, "deinit"))
        {
            freed_inner = true;
        }
    }
    try std.testing.expect(freed_inner);

    var allocated_payload = false;
    for (summaries.build.result_heap_fields) |field| {
        if (std.mem.eql(u8, field, "payload")) allocated_payload = true;
    }
    try std.testing.expect(allocated_payload);
}

test "FileCache: resolveTransitiveTakes propagates through cross-file callee" {
    // `wrapper` in this file calls `node.kill(gpa)` where `kill` is
    // defined in an @import'd file.  resolveTransitiveTakes should
    // propagate takes_ownership_of=0 into `wrapper`.
    const gpa = std.testing.allocator;
    const tio = std.testing.io;

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.writeFile(tio, .{
        .sub_path = "node_lib.zig",
        .data =
        \\pub const Node = struct {
        \\    pub fn kill(self: *Node, gpa: std.mem.Allocator) void {
        \\        gpa.destroy(self);
        \\    }
        \\};
        ,
    });
    try tmp.dir.writeFile(tio, .{
        .sub_path = "wrapper.zig",
        .data =
        \\const node_lib = @import("./node_lib.zig");
        \\pub fn wrapper(node: *node_lib.Node, gpa: std.mem.Allocator) void {
        \\    node.kill(gpa);
        \\}
        ,
    });

    const fixture_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(fixture_root);
    const from_path = try std.fs.path.join(gpa, &.{ fixture_root, "wrapper.zig" });
    defer gpa.free(from_path);

    const src: [:0]const u8 =
        \\const node_lib = @import("./node_lib.zig");
        \\pub fn wrapper(node: *node_lib.Node, gpa: std.mem.Allocator) void {
        \\    node.kill(gpa);
        \\}
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);

    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{fixture_root} });
    defer pc.deinit();

    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    try cache.resolveTransitiveTakes();

    // `wrapper` calls `node.kill(gpa)` where `kill` takes ownership of
    // its receiver (param 0).  After transitive propagation, `wrapper`
    // should also have takes_ownership_of = 0 (its first param `node`).
    const summary = (try cache.summaryByName("wrapper")) orelse return error.MissingSummary;
    try std.testing.expectEqual(@as(?u32, 0), summary.takes_ownership_of);
}

test "FileCache: may_free_fields keeps same-file field deinit (refactor regression)" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\const Outer = struct {
        \\    inner: Inner,
        \\    pub fn deinitOuter(self: *Outer) void { self.inner.deinit(); }
        \\};
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    try cache.resolveTransitiveTakes();

    // `self.inner.deinit()` — Inner.deinit is cleanup-named → field kept.
    const s = (try cache.summaryByMethod("Outer", "deinitOuter")).?;
    try std.testing.expect(s.may_free_fields.len >= 1);
    try std.testing.expectEqualStrings("inner", s.may_free_fields[0].field);
}

test "FileCache: may_free_fields drops field whose type lacks the method" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const Inner = struct { x: u32 };
        \\const Outer = struct {
        \\    inner: Inner,
        \\    pub fn deinitOuter(self: *Outer) void { self.inner.deinit(); }
        \\};
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    try cache.resolveTransitiveTakes();

    // Inner has no `deinit` → the raw field-free entry is filtered out.
    const s = (try cache.summaryByMethod("Outer", "deinitOuter")).?;
    try std.testing.expectEqual(@as(usize, 0), s.may_free_fields.len);
}

test "FileCache: may_free_fields resolves CROSS-FILE field deinit (#20)" {
    // The composed-owner shape `self.inner.deinit()` where `inner`'s type
    // lives in an @import'd file.  Before #20 the field was unconditionally
    // dropped at the file boundary; now filterMayFreeFields resolves the
    // cleanup method cross-file via summaryByMethodCrossFile.
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.writeFile(tio, .{
        .sub_path = "inner.zig",
        .data =
        \\pub const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        ,
    });
    try tmp.dir.writeFile(tio, .{
        .sub_path = "outer.zig",
        .data =
        \\const innermod = @import("./inner.zig");
        \\pub const Outer = struct {
        \\    inner: innermod.Inner,
        \\    pub fn deinitOuter(self: *Outer) void { self.inner.deinit(); }
        \\};
        ,
    });

    const fixture_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(fixture_root);
    const from_path = try std.fs.path.join(gpa, &.{ fixture_root, "outer.zig" });
    defer gpa.free(from_path);

    const outer_src: [:0]const u8 =
        \\const innermod = @import("./inner.zig");
        \\pub const Outer = struct {
        \\    inner: innermod.Inner,
        \\    pub fn deinitOuter(self: *Outer) void { self.inner.deinit(); }
        \\};
    ;
    var tree = try Ast.parse(gpa, outer_src, .zig);
    defer tree.deinit(gpa);

    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{fixture_root} });
    defer pc.deinit();
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    try cache.resolveTransitiveTakes();

    // The owner resolves its field type through the exact `innermod` alias,
    // then keeps the cleanup effect declared by `inner.zig`.
    const s = (try cache.summaryByMethod("Outer", "deinitOuter")).?;
    try std.testing.expect(s.may_free_fields.len >= 1);
    try std.testing.expectEqualStrings("inner", s.may_free_fields[0].field);
}

test "FileCache: summaryByMethodCrossFile resolves TRANSITIVE takes in foreign file (#20)" {
    // `kill` doesn't free directly — it DELEGATES to a same-file
    // `reallyFree` that does.  Direct inference yields null; cross-file
    // resolution must follow the foreign file's own transitive
    // propagation to see that `kill` takes ownership of self.
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.writeFile(tio, .{
        .sub_path = "destroyer.zig",
        .data =
        \\pub const Xf20Node = struct {
        \\    pub fn kill(self: *Xf20Node, gpa: std.mem.Allocator) void {
        \\        self.reallyFree(gpa);
        \\    }
        \\    pub fn reallyFree(self: *Xf20Node, gpa: std.mem.Allocator) void {
        \\        gpa.destroy(self);
        \\    }
        \\};
        ,
    });
    try tmp.dir.writeFile(tio, .{
        .sub_path = "consumer.zig",
        .data =
        \\const destroyer = @import("./destroyer.zig");
        \\pub fn useNode(n: *destroyer.Xf20Node) void { _ = n; }
        ,
    });

    const fixture_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(fixture_root);
    const from_path = try std.fs.path.join(gpa, &.{ fixture_root, "consumer.zig" });
    defer gpa.free(from_path);

    const consumer_src: [:0]const u8 =
        \\const destroyer = @import("./destroyer.zig");
        \\pub fn useNode(n: *destroyer.Xf20Node) void { _ = n; }
    ;
    var tree = try Ast.parse(gpa, consumer_src, .zig);
    defer tree.deinit(gpa);

    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{fixture_root} });
    defer pc.deinit();
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    // Resolve through the exact `destroyer` import; the foreign method's
    // same-file transitive takes effect is returned by value.
    const s = (try cache.summaryByMethodCrossFile("destroyer.Xf20Node", "kill")) orelse
        return error.CrossFileResolutionFailed;
    try std.testing.expectEqual(@as(?u32, 0), s.takes_ownership_of);
}

test "FileCache: project-less FileCache computes transitive takes (#20 mechanism)" {
    // Deterministic guard for the mechanism summaryByMethodCrossFile relies
    // on for cross-file TRANSITIVE takes: a throwaway project-less FileCache
    // built over a foreign file's tree resolves a delegating method's takes
    // via the same-file fixed point.  `kill` delegates to `reallyFree` which
    // destroys self — so kill transitively takes ownership of self (param 0).
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\pub const Xf20Node = struct {
        \\    pub fn kill(self: *Xf20Node, g: std.mem.Allocator) void { self.reallyFree(g); }
        \\    pub fn reallyFree(self: *Xf20Node, g: std.mem.Allocator) void { g.destroy(self); }
        \\};
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    // No setProject — exactly the project-less foreign cache that
    // summaryByMethodCrossFile constructs over rm.tree.
    var fc = FileCache.init(gpa, &tree);
    defer fc.deinit();
    try fc.resolveTransitiveTakes();

    const reallyFree = (try fc.summaryByMethod("Xf20Node", "reallyFree")).?;
    try std.testing.expectEqual(@as(?u32, 0), reallyFree.takes_ownership_of);
    const kill = (try fc.summaryByMethod("Xf20Node", "kill")).?;
    try std.testing.expectEqual(@as(?u32, 0), kill.takes_ownership_of);
}

test "effect: may_grow propagates through same-file self.method() (#20)" {
    // The unified effect propagation now follows METHOD calls (the old
    // bare-call-only phases skipped `self.grow()`).  `outer` calls
    // `self.grow()`, which grows a collection -> outer inherits may_grow.
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const std = @import("std");
        \\const T = struct {
        \\    list: std.ArrayList(u32),
        \\    fn grow(self: *T, x: u32) void { self.list.append(x) catch {}; }
        \\    fn outer(self: *T) void { self.grow(1); }
        \\};
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    try cache.resolveTransitiveTakes();
    const grow_s = (try cache.summaryByMethod("T", "grow")).?;
    try std.testing.expect(grow_s.may_grow_collections); // direct
    const outer_s = (try cache.summaryByMethod("T", "outer")).?;
    try std.testing.expect(outer_s.may_grow_collections); // transitive via self.grow()
}

test "effect: may_grow propagates across @import via method call (#20)" {
    // `run` calls `g.add(1)` where `g`'s type lives in another file and
    // `add` grows a collection.  run must inherit may_grow cross-file.
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(tio, .{
        .sub_path = "grower.zig",
        .data =
        \\const std = @import("std");
        \\pub const Xf20Grower = struct {
        \\    list: std.ArrayList(u32),
        \\    pub fn add(self: *Xf20Grower, x: u32) void { self.list.append(x) catch {}; }
        \\};
        ,
    });
    try tmp.dir.writeFile(tio, .{
        .sub_path = "caller.zig",
        .data =
        \\const grower = @import("./grower.zig");
        \\pub fn run(g: *grower.Xf20Grower) void { g.add(1); }
        ,
    });
    const fixture_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(fixture_root);
    const from_path = try std.fs.path.join(gpa, &.{ fixture_root, "caller.zig" });
    defer gpa.free(from_path);
    const caller_src: [:0]const u8 =
        \\const grower = @import("./grower.zig");
        \\pub fn run(g: *grower.Xf20Grower) void { g.add(1); }
    ;
    var tree = try Ast.parse(gpa, caller_src, .zig);
    defer tree.deinit(gpa);
    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{fixture_root} });
    defer pc.deinit();
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);
    try cache.resolveTransitiveTakes();
    // `grower.Xf20Grower` resolves through the exact import alias.
    const s = (try cache.summaryByName("run")).?;
    try std.testing.expect(s.may_grow_collections);
}

test "FileCache: qualified parameter effects distinguish nested import and local names" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{
        .sub_path = "owners.zig",
        .data =
        \\const std = @import("std");
        \\pub const Nested = struct {
        \\    pub const Node = struct {
        \\        pub fn kill(self: *Node, gpa: std.mem.Allocator) void {
        \\            gpa.destroy(self);
        \\        }
        \\        pub fn grow(self: *Node, gpa: std.mem.Allocator) void { self.items.append(gpa, 1) catch {}; }
        \\        items: std.ArrayList(u32),
        \\    };
        \\};
        ,
    });
    const src: [:0]const u8 =
        \\const std = @import("std");
        \\const owners = @import("./owners.zig");
        \\const Node = struct {
        \\    fn kill(_: *Node, _: std.mem.Allocator) void {}
        \\    fn grow(_: *Node, _: std.mem.Allocator) void {}
        \\};
        \\fn imported(node: *owners.Nested.Node, gpa: std.mem.Allocator) void {
        \\    node.kill(gpa);
        \\    node.grow(gpa);
        \\}
        \\fn local(node: *Node, gpa: std.mem.Allocator) void {
        \\    node.kill(gpa);
        \\    node.grow(gpa);
        \\}
    ;
    try tmp.dir.writeFile(io, .{ .sub_path = "caller.zig", .data = src });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const path = try std.fs.path.join(gpa, &.{ root, "caller.zig" });
    defer gpa.free(path);
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var project = project_cache_mod.ProjectCache.init(gpa, io, .{ .roots = &.{root} });
    defer project.deinit();
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&project, path);
    try cache.resolveTransitiveTakes();
    const imported = (try cache.summaryByName("imported")).?;
    try std.testing.expectEqual(@as(?u32, 0), imported.takes_ownership_of);
    try std.testing.expect(imported.may_grow_collections);
    const local = (try cache.summaryByName("local")).?;
    try std.testing.expectEqual(@as(?u32, null), local.takes_ownership_of);
    try std.testing.expect(!local.may_grow_collections);
}

test "FileCache: normal success cleanup differs from error and conditional sites" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const std = @import("std");
        \\fn always(gpa: std.mem.Allocator, data: []u8) void { gpa.free(data); }
        \\fn later(gpa: std.mem.Allocator, data: []u8) void { defer gpa.free(data); }
        \\fn error_cleanup(gpa: std.mem.Allocator, data: []u8) !void {
        \\    errdefer gpa.free(data);
        \\}
        \\fn conditional(gpa: std.mem.Allocator, data: []u8, yes: bool) void {
        \\    if (yes) gpa.free(data);
        \\}
        \\fn failed(gpa: std.mem.Allocator, data: []u8, yes: bool) !void {
        \\    if (yes) { gpa.free(data); return error.Failed; }
        \\}
        \\fn delegated(gpa: std.mem.Allocator, data: []u8) void { always(gpa, data); }
        \\const Pretend = struct { fn free(_: Pretend, _: []u8) void {} };
        \\fn impostor(p: Pretend, data: []u8) void { p.free(data); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-normal-cleanup-test.zig" });
    defer gpa.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, src);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    for ([_][]const u8{ "always", "later", "delegated" }) |name| {
        const summary = (try cache.summaryByName(name)).?.*;
        try std.testing.expectEqual(@as(usize, 1), summary.normal_success_definite_freed_paths.len);
        try std.testing.expectEqual(@as(u32, 1), summary.normal_success_definite_freed_paths[0].param);
    }
    for ([_][]const u8{ "error_cleanup", "failed", "impostor" }) |name| {
        const summary = (try cache.summaryByName(name)).?.*;
        try std.testing.expectEqual(@as(usize, 0), summary.normal_success_definite_freed_paths.len);
        try std.testing.expectEqual(@as(usize, 0), summary.normal_success_may_freed_paths.len);
    }
    const conditional = (try cache.summaryByName("conditional")).?.*;
    try std.testing.expectEqual(@as(usize, 0), conditional.normal_success_definite_freed_paths.len);
    try std.testing.expectEqual(@as(usize, 1), conditional.normal_success_may_freed_paths.len);
}

test "FileCache: retained formals require same typed owner field cleanup" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const std = @import("std");
        \\const Owner = struct {
        \\    gpa: std.mem.Allocator, first: []u8, second: []u8, borrowed: []u8,
        \\    fn init(gpa: std.mem.Allocator, borrowed: []u8, first: []u8, second: []u8) Owner {
        \\        return .{ .gpa = gpa, .borrowed = borrowed, .first = first, .second = second };
        \\    }
        \\    fn release(self: *Owner) void {
        \\        self.gpa.free(self.first);
        \\        self.gpa.free(self.second);
        \\    }
        \\};
        \\const Borrow = struct {
        \\    ctx: *u8,
        \\    fn init(ctx: *u8) Borrow { return .{ .ctx = ctx }; }
        \\    fn deinit(self: *Borrow) void { _ = self; }
        \\};
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-retained-summary-test.zig" });
    defer gpa.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, src);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const owner = (try cache.summaryByMethod("Owner", "init")).?.*;
    try std.testing.expectEqualSlices(u32, &.{ 2, 3 }, owner.retained_owned_params);
    try std.testing.expectEqual(@as(?u32, null), owner.takes_ownership_of);
    const borrowed = (try cache.summaryByMethod("Borrow", "init")).?.*;
    try std.testing.expectEqual(@as(usize, 0), borrowed.retained_owned_params.len);
}

test "FileCache: foreign positive cleanup and retention clones survive failure and retry" {
    const gpa = std.testing.allocator;
    const foreign_source: [:0]const u8 =
        \\const std = @import("std");
        \\pub const Owner = struct {
        \\    gpa: std.mem.Allocator, data: []u8,
        \\    pub fn init(gpa: std.mem.Allocator, data: []u8) Owner { return .{ .gpa = gpa, .data = data }; }
        \\    pub fn finish(self: *Owner) void { const alias = self; self.gpa.free(alias.data); }
        \\};
    ;
    const caller_source: [:0]const u8 =
        \\const std = @import("std");
        \\const owners = @import("./owners.zig");
        \\const Alias = owners.Owner;
        \\fn use(gpa: std.mem.Allocator, data: []u8) void {
        \\    var owner = Alias.init(gpa, data);
        \\    owner.finish();
        \\}
    ;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "owners.zig", .data = foreign_source });
    try tmp.dir.writeFile(io, .{ .sub_path = "caller.zig", .data = caller_source });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const caller_path = try std.fs.path.join(gpa, &.{ root, "caller.zig" });
    defer gpa.free(caller_path);
    var context: engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{root} };
    var caller_resolver: engine.TypeResolver = undefined;
    try caller_resolver.init(&context, gpa, caller_path, caller_source);
    defer caller_resolver.deinit();
    const tree = &caller_resolver.handle.document.tree;
    var release_token: ?Ast.TokenIndex = null;
    var init_token: ?Ast.TokenIndex = null;
    var index: usize = 1;
    while (index < tree.nodes.len) : (index += 1) {
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(index)) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
        const name = tree.tokenSlice(tree.lastToken(call.ast.fn_expr));
        if (std.mem.eql(u8, name, "finish")) release_token = tree.nodeMainToken(call.ast.fn_expr);
        if (std.mem.eql(u8, name, "init")) init_token = tree.nodeMainToken(call.ast.fn_expr);
    }
    const read = struct {
        fn run(cache: *FileCache, release: Ast.TokenIndex, init: Ast.TokenIndex) !void {
            const release_call = (try cache.actualCallSummaryAt(release, null)).?;
            const released = (try cache.summaryOfResolvedMethod(release_call.callee)).?;
            try std.testing.expectEqual(@as(usize, 1), released.normal_success_definite_freed_paths.len);
            try std.testing.expectEqualStrings("data", released.normal_success_definite_freed_paths[0].path);
            const init_call = (try cache.actualCallSummaryAt(init, null)).?;
            const retained = (try cache.summaryOfResolvedMethod(init_call.callee)).?;
            try std.testing.expectEqualSlices(u32, &.{1}, retained.retained_owned_params);
            try std.testing.expectEqualStrings("data", released.normal_success_may_freed_paths[0].path);
        }
    }.run;
    var offset: usize = 0;
    while (true) : (offset += 1) {
        var failing: std.testing.FailingAllocator = .init(gpa, .{});
        var cache = FileCache.init(failing.allocator(), &caller_resolver.handle.document.tree);
        defer cache.deinit();
        cache.setZls(&caller_resolver);
        failing.fail_index = failing.alloc_index + offset;
        read(&cache, release_token.?, init_token.?) catch |err| {
            try std.testing.expectEqual(error.OutOfMemory, err);
            try std.testing.expect(failing.has_induced_failure);
            failing.fail_index = std.math.maxInt(usize);
            try read(&cache, release_token.?, init_token.?);
            continue;
        };
        if (!failing.has_induced_failure) break;
    }
}

test "FileCache: all cleanup outcome payloads own receiving arena text" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var path_text = [_]u8{ 's', 'l', 'o', 't' };
    var method_text = [_]u8{ 'd', 'r', 'o', 'p' };
    var paths = [_]fn_summary.ParamPath{.{ .param = 2, .path = &path_text }};
    var fields = [_]fn_summary.FieldFree{.{ .param = 2, .field = &path_text, .method = &method_text }};
    var retained = [_]u32{3};
    var operations = [_]fn_summary.StorageOperation{.{ .path = paths[0], .kind = .replace, .allocator = paths[0] }};
    var storage_outcomes = [_]fn_summary.StorageOutcome{.{ .operations = &operations }};
    var source = fn_summary.FnSummary{ .normal_success_effects_complete = true, .error_effects_complete = true };
    inline for (.{ "normal_success_definite_freed_paths", "normal_success_may_freed_paths", "error_definite_freed_paths", "error_may_freed_paths" }) |name| {
        @field(source, name) = &paths;
    }
    inline for (.{ "normal_success_definite_free_fields", "normal_success_may_free_fields", "error_definite_free_fields", "error_may_free_fields" }) |name| {
        @field(source, name) = &fields;
    }
    source.retained_owned_params = &retained;
    source.normal_success_storage_outcomes = &storage_outcomes;
    source.error_storage_outcomes = &storage_outcomes;
    source.normal_success_storage_effects_complete = true;
    source.error_storage_effects_complete = true;
    const copied = try cloneFnSummary(arena.allocator(), source);
    @memset(&path_text, 'x');
    @memset(&method_text, 'x');
    paths[0].param = 9;
    fields[0].param = 9;
    retained[0] = 9;
    operations[0].path.param = 9;
    operations[0].kind = .release_current;
    operations[0].allocator = null;
    storage_outcomes[0].operations = &.{};
    inline for (.{ "normal_success_definite_freed_paths", "normal_success_may_freed_paths", "error_definite_freed_paths", "error_may_freed_paths" }) |name| {
        const copied_path = @field(copied, name)[0];
        try std.testing.expectEqual(@as(u32, 2), copied_path.param);
        try std.testing.expectEqualStrings("slot", copied_path.path);
    }
    inline for (.{ "normal_success_definite_free_fields", "normal_success_may_free_fields", "error_definite_free_fields", "error_may_free_fields" }) |name| {
        const copied_field = @field(copied, name)[0];
        try std.testing.expectEqual(@as(u32, 2), copied_field.param);
        try std.testing.expectEqualStrings("slot", copied_field.field);
        try std.testing.expectEqualStrings("drop", copied_field.method);
    }
    try std.testing.expectEqualSlices(u32, &.{3}, copied.retained_owned_params);
    try std.testing.expect(copied.normal_success_effects_complete);
    try std.testing.expect(copied.error_effects_complete);
    inline for (.{ "normal_success_storage_outcomes", "error_storage_outcomes" }) |name| {
        const copied_operation = @field(copied, name)[0].operations[0];
        try std.testing.expectEqual(@as(u32, 2), copied_operation.path.param);
        try std.testing.expectEqualStrings("slot", copied_operation.path.path);
        try std.testing.expect(copied_operation.kind == .replace);
        try std.testing.expectEqual(@as(u32, 2), copied_operation.allocator.?.param);
        try std.testing.expectEqualStrings("slot", copied_operation.allocator.?.path);
    }
    try std.testing.expect(copied.normal_success_storage_effects_complete);
    try std.testing.expect(copied.error_storage_effects_complete);
}

test "FileCache: nested saved payload releases refuse current-version mapping" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\fn drop(allocator: std.mem.Allocator, bytes: []u8) void { allocator.free(bytes); }
        \\const Holder = struct {
        \\    storage: struct { indexes: []u8 },
        \\    fn replace(self: *Holder, allocator: std.mem.Allocator) !void {
        \\        const old = self.storage.indexes;
        \\        self.storage.indexes = try allocator.alloc(u8, 8);
        \\        drop(allocator, old);
        \\    }
        \\};
        \\fn use(holder: *Holder, allocator: std.mem.Allocator) !void { try holder.replace(allocator); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-cleanup-saved-call-payload.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access or
            !std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "replace")) continue;
        const actual = (try cache.actualCallSummaryAt(tree.nodeMainToken(call.ast.fn_expr), null)).?;
        const summary = (try cache.summaryOfResolvedMethod(actual.callee)).?;
        try std.testing.expect(!summary.normal_success_storage_effects_complete);
        try std.testing.expectEqual(@as(usize, 1), summary.normal_success_may_freed_paths.len);
        try std.testing.expectEqualStrings("storage.indexes", summary.normal_success_may_freed_paths[0].path);
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), checked);
}

test "FileCache: active storage clone preflight uses cleanup allowance" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "fn use() void {}", .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const node = tree.rootDecls()[0];
    const operations = [_]fn_summary.StorageOperation{.{
        .path = .{ .param = 0, .path = "storage.indexes" },
        .kind = .replace,
    }};
    const outcomes = [_]fn_summary.StorageOutcome{.{ .operations = &operations }};
    const summary = fn_summary.FnSummary{ .normal_success_storage_outcomes = &outcomes };
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    try cache.enterNormalCleanup(node);
    defer cache.leaveNormalCleanup();
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    try cache.normalCleanupStorageWork(node, 50_000);
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.chargeCleanupStorageClone(summary, &tree, node));
    try std.testing.expectEqual(budget_mod.Limit.normal_cleanup_nodes, budget_mod.take().?.limit);
}

test "FileCache: foreign storage clone preflight retains initiating node ownership" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const io = std.testing.io;
    try tmp.dir.writeFile(io, .{
        .sub_path = "caller.zig",
        .data = "const imported = @import(\"foreign file%.zig\");\nfn caller() void {}",
    });
    try tmp.dir.writeFile(io, .{
        .sub_path = "foreign file%.zig",
        .data = "const padding = .{" ++ "0," ** 16 ++ "};\nfn foreign() void {}",
    });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const caller_path = try std.fs.path.join(gpa, &.{ root, "caller.zig" });
    defer gpa.free(caller_path);
    const foreign_path = try std.fs.path.join(gpa, &.{ root, "foreign file%.zig" });
    defer gpa.free(foreign_path);
    var context: engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{root} };
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, caller_path, null);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const imported = try context.sourceHandle(foreign_path, .unscoped);
    const foreign = &imported.document.tree;
    const source_scope = budget_mod.SourceScope.begin(&context.store);
    defer source_scope.end();
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const node = foreign.rootDecls()[1];
    try std.testing.expect(@intFromEnum(node) >= tree.nodes.len);
    const outcomes = [_]fn_summary.StorageOutcome{.{ .operations = &.{} }};
    const summary = fn_summary.FnSummary{ .normal_success_storage_outcomes = &outcomes };
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    try cache.enterNormalCleanupAt(foreign, node);
    defer cache.leaveNormalCleanup();
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    cleanup_budget.remaining = 0;
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.chargeCleanupStorageClone(summary, cleanup_budget.initiating_tree.?, cleanup_budget.initiating_node.?));
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.normal_cleanup_nodes, failure.limit);
    try std.testing.expectEqualStrings("foreign", failure.function.slice());
    try std.testing.expectEqualStrings(foreign_path, failure.document);
    try std.testing.expect(!std.mem.eql(u8, caller_path, failure.document));
    try std.testing.expectEqual(foreign.tokenStart(foreign.nodeMainToken(node)), failure.byte);
}

test "FileCache: cleanup freshness requires heap allocation provenance" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\fn use(allocator: std.mem.Allocator, capacity: usize) !void {
        \\    const scalar = capacity;
        \\    const literal = &[_]u8{};
        \\    const allocated = try allocator.alloc(u8, 4);
        \\    const alias = allocated;
        \\    var reused = allocated;
        \\    reused = try allocator.alloc(u8, 8);
        \\    const after = reused;
        \\    _ = scalar;
        \\    _ = literal;
        \\    _ = alias;
        \\    _ = after;
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-cleanup-heap-provenance.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        const declaration = tree.fullVarDecl(node) orelse continue;
        const name = tree.tokenSlice(declaration.ast.mut_token + 1);
        if (!std.mem.eql(u8, name, "scalar") and !std.mem.eql(u8, name, "literal") and
            !std.mem.eql(u8, name, "allocated") and !std.mem.eql(u8, name, "alias") and
            !std.mem.eql(u8, name, "after")) continue;
        const value = declaration.ast.init_node.unwrap().?;
        const expected = std.mem.eql(u8, name, "allocated") or std.mem.eql(u8, name, "alias");
        try std.testing.expectEqual(expected, try cache.normalCleanupFresh(value));
        const allocator = try cache.normalCleanupAllocator(value);
        try std.testing.expectEqual(expected, allocator != null);
        if (allocator) |path| {
            try std.testing.expectEqual(@as(u32, 0), path.param);
            try std.testing.expectEqualStrings("", path.path);
        }
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 5), checked);
}

test "FileCache: cleanup allocation retains a formal allocator field requirement" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Owner = struct {
        \\    allocator: std.mem.Allocator,
        \\    fn replace(self: *Owner) !void {
        \\        const fresh = try self.allocator.alloc(u8, 4);
        \\        _ = fresh;
        \\    }
        \\};
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-cleanup-field-provenance.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const declaration = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(declaration.ast.mut_token + 1), "fresh")) continue;
        const value = declaration.ast.init_node.unwrap().?;
        try std.testing.expect(try cache.normalCleanupFresh(value));
        const allocator = (try cache.normalCleanupAllocator(value)) orelse
            return error.MissingAllocatorProvenance;
        try std.testing.expectEqual(@as(u32, 0), allocator.param);
        try std.testing.expectEqualStrings("allocator", allocator.path);
        // Backing allocation identity does not certify its provider lifetime.
        try std.testing.expect(!try cache.provesFreshStorage(.{
            .first = tree.firstToken(value),
            .last = tree.lastToken(value),
        }, null));
        return;
    }
    return error.MissingAllocation;
}

test "FileCache: actual cleanup contexts retain conditional and error-only field hazards" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Holder = struct {
        \\    nested: struct { bytes: []u8 },
        \\    fn release(self: *Holder, allocator: std.mem.Allocator, comptime enabled: bool) void {
        \\        if (enabled) allocator.free(self.nested.bytes);
        \\    }
        \\    fn maybe(self: *Holder, allocator: std.mem.Allocator, enabled: bool) void {
        \\        if (enabled) allocator.free(self.nested.bytes);
        \\    }
        \\    fn start(self: *Holder, allocator: std.mem.Allocator, fail: bool) error{Start}!void {
        \\        errdefer allocator.free(self.nested.bytes);
        \\        if (fail) return error.Start;
        \\    }
        \\    fn uncertain(self: *Holder, allocator: std.mem.Allocator) void {
        \\        allocator.free(self.nested.bytes);
        \\        unresolvedBoundary();
        \\    }
        \\    fn noop(self: *Holder) void { _ = self; }
        \\};
        \\fn use(holder: *Holder, allocator: std.mem.Allocator, enabled: bool, fail: bool) void {
        \\    holder.release(allocator, true);
        \\    holder.release(allocator, false);
        \\    holder.maybe(allocator, enabled);
        \\    holder.start(allocator, fail) catch {};
        \\    holder.uncertain(allocator);
        \\    holder.noop();
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-actual-cleanup-contexts.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
        const name = tree.tokenSlice(tree.lastToken(call.ast.fn_expr));
        if (!std.mem.eql(u8, name, "release") and !std.mem.eql(u8, name, "maybe") and
            !std.mem.eql(u8, name, "start") and !std.mem.eql(u8, name, "uncertain") and
            !std.mem.eql(u8, name, "noop")) continue;
        const record = (try cache.actualCallSummaryAt(tree.nodeMainToken(call.ast.fn_expr), null)).?;
        const summary = (try cache.summaryOfResolvedMethod(record.callee)).?;
        if (std.mem.eql(u8, name, "release")) {
            const enabled = std.mem.eql(u8, tree.getNodeSource(call.ast.params[1]), "true");
            const expected: usize = @intFromBool(enabled);
            try std.testing.expectEqual(expected, summary.normal_success_definite_freed_paths.len);
            try std.testing.expectEqual(expected, summary.normal_success_may_freed_paths.len);
            try std.testing.expect(summary.normal_success_effects_complete);
        } else if (std.mem.eql(u8, name, "maybe") or std.mem.eql(u8, name, "uncertain")) {
            try std.testing.expectEqual(@as(usize, 0), summary.normal_success_definite_freed_paths.len);
            try std.testing.expectEqual(@as(usize, 1), summary.normal_success_may_freed_paths.len);
            try std.testing.expectEqual(std.mem.eql(u8, name, "maybe"), summary.normal_success_effects_complete);
        } else if (std.mem.eql(u8, name, "start")) {
            try std.testing.expectEqual(@as(usize, 0), summary.normal_success_may_freed_paths.len);
            try std.testing.expectEqual(@as(usize, 1), summary.error_definite_freed_paths.len);
            try std.testing.expectEqual(@as(usize, 1), summary.error_may_freed_paths.len);
            try std.testing.expect(summary.error_effects_complete);
        } else {
            try std.testing.expectEqual(@as(usize, 0), summary.normal_success_may_freed_paths.len);
            try std.testing.expect(summary.normal_success_effects_complete);
        }
        for (summary.normal_success_may_freed_paths) |path| {
            try std.testing.expectEqual(@as(u32, 0), path.param);
            try std.testing.expectEqualStrings("nested.bytes", path.path);
        }
        for (summary.error_may_freed_paths) |path| {
            try std.testing.expectEqual(@as(u32, 0), path.param);
            try std.testing.expectEqualStrings("nested.bytes", path.path);
        }
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 6), checked);
}

test "FileCache: value-only calls stay unknown without inventing cleanup certificates" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\fn sink(value: anytype) void { opaqueCallback(value); }
        \\fn scalar(count: usize, flag: bool) void {
        \\    sink(count);
        \\    sink(flag);
        \\    sink(.{count, flag});
        \\    std.debug.print("{d} {any}", .{count, flag});
        \\}
        \\fn storage(bytes: []u8) void { sink(bytes); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-value-cleanup-demand.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const scalar = (try cache.summaryByName("scalar")).?.*;
    try std.testing.expect(!scalar.normal_success_effects_complete);
    try std.testing.expectEqual(@as(usize, 0), scalar.normal_success_may_freed_paths.len);
    var queried_print = false;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "print")) continue;
        const actual = (try cache.actualCallSummaryAt(fresh_storage_mod.calleeQueryToken(tree, call), null)).?;
        const summary = (try cache.summaryOfResolvedMethod(actual.callee)).?;
        try std.testing.expect(!summary.normal_success_effects_complete);
        try std.testing.expect(!summary.error_effects_complete);
        try std.testing.expectEqual(@as(usize, 0), summary.normal_success_definite_freed_paths.len);
        try std.testing.expectEqual(@as(usize, 0), summary.normal_success_may_freed_paths.len);
        try std.testing.expectEqual(@as(usize, 0), summary.error_definite_freed_paths.len);
        try std.testing.expectEqual(@as(usize, 0), summary.error_may_freed_paths.len);
        try std.testing.expectEqual(@as(usize, 0), summary.retained_owned_params.len);
        queried_print = true;
    }
    try std.testing.expect(queried_print);
    const storage = (try cache.summaryByName("storage")).?.*;
    try std.testing.expect(!storage.normal_success_effects_complete);
    try std.testing.expectEqual(@as(usize, 0), storage.normal_success_definite_freed_paths.len);
    try std.testing.expectEqual(@as(usize, 0), storage.retained_owned_params.len);
}

test "FileCache: reflective exports refuse only the exact escaped declaration" {
    const cases = [_]struct { source: [:0]const u8, closed: bool }{
        .{ .source =
        \\fn target(value: usize) usize { return value; }
        \\fn other() void {}
        \\comptime { @export(&other, .{ .name = "other" }); }
        \\pub fn entry() usize { return target(5); }
        , .closed = true },
        .{ .source =
        \\fn target(value: usize) usize { return value; }
        \\comptime { @export(&target, .{ .name = "target" }); }
        \\pub fn entry() usize { return target(5); }
        , .closed = false },
        .{ .source =
        \\fn target(value: usize) usize { return value; }
        \\const alias = target;
        \\comptime { @export(&alias, .{ .name = "target" }); }
        \\pub fn entry() usize { return target(5); }
        , .closed = false },
        .{ .source =
        \\fn target(value: usize) usize { return value; }
        \\comptime { @export(unknownFunction, .{ .name = "unknown" }); }
        \\pub fn entry() usize { return target(5); }
        , .closed = false },
    };
    const gpa = std.testing.allocator;
    for (cases) |case| {
        var context: engine.TypeContext = undefined;
        try context.init(gpa, std.testing.io);
        defer context.deinit();
        var resolver: engine.TypeResolver = undefined;
        try resolver.init(&context, gpa, "/tmp/zbc-reflective-census.zig", case.source);
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        var cache = FileCache.init(gpa, tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        const model = try cache.fileModel();
        const target = model.findFn("target").?.fn_decl;
        const calls = try cache.closedLocalCalls(target);
        try std.testing.expectEqual(case.closed, calls != null);
        if (calls) |sites| try std.testing.expectEqual(@as(usize, 1), sites.len);
    }
}

test "FileCache: cleanup demand keeps multiple owned formals and separate subsets" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\var shared: []u8 = undefined;
        \\fn release(allocator: std.mem.Allocator, first: []u8, second: []u8) void {
        \\    allocator.free(first);
        \\    allocator.free(second);
        \\}
        \\fn both(allocator: std.mem.Allocator, first: []u8, second: []u8) void {
        \\    release(allocator, first, second);
        \\}
        \\fn onlyFirst(allocator: std.mem.Allocator, bytes: []u8) void {
        \\    release(allocator, bytes, shared);
        \\}
        \\fn onlySecond(allocator: std.mem.Allocator, bytes: []u8) void {
        \\    release(allocator, shared, bytes);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-formal-cleanup-demand.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const both = (try cache.summaryByName("both")).?.*;
    try std.testing.expect(both.normal_success_effects_complete);
    try std.testing.expectEqual(@as(usize, 2), both.normal_success_definite_freed_paths.len);
    for ([_][]const u8{ "onlyFirst", "onlySecond" }) |name| {
        const subset = (try cache.summaryByName(name)).?.*;
        try std.testing.expect(!subset.normal_success_effects_complete);
        try std.testing.expectEqual(@as(usize, 1), subset.normal_success_may_freed_paths.len);
        try std.testing.expectEqual(@as(u32, 1), subset.normal_success_may_freed_paths[0].param);
    }
}

test "FileCache: noreturn calls do not traverse unreachable cleanup outcomes" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\fn failed(message: []const u8) noreturn {
        \\    std.debug.panic("failure: {s}", .{message});
        \\}
        \\fn conditional(message: []const u8, fail: bool) void {
        \\    if (fail) failed(message);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-noreturn-cleanup.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const failed = (try cache.summaryByName("failed")).?.*;
    try std.testing.expect(!failed.normal_success_effects_complete);
    try std.testing.expect(!failed.error_effects_complete);
    try std.testing.expectEqual(@as(usize, 0), failed.normal_success_may_freed_paths.len);
    const conditional = (try cache.summaryByName("conditional")).?.*;
    try std.testing.expect(conditional.normal_success_effects_complete);
    try std.testing.expectEqual(@as(usize, 0), conditional.normal_success_may_freed_paths.len);
    try std.testing.expectEqual(@as(u32, 0), cleanup_budget.depth);
    try std.testing.expectEqual(@as(u32, 0), cleanup_budget.queries);
}

test "FileCache: possible outparameter mutation is not definite initialization" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const Pair = struct { a: u32, b: u32 };
        \\const Origin = struct { origin: [2]u32 };
        \\const Defaulted = struct { a: u32, b: u32 = undefined };
        \\fn originWrite(p: *Origin, input: u32) void { p.origin = .{ input, 0 }; }
        \\fn omittedWrite(p: *Defaulted) void { p.* = .{ .a = 1 }; }
        \\extern fn opaqueWrite(p: *Pair) void;
        \\fn whole(p: *Pair, value: u32) void { p.* = .{ .a = value, .b = 2 }; }
        \\fn fields(p: *Pair) void { p.a = 1; p.b = 2; }
        \\fn partial(p: *Pair) void { p.a = 1; }
        \\fn conditional(p: *Pair, yes: bool) void { if (yes) p.* = .{ .a = 1, .b = 2 }; }
        \\fn poison(p: *Pair) void { p.* = undefined; }
        \\fn noncovering(p: *Pair) void { p.a = 1; return; p.b = 2; }
        \\fn caller(yes: bool) void {
        \\    var unknown: Pair = undefined; opaqueWrite(&unknown);
        \\    var complete: Pair = undefined; whole(&complete, 3);
        \\    var covered: Pair = undefined; fields(&covered);
        \\    var missing: Pair = undefined; partial(&missing);
        \\    var branch: Pair = undefined; conditional(&branch, yes);
        \\    var poisoned: Pair = undefined; poison(&poisoned);
        \\    var early: Pair = undefined; noncovering(&early);
        \\    var projection: Pair = undefined; scalar(&projection.a);
        \\    var counter: u32 = undefined; scalar(&counter);
        \\    var origin: Origin = undefined; originWrite(&origin, 2);
        \\    var omitted: Defaulted = undefined; omittedWrite(&omitted);
        \\}
        \\fn scalar(p: *u32) void { p.* = 1; }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-outparameter-proof-test.zig" });
    defer gpa.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, src);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        const root = tokens.rootIdentifier(tree, operand).?;
        const use = (try cache.addressUseAt(tree.nodeMainToken(root))).?;
        const name = tree.tokenSlice(tree.nodeMainToken(root));
        try std.testing.expect(use.may_write);
        // `&projection.a` is a field operand: the callee stores all of that
        // one field, which is what its address designates. The consumer
        // treats it like the field store `projection.a = 1`.
        try std.testing.expectEqual(
            std.mem.eql(u8, name, "complete") or std.mem.eql(u8, name, "covered") or
                std.mem.eql(u8, name, "counter") or std.mem.eql(u8, name, "origin") or
                std.mem.eql(u8, name, "projection"),
            use.definite_write,
        );
    }
}

test "FileCache: namespace type values do not define undefined member values" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const N = struct { const good: u64 = 4; const bad: u64 = undefined; };
        \\const E = enum { good, pub const bad: @This() = undefined; };
        \\fn constant(out: *u64) void { out.* = N.good; }
        \\fn poison(out: *u64) void { out.* = N.bad; }
        \\fn tag(out: *E) void { out.* = E.good; }
        \\fn badTag(out: *E) void { out.* = E.bad; }
        \\fn use() void {
        \\    var safe_constant: u64 = undefined; constant(&safe_constant);
        \\    var unsafe_constant: u64 = undefined; poison(&unsafe_constant);
        \\    var safe_tag: E = undefined; tag(&safe_tag);
        \\    var unsafe_tag: E = undefined; badTag(&unsafe_tag);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-namespace-output-dependency.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var cases: usize = 0;
    for (tree.nodes.items(.tag), 0..) |node_tag, raw| {
        if (node_tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        if (tree.nodeTag(operand) != .identifier) continue;
        const name = tree.tokenSlice(tree.nodeMainToken(operand));
        if (!std.mem.startsWith(u8, name, "safe_") and !std.mem.startsWith(u8, name, "unsafe_")) continue;
        const use = (try cache.addressUseAt(tree.nodeMainToken(operand))).?;
        try std.testing.expectEqual(std.mem.startsWith(u8, name, "safe_"), use.definite_write);
        cases += 1;
    }
    try std.testing.expectEqual(@as(usize, 4), cases);
}

test "FileCache: exact copied pointer formals retain output identity" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\extern fn change(alias: *[*c]f64) void;
        \\fn translated(arg_hi: [*c]f64, arg_lo: [*c]f64, arg_a: f64, arg_b: f64) void {
        \\    @setFloatMode(.strict);
        \\    var hi = arg_hi; _ = &hi;
        \\    var lo = arg_lo; _ = &lo;
        \\    var a = arg_a; _ = &a;
        \\    var b = arg_b; _ = &b;
        \\    var e: f64 = undefined; _ = &e;
        \\    hi.* = a + b;
        \\    e = hi.* - a;
        \\    lo.* = b - e;
        \\}
        \\fn write(out: *f64, value: f64) void { out.* = value; }
        \\fn forward(out: *f64, value: f64) void {
        \\    const copied = out;
        \\    write(copied, value);
        \\}
        \\fn readInput(input: *const f64, out: *f64) void {
        \\    const copied_input = input;
        \\    const copied_output = out;
        \\    copied_output.* = copied_input.*;
        \\}
        \\fn rebound(out: [*c]f64, other: [*c]f64) void {
        \\    var copied = out;
        \\    copied = other;
        \\    copied.* = 1;
        \\}
        \\fn escaped(out: [*c]f64) void {
        \\    var copied = out;
        \\    change(&copied);
        \\    copied.* = 1;
        \\}
        \\fn poisoned(out: [*c]f64) void {
        \\    const copied = out;
        \\    copied.* = 1;
        \\    out.* = undefined;
        \\}
        \\fn use(value: f64) void {
        \\    var safe_high: f64 = undefined; var safe_low: f64 = undefined;
        \\    translated(&safe_high, &safe_low, value, 2);
        \\    var safe_forward: f64 = undefined; forward(&safe_forward, value);
        \\    const initialized: f64 = value;
        \\    var safe_input: f64 = undefined; readInput(&initialized, &safe_input);
        \\    var other: f64 = undefined;
        \\    var unsafe_rebound: f64 = undefined; rebound(&unsafe_rebound, &other);
        \\    var unsafe_escape: f64 = undefined; escaped(&unsafe_escape);
        \\    var unsafe_poison: f64 = undefined; poisoned(&unsafe_poison);
        \\    var unsafe_input: f64 = undefined; readInput(&other, &unsafe_input);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-copied-pointer-output.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var cases: usize = 0;
    var correct = true;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        if (tree.nodeTag(operand) != .identifier) continue;
        const name = tree.tokenSlice(tree.nodeMainToken(operand));
        if (!std.mem.startsWith(u8, name, "safe_") and !std.mem.startsWith(u8, name, "unsafe_")) continue;
        const use = (try cache.addressUseAt(tree.nodeMainToken(operand))).?;
        if (use.definite_write != std.mem.startsWith(u8, name, "safe_")) {
            std.debug.print("copied pointer case {s}: definite_write={any}\n", .{ name, use.definite_write });
            correct = false;
        }
        cases += 1;
    }
    try std.testing.expectEqual(@as(usize, 8), cases);
    try std.testing.expect(correct);
}

test "FileCache: checked scalar calls prove only successful defined results" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\extern fn opaqueValue(a: u64, b: u64) u64;
        \\fn opaqueFallible(a: u64, b: u64) !u64 { return opaqueValue(a, b); }
        \\fn checked(a: u64, b: u64, out: *u64) !void {
        \\    out.* = std.math.add(u64, a, b) catch return error.LimitExceeded;
        \\}
        \\fn checkedInput(input: *const u64, b: u64, out: *u64) !void {
        \\    out.* = std.math.add(u64, input.*, b) catch return error.LimitExceeded;
        \\}
        \\fn forwarded(a: u64, b: u64, out: *u64) !void {
        \\    out.* = std.math.sub(u64, a, b) catch |err| return err;
        \\}
        \\fn multiplied(a: u64, b: u64, out: *u64) !void {
        \\    out.* = std.math.mul(u64, a, b) catch return error.LimitExceeded;
        \\}
        \\fn opaqueOutput(a: u64, b: u64, out: *u64) !void {
        \\    out.* = opaqueFallible(a, b) catch return error.LimitExceeded;
        \\}
        \\fn wrongCatch(a: u64, b: u64, out: *u64) void {
        \\    out.* = std.math.add(u64, a, b) catch undefined;
        \\}
        \\fn wrongForward(a: u64, b: u64, out: *u64) !void {
        \\    out.* = std.math.add(u64, a, b) catch |err| { _ = err; return; };
        \\}
        \\fn onlyError(a: u64, b: u64) !u64 { _ = a; _ = b; return error.Bad; }
        \\fn errorOutput(a: u64, b: u64, out: *u64) !void {
        \\    out.* = onlyError(a, b) catch return error.LimitExceeded;
        \\}
        \\fn staleGuard(a: u64, b: u64) u64 {
        \\    var flag = false;
        \\    flag = true;
        \\    const cached = flag;
        \\    if (cached) return undefined;
        \\    return a + b;
        \\}
        \\fn staleOutput(a: u64, b: u64, out: *u64) void { out.* = staleGuard(a, b); }
        \\const Partial = struct { first: u64, second: u64 = undefined };
        \\fn partialValue(a: u64, b: u64) u64 {
        \\    const local: Partial = .{ .first = a };
        \\    _ = b;
        \\    return local.second;
        \\}
        \\fn partialOutput(a: u64, b: u64, out: *u64) void { out.* = partialValue(a, b); }
        \\fn caller(a: u64, b: u64) !void {
        \\    var safe_add: u64 = undefined; try checked(a, b, &safe_add);
        \\    var safe_sub: u64 = undefined; try forwarded(a, b, &safe_sub);
        \\    var safe_mul: u64 = undefined; try multiplied(a, b, &safe_mul);
        \\    const initialized: u64 = a;
        \\    var safe_pointer: u64 = undefined; try checkedInput(&initialized, b, &safe_pointer);
        \\    var poison: u64 = undefined;
        \\    var unsafe_input: u64 = undefined; try checked(poison, b, &unsafe_input);
        \\    var unsafe_pointer: u64 = undefined; try checkedInput(&poison, b, &unsafe_pointer);
        \\    var unsafe_opaque: u64 = undefined; try opaqueOutput(a, b, &unsafe_opaque);
        \\    var unsafe_catch: u64 = undefined; wrongCatch(a, b, &unsafe_catch);
        \\    var unsafe_forward: u64 = undefined; try wrongForward(a, b, &unsafe_forward);
        \\    var unsafe_error: u64 = undefined; try errorOutput(a, b, &unsafe_error);
        \\    var unsafe_stale: u64 = undefined; staleOutput(a, b, &unsafe_stale);
        \\    var unsafe_partial: u64 = undefined; partialOutput(a, b, &unsafe_partial);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-checked-scalar-output.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var cases: usize = 0;
    var correct = true;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        const name = tree.tokenSlice(tree.nodeMainToken(operand));
        if (!std.mem.startsWith(u8, name, "safe_") and !std.mem.startsWith(u8, name, "unsafe_")) continue;
        const use = (try cache.addressUseAt(tree.nodeMainToken(operand))).?;
        try std.testing.expect(use.may_write);
        if (use.definite_write != std.mem.startsWith(u8, name, "safe_")) {
            std.debug.print("checked scalar case {s}: definite_write={any}\n", .{ name, use.definite_write });
            correct = false;
        }
        const repeated = (try cache.addressUseAt(tree.nodeMainToken(operand))).?;
        try std.testing.expectEqual(use.definite_write, repeated.definite_write);
        cases += 1;
    }
    try std.testing.expectEqual(@as(usize, 12), cases);
    try std.testing.expect(correct);
}

test "FileCache: scalar output dependencies compose through calls and pointer inputs" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\extern fn opaqueValue(value: f64) f64;
        \\fn sum(a: f64, b: f64, tail: *f64) f64 {
        \\    const high = a + b;
        \\    tail.* = b - (high - a);
        \\    return high;
        \\}
        \\fn rounded(a: f64, b: f64) f64 { return @mulAdd(f64, a, b, -a); }
        \\fn compound(a: f64, out: *f64) f64 {
        \\    var tail: f64 = undefined;
        \\    const high = sum(a, rounded(a, a), &tail);
        \\    out.* = high + tail;
        \\    return high;
        \\}
        \\fn load(input: *const f64, out: *f64) void { out.* = input.*; }
        \\fn unresolved(a: f64, out: *f64) void { out.* = opaqueValue(a); }
        \\fn use(value: f64, input: *const f64) void {
        \\    var composed: f64 = undefined; _ = compound(value, &composed);
        \\    var loaded: f64 = undefined; load(input, &loaded);
        \\    var prior: f64 = undefined; const high = sum(value, 2, &prior);
        \\    var following: f64 = undefined; _ = sum(high, prior, &following);
        \\    var poison: f64 = undefined; var unsafe_actual: f64 = undefined; _ = sum(poison, 2, &unsafe_actual);
        \\    var unsafe_pointer: f64 = undefined; load(&poison, &unsafe_pointer);
        \\    var unsafe_opaque: f64 = undefined; unresolved(value, &unsafe_opaque);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-composed-output-dependencies.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        const root = tokens.rootIdentifier(tree, operand) orelse continue;
        const name = tree.tokenSlice(tree.nodeMainToken(root));
        if (!std.mem.eql(u8, name, "composed") and !std.mem.eql(u8, name, "loaded") and
            !std.mem.eql(u8, name, "following") and !std.mem.startsWith(u8, name, "unsafe_")) continue;
        const use = (try cache.addressUseAt(tree.nodeMainToken(root))).?;
        try std.testing.expectEqual(!std.mem.startsWith(u8, name, "unsafe_") and
            !std.mem.eql(u8, name, "loaded"), use.definite_write);
    }
}

test "FileCache: partial local output metadata remains an exact scalar dependency" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const Pair = struct { exponent: u32, inactive: [4]u32 };
        \\fn decode(out: *Pair, value: u32) void { out.exponent = value; }
        \\fn good(value: u32, out: *u32) void {
        \\    var decoded: Pair = undefined;
        \\    decode(&decoded, value);
        \\    out.* = decoded.exponent;
        \\}
        \\fn bad(value: u32, out: *u32) void {
        \\    var decoded: Pair = undefined;
        \\    decode(&decoded, value);
        \\    out.* = decoded.inactive[0];
        \\}
        \\fn use(value: u32) void {
        \\    var safe: u32 = undefined; good(value, &safe);
        \\    var unsafe: u32 = undefined; bad(value, &unsafe);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-local-partial-output-metadata.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        const root = tokens.rootIdentifier(tree, operand) orelse continue;
        const name = tree.tokenSlice(tree.nodeMainToken(root));
        if (!std.mem.eql(u8, name, "safe") and !std.mem.eql(u8, name, "unsafe")) continue;
        const use = (try cache.addressUseAt(tree.nodeMainToken(root))).?;
        try std.testing.expectEqual(std.mem.eql(u8, name, "safe"), use.definite_write);
    }
}

test "FileCache: root output certificates cache successes but not unsafe actuals" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn write(out: *u32, value: u32) void { out.* = value; }
        \\fn caller() void {
        \\    var good: u32 = undefined;
        \\    write(&good, 7);
        \\    var bad: u32 = undefined;
        \\    write(&bad, undefined);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-root-output-memo-test.zig" });
    defer gpa.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var good_call: ?Ast.Node.Index = null;
    var bad_call: ?Ast.Node.Index = null;
    for (cache.tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = cache.tree.fullCall(&buffer, node) orelse continue;
        if (call.ast.params.len != 2) continue;
        if (cache.tree.nodeTag(call.ast.params[1]) == .number_literal) good_call = node else bad_call = node;
    }
    try std.testing.expect(try cache.definiteCallParameterWrite(good_call.?, 0));
    try std.testing.expect(try cache.definiteCallParameterWrite(good_call.?, 0));
    try std.testing.expectEqual(@as(usize, 1), cache.definite_parameter_writes.count());
    try std.testing.expect(!try cache.definiteCallParameterWrite(bad_call.?, 0));
    try std.testing.expect(!try cache.definiteCallParameterWrite(bad_call.?, 0));
    try std.testing.expectEqual(@as(usize, 1), cache.definite_parameter_writes.count());
    var entries = cache.definite_parameter_writes.keyIterator();
    const key = entries.next().?.*;
    var other = key;
    other.parameter_index += 1;
    try std.testing.expect(!cache.definite_parameter_writes.contains(other));
    other = key;
    other.caller_context = key.callee_context;
    try std.testing.expect(!cache.definite_parameter_writes.contains(other));
}
test "FileCache: computed scalar output proof and consumer preserve unsafe controls" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const Replaced = struct { a: f64, b: f64 = undefined };
        \\const DefaultedReplacement = struct { a: f64, b: f64 = 2 };
        \\const NestedReplacement = struct { inner: Replaced = .{ .a = 1 }, c: f64 };
        \\extern fn external(p: *f64) void;
        \\extern fn externalValue() f64;
        \\fn computed(comptime T: type, a: T, b: T, out: *T) T {
        \\    @setFloatMode(.optimized);
        \\    const sum = a + b;
        \\    const tail = b - (sum - a);
        \\    out.* = tail;
        \\    return sum;
        \\}
        \\fn conditional(out: *f64, yes: bool) void { if (yes) out.* = 1; }
        \\fn early(out: *f64, yes: bool) void { if (yes) return; out.* = 1; }
        \\fn poison(out: *f64) void { const bad: f64 = undefined; out.* = bad + 1; }
        \\fn mutated(out: *f64) void { var value: f64 = 1; value = undefined; out.* = value + 1; }
        \\fn redefined(out: *f64) void { var value: f64 = undefined; value = 2; out.* = value + 1; }
        \\fn pointerLoad(out: *f64, input: *const f64) void { out.* = input.*; }
        \\fn unknownValue(out: *f64) void { out.* = externalValue(); }
        \\fn overwritten(out: *f64) void { out.* = 1; external(out); }
        \\fn aliasWrite(out: *f64) void { const alias = out; out.* = 1; alias.* = undefined; }
        \\fn shadowed(out: *f64, value: f64) void { const local = value; { const poisoned: f64 = undefined; out.* = poisoned; } _ = local; }
        \\fn mapped(input: *f64, value: f64, out: *f64) void { out.* = value + 1; _ = input; }
        \\fn inputValue(out: *f64, value: f64) void { out.* = value + 1; }
        \\fn scalarFromPair(out: *f64, value: struct { a: f64, b: f64 }) void { out.* = value.b; }
        \\fn replaced(out: *Replaced) void { out.b = 2; out.* = .{ .a = 1 }; }
        \\fn replacedDefined(out: *DefaultedReplacement) void { out.b = 2; out.* = .{ .a = 1 }; }
        \\fn replacedNested(out: *NestedReplacement) void { out.* = .{ .c = 1 }; }
        \\fn caller(yes: bool, value: f64, input: *const f64) void {
        \\    var computed_output: f64 = undefined; _ = computed(f64, value, 2, &computed_output);
        \\    var conditional_output: f64 = undefined; conditional(&conditional_output, yes);
        \\    var early_output: f64 = undefined; early(&early_output, yes);
        \\    var poisoned_output: f64 = undefined; poison(&poisoned_output);
        \\    var mutated_output: f64 = undefined; mutated(&mutated_output);
        \\    var redefined_output: f64 = undefined; redefined(&redefined_output);
        \\    var load_output: f64 = undefined; pointerLoad(&load_output, input);
        \\    var external_output: f64 = undefined; unknownValue(&external_output);
        \\    var overwritten_output: f64 = undefined; overwritten(&overwritten_output);
        \\    var alias_output: f64 = undefined; aliasWrite(&alias_output);
        \\    var shadow_output: f64 = undefined; shadowed(&shadow_output, value);
        \\    var mapped_input: f64 = undefined; var mapped_output: f64 = undefined; mapped(&mapped_input, 3, &mapped_output);
        \\    var bad_actual: f64 = undefined; var bad_actual_output: f64 = undefined; inputValue(&bad_actual_output, bad_actual);
        \\    const good_actual: f64 = value + 2; var local_actual_output: f64 = undefined; inputValue(&local_actual_output, good_actual);
        \\    var changed_actual: f64 = 2; changed_actual = undefined; var changed_actual_output: f64 = undefined; inputValue(&changed_actual_output, changed_actual);
        \\    var aggregate_output: f64 = undefined; scalarFromPair(&aggregate_output, .{ .a = 1, .b = undefined });
        \\    var replacement_output: Replaced = undefined; replaced(&replacement_output);
        \\    var default_output: DefaultedReplacement = undefined; replacedDefined(&default_output);
        \\    var nested_output: NestedReplacement = undefined; replacedNested(&nested_output);
        \\    _ = computed_output + 0;
        \\    _ = conditional_output + 0;
        \\    _ = early_output + 0;
        \\    _ = poisoned_output + 0;
        \\    _ = mutated_output + 0;
        \\    _ = redefined_output + 0;
        \\    _ = load_output + 0;
        \\    _ = external_output + 0;
        \\    _ = overwritten_output + 0;
        \\    _ = alias_output + 0;
        \\    _ = shadow_output + 0;
        \\    _ = mapped_input + 0;
        \\    _ = mapped_output + 0;
        \\    _ = bad_actual_output + 0;
        \\    _ = local_actual_output + 0;
        \\    _ = changed_actual_output + 0;
        \\    _ = aggregate_output + 0;
        \\    _ = replacement_output.b + 0;
        \\    _ = default_output.b + 0;
        \\    _ = nested_output.inner.b + 0;
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-computed-scalar-output-proof.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        const root = tokens.rootIdentifier(tree, operand).?;
        const use = (try cache.addressUseAt(tree.nodeMainToken(root))).?;
        const name = tree.tokenSlice(tree.nodeMainToken(root));
        const expected = std.mem.eql(u8, name, "computed_output") or
            std.mem.eql(u8, name, "redefined_output") or
            std.mem.eql(u8, name, "mapped_output") or
            std.mem.eql(u8, name, "local_actual_output") or std.mem.eql(u8, name, "default_output");
        try std.testing.expect(use.may_write);
        try std.testing.expectEqual(expected, use.definite_write);
        const repeated = (try cache.addressUseAt(tree.nodeMainToken(root))).?;
        try std.testing.expectEqual(expected, repeated.definite_write);
    }
    var caller: ?Ast.Node.Index = null;
    for (tree.rootDecls()) |declaration| {
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration) orelse continue;
        const name_token = proto.name_token orelse continue;
        if (std.mem.eql(u8, tree.tokenSlice(name_token), "caller")) caller = declaration;
    }
    var graph = (try cfg_builder_mod.lowerFunctionFullWithZls(
        gpa,
        tree,
        caller.?,
        &@import("../config.zig").Default,
        &cache,
        &resolver,
    )).?;
    defer graph.deinit(gpa);
    var problems: std.ArrayListUnmanaged(@import("../problem.zig").Problem) = .empty;
    defer {
        for (problems.items) |*problem| problem.deinit(gpa);
        problems.deinit(gpa);
    }
    try @import("../flow/worklist.zig").check(
        gpa,
        &graph,
        .{ .path = "/tmp/zbc-computed-scalar-output-proof.zig" },
        &problems,
    );
    const reads = [_]struct { name: []const u8, warns: bool }{
        .{ .name = "computed_output", .warns = false },
        .{ .name = "conditional_output", .warns = true },
        .{ .name = "early_output", .warns = true },
        .{ .name = "poisoned_output", .warns = true },
        .{ .name = "mutated_output", .warns = true },
        .{ .name = "redefined_output", .warns = false },
        .{ .name = "load_output", .warns = false },
        .{ .name = "external_output", .warns = false },
        .{ .name = "overwritten_output", .warns = false },
        .{ .name = "alias_output", .warns = true },
        .{ .name = "shadow_output", .warns = true },
        .{ .name = "mapped_input", .warns = true },
        .{ .name = "mapped_output", .warns = false },
        .{ .name = "bad_actual_output", .warns = true },
        .{ .name = "local_actual_output", .warns = false },
        .{ .name = "changed_actual_output", .warns = true },
        .{ .name = "aggregate_output", .warns = true },
        .{ .name = "replacement_output", .warns = true },
        .{ .name = "default_output", .warns = false },
        .{ .name = "nested_output", .warns = true },
    };
    for (reads) |read| {
        // The last occurrence is the real source read, not the earlier
        // address argument or declaration. Assert that exact diagnostic site.
        var read_token: ?Ast.TokenIndex = null;
        for (tree.tokens.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const token: Ast.TokenIndex = @intCast(raw);
            if (std.mem.eql(u8, tree.tokenSlice(token), read.name)) read_token = token;
        }
        const byte = tree.tokens.items(.start)[read_token.?];
        var reported = false;
        for (problems.items) |problem| {
            if (!std.mem.eql(u8, problem.rule_id, "use-undefined")) continue;
            if (problem.start.byte == byte and std.mem.indexOf(u8, problem.message, read.name) != null)
                reported = true;
        }
        if (read.warns != reported)
            std.debug.print("output read {s}: expected undefined={}, reported={}\n", .{ read.name, read.warns, reported });
        try std.testing.expectEqual(read.warns, reported);
    }
}

test "FileCache: output certificates retain skipped calls poisoned inputs and unselected errors" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\extern fn opaqueValue(input: *u32) void;
        \\fn fill(out: *u32) bool { out.* = 1; return true; }
        \\fn checked(out: *u32, fail: bool) !void { if (fail) return error.Bad; out.* = 1; }
        \\fn poison(input: *u32) void { input.* = undefined; }
        \\fn load(input: *const u32, out: *u32) void { out.* = input.*; }
        \\const Payload = struct { value: u32 };
        \\fn loadIndex(input: *const [4]u32, out: *u32) void { out.* = input[3]; }
        \\fn loadField(input: *const Payload, out: *u32) void { out.* = input.value; }
        \\fn loadSlice(input: []const u32, out: *u32) void { out.* = input[0]; }
        \\fn loadSliceLen(input: []const u32, out: *u32) void { out.* = @intCast(input.len); }
        \\fn loadValueIndex(input: [4]u32, out: *u32) void { out.* = input[3]; }
        \\fn loadValueField(input: Payload, out: *u32) void { out.* = input.value; }
        \\fn first(out: [*c]u32) void { out.* = 1; }
        \\fn skippedAnd(out: *u32) void { var temp: u32 = undefined; const flag = false and fill(&temp); _ = flag; out.* = temp; }
        \\fn skippedOr(out: *u32) void { var temp: u32 = undefined; const flag = true or fill(&temp); _ = flag; out.* = temp; }
        \\fn maybeAnd(out: *u32, yes: bool) void { var temp: u32 = undefined; const flag = yes and fill(&temp); _ = flag; out.* = temp; }
        \\fn selectedAnd(out: *u32) void { var temp: u32 = undefined; const flag = true and fill(&temp); _ = flag; out.* = temp; }
        \\fn discarded(out: *u32, fail: bool) void { var temp: u32 = undefined; _ = checked(&temp, fail); out.* = temp; }
        \\fn stored(out: *u32, fail: bool) void { var temp: u32 = undefined; const status = checked(&temp, fail); _ = status; out.* = temp; }
        \\fn selectedTry(out: *u32, fail: bool) !void { var temp: u32 = undefined; try checked(&temp, fail); out.* = temp; }
        \\fn selectedCatch(out: *u32, fail: bool) !void { var temp: u32 = undefined; checked(&temp, fail) catch |err| return err; out.* = temp; }
        \\fn selectedUnreachable(out: *u32, fail: bool) void { var temp: u32 = undefined; checked(&temp, fail) catch unreachable; out.* = temp; }
        \\fn cArray(out: *u32) void { var temp: [4]u32 = undefined; first(&temp); out.* = temp[3]; }
        \\fn cSlice(out: *u32) void { var temp: [4]u32 = undefined; first(temp[0..4]); out.* = temp[3]; }
        \\fn unsafe_and() u32 { var result: u32 = undefined; skippedAnd(&result); return result; }
        \\fn unsafe_or() u32 { var result: u32 = undefined; skippedOr(&result); return result; }
        \\fn unsafe_maybe(yes: bool) u32 { var result: u32 = undefined; maybeAnd(&result, yes); return result; }
        \\fn safe_and() u32 { var result: u32 = undefined; selectedAnd(&result); return result; }
        \\fn unsafe_direct(input: *u32) u32 { input.* = 2; input.* = undefined; var result: u32 = undefined; load(input, &result); return result; }
        \\fn unsafe_poison(input: *u32) u32 { input.* = 2; poison(input); var result: u32 = undefined; load(input, &result); return result; }
        \\fn safe_opaque(input: *u32) u32 { input.* = 2; opaqueValue(input); var result: u32 = undefined; load(input, &result); return result; }
        \\fn safe_entry(input: *u32) u32 { var result: u32 = undefined; load(input, &result); return result; }
        \\fn safe_rewritten(input: *u32) u32 { input.* = undefined; input.* = 2; var result: u32 = undefined; load(input, &result); return result; }
        \\fn safe_local() u32 { const temp: u32 = 2; var result: u32 = undefined; load(&temp, &result); return result; }
        \\fn unsafe_local() u32 { const temp: u32 = undefined; var result: u32 = undefined; load(&temp, &result); return result; }
        \\fn unsafe_discard(fail: bool) u32 { var result: u32 = undefined; discarded(&result, fail); return result; }
        \\fn unsafe_stored(fail: bool) u32 { var result: u32 = undefined; stored(&result, fail); return result; }
        \\fn safe_try(fail: bool) !u32 { var result: u32 = undefined; try selectedTry(&result, fail); return result; }
        \\fn safe_catch(fail: bool) !u32 { var result: u32 = undefined; try selectedCatch(&result, fail); return result; }
        \\fn safe_unreachable(fail: bool) u32 { var result: u32 = undefined; selectedUnreachable(&result, fail); return result; }
        \\fn unsafe_c_array() u32 { var result: [4]u32 = undefined; first(&result); return result[3]; }
        \\fn unsafe_c_nested() u32 { var result: u32 = undefined; cArray(&result); return result; }
        \\fn unsafe_c_slice() u32 { var result: [4]u32 = undefined; first(result[0..4]); return result[3]; }
        \\fn unsafe_c_slice_nested() u32 { var result: u32 = undefined; cSlice(&result); return result; }
        \\fn safe_c_scalar() u32 { var result: u32 = undefined; first(&result); return result; }
        \\fn unsafe_index(input: *[4]u32) u32 { input.* = undefined; var result: u32 = undefined; loadIndex(input, &result); return result; }
        \\fn unsafe_field(input: *Payload) u32 { input.* = undefined; var result: u32 = undefined; loadField(input, &result); return result; }
        \\fn unsafe_slice(input: []u32) u32 { input[0] = undefined; var result: u32 = undefined; loadSlice(input, &result); return result; }
        \\fn safe_slice_entry(input: []const u32) u32 { var result: u32 = undefined; loadSlice(input, &result); return result; }
        \\fn safe_index() u32 { const temp: [4]u32 = .{ 1, 2, 3, 4 }; var result: u32 = undefined; loadIndex(&temp, &result); return result; }
        \\fn unsafe_index_local() u32 { const temp: [4]u32 = undefined; var result: u32 = undefined; loadIndex(&temp, &result); return result; }
        \\fn safe_field() u32 { const temp: Payload = .{ .value = 1 }; var result: u32 = undefined; loadField(&temp, &result); return result; }
        \\fn unsafe_field_local() u32 { const temp: Payload = undefined; var result: u32 = undefined; loadField(&temp, &result); return result; }
        \\fn safe_slice_header(input: []u32) u32 { input[0] = undefined; var result: u32 = undefined; loadSliceLen(input, &result); return result; }
        \\fn safe_slice_payload() u32 { const temp: [4]u32 = .{ 1, 2, 3, 4 }; var result: u32 = undefined; loadSlice(temp[0..], &result); return result; }
        \\fn unsafe_slice_local() u32 { const temp: [4]u32 = undefined; var result: u32 = undefined; loadSlice(temp[0..], &result); return result; }
        \\fn safe_local_slice_header() u32 { const temp: [4]u32 = undefined; var result: u32 = undefined; loadSliceLen(temp[0..], &result); return result; }
        \\fn safe_byvalue_array() u32 { const temp: [4]u32 = .{ 1, 2, 3, 4 }; var result: u32 = undefined; loadValueIndex(temp, &result); return result; }
        \\fn safe_byvalue_field() u32 { const temp: Payload = .{ .value = 1 }; var result: u32 = undefined; loadValueField(temp, &result); return result; }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-output-certificate-paths.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var correct = true;
    for (tree.rootDecls()) |declaration| {
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration) orelse continue;
        const name = tree.tokenSlice(proto.name_token orelse continue);
        const safe = std.mem.startsWith(u8, name, "safe_");
        if (!safe and !std.mem.startsWith(u8, name, "unsafe_")) continue;
        var graph = (try cfg_builder_mod.lowerFunctionFullWithZls(
            gpa,
            tree,
            declaration,
            &@import("../config.zig").Default,
            &cache,
            &resolver,
        )).?;
        defer graph.deinit(gpa);
        var problems: std.ArrayListUnmanaged(@import("../problem.zig").Problem) = .empty;
        defer {
            for (problems.items) |*problem| problem.deinit(gpa);
            problems.deinit(gpa);
        }
        try @import("../flow/worklist.zig").check(
            gpa,
            &graph,
            .{ .path = "/tmp/zbc-output-certificate-paths.zig" },
            &problems,
        );
        var read_token: ?Ast.TokenIndex = null;
        var token = tree.firstToken(declaration);
        while (token <= tree.lastToken(declaration)) : (token += 1) {
            if (tree.tokenTag(token) == .identifier and std.mem.eql(u8, tree.tokenSlice(token), "result"))
                read_token = token;
        }
        const byte = tree.tokens.items(.start)[read_token.?];
        var reported = false;
        for (problems.items) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and problem.start.byte == byte)
                reported = true;
        }
        if (reported == safe) {
            std.debug.print("output certificate caller {s}: expected use-undefined={any}, found {any}\n", .{ name, !safe, reported });
            correct = false;
        }
    }
    try std.testing.expect(correct);
}

test "FileCache: successful branch and switch output stores preserve unsafe paths" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const Pair = struct { a: u32, b: u32 };
        \\fn poisonField(out: *Pair) void { out.a = undefined; out.b = 2; }
        \\fn poisonDelegate(out: *Pair) void { out.a = 1; poisonField(out); }
        \\const Endpoint = struct {
        \\    fn begin(_: *Endpoint, command: *usize, frame: *Pair) !void {
        \\        command.* = 1; frame.* = .{ .a = 2, .b = 3 };
        \\    }
        \\};
        \\fn scalar(out: *u32, yes: bool, value: u32) void {
        \\    if (yes) { out.* = value + 1; } else { const sum = value + 2; out.* = sum; }
        \\}
        \\fn aggregate(out: *Pair, yes: bool, input: Pair) void {
        \\    if (yes) out.* = input else out.* = input;
        \\}
        \\fn cOutput(out: [*c]u32, yes: bool) void { if (yes) out.* = 1 else out.* = 2; }
        \\fn cPair(high: [*c]u32, low: [*c]u32, value: u32) void {
        \\    high.* = value + 1; low.* = high.* - value;
        \\}
        \\fn first(out: *u32) void { out.* = 1; }
        \\fn second(out: *u32) void { out.* = 2; }
        \\fn delegates(out: *Pair, yes: bool) void {
        \\    if (yes) { first(&out.a); second(&out.b); } else { second(&out.b); first(&out.a); }
        \\}
        \\fn selection(out: *u32, yes: bool, value: u32) !u32 {
        \\    return switch (yes) {
        \\        true => blk: { out.* = 1; break :blk value; },
        \\        false => blk: { out.* = 2; break :blk value; },
        \\    };
        \\}
        \\fn errorExit(out: *u32, yes: bool) !void {
        \\    if (yes) return error.Failed;
        \\    out.* = 1;
        \\}
        \\const Status = enum { done, retry, fail };
        \\fn looping(out: *u32, status: Status) !void {
        \\    while (true) switch (status) {
        \\        .done => { out.* = 1; return; },
        \\        .retry => continue,
        \\        .fail => return error.Failed,
        \\    };
        \\}
        \\fn forwarded(out: *u32, status: Status) !void {
        \\    looping(out, status) catch |err| return err;
        \\}
        \\fn missing(out: *u32, yes: bool) void { if (yes) out.* = 1; }
        \\fn early(out: *u32, yes: bool) void { if (yes) return; out.* = 1; }
        \\fn poisoned(out: *u32, yes: bool) void { if (yes) out.* = 1 else out.* = undefined; }
        \\fn merged(out: *u32, yes: bool) void {
        \\    var value: u32 = undefined; if (yes) value = 1; out.* = value;
        \\}
        \\fn caller(endpoint: *Endpoint, yes: bool, input: Pair, value: u32, status: Status) !void {
        \\    var safe_scalar: u32 = undefined; scalar(&safe_scalar, yes, value);
        \\    var safe_aggregate: Pair = undefined; aggregate(&safe_aggregate, yes, input);
        \\    var safe_c: u32 = undefined; cOutput(&safe_c, yes);
        \\    var safe_c_high: u32 = undefined; var safe_c_low: u32 = undefined;
        \\    cPair(&safe_c_high, &safe_c_low, value);
        \\    var safe_delegates: Pair = undefined; delegates(&safe_delegates, yes);
        \\    var safe_switch: u32 = undefined; _ = try selection(&safe_switch, yes, value);
        \\    var safe_error: u32 = undefined; try errorExit(&safe_error, yes);
        \\    var safe_loop: u32 = undefined; try forwarded(&safe_loop, status);
        \\    var safe_command: usize = undefined; var safe_method: Pair = undefined;
        \\    try endpoint.begin(&safe_command, &safe_method);
        \\    var bad_missing: u32 = undefined; missing(&bad_missing, yes);
        \\    var bad_early: u32 = undefined; early(&bad_early, yes);
        \\    var bad_poison: u32 = undefined; poisoned(&bad_poison, yes);
        \\    var bad_merge: u32 = undefined; merged(&bad_merge, yes);
        \\    var bad_delegate: Pair = undefined; poisonDelegate(&bad_delegate);
        \\    _ = safe_scalar + safe_c + safe_switch + safe_error;
        \\    _ = safe_c_high + safe_c_low;
        \\    _ = safe_loop + 0;
        \\    _ = safe_aggregate.a + safe_delegates.b + safe_method.a;
        \\    _ = safe_command + 0;
        \\    _ = bad_missing + 0;
        \\    _ = bad_early + 0;
        \\    _ = bad_poison + 0;
        \\    _ = bad_merge + 0;
        \\    _ = bad_delegate.a + 0;
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-branch-output-proof.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var correct = true;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        const root = tokens.rootIdentifier(tree, operand).?;
        const name = tree.tokenSlice(tree.nodeMainToken(root));
        if (!std.mem.startsWith(u8, name, "safe_") and !std.mem.startsWith(u8, name, "bad_")) continue;
        const use = (try cache.addressUseAt(tree.nodeMainToken(root))).?;
        if (use.definite_write != std.mem.startsWith(u8, name, "safe_")) {
            std.debug.print("branch output case {s}: definite_write={any}\n", .{ name, use.definite_write });
            correct = false;
        }
    }
    try std.testing.expect(correct);
    var caller: ?Ast.Node.Index = null;
    for (tree.rootDecls()) |declaration| {
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration) orelse continue;
        const name_token = proto.name_token orelse continue;
        if (std.mem.eql(u8, tree.tokenSlice(name_token), "caller")) caller = declaration;
    }
    var graph = (try cfg_builder_mod.lowerFunctionFullWithZls(
        gpa,
        tree,
        caller.?,
        &@import("../config.zig").Default,
        &cache,
        &resolver,
    )).?;
    defer graph.deinit(gpa);
    var problems: std.ArrayListUnmanaged(@import("../problem.zig").Problem) = .empty;
    defer {
        for (problems.items) |*problem| problem.deinit(gpa);
        problems.deinit(gpa);
    }
    try @import("../flow/worklist.zig").check(gpa, &graph, .{ .path = "/tmp/zbc-branch-output-proof.zig" }, &problems);
    correct = true;
    for ([_][]const u8{
        "safe_scalar",    "safe_c",      "safe_switch",  "safe_error",  "safe_aggregate",
        "safe_delegates", "safe_method", "safe_command", "bad_missing", "bad_early",
        "bad_poison",     "bad_merge",   "safe_c_high",  "safe_c_low",  "safe_loop",
        "bad_delegate",
    }) |name| {
        var reported = false;
        for (problems.items) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                std.mem.indexOf(u8, problem.message, name) != null) reported = true;
        }
        if (reported != std.mem.startsWith(u8, name, "bad_")) {
            std.debug.print("branch output consumer case {s}: reported={any}\n", .{ name, reported });
            correct = false;
        }
    }
    try std.testing.expect(correct);
}

test "FileCache: complete aggregate literals supply scalar output dependencies" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const Inner = struct { value: u32 = 7 };
        \\const Context = struct {
        \\    inner: Inner = .{},
        \\    slots: [2]u32 = .{ 2, 3 },
        \\    fn output(self: *const Context, out: *u32) void { out.* = self.inner.value + self.slots[0]; }
        \\};
        \\fn Box(comptime T: type) type { return struct { value: T = 9 }; }
        \\const Partial = struct { good: u32 = 1, bad: u32 = undefined };
        \\const NestedPartial = struct { inner: Partial = .{} };
        \\fn write(value: u32, out: *u32) void { out.* = value; }
        \\fn local(value: u32) u32 {
        \\    const context: Context = .{ .inner = .{ .value = value } };
        \\    return context.inner.value;
        \\}
        \\fn caller(value: u32) void {
        \\    var safe_local: u32 = undefined; write(local(value), &safe_local);
        \\    const typed = Context{ .inner = .{ .value = value } };
        \\    var safe_typed: u32 = undefined; write(typed.inner.value, &safe_typed);
        \\    const defaulted: Context = .{};
        \\    var safe_default: u32 = undefined; write(defaulted.inner.value, &safe_default);
        \\    var safe_receiver: u32 = undefined; defaulted.output(&safe_receiver);
        \\    const generic: Box(u32) = .{};
        \\    var safe_generic: u32 = undefined; write(generic.value, &safe_generic);
        \\    const overridden: Partial = .{ .bad = value };
        \\    var safe_override: u32 = undefined; write(overridden.bad, &safe_override);
        \\    const omitted: Partial = .{};
        \\    var unsafe_omitted: u32 = undefined; write(omitted.bad, &unsafe_omitted);
        \\    const nested: NestedPartial = .{};
        \\    var unsafe_nested: u32 = undefined; write(nested.inner.bad, &unsafe_nested);
        \\    const explicit_nested: NestedPartial = .{ .inner = .{ .good = value } };
        \\    var unsafe_explicit_nested: u32 = undefined; write(explicit_nested.inner.bad, &unsafe_explicit_nested);
        \\    const unresolved: Missing = .{ .value = value };
        \\    var unsafe_unknown: u32 = undefined; write(unresolved.value, &unsafe_unknown);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-complete-aggregate-output.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var cases: usize = 0;
    var correct = true;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        const name = tree.tokenSlice(tree.nodeMainToken(operand));
        if (!std.mem.startsWith(u8, name, "safe_") and !std.mem.startsWith(u8, name, "unsafe_")) continue;
        const use = (try cache.addressUseAt(tree.nodeMainToken(operand))).?;
        try std.testing.expect(use.may_write);
        if (use.definite_write != std.mem.startsWith(u8, name, "safe_")) {
            std.debug.print("aggregate output case {s}: definite_write={any}\n", .{ name, use.definite_write });
            correct = false;
        }
        const repeated = (try cache.addressUseAt(tree.nodeMainToken(operand))).?;
        try std.testing.expectEqual(use.definite_write, repeated.definite_write);
        cases += 1;
    }
    try std.testing.expectEqual(@as(usize, 10), cases);
    try std.testing.expect(correct);
}

test "FileCache: aggregate literal proof checks actual defaults and array shape" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const Good = struct { value: u32 = 1 };
        \\const Bad = struct { value: u32 = undefined };
        \\const Nested = struct { inner: Bad = .{} };
        \\const ArrayDefault = struct { items: [2]u32 = .{ 1, undefined } };
        \\const UnknownDefault = struct { value: u32 = opaqueValue() };
        \\extern fn opaqueValue() u32;
        \\fn caller() void {
        \\    const safe_empty: Good = .{};
        \\    const safe_nested: struct { inner: Good } = .{ .inner = .{} };
        \\    const safe_override = Bad{ .value = 2 };
        \\    const safe_array: [2]u32 = .{ 1, 2 };
        \\    const safe_zero = [0]u32{};
        \\    const unsafe_omitted: Bad = .{};
        \\    const unsafe_nested: Nested = .{};
        \\    const unsafe_array_default: ArrayDefault = .{};
        \\    const unsafe_array: [2]u32 = .{ 1, undefined };
        \\    const unknown_type = Missing{ .value = 2 };
        \\    const unknown_default: UnknownDefault = .{};
        \\    const unknown_shape: [2]u32 = .{};
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-aggregate-literal-verdict.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var cases: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        const variable = tree.fullVarDecl(node) orelse continue;
        const name = tree.tokenSlice(variable.ast.mut_token + 1);
        if (!std.mem.startsWith(u8, name, "safe_") and !std.mem.startsWith(u8, name, "unsafe_") and
            !std.mem.startsWith(u8, name, "unknown_")) continue;
        const value = variable.ast.init_node.unwrap().?;
        var proof: FileCache.DefiniteStoreProof = .{
            .tree = tree,
            .frame = resolver.resolutionFrame(),
            .call_node = value,
            .call_tree = tree,
        };
        const expected: FileCache.DefiniteStoreValue = if (std.mem.startsWith(u8, name, "safe_"))
            .defined
        else if (std.mem.startsWith(u8, name, "unsafe_"))
            .undefined_value
        else
            .unknown;
        try std.testing.expectEqual(expected, try cache.definiteStoreValue(&proof, value, 1));
        cases += 1;
    }
    try std.testing.expectEqual(@as(usize, 12), cases);
}

test "FileCache: computed scalar output proof preserves shared work and depth limits" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "fn literal() u8 { return 1; }", .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var literal: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag == .number_literal) literal = @enumFromInt(raw);
    }
    var proof: FileCache.DefiniteStoreProof = .{
        .tree = &tree,
        .frame = undefined, // The literal proof does not ask a type question.
        .call_node = literal.?,
        .call_tree = &tree,
    };
    _ = budget_mod.take();
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    try std.testing.expectEqual(@as(u32, 50_000), cleanup_budget.remaining);
    try std.testing.expectEqual(FileCache.DefiniteStoreValue.defined, try cache.definiteStoreValue(&proof, literal.?, 63));
    try std.testing.expectEqual(@as(u32, 49_999), cleanup_budget.remaining);
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.definiteStoreValue(&proof, literal.?, 64));
    const depth_failure = budget_mod.take().?;
    try std.testing.expectEqual(budget_mod.Limit.normal_cleanup_depth, depth_failure.limit);
    cleanup_budget.remaining = 0;
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.definiteStoreValue(&proof, literal.?, 0));
    const work_failure = budget_mod.take().?;
    try std.testing.expectEqual(budget_mod.Limit.normal_cleanup_nodes, work_failure.limit);
}

test "FileCache: owned header getters preserve cleanup while value releases remain visible" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Header = struct {
        \\    bytes: []u8,
        \\    fn size(self: Header) usize { return self.bytes.len; }
        \\    fn load(self: Header) usize { return self.g0(); }
        \\    fn g0(self: Header) usize { return self.g1(); }
        \\    fn g1(self: Header) usize { return self.g2(); }
        \\    fn g2(self: Header) usize { return self.g3(); }
        \\    fn g3(self: Header) usize { return self.g4(); }
        \\    fn g4(self: Header) usize { return self.g5(); }
        \\    fn g5(self: Header) usize { return self.g6(); }
        \\    fn g6(self: Header) usize { return self.g7(); }
        \\    fn g7(self: Header) usize { return self.g8(); }
        \\    fn g8(self: Header) usize { return self.g9(); }
        \\    fn g9(self: Header) usize { return self.g10(); }
        \\    fn g10(self: Header) usize { return self.g11(); }
        \\    fn g11(self: Header) usize { return self.g12(); }
        \\    fn g12(self: Header) usize { return self.g13(); }
        \\    fn g13(self: Header) usize { return self.g14(); }
        \\    fn g14(self: Header) usize { return self.g15(); }
        \\    fn g15(self: Header) usize { return self.size(); }
        \\    fn release(self: Header, allocator: std.mem.Allocator) void { allocator.free(self.bytes); }
        \\    fn maybe(self: Header, allocator: std.mem.Allocator, flag: bool) void {
        \\        if (flag) self.release(allocator);
        \\    }
        \\};
        \\fn inspect(header: Header) usize { return header.load(); }
        \\fn dispose(header: Header, allocator: std.mem.Allocator) void {
        \\    _ = header.load();
        \\    header.release(allocator);
        \\}
        \\fn conditional(header: Header, allocator: std.mem.Allocator, flag: bool) void {
        \\    header.maybe(allocator, flag);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-owned-header-cleanup.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const inspect = (try cache.summaryByName("inspect")).?;
    try std.testing.expect(inspect.normal_success_effects_complete);
    try std.testing.expectEqual(@as(usize, 0), inspect.normal_success_may_freed_paths.len);
    const dispose = (try cache.summaryByName("dispose")).?;
    try std.testing.expect(dispose.normal_success_effects_complete);
    try std.testing.expectEqual(@as(usize, 1), dispose.normal_success_definite_freed_paths.len);
    try std.testing.expectEqualStrings("bytes", dispose.normal_success_definite_freed_paths[0].path);
    const conditional = (try cache.summaryByName("conditional")).?;
    try std.testing.expectEqual(@as(usize, 0), conditional.normal_success_definite_freed_paths.len);
    try std.testing.expectEqual(@as(usize, 1), conditional.normal_success_may_freed_paths.len);
    try std.testing.expectEqualStrings("bytes", conditional.normal_success_may_freed_paths[0].path);
}

test "FileCache: delegated stores credit receivers, field operands and aggregates; unsafe controls abstain" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const Handle = struct { id: u32, ptr: *u8 };
        \\const Context = struct {
        \\    handle: Handle,
        \\    a: u32,
        \\    b: u32,
        \\    fn make() Context { return .{ .handle = undefined, .a = 0, .b = 0 }; }
        \\    fn initFull(self: *Context, handle: Handle) !void { try self.initWith(handle, 1); }
        \\    fn initWith(self: *Context, handle: Handle, a: u32) !void {
        \\        self.handle = handle;
        \\        self.a = a;
        \\        self.b = a + 1;
        \\    }
        \\    fn initSplit(self: *Context, handle: Handle) !void { self.handle = handle; try self.rest(); }
        \\    fn rest(self: *Context) !void { self.a = 1; self.b = 2; }
        \\    fn initReturn(self: *Context, handle: Handle) !void { return self.initWith(handle, 2); }
        \\    fn partialWrap(self: *Context, handle: Handle) !void { try self.onlyHandle(handle); }
        \\    fn onlyHandle(self: *Context, handle: Handle) !void { self.handle = handle; self.a = 1; }
        \\    fn neverWrites(self: *Context) !void { try self.nothing(); }
        \\    fn nothing(self: *Context) !void { _ = self; }
        \\    fn fail(self: *Context) !void { _ = self; return error.Bad; }
        \\    fn failFirst(self: *Context, handle: Handle) !void { try self.fail(); try self.initWith(handle, 1); }
        \\    fn failMiddle(self: *Context, handle: Handle) !void { try self.writeThenFail(handle); }
        \\    fn writeThenFail(self: *Context, handle: Handle) !void {
        \\        self.handle = handle;
        \\        self.a = 1;
        \\        try self.fail();
        \\        self.b = 2;
        \\    }
        \\    fn cycleA(self: *Context) !void { try self.cycleB(); }
        \\    fn cycleB(self: *Context) !void { try self.cycleA(); }
        \\    fn byValue(self: Context) void { _ = self; }
        \\};
        \\const Holder = struct { tag: u32, context: Context };
        \\fn caller(handle: Handle) !void {
        \\    var full: Context = undefined; try full.initFull(handle);
        \\    var split: Context = undefined; try split.initSplit(handle);
        \\    var returned: Context = undefined; try returned.initReturn(handle);
        \\    var static_call: Context = undefined; try Context.initFull(&static_call, handle);
        \\    var held: Holder = .{ .tag = 1, .context = undefined }; try held.context.initFull(handle);
        \\    var held_static: Holder = .{ .tag = 1, .context = undefined }; try Context.initFull(&held_static.context, handle);
        \\    var partial: Context = undefined; try partial.partialWrap(handle);
        \\    var never: Context = undefined; try never.neverWrites();
        \\    var fail_first: Context = undefined; try fail_first.failFirst(handle);
        \\    var fail_middle: Context = undefined; try fail_middle.failMiddle(handle);
        \\    var cycle: Context = undefined; try cycle.cycleA();
        \\    var bad_handle: Handle = undefined; var bad_actual: Context = undefined; try bad_actual.initFull(bad_handle);
        \\    var by_value: Context = undefined; by_value.byValue();
        \\}
        \\fn unseeded(handle: Handle) !void {
        \\    var plain = Context.make();
        \\    try plain.initFull(handle);
        \\}
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-delegated-store-proof.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    const credited = [_][]const u8{ "full", "split", "returned", "static_call", "held", "held_static", "plain" };
    const abstained = [_][]const u8{ "partial", "never", "fail_first", "fail_middle", "cycle", "bad_actual", "by_value" };
    var seen: usize = 0;
    var correct = true;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var root: Ast.Node.Index = undefined;
        var receiver = false;
        if (tag == .address_of) {
            root = tokens.rootIdentifier(tree, tree.nodeData(node).node) orelse continue;
        } else {
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node) orelse continue;
            if (tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
            root = FileCache.receiverRoot(tree, tree.nodeData(call.ast.fn_expr).node_and_token[0]) orelse continue;
            receiver = true;
        }
        const name = tree.tokenSlice(tree.nodeMainToken(root));
        const use = try cache.addressUseAt(tree.nodeMainToken(root));
        const repeated = try cache.addressUseAt(tree.nodeMainToken(root));
        for (credited) |expected| {
            if (!std.mem.eql(u8, name, expected)) continue;
            const complete = if (use) |answer| answer.may_write and answer.definite_write else false;
            const cached_complete = if (repeated) |answer| answer.definite_write else false;
            if (!complete or !cached_complete) {
                std.debug.print("delegated output case {s}: complete={any}, cached={any}\n", .{ name, complete, cached_complete });
                correct = false;
            }
            seen += 1;
        }
        for (abstained) |expected| {
            if (!std.mem.eql(u8, name, expected)) continue;
            const complete = if (use) |answer| answer.definite_write else false;
            const cached_complete = if (repeated) |answer| answer.definite_write else false;
            if (complete or cached_complete) {
                std.debug.print("delegated output case {s}: unexpected complete store\n", .{name});
                correct = false;
            }
            if (std.mem.eql(u8, name, "partial")) {
                const answer = use orelse return error.TestExpectedPartialStore;
                var handle_written = false;
                var a_written = false;
                for (answer.fields[0..answer.field_count]) |field| {
                    if (std.mem.eql(u8, field, "handle")) handle_written = true;
                    if (std.mem.eql(u8, field, "a")) a_written = true;
                    try std.testing.expect(!std.mem.eql(u8, field, "b"));
                }
                try std.testing.expect(handle_written and a_written);
            }
            try std.testing.expect(receiver);
            seen += 1;
        }
    }
    try std.testing.expectEqual(credited.len + abstained.len, seen);
    try std.testing.expect(correct);
    try std.testing.expectEqual(@as(u32, 0), cleanup_budget.depth);
    try std.testing.expectEqual(@as(u32, 0), cleanup_budget.queries);
}

test "FileCache: foreign diagnostic replay exhaustion retains node ownership" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    const callee_source: [:0]const u8 =
        \\const defaults = @import("./defaults.zig");
        \\const pad00 = 0;
        \\const pad01 = 1;
        \\const pad02 = 2;
        \\const pad03 = 3;
        \\const pad04 = 4;
        \\const pad05 = 5;
        \\const pad06 = 6;
        \\const pad07 = 7;
        \\const pad08 = 8;
        \\const pad09 = 9;
        \\const pad10 = 10;
        \\const pad11 = 11;
        \\const pad12 = 12;
        \\const pad13 = 13;
        \\const pad14 = 14;
        \\const pad15 = 15;
        \\pub fn poison() u32 { return undefined; }
        \\pub fn write(out: *u32) void { out.* = undefined; }
        \\pub fn omitted() defaults.Value { return .{}; }
    ;
    const defaults_source: [:0]const u8 =
        \\const pad00 = 0;
        \\const pad01 = 1;
        \\const pad02 = 2;
        \\const pad03 = 3;
        \\const pad04 = 4;
        \\const pad05 = 5;
        \\const pad06 = 6;
        \\const pad07 = 7;
        \\const pad08 = 8;
        \\const pad09 = 9;
        \\const pad10 = 10;
        \\const pad11 = 11;
        \\const pad12 = 12;
        \\const pad13 = 13;
        \\const pad14 = 14;
        \\const pad15 = 15;
        \\pub const Value = struct { value: u32 = undefined };
    ;
    const Query = enum { syntax, replay, stores, defaults, initiating_redirect };
    for (std.enums.values(Query)) |query| {
        const caller_source: [:0]const u8 = switch (query) {
            .stores =>
            \\const foreign = @import("./callee.zig");
            \\pub fn entry() void { var value: u32 = 1; foreign.write(&value); }
            ,
            .defaults =>
            \\const foreign = @import("./callee.zig");
            \\pub fn entry() void { _ = foreign.omitted(); }
            ,
            else =>
            \\const foreign = @import("./callee.zig");
            \\pub fn entry() u32 { return foreign.poison(); }
            ,
        };
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        try tmp.dir.writeFile(io, .{ .sub_path = "callee.zig", .data = callee_source });
        try tmp.dir.writeFile(io, .{ .sub_path = "defaults.zig", .data = defaults_source });
        try tmp.dir.writeFile(io, .{ .sub_path = "caller.zig", .data = caller_source });
        const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
        defer gpa.free(root);
        const caller_path = try std.fs.path.join(gpa, &.{ root, "caller.zig" });
        defer gpa.free(caller_path);
        var context: engine.TypeContext = undefined;
        try context.init(gpa, io);
        defer context.deinit();
        context.store.source_policy = .{ .roots = &.{root} };
        var resolver: engine.TypeResolver = undefined;
        try resolver.init(&context, gpa, caller_path, caller_source);
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        var cache = FileCache.init(gpa, tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        cache.file_path = caller_path;
        const wanted = switch (query) {
            .stores => "write",
            .defaults => "omitted",
            else => "poison",
        };
        var call_node: ?Ast.Node.Index = null;
        var token: ?Ast.TokenIndex = null;
        var address: ?Ast.Node.Index = null;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (tag == .address_of) address = node;
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), wanted)) continue;
            call_node = node;
            token = fresh_storage_mod.calleeQueryToken(tree, call);
        }
        // Resolve real imports before spending the cleanup allowance. Keep
        // return syntax and verdicts cold so the failure is in replay, not lookup.
        const canonical = (try cache.actualCallSummaryAt(token.?, null)).?;
        const declaring = (try canonical.declaringCache(&cache)).?;
        try std.testing.expect(canonical.callee.tree == declaring.tree);
        try std.testing.expect(declaring.tree != tree);
        try std.testing.expectEqualStrings(callee_source, declaring.tree.source);
        var failed_tree = canonical.callee.tree;
        var failed_node = tokens.bodyOf(failed_tree, canonical.callee.declaration).?;
        var expected_function: []const u8 = wanted;
        var default_frame: ?TypeResolver.ResolutionFrame = null;
        if (query == .defaults) {
            // Exercise the source predicate in the default's own document.
            // Its type owner is a third file, not the caller or callee.
            const declared = canonical.callee.reference.actual_type.data.function.return_value.*;
            const result = (try resolver.normalizedType(declared)).?;
            default_frame = resolver.frameForContainer(result.data.container);
            const scope = result.data.container.scope_handle;
            failed_tree = &scope.handle.document.tree;
            var buffer: [2]Ast.Node.Index = undefined;
            const container = failed_tree.fullContainerDecl(&buffer, scope.toNode()).?;
            const field = failed_tree.fullContainerField(container.ast.members[0]).?;
            failed_node = field.ast.value_expr.unwrap().?;
            expected_function = "";
            try std.testing.expect(failed_tree != declaring.tree);
        }
        // This small fixture must distinguish numeric node ownership: the
        // foreign node would be out of bounds if read against the caller AST.
        try std.testing.expect(@intFromEnum(failed_node) >= tree.nodes.len);
        _ = budget_mod.take();
        defer _ = budget_mod.take();
        cache.beginNormalCleanup();
        defer cache.endNormalCleanup();
        if (query == .initiating_redirect) {
            try cache.enterNormalCleanup(call_node.?);
            defer cache.leaveNormalCleanup();
            cleanup_budget.remaining = 0;
            try std.testing.expectError(error.AnalysisBudgetExceeded, cache.callResultMayBeUndefinedAt(token.?, null));
            failed_tree = tree;
            failed_node = call_node.?;
            expected_function = "entry";
        } else {
            cleanup_budget.remaining = 0;
            try std.testing.expect(cleanup_budget.initiating_cache == null);
            switch (query) {
                .syntax => try std.testing.expectError(error.AnalysisBudgetExceeded, cache.callResultMayBeUndefinedAt(token.?, null)),
                .defaults => try std.testing.expectError(error.AnalysisBudgetExceeded, cache.returnSourceEligibility(default_frame.?, failed_node, false)),
                .replay => try std.testing.expectError(error.AnalysisBudgetExceeded, cache.callResultValueAt(token.?, null, true, &canonical)),
                .stores => {
                    var use: FileCache.AddressUse = .{
                        .operand = tree.nodeData(address.?).node,
                        .address_node = address.?,
                        .call_node = call_node.?,
                        .may_write = true,
                    };
                    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.populateUndefinedAddressStores(&use));
                    try std.testing.expectEqual(@as(usize, 0), use.undefined_field_count);
                    try std.testing.expect(!use.definite_write);
                },
                .initiating_redirect => unreachable,
            }
        }
        const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
        const expected_byte = failed_tree.tokenStart(failed_tree.nodeMainToken(failed_node));
        const position = budget_mod.lineCol(failed_tree.source, expected_byte);
        try std.testing.expectEqual(budget_mod.Limit.normal_cleanup_nodes, failure.limit);
        try std.testing.expectEqual(@as(u32, 50_000), failure.limit_value);
        try std.testing.expectEqual(@as(u32, 50_000), failure.reached);
        try std.testing.expectEqual(expected_byte, failure.byte);
        try std.testing.expectEqual(position.line, failure.line);
        try std.testing.expectEqual(position.column, failure.column);
        try std.testing.expectEqualStrings(expected_function, failure.function.slice());
        try std.testing.expectEqual(@as(usize, 0), cache.return_defined_summaries.count());
        try std.testing.expectEqual(@as(usize, 0), cache.return_defined_visiting.count());
        // A fresh allowance must retry, not read an unfinished replay as a
        // positive certificate or a cached negative verdict.
        cache.endNormalCleanup();
        cache.beginNormalCleanup();
        if (query == .stores) {
            var use: FileCache.AddressUse = .{
                .operand = tree.nodeData(address.?).node,
                .address_node = address.?,
                .call_node = call_node.?,
                .may_write = true,
            };
            try cache.populateUndefinedAddressStores(&use);
            try std.testing.expect(use.undefined_field_count != 0);
            try std.testing.expect(!use.definite_write);
        } else {
            try std.testing.expect(!try cache.callResultDefinedAt(token.?, null));
            try std.testing.expect(try cache.callResultMayBeUndefinedAt(token.?, null));
        }
    }
}

test "FileCache: foreign nested store literal exhaustion retains node ownership" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    const caller_source: [:0]const u8 =
        "const padding = .{" ++ "0," ** 32 ++ "};\n" ++
        \\const wrapper = @import("./wrapper.zig");
        \\pub fn entry() void { var value: u32 = 1; wrapper.write(&value); }
    ;
    const wrapper_source: [:0]const u8 =
        \\const leaf = @import("./leaf.zig");
        \\pub fn write(out: *u32) void {
        \\    var local: u32 = 1;
        \\    leaf.write(&local);
        \\    out.* = local;
        \\}
    ;
    const leaf_source: [:0]const u8 =
        "const padding = .{" ++ "0," ** 128 ++ "};\n" ++
        \\pub fn write(out: *u32) void { out.* = undefined; }
    ;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "caller.zig", .data = caller_source });
    try tmp.dir.writeFile(io, .{ .sub_path = "wrapper.zig", .data = wrapper_source });
    try tmp.dir.writeFile(io, .{ .sub_path = "leaf.zig", .data = leaf_source });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const caller_path = try std.fs.path.join(gpa, &.{ root, "caller.zig" });
    defer gpa.free(caller_path);
    var context: engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{root} };
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, caller_path, caller_source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.file_path = caller_path;
    var address: ?Ast.Node.Index = null;
    var call_node: ?Ast.Node.Index = null;
    var canonical: ?FileCache.ActualCallSummary = null;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tag == .address_of) address = node;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        call_node = node;
        canonical = try cache.actualCallSummaryAt(call.queryToken(tree, node), null);
    }
    const wrapper = (try canonical.?.declaringCache(&cache)).?;
    try std.testing.expect(@intFromEnum(call_node.?) >= wrapper.tree.nodes.len);
    var leaf: ?*FileCache = null;
    const wrapper_frame = wrapper.zls.?.frameForFunction(canonical.?.callee.reference);
    for (wrapper.tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(wrapper.tree, &buffer, node) orelse continue;
        const nested = (try wrapper.actualCallSummaryAt(call.queryToken(wrapper.tree, node), wrapper_frame)).?;
        leaf = (try nested.declaringCache(wrapper)).?;
    }
    const leaf_tree = leaf.?.tree;
    var literal: ?Ast.Node.Index = null;
    for (leaf_tree.nodes.items(.tag), 0..) |tag, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tag == .identifier and
            std.mem.eql(u8, leaf_tree.tokenSlice(leaf_tree.nodeMainToken(node)), "undefined")) literal = node;
    }
    try std.testing.expect(@intFromEnum(literal.?) >= tree.nodes.len);
    const saved_site = replay_failure_site;
    defer replay_failure_site = saved_site;
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    var allowance: ?u32 = null;
    var source_allowance: ?u32 = null;
    // The direct literal is charged first by wholeStoreFieldSource, then by
    // literalStoreUndefinedValueMode. Select the second consecutive charge.
    // Each scope retries with fresh lexical state and no positive certificate.
    for (0..256) |remaining| {
        cache.beginNormalCleanup();
        defer cache.endNormalCleanup();
        replay_failure_site = null;
        cleanup_budget.remaining = @intCast(remaining);
        var use: FileCache.AddressUse = .{
            .operand = tree.nodeData(address.?).node,
            .address_node = address.?,
            .call_node = call_node.?,
            .may_write = true,
        };
        _ = cache.definiteAddressWrite(&use) catch |err| {
            if (err != error.AnalysisBudgetExceeded) return err;
            try std.testing.expect(!use.definite_write);
            const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
            try std.testing.expectEqual(budget_mod.Limit.normal_cleanup_nodes, failure.limit);
            try std.testing.expectEqualStrings("entry", failure.function.slice());
            const site = replay_failure_site orelse return error.TestUnexpectedResult;
            if (site.tree == leaf_tree and site.node == literal.?) {
                if (source_allowance) |previous| {
                    try std.testing.expectEqual(previous + 1, @as(u32, @intCast(remaining)));
                    allowance = @intCast(remaining);
                    break;
                }
                source_allowance = @intCast(remaining);
            }
            continue;
        };
        try std.testing.expect(!use.definite_write);
    }
    try std.testing.expect(allowance != null);
    for (0..2) |_| {
        cache.beginNormalCleanup();
        defer cache.endNormalCleanup();
        replay_failure_site = null;
        cleanup_budget.remaining = allowance.?;
        var use: FileCache.AddressUse = .{
            .operand = tree.nodeData(address.?).node,
            .address_node = address.?,
            .call_node = call_node.?,
            .may_write = true,
        };
        try std.testing.expectError(error.AnalysisBudgetExceeded, cache.definiteAddressWrite(&use));
        try std.testing.expect(!use.definite_write);
        const site = replay_failure_site orelse return error.TestUnexpectedResult;
        try std.testing.expect(site.tree == leaf_tree and site.node == literal.?);
        const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
        try std.testing.expectEqualStrings("entry", failure.function.slice());
        try std.testing.expectEqual(tree.tokenStart(tree.nodeMainToken(call_node.?)), failure.byte);
    }
    var retry_result: ?bool = null;
    for (0..2) |_| {
        var use: FileCache.AddressUse = .{
            .operand = tree.nodeData(address.?).node,
            .address_node = address.?,
            .call_node = call_node.?,
            .may_write = true,
        };
        const retained = try cache.definiteAddressWrite(&use);
        if (retry_result) |previous| try std.testing.expectEqual(previous, retained);
        retry_result = retained;
        try std.testing.expect(!use.definite_write);
    }
    try std.testing.expectEqual(@as(u32, 0), cleanup_budget.depth);
    try std.testing.expectEqual(@as(u32, 0), cleanup_budget.queries);
}

test "FileCache: an exhausted budget in an array return source is an error, not an abstention" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn pick(value: usize) usize { return value; }
        \\fn entry(count: usize) usize { return pick(count); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-array-return-budget.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var token: ?Ast.TokenIndex = null;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "pick")) continue;
        token = fresh_storage_mod.calleeQueryToken(tree, call);
    }
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    // Within budget the walk reaches its end: a source or an abstention.
    _ = try cache.arrayReturnSourceAt(token.?, null, &.{});
    // Inside a proof whose allowance is spent the same query must raise.
    // Answering null would read an unfinished walk as a finished refusal.
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    cleanup_budget.remaining = 0;
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.arrayReturnSourceAt(token.?, null, &.{}));
    try std.testing.expect(budget_mod.take() != null);
}

test "FileCache: a root that gave up stays failed instead of publishing its partial summary" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 = "fn plain() void {}";
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const model = try cache.fileModel();
    const root = model.findFn("plain").?;
    // An earlier phase finished: the summary is complete and readable.
    _ = try cache.summaryOfFn(root.fn_decl);
    try std.testing.expectEqual(@as(u32, 1), cache.summaries.count());

    var failures: std.ArrayListUnmanaged(SummaryFailure) = .empty;
    defer failures.deinit(gpa);
    var roots = try RootFailures.init(gpa, tree.nodes.len, &failures);
    defer roots.deinit(gpa);
    budget_mod.clear();
    defer budget_mod.clear();
    // A later phase gave up on the same root.
    try std.testing.expectEqual(error.AnalysisBudgetExceeded, budget_mod.fail(.{ .limit = .block_visits, .limit_value = 7, .reached = 7 }));
    try roots.note(&cache, root.fn_decl, error.AnalysisBudgetExceeded);
    try std.testing.expectEqual(@as(usize, 1), failures.items.len);
    const recorded = failures.items[0].budget orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.block_visits, recorded.limit);
    try std.testing.expect(roots.skipped(root.fn_decl));

    // What the earlier phases published is withdrawn, not left readable ...
    try std.testing.expectEqual(@as(u32, 0), cache.summaries.count());
    // ... and a lookup raises the recorded failure rather than recomputing
    // the body-only answer and presenting it as the finished one.
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.summaryByName("plain"));
    const reraised = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.block_visits, reraised.limit);
    try std.testing.expectEqual(@as(u32, 7), reraised.limit_value);
    try std.testing.expectEqual(@as(u32, 0), cache.summaries.count());
}

/// A type whose `methods` methods each call the next one; the last grows a
/// collection.  Declared callers-first, so the effect moves one call per pass.
fn growChainSource(gpa: std.mem.Allocator, methods: usize) ![:0]u8 {
    var text: std.ArrayListUnmanaged(u8) = .empty;
    defer text.deinit(gpa);
    try text.appendSlice(gpa, "const std = @import(\"std\");\nconst T = struct {\n    list: std.ArrayList(u32),\n");
    for (0..methods - 1) |index| {
        try text.print(gpa, "    fn m{d}(self: *T) void {{ self.m{d}(); }}\n", .{ index, index + 1 });
    }
    try text.print(gpa, "    fn m{d}(self: *T) void {{ self.list.append(1) catch {{}}; }}\n}};\n", .{methods - 1});
    return gpa.dupeZ(u8, text.items);
}

test "FileCache: a transitive fixpoint that has not settled is a budget failure, not a partial answer" {
    const gpa = std.testing.allocator;
    {
        const settled = try growChainSource(gpa, 6);
        defer gpa.free(settled);
        var tree = try Ast.parse(gpa, settled, .zig);
        defer tree.deinit(gpa);
        var cache = FileCache.init(gpa, &tree);
        defer cache.deinit();
        try cache.resolveTransitiveTakes();
        try std.testing.expect(cache.transitive_resolved);
        const head = (try cache.summaryByMethod("T", "m0")).?;
        try std.testing.expect(head.may_grow_collections);
    }
    // The effect needs more passes than the bound allows to reach the head of
    // the chain: stopping there would leave the callers above it unmarked.
    const unsettled = try growChainSource(gpa, max_fixpoint_rounds + 4);
    defer gpa.free(unsettled);
    var tree = try Ast.parse(gpa, unsettled, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.resolveTransitiveTakes());
    const stop = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.transitive_fixpoint_rounds, stop.limit);
    try std.testing.expectEqual(max_fixpoint_rounds, stop.limit_value);
    try std.testing.expect(!cache.transitive_resolved);
}

test "FileCache: a comptime scope nested deeper than the walk reads is an exhausted bound" {
    const gpa = std.testing.allocator;
    var text: std.ArrayListUnmanaged(u8) = .empty;
    defer text.deinit(gpa);
    try text.appendSlice(gpa, "fn deep() void {\n");
    for (0..max_fill_scope_depth + 6) |_| try text.append(gpa, '{');
    try text.appendSlice(gpa, "marker;");
    for (0..max_fill_scope_depth + 6) |_| try text.append(gpa, '}');
    try text.appendSlice(gpa, "\n}\nfn shallow() void { comptime { marker; } }\nfn runtime() void { marker; }\n");
    const source = try gpa.dupeZ(u8, text.items);
    defer gpa.free(source);
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var markers: [3]Ast.TokenIndex = undefined;
    var found: usize = 0;
    for (tree.tokens.items(.tag), 0..) |tag, raw| {
        if (tag != .identifier) continue;
        const token: Ast.TokenIndex = @intCast(raw);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "marker")) continue;
        markers[found] = token;
        found += 1;
    }
    try std.testing.expectEqual(@as(usize, 3), found);
    // Within the bound the answer is exact, in both directions.
    const shallow = tokens.enclosingFnDecl(&tree, markers[1]).?;
    try std.testing.expect(!try cache.isRuntimeUse(shallow, markers[1]));
    const runtime = tokens.enclosingFnDecl(&tree, markers[2]).?;
    try std.testing.expect(try cache.isRuntimeUse(runtime, markers[2]));
    // Past it the scope was not read: that is not "no comptime block".
    const deep = tokens.enclosingFnDecl(&tree, markers[0]).?;
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.isRuntimeUse(deep, markers[0]));
    const stop = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.comptime_scope_depth, stop.limit);
    try std.testing.expectEqual(@as(u32, max_fill_scope_depth), stop.limit_value);
    try std.testing.expect(stop.line != 0);
}

test "FileCache: fileModel builds once" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const Foo = struct {
        \\    x: u32,
        \\    pub fn deinit(self: *Foo) void { _ = self; }
        \\};
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();

    const a = try cache.fileModel();
    const b = try cache.fileModel();
    try std.testing.expect(a == b);
}

test "FileCache: localBindings caches per body" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\fn foo(x: u32) void { _ = x; }
        \\fn bar(y: u32) void { _ = y; }
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();

    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(&tree);
    const foo = fns.next(&proto_buf).?;
    const bar = fns.next(&proto_buf).?;

    // Pointers are borrowed until another body grows the map, so compare
    // each pair before the next body is built.
    const a1 = try cache.localBindings(foo.proto, foo.body);
    const a2 = try cache.localBindings(foo.proto, foo.body);
    try std.testing.expect(a1 == a2);
    const b1 = try cache.localBindings(bar.proto, bar.body);
    const b2 = try cache.localBindings(bar.proto, bar.body);
    try std.testing.expect(b1 == b2);
    try std.testing.expect(b1 != try cache.localBindings(foo.proto, foo.body));
}

// ── Address-use walk budget ─────────────────────────────────

/// `orelse` nesting inside one expression.  Each level adds one walk
/// frame, so `depth` maps directly onto the walk's frame count.
const max_address_use_frames = FileCache.max_address_use_frames;

fn addressUseSource(gpa: std.mem.Allocator, depth: usize) ![:0]u8 {
    var text: std.ArrayListUnmanaged(u8) = .empty;
    defer text.deinit(gpa);
    try text.appendSlice(gpa, "fn nest() u32 {\n    var v: u32 = 0;\n    v = ");
    for (0..depth) |_| try text.appendSlice(gpa, "0 orelse ");
    try text.appendSlice(gpa, "1;\n    return v;\n}\n");
    return gpa.dupeZ(u8, text.items);
}

test "FileCache: address-use walk names the frame-depth limit and the function" {
    const gpa = std.testing.allocator;
    const source = try addressUseSource(gpa, max_address_use_frames + 4);
    defer gpa.free(source);
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();

    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.addressUseAt(0));
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.address_use_depth, failure.limit);
    try std.testing.expectEqual(@as(u32, max_address_use_frames), failure.limit_value);
    try std.testing.expectEqualStrings("nest", failure.function.slice());
    try std.testing.expect(failure.line > 0);
    try std.testing.expect(failure.byte > 0);
}

test "FileCache: an address-use walk under the frame cap still indexes the file" {
    const gpa = std.testing.allocator;
    const source = try addressUseSource(gpa, max_address_use_frames - 8);
    defer gpa.free(source);
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();

    budget_mod.clear();
    defer budget_mod.clear();
    // Below the cap the walk completes, so the lookup answers normally and
    // leaves no failure record behind.
    _ = try cache.addressUseAt(0);
    try std.testing.expect(budget_mod.peek() == null);
}

test "FileCache: embedded extents follow canonical symlink parents and policy" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.createDirPath(io, "allowed");
    try tmp.dir.createDirPath(io, "outside/deep");
    try tmp.dir.writeFile(io, .{ .sub_path = "allowed/probe.bin", .data = "x" });
    try tmp.dir.writeFile(io, .{ .sub_path = "outside/probe.bin", .data = &([_]u8{0} ** 256) });
    try tmp.dir.symLink(io, "../outside/deep", "allowed/link", .{ .is_directory = true });
    const source = "const bytes = @embedFile(\"link/../probe.bin\");";
    try tmp.dir.writeFile(io, .{ .sub_path = "allowed/main.zig", .data = source });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const allowed = try std.fs.path.join(gpa, &.{ root, "allowed" });
    defer gpa.free(allowed);
    const path = try std.fs.path.join(gpa, &.{ allowed, "main.zig" });
    defer gpa.free(path);
    for ([_]bool{ false, true }) |admit_outside| {
        var context: engine.TypeContext = undefined;
        try context.init(gpa, io);
        defer context.deinit();
        context.store.source_policy = .{ .roots = &.{if (admit_outside) root else allowed} };
        var resolver: engine.TypeResolver = undefined;
        try resolver.init(&context, gpa, path, source);
        defer resolver.deinit();
        var cache = FileCache.init(gpa, &resolver.handle.document.tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        cache.file_path = path;
        const embed = (try cache.fileConstInitializer("bytes")).?;
        const expected: ?u64 = if (admit_outside) 256 else null;
        try std.testing.expectEqual(expected, try cache.embeddedFileLength(embed));
        try std.testing.expectEqual(expected, try cache.embeddedFileLength(embed));
        try std.testing.expectEqual(@as(usize, 1), cache.embedded_file_lengths.count());
    }
}

test "FileCache: embedded metadata allocation and cancellation failures are not cached as absent files" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source = "const bytes = @embedFile(\"data.bin\");";
    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data = source });
    try tmp.dir.writeFile(io, .{ .sub_path = "data.bin", .data = "hello" });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const path = try std.fs.path.join(gpa, &.{ root, "main.zig" });
    defer gpa.free(path);
    var context: engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{root} };
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    var locating = FileCache.init(gpa, &resolver.handle.document.tree);
    defer locating.deinit();
    const embed = (try locating.fileConstInitializer("bytes")).?;
    for (0..3) |fail_index| {
        var failing = std.testing.FailingAllocator.init(gpa, .{ .fail_index = fail_index });
        var cache = FileCache.init(failing.allocator(), &resolver.handle.document.tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        cache.file_path = path;
        try std.testing.expectError(error.OutOfMemory, cache.embeddedFileLength(embed));
        try std.testing.expectEqual(@as(usize, 0), cache.embedded_file_lengths.count());
    }
    var canceled_vtable = io.vtable.*;
    canceled_vtable.fileStat = struct {
        fn stat(_: ?*anyopaque, _: std.Io.File) std.Io.File.StatError!std.Io.File.Stat {
            return error.Canceled;
        }
    }.stat;
    context.store.io = .{ .userdata = io.userdata, .vtable = &canceled_vtable };
    defer context.store.io = io;
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.file_path = path;
    try std.testing.expectError(error.Canceled, cache.embeddedFileLength(embed));
    try std.testing.expectEqual(@as(usize, 0), cache.embedded_file_lengths.count());
    canceled_vtable.fileStat = struct {
        fn stat(_: ?*anyopaque, _: std.Io.File) std.Io.File.StatError!std.Io.File.Stat {
            return error.SystemResources;
        }
    }.stat;
    try std.testing.expectError(error.SystemResources, cache.embeddedFileLength(embed));
    try std.testing.expectEqual(@as(usize, 0), cache.embedded_file_lengths.count());
    context.store.io = io;
    try std.testing.expectEqual(@as(?u64, 5), try cache.embeddedFileLength(embed));
}

test "FileCache: a missing embedded file reports its source error and can be retried" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source = "const bytes = @embedFile(\"late.bin\");";
    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data = source });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const path = try std.fs.path.join(gpa, &.{ root, "main.zig" });
    defer gpa.free(path);
    var context: engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{root} };
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.file_path = path;
    const embed = (try cache.fileConstInitializer("bytes")).?;
    try std.testing.expectError(error.FileNotFound, cache.embeddedFileLength(embed));
    try std.testing.expectEqual(@as(usize, 0), cache.embedded_file_lengths.count());
    try tmp.dir.writeFile(io, .{ .sub_path = "late.bin", .data = "hello" });
    try std.testing.expectEqual(@as(?u64, 5), try cache.embeddedFileLength(embed));
}

test "FileCache: lexical excluded embed components cannot alias an allowed canonical file" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.createDir(io, "nested", .default_dir);
    try tmp.dir.symLink(io, "nested", ".git", .{ .is_directory = true });
    try tmp.dir.symLink(io, "nested", "blocked", .{ .is_directory = true });
    try tmp.dir.writeFile(io, .{ .sub_path = "data.bin", .data = "hello" });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const path = try std.fs.path.join(gpa, &.{ root, "main.zig" });
    defer gpa.free(path);
    const target = try std.fs.path.join(gpa, &.{ root, "data.bin" });
    defer gpa.free(target);
    const canonical_alias = try tmp.dir.realPathFileAlloc(io, ".git/../data.bin", gpa);
    defer gpa.free(canonical_alias);
    try std.testing.expectEqualStrings(target, canonical_alias);
    const sources = [_][:0]const u8{
        "const bytes = @embedFile(\".git/../data.bin\");",
        "const bytes = @embedFile(\"blocked/../data.bin\");",
    };
    for (sources) |source| {
        try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data = source });
        var context: engine.TypeContext = undefined;
        try context.init(gpa, io);
        defer context.deinit();
        context.store.source_policy = .{ .roots = &.{root}, .excludes = &.{"blocked"} };
        try std.testing.expect(context.store.source_policy.allowsAbsolutePath(target));
        var resolver: engine.TypeResolver = undefined;
        try resolver.init(&context, gpa, path, source);
        defer resolver.deinit();
        var cache = FileCache.init(gpa, &resolver.handle.document.tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        cache.file_path = path;
        const embed = (try cache.fileConstInitializer("bytes")).?;
        try std.testing.expectEqual(@as(?u64, null), try cache.embeddedFileLength(embed));
        try std.testing.expectEqual(@as(usize, 1), cache.embedded_file_lengths.count());
    }
}

test "FileCache: ordinary completed call identities retain contextual return separation" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const Safe = struct { const value: u8 = 7; };
        \\const Poisoned = struct { const value: u8 = undefined; };
        \\fn leaf(comptime T: type) u8 { return T.value; }
        \\fn pick(comptime T: type) u8 { return leaf(T); }
        \\fn safe() u8 { return pick(Safe); }
        \\fn unsafe() u8 { return pick(Poisoned); }
        \\fn knownUndefined() u8 { return undefined; }
        \\fn negativeControl() u8 { return knownUndefined(); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-completed-return-identity.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var outer_tokens: [2]Ast.TokenIndex = undefined;
    var outer_count: usize = 0;
    var inner_token: ?Ast.TokenIndex = null;
    var negative_token: ?Ast.TokenIndex = null;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        const token = call.queryToken(tree, node);
        if (std.mem.eql(u8, tree.tokenSlice(token), "leaf")) inner_token = token;
        if (std.mem.eql(u8, tree.tokenSlice(token), "knownUndefined")) negative_token = token;
        if (!std.mem.eql(u8, tree.tokenSlice(token), "pick")) continue;
        try std.testing.expect(outer_count < outer_tokens.len);
        outer_tokens[outer_count] = token;
        outer_count += 1;
    }
    try std.testing.expectEqual(outer_tokens.len, outer_count);
    var calls: [2]FileCache.ActualCallSummary = undefined;
    for (outer_tokens, 0..) |token, index| {
        // The ordinary producer finishes first, as in the summary fold.
        const completed = (try grow_analysis_mod.actualCalleeOf(&cache, token, null)).?;
        try std.testing.expect(completed.caller_frame == null);
        calls[index] = (try cache.returnCallAt(token, resolver.resolutionFrame())).?;
        try std.testing.expect(calls[index].callee.caller_frame != null);
        try std.testing.expect(calls[index].callee.reference.actual_type.eql(completed.reference.actual_type));
        try std.testing.expect(cache.actual_callees.get(token).?.?.caller_frame == null);
    }
    try std.testing.expect(!calls[0].callee.reference.actual_type.eql(calls[1].callee.reference.actual_type));
    const ordinary_count = cache.actual_callees.count();
    var nested: [2]FileCache.ActualCallSummary = undefined;
    for (calls, 0..) |outer, index| {
        const frame = resolver.frameForFunction(outer.callee.reference);
        nested[index] = (try cache.returnCallAt(inner_token.?, frame)).?;
        try std.testing.expect(nested[index].callee.caller_frame.?.actual_type.?.eql(frame.actual_type.?));
    }
    try std.testing.expectEqual(ordinary_count, cache.actual_callees.count());
    try std.testing.expect(!nested[0].callee.reference.actual_type.eql(nested[1].callee.reference.actual_type));
    var defined: [2]bool = undefined;
    var may_undefined: [2]bool = undefined;
    for (outer_tokens, 0..) |token, index| {
        defined[index] = try cache.callResultDefinedAt(token, resolver.resolutionFrame());
        try std.testing.expectEqual(
            if (index == 0) FileCache.SourceEligibility.absent else FileCache.SourceEligibility.present,
            try cache.diagnosticReturnSeed(calls[index], resolver.resolutionFrame()),
        );
        may_undefined[index] = try cache.callResultMayBeUndefinedAt(token, resolver.resolutionFrame());
    }
    try std.testing.expect(!try cache.callResultDefinedAt(negative_token.?, resolver.resolutionFrame()));
    try std.testing.expect(try cache.callResultMayBeUndefinedAt(negative_token.?, resolver.resolutionFrame()));
    // Finished positive and negative results remain usable with no work left.
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    cleanup_budget.remaining = 0;
    for (outer_tokens, 0..) |token, index| {
        try std.testing.expectEqual(defined[index], try cache.callResultDefinedAt(token, resolver.resolutionFrame()));
        try std.testing.expectEqual(may_undefined[index], try cache.callResultMayBeUndefinedAt(token, resolver.resolutionFrame()));
    }
    try std.testing.expect(!try cache.callResultDefinedAt(negative_token.?, resolver.resolutionFrame()));
    try std.testing.expect(try cache.callResultMayBeUndefinedAt(negative_token.?, resolver.resolutionFrame()));
    try std.testing.expectEqual(@as(usize, 0), cache.return_defined_visiting.count());
    try std.testing.expectEqual(@as(usize, 0), cache.return_source_visiting.count());
}

test "FileCache: completed source-free return cycles retain exact instantiation separation" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\const Safe = struct { const value: u8 = 7; };
        \\const Poisoned = struct { const value: u8 = undefined; };
        \\fn first(comptime T: type, again: bool) u8 {
        \\    if (again) return second(T, again);
        \\    return T.value;
        \\}
        \\fn second(comptime T: type, again: bool) u8 { return first(T, again); }
        \\fn safe(again: bool) u8 { return first(Safe, again); }
        \\fn unsafe(again: bool) u8 { return first(Poisoned, again); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-source-free-return-cycle.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var calls: [2]FileCache.ActualCallSummary = undefined;
    var count: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        if (call.ast.params.len != 2) continue;
        const argument = tree.tokenSlice(tree.nodeMainToken(call.ast.params[0]));
        if (!std.mem.eql(u8, argument, "Safe") and !std.mem.eql(u8, argument, "Poisoned")) continue;
        try std.testing.expect(count < calls.len);
        calls[count] = (try cache.returnCallAt(call.queryToken(tree, node), resolver.resolutionFrame())).?;
        count += 1;
    }
    try std.testing.expectEqual(calls.len, count);
    try std.testing.expect(!calls[0].callee.reference.actual_type.eql(calls[1].callee.reference.actual_type));
    for (calls, 0..) |call, index| {
        try std.testing.expectEqual(
            if (index == 0) FileCache.SourceEligibility.absent else FileCache.SourceEligibility.present,
            try cache.diagnosticReturnSeed(call, resolver.resolutionFrame()),
        );
    }
    // A closed absence is reusable with no allowance. An intermediate cycle
    // must not hide the poisoned instantiation's source in the same document.
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    cleanup_budget.remaining = 0;
    for (calls, 0..) |call, index| {
        try std.testing.expectEqual(
            if (index == 0) FileCache.SourceEligibility.absent else FileCache.SourceEligibility.present,
            try cache.diagnosticReturnSeed(call, resolver.resolutionFrame()),
        );
    }
    try std.testing.expectEqual(@as(usize, 0), cache.return_source_visiting.count());
}

test "FileCache: return replay failures retain allowances contexts and first diagnostic ownership" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn hole(comptime poisoned: bool, value: u8) u8 {
        \\    if (poisoned) return undefined;
        \\    return value;
        \\}
        \\fn first() u8 { return hole(true, 7); }
        \\fn second() u8 { return hole(true, 7); }
        \\fn safe() u8 { return hole(false, 7); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-return-replay-failure.zig", source);
    const source_scope = budget_mod.SourceScope.begin(&context.store);
    defer source_scope.end();
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var calls: [3]FileCache.ActualCallSummary = undefined;
    var nodes: [3]Ast.Node.Index = undefined;
    var query_tokens: [3]Ast.TokenIndex = undefined;
    var count: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        const token = call.queryToken(tree, node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "hole")) continue;
        try std.testing.expect(count < calls.len);
        calls[count] = (try cache.returnCallAt(token, null)).?;
        nodes[count] = node;
        query_tokens[count] = token;
        count += 1;
    }
    try std.testing.expectEqual(calls.len, count);
    try std.testing.expect(calls[0].callee.reference.actual_type.eql(calls[1].callee.reference.actual_type));
    try std.testing.expect(!calls[0].callee.reference.actual_type.eql(calls[2].callee.reference.actual_type));
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    const owners = [_][]const u8{ "first", "first", "safe" };
    for (calls, 0..) |call, index| {
        cache.beginNormalCleanup();
        // Source admission leaves an initiating caller after its stack unwinds.
        // A memo retains the first stopped walk, not the later caller's site.
        try cache.enterNormalCleanup(nodes[index]);
        cache.leaveNormalCleanup();
        cleanup_budget.remaining = 0;
        try std.testing.expectError(error.AnalysisBudgetExceeded, cache.callResultValueAt(query_tokens[index], null, true, &call));
        const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
        try std.testing.expectEqualStrings("/tmp/zbc-return-replay-failure.zig", failure.document);
        try std.testing.expectEqualStrings(owners[index], failure.function.slice());
        const diagnostic_node = nodes[if (index == 1) 0 else index];
        try std.testing.expectEqual(tree.tokenStart(tree.nodeMainToken(diagnostic_node)), failure.byte);
        try std.testing.expectEqual(@as(u32, 0), cleanup_budget.remaining);
        cache.endNormalCleanup();
        try std.testing.expectEqual(@as(usize, if (index == 2) 2 else 1), cache.return_replay_failures.count());
    }
    // An unequal allowance must walk again, even though both attempts fail.
    cache.beginNormalCleanup();
    cleanup_budget.remaining = 1;
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.callResultValueAt(query_tokens[0], null, true, &calls[0]));
    try std.testing.expect(budget_mod.take() != null);
    cache.endNormalCleanup();
    try std.testing.expectEqual(@as(usize, 3), cache.return_replay_failures.count());
    // New completed facts must invalidate an old exact-allowance failure:
    // the same bounded replay can become cheaper after a syntax index settles.
    const first_key: ReplayFailureKey = .{
        .callee = resolvedCleanupKey(calls[0].callee.reference, calls[0].callee.declaration),
        .remaining = 0,
        .depth = 0,
    };
    // Settling a nested failure also changes the work a replay would do.
    // Its stamp is separate from completed entries to prevent cancellation.
    try std.testing.expectEqual(@as(usize, 0), cache.return_replay_failures.get(first_key).?.exhausted_entries);
    try cache.effects_state.exhausted.put(gpa, .{
        .key = .{
            .declaration = first_key.callee.declaration,
            .parameter = 0,
            .path = 0,
            .context = null,
        },
        .mode = .whole,
    }, .{ .budget = 50_000, .diagnostic = .{
        .limit = .normal_cleanup_nodes,
        .limit_value = 50_000,
        .reached = 50_000,
    } });
    cache.beginNormalCleanup();
    cleanup_budget.remaining = 0;
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.callResultValueAt(query_tokens[0], null, true, &calls[0]));
    _ = budget_mod.take();
    cache.endNormalCleanup();
    try std.testing.expectEqual(@as(usize, 1), cache.return_replay_failures.get(first_key).?.exhausted_entries);
    const old_stamp = cache.return_replay_failures.get(first_key).?.memo_entries;
    cache.beginNormalCleanup();
    _ = try cache.returnReplaySyntax(calls[0].callee);
    cache.endNormalCleanup();
    cache.beginNormalCleanup();
    cleanup_budget.remaining = 0;
    _ = cache.callResultValueAt(query_tokens[0], null, true, &calls[0]) catch |err| retry: {
        try std.testing.expect(err == error.AnalysisBudgetExceeded);
        if (cache.return_replay_failures.get(first_key)) |failure|
            try std.testing.expect(failure.memo_entries != old_stamp);
        _ = budget_mod.take();
        break :retry false;
    };
    cache.endNormalCleanup();
    // Fresh allowances can complete. Completed verdicts always win over
    // an earlier failure, even when the next caller has no work left.
    const first_may_undefined = try cache.callResultValueAt(query_tokens[0], null, true, &calls[0]);
    const safe_defined = try cache.callResultValueAt(query_tokens[2], null, false, &calls[2]);
    try std.testing.expectEqual(@as(usize, 2), cache.return_defined_summaries.count());
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    cleanup_budget.remaining = 0;
    try std.testing.expectEqual(first_may_undefined, try cache.callResultValueAt(query_tokens[1], null, true, &calls[1]));
    try std.testing.expectEqual(safe_defined, try cache.callResultValueAt(query_tokens[2], null, false, &calls[2]));
    try std.testing.expect(budget_mod.take() == null);
}

test "FileCache: nested replay failures preserve raw sites for outer collectors" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn hole() u8 { return undefined; }
        \\fn caller() u8 { return hole(); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-nested-replay-site.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var actual: ?FileCache.ActualCallSummary = null;
    var caller_node: ?Ast.Node.Index = null;
    var query_token: ?Ast.TokenIndex = null;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        const token = call.queryToken(tree, node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "hole")) continue;
        actual = (try cache.returnCallAt(token, null)).?;
        caller_node = node;
        query_token = token;
    }
    const call = actual orelse return error.TestUnexpectedResult;
    const saved_site = replay_failure_site;
    defer replay_failure_site = saved_site;
    replay_failure_site = null;
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    for (0..64) |_| try cache.enterNormalCleanup(caller_node.?);
    defer for (0..64) |_| cache.leaveNormalCleanup();
    try std.testing.expectError(error.AnalysisBudgetExceeded,
        cache.callResultValueAt(query_token.?, null, true, &call));
    // This child does not own the outer collector. Its raw failure must
    // survive its unwind, while the visible diagnostic keeps the caller.
    const site = replay_failure_site orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(tree, site.tree);
    try std.testing.expectEqual(tokens.bodyOf(call.callee.tree, call.callee.declaration).?, site.node);
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqualStrings("caller", failure.function.slice());
    try std.testing.expectEqual(tree.tokenStart(tree.nodeMainToken(caller_node.?)), failure.byte);
    try std.testing.expectEqual(@as(usize, 0), cache.return_replay_failures.count());
}

test "FileCache: memoized replay failures outlive nested caches and borrowed demands" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn hole() u8 { return undefined; }
        \\fn first() u8 { return hole(); }
        \\fn second() u8 { return hole(); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-replay-failure-lifetime.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var calls: [2]FileCache.ActualCallSummary = undefined;
    var nodes: [2]Ast.Node.Index = undefined;
    var count: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        const token = call.queryToken(tree, node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "hole")) continue;
        try std.testing.expect(count < calls.len);
        calls[count] = (try cache.returnCallAt(token, null)).?;
        nodes[count] = node;
        count += 1;
    }
    try std.testing.expectEqual(calls.len, count);
    var foreign = try Ast.parse(gpa, "fn foreign() u8 { return undefined; }", .zig);
    defer foreign.deinit(gpa);
    const foreign_node = foreign.rootDecls()[0];
    const saved_site = replay_failure_site;
    defer replay_failure_site = saved_site;
    replay_failure_site = null;
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    const probe_dumped = cleanup_probe_dumped.swap(false, .monotonic);
    defer cleanup_probe_dumped.store(probe_dumped, .monotonic);
    const key: ReplayFailureKey = .{
        .callee = resolvedCleanupKey(calls[0].callee.reference, calls[0].callee.declaration),
        .remaining = 0,
        .depth = 0,
    };
    cache.beginNormalCleanup();
    try cache.enterNormalCleanup(nodes[0]);
    cache.leaveNormalCleanup();
    cleanup_budget.remaining = 0;
    {
        var nested = FileCache.init(gpa, &foreign);
        defer nested.deinit();
        const demand = try std.heap.page_allocator.alloc(u32, 1);
        defer std.heap.page_allocator.free(demand);
        demand[0] = 3;
        nested.cleanup_demand = .{ .many = demand };
        try std.testing.expect(nested.cleanupBudgetFailureAt(
            &foreign, .normal_cleanup_nodes, 50_000, foreign_node) == error.AnalysisBudgetExceeded);
        const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
        try std.testing.expectEqualStrings("first", failure.function.slice());
        try cache.return_replay_failures.put(gpa, key, .{
            .site = replay_failure_site orelse return error.TestUnexpectedResult,
            .diagnostic = failure,
            .remaining = cleanup_budget.remaining,
            .memo_entries = cache.replayMemoEntries(&cache),
            .exhausted_entries = cache.replayExhaustedEntries(&cache),
        });
    }
    cache.endNormalCleanup();
    // The nested cache has unwound, and its demand page is now unmapped.
    // The memo hit must consult only the current live caller cache.
    replay_failure_site = null;
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    try cache.enterNormalCleanup(nodes[1]);
    cache.leaveNormalCleanup();
    cleanup_budget.remaining = 0;
    const call = calls[1];
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.callResultValueAt(tree.nodeMainToken(nodes[1]), null, true, &call));
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqualStrings("first", failure.function.slice());
    try std.testing.expectEqual(.normal_cleanup_nodes, failure.limit);
    try std.testing.expectEqual(@as(u32, 50_000), failure.limit_value);
    try std.testing.expectEqual(@as(u32, 50_000), failure.reached);
    try std.testing.expectEqual(tree.tokenStart(tree.nodeMainToken(nodes[0])), failure.byte);
    try std.testing.expectEqual(@as(u32, 0), cleanup_budget.remaining);
    try std.testing.expectEqual(&foreign, replay_failure_site.?.tree);
    try std.testing.expectEqual(foreign_node, replay_failure_site.?.node);
}

test "FileCache: computed store result handles retain ordered repairs and bounded alternatives" {
    var pool: FileCache.ComputedStoreBuilders = .{};
    const initial = [_]FileCache.ComputedStoreWrite{
        .{ .path = "safe" },
        .{ .path = "hole", .literal_undefined = true },
    };
    const root = pool.add(.{ .whole_value = true, .writes = &initial }).?;
    var proof: FileCache.DefiniteStoreProof = .{
        .tree = undefined,
        .frame = undefined,
        .call_node = .root,
        .call_tree = undefined,
        .computed_templates = &pool,
    };
    const repaired = FileCache.appendComputedStoreWrite(
        &proof,
        .{ .computations = root },
        .{ .path = "hole" },
    ).?;
    try std.testing.expect(root != repaired);
    const root_node = pool.values[@ctz(root)].?;
    const repair_node = pool.values[@ctz(repaired)].?;
    try std.testing.expect(root_node.writes[1].literal_undefined);
    try std.testing.expect(!repair_node.writes[0].literal_undefined);
    try std.testing.expectEqual(root, repair_node.base_computations);
    try std.testing.expectEqual(@as(u8, 1), pool.alternativeCount(.{ .computations = repaired }).?);
    const independent = pool.add(.{ .whole_value = true, .writes = &initial }).?;
    try std.testing.expectEqual(@as(u8, 2), pool.alternativeCount(.{ .computations = repaired | independent }).?);
    try std.testing.expect(!pool.overflow);
    try std.testing.expectEqual(root, independent);
    var previous = repaired;
    while (pool.count < 8) {
        previous = pool.add(.{ .base_computations = previous, .writes = &initial }).?;
    }
    try std.testing.expect(pool.add(.{ .base_computations = previous, .writes = &initial }) == null);
    try std.testing.expect(pool.overflow);
    try std.testing.expect(root_node.writes[1].literal_undefined);
}

test "FileCache: computed dependency recipes never taint sibling constructor fields" {
    var pool: FileCache.ComputedStoreBuilders = .{};
    const values = [_]FileCache.ComputedStoreWrite{
        .{ .path = "known", .dependencies = .{ .reads = 1 } },
        .{ .path = "runtime", .dependencies = .{ .inputs = 2 } },
    };
    const root = pool.add(.{ .whole_value = true, .writes = &values }).?;
    try std.testing.expect((FileCache.computedFieldDependencies(&pool, root, "known")).eql(.{ .reads = 1 }));
    try std.testing.expect((FileCache.computedFieldDependencies(&pool, root, "runtime")).eql(.{ .inputs = 2 }));
    try std.testing.expect((FileCache.computedFieldDependencies(&pool, root, "unrelated")).isEmpty());
}

test "FileCache: computed store expansion abstains at eight alternatives and rejects forward bases" {
    var eight: FileCache.ComputedStoreBuilders = .{};
    const supported = [_]FileCache.ComputedStoreWrite{.{
        .path = "value",
        .source = .{ .sources = 0xff, .opaque_alternative = false },
    }};
    const root = eight.add(.{ .whole_value = true, .writes = &supported }).?;
    try std.testing.expectEqual(@as(u8, 8), eight.alternativeCount(.{ .computations = root }).?);
    var nine: FileCache.ComputedStoreBuilders = .{};
    const unsupported = [_]FileCache.ComputedStoreWrite{.{
        .path = "value",
        .source = .{ .sources = 0xff, .opaque_alternative = true },
    }};
    try std.testing.expect(nine.add(.{ .whole_value = true, .writes = &unsupported }) == null);
    try std.testing.expect(nine.overflow);
    try std.testing.expectEqual(@as(usize, 0), nine.count);
    var forward: FileCache.ComputedStoreBuilders = .{};
    try std.testing.expect(forward.add(.{
        .base_computations = 1,
        .writes = &supported,
    }) == null);
    try std.testing.expect(forward.overflow);
    try std.testing.expectEqual(@as(usize, 0), forward.count);
}

test "FileCache: computed literal MAY alternatives obey the expanded eight-arm bound" {
    const component: FileCache.ComputedStoreWrite = .{
        .path = "hole",
        .literal_may_undefined = true,
        .opaque_alternative = true,
    };
    const three = [_]FileCache.ComputedStoreWrite{component} ** 3;
    var admitted: FileCache.ComputedStoreBuilders = .{};
    const supported = admitted.add(.{ .whole_value = true, .writes = &three }).?;
    try std.testing.expectEqual(@as(u8, 8), admitted.alternativeCount(.{ .computations = supported }).?);
    try std.testing.expect(!admitted.overflow);
    const four = [_]FileCache.ComputedStoreWrite{component} ** 4;
    var declined: FileCache.ComputedStoreBuilders = .{};
    try std.testing.expect(declined.add(.{ .whole_value = true, .writes = &four }) == null);
    try std.testing.expect(declined.overflow);
    try std.testing.expectEqual(@as(usize, 0), declined.count);
    try std.testing.expectEqual(@as(usize, 0), declined.write_count);
}

test "FileCache: literal ALL already includes MAY without another alternative" {
    const component: FileCache.ComputedStoreWrite = .{
        .path = "hole",
        .literal_undefined = true,
        .literal_may_undefined = true,
    };
    const four = [_]FileCache.ComputedStoreWrite{component} ** 4;
    var pool: FileCache.ComputedStoreBuilders = .{};
    const supported = pool.add(.{ .whole_value = true, .writes = &four }).?;
    try std.testing.expectEqual(@as(u8, 1), pool.alternativeCount(.{ .computations = supported }).?);
    try std.testing.expectEqual(@as(u16, 1), FileCache.ComputedStoreBuilders.sourceAlternativeCount(null, component));
    var opaque_component = component;
    opaque_component.opaque_alternative = true;
    try std.testing.expectEqual(@as(u16, 2), FileCache.ComputedStoreBuilders.sourceAlternativeCount(null, opaque_component));
    try std.testing.expect(!pool.overflow);
}

test "FileCache: publication skips unconsumed roots but retains selected output-read closure" {
    var pool: FileCache.ComputedStoreBuilders = .{};
    const writes = [_]FileCache.ComputedStoreWrite{.{ .path = "hole", .literal_undefined = true }};
    const handle = pool.add(.{ .whole_value = true, .writes = &writes }).?;
    const root: FileCache.ComputedStoreBase = .{ .computations = handle };
    // Publication accesses only the arena and allocator. No document or value
    // lookup participates in this immutable-template ownership test.
    var owner: FileCache = undefined;
    owner.gpa = std.testing.allocator;
    owner.summary_arena = null;
    defer if (owner.summary_arena) |*arena| arena.deinit();
    var use: FileCache.AddressUse = undefined;
    var reads: [8]?FileCache.WrittenRead = @splat(null);
    try std.testing.expect(try pool.publish(&owner, root, false, &reads, 0, &use));
    try std.testing.expect(owner.summary_arena == null);
    for (use.written_computations) |entry| try std.testing.expect(entry == null);
    reads[0] = .{ .argument = .root, .tree = undefined, .node = .root, .output_base = root };
    try std.testing.expect(try pool.publish(&owner, root, false, &reads, 1, &use));
    try std.testing.expect(owner.summary_arena != null);
    try std.testing.expectEqual(@as(usize, 1), use.written_computations[@ctz(handle)].?.writes.len);
}

test "FileCache: partial field identities use ordered authenticated sources not dependencies" {
    var pool: FileCache.ComputedStoreBuilders = .{};
    const runtime_write = [_]FileCache.ComputedStoreWrite{.{
        .path = "runtime", .source = .{ .projections = 1, .opaque_alternative = false },
    }};
    const first = pool.add(.{ .base_original_alternative = true, .writes = &runtime_write }).?;
    const sibling_write = [_]FileCache.ComputedStoreWrite{.{ .path = "safe", .dependencies = .{ .reads = 2 } }};
    const sibling = pool.add(.{ .base_computations = first, .writes = &sibling_write }).?;
    var memo: [8]?FileCache.ComputedFieldRecipe = @splat(null);
    const kept = FileCache.computedFieldRecipe(&pool, .{ .computations = sibling }, "runtime", &memo);
    try std.testing.expectEqual(@as(u8, 1), kept.source.projections);
    try std.testing.expect(!kept.source.opaque_alternative);
    try std.testing.expect(!kept.needs_root);
    memo = @splat(null);
    const no_identity = FileCache.computedFieldRecipe(&pool, .{ .computations = sibling }, "safe", &memo);
    try std.testing.expectEqual(@as(u8, 0), no_identity.source.projections);
    try std.testing.expect(no_identity.source.opaque_alternative);
    const replacement_write = [_]FileCache.ComputedStoreWrite{.{
        .path = "runtime", .source = .{ .projections = 4, .opaque_alternative = false },
    }};
    const replaced = pool.add(.{ .base_computations = sibling, .writes = &replacement_write }).?;
    memo = @splat(null);
    const changed = FileCache.computedFieldRecipe(&pool, .{ .computations = replaced }, "runtime", &memo);
    try std.testing.expectEqual(@as(u8, 4), changed.source.projections);
    try std.testing.expect(!changed.source.opaque_alternative);
    memo = @splat(null);
    const alternatives = FileCache.computedFieldRecipe(&pool, .{ .computations = sibling | replaced }, "runtime", &memo);
    try std.testing.expectEqual(@as(u8, 5), alternatives.source.projections);
    try std.testing.expect(!alternatives.source.opaque_alternative);
    const child_write = [_]FileCache.ComputedStoreWrite{.{ .path = "runtime.child" }};
    const modified = pool.add(.{ .base_computations = replaced, .writes = &child_write }).?;
    memo = @splat(null);
    const abstained = FileCache.computedFieldRecipe(&pool, .{ .computations = modified }, "runtime", &memo);
    try std.testing.expectEqual(@as(u8, 0), abstained.source.projections);
    try std.testing.expect(abstained.source.opaque_alternative);
    try std.testing.expect(abstained.needs_root);
}

test "FileCache: computed field replacements retain ordered indexed child recipes" {
    var pool: FileCache.ComputedStoreBuilders = .{};
    const children = [_]FileCache.ComputedStoreWrite{
        .{ .path = "", .array_index = 0, .source = .{ .projections = 1, .opaque_alternative = false } },
        .{ .path = "", .array_index = 1, .literal_undefined = true },
    };
    const child = pool.add(.{ .whole_value = true, .is_array = true, .array_extent = 2, .writes = &children }).?;
    var proof: FileCache.DefiniteStoreProof = .{
        .tree = undefined,
        .frame = undefined,
        .call_node = .root,
        .call_tree = undefined,
        .computed_templates = &pool,
    };
    const state: FileCache.ComputedStoreState = .{ .computations = child, .value_nonidentity = true };
    const fields = [_][]const u8{ "runtime", "spare" };
    const replaced = FileCache.appendComputedFieldStoreWrite(&proof, .{ .original_alternative = true },
        .{ .path = "runtime", .opaque_alternative = true, .literal_may_undefined = true }, state, &fields).?;
    const node = pool.values[@ctz(replaced.computations)].?;
    try std.testing.expectEqual(@as(usize, 3), node.writes.len);
    try std.testing.expectEqualStrings("runtime", node.writes[0].path);
    try std.testing.expect(node.writes[0].is_array);
    try std.testing.expectEqual(@as(?u64, 2), node.writes[0].array_extent);
    try std.testing.expect(!node.writes[0].literal_may_undefined);
    try std.testing.expectEqual(@as(?u7, 0), node.writes[1].parent);
    try std.testing.expectEqual(@as(?u64, 0), node.writes[1].array_index);
    try std.testing.expectEqual(@as(u8, 1), node.writes[1].source.?.projections);
    try std.testing.expectEqual(@as(?u7, 0), node.writes[2].parent);
    try std.testing.expectEqual(@as(?u64, 1), node.writes[2].array_index);
    try std.testing.expect(node.writes[2].literal_undefined);
    var scratch: [128]FileCache.ComputedStoreWrite = undefined;
    var count: usize = 0;
    try std.testing.expect(FileCache.appendComputedComponent(&proof, 0, &scratch, &count,
        .{ .path = "runtime", .opaque_alternative = true, .literal_may_undefined = true }, state));
    try std.testing.expectEqual(@as(usize, 3), count);
    try std.testing.expect(!scratch[0].literal_undefined);
    try std.testing.expect(!scratch[0].literal_may_undefined);
    try std.testing.expect(scratch[2].literal_undefined);
}


test "FileCache: pointee MAY invalidation retains COW negatives with UNKNOWN" {
    var inputs: [8]?Ast.Node.Index = @splat(null);
    var proof: FileCache.DefiniteStoreProof = undefined;
    proof.binding_count = 0;
    proof.out_coverage = null;
    proof.written_inputs = &inputs;
    proof.pointee_count = 1;
    proof.pointees[0] = .{
        .token = 0,
        .value = .defined,
        .computed = .{
            .original = .{ .projections = 1, .opaque_alternative = false },
            .base = .{ .computations = 2 },
        },
    };
    proof.invalidateStorePointees();
    const kept = proof.pointees[0].computed.?;
    try std.testing.expectEqual(FileCache.DefiniteStoreValue.unknown, proof.pointees[0].value);
    try std.testing.expectEqual(@as(u8, 2), kept.base.computations);
    try std.testing.expect(kept.base.opaque_alternative);
    try std.testing.expectEqual(@as(u8, 0), kept.original.projections);
    try std.testing.expect(kept.original.opaque_alternative);
}

test "FileCache: callee local C element stores retain selected array holes" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\extern fn opaqueArray(input: *[4]u32) void;
        \\fn first(out: [*c]u32) void { out.* = 1; }
        \\fn poison(out: [*c]u32) void { out.* = undefined; }
        \\fn hole(out: *u32) void { var temp: [4]u32 = undefined; first(&temp); out.* = temp[3]; }
        \\fn sliceHole(out: *u32) void { var temp: [4]u32 = undefined; first(temp[0..4]); out.* = temp[3]; }
        \\fn repaired(out: *u32) void { var temp: [4]u32 = undefined; first(&temp); out.* = temp[0]; }
        \\fn sliceRepaired(out: *u32) void { var temp: [4]u32 = undefined; first(temp[0..4]); out.* = temp[0]; }
        \\fn initialized(out: *u32) void { var temp: [4]u32 = .{1, 2, 3, 4}; first(&temp); out.* = temp[3]; }
        \\fn unknown(out: *u32) void { var temp: [4]u32 = undefined; opaqueArray(&temp); first(&temp); out.* = temp[3]; }
        \\fn poisoned(out: *u32) void { var temp: [4]u32 = .{1, 2, 3, 4}; poison(&temp); out.* = temp[0]; }
        \\fn initializedOpaque(out: *u32) void { var temp: [4]u32 = .{1, 2, 3, 4}; opaqueArray(&temp); first(&temp); out.* = temp[3]; }
        \\fn repairedOpaque(out: *u32) void { var temp: [4]u32 = undefined; opaqueArray(&temp); first(&temp); out.* = temp[0]; }
        \\fn runtimeHole(out: *u32, index: usize) void { var temp: [4]u32 = undefined; first(&temp); out.* = temp[index % 4]; }
        \\fn runtimeInitialized(out: *u32, index: usize) void { var temp: [4]u32 = .{1, 2, 3, 4}; first(&temp); out.* = temp[index % 4]; }
        \\fn runtimeFrozenHole(out: *u32, index: usize) void { var temp: [4]u32 = undefined; first(&temp); const selected = temp[index % 4]; temp = .{1, 2, 3, 4}; out.* = selected; }
        \\fn runtimeFrozenSafe(out: *u32, index: usize) void { var temp: [4]u32 = .{1, 2, 3, 4}; first(&temp); const selected = temp[index % 4]; temp = undefined; out.* = selected; }
        \\fn unsafe_hole() u32 { var result: u32 = undefined; hole(&result); return result; }
        \\fn unsafe_slice() u32 { var result: u32 = undefined; sliceHole(&result); return result; }
        \\fn safe_repaired() u32 { var result: u32 = undefined; repaired(&result); return result; }
        \\fn safe_slice_repaired() u32 { var result: u32 = undefined; sliceRepaired(&result); return result; }
        \\fn safe_initialized() u32 { var result: u32 = undefined; initialized(&result); return result; }
        \\fn unsafe_opaque() u32 { var result: u32 = undefined; unknown(&result); return result; }
        \\fn safe_initialized_opaque() u32 { var result: u32 = undefined; initializedOpaque(&result); return result; }
        \\fn safe_repaired_opaque() u32 { var result: u32 = undefined; repairedOpaque(&result); return result; }
        \\fn unsafe_poisoned() u32 { var result: u32 = undefined; poisoned(&result); return result; }
        \\fn unsafe_runtime(index: usize) u32 { var result: u32 = undefined; runtimeHole(&result, index); return result; }
        \\fn safe_runtime(index: usize) u32 { var result: u32 = undefined; runtimeInitialized(&result, index); return result; }
        \\fn unsafe_runtime_frozen(index: usize) u32 { var result: u32 = undefined; runtimeFrozenHole(&result, index); return result; }
        \\fn safe_runtime_frozen(index: usize) u32 { var result: u32 = undefined; runtimeFrozenSafe(&result, index); return result; }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-callee-local-c-hole.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        const root = tokens.rootIdentifier(tree, operand) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(root)), "temp")) continue;
        const use = (try cache.addressUseAt(tree.nodeMainToken(root))) orelse continue;
        try std.testing.expect(!use.definite_write);
        if (use.location_element_index) |index| {
            try std.testing.expectEqual(@as(u64, 0), index);
            try std.testing.expect(use.location_written);
        }
    }
    var correct = true;
    for (tree.rootDecls()) |declaration| {
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration) orelse continue;
        const name = tree.tokenSlice(proto.name_token orelse continue);
        const safe = std.mem.startsWith(u8, name, "safe_");
        if (!safe and !std.mem.startsWith(u8, name, "unsafe_")) continue;
        var graph = (try cfg_builder_mod.lowerFunctionFullWithZls(
            gpa, tree, declaration, &@import("../config.zig").Default, &cache, &resolver,
        )).?;
        defer graph.deinit(gpa);
        var problems: std.ArrayListUnmanaged(@import("../problem.zig").Problem) = .empty;
        defer {
            for (problems.items) |*problem| problem.deinit(gpa);
            problems.deinit(gpa);
        }
        try @import("../flow/worklist.zig").check(
            gpa, &graph, .{ .path = "/tmp/zbc-callee-local-c-hole.zig" }, &problems,
        );
        var read_token: ?Ast.TokenIndex = null;
        var token = tree.firstToken(declaration);
        while (token <= tree.lastToken(declaration)) : (token += 1) {
            if (tree.tokenTag(token) == .identifier and std.mem.eql(u8, tree.tokenSlice(token), "result"))
                read_token = token;
        }
        const byte = tree.tokens.items(.start)[read_token.?];
        try std.testing.expect(tree.tokenTag(read_token.? - 1) == .keyword_return);
        const return_byte = tree.tokens.items(.start)[read_token.? - 1];
        var reported = false;
        for (problems.items) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                problem.start.byte >= return_byte and problem.start.byte <= byte)
                reported = true;
        }
        if (reported == safe) {
            std.debug.print("local C caller {s}: expected use-undefined={any}, found {any}\n", .{ name, !safe, reported });
            correct = false;
        }
    }
    try std.testing.expect(correct);
}

test "FileCache: conditional scalar physical writes do not grant poisoned input certificates" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn seed(accept: bool, out: *u32) bool { if (!accept) return false; out.* = 1; return true; }
        \\fn definedCaller() u32 { const accept: bool = true; var value: u32 = undefined; if (!seed(accept, &value)) return 0; return value; }
        \\fn poisonedCaller() u32 { const accept: bool = undefined; var value: u32 = undefined; if (!seed(accept, &value)) return 0; return value; }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-conditional-scalar-physical.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var addresses: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .address_of) continue;
        const operand = tree.nodeData(@as(Ast.Node.Index, @enumFromInt(raw))).node;
        const use = (try cache.addressUseOnBooleanAt(tree.nodeMainToken(operand), true)).?;
        try std.testing.expectEqual(addresses == 0, use.definite_write);
        // A strict certificate can omit diagnostic-only recipe publication.
        if (!use.definite_write) {
            try std.testing.expect(use.location_written);
            try std.testing.expect(use.location_computed_complete);
        }
        addresses += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), addresses);
}

test "FileCache: syntax routed return keys retain every contextual distinction" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "fn f() void {}", .zig);
    defer tree.deinit(gpa);
    var other_tree = try Ast.parse(gpa, "fn f() void {}", .zig);
    defer other_tree.deinit(gpa);
    var resolver: TypeResolver = undefined;
    var other_resolver: TypeResolver = undefined;
    const narrow: TypeResolver.ActualTypeID = .{
        .data = .{ .ip_index = .{ .type = .u8_type, .index = null } },
        .is_type_val = false,
    };
    const wide: TypeResolver.ActualTypeID = .{
        .data = .{ .ip_index = .{ .type = .u16_type, .index = null } },
        .is_type_val = false,
    };
    const base: FileCache.ReturnCallKey = .{
        .token = 1,
        .resolver = &resolver,
        .tree = &tree,
        .module = @enumFromInt(0),
        .callable = narrow,
        .container = narrow,
    };
    var keys = [_]FileCache.ReturnCallKey{base} ** 9;
    keys[1].callable = wide;
    keys[2].container = wide;
    keys[3].callable = null;
    keys[4].container = null;
    keys[5].token = 2;
    keys[6].module = @enumFromInt(1);
    keys[7].resolver = &other_resolver;
    keys[8].tree = &other_tree;
    // Deliberate routing collisions must not combine actual instantiations.
    const routing: FileCache.ReturnCallKeyContext = .{};
    try std.testing.expectEqual(routing.hash(keys[0]), routing.hash(keys[1]));
    try std.testing.expectEqual(routing.hash(keys[0]), routing.hash(keys[2]));
    var calls: std.HashMapUnmanaged(FileCache.ReturnCallKey, usize, FileCache.ReturnCallKeyContext, 80) = .empty;
    defer calls.deinit(gpa);
    for (keys, 0..) |key, value| try calls.put(gpa, key, value);
    try std.testing.expectEqual(keys.len, calls.count());
    for (keys, 0..) |key, value| try std.testing.expectEqual(value, calls.get(key).?);

    const source: FileCache.ReturnSourceKey = .{
        .frame = base, .node = @enumFromInt(1), .returns = true,
    };
    var sources = [_]FileCache.ReturnSourceKey{source} ** 6;
    sources[1].returns = false;
    sources[2].stores = true;
    sources[3].mutation_root = @enumFromInt(1);
    sources[4].mutation_root = @enumFromInt(2);
    sources[5].node = @enumFromInt(2);
    var answers: std.HashMapUnmanaged(FileCache.ReturnSourceKey, usize, FileCache.ReturnSourceKeyContext, 80) = .empty;
    defer answers.deinit(gpa);
    for (sources, 0..) |key, value| try answers.put(gpa, key, value);
    try std.testing.expectEqual(sources.len, answers.count());
    for (sources, 0..) |key, value| try std.testing.expectEqual(value, answers.get(key).?);
}

test "FileCache: private module declarations cannot become unrelated opaque method callees" {
    const sources = [_][:0]const u8{
        \\fn hidden(value: u32) u32 { return value; }
        \\pub fn use(value: u32) u32 { return hidden(value); }
        \\pub fn opaqueUser(receiver: anytype) void { receiver.initOwned(); }
        ,
        \\const Private = struct { fn hidden(value: u32) u32 { return value; } };
        \\pub fn namespace() type { return Private; }
        \\pub fn use(value: u32) u32 { return Private.hidden(value); }
        \\pub fn opaqueUser(receiver: anytype) void { receiver.initOwned(); }
        ,
    };
    for (sources) |source| {
        const gpa = std.testing.allocator;
        var context: engine.TypeContext = undefined;
        try context.init(gpa, std.testing.io);
        defer context.deinit();
        var resolver: engine.TypeResolver = undefined;
        try resolver.init(&context, gpa, "/tmp/zbc-private-module-census.zig", source);
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        var cache = FileCache.init(gpa, tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        var target: ?Ast.Node.Index = null;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .fn_decl) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &buffer, node).?;
            if (std.mem.eql(u8, tree.tokenSlice(proto.name_token.?), "hidden")) target = node;
        }
        const calls = (try cache.closedLocalCalls(target.?)) orelse return error.TestExpectedClosedPrivateCalls;
        try std.testing.expectEqual(@as(usize, 1), calls.len);
    }
}

test "FileCache: contextual constructor member lookup cannot rename an unescaped private target" {
    const sources = [_][:0]const u8{
        \\fn hidden(value: u32) u32 { return value; }
        \\pub fn use(value: u32) u32 { return hidden(value); }
        \\pub fn factory(comptime T: type) T { return .init(); }
        ,
        \\fn hidden(value: u32) Alias { _ = value; return .{}; }
        \\const Alias = struct { pub const init = hidden; };
        \\pub fn factory() Alias { return .init(1); }
        ,
        \\fn hidden() u32 { return 1; }
        \\pub fn use() u32 { return hidden(); }
        \\pub fn factory(comptime T: type) T { return .hidden(); }
        ,
    };
    for (sources, 0..) |source, index| {
        const gpa = std.testing.allocator;
        var context: engine.TypeContext = undefined;
        try context.init(gpa, std.testing.io);
        defer context.deinit();
        var resolver: engine.TypeResolver = undefined;
        try resolver.init(&context, gpa, "/tmp/zbc-constructor-member-census.zig", source);
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        var cache = FileCache.init(gpa, tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        var target: ?Ast.Node.Index = null;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .fn_decl) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &buffer, node).?;
            if (std.mem.eql(u8, tree.tokenSlice(proto.name_token.?), "hidden")) target = node;
        }
        const calls = try cache.closedLocalCalls(target.?);
        if (index == 0) {
            try std.testing.expect(calls != null);
            try std.testing.expectEqual(@as(usize, 1), calls.?.len);
        } else try std.testing.expect(calls == null);
    }
}

test "FileCache: diagnostic actual counts never create strict return certificates" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn consume(input: []const u8, count: usize) u8 {
        \\    var value: u8 = undefined;
        \\    for (0..count) |index| value = input[index];
        \\    return value;
        \\}
        \\fn safe(input: []const u8) u8 { return consume(input, 1); }
        \\fn unsafe(input: []const u8) u8 { return consume(input, 0); }
        \\fn alias(input: []const u8) u8 { const count: usize = 1; const copied = count; return consume(input, copied); }
    ;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-diagnostic-actual-count.zig", source);
    defer resolver.deinit();
    var cache = FileCache.init(gpa, &resolver.handle.document.tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const tree = cache.tree;
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        const token = call.queryToken(tree, node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "consume")) continue;
        try std.testing.expectEqual(@as(usize, 2), call.ast.params.len);
        const zero = std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(call.ast.params[1])), "0");
        try std.testing.expect(!try cache.callResultDefinedAt(token, resolver.resolutionFrame()));
        try std.testing.expectEqual(zero, try cache.callResultMayBeUndefinedAt(token, resolver.resolutionFrame()));
        // A diagnostic-only selected replay must not replace the generic
        // negative/UNKNOWN-input verdict used by strict return consumers.
        try std.testing.expect(!try cache.callResultDefinedAt(token, resolver.resolutionFrame()));
        seen += 1;
    }
    try std.testing.expectEqual(@as(usize, 3), seen);
}
