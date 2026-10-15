//! The grow fold: where a declaration's reallocations land.
//!
//! Phase 8 of `FileCache.resolveTransitiveTakes` answers "whose buffer
//! moves", which is a different question from the coarse "can anything
//! move" flag: a getter this file never declared must stop charging its
//! caller, and a callee that reallocates only a list it built for
//! itself must not charge every caller above it.  That answer needs
//! the DECLARATION a call reaches, read where it is declared, and
//! folded transitively across documents under one shared allowance —
//! none of which is about the rest of a file's per-file state, so none
//! of it belongs on the cache that holds it.
//!
//! THE STORAGE IS NOT HERE.  `FileCache` still owns every summary
//! table, every memo, and the single `GrowState` this module's driver
//! runs on; each function takes the cache it reads as its first
//! argument rather than holding a second reference to any of it.  What
//! is here is the fold itself: the bounded path domain, the
//! cross-document state that bounds it, and the driver that folds one
//! declaration at a time.
//!
//! THE THREE CHARGES ARE THE POINT OF `GrowState`.  A declaration
//! entered for its own fold, a fold round, and a call edge traversed to
//! reach a callee are each charged BEFORE the work they pay for, so a
//! wide declaration that reaches thousands of callees spends one unit
//! per edge however cheap each edge is, and a fold cut short says so
//! by name instead of reading downstream as "grows nothing".

const std = @import("std");
const Ast = std.zig.Ast;

const file_cache = @import("file_cache.zig");
const file_model = @import("../model/file_model.zig");
const fn_summary = @import("../model/fn_summary.zig");
const local_bindings = @import("../model/local_bindings.zig");
const tokens = @import("../ast/tokens.zig");
const zls_resolver_mod = @import("../type_resolver.zig");
const budget_mod = @import("../budget.zig");

const FileCache = file_cache.FileCache;
const fresh_storage = @import("fresh_storage.zig");
const DeclKey = file_cache.DeclKey;
const DocumentKey = struct {
    tree: *const Ast,
    module: ModuleId,
    ctx: *zls_resolver_mod.TypeContext,
};
const OpenError = file_cache.OpenError;
const SummaryError = file_cache.SummaryError;
const ActualCallee = FileCache.ActualCallee;
const TokenRange = FileCache.TokenRange;
const ModuleId = @import("type_engine").ModuleId;

/// Where a declaration's reallocations land: the parameter-rooted paths
/// it can grow, the parameters whose handover absorbed a grow this
/// declaration could not root, and whether one of them reached storage
/// it named ITSELF.  An empty `paths` with `unknown` set is the reading
/// that keeps a consumer conservative; the default is exactly that,
/// because a declaration whose analysis has not run cannot say less.
pub const GrowVerdict = struct {
    paths: []const fn_summary.GrowPath = &.{},
    unplaced: []const u32 = &.{},
    unknown: bool = true,
};

const max_grow_field_depth: usize = 8;
const max_grow_paths_per_param: usize = 32;

fn hasRootGrowPath(paths: []const fn_summary.GrowPath, param: u32) bool {
    for (paths) |gp| {
        if (gp.param == param and gp.field.len == 0) return true;
    }
    return false;
}

fn hasUnplacedParam(unplaced: []const u32, param: u32) bool {
    for (unplaced) |seen| {
        if (seen == param) return true;
    }
    return false;
}

pub fn growFieldCovers(prefix: []const u8, field: []const u8) bool {
    if (prefix.len == 0) return true;
    return std.mem.startsWith(u8, field, prefix) and
        (field.len == prefix.len or field[prefix.len] == '.');
}

fn growFieldTooDeep(field: []const u8) bool {
    var depth: usize = 1;
    for (field) |byte| {
        if (byte != '.') continue;
        depth += 1;
        if (depth > max_grow_field_depth) return true;
    }
    return false;
}

/// Keep a bounded prefix antichain per parameter. A wider path covers its
/// descendants. Deep or branching recursion widens to the parameter root,
/// preserving every possible grow effect without enumerating field chains.
fn appendGrowPath(
    arena: std.mem.Allocator,
    paths: *std.ArrayListUnmanaged(fn_summary.GrowPath),
    gp: fn_summary.GrowPath,
) !void {
    var count: usize = 0;
    for (paths.items) |existing| {
        if (existing.param != gp.param) continue;
        if (growFieldCovers(existing.field, gp.field)) return;
        count += 1;
    }
    var widened = gp;
    if (count >= max_grow_paths_per_param or growFieldTooDeep(gp.field)) widened.field = "";
    var index: usize = 0;
    while (index < paths.items.len) {
        const existing = paths.items[index];
        if (existing.param == widened.param and growFieldCovers(widened.field, existing.field)) {
            _ = paths.swapRemove(index);
        } else {
            index += 1;
        }
    }
    try paths.append(arena, widened);
}

/// The round's answer, copied into storage that outlives the round.
/// Each path's field text is copied with it: a parameter's own storage
/// has no text, and one join per stored path is the whole cost.
fn copyGrowPaths(
    arena: std.mem.Allocator,
    paths: []const fn_summary.GrowPath,
) ![]const fn_summary.GrowPath {
    const kept = try arena.alloc(fn_summary.GrowPath, paths.len);
    for (paths, kept) |path, *out| {
        out.* = .{
            .param = path.param,
            .field = if (path.field.len == 0) "" else try arena.dupe(u8, path.field),
        };
    }
    return kept;
}

/// Order-insensitive comparison of two grow-path sets, used to
/// tell a Phase 8 pass that learned nothing new from one that did.
fn growPathsEqual(
    a: []const fn_summary.GrowPath,
    b: []const fn_summary.GrowPath,
) bool {
    if (a.len != b.len) return false;
    outer: for (a) |lhs| {
        for (b) |rhs| {
            if (lhs.param == rhs.param and std.mem.eql(u8, lhs.field, rhs.field)) continue :outer;
        }
        return false;
    }
    return true;
}

/// The same comparison for the handover list.  A pass that
/// learned the same parameters again is not a pass that changed
/// anything, and treating it as one would keep the fixed point
/// running until its cap — and then widen every answer.
fn growParamsEqual(a: []const u32, b: []const u32) bool {
    if (a.len != b.len) return false;
    outer: for (a) |lhs| {
        for (b) |rhs| {
            if (lhs == rhs) continue :outer;
        }
        return false;
    }
    return true;
}

/// A document this cache reads declarations from: the resolver that
/// types it, and the per-file state that analyses it.  Both are owned
/// until the root cache tears down, so a grow path borrowed from them
/// cannot dangle.  The resolver borrows the store's own handle, which is
/// what keeps the document's imports and toolchain sources resolving the
/// way they do for the file under analysis.
pub const SourceDocument = struct {
    resolver: *zls_resolver_mod.TypeResolver,
    cache: FileCache,

    /// Release what this document borrowed and built.  The
    /// `SourceDocument` itself belongs to whoever opened it.
    pub fn deinit(self: *SourceDocument) void {
        self.cache.deinit();
        self.resolver.deinit();
    }
};

/// Declarations a demand-driven fold may have open at once.  The shared
/// cycle set bounds ONE declaration repeating; a chain of distinct ones
/// is a different thing, and each link costs a frame and a document.
/// Past this depth the chain is not read to the end: it gives up as
/// the NAMED resource bound it hit, which travels out as
/// `error.AnalysisBudgetExceeded` and which the CLI can say by name,
/// instead of answering "unknown" forever — an unknown here is read by
/// the caller as unattributed growth, so a chain the analyser simply
/// stopped reading was charged to every caller above it as if it had
/// been proved.  A TRUE cycle, one declaration meeting itself, still
/// answers unknown: there the fold genuinely has nothing more to add,
/// and no work was refused.
const max_open_grow_folds: u32 = 64;

/// Semantic graph work one outermost demand query may spend.  Three
/// things are charged, and each is charged BEFORE the work it pays for:
/// a declaration entered for its own fold, a fold round run, and a
/// call edge traversed to reach a callee.  What makes the bound a
/// bound is that it is the GRAPH that is counted: a wide declaration
/// that reaches thousands of callees spends one unit per edge however
/// cheap each edge is, and the rounds that re-walk the same body spend
/// again, so a fold cannot buy unbounded work by spreading it over
/// passes.  A verdict already computed is read without being charged
/// — only the edge that reaches it is — because re-entering a
/// declaration spends nothing until it is folded.  A body scan or a
/// type-model resolution behind one of those units is NOT counted
/// here: this number bounds how far the graph is walked, not what one
/// node of it costs to read.  Exactly spending the allowance is
/// success; only asking for the NEXT unit is a failure.
const max_grow_fold_work: u32 = 8192;

/// The grow-analysis state one root cache shares with every source
/// document it opens.  Sharing it is what lets a cycle that crosses
/// documents be recognised: each end asks the same set what is being
/// computed right now, instead of opening a second analysis of a file
/// that is already on the stack.
///
/// Public because `FileCache` names it to hold the pointer: the cache
/// owns the one instance and hands it to every document it opens, so
/// there is one type here and exactly one state per root cache.
pub const GrowState = struct {
    /// The root cache, which alone tears this down.
    owner: *FileCache,
    /// One per document, keyed by its tree, module and source context: an
    /// ordinary document cache never lends another context its semantic facts.
    documents: std.AutoHashMapUnmanaged(DocumentKey, *SourceDocument) = .empty,
    /// Verdicts already computed, keyed by the declaration they answer.
    verdicts: std.AutoHashMapUnmanaged(DeclKey, GrowVerdict) = .empty,
    /// Declarations being computed right now.  Meeting one again is a
    /// cycle, and a cycle is charged by the caller — never read as a
    /// declaration that grows nothing.
    active: std.AutoHashMapUnmanaged(DeclKey, void) = .empty,
    /// How many distinct declarations are being folded right now.  The
    /// cycle set stops one declaration repeating; it does not stop a chain
    /// of DIFFERENT declarations, each of which costs a frame and opens its
    /// own document.  This counts that chain.
    open: u32 = 0,
    /// Semantic graph work the OUTERMOST demand query in flight may
    /// still spend, and how many demand queries are on the stack right
    /// now.  One counter, shared by every document the query reaches, so
    /// a chain that crosses documents is bounded once instead of once per
    /// hop.  A query that opens with no query under it starts a whole new
    /// allowance, which is what keeps an error that unwound out of one
    /// query — work half spent, a declaration left on no stack — from
    /// leaving the next query short: the reset happens on the way out of
    /// every query, not only on the way in, and never records the failure
    /// anywhere a later query would read it.
    work_left: u32 = 0,
    queries: u32 = 0,
    /// The call in the file being analysed that opened the demand query
    /// in flight.  Recorded by whoever opens it, and read only to place a
    /// failure: a fold that runs out of resource inside an imported
    /// document has no position in the analysed file, and this is the
    /// point where that walk left it.
    entry_tree: ?*const Ast = null,
    entry_anchor: Ast.TokenIndex = 0,

    /// Note the call that opens the next demand query.  A query already in
    /// flight owns the entry point of the one that opened it, so this
    /// never overwrites one: it is the OUTERMOST entry that is wanted.
    pub fn noteEntry(self: *GrowState, tree: *const Ast, anchor: Ast.TokenIndex) void {
        if (self.queries != 0) return;
        self.entry_tree = tree;
        self.entry_anchor = anchor;
    }

    // ── The query's own lifetime and allowance ──────────────────────
    //
    // These operations ARE the resource discipline: what a query owns,
    // when it starts, when it is handed back, what one unit of it
    // costs, and where an exhausted one is reported.  They live with the
    // counters they move rather than beside them in `FileCache`, so the
    // counters and the rules that keep them honest cannot drift apart:
    // there is no way to reset `work_left` without going through
    // `endQuery`, and no way to spend one without going through
    // `charge`.

    /// Enter one demand query.  The OUTERMOST one owns the allowance and
    /// every declaration under it spends from that one, so it is reset on
    /// the way IN: a query whose work was refused on the way out cannot
    /// hand the next one a depleted budget, and no failure is recorded
    /// anywhere a later query would read it.
    pub fn beginQuery(self: *GrowState) void {
        if (self.queries == 0) self.work_left = max_grow_fold_work;
        self.queries += 1;
    }

    /// Leave one demand query, on EVERY exit — error or success alike —
    /// so no half-folded query leaves a counter or a stack entry behind
    /// for a later one to read.  The last one out drops the allowance and
    /// the entry point with it.
    pub fn endQuery(self: *GrowState) void {
        self.queries -= 1;
        if (self.queries == 0) {
            self.work_left = 0;
            self.entry_tree = null;
        }
    }

    /// Spend one unit of the allowance the query in flight owns, for work
    /// `anchor` is about to start.  Nothing is charged when no query is
    /// open: the fixed-point fold of the file under analysis is bounded by
    /// its own round cap, and a source document is only ever folded from
    /// inside a query, so there is no path that spends this counter
    /// without someone above it accountable for the total.
    pub fn charge(
        self: *GrowState,
        tree: *const Ast,
        anchor: Ast.TokenIndex,
    ) budget_mod.BudgetError!void {
        if (self.queries == 0) return;
        if (self.work_left == 0) {
            return self.failure(.grow_fold_work, max_grow_fold_work, max_grow_fold_work, tree, anchor);
        }
        self.work_left -= 1;
    }

    /// Has the demand query in flight already folded this document's own
    /// declaration?  Its entry in `verdicts` is written once, when the
    /// fold that produces the answer completes, so a read of it before
    /// that moment is a read of a partial answer.  The memo is the same
    /// one that answers a demand query, keyed by the declaration this
    /// document's own tree and module name.
    pub fn settled(
        self: *const GrowState,
        tree: *const Ast,
        module: ModuleId,
        declaration: Ast.Node.Index,
    ) bool {
        return self.verdicts.contains(.{ .tree = tree, .module = module, .declaration = declaration });
    }

    /// Describe a demand-driven grow fold that ran out of resource.
    /// Anchors on the token the refused work was about for, so the
    /// diagnostic points at the call or declaration that could not be
    /// read rather than at the head of the file, and names the function
    /// that contains it.  Line/column come from a direct scan for the
    /// same reason `addressUseFailure` does it: reporting a failure must
    /// not need memory the refused walk could not get.  Allocation free.
    pub fn failure(
        self: *GrowState,
        limit: budget_mod.Limit,
        limit_value: u32,
        reached: u32,
        tree: *const Ast,
        anchor: Ast.TokenIndex,
    ) budget_mod.BudgetError {
        const site = self.failureSite(tree, anchor);
        const at = site.tree;
        const byte = at.tokens.items(.start)[site.anchor];
        const line_col = budget_mod.lineCol(at.source, byte);
        var name: budget_mod.NameBuf = .{};
        if (tokens.enclosingFnDecl(at, site.anchor)) |decl| {
            var buffer: [1]Ast.Node.Index = undefined;
            if (tokens.fnProto(at, &buffer, decl)) |proto| {
                if (proto.name_token) |name_tok| name.set(at.tokenSlice(name_tok));
            }
        }
        return budget_mod.fail(.{
            .limit = limit,
            .limit_value = limit_value,
            .reached = reached,
            .byte = byte,
            .document = budget_mod.documentForTree(at),
            .line = line_col.line,
            .column = line_col.column,
            .function = name,
        });
    }

    /// Where a grow fold failure is reported: the refused site itself when
    /// the fold was running in the file this analysis is ABOUT, and
    /// otherwise the call that opened the demand query, which is the point
    /// in the analysed file where this walk left it. The document identity
    /// always belongs to the tree selected here.
    pub fn failureSite(
        self: *const GrowState,
        tree: *const Ast,
        anchor: Ast.TokenIndex,
    ) struct { tree: *const Ast, anchor: Ast.TokenIndex } {
        if (tree == self.owner.tree) return .{ .tree = tree, .anchor = anchor };
        const entry = self.entry_tree orelse return .{ .tree = tree, .anchor = anchor };
        return .{ .tree = entry, .anchor = self.entry_anchor };
    }

    pub fn deinit(self: *GrowState, gpa: std.mem.Allocator) void {
        var it = self.documents.valueIterator();
        while (it.next()) |entry| {
            const document = entry.*;
            document.deinit();
            gpa.destroy(document.resolver);
            gpa.destroy(document);
        }
        self.documents.deinit(gpa);
        self.verdicts.deinit(gpa);
        self.active.deinit(gpa);
        gpa.destroy(self);
    }
};

/// Rounds a grow-path fold may take to settle.  Each round folds
/// exactly one call hop, so a chain of N hops settles in N rounds;
/// a set still arriving at the cap is an under-approximation and
/// is widened rather than reported at the precision it never
/// reached.
///
/// Public because `FileCache` drives Phase 8's own fixed-point loop
/// against it: the fold over the file under analysis and an on-demand
/// fold inside an imported document are the SAME fold, so they are
/// bounded by this one number rather than by two that could drift.
pub const max_grow_rounds: u32 = 64;

/// Read a summary as a verdict.  The split matters here: a
/// summary's `grows_unknown_path` is the union of what the
/// callee NAMES and what it was HANDED, and folding that union
/// back into a caller's `unknown` would undo the split one level
/// up — every same-file call would carry its callee's handovers
/// as unattributable again.
fn verdictOf(summary: *const fn_summary.FnSummary) GrowVerdict {
    return .{
        .paths = summary.grow_paths,
        .unplaced = summary.unplaced_args,
        .unknown = summary.grows_self_named,
    };
}

/// Re-aim a callee's verdict at this fn's OWN parameters, through
/// the arguments that supplied them.
///
/// The two halves of an unattributed grow are routed apart, and
/// the split is the whole point of this fn: a parameter the
/// CALLER also holds is a handover it can decide on (map it
/// through `call.args`), while a grow that reached a name the
/// CALLEE owns — a global, a threadlocal, storage an opaque
/// constructor handed back — is reachable without any argument at
/// all.  Folding the first into `unknown` is what used to make
/// every call with an unreadable argument look like a call that
/// could move anything; the caller could never discharge it.
fn foldCalleeGrow(
    arena: std.mem.Allocator,
    paths: *std.ArrayListUnmanaged(fn_summary.GrowPath),
    unplaced: *std.ArrayListUnmanaged(u32),
    unknown: *bool,
    call: fn_summary.GrowCall,
    verdict: GrowVerdict,
) !void {
    if (verdict.unknown) unknown.* = true;
    for (verdict.paths) |gp| {
        if (gp.param >= call.args.len) continue;
        switch (call.args[gp.param]) {
            .unknown => try appendUnplacedParam(arena, unplaced, gp.param),
            .param => |pp| {
                if (hasRootGrowPath(paths.items, pp.param)) continue;
                try appendGrowPath(arena, paths, .{
                    .param = pp.param,
                    .field = try fn_summary.joinPath(arena, pp.path, gp.field),
                });
            },
        }
    }
    for (verdict.unplaced) |param| {
        if (param >= call.args.len) continue;
        switch (call.args[param]) {
            .unknown => try appendUnplacedParam(arena, unplaced, param),
            .param => |pp| {
                if (hasRootGrowPath(paths.items, pp.param)) continue;
                try appendGrowPath(arena, paths, .{ .param = pp.param, .field = "" });
            },
        }
    }
}

/// One handover, recorded once.  Duplicates cost a scan and buy
/// nothing: the consumer only asks "was this parameter charged?".
fn appendUnplacedParam(
    arena: std.mem.Allocator,
    unplaced: *std.ArrayListUnmanaged(u32),
    param: u32,
) !void {
    for (unplaced.items) |seen| {
        if (seen == param) return;
    }
    try unplaced.append(arena, param);
}

/// Where the declaration a call TOKEN actually reaches grows, read from the
/// document that declares it.  Null when the type engine cannot connect the
/// token to a declaration, and when that declaration's fold met a cycle: both
/// are open questions, so a caller keeps the name-based summary (or its own
/// conservative reading) instead of treating null as "grows nothing".
pub fn calleeGrowVerdict(cache: *FileCache, callee_token: Ast.TokenIndex) SummaryError!?GrowVerdict {
    const callee = (try actualCalleeOf(cache, callee_token, null)) orelse return null;
    return growVerdictOf(cache, callee);
}

/// A summary read as a verdict; see `verdictOf`.
pub fn summaryGrowVerdict(summary: *const fn_summary.FnSummary) GrowVerdict {
    return verdictOf(summary);
}

pub fn isStandardSliceComparison(cache: *FileCache, callee_token: Ast.TokenIndex) SummaryError!bool {
    const resolver = cache.zls orelse return false;
    const index = try cache.getCallIndex();
    const node = index.by_callee_token.get(callee_token) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = cache.tree.fullCall(&buffer, node) orelse return false;
    return try resolver.stdMemEqlOf(call.ast.fn_expr, call.ast.params.len);
}

/// Propagate the coarse grow flag into `fn_decl` from its
/// callees.  Considers same-file bare calls (`foo()` -> summaryByName)
/// AND same-file/cross-file method calls (`recv.method()` ->
/// summaryByMethod / summaryByMethodCrossFile).  `receiver_type` is the
/// enclosing type for methods (so `cache.method()` resolves), null for
/// free fns.  Returns true iff this call set the flag.
pub fn propagateGrowCoarseOne(
    cache: *FileCache,
    fn_decl: Ast.Node.Index,
    receiver_type: ?[]const u8,
) !bool {
    const s_ptr = try cache.summaryOfFn(fn_decl);
    if (s_ptr.may_grow_collections) return false;

    const tree = cache.tree;
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
                // Bare call -> same-file free fn.
                if (try cache.summaryByName(tree.tokenSlice(t))) |cs| break :blk cs.may_grow_collections;
                break :blk false;
            }
            // Method call `recv.method(` — recv is two tokens back.
            if (t < first + 2 or tags[t - 2] != .identifier) break :blk false;
            const method = tree.tokenSlice(t);
            const recv = tree.tokenSlice(t - 2);
            const recv_type: ?[]const u8 = rt: {
                if (proto) |p| {
                    if (file_cache.paramIndexFor(tree, p, recv)) |pi| {
                        if (try cache.paramContainerName(p, pi)) |tn| break :rt tn;
                    }
                }
                if (std.mem.eql(u8, recv, "cache") or std.mem.eql(u8, recv, "this")) break :rt receiver_type;
                break :rt null;
            };
            const tn: []const u8 = recv_type orelse {
                // `recv` names no container type, so `helpers.growNames(`
                // may still be a free function in the module a file-level
                // declaration names.  A longer chain (`a.b.c(`) is not
                // one: there the qualifier is a field of something else.
                if (t >= first + 3 and tags[t - 3] == .period) break :blk false;
                if (try cache.summaryByQualifiedName(recv, method)) |qs| break :blk qs.may_grow_collections;
                break :blk false;
            };
            if (try cache.summaryByMethod(tn, method)) |cs| break :blk cs.may_grow_collections;
            if (try cache.summaryByMethodCrossFile(tn, method)) |cs| break :blk cs.may_grow_collections;
            break :blk false;
        };
        if (has_effect) {
            const key = @intFromEnum(body);
            if (cache.summaries.getPtr(key)) |entry| {
                entry.may_grow_collections = true;
                return true;
            }
        }
    }
    return false;
}

/// `inferGrowEffects` for one body, computed once and reused by
/// every round that folds it.
///
/// The canonical collector reads only the immutable AST, the proto,
/// the body and the bindings — never a callee's summary — so the
/// answer cannot change between rounds, and re-running it per round
/// re-walks the same body and re-allocates the same paths, calls
/// and claims in the arena.  A body whose analysis ran out of
/// memory is left uncached and recomputed on the next attempt
/// rather than half-filled.
pub fn directGrowEffects(
    cache: *FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    bindings: *const local_bindings.LocalBindings,
) SummaryError!fn_summary.GrowEffects {
    const key = @intFromEnum(body);
    if (cache.direct_effects.get(key)) |cached| return cached;
    if (cache.summary_arena == null) cache.summary_arena = std.heap.ArenaAllocator.init(cache.gpa);
    const effects = try fn_summary.inferGrowEffects(
        cache.summary_arena.?.allocator(),
        cache.tree,
        proto,
        body,
        bindings,
    );
    try cache.direct_effects.put(cache.gpa, key, effects);
    return effects;
}

/// Fill one fn's `grow_paths` / `grows_unknown_path` from its own
/// body plus every call site's folded effects.  Returns true iff
/// this changed the stored answer, which is what Phase 8 iterates
/// on.
///
/// `receiver_type` is the enclosing type of a method, so a
/// `cache.`/`this.` receiver still reaches the type's own methods
/// when its parameter's type expression names no container.
///
/// `unsettled` is set when a name-based read below took a summary of
/// THIS document whose declaration the query had not folded even
/// after settling it on the spot — the declaration is one this query
/// is ALREADY folding, so the entry is a cycle's partial answer
/// rather than a late fill.  It is the one input a round reads that
/// a later round can answer differently, so `resolveGrowPathsAt` —
/// and only it, since a demand query's callee verdicts are complete
/// the moment they are read — uses the flag to decide whether
/// repeating the round can still learn anything.  Phase 8 reads LIVE
/// summaries, which every round changes on purpose, and ignores it.
///
/// A callee this file cannot resolve is charged to the storage the
/// call handed over, AT THAT STORAGE'S PATH.  What an arbitrary
/// free function does with the storage it is given is not decided
/// by its name: it can only reallocate what the arguments reach,
/// so a call that passes nothing reaches nothing, and one that
/// passes anything keeps the possibility open — for exactly the
/// argument it passed, which is what a caller comparing its own
/// storage needs to hear.  An imported free function this file CAN
/// name (`helpers.growNames(…)`) is resolved from the module the
/// qualifier names, and only an unreadable one is charged.
///
/// This function, `foldActualGrow`, `growVerdictOf`, `demandVerdict` and
/// `resolveGrowPathsAt` are declared with `SummaryError` — the union
/// `FileCache` derives from the fallible steps of the whole summary and
/// grow fold — rather than with an inferred set: the fold is mutually
/// recursive, since a declaration's paths come from the declarations it
/// reaches and a source document's own fold is entered from one of
/// them, so reading each other's inferred set is a dependency loop
/// rather than a program.  The named union breaks that loop exactly as
/// an inferred one would not, and it claims only what these steps can
/// return.  `FileCache.resolveTransitiveTakes` makes the same break for
/// the same reason.
pub fn resolveGrowPathsOne(
    cache: *FileCache,
    fn_decl: Ast.Node.Index,
    receiver_type: ?[]const u8,
    unsettled: *bool,
) SummaryError!bool {
    var pbuf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(cache.tree, &pbuf, fn_decl) orelse return false;
    const body = tokens.bodyOf(cache.tree, fn_decl) orelse return false;
    const bindings = try cache.localBindings(proto, body);
    if (cache.summary_arena == null) {
        cache.summary_arena = std.heap.ArenaAllocator.init(cache.gpa);
    }
    // Every path, joined segment and copied field this round builds is a
    // step towards one answer.  They live in an arena that is released
    // when the round ends, and only the answer itself is copied into
    // the cache's own arena below — so a fold that takes its round cap
    // keeps the final set, not thirty-nine rounds of attempts at it.
    var round = std.heap.ArenaAllocator.init(cache.gpa);
    defer round.deinit();
    const arena = round.allocator();
    const kept = cache.summary_arena.?.allocator();

    const direct = try directGrowEffects(cache, proto, body, bindings);
    // Admit the argument domain once; every saturation check in this
    // round reuses its checked width.
    var widest_count: usize = 0;
    for (direct.calls) |call| {
        widest_count = @max(widest_count, call.args.len);
    }
    const widest = std.math.cast(u32, widest_count) orelse return error.SourceTooWide;
    var paths: std.ArrayListUnmanaged(fn_summary.GrowPath) = .empty;
    // A root is the conservative top for this parameter. Keep it across
    // passes so widening cannot narrow again through a recursive call.
    if (cache.summaries.get(@intFromEnum(body))) |previous| {
        for (previous.grow_paths) |gp| {
            if (gp.field.len == 0) try appendGrowPath(arena, &paths, gp);
        }
    }
    for (direct.paths) |gp| try appendGrowPath(arena, &paths, gp);
    var unknown = direct.unknown;
    // Two kinds of unattributed growth, kept apart because a
    // caller can discharge only one of them.  A grow this fn
    // reached through a NAME IT INTRODUCED is reachable from
    // anywhere, so no argument map reaches it; a grow charged to
    // an argument it could not root is the caller's own storage,
    // and the caller knows what it handed over.
    var unplaced: std.ArrayListUnmanaged(u32) = .empty;
    for (direct.claims) |claim| {
        // A claim the declarations cannot vouch for is storage
        // somebody else may still be walking.
        if (!try cache.provesFreshStorage(claim, null)) unknown = true;
    }

    // Declarations of THIS document whose own summary a call below
    // read and that were still unfolded when the round ended, which
    // means this query was already folding them.  It is the one
    // input a round reads that a later round can answer differently,
    // so the list is checked once the round has finished folding —
    // see the report at the end of the loop.
    var unsettled_reads: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
    for (direct.calls) |call| {
        // The answer this round has built is already decided: every
        // edge left would read back exactly what it is about to
        // write.  That is a FIXED POINT of the fold rather than an
        // approximation of one — `growFoldSaturated` says why — and
        // stopping here leaves the verdict a later edge could have
        // refined exactly as it stands.  What it saves is the rest
        // of this declaration's reachable graph, which for a call
        // into a large module is most of a standard library.
        if (growFoldSaturated(cache, proto, widest, paths.items, unplaced.items, unknown)) break;
        if (try isStandardSliceComparison(cache, call.callee_token)) continue;
        if (try isStandardListLifecycleCall(cache, call.callee_token)) continue;
        // The declaration this call actually reaches, in the
        // document that declares it.  A name alone cannot say
        // which one that is: an alias reaches it, a same-named
        // declaration elsewhere does not, and a receiver this file
        // never declared may still be one.
        if (try foldActualGrow(cache, proto, body, call, arena, &paths, &unplaced, &unknown)) continue;
        // A real call whose callee the type engine could not
        // connect to any declaration.  The invocation still
        // happens; only its identity is unreadable.
        const opaque_callee = cache.zls != null and try isUnnamedCall(cache, call.callee_token);
        var charged_storage = false;
        // Every summary lookup may insert into `cache.summaries`
        // and invalidate earlier pointers, so each callee is read
        // before the next lookup happens.
        switch (call.kind) {
            .bare => {
                // This file's own answer for the name, read
                // WITHOUT the type engine having named the
                // declaration.  A demand fold settles that
                // declaration FIRST: this is the one input a round
                // reads that a later round could answer differently,
                // and an entry the query has not folded reads as
                // "grows nothing" — an answer a later round has to
                // take back by walking the whole body again and
                // re-charging every call edge in it.  Settling it
                // here makes the read complete, so the round this
                // belongs to settles instead of being revised.
                const own_decl = try ownGrowUnsettledByName(cache, call.name);
                if (own_decl) |decl| try settleOwnGrowDecl(cache, decl);
                if (try cache.summaryByName(call.name)) |cs| {
                    // Unsettled still: the fold above met a cycle it
                    // cannot settle, so the entry read here is a
                    // partial answer and the next round has to hear
                    // about it.
                    if (own_decl != null and !ownGrowSettled(cache, own_decl.?)) {
                        try unsettled_reads.append(arena, own_decl.?);
                    }
                    try foldCalleeGrow(arena, &paths, &unplaced, &unknown, call, .{
                        .paths = cs.grow_paths,
                        .unplaced = cs.unplaced_args,
                        .unknown = cs.grows_self_named,
                    });
                } else {
                    // Unresolved, so nothing is known about what
                    // it does — but it can only reallocate what
                    // the call handed it, and that is exactly the
                    // path each argument was rooted at.
                    charged_storage = try chargeHandedStorage(cache, proto, arena, &paths, &unplaced, call, true);
                }
            },
            .qualified => qualified: {
                // No actual call frame was resolved. The qualified query
                // reads the exact imported declaration's direct grow facts,
                // not a contextual normal-cleanup certificate.
                if (try cache.summaryByQualifiedName(call.qualifier, call.name)) |cs| {
                    try foldCalleeGrow(arena, &paths, &unplaced, &unknown, call, .{
                        .paths = cs.grow_paths,
                        .unplaced = cs.unplaced_args,
                        .unknown = cs.grows_self_named,
                    });
                    break :qualified;
                }
                if (try cache.qualifierModule(call.qualifier)) |_| {
                    // The module is readable but its function is not:
                    // the same blind spot as an unresolved bare call.
                    charged_storage = try chargeHandedStorage(cache, proto, arena, &paths, &unplaced, call, true);
                    break :qualified;
                }
                // No readable module — no project, a qualifier that
                // is not an `@import` declaration, a module this
                // project cannot reach, or an import that failed
                // (whose failure the session reports, so it is
                // never a clean bill of health here).  Nothing is
                // known about the callee, but it was handed
                // storage this fn holds, and that storage may be
                // the one somebody is walking.
                charged_storage = try chargeHandedStorage(cache, proto, arena, &paths, &unplaced, call, false);
            },
            .method => method: {
                // `argOwners` always prepends the receiver, but a
                // malformed call must not index past the end.
                if (call.args.len == 0) break :method;
                const owner: fn_summary.ParamPath = switch (call.args[0]) {
                    .unknown => break :method,
                    .param => |p| p,
                };
                const type_name: ?[]const u8 = blk: {
                    if (try receiverTypeName(cache, proto, owner)) |name| break :blk name;
                    if (owner.path.len == 0) {
                        if (cache.paramNameFor(proto, owner.param)) |pname| {
                            if (std.mem.eql(u8, pname, "cache") or std.mem.eql(u8, pname, "this")) {
                                break :blk receiver_type;
                            }
                        }
                    }
                    break :blk null;
                };
                if (type_name) |tn| {
                    // Settled before the read for the same reason
                    // the bare call above settles its own name.
                    const own_decl = try ownGrowUnsettledByMethod(cache, tn, call.name);
                    if (own_decl) |decl| try settleOwnGrowDecl(cache, decl);
                    if (try cache.summaryByMethod(tn, call.name)) |cs| {
                        if (own_decl != null and !ownGrowSettled(cache, own_decl.?)) {
                            try unsettled_reads.append(arena, own_decl.?);
                        }
                        try foldCalleeGrow(arena, &paths, &unplaced, &unknown, call, .{
                            .paths = cs.grow_paths,
                            .unplaced = cs.unplaced_args,
                            .unknown = cs.grows_self_named,
                        });
                        break :method;
                    }
                    if (cache.findMethodAcrossImports(tn, call.name) != null) {
                        // A method another file declares: this file reads
                        // none of its body, so where it reallocates is not
                        // something this fold can place.
                        unknown = true;
                        break :method;
                    }
                }
                // Not resolved: the receiver type or the method is
                // out of this file's reach.  A grow-vocabulary
                // method never reaches here — it is attributed by
                // `inferGrowEffects`'s grow-site pass — but any
                // other name can still reallocate what the call
                // hands it, and only that.  The coarse flag
                // agrees: Phase 9 re-propagates it from here.
                charged_storage = try chargeHandedStorage(cache, proto, arena, &paths, &unplaced, call, false);
            },
            .unresolved => {
                // A method on a receiver this fn was NOT
                // handed and cannot root on a
                // parameter.  Its name is a method name and must not be dispatched
                // to a file-level declaration that shares it, so
                // all that is left is what the call hands over.
                charged_storage = try chargeHandedStorage(cache, proto, arena, &paths, &unplaced, call, false);
            },
        }
        // An opaque callee that was handed nothing of this fn's is
        // not thereby harmless: an indirect invocation reaches
        // whatever it names on its own, including storage this fn
        // never held — a callback taking no collection, a function
        // pointer chosen at runtime.  One that WAS handed this
        // fn's own parameter is already charged at that path,
        // which is the reach a caller comparing its buffer needs.
        if (opaque_callee and !charged_storage) unknown = true;
    }

    // Whether another round could learn anything.  Every other
    // input is a fixed point by the time this one has read it: the
    // direct effects are computed once per body, each callee
    // verdict is COMPLETE the moment `demandVerdict` returns it (and
    // a cycle answers null, which answers null again), and this
    // declaration's own stored answer only changes when this round
    // writes it.  A same-document summary read by the name-based
    // fallback is the exception — it is filled when the declaration
    // behind it is folded, so a read taken before that fill and a
    // read taken after it disagree.  Only a fill that actually
    // happened between the two readings is reported, and Phase 8 —
    // which reads live summaries on purpose — ignores the report.
    for (unsettled_reads.items) |decl| {
        if (ownGrowSettled(cache, decl)) {
            unsettled.* = true;
            break;
        }
    }

    const entry = cache.summaries.getPtr(@intFromEnum(body)) orelse return false;
    // An effect nobody could place is still a reallocation, and so
    // is one this fn placed at a path: either has to reach the
    // coarse flag, or `may_grow_collections` being false would hide
    // the reallocation `grow_paths` / `grows_unknown_path` record.
    if (unknown or paths.items.len != 0 or unplaced.items.len != 0) entry.may_grow_collections = true;
    // The union flag keeps its old meaning for consumers that only
    // ask "can anything move?"; the split beside it is what lets a
    // caller discharge a HANDOVER it can see and never a name the
    // callee owns.
    const unattributed = unknown or unplaced.items.len != 0;
    if (entry.grows_unknown_path == unattributed and
        entry.grows_self_named == unknown and
        growParamsEqual(entry.unplaced_args, unplaced.items) and
        growPathsEqual(entry.grow_paths, paths.items))
    {
        return false;
    }
    entry.grows_unknown_path = unattributed;
    entry.grows_self_named = unknown;
    entry.unplaced_args = try kept.dupe(u32, unplaced.items);
    entry.grow_paths = try copyGrowPaths(kept, paths.items);
    return true;
}

/// `GrowState.settled` for THIS document's own declaration, which is
/// the tree and module every name in here is written in.
pub fn ownGrowSettled(cache: *FileCache, fn_decl: Ast.Node.Index) bool {
    const state = cache.grow_state orelse return false;
    return state.settled(cache.tree, cache.module_id, fn_decl);
}

/// The declaration `name` names in this document while the demand
/// query in flight has NOT folded it yet, and null otherwise: a
/// name this file does not declare, or one whose answer is already
/// memoized, is a read no later round can answer differently.
pub fn ownGrowUnsettledByName(cache: *FileCache, name: []const u8) SummaryError!?Ast.Node.Index {
    const model = try cache.fileModel();
    const fi = model.findFn(name) orelse return null;
    return if (ownGrowSettled(cache, fi.fn_decl)) null else fi.fn_decl;
}

/// `ownGrowUnsettledByName` for the method `method_name` of
/// `type_name` here, on the same terms.
pub fn ownGrowUnsettledByMethod(
    cache: *FileCache,
    type_name: []const u8,
    method_name: []const u8,
) SummaryError!?Ast.Node.Index {
    const model = try cache.fileModel();
    const ti = model.findType(type_name) orelse return null;
    const m = ti.findMethod(method_name) orelse return null;
    return if (ownGrowSettled(cache, m.fn_decl)) null else m.fn_decl;
}

/// Fold a declaration of THIS document now, so the name-based read
/// that follows it takes a finished answer.
///
/// This is the demand fold's last moving input.  Every other input a
/// round reads is already a fixed point the moment it is read: the
/// direct effects are computed once per body, and an actual callee
/// is answered by `demandVerdict`, which memoizes a COMPLETE verdict
/// or answers null for a cycle — both of which answer the same way
/// again next round.  A same-document NAME reaches `summaries` LIVE,
/// and an entry the query has not folded yet reads as "grows
/// nothing".  Reading that fixed an answer a later round had to take
/// back, and taking it back meant walking the whole body again and
/// charging every call edge in it a second time — a repeat charged in
/// full, because every edge really is traversed and charged again,
/// for an input that was already complete the whole time.
///
/// Settling the declaration first removes the moving input instead
/// of iterating around it: the read is complete, one round settles,
/// and the memo that answers it is the same one the actual-callee
/// path uses, so the two routes cannot disagree about a declaration.
/// A declaration this query is ALREADY folding is left alone —
/// `demandVerdict` answers null for it, and a cycle stays an open
/// question the caller charges rather than something this settles.
///
/// Every cache folds on demand: no loop of its own converges on live
/// summaries first, so a same-document name read before its
/// declaration is folded would read the unfolded default.
pub fn settleOwnGrowDecl(cache: *FileCache, fn_decl: Ast.Node.Index) SummaryError!void {
    if (ownGrowSettled(cache, fn_decl)) return;
    _ = try demandVerdict(cache, cache.tree, cache, fn_decl);
}

/// Spend one unit of the allowance the demand query in flight owns.
///
/// This is the only door to the allowance, and it does not exist
/// until a demand query has been opened: a cache with no grow state
/// spends nothing, which is what keeps the fixed-point fold of the
/// file under analysis — bounded by `max_grow_rounds` instead — out
/// of a budget that belongs to queries.  The discipline itself lives
/// with the counters it moves; see `GrowState.charge`.
pub fn chargeGrowWork(
    cache: *FileCache,
    tree: *const Ast,
    anchor: Ast.TokenIndex,
) budget_mod.BudgetError!void {
    const state = cache.grow_state orelse return;
    try state.charge(tree, anchor);
}

pub fn growStateAlloc(cache: *FileCache) error{OutOfMemory}!*GrowState {
    if (cache.grow_state == null) {
        const state: GrowState = .{
            .owner = cache,
            .documents = .empty,
            .verdicts = .empty,
            .active = .empty,
        };
        cache.grow_state = try cache.gpa.create(GrowState);
        cache.grow_state.?.* = state;
    }
    return cache.grow_state.?;
}

/// The per-file state that reads declarations of `handle`, opened
/// once per document and source context and owned until teardown. Its resolver
/// borrows the supplied context's handle, so imports and toolchain sources
/// follow the actual caller without changing the root cache's resolver.
pub fn sourceDocument(
    cache: *FileCache,
    handle: @import("type_engine").DocumentStore.Handle,
    ctx: *zls_resolver_mod.TypeContext,
) OpenError!*SourceDocument {
    const state = try growStateAlloc(cache);
    const key: DocumentKey = .{ .tree = &handle.document.tree, .module = handle.module, .ctx = ctx };
    if (state.documents.get(key)) |document| return document;
    // Heap-allocated before it is initialized: the analyser's
    // allocator points into the resolver's own arena, so the
    // resolver must not move once it holds one.
    const resolver = try cache.gpa.create(zls_resolver_mod.TypeResolver);
    errdefer cache.gpa.destroy(resolver);
    resolver.* = undefined;
    try resolver.initBorrowed(ctx, cache.gpa, handle);
    errdefer resolver.deinit();
    const document = try cache.gpa.create(SourceDocument);
    errdefer cache.gpa.destroy(document);
    document.* = .{ .resolver = resolver, .cache = undefined };
    // `FileCache.init` cannot fail: it holds the tree it is handed and
    // allocates nothing, so there is no half-open document to unwind.
    document.cache = FileCache.init(cache.gpa, &resolver.handle.document.tree);
    // Wired after the document is in its final place: the cache
    // borrows the resolver, and neither is ever moved.
    document.cache.setZls(resolver);
    document.cache.grow_state = state;
    document.cache.grow_on_demand = true;
    try state.documents.put(cache.gpa, key, document);
    return document;
}

/// The declaration a call's callee expression reaches, resolved
/// once per callee token.  Null when the type engine cannot name
/// it, when the token belongs to no call, or when the token is not
/// the `fn` keyword of the declaration it points at.
///
/// RESOLVED FIRST, PUBLISHED SECOND.  The memo takes the key in the
/// one operation that stores a verdict `resolveActualCallee`
/// returned, so every entry in `actual_callees` is a resolution
/// that ran to the end.  Resolving through `getOrPut` reserved the
/// slot first and assigned the value after the work, so a
/// resolution that ran out of memory left the key present holding a
/// byte pattern nothing had ever written — and `isUnnamedCall`
/// reads that slot directly, so it answered from it.  Nothing is
/// published on any failure path, and the next caller resolves
/// again from the beginning.
pub fn actualCalleeOf(
    cache: *FileCache,
    callee_token: Ast.TokenIndex,
    frame: ?zls_resolver_mod.TypeResolver.ResolutionFrame,
) SummaryError!?ActualCallee {
    // A token memo belongs to this document's ordinary resolution context.
    // Instantiated queries borrow their original resolver and never publish
    // contextual answers into a foreign document's token-only memo.
    if (frame == null) {
        if (cache.actual_callees.get(callee_token)) |cached| return cached;
    }
    const resolved = try resolveActualCallee(cache, callee_token, frame);
    if (frame == null) try cache.actual_callees.put(cache.gpa, callee_token, resolved);
    return resolved;
}

/// Standard-list construction and destruction do not grow a caller's list.
/// Resolve the declaration and arity; project lookalikes remain opaque.
pub fn isStandardListLifecycleCall(cache: *FileCache, callee_token: Ast.TokenIndex) !bool {
    const callee = (try actualCalleeOf(cache, callee_token, null)) orelse return false;
    // This lifecycle query owns the ordinary context used by actualCalleeOf.
    const std_tree = (try fresh_storage.toolchainArrayListTree(cache, null)) orelse return false;
    if (callee.tree != std_tree) return false;
    const name = std_tree.tokenSlice(callee.fn_token + 1);
    if (!std.mem.eql(u8, name, "init") and
        !std.mem.eql(u8, name, "initCapacity") and
        !std.mem.eql(u8, name, "deinit")) return false;
    var buffer: [2]Ast.Node.Index = undefined;
    return (try cache.zls.?.callArgumentsOf(&buffer, callee.call_node)) != null;
}

/// True when this callee token really is an INVOCATION whose
/// declaration the type engine could not name.  A token with no
/// call node behind it is a type application or a spelled name, not
/// something that runs, and must not be charged as one.
///
/// It asks `actualCalleeOf` rather than reading `actual_callees`
/// itself, so this answer is the SAME verdict the grow fold acted
/// on and cannot disagree with it: a direct map read had no way to
/// tell a resolution that ran out of memory part-way — whose key
/// used to be left behind holding an unwritten slot — from one that
/// had settled on "resolves to nothing". Source, cancellation and resource
/// failures propagate instead of answering "not an unnamed call".
pub fn isUnnamedCall(cache: *FileCache, callee_token: Ast.TokenIndex) SummaryError!bool {
    const index = try cache.getCallIndex();
    if (index.by_callee_token.get(callee_token) == null) return false;
    return (try actualCalleeOf(cache, callee_token, null)) == null;
}

/// Resolve an invocation's reached declaration without publishing a memo.
/// Structural unknown and non-callable expressions return `null`; source,
/// cancellation and resource failures propagate to the caller.
pub fn resolveActualCallee(
    cache: *FileCache,
    callee_token: Ast.TokenIndex,
    frame: ?zls_resolver_mod.TypeResolver.ResolutionFrame,
) SummaryError!?ActualCallee {
    const query = frame orelse (cache.zls orelse return null).resolutionFrame();
    const index = try cache.getCallIndex();
    const node = index.by_callee_token.get(callee_token) orelse return null;
    const reference = switch (try query.functionReferenceOfCall(node)) {
        .function => |reference| reference,
        .unknown, .not_callable => return null,
    };
    // A named declaration remains known even when an extern function has no
    // body. An unnamed function-type prototype is not a reached declaration.
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const declaration = tokens.enclosingFnDecl(reference.tree, reference.fn_token) orelse declaration: {
        for (reference.tree.nodes.items(.tag), 0..) |tag, index_value| {
            const candidate: Ast.Node.Index = @enumFromInt(index_value);
            const proto = switch (tag) {
                .fn_proto => reference.tree.fnProto(candidate),
                .fn_proto_multi => reference.tree.fnProtoMulti(candidate),
                .fn_proto_one => reference.tree.fnProtoOne(&proto_buffer, candidate),
                .fn_proto_simple => reference.tree.fnProtoSimple(&proto_buffer, candidate),
                else => continue,
            };
            if (proto.ast.fn_token == reference.fn_token and proto.name_token != null)
                break :declaration candidate;
        }
        return null;
    };
    return .{
        .call_node = node,
        .tree = reference.tree,
        .fn_token = reference.fn_token,
        .handle = reference.handle,
        .declaration = declaration,
        .reference = reference,
        .caller_frame = frame,
    };
}

/// Where `callee`'s own reallocations land, computed in the
/// document that declares it.
///
/// A declaration of the file under analysis is folded on demand in
/// that file's own cache.  A declaration anywhere else is computed
/// here, in its own document and with its own imports intact —
/// transitively, because that document folds its callees the same
/// way.  Null when the declaration is already being computed: a
/// cycle is not an answer, and the caller charges it.
///
/// Every branch below opens a demand query, and this is the last
/// place that knows which CALL in the file being analysed opened it:
/// the fold that follows runs in a document this file imports, and a
/// position in an imported document printed under this file's path
/// would name a line this file does not have.
pub fn growVerdictOf(cache: *FileCache, callee: ActualCallee) SummaryError!?GrowVerdict {
    const query = try growStateAlloc(cache);
    query.noteEntry(cache.tree, cache.tree.firstToken(callee.call_node));
    if (callee.tree == cache.tree) return demandVerdict(cache, cache.tree, cache, callee.declaration);
    const resolver = if (callee.caller_frame) |frame| frame.resolver else cache.zls orelse return null;
    const document = try sourceDocument(cache, callee.handle, resolver.ctx);
    return demandVerdict(cache, callee.tree, &document.cache, callee.declaration);
}

/// `growVerdictOf` for the free fn `name` of THIS document, for a caller
/// whose type engine cannot connect the call token to a declaration.  Null
/// when the file declares no such fn and when the fold met a cycle.
pub fn ownFnGrowVerdict(cache: *FileCache, name: []const u8) SummaryError!?GrowVerdict {
    const model = try cache.fileModel();
    const fi = model.findFn(name) orelse return null;
    const query = try growStateAlloc(cache);
    query.noteEntry(cache.tree, cache.tree.nodeMainToken(fi.fn_decl));
    return demandVerdict(cache, cache.tree, cache, fi.fn_decl);
}

/// Compute one declaration's verdict on demand, once per
/// declaration, guarded against re-entering one already on the
/// stack.  A cycle is not an answer: it reads as null so the caller
/// charges, never as a declaration that grows nothing.
///
/// Two bounds apply to the chain of DISTINCT declarations this opens,
/// and both belong to the query rather than to any one declaration:
/// `max_open_grow_folds` declarations at once, and `max_grow_fold_work`
/// units of semantic graph work per OUTERMOST query, shared down
/// whatever documents the chain crosses.  Exceeding either is a named
/// resource failure the CLI reports, which is what keeps a fold that
/// was cut short from reading downstream as "this callee grows
/// nothing" — and keeps a true cycle, where nothing was cut short,
/// reading as unknown.
pub fn demandVerdict(
    cache: *FileCache,
    tree: *const Ast,
    document: *FileCache,
    fn_decl: Ast.Node.Index,
) SummaryError!?GrowVerdict {
    const state = try growStateAlloc(cache);
    const key: DeclKey = .{ .tree = tree, .module = document.module_id, .declaration = fn_decl };
    if (state.verdicts.get(key)) |verdict| return verdict;
    // Entering one is an open question, never an answer, and nothing
    // incomplete is ever cached as a declaration that grows nothing.
    if (state.active.contains(key)) return null;
    // A chain this deep is not read to the end, and saying so as an
    // unknown would charge every caller above it for growth nobody
    // proved: the fold stopped, which is a resource failure to report.
    if (state.open >= max_open_grow_folds) {
        return state.failure(
            .grow_fold_depth,
            max_open_grow_folds,
            state.open,
            tree,
            tree.nodeMainToken(fn_decl),
        );
    }
    // The outermost query owns the allowance; every declaration under
    // it spends from that one, and both halves of that are the
    // state's business: `beginQuery` resets the allowance on the way
    // IN so a query whose work was refused on the way out cannot hand
    // the next one a depleted budget, and `endQuery` runs on the way
    // out of every exit — error or success alike — so no half-folded
    // query leaves a counter or a stack entry behind for a later one
    // to read.
    state.beginQuery();
    defer state.endQuery();
    // One unit for entering this declaration, spent before it is
    // folded.  A verdict already computed above returned without
    // reaching here, and a cycle already on the stack is not work at
    // all: neither re-reads a body.
    try chargeGrowWork(cache, tree, tree.nodeMainToken(fn_decl));
    try state.active.put(cache.gpa, key, {});
    state.open += 1;
    defer {
        state.open -= 1;
        _ = state.active.remove(key);
    }
    const verdict = try resolveGrowPathsAt(document, fn_decl);
    try state.verdicts.put(cache.gpa, key, verdict);
    return verdict;
}

/// One declaration's grow paths, folded to the same fixed point
/// the file under analysis uses, on demand.  `resolveGrowPathsOne`
/// is a step of that fold; here it is driven one declaration at a
/// time, because no outer loop over a whole source document is
/// running to drive it.
///
/// A declaration that returns the literal `type` builds one.  Its
/// body is evaluated at comptime and yields no runtime storage, so
/// there is nothing in it a caller could have handed over.  That is
/// also what keeps a generic INSTANTIATION out of the fold: in a
/// type position `std.array_list.Managed(u32)` has a call's whole
/// shape — callee, parenthesised arguments — and reaches a
/// declaration like this one, so reading its body as unattributed
/// growth would charge a type annotation as if it were a realloc.
///
/// ONE round settles a declaration here, where the file under
/// analysis needs several.  A demand fold reads its callees
/// through `demandVerdict`, which returns a COMPLETE verdict or
/// nothing: a callee that is still being computed answers null and
/// is charged as unknown, and one that is not is already memoized
/// at its own fixed point.  So every verdict this round folds in is
/// the verdict the next round would fold in too, and the work the
/// next round spends re-walking the body buys the answer it already
/// has.  That is not a shortcut around the cap — the cap is charged
/// per round below, so a fold that still needs a second one still
/// pays for it — it is the removal of a round that could only
/// re-derive what this one derived.
///
/// What is left is the ONE input that can still move, and
/// `unsettled` names it: a call the type engine could not connect is
/// answered from THIS document's own summary table, whose entry is
/// filled when its declaration is folded.  That read is settled
/// before it is taken (`settleOwnGrowDecl`), so the only declaration
/// still unsettled at the end of a round is one this query is
/// ALREADY folding — a cycle, which no round of this one can settle
/// and which the round cap below bounds exactly as before.
///
/// A repeat round is therefore paid for in full: the unit below is
/// spent before the round walks the body again, and every call edge
/// it re-traverses is charged again inside `foldActualGrow`.  What
/// changed is how OFTEN one is asked for — a complete read makes the
/// answer it produces the answer the next round would produce, so
/// `changed` reports no movement and the loop stops.
pub fn resolveGrowPathsAt(cache: *FileCache, fn_decl: Ast.Node.Index) SummaryError!GrowVerdict {
    if (tokens.returnsType(cache.tree, fn_decl)) return .{ .paths = &.{}, .unknown = false };
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(cache.tree, &proto_buffer, fn_decl) orelse return .{};
    const body = tokens.bodyOf(cache.tree, fn_decl) orelse return .{};
    // Phase 8 writes through `summaries`, so the entry has to exist
    // before the first pass reads it back.
    _ = try cache.summaryOfFn(fn_decl);
    const model = try cache.fileModel();
    const receiver_type: ?[]const u8 = if (model.containingTypeAtToken(proto.ast.fn_token)) |owner|
        owner.qualified_name
    else
        null;
    var rounds: u32 = 0;
    // One unit per round, spent before the round walks the body
    // again.  The round cap below still decides when a set is called
    // unconverged; this decides when a fold has cost more than one
    // query may spend, which a wide declaration reaches long before
    // any single declaration needs 64 rounds.
    while (rounds < max_grow_rounds) : (rounds += 1) {
        try chargeGrowWork(cache, cache.tree, proto.ast.fn_token);
        var unsettled = false;
        const changed = try resolveGrowPathsOne(cache, fn_decl, receiver_type, &unsettled);
        if (!changed) return growVerdictStored(cache, body);
        if (!unsettled) return growVerdictStored(cache, body);
    }
    // The cap was reached with paths still arriving, so this set is
    // an under-approximation.  Say so rather than report precision
    // this document never reached.
    const entry = cache.summaries.getPtr(@intFromEnum(body)) orelse return .{};
    if (entry.may_grow_collections) {
        entry.grows_unknown_path = true;
        entry.grows_self_named = true;
    }
    return verdictOf(entry);
}

pub fn growVerdictStored(cache: *FileCache, body: Ast.Node.Index) GrowVerdict {
    const entry = cache.summaries.getPtr(@intFromEnum(body)) orelse return .{};
    return verdictOf(entry);
}

/// True when `callee` is declared in the toolchain's `std` sources.
fn declaredInToolchain(cache: *FileCache, callee: ActualCallee) SummaryError!bool {
    const resolver = if (callee.caller_frame) |frame| frame.resolver else cache.zls orelse return false;
    return resolver.declaredUnderToolchain(callee.handle, "/std");
}

/// Fold the grow paths of the declaration `call` actually reaches
/// into this fn's own answer.  True when the call was dispatched.
///
/// Once identity is known the call belongs to that declaration and
/// to nothing else, so every outcome here is an answer about IT:
///
///   - paths folded through the arguments the parameters actually
///     received — the real receiver arity, the real variadic rule;
///   - `unknown` carried over when the declaration has a
///     reallocation its own document could not place;
///   - `unknown` recorded for a cycle or an argument map the
///     declaration's own arity does not admit. Source and analysis failures
///     propagate rather than becoming a growth verdict. None of those is
///     evidence that the declaration grows nothing, and none of
///     them may fall back to a NAME lookup, which could reach a
///     different declaration that happens to share the spelling.
///
/// A declaration read as growing NOTHING is kept as precision: the
/// whole point of resolving the actual callee is that a getter this
/// file never declared stops charging its caller.
///
/// False leaves the call to the name-based routing below, which is
/// for a token the type engine could not connect to any call at
/// all — and then the routing below also carries the opaque-call
/// rule, because an invocation whose identity is unreadable may
/// reach storage this fn never held.
pub fn foldActualGrow(
    cache: *FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    call: fn_summary.GrowCall,
    arena: std.mem.Allocator,
    paths: *std.ArrayListUnmanaged(fn_summary.GrowPath),
    unplaced: *std.ArrayListUnmanaged(u32),
    unknown: *bool,
) SummaryError!bool {
    if (cache.zls == null) return false;
    const callee = (try actualCalleeOf(cache, call.callee_token, null)) orelse return false;
    // The toolchain's own library reallocates through an allocator interface
    // whose calls no declaration can name, so a fold INTO it can only read
    // as "unknown".  What a std routine can move is what the call hands it:
    // that is charged, per argument, exactly like a callee this file cannot
    // read, and nothing beyond it.
    if (try declaredInToolchain(cache, callee)) {
        _ = try chargeHandedStorage(cache, proto, arena, paths, unplaced, call, false);
        return true;
    }
    const resolver = cache.zls.?;
    // One buffer backs both reads: the call's own argument storage
    // for the fixed-arity call shapes, so it outlives every node
    // taken from it here.
    var call_buffer: [2]Ast.Node.Index = undefined;
    // One unit for the EDGE, spent before it is traversed — and spent
    // whether or not the callee already has an answer, because
    // reaching it is the graph work either way.  What the callee's
    // own fold costs is charged inside `demandVerdict`, so a verdict
    // read from the memo is never charged twice for the same
    // traversal, and a fresh one pays for both.
    try chargeGrowWork(cache, cache.tree, call.callee_token);
    const verdict = (try growVerdictOf(cache, callee)) orelse {
        // The declaration is known and its analysis did not
        // finish.  That is an open question, not a negative one.
        unknown.* = true;
        return true;
    };
    if (verdict.unknown) unknown.* = true;
    if (verdict.paths.len == 0 and verdict.unplaced.len == 0) return true;
    // Read here, not by the caller: `growVerdictOf` above may have
    // folded a declaration of THIS document, and every such fold
    // builds the bindings of another body in the same table — which
    // rehashes it and moves every pointer into it.
    const bindings = try cache.localBindings(proto, body);
    // A handover this fn's own call supplied: the callee grows
    // whatever it was given, and this call is the one that gave
    // it.  A parameter the call does not pass is the callee's own
    // business and stays unattributed.
    for (verdict.unplaced) |param| {
        const argument = (try resolver.callArgumentIn(&call_buffer, callee.call_node, param)) orelse {
            unknown.* = true;
            continue;
        };
        const first = cache.tree.firstToken(argument);
        const last = cache.tree.lastToken(argument);
        switch (try fn_summary.ownerOfExpr(arena, cache.tree, proto, bindings, first, last, 0)) {
            .param => |pp| try appendGrowPath(arena, paths, .{ .param = pp.param, .field = "" }),
            .unknown => try appendUnplacedParam(arena, unplaced, param),
        }
    }
    // A verdict read from another document points into that
    // document's arena.  It is copied in rather than borrowed, so
    // the path this records survives independently of the source it
    // was read from.
    const own = callee.tree == cache.tree;
    for (verdict.paths) |gp| {
        const argument = (try resolver.callArgumentIn(&call_buffer, callee.call_node, gp.param)) orelse {
            // This declaration grows a parameter this call does not
            // hand it.  Where that storage came from is undecided.
            unknown.* = true;
            continue;
        };
        const first = cache.tree.firstToken(argument);
        const last = cache.tree.lastToken(argument);
        const field: []const u8 = if (own) gp.field else try arena.dupe(u8, gp.field);
        const rooted: ?fn_summary.ParamPath = blk: {
            switch (try fn_summary.ownerOfExpr(arena, cache.tree, proto, bindings, first, last, 0)) {
                .param => |pp| break :blk pp,
                .unknown => {},
            }
            // Not one of this fn's parameters.  A receiver or an
            // explicit argument this fn BUILT is still not storage
            // its caller holds, and only the canonical fresh proof
            // says so: a header copied from a parameter, a global,
            // and anything this file cannot trace all keep the
            // possibility open.  The same proof is asked of an
            // explicit argument as of a receiver — one that was
            // constructed here is as private as one that was not
            // handed over.
            switch (try fn_summary.growBaseOfExpr(arena, cache.tree, proto, bindings, first, last)) {
                .unproven => |claim| {
                    // A receiver or an explicit argument this call
                    // HANDED OVER, whose initializer the
                    // declarations cannot vouch for.  It is the
                    // caller's storage, not a name the callee
                    // owns: record the handover so a caller that
                    // mapped its arguments can decide.  Folding it
                    // into `unknown` said only "somewhere", which
                    // no caller can ever discharge — and that is
                    // what charged `&out.writer` to every list the
                    // caller happened to be walking.
                    if (!try cache.provesFreshStorage(claim, null)) {
                        try appendUnplacedParam(arena, unplaced, gp.param);
                    }
                    break :blk null;
                },
                .storage => |storage| switch (storage) {
                    // An argument this call HANDED OVER and this
                    // file cannot root is the caller's storage, not
                    // a name the callee owns: record which handover
                    // it was so a caller that mapped its arguments
                    // can decide.  Folding it into `unknown` would
                    // say only "somewhere", which no caller can
                    // ever discharge.
                    .unknown => {
                        try appendUnplacedParam(arena, unplaced, gp.param);
                        break :blk null;
                    },
                    .param => |pp| break :blk pp,
                },
            }
        };
        const path = rooted orelse continue;
        if (hasRootGrowPath(paths.items, path.param)) continue;
        try appendGrowPath(arena, paths, .{
            .param = path.param,
            .field = try fn_summary.joinPath(arena, path.path, field),
        });
    }
    return true;
}

/// Conservative fallback for a Phase 8 that hit its iteration cap:
/// every summary that grows anything also grows storage its paths
/// never recorded.
pub fn widenUnconvergedGrowEffects(cache: *FileCache) !void {
    var it = cache.summaries.valueIterator();
    while (it.next()) |entry| {
        // An under-approximated answer is read as "can move
        // anything", and that reading belongs to the half no
        // caller can map: naming it as a handover would promise a
        // parameter index the cap never produced.
        if (entry.may_grow_collections) {
            entry.grows_unknown_path = true;
            entry.grows_self_named = true;
        }
    }
}

pub fn propagateCoarseGrowAgain(cache: *FileCache, model: *const file_model.FileModel) !void {
    var iters: u32 = 0;
    while (iters < 16) : (iters += 1) {
        var changed = false;
        for (model.fns) |fi| {
            if (try propagateGrowCoarseOne(cache, fi.fn_decl, null)) changed = true;
        }
        for (model.types) |ti| {
            for (ti.methods) |m| {
                if (try propagateGrowCoarseOne(cache, m.fn_decl, ti.qualified_name)) changed = true;
            }
        }
        if (!changed) break;
    }
}

/// Type name of the container `owner` designates: the parameter's
/// own container for a bare parameter, or the field chain's final
/// struct.  Null when the chain's types do not resolve.
pub fn receiverTypeName(
    cache: *FileCache,
    proto: Ast.full.FnProto,
    owner: fn_summary.ParamPath,
) !?[]const u8 {
    const root = (try cache.paramContainerName(proto, owner.param)) orelse return null;
    if (owner.path.len == 0) return root;
    var resolved = cache.resolvedTypeAcrossImports(root) orelse return null;
    var rest = owner.path;
    while (rest.len != 0) {
        const dot = std.mem.indexOfScalar(u8, rest, '.');
        const segment = if (dot) |at| rest[0..at] else rest;
        resolved = cache.fieldType(resolved, segment) orelse return null;
        if (dot == null) break;
        rest = rest[dot.? + 1 ..];
    }
    return resolved.info.qualified_name;
}

/// Only declared narrow primitive values cannot carry an address.
/// Unknown types and pointer-sized values retain storage effects.
///
/// The answer is a property of the parameter's own declared type, so
/// it is asked once per `(declaration, parameter)` and remembered: an
/// unresolved callee is charged per call edge, every fold round
/// re-walks the same bodies, and each of those asks the type engine
/// the same three questions about the same syntax.  Both answers are
/// kept — a parameter that is a narrow scalar and one that is not are
/// both complete readings — and only a question that RAN TO THE END
/// is filed, so a resolution that failed for want of memory asks
/// again next time instead of being answered from a guess.
pub fn parameterIsNonAddressScalar(
    cache: *FileCache,
    proto: Ast.full.FnProto,
    origin: fn_summary.ParamPath,
) SummaryError!bool {
    if (origin.path.len != 0) return false;
    const key = (@as(u64, proto.ast.fn_token) << 32) | @as(u64, origin.param);
    if (cache.scalar_params.get(key)) |cached| return cached;
    const verdict = try classifyParameterScalar(cache, proto, origin.param);
    // Source failures propagate before publication. A successful unresolved
    // type leaves no scalar certificate, so a later query can resolve it.
    if (verdict) |answer| try cache.scalar_params.put(cache.gpa, key, answer);
    return verdict orelse false;
}

/// The type engine's own answer about the `index`-th parameter's
/// declared type: `true` for a narrow primitive, `false` when
/// nothing here can say it is one, and null when the type engine
/// could not answer at all.  A `false` reached by finishing the walk
/// is an answer and is kept; a null is not one and never is.
pub fn classifyParameterScalar(
    cache: *FileCache,
    proto: Ast.full.FnProto,
    index: u32,
) SummaryError!?bool {
    var parameters = proto.iterate(cache.tree);
    var position: u32 = 0;
    while (parameters.next()) |parameter| : (position += 1) {
        if (position != index) continue;
        const type_node = parameter.type_expr orelse return false;
        if (cache.zls) |resolver| {
            const bool_type = (try resolver.isBoolType(type_node)) orelse return null;
            if (bool_type) return true;
            const int = try resolver.intInfo(type_node);
            if (int) |info| return info.bits < @bitSizeOf(usize);
            const bits = try resolver.floatBits(type_node);
            if (bits) |width| return width < @bitSizeOf(usize);
            return false;
        }
        // In syntax-only mode, only unambiguous primitive declarations
        // prove a scalar. Aliases, wrappers and pointer-sized values do not.
        if (cache.tree.nodeTag(type_node) != .identifier) return false;
        const name = cache.tree.tokenSlice(cache.tree.nodeMainToken(type_node));
        if (!std.zig.isPrimitive(name)) return false;
        if (std.mem.eql(u8, name, "bool")) return true;
        if (name.len > 1 and (name[0] == 'i' or name[0] == 'u')) {
            if (name.len > 2 and name[1] == '0') return false;
            const bits = std.fmt.parseInt(u16, name[1..], 10) catch return false;
            return bits < @bitSizeOf(usize);
        }
        if (name.len > 1 and name[0] == 'f') {
            const bits = std.fmt.parseInt(u16, name[1..], 10) catch return false;
            return bits < @bitSizeOf(usize);
        }
        return false;
    }
    return false;
}

/// Charge what an UNRESOLVED callee was handed.
///
/// Nothing is known about what such a callee does, so the only
/// claim this file can make is the one its arguments support: it
/// can reallocate the storage each argument was rooted at, and
/// nothing else.  That is a PATH, not unattributed storage — the
/// argument's own `ParamPath` — so a caller comparing its own
/// storage against the result sees a handover to `problems` as
/// disjoint from a loop walking `tree.nodes`.
///
/// An argument this file cannot root is the one exception: where
/// it points is exactly what the callee may move, so
/// `charge_unplaced` records it as a HANDOVER — this parameter
/// index — rather than as storage nobody can place.  The caller
/// that wrote the argument knows what it handed over, and an
/// index is the one answer it can act on; a handover that merely
/// said "somewhere" is no answer at all.  A method or a call
/// through a named module never records the handover
/// (`charge_unplaced` is false): a constructor is routinely handed
/// exactly such an argument (`std.heap.page_allocator`), and
/// charging it would turn every locally built header into
/// somebody else's buffer.  A bare call this file cannot resolve
/// keeps the coarse reading — there, an unplaceable argument is
/// all the evidence there is.
pub fn chargeHandedStorage(
    cache: *FileCache,
    proto: Ast.full.FnProto,
    arena: std.mem.Allocator,
    paths: *std.ArrayListUnmanaged(fn_summary.GrowPath),
    unplaced: *std.ArrayListUnmanaged(u32),
    call: fn_summary.GrowCall,
    comptime charge_unplaced: bool,
) SummaryError!bool {
    var charged = false;
    for (call.args, 0..) |arg, param| {
        switch (arg) {
            .param => |pp| {
                if (try parameterIsNonAddressScalar(cache, proto, pp)) continue;
                charged = true;
                try appendGrowPath(arena, paths, .{
                    .param = pp.param,
                    .field = pp.path,
                });
            },
            .unknown => if (charge_unplaced) {
                try appendUnplacedParam(arena, unplaced, @intCast(param));
            },
        }
    }
    return charged;
}

/// Has the verdict this round has built stopped being able to change?
///
/// The fold is monotone over a small domain — parameter-rooted paths,
/// handover indices, and one flag — so a verdict in which all three
/// are already decided is a FIXED POINT of it.  Every remaining edge
/// computes what it would write, finds that already there, and writes
/// nothing.  That is what makes stopping here a change of COST and
/// never of ANSWER: no path a later callee could add is dropped,
/// because there is none left to add, and no edge that would have
/// widened the verdict is skipped, because none of them would.
///
///   - `unknown` is monotone.  A `true` is never taken back, and a
///     `false` cannot be settled by looking at what is left, so the
///     flag has to be TRUE before the remaining edges may be
///     dropped.  A declaration that has not yet reached one folds
///     every edge it has.
///   - every path a callee contributes is compared against
///     `hasRootGrowPath` first, and an existing root path at that
///     parameter absorbs any deeper one — `appendGrowPath` covers
///     by prefix, so `""` covers the whole parameter.  The universe
///     is EVERY DECLARED PARAMETER, not just the ones this body's
///     calls mention: `growBaseOfExpr` follows an alias chain that
///     `argOwners` does not always accept, so an argument the
///     precomputed owners called unplaceable can still root at a
///     parameter nothing here predicted.  Requiring all of them is
///     what keeps that case a fixed point rather than a guess.
///   - a handover index is always below the argument count of the
///     call that produced it, so a handover list already covering
///     `[0, widest)` absorbs every one any remaining call can add.
///
/// A declaration that cannot reach this reading is folded to the end,
/// which is what every declaration did before.
/// `widest` is the checked largest argument count for this round.
pub fn growFoldSaturated(
    cache: *FileCache,
    proto: Ast.full.FnProto,
    widest: u32,
    paths: []const fn_summary.GrowPath,
    unplaced: []const u32,
    unknown: bool,
) bool {
    if (!unknown) return false;
    var parameters = proto.iterate(cache.tree);
    var index: u32 = 0;
    while (parameters.next() != null) : (index += 1) {
        if (!hasRootGrowPath(paths, index)) return false;
    }
    for (0..widest) |param| {
        if (!hasUnplacedParam(unplaced, @intCast(param))) return false;
    }
    return true;
}
