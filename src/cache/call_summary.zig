//! Canonical call identity, binding and parameter-rooted body effects.
//!
//! All documents come from the existing grow state; no source is reopened
//! and no resolver is reconstructed from a spelling.  Finished answers
//! belong to the root FileCache and borrow its immutable snapshots.
//!
//! WHAT IS STORED.  One declaration's answer is a WITNESS SET: the
//! parameter-rooted paths its body was shown to touch, each with the
//! effect that path takes, plus everything the body reached that no
//! formal of it names.  A set is filed under the declaration (tree,
//! module and node), the question asked of it, and the complete
//! instantiated identity of the callee — so two instantiations of one
//! generic declaration never share an entry.  Every path a key holds is
//! an owned copy; nothing here borrows bytes a later pass could move.
//!
//! WHAT IS NOT STORED.  A disjointness proof between the storage a CALL
//! SITE handed this call and the storage another argument names is a fact
//! about that call site and never about the declaration, so it is taken
//! while the query runs and is never written into the memo.  A formal is
//! a coordinate here, not a disjointness proof: nothing is discharged for
//! "that is a different parameter" without the caller's own storage or a
//! positively proved private construction in front of it.
//!
//! EXHAUSTED ROOT DEMANDS.  A root witness demand (empty stack, the query's
//! own 50,000-unit allowance) whose walk ran that allowance out is recorded
//! under its memo key, its walk mode and the allowance it started with.  The
//! same demand with no more allowance stops at once with the same labelled
//! budget failure.  It is a refusal to answer, never an answer: completed
//! answers are looked up first, and nested, borrowed-allowance or cut walks
//! are never recorded.
//!
//! `callEffectAt` asks about parameter-rooted or unrooted storage, or selects
//! all mutation effects with `.whole`. The whole verdict does not certify
//! returned storage, source values, loans, or initialization.
//! A stopped scan is not a completed witness set, but it can complete a
//! read-only-versus-unsafe question. Independent verdict witnesses are kept
//! separately and reused only by that same short-circuit question. Precise
//! effects still walk to EOF; budget failures and cycle cutoffs file nothing.
//! Empty completed all-storage sets also answer narrower questions. Within
//! one body frame, completed acyclic origins are reused by node and depth;
//! failed or cycle-dependent walks never become origin answers.
const std = @import("std");
const Ast = std.zig.Ast;
const file_cache = @import("file_cache.zig");
const FileCache = file_cache.FileCache;
const fn_summary = @import("../model/fn_summary.zig");
const LocalBindings = @import("../model/local_bindings.zig").LocalBindings;
const tokens = @import("../ast/tokens.zig");

const grow_analysis = @import("grow_analysis.zig");
const call_effects = @import("call_effects.zig");
const storage_alias = @import("storage_alias.zig");
const fresh_storage = @import("fresh_storage.zig");
const budget_mod = @import("../budget.zig");
const resolver_mod = @import("../type_resolver.zig");
const TypeResolver = resolver_mod.TypeResolver;
const Iterator = @import("type_engine").AstIterator;

/// Everything a call summary can fail at.  It includes `FileCache`'s
/// `SummaryError` because a summary IS how this module reads a callee, and
/// that read models the callee's own document first: a callee in a source
/// that does not parse, whose token table `std.zig.Ast` cannot address, or
/// which declares more types than a `u32` index holds fails the same way
/// whether it was reached from here or from the summary fold.
pub const Error = file_cache.SummaryError;
pub const Effect = enum { read_only, writes_without_invalidation, may_invalidate, unknown };

/// Which parameter-rooted storage one effect question is about.  Formal
/// numbering counts an implicit instance receiver as parameter zero; `path`
/// is the dotted field path from that formal's own storage, and `""` is the
/// whole of it.
pub const ParameterSelection = struct {
    param: u32,
    path: []const u8 = "",
    /// The caller needs only whether the answer is `.read_only`. Any other
    /// verdict then stands for "not read-only" and its kind is unspecified.
    /// Applies to whole-storage questions (`path == ""`).
    read_only_only: bool = false,
};

/// Storage selected for one mutation-effect question.
pub const EffectSelection = union(enum) {
    /// Storage the caller handed this call, named by a formal of the callee.
    parameter: ParameterSelection,
    /// Storage this call reaches that no formal of the callee names: what
    /// the body writes through a file-level variable, a capture it could
    /// not root, or storage an unresolved callee may touch.  It is never
    /// answered by a parameter's own verdict.
    unrooted,
    /// All formal-rooted and unrooted effects, without caller-storage projection.
    /// `null` resolves the call normally; a supplied canonical callee borrows
    /// its original resolver and must match `token` and the query frame.
    /// Only `.read_only` certifies no mutation, not returned-storage safety.
    whole: ?FileCache.ActualCallee,
};

pub const ActualCallSummary = struct {
    callee: FileCache.ActualCallee,
    /// Declaration and return-provenance facts, without an eager cleanup walk.
    /// Cleanup consumers request FileCache.summaryOfResolvedMethod(callee).
    summary: ?fn_summary.FnSummary,
    argument_offset: ?u1,
    /// Identity queries do not fold effects. Use callEffectAt for a verdict.
    read_only: ?bool,

    /// The buffer belongs to the caller, as it does in TypeResolver.
    /// Argument mapping follows the frame the CALL was reached in, not the
    /// callee's own body frame: the bindings a caller instantiates are the
    /// ones its own arguments were resolved against.
    /// An unsupported argument map returns `null`; source, cancellation and
    /// resource failures propagate without becoming a missing argument.
    pub fn callArgumentFor(
        self: ActualCallSummary,
        cache: *FileCache,
        buffer: *[2]Ast.Node.Index,
        parameter: u32,
    ) Error!?Ast.Node.Index {
        const view = viewFor(cache, self.callee) orelse return null;
        return try view.callArgumentIn(buffer, self.callee.call_node, parameter);
    }

    /// The cache is immovable and owned by the canonical grow state until the
    /// root cache's deinit. The supplied caller frame selects the source
    /// context; a failed open is not a body/purity observation.
    pub fn declaringCache(self: ActualCallSummary, cache: *FileCache) Error!?*FileCache {
        return cacheFor(cache, self.callee);
    }
};

/// Formals used as a QUESTION, not as a coordinate of a witness: `any_param`
/// asks about every formal of a body, `global_only` about the storage none
/// of them names.  A witness owner is a real formal index, `unrooted_param`,
/// or one of these two in a whole-body answer.
const any_param = std.math.maxInt(u32);
const global_only = std.math.maxInt(u32) - 1;
const unrooted_param = std.math.maxInt(u32) - 2;

/// The interned empty path: `State` interns `""` before anything else, so
/// this id is the whole of every formal's own storage.
const root_path: u32 = 0;

/// One allowance for one outermost semantic query, shared by everything that
/// query reaches: this producer's own steps, the storage-disjointness
/// questions it asks, and whatever fresh-storage proofs those run.  A root
/// query seeds one counter here; every recursive edge and every nested query
/// spends the SAME one.
pub const actual_query_work_limit: u32 = 50_000;

/// The enclosing query's context, borrowed.  `frame` is the contextual view
/// the caller's own nodes resolve in; `remaining` is that query's counter,
/// charged directly rather than copied.  A root call passes `.{}` and pays
/// for one allowance of its own.
pub const QueryContext = storage_alias.QueryContext;

const max_depth: u32 = 64;

/// One COMPLETE fact about a body: the formal that owns the storage, the
/// interned path from that formal's root, and what the body does to it.
const Witness = struct {
    param: u32,
    path: u32,
    effect: Effect,
};

/// The same fact while the body is still being scanned.  `operand` and `at`
/// are the expression naming the storage and the node the question is asked
/// at; they are set only for a witness that is not already rooted at the
/// asked formal and therefore still needs this body's own proof.
const Raw = struct {
    param: u32,
    path: u32,
    effect: Effect,
    operand: ?Ast.Node.Index = null,
    /// Only the callee-relative suffix, not the operand's already-spelled path.
    operand_path: u32 = root_path,
    at: ?Ast.Node.Index = null,
};

const Key = struct {
    declaration: file_cache.DeclKey,
    parameter: u32,
    path: u32,
    context: ?TypeResolver.ActualTypeID,
};

const KeyContext = struct {
    pub fn hash(_: KeyContext, key: Key) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const tree = @intFromPtr(key.declaration.tree);
        hasher.update(std.mem.asBytes(&tree));
        hasher.update(std.mem.asBytes(&key.declaration.module));
        hasher.update(std.mem.asBytes(&key.declaration.declaration));
        hasher.update(std.mem.asBytes(&key.parameter));
        hasher.update(std.mem.asBytes(&key.path));
        const present: u8 = @intFromBool(key.context != null);
        hasher.update(std.mem.asBytes(&present));
        // The instantiated identity is a graph, so it is hashed through the
        // engine's own structural hash and never by pointer address.
        if (key.context) |actual| hasher.update(std.mem.asBytes(&actual.hash64()));
        return hasher.final();
    }

    pub fn eql(_: KeyContext, a: Key, b: Key) bool {
        if (a.declaration.tree != b.declaration.tree) return false;
        if (a.declaration.module != b.declaration.module) return false;
        if (a.declaration.declaration != b.declaration.declaration) return false;
        if (a.parameter != b.parameter or a.path != b.path) return false;
        if (a.context == null or b.context == null) return a.context == null and b.context == null;
        return a.context.?.eql(b.context.?);
    }
};

/// How much of a root demand's answer the asker needs; part of the key of a
/// recorded budget failure because a stopping walk and a complete walk are
/// different walks over one declaration.
const DemandMode = enum { complete, whole, cut, cut_advisory };

fn demandMode(mode: Mode) ?DemandMode {
    return switch (mode) {
        .complete => .complete,
        .whole => .whole,
        // A parent frame makes the demand part of a stack; only a root
        // question has none.
        .cut => |cut| if (cut.parent != null) null else if (cut.advisory_ok) .cut_advisory else .cut,
    };
}

/// One root demand: the complete memo key plus the walk mode.
const ExhaustedKey = struct {
    key: Key,
    mode: DemandMode,
};

const ExhaustedKeyContext = struct {
    pub fn hash(_: ExhaustedKeyContext, demand: ExhaustedKey) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const key_hash = KeyContext.hash(.{}, demand.key);
        hasher.update(std.mem.asBytes(&key_hash));
        hasher.update(std.mem.asBytes(&demand.mode));
        return hasher.final();
    }

    pub fn eql(_: ExhaustedKeyContext, a: ExhaustedKey, b: ExhaustedKey) bool {
        return a.mode == b.mode and KeyContext.eql(.{}, a.key, b.key);
    }
};

/// A root demand whose standalone walk ran its whole allowance out.  The walk
/// is a pure function of the key, the allowance it started with and the
/// file's completed answers, which only ever make a later walk cheaper; so a
/// later demand of the same key with no more allowance stops the same way.
/// Never an answer: only the failure to give one.
const Exhausted = struct {
    /// The allowance the exhausted walk started with.
    budget: u32,
    diagnostic: budget_mod.Diagnostic,
};

/// Scopes the thread's pending budget diagnostic to one walk.  `begin` sets
/// the unclaimed record aside; `end` returns the walk's own first failure
/// and leaves the pending record exactly as it would have been without the
/// guard (first failure wins, an older unclaimed one first).
pub const PendingGuard = struct {
    saved: ?budget_mod.Diagnostic,

    pub fn begin() PendingGuard {
        return .{ .saved = budget_mod.take() };
    }

    pub fn end(self: PendingGuard) ?budget_mod.Diagnostic {
        const own = budget_mod.take();
        if (self.saved) |older| budget_mod.fail(older) catch {};
        if (own) |first| budget_mod.fail(first) catch {};
        return own;
    }
};

/// Only source traversal omits the formal/path coordinates. Its instantiated
/// branch proofs still belong to the complete callable graph.
pub const SourcePlanKey = struct {
    declaration: file_cache.DeclKey,
    context: ?TypeResolver.ActualTypeID,
};

pub const SourcePlanKeyContext = struct {
    fn effectKey(key: SourcePlanKey) Key {
        return .{
            .declaration = key.declaration,
            .parameter = any_param,
            .path = root_path,
            .context = key.context,
        };
    }

    pub fn hash(_: SourcePlanKeyContext, key: SourcePlanKey) u64 {
        return KeyContext.hash(.{}, effectKey(key));
    }

    pub fn eql(_: SourcePlanKeyContext, a: SourcePlanKey, b: SourcePlanKey) bool {
        return KeyContext.eql(.{}, effectKey(a), effectKey(b));
    }
};

/// Completed ordered source evidence, not an effect answer. Every stored
/// event is processed again for each formal/path question in a fresh Frame.
/// Identifier uses retain declaration-token identity, including shadowing.
pub const SourcePlan = struct {
    events: []const call_effects.Event,
    formal_uses: std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index),

    pub fn deinit(self: *SourcePlan, gpa: std.mem.Allocator) void {
        gpa.free(self.events);
        self.formal_uses.deinit(gpa);
    }
};

/// Completed body-syntax write evidence. Name and binding-token identity
/// distinguish shadowed variables; token-range and unresolved-write policy
/// remain part of each live origin question, not of this immutable index.
pub const BindingWriteIndex = struct {
    const Write = struct { token: Ast.TokenIndex, declaration: ?Ast.TokenIndex };
    writes: std.StringHashMapUnmanaged(std.ArrayListUnmanaged(Write)) = .empty,

    pub fn deinit(self: *BindingWriteIndex, gpa: std.mem.Allocator) void {
        var lists = self.writes.valueIterator();
        while (lists.next()) |list| list.deinit(gpa);
        self.writes.deinit(gpa);
    }
};

const SourcePlanBuilder = struct {
    events: std.ArrayListUnmanaged(call_effects.Event) = .empty,
    formal_uses: std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index) = .empty,

    fn deinit(self: *SourcePlanBuilder, gpa: std.mem.Allocator) void {
        self.events.deinit(gpa);
        self.formal_uses.deinit(gpa);
    }

    fn note(self: *SourcePlanBuilder, frame: *Frame, node: Ast.Node.Index) Error!void {
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) != .identifier) return;
        const token = tree.nodeMainToken(node);
        const binding = frame.currentBindings().findAt(tree.tokenSlice(token), token) orelse return;
        if (binding.origin != .param) return;
        const entry = try self.formal_uses.getOrPut(frame.cache.gpa, binding.name_token);
        if (!entry.found_existing) entry.value_ptr.* = node;
    }

    fn append(self: *SourcePlanBuilder, gpa: std.mem.Allocator, event: call_effects.Event) Error!void {
        try self.events.append(gpa, event);
    }

    /// Publication follows both Scan EOF and successful frozen witnesses.
    /// A failed allocation leaves no entry; a recursive complete insertion
    /// wins without replacing its owned buffers.
    fn publish(self: *SourcePlanBuilder, cache: *FileCache, key: SourcePlanKey) Error!void {
        const events = try self.events.toOwnedSlice(cache.gpa);
        errdefer cache.gpa.free(events);
        const entry = try cache.effect_source_plans.getOrPut(cache.gpa, key);
        if (entry.found_existing) {
            cache.gpa.free(events);
            return;
        }
        entry.value_ptr.* = .{ .events = events, .formal_uses = self.formal_uses };
        self.formal_uses = .empty;
    }
};

/// Marks a walk with no open global key reached.
const no_hit = std.math.maxInt(u32);

/// One global reachability walk. Visit order numbers the global demands; a
/// demand that reaches an open one (a back or cross edge) cannot be complete
/// until that component closes, and it closes when the first-visited member
/// finishes. Every member's answer is then the union that member folded.
const Walk = struct {
    const Visit = struct {
        index: u32,
        /// Its component has closed, so its answer is final.
        closed: bool = false,
    };
    const Open = struct { key: Key, index: u32 };
    const Partial = struct { set: []const Witness, low: u32 };

    visits: std.HashMapUnmanaged(Key, Visit, KeyContext, 80) = .empty,
    /// Visited keys whose component has not closed, in visit order.
    open: std.ArrayListUnmanaged(Open) = .empty,
    /// Rooted answers computed while an open key was unfinished. They are
    /// reused only while that key stays open, and never filed in `sets`.
    partial: std.HashMapUnmanaged(Key, Partial, KeyContext, 80) = .empty,
    next_index: u32 = 0,
    /// The lowest open visit index the answer being computed depends on.
    low: u32 = no_hit,

    fn deinit(self: *Walk, gpa: std.mem.Allocator) void {
        self.visits.deinit(gpa);
        self.open.deinit(gpa);
        self.partial.deinit(gpa);
    }

    fn isOpen(self: *const Walk, index: u32) bool {
        var low: usize = 0;
        var high: usize = self.open.items.len;
        while (low < high) {
            const middle = low + (high - low) / 2;
            const found = self.open.items[middle].index;
            if (found == index) return true;
            if (found < index) low = middle + 1 else high = middle;
        }
        return false;
    }
};

const Scoped = struct { set: []const Witness, epoch: u32 };

const Verdict = struct {
    whole: ?[]const Witness = null,
    cut: ?[]const Witness = null,
};

/// A scoped effect fold's memo, cycle set and allowance. Nested queries adopt
/// their caller's counter. An enclosing ownership fold may retain completed
/// witnesses and syntax indexes across queries until its own deferred deinit.
pub const State = struct {
    /// Interned dotted paths. A memo key and witness compare by id; their
    /// owned bytes live until this scoped state is deinitialized.
    paths: std.StringHashMapUnmanaged(u32) = .empty,
    path_text: std.ArrayListUnmanaged([]const u8) = .empty,
    /// Completed witness sets, one per declaration, question and identity.
    sets: std.HashMapUnmanaged(Key, []const Witness, KeyContext, 80) = .empty,
    /// Completed negative read-only verdicts, never complete witness sets.
    /// Rooted cuts retain only an own-formal witness, so neither the caller's
    /// actual storage nor its advisory-discharge chain shapes their reuse.
    verdicts: std.HashMapUnmanaged(Key, Verdict, KeyContext, 80) = .empty,
    /// Count both verdict modes, even if they share one semantic key.
    verdict_count: usize = 0,
    /// Completed structural type proofs, bound to the original resolver and frame.
    address_free: fresh_storage.AddressFreeMemo = .{},
    /// The keys on the current stack. Rooted cycles remain unknown; global
    /// back edges are folded as graph reachability without filing partial sets.
    active: std.HashMapUnmanaged(Key, u32, KeyContext, 80) = .empty,
    /// Answers that depend on which keys were on the stack when they were
    /// computed: a rooted back edge to a key above them made them unknown. A
    /// fresh walk from another entry would not meet that edge, so they are
    /// reused only inside the scope that computed them, never filed in `sets`.
    scoped: std.HashMapUnmanaged(Key, Scoped, KeyContext, 80) = .empty,
    /// Root demands whose standalone walk exhausted its whole allowance.
    exhausted: std.HashMapUnmanaged(ExhaustedKey, Exhausted, ExhaustedKeyContext, 80) = .empty,
    /// The shallowest stack depth a rooted back edge of the answer being
    /// computed reached, or `no_hit`.
    floor: u32 = no_hit,
    /// Names the scope `scoped` entries belong to. A scope is one root query,
    /// or one ownership fold that spans several.
    epoch: u32 = 0,
    scopes: u32 = 0,
    /// A global reachability walk visits each semantic demand once and folds
    /// strongly connected components of global demands as a unit.
    global_walk: ?*Walk = null,
    memo: ?std.heap.ArenaAllocator = null,
    scratch: ?std.heap.ArenaAllocator = null,
    /// The ORIGINAL resolver of this root, threaded through every document a
    /// query opens.  A contextual frame is built from it, never from a
    /// foreign document's own resolver.
    resolver: ?*TypeResolver = null,
    queries: u32 = 0,
    depth: u32 = 0,
    steps_left: u32 = 0,
    /// The enclosing query's counter when one was handed in; this state
    /// charges that one directly instead of starting a second allowance.
    remaining: ?*u32 = null,
    entry_tree: ?*const Ast = null,
    entry_token: Ast.TokenIndex = 0,

    pub fn deinit(self: *State, gpa: std.mem.Allocator) void {
        self.paths.deinit(gpa);
        self.path_text.deinit(gpa);
        self.sets.deinit(gpa);
        self.verdicts.deinit(gpa);
        self.address_free.deinit(gpa);
        self.active.deinit(gpa);
        self.scoped.deinit(gpa);
        self.exhausted.deinit(gpa);
        if (self.memo) |*arena| arena.deinit();
        self.memo = null;
        if (self.scratch) |*arena| arena.deinit();
        self.scratch = null;
    }

    /// File a completed answer: reusable by every later question when it is
    /// independent of the stack it was computed on, else for this scope only.
    /// Filing is optional; false reports a refused table growth.
    fn file(self: *State, gpa: std.mem.Allocator, key: Key, set: []const Witness, independent: bool) bool {
        if (independent) {
            self.sets.put(gpa, key, set) catch return false;
        } else {
            self.scoped.put(gpa, key, .{ .set = set, .epoch = self.epoch }) catch return false;
        }
        return true;
    }

    fn verdict(self: *const State, key: Key, mode: Mode) ?[]const Witness {
        const known = self.verdicts.get(key) orelse return null;
        return switch (mode) {
            .complete => null,
            .whole => known.whole,
            .cut => known.cut,
        };
    }

    fn fileVerdict(self: *State, gpa: std.mem.Allocator, key: Key, mode: Mode, set: []const Witness) Error!void {
        const frozen = try (try self.memoAllocator(gpa)).dupe(Witness, set);
        const result = try self.verdicts.getOrPut(gpa, key);
        if (!result.found_existing) result.value_ptr.* = .{};
        switch (mode) {
            .complete => unreachable,
            .whole => {
                if (result.value_ptr.whole == null) self.verdict_count += 1;
                result.value_ptr.whole = frozen;
            },
            .cut => {
                if (result.value_ptr.cut == null) self.verdict_count += 1;
                result.value_ptr.cut = frozen;
            },
        }
    }

    fn begin(
        self: *State,
        gpa: std.mem.Allocator,
        tree: *const Ast,
        token: Ast.TokenIndex,
        resolver: ?*TypeResolver,
        context: QueryContext,
    ) void {
        if (self.queries == 0) {
            if (self.scopes == 0) self.epoch +%= 1;
            self.floor = no_hit;
            self.steps_left = actual_query_work_limit;
            self.remaining = context.remaining;
            self.entry_tree = tree;
            self.entry_token = token;
            self.resolver = resolver;
            self.scratch = std.heap.ArenaAllocator.init(gpa);
        }
        self.queries += 1;
    }

    fn end(self: *State) void {
        self.queries -= 1;
        if (self.queries == 0) {
            self.steps_left = 0;
            self.remaining = null;
            self.entry_tree = null;
            self.resolver = null;
            self.scratch.?.deinit();
            self.scratch = null;
        }
    }

    /// The counter this query spends: the enclosing query's own when one was
    /// handed in, and this root's own counter otherwise.  Both are mutable
    /// because both are spent in place — nothing copies an allowance and no
    /// recursive edge starts a fresh one.
    fn counter(self: *State) *u32 {
        return self.remaining orelse &self.steps_left;
    }

    fn charge(self: *State) Error!void {
        const budget = self.counter();
        if (budget.* == 0) return self.failure(.readonly_call_nodes, actual_query_work_limit, actual_query_work_limit);
        budget.* -= 1;
    }

    fn failure(self: *State, limit: budget_mod.Limit, cap: u32, reached: u32) Error {
        return self.report(limit, cap, reached);
    }

    /// Record the labelled budget failure at the position of this root
    /// query's own entry.
    fn report(self: *State, limit: budget_mod.Limit, cap: u32, reached: u32) Error {
        const tree = self.entry_tree.?;
        const byte = tree.tokenStart(self.entry_token);
        const position = budget_mod.lineCol(tree.source, byte);
        var name: budget_mod.NameBuf = .{};
        if (tokens.enclosingFnDecl(tree, self.entry_token)) |declaration| {
            var buffer: [1]Ast.Node.Index = undefined;
            if (tokens.fnProto(tree, &buffer, declaration)) |proto| {
                if (proto.name_token) |token| name.set(tree.tokenSlice(token));
            }
        }
        return budget_mod.fail(.{
            .limit = limit,
            .limit_value = cap,
            .reached = reached,
            .byte = byte,
            .document = budget_mod.documentForTree(tree),
            .line = position.line,
            .column = position.column,
            .function = name,
        });
    }

    /// File one dotted path under a stable id.  The bytes are owned by the
    /// persistent memo arena — never by the caller's frame, never by the
    /// per-query scratch — and BOTH containers are grown before either is
    /// written, so a failure at any point publishes nothing and leaves the
    /// table exactly as it was for the next attempt.
    fn intern(self: *State, gpa: std.mem.Allocator, path: []const u8) Error!u32 {
        if (self.paths.get(path)) |existing| return existing;
        if (self.path_text.items.len > std.math.maxInt(u32))
            return self.failure(.readonly_call_nodes, std.math.maxInt(u32), std.math.maxInt(u32));
        const owned = try (try self.memoAllocator(gpa)).dupe(u8, path);
        try self.path_text.ensureUnusedCapacity(gpa, 1);
        try self.paths.ensureUnusedCapacity(gpa, 1);
        const id: u32 = @intCast(self.path_text.items.len);
        self.path_text.appendAssumeCapacity(owned);
        self.paths.putAssumeCapacity(owned, id);
        return id;
    }

    fn text(self: *const State, id: u32) []const u8 {
        return self.path_text.items[id];
    }

    fn scratchAllocator(self: *State) std.mem.Allocator {
        return self.scratch.?.allocator();
    }

    fn memoAllocator(self: *State, gpa: std.mem.Allocator) error{OutOfMemory}!std.mem.Allocator {
        if (self.memo == null) self.memo = std.heap.ArenaAllocator.init(gpa);
        return self.memo.?.allocator();
    }
};

/// The root cache's persistent effect state. A document opened for a demand
/// query borrows the root's grow state, which names that root.
fn rootState(cache: *FileCache) *State {
    const root = if (cache.grow_state) |grow| grow.owner else cache;
    return &root.effects_state;
}

/// How many completed effect answers the file's root state holds.  A walk
/// that leaves this unchanged filed nothing a repeat of it could reuse.
pub fn filedAnswerCount(cache: *FileCache) usize {
    const state = rootState(cache);
    return state.sets.count() + state.scoped.count() + state.verdict_count;
}

/// An ownership fold that asks several root questions shares one scope of
/// stack-dependent answers.
pub fn openScope(cache: *FileCache) void {
    const state = rootState(cache);
    if (state.scopes == 0) state.epoch +%= 1;
    state.scopes += 1;
}

pub fn closeScope(cache: *FileCache) void {
    rootState(cache).scopes -= 1;
}

fn cacheFor(cache: *FileCache, callee: FileCache.ActualCallee) Error!?*FileCache {
    if (callee.tree == cache.tree and callee.handle.module == cache.module_id) return cache;
    const resolver = if (callee.caller_frame) |frame| frame.resolver else cache.zls orelse return null;
    const document = try grow_analysis.sourceDocument(cache, callee.handle, resolver.ctx);
    return &document.cache;
}

/// The contextual view a call is read in.  A root call has no frame and
/// reads this document's own resolver; an instantiated one carries the frame
/// its CALLER resolved it in, which is not the frame its body is read in.
const View = union(enum) {
    resolver: *TypeResolver,
    frame: TypeResolver.ResolutionFrame,

    fn callArgumentsOf(
        self: View,
        buffer: *[2]Ast.Node.Index,
        node: Ast.Node.Index,
    ) !?TypeResolver.CallArguments {
        return switch (self) {
            .resolver => |r| try r.callArgumentsOf(buffer, node),
            .frame => |f| try f.callArgumentsOf(buffer, node),
        };
    }

    fn callArgumentIn(
        self: View,
        buffer: *[2]Ast.Node.Index,
        node: Ast.Node.Index,
        parameter: usize,
    ) !?Ast.Node.Index {
        return switch (self) {
            .resolver => |r| try r.callArgumentIn(buffer, node, parameter),
            .frame => |f| try f.callArgumentIn(buffer, node, parameter),
        };
    }

    fn stdCollectionAppendOf(self: View, callee: Ast.Node.Index, arguments: usize) !TypeResolver.StdCollectionAppend {
        return switch (self) {
            .resolver => |r| try r.stdCollectionAppendOf(callee, arguments),
            .frame => |f| try f.stdCollectionAppendOf(callee, arguments),
        };
    }

    fn isBoolType(self: View, node: Ast.Node.Index) !?bool {
        return switch (self) {
            .resolver => |r| try r.isBoolType(node),
            .frame => |f| try f.isBoolType(node),
        };
    }

    fn isEnumType(self: View, node: Ast.Node.Index) !?bool {
        return switch (self) {
            .resolver => |r| try r.isEnumType(node),
            .frame => |f| try f.isEnumType(node),
        };
    }
    fn isStdAllocator(self: View, node: Ast.Node.Index) !?bool {
        return switch (self) {
            .resolver => |r| try r.isStdAllocator(node),
            .frame => |f| try f.isStdAllocator(node),
        };
    }

    fn intInfo(self: View, node: Ast.Node.Index) !?TypeResolver.IntInfo {
        return switch (self) {
            .resolver => |r| try r.intInfo(node),
            .frame => |f| try f.intInfo(node),
        };
    }

    fn floatBits(self: View, node: Ast.Node.Index) !?u16 {
        return switch (self) {
            .resolver => |r| try r.floatBits(node),
            .frame => |f| try f.floatBits(node),
        };
    }

    /// The ORIGINAL resolver behind this view.  A frame borrows the resolver
    /// it was built from, so a type question asked through it is asked of the
    /// same analyser state the body is being read in — never of a foreign
    /// document's own resolver.
    fn resolverOf(self: View) *TypeResolver {
        return switch (self) {
            .resolver => |r| r,
            .frame => |f| f.resolver,
        };
    }

    fn typeOfNode(self: View, node: Ast.Node.Index) !?TypeResolver.ActualType {
        return switch (self) {
            .resolver => |r| try r.resolutionFrame().typeOfNode(node),
            .frame => |f| try f.typeOfNode(node),
        };
    }
};

/// The frame a call SITE's arguments are read in.
fn viewFor(cache: *FileCache, callee: FileCache.ActualCallee) ?View {
    if (callee.caller_frame) |frame| return .{ .frame = frame };
    const resolver = cache.zls orelse return null;
    return .{ .resolver = resolver };
}

/// The view a CALLEE'S BODY is read in: the original resolver, carrying the
/// complete instantiated identity of that callable.  Built from the root's
/// resolver even when the body lives in another document, so a contextual
/// answer never borrows a foreign document's own resolution state.
fn bodyView(cache: *FileCache, callee: FileCache.ActualCallee, state: *const State) ?View {
    const resolver = state.resolver orelse cache.zls orelse return null;
    return .{ .frame = resolver.frameForFunction(callee.reference) };
}

fn frameOf(view: ?View) ?TypeResolver.ResolutionFrame {
    return switch (view orelse return null) {
        .resolver => null,
        .frame => |f| f,
    };
}

/// The identity a memo entry is filed under: the complete instantiated
/// callable this body was reached as, not the container it happens to live
/// in.  Two instantiations of one generic declaration are two entries.
fn contextOf(view: ?View) ?TypeResolver.ActualTypeID {
    return switch (view orelse return null) {
        .resolver => null,
        .frame => |f| f.actual_type,
    };
}

/// Identity resolution is exactly actualCalleeOf. A known declaration without
/// a readable body remains a record with no summary and no purity credit.
pub fn actualCallSummaryAt(
    cache: *FileCache,
    token: Ast.TokenIndex,
    frame: ?TypeResolver.ResolutionFrame,
) Error!?ActualCallSummary {
    const callee = (try grow_analysis.actualCalleeOf(cache, token, frame)) orelse return null;
    var result: ActualCallSummary = .{
        .callee = callee,
        .summary = null,
        .argument_offset = null,
        .read_only = null,
    };
    const view = viewFor(cache, callee) orelse return result;
    var buffer: [2]Ast.Node.Index = undefined;
    const arguments = try view.callArgumentsOf(&buffer, callee.call_node);
    if (arguments) |actual| result.argument_offset = @intFromBool(actual.receiver != null);
    // A bodyless declaration is still a canonical record: the identity and the
    // summary are read, and nothing about its effects is inferred from the
    // absence of a body.
    if (tokens.bodyOf(callee.tree, callee.declaration) == null) return result;
    result.summary = try cache.summaryOfResolvedDeclaration(callee);
    return result;
}

/// What the CALL at `token` does to the storage `selection` names.
///
/// `context` carries the caller's own contextual view and, when this query
/// runs inside another one, that query's counter: the whole recursive walk
/// then spends one allowance.  A root call passes `.{}`.
pub fn callEffectAt(
    cache: *FileCache,
    token: Ast.TokenIndex,
    selection: EffectSelection,
    context: QueryContext,
) Error!?Effect {
    const callee = switch (selection) {
        .whole => |resolved| resolved orelse
            (try grow_analysis.actualCalleeOf(cache, token, context.frame)) orelse return null,
        else => (try grow_analysis.actualCalleeOf(cache, token, context.frame)) orelse return null,
    };
    if (selection == .whole and selection.whole != null) {
        const index = try cache.getCallIndex();
        if (index.by_callee_token.get(token) != callee.call_node) return .unknown;
        if (callee.tree != &callee.handle.document.tree) return .unknown;
        const reference = callee.reference;
        if (reference.tree != callee.tree or reference.fn_token != callee.fn_token or
            !reference.handle.eql(callee.handle)) return .unknown;
        const function = switch (reference.actual_type.data) {
            .function => |function| function,
            else => return .unknown,
        };
        if (!function.handle.eql(callee.handle) or function.fn_token != callee.fn_token)
            return .unknown;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(callee.tree, &proto_buffer, callee.declaration) orelse
            return .unknown;
        if (proto.ast.fn_token != callee.fn_token) return .unknown;
        if (formalCount(callee.tree, proto) != function.parameters.len) return .unknown;
        if (callee.caller_frame) |caller| {
            const supplied = context.frame orelse return .unknown;
            if (&caller.handle.document.tree != cache.tree) return .unknown;
            if (caller.resolver != supplied.resolver or !caller.handle.eql(supplied.handle))
                return .unknown;
            if ((caller.actual_type == null) != (supplied.actual_type == null)) return .unknown;
            if (caller.actual_type) |actual|
                if (!actual.eql(supplied.actual_type.?)) return .unknown;
            if ((caller.container_type == null) != (supplied.container_type == null))
                return .unknown;
            if (caller.container_type) |container|
                if (!container.eql(supplied.container_type.?)) return .unknown;
        } else if (context.frame != null) return .unknown;
    }
    const declaring = (try cacheFor(cache, callee)) orelse return .unknown;
    const view = viewFor(cache, callee) orelse return .unknown;
    // A root question reuses the file's completed answers; an enclosing
    // query lends its own State, and a root State already mid-query belongs
    // to that query, so an unrelated nested question gets a private one.
    const shared: ?*State = context.effects_state orelse blk: {
        const root = rootState(cache);
        break :blk if (root.queries == 0) root else null;
    };
    var state_slot: State = .{};
    const state = shared orelse &state_slot;
    defer if (shared == null) state_slot.deinit(cache.gpa);
    state.begin(cache.gpa, cache.tree, token, if (context.frame) |frame| frame.resolver else cache.zls, context);
    defer state.end();
    var call_buffer: [2]Ast.Node.Index = undefined;
    const call = TypeResolver.CallOperands.full(cache.tree, &call_buffer, callee.call_node) orelse return .unknown;
    var argument_buffer: [2]Ast.Node.Index = undefined;
    const arguments = (try view.callArgumentsOf(&argument_buffer, callee.call_node)) orelse
        return .unknown;
    const count = arguments.arguments.len + @intFromBool(arguments.receiver != null);
    const callee_view = bodyView(declaring, callee, state) orelse return .unknown;
    if (selection == .whole) {
        const function = switch (callee.reference.actual_type.data) {
            .function => |function| function,
            else => return .unknown,
        };
        if (count != function.parameters.len) return .unknown;
    }
    if (try allocatorFreeBuffer(cache, callee, view, callee_view, arguments, state)) |released| {
        if (try emptyBuffer(cache, released, state, 0)) return .read_only;
        switch (selection) {
            .parameter => |selected| if (selected.param == 1 and selected.path.len == 0) return .may_invalidate,
            .unrooted => {},
            .whole => return .may_invalidate,
        }
    }
    switch (selection) {
        .whole => {
            // The existing all-formals question owns every formal and every
            // unrooted witness. No physical actual storage needs projection.
            const set = try collectWitnesses(
                declaring,
                callee.declaration,
                any_param,
                "",
                callee_view,
                state,
                .whole,
            );
            return mergeAll(set);
        },
        .unrooted => {
            // Storage no formal of this callee names cannot be projected onto
            // a caller's own storage: the caller's argument nodes and the
            // callee's own storage live in different documents, so the fold
            // is read where it was computed.
            const set = try witnessesFor(declaring, callee.declaration, global_only, "", callee_view, state);
            return mergeAll(set);
        },
        .parameter => |selected| {
            if (selected.param >= count) return .unknown;
            try state.charge();
            if (selected.param == 0 and count != 0) {
                const append = try view.stdCollectionAppendOf(call.ast.fn_expr, count - 1);
                // Existing SDK identity/arity query distinguishes this
                // append's new-slot/length stores from writes poisoning
                // existing elements.
                switch (append) {
                    .infallible => return .writes_without_invalidation,
                    .fallible => return .may_invalidate,
                    .no => {},
                }
            }
            const mode: Mode = if (selected.read_only_only and selected.path.len == 0) .{
                .cut = .{ .advisory_ok = try selectedActualKeepsAdvisory(view, callee, selected.param, state) },
            } else .complete;
            const set = try collectWitnesses(
                declaring,
                callee.declaration,
                selected.param,
                selected.path,
                callee_view,
                state,
                mode,
            );
            const projected = try project(cache, state, callee, selected, set, context.declaration);
            return projected;
        },
    }
}

/// Combine two witnesses about the SAME storage.
///
/// `.may_invalidate` is a DEFINITE claim that this storage can be released,
/// and it outranks `.unknown` here: a body that demonstrably frees the buffer
/// it was handed and also reaches something it cannot read has still answered
/// the question the caller can act on, and both answers are unsafe.  A
/// call-site alias proof removes witnesses BEFORE this runs, so a discharged
/// witness never reaches the merge.
///
/// `.unknown` outranks a mere write.  An unresolved or unrooted reach is
/// never turned into a quiet verdict by a rooted store found elsewhere in the
/// same body, and an unknown on its own stays unknown.
fn merge(left: Effect, right: Effect) Effect {
    if (left == .may_invalidate or right == .may_invalidate) return .may_invalidate;
    if (left == .unknown or right == .unknown) return .unknown;
    if (left == .writes_without_invalidation or right == .writes_without_invalidation)
        return .writes_without_invalidation;
    return .read_only;
}

fn mergeAll(set: []const Witness) Effect {
    var effect: Effect = .read_only;
    for (set) |witness| effect = merge(effect, witness.effect);
    return effect;
}

/// The asked storage's own verdict, beside what OTHER origins say about
/// themselves.
///
/// A COMPLETED positive invalidation about the storage that was asked about is
/// the answer.  What another origin says is advisory: it is never promoted
/// into a verdict of its own, but it can raise a quiet answer, and an
/// unresolved one keeps the answer unresolved.
fn combineSelected(own: Effect, advisory: Effect) Effect {
    if (own == .may_invalidate) return .may_invalidate;
    if (own == .unknown or advisory == .unknown) return .unknown;
    if (own == .writes_without_invalidation) return .writes_without_invalidation;
    if (advisory == .may_invalidate) return .may_invalidate;
    if (advisory == .writes_without_invalidation) return .writes_without_invalidation;
    return .read_only;
}

/// The answer for storage rooted at `parameter` from one declaration's
/// witnesses: the witnesses this body filed against that formal, together
/// with the storage it reached without naming any formal at all.  A witness
/// against ANOTHER formal is not counted here — whether the caller made those
/// two the same storage is a fact about the call site, and `project` is where
/// that question is asked.
fn mergeRooted(set: []const Witness, parameter: u32) Effect {
    var own: Effect = .read_only;
    var advisory: Effect = .read_only;
    for (set) |witness| {
        if (witness.param == parameter) {
            own = merge(own, witness.effect);
        } else if (witness.param == unrooted_param) {
            advisory = merge(advisory, witness.effect);
        }
    }
    return combineSelected(own, advisory);
}

/// Project one declaration's witnesses onto the storage the CALLER handed
/// this call.
///
/// A witness rooted at the asked formal IS that storage and is kept as it
/// stands.  A witness naming another formal is mapped to the actual argument
/// that formal received, and the caller's own storage decides whether the two
/// can be the same storage.  A witness no formal names stays: storage a body
/// reached without a formal may be anything the caller holds, and no
/// call-site answer can discharge it.
fn project(
    cache: *FileCache,
    state: *State,
    callee: FileCache.ActualCallee,
    selection: ParameterSelection,
    set: []const Witness,
    caller_declaration: ?Ast.Node.Index,
) Error!Effect {
    const view = viewFor(cache, callee) orelse return mergeAll(set);
    var own: Effect = .read_only;
    var advisory: Effect = .read_only;
    var selected_buffer: [2]Ast.Node.Index = undefined;
    var selected: Ast.Node.Index = undefined;
    var have_selected = false;
    var selected_value: ?bool = null;
    for (set) |witness| {
        if (witness.param != selection.param and selection.path.len == 0) {
            if (selected_value == null) {
                selected_value = false;
                if (try view.callArgumentIn(
                    &selected_buffer,
                    callee.call_node,
                    selection.param,
                )) |argument| {
                    selected = argument;
                    have_selected = true;
                    selected_value = try valueAddressFree(view, argument, state);
                }
            }
            if (selected_value.?) continue;
        }
        if (witness.param == selection.param) {
            own = merge(own, witness.effect);
            continue;
        }
        if (witness.param == unrooted_param or witness.param >= global_only) {
            // What the callee reached without a formal of its own stays
            // advisory: no call-site answer here can place it.
            advisory = merge(advisory, witness.effect);
            continue;
        }
        try state.charge();
        var other_buffer: [2]Ast.Node.Index = undefined;
        const other = (try view.callArgumentIn(&other_buffer, callee.call_node, witness.param)) orelse {
            advisory = merge(advisory, witness.effect);
            continue;
        };
        if (!have_selected) {
            selected = (try view.callArgumentIn(
                &selected_buffer,
                callee.call_node,
                selection.param,
            )) orelse {
                advisory = merge(advisory, witness.effect);
                continue;
            };
            have_selected = true;
        }
        try state.charge();
        const shares = try storage_alias.mayShareStorageAt(cache, callee.call_node, .{
            .node = other,
            .path = state.text(witness.path),
        }, .{
            .node = selected,
            .path = selection.path,
        }, .reachable_storage, .{
            // Both selections are written in the caller's own snapshot, so
            // the frame is the one the CALL was reached in, and the counter
            // is this query's own.
            .frame = callee.caller_frame,
            .remaining = state.counter(),
            .declaration = caller_declaration,
            .effects_state = state,
        });
        if (shares) advisory = merge(advisory, witness.effect);
    }
    return combineSelected(own, advisory);
}

/// Every completed witness about the storage rooted at (parameter, path) in
/// `declaration`, in that body's OWN coordinates: a witness naming another
/// formal of the same body names that formal, and a witness naming storage no
/// formal owns stays unrooted.
fn witnessesFor(
    cache: *FileCache,
    declaration: Ast.Node.Index,
    parameter: u32,
    path: []const u8,
    view: ?View,
    state: *State,
) Error![]const Witness {
    return collectWitnesses(cache, declaration, parameter, path, view, state, .complete);
}

/// How much of a demand's answer the asker needs.
const Mode = union(enum) {
    /// Every witness, filed for reuse.
    complete,
    /// A whole certificate needs only one surviving negative witness to fail.
    whole,
    /// The asker needs only `.read_only` versus anything else about this
    /// formal's whole storage. The first witness that must survive into the
    /// final answer ends the walk. Its prefix is never filed as a complete
    /// witness set; an independent own-formal verdict can be reused.
    cut: Cut,

    const Cut = struct {
        /// The frame whose demand this is, when it asks about the very
        /// storage that frame was asked about.
        parent: ?*Frame = null,
        /// A root question only: the caller's selected actual is not an
        /// address-free value, so witnesses about other storage survive.
        advisory_ok: bool = false,
    };
};

/// Does the selected actual hand the callee storage other witnesses may
/// reach? `project` drops witnesses about other storage when it is an
/// address-free value.
fn selectedActualKeepsAdvisory(view: View, callee: FileCache.ActualCallee, parameter: u32, state: *State) Error!bool {
    var buffer: [2]Ast.Node.Index = undefined;
    const argument = (try view.callArgumentIn(&buffer, callee.call_node, parameter)) orelse return true;
    return !try valueAddressFree(view, argument, state);
}

/// One witness demand.  A demand that begins a walk on an empty stack, in a
/// query that owns its allowance, and whose identical walk already ran that
/// whole allowance out, fails again at once instead of repeating the walk.
///
/// A failure is recorded only when nothing outside the key could have shaped
/// it: the stack is empty (no active key, no open global walk, no frame
/// above), the allowance is this query's own and not a consumer's borrowed
/// one, no fresh-storage walk of the declaring file is open, the walk ended
/// because the counter reached zero, and the walk filed no completed answer
/// of its own (a repeat would otherwise be cheaper than the walk it
/// replaces).  The recorded fact is the key, the walk mode and the allowance
/// it started with; a completed answer is looked up first and is never
/// replaced by it, and a walk that completes removes it.
fn collectWitnesses(
    cache: *FileCache,
    declaration: Ast.Node.Index,
    parameter: u32,
    path: []const u8,
    view: ?View,
    state: *State,
    mode: Mode,
) Error![]const Witness {
    const demand_mode = demandMode(mode) orelse
        return collectWitnessesWalk(cache, declaration, parameter, path, view, state, mode);
    if (state.queries != 1 or state.depth != 0 or state.global_walk != null or
        state.remaining != null or cache.fresh_visiting.count() != 0)
        return collectWitnessesWalk(cache, declaration, parameter, path, view, state, mode);
    const gpa = cache.gpa;
    if (state.path_text.items.len == 0) _ = try state.intern(gpa, "");
    const demand: ExhaustedKey = .{
        .key = .{
            .declaration = .{ .tree = cache.tree, .module = cache.module_id, .declaration = declaration },
            .parameter = parameter,
            .path = try state.intern(gpa, path),
            .context = contextOf(view),
        },
        .mode = demand_mode,
    };
    // A completed answer is never shadowed by a recorded failure.
    if (state.sets.contains(demand.key) or state.verdict(demand.key, mode) != null)
        return collectWitnessesWalk(cache, declaration, parameter, path, view, state, mode);
    if (state.scoped.get(demand.key)) |scoped| {
        if (scoped.epoch == state.epoch)
            return collectWitnessesWalk(cache, declaration, parameter, path, view, state, mode);
    }
    const allowance = state.counter().*;
    if (state.exhausted.get(demand)) |known| {
        if (allowance <= known.budget) {
            // Exactly what the exhausted walk left behind: no allowance.
            state.counter().* = 0;
            return budget_mod.fail(known.diagnostic);
        }
    }
    const filed = state.sets.count() + state.scoped.count() + state.verdict_count;
    const guard = PendingGuard.begin();
    const result = collectWitnessesWalk(cache, declaration, parameter, path, view, state, mode);
    const own = guard.end();
    if (result) |set| {
        _ = state.exhausted.remove(demand);
        return set;
    } else |err| {
        if (err == error.AnalysisBudgetExceeded and state.counter().* == 0 and
            state.sets.count() + state.scoped.count() + state.verdict_count == filed)
        {
            if (own) |first| state.exhausted.put(gpa, demand, .{
                .budget = allowance,
                .diagnostic = first,
            }) catch {};
        }
        return err;
    }
}

fn collectWitnessesWalk(
    cache: *FileCache,
    declaration: Ast.Node.Index,
    parameter: u32,
    path: []const u8,
    view: ?View,
    state: *State,
    mode: Mode,
) Error![]const Witness {
    const gpa = cache.gpa;
    if (state.path_text.items.len == 0) _ = try state.intern(gpa, "");
    const key: Key = .{
        .declaration = .{ .tree = cache.tree, .module = cache.module_id, .declaration = declaration },
        .parameter = parameter,
        .path = try state.intern(gpa, path),
        .context = contextOf(view),
    };
    try state.charge();
    if (state.sets.get(key)) |set| {
        return set;
    }
    // An independently completed all-storage proof has no witness to
    // project or discharge. It answers every narrower demand of this exact
    // callable, but a negative verdict or a stack-dependent set cannot.
    if (parameter != any_param or key.path != root_path) {
        var whole_key = key;
        whole_key.parameter = any_param;
        whole_key.path = root_path;
        if (state.sets.get(whole_key)) |whole| {
            if (whole.len == 0) return whole;
        }
    }
    if (state.scoped.get(key)) |scoped| {
        if (scoped.epoch == state.epoch) {
            state.floor = 0;
            return scoped.set;
        }
    }
    if (state.verdict(key, mode)) |set| return set;
    var walk_storage: Walk = .{};
    const global_root = parameter == global_only and state.global_walk == null;
    if (global_root) state.global_walk = &walk_storage;
    defer if (global_root) {
        state.global_walk = null;
        walk_storage.deinit(gpa);
    };
    const walk = state.global_walk;
    if (walk) |w| {
        if (parameter != global_only) {
            if (w.partial.get(key)) |partial| {
                if (w.isOpen(partial.low)) {
                    w.low = @min(w.low, partial.low);
                    return partial.set;
                }
                // What it lacked has been completed and filed since.
                _ = w.partial.remove(key);
            }
        } else if (w.visits.get(key)) |visit| {
            // This edge's events already contribute to the enclosing root, or
            // its completed answer could not be filed. Neither is a full
            // answer for the frames above, so they stay unfiled.
            w.low = @min(w.low, if (visit.closed) 0 else visit.index);
            return &.{};
        }
    }
    if (state.active.get(key)) |depth| {
        if (parameter != global_only) {
            // Whether this key is on the stack is a fact about the stack, so
            // every answer that met it and sits above it is not final.
            state.floor = @min(state.floor, depth);
            return unknown_set;
        }
        if (walk) |w| w.low = 0;
        return &.{};
    }
    if (state.depth == max_depth) return @as(Error![]const Witness, state.failure(.readonly_call_depth, max_depth, state.depth));
    var buffer: [1]Ast.Node.Index = undefined;
    // A body this document cannot read — an extern declaration, or a
    // prototype the closed scanner cannot decode — is a canonical record and
    // no effect at all.
    const proto = tokens.fnProto(cache.tree, &buffer, declaration) orelse {
        return unknown_set;
    };
    const body = tokens.bodyOf(cache.tree, declaration) orelse {
        return unknown_set;
    };
    const formals = formalCount(cache.tree, proto);
    if (parameter < global_only and parameter >= formals) {
        return unknown_set;
    }
    try state.charge();
    var index: u32 = 0;
    var stack_position: usize = 0;
    var saved_low: u32 = no_hit;
    if (walk) |w| {
        saved_low = w.low;
        w.low = no_hit;
        if (parameter == global_only) {
            index = w.next_index;
            w.next_index += 1;
            stack_position = w.open.items.len;
            try w.visits.put(gpa, key, .{ .index = index });
            try w.open.append(gpa, .{ .key = key, .index = index });
        }
    }
    const my_depth = state.depth;
    const saved_floor = state.floor;
    state.floor = no_hit;
    try state.active.put(gpa, key, my_depth);
    state.depth += 1;
    defer {
        state.depth -= 1;
        _ = state.active.remove(key);
    }
    // The bindings are SEEDED once here and read by body key afterwards.
    // A reentrant fold of another body can grow that table, so a pointer
    // taken before the scan would dangle before the scan ends; the entries'
    // own items are arena-backed and never move.
    _ = try cache.localBindings(proto, body);
    var frame: Frame = .{
        .cache = cache,
        .declaration = declaration,
        .body = body,
        .proto = proto,
        .parameter = parameter,
        .path_text = state.text(key.path),
        .queried_name = if (parameter < global_only) formalNameToken(cache.tree, proto, parameter) else null,
        .view = view,
        .state = state,
        .whole_certificate = mode == .whole,
        .cut_mode = switch (mode) {
            .cut => |cut| cut,
            else => null,
        },
    };
    defer frame.raw_keys.deinit(gpa);
    var scan = call_effects.Scan.init(cache.tree, declaration, frame.currentBindings());
    const source_key: SourcePlanKey = .{ .declaration = key.declaration, .context = key.context };
    // Reentrant calls may grow the map. Its owned event/use buffers remain
    // stable, so borrow the completed plan by value rather than getPtr.
    const source_plan = cache.effect_source_plans.get(source_key);
    if (source_plan) |plan| {
        // Selection is consumed only after EOF. Collecting every formal on
        // the cold walk also supports a first global-only question.
        if (frame.queried_name) |formal| frame.selected = plan.formal_uses.get(formal);
    }
    var source_builder: SourcePlanBuilder = .{};
    defer source_builder.deinit(gpa);
    var source_cursor: usize = 0;
    var raw: std.ArrayListUnmanaged(Raw) = .empty;
    defer raw.deinit(gpa);
    while (true) {
        const event = if (source_plan) |plan| replay: {
            if (source_cursor == plan.events.len) break;
            const next = plan.events[source_cursor];
            source_cursor += 1;
            break :replay next;
        } else scan_next: {
            // Resolving a callee can grow the bindings table.
            scan.bindings = frame.currentBindings();
            break :scan_next (try scan.next()) orelse break;
        };
        try state.charge();
        if (source_plan == null) switch (event) {
            .node => |node| try source_builder.note(&frame, node),
            else => try source_builder.append(gpa, event),
        };
        switch (event) {
            .node => |node| {
                frame.note(node);
                scan.pending_children = try knownChildren(&frame, node);
            },
            .call => |node| try callWitness(&frame, &raw, node),
            .write => |w| try writeWitness(&frame, &raw, w.node, w.target, w.value),
            .write_or_unknown => |node| try opaqueWitness(&frame, &raw, node),
        }
        // A prefix is never a complete witness set or syntax source plan.
        // It can, however, finish a read-only-versus-unsafe question. Reuse
        // only stack-independent evidence; a rooted verdict must name its
        // own formal, not an advisory witness kept by this caller's chain.
        if (frame.whole_negative) {
            const negative = try frame.negativeSet();
            const independent = state.floor == no_hit and
                (if (walk) |w| w.low == no_hit else true);
            const reusable = mode == .whole or
                (if (frame.cut) |cut| parameter == global_only or cut.param == parameter else false);
            if (independent and reusable) try state.fileVerdict(gpa, key, mode, negative);
            if (walk) |w| w.low = @min(saved_low, w.low);
            state.floor = @min(saved_floor, state.floor);
            return negative;
        }
    }
    var list: std.ArrayListUnmanaged(Witness) = .empty;
    // `defer`, not `errdefer`: the success path below releases the list too,
    // once its contents have been copied into the memo arena.
    defer list.deinit(gpa);
    const selected_value = raw.items.len != 0 and try frame.selectionAddressFree();
    for (raw.items) |entry| {
        // A by-value address-free graph cannot alias externally reached
        // storage. Own witnesses still describe stores into that value.
        if (selected_value and entry.param != parameter) continue;
        if (entry.operand) |operand| {
            if (try frame.discharged(entry.at.?, operand, state.text(entry.operand_path))) continue;
        }
        try list.append(gpa, .{ .param = entry.param, .path = entry.path, .effect = entry.effect });
    }
    // The completed set is COPIED into the memo arena and the working list is
    // released here.  `toOwnedSlice` cannot perform this handover, because it
    // hands the memory it already owns to a second allocator by asking that
    // allocator to `remap` it — and the arena never allocated it.  A query
    // whose only interned path is the empty one leaves the arena with no node
    // at all, so that `remap` dereferences a null node and aborts the walk.
    // Copying into the arena is the same ownership move done correctly: these
    // bytes then live exactly as long as the memo that files them.
    const frozen = try (try state.memoAllocator(gpa)).dupe(Witness, list.items);
    if (source_plan == null) try source_builder.publish(cache, source_key);
    // The owned answer is already complete. Filing it is optional: a refused
    // table growth loses only a reuse opportunity, not its arena-owned bytes.
    // Source reads and all allocations needed to build the set still use try.
    const independent = state.floor >= my_depth;
    state.floor = @min(saved_floor, state.floor);
    if (walk) |w| {
        const sub_low = w.low;
        if (parameter == global_only) {
            if (sub_low >= index) {
                // This key is the first visited of its component: every open
                // key above it reaches it and is reached by it, so the union
                // this frame folded is each member's own reachability answer.
                for (w.open.items[stack_position..]) |member| {
                    const visit = w.visits.getPtr(member.key).?;
                    visit.closed = true;
                    if (!state.file(gpa, member.key, frozen, independent)) continue;
                }
                w.open.shrinkRetainingCapacity(stack_position);
                w.low = saved_low;
            } else {
                w.low = @min(saved_low, sub_low);
            }
        } else if (sub_low == no_hit) {
            _ = state.file(gpa, key, frozen, independent);
            w.low = saved_low;
        } else {
            // Valid for this walk only: it is missing what an open key will
            // contribute, and that key's component is not complete yet.
            w.partial.put(gpa, key, .{ .set = frozen, .low = sub_low }) catch {};
            w.low = @min(saved_low, sub_low);
        }
    } else {
        _ = state.file(gpa, key, frozen, independent);
    }
    return frozen;
}

/// A body with no readable evidence and a rooted recursive storage question
/// remain unknown. Global cycles are handled separately as reachability over
/// known bodies, with every unresolved edge still retaining its witness.
const unknown_set: []const Witness = &[_]Witness{.{
    .param = unrooted_param,
    .path = root_path,
    .effect = .unknown,
}};

/// One body being scanned for one question about it.
const Frame = struct {
    cache: *FileCache,
    declaration: Ast.Node.Index,
    body: Ast.Node.Index,
    proto: Ast.full.FnProto,
    /// The formal being asked about, or `any_param` / `global_only`.
    parameter: u32,
    path_text: []const u8,
    /// Name token of the asked formal, when the question names exactly one.
    queried_name: ?Ast.TokenIndex,
    /// A node in this body that names the asked formal.  Found by the scan
    /// itself, so asking costs no extra walk.
    selected: ?Ast.Node.Index = null,
    view: ?View,
    state: *State,
    raw_keys: std.AutoHashMapUnmanaged(Raw, void) = .empty,
    whole_certificate: bool = false,
    cut_mode: ?Mode.Cut = null,
    advisory_memo: ?bool = null,
    first_use: ?Ast.Node.Index = null,
    first_use_searched: bool = false,
    whole_negative: bool = false,
    cut: ?Witness = null,
    /// Expression recursion is scoped to this actual body, context and
    /// storage question. A back edge is unknown, not a completed memo answer.
    origin_active: ?*const OriginVisit = null,
    origin_cycles: u32 = 0,
    origin_memo: std.AutoHashMapUnmanaged(OriginKey, Origin) = .empty,

    /// Reuse only a fully constructed syntax index. No origin/effect answer,
    /// failed walk, or question-specific token-range verdict is cached here.
    fn hasRebinding(self: *Frame, name: []const u8, declaration: Ast.TokenIndex, after: Ast.TokenIndex, before: Ast.TokenIndex, unresolved_is_write: bool) Error!bool {
        const body_key = @intFromEnum(self.body);
        var index = self.cache.effect_binding_writes.get(body_key);
        if (index == null) {
            var built: BindingWriteIndex = .{};
            defer built.deinit(self.cache.gpa);
            const escapes = try self.cache.escapeRoots(self.body);
            for (escapes.writes) |write| {
                try self.state.charge();
                if (write.declares) continue;
                const binding = self.currentBindings().findAt(write.name, write.token);
                const name_token: ?Ast.TokenIndex = if (binding) |assigned| assigned.name_token else null;
                const entry = try built.writes.getOrPut(self.cache.gpa, write.name);
                if (!entry.found_existing) entry.value_ptr.* = .empty;
                try entry.value_ptr.append(self.cache.gpa, .{ .token = write.token, .declaration = name_token });
            }
            const entry = try self.cache.effect_binding_writes.getOrPut(self.cache.gpa, body_key);
            if (!entry.found_existing) {
                entry.value_ptr.* = built;
                built = .{};
            }
            // Borrow by value: later body resolution can grow the cache map.
            index = entry.value_ptr.*;
        }
        const writes = index.?.writes.get(name) orelse return false;
        for (writes.items) |write| {
            try self.state.charge();
            if (write.token <= after or write.token >= before) continue;
            if (write.declaration) |assigned| {
                if (assigned == declaration) return true;
            } else if (unresolved_is_write) return true;
        }
        return false;
    }

    /// This body's bindings, taken from the cache by body key.  Reacquired at
    /// every read rather than carried in the frame, because resolving another
    /// declaration can grow the table this one was read from.
    fn currentBindings(self: *const Frame) *const LocalBindings {
        return self.cache.bindings.getPtr(@intFromEnum(self.body)).?;
    }

    /// Remember a node in this body that really names the asked formal.
    ///
    /// A USE and the formal's own declaration are different tokens, so token
    /// identity alone can never match them.  What says a position names that
    /// formal is the binding table: the binding a use resolves to carries the
    /// name token of the declaration it came from, and only the asked
    /// formal's own binding has that one.  A local shadowing the name has its
    /// own declaration token and is not it.
    fn note(self: *Frame, node: Ast.Node.Index) void {
        if (self.selected != null) return;
        const formal = self.queried_name orelse return;
        const tree = self.cache.tree;
        if (tree.nodeTag(node) != .identifier) return;
        const token = tree.nodeMainToken(node);
        if (token == formal) {
            self.selected = node;
            return;
        }
        const binding = self.currentBindings().findAt(tree.tokenSlice(token), token) orelse return;
        if (binding.origin == .param and binding.name_token == formal) self.selected = node;
    }

    fn selectionAddressFree(self: *Frame) Error!bool {
        if (self.parameter >= global_only or self.path_text.len != 0) return false;
        const view = self.view orelse return false;
        if (self.selected) |selected| return valueAddressFree(view, selected, self.state);
        var parameters = self.proto.iterate(self.cache.tree);
        var index: u32 = 0;
        while (parameters.next()) |parameter| : (index += 1) {
            if (index != self.parameter) continue;
            const type_node = parameter.type_expr orelse return false;
            return valueAddressFree(view, type_node, self.state);
        }
        return false;
    }

    /// Does this body PROVE that the storage `operand` names is not the asked
    /// one?  Only a positively proved private construction answers that; the
    /// same storage, an incoming field, a copied header, publication, an
    /// unsupported shape and a cycle all answer "may share".
    fn discharged(self: *Frame, at: Ast.Node.Index, operand: Ast.Node.Index, suffix: []const u8) Error!bool {
        if (self.parameter >= global_only) return false;
        const selected = self.selected orelse return false;
        try self.state.charge();
        // The alias query derives the operand's own chain. A nested call's
        // witness adds only its callee-relative suffix, never that chain twice.
        const shares = try storage_alias.mayShareStorageAt(self.cache, at, .{
            .node = operand,
            .path = suffix,
        }, .{
            .node = selected,
            .path = self.path_text,
        }, .reachable_storage, .{
            // The frame the operands are written in, and this query's own
            // counter: one allowance covers the whole recursive walk, and no
            // edge starts a fresh one.
            .frame = frameOf(self.view),
            .remaining = self.state.counter(),
            .declaration = self.declaration,
            .effects_state = self.state,
        });
        return !shares;
    }

    fn append(self: *Frame, raw: *std.ArrayListUnmanaged(Raw), entry: Raw) Error!void {
        if (self.raw_keys.contains(entry)) return;
        try self.state.charge();
        try self.raw_keys.put(self.cache.gpa, entry, {});
        try raw.append(self.cache.gpa, entry);
        if (self.whole_certificate and entry.effect != .read_only)
            self.whole_negative = true;
        if (self.cut_mode != null and entry.effect != .read_only and !self.whole_negative) {
            // The verdict is only `.read_only` versus anything else, so the
            // first witness that must survive into the final answer decides
            // it. A global frame filters nothing; an own, undischargeable
            // witness always survives; an advisory one survives while no
            // frame on the way to the root drops it.
            const decisive = if (self.parameter >= global_only)
                true
            else if (entry.operand != null)
                false
            else if (entry.param == self.parameter)
                true
            else if (entry.param == unrooted_param)
                try self.advisoryKept()
            else
                false;
            if (decisive) {
                self.whole_negative = true;
                self.cut = .{ .param = entry.param, .path = entry.path, .effect = entry.effect };
            }
        }
    }

    /// Does every frame between this one and the root keep witnesses that
    /// are not about its own formal? A frame whose formal is an address-free
    /// value drops them, and so does a root whose actual is one. The formal's
    /// type is read from a use of it, as the final filter reads it; a formal
    /// the body never uses is not decided here and is not kept.
    fn advisoryKept(self: *Frame) Error!bool {
        if (self.advisory_memo) |kept| return kept;
        const cut_mode = self.cut_mode orelse return false;
        if (self.parameter >= global_only) return true;
        var kept = if (cut_mode.parent) |parent| try parent.advisoryKept() else cut_mode.advisory_ok;
        if (kept) {
            if (self.view) |view| {
                if (try self.firstFormalUse()) |use| {
                    kept = !try valueAddressFree(view, use, self.state);
                } else kept = false;
            }
        }
        self.advisory_memo = kept;
        return kept;
    }

    /// A node of this body that names the asked formal: the scan's own pick
    /// when it has one, else the first such identifier in source order. Every
    /// use of one binding has the binding's type.
    fn firstFormalUse(self: *Frame) Error!?Ast.Node.Index {
        if (self.selected) |node| return node;
        if (self.first_use_searched) return self.first_use;
        self.first_use_searched = true;
        const formal = self.queried_name orelse return null;
        const tree = self.cache.tree;
        var index: u32 = @intFromEnum(self.proto.ast.proto_node) + 1;
        const last: u32 = @intFromEnum(self.body);
        while (index <= last) : (index += 1) {
            try self.state.charge();
            const node: Ast.Node.Index = @enumFromInt(index);
            if (tree.nodeTag(node) != .identifier) continue;
            const token = tree.nodeMainToken(node);
            const binding = self.currentBindings().findAt(tree.tokenSlice(token), token) orelse continue;
            if (binding.origin == .param and binding.name_token == formal) {
                self.first_use = node;
                return node;
            }
        }
        return null;
    }

    /// What a stopped frame returns. A whole certificate has no verdict
    /// witness; a verdict stop returns the one witness that decided it.
    /// Neither is a complete witness set. Independent verdicts have their
    /// own memo and are never used by a precise effect question.
    fn negativeSet(self: *const Frame) Error![]const Witness {
        const decided = self.cut orelse return unknown_set;
        const set = try self.state.scratchAllocator().alloc(Witness, 1);
        set[0] = .{ .param = decided.param, .path = decided.path, .effect = decided.effect };
        return set;
    }

    fn joinPath(self: *Frame, parent: []const u8, child: []const u8) Error!u32 {
        const joined = if (parent.len == 0)
            child
        else if (child.len == 0)
            parent
        else
            try std.mem.concat(self.state.scratchAllocator(), u8, &.{ parent, ".", child });
        return self.state.intern(self.cache.gpa, joined);
    }

    /// Record one piece of storage this body was shown to touch, in this
    /// body's own coordinates.  `severity` is what the operation does to that
    /// storage and `suffix` the path from the operation's own base to it; the
    /// question of whether it is the asked storage is answered here.
    fn charge(
        self: *Frame,
        raw: *std.ArrayListUnmanaged(Raw),
        origin: Origin,
        suffix: []const u8,
        severity: Effect,
        operand: Ast.Node.Index,
        at: Ast.Node.Index,
    ) Error!void {
        var verdict = self.meet(origin);
        if (verdict == .none) return;
        const owner = switch (origin) {
            .formal => |formal| formal,
            .unrooted, .private_value, .private_storage => null,
        };
        const param: u32 = if (owner) |formal| formal.param else unrooted_param;
        const base: []const u8 = if (owner) |formal| formal.path else "";
        const path = try self.joinPath(base, suffix);
        // When the origin and query share a root but the actual
        // operation path diverges, the witness is about a sibling
        // storage cell, not the queried one. Divergent paths are
        // treated as distinct rather than conservatively merged.
        const path_text = self.state.text(path);
        if (verdict == .own and self.state.path_text.items.len != 0 and path_text.len != 0) {
            if (!pathContains(self.path_text, path_text) and !pathContains(path_text, self.path_text)) {
                verdict = .other;
            }
        }
        try self.append(raw, .{
            .param = param,
            .path = path,
            .effect = severity,
            .operand = if (verdict == .own) null else operand,
            .operand_path = if (verdict == .own) root_path else try self.state.intern(self.cache.gpa, suffix),
            .at = if (verdict == .own) null else at,
        });
    }

    /// Record a witness about storage this body handed a callee under a
    /// DIFFERENT formal than the asked one.  Storage that is not one of this
    /// body's own formals has no coordinate here — it is storage this body
    /// built or reached — so it is charged unrooted rather than dropped: a
    /// caller's own argument can be exactly that storage, and no caller
    /// answer may discharge a witness it cannot place.
    fn chargeForeign(
        self: *Frame,
        raw: *std.ArrayListUnmanaged(Raw),
        origin: Origin,
        suffix: []const u8,
        severity: Effect,
        operand: Ast.Node.Index,
        at: Ast.Node.Index,
    ) Error!void {
        if (try mutableLocalAddressFree(self, operand)) return;
        switch (origin) {
            .formal => try self.charge(raw, origin, suffix, severity, operand, at),
            // A local's own storage is a place the callee writes, and at a
            // call site the caller's own argument may be exactly it — so it
            // is charged with the operand the storage proof reads.  A value
            // with no storage at all is the callee's own business.
            .unrooted, .private_storage => try self.append(raw, .{
                .param = unrooted_param,
                .path = root_path,
                .effect = severity,
                .operand = operand,
                .operand_path = try self.state.intern(self.cache.gpa, suffix),
                .at = at,
            }),
            .private_value => {},
        }
    }

    fn meet(self: *const Frame, origin: Origin) Meet {
        switch (origin) {
            .private_value, .private_storage => return .none,
            .unrooted => return if (self.parameter >= global_only) .own else .other,
            .formal => |owner| {
                if (self.parameter == any_param) return .own;
                if (self.parameter == global_only) return .none;
                if (owner.param != self.parameter) return .other;
                // One path naming the other is that storage itself.  Two
                // paths that only share a root are NOT two proofs of separate
                // storage: `a.b` and `a.c` can name the same buffer, so the
                // pair needs this body's own storage proof, not a spelling
                // comparison.  Only a positively proved private construction
                // takes one out of the question.
                if (pathContains(owner.path, self.path_text) or
                    pathContains(self.path_text, owner.path)) return .own;
                return .other;
            },
        }
    }
};

/// How one piece of storage meets the storage being asked about: the same
/// storage (`own`), storage this body reached that the question does not name
/// (`other`), or neither (`none`).
const Meet = enum { none, own, other };

/// Where one expression's storage comes from, in the coordinates of the body
/// that spells it.
const Origin = union(enum) {
    /// Storage this body was handed: a formal and a path from its root.
    formal: fn_summary.ParamPath,
    /// Storage this body reached that no formal of it names: a file-level
    /// variable, a capture of a call result, an index, a call result.  It may
    /// be anything the caller holds, and only a positively proved private
    /// construction takes it out of the question.
    unrooted,
    /// A LOCAL's own storage: a stack hasher, a scratch buffer, a header this
    /// body built.  No formal of this body owns it and the body was not handed
    /// it — but it is still a place a call writes, and at a call site the
    /// caller's own argument may be exactly this storage, so it is charged
    /// there as unrooted and decided by the storage proof rather than by the
    /// pointer spelling.
    private_storage,
    /// A value with no storage behind it that anyone handed over.
    private_value,
};

fn combineOrigins(left: Origin, right: Origin) Origin {
    return switch (left) {
        .private_value => right,
        .private_storage => switch (right) {
            .private_value, .private_storage => left,
            // A local's own storage carries nothing the caller handed over, so
            // what the other side names is what this expression still holds.
            .formal => right,
            .unrooted => .unrooted,
        },
        .formal => |owner| switch (right) {
            .private_value, .private_storage => left,
            .formal => |other| if (owner.param == other.param and
                std.mem.eql(u8, owner.path, other.path)) left else .unrooted,
            .unrooted => .unrooted,
        },
        .unrooted => switch (right) {
            .private_value => left,
            else => .unrooted,
        },
    };
}

fn valueAddressFree(view: View, node: Ast.Node.Index, state: *State) Error!bool {
    try state.charge();
    const ty = (try view.typeOfNode(node)) orelse return false;
    const resolution = frameOf(view) orelse view.resolverOf().resolutionFrame();
    return state.address_free.proves(state.scratch.?.child_allocator, resolution, ty, node, state.counter());
}

/// A mutable local with no reachable addresses is a new stack value, even
/// when its initializer copied scalar fields from a formal. Readonly objects
/// may share static storage; pointer-bearing locals may retain caller storage.
fn mutableLocalAddressFree(frame: *Frame, node: Ast.Node.Index) Error!bool {
    const view = frame.view orelse return false;
    const tree = frame.cache.tree;
    var value = node;
    for (0..max_depth) |_| {
        switch (tree.nodeTag(value)) {
            .address_of, .@"try" => value = tree.nodeData(value).node,
            .grouped_expression => value = tree.nodeData(value).node_and_token[0],
            else => break,
        }
    } else return false;
    const root = tokens.rootIdentifier(tree, value) orelse return false;
    const token = tree.nodeMainToken(root);
    const binding = frame.currentBindings().findAt(tree.tokenSlice(token), token) orelse return false;
    if (binding.is_const or binding.origin == .param or binding.origin == .loop_capture) return false;
    return valueAddressFree(view, root, frame.state);
}

/// A branch proof is about this instantiated frame, never a helper's name.
/// Its condition is still scanned: evaluating it may itself have effects.
fn knownChildren(frame: *Frame, node: Ast.Node.Index) Error!?Iterator {
    const tree = frame.cache.tree;
    const view = frame.view orelse return null;
    const resolution = frameOf(view) orelse view.resolverOf().resolutionFrame();
    if (tree.fullIf(node)) |branch| {
        if (branch.payload_token != null or branch.error_token != null) return null;
        try frame.state.charge();
        const condition = (try resolution.boolValueOfNode(branch.ast.cond_expr)) orelse
            return null;
        return .{ .array = .{
            branch.ast.cond_expr.toOptional(),
            if (condition) branch.ast.then_expr.toOptional() else branch.ast.else_expr,
            .none,
            .none,
            .none,
        } };
    }
    const branch = tree.fullSwitch(node) orelse return null;
    var two: [2]Ast.Node.Index = undefined;
    const condition = branch.ast.condition;
    switch (tree.nodeTag(condition)) {
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
        else => return null,
    }
    if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(condition)), "@typeInfo")) return null;
    const operands = builtinOperands(tree, condition, &two);
    if (operands.len != 1) return null;
    try frame.state.charge();
    const value = (try resolution.resolveValueOfNode(operands[0])) orelse return null;
    if (!value.is_type_val) return null;
    const ty = (try resolution.resolver.normalizedType(value)) orelse return null;
    const tag = resolution.resolver.typeTag(ty) orelse return null;
    var selected: ?Ast.Node.Index = null;
    var fallback: ?Ast.Node.Index = null;
    for (branch.ast.cases) |case_node| {
        try frame.state.charge();
        const case = tree.fullSwitchCase(case_node) orelse return null;
        if (case.ast.values.len == 0) {
            if (fallback != null) return null;
            fallback = case_node;
        }
        for (case.ast.values) |case_value| {
            try frame.state.charge();
            if (tree.nodeTag(case_value) != .enum_literal) return null;
            var name = tree.tokenSlice(tree.nodeMainToken(case_value));
            if (std.mem.startsWith(u8, name, "@\"") and std.mem.endsWith(u8, name, "\""))
                name = name[2 .. name.len - 1];
            if (!std.mem.eql(u8, name, @tagName(tag))) continue;
            if (selected != null) return null;
            selected = case_node;
        }
    }
    const chosen = selected orelse fallback orelse return null;
    return .{ .array = .{
        condition.toOptional(), chosen.toOptional(), .none, .none, .none,
    } };
}

const OriginVisit = struct {
    node: Ast.Node.Index,
    previous: ?*const OriginVisit,
};

/// The binding stores only the condition's span. Recover its while by the
/// capture token's AST identity, following only children that contain it.
fn enclosingWhileCapture(frame: *Frame, name_token: Ast.TokenIndex) Error!?Ast.Node.Index {
    const tree = frame.cache.tree;
    var node = frame.body;
    while (true) {
        try frame.state.charge();
        if (tree.fullWhile(node)) |loop| {
            if (loop.error_token == name_token) return node;
            if (loop.payload_token) |payload| {
                if (payload + @intFromBool(tree.tokenTag(payload) == .asterisk) == name_token)
                    return node;
            }
        }
        var children = Iterator.init(tree, node);
        var containing: ?Ast.Node.Index = null;
        while (children.next(tree)) |child| {
            try frame.state.charge();
            if (tree.firstToken(child) <= name_token and name_token <= tree.lastToken(child)) {
                containing = child;
                break;
            }
        }
        node = containing orelse return null;
    }
}

/// Captures project the value evaluated before entering their body. Their
/// binding names only the scrutinee; a while additionally needs its back edge.
fn captureOrigin(frame: *Frame, rhs: Ast.Node.Index, name_token: Ast.TokenIndex, depth: u32) Error!Origin {
    const tree = frame.cache.tree;
    if (tree.fullWhile(rhs) == null) {
        if (try enclosingWhileCapture(frame, name_token)) |loop_node|
            return captureOrigin(frame, loop_node, name_token, depth);
    }
    if (tree.fullWhile(rhs)) |loop| {
        if (loop.error_token == name_token) return .private_storage;
        if (loop.payload_token) |payload| {
            const captured = payload + @intFromBool(tree.tokenTag(payload) == .asterisk);
            if (captured == name_token) {
                // A cursor may be rebound on the back edge, including AFTER
                // this use of the capture. The initial value alone cannot
                // certify every iteration's storage.
                // Indexing writes may build tables, so bindings below are
                // always reacquired by body identity.
                // Inspect every referenced binding, not just a root name:
                // calls and projections can return a rebound argument.
                var token = tree.firstToken(loop.ast.cond_expr);
                while (token <= tree.lastToken(loop.ast.cond_expr)) : (token += 1) {
                    try frame.state.charge();
                    if (tree.tokenTag(token) != .identifier) continue;
                    const binding = frame.currentBindings().findAt(tree.tokenSlice(token), token) orelse continue;
                    if (try frame.hasRebinding(binding.name, binding.name_token, name_token, tree.lastToken(rhs) + 1, false))
                        return .unrooted;
                }
                return relate(frame, loop.ast.cond_expr, depth);
            }
        }
        return .unrooted;
    }
    if (tree.fullIf(rhs)) |branch| {
        if (branch.error_token == name_token) return .private_storage;
        if (branch.payload_token) |payload| {
            if (payload + @intFromBool(tree.tokenTag(payload) == .asterisk) == name_token)
                return relate(frame, branch.ast.cond_expr, depth);
        }
        return .unrooted;
    }
    if (tree.fullFor(rhs)) |loop| {
        var token = loop.payload_token;
        for (loop.ast.inputs) |input| {
            if (tree.tokenTag(token) == .asterisk) token += 1;
            if (token == name_token) {
                if (tree.nodeTag(input) == .for_range) return .private_storage;
                return relate(frame, input, depth);
            }
            token += 1;
            if (tree.tokenTag(token) != .comma) break;
            token += 1;
        }
        return .unrooted;
    }
    if (tree.fullSwitch(rhs)) |branch| {
        for (branch.ast.cases) |case_node| {
            try frame.state.charge();
            const case = tree.fullSwitchCase(case_node) orelse return .unrooted;
            if (case.payload_token) |payload| {
                const captured = payload + @intFromBool(tree.tokenTag(payload) == .asterisk);
                if (captured == name_token)
                    return relate(frame, branch.ast.condition, depth);
                // A second switch capture is the scalar active tag.
                if (tree.tokenTag(captured + 1) == .comma and captured + 2 == name_token)
                    return .private_storage;
            }
        }
        return .unrooted;
    }
    // Some binding entries already name the scrutinee or iterable rather
    // than its control-flow node. This expression is still at that horizon.
    // A case entry can name only the arm; recover its enclosing switch by
    // AST identity, never by a capture's spelling or a source excerpt.
    if (tree.fullSwitchCase(rhs) != null) {
        for (0..tree.nodes.len) |index| {
            try frame.state.charge();
            const candidate: Ast.Node.Index = @enumFromInt(index);
            const branch = tree.fullSwitch(candidate) orelse continue;
            for (branch.ast.cases) |case_node| {
                if (case_node == rhs) return captureOrigin(frame, candidate, name_token, depth);
            }
        }
        return .unrooted;
    }
    return relate(frame, rhs, depth);
}

/// Omitted defaults belong to the aggregate's declaring frame, not this
/// caller. Until their provenance is resolved there, retain an unknown root.
fn aggregateDefaultsOrigin(frame: *Frame, node: Ast.Node.Index, fields: []const Ast.Node.Index) Error!Origin {
    const view = frame.view orelse return .unrooted;
    try frame.state.charge();
    const resolver = view.resolverOf();
    const ty = (try view.typeOfNode(node)) orelse return .unrooted;
    const resolution = frameOf(view) orelse resolver.resolutionFrame();
    if (try fresh_storage.actualTypeAddressFree(resolution, ty, 0, frame.state.counter())) return .private_value;
    const actual = (try resolver.normalizedType(ty)) orelse return .unrooted;
    if (actual.data != .container) return .unrooted;
    const container = actual.data.container;
    const declaring = resolver.frameForContainer(container);
    const tree = &container.scope_handle.handle.document.tree;
    var buffer: [2]Ast.Node.Index = undefined;
    const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return .unrooted;
    for (declaration.ast.members) |member| {
        try frame.state.charge();
        const field = tree.fullContainerField(member) orelse continue;
        if (field.ast.value_expr == .none) continue;
        var supplied = false;
        for (fields) |value| {
            try frame.state.charge();
            const first = frame.cache.tree.firstToken(value);
            if (first < 3 or frame.cache.tree.tokenTag(first - 1) != .equal or
                frame.cache.tree.tokenTag(first - 2) != .identifier or
                frame.cache.tree.tokenTag(first - 3) != .period) continue;
            if (std.mem.eql(u8, frame.cache.tree.tokenSlice(first - 2), tree.tokenSlice(field.ast.main_token))) {
                supplied = true;
                break;
            }
        }
        if (!supplied) {
            const type_node = field.ast.type_expr.unwrap() orelse return .unrooted;
            const field_type = (try declaring.typeOfNode(type_node)) orelse return .unrooted;
            if (!try fresh_storage.actualTypeAddressFree(declaring, field_type, 0, frame.state.counter()))
                return .unrooted;
        }
    }
    return .private_value;
}

const OriginKey = struct { node: Ast.Node.Index, depth: u32 };

fn relate(frame: *Frame, node: Ast.Node.Index, depth: u32) Error!Origin {
    try frame.state.charge();
    var active = frame.origin_active;
    while (active) |visit| : (active = visit.previous) {
        try frame.state.charge();
        if (visit.node == node) {
            frame.origin_cycles += 1;
            return .unrooted;
        }
    }
    if (depth == max_depth) return @as(Error!Origin, frame.state.failure(.readonly_call_depth, max_depth, depth));
    const key: OriginKey = .{ .node = node, .depth = depth };
    if (frame.origin_memo.get(key)) |known| return known;
    const visit: OriginVisit = .{ .node = node, .previous = frame.origin_active };
    frame.origin_active = &visit;
    defer frame.origin_active = visit.previous;
    const cycles = frame.origin_cycles;
    const answer = try relateWalk(frame, node, depth);
    if (frame.origin_cycles == cycles)
        try frame.origin_memo.put(frame.state.scratchAllocator(), key, answer);
    return answer;
}

fn relateWalk(frame: *Frame, node: Ast.Node.Index, depth: u32) Error!Origin {
    const cache = frame.cache;
    const tree = cache.tree;
    var static_owner_complete = true;
    if (tokens.rootIdentifier(tree, node)) |root| {
        const token = tree.nodeMainToken(root);
        if (frame.currentBindings().findAt(tree.tokenSlice(token), token)) |binding| {
            // Static ownership follows the initial capture value. A loop's
            // back edge must be checked before accepting that coordinate.
            if (binding.origin == .loop_capture) static_owner_complete = false;
            if (binding.origin != .param) {
                // The binding pointer is not held across the escape index
                // build: resolving it can grow the table this one lives in.
                const name = binding.name;
                const name_token = binding.name_token;
                if (try frame.hasRebinding(name, name_token, name_token, token, true))
                    return .unrooted;
            }
        }
    }
    if (static_owner_complete) {
        const owner = try fn_summary.ownerOfExpr(frame.state.scratchAllocator(), tree, frame.proto, frame.currentBindings(), tree.firstToken(node), tree.lastToken(node), 0);
        switch (owner) {
            .param => |path| return .{ .formal = path },
            .unknown => {},
        }
    }
    switch (tree.nodeTag(node)) {
        .identifier => {
            const token = tree.nodeMainToken(node);
            const name = tree.tokenSlice(token);
            if (std.mem.eql(u8, name, "undefined") or std.mem.eql(u8, name, "null") or
                std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false")) return .private_value;
            const binding = frame.currentBindings().findAt(name, token) orelse return .unrooted;
            if (binding.origin == .param) return .unrooted;
            const rhs = cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse
                return .unrooted;
            if (rhs == node) return .unrooted;
            // Captures retain pointee relevance even when a by-value element
            // copied its header.  Their iterable is not an ownership proof.
            //
            // Following a name to a literal does not make the NAME valueless:
            // the local it names is still a place a call writes, so what came
            // back is this body's own storage, not a value.
            const followed = if (binding.origin == .loop_capture)
                try captureOrigin(frame, rhs, binding.name_token, depth + 1)
            else
                try relate(frame, rhs, depth + 1);
            return switch (followed) {
                .private_value => .private_storage,
                else => followed,
            };
        },
        .address_of => return relate(frame, tree.nodeData(node).node, depth + 1),
        .deref => return relate(frame, tree.nodeData(node).node, depth + 1),
        .@"try" => return relate(frame, tree.nodeData(node).node, depth + 1),
        .unwrap_optional => return relate(frame, tree.nodeData(node).node_and_token[0], depth + 1),
        .grouped_expression => return relate(frame, tree.nodeData(node).node_and_token[0], depth + 1),
        .array_access => return relate(frame, tree.nodeData(node).node_and_node[0], depth + 1),
        .field_access => return relate(frame, tree.nodeData(node).node_and_token[0], depth + 1),
        .slice_open, .slice, .slice_sentinel => {
            const slice = tree.fullSlice(node).?;
            return relate(frame, slice.ast.sliced, depth + 1);
        },
        .call, .call_one, .call_comma, .call_one_comma => return resultOrigin(frame, node, depth + 1),
        .number_literal, .char_literal, .string_literal, .multiline_string_literal, .enum_literal, .error_value => return .private_value,
        else => {
            // Type expressions do not carry runtime addresses, but omitted
            // defaults can. Spelled fields alone are not a completeness proof.
            var literal_buffer: [2]Ast.Node.Index = undefined;
            const structure = tree.fullStructInit(&literal_buffer, node);
            const values: ?[]const Ast.Node.Index = if (structure) |literal|
                literal.ast.fields
            else if (tree.fullArrayInit(&literal_buffer, node)) |literal|
                literal.ast.elements
            else
                null;
            if (values) |items| {
                // Named aggregate literals can omit defaults declared in a
                // different frame. Their spelled fields are not a complete
                // provenance proof. Address-free types need no such origins.
                var result: Origin = if (structure != null)
                    try aggregateDefaultsOrigin(frame, node, items)
                else
                    .private_value;
                if (result == .unrooted) return .unrooted;
                for (items) |item| {
                    result = combineOrigins(result, try relate(frame, item, depth + 1));
                    if (result == .unrooted) return .unrooted;
                }
                return result;
            }
            var children = Iterator.init(tree, node);
            var result: Origin = .private_value;
            var found = false;
            while (children.next(tree)) |child| {
                found = true;
                result = combineOrigins(result, try relate(frame, child, depth + 1));
                // Unknown is absorbing: another origin cannot make this
                // expression more precise, so do not traverse it again.
                if (result == .unrooted) return .unrooted;
            }
            return if (found) result else .unrooted;
        },
    }
}

/// What a call RESULT carries.  A result that may carry the asked storage is
/// a use of it, so a body that stores the result writes storage it was
/// handed; a result whose provenance this file cannot read carries
/// everything.
fn resultOrigin(frame: *Frame, node: Ast.Node.Index, depth: u32) Error!Origin {
    const cache = frame.cache;
    var buffer: [2]Ast.Node.Index = undefined;
    const call = TypeResolver.CallOperands.full(cache.tree, &buffer, node) orelse return .unrooted;
    const actual = (try cache.actualCallSummaryAt(
        call.queryToken(cache.tree, node),
        frameOf(frame.view),
    )) orelse return .unrooted;
    const callee = actual.callee;
    const summary = actual.summary orelse return .unrooted;
    // Returned arguments cannot close an incomplete result summary. Keep
    // unknown without expanding dependencies whose origins cannot change it.
    if (!summary.result_params_complete) return .unrooted;
    const view = viewFor(cache, callee) orelse return .unrooted;
    var arguments_buffer: [2]Ast.Node.Index = undefined;
    const arguments = (try view.callArgumentsOf(&arguments_buffer, node)) orelse return .unrooted;
    var result: Origin = .private_value;
    const count = arguments.arguments.len + @intFromBool(arguments.receiver != null);
    for (0..count) |index| {
        const dependency = summary.returnedParamDependency(@intCast(index));
        if (dependency == false) continue;
        const argument = (try actual.callArgumentFor(cache, &arguments_buffer, @intCast(index))) orelse
            return .unrooted;
        result = combineOrigins(result, try relate(frame, argument, depth));
        if (result == .unrooted) return .unrooted;
    }
    return result;
}

/// A store this body spells out.  Which storage it lands in and what it does
/// to that storage are two questions, and neither answers the other: an
/// ordinary cell store proves the address did not move, never that the value
/// stored is a defined one.
fn writeWitness(
    frame: *Frame,
    raw: *std.ArrayListUnmanaged(Raw),
    node: Ast.Node.Index,
    target: Ast.Node.Index,
    value: Ast.Node.Index,
) Error!void {
    const tree = frame.cache.tree;
    if (tree.nodeTag(target) == .identifier) {
        const token = tree.nodeMainToken(target);
        if (frame.currentBindings().findAt(tree.tokenSlice(token), token)) |binding| {
            // Rebinding a local replaces its own slot, not any storage its
            // old or new pointer value reaches. Indexed and dereferenced
            // destinations still take the rooted storage path below.
            if (binding.origin != .param) return;
        }
    }
    // Classify the physical destination before following initializer value
    // dependencies. An actual address-free mutable local owns every inline
    // cell in its graph, even when a factory computed those cells from an
    // incoming seed. Pointer/slice-bearing roots cannot pass this certificate.
    if (try mutableLocalAddressFree(frame, target)) return;
    const origin = try relate(frame, target, 0);
    var severity = try storeSeverity(frame, node, target, value);
    switch (origin) {
        .formal => |owner| if (pathIsAncestor(frame.path_text, owner.path)) {
            // The store replaces an object that CONTAINS the asked storage, so
            // whatever that storage was is gone.
            severity = .may_invalidate;
        },
        else => {},
    }
    try frame.charge(raw, origin, "", severity, target, node);
}

fn storeSeverity(frame: *Frame, node: Ast.Node.Index, target: Ast.Node.Index, value: Ast.Node.Index) Error!Effect {
    const tree = frame.cache.tree;
    switch (tree.nodeTag(node)) {
        // A shift can manufacture any bit pattern, which is poison wherever
        // the caller reads it back.
        .assign_shl, .assign_shl_sat, .assign_shr => return .may_invalidate,
        else => {},
    }
    if (isUndefinedValue(frame, value)) return .may_invalidate;
    switch (tree.nodeTag(target)) {
        // A store through a pointer writes whatever the pointer names, which
        // this body never proved to be storage the caller handed over.
        .deref => return .may_invalidate,
        .array_access => {
            // An indexed cell is a real destination only when its index is a
            // defined value; an undefined one is not a cell at all.
            if (isUndefinedValue(frame, tree.nodeData(target).node_and_node[1])) return .unknown;
        },
        else => {},
    }
    // What is left is an ordinary store into a cell this body can name, and
    // it takes BOTH halves of a proof to keep the caller's reference alive:
    // the DESTINATION must be a cell whose actual type is a known narrow
    // scalar, and the VALUE must be one this analysis cannot see poison in.
    // A composite destination is exactly what a header replaces, and an
    // unresolved one is exactly what this analysis must not guess about.
    if (!try isKnownScalarType(frame, target)) return .may_invalidate;
    if (!try valueIsNonPoisonScalar(frame, value)) return .may_invalidate;
    return .writes_without_invalidation;
}

/// Does the ACTUAL frame resolve this expression's own type to a narrow
/// primitive?
///
/// Asked through the view the expression is written in, so an instantiated
/// generic's parameter type is the type this call really carried and never a
/// bare generic form.  A pointer, slice, optional, struct, union, call result,
/// and anything the engine cannot answer are all refused.
/// Unresolved structure is refused; source, policy and resource failures
/// abort the query so no completed witness set can contain that refusal.
fn isKnownScalarType(frame: *Frame, node: Ast.Node.Index) Error!bool {
    const view = frame.view orelse return false;
    if (try view.isBoolType(node)) |is_bool| {
        if (is_bool) return true;
    }
    if (try view.isEnumType(node)) |is_enum| {
        if (is_enum) return true;
    }
    if (try view.intInfo(node)) |info| {
        return info.bits < @bitSizeOf(usize);
    }
    if (try view.floatBits(node)) |width| {
        return width < @bitSizeOf(usize);
    }
    return false;
}

/// What an intrinsic's bytes land IN: the actual ELEMENT of this
/// destination, read from the same type graph the body is resolved in.
///
/// A pointer or slice destination root is the NORMAL shape for a byte
/// intrinsic and proves nothing by itself, so it is peeled once — with one
/// bounded optional unwrap before it — and the ELEMENT is what is classified.
/// An element that resolves to a bool, an enum, an int or a float is a plain
/// cell; a struct, a union, a pointer, a slice, another aggregate, or an
/// element this run cannot resolve is refused.  Nothing here reads a
/// declaration spelling or names a container type.
/// Resolution failures propagate rather than becoming an element verdict.
fn elementIsScalarElement(frame: *Frame, node: Ast.Node.Index) Error!bool {
    const view = frame.view orelse return false;
    const resolver = view.resolverOf();
    var current = (try view.typeOfNode(node)) orelse return false;
    // One optional wrapper is peeled before the pointer/array the bytes are
    // actually written through; the bound stops a malformed cycle.
    var peeled: u8 = 0;
    while (peeled < 2) : (peeled += 1) {
        const tag = resolver.typeTag(current) orelse return false;
        if (tag != .optional) break;
        current = resolver.childType(current) orelse return false;
    }
    const tag = resolver.typeTag(current) orelse return false;
    const child = switch (tag) {
        .pointer => blk: {
            // Only a resolved pointer, slice or C pointer gets here; an
            // unresolved one is not a destination this run can describe.
            _ = resolver.pointerSize(current) orelse return false;
            break :blk resolver.childType(current);
        },
        .array, .vector => resolver.childType(current),
        else => return false,
    } orelse return false;
    // The child is a structural instance; normalize it before it is classified.
    const element = (try resolver.normalizedType(child)) orelse return false;
    return switch (resolver.typeTag(element) orelse return false) {
        .bool, .@"enum", .int, .comptime_int, .float, .comptime_float => true,
        else => false,
    };
}

/// Can this analysis prove the stored VALUE is defined and non-poison?
///
/// A literal is one — an enum literal included, because it is the TARGET's
/// scalar type that decides what it coerces into (`Row{ .bytes = undefined }`
/// spelled `.poisoned` is refused by the destination proof, not here).  A name
/// is one when its own type resolves to a narrow primitive.
fn valueIsNonPoisonScalar(frame: *Frame, node: Ast.Node.Index) Error!bool {
    const tree = frame.cache.tree;
    switch (tree.nodeTag(node)) {
        .number_literal, .char_literal, .enum_literal => return true,
        .identifier, .field_access => {},
        else => return false,
    }
    return isKnownScalarType(frame, node);
}

/// Syntax this scanner cannot read: a memory intrinsic, assembly, a
/// destructuring assign, a shape the closed scanner does not decode.  It is
/// charged at full strength unless every operand it names is provably not the
/// asked storage — never for its own sake, because "the base did not move"
/// says nothing about what the operation does to the cells it reaches.
fn opaqueWitness(frame: *Frame, raw: *std.ArrayListUnmanaged(Raw), node: Ast.Node.Index) Error!void {
    const tree = frame.cache.tree;
    var two: [2]Ast.Node.Index = undefined;
    const operands = builtinOperands(tree, node, &two);
    if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@call")) {
        try callWitness(frame, raw, node);
        return;
    }
    switch (intrinsicWrite(tree, node)) {
        // A load reads and writes nothing, so it charges nothing here.
        .reads_only => {},
        // `@memset` writes its FIRST operand with a value it also names, and
        // that value has to be a provable non-poison scalar: `@memset(dst, v)`
        // is only as safe as `v`.
        .first => try writeIntrinsic(frame, raw, node, operands, 0, 1),
        // `@memcpy`/`@memmove` write arbitrary bytes over the destination, so
        // whatever landed there may be a header this body cannot see.
        .bytes => try writeIntrinsic(frame, raw, node, operands, 0, null),
        // An atomic store, read-modify-write and compare-exchange all write
        // through a pointer at their SECOND operand, and whatever they store
        // replaces what was there.
        .second => try writeIntrinsic(frame, raw, node, operands, 1, null),
        .@"opaque" => {
            if (operands.len == 0) {
                try frame.charge(raw, .unrooted, "", .unknown, node, node);
                return;
            }
            var poison = false;
            for (operands, 0..) |operand, index| {
                if (index == 0) continue;
                if (isUndefinedValue(frame, operand)) poison = true;
            }
            for (operands) |operand| {
                try frame.charge(
                    raw,
                    try relate(frame, operand, 0),
                    "",
                    if (poison) .may_invalidate else .unknown,
                    operand,
                    node,
                );
                if (frame.whole_negative) return;
            }
        },
    }
}

/// One destination of a known memory intrinsic: the cells it writes and what
/// writing them means.  `stored_value` is the operand whose value lands in
/// those cells, or null when the bytes come from somewhere the call does not
/// name.  A destination no formal owns is unknown storage, so it keeps the
/// opaque strength however well the intrinsic is known.
fn writeIntrinsic(
    frame: *Frame,
    raw: *std.ArrayListUnmanaged(Raw),
    node: Ast.Node.Index,
    operands: []const Ast.Node.Index,
    index: usize,
    stored_value: ?usize,
) Error!void {
    if (index >= operands.len) {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    }
    const destination = operands[index];
    // What decides is the CONTENT that lands there and the CELL it lands in:
    // for `@memset` the value it also names, and the actual ELEMENT of the
    // destination read from the type graph.  The destination ROOT is a pointer
    // or a slice by construction here and proves nothing either way.  A
    // composite element is refused — those bytes can be a header.
    var severity: Effect = .may_invalidate;
    if (stored_value) |value_index| {
        if (value_index < operands.len and
            try valueIsNonPoisonScalar(frame, operands[value_index]) and
            try elementIsScalarElement(frame, destination)) severity = .writes_without_invalidation;
    }
    for (operands, 0..) |operand, at| {
        if (at == index) continue;
        // `undefined` among the operands poisons the destination outright.
        if (isUndefinedValue(frame, operand)) severity = .may_invalidate;
    }
    const origin = try relate(frame, destination, 0);
    try frame.charge(raw, origin, "", switch (origin) {
        .formal => severity,
        else => .unknown,
    }, destination, node);
}

/// Which operand a compiler intrinsic writes, by the shape the parser gives
/// it.  These are COMPILER intrinsics, where the name is the semantics: no SDK
/// method this producer folds is ever named here.
const IntrinsicWrite = enum { reads_only, first, bytes, second, @"opaque" };

fn intrinsicWrite(tree: *const Ast, node: Ast.Node.Index) IntrinsicWrite {
    const name = tree.tokenSlice(tree.nodeMainToken(node));
    const is = std.mem.eql;
    if (is(u8, name, "@This")) return .reads_only;
    if (is(u8, name, "@atomicLoad")) return .reads_only;
    if (is(u8, name, "@atomicRmw") or is(u8, name, "@atomicStore") or
        is(u8, name, "@cmpxchgWeak") or is(u8, name, "@cmpxchgStrong")) return .second;
    if (is(u8, name, "@memset")) return .first;
    if (is(u8, name, "@memcpy") or is(u8, name, "@memmove")) return .bytes;
    return .@"opaque";
}

/// The operands an intrinsic was written with, in the shape the parser gave
/// them.  An absent operand is `OptionalIndex.none`, which is not a node index
/// at all and is skipped rather than read into the node table.
fn builtinOperands(tree: *const Ast, node: Ast.Node.Index, two: *[2]Ast.Node.Index) []const Ast.Node.Index {
    const data = tree.nodeData(node);
    return switch (tree.nodeTag(node)) {
        // THREE or more parameters: every operand is in one extra range.
        .builtin_call, .builtin_call_comma => tree.extraDataSlice(data.extra_range, Ast.Node.Index),
        .builtin_call_two, .builtin_call_two_comma => blk: {
            var count: usize = 0;
            inline for (data.opt_node_and_opt_node) |maybe| {
                if (maybe.unwrap()) |operand| {
                    two[count] = operand;
                    count += 1;
                }
            }
            break :blk two[0..count];
        },
        else => &.{},
    };
}

/// Only this canonical SDK declaration and its actual signature establish
/// release semantics; a caller's method spelling is not evidence.
fn allocatorFreeBuffer(
    cache: *FileCache,
    callee: FileCache.ActualCallee,
    caller: View,
    body: ?View,
    arguments: TypeResolver.CallArguments,
    state: *State,
) Error!?Ast.Node.Index {
    const resolver = caller.resolverOf();
    try state.charge();
    if (!try resolver.declaredInToolchainFile(callee.handle, "/std/mem/Allocator.zig"))
        return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(callee.tree, &buffer, callee.declaration) orelse return null;
    const name = proto.name_token orelse return null;
    if (!std.mem.eql(u8, callee.tree.tokenSlice(name), "free")) return null;
    var parameters = proto.iterate(callee.tree);
    const allocator = parameters.next() orelse return null;
    const memory = parameters.next() orelse return null;
    if (parameters.next() != null) return null;
    const generic = memory.anytype_ellipsis3 orelse return null;
    if (callee.tree.tokenTag(generic) != .keyword_anytype) return null;
    const allocator_type = allocator.type_expr orelse return null;
    const released = argumentAt(arguments, 1) orelse return null;
    const return_node = proto.ast.return_type.unwrap() orelse return null;
    // The receiver and its erased callback are not evaluated on the SDK's
    // zero-byte path. An explicitly typed const slice and its literal
    // initializer prove that path without depending on generic value coercion.
    if (callee.tree.nodeTag(return_node) == .identifier and
        std.mem.eql(u8, callee.tree.tokenSlice(callee.tree.nodeMainToken(return_node)), "void") and
        try declaredEmptySlice(cache, released, state))
    {
        for (callee.tree.rootDecls()) |root| {
            try state.charge();
            if (root == callee.declaration) return released;
        }
    }
    const body_view = body orelse return null;
    if (try body_view.isStdAllocator(allocator_type) != true) return null;
    const return_type = (try body_view.typeOfNode(return_node)) orelse return null;
    if (resolver.typeTag(return_type) != .void) return null;
    const receiver = argumentAt(arguments, 0) orelse return null;
    if (try caller.isStdAllocator(receiver) != true) return null;
    const released_type = (try caller.typeOfNode(released)) orelse return null;
    if (resolver.pointerSize(released_type) != .slice) return null;
    return released;
}

/// A constant local may carry a statically empty slice. Mutable headers,
/// globals and unknown values cannot establish the zero-length no-op.
fn emptyBuffer(cache: *FileCache, node: Ast.Node.Index, state: *State, depth: u32) Error!bool {
    if (depth == max_depth) return false;
    try state.charge();
    const tree = cache.tree;
    switch (tree.nodeTag(node)) {
        .identifier => {
            const token = tree.nodeMainToken(node);
            const declaration = tokens.enclosingFnDecl(tree, token) orelse return false;
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
            const body = tokens.bodyOf(tree, declaration) orelse return false;
            const bindings = try cache.localBindings(proto, body);
            const binding = bindings.findAt(tree.tokenSlice(token), token) orelse return false;
            if (!binding.is_const or binding.origin == .param) return false;
            const initializer = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
            if (initializer == node) return false;
            return emptyBuffer(cache, initializer, state, depth + 1);
        },
        .address_of => {
            var buffer: [2]Ast.Node.Index = undefined;
            const value = tree.nodeData(node).node;
            const array_type = if (tree.fullArrayInit(&buffer, value)) |literal| blk: {
                if (literal.ast.elements.len != 0) return false;
                break :blk literal.ast.type_expr.unwrap() orelse return false;
            } else if (tree.fullStructInit(&buffer, value)) |literal| blk: {
                // The parser represents an empty typed initializer as a
                // struct initializer, even when its type is an array.
                if (literal.ast.fields.len != 0) return false;
                break :blk literal.ast.type_expr.unwrap() orelse return false;
            } else return false;
            // A sentinel is an extra byte even when the visible slice is
            // empty. Only a plain zero/inferred-length array proves the no-op.
            if (tree.nodeTag(array_type) != .array_type) return false;
            const count = tree.nodeData(array_type).node_and_node[0];
            return (tree.nodeTag(count) == .number_literal and
                std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(count)), "0")) or
                (tree.nodeTag(count) == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(count)), "_"));
        },
        .grouped_expression => return emptyBuffer(cache, tree.nodeData(node).node_and_token[0], state, depth + 1),
        else => return false,
    }
}

/// Prove a plain slice's zero length from its own declaration and initializer.
/// A type annotation is required: an inferred pointer-to-array is not the
/// slice that the canonical allocator API accepts. Sentinel slices may retain
/// a byte despite zero visible elements and are never discharged here.
fn declaredEmptySlice(cache: *FileCache, node: Ast.Node.Index, state: *State) Error!bool {
    try state.charge();
    const tree = cache.tree;
    if (tree.nodeTag(node) != .identifier) return false;
    const token = tree.nodeMainToken(node);
    const declaration = tokens.enclosingFnDecl(tree, token) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    const bindings = try cache.localBindings(proto, body);
    const binding = bindings.findAt(tree.tokenSlice(token), token) orelse return false;
    if (!binding.is_const or binding.origin == .param or binding.origin == .loop_capture) return false;
    if (tree.tokenTag(binding.name_token + 1) != .colon) return false;
    const first = binding.name_token + 2;
    if (binding.rhs_first < 2 or binding.rhs_first - 2 < first) return false;
    const type_node = cache.nodeForExactSpan(first, binding.rhs_first - 2) orelse return false;
    const slice = tree.fullPtrType(type_node) orelse return false;
    if (slice.size != .slice or slice.ast.sentinel != .none) return false;
    return emptyBuffer(cache, node, state, 0);
}

/// What one call does, in this body's coordinates.  Every operand the call was
/// handed is followed to the storage it names, and every witness the callee
/// produced is re-expressed here; storage a callee can reach without being
/// handed anything of ours is charged on its own.
fn callWitness(frame: *Frame, raw: *std.ArrayListUnmanaged(Raw), node: Ast.Node.Index) Error!void {
    const cache = frame.cache;
    var buffer: [2]Ast.Node.Index = undefined;
    const call = TypeResolver.CallOperands.full(cache.tree, &buffer, node) orelse {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    };
    const callee = (try grow_analysis.actualCalleeOf(cache, call.queryToken(cache.tree, node), frameOf(frame.view))) orelse {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    };
    if ((try cacheFor(cache, callee)) == null) {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    }
    const view = viewFor(cache, callee) orelse {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    };
    var arguments_buffer: [2]Ast.Node.Index = undefined;
    const arguments = (try view.callArgumentsOf(&arguments_buffer, node)) orelse {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    };
    try resolvedCallWitness(frame, raw, node, call.ast.fn_expr, callee, view, arguments);
}

fn resolvedCallWitness(
    frame: *Frame,
    raw: *std.ArrayListUnmanaged(Raw),
    node: Ast.Node.Index,
    fn_expr: Ast.Node.Index,
    callee: FileCache.ActualCallee,
    view: View,
    arguments: TypeResolver.CallArguments,
) Error!void {
    const cache = frame.cache;
    const declaring = (try cacheFor(cache, callee)) orelse unreachable;
    const count = arguments.arguments.len + @intFromBool(arguments.receiver != null);
    const callee_view = bodyView(declaring, callee, frame.state);
    if (try allocatorFreeBuffer(cache, callee, view, callee_view, arguments, frame.state)) |released| {
        // A proved empty slice executes neither poisoning nor the allocator
        // callback. Otherwise the release is a rooted fact even when the
        // allocator's erased vtable body cannot be resolved.
        if (try emptyBuffer(cache, released, frame.state, 0)) return;
        try frame.charge(raw, try relate(frame, released, 0), "", .may_invalidate, released, node);
        if (frame.whole_negative) return;
    }
    if (count != 0) {
        const append = try view.stdCollectionAppendOf(fn_expr, count - 1);
        if (append != .no) {
            const receiver = arguments.receiver orelse arguments.arguments[0];
            const severity: Effect = if (append == .infallible)
                .writes_without_invalidation
            else
                .may_invalidate;
            try frame.charge(raw, try relate(frame, receiver, 0), "", severity, receiver, node);
            return;
        }
    }
    if (frame.whole_certificate) {
        // Ask the same no-mutation question recursively, not a truncated
        // parameter effect. A positive answer covers every callee effect.
        const whole = try collectWitnesses(
            declaring,
            callee.declaration,
            any_param,
            "",
            callee_view,
            frame.state,
            .whole,
        );
        if (mergeAll(whole) == .read_only) return;
    }
    for (0..count) |index| {
        try frame.state.charge();
        const argument = argumentAt(arguments, @intCast(index)) orelse continue;
        if (try mutableLocalAddressFree(frame, argument)) continue;
        // Explicit address-free arguments are values copied into the callee.
        // An implicit receiver can instead be addressed by method coercion.
        if ((arguments.receiver == null or index != 0) and
            try valueAddressFree(view, argument, frame.state)) continue;
        const origin = try relate(frame, argument, 0);
        switch (origin) {
            .private_value => {
                // A value this body was handed holds no storage of the
                // caller's, so whatever the callee does to it is its own.
                continue;
            },
            .formal => if (frame.parameter == global_only) continue,
            else => {},
        }
        if (frame.whole_certificate) {
            // The child withheld its whole certificate and this actual may
            // expose storage relevant to our root. Withhold ours too, without
            // claiming which parameter was written or caching a partial body.
            if (frame.meet(origin) == .none) continue;
            try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
            return;
        }
        const sub = try collectWitnesses(
            declaring,
            callee.declaration,
            @intCast(index),
            "",
            callee_view,
            frame.state,
            // A callee's own witness about the storage this frame was asked
            // about is a verdict witness of this frame too, so one may stop
            // as soon as the callee finds it.
            if (frame.cut_mode != null and frame.meet(origin) == .own)
                .{ .cut = .{ .parent = frame } }
            else
                .complete,
        );
        try reexpress(frame, raw, origin, sub, arguments, node, @intCast(index));
        if (frame.whole_negative) return;
    }
    // A known callee can reach globally aliased storage without receiving any
    // relevant operand.  That possibility is asked separately: formal flow
    // never proves nonaliasing of caller storage, and an opaque callee cannot
    // discharge it.
    const globals = try collectWitnesses(
        declaring,
        callee.declaration,
        global_only,
        "",
        callee_view,
        frame.state,
        // Nothing a global frame folds is filtered, and an advisory witness
        // that survives every frame above decides the verdict by itself.
        if (frame.cut_mode != null and try frame.advisoryKept()) .{ .cut = .{} } else .complete,
    );
    for (globals) |witness| {
        try frame.append(raw, .{
            .param = unrooted_param,
            .path = root_path,
            .effect = witness.effect,
        });
        if (frame.whole_negative) return;
    }
}

/// Re-express one callee's witnesses in the coordinates of the body that made
/// the call.
///
/// A witness the callee filed against the formal this call was asked about
/// hangs under the storage this argument named.  A witness against ANOTHER of
/// the callee's formals is asked of the argument that formal actually
/// received, because that is where its storage now lives — so a callee that
/// writes its second parameter is charged to the caller's second argument and
/// not to the whole call.
fn reexpress(
    frame: *Frame,
    raw: *std.ArrayListUnmanaged(Raw),
    origin: Origin,
    sub: []const Witness,
    arguments: TypeResolver.CallArguments,
    at: Ast.Node.Index,
    asked: u32,
) Error!void {
    const state = frame.state;
    for (sub) |witness| {
        if (frame.whole_negative) return;
        try state.charge();
        if (witness.param == asked) {
            try frame.charge(raw, origin, state.text(witness.path), witness.effect, argumentAt(arguments, asked) orelse at, at);
            continue;
        }
        if (witness.param == unrooted_param or witness.param >= global_only) {
            // Storage the callee could not root is not spellable at this node,
            // so no body here can prove it apart.
            try frame.append(raw, .{
                .param = unrooted_param,
                .path = root_path,
                .effect = witness.effect,
            });
            continue;
        }
        const actual = argumentAt(arguments, witness.param) orelse {
            try frame.append(raw, .{
                .param = unrooted_param,
                .path = root_path,
                .effect = witness.effect,
            });
            continue;
        };
        try frame.chargeForeign(raw, try relate(frame, actual, 0), state.text(witness.path), witness.effect, actual, at);
    }
}

fn argumentAt(arguments: TypeResolver.CallArguments, formal: u32) ?Ast.Node.Index {
    const count = arguments.arguments.len + @intFromBool(arguments.receiver != null);
    if (formal >= count) return null;
    if (arguments.receiver != null and formal == 0) return arguments.receiver.?;
    return arguments.arguments[formal - @intFromBool(arguments.receiver != null)];
}

/// Is this expression the `undefined` value, directly or through the local
/// that was initialised with it?
fn isUndefinedValue(frame: *Frame, node: Ast.Node.Index) bool {
    const cache = frame.cache;
    const tree = cache.tree;
    switch (tree.nodeTag(node)) {
        .identifier => {
            const token = tree.nodeMainToken(node);
            const name = tree.tokenSlice(token);
            if (std.mem.eql(u8, name, "undefined")) return true;
            const binding = frame.currentBindings().findAt(name, token) orelse return false;
            if (binding.origin != .literal) return false;
            const rhs = cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse
                return false;
            return isUndefinedValue(frame, rhs);
        },
        .@"try", .address_of, .deref => return isUndefinedValue(frame, tree.nodeData(node).node),
        .grouped_expression, .unwrap_optional => return isUndefinedValue(frame, tree.nodeData(node).node_and_token[0]),
        else => return false,
    }
}

fn formalCount(tree: *const Ast, proto: Ast.full.FnProto) u32 {
    var parameters = proto.iterate(tree);
    var count: u32 = 0;
    while (parameters.next()) |_| count += 1;
    return count;
}

fn formalNameToken(tree: *const Ast, proto: Ast.full.FnProto, index: u32) ?Ast.TokenIndex {
    var parameters = proto.iterate(tree);
    var at: u32 = 0;
    while (parameters.next()) |parameter| : (at += 1) {
        if (at == index) return parameter.name_token;
    }
    return null;
}

/// The `index`-th dotted field of `path`, with the spacing the file wrote
/// around it removed: `a . b` names the same field as `a.b`.
fn fieldAt(path: []const u8, index: usize) ?[]const u8 {
    if (path.len == 0) return null;
    var rest = path;
    var at: usize = 0;
    while (at <= index) {
        const cut = std.mem.indexOfScalar(u8, rest, '.') orelse return if (at == index)
            std.mem.trim(u8, rest, " \t\r\n")
        else
            null;
        if (at == index) return std.mem.trim(u8, rest[0..cut], " \t\r\n");
        rest = rest[cut + 1 ..];
        at += 1;
    }
    return null;
}

/// True when `prefix` names an ancestor-or-self path of `path`: the whole of a
/// formal is a prefix of every field under it, and `a.b` prefixes `a.b.c`.
fn pathContains(path: []const u8, prefix: []const u8) bool {
    var index: usize = 0;
    while (fieldAt(prefix, index)) |segment| : (index += 1) {
        const found = fieldAt(path, index) orelse return false;
        if (!std.mem.eql(u8, found, segment)) return false;
    }
    return true;
}

/// True when `prefix` names an ancestor of `path` and not `path` itself: the
/// whole of a formal, or one of its fields, strictly above what was asked.
fn pathIsAncestor(path: []const u8, prefix: []const u8) bool {
    return fieldCount(prefix) < fieldCount(path) and pathContains(path, prefix);
}

fn fieldCount(path: []const u8) usize {
    if (path.len == 0) return 0;
    var count: usize = 1;
    for (path) |byte| {
        if (byte == '.') count += 1;
    }
    return count;
}

/// The rooted answer for a declaration this cache owns: what this body does
/// to the storage rooted at `selection`, counting the storage it reached
/// without a formal and leaving the question of whether the caller made two
/// formals one storage to the call site.
fn declarationEffect(
    cache: *FileCache,
    declaration: Ast.Node.Index,
    selection: ParameterSelection,
) Error!Effect {
    var state_slot: State = .{};
    defer state_slot.deinit(cache.gpa);
    const state = &state_slot;
    state.begin(cache.gpa, cache.tree, cache.tree.nodeMainToken(declaration), cache.zls, .{});
    defer state.end();
    const view: ?View = if (cache.zls) |resolver| .{ .resolver = resolver } else null;
    const set = try witnessesFor(cache, declaration, selection.param, selection.path, view, state);
    return mergeRooted(set, selection.param);
}

test "sibling generic callers reuse a completed nongeneric callee effect" {
    const source: [:0]const u8 =
        \\const Cell = struct {
        \\    value: u32,
        \\    fn poison(self: *Cell) void { self.value = undefined; }
        \\    fn forward(self: *Cell, value: anytype) void { _ = value; self.poison(); }
        \\};
        \\fn use(cell: *Cell) void {
        \\    cell.forward(@as(u8, 1));
        \\    cell.forward(@as(u64, 2));
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const tree = typed.tree();
    const poison_token = callNamed(tree, "poison") orelse return error.TestExpectedCall;
    var callees: [2]FileCache.ActualCallee = undefined;
    var count: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "forward")) continue;
        const forward = (try grow_analysis.actualCalleeOf(cache, call.queryToken(tree, node), null)) orelse return error.TestExpectedCall;
        const caller = typed.resolver.frameForFunction(forward.reference);
        const callee = (try grow_analysis.actualCalleeOf(cache, poison_token, caller)) orelse return error.TestExpectedCall;
        try std.testing.expect(count < callees.len);
        callees[count] = callee;
        count += 1;
    }
    try std.testing.expectEqual(callees.len, count);
    var state: State = .{};
    defer state.deinit(gpa);
    var remaining: u32 = actual_query_work_limit;
    state.begin(gpa, tree, poison_token, cache.zls, .{ .remaining = &remaining });
    const first = try witnessesFor(cache, callees[0].declaration, 0, "", bodyView(cache, callees[0], &state), &state);
    try std.testing.expectEqual(Effect.may_invalidate, mergeRooted(first, 0));
    try std.testing.expect(remaining < actual_query_work_limit - 1);
    state.end();

    // Same unsafe method, reached through another generic caller's frame:
    // only the completed-answer lookup is charged, not its body.
    remaining = 1;
    state.begin(gpa, tree, poison_token, cache.zls, .{ .remaining = &remaining });
    defer state.end();
    const second = try witnessesFor(cache, callees[1].declaration, 0, "", bodyView(cache, callees[1], &state), &state);
    try std.testing.expectEqual(Effect.may_invalidate, mergeRooted(second, 0));
    try std.testing.expectEqual(@as(u32, 0), remaining);
}
test "readonly shared aggregate origins complete without losing a pointee write" {
    const gpa = std.testing.allocator;
    var out: std.Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    try out.writer.writeAll("fn touch(value: anytype) void { _ = value; }\n");
    for ([_][]const u8{ "quiet", "poison" }) |name| {
        try out.writer.print("fn {s}(p: *u32) void {{\nconst a0 = .{{p, p}};\n", .{name});
        for (1..13) |index|
            try out.writer.print("const a{d} = .{{a{d}, a{d}}};\n", .{ index, index - 1, index - 1 });
        try out.writer.writeAll("touch(a12);\n");
        if (std.mem.eql(u8, name, "poison")) try out.writer.writeAll("p.* = undefined;\n");
        try out.writer.writeAll("}\n");
    }
    const source = try gpa.dupeZ(u8, out.written());
    defer gpa.free(source);
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const model = try typed.cache.fileModel();
    budget_mod.clear();
    defer budget_mod.clear();
    for ([_][]const u8{ "quiet", "poison" }) |name| {
        const declaration = model.findFn(name).?.fn_decl;
        try std.testing.expectEqual(
            if (std.mem.eql(u8, name, "quiet")) Effect.read_only else Effect.may_invalidate,
            try declarationEffect(typed.cache, declaration, .{ .param = 0 }),
        );
        try std.testing.expect(budget_mod.peek() == null);
    }
}

test "completed whole readonly bodies answer narrow demands within one lookup" {
    const source: [:0]const u8 =
        \\fn quiet(p: *u32, q: *u32) u32 { _ = q; return p.*; }
        \\fn poison(p: *u32, q: *u32) void { _ = p; q.* = undefined; }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const model = try cache.fileModel();
    const view: View = .{ .resolver = &typed.resolver };
    var state: State = .{};
    defer state.deinit(gpa);
    budget_mod.clear();
    defer budget_mod.clear();
    const quiet = model.findFn("quiet").?.fn_decl;
    const poison = model.findFn("poison").?.fn_decl;
    for ([_]Ast.Node.Index{ quiet, poison }) |declaration| {
        state.begin(gpa, cache.tree, cache.tree.nodeMainToken(declaration), cache.zls, .{});
        _ = try collectWitnesses(cache, declaration, any_param, "", view, &state, .whole);
        state.end();
    }
    var remaining: u32 = 1;
    state.begin(gpa, cache.tree, cache.tree.nodeMainToken(quiet), cache.zls, .{ .remaining = &remaining });
    try std.testing.expectEqual(Effect.read_only, mergeRooted(try witnessesFor(cache, quiet, 1, "", view, &state), 1));
    state.end();
    // A negative whole verdict says nothing about a selected formal.
    state.begin(gpa, cache.tree, cache.tree.nodeMainToken(poison), cache.zls, .{});
    defer state.end();
    try std.testing.expectEqual(Effect.may_invalidate, mergeRooted(try witnessesFor(cache, poison, 1, "", view, &state), 1));
}

test "completed readonly verdicts reuse callee bodies without hiding parameter writes" {
    const source: [:0]const u8 =
        \\fn peek(p: *u32, q: *u32) u32 { _ = q; return p.*; }
        \\fn poison(p: *u32, q: *u32) void {
        \\    _ = p.* +% p.* +% p.*;
        \\    p.* = undefined;
        \\    q.* = undefined;
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const model = try cache.fileModel();
    const view: View = .{ .resolver = &typed.resolver };
    var state: State = .{};
    defer state.deinit(gpa);
    budget_mod.clear();
    defer budget_mod.clear();
    for ([_][]const u8{ "peek", "poison" }) |name| {
        const declaration = model.findFn(name).?.fn_decl;
        const entry = cache.tree.nodeMainToken(declaration);
        var remaining: u32 = 1;
        const filed = state.verdict_count;
        state.begin(gpa, cache.tree, entry, cache.zls, .{ .remaining = &remaining });
        try std.testing.expectError(error.AnalysisBudgetExceeded, collectWitnesses(cache, declaration, 0, "", view, &state, .{ .cut = .{} }));
        try std.testing.expectEqual(filed, state.verdict_count);
        state.end();
        budget_mod.clear();

        remaining = actual_query_work_limit;
        state.begin(gpa, cache.tree, entry, cache.zls, .{ .remaining = &remaining });
        const first = try collectWitnesses(cache, declaration, 0, "", view, &state, .{ .cut = .{} });
        const effect = mergeRooted(first, 0);
        try std.testing.expectEqual(
            if (std.mem.eql(u8, name, "peek")) Effect.read_only else Effect.may_invalidate,
            effect,
        );
        try std.testing.expect(remaining < actual_query_work_limit - 1);
        state.end();

        // A new root query can afford the memo lookup, but not one body node.
        remaining = 1;
        state.begin(gpa, cache.tree, entry, cache.zls, .{ .remaining = &remaining });
        const second = try collectWitnesses(cache, declaration, 0, "", view, &state, .{ .cut = .{} });
        try std.testing.expectEqual(effect, mergeRooted(second, 0));
        try std.testing.expectEqual(@as(u32, 0), remaining);
        state.end();
    }

    // A verdict prefix is not a complete witness set. The precise question
    // must still discover the second parameter's later write.
    const poison = model.findFn("poison").?.fn_decl;
    state.begin(gpa, cache.tree, cache.tree.nodeMainToken(poison), cache.zls, .{});
    defer state.end();
    const complete = try witnessesFor(cache, poison, 0, "", view, &state);
    var saw_second = false;
    for (complete) |witness| saw_second = saw_second or witness.param == 1;
    try std.testing.expect(saw_second);
}

test "whole readonly verdict reuse preserves unknown and does not cache cycle cutoffs" {
    const source: [:0]const u8 =
        \\extern fn foreign(p: *u32) void;
        \\fn unresolved(p: *u32) void { foreign(p); }
        \\fn recursive(p: *u32) void { recursive(p); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const model = try cache.fileModel();
    const view: View = .{ .resolver = &typed.resolver };
    var state: State = .{};
    defer state.deinit(gpa);
    const opaque_decl = model.findFn("unresolved").?.fn_decl;
    const entry = cache.tree.nodeMainToken(opaque_decl);
    state.begin(gpa, cache.tree, entry, cache.zls, .{});
    try std.testing.expectEqual(Effect.unknown, mergeAll(try collectWitnesses(cache, opaque_decl, any_param, "", view, &state, .whole)));
    state.end();
    var remaining: u32 = 1;
    state.begin(gpa, cache.tree, entry, cache.zls, .{ .remaining = &remaining });
    try std.testing.expectEqual(Effect.unknown, mergeAll(try collectWitnesses(cache, opaque_decl, any_param, "", view, &state, .whole)));
    try std.testing.expectEqual(@as(u32, 0), remaining);
    state.end();

    const recursive = model.findFn("recursive").?.fn_decl;
    const filed = state.verdicts.count();
    state.begin(gpa, cache.tree, cache.tree.nodeMainToken(recursive), cache.zls, .{});
    defer state.end();
    try std.testing.expectEqual(Effect.unknown, mergeAll(try collectWitnesses(cache, recursive, any_param, "", view, &state, .whole)));
    try std.testing.expectEqual(filed, state.verdicts.count());
}

test "readonly verdict memo keeps exact generic instantiations separate" {
    const source: [:0]const u8 =
        \\fn select(comptime poison: bool, p: *u32) void {
        \\    if (poison) p.* = undefined;
        \\}
        \\fn loud(p: *u32) void { select(true, p); }
        \\fn quiet(p: *u32) void { select(false, p); }
        \\fn use(p: *u32) void { loud(p); quiet(p); }
    ;
    const gpa = std.testing.allocator;
    for ([_]bool{ false, true }) |loud_first| {
        const typed = try Typed.init(gpa, source);
        defer typed.deinit(gpa);
        const loud = callNamed(typed.tree(), "loud") orelse return error.TestExpectedCall;
        const quiet = callNamed(typed.tree(), "quiet") orelse return error.TestExpectedCall;
        const first = if (loud_first) loud else quiet;
        const second = if (loud_first) quiet else loud;
        try std.testing.expectEqual(!loud_first, (try callEffectAt(typed.cache, first, .{ .whole = null }, .{})).? == .read_only);
        try std.testing.expectEqual(loud_first, (try callEffectAt(typed.cache, second, .{ .whole = null }, .{})).? == .read_only);
        try std.testing.expect(typed.cache.effects_state.verdict_count != 0);
    }
}

test "global cold source plan retains qualified selections and sibling discharge" {
    const source: [:0]const u8 =
        \\const Pair = struct { first: u32, second: u32, third: u32 };
        \\fn change(left: *Pair, right: *Pair) void {
        \\    { const left: u32 = 0; _ = left; }
        \\    const alias = left;
        \\    { var alias = right; alias = left; _ = alias; }
        \\    const other = right;
        \\    alias.first += 1;
        \\    other.first += 1;
        \\    left.second = undefined;
        \\    right.second = undefined;
        \\}
    ;
    const gpa = std.testing.allocator;
    for ([_]bool{ false, true }) |global_first| {
        const typed = try Typed.init(gpa, source);
        defer typed.deinit(gpa);
        const cache = typed.cache;
        const declaration = (try cache.fileModel()).findFn("change").?.fn_decl;
        var state: State = .{};
        defer state.deinit(gpa);
        state.begin(gpa, cache.tree, cache.tree.nodeMainToken(declaration), cache.zls, .{});
        defer state.end();
        const view: View = .{ .resolver = &typed.resolver };
        if (global_first) _ = try witnessesFor(cache, declaration, global_only, "", view, &state);
        for ([_]u32{ 0, 1 }) |formal| {
            const third = try witnessesFor(cache, declaration, formal, "third", view, &state);
            // The lifetime consumer accepts both non-invalidating classes.
            // Ordinary local-slot writes must not pin stricter no-store
            // precision; a lost/wrong selection still retains sibling poison.
            try std.testing.expect(switch (mergeRooted(third, formal)) {
                .read_only, .writes_without_invalidation => true,
                .may_invalidate, .unknown => false,
            });
            const first = try witnessesFor(cache, declaration, formal, "first", view, &state);
            try std.testing.expect(switch (mergeRooted(first, formal)) {
                .read_only, .writes_without_invalidation => true,
                .may_invalidate, .unknown => false,
            });
            const second = try witnessesFor(cache, declaration, formal, "second", view, &state);
            try std.testing.expectEqual(Effect.may_invalidate, mergeRooted(second, formal));
            const root = try witnessesFor(cache, declaration, formal, "", view, &state);
            try std.testing.expectEqual(Effect.may_invalidate, mergeRooted(root, formal));
        }
    }
}

test "source replay retains opaque descendants after a global cold question" {
    const source: [:0]const u8 =
        \\const Cell = struct { value: u32 };
        \\extern fn foreign(value: u32) void;
        \\fn inspect(input: *Cell, output: *Cell) void {
        \\    { const input = output; _ = input; }
        \\    foreign(blk: {
        \\        output.* = undefined;
        \\        break :blk input.value;
        \\    });
        \\}
    ;
    const gpa = std.testing.allocator;
    for ([_]bool{ false, true }) |global_first| {
        const typed = try Typed.init(gpa, source);
        defer typed.deinit(gpa);
        const cache = typed.cache;
        const declaration = (try cache.fileModel()).findFn("inspect").?.fn_decl;
        var state: State = .{};
        defer state.deinit(gpa);
        state.begin(gpa, cache.tree, cache.tree.nodeMainToken(declaration), cache.zls, .{});
        defer state.end();
        const view: View = .{ .resolver = &typed.resolver };
        if (global_first) {
            const globals = try witnessesFor(cache, declaration, global_only, "", view, &state);
            try std.testing.expectEqual(Effect.unknown, mergeAll(globals));
        }
        const output = try witnessesFor(cache, declaration, 1, "", view, &state);
        try std.testing.expectEqual(Effect.may_invalidate, mergeRooted(output, 1));
        const field = try witnessesFor(cache, declaration, 1, "value", view, &state);
        try std.testing.expectEqual(Effect.may_invalidate, mergeRooted(field, 1));
        const input = try witnessesFor(cache, declaration, 0, "value", view, &state);
        try std.testing.expect(mergeRooted(input, 0) != .read_only);
    }
}

test "source replay keeps comptime branch contexts separate in both warm orders" {
    const source: [:0]const u8 =
        \\const Cell = struct { value: u32 };
        \\fn select(comptime poison: bool, cell: *Cell) void {
        \\    if (poison) cell.value = undefined;
        \\}
        \\fn quiet(cell: *Cell) void { select(false, cell); }
        \\fn loud(cell: *Cell) void { select(true, cell); }
    ;
    const gpa = std.testing.allocator;
    for ([_]bool{ false, true }) |loud_first| {
        const typed = try Typed.init(gpa, source);
        defer typed.deinit(gpa);
        const model = try typed.cache.fileModel();
        const quiet = model.findFn("quiet").?.fn_decl;
        const loud = model.findFn("loud").?.fn_decl;
        if (loud_first) {
            try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(typed.cache, loud, .{ .param = 0 }));
        } else {
            try std.testing.expectEqual(Effect.read_only, try declarationEffect(typed.cache, quiet, .{ .param = 0 }));
        }
        try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(typed.cache, loud, .{ .param = 0, .path = "value" }));
        try std.testing.expectEqual(Effect.read_only, try declarationEffect(typed.cache, quiet, .{ .param = 0, .path = "value" }));
    }
}

test "an interrupted source walk retries the full poisoning body" {
    const source: [:0]const u8 =
        \\const Cell = struct { value: u32 };
        \\fn poison(input: *Cell, output: *Cell) void {
        \\    const value = input.value +% input.value +% input.value;
        \\    _ = value;
        \\    output.* = undefined;
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const declaration = (try cache.fileModel()).findFn("poison").?.fn_decl;
    budget_mod.clear();
    defer budget_mod.clear();
    {
        var remaining: u32 = 4;
        var state: State = .{};
        defer state.deinit(gpa);
        state.begin(gpa, cache.tree, cache.tree.nodeMainToken(declaration), cache.zls, .{ .remaining = &remaining });
        defer state.end();
        try std.testing.expectError(error.AnalysisBudgetExceeded, witnessesFor(cache, declaration, 0, "", .{ .resolver = &typed.resolver }, &state));
        try std.testing.expectEqual(@as(u32, 0), remaining);
    }
    budget_mod.clear();
    try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(cache, declaration, .{ .param = 1 }));
    try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(cache, declaration, .{ .param = 1, .path = "value" }));
}

/// A source whose `heavy` body alone is longer than one allowance, beside a
/// `light` body that completes at once.
fn exhaustingSource(gpa: std.mem.Allocator) ![:0]u8 {
    var out: std.Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    try out.writer.writeAll("fn light(p: *u32) u32 { return p.*; }\n");
    try out.writer.writeAll("fn heavy(p: *u32) u32 {\n    var a: u32 = 0;\n");
    for (0..actual_query_work_limit / 2) |_| try out.writer.writeAll("    _ = a;\n");
    try out.writer.writeAll("    return p.*;\n}\n");
    try out.writer.writeAll("fn use(p: *u32) u32 { return heavy(p) + heavy(p) + light(p); }\n");
    return gpa.dupeZ(u8, out.written());
}

test "an exhausted root demand fails again at once with the same diagnostic" {
    const gpa = std.testing.allocator;
    const source = try exhaustingSource(gpa);
    defer gpa.free(source);
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const model = try cache.fileModel();
    const heavy = model.findFn("heavy").?.fn_decl;
    const light = model.findFn("light").?.fn_decl;
    const view: View = .{ .resolver = cache.zls.? };
    budget_mod.clear();
    defer budget_mod.clear();
    var state: State = .{};
    defer state.deinit(gpa);
    const entry = cache.tree.nodeMainToken(heavy);

    state.begin(gpa, cache.tree, entry, cache.zls, .{});
    try std.testing.expectError(error.AnalysisBudgetExceeded, witnessesFor(cache, heavy, 0, "", view, &state));
    const first = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.readonly_call_nodes, first.limit);
    try std.testing.expectEqual(@as(u32, 0), state.steps_left);
    try std.testing.expectEqual(@as(u32, 1), state.exhausted.count());
    state.end();

    // The identical root demand stops at once, with the same label, and
    // leaves its counter exactly where the exhausted walk left it.
    state.begin(gpa, cache.tree, entry, cache.zls, .{});
    try std.testing.expectError(error.AnalysisBudgetExceeded, witnessesFor(cache, heavy, 0, "", view, &state));
    try std.testing.expectEqual(@as(u32, 0), state.steps_left);
    const second = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(first.limit, second.limit);
    try std.testing.expectEqual(first.limit_value, second.limit_value);
    try std.testing.expectEqual(first.reached, second.reached);
    try std.testing.expectEqual(first.byte, second.byte);
    try std.testing.expectEqual(first.line, second.line);
    try std.testing.expectEqual(first.column, second.column);
    try std.testing.expectEqualStrings(first.document, second.document);
    try std.testing.expectEqualStrings(first.function.slice(), second.function.slice());
    try std.testing.expectEqual(@as(u32, 1), state.exhausted.count());
    state.end();

    // A different key is a different walk: another path of the same body
    // runs its own allowance out and is recorded under its own key.
    state.begin(gpa, cache.tree, entry, cache.zls, .{});
    try std.testing.expectError(error.AnalysisBudgetExceeded, witnessesFor(cache, heavy, 0, "x", view, &state));
    try std.testing.expectEqual(@as(u32, 0), state.steps_left);
    try std.testing.expectEqual(@as(u32, 2), state.exhausted.count());
    _ = budget_mod.take();
    state.end();

    // So is another walk mode of the same formal and path.
    state.begin(gpa, cache.tree, entry, cache.zls, .{});
    try std.testing.expectError(error.AnalysisBudgetExceeded, collectWitnesses(cache, heavy, 0, "", view, &state, .whole));
    try std.testing.expectEqual(@as(u32, 0), state.steps_left);
    try std.testing.expectEqual(@as(u32, 3), state.exhausted.count());
    _ = budget_mod.take();
    state.end();

    // And another declaration completes normally beside the recorded ones.
    state.begin(gpa, cache.tree, entry, cache.zls, .{});
    try std.testing.expectEqual(Effect.read_only, mergeRooted(try witnessesFor(cache, light, 0, "", view, &state), 0));
    try std.testing.expect(state.steps_left > actual_query_work_limit - 64);
    try std.testing.expectEqual(@as(u32, 3), state.exhausted.count());
    state.end();
    try std.testing.expect(budget_mod.take() == null);
}

test "a recorded failure never replaces a completed answer and a completed walk removes it" {
    const gpa = std.testing.allocator;
    const source = try exhaustingSource(gpa);
    defer gpa.free(source);
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const light = (try cache.fileModel()).findFn("light").?.fn_decl;
    const view: View = .{ .resolver = cache.zls.? };
    budget_mod.clear();
    defer budget_mod.clear();
    var state: State = .{};
    defer state.deinit(gpa);
    state.begin(gpa, cache.tree, cache.tree.nodeMainToken(light), cache.zls, .{});
    defer state.end();
    _ = try state.intern(gpa, "");
    const demand: ExhaustedKey = .{
        .key = .{
            .declaration = .{ .tree = cache.tree, .module = cache.module_id, .declaration = light },
            .parameter = 0,
            .path = root_path,
            .context = null,
        },
        .mode = .complete,
    };
    const stale: Exhausted = .{
        .budget = actual_query_work_limit,
        .diagnostic = .{
            .limit = .readonly_call_nodes,
            .limit_value = actual_query_work_limit,
            .reached = actual_query_work_limit,
        },
    };

    // A record whose allowance is smaller than this query's does not stop it;
    // the walk completes, files its answer and drops the record.
    try state.exhausted.put(gpa, demand, .{ .budget = 1, .diagnostic = stale.diagnostic });
    const done = try witnessesFor(cache, light, 0, "", view, &state);
    try std.testing.expectEqual(Effect.read_only, mergeRooted(done, 0));
    try std.testing.expectEqual(@as(u32, 0), state.exhausted.count());
    try std.testing.expect(state.sets.contains(demand.key));

    // Even a record that would otherwise stop the demand loses to the
    // completed answer, which is returned as filed.
    try state.exhausted.put(gpa, demand, stale);
    const again = try witnessesFor(cache, light, 0, "", view, &state);
    try std.testing.expectEqual(done.ptr, again.ptr);
    try std.testing.expect(budget_mod.take() == null);
}

test "a starved borrowed allowance is not recorded as an exhausted root demand" {
    const gpa = std.testing.allocator;
    const source = try exhaustingSource(gpa);
    defer gpa.free(source);
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const heavy = (try cache.fileModel()).findFn("heavy").?.fn_decl;
    const view: View = .{ .resolver = cache.zls.? };
    budget_mod.clear();
    defer budget_mod.clear();
    var remaining: u32 = 4;
    var state: State = .{};
    defer state.deinit(gpa);
    state.begin(gpa, cache.tree, cache.tree.nodeMainToken(heavy), cache.zls, .{ .remaining = &remaining });
    defer state.end();
    try std.testing.expectError(error.AnalysisBudgetExceeded, witnessesFor(cache, heavy, 0, "", view, &state));
    try std.testing.expectEqual(@as(u32, 0), remaining);
    try std.testing.expectEqual(@as(u32, 0), state.exhausted.count());
}

test "a root effect query that exhausted its allowance fails identically on the next ask" {
    const gpa = std.testing.allocator;
    const source = try exhaustingSource(gpa);
    defer gpa.free(source);
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const token = callNamed(typed.tree(), "heavy") orelse return error.TestExpectedCall;
    const light = callNamed(typed.tree(), "light") orelse return error.TestExpectedCall;
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.callEffectAt(token, .{ .parameter = .{ .param = 0 } }, .{}));
    const first = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(u32, 1), cache.effects_state.exhausted.count());
    try std.testing.expectError(error.AnalysisBudgetExceeded, cache.callEffectAt(token, .{ .parameter = .{ .param = 0 } }, .{}));
    const second = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(first.limit, second.limit);
    try std.testing.expectEqual(first.limit_value, second.limit_value);
    try std.testing.expectEqual(first.byte, second.byte);
    try std.testing.expectEqual(@as(u32, 1), cache.effects_state.exhausted.count());
    // The unsafe control still fires for the other callee, which completes.
    try std.testing.expectEqual(Effect.read_only, (try cache.callEffectAt(light, .{ .parameter = .{ .param = 0 } }, .{})).?);
    try std.testing.expect(budget_mod.take() == null);
}

test "parameter effects distinguish a written formal from a read formal" {
    // Without a resolver nothing can prove what `input.value` holds, and a
    // store this analysis cannot TYPE is charged as a replacement rather than
    // a plain write: the answer is never quieter than its evidence.  With a
    // resolver the same store narrows to a scalar and writes instead.
    const source: [:0]const u8 =
        \\const Cell = struct { value: u32 };
        \\fn inspect(input: *const Cell, output: *Cell) u32 {
        \\    output.value = input.value;
        \\    return input.value;
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const declaration = (try cache.fileModel()).findFn("inspect").?.fn_decl;
    try std.testing.expectEqual(Effect.read_only, try declarationEffect(&cache, declaration, .{ .param = 0 }));
    try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(&cache, declaration, .{ .param = 1 }));
}

test "opaque destructuring and assembly stores cannot certify read only" {
    const source: [:0]const u8 =
        \\fn destructure(p: *u32, q: *u32) void {
        \\    p.*, q.* = .{ @as(u32, undefined), @as(u32, undefined) };
        \\}
        \\fn assembled(p: *u32) void {
        \\    asm volatile ("" : : [ptr] "r" (p) : .{ .memory = true });
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const model = try cache.fileModel();
    try std.testing.expect((try declarationEffect(&cache, model.findFn("destructure").?.fn_decl, .{ .param = 0 })) != .read_only);
    try std.testing.expect((try declarationEffect(&cache, model.findFn("destructure").?.fn_decl, .{ .param = 1 })) != .read_only);
    try std.testing.expect((try declarationEffect(&cache, model.findFn("assembled").?.fn_decl, .{ .param = 0 })) != .read_only);
}

test "unknown memory intrinsic cannot certify a parameter read only" {
    const source: [:0]const u8 =
        \\fn overwrite(bytes: []u8) void { @memset(bytes, 0); }
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const declaration = (try cache.fileModel()).findFn("overwrite").?.fn_decl;
    try std.testing.expect((try declarationEffect(&cache, declaration, .{ .param = 0 })) != .read_only);
}

test "a memory intrinsic is charged at its destination operand" {
    const source: [:0]const u8 =
        \\const Cell = struct { value: u32 };
        \\fn filled(bytes: []u8) void { @memset(bytes, 0); }
        \\fn released(bytes: []u8) void { @memset(bytes, undefined); }
        \\fn stored(cell: *Cell) void { @atomicStore(u32, &cell.value, 1, .seq_cst); }
        \\fn bumped(cell: *Cell) void { @atomicRmw(u32, &cell.value, .Add, @as(u32, 1), .monotonic); }
        \\fn loaded(cell: *const Cell) u32 { return @atomicLoad(u32, &cell.value, .seq_cst); }
        \\fn shouted(message: []const u8) void { @panic(message); }
        \\fn zeroOperands(bytes: []const u8) void { _ = bytes; _ = @This(); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const at = struct {
        fn effect(t: *Typed, name: []const u8, path: []const u8) !Effect {
            const found = try t.cache.fileModel();
            return declarationEffect(t.cache, found.findFn(name).?.fn_decl, .{ .param = 0, .path = path });
        }
    }.effect;
    // A memset's destination root is a pointer or a slice, which proves
    // nothing either way; what decides is the CONTENT it names, and a defined
    // scalar over the selected bytes keeps the caller's storage.
    try std.testing.expectEqual(Effect.writes_without_invalidation, try at(typed, "filled", ""));
    // The same store with `undefined` poisons what it writes.
    try std.testing.expectEqual(Effect.may_invalidate, try at(typed, "released", ""));
    // An atomic replaces what the pointer names, at operand one.
    try std.testing.expectEqual(Effect.may_invalidate, try at(typed, "stored", ""));
    try std.testing.expectEqual(Effect.may_invalidate, try at(typed, "bumped", ""));
    // A load reads and writes nothing, and a one-operand builtin has an
    // ABSENT second slot that is not a node at all.
    try std.testing.expectEqual(Effect.read_only, try at(typed, "loaded", ""));
    // A zero-operand builtin has no operand range to slice or dereference.
    try std.testing.expectEqual(Effect.read_only, try at(typed, "zeroOperands", ""));
    // An intrinsic this table does not know is charged at full strength.
    try std.testing.expectEqual(Effect.unknown, try at(typed, "shouted", ""));
}

/// Resolver, model and binding setup use the real allocator. Each call builds
/// a fresh query State; only that demand query uses the injected allocator.
fn effectUnderAllocator(
    typed: *Typed,
    declaration: Ast.Node.Index,
    gpa: std.mem.Allocator,
) !Effect {
    const original = typed.cache.gpa;
    typed.cache.gpa = gpa;
    defer typed.cache.gpa = original;
    return declarationEffect(typed.cache, declaration, .{ .param = 0, .path = "first" });
}

test "a completed query keeps its answer when only the memo filing runs out" {
    const source: [:0]const u8 =
        \\const Pair = struct { first: u32, second: u32 };
        \\fn bump(pair: *Pair) void { pair.first += 1; }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const declaration = (try typed.cache.fileModel()).findFn("bump").?.fn_decl;
    const expected = try declarationEffect(typed.cache, declaration, .{ .param = 0, .path = "first" });
    try std.testing.expectEqual(Effect.writes_without_invalidation, expected);
    var counting: std.testing.FailingAllocator = .init(gpa, .{});
    try std.testing.expectEqual(expected, try effectUnderAllocator(typed, declaration, counting.allocator()));
    try std.testing.expect(counting.alloc_index != 0);
    var survived_failure = false;
    var fail_index: usize = 0;
    while (fail_index < counting.alloc_index) : (fail_index += 1) {
        var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = fail_index });
        const answer = effectUnderAllocator(typed, declaration, failing.allocator()) catch |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expect(failing.has_induced_failure);
                continue;
            },
            else => return err,
        };
        try std.testing.expectEqual(expected, answer);
        survived_failure = survived_failure or failing.has_induced_failure;
    }
    try std.testing.expect(survived_failure);
}

test "a sibling field is charged and a field no site names is not" {
    const source: [:0]const u8 =
        \\const Pair = struct { first: u32, second: u32, third: u32 };
        \\fn bump(pair: *Pair) void { pair.first += 1; pair.second += 1; }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const declaration = (try typed.cache.fileModel()).findFn("bump").?.fn_decl;
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
        try declarationEffect(typed.cache, declaration, .{ .param = 0, .path = "first" }),
    );
    // Both fields are actually written. The address-free object graph proves
    // that the third field cannot alias either scalar destination.
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
        try declarationEffect(typed.cache, declaration, .{ .param = 0, .path = "second" }),
    );
    try std.testing.expectEqual(
        Effect.read_only,
        try declarationEffect(typed.cache, declaration, .{ .param = 0, .path = "third" }),
    );
}

test "sibling slice fields can carry the same backing storage" {
    const source: [:0]const u8 =
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn bump(pair: *Pair) void { @memset(pair.first, undefined); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const declaration = (try typed.cache.fileModel()).findFn("bump").?.fn_decl;
    try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(
        typed.cache,
        declaration,
        .{ .param = 0, .path = "second" },
    ));
}

test "an indexed scalar store keeps the container and an undefined one does not" {
    const source: [:0]const u8 =
        \\fn set(cell: []u32) void { cell[0] = 1; }
        \\fn poison(cell: []u32) void { cell[0] = undefined; }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const model = try typed.cache.fileModel();
    // The cell is a u32 this analysis typed and the value is a literal, so
    // the container the caller holds survives the store.
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
        try declarationEffect(typed.cache, model.findFn("set").?.fn_decl, .{ .param = 0 }),
    );
    try std.testing.expectEqual(
        Effect.may_invalidate,
        try declarationEffect(typed.cache, model.findFn("poison").?.fn_decl, .{ .param = 0 }),
    );
}

test "replacing the object a field lives in invalidates that field" {
    const source: [:0]const u8 =
        \\const Cell = struct { value: u32 };
        \\fn replace(cell: *Cell, other: Cell) void { cell.* = other; }
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const declaration = (try cache.fileModel()).findFn("replace").?.fn_decl;
    try std.testing.expectEqual(
        Effect.may_invalidate,
        try declarationEffect(&cache, declaration, .{ .param = 0, .path = "value" }),
    );
}

test "an opaque write to a private construction leaves the formal alone" {
    const source: [:0]const u8 =
        \\fn wipe(bytes: []u8) void {
        \\    _ = bytes;
        \\    var scratch = [_]u8{0};
        \\    @memset(&scratch, 0);
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const declaration = (try cache.fileModel()).findFn("wipe").?.fn_decl;
    try std.testing.expectEqual(Effect.read_only, try declarationEffect(&cache, declaration, .{ .param = 0 }));
}

test "an opaque write to file level storage keeps the formal unknown" {
    const source: [:0]const u8 =
        \\var shared: []u8 = undefined;
        \\fn wipe(bytes: []u8) void { @memset(shared, 0); }
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const declaration = (try cache.fileModel()).findFn("wipe").?.fn_decl;
    try std.testing.expectEqual(Effect.unknown, try declarationEffect(&cache, declaration, .{ .param = 0 }));
}

test "a bodyless declaration is a record and no effect" {
    const source: [:0]const u8 =
        \\extern "c" fn fill(bytes: []u8) void;
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const declaration = (try cache.fileModel()).findFn("fill").?.fn_decl;
    try std.testing.expectEqual(Effect.unknown, try declarationEffect(&cache, declaration, .{ .param = 0 }));
}

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

/// The cache's own token for the first call spelled `name`: the key
/// `FileCache.getCallIndex` files it under.
fn callNamed(tree: *const Ast, name: []const u8) ?Ast.TokenIndex {
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), name)) continue;
        return tree.nodeMainToken(call.ast.fn_expr);
    }
    return null;
}

test "excluded actual callees fail without publishing a null memo and can be retried" {
    // Real import admission distinguishes a failed lookup from an opaque
    // callback. A failed lookup must not become the callback's successful null.
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{
        .sub_path = "remote.zig",
        .data = "pub const Scalar = u8; pub fn read(bytes: []const u8) u8 { return bytes[0]; }",
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
        \\fn use(bytes: []const u8) u8 { return remote.read(bytes); }
        \\fn intrinsic(bytes: []const u8) u8 { return @call(.auto, remote.read, .{bytes}); }
        \\fn narrow(value: remote.Scalar) void { _ = value; }
        \\fn invokeCallback(callback: *const fn ([]const u8) u8, bytes: []const u8) u8 {
        \\    return callback(bytes);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const cache = try gpa.create(FileCache);
    defer gpa.destroy(cache);
    cache.* = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const token = callNamed(tree, "read") orelse return error.TestExpectedCall;
    try std.testing.expectError(error.SourceExcluded, actualCallSummaryAt(cache, token, null));
    try std.testing.expect(!cache.actual_callees.contains(token));
    const intrinsic = (try cache.fileModel()).findFn("intrinsic").?.fn_decl;
    try std.testing.expectError(
        error.SourceExcluded,
        declarationEffect(cache, intrinsic, .{ .param = 0 }),
    );
    const narrow = (try cache.fileModel()).findFn("narrow").?.fn_decl;
    var narrow_buffer: [1]Ast.Node.Index = undefined;
    const narrow_proto = tokens.fnProto(tree, &narrow_buffer, narrow).?;
    try std.testing.expectError(
        error.SourceExcluded,
        grow_analysis.parameterIsNonAddressScalar(cache, narrow_proto, .{ .param = 0, .path = "" }),
    );
    try std.testing.expectEqual(@as(u32, 0), cache.scalar_params.count());
    context.store.source_policy = .{ .roots = &.{directory} };
    const record = (try actualCallSummaryAt(cache, token, null)) orelse
        return error.TestExpectedCallee;
    try std.testing.expect(cache.actual_callees.contains(token));
    var buffer: [2]Ast.Node.Index = undefined;
    const argument = (try record.callArgumentFor(cache, &buffer, 0)) orelse
        return error.TestExpectedArgument;
    try std.testing.expectEqualStrings("bytes", tree.tokenSlice(tree.nodeMainToken(argument)));
    try std.testing.expectEqual(
        @as(?Ast.Node.Index, null),
        try record.callArgumentFor(cache, &buffer, 1),
    );
    try std.testing.expectEqual(
        Effect.read_only,
        try declarationEffect(cache, intrinsic, .{ .param = 0 }),
    );
    try std.testing.expect(try grow_analysis.parameterIsNonAddressScalar(
        cache,
        narrow_proto,
        .{ .param = 0, .path = "" },
    ));
    const opaque_call = callNamed(tree, "callback") orelse return error.TestExpectedCall;
    try std.testing.expect((try actualCallSummaryAt(cache, opaque_call, null)) == null);
    try std.testing.expect(cache.actual_callees.contains(opaque_call));
}

test "scalar effect failures publish no witness memo and can be retried" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{
        .sub_path = "remote.zig",
        .data = "pub const Scalar = u8; pub const value: u8 = 1;",
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    const remote = try std.fs.path.join(gpa, &.{ directory, "remote.zig" });
    defer gpa.free(remote);
    // Exercise both destination and stored-value queries for ordinary stores
    // and byte intrinsics. Each resolver starts with an unread remote source.
    const sources = [_][:0]const u8{
        \\const remote = @import("remote.zig");
        \\fn write(bytes: []remote.Scalar) void { bytes[0] = 1; }
        ,
        \\const remote = @import("remote.zig");
        \\fn write(bytes: []u8) void { bytes[0] = remote.value; }
        ,
        \\const remote = @import("remote.zig");
        \\fn write(bytes: []remote.Scalar) void { @memset(bytes, 1); }
        ,
        \\const remote = @import("remote.zig");
        \\fn write(bytes: []u8) void { @memset(bytes, remote.value); }
        ,
    };
    for (sources) |source| {
        var context: Typed.engine.TypeContext = undefined;
        try context.init(gpa, io);
        defer context.deinit();
        context.store.source_policy = .{ .roots = &.{directory}, .excludes = &.{remote} };
        var resolver: TypeResolver = undefined;
        try resolver.init(&context, gpa, path, source);
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        const cache = try gpa.create(FileCache);
        defer gpa.destroy(cache);
        cache.* = FileCache.init(gpa, tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        const declaration = (try cache.fileModel()).findFn("write").?.fn_decl;
        var state: State = .{};
        defer state.deinit(gpa);
        state.begin(gpa, tree, tree.nodeMainToken(declaration), &resolver, .{});
        defer state.end();
        const view: View = .{ .resolver = &resolver };
        try std.testing.expectError(
            error.SourceExcluded,
            witnessesFor(cache, declaration, 0, "", view, &state),
        );
        try std.testing.expectEqual(@as(usize, 0), state.sets.count());
        try std.testing.expectEqual(@as(usize, 0), state.active.count());
        try std.testing.expectEqual(@as(u32, 0), state.depth);
        context.store.source_policy = .{ .roots = &.{directory} };
        try std.testing.expectEqual(
            Effect.writes_without_invalidation,
            mergeRooted(try witnessesFor(cache, declaration, 0, "", view, &state), 0),
        );
        try std.testing.expectEqual(@as(usize, 1), state.sets.count());
    }
}

test "a callee's parameter path is carried into the caller's own path" {
    const source: [:0]const u8 =
        \\const Cell = struct { value: u32, other: u32 };
        \\const Pair = struct { inner: Cell, spare: Cell };
        \\fn setValue(cell: *Cell) void { cell.value = 1; }
        \\fn use(pair: *Pair) void { setValue(&pair.inner); }
        \\fn readOnly(pair: *const Pair) u32 { return pair.inner.value; }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const model = try typed.cache.fileModel();
    const use = model.findFn("use").?.fn_decl;
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
        try declarationEffect(typed.cache, use, .{ .param = 0, .path = "inner.value" }),
    );
    // These scalar fields occupy different cells in an address-free graph.
    try std.testing.expectEqual(
        Effect.read_only,
        try declarationEffect(typed.cache, use, .{ .param = 0, .path = "inner.other" }),
    );
    try std.testing.expectEqual(
        Effect.read_only,
        try declarationEffect(typed.cache, use, .{ .param = 0, .path = "spare" }),
    );
    // A body that writes nothing answers read only on every path of it.
    const read_only = model.findFn("readOnly").?.fn_decl;
    try std.testing.expectEqual(
        Effect.read_only,
        try declarationEffect(typed.cache, read_only, .{ .param = 0, .path = "spare.value" }),
    );
}

test "storage a callee reaches without a formal reaches the caller's question too" {
    const source: [:0]const u8 =
        \\var shared: []u8 = undefined;
        \\fn helper(bytes: []u8) void { @memset(shared, 0); }
        \\fn use(bytes: []u8) void { helper(bytes); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const cache = typed.cache;
    const declaration = (try cache.fileModel()).findFn("use").?.fn_decl;
    try std.testing.expectEqual(Effect.unknown, try declarationEffect(cache, declaration, .{ .param = 0 }));
    const token = callNamed(typed.tree(), "helper") orelse return error.TestExpectedCall;
    // The same question asked of the storage this call reaches outside every
    // formal it was handed.
    try std.testing.expectEqual(Effect.unknown, (try cache.callEffectAt(token, .unrooted, .{})).?);
    // And the parameter question is never quietened by a rooted verdict.
    try std.testing.expectEqual(Effect.unknown, (try cache.callEffectAt(token, .{ .parameter = .{ .param = 0 } }, .{})).?);
}

test "whole mutation proof retains uncertain global and formal error branches" {
    // A consumer may omit mutation work only when every reachable effect is read-only.
    const source: [:0]const u8 =
        \\extern fn foreign() void;
        \\fn quiet(value: usize) usize { return value + 1; }
        \\fn quiet_forward(value: usize) usize { return quiet(value); }
        \\fn change_private(value: *u32) void { value.* = 1; }
        \\fn quiet_local() void { var value: u32 = 0; change_private(&value); }
        \\fn global(flag: bool) void { if (flag) foreign(); }
        \\fn formal(value: *u32, fail: bool) !void {
        \\    if (fail) { value.* = undefined; return error.Failed; }
        \\}
        \\fn use(value: *u32, flag: bool) !void {
        \\    _ = quiet(1);
        \\    _ = quiet_forward(1);
        \\    quiet_local();
        \\    global(flag);
        \\    try formal(value, flag);
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    for ([_][]const u8{ "quiet", "quiet_forward", "quiet_local", "global", "formal" }) |name| {
        const token = callNamed(typed.tree(), name) orelse return error.TestExpectedCall;
        const actual = (try actualCallSummaryAt(typed.cache, token, null)) orelse
            return error.TestExpectedCall;
        const effect = (try callEffectAt(typed.cache, token, .{ .whole = actual.callee }, .{})) orelse
            return error.TestExpectedCall;
        try std.testing.expectEqual(std.mem.startsWith(u8, name, "quiet"), effect == .read_only);
    }
}

test "whole negative prefix never publishes a completed body or source plan" {
    const source: [:0]const u8 =
        \\extern fn foreign() void;
        \\fn change(value: *u32) void {
        \\    value.* = 1;
        \\    foreign();
        \\}
        \\fn forward(value: *u32) void { change(value); }
        \\fn use(value: *u32) void { forward(value); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    var state: State = .{};
    defer state.deinit(gpa);
    const token = callNamed(typed.tree(), "forward") orelse return error.TestExpectedCall;
    const actual = (try actualCallSummaryAt(typed.cache, token, null)) orelse
        return error.TestExpectedCall;
    try std.testing.expectEqual(Effect.unknown, (try callEffectAt(
        typed.cache,
        token,
        .{ .whole = actual.callee },
        .{ .effects_state = &state },
    )).?);
    try std.testing.expectEqual(@as(usize, 0), state.sets.count());
    try std.testing.expectEqual(@as(usize, 0), state.active.count());
    try std.testing.expectEqual(@as(usize, 0), typed.cache.effect_source_plans.count());
    // The precise question must still reach the opaque call after the store.
    try std.testing.expectEqual(Effect.unknown, (try callEffectAt(
        typed.cache,
        token,
        .unrooted,
        .{ .effects_state = &state },
    )).?);
    try std.testing.expect(state.sets.count() != 0);
    try std.testing.expect(typed.cache.effect_source_plans.count() != 0);
}

test "instantiated reflection excludes impossible effects but runtime branches stay unknown" {
    const source: [:0]const u8 =
        \\extern fn foreign() void;
        \\fn inspect(comptime T: type, value: T) void {
        \\    switch (@typeInfo(T)) {
        \\        .pointer => foreign(),
        \\        else => { _ = value; },
        \\    }
        \\}
        \\fn known(value: u32) void { inspect(u32, value); }
        \\fn pointer(value: *u32) void { inspect(*u32, value); }
        \\fn conditional(flag: bool) void { if (flag) foreign(); }
        \\fn unknown(flag: bool) void { conditional(flag); }
    ;
    const gpa = std.testing.allocator;
    for ([_]bool{ false, true }) |pointer_first| {
        const typed = try Typed.init(gpa, source);
        defer typed.deinit(gpa);
        const known = callNamed(typed.tree(), "inspect") orelse return error.TestExpectedCall;
        const unknown = callNamed(typed.tree(), "conditional") orelse return error.TestExpectedCall;
        const pointer = (try typed.cache.fileModel()).findFn("pointer").?.fn_decl;
        if (pointer_first) {
            try std.testing.expectEqual(
                Effect.unknown,
                try declarationEffect(typed.cache, pointer, .{ .param = 0 }),
            );
        }
        try std.testing.expectEqual(
            Effect.read_only,
            (try typed.cache.callEffectAt(known, .unrooted, .{})).?,
        );
        try std.testing.expectEqual(
            Effect.unknown,
            try declarationEffect(typed.cache, pointer, .{ .param = 0 }),
        );
        try std.testing.expectEqual(
            Effect.unknown,
            (try typed.cache.callEffectAt(unknown, .unrooted, .{})).?,
        );
    }
}

test "mutable address-free scratch does not become an unrooted caller effect" {
    const source: [:0]const u8 =
        \\const State = struct { bits: u64 };
        \\fn change(state: *State, next: u64) void { state.bits = next; }
        \\fn compute(bytes: []const u8) u64 {
        \\    var state = State{ .bits = 0 };
        \\    change(&state, bytes[0]);
        \\    return state.bits;
        \\}
        \\fn use(bytes: []const u8) u64 { return compute(bytes); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const token = callNamed(typed.tree(), "compute") orelse return error.TestExpectedCall;
    try std.testing.expectEqual(
        Effect.read_only,
        (try typed.cache.callEffectAt(token, .unrooted, .{})).?,
    );
    try std.testing.expectEqual(
        Effect.read_only,
        (try typed.cache.callEffectAt(token, .{ .parameter = .{ .param = 0 } }, .{})).?,
    );
}

test "factory value dependencies are not the destination of private inline stores" {
    const source: [:0]const u8 =
        \\const State = struct {
        \\    bits: u64, cells: [2]u64,
        \\    fn init(seed: u64) State { return .{ .bits = seed, .cells = .{ seed, seed } }; }
        \\};
        \\fn compute(bytes: []const u8) u64 {
        \\    var state = State.init(bytes.len);
        \\    state.bits = bytes.len;
        \\    state.cells[0] = bytes[0];
        \\    return state.bits;
        \\}
        \\fn pointerFactory(state: *State) *State { return state; }
        \\fn pointerWrite(state: *State) void {
        \\    var borrowed = pointerFactory(state);
        \\    borrowed.bits = undefined;
        \\}
        \\const Header = struct { cells: []u64 };
        \\fn sliceFactory(cells: []u64) Header { return .{ .cells = cells }; }
        \\fn sliceWrite(cells: []u64) void {
        \\    var borrowed = sliceFactory(cells);
        \\    borrowed.cells[0] = undefined;
        \\}
        \\fn use(bytes: []const u8) u64 { return compute(bytes); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const token = callNamed(typed.tree(), "compute") orelse return error.TestExpectedCall;
    try std.testing.expectEqual(Effect.read_only, (try typed.cache.callEffectAt(token, .unrooted, .{})).?);
    try std.testing.expectEqual(Effect.read_only, (try typed.cache.callEffectAt(token, .{
        .parameter = .{ .param = 0 },
    }, .{})).?);
    const model = try typed.cache.fileModel();
    for ([_][]const u8{ "pointerWrite", "sliceWrite" }) |name| {
        try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(
            typed.cache,
            model.findFn(name).?.fn_decl,
            .{ .param = 0 },
        ));
    }
}

test "unrooted recursion closes known bodies without caching an incomplete cycle" {
    const source: [:0]const u8 =
        \\extern fn foreign() void;
        \\fn quiet(depth: u32) void { if (depth != 0) quiet(depth - 1); }
        \\fn first(depth: u32) void { if (depth != 0) second(depth - 1); foreign(); }
        \\fn second(depth: u32) void { if (depth != 0) first(depth - 1); }
        \\fn use(depth: u32) void { quiet(depth); first(depth); second(depth); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const model = try typed.cache.fileModel();
    var state: State = .{};
    defer state.deinit(gpa);
    state.begin(gpa, typed.tree(), 0, typed.cache.zls, .{});
    defer state.end();
    const view: View = .{ .resolver = typed.cache.zls.? };
    const quiet = model.findFn("quiet").?.fn_decl;
    const first = model.findFn("first").?.fn_decl;
    const second = model.findFn("second").?.fn_decl;
    try std.testing.expectEqual(
        Effect.read_only,
        mergeAll(try witnessesFor(typed.cache, quiet, global_only, "", view, &state)),
    );
    try std.testing.expectEqual(
        Effect.unknown,
        mergeAll(try witnessesFor(typed.cache, first, global_only, "", view, &state)),
    );
    try std.testing.expectEqual(
        Effect.unknown,
        mergeAll(try witnessesFor(typed.cache, second, global_only, "", view, &state)),
    );
}

test "a closed global component files each member's own union" {
    const source: [:0]const u8 =
        \\extern fn foreign() void;
        \\fn first(depth: u32) void { if (depth != 0) second(depth - 1); }
        \\fn second(depth: u32) void { if (depth != 0) third(depth - 1); }
        \\fn third(depth: u32) void { if (depth != 0) first(depth - 1); foreign(); }
        \\fn quiet(depth: u32) void { if (depth != 0) quiet(depth - 1); }
        \\fn use(depth: u32) void { first(depth); quiet(depth); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    var state: State = .{};
    defer state.deinit(gpa);
    const first = callNamed(typed.tree(), "first") orelse return error.TestExpectedCall;
    try std.testing.expectEqual(Effect.unknown, (try callEffectAt(typed.cache, first, .unrooted, .{ .effects_state = &state })).?);
    // One walk from the first member answers all three: the foreign call
    // lives in the last member only, and each of them reaches it.
    for ([_][]const u8{ "second", "third" }) |name| {
        const token = callNamed(typed.tree(), name) orelse return error.TestExpectedCall;
        var allowance: u32 = actual_query_work_limit;
        try std.testing.expectEqual(Effect.unknown, (try callEffectAt(typed.cache, token, .unrooted, .{
            .effects_state = &state,
            .remaining = &allowance,
        })).?);
        try std.testing.expect(actual_query_work_limit - allowance <= 3);
    }
    // A body that only meets itself is a component of one.
    const quiet = callNamed(typed.tree(), "quiet") orelse return error.TestExpectedCall;
    try std.testing.expectEqual(Effect.read_only, (try callEffectAt(typed.cache, quiet, .unrooted, .{ .effects_state = &state })).?);
    var again: u32 = actual_query_work_limit;
    try std.testing.expectEqual(Effect.read_only, (try callEffectAt(typed.cache, quiet, .unrooted, .{
        .effects_state = &state,
        .remaining = &again,
    })).?);
    try std.testing.expect(actual_query_work_limit - again <= 3);
}

test "a stopped read-only-only question files nothing partial and stays exact when complete" {
    const source: [:0]const u8 =
        \\extern fn foreign() void;
        \\fn deep(value: *u32) void { value.* = 1; }
        \\fn middle(value: *u32) void { deep(value); foreign(); }
        \\fn top(value: *u32) void { middle(value); }
        \\fn peek(value: *u32) u32 { return value.*; }
        \\fn use(value: *u32) void { top(value); _ = peek(value); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    var state: State = .{};
    defer state.deinit(gpa);
    const top = callNamed(typed.tree(), "top") orelse return error.TestExpectedCall;
    const stopped = (try callEffectAt(typed.cache, top, .{ .parameter = .{ .param = 0, .read_only_only = true } }, .{ .effects_state = &state })).?;
    try std.testing.expect(stopped != .read_only);
    try std.testing.expectEqual(@as(usize, 0), state.sets.count());
    try std.testing.expectEqual(@as(usize, 0), typed.cache.effect_source_plans.count());
    try std.testing.expectEqual(@as(usize, 0), state.active.count());
    // The same question asked completely keeps its exact verdict.
    try std.testing.expectEqual(Effect.may_invalidate, (try callEffectAt(typed.cache, top, .{ .parameter = .{ .param = 0 } }, .{ .effects_state = &state })).?);
    try std.testing.expect(state.sets.count() != 0);
    // And a read-only callee is still certified through the stopping form.
    const peek = callNamed(typed.tree(), "peek") orelse return error.TestExpectedCall;
    try std.testing.expectEqual(Effect.read_only, (try callEffectAt(typed.cache, peek, .{ .parameter = .{ .param = 0, .read_only_only = true } }, .{ .effects_state = &state })).?);
}

test "advisory witnesses stop a read-only-only question only while the formal can carry them" {
    const source: [:0]const u8 =
        \\extern fn foreign() void;
        \\fn address(value: *u32) void { _ = value; foreign(); }
        \\fn scalar(value: u32) void { _ = value; foreign(); }
        \\fn use(value: *u32) void { address(value); scalar(value.*); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const address = callNamed(typed.tree(), "address") orelse return error.TestExpectedCall;
    const scalar = callNamed(typed.tree(), "scalar") orelse return error.TestExpectedCall;
    for ([_]bool{ false, true }) |read_only_only| {
        const carried = (try typed.cache.callEffectAt(address, .{ .parameter = .{ .param = 0, .read_only_only = read_only_only } }, .{})).?;
        try std.testing.expect(carried != .read_only);
        // A by-value scalar cannot reach the foreign call's storage.
        const copied = (try typed.cache.callEffectAt(scalar, .{ .parameter = .{ .param = 0, .read_only_only = read_only_only } }, .{})).?;
        try std.testing.expectEqual(Effect.read_only, copied);
    }
}

test "a second root question reuses the file's completed answers" {
    const source: [:0]const u8 =
        \\fn leaf(value: *u32) u32 { return value.*; }
        \\fn inner(value: *u32) u32 { return leaf(value) + leaf(value); }
        \\fn outer(value: *u32) u32 { return inner(value) + inner(value); }
        \\fn use(value: *u32) u32 { return outer(value); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const token = callNamed(typed.tree(), "outer") orelse return error.TestExpectedCall;
    var first: u32 = actual_query_work_limit;
    try std.testing.expectEqual(Effect.read_only, (try typed.cache.callEffectAt(token, .{ .parameter = .{ .param = 0 } }, .{ .remaining = &first })).?);
    var second: u32 = actual_query_work_limit;
    try std.testing.expectEqual(Effect.read_only, (try typed.cache.callEffectAt(token, .{ .parameter = .{ .param = 0 } }, .{ .remaining = &second })).?);
    try std.testing.expect(second > first);
    try std.testing.expect(actual_query_work_limit - second <= 4);
    try std.testing.expect(typed.cache.effects_state.sets.count() != 0);
}

test "dense recursive components fold within one allowance" {
    const gpa = std.testing.allocator;
    var out: std.Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    const count = 14;
    try out.writer.writeAll("extern fn foreign() void;\n");
    for (0..count) |index| {
        try out.writer.print(
            "fn f{d}(p: *u32, depth: u32) void {{ if (depth != 0) {{ f{d}(p, depth - 1); f{d}(p, depth - 1); f{d}(p, depth - 1); }} if (depth == 99) foreign(); }}\n",
            .{ index, (index + 1) % count, (index + 5) % count, (index + 9) % count },
        );
    }
    try out.writer.writeAll("fn use(p: *u32) void { f0(p, 3); }\n");
    const source = try gpa.dupeZ(u8, out.written());
    defer gpa.free(source);
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const token = callNamed(typed.tree(), "f0") orelse return error.TestExpectedCall;
    try std.testing.expect((try typed.cache.callEffectAt(token, .unrooted, .{})).? != .read_only);
    try std.testing.expect((try typed.cache.callEffectAt(token, .{ .parameter = .{ .param = 0 } }, .{})).? != .read_only);
}

test "shared recursive global branches retain writes and opaque captures at each entry" {
    const source: [:0]const u8 =
        \\var stored: u32 = 0;
        \\extern fn foreign() void;
        \\fn left(depth: u32) void {
        \\    if (depth != 0) right(depth - 1);
        \\    stored = 1;
        \\}
        \\fn right(depth: u32) void {
        \\    if (depth != 0) left(depth - 1);
        \\}
        \\fn opaqueLeft(depth: u32) void {
        \\    if (depth != 0) opaqueRight(depth - 1);
        \\    foreign();
        \\}
        \\fn opaqueRight(depth: u32) void {
        \\    if (depth != 0) opaqueLeft(depth - 1);
        \\}
        \\fn diamond(depth: u32) void {
        \\    left(depth); right(depth); left(depth);
        \\    opaqueLeft(depth); opaqueRight(depth); opaqueLeft(depth);
        \\}
        \\fn use(depth: u32) void {
        \\    diamond(depth); right(depth); opaqueRight(depth);
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const diamond = callNamed(typed.tree(), "diamond") orelse return error.TestExpectedCall;
    try std.testing.expect((try typed.cache.callEffectAt(diamond, .unrooted, .{})).? != .read_only);
    // These entries share the completed root's cache, but neither may reuse
    // an intermediate answer that omitted its recursive sibling's events.
    const right = callNamed(typed.tree(), "right") orelse return error.TestExpectedCall;
    try std.testing.expect((try typed.cache.callEffectAt(right, .unrooted, .{})).? != .read_only);
    const opaque_right = callNamed(typed.tree(), "opaqueRight") orelse return error.TestExpectedCall;
    try std.testing.expectEqual(Effect.unknown, (try typed.cache.callEffectAt(opaque_right, .unrooted, .{})).?);
}

test "global demand retains writes through a by-value formal receiver and recursive entries" {
    const source: [:0]const u8 =
        \\var touched: u32 = 0;
        \\fn touchGlobal(depth: u32) void {
        \\    if (depth != 0) sibling(depth - 1);
        \\    touched = undefined;
        \\}
        \\fn sibling(depth: u32) void {
        \\    if (depth != 0) touchGlobal(depth - 1);
        \\}
        \\const Value = struct {
        \\    n: u32,
        \\    fn run(self: Value) void { touchGlobal(self.n); }
        \\};
        \\fn outer(value: Value) void { value.run(); }
        \\fn use(value: Value) void { outer(value); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    var state: State = .{};
    defer state.deinit(gpa);
    // Reuse one supplied state across complete public queries. Both SCC
    // entries must retain the write after the outer query has retired.
    for ([_][]const u8{ "outer", "touchGlobal", "sibling", "outer" }) |name| {
        const token = callNamed(typed.tree(), name) orelse return error.TestExpectedCall;
        const effect = (try typed.cache.callEffectAt(token, .unrooted, .{
            .effects_state = &state,
        })) orelse return error.TestExpectedCall;
        try std.testing.expectEqual(Effect.may_invalidate, effect);
    }
}

test "global demand retains opaque reach through a by-value formal receiver and recursive entries" {
    const source: [:0]const u8 =
        \\extern fn foreign() void;
        \\fn touchGlobal(depth: u32) void {
        \\    if (depth != 0) sibling(depth - 1);
        \\    foreign();
        \\}
        \\fn sibling(depth: u32) void {
        \\    if (depth != 0) touchGlobal(depth - 1);
        \\}
        \\const Value = struct {
        \\    n: u32,
        \\    fn run(self: Value) void { touchGlobal(self.n); }
        \\};
        \\fn outer(value: Value) void { value.run(); }
        \\fn use(value: Value) void { outer(value); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    var state: State = .{};
    defer state.deinit(gpa);
    for ([_][]const u8{ "outer", "touchGlobal", "sibling", "outer" }) |name| {
        const token = callNamed(typed.tree(), name) orelse return error.TestExpectedCall;
        const effect = (try typed.cache.callEffectAt(token, .unrooted, .{
            .effects_state = &state,
        })) orelse return error.TestExpectedCall;
        try std.testing.expectEqual(Effect.unknown, effect);
    }
}

test "a callee that writes another formal charges that argument, not the call" {
    const source: [:0]const u8 =
        \\fn store(target: *u32, value: *u32) void { _ = target; value.* = 0; }
        \\fn use(target: *u32) void {
        \\    var spare: u32 = 0;
        \\    store(target, &spare);
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const declaration = (try typed.cache.fileModel()).findFn("use").?.fn_decl;
    // `spare` is a private construction, so the call does not touch what the
    // caller handed `target`.
    try std.testing.expectEqual(Effect.read_only, try declarationEffect(typed.cache, declaration, .{ .param = 0 }));
}

test "call intrinsic folds its actual generic body and keeps unknown callbacks unsafe" {
    const source: [:0]const u8 =
        \\fn read(comptime T: type, bytes: []const T) T { return bytes[0]; }
        \\fn write(bytes: []u8) void { @memset(bytes, undefined); }
        \\fn readWrap(bytes: []const u8) u8 { return @call(.auto, read, .{ u8, bytes }); }
        \\fn writeWrap(bytes: []u8) void { @call(.always_inline, write, .{bytes}); }
        \\fn unknownWrap(callback: *const fn ([]u8) void, bytes: []u8) void {
        \\    @call(.auto, callback, .{bytes});
        \\}
        \\fn use(callback: *const fn ([]u8) void, bytes: []u8) void { unknownWrap(callback, bytes); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const model = try typed.cache.fileModel();
    const read = model.findFn("readWrap").?.fn_decl;
    const write = model.findFn("writeWrap").?.fn_decl;
    const unknown = model.findFn("unknownWrap").?.fn_decl;
    try std.testing.expectEqual(
        Effect.read_only,
        try declarationEffect(typed.cache, read, .{ .param = 0 }),
    );
    try std.testing.expectEqual(
        Effect.may_invalidate,
        try declarationEffect(typed.cache, write, .{ .param = 0 }),
    );
    try std.testing.expectEqual(
        Effect.unknown,
        try declarationEffect(typed.cache, unknown, .{ .param = 1 }),
    );
    const callback_token = callNamed(typed.tree(), "unknownWrap") orelse return error.TestExpectedCall;
    try std.testing.expectEqual(
        Effect.unknown,
        (try typed.cache.callEffectAt(callback_token, .unrooted, .{})).?,
    );
}

test "call intrinsic maps explicit namespace self and keeps dynamic tuples unknown" {
    const source: [:0]const u8 =
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn poison(self: *Owner) void { @memset(self.bytes, undefined); }
        \\};
        \\fn explicit(owner: *Owner) void { @call(.auto, Owner.poison, .{owner}); }
        \\fn dynamic(owner: *Owner, args: struct { *Owner }) void { @call(.auto, Owner.poison, args); _ = owner; }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const model = try typed.cache.fileModel();
    try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(
        typed.cache,
        model.findFn("explicit").?.fn_decl,
        .{ .param = 0, .path = "bytes" },
    ));
    try std.testing.expectEqual(Effect.unknown, try declarationEffect(
        typed.cache,
        model.findFn("dynamic").?.fn_decl,
        .{ .param = 0 },
    ));
    const tree = typed.tree();
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .builtin_call and tag != .builtin_call_comma) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const token = tree.nodeMainToken(node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "@call")) continue;
        var scratch: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &scratch, node)) |_| {
            const actual = (try typed.cache.actualCallSummaryAt(token, null)) orelse return error.TestExpectedCallee;
            try std.testing.expectEqual(@as(?u1, 0), actual.argument_offset);
            try std.testing.expectEqual(Effect.may_invalidate, (try typed.cache.callEffectAt(
                token,
                .{ .parameter = .{ .param = 0, .path = "bytes" } },
                .{},
            )).?);
            try std.testing.expectEqual(Effect.read_only, (try typed.cache.callEffectAt(token, .unrooted, .{})).?);
        } else {
            try std.testing.expect((try typed.cache.actualCallSummaryAt(token, null)) == null);
        }
        seen += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), seen);
}

test "call intrinsic requires an immutable callable identity" {
    const source: [:0]const u8 =
        \\const Methods = struct {
        \\    fn read(bytes: []u8) void { _ = bytes; }
        \\    var readAlias = &read;
        \\};
        \\fn write(bytes: []u8) void { @memset(bytes, undefined); }
        \\fn mutable(bytes: []u8) void {
        \\    var callback = &Methods.read;
        \\    callback = &write;
        \\    @call(.auto, callback, .{bytes});
        \\}
        \\fn addressedAlias(bytes: []u8) void {
        \\    var callback = &Methods.read;
        \\    const alias = &callback;
        \\    callback = &write;
        \\    @call(.auto, alias.*, .{bytes});
        \\}
        \\fn mutableMember(bytes: []u8) void { @call(.auto, Methods.readAlias, .{bytes}); }
        \\fn stable(bytes: []u8) void {
        \\    const callback = &Methods.read;
        \\    @call(.auto, callback, .{bytes});
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const model = try typed.cache.fileModel();
    for ([_][]const u8{ "mutable", "addressedAlias", "mutableMember" }) |name| {
        try std.testing.expectEqual(
            Effect.unknown,
            try declarationEffect(typed.cache, model.findFn(name).?.fn_decl, .{ .param = 0 }),
        );
    }
    try std.testing.expectEqual(
        Effect.read_only,
        try declarationEffect(typed.cache, model.findFn("stable").?.fn_decl, .{ .param = 0 }),
    );
}

test "zero-length no-op requires a const plain slice and an exact empty initializer" {
    const source: [:0]const u8 =
        \\fn use() void {
        \\    const empty: []const u8 = &[_]u8{};
        \\    var mutable: []const u8 = &[_]u8{};
        \\    const sentinel: [:0]const u8 = &[_:0]u8{};
        \\    const nonempty: []const u8 = &[_]u8{1};
        \\    probe(empty, mutable, sentinel, nonempty);
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var state: State = .{};
    defer state.deinit(gpa);
    state.begin(gpa, &tree, 0, null, .{});
    defer state.end();
    var found = false;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "probe")) continue;
        try std.testing.expectEqual(@as(usize, 4), call.ast.params.len);
        for (call.ast.params, 0..) |argument, index| {
            try std.testing.expectEqual(index == 0, try declaredEmptySlice(&cache, argument, &state));
        }
        found = true;
    }
    try std.testing.expect(found);
}

test "nested effect queries cannot reset an exhausted consumer allowance" {
    const source: [:0]const u8 =
        \\fn peek(bytes: []const u8) u8 { return bytes[0]; }
        \\fn use(bytes: []const u8) u8 { return peek(bytes); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const token = callNamed(typed.tree(), "peek") orelse return error.TestExpectedCall;
    var remaining: u32 = 0;
    var state: State = .{};
    defer state.deinit(gpa);
    state.begin(gpa, typed.tree(), token, typed.cache.zls, .{ .remaining = &remaining });
    defer state.end();
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, typed.cache.callEffectAt(
        token,
        .{ .parameter = .{ .param = 0 } },
        .{
            .remaining = &remaining,
            .effects_state = &state,
        },
    ));
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.readonly_call_nodes, failure.limit);
}

test "the same storage passed twice is not a disjoint pair" {
    const source: [:0]const u8 =
        \\fn store(target: *u32, value: *u32) void { _ = target; value.* = 0; }
        \\fn use(target: *u32) void { store(target, target); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const declaration = (try typed.cache.fileModel()).findFn("use").?.fn_decl;
    try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(typed.cache, declaration, .{ .param = 0 }));
}

// ─────────────────────────────────────────────────────────────────────────────
// CONSUMER-BOUNDARY TESTS FOR THE CANONICAL CALL CONTRACT  —  snippet only.
//
// Append to `src/cache/call_summary.zig`, below its existing test section.
// Not a standalone module: it borrows the host file's scope for `std`, `Ast`,
// `FileCache`, `Effect`, `ActualCallSummary`, `actualCallSummaryAt`,
// `callEffectAt` and `resolver_mod`.
//
// Namespaced, so it declares no name the module already has.  Every call into
// the contract goes through `Fixture.recordAt` / `Fixture.effectAt` /
// `Fixture.unrootedAt`, so a signature change is a one-line edit here.
//
// API this block is written against (final names, no shim):
//   actualCallSummaryAt(cache, token, null)
//   callEffectAt(cache, token, .{ .parameter = sel }, .{})   — sel is a
//                                                            ParameterSelection
//   callEffectAt(cache, token, .{ .unrooted = {} }, .{})     — no formal in hand
// The trailing argument is a QueryContext, not a frame: `.{}` asks with this
// file's own allowance. `.{ .unrooted = {} }` assumes `unrooted` carries no
// payload, which is what "nothing in hand" means.
//
// What each case pins:
//   1. one alias and one container name reach ONE declaration; the receiver
//      in the binding is decided by ARITY, never by the declaration's first
//      formal's type.
//   2. the whole summary survives: borrowed-from provenance plus the complete
//      mask that makes an absent bit a proof.
//   3. a read formal and a written formal, told apart on provably distinct
//      objects.
//   4. a wrapper's query needs the transitive fold, not the direct body.
//   5. a release through a pointer capture cannot certify the buffer.
//   6. a body this run cannot read is a record with no summary and no purity
//      credit.
//   7. a real map: the SDK's own `get` and `count` both fold to read_only,
//      and the insert does not.
//   8. ONE SDK declaration, two bound contexts: the void context reads the
//      map, and a context carrying a pointer to it writes that same map.
//   9. unrooted: a body that touches only its formals is read_only, and a
//      global store is not — with no argument in hand to hide behind.
//  10. one generic declaration answers correctly for each instantiation,
//      and a whole-object write through a formal stays read_only unrooted.
//  11. a callback handed a buffer cannot be certified not to write it.
//  12. a fold deeper than the bindings table grows: the root's own borrowed
//      bindings frame is read again after the table under it rehashes.
//
// The producer's own OOM behaviour is covered by the permanent tests at the
// tail of `file_cache.zig`; this block does not repeat them.
// ─────────────────────────────────────────────────────────────────────────────

/// Absolute, per-fixture, and never read: the text is handed to the resolver
/// in memory, so the path is an IDENTITY, not a spelling this run opens.
const fixture_root = "/home/tmp2/gertullj/scratch/zbc-issues.z7MazLWs/canonical-call-tests";

const canonical_call_boundary = struct {
    /// One analysed document: context, resolver and cache, each on the heap.
    ///
    /// HEAP, NOT STACK FIELDS: `TypeResolver` keeps `ctx`, `FileCache` keeps
    /// `zls`, and the grow state is addressed INSIDE the `FileCache` value.
    /// A fixture built as a stack struct would hand out the address of a
    /// local that dies with `open`'s frame.
    const Fixture = struct {
        gpa: std.mem.Allocator,
        context: *resolver_mod.TypeContext,
        resolver: *resolver_mod.TypeResolver,
        cache: *FileCache,

        fn open(gpa: std.mem.Allocator, name: []const u8, source: [:0]const u8) !Fixture {
            const context = try gpa.create(resolver_mod.TypeContext);
            errdefer gpa.destroy(context);
            try context.init(gpa, std.testing.io);
            errdefer context.deinit();

            const resolver = try gpa.create(resolver_mod.TypeResolver);
            errdefer gpa.destroy(resolver);
            var path_buffer: [256]u8 = undefined;
            try resolver.init(context, gpa, try fixturePath(&path_buffer, name), source);
            errdefer resolver.deinit();

            const cache = try gpa.create(FileCache);
            errdefer gpa.destroy(cache);
            cache.* = FileCache.init(gpa, &resolver.handle.document.tree);
            errdefer cache.deinit();
            cache.setZls(resolver);
            // A fixture that does not parse resolves no declaration, so every
            // expectation below would be vacuously true.
            if (cache.tree.errors.len != 0) return error.InvalidSyntax;

            return .{ .gpa = gpa, .context = context, .resolver = resolver, .cache = cache };
        }

        fn deinit(self: Fixture) void {
            self.cache.deinit();
            self.gpa.destroy(self.cache);
            self.resolver.deinit();
            self.gpa.destroy(self.resolver);
            self.context.deinit();
            self.gpa.destroy(self.context);
        }

        /// The one document every answer below is read out of.
        fn ast(self: Fixture) *const Ast {
            return &self.resolver.handle.document.tree;
        }

        /// The source a bound argument or capture was spelled with.
        fn text(self: Fixture, node: Ast.Node.Index) []const u8 {
            const tree = self.ast();
            return tree.tokenSlice(tree.nodeMainToken(node));
        }

        /// The cache's own token for the `occurrence`-th call whose callee
        /// expression is spelled `name`, in source order.  The NAME is the
        /// last token of the callee expression, and the TOKEN is the one
        /// `FileCache.getCallIndex` files that call under —
        /// `nodeMainToken(fn_expr)` — because that is the key
        /// `actualCallSummaryAt` and `callEffectAt` resolve.  For a
        /// container-qualified call the two differ: `map.get(key)` is
        /// matched on `get` and addressed by the `.` before it.
        fn calleeToken(self: Fixture, name: []const u8, occurrence: usize) !Ast.TokenIndex {
            const tree = self.ast();
            var buffer: [1]Ast.Node.Index = undefined;
            var seen: usize = 0;
            for (tree.nodes.items(.tag), 0..) |_, index| {
                const node: Ast.Node.Index = @enumFromInt(index);
                const call = tree.fullCall(&buffer, node) orelse continue;
                if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), name)) continue;
                if (seen == occurrence) return tree.nodeMainToken(call.ast.fn_expr);
                seen += 1;
            }
            return error.NoSuchCallInFixture;
        }

        fn recordAt(self: Fixture, name: []const u8, occurrence: usize) !ActualCallSummary {
            return (try actualCallSummaryAt(self.cache, try self.calleeToken(name, occurrence), null)) orelse
                return error.CalleeNotResolved;
        }

        /// `selection` is a `ParameterSelection`, so "the receiver" and "the
        /// first written argument" cannot be written the same way.  The
        /// trailing argument is this file's own QueryContext: no frame
        /// travels with the question, because every fixture here asks about
        /// the document the cache is already holding.
        fn effectAt(self: Fixture, name: []const u8, occurrence: usize, selection: ParameterSelection) !Effect {
            const token = try self.calleeToken(name, occurrence);
            return (try callEffectAt(self.cache, token, .{ .parameter = selection }, .{})) orelse
                return error.NoParameterEffect;
        }

        /// The same question with NO formal in hand: what this call reaches
        /// that the caller did not hand it.
        fn unrootedAt(self: Fixture, name: []const u8, occurrence: usize) !Effect {
            const token = try self.calleeToken(name, occurrence);
            return (try callEffectAt(self.cache, token, .{ .unrooted = {} }, .{})) orelse
                return error.NoUnrootedEffect;
        }
    };

    fn fixturePath(buffer: *[256]u8, name: []const u8) ![]const u8 {
        return std.fmt.bufPrint(buffer, "{s}/{s}.zig", .{ fixture_root, name });
    }

    // ── 1. One declaration under two names; arity alone decides the receiver ──

    const module_selector_source: [:0]const u8 =
        \\const Cell = struct {
        \\    value: u32,
        \\
        \\    // One formal, passed as written: the receiver is nothing.
        \\    fn make(default: u32) Cell {
        \\        return .{ .value = default };
        \\    }
        \\
        \\    // Receiver-shaped first formal, and the call omits it.
        \\    fn setValue(self: *Cell, next: u32) void {
        \\        self.value = next;
        \\    }
        \\
        \\    // Receiver-shaped first formal, and the call WRITES it out.
        \\    fn taggedSeed(self: *Cell, tag: u32) u32 {
        \\        return self.value + tag;
        \\    }
        \\};
        \\
        \\// A typed alias of the container: one declaration, a second name.
        \\const Alias = Cell;
        \\
        \\fn throughAlias(seed: u32) Cell {
        \\    return Alias.make(seed);
        \\}
        \\
        \\fn throughContainer(seed: u32) Cell {
        \\    return Cell.make(seed);
        \\}
        \\
        \\fn throughReceiver(box: *Cell, next: u32) void {
        \\    box.setValue(next);
        \\}
        \\
        \\fn throughQualifiedReceiver(box: *Cell, tag: u32) u32 {
        \\    return Alias.taggedSeed(box, tag);
        \\}
    ;

    test "module selector: an alias and the container it names reach one declaration, and arity alone decides the receiver" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-module-selector", module_selector_source);
        defer fixture.deinit();

        // Source order: `make` is called twice, alias first.
        const via_alias = try fixture.recordAt("make", 0);
        const via_container = try fixture.recordAt("make", 1);
        const via_receiver = try fixture.recordAt("setValue", 0);
        const via_qualified_receiver = try fixture.recordAt("taggedSeed", 0);

        // An alias is not a second declaration: both spellings reach the same
        // declaration of the same document compiled in the same module.
        try std.testing.expectEqual(via_container.callee.declaration, via_alias.callee.declaration);
        try std.testing.expectEqual(via_container.callee.fn_token, via_alias.callee.fn_token);
        try std.testing.expectEqual(via_container.callee.handle.module, via_alias.callee.handle.module);
        try std.testing.expect(fixture.ast() == via_alias.callee.tree);
        try std.testing.expectEqual(fixture.cache.module_id, via_alias.callee.handle.module);

        // Every written argument is bound where it was written.
        try std.testing.expectEqual(@as(?u1, 0), via_alias.argument_offset);
        try std.testing.expectEqual(@as(?u1, 0), via_container.argument_offset);
        // `setValue` is the only call here that leaves its receiver out.
        try std.testing.expectEqual(@as(?u1, 1), via_receiver.argument_offset);
        // `taggedSeed` declares a receiver-shaped first formal and is still
        // offset 0: the call spells the receiver, so nothing is implicit.
        // Reading the declaration's first parameter type here is how a
        // written-out argument gets shifted by one.
        try std.testing.expectEqual(@as(?u1, 0), via_qualified_receiver.argument_offset);

        // The offset is what maps a formal onto the expression it received.
        var buffer: [2]Ast.Node.Index = undefined;
        const implicit_receiver = (try via_receiver.callArgumentFor(fixture.cache, &buffer, 0)) orelse
            return error.ImplicitReceiverNotBound;
        try std.testing.expectEqualStrings("box", fixture.text(implicit_receiver));
        const written_next = (try via_receiver.callArgumentFor(fixture.cache, &buffer, 1)) orelse
            return error.WrittenArgumentNotBound;
        try std.testing.expectEqualStrings("next", fixture.text(written_next));

        const explicit_receiver = (try via_qualified_receiver.callArgumentFor(fixture.cache, &buffer, 0)) orelse
            return error.ExplicitReceiverNotBound;
        try std.testing.expectEqualStrings("box", fixture.text(explicit_receiver));
        const written_tag = (try via_qualified_receiver.callArgumentFor(fixture.cache, &buffer, 1)) orelse
            return error.WrittenTagNotBound;
        try std.testing.expectEqualStrings("tag", fixture.text(written_tag));

        const only_argument = (try via_alias.callArgumentFor(fixture.cache, &buffer, 0)) orelse
            return error.NamespaceArgumentNotBound;
        try std.testing.expectEqualStrings("seed", fixture.text(only_argument));
        try std.testing.expect((try via_alias.callArgumentFor(fixture.cache, &buffer, 1)) == null);
    }

    // ── 2. The summary a consumer receives is the whole one ───────────────

    const summary_source: [:0]const u8 =
        \\// The result borrows formal 0.  Formal 1 is never returned, and
        \\// only a COMPLETE scan makes that absence a proof rather than a gap.
        \\fn borrowFirst(input: []const u8, extra: u32) []const u8 {
        \\    _ = extra;
        \\    return input;
        \\}
        \\
        \\fn borrowCaller(text: []const u8, count: u32) []const u8 {
        \\    return borrowFirst(text, count);
        \\}
    ;

    test "actual summary: the borrowed-from tag and the complete parameter mask both survive the trip" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-summary-metadata", summary_source);
        defer fixture.deinit();

        const record = try fixture.recordAt("borrowFirst", 0);
        const summary = record.summary orelse return error.NoSummaryForCallee;

        // Provenance, not just shape: a `plain` label would let a caller keep
        // a borrow whose lifetime it never bound.
        switch (summary.returns) {
            .borrowed_from => |param| try std.testing.expectEqual(@as(u32, 0), param),
            else => return error.ResultNotBorrowedFromFormalZero,
        }

        // The mask, and the completeness that makes it one.
        try std.testing.expect(summary.result_params_complete);
        try std.testing.expectEqual(@as(?bool, true), summary.returnedParamDependency(0));
        // The one answer only completeness can give.
        try std.testing.expectEqual(@as(?bool, false), summary.returnedParamDependency(1));

        try std.testing.expectEqual(@as(?u1, 0), record.argument_offset);
    }

    // ── 3. Read versus write, on objects that cannot be the same object ───

    const read_write_source: [:0]const u8 =
        \\const std = @import("std");
        \\const Cell = struct { value: u32 };
        \\
        \\// Formal 0 is only READ through a field; formal 1 is WRITTEN
        \\// through a field of its own.
        \\fn copyOut(input: *const Cell, output: *Cell) void {
        \\    output.value = input.value;
        \\}
        \\
        \\// Two DISTINCT fresh allocations, each live across the call.  Two
        \\// pointer formals may alias, and nothing about their NAMES proves
        \\// they do not; separate live storage is what makes the read_only
        \\// answer below a fact rather than a guess.
        \\fn driveCopy(gpa: std.mem.Allocator) !void {
        \\    const input = try gpa.create(Cell);
        \\    defer gpa.destroy(input);
        \\    const output = try gpa.create(Cell);
        \\    defer gpa.destroy(output);
        \\    input.* = .{ .value = 1 };
        \\    output.* = .{ .value = 0 };
        \\    copyOut(input, output);
        \\}
    ;

    test "parameter effect: a read formal stays read_only while the written one may invalidate" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-read-write", read_write_source);
        defer fixture.deinit();

        // One call, two formals.  A query that cannot tell them apart would
        // report the store to `output` as evidence about `input` too.
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.effectAt("copyOut", 0, .{ .param = 0 }),
        );
        // The written formal is NOT read_only.  Which non-read_only class it
        // gets is the callee's business: a typed store into a defined
        // scalar may be reported as `writes_without_invalidation`, and this
        // test must not pin a class it has no stake in.
        try std.testing.expect((try fixture.effectAt("copyOut", 0, .{ .param = 1 })) != .read_only);

        // The effects are about the CALLER's formals, so the record must bind
        // the caller's two arguments to the callee's two formals.
        const record = try fixture.recordAt("copyOut", 0);
        try std.testing.expectEqual(@as(?u1, 0), record.argument_offset);
        var buffer: [2]Ast.Node.Index = undefined;
        const read_argument = (try record.callArgumentFor(fixture.cache, &buffer, 0)) orelse
            return error.ReadFormalNotBound;
        try std.testing.expectEqualStrings("input", fixture.text(read_argument));
        const written_argument = (try record.callArgumentFor(fixture.cache, &buffer, 1)) orelse
            return error.WrittenFormalNotBound;
        try std.testing.expectEqualStrings("output", fixture.text(written_argument));
    }

    // ── 4. The store is two hops away, and the query must reach it ─────────

    const helper_source: [:0]const u8 =
        \\const Cell = struct { value: u32 };
        \\
        \\fn bump(self: *Cell) void {
        \\    self.value += 1;
        \\}
        \\
        \\// The control, same shape, nothing stored anywhere.
        \\fn readBack(self: *const Cell) u32 {
        \\    return self.value;
        \\}
        \\
        \\// The queried fns: one hop from the store, one hop from `drive*`.
        \\// Reading only the queried body answers read_only here.
        \\fn change(cell: *Cell) void {
        \\    bump(cell);
        \\}
        \\
        \\fn peek(cell: *const Cell) u32 {
        \\    return readBack(cell);
        \\}
        \\
        \\fn driveChange(box: *Cell) void {
        \\    change(box);
        \\}
        \\
        \\fn drivePeek(box: *const Cell) u32 {
        \\    return peek(box);
        \\}
    ;

    test "parameter effect: a helper's own field write reaches the formal the call handed it" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-helper-fold", helper_source);
        defer fixture.deinit();

        // Queried at `change`, whose own body spells no store.
        // Not read_only; again the class is the fold's to choose.
        try std.testing.expect((try fixture.effectAt("change", 0, .{ .param = 0 })) != .read_only);
        // The control, so the answer above is a fact about the store and not
        // about this fixture's shape.
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.effectAt("peek", 0, .{ .param = 0 }),
        );

        // `bump(cell)` and `readBack(cell)` spell their receiver, so the
        // queried wrappers carry no implicit receiver of their own.
        try std.testing.expectEqual(@as(?u1, 0), (try fixture.recordAt("change", 0)).argument_offset);
        try std.testing.expectEqual(@as(?u1, 0), (try fixture.recordAt("peek", 0)).argument_offset);
    }

    // ── 5. A pointer capture is the caller's own storage ──────────────────

    const capture_source: [:0]const u8 =
        \\const std = @import("std");
        \\const Row = struct { bytes: []u8 };
        \\
        \\// A free function: every argument is written, so there is no
        \\// implicit receiver and `view` is formal 1.  A POINTER capture is an
        \\// element of the caller's own buffer, not a copy this fn owns, so a
        \\// real release through it reaches storage the caller still holds.
        \\fn releaseAll(gpa: std.mem.Allocator, view: []Row) void {
        \\    for (view) |*row| {
        \\        gpa.free(row.bytes);
        \\    }
        \\}
        \\
        \\fn drain(gpa: std.mem.Allocator, view: []Row) void {
        \\    releaseAll(gpa, view);
        \\}
    ;

    test "parameter effect: a release reached through a for-loop pointer capture cannot certify the captured buffer read only" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-pointer-capture", capture_source);
        defer fixture.deinit();

        // `view` is formal 1 at the call site, and it is the buffer the loop
        // captured from.
        const effect = try fixture.effectAt("releaseAll", 0, .{ .param = 1 });
        // The loop is over a byte-offset capture and the release is behind a
        // pointer; a caller must not read that as "this call cannot touch my
        // buffer".  `.may_invalidate` (the capture reaches the storage and a
        // release does) and `.unknown` (this run will not commit to the
        // path) are both sound; `.read_only` loses the storage.
        try std.testing.expect(effect != .read_only);

        // The query is about that buffer, not about the allocator beside it.
        const record = try fixture.recordAt("releaseAll", 0);
        try std.testing.expectEqual(@as(?u1, 0), record.argument_offset);
        var buffer: [2]Ast.Node.Index = undefined;
        const allocator_argument = (try record.callArgumentFor(fixture.cache, &buffer, 0)) orelse
            return error.AllocatorNotBound;
        try std.testing.expectEqualStrings("gpa", fixture.text(allocator_argument));
        const captured = (try record.callArgumentFor(fixture.cache, &buffer, 1)) orelse
            return error.CapturedBufferNotBound;
        try std.testing.expectEqualStrings("view", fixture.text(captured));
    }

    // ── 6. A body this run cannot read is never negative evidence ─────────

    const extern_source: [:0]const u8 =
        \\// Declared, never defined here: the name is canonical, and there is
        \\// no body in this snapshot to read anything from.
        \\extern fn foreignRelease(bytes: []u8) void;
        \\
        \\fn driveForeign(bytes: []u8) void {
        \\    foreignRelease(bytes);
        \\}
    ;

    const extern_body_source: [:0]const u8 =
        \\// A body that is not Zig at all: the implementation is the
        \\// linker's, so no store, no release and no read are visible here.
        \\fn foreignWrite(bytes: []u8) void {
        \\    const foreign = @extern(*const fn ([]u8) void, .{ .name = "foreign_write" });
        \\    foreign(bytes);
        \\}
        \\
        \\fn driveForeignWrite(bytes: []u8) void {
        \\    foreignWrite(bytes);
        \\}
    ;

    test "a body this run cannot read publishes no summary and no purity credit" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-extern-body", extern_source);
        defer fixture.deinit();

        // IDENTITY IS NOT SUMMARY. A declaration that is resolved but has no
        // body to read is still a record: the callee is a fact, and only the
        // summary is absent.
        const record = try fixture.recordAt("foreignRelease", 0);
        try std.testing.expect(record.summary == null);
        // `read_only` is only ever published from a body that was read.
        try std.testing.expect(record.read_only == null);
        try std.testing.expectEqual(
            Effect.unknown,
            try fixture.effectAt("foreignRelease", 0, .{ .param = 0 }),
        );
        try std.testing.expectEqual(Effect.unknown, try fixture.unrootedAt("foreignRelease", 0));

        // The other shape of the same fact: the declaration HAS a body, and
        // that body is an `@extern` — a call this run must not model.
        const linker = try Fixture.open(gpa, "canonical-extern-body-call", extern_body_source);
        defer linker.deinit();

        const linker_record = try linker.recordAt("foreignWrite", 0);
        // A summary exists here and says nothing about the result's
        // dependence on a formal: there is no return to read.
        const linker_summary = linker_record.summary orelse return error.NoSummaryForCallee;
        try std.testing.expectEqual(@as(?bool, null), linker_summary.returnedParamDependency(0));
        try std.testing.expect(!linker_summary.result_params_complete);
        try std.testing.expectEqual(
            Effect.unknown,
            try linker.effectAt("foreignWrite", 0, .{ .param = 0 }),
        );
        try std.testing.expectEqual(Effect.unknown, try linker.unrootedAt("foreignWrite", 0));
    }

    test "SDK free releases its buffer but a project free does not" {
        const sdk_source: [:0]const u8 =
            \\const std = @import("std");
            \\fn release(gpa: std.mem.Allocator, bytes: []u8) void {
            \\    gpa.free(bytes);
            \\}
        ;
        const gpa = std.testing.allocator;
        const sdk = try Fixture.open(gpa, "canonical-sdk-release", sdk_source);
        defer sdk.deinit();
        try std.testing.expectEqual(Effect.may_invalidate, try sdk.effectAt("free", 0, .{ .param = 1 }));
        // The allocator callback remains globally unresolved; recognizing
        // its rooted release must not certify unrelated global storage.
        try std.testing.expectEqual(Effect.unknown, try sdk.unrootedAt("free", 0));

        const project_source: [:0]const u8 =
            \\const Allocator = struct {
            \\    fn free(_: Allocator, bytes: []u8) void { _ = bytes; }
            \\};
            \\fn release(bytes: []u8) void {
            \\    const allocator: Allocator = .{};
            \\    allocator.free(bytes);
            \\}
        ;
        const project_fixture = try Fixture.open(gpa, "canonical-project-release", project_source);
        defer project_fixture.deinit();
        try std.testing.expectEqual(Effect.read_only, try project_fixture.effectAt("free", 0, .{ .param = 1 }));
        try std.testing.expectEqual(Effect.read_only, try project_fixture.unrootedAt("free", 0));
    }

    test "rebinding a local cursor does not write its incoming pointee" {
        const source: [:0]const u8 =
            \\fn probe(bytes: []u8) void {
            \\    var cursor = bytes.ptr;
            \\    var remaining = bytes.len;
            \\    while (remaining != 0) {
            \\        _ = cursor[0];
            \\        remaining -= 1;
            \\        cursor = cursor + 1;
            \\    }
            \\}
            \\fn poison(bytes: []u8) void {
            \\    var cursor = bytes.ptr;
            \\    cursor = cursor + 1;
            \\    cursor[0] = undefined;
            \\}
            \\fn run(bytes: []u8) void {
            \\    probe(bytes);
            \\    poison(bytes);
            \\}
        ;
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-local-cursor", source);
        defer fixture.deinit();
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.effectAt("probe", 0, .{ .param = 0 }),
        );
        try std.testing.expectEqual(
            Effect.may_invalidate,
            try fixture.effectAt("poison", 0, .{ .param = 0 }),
        );
    }

    test "capture origins exclude loop bodies but retain captured writes and opaque reach" {
        const source: [:0]const u8 =
            \\const Node = struct { next: ?*Node, value: u32 };
            \\extern fn foreign(node: *Node) void;
            \\fn peek(node: *Node) u32 { return node.value; }
            \\fn read(first: ?*Node) void {
            \\    var cursor = first;
            \\    while (cursor) |node| {
            \\        _ = peek(node);
            \\        cursor = node.next;
            \\    }
            \\}
            \\fn poison(first: ?*Node) void {
            \\    var cursor = first;
            \\    while (cursor) |node| {
            \\        node.value = undefined;
            \\        cursor = node.next;
            \\    }
            \\}
            \\fn opaqueRead(first: ?*Node) void {
            \\    while (first) |node| { foreign(node); }
            \\}
            \\fn run(first: ?*Node) void {
            \\    read(first);
            \\    poison(first);
            \\    opaqueRead(first);
            \\}
        ;
        const fixture = try Fixture.open(std.testing.allocator, "canonical-loop-capture-origin", source);
        defer fixture.deinit();
        try std.testing.expectEqual(Effect.read_only, try fixture.effectAt("read", 0, .{ .param = 0 }));
        try std.testing.expect(try fixture.effectAt("poison", 0, .{ .param = 0 }) != .read_only);
        try std.testing.expect(try fixture.effectAt("opaqueRead", 0, .{ .param = 0 }) != .read_only);
    }

    test "call-wrapped loop conditions retain the rebound second pointee" {
        const source: [:0]const u8 =
            \\fn id(value: ?*u32) ?*u32 { return value; }
            \\fn carried(first: ?*u32, next: ?*u32) void {
            \\    var cursor = first;
            \\    while (id(cursor)) |node| {
            \\        node.* = undefined;
            \\        if (cursor == next) break;
            \\        cursor = next;
            \\    }
            \\}
            \\fn run() void {
            \\    var a: u32 = 0;
            \\    var b: u32 = 0;
            \\    carried(&a, &b);
            \\}
        ;
        const fixture = try Fixture.open(std.testing.allocator, "canonical-wrapped-loop-backedge", source);
        defer fixture.deinit();
        try std.testing.expect(try fixture.effectAt("carried", 0, .{ .param = 0 }) != .read_only);
        try std.testing.expect(try fixture.effectAt("carried", 0, .{ .param = 1 }) != .read_only);
    }

    test "omitted pointer defaults retain writes to shared storage" {
        const source: [:0]const u8 =
            \\var shared: u32 = 0;
            \\const Holder = struct { ptr: *u32 = &shared };
            \\fn poison(asked: *u32) void {
            \\    _ = asked;
            \\    const holder = Holder{};
            \\    holder.ptr.* = undefined;
            \\}
            \\fn privateScalar(asked: *u32) void {
            \\    _ = asked;
            \\    const Scalar = struct { value: u32 = 0 };
            \\    var holder = Scalar{};
            \\    holder.value = undefined;
            \\}
            \\fn run() void { poison(&shared); privateScalar(&shared); }
        ;
        const fixture = try Fixture.open(std.testing.allocator, "canonical-omitted-pointer-default", source);
        defer fixture.deinit();
        try std.testing.expect(try fixture.effectAt("poison", 0, .{ .param = 0 }) != .read_only);
        try std.testing.expect(try fixture.unrootedAt("poison", 0) != .read_only);
        try std.testing.expectEqual(Effect.read_only, try fixture.effectAt("privateScalar", 0, .{ .param = 0 }));
        try std.testing.expectEqual(Effect.read_only, try fixture.unrootedAt("privateScalar", 0));
    }

    test "address-free omitted defaults preserve header storage origins" {
        const source: [:0]const u8 =
            \\const Header = struct { bytes: []u8, count: u32 = 0 };
            \\fn poison(bytes: []u8) void {
            \\    const header = Header{ .bytes = bytes };
            \\    @memset(header.bytes, undefined);
            \\}
            \\fn scratch(asked: []u8) void {
            \\    _ = asked;
            \\    var cells = [_]u8{0};
            \\    const header = Header{ .bytes = &cells };
            \\    @memset(header.bytes, undefined);
            \\}
            \\fn run(bytes: []u8) void { poison(bytes); scratch(bytes); }
        ;
        const fixture = try Fixture.open(std.testing.allocator, "canonical-address-free-header-default", source);
        defer fixture.deinit();
        try std.testing.expectEqual(Effect.may_invalidate, try fixture.effectAt("poison", 0, .{ .param = 0 }));
        try std.testing.expectEqual(Effect.read_only, try fixture.effectAt("scratch", 0, .{ .param = 0 }));
        try std.testing.expectEqual(Effect.read_only, try fixture.unrootedAt("scratch", 0));
    }

    test "control-flow captures retain pointer loans and iteration-carried aliases" {
        const source: [:0]const u8 =
            \\const Choice = union(enum) { node: *u32, empty };
            \\fn ifLoan(value: ?*u32) void {
            \\    if (value) |node| { node.* = undefined; }
            \\}
            \\fn forLoan(values: []*u32) void {
            \\    for (values, 0..) |node, index| { _ = index; node.* = undefined; }
            \\}
            \\fn switchLoan(value: Choice) void {
            \\    switch (value) { .node => |node| node.* = undefined, .empty => {} }
            \\}
            \\fn carried(first: ?*u32, next: ?*u32) void {
            \\    var cursor = first;
            \\    while (cursor) |node| {
            \\        node.* = undefined;
            \\        cursor = next;
            \\    }
            \\}
            \\fn run(value: ?*u32, values: []*u32, choice: Choice, next: ?*u32) void {
            \\    ifLoan(value);
            \\    forLoan(values);
            \\    switchLoan(choice);
            \\    carried(value, next);
            \\}
        ;
        const fixture = try Fixture.open(std.testing.allocator, "canonical-capture-loans", source);
        defer fixture.deinit();
        try std.testing.expect(try fixture.effectAt("ifLoan", 0, .{ .param = 0 }) != .read_only);
        try std.testing.expect(try fixture.effectAt("forLoan", 0, .{ .param = 0 }) != .read_only);
        try std.testing.expect(try fixture.effectAt("switchLoan", 0, .{ .param = 0 }) != .read_only);
        try std.testing.expect(try fixture.effectAt("carried", 0, .{ .param = 0 }) != .read_only);
        try std.testing.expect(try fixture.effectAt("carried", 0, .{ .param = 1 }) != .read_only);
    }

    test "reflected pointer child reaches the actual method through a generic call" {
        const source: [:0]const u8 =
            \\const Reader = struct {
            \\    pub fn inspect(_: *Reader, key: *u64, comptime strategy: bool) void {
            \\        if (strategy) _ = key.*;
            \\    }
            \\};
            \\const Writer = struct {
            \\    pub fn inspect(_: *Writer, key: *u64, comptime strategy: bool) void {
            \\        if (strategy) key.* = 9;
            \\    }
            \\};
            \\const Opaque = struct {
            \\    pub fn inspect(_: *Opaque, key: *u64, comptime strategy: bool) void {
            \\        if (strategy) foreign(key);
            \\    }
            \\};
            \\extern fn foreign(key: *u64) void;
            \\fn dispatch(owner: anytype, key: *u64, comptime strategy: bool) void {
            \\    const Declaring = switch (@typeInfo(@TypeOf(owner))) {
            \\        .pointer => |info| info.child,
            \\        else => @TypeOf(owner),
            \\    };
            \\    @call(.always_inline, Declaring.inspect, .{ owner, key, strategy });
            \\}
            \\fn read(owner: *Reader, key: *u64) void { dispatch(owner, key, true); }
            \\fn write(owner: *Writer, key: *u64) void { dispatch(owner, key, true); }
            \\fn opaqueQuery(owner: *Opaque, key: *u64) void { dispatch(owner, key, true); }
        ;
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-reflected-pointer-child", source);
        defer fixture.deinit();
        try std.testing.expectEqual(Effect.read_only, try fixture.effectAt("dispatch", 0, .{ .param = 1 }));
        try std.testing.expectEqual(Effect.may_invalidate, try fixture.effectAt("dispatch", 1, .{ .param = 1 }));
        try std.testing.expect((try fixture.effectAt("dispatch", 2, .{ .param = 1 })) != .read_only);
    }

    // ── 7. A real map: read-only accessors and a mutating insert ──────────

    const std_map_source: [:0]const u8 =
        \\const std = @import("std");
        \\fn readOwn(map: *std.AutoHashMap(u64, u64), key: u64) ?u64 {
        \\    return map.get(key);
        \\}
        \\
        \\fn sizeOwn(map: *std.AutoHashMap(u64, u64)) usize {
        \\    return map.count();
        \\}
        \\
        \\fn writeOwn(map: *std.AutoHashMap(u64, u64), key: u64) !void {
        \\    try map.put(key, key);
        \\}
    ;

    test "a real map: the size read is read_only, and the name is not what decides the rest" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-std-map-readonly", std_map_source);
        defer fixture.deinit();

        // `map` is the receiver at all three call sites, so it is formal 0.
        try std.testing.expectEqual(@as(?u1, 1), (try fixture.recordAt("get", 0)).argument_offset);
        try std.testing.expectEqual(@as(?u1, 1), (try fixture.recordAt("count", 0)).argument_offset);
        try std.testing.expectEqual(@as(?u1, 1), (try fixture.recordAt("put", 0)).argument_offset);

        // A size read touches the map's header and writes none of it, and
        // `count` folds to the stored length with no intrinsic in between.
        // This is the answer a consumer relies on to keep a borrow across a
        // probe, and it is proved through the SDK's own declaration.
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.effectAt("count", 0, .{ .param = 0 }),
        );

        // A lookup reads the map's storage and writes none of it.  This is
        // the SDK's own body: `get` delegating to the unmanaged form, whose
        // `getIndex` walks metadata and asks a context to hash. Its actual
        // `@call` reaches a bound hasher body; writes to that private hasher
        // do not mutate the map or escape as global effects.
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.effectAt("get", 0, .{ .param = 0 }),
        );

        // THE CONTROL: the insert writes, through the same map and the same
        // chain.  A query that answered alike for `count` and for `put`
        // would be reading the NAME, not the body.
        try std.testing.expect((try fixture.effectAt("put", 0, .{ .param = 0 })) != .read_only);
    }

    // ── 8. One SDK declaration, two bound contexts, two answers ──────────

    const context_target_source: [:0]const u8 =
        \\const std = @import("std");
        \\// Two maps of the SAME SDK type family, reaching the SAME SDK body,
        \\// with two different hash contexts.  Both contexts are REAL structs
        \\// with `hash` and `eql` members: a lookup reaches them, so a
        \\// context with no methods cannot stand in for a read-only one.
        \\const ReadOnlyContext = struct {
        \\    pub fn hash(_: ReadOnlyContext, key: u64) u64 {
        \\        return key;
        \\    }
        \\
        \\    pub fn eql(_: ReadOnlyContext, a: u64, b: u64) bool {
        \\        return a == b;
        \\    }
        \\};
        \\
        \\// A context is not a separate object from the map it walks: this
        \\// one CARRIES POINTERS to it and to the allocator that ends it.  The
        \\// SDK takes the context BY VALUE — `hash(ctx: Context, key: K)`,
        \\// `eql(ctx: @This(), ...)` — so those pointers are the whole of the
        \\// reachability, and the storage they reach is the caller's map.
        \\const ReleasingContext = struct {
        \\    map: *ReleasingMap,
        \\    allocator: std.mem.Allocator,
        \\
        \\    pub fn hash(ctx: ReleasingContext, key: u64) u64 {
        \\        ctx.map.clearAndFree(ctx.allocator);
        \\        return key;
        \\    }
        \\
        \\    pub fn eql(_: ReleasingContext, a: u64, b: u64) bool {
        \\        return a == b;
        \\    }
        \\};
        \\
        \\const ReadOnlyMap = std.HashMapUnmanaged(u64, u64, ReadOnlyContext, std.hash_map.default_max_load_percentage);
        \\const ReleasingMap = std.HashMapUnmanaged(u64, u64, ReleasingContext, std.hash_map.default_max_load_percentage);
        \\
        \\fn lookupReadOnly(map: *ReadOnlyMap, key: u64) ?u64 {
        \\    return map.getContext(key, .{});
        \\}
        \\
        \\fn lookupReleasing(map: *ReleasingMap, allocator: std.mem.Allocator, key: u64) ?u64 {
        \\    const ctx: ReleasingContext = .{ .map = map, .allocator = allocator };
        \\    return map.getContext(key, ctx);
        \\}
    ;

    test "one SDK declaration answers for the map each context is bound to" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-context-target", context_target_source);
        defer fixture.deinit();

        // BOTH call sites name `getContext` — the same declaration, in the
        // same SDK document, under the same module.  What differs is which
        // map each one reaches, and a fold that answered from the
        // declaration alone would give both the same verdict.
        try std.testing.expectEqual(@as(?u1, 1), (try fixture.recordAt("getContext", 0)).argument_offset);
        try std.testing.expectEqual(@as(?u1, 1), (try fixture.recordAt("getContext", 1)).argument_offset);

        // The void context hashes with the SDK's own hasher and writes
        // nothing: the lookup reads the map.
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.effectAt("getContext", 0, .{ .param = 0 }),
        );

        // The second context CARRIES the map it was built for, and releasing
        // it is reached from inside `hash`.  A DIFFERENT FORMAL IS NOT A
        // DIFFERENT OBJECT: the context is not separate storage from the map
        // it walks, so the allocation that dies is the very one the caller
        // handed over.  This is the exact control the first assertion needs —
        // same SDK declaration, same accessor, one real release away.
        try std.testing.expectEqual(
            Effect.may_invalidate,
            try fixture.effectAt("getContext", 1, .{ .param = 0 }),
        );
    }

    // ── 9. Unrooted: what a call reaches that it was not handed ───────────

    const unrooted_source: [:0]const u8 =
        \\const std = @import("std");
        \\const Cell = struct { value: u32 };
        \\
        \\// Storage this file OWNS.  Not a typed scalar in some object: a
        \\// live allocation with an owner, which a release actually ends.
        \\var held: []u8 = undefined;
        \\var held_allocator: std.mem.Allocator = undefined;
        \\
        \\fn installShared(gpa: std.mem.Allocator) !void {
        \\    held = try gpa.alloc(u8, 1);
        \\    held_allocator = gpa;
        \\}
        \\
        \\fn releaseEmpty(gpa: std.mem.Allocator) void {
        \\    const empty: []const u8 = &[_]u8{};
        \\    gpa.free(empty);
        \\}
        \\
        \\// Reaches nothing but its own formals: whatever this call does to
        \\// the caller's arguments, it does to no storage the caller did not
        \\// hand it.  This is the body a consumer can call with a live borrow
        \\// it holds elsewhere.
        \\fn rewriteLocal(self: *Cell, other: *Cell) void {
        \\    self.value = other.value;
        \\}
        \\
        \\// A REAL release of the global buffer, reached by a call with NO
        \\// argument at all.  Nothing in hand, so nothing to charge it to —
        \\// which is exactly why an unrooted question has to be asked.
        \\fn releaseShared() void {
        \\    held_allocator.free(held);
        \\}
        \\
        \\// The same release, in a body that also takes an UNRELATED formal.
        \\// The marker is not an allocator and owns nothing: an allocator
        \\// formal would carry its own vtable bookkeeping, so read_only on it
        \\// would be a claim about the allocator rather than about this body.
        \\fn releaseSharedMarked(marker: u32) void {
        \\    _ = marker;
        \\    held_allocator.free(held);
        \\}
        \\
        \\// An unrooted question is asked of a CALL, so every body above
        \\// needs one site that reaches it.  Each driver hands the callee
        \\// only what the question is about: two live cells, nothing, and
        \\// one unrelated scalar.
        \\fn driveLocal(self: *Cell, other: *Cell) void {
        \\    rewriteLocal(self, other);
        \\}
        \\
        \\fn driveShared(gpa: std.mem.Allocator) !void {
        \\    try installShared(gpa);
        \\    releaseShared();
        \\}
        \\
        \\fn driveSharedMarked(gpa: std.mem.Allocator, marker: u32) !void {
        \\    try installShared(gpa);
        \\    releaseSharedMarked(marker);
        \\}
        \\
        \\fn driveEmpty(gpa: std.mem.Allocator) void {
        \\    releaseEmpty(gpa);
        \\}
    ;

    test "unrooted: a body that touches only its formals is read_only, and a global release is not" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-unrooted", unrooted_source);
        defer fixture.deinit();

        // Writes one formal, reads the other, and reaches nothing else.
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.unrootedAt("rewriteLocal", 0),
        );

        // A real release of storage this file owns is unsafe however it was
        // reached.  The zero-argument call is the sharp one: there is no
        // formal to attribute it to, so an answer that only ever asks about
        // formals would report nothing at all.
        try std.testing.expectEqual(
            Effect.may_invalidate,
            try fixture.unrootedAt("releaseShared", 0),
        );

        // THE PAIR: a formal that owns nothing, next to a release that ends
        // storage this file owns.  The parameter is read_only while the
        // unrooted question is still may_invalidate.  Charging the release to
        // the formal would be charging the caller for storage the caller
        // never owned, and discharging it as read_only because the formal is
        // untouched would lose the release entirely.
        try std.testing.expectEqual(
            Effect.may_invalidate,
            try fixture.unrootedAt("releaseSharedMarked", 0),
        );
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.effectAt("releaseSharedMarked", 0, .{ .param = 0 }),
        );
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.unrootedAt("releaseEmpty", 0),
        );
    }

    // ── 10. One generic declaration, two instantiations, two correct answers ──

    const generic_source: [:0]const u8 =
        \\const Cell = struct { value: u32 };
        \\const Tag = struct { id: u32 };
        \\
        \\// One syntax for every instantiation: it writes whatever it is
        \\// handed, through the pointer the caller passed.
        \\fn reset(comptime T: type, self: *T, value: T) void {
        \\    self.* = value;
        \\}
        \\
        \\fn driveBoth(cell: *Cell, tag: *Tag) void {
        \\    reset(Cell, cell, .{ .value = 0 });
        \\    reset(Tag, tag, .{ .id = 0 });
        \\}
    ;

    test "one generic declaration answers correctly for each instantiation" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-generic-instantiations", generic_source);
        defer fixture.deinit();

        // Two call sites, two instantiations, one declaration.  The store is
        // behind whichever formal the call handed over, so each call answers
        // about ITS OWN argument — the failure being pinned is one call's
        // answer being read off the other's.
        // Not read_only for either call — each about ITS OWN argument.
        try std.testing.expect((try fixture.effectAt("reset", 0, .{ .param = 1 })) != .read_only);
        try std.testing.expect((try fixture.effectAt("reset", 1, .{ .param = 1 })) != .read_only);

        // Explicit comptime arguments retain their declared formal indices;
        // only an implicit method receiver changes the argument offset.
        try std.testing.expectEqual(@as(?u1, 0), (try fixture.recordAt("reset", 0)).argument_offset);
        try std.testing.expectEqual(@as(?u1, 0), (try fixture.recordAt("reset", 1)).argument_offset);

        // And UNROOTED it is still read_only.  `self.* = value` is a
        // whole-object write, and it is entirely ROOTED: the object it
        // writes is the one the caller handed over.  A fold that reported a
        // formal-rooted store here would be claiming the call reaches
        // storage nobody gave it, which is exactly the claim case 9 refuses.
        try std.testing.expectEqual(
            Effect.read_only,
            try fixture.unrootedAt("reset", 0),
        );
    }

    // ── 11. A callback handed a buffer is not a read-only call ────────────

    const callback_source: [:0]const u8 =
        \\const Cell = struct { value: u32 };
        \\
        \\// The callback itself, declared where a driver can also CALL it:
        \\// the outer answer below is about a body that really does store,
        \\// and that body is the same one handed over as the callback.
        \\fn apply(cell: *Cell, next: u32) void {
        \\    cell.value = next;
        \\}
        \\
        \\// The caller hands over a function and a buffer, and names no
        \\// relationship between them.  Whatever the callback does, it is
        \\// done TO the buffer.
        \\fn runWith(callback: *const fn (*Cell, u32) void, target: *Cell) void {
        \\    callback(target, 1);
        \\}
        \\
        \\fn driveCallback(target: *Cell) void {
        \\    runWith(apply, target);
        \\}
        \\
        \\// A direct call of the callback body, so what it does to the cell
        \\// it is handed can be read as a call like any other.
        \\fn driveApply(cell: *Cell) void {
        \\    apply(cell, 1);
        \\}
    ;

    test "a callback handed a buffer cannot be certified not to write it" {
        const gpa = std.testing.allocator;
        const fixture = try Fixture.open(gpa, "canonical-callback-mixed", callback_source);
        defer fixture.deinit();

        // `runWith` is free: `callback` is formal 0 and `target` is formal 1.
        try std.testing.expectEqual(@as(?u1, 0), (try fixture.recordAt("runWith", 0)).argument_offset);
        var buffer: [2]Ast.Node.Index = undefined;
        const record = try fixture.recordAt("runWith", 0);
        const handed_target = (try record.callArgumentFor(fixture.cache, &buffer, 1)) orelse
            return error.TargetNotBound;
        try std.testing.expectEqualStrings("target", fixture.text(handed_target));

        // The indirect call names no body this run can read, so the buffer it
        // was handed is not proven untouched.  `.unknown` is the sound
        // answer; `.may_invalidate` if the fold reaches the spelled-out
        // callee at the outer call site.  `.read_only` is the answer this
        // query would give if it followed the callback's NAME.
        try std.testing.expect((try fixture.effectAt("runWith", 0, .{ .param = 1 })) != .read_only);

        // The callback itself does store, so the outer answer is not a
        // complaint about an inert function.
        try std.testing.expect((try fixture.effectAt("apply", 0, .{ .param = 0 })) != .read_only);
    }

    // ── 12. A fold deeper than the bindings table grows ───────────────────

    /// Deep enough that folding the top hop inserts an entry per declaration
    /// and the bindings table grows out of its initial capacity and REHASHES
    /// while the scan is still holding a borrowed frame into it.
    const rehash_hops = 40;

    /// A chain of `rehash_hops` distinct declarations over one formal, a leaf
    /// whose body is `leaf_body`, and a final callee whose body is
    /// `finish_body`.  Built through one growing buffer and a stack scratch
    /// line: forty separate string literals would be forty separate fixtures
    /// to keep in step, and the whole point is that they stay in step.
    ///
    /// The root takes its alias BEFORE the chain and USES it AFTER, so the
    /// frame the root's scan borrowed is read again once the fold has filed
    /// an entry per hop and rehashed the table underneath it.
    fn chainSource(gpa: std.mem.Allocator, leaf_body: []const u8, finish_body: []const u8) ![:0]const u8 {
        var out: std.ArrayList(u8) = .empty;
        errdefer out.deinit(gpa);
        try out.appendSlice(gpa, "const Cell = struct { value: u32 };\n\n");

        // Wide enough for the widest line this formats: the root and driver
        // block at the end, not the one-hop declarations above.
        var line: [256]u8 = undefined;
        var index: usize = 0;
        while (index < rehash_hops) : (index += 1) {
            try out.appendSlice(gpa, if (index == 0)
                try std.fmt.bufPrint(&line, "fn hop{d}(cell: *Cell) void {{ leaf(cell); }}\n", .{index})
            else
                try std.fmt.bufPrint(&line, "fn hop{d}(cell: *Cell) void {{ hop{d}(cell); }}\n", .{ index, index - 1 }));
        }

        // The leaf the last hop calls, the final callee, and then the root
        // that reaches it through its own alias — after the whole chain has
        // been folded.
        try out.appendSlice(gpa, "\nfn leaf(cell: *Cell) void {\n");
        try out.appendSlice(gpa, leaf_body);
        try out.appendSlice(gpa, "\n}\n\nfn finish(cell: *Cell) void {\n");
        try out.appendSlice(gpa, finish_body);
        try out.appendSlice(gpa, "\n}\n\n");
        try out.appendSlice(gpa, try std.fmt.bufPrint(&line,
            \\fn root(cell: *Cell) void {{
            \\    var mirror = cell;
            \\    hop{d}(cell);
            \\    finish(mirror);
            \\}}
            \\
            \\fn driver(cell: *Cell) void {{
            \\    root(cell);
            \\}}
            \\
        , .{rehash_hops - 1}));
        return out.toOwnedSliceSentinel(gpa, 0);
    }

    test "a fold deeper than the bindings table grows still resolves the root's own alias" {
        const gpa = std.testing.allocator;

        // Queried at `driver`'s call to `root`, so the body being scanned IS
        // the root's.  The root takes its alias before the deep call and
        // uses it after; the chain files an entry per hop in between, so the
        // bindings table rehashes between the root borrowing its frame and
        // the root reading that frame again.
        const stored = try chainSource(
            gpa,
            "    cell.value += 1;\n",
            "    cell.value += 1;\n",
        );
        defer gpa.free(stored);
        const writer = try Fixture.open(gpa, "canonical-bindings-rehash-write", stored);
        defer writer.deinit();

        // Not read_only — `mirror.value += 1` is a store, and the class the
        // fold reports for it (`writes_without_invalidation` once that proof
        // lands) is not what this case is about.  What it is about is that
        // the root's own alias still resolves at all, after the rehash.
        try std.testing.expect((try writer.effectAt("root", 0, .{ .param = 0 })) != .read_only);

        // THE CONTROL: the same root, the same alias used at the same point
        // in the same body, and a callee that only reads.  Without it, the
        // answer above could be coming from the rehash rather than from the
        // store.
        const read_only = try chainSource(
            gpa,
            "    _ = cell.value;\n",
            "    _ = cell.value;\n",
        );
        defer gpa.free(read_only);
        const reader = try Fixture.open(gpa, "canonical-bindings-rehash-read", read_only);
        defer reader.deinit();

        try std.testing.expectEqual(
            Effect.read_only,
            try reader.effectAt("root", 0, .{ .param = 0 }),
        );
    }
};

// The boundary cases live in a container, and a test inside a declaration
// nothing references is never discovered.  This is what puts all twelve in
// the run; it asserts nothing of its own.
test {
    std.testing.refAllDecls(canonical_call_boundary);
}
