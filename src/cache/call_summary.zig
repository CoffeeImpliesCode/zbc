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
//! TWO QUESTIONS, ONE ENTRY.  `callEffectAt` asks about storage rooted at
//! a formal and path of the callee, or about the storage a call reaches
//! that NO formal of it names.  A whole-body read-only verdict is only
//! ever the answer to the first question with the second one folded in;
//! a consumer that cares about the caller's own buffer asks for both.
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
};

/// The two storages one call can be asked about.
pub const EffectSelection = union(enum) {
    /// Storage the caller handed this call, named by a formal of the callee.
    parameter: ParameterSelection,
    /// Storage this call reaches that no formal of the callee names: what
    /// the body writes through a file-level variable, a capture it could
    /// not root, or storage an unresolved callee may touch.  It is never
    /// answered by a parameter's own verdict.
    unrooted,
};

pub const ActualCallSummary = struct {
    callee: FileCache.ActualCallee,
    summary: ?fn_summary.FnSummary,
    argument_offset: ?u1,
    read_only: ?bool,

    /// The buffer belongs to the caller, as it does in TypeResolver.
    /// Argument mapping follows the frame the CALL was reached in, not the
    /// callee's own body frame: the bindings a caller instantiates are the
    /// ones its own arguments were resolved against.
    pub fn callArgumentFor(
        self: ActualCallSummary,
        cache: *FileCache,
        buffer: *[1]Ast.Node.Index,
        parameter: u32,
    ) Error!?Ast.Node.Index {
        const view = viewFor(cache, self.callee) orelse return null;
        return view.callArgumentIn(buffer, self.callee.call_node, parameter) catch |err| switch (err) {
            error.OutOfMemory => error.OutOfMemory,
            else => null,
        };
    }

    /// The cache is immovable and owned by the canonical grow state until the
    /// root cache's deinit. A failed open is not a body/purity observation.
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

/// One query's working state: the memo and cycle set that walk fills, plus
/// the allowance it spends.  A nested query adopts its caller's counter, so
/// one allowance still covers the complete walk; each walk's memo dies with it.
pub const State = struct {
    /// Interned dotted paths.  A memo key and a witness compare by id, and
    /// the bytes behind one id are owned for the life of the root cache.
    paths: std.StringHashMapUnmanaged(u32) = .empty,
    path_text: std.ArrayListUnmanaged([]const u8) = .empty,
    /// Completed witness sets, one per declaration, question and identity.
    sets: std.HashMapUnmanaged(Key, []const Witness, KeyContext, 80) = .empty,
    /// The keys on the current stack.  A set that meets itself is a cycle,
    /// and a cycle answers unknown rather than recursing.
    active: std.HashMapUnmanaged(Key, void, KeyContext, 80) = .empty,
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
        self.active.deinit(gpa);
        if (self.memo) |*arena| arena.deinit();
        self.memo = null;
        if (self.scratch) |*arena| arena.deinit();
        self.scratch = null;
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
            .limit = limit, .limit_value = cap, .reached = reached,
            .byte = byte, .line = position.line, .column = position.column, .function = name,
        });
    }

    /// File one dotted path under a stable id.  The bytes are owned by the
    /// persistent memo arena — never by the caller's frame, never by the
    /// per-query scratch — and BOTH containers are grown before either is
    /// written, so a failure at any point publishes nothing and leaves the
    /// table exactly as it was for the next attempt.
    fn intern(self: *State, gpa: std.mem.Allocator, path: []const u8) error{OutOfMemory}!u32 {
        if (self.paths.get(path)) |existing| return existing;
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

fn cacheFor(cache: *FileCache, callee: FileCache.ActualCallee) Error!?*FileCache {
    if (callee.tree == cache.tree and callee.handle.module == cache.module_id) return cache;
    if (cache.zls == null) return null;
    const document = grow_analysis.sourceDocument(cache, callee.handle) catch return null;
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
        buffer: *[1]Ast.Node.Index,
        node: Ast.Node.Index,
    ) !?TypeResolver.CallArguments {
        return switch (self) {
            .resolver => |r| try r.callArgumentsOf(buffer, node),
            .frame => |f| try f.callArgumentsOf(buffer, node),
        };
    }

    fn callArgumentIn(
        self: View,
        buffer: *[1]Ast.Node.Index,
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
        .callee = callee, .summary = null, .argument_offset = null, .read_only = null,
    };
    const view = viewFor(cache, callee) orelse return result;
    var buffer: [1]Ast.Node.Index = undefined;
    const arguments = view.callArgumentsOf(&buffer, callee.call_node) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => null,
    };
    if (arguments) |actual| result.argument_offset = @intFromBool(actual.receiver != null);
    // A bodyless declaration is still a canonical record: the identity and the
    // summary are read, and nothing about its effects is inferred from the
    // absence of a body.
    if (tokens.bodyOf(callee.tree, callee.declaration) == null) return result;
    const declaring = (try cacheFor(cache, callee)) orelse return result;
    const found = declaring.summaryOfResolvedMethod(.{
        .tree = callee.tree, .module = callee.handle.module, .fn_decl = callee.declaration,
    }) catch |err| return err;
    result.summary = if (found) |s| s.* else null;
    if (result.summary == null) return result;
    var state_slot: State = .{};
    defer state_slot.deinit(cache.gpa);
    const state = &state_slot;
    if (bodyReadOnly(cache, callee, state)) |read_only| result.read_only = read_only;
    return result;
}

/// The whole-body verdict, only when a demand query has already folded it.
/// Nothing here walks a body: an identity question must not pay for an effect
/// analysis nobody asked for, and a fold nothing asked for is not a verdict —
/// an absent entry stays null, because "this body writes nothing" and "this
/// body has not been looked at" are different answers.  A consumer that
/// needs the whole-body fact asks `callEffectAt` for it.  This verdict is over
/// EVERY formal and the unrooted storage together, so a `true` here is also
/// the answer to `.unrooted`.
fn bodyReadOnly(cache: *FileCache, callee: FileCache.ActualCallee, state: *State) ?bool {
    const declaring = (cacheFor(cache, callee) catch return null) orelse return null;
    const view = bodyView(declaring, callee, state) orelse return null;
    const key: Key = .{
        .declaration = .{
            .tree = declaring.tree, .module = declaring.module_id, .declaration = callee.declaration,
        },
        .parameter = any_param,
        .path = root_path,
        .context = contextOf(view),
    };
    const set = state.sets.get(key) orelse return null;
    return switch (mergeAll(set)) {
        .read_only => true,
        .writes_without_invalidation, .may_invalidate => false,
        .unknown => null,
    };
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
    const callee = (try grow_analysis.actualCalleeOf(cache, token, context.frame)) orelse return null;
    const declaring = (try cacheFor(cache, callee)) orelse return .unknown;
    const view = viewFor(cache, callee) orelse return .unknown;
    var state_slot: State = .{};
    defer state_slot.deinit(cache.gpa);
    const state = &state_slot;
    state.begin(cache.gpa, cache.tree, token, cache.zls, context);
    defer state.end();
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = cache.tree.fullCall(&call_buffer, callee.call_node) orelse return .unknown;
    var argument_buffer: [1]Ast.Node.Index = undefined;
    const arguments = view.callArgumentsOf(&argument_buffer, callee.call_node) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return .unknown,
    } orelse return .unknown;
    const count = arguments.arguments.len + @intFromBool(arguments.receiver != null);
    const callee_view = bodyView(declaring, callee, state) orelse return .unknown;
    switch (selection) {
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
                const append = view.stdCollectionAppendOf(call.ast.fn_expr, count - 1) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => .no,
                };
                // Existing SDK identity/arity query distinguishes this
                // append's new-slot/length stores from writes poisoning
                // existing elements.
                switch (append) {
                    .infallible => return .writes_without_invalidation,
                    .fallible => return .may_invalidate,
                    .no => {},
                }
            }
            const set = try witnessesFor(
                declaring,
                callee.declaration,
                selected.param,
                selected.path,
                callee_view,
                state,
            );
            return try project(cache, state, callee, selected, set);
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
) Error!Effect {
    const view = viewFor(cache, callee) orelse return mergeAll(set);
    var own: Effect = .read_only;
    var advisory: Effect = .read_only;
    var selected_buffer: [1]Ast.Node.Index = undefined;
    var selected: Ast.Node.Index = undefined;
    var have_selected = false;
    for (set) |witness| {
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
        var other_buffer: [1]Ast.Node.Index = undefined;
        const other = view.callArgumentIn(&other_buffer, callee.call_node, witness.param) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => null,
        } orelse {
            advisory = merge(advisory, witness.effect);
            continue;
        };
        if (!have_selected) {
            selected = view.callArgumentIn(&selected_buffer, callee.call_node, selection.param) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => null,
            } orelse {
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
    const gpa = cache.gpa;
    if (state.path_text.items.len == 0) _ = try state.intern(gpa, "");
    const key: Key = .{
        .declaration = .{ .tree = cache.tree, .module = cache.module_id, .declaration = declaration },
        .parameter = parameter,
        .path = try state.intern(gpa, path),
        .context = contextOf(view),
    };
    try state.charge();
    if (state.sets.get(key)) |set| return set;
    if (state.active.contains(key)) return unknown_set;
    if (state.depth == max_depth) return state.failure(.readonly_call_depth, max_depth, state.depth);
    var buffer: [1]Ast.Node.Index = undefined;
    // A body this document cannot read — an extern declaration, or a
    // prototype the closed scanner cannot decode — is a canonical record and
    // no effect at all.
    const proto = tokens.fnProto(cache.tree, &buffer, declaration) orelse return unknown_set;
    const body = tokens.bodyOf(cache.tree, declaration) orelse return unknown_set;
    const formals = formalCount(cache.tree, proto);
    if (parameter < global_only and parameter >= formals) return unknown_set;
    try state.charge();
    try state.active.put(gpa, key, {});
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
        .body = body,
        .proto = proto,
        .parameter = parameter,
        .path_text = state.text(key.path),
        .queried_name = if (parameter < global_only) formalNameToken(cache.tree, proto, parameter) else null,
        .view = view,
        .state = state,
    };
    var scan = call_effects.Scan.init(cache.tree, declaration, frame.currentBindings());
    var raw: std.ArrayListUnmanaged(Raw) = .empty;
    defer raw.deinit(gpa);
    while (true) {
        // Resolving a callee can build another body's bindings and grow the
        // table, so the scan's own pointer is refreshed before every step.
        scan.bindings = frame.currentBindings();
        const event = (try scan.next()) orelse break;
        try state.charge();
        switch (event) {
            .node => |node| frame.note(node),
            .call => |node| try callWitness(&frame, &raw, node),
            .write => |w| try writeWitness(&frame, &raw, w.node, w.target, w.value),
            .write_or_unknown => |node| try opaqueWitness(&frame, &raw, node),
        }
    }
    var list: std.ArrayListUnmanaged(Witness) = .empty;
    // `defer`, not `errdefer`: the success path below releases the list too,
    // once its contents have been copied into the memo arena.
    defer list.deinit(gpa);
    for (raw.items) |entry| {
        if (entry.operand) |operand| {
            if (try frame.discharged(entry.at.?, operand)) continue;
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
    // Publishing the memo is a cache write, not part of the answer: a table
    // that could not grow costs a later query one re-derivation, never the
    // caller a fact this scan has already completed.  Every OOM on the way
    // here — materialising the set, owning a path, growing the arena — still
    // travels out, because nothing was completed.
    state.sets.put(gpa, key, frozen) catch {};
    return frozen;
}

/// The answer for a body nothing can be read out of, and for a cycle.  Both
/// are the same statement: this analysis was shown nothing about the storage,
/// which is precisely what is not known.
const unknown_set: []const Witness = &[_]Witness{.{
    .param = unrooted_param,
    .path = root_path,
    .effect = .unknown,
}};

/// One body being scanned for one question about it.
const Frame = struct {
    cache: *FileCache,
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

    /// Does this body PROVE that the storage `operand` names is not the asked
    /// one?  Only a positively proved private construction answers that; the
    /// same storage, an incoming field, a copied header, publication, an
    /// unsupported shape and a cycle all answer "may share".
    fn discharged(self: *Frame, at: Ast.Node.Index, operand: Ast.Node.Index) Error!bool {
        if (self.parameter >= global_only) return false;
        const selected = self.selected orelse return false;
        try self.state.charge();
        // The path is left to the alias query: it derives the operand's own
        // chain itself, and an alias-resolved path added here would be
        // counted twice.
        return !try storage_alias.mayShareStorageAt(self.cache, at, .{
            .node = operand,
            .path = "",
        }, .{
            .node = selected,
            .path = self.path_text,
        }, .reachable_storage, .{
            // The frame the operands are written in, and this query's own
            // counter: one allowance covers the whole recursive walk, and no
            // edge starts a fresh one.
            .frame = frameOf(self.view),
            .remaining = self.state.counter(),
        });
    }

    fn append(self: *Frame, raw: *std.ArrayListUnmanaged(Raw), entry: Raw) Error!void {
        try self.state.charge();
        try raw.append(self.cache.gpa, entry);
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
        const verdict = self.meet(origin);
        if (verdict == .none) return;
        const owner = switch (origin) {
            .formal => |formal| formal,
            .unrooted, .private_value, .private_storage => null,
        };
        const param: u32 = if (owner) |formal| formal.param else unrooted_param;
        const base: []const u8 = if (owner) |formal| formal.path else "";
        const path = try self.joinPath(base, suffix);
        try self.append(raw, .{
            .param = param,
            .path = path,
            .effect = severity,
            .operand = if (verdict == .own) null else operand,
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

fn relate(frame: *Frame, node: Ast.Node.Index, depth: u32) Error!Origin {
    if (depth == max_depth) return frame.state.failure(.readonly_call_depth, max_depth, depth);
    try frame.state.charge();
    const cache = frame.cache;
    const tree = cache.tree;
    if (tokens.rootIdentifier(tree, node)) |root| {
        const token = tree.nodeMainToken(root);
        if (frame.currentBindings().findAt(tree.tokenSlice(token), token)) |binding| {
            if (binding.origin != .param) {
                // The binding pointer is not held across the escape index
                // build: resolving it can grow the table this one lives in.
                const name = binding.name;
                const name_token = binding.name_token;
                const escapes = try cache.escapeRoots(frame.body);
                for (escapes.writes) |write| {
                    try frame.state.charge();
                    if (write.declares or write.token <= name_token or write.token >= token) continue;
                    if (!std.mem.eql(u8, write.name, name)) continue;
                    const assigned = frame.currentBindings().findAt(write.name, write.token) orelse return .unrooted;
                    if (assigned.name_token == name_token) return .unrooted;
                }
            }
        }
    }
    const owner = try fn_summary.ownerOfExpr(frame.state.scratchAllocator(), tree, frame.proto,
        frame.currentBindings(), tree.firstToken(node), tree.lastToken(node), 0);
    switch (owner) {
        .param => |path| return .{ .formal = path },
        .unknown => {},
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
            const followed = try relate(frame, rhs, depth + 1);
            return switch (followed) {
                .private_value => .private_storage,
                else => followed,
            };
        },
        .address_of, .deref, .@"try" => return relate(frame, tree.nodeData(node).node, depth + 1),
        .unwrap_optional, .grouped_expression =>
            return relate(frame, tree.nodeData(node).node_and_token[0], depth + 1),
        .array_access => return relate(frame, tree.nodeData(node).node_and_node[0], depth + 1),
        .field_access => return relate(frame, tree.nodeData(node).node_and_token[0], depth + 1),
        .slice_open, .slice, .slice_sentinel => {
            const slice = tree.fullSlice(node).?;
            return relate(frame, slice.ast.sliced, depth + 1);
        },
        .call, .call_one, .call_comma, .call_one_comma => return resultOrigin(frame, node, depth + 1),
        .number_literal, .char_literal, .string_literal, .multiline_string_literal, .enum_literal, .error_value =>
            return .private_value,
        else => {
            var children = Iterator.init(tree, node);
            var result: Origin = .private_value;
            var found = false;
            while (children.next(tree)) |child| {
                found = true;
                result = combineOrigins(result, try relate(frame, child, depth + 1));
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
    var buffer: [1]Ast.Node.Index = undefined;
    const call = cache.tree.fullCall(&buffer, node) orelse return .unrooted;
    const callee = (try grow_analysis.actualCalleeOf(cache, callCalleeToken(cache.tree, call), frameOf(frame.view))) orelse
        return .unrooted;
    const declaring = (try cacheFor(cache, callee)) orelse return .unrooted;
    if (tokens.bodyOf(callee.tree, callee.declaration) == null) return .unrooted;
    const summary = (declaring.summaryOfResolvedMethod(.{
        .tree = callee.tree, .module = callee.handle.module, .fn_decl = callee.declaration,
    }) catch |err| return err) orelse return .unrooted;
    const view = viewFor(cache, callee) orelse return .unrooted;
    var arguments_buffer: [1]Ast.Node.Index = undefined;
    const arguments = view.callArgumentsOf(&arguments_buffer, node) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return .unrooted,
    } orelse return .unrooted;
    var result: Origin = .private_value;
    const count = arguments.arguments.len + @intFromBool(arguments.receiver != null);
    for (0..count) |index| {
        const dependency = summary.returnedParamDependency(@intCast(index));
        if (dependency == false) continue;
        const argument = argumentAt(arguments, @intCast(index)) orelse return .unrooted;
        result = combineOrigins(result, try relate(frame, argument, depth));
    }
    if (!summary.result_params_complete) return combineOrigins(result, .unrooted);
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
    const origin = try relate(frame, target, 0);
    var severity = storeSeverity(frame, node, target, value);
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

fn storeSeverity(frame: *Frame, node: Ast.Node.Index, target: Ast.Node.Index, value: Ast.Node.Index) Effect {
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
    if (!isKnownScalarType(frame, target)) return .may_invalidate;
    if (!valueIsNonPoisonScalar(frame, value)) return .may_invalidate;
    return .writes_without_invalidation;
}

/// Does the ACTUAL frame resolve this expression's own type to a narrow
/// primitive?
///
/// Asked through the view the expression is written in, so an instantiated
/// generic's parameter type is the type this call really carried and never a
/// bare generic form.  A pointer, slice, optional, struct, union, call result,
/// and anything the engine cannot answer are all refused.
fn isKnownScalarType(frame: *Frame, node: Ast.Node.Index) bool {
    const view = frame.view orelse return false;
    if (view.isBoolType(node) catch return false) |is_bool| {
        if (is_bool) return true;
    }
    if (view.isEnumType(node) catch return false) |is_enum| {
        if (is_enum) return true;
    }
    if (view.intInfo(node) catch return false) |info| {
        return info.bits < @bitSizeOf(usize);
    }
    if (view.floatBits(node) catch return false) |width| {
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
fn elementIsScalarElement(frame: *Frame, node: Ast.Node.Index) bool {
    const view = frame.view orelse return false;
    const resolver = view.resolverOf();
    var current = (view.typeOfNode(node) catch return false) orelse return false;
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
    const element = (resolver.normalizedType(child) catch return false) orelse return false;
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
fn valueIsNonPoisonScalar(frame: *Frame, node: Ast.Node.Index) bool {
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
    if (operands.len == 0) {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
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
            var poison = false;
            for (operands[1..]) |operand| {
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
            valueIsNonPoisonScalar(frame, operands[value_index]) and
            elementIsScalarElement(frame, destination)) severity = .writes_without_invalidation;
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

/// The token that identifies one call in the cache's own call index.
/// `FileCache.getCallIndex` files every call under
/// `nodeMainToken(call.ast.fn_expr)`, and `resolveActualCallee` looks a call
/// up under exactly that key — so a container-qualified call (`map.get(key)`)
/// is named by the token of its `.`, not by the method name at the end of the
/// expression.  Asking under the last token instead misses every qualified
/// call, and a miss reads as "this call resolves to nothing", which is how a
/// method call came to be charged as unknown storage.
fn callCalleeToken(tree: *const Ast, call: Ast.full.Call) Ast.TokenIndex {
    return tree.nodeMainToken(call.ast.fn_expr);
}

/// What one call does, in this body's coordinates.  Every operand the call was
/// handed is followed to the storage it names, and every witness the callee
/// produced is re-expressed here; storage a callee can reach without being
/// handed anything of ours is charged on its own.
fn callWitness(frame: *Frame, raw: *std.ArrayListUnmanaged(Raw), node: Ast.Node.Index) Error!void {
    const cache = frame.cache;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = cache.tree.fullCall(&buffer, node) orelse {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    };
    const callee = (try grow_analysis.actualCalleeOf(cache, callCalleeToken(cache.tree, call), frameOf(frame.view))) orelse {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    };
    const declaring = (try cacheFor(cache, callee)) orelse {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    };
    const view = viewFor(cache, callee) orelse {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    };
    var arguments_buffer: [1]Ast.Node.Index = undefined;
    const arguments = view.callArgumentsOf(&arguments_buffer, node) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => {
            try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
            return;
        },
    } orelse {
        try frame.append(raw, .{ .param = unrooted_param, .path = root_path, .effect = .unknown });
        return;
    };
    const count = arguments.arguments.len + @intFromBool(arguments.receiver != null);
    const callee_view = bodyView(declaring, callee, frame.state);
    if (count != 0) {
        const append = view.stdCollectionAppendOf(call.ast.fn_expr, count - 1) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => .no,
        };
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
    for (0..count) |index| {
        try frame.state.charge();
        const argument = argumentAt(arguments, @intCast(index)) orelse continue;
        const origin = try relate(frame, argument, 0);
        switch (origin) {
            .private_value => {
                // A value this body was handed holds no storage of the
                // caller's, so whatever the callee does to it is its own.
                continue;
            },
            else => {},
        }
        const sub = try witnessesFor(
            declaring,
            callee.declaration,
            @intCast(index),
            "",
            callee_view,
            frame.state,
        );
        try reexpress(frame, raw, origin, sub, arguments, node, @intCast(index));
    }
    // A known callee can reach globally aliased storage without receiving any
    // relevant operand.  That possibility is asked separately: formal flow
    // never proves nonaliasing of caller storage, and an opaque callee cannot
    // discharge it.
    const globals = try witnessesFor(declaring, callee.declaration, global_only, "", callee_view, frame.state);
    for (globals) |witness| {
        try frame.append(raw, .{
            .param = unrooted_param,
            .path = root_path,
            .effect = witness.effect,
        });
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
        .grouped_expression, .unwrap_optional =>
            return isUndefinedValue(frame, tree.nodeData(node).node_and_token[0]),
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
    // An intrinsic this table does not know is charged at full strength.
    try std.testing.expectEqual(Effect.unknown, try at(typed, "shouted", ""));
}

/// One complete query, through whichever allocator it is handed — so the
/// refusal point can be swept across the whole build.
fn effectUnderFailing(
    gpa: std.mem.Allocator,
    source: [:0]const u8,
) !?Effect {
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const declaration = (try typed.cache.fileModel()).findFn("bump").?.fn_decl;
    return try declarationEffect(typed.cache, declaration, .{ .param = 0, .path = "first" });
}

test "a completed query keeps its answer when only the memo filing runs out" {
    const source: [:0]const u8 =
        \\const Pair = struct { first: u32, second: u32 };
        \\fn bump(pair: *Pair) void { pair.first += 1; }
    ;
    const gpa = std.testing.allocator;
    const expected = (try effectUnderFailing(gpa, source)) orelse return error.TestExpectedEffect;
    try std.testing.expectEqual(Effect.writes_without_invalidation, expected);
    var fail_index: usize = 0;
    while (fail_index < 96) : (fail_index += 1) {
        var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = fail_index });
        const answer = effectUnderFailing(failing.allocator(), source) catch |err| switch (err) {
            // Refusing an allocation before the fact is complete travels out;
            // nothing was finished, so nothing is published or returned.
            error.OutOfMemory => continue,
            else => return err,
        };
        // A fact this scan DID complete is returned even when the table that
        // would have filed it could not grow.
        try std.testing.expectEqual(expected, answer.?);
    }
}

test "a sibling field is charged and a field no site names is not" {
    const source: [:0]const u8 =
        \\const Pair = struct { first: u32, second: u32, third: u32 };
        \\fn bump(pair: *Pair) void { pair.first += 1; }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const declaration = (try typed.cache.fileModel()).findFn("bump").?.fn_decl;
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
        try declarationEffect(typed.cache, declaration, .{ .param = 0, .path = "first" }),
    );
    // Two paths that only share a root may name the same buffer, so the
    // sibling's store is charged against this one rather than read as proof
    // that nothing else in the object moved.
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
        try declarationEffect(typed.cache, declaration, .{ .param = 0, .path = "second" }),
    );
    try std.testing.expectEqual(
        Effect.read_only,
        try declarationEffect(typed.cache, declaration, .{ .param = 0, .path = "third" }),
    );
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
        \\    const scratch = &[_]u8{0};
        \\    @memset(scratch, 0);
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
    // A path that only shares a root with the written one may still name the
    // same buffer, so the callee's store is charged here rather than dropped.
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
        try declarationEffect(typed.cache, use, .{ .param = 0, .path = "inner.other" }),
    );
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
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

test "a callee that writes another formal charges that argument, not the call" {
    const source: [:0]const u8 =
        \\fn store(target: *u32, value: *u32) void { value.* = 0; }
        \\fn use(target: *u32) void {
        \\    const spare = &[_]u32{0};
        \\    store(target, spare);
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

test "the same storage passed twice is not a disjoint pair" {
    const source: [:0]const u8 =
        \\fn store(target: *u32, value: *u32) void { value.* = 0; }
        \\fn use(target: *u32) void { store(target, target); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const declaration = (try typed.cache.fileModel()).findFn("use").?.fn_decl;
    try std.testing.expectEqual(Effect.may_invalidate, try declarationEffect(typed.cache, declaration, .{ .param = 0 }));
}

test "a selection path is the producer's own copy, not the caller's buffer" {
    const source: [:0]const u8 =
        \\const Cell = struct { value: u32, other: u32 };
        \\fn bump(cell: *Cell) void { cell.value += 1; }
        \\fn nothing(cell: *Cell) void { _ = cell.other; }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    const model = try typed.cache.fileModel();
    const bump = model.findFn("bump").?.fn_decl;
    const nothing = model.findFn("nothing").?.fn_decl;
    var owned: [5]u8 = undefined;
    @memcpy(&owned, "value");
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
        try declarationEffect(typed.cache, bump, .{ .param = 0, .path = owned[0..] }),
    );
    // The caller's buffer changes under the producer.  A borrowed memo key
    // would now read as a path nobody asked about, and the entry filed under
    // it would answer for whatever the buffer spells.
    @memset(&owned, 'x');
    try std.testing.expectEqual(
        Effect.writes_without_invalidation,
        try declarationEffect(typed.cache, bump, .{ .param = 0, .path = "value" }),
    );
    // A declaration that writes nothing answers read only, and it must not be
    // answered from the entry the mutated buffer now aliases.
    try std.testing.expectEqual(
        Effect.read_only,
        try declarationEffect(typed.cache, nothing, .{ .param = 0, .path = "xxxxx" }),
    );
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
            // A declaration's canonical identity is (tree, module): with the
            // cache's default, every same-file question is asked of a
            // document nobody opened.
            cache.module_id = resolver.handle.module;
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
        var buffer: [1]Ast.Node.Index = undefined;
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
        var buffer: [1]Ast.Node.Index = undefined;
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
        var buffer: [1]Ast.Node.Index = undefined;
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
        \\    @extern(*const fn ([]u8) void, .{ .name = "foreign_write" });
        \\    _ = bytes;
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
    }

    // ── 7. A real map: one accessor provably reads, one this run cannot
    //      finish reading, and one that writes ─────────────────────────────

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
        // `getIndex` walks metadata and asks a context to hash.  Every
        // intrinsic on that path is a compiler directive that stores
        // nothing, so the whole chain folds to `read_only`.
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

        // And the declaration is reached through the resolver, in the
        // document and module the resolver proved — the identity case 1 pins,
        // reached through a generic instantiation rather than a second name.
        const record = try fixture.recordAt("getContext", 1);
        try std.testing.expect(fixture.ast() != record.callee.tree);
        try std.testing.expectEqual(fixture.cache.module_id, record.callee.handle.module);
    }

    // ── 9. Unrooted: what a call reaches that it was not handed ───────────

    const unrooted_source: [:0]const u8 =
        \\const std = @import("std");
        \\const Cell = struct { value: u32 };
        \\
        \\// Storage this file OWNS.  Not a typed scalar in some object: a
        \\// live allocation with an owner, which a release actually ends.
        \\var held: []u8 = @constCast(&[_]u8{});
        \\var held_allocator: std.mem.Allocator = undefined;
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
        \\fn driveShared() void {
        \\    releaseShared();
        \\}
        \\
        \\fn driveSharedMarked(marker: u32) void {
        \\    releaseSharedMarked(marker);
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
        \\    reset(cell, .{ .value = 0 });
        \\    reset(tag, .{ .id = 0 });
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
        try std.testing.expect((try fixture.effectAt("reset", 0, .{ .param = 0 })) != .read_only);
        try std.testing.expect((try fixture.effectAt("reset", 1, .{ .param = 0 })) != .read_only);

        // `comptime T` is not an argument, so both formals are written
        // exactly as the call spelled them.
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
        var buffer: [1]Ast.Node.Index = undefined;
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