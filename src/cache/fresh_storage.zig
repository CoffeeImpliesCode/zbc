//! The fresh-storage prover: does an initializer build storage this
//! expression laid out, or does it hand back a header somebody else is
//! holding?
//!
//! `fn_summary` refuses to answer that from spelling: `Foo.init` may
//! return a global, and a struct literal may fill an omitted field
//! from a default that reads one.  The answer comes from DECLARATIONS
//! instead — the declaration a constructor call resolves to, a project
//! constructor's own returns, and the type's own field list and those
//! fields' defaults — and everything else stays unknown, which is what
//! the caller charges as unattributed storage.
//!
//! NONE OF THAT IS ABOUT A FILE'S PER-FILE STATE, so none of it belongs
//! on the cache that holds it.  `FileCache` keeps every table the walk
//! reads and writes — the verdicts memo, the visiting set, the summary
//! arena — and each function here takes the cache it reads as its
//! first argument rather than holding a second reference to any of it.
//!
//! THE WALK IS CARRIED AS ONE VALUE.  `FreshWalk` is the initializer
//! a question is about together with how many levels have been spent
//! reaching it, because every hop changes both together; the memo is
//! keyed by that same depth, so the budget's meaning is unchanged.

const std = @import("std");
const Ast = std.zig.Ast;

const file_cache = @import("file_cache.zig");
const file_model = @import("../model/file_model.zig");
const fn_summary = @import("../model/fn_summary.zig");
const tokens = @import("../ast/tokens.zig");
const local_bindings = @import("../model/local_bindings.zig");
const type_query = @import("../model/type_query.zig");
const type_engine = @import("type_engine");
const grow_analysis = @import("grow_analysis.zig");

/// Everything a freshness walk can fail at.  It is the cache's own summary
/// set, because this is how a walk fails: it reads a call through
/// `canonicalCall`, and that read models the callee's document before it
/// summarises it — so a callee in a source `std.zig.Ast` cannot address is a
/// walk that cannot answer, exactly as an allocation that ran out is.
const FreshError = file_cache.SummaryError;

const FileCache = file_cache.FileCache;
const DeclKey = file_cache.DeclKey;
const TokenRange = FileCache.TokenRange;
const ResolvedType = FileCache.ResolvedType;


/// One question the fresh-storage prover is answering: the initializer
/// it is about, and how many levels of the walk have been spent
/// reaching it.
///
/// THE PAIR IS ONE VALUE because every hop changes both together — a
/// level is spent to ask about an expression — and a caller that
/// passed them as two arguments could reorder them without a type
/// error.  `depth` counts levels SPENT, so it maps one-to-one onto
/// `FreshKey.depth` and onto every `depth > max_fresh_depth` bound
/// below: nothing about the budget's meaning changes, only where it
/// lives.
pub const FreshWalk = struct {
    claim: fn_summary.FreshClaim,
    depth: u8,
    /// Borrowed work allowance of an enclosing storage query. Null preserves
    /// the original depth-only freshness walk; no new global cap is imposed.
    remaining: ?*u32 = null,
    /// Borrowed actual instantiation context; its original resolver owns every
    /// type used by this proof until the root FileCache is torn down.
    frame: ?type_engine.TypeResolver.ResolutionFrame = null,

    /// The outermost question about `claim`.
    pub fn root(claim: fn_summary.FreshClaim) FreshWalk {
        return .{ .claim = claim, .depth = 0 };
    }

    /// Has this walk spent the whole bound?
    pub fn spent(self: FreshWalk) bool {
        return self.depth > max_fresh_depth;
    }

    /// The same initializer one level further in, or null once the
    /// bound is spent — which is exactly where the level it guards
    /// used to answer `false`.
    pub fn deeper(self: FreshWalk) ?FreshWalk {
        if (self.spent()) return null;
        var next = self;
        next.depth += 1;
        return next;
    }

    /// A DIFFERENT initializer one level further in: what a struct
    /// literal's value and a declaration's `return` ask about.
    pub fn about(self: FreshWalk, claim: fn_summary.FreshClaim) ?FreshWalk {
        if (self.spent()) return null;
        var next = self;
        next.claim = claim;
        next.depth += 1;
        return next;
    }
};

/// What a freshness verdict is filed under: the initializer's
/// token range — what NAMES the expression — and the depth the
/// walk that answered it was given, which is what says how much
/// of the budget was left when it answered.
pub const FreshKey = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    depth: u8,
    tree: *const Ast,
    module: type_engine.ModuleId,
    origin: ?type_engine.TypeResolver.ActualType,
};

pub const FreshKeyContext = struct {
    pub fn hash(_: FreshKeyContext, key: FreshKey) u64 {
        var hasher: std.hash.Wyhash = .init(0);
        std.hash.autoHash(&hasher, key.first);
        std.hash.autoHash(&hasher, key.last);
        std.hash.autoHash(&hasher, key.depth);
        std.hash.autoHash(&hasher, key.tree);
        std.hash.autoHash(&hasher, key.module);
        std.hash.autoHash(&hasher, key.origin != null);
        if (key.origin) |origin| std.hash.autoHash(&hasher, origin.hash64());
        return hasher.final();
    }

    pub fn eql(_: FreshKeyContext, left: FreshKey, right: FreshKey) bool {
        if (left.first != right.first or left.last != right.last or
            left.depth != right.depth or left.tree != right.tree or
            left.module != right.module or (left.origin == null) != (right.origin == null)) return false;
        if (left.origin) |origin| return origin.eql(right.origin.?);
        return true;
    }
};

/// Depth cap for the declaration walk: a constructor may build
/// through another constructor, and each level costs another
/// pass over a body.
const max_fresh_depth = 4;

/// Does `claim` provably build storage this fn built for itself?
///
/// Proves expression-laid-out buffers, actual SDK allocation results, and
/// constructors whose every returned value is independently owned. Aggregate
/// fields are checked separately: address-free values can be copied, but each
/// address-bearing field needs independent allocation or independent literal
/// storage. Omitted fields keep the no-name, fully initialized default contract.
///
/// Calls use the internal canonical declaration query. Foreign returns are
/// read in the cache of their actual source tree and module, with that source's
/// resolver and imports. A local header, allocation elsewhere in the body,
/// method spelling, or incomplete forwarding metadata is never ownership.
///
/// What is NOT proved is a factory that hands back storage somebody
/// else holds.  Every route requires EVERY `return` of the
/// declaration to be proved fresh, so a constructor that returns a
/// borrow, copies a header out of a parameter, or escapes a cached
/// object is refused exactly as it was before.
pub fn provesFreshStorage(
    cache: *FileCache,
    claim: fn_summary.FreshClaim,
    remaining: ?*u32,
) FreshError!bool {
    return freshStorageAt(cache, .{ .claim = claim, .depth = 0, .remaining = remaining });
}

/// Unknown identity or provenance leaves a claim unproved. Resource failures
/// are not verdicts: allocation failure and attributed analysis-budget
/// exhaustion propagate without entering the memo.
pub fn freshStorageAt(
    cache: *FileCache,
    walk: FreshWalk,
) FreshError!bool {
    if (walk.claim.first > walk.claim.last) return false;
    if (walk.spent()) return false;
    if (walk.frame) |frame| {
        if (&frame.handle.document.tree != cache.tree or frame.handle.module != cache.module_id) return false;
    }
    try charge(walk.remaining);
    const key: FreshKey = .{
        // The actual function type additionally carries caller-bound arguments.
        // Container-only proofs can use the frame's complete container type.
        .first = walk.claim.first,
        .last = walk.claim.last,
        .depth = walk.depth,
        .tree = cache.tree,
        .module = cache.module_id,
        .origin = if (walk.frame) |frame| frame.actual_type orelse frame.container_type else null,
    };
    if (cache.fresh_storage.get(key)) |cached| return cached;
    // Written only once the walk is done, so a claim that reaches
    // itself cannot read a half-finished verdict.
    const verdict = try resolveFreshStorage(cache, walk);
    try cache.fresh_storage.put(cache.gpa, key, verdict);
    return verdict;
}

pub fn resolveFreshStorage(cache: *FileCache, walk: FreshWalk) FreshError!bool {
    const claim = walk.claim;
    if (try independentValue(cache, claim, walk)) |verdict| return verdict;
    if (try sdkCollectionBuildsFreshStorage(cache, walk)) return true;
    const tree = cache.tree;
    const tags = tree.tokens.items(.tag);
    var first = claim.first;
    const last = claim.last;
    if (if (walk.frame) |frame| frame.resolver else cache.zls) |resolver| {
        if (cache.nodeForExactSpan(first, last)) |node| {
            const type_node = if (claim.type_first) |type_first|
                cache.nodeForExactSpan(type_first, claim.type_last.?)
            else
                null;
            try charge(walk.remaining);
            const empty = if (walk.frame) |frame| frame.stdCollectionEmptyOf(node, type_node) else resolver.stdCollectionEmptyOf(node, type_node);
            if (empty catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => false,
            }) {
                return true;
            }
        }
    }
    // `&[_]T{ … }` / `&.{}`: a buffer this expression lays out, so
    // no binding can be holding it yet.
    if (first < last and tags[first] == .ampersand) {
        const next = first + 1;
        const anonymous_comptime = tags[next] == .period and
            next + 1 <= last and tags[next + 1] == .l_brace;
        if (tags[last] == .r_brace and (tags[next] == .l_bracket or anonymous_comptime)) {
            return true;
        }
    }
    // `&x` and `try x` wrap an expression without changing where
    // the value came from.
    while (first <= last and (tags[first] == .ampersand or tags[first] == .keyword_try)) {
        try charge(walk.remaining);
        first += 1;
    }
    if (first > last) return false;
    // `@import("…")` names a module.  A module holds no header and
    // no buffer, so a claim resting on one is not an unplaced
    // header that may alias somebody else's — there is nothing to
    // alias.  Reading it as unproved instead charges every name
    // reached THROUGH a module: the receiver of
    // `std.ArrayList(u32).initCapacity(…)`, and an argument spelled
    // `std.heap.page_allocator`, both become "may be shared
    // storage" when neither ever was.
    if (tokens.importLiteralFromTokens(tree, first, last) != null) return true;
    if (tags[first] == .period) {
        // `.{ … }` names no type, so only the binding's own
        // declaration can say what it left out.
        if (first + 1 > last) return false;
        if (tags[first + 1] != .l_brace or tags[last] != .r_brace) return false;
        const declared: ?TokenRange = if (claim.type_first) |tf| .{
            .first = tf,
            .last = claim.type_last.?,
        } else null;
        return try literalBuildsFreshStorage(cache, declared, first + 2, last - 1, walk);
    }
    if (tags[first] != .identifier) return false;
    // Walk the type path, `t` naming one of its segments.  A `(`
    // group after a segment is GENERIC ARGUMENTS while the path
    // CONTINUES past it — `std.array_list.Managed(u32).init` — and
    // the CONSTRUCTOR'S OWN ARGUMENT LIST when the group is the
    // last thing in the expression.  Only a group that reaches
    // `last` can be the latter, and only that one names a call
    // whose declaration answers the question; a group the path
    // walks through is stepped over and the walk continues.
    var t = first;
    while (true) {
        try charge(walk.remaining);
        if (t + 1 > last) return false;
        switch (tags[t + 1]) {
            .period => {
                t += 2;
                if (t > last or tags[t] != .identifier) return false;
                if (t + 1 > last) return false;
                if (tags[t + 1] == .l_paren) {
                    const rp = tokens.matchParen(tags, t + 1, last) orelse return false;
                    if (rp == last) {
                        // `t` is the constructor and `t - 1` its
                        // `.`, so the TYPE it is reached on is
                        // what precedes them: the method segment
                        // is not part of that type's own name.
                        if (t < first + 2) return false;
                        return try constructorBuildsFreshStorage(cache, 
                            .{ .first = first, .last = t - 2 },
                            t,
                            .{ .first = first, .last = last },
                            walk,
                        );
                    }
                    t = rp;
                }
            },
            .l_brace => {
                if (tags[last] != .r_brace) return false;
                return try literalBuildsFreshStorage(cache, .{ .first = first, .last = t }, t + 2, last - 1, walk);
            },
            // Canonical calls were considered above. Unresolved expressions
            // cannot claim freshness merely because their spelling is familiar.
            else => return false,
        }
    }
}

/// `<Type>.<ctor>(…)`, whose type path is `type_path`, whose
/// constructor name is at `ctor`, and whose whole call is `call`.
///
/// What the callee hands back is the question, so it is answered
/// from the DECLARATION the call resolves to, never from the name
/// the file spelled.
///
/// The canonical declaration is tried first. Syntax-only callers retain the
/// existing local type-declaration route, at the same structural depth. When
/// a type engine is present, an unresolved call stays unresolved: no guessed
/// declaration may overrule the canonical query.
///
/// `type_path` and `ctor` belong to that fallback and to nothing
/// else.  Nothing here widens what a constructor may return: both
/// routes prove a value fresh only when EVERY `return` of the
/// declaration is fresh, so a factory that hands back a borrow, a
/// cached header, or a pointer into something else is still refused.
pub fn constructorBuildsFreshStorage(
    cache: *FileCache,
    type_path: TokenRange,
    ctor: Ast.TokenIndex,
    call: TokenRange,
    walk: FreshWalk,
) FreshError!bool {
    if (walk.spent()) return false;
    if (try standardListConstructor(cache, call, walk) and try standardListFieldsIndependent(cache, call, walk)) return true;
    if (try resolvedCalleeBuildsFreshStorage(cache, call, walk)) return true;
    if (cache.zls != null) return false;
    const type_name = (try typePathName(cache, type_path.first, type_path.last, walk.remaining)) orelse return false;
    const resolved = (try resolveDeclaredType(cache, type_name, walk.depth + 1, walk.remaining)) orelse return false;
    // Only this file's own declarations are read on this route; see
    // the note on `provesFreshStorage`.  A model that cannot be
    // built leaves the claim unproved, which is the direction this
    // walk is allowed to fail in: the caller charges unknown
    // storage.
    const model = cache.fileModel() catch |err| return resourceFailure(err);
    if (resolved.model != model) return false;
    const method = resolved.info.findMethod(cache.tree.tokenSlice(ctor)) orelse return false;
    return declBuildsFreshStorage(cache, resolved.model.tree, method.fn_decl, walk.deeper() orelse return false);
}

/// Read the exact canonical callee in its declaring document/module. Every
/// return must correlate to storage made by that callee. Forwarding a formal
/// stays unproved even when the caller itself allocated the actual argument:
/// copying that header is not a new allocation. Consumers can separately
/// discharge other arguments only from complete canonical dependency metadata.
pub fn resolvedCalleeBuildsFreshStorage(
    cache: *FileCache,
    call: TokenRange,
    walk: FreshWalk,
) FreshError!bool {
    if (walk.spent()) return false;
    const canonical = (try canonicalCall(cache, call, walk)) orelse return false;
    const callee = canonical.callee;
    const declaring = (try canonical.declaringCache(cache)) orelse return false;
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    if (!try allocatorArgumentsSafeForResult(cache, canonical, walk)) return false;
    var next = walk.deeper() orelse return false;
    next.frame = resolver.frameForFunction(callee.reference);
    return declBuildsFreshStorage(declaring, callee.tree, callee.declaration, next);
}

fn canonicalCall(cache: *FileCache, call: TokenRange, walk: FreshWalk) FreshError!?FileCache.ActualCallSummary {
    try charge(walk.remaining);
    const node = cache.nodeForExactSpan(call.first, call.last) orelse return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const expression = cache.tree.fullCall(&buffer, node) orelse return null;
    return cache.actualCallSummaryAt(calleeQueryToken(cache.tree, expression), walk.frame);
}

/// The token a cache query addresses this call by.  The call index is
/// keyed on `Ast.nodeMainToken` of the callee expression, which for a
/// method call is the `.` introducing the method name; a query that
/// looked the call up by the `lastToken` of the same expression named a
/// token the index never holds, and every method call — every SDK
/// constructor, append, and store — read as unresolved.
pub fn calleeQueryToken(tree: *const Ast, call: Ast.full.Call) Ast.TokenIndex {
    return tree.nodeMainToken(call.ast.fn_expr);
}

/// Is `call` a constructor of a standard-library list, proven from
/// the declaration the compiler resolved FOR IT?
///
/// `std/array_list.zig`'s `init` returns a header over no storage
/// and its `initCapacity` one over memory that call allocated, so
/// growing either moves only what the constructor's own caller
/// owns.  That is a fact about the DECLARATION, so it is read
/// there: the document it is declared in must be this toolchain's
/// own `std/array_list.zig`, its own name must be one of the
/// constructors, and its own parameter count must be EXACTLY what
/// the call passes.  A project type that spells the same name never
/// matches, and neither does a file that binds `std` to a module
/// of its own — its calls resolve to a different declaration or
/// to none at all.
pub fn standardListConstructor(cache: *FileCache, call: TokenRange, walk: FreshWalk) FreshError!bool {
    const canonical = (try canonicalCall(cache, call, walk)) orelse return false;
    const reference = canonical.callee;
    const tree = reference.tree;
    if (reference.fn_token + 1 >= tree.tokens.len) return false;
    const std_tree = (try toolchainArrayListTree(cache)) orelse return false;
    if (tree != std_tree) return false;
    const name_token = reference.fn_token + 1;
    if (tree.tokenTag(name_token) != .identifier) return false;
    const name = tree.tokenSlice(name_token);
    if (!std.mem.eql(u8, name, "init") and !std.mem.eql(u8, name, "initCapacity")) return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, reference.declaration) orelse return false;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const actual = cache.tree.fullCall(&call_buffer, reference.call_node) orelse return false;
    var declared: usize = 0;
    var parameters = proto.iterate(tree);
    while (parameters.next() != null) {
        try charge(walk.remaining);
        declared += 1;
    }
    if (declared != actual.ast.params.len) return false;
    var receiver_buffer: [1]Ast.Node.Index = undefined;
    const allocator = (try canonical.callArgumentFor(cache, &receiver_buffer, 0)) orelse return false;
    return allocatorOriginIsExternal(cache, allocator, walk, 0);
}

/// This toolchain's own `std/array_list.zig`, read through the
/// same document store the analyser itself resolves `@import("std")`
/// through.  `absent` records that this session has no toolchain to
/// read, so the answer is sought once rather than per claim.
pub fn toolchainArrayListTree(cache: *FileCache) !?*const Ast {
    switch (cache.std_list_tree) {
        .known => |tree| return tree,
        .absent => return null,
        .unknown => {},
    }
    const resolver = cache.zls orelse return null;
    const library = resolver.ctx.toolchain.zig_lib orelse {
        cache.std_list_tree = .absent;
        return null;
    };
    // `sourceHandle` addresses documents by absolute path; a
    // relative one is not a path this can read, not a toolchain.
    if (!std.fs.path.isAbsolute(library)) {
        cache.std_list_tree = .absent;
        return null;
    }
    const path = try std.fs.path.join(cache.gpa, &.{ library, "std", "array_list.zig" });
    defer cache.gpa.free(path);
    // A document this store will not serve is recorded once, so
    // the answer is not re-sought per claim.  Running out of
    // memory is not that: caching it would leave every later
    // claim in this session unable to resolve a constructor for a
    // reason that has nothing to do with the code under analysis,
    // so it is reported instead.  The store's own error set is
    // open-ended, so the retry is named rather than propagated by
    // value.
    const handle = resolver.ctx.sourceHandle(path, cache.module_id) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => {
            cache.std_list_tree = .absent;
            return null;
        },
    };
    // The document is a store-owned allocation reached through the
    // handle, so the address outlives the handle this function
    // received by value.
    cache.std_list_tree = .{ .known = &handle.document.tree };
    return &handle.document.tree;
}

/// `.{ … }` / `<Type>{ … }` over `[first, last]`.  `spelled` is the
/// type the path named; an anonymous literal falls back to the
/// type its binding declared.
pub fn literalBuildsFreshStorage(
    cache: *FileCache,
    spelled: ?TokenRange,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    walk: FreshWalk,
) FreshError!bool {
    const type_range = spelled orelse return false;
    const type_name = (try typePathName(cache, type_range.first, type_range.last, walk.remaining)) orelse return false;
    const resolved = (try resolveDeclaredType(cache, type_name, walk.depth + 1, walk.remaining)) orelse return false;
    if (!try actualOwnerMatches(cache, type_range, resolved, walk)) return false;
    return try literalFieldsFresh(cache, resolved, first, last, walk);
}

/// Every listed value of a struct literal is proved fresh or is
/// a value that reads no name, and every field of `resolved` the
/// literal left out is one the type gives a default.  An EMPTY
/// literal lists nothing at all, so its whole question is the
/// fields the type leaves to its own defaults.
pub fn literalFieldsFresh(
    cache: *FileCache,
    resolved: ResolvedType,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    walk: FreshWalk,
) FreshError!bool {
    for (resolved.info.fields) |field| {
        try charge(walk.remaining);
        if (try literalFieldValue(cache.tree, first, last, field.name, walk.remaining)) |value| {
            if (!try fieldValueFresh(cache, resolved, field, value, walk)) return false;
            continue;
        }
        // Defaults keep their original strict contract: no named storage and
        // no undefined sibling can be hidden by another field's allocation.
        if (!field.has_default) return false;
        const expr = (try fieldDefaultExpr(resolved.model.tree, field, walk.remaining)) orelse return false;
        if (resolved.model.tree == cache.tree) {
            if (!try fieldValueFresh(cache, resolved, field, expr, walk)) return false;
        } else if (!try readsNoName(resolved.model.tree, expr.first, expr.last, walk.remaining) or
            resolved.model.tree.tokenTag(expr.first) == .period) return false;
    }
    return true;
}


/// Does every `return` of this declaration hand back storage this
/// fn built?  A declaration with no return proves nothing: its
/// result comes from wherever its caller cannot see.
pub fn declBuildsFreshStorage(
    cache: *FileCache,
    tree: *const Ast,
    fn_decl: Ast.Node.Index,
    walk: FreshWalk,
) FreshError!bool {
    if (walk.spent()) return false;
    try charge(walk.remaining);
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buf, fn_decl) orelse return false;
    _ = tokens.bodyOf(tree, fn_decl) orelse return false;
    // `return .{ … };` names no type, so the declaration's own
    // return type is what says which fields it filled in.
    const return_type = valueReturnType(tree, proto.ast.return_type.unwrap());
    const key: DeclKey = .{ .tree = tree, .module = cache.module_id, .declaration = fn_decl };
    if (cache.fresh_visiting.contains(key)) return false;
    try cache.fresh_visiting.put(cache.gpa, key, {});
    defer _ = cache.fresh_visiting.remove(key);
    var returns: u32 = 0;
    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        try charge(walk.remaining);
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .@"return") continue;
        const value = tree.nodeData(node).opt_node.unwrap() orelse continue;
        const first = tree.firstToken(value);
        // A nested `fn`'s return is not this declaration's.
        if ((tokens.enclosingFnDecl(tree, first) orelse fn_decl) != fn_decl) continue;
        const next = walk.about(.{
            .first = first,
            .last = tree.lastToken(value),
            .type_first = if (return_type) |rt| tree.firstToken(rt) else null,
            .type_last = if (return_type) |rt| tree.lastToken(rt) else null,
        }) orelse return false;
        if (!try freshStorageAt(cache, next)) return false;
        if (!try @import("storage_alias.zig").allocationSurvivesHandoff(cache, value, tree.firstToken(node), .{
            .frame = walk.frame,
            .remaining = walk.remaining,
        })) return false;
        returns += 1;
    }
    return returns != 0;
}

/// The type `name` resolves to: one this project declares, in this
/// file or in one it imports.  `const List = std.ArrayList(u32);`
/// is followed to what `List` actually names.  Null when no
/// declaration here or in this project's reach carries that name —
/// the standard library included, whose types this tool never
/// reads as declarations.
pub fn resolveDeclaredType(cache: *FileCache, name: []const u8, depth: u8, remaining: ?*u32) FreshError!?ResolvedType {
    if (depth > max_fresh_depth) return null;
    try charge(remaining);
    if (cache.resolvedTypeAcrossImports(name)) |resolved| return resolved;
    const dot = std.mem.indexOfScalar(u8, name, '.');
    const head = if (dot) |at| name[0..at] else name;
    // A file-level declaration OWNS its name: follow it to what
    // it aliases, and answer nothing at all when it says nothing
    // this tool can read — a name that has an owner is not free
    // for some other declaration to claim.
    if (file_cache.rootDeclInitRange(cache.tree, head)) |aliased| {
        const aliased_name = (try typePathName(cache, aliased.first, aliased.last, remaining)) orelse return null;
        return try resolveDeclaredType(cache, aliased_name, depth + 1, remaining);
    }
    if (dot != null) return null;
    // No file-level declaration owns this bare name, and it is a
    // bare one: a type declared INSIDE a container of this file
    // is addressed by its bare name from inside that container —
    // `pub fn init(…) Bag` written inside `const Registry =
    // struct { pub const Bag = …; }` — while the qualified lookup
    // above only answers the name a file spells from the OUTSIDE
    // (`Registry.Bag`).  One match is that type; two are a name
    // this file does not disambiguate, and an ambiguous answer
    // is no answer.
    // `fileModel` builds one arena and grows two lists, but it also has to
    // read the source it is given, so `OutOfMemory` is only one of what it
    // can fail on.  An allocation gave out is this walk's own resource
    // failure and propagates; a source that does not parse, a token table
    // `std.zig.Ast` cannot address, or more types than a `u32` index holds
    // are facts about THIS document that no retry changes, and every name
    // the model would have carried is exactly as unreadable as none of them.
    // That is the same answer this function already gives a name no
    // declaration owns: no resolved type, so no proof.
    const model = cache.fileModel() catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.InvalidSyntax, error.SourceTooWide, error.TooManyTypes => return null,
    };
    var found: ?ResolvedType = null;
    for (model.types) |*ti| {
        try charge(remaining);
        if (!std.mem.eql(u8, ti.name, name)) continue;
        if (found != null) return null;
        found = .{ .model = model, .info = ti, .path = cache.file_path, .module = cache.module_id };
    }
    return found;
}

/// The dotted name of the type path in `[first, last]`, with
/// generic argument groups dropped — `std.array_list.Managed(u32)`
/// becomes "std.array_list.Managed" — and leading `?` / `*` /
/// `const` qualifiers stripped.  Anything that is not an
/// identifier path (a slice, a fn type, a call) has no name to
/// resolve.  The result lives in the cache's summary arena.
pub fn typePathName(cache: *FileCache, first: Ast.TokenIndex, last: Ast.TokenIndex, remaining: ?*u32) FreshError!?[]const u8 {
    if (first > last) return null;
    const tree = cache.tree;
    const tags = tree.tokens.items(.tag);
    var t = first;
    while (t <= last) : (t += 1) {
        try charge(remaining);
        switch (tags[t]) {
            .question_mark, .asterisk, .asterisk_asterisk, .keyword_const, .keyword_volatile, .keyword_allowzero => {},
            .identifier => break,
            else => return null,
        }
    }
    if (t > last) return null;
    if (cache.summary_arena == null) {
        cache.summary_arena = std.heap.ArenaAllocator.init(cache.gpa);
    }
    var out: std.ArrayListUnmanaged(u8) = .empty;
    var wrote = false;
    while (t <= last) {
        try charge(remaining);
        switch (tags[t]) {
            .identifier => {
                if (wrote) try out.append(cache.summary_arena.?.allocator(), '.');
                try out.appendSlice(cache.summary_arena.?.allocator(), tree.tokenSlice(t));
                wrote = true;
            },
            .period => {
                if (!wrote) return null;
                if (out.items.len == 0 or out.items[out.items.len - 1] == '.') return null;
            },
            // Generic arguments name no field of the type; the
            // container is what this has to resolve.
            .l_paren => {
                if (!wrote) return null;
                t = tokens.matchParen(tags, t, last) orelse return null;
            },
            else => return null,
        }
        t += 1;
    }
    if (!wrote) return null;
    return try out.toOwnedSlice(cache.summary_arena.?.allocator());
}

/// The `= <expr>` a struct field declares, or null.  A field with no
/// default is left undefined when a struct literal omits it, which no
/// other binding is holding; a default that reads a NAME can hand back
/// a global's header, which is the case `.{}` must never claim as its
/// own.
pub fn fieldDefaultExpr(tree: *const Ast, field: file_model.FieldInfo, remaining: ?*u32) FreshError!?FileCache.TokenRange {
if (field.type_last + 1 >= tree.tokens.len) return null;
const tags = tree.tokens.items(.tag);
var t = field.type_last + 1;
var depth: u32 = 0;
var equal: ?Ast.TokenIndex = null;
while (t < tree.tokens.len) : (t += 1) {
    try charge(remaining);
    switch (tags[t]) {
        .l_paren, .l_bracket, .l_brace => depth += 1,
        .r_paren, .r_bracket, .r_brace => if (depth > 0) {
            depth -= 1;
        } else break,
        .equal => if (depth == 0) {
            equal = t;
        },
        .comma => if (depth == 0) break,
        else => {},
    }
}
const start = (equal orelse return null) + 1;
if (start > t) return null;
return .{ .first = start, .last = t - 1 };
}


/// `undefined` is not a keyword: the tokenizer spells it an ordinary
/// `.identifier`, and the language reserves exactly that one identifier for
/// the uninitialised value.  Both queries below turn on it being a VALUE
/// that names no binding, so it is read through its reserved spelling — never
/// by treating identifiers generally as unknown, and never through the name
/// of some other declaration that happens to be spelled the same way.
fn isUndefinedToken(tree: *const Ast, token: Ast.TokenIndex) bool {
    return tree.tokenTag(token) == .identifier and
        std.mem.eql(u8, tree.tokenSlice(token), "undefined");
}

/// The reserved literal values the language gives no address: `true`,
/// `false`, and `null`. Each is an ordinary identifier to the tokenizer
/// and each names a value rather than a binding, so a value that reads
/// one holds no storage at all. `undefined` is deliberately NOT among
/// them: it is the uninitialised value, and a field carrying it is a
/// field nobody has established.
fn isAddressFreeLiteral(tree: *const Ast, token: Ast.TokenIndex) bool {
    if (tree.tokenTag(token) != .identifier) return false;
    const spelling = tree.tokenSlice(token);
    return std.mem.eql(u8, spelling, "true") or std.mem.eql(u8, spelling, "false") or
        std.mem.eql(u8, spelling, "null");
}

/// A value that reads no name: a number, a string, `null`, a
/// boolean, an enum member (`.tag`, whose identifier names a value
/// rather than storage), or punctuation-only compound arithmetic.
/// Anything else — a name, a call, a builtin — can hand back a header
/// somebody else is holding.
pub fn readsNoName(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex, remaining: ?*u32) FreshError!bool {
if (first > last) return false;
const tags = tree.tokens.items(.tag);
// `if (c) A else B` evaluates to A or to B and to nothing else, so when
// both arms read no name the result reads no name whatever the
// condition selected. The condition decides WHICH arm; it contributes no
// storage of its own to the value that comes out. A one-armed `if` is
// not a conditional expression here — it is a syntax error, and a value
// this tool cannot read is no name-free value.
if (tags[first] == .keyword_if) {
    try charge(remaining);
    if (first + 1 > last or tags[first + 1] != .l_paren) return false;
    const close = tokens.matchParen(tags, first + 1, last) orelse return false;
    if (close + 1 > last) return false;
    var depth: u32 = 0;
    var token = close + 1;
    while (token <= last) : (token += 1) {
        try charge(remaining);
        switch (tags[token]) {
            .l_paren, .l_bracket, .l_brace => depth += 1,
            .r_paren, .r_bracket, .r_brace => if (depth > 0) {
                depth -= 1;
            } else return false,
            // The first top-level `else` belongs to THIS `if`: what
            // follows it is the else-arm, nested conditionals included.
            .keyword_else => if (depth == 0) {
                if (!try readsNoName(tree, close + 1, token - 1, remaining)) return false;
                return try readsNoName(tree, token + 1, last, remaining);
            },
            else => {},
        }
    }
    return false;
}
var previous: ?std.zig.Token.Tag = null;
    var token = first;
    while (token <= last) : (token += 1) {
        try charge(remaining);
        const tag = tags[token];
        switch (tag) {
            // After a `.` the reserved spelling names a field or an enum
            // member, which is a name somebody holds storage through.
            .identifier => if (isUndefinedToken(tree, token) or
                (previous != .period and !isAddressFreeLiteral(tree, token))) return false,
            .builtin, .l_paren, .l_brace, .l_bracket => return false,
            else => {},
        }
        previous = tag;
    }
return true;
}

fn resourceFailure(err: anyerror) FreshError!bool {
    return switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        error.AnalysisBudgetExceeded => error.AnalysisBudgetExceeded,
        else => false,
    };
}

fn definedValue(tree: *const Ast, range: TokenRange, remaining: ?*u32) FreshError!bool {
    if (range.first > range.last) return false;
    var token = range.first;
    while (token <= range.last) : (token += 1) {
        try charge(remaining);
        if (isUndefinedToken(tree, token)) return false;
    }
    return true;
}


fn fieldValueFresh(
    cache: *FileCache,
    owner: ResolvedType,
    field: file_model.FieldInfo,
    value: TokenRange,
    walk: FreshWalk,
) FreshError!bool {
    if (!try definedValue(cache.tree, value, walk.remaining)) return false;
    // The shared type query is one semantic edge. Its own bounded internals
    // are not AST visits of this walk and are not claimed as metered here.
    try charge(walk.remaining);
    if (walk.frame == null and type_query.typeRangeIsAddressFree(cache, .{
        .tree = owner.model.tree,
        .first = field.type_first,
        .last = field.type_last,
        .owner = owner,
        .allow_array_length_expr = true,
    }, 0)) return true;
    if (walk.frame) |frame| {
        if (owner.model.tree == &frame.handle.document.tree) {
            const type_node = cache.nodeForExactSpan(field.type_first, field.type_last) orelse return false;
            try charge(walk.remaining);
            const actual_type = (frame.typeOfNode(type_node) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => null,
            }) orelse return false;
            if (try actualTypeAddressFree(frame, actual_type, 0, walk.remaining)) return true;
        }
    }
    if (walk.frame) |frame| {
        if (cache.nodeForExactSpan(value.first, value.last)) |node| {
            switch (cache.tree.nodeTag(node)) {
                .identifier, .field_access, .deref => {
                    try charge(walk.remaining);
                    const value_type = frame.typeOfNode(node) catch |err| switch (err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        else => null,
                    };
                    if (value_type) |ty| {
                        if (try actualTypeAddressFree(frame, ty, 0, walk.remaining)) return true;
                    }
                },
                else => {},
            }
        }
    }
    const next = walk.about(.{ .first = value.first, .last = value.last }) orelse return false;
    return (try freshStorageAt(cache, next)) or
        (cache.tree.tokenTag(value.first) != .period and try readsNoName(cache.tree, value.first, value.last, walk.remaining));
}

/// A named initializer at this literal's own item level, borrowing its tokens.
fn literalFieldValue(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex, name: []const u8, remaining: ?*u32) FreshError!?TokenRange {
    if (first > last) return null;
    var item = first;
    while (item <= last) {
        var end = item;
        var nesting: u32 = 0;
        while (end <= last) : (end += 1) {
            try charge(remaining);
            switch (tree.tokenTag(end)) {
                .l_paren, .l_bracket, .l_brace => nesting += 1,
                .r_paren, .r_bracket, .r_brace => if (nesting > 0) { nesting -= 1; } else return null,
                .comma => if (nesting == 0) break,
                else => {},
            }
        }
        if (item + 3 < end and tree.tokenTag(item) == .period and
            tree.tokenTag(item + 1) == .identifier and tree.tokenTag(item + 2) == .equal and
            std.mem.eql(u8, tree.tokenSlice(item + 1), name))
        {
            return .{ .first = item + 3, .last = end - 1 };
        }
        item = end + 1;
    }
    return null;
}

/// Null permits the literal/syntax route. A known negative allocation
/// origin is settled here and must not be retried through its SDK body
/// with the original allocator replaced by a generic formal parameter.
fn independentValue(cache: *FileCache, claim: fn_summary.FreshClaim, walk: FreshWalk) FreshError!?bool {
    const tree = cache.tree;
    var first = claim.first;
    while (first < claim.last and tree.tokenTag(first) == .keyword_try) {
        try charge(walk.remaining);
        first += 1;
    }
    if (!try definedValue(tree, .{ .first = first, .last = claim.last }, walk.remaining)) return false;
    const node = cache.nodeForExactSpan(first, claim.last);
    if (node) |expression| {
        var call_buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&call_buffer, expression)) |_| {
            const range: TokenRange = .{ .first = first, .last = claim.last };
            const canon_opt = try canonicalCall(cache, range, walk);
            const canonical = canon_opt orelse return null;
            if (if (walk.frame) |frame| frame.resolver else cache.zls) |resolver| {
                // Only the actual SDK declaration grants allocation semantics.
                // A project method called dupe or a body-wide allocation does not.
                if (resolver.declaredInToolchainFile(canonical.callee.handle, "/std/mem/Allocator.zig") catch |err| return try resourceFailure(err)) {
                    var receiver_buffer: [1]Ast.Node.Index = undefined;
                    const receiver = (try canonical.callArgumentFor(cache, &receiver_buffer, 0)) orelse return false;
                    if (!try allocatorOriginIsExternal(cache, receiver, walk, 0)) return false;
                    const name = canonical.callee.tree.tokenSlice(canonical.callee.fn_token + 1);
                    if (std.mem.eql(u8, name, "dupe") or std.mem.eql(u8, name, "dupeZ") or
                        std.mem.eql(u8, name, "alloc") or std.mem.eql(u8, name, "allocSentinel") or
                        std.mem.eql(u8, name, "create")) {
                        return true;
                    }
                }
            }
            if (try standardListConstructor(cache, range, walk)) return try standardListFieldsIndependent(cache, range, walk);
            if (if (walk.frame) |frame| frame.resolver else cache.zls) |resolver| {
                if (resolver.declaredInToolchainFile(canonical.callee.handle, "/std/array_list.zig") catch |err| return try resourceFailure(err)) {
                    const name = canonical.callee.tree.tokenSlice(canonical.callee.fn_token + 1);
                    if (std.mem.eql(u8, name, "init") or std.mem.eql(u8, name, "initCapacity")) return false;
                }
            }
            return try resolvedCalleeBuildsFreshStorage(cache, range, walk);
        }
    }
    if (first != claim.last or tree.tokenTag(first) != .identifier) return null;
    const declaration = tokens.enclosingFnDecl(tree, first) orelse return null;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return null;
    const body = tokens.bodyOf(tree, declaration) orelse return null;
    // Borrow the arena-owned items, not a hash-table slot that recursive
    // declaration queries can relocate when they add another body's bindings.
    const bindings = (try cache.localBindings(proto, body)).*;
    const binding = bindings.findAt(tree.tokenSlice(first), first) orelse return null;
    if (binding.origin == .param or binding.origin == .loop_capture) return false;
    // A returned local's fields, including writes after undefined initialization,
    // must each be established at this use. A header copy alone proves nothing.
    if (try localAggregateFresh(cache, &bindings, binding, claim, walk)) return true;
    if (!binding.is_const) return false;
    if (!try plainLocalStillIndependent(tree, &bindings, binding, claim.first, walk.remaining)) return false;
    // A local header alias is not another callee or returned-field hop. Its
    // initializer must precede the use, so same-depth descent strictly moves
    // backward and cannot cycle even when the optional work meter is absent.
    if (binding.rhs_first >= claim.first) return false;
    var next = walk;
    next.claim = .{ .first = binding.rhs_first, .last = binding.rhs_last };
    return try freshStorageAt(cache, next);
}

fn localAggregateFresh(
    cache: *FileCache,
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
    claim: fn_summary.FreshClaim,
    walk: FreshWalk,
) FreshError!bool {
    const tree = cache.tree;
    var type_range: ?TokenRange = if (claim.type_first) |first| .{ .first = first, .last = claim.type_last.? } else null;
    if (binding.name_token + 1 < binding.rhs_first and tree.tokenTag(binding.name_token + 1) == .colon) {
        type_range = .{ .first = binding.name_token + 2, .last = binding.rhs_first - 2 };
    }
    const range = type_range orelse return false;
    const type_name = (try typePathName(cache, range.first, range.last, walk.remaining)) orelse return false;
    const resolved = (try resolveDeclaredType(cache, type_name, walk.depth, walk.remaining)) orelse return false;
    if (resolved.info.kind != .struct_) return false;
    if (!try actualOwnerMatches(cache, range, resolved, walk)) return false;
    const init_node = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last);
    var literal_buffer: [2]Ast.Node.Index = undefined;
    const literal = if (init_node) |node| tree.fullStructInit(&literal_buffer, node) else null;
    for (resolved.info.fields) |field| {
        try charge(walk.remaining);
        var value: ?TokenRange = null;
        if (literal) |init| {
            for (init.ast.fields) |node| {
                try charge(walk.remaining);
                const first = tree.firstToken(node);
                if (first < 2 or !std.mem.eql(u8, tree.tokenSlice(first - 2), field.name)) continue;
                value = .{ .first = first, .last = tree.lastToken(node) };
            }
        }
        var token = binding.rhs_last + 1;
        while (token < claim.first) : (token += 1) {
            try charge(walk.remaining);
            if (tree.tokenTag(token) != .identifier or !std.mem.eql(u8, tree.tokenSlice(token), binding.name)) continue;
            const actual = bindings.findAt(binding.name, token) orelse continue;
            if (actual.name_token != binding.name_token) continue;
            if (token > 0 and tree.tokenTag(token - 1) == .period) continue;
            // Only a plain, direct statement in the local's own block is a
            // definite overwrite. Any escape/unknown use can rewrite its fields.
            if (token + 3 >= claim.first or tree.tokenTag(token + 1) != .period or
                tree.tokenTag(token + 2) != .identifier or tree.tokenTag(token + 3) != .equal) return false;
            if (token == 0 or (tree.tokenTag(token - 1) != .semicolon and tree.tokenTag(token - 1) != .l_brace)) return false;
            if (!try sameBlock(tree, binding.scope_open, token, walk.remaining)) return false;
            var end = token + 4;
            var nesting: u32 = 0;
            while (end < claim.first) : (end += 1) {
                try charge(walk.remaining);
                switch (tree.tokenTag(end)) {
                    .l_paren, .l_bracket, .l_brace => nesting += 1,
                    .r_paren, .r_bracket, .r_brace => if (nesting > 0) { nesting -= 1; } else return false,
                    .semicolon => if (nesting == 0) break,
                    else => {},
                }
            }
            if (end == claim.first) return false;
            if (std.mem.eql(u8, tree.tokenSlice(token + 2), field.name)) {
                value = .{ .first = token + 4, .last = end - 1 };
            }
            token = end;
        }
        if (value) |expr| {
            if (!try fieldValueFresh(cache, resolved, field, expr, walk)) return false;
        } else if (literal != null and field.has_default) {
            const expr = (try fieldDefaultExpr(resolved.model.tree, field, walk.remaining)) orelse return false;
            if (!try readsNoName(resolved.model.tree, expr.first, expr.last, walk.remaining)) return false;
        } else return false;
    }
    return resolved.info.fields.len != 0;
}

fn sameBlock(tree: *const Ast, open: Ast.TokenIndex, use: Ast.TokenIndex, remaining: ?*u32) FreshError!bool {
    var depth: u32 = 0;
    for (tree.tokens.items(.tag)[open + 1 .. use]) |tag| {
        try charge(remaining);
        switch (tag) {
            .l_brace => depth += 1,
            .r_brace => if (depth > 0) { depth -= 1; } else return false,
            else => {},
        }
    }
    return depth == 0;
}

fn valueReturnType(tree: *const Ast, return_type: ?Ast.Node.Index) ?Ast.Node.Index {
    var node = return_type orelse return null;
    while (tree.nodeTag(node) == .error_union) node = tree.nodeData(node).node_and_node[1];
    return node;
}


/// A const header can still be freed or published. Only known non-retaining
/// memory builtins (and an earlier return on a different path) are exempt;
/// call names and an empty effect list are not a publication proof.
fn plainLocalStillIndependent(
    tree: *const Ast,
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
    use: Ast.TokenIndex,
    remaining: ?*u32,
) FreshError!bool {
    const declaration = tokens.enclosingFnDecl(tree, use) orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    var token = binding.rhs_last + 1;
    while (token < use) : (token += 1) {
        try charge(remaining);
        if (tree.tokenTag(token) != .identifier or !std.mem.eql(u8, tree.tokenSlice(token), binding.name)) continue;
        if (token > 0 and tree.tokenTag(token - 1) == .period) continue;
        const actual = bindings.findAt(binding.name, token) orelse continue;
        if (actual.name_token != binding.name_token) continue;
        if (try tokenInsideActiveErrdefer(tree, body, token, use, remaining)) continue;
        if (token > 0 and tree.tokenTag(token - 1) == .keyword_return) continue;
        var safe_builtin = false;
        var opener = binding.rhs_last + 1;
        while (opener < token) : (opener += 1) {
            try charge(remaining);
            if (tree.tokenTag(opener) != .builtin or !tokens.isWriteFirstArgBuiltin(tree.tokenSlice(opener))) continue;
            if (opener + 1 >= token or tree.tokenTag(opener + 1) != .l_paren) continue;
            const close = tokens.matchParen(tree.tokens.items(.tag), opener + 1, use) orelse continue;
            if (token >= close) continue;
            // Only a direct value argument, never &header or an expression
            // that could rewrite the pointer-valued header while evaluating.
            const before = tree.tokenTag(token - 1);
            const after = tree.tokenTag(token + 1);
            if ((before == .l_paren or before == .comma) and (after == .comma or after == .r_paren)) {
                safe_builtin = true;
                break;
            }
        }
        if (!safe_builtin) return false;
    }
    return true;
}

test "returned local fields must all be independent and initialized" {
    const source: [:0]const u8 =
        \\const Packet = struct { bytes: []const u8, other: []const u8, level: u32 };
        \\fn independent(seed: u32) Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = &[_]u8{2};
        \\    out.level = seed;
        \\    return out;
        \\}
        \\fn borrowed(input: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = input;
        \\    out.level = 0;
        \\    return out;
        \\}
        \\fn incomplete() Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.level = 0;
        \\    return out;
        \\}
        \\fn conditional(flag: bool) Packet {
        \\    var out: Packet = undefined;
        \\    if (flag) { out.bytes = &[_]u8{1}; }
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    return out;
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const model = try cache.fileModel();
    try std.testing.expect(try declBuildsFreshStorage(&cache, &tree, model.findFn("independent").?.fn_decl, .root(.{ .first = 0, .last = 0 })));
    for ([_][]const u8{ "borrowed", "incomplete", "conditional" }) |name| {
        try std.testing.expect(!try declBuildsFreshStorage(&cache, &tree, model.findFn(name).?.fn_decl, .root(.{ .first = 0, .last = 0 })));
    }
}

test "aggregate allocation correlation uses actual SDK receiver identity" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Packet = struct { bytes: []const u8, level: u32 };
        \\const Source = struct {
        \\    gpa: std.mem.Allocator,
        \\    bytes: []const u8,
        \\    level: u32,
        \\    fn copy(self: Source) !Packet {
        \\        var out: Packet = undefined;
        \\        out.bytes = try self.gpa.dupe(u8, self.bytes);
        \\        out.level = self.level;
        \\        return out;
        \\    }
        \\    fn shallow(self: Source) Packet {
        \\        return .{ .bytes = self.bytes, .level = self.level };
        \\    }
        \\    fn unrelated(self: Source) !Packet {
        \\        const scratch = try self.gpa.alloc(u8, 1);
        \\        defer self.gpa.free(scratch);
        \\        return .{ .bytes = self.bytes, .level = self.level };
        \\    }
        \\};
        \\const Mimic = struct {
        \\    bytes: []const u8,
        \\    fn dupe(self: Mimic, comptime T: type, input: []const T) []const T {
        \\        _ = self; return input;
        \\    }
        \\};
        \\fn mimic(gpa: Mimic, bytes: []const u8) Packet {
        \\    return .{ .bytes = gpa.dupe(u8, bytes), .level = 0 };
        \\}
        \\fn allocated(gpa: std.mem.Allocator, bytes: []const u8) !Packet {
        \\    const own = try gpa.alloc(u8, bytes.len);
        \\    @memcpy(own, bytes);
        \\    return .{ .bytes = own, .level = 0 };
        \\}
        \\fn identity(bytes: []const u8) []const u8 { return bytes; }
        \\fn deferred(gpa: std.mem.Allocator) !Packet {
        \\    const own = try gpa.alloc(u8, 1);
        \\    defer gpa.free(own);
        \\    return .{ .bytes = own, .level = 0 };
        \\}
        \\fn errorDeferred(gpa: std.mem.Allocator) !Packet {
        \\    const own = try gpa.alloc(u8, 1);
        \\    errdefer gpa.free(own);
        \\    return .{ .bytes = own, .level = 0 };
        \\}
        \\fn aliasDeferred(gpa: std.mem.Allocator) !Packet {
        \\    const own = try gpa.alloc(u8, 1);
        \\    const held = own;
        \\    defer gpa.free(own);
        \\    return .{ .bytes = held, .level = 0 };
        \\}
        \\fn aliasLive(gpa: std.mem.Allocator) !Packet {
        \\    const own = try gpa.alloc(u8, 1);
        \\    const held = own;
        \\    return .{ .bytes = held, .level = 0 };
        \\}
        \\fn unrelatedDeferred(gpa: std.mem.Allocator) !Packet {
        \\    const own = try gpa.alloc(u8, 1);
        \\    const other = try gpa.alloc(u8, 1);
        \\    defer gpa.free(other);
        \\    return .{ .bytes = own, .level = 0 };
        \\}
        \\fn freed(gpa: std.mem.Allocator) !Packet {
        \\    const own = try gpa.alloc(u8, 1);
        \\    gpa.free(own);
        \\    return .{ .bytes = own, .level = 0 };
        \\}
        \\fn unusedAllocator(ignored: std.mem.Allocator, n: usize) !Packet {
        \\    _ = ignored;
        \\    return .{ .bytes = &[_]u8{1}, .level = @intCast(n) };
        \\}
        \\const ScratchSource = struct {
        \\    scratch: [64]u8 = undefined,
        \\    fn receiverBuffered(self: *ScratchSource, n: usize) !Packet {
        \\        var fba = std.heap.FixedBufferAllocator.init(self.scratch[0..]);
        \\        const local_gpa = fba.allocator();
        \\        return .{ .bytes = try local_gpa.alloc(u8, n), .level = 0 };
        \\    }
        \\    fn forwardedReceiver(self: *ScratchSource, n: usize) !Packet {
        \\        var fba = std.heap.FixedBufferAllocator.init(self.scratch[0..]);
        \\        const local_gpa = fba.allocator();
        \\        return allocated(local_gpa, self.scratch[0..n]);
        \\    }
        \\};
        \\fn frameBuffered(n: usize) !Packet {
        \\    var scratch: [64]u8 = undefined;
        \\    var fba = std.heap.FixedBufferAllocator.init(scratch[0..]);
        \\    const local_gpa = fba.allocator();
        \\    return .{ .bytes = try local_gpa.alloc(u8, n), .level = 0 };
        \\}
        \\fn forwardedBuffered(n: usize) !Packet {
        \\    var scratch: [64]u8 = undefined;
        \\    var fba = std.heap.FixedBufferAllocator.init(scratch[0..]);
        \\    const local_gpa = fba.allocator();
        \\    return allocated(local_gpa, scratch[0..n]);
        \\}
        \\fn heapPage(n: usize) !Packet {
        \\    return .{ .bytes = try std.heap.page_allocator.alloc(u8, n), .level = 0 };
        \\}
        \\fn claims(value: Source, gpa: std.mem.Allocator, bytes: []const u8) !void {
        \\    const annotated: Source = value;
        \\    const inferred = value;
        \\    _ = try annotated.copy();
        \\    _ = try inferred.copy();
        \\    _ = annotated.shallow();
        \\    _ = try annotated.unrelated();
        \\    _ = mimic(.{ .bytes = bytes }, bytes);
        \\    _ = try allocated(gpa, bytes);
        \\    _ = identity(try gpa.alloc(u8, 1));
        \\    _ = try freed(gpa);
        \\    var receiver_scratch: ScratchSource = .{};
        \\    _ = try receiver_scratch.receiverBuffered(3);
        \\    _ = try receiver_scratch.forwardedReceiver(3);
        \\    var local_fba = std.heap.FixedBufferAllocator.init(receiver_scratch.scratch[0..]);
        \\    const buffered_gpa = local_fba.allocator();
        \\    _ = try unusedAllocator(buffered_gpa, 3);
        \\    _ = try frameBuffered(3);
        \\    _ = try forwardedBuffered(3);
        \\    _ = try deferred(gpa);
        \\    _ = try errorDeferred(gpa);
        \\    _ = try aliasDeferred(gpa);
        \\    _ = try aliasLive(gpa);
        \\    _ = try unrelatedDeferred(gpa);
        \\    _ = try heapPage(3);
        \\}
    ;
    const gpa = std.testing.allocator;
    const engine = @import("type_engine");
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-fresh-storage-query-test.zig" });
    defer gpa.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.module_id = resolver.handle.module;
    var copy_count: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, raw_node| {
        const node: Ast.Node.Index = @enumFromInt(raw_node);
        if (raw_node == 0) continue;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        const caller = tokens.enclosingFnDecl(tree, tree.firstToken(node)) orelse continue;
        var caller_buffer: [1]Ast.Node.Index = undefined;
        const caller_proto = tokens.fnProto(tree, &caller_buffer, caller) orelse continue;
        const caller_name = caller_proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(caller_name), "claims")) continue;
        const name = tree.tokenSlice(tree.lastToken(call.ast.fn_expr));
        const independent = std.mem.eql(u8, name, "copy") or std.mem.eql(u8, name, "allocated") or std.mem.eql(u8, name, "heapPage") or
            std.mem.eql(u8, name, "errorDeferred") or std.mem.eql(u8, name, "aliasLive") or
            std.mem.eql(u8, name, "unrelatedDeferred") or std.mem.eql(u8, name, "unusedAllocator");
        const borrowed = std.mem.eql(u8, name, "shallow") or std.mem.eql(u8, name, "unrelated") or
            std.mem.eql(u8, name, "mimic") or std.mem.eql(u8, name, "identity") or std.mem.eql(u8, name, "freed") or
            std.mem.eql(u8, name, "receiverBuffered") or std.mem.eql(u8, name, "frameBuffered") or
            std.mem.eql(u8, name, "deferred") or std.mem.eql(u8, name, "aliasDeferred") or
            std.mem.eql(u8, name, "forwardedBuffered") or std.mem.eql(u8, name, "forwardedReceiver");
        if (!independent and !borrowed) continue;
        const claim: fn_summary.FreshClaim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) };
        const verdict = try provesFreshStorage(&cache, claim, null);
        try std.testing.expectEqual(independent, verdict);
        if (std.mem.eql(u8, name, "copy")) copy_count += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), copy_count);
}

test "undefined and name-bearing defaults are not independent storage" {
    const source: [:0]const u8 = "const n = 1; const bad = undefined; const good = 2;";
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    for (tree.tokens.items(.tag), 0..) |_, index| {
        const token: Ast.TokenIndex = @intCast(index);
        if (!isUndefinedToken(&tree, token)) continue;
        try std.testing.expect(!try readsNoName(&tree, token, token, null));
    }
}

fn charge(remaining: ?*u32) FreshError!void {
    const allowance = remaining orelse return;
    if (allowance.* == 0) return error.AnalysisBudgetExceeded;
    allowance.* -= 1;
}

test "shared fresh work exhaustion does not publish a verdict and memo hits only charge lookup" {
    const source: [:0]const u8 = "fn make() []const u8 { return &[_]u8{1}; }";
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var claim: ?fn_summary.FreshClaim = null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .address_of) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        claim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) };
        break;
    }
    var remaining: u32 = 1;
    try std.testing.expectError(error.AnalysisBudgetExceeded, provesFreshStorage(&cache, claim.?, &remaining));
    try std.testing.expectEqual(@as(u32, 0), cache.fresh_storage.count());
    try std.testing.expect(try provesFreshStorage(&cache, claim.?, null));
    remaining = 1;
    try std.testing.expect(try provesFreshStorage(&cache, claim.?, &remaining));
    try std.testing.expectEqual(@as(u32, 0), remaining);
    try std.testing.expectError(error.AnalysisBudgetExceeded, provesFreshStorage(&cache, claim.?, &remaining));
}

test "SDK map defaults prove new backing but project lookalikes and cached headers do not" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Map = std.AutoHashMapUnmanaged(u32, u32);
        \\const ArrayMap = std.AutoArrayHashMapUnmanaged(bool, std.ArrayList(u8));
        \\var shared: Map = .empty;
        \\const Mimic = struct {
        \\    data: *Map,
        \\    const empty: Mimic = .{ .data = &shared };
        \\};
        \\fn Factory(comptime K: type, comptime V: type) type {
        \\    return struct {
        \\        const OwnedMap = std.AutoHashMapUnmanaged(K, V);
        \\        fn direct() OwnedMap { return .empty; }
        \\        fn indirect() OwnedMap { return direct(); }
        \\    };
        \\}
        \\fn claims(gpa: std.mem.Allocator) void {
        \\    var a: Map = .empty;
        \\    var b: Map = .{};
        \\    var c = Map{};
        \\    var d = std.AutoHashMap(u32, u32).init(gpa);
        \\    var e = Mimic.empty;
        \\    var f = shared;
        \\    var g = Factory(u32, u32).direct();
        \\    var h = Factory(u32, u32).indirect();
        \\    var i: ArrayMap = .empty;
        \\    var j: ArrayMap = .{};
        \\    var k: ArrayMap = .{ .entries = .{ .len = 1 } };
        \\    var l: ArrayMap = .{ .entries = .{ .capacity = 1 } };
        \\    _ = &a; _ = &b; _ = &c; _ = &d; _ = &e; _ = &f; _ = &g; _ = &h;
        \\    _ = &i; _ = &j; _ = &k; _ = &l;
        \\}
    ;
    const gpa = std.testing.allocator;
    const engine = @import("type_engine");
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-map-fresh-storage-query-test.zig" });
    defer gpa.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.module_id = resolver.handle.module;
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, raw_node| {
        if (raw_node == 0) continue;
        const node: Ast.Node.Index = @enumFromInt(raw_node);
        const declaration = tree.fullVarDecl(node) orelse continue;
        const name = tree.tokenSlice(declaration.ast.mut_token + 1);
        if (name.len != 1 or name[0] < 'a' or name[0] > 'l') continue;
        const value = declaration.ast.init_node.unwrap().?;
        const type_node = declaration.ast.type_node.unwrap();
        const claim: fn_summary.FreshClaim = .{
            .first = tree.firstToken(value),
            .last = tree.lastToken(value),
            .type_first = if (type_node) |ty| tree.firstToken(ty) else null,
            .type_last = if (type_node) |ty| tree.lastToken(ty) else null,
        };
        const fresh = name[0] != 'd' and name[0] != 'e' and name[0] != 'f' and name[0] != 'h' and name[0] != 'k' and name[0] != 'l';
        try std.testing.expectEqual(fresh, try provesFreshStorage(&cache, claim, null));
        if (name[0] >= 'a' and name[0] <= 'd' or name[0] >= 'i') {
            try std.testing.expectEqual(name[0] != 'k', try sdkCollectionIsEmpty(&cache, .root(claim)));
        }
        seen += 1;
    }
    try std.testing.expectEqual(@as(usize, 12), seen);
}

/// SDK collection headers are proved from their actual container fields and selected
/// constant initializer, not a constructor-name list. This is backing-storage
/// evidence at initialization, not evidence about payloads inserted later.
fn sdkCollectionBuildsFreshStorage(cache: *FileCache, walk: FreshWalk) FreshError!bool {
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    const tree = cache.tree;
    const expression = cache.nodeForExactSpan(walk.claim.first, walk.claim.last) orelse return false;
    var buffer: [2]Ast.Node.Index = undefined;
    const literal = tree.fullStructInit(&buffer, expression);
    if (literal == null and tree.nodeTag(expression) != .enum_literal and tree.nodeTag(expression) != .field_access) return false;
    const owner_node = if (walk.claim.type_first) |first|
        cache.nodeForExactSpan(first, walk.claim.type_last.?) orelse return false
    else
        expression;
    try charge(walk.remaining);
    const resolved_container = if (walk.frame) |frame| frame.containerOfNode(owner_node) else resolver.containerOfNode(owner_node);
    const container = (resolved_container catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => null,
    }) orelse return false;
    const in_hash_map = resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/hash_map.zig") catch |err| return resourceFailure(err);
    const in_array_hash_map = resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/array_hash_map.zig") catch |err| return resourceFailure(err);
    const in_array_list = resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/array_list.zig") catch |err| return resourceFailure(err);
    if (!in_hash_map and !in_array_hash_map and !in_array_list) return false;
    const actual_type: type_engine.TypeResolver.ActualType = .{ .data = .{ .container = container }, .is_type_val = true };
    return actualAggregateFresh(cache, expression, actual_type, walk, 0);
}

fn actualAggregateFresh(
    cache: *FileCache,
    expression: Ast.Node.Index,
    expected: type_engine.TypeResolver.ActualType,
    walk: FreshWalk,
    type_depth: u8,
) FreshError!bool {
    if (walk.spent() or type_depth >= type_query.max_element_depth or expected.data != .container) return false;
    try charge(walk.remaining);
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    const container = expected.data.container;
    const frame = resolver.frameForContainer(container);
    const owner_tree = &frame.handle.document.tree;
    const owner_node = container.scope_handle.toNode();
    if (owner_tree.tokenTag(owner_tree.nodeMainToken(owner_node)) != .keyword_struct) return false;
    var owner_buffer: [2]Ast.Node.Index = undefined;
    const declared = owner_tree.fullContainerDecl(&owner_buffer, owner_node) orelse return false;
    const selected = (try selectActualLiteral(cache, expression, expected, walk)) orelse return false;
    if (selected.cache != cache or selected.expression != expression) {
        return actualAggregateFresh(selected.cache, selected.expression, expected, selected.walk, type_depth);
    }
    var value_buffer: [2]Ast.Node.Index = undefined;
    const literal = cache.tree.fullStructInit(&value_buffer, expression) orelse return false;
    const owner_cache = (try actualSourceCache(cache, frame.handle)) orelse return false;
    for (declared.ast.members) |member| {
        try charge(walk.remaining);
        const field = owner_tree.fullContainerField(member) orelse continue;
        if (field.ast.tuple_like) return false;
        const type_node = field.ast.type_expr.unwrap() orelse return false;
        const name = owner_tree.tokenSlice(field.ast.main_token);
        var supplied: ?Ast.Node.Index = null;
        for (literal.ast.fields) |value| {
            try charge(walk.remaining);
            const first = cache.tree.firstToken(value);
            if (first >= 2 and std.mem.eql(u8, cache.tree.tokenSlice(first - 2), name)) supplied = value;
        }
        const value_cache = if (supplied != null) cache else owner_cache;
        const value = supplied orelse field.ast.value_expr.unwrap() orelse return false;
        const range: TokenRange = .{ .first = value_cache.tree.firstToken(value), .last = value_cache.tree.lastToken(value) };
        if (!try definedValue(value_cache.tree, range, walk.remaining)) {
            // Only a physically unused pointer in the exact SDK zero-capacity
            // representation can be undefined. This is not a general field
            // exemption and cannot discharge an arbitrary undefined payload.
            if (range.first != range.last or !isUndefinedToken(value_cache.tree, range.first)) return false;
            try charge(walk.remaining);
            const undefined_type = (frame.typeOfNode(type_node) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => null,
            }) orelse return false;
            if (!actualTypeIsPointer(frame, undefined_type) or
                !try sdkUnusedBackingPointer(cache, expression, expected, walk)) return false;
            continue;
        }
        if (value_cache.tree.tokenTag(range.first) != .period and
            try readsNoName(value_cache.tree, range.first, range.last, walk.remaining)) continue;
        var next = walk.about(.{
            .first = range.first,
            .last = range.last,
            .type_first = if (value_cache.tree == owner_tree) owner_tree.firstToken(type_node) else null,
            .type_last = if (value_cache.tree == owner_tree) owner_tree.lastToken(type_node) else null,
        }) orelse return false;
        if (value_cache.tree == owner_tree) {
            next.frame = frame;
        }
        try charge(walk.remaining);
        const field_type = (frame.typeOfNode(type_node) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => null,
        });
        if (field_type) |ty| {
            if (try actualTypeAddressFree(frame, ty, 0, walk.remaining)) continue;
            if (ty.data == .container) {
                // A nested SDK header's structural fields are not another
                // callee hop. Calls proving a field still use next.depth.
                var structural = next;
                structural.depth = walk.depth;
                if (try actualAggregateFresh(value_cache, value, ty, structural, type_depth + 1)) continue;
            }
        }
        if (!try freshStorageAt(value_cache, next)) return false;
    }
    return true;
}

fn actualSourceCache(
    cache: *FileCache,
    handle: type_engine.DocumentStore.Handle,
) FreshError!?*FileCache {
    if (&handle.document.tree == cache.tree and handle.module == cache.module_id) return cache;
    // `sourceDocument` names its error set: opening a document can only run
    // out of memory, and that is the walk's own resource failure, not a
    // verdict about the document.  So it propagates and there is no second
    // outcome to map onto null.
    const document = try grow_analysis.sourceDocument(cache, handle);
    return &document.cache;
}

/// Whether `ty` is a pointer, read through the same route
/// `actualTypeAddressFree` reads a type's KIND. `ActualType.data` is not that
/// answer: the engine interns every type it has no structural node for, so a
/// primitive pointer such as `[*]u8` arrives as an unnamed pool index and a
/// raw `.data != .pointer` test refuses it as if it were not a pointer at all.
/// Only the pool's own tag says which kind this type actually is.
fn actualTypeIsPointer(
    frame: type_engine.TypeResolver.ResolutionFrame,
    ty: type_engine.TypeResolver.ActualType,
) bool {
    if (ty.data == .ip_index) {
        return frame.resolver.ctx.ip.zigTypeTag(ty.ipIndex() orelse return false) == .pointer;
    }
    return ty.data == .pointer;
}

/// The shared token type proof cannot recover a generic container's bound
/// fields from another document. Read that same bounded address-free question
/// through its actual resolution frame; never classify a whole nonpointer
/// aggregate as scalar. This carries no storage provenance or second resolver.
pub fn actualTypeAddressFree(
    frame: type_engine.TypeResolver.ResolutionFrame,
    ty: type_engine.TypeResolver.ActualType,
    depth: u8,
    remaining: ?*u32,
) FreshError!bool {
    if (depth > type_query.max_element_depth) return false;
    try charge(remaining);
    // Structural wrapper children are instance types; intern-pool children
    // may already be type values. Normalize through the same resolver rather
    // than changing flags or losing the wrapper's address-bearing shape.
    const actual = (frame.resolver.normalizedType(ty) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
    }) orelse return false;
    switch (actual.data) {
        .ip_index => {
            // The pool reports a tag it cannot name as null.  That is the same
            // "this walk could not read it" answer every other unresolved
            // question here gets — never a guessed kind — so an unnamed
            // interned type is not proved address-free.
            const tag = frame.resolver.ctx.ip.zigTypeTag(actual.ipIndex() orelse return false) orelse return false;
            return switch (tag) {
                .int, .float, .bool, .@"enum", .void, .comptime_int, .comptime_float, .null => true,
                .array, .vector, .optional => if (frame.resolver.childType(actual)) |child|
                    actualTypeAddressFree(frame, child, depth + 1, remaining)
                else
                    false,
                else => false,
            };
        },
        .array => |array| return actualTypeAddressFree(frame, array.elem_ty.*, depth + 1, remaining),
        .union_tag => return true,
        .optional => |payload| return actualTypeAddressFree(frame, payload.*, depth + 1, remaining),
        .container => |container| {
            const nested = frame.resolver.frameForContainer(container);
            const tree = &nested.handle.document.tree;
            const node = container.scope_handle.toNode();
            switch (tree.tokenTag(tree.nodeMainToken(node))) {
                .keyword_enum => return true,
                .keyword_struct => {},
                else => return false,
            }
            var buffer: [2]Ast.Node.Index = undefined;
            const declaration = tree.fullContainerDecl(&buffer, node) orelse return false;
            for (declaration.ast.members) |member| {
                try charge(remaining);
                const field = tree.fullContainerField(member) orelse continue;
                const type_node = field.ast.type_expr.unwrap() orelse return false;
                try charge(remaining);
                const field_type = (nested.typeOfNode(type_node) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => null,
                }) orelse return false;
                if (!try actualTypeAddressFree(nested, field_type, depth + 1, remaining)) return false;
            }
            return true;
        },
        else => return false,
    }
}


/// Borrowed source selection, not an ownership or empty-occupancy verdict.
const ActualLiteral = struct {
    cache: *FileCache,
    expression: Ast.Node.Index,
    walk: FreshWalk,
};

/// Resolve only the initializer actually selected by this expression. In
/// particular, Project.empty cannot be replaced by SDKType.empty merely
/// because its value has the SDK type.
fn selectActualLiteral(
    cache: *FileCache,
    expression: Ast.Node.Index,
    expected: type_engine.TypeResolver.ActualType,
    walk: FreshWalk,
) FreshError!?ActualLiteral {
    if (expected.data != .container) return null;
    var literal_buffer: [2]Ast.Node.Index = undefined;
    if (cache.tree.fullStructInit(&literal_buffer, expression) != null) {
        return .{ .cache = cache, .expression = expression, .walk = walk };
    }
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return null;
    const member = switch (cache.tree.nodeTag(expression)) {
        .enum_literal => cache.tree.tokenSlice(cache.tree.nodeMainToken(expression)),
        .field_access => blk: {
            const access = cache.tree.nodeData(expression).node_and_token;
            try charge(walk.remaining);
            const resolved = if (walk.frame) |frame| frame.containerOfNode(access[0]) else resolver.containerOfNode(access[0]);
            const receiver = (resolved catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => null,
            }) orelse return null;
            const actual_receiver: type_engine.TypeResolver.ActualType = .{ .data = .{ .container = receiver }, .is_type_val = true };
            if (!expected.eql(actual_receiver)) return null;
            break :blk cache.tree.tokenSlice(access[1]);
        },
        else => return null,
    };
    const Analysis = @TypeOf(resolver.analyser);
    try charge(walk.remaining);
    const declaration = (Analysis.lookupSymbolContainer(expected, member, .other) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
    }) orelse return null;
    if (!declaration.isConst()) return null;
    const node = switch (declaration.decl) {
        .ast_node => |node| node,
        else => return null,
    };
    const source = (try actualSourceCache(cache, declaration.handle)) orelse return null;
    const variable = source.tree.fullVarDecl(node) orelse return null;
    const initializer = variable.ast.init_node.unwrap() orelse return null;
    // Selecting a literal is not a callee hop. Nonliteral aliases are not
    // chased, so neither a cached header nor a const cycle acquires a proof.
    var initializer_buffer: [2]Ast.Node.Index = undefined;
    if (source.tree.fullStructInit(&initializer_buffer, initializer) == null) return null;
    var next = walk;
    next.claim = .{ .first = source.tree.firstToken(initializer), .last = source.tree.lastToken(initializer) };
    next.frame = resolver.frameForContainer(expected.data.container);
    return .{ .cache = source, .expression = initializer, .walk = next };
}

/// Prove zero user-visible occupancy separately from backing ownership. Only
/// actual SDK map count declarations select the representation to inspect;
/// cached headers and project lookalikes never supply default fields.
pub fn sdkCollectionIsEmpty(cache: *FileCache, walk: FreshWalk) FreshError!bool {
    if (walk.spent()) return false;
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    const expression = cache.nodeForExactSpan(walk.claim.first, walk.claim.last) orelse return false;
    const owner_node = if (walk.claim.type_first) |first|
        cache.nodeForExactSpan(first, walk.claim.type_last.?) orelse return false
    else
        expression;
    try charge(walk.remaining);
    const resolved = if (walk.frame) |frame| frame.containerOfNode(owner_node) else resolver.containerOfNode(owner_node);
    const container = (resolved catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => null,
    }) orelse return false;
    if (!try sdkMapDocument(resolver, container.scope_handle.handle)) return false;
    const expected: type_engine.TypeResolver.ActualType = .{ .data = .{ .container = container }, .is_type_val = true };
    const frame = resolver.frameForContainer(container);
    const Analysis = @TypeOf(resolver.analyser);
    try charge(walk.remaining);
    const count = (Analysis.lookupSymbolContainer(expected, "count", .other) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
    }) orelse return false;
    const count_node = switch (count.decl) {
        .ast_node => |node| node,
        else => return false,
    };
    const source = (try actualSourceCache(cache, count.handle)) orelse return false;
    if (!try sdkMapDocument(resolver, count.handle)) return false;
    var count_walk = walk;
    count_walk.frame = frame;
    var path: SdkFieldPath = .{};
    if (!try sdkCountPath(source, count_node, count_walk, &path, 0)) return false;
    return sdkPathIsZero(cache, expression, expected, walk, path.names[0..path.len], 0);
}

const SdkFieldPath = struct {
    names: [type_query.max_element_depth][]const u8 = undefined,
    len: usize = 0,

    fn append(self: *SdkFieldPath, name: []const u8) bool {
        if (self.len == self.names.len) return false;
        self.names[self.len] = name;
        self.len += 1;
        return true;
    }
};

fn sdkMapDocument(resolver: *type_engine.TypeResolver, handle: anytype) FreshError!bool {
    return (resolver.declaredInToolchainFile(handle, "/std/hash_map.zig") catch |err| return resourceFailure(err)) or
        (resolver.declaredInToolchainFile(handle, "/std/array_hash_map.zig") catch |err| return resourceFailure(err));
}

fn sdkCountPath(cache: *FileCache, declaration: Ast.Node.Index, walk: FreshWalk, path: *SdkFieldPath, depth: u8) FreshError!bool {
    if (depth >= max_fresh_depth) return false;
    const tree = cache.tree;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
    var parameters = proto.iterate(tree);
    const receiver = (parameters.next() orelse return false).name_token orelse return false;
    if (parameters.next() != null) return false;
    const value = (try uniqueReturnedValue(tree, declaration, walk.remaining)) orelse return false;
    if (tree.nodeTag(value) == .field_access) {
        return try appendSdkReceiverPath(tree, value, tree.tokenSlice(receiver), path, walk.remaining);
    }
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, value) orelse return false;
    if (call.ast.params.len != 0 or tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
    const access = tree.nodeData(call.ast.fn_expr).node_and_token;
    if (!try appendSdkReceiverPath(tree, access[0], tree.tokenSlice(receiver), path, walk.remaining)) return false;
    const range: TokenRange = .{ .first = tree.firstToken(value), .last = tree.lastToken(value) };
    const canonical = (try canonicalCall(cache, range, walk)) orelse return false;
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    if (!try sdkMapDocument(resolver, canonical.callee.handle)) return false;
    const declaring = (try canonical.declaringCache(cache)) orelse return false;
    var next = walk;
    next.frame = resolver.frameForFunction(canonical.callee.reference);
    return sdkCountPath(declaring, canonical.callee.declaration, next, path, depth + 1);
}

fn appendSdkReceiverPath(tree: *const Ast, node: Ast.Node.Index, receiver: []const u8, path: *SdkFieldPath, remaining: ?*u32) FreshError!bool {
    try charge(remaining);
    return switch (tree.nodeTag(node)) {
        .identifier => std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), receiver),
        .field_access => blk: {
            const access = tree.nodeData(node).node_and_token;
            if (!try appendSdkReceiverPath(tree, access[0], receiver, path, remaining)) break :blk false;
            break :blk path.append(tree.tokenSlice(access[1]));
        },
        else => false,
    };
}

fn uniqueReturnedValue(tree: *const Ast, declaration: Ast.Node.Index, remaining: ?*u32) FreshError!?Ast.Node.Index {
    const body = tokens.bodyOf(tree, declaration) orelse return null;
    var buffer: [2]Ast.Node.Index = undefined;
    const statements = tree.blockStatements(&buffer, body) orelse return null;

    // SDK count selectors and literal initializers need no preceding effects
    // or control-flow interpretation. Anything else stays unknown.
    if (statements.len != 1) return null;
    try charge(remaining);
    const statement = statements[0];
    if (tree.nodeTag(statement) != .@"return") return null;
    return tree.nodeData(statement).opt_node.unwrap();
}

fn sdkPathIsZero(
    cache: *FileCache,
    expression: Ast.Node.Index,
    expected: type_engine.TypeResolver.ActualType,
    walk: FreshWalk,
    path: []const []const u8,
    depth: u8,
) FreshError!bool {
    if (path.len == 0 or depth >= type_query.max_element_depth or expected.data != .container) return false;
    const selected = (try selectActualLiteral(cache, expression, expected, walk)) orelse {
        // A genuine SDK initializer may expose its literal through a return.
        // Do not infer zero occupancy for a project call or a returned local
        // whose writes this query has not observed.
        var call_buffer: [1]Ast.Node.Index = undefined;
        _ = cache.tree.fullCall(&call_buffer, expression) orelse return false;
        const range: TokenRange = .{ .first = cache.tree.firstToken(expression), .last = cache.tree.lastToken(expression) };
        const canonical = (try canonicalCall(cache, range, walk)) orelse return false;
        const original = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
        if (!try sdkMapDocument(original, canonical.callee.handle)) return false;
        const declaring = (try canonical.declaringCache(cache)) orelse return false;
        const value = (try uniqueReturnedValue(declaring.tree, canonical.callee.declaration, walk.remaining)) orelse return false;
        var next = walk;
        next.claim = .{ .first = declaring.tree.firstToken(value), .last = declaring.tree.lastToken(value) };
        next.frame = original.frameForFunction(canonical.callee.reference);
        return sdkPathIsZero(declaring, value, expected, next, path, depth + 1);
    };
    const resolver = if (selected.walk.frame) |frame| frame.resolver else selected.cache.zls orelse return false;
    const frame = resolver.frameForContainer(expected.data.container);
    const owner_tree = &frame.handle.document.tree;
    const owner_node = expected.data.container.scope_handle.toNode();
    var owner_buffer: [2]Ast.Node.Index = undefined;
    const declared = owner_tree.fullContainerDecl(&owner_buffer, owner_node) orelse return false;
    var value_buffer: [2]Ast.Node.Index = undefined;
    const literal = selected.cache.tree.fullStructInit(&value_buffer, selected.expression) orelse return false;
    for (declared.ast.members) |member| {
        try charge(walk.remaining);
        const field = owner_tree.fullContainerField(member) orelse continue;
        if (!std.mem.eql(u8, owner_tree.tokenSlice(field.ast.main_token), path[0])) continue;
        var value: ?Ast.Node.Index = null;
        for (literal.ast.fields) |candidate| {
            try charge(walk.remaining);
            const token = selected.cache.tree.firstToken(candidate);
            if (token >= 2 and std.mem.eql(u8, selected.cache.tree.tokenSlice(token - 2), path[0])) value = candidate;
        }
        const value_cache = if (value != null) selected.cache else (try actualSourceCache(cache, frame.handle)) orelse return false;
        const actual_value = value orelse field.ast.value_expr.unwrap() orelse return false;
        if (path.len == 1) return numericValueIsZero(value_cache, actual_value, walk);
        const type_node = field.ast.type_expr.unwrap() orelse return false;
        try charge(walk.remaining);
        const field_type = (frame.typeOfNode(type_node) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => null,
        }) orelse return false;
        var next = selected.walk;
        next.claim = .{ .first = value_cache.tree.firstToken(actual_value), .last = value_cache.tree.lastToken(actual_value) };
        if (value == null) {
            next.frame = frame;
        }
        return sdkPathIsZero(value_cache, actual_value, field_type, next, path[1..], depth + 1);
    }
    return false;
}

/// MultiArrayList's SDK representation exposes occupied length and allocated
/// capacity directly. Both must be proved zero from the actual initializer;
/// neither a project field called len nor zero occupancy with spare capacity
/// can make an undefined physical pointer fresh.
fn sdkUnusedBackingPointer(cache: *FileCache, expression: Ast.Node.Index, expected: type_engine.TypeResolver.ActualType, walk: FreshWalk) FreshError!bool {
    if (expected.data != .container) return false;
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    if (!(resolver.declaredInToolchainFile(expected.data.container.scope_handle.handle, "/std/multi_array_list.zig") catch |err| return resourceFailure(err))) return false;
    return (try sdkPathIsZero(cache, expression, expected, walk, &.{"len"}, 0)) and
        (try sdkPathIsZero(cache, expression, expected, walk, &.{"capacity"}, 0));
}

/// The container a constructor's own declaration says it returns.
///
/// The CALL's own type is not that answer. A fallible SDK constructor is
/// declared `Allocator.Error!Self`, so the type of the call expression is an
/// error union, and the type engine unwraps no error union when it walks a
/// type toward its container — `containerOfNode` reads every fallible
/// constructor as "not a container at all", which refused the header the very
/// same call was proven to have built. The declared result type, unwrapped to
/// its payload, is what names that header; it is read from the canonical
/// declaration the compiler resolved, never from the spelling at the call.
fn constructorResultContainer(
    cache: *FileCache,
    call: TokenRange,
    walk: FreshWalk,
) FreshError!?type_engine.TypeResolver.ActualType.Data.Container {
    const canonical = (try canonicalCall(cache, call, walk)) orelse return null;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration) orelse return null;
    var returned = proto.ast.return_type.unwrap() orelse return null;
    while (canonical.callee.tree.nodeTag(returned) == .error_union) {
        try charge(walk.remaining);
        returned = canonical.callee.tree.nodeData(returned).node_and_node[1];
    }
    const resolver = if (canonical.callee.caller_frame) |caller|
        caller.resolver
    else
        cache.zls orelse return null;
    try charge(walk.remaining);
    // `returned` is a node of the CALLEE's own document, so it is read in the
    // callee's own frame — the frame `listConstructorProjection` reads the
    // same declaration through.
    return resolver.frameForFunction(canonical.callee.reference).containerOfNode(returned) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => null,
    };
}

/// The SDK constructor intrinsic proves its newly allocated slice, not an
/// allocator/interface field captured by a managed header. Every other
/// declared field must independently be address-free.
fn standardListFieldsIndependent(cache: *FileCache, call: TokenRange, walk: FreshWalk) FreshError!bool {
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    try charge(walk.remaining);
    const container = (try constructorResultContainer(cache, call, walk)) orelse return false;
    const frame = resolver.frameForContainer(container);
    const tree = &frame.handle.document.tree;
    var buffer: [2]Ast.Node.Index = undefined;
    const declared = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return false;
    var slices: u32 = 0;
    for (declared.ast.members) |member| {
        try charge(walk.remaining);
        const field = tree.fullContainerField(member) orelse continue;
        const type_node = field.ast.type_expr.unwrap() orelse return false;
        const ty = (frame.typeOfNode(type_node) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => null,
        }) orelse return false;
        if (try actualTypeAddressFree(frame, ty, 0, walk.remaining)) continue;
        // An unnamed pointer size is not the one single-slice field this
        // constructor is allowed to leave shared, so it proves nothing here.
        if ((frame.resolver.pointerSize(ty) orelse return false) != .slice) return false;
        slices += 1;
    }
    return slices == 1;
}

fn tree2(cache: *FileCache, n: Ast.Node.Index) []const u8 {
    return cache.tree.source[cache.tree.tokens.items(.start)[cache.tree.firstToken(n)]..cache.tree.tokens.items(.start)[cache.tree.lastToken(n)]];
}

fn numericValueIsZero(cache: *FileCache, value: Ast.Node.Index, walk: FreshWalk) FreshError!bool {
    const numeric_eval = @import("../flow/numeric_eval.zig");
    const budget_mod = @import("../budget.zig");
    // With no cache, facts, or alias table the evaluator cannot leave this
    // expression. Its source tokens bound all AST work, prepaid against the
    // caller's meter. Its own structural depth stop is merely inconclusive.
    const work = cache.tree.lastToken(value) - cache.tree.firstToken(value) + 1;
    if (walk.remaining) |remaining| {
        if (remaining.* < work) {
            remaining.* = 0;
            return error.AnalysisBudgetExceeded;
        }
        remaining.* -= work;
    }
    var local_work: u32 = work;
    var stopped: ?budget_mod.Stop = null;
    var evaluator: numeric_eval.Evaluator = .{
        .tree = cache.tree,
        .cache = null,
        .facts = &.{},
        .budget = &local_work,
        .std_valid = false,
        .budget_cap = work,
        .stopped = &stopped,
    };
    const value_range = evaluator.evaluate(value);
    if (stopped != null) return false;
    return value_range == .integer and value_range.integer.min == 0 and value_range.integer.max == 0;
}

/// An external allocator parameter is the allocator contract boundary; its
/// new allocations do not depend on this declaration's input payloads.
/// Explicitly constructed allocator headers are different: forwarding such a
/// header through a real SDK alloc method cannot erase its backing provenance.
fn allocatorOriginIsExternal(cache: *FileCache, expression: Ast.Node.Index, walk: FreshWalk, depth: u8) FreshError!bool {
    if (depth >= max_fresh_depth) return false;
    try charge(walk.remaining);
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    // `isStdAllocator` answers tri-state: `true` is the SDK allocator header,
    // `false` a resolved non-allocator, and null an identity this session
    // could not read.  Null proves nothing in either direction, so it reads
    // as "not an allocator" here and stops the route — never as a proof.
    const allocator_type = if (walk.frame) |frame| frame.isStdAllocator(expression) else resolver.isStdAllocator(expression);
    const is_std_allocator = ((allocator_type catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => false,
    }) orelse false);
    if (!is_std_allocator) return false;
    const tree = cache.tree;
    switch (tree.nodeTag(expression)) {
        .identifier => {
            const token = tree.nodeMainToken(expression);
            const declaration = tokens.enclosingFnDecl(tree, token) orelse return false;
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
            const body = tokens.bodyOf(tree, declaration) orelse return false;
            try charge(walk.remaining);
            const bindings = (try cache.localBindings(proto, body)).*;
            const binding = bindings.findAt(tree.tokenSlice(token), token) orelse return false;
            if (binding.origin == .param) return true;
            if (!binding.is_const or !try plainLocalStillIndependent(tree, &bindings, binding, token, walk.remaining)) return false;
            const initializer = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
            return allocatorOriginIsExternal(cache, initializer, walk, depth + 1);
        },
        .field_access => {
            const access = tree.nodeData(expression).node_and_token;
            var root = access[0];
            while (tree.nodeTag(root) == .field_access or tree.nodeTag(root) == .deref) {
                try charge(walk.remaining);
                root = if (tree.nodeTag(root) == .deref) tree.nodeData(root).node else tree.nodeData(root).node_and_token[0];
            }
            if (tree.nodeTag(root) == .identifier) {
                const token = tree.nodeMainToken(root);
                if (tokens.enclosingFnDecl(tree, token)) |declaration| {
                    var buffer: [1]Ast.Node.Index = undefined;
                    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
                    const body = tokens.bodyOf(tree, declaration) orelse return false;
                    try charge(walk.remaining);
                    const bindings = (try cache.localBindings(proto, body)).*;
                    if (bindings.findAt(tree.tokenSlice(token), token)) |binding| {
                        if (binding.origin == .param) return formalAllocatorRootUnchanged(tree, &bindings, binding, token, walk.remaining);
                    }
                }
            }
            // A genuine SDK heap constant is a process-lifetime allocator
            // contract, not a project field that merely spells page_allocator.
            try charge(walk.remaining);
            const owner = if (walk.frame) |frame| frame.containerOfNode(access[0]) else resolver.containerOfNode(access[0]);
            const container = (owner catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => null,
            }) orelse return false;
            if (!(resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/heap.zig") catch |err| return resourceFailure(err))) return false;
            const actual_owner: type_engine.TypeResolver.ActualType = .{ .data = .{ .container = container }, .is_type_val = true };
            const Analysis = @TypeOf(resolver.analyser);
            const member = tree.tokenSlice(access[1]);
            const global = (Analysis.lookupSymbolContainer(actual_owner, member, .other) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
            }) orelse return false;
            if (!global.isConst() or !(resolver.declaredInToolchainFile(global.handle, "/std/heap.zig") catch |err| return resourceFailure(err))) return false;
            const node = switch (global.decl) {
                .ast_node => |node| node,
                else => return false,
            };
            const source = (try actualSourceCache(cache, global.handle)) orelse return false;
            const variable = source.tree.fullVarDecl(node) orelse return false;
            const initializer = variable.ast.init_node.unwrap() orelse return false;
            var literal_buffer: [2]Ast.Node.Index = undefined;
            return source.tree.fullStructInit(&literal_buffer, initializer) != null;
        },
        .call, .call_comma, .call_one, .call_one_comma => {
            const canonical = (try canonicalCall(cache, .{ .first = tree.firstToken(expression), .last = tree.lastToken(expression) }, walk)) orelse return false;
            const summary = canonical.summary orelse return false;
            if (!summary.result_params_complete) return false;
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, expression) orelse return false;
            const offset = canonical.argument_offset orelse return false;
            const count = call.ast.params.len + offset;
            var found = false;
            for (0..count) |parameter| {
                try charge(walk.remaining);
                if (summary.returnedParamDependency(@intCast(parameter)) != true) continue;
                var argument_buffer: [1]Ast.Node.Index = undefined;
                const argument = (try canonical.callArgumentFor(cache, &argument_buffer, @intCast(parameter))) orelse return false;
                // A FixedBufferAllocator receiver is not an external
                // Allocator header. Its borrowed/frame buffer cannot become
                // independent through allocator() then SDK alloc().
                if (!try allocatorOriginIsExternal(cache, argument, walk, depth + 1)) return false;
                found = true;
            }
            return found;
        },
        else => return false,
    }
}

fn formalAllocatorRootUnchanged(tree: *const Ast, bindings: *const local_bindings.LocalBindings, binding: *const local_bindings.Binding, use: Ast.TokenIndex, remaining: ?*u32) FreshError!bool {
    var token = binding.scope_open + 1;
    while (token < use) : (token += 1) {
        try charge(remaining);
        if (tree.tokenTag(token) != .identifier or !std.mem.eql(u8, tree.tokenSlice(token), binding.name)) continue;
        const actual = bindings.findAt(binding.name, token) orelse continue;
        if (actual.name_token != binding.name_token) continue;
        if (token > 0 and tree.tokenTag(token - 1) == .ampersand) return false;
        var end = token + 1;
        while (end + 1 < use and tree.tokenTag(end) == .period and tree.tokenTag(end + 1) == .identifier) end += 2;
        if (end >= use) continue;
        switch (tree.tokenTag(end)) {
            .equal, .plus_equal, .minus_equal, .asterisk_equal, .slash_equal,
            .percent_equal, .ampersand_equal, .pipe_equal, .caret_equal,
            .angle_bracket_angle_bracket_left_equal, .angle_bracket_angle_bracket_right_equal,
            => return false,
            else => {},
        }
        if (end == token + 1 and (tree.tokenTag(end) == .comma or tree.tokenTag(end) == .r_paren)) return false;
    }
    return true;
}

/// File-model spelling locates candidate metadata; the actual instantiated
/// declaration must confirm its identity before that field list is trusted.
fn actualOwnerMatches(cache: *FileCache, range: TokenRange, owner: ResolvedType, walk: FreshWalk) FreshError!bool {
    const frame = walk.frame orelse return true;
    const node = cache.nodeForExactSpan(range.first, range.last) orelse return false;
    try charge(walk.remaining);
    const container = (frame.containerOfNode(node) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => null,
    }) orelse return false;
    const tree = &container.scope_handle.handle.document.tree;
    if (tree != owner.model.tree) return false;
    if (owner.info.body_first == 0) return container.scope_handle.scope == .root;
    return tree.lastToken(container.scope_handle.toNode()) == owner.info.body_last;
}

/// Only cleanup in a still-active scope is absent from a successful handoff.
/// Follow only the AST child containing this use, with no parent table,
/// allocation, tree-wide scan, or independent allowance.
fn tokenInsideActiveErrdefer(tree: *const Ast, body: Ast.Node.Index, token: Ast.TokenIndex, horizon: Ast.TokenIndex, remaining: ?*u32) FreshError!bool {
    const Iterator = type_engine.AstIterator;
    var current = body;
    var scope_close = tree.lastToken(body);
    while (true) {
        try charge(remaining);
        switch (tree.nodeTag(current)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => scope_close = tree.lastToken(current),
            .@"errdefer" => return horizon < scope_close,
            else => {},
        }
        var children = Iterator.init(tree, current);
        var containing: ?Ast.Node.Index = null;
        while (children.next(tree)) |child| {
            try charge(remaining);
            if (token >= tree.firstToken(child) and token <= tree.lastToken(child)) {
                containing = child;
                break;
            }
        }
        current = containing orelse return false;
    }
}

/// A known caller-side buffer allocator must not acquire the generic external
/// allocator contract merely by crossing a user-factory boundary. An unused
/// allocator operand is harmless only with both canonical no-result and
/// parameter-read-only evidence.
fn allocatorArgumentsSafeForResult(cache: *FileCache, canonical: FileCache.ActualCallSummary, walk: FreshWalk) FreshError!bool {
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    const tree = cache.tree;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, canonical.callee.call_node) orelse return false;
    const offset = canonical.argument_offset orelse return false;
    const count = call.ast.params.len + offset;
    for (0..count) |parameter| {
        try charge(walk.remaining);
        var buffer: [1]Ast.Node.Index = undefined;
        const argument = (try canonical.callArgumentFor(cache, &buffer, @intCast(parameter))) orelse return false;
        const kind = if (walk.frame) |frame| frame.isStdAllocator(argument) else resolver.isStdAllocator(argument);
        const is_std_allocator = ((kind catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => false,
        }) orelse false);
        if (!is_std_allocator) continue;
        if (try allocatorOriginIsExternal(cache, argument, walk, 0)) continue;
        const summary = canonical.summary orelse return false;
        if (summary.returnedParamDependency(@intCast(parameter)) != false) return false;
        const effect = (try cache.callEffectAt(calleeQueryToken(tree, call), .{
            .parameter = .{ .param = @intCast(parameter) },
        }, .{ .frame = walk.frame, .remaining = walk.remaining })) orelse return false;
        if (effect != .read_only) return false;
    }
    return true;
}
