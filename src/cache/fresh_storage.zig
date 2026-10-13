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
//! on the cache that holds it. `FileCache` owns expression verdicts, the
//! visiting set and the summary arena; functions borrow that cache.
//! `call_summary.State` separately owns completed canonical-type address-free
//! proofs. Those proofs skip non-field declarations, use the same query work
//! allowance, and never memoize a walk stopped by its work or depth bound.
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
const call_summary = @import("call_summary.zig");
const budget_mod = @import("../budget.zig");

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
/// Proves expression-laid-out buffers, static tag-name storage, actual SDK
/// allocation results, and constructors whose returned values are independent.
/// Aggregate fields are checked separately: address-free values can be copied, but each
/// address-bearing field needs independent allocation or independent literal
/// storage. Omitted fields keep the no-name, fully initialized default contract.
/// Computed try/catch/orelse values require independent storage in every
/// value-producing arm. Literal unreachable contributes no value. Memory
/// builtins may write scalar elements through nested views of fresh storage,
/// but cannot establish independence by copying pointer-bearing elements.
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

/// Unknown identity or provenance leaves a claim unproved. Source, policy,
/// cancellation, allocation, and attributed analysis-budget failures propagate
/// without entering the memo.
pub fn freshStorageAt(
    cache: *FileCache,
    walk: FreshWalk,
) FreshError!bool {
    if (walk.claim.first > walk.claim.last) return false;
    if (walk.spent()) return false;
    if (walk.frame) |frame| {
        if (&frame.handle.document.tree != cache.tree or frame.handle.module != cache.module_id) return false;
    }
    try charge(walk.remaining, cache.tree, walk.claim.first);
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
            try charge(walk.remaining, tree, tree.nodeMainToken(node));
            const empty = if (walk.frame) |frame| frame.stdCollectionEmptyOf(node, type_node) else resolver.stdCollectionEmptyOf(node, type_node);
            if (try empty) {
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
        try charge(walk.remaining, tree, first);
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
        try charge(walk.remaining, tree, t);
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
                        return try constructorBuildsFreshStorage(
                            cache,
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
    // An unreadable source is a failed query, not a negative storage proof.
    const model = try cache.fileModel();
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
    try charge(walk.remaining, cache.tree, call.first);
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

pub const AllocatorPrimitive = struct {
    operation: enum { allocate, replace, release },
    allocator_parameter: u32 = 0,
    previous_parameter: ?u32 = null,
    copies_elements: bool = false,
};

/// Authenticate the SDK declaration before assigning primitive semantics.
/// Replacement preserves a possible old-backing loan; it is never allocation.
pub fn allocatorPrimitive(
    cache: *FileCache,
    actual: FileCache.ActualCallSummary,
    walk: FreshWalk,
) FreshError!?AllocatorPrimitive {
    try charge(walk.remaining, cache.tree, walk.claim.first);
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return null;
    if (!try resolver.declaredInToolchainFile(actual.callee.handle, "/std/mem/Allocator.zig")) return null;
    const tree = actual.callee.tree;
    const token = actual.callee.fn_token + 1;
    if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return null;
    const name = tree.tokenSlice(token);
    if (std.mem.eql(u8, name, "dupe") or std.mem.eql(u8, name, "dupeZ"))
        return .{ .operation = .allocate, .copies_elements = true };
    if (std.mem.eql(u8, name, "alloc") or std.mem.eql(u8, name, "allocSentinel") or
        std.mem.eql(u8, name, "create") or std.mem.eql(u8, name, "rawAlloc"))
        return .{ .operation = .allocate };
    if (std.mem.eql(u8, name, "rawRemap") or std.mem.eql(u8, name, "realloc") or std.mem.eql(u8, name, "remap"))
        return .{ .operation = .replace, .previous_parameter = 1 };
    if (std.mem.eql(u8, name, "free") or std.mem.eql(u8, name, "destroy") or std.mem.eql(u8, name, "rawFree"))
        return .{ .operation = .release, .previous_parameter = 1 };
    return null;
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
    const std_tree = (try toolchainArrayListTree(cache, walk.frame)) orelse return false;
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
        try charge(walk.remaining, tree, reference.fn_token);
        declared += 1;
    }
    if (declared != actual.ast.params.len) return false;
    var receiver_buffer: [2]Ast.Node.Index = undefined;
    const allocator = (try canonical.callArgumentFor(cache, &receiver_buffer, 0)) orelse return false;
    return allocatorOriginIsExternal(cache, allocator, walk, 0);
}

/// Select the unique direct slice field of an authenticated list constructor's
/// actual return type. The caller first authenticates `standardListConstructor`
/// under the same canonical provided frame and enclosing work counter.
///
/// This is a structural selection only: it proves neither backing ownership,
/// lifetime, nor element initialization. Allocator-origin requirements remain
/// the caller's responsibility. Types borrow the canonical caller's original
/// resolver, and every edge spends the supplied enclosing work allowance.
pub fn listConstructorProjection(
    cache: *FileCache,
    canonical: FileCache.ActualCallSummary,
    selected_fields: []const []const u8,
    remaining: ?*u32,
) FreshError!bool {
    if (selected_fields.len != 1) return false;
    const resolver = if (canonical.callee.caller_frame) |caller|
        caller.resolver
    else
        cache.zls orelse return false;
    const resolution = resolver.frameForFunction(canonical.callee.reference);
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(
        canonical.callee.tree,
        &proto_buffer,
        canonical.callee.declaration,
    ) orelse return false;
    var returned_type = proto.ast.return_type.unwrap() orelse return false;
    while (canonical.callee.tree.nodeTag(returned_type) == .error_union) {
        try charge(remaining, canonical.callee.tree, canonical.callee.tree.nodeMainToken(returned_type));
        returned_type = canonical.callee.tree.nodeData(returned_type).node_and_node[1];
    }
    try charge(remaining, canonical.callee.tree, canonical.callee.tree.nodeMainToken(returned_type));
    const container = (try resolution.containerOfNode(returned_type)) orelse return false;
    const owner = resolver.frameForContainer(container);
    const tree = &owner.handle.document.tree;
    var container_buffer: [2]Ast.Node.Index = undefined;
    const declaration = tree.fullContainerDecl(
        &container_buffer,
        container.scope_handle.toNode(),
    ) orelse return false;
    var slices: usize = 0;
    var selected_slice = false;
    for (declaration.ast.members) |member| {
        try charge(remaining, tree, tree.nodeMainToken(member));
        const field = tree.fullContainerField(member) orelse continue;
        if (field.ast.tuple_like) return false;
        const field_type = field.ast.type_expr.unwrap() orelse return false;
        try charge(remaining, tree, tree.nodeMainToken(field_type));
        const actual_type = (try owner.typeOfNode(field_type)) orelse return false;
        if (resolver.pointerSize(actual_type) != .slice) continue;
        slices += 1;
        if (std.mem.eql(u8, tree.tokenSlice(field.ast.main_token), selected_fields[0]))
            selected_slice = true;
    }
    // The actual return declaration identifies the selected unique slice;
    // allocator/context fields gain no ownership from this structural fact.
    return slices == 1 and selected_slice;
}

/// This toolchain's own `std/array_list.zig`, read through the same document
/// store that resolves `@import("std")` in the supplied frame. Only a query
/// without a frame may select the cache's ordinary resolver.
///
/// The ordinary-context memo borrows that resolver's store-owned document.
/// A different supplied resolver cannot read or publish that memo; its
/// original context must outlive the query and every resulting type proof.
pub fn toolchainArrayListTree(
    cache: *FileCache,
    frame: ?type_engine.TypeResolver.ResolutionFrame,
) FreshError!?*const Ast {
    const resolver = if (frame) |provided| provided.resolver else cache.zls orelse return null;
    const ordinary_context = frame == null or cache.zls == resolver;
    if (ordinary_context) {
        switch (cache.std_list_tree) {
            .known => |tree| return tree,
            .absent => return null,
            .unknown => {},
        }
    }
    const configured_root = if (resolver.ctx.store.config.zig_lib_dir) |directory| directory.path else null;
    const library_path = configured_root orelse {
        if (ordinary_context) cache.std_list_tree = .absent;
        return null;
    };
    // `sourceHandle` addresses documents by absolute path; a
    // relative one is not a path this can read, not a toolchain.
    if (!std.fs.path.isAbsolute(library_path)) {
        if (ordinary_context) cache.std_list_tree = .absent;
        return null;
    }
    // A configured root that cannot be read is a failed query, not absent
    // configuration. Keep its allocation, cancellation and path errors typed.
    const library = try resolver.ctx.canonicalPath(library_path);
    const path = try std.fs.path.join(cache.gpa, &.{ library, "std", "array_list.zig" });
    defer cache.gpa.free(path);
    // Root and source-load failures leave this entry unknown so a later query
    // can retry the exact document. Only absent configuration is cached above.
    const handle = try resolver.ctx.sourceHandle(path, cache.module_id);
    // The document is a store-owned allocation reached through the
    // handle, so the address outlives the handle this function
    // received by value.
    if (ordinary_context) cache.std_list_tree = .{ .known = &handle.document.tree };
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
        try charge(walk.remaining, resolved.model.tree, field.type_first);
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
    try charge(walk.remaining, tree, tree.nodeMainToken(fn_decl));
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buf, fn_decl) orelse return false;
    const body = tokens.bodyOf(tree, fn_decl) orelse return false;
    // `return .{ … };` names no type, so the declaration's own
    // return type is what says which fields it filled in.
    const return_type = valueReturnType(tree, proto.ast.return_type.unwrap());
    const key: DeclKey = .{ .tree = tree, .module = cache.module_id, .declaration = fn_decl };
    if (cache.fresh_visiting.contains(key)) return false;
    try cache.fresh_visiting.put(cache.gpa, key, {});
    defer _ = cache.fresh_visiting.remove(key);
    var returns: u32 = 0;
    var walker = try type_engine.AstWalker.init(cache.gpa, tree, body);
    defer walker.deinit(cache.gpa);
    while (try walker.nextIgnoreClose(cache.gpa, tree)) |node| {
        try charge(walk.remaining, tree, tree.nodeMainToken(node));
        // A nested `fn`'s return is not this declaration's.
        if (tree.nodeTag(node) == .fn_decl) {
            walker.skip();
            continue;
        }
        if (walker.stack.items.len > 64) return located(tree, node, .fresh_storage_depth, 64, @intCast(walker.stack.items.len));
        if (tree.nodeTag(node) != .@"return") continue;
        const value = tree.nodeData(node).opt_node.unwrap() orelse continue;
        const first = tree.firstToken(value);
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
    try charge(remaining, cache.tree, 0);
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
    // Invalid source and model limits terminate this query. Neither is evidence
    // that the requested declaration is absent.
    const model = try cache.fileModel();
    var found: ?ResolvedType = null;
    for (model.types) |*ti| {
        try charge(remaining, model.tree, ti.body_first);
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
        try charge(remaining, tree, t);
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
        try charge(remaining, tree, t);
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
        try charge(remaining, tree, t);
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
        try charge(remaining, tree, first);
        if (first + 1 > last or tags[first + 1] != .l_paren) return false;
        const close = tokens.matchParen(tags, first + 1, last) orelse return false;
        if (close + 1 > last) return false;
        var depth: u32 = 0;
        var token = close + 1;
        while (token <= last) : (token += 1) {
            try charge(remaining, tree, token);
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
        try charge(remaining, tree, token);
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

fn definedValue(tree: *const Ast, range: TokenRange, remaining: ?*u32) FreshError!bool {
    if (range.first > range.last) return false;
    var token = range.first;
    while (token <= range.last) : (token += 1) {
        try charge(remaining, tree, token);
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
    try charge(walk.remaining, owner.model.tree, field.type_first);
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
            try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(type_node));
            const actual_type = (try frame.typeOfNode(type_node)) orelse return false;
            if (try actualTypeAddressFree(frame, actual_type, 0, walk.remaining)) return true;
        }
    }
    if (walk.frame) |frame| {
        if (cache.nodeForExactSpan(value.first, value.last)) |node| {
            switch (cache.tree.nodeTag(node)) {
                .identifier, .field_access, .deref => {
                    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(node));
                    const value_type = try frame.typeOfNode(node);
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
            try charge(remaining, tree, end);
            switch (tree.tokenTag(end)) {
                .l_paren, .l_bracket, .l_brace => nesting += 1,
                .r_paren, .r_bracket, .r_brace => if (nesting > 0) {
                    nesting -= 1;
                } else return null,
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
    if (cache.nodeForExactSpan(claim.first, claim.last)) |expression| {
        switch (tree.nodeTag(expression)) {
            .@"try", .grouped_expression => {
                const operand = if (tree.nodeTag(expression) == .@"try")
                    tree.nodeData(expression).node
                else
                    tree.nodeData(expression).node_and_token[0];
                var next = walk;
                next.claim = .{ .first = tree.firstToken(operand), .last = tree.lastToken(operand) };
                return try freshStorageAt(cache, next);
            },
            .@"catch", .@"orelse" => {
                const pair = tree.nodeData(expression).node_and_node;
                const operands = [_]@TypeOf(pair[0]){ pair[0], pair[1] };
                for (operands, 0..) |operand, index| {
                    try charge(walk.remaining, tree, tree.nodeMainToken(operand));
                    // Only literal unreachable has no alternative value. Calls
                    // and blocks must prove their returned storage normally.
                    if (index == 1 and tree.firstToken(operand) == tree.lastToken(operand) and
                        tree.tokenTag(tree.firstToken(operand)) == .keyword_unreachable) continue;
                    var next = walk;
                    next.claim = .{ .first = tree.firstToken(operand), .last = tree.lastToken(operand) };
                    if (!try freshStorageAt(cache, next)) return false;
                }
                return true;
            },
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                // Selection by an enum value does not copy or retain that
                // value's storage: Zig's tag-name bytes have static lifetime.
                if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(expression)), "@tagName"))
                    return true;
            },
            else => {},
        }
    }
    var first = claim.first;
    while (first < claim.last and tree.tokenTag(first) == .keyword_try) {
        try charge(walk.remaining, tree, first);
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
            if (try allocatorPrimitive(cache, canonical, walk)) |primitive| {
                if (primitive.operation != .allocate) return false;
                var receiver_buffer: [2]Ast.Node.Index = undefined;
                const receiver = (try canonical.callArgumentFor(cache, &receiver_buffer, primitive.allocator_parameter)) orelse return false;
                if (!try allocatorOriginIsExternal(cache, receiver, walk, 0)) return false;
                if (primitive.copies_elements)
                    return try sdkDuplicatedElementsAddressFree(cache, expression, walk);
                return true;
            }
            if (try standardListConstructor(cache, range, walk)) return try standardListFieldsIndependent(cache, range, walk);
            if (if (walk.frame) |frame| frame.resolver else cache.zls) |resolver| {
                if (try resolver.declaredInToolchainFile(canonical.callee.handle, "/std/array_list.zig")) {
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
    if (!try plainLocalStillIndependent(cache, &bindings, binding, claim.first, walk)) return false;
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
        try charge(walk.remaining, resolved.model.tree, field.type_first);
        var value: ?TokenRange = null;
        if (literal) |init| {
            for (init.ast.fields) |node| {
                try charge(walk.remaining, tree, tree.nodeMainToken(node));
                const first = tree.firstToken(node);
                if (first < 2 or !std.mem.eql(u8, tree.tokenSlice(first - 2), field.name)) continue;
                value = .{ .first = first, .last = tree.lastToken(node) };
            }
        }
        var token = binding.rhs_last + 1;
        while (token < claim.first) : (token += 1) {
            try charge(walk.remaining, tree, token);
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
                try charge(walk.remaining, tree, end);
                switch (tree.tokenTag(end)) {
                    .l_paren, .l_bracket, .l_brace => nesting += 1,
                    .r_paren, .r_bracket, .r_brace => if (nesting > 0) {
                        nesting -= 1;
                    } else return false,
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
    for (tree.tokens.items(.tag)[open + 1 .. use], open + 1..) |tag, raw| {
        try charge(remaining, tree, @intCast(raw));
        switch (tag) {
            .l_brace => depth += 1,
            .r_brace => if (depth > 0) {
                depth -= 1;
            } else return false,
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
    cache: *FileCache,
    bindings: *const local_bindings.LocalBindings,
    binding: *const local_bindings.Binding,
    use: Ast.TokenIndex,
    walk: FreshWalk,
) FreshError!bool {
    const tree = cache.tree;
    const remaining = walk.remaining;
    const declaration = tokens.enclosingFnDecl(tree, use) orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    var token = binding.rhs_last + 1;
    while (token < use) : (token += 1) {
        try charge(remaining, tree, token);
        if (tree.tokenTag(token) != .identifier or !std.mem.eql(u8, tree.tokenSlice(token), binding.name)) continue;
        if (token > 0 and tree.tokenTag(token - 1) == .period) continue;
        const actual = bindings.findAt(binding.name, token) orelse continue;
        if (actual.name_token != binding.name_token) continue;
        if (try tokenInsideActiveErrdefer(tree, body, token, use, remaining)) continue;
        if (token > 0 and tree.tokenTag(token - 1) == .keyword_return) continue;
        var safe_builtin = false;
        var opener = binding.rhs_last + 1;
        while (opener < token) : (opener += 1) {
            try charge(remaining, tree, opener);
            if (tree.tokenTag(opener) != .builtin or !tokens.isWriteFirstArgBuiltin(tree.tokenSlice(opener))) continue;
            if (opener + 1 >= token or tree.tokenTag(opener + 1) != .l_paren) continue;
            const close = tokens.matchParen(tree.tokens.items(.tag), opener + 1, use) orelse continue;
            if (token >= close) continue;
            if (try independentBuiltinArgument(cache, opener, token, close, walk)) {
                safe_builtin = true;
                break;
            }
        }
        if (!safe_builtin) return false;
    }
    return true;
}

/// Memory writes change elements, not the slice header used to reach them.
/// That is independence-preserving only for address-free destination elements.
fn independentBuiltinArgument(
    cache: *FileCache,
    opener: Ast.TokenIndex,
    token: Ast.TokenIndex,
    close: Ast.TokenIndex,
    walk: FreshWalk,
) FreshError!bool {
    const tree = cache.tree;
    const builtin = cache.nodeForExactSpan(opener, close) orelse return false;
    var arguments = type_engine.AstIterator.init(tree, builtin);
    var index: usize = 0;
    while (arguments.next(tree)) |argument| : (index += 1) {
        try charge(walk.remaining, tree, tree.nodeMainToken(argument));
        if (token < tree.firstToken(argument) or token > tree.lastToken(argument)) continue;
        if (index != 0) {
            // A source value is read, not retained. Taking &header or evaluating
            // a call involving the header is not a direct source value.
            return tree.nodeTag(argument) == .identifier and tree.nodeMainToken(argument) == token;
        }
        var root = argument;
        while (true) {
            try charge(walk.remaining, tree, tree.nodeMainToken(root));
            if (tree.fullSlice(root)) |slice| {
                if (!try memoryIndexIsPure(tree, slice.ast.start, walk.remaining, 0)) return false;
                if (slice.ast.end.unwrap()) |end| {
                    if (!try memoryIndexIsPure(tree, end, walk.remaining, 0)) return false;
                }
                if (slice.ast.sentinel.unwrap()) |sentinel| {
                    if (!try memoryIndexIsPure(tree, sentinel, walk.remaining, 0)) return false;
                }
                root = slice.ast.sliced;
            } else if (tree.nodeTag(root) == .array_access) {
                const operands = tree.nodeData(root).node_and_node;
                if (!try memoryIndexIsPure(tree, operands[1], walk.remaining, 0)) return false;
                root = operands[0];
            } else break;
        }
        if (tree.nodeTag(root) != .identifier or tree.nodeMainToken(root) != token) return false;
        const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
        const frame = walk.frame orelse resolver.resolutionFrame();
        try charge(walk.remaining, tree, tree.nodeMainToken(argument));
        const destination = (try frame.typeOfNode(argument)) orelse return false;
        const tag = resolver.typeTag(destination);
        if (tag != .pointer and tag != .array) return false;
        const element = resolver.childType(destination) orelse return false;
        return try actualTypeAddressFree(frame, element, 0, walk.remaining);
    }
    return false;
}

/// Bounds can read scalars, but cannot execute unknown calls or stores while
/// forming a destination. Their spelling never grants an effect exemption.
fn memoryIndexIsPure(tree: *const Ast, node: Ast.Node.Index, remaining: ?*u32, depth: u8) FreshError!bool {
    if (depth > max_fresh_depth) return false;
    try charge(remaining, tree, tree.nodeMainToken(node));
    switch (tree.nodeTag(node)) {
        .number_literal, .char_literal, .identifier => return true,
        .field_access => return memoryIndexIsPure(tree, tree.nodeData(node).node_and_token[0], remaining, depth + 1),
        .grouped_expression => return memoryIndexIsPure(tree, tree.nodeData(node).node_and_token[0], remaining, depth + 1),
        .negation, .bit_not => return memoryIndexIsPure(tree, tree.nodeData(node).node, remaining, depth + 1),
        .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor => {
            const operands = tree.nodeData(node).node_and_node;
            return try memoryIndexIsPure(tree, operands[0], remaining, depth + 1) and
                try memoryIndexIsPure(tree, operands[1], remaining, depth + 1);
        },
        else => return false,
    }
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
        \\fn rebound(input: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    out.bytes = input;
        \\    return out;
        \\}
        \\fn escaped() Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    publish(&out);
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
    for ([_][]const u8{ "borrowed", "incomplete", "conditional", "rebound", "escaped" }) |name| {
        try std.testing.expect(!try declBuildsFreshStorage(&cache, &tree, model.findFn(name).?.fn_decl, .root(.{ .first = 0, .last = 0 })));
    }
}

/// Freshness of the single value each `return` of `fn_decl` hands back,
/// asked of the fresh-storage prover alone (no handoff/lifetime stage), so a
/// verdict here is this module's own contract for the returned claim.
fn returnedClaimsFresh(cache: *FileCache, tree: *const Ast, fn_decl: Ast.Node.Index) !bool {
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, fn_decl).?;
    const body = tokens.bodyOf(tree, fn_decl).?;
    const return_type = valueReturnType(tree, proto.ast.return_type.unwrap());
    var walker = try type_engine.AstWalker.init(cache.gpa, tree, body);
    defer walker.deinit(cache.gpa);
    var verdict: ?bool = null;
    while (try walker.nextIgnoreClose(cache.gpa, tree)) |node| {
        if (tree.nodeTag(node) != .@"return") continue;
        const value = tree.nodeData(node).opt_node.unwrap().?;
        const fresh = try freshStorageAt(cache, .root(.{
            .first = tree.firstToken(value),
            .last = tree.lastToken(value),
            .type_first = if (return_type) |rt| tree.firstToken(rt) else null,
            .type_last = if (return_type) |rt| tree.lastToken(rt) else null,
        }));
        verdict = (verdict orelse true) and fresh;
    }
    return verdict.?;
}

test "computed owned selectors prove freshness only when no borrowed field can be selected" {
    const source: [:0]const u8 =
        \\const Packet = struct { bytes: []const u8, other: []const u8, level: u32 };
        \\const Kind = enum { first, second };
        \\const Config = struct { level: u32 };
        \\const Holder = struct { bytes: []const u8 };
        \\fn directStores() Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    return out;
        \\}
        \\fn scalarValueSelected(cfg: Config, comptime name: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = &[_]u8{2};
        \\    out.level = @field(cfg, name);
        \\    return out;
        \\}
        \\fn tagNameStored(kind: Kind) Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = @tagName(kind);
        \\    out.level = 0;
        \\    return out;
        \\}
        \\fn tagNameLiteral(kind: Kind) Packet {
        \\    return .{ .bytes = &[_]u8{1}, .other = @tagName(kind), .level = 0 };
        \\}
        \\fn scalarLiteralSelected(cfg: Config, comptime name: []const u8) Packet {
        \\    return .{ .bytes = &[_]u8{1}, .other = &[_]u8{2}, .level = @field(cfg, name) };
        \\}
        \\fn borrowedDirect(input: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = input;
        \\    out.level = 0;
        \\    return out;
        \\}
        \\fn fieldStoreBorrowedSibling(comptime name: []const u8, input: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.other = input;
        \\    out.level = 0;
        \\    @field(out, name) = &[_]u8{1};
        \\    return out;
        \\}
        \\fn fieldStoreBorrowedValue(comptime name: []const u8, input: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    @field(out, name) = input;
        \\    return out;
        \\}
        \\fn fieldStoreAllOwned(comptime name: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.level = 0;
        \\    @field(out, name) = &[_]u8{1};
        \\    out.other = &[_]u8{2};
        \\    return out;
        \\}
        \\fn fieldStoreLiteralName() Packet {
        \\    var out: Packet = undefined;
        \\    out.level = 0;
        \\    @field(out, "bytes") = &[_]u8{1};
        \\    @field(out, "other") = &[_]u8{2};
        \\    return out;
        \\}
        \\fn inlineForOwned() Packet {
        \\    var out: Packet = undefined;
        \\    out.level = 0;
        \\    inline for (.{ "bytes", "other" }) |name| {
        \\        @field(out, name) = &[_]u8{1};
        \\    }
        \\    return out;
        \\}
        \\fn inlineForBorrowed(input: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.level = 0;
        \\    inline for (.{ "bytes", "other" }) |name| {
        \\        @field(out, name) = if (name.len == 5) &[_]u8{1} else input;
        \\    }
        \\    return out;
        \\}
        \\fn switchStoreOwned(kind: Kind) Packet {
        \\    var out: Packet = undefined;
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    switch (kind) {
        \\        .first => out.bytes = &[_]u8{1},
        \\        .second => out.bytes = &[_]u8{3},
        \\    }
        \\    return out;
        \\}
        \\fn switchStoreBorrowed(kind: Kind, input: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    switch (kind) {
        \\        .first => out.bytes = &[_]u8{1},
        \\        .second => out.bytes = input,
        \\    }
        \\    return out;
        \\}
        \\fn switchBlockStore(kind: Kind, input: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    switch (kind) {
        \\        .first => { out.bytes = &[_]u8{1}; },
        \\        .second => { out.bytes = input; },
        \\    }
        \\    return out;
        \\}
        \\fn slotPointerStore(comptime name: []const u8, input: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    const slot = &@field(out, name);
        \\    slot.* = input;
        \\    return out;
        \\}
        \\fn fieldValueBorrowed(holder: Holder, comptime name: []const u8) Packet {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = @field(holder, name);
        \\    out.level = 0;
        \\    return out;
        \\}
        \\fn literalFieldValueBorrowed(holder: Holder, comptime name: []const u8) Packet {
        \\    return .{ .bytes = &[_]u8{1}, .other = @field(holder, name), .level = 0 };
        \\}
        \\fn literalIfSelected(flag: bool, input: []const u8) Packet {
        \\    return .{ .bytes = &[_]u8{1}, .other = if (flag) &[_]u8{2} else input, .level = 0 };
        \\}
        \\fn literalSwitchBorrowed(kind: Kind, input: []const u8) Packet {
        \\    return .{ .bytes = &[_]u8{1}, .other = switch (kind) { .first => &[_]u8{2}, .second => input }, .level = 0 };
        \\}
        \\fn literalSwitchOwned(kind: Kind) Packet {
        \\    return .{ .bytes = &[_]u8{1}, .other = switch (kind) { .first => &[_]u8{2}, .second => &[_]u8{3} }, .level = 0 };
        \\}
        \\fn literalIndexSelected(index: usize) Packet {
        \\    const own = [_][]const u8{ &[_]u8{1}, &[_]u8{2} };
        \\    return .{ .bytes = own[index], .other = &[_]u8{2}, .level = 0 };
        \\}
        \\fn returnedFieldSelection(comptime name: []const u8) []const u8 {
        \\    var out: Packet = undefined;
        \\    out.bytes = &[_]u8{1};
        \\    out.other = &[_]u8{2};
        \\    out.level = 0;
        \\    return @field(out, name);
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const model = try cache.fileModel();

    // Safe controls: every selected value is independent, initialized, or
    // address-free. A static store, a scalar read through a computed
    // selector, and an enum-tag name (static lifetime) all prove.
    for ([_][]const u8{
        "directStores",
        "scalarValueSelected",
        "tagNameStored",
        "tagNameLiteral",
        "scalarLiteralSelected",
    }) |name| {
        errdefer std.debug.print("expected fresh: {s}\n", .{name});
        try std.testing.expect(try returnedClaimsFresh(&cache, &tree, model.findFn(name).?.fn_decl));
    }
    try std.testing.expect(try declBuildsFreshStorage(&cache, &tree, model.findFn("directStores").?.fn_decl, .root(.{ .first = 0, .last = 0 })));

    // Unsafe controls and unresolved selectors. A store through `@field`
    // with a runtime/comptime name, an inline-for, or a switch prong is not a
    // definite statement-level store of one named field, so the returned
    // local is never proved fresh; the verdict is unproven, not fresh, even
    // when every selectable value happens to be owned (the conservative
    // `fieldStoreAllOwned`, `inlineForOwned`, `switchStoreOwned`,
    // `literalSwitchOwned` cases) and certainly when a borrowed sibling or
    // borrowed value can be reached.
    for ([_][]const u8{
        "borrowedDirect",
        "fieldStoreBorrowedSibling",
        "fieldStoreBorrowedValue",
        "fieldStoreAllOwned",
        "fieldStoreLiteralName",
        "inlineForOwned",
        "inlineForBorrowed",
        "switchStoreOwned",
        "switchStoreBorrowed",
        "switchBlockStore",
        "slotPointerStore",
        "fieldValueBorrowed",
        "literalFieldValueBorrowed",
        "literalIfSelected",
        "literalSwitchBorrowed",
        "literalSwitchOwned",
        "literalIndexSelected",
        "returnedFieldSelection",
    }) |name| {
        errdefer std.debug.print("expected not fresh: {s}\n", .{name});
        const fn_decl = model.findFn(name).?.fn_decl;
        try std.testing.expect(!try returnedClaimsFresh(&cache, &tree, fn_decl));
        try std.testing.expect(!try declBuildsFreshStorage(&cache, &tree, fn_decl, .root(.{ .first = 0, .last = 0 })));
    }
}

test "aggregate allocation correlation uses actual SDK receiver identity" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Packet = struct { bytes: []const u8, level: u32 };
        \\const GraphPacket = struct { bytes: [][]const u8 };
        \\fn shallowGraph(gpa: std.mem.Allocator, bytes: [][]const u8) !GraphPacket {
        \\    return .{ .bytes = try gpa.dupe([]const u8, bytes) };
        \\}
        \\fn copiedGraph(gpa: std.mem.Allocator, bytes: [][]const u8) !GraphPacket {
        \\    const own = try gpa.alloc([]const u8, bytes.len);
        \\    @memcpy(own, bytes);
        \\    return .{ .bytes = own };
        \\}
        \\const Source = struct {
        \\    gpa: std.mem.Allocator,
        \\    bytes: []const u8,
        \\    level: u32,
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
        \\fn fieldLive(gpa: std.mem.Allocator) !Packet {
        \\    var out: Packet = undefined;
        \\    const own = try gpa.alloc(u8, 1);
        \\    out.bytes = own;
        \\    out.level = 0;
        \\    return out;
        \\}
        \\fn fieldFreed(gpa: std.mem.Allocator) !Packet {
        \\    var out: Packet = undefined;
        \\    const own = try gpa.alloc(u8, 1);
        \\    out.bytes = own;
        \\    out.level = 0;
        \\    gpa.free(own);
        \\    return out;
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
        \\fn arenaOwned(gpa: std.mem.Allocator, n: usize) !Packet {
        \\    var arena = std.heap.ArenaAllocator.init(gpa);
        \\    defer arena.deinit();
        \\    const local_gpa = arena.allocator();
        \\    return .{ .bytes = try local_gpa.alloc(u8, n), .level = 0 };
        \\}
        \\fn catchCopy(gpa: std.mem.Allocator, bytes: []const u8) []u8 {
        \\    const own = gpa.alloc(u8, bytes.len) catch unreachable;
        \\    @memcpy(own[0..][0..bytes.len], bytes);
        \\    return own;
        \\}
        \\fn catchOwned(gpa: std.mem.Allocator) []u8 {
        \\    return gpa.alloc(u8, 1) catch (gpa.alloc(u8, 2) catch unreachable);
        \\}
        \\fn catchBorrowed(gpa: std.mem.Allocator, bytes: []u8) []u8 {
        \\    return gpa.alloc(u8, 1) catch bytes;
        \\}
        \\fn unreachableValue(bytes: []u8) []u8 { return bytes; }
        \\fn catchCalled(gpa: std.mem.Allocator, bytes: []u8) []u8 {
        \\    return gpa.alloc(u8, 1) catch unreachableValue(bytes);
        \\}
        \\fn catchBlock(gpa: std.mem.Allocator, bytes: []u8) []u8 {
        \\    return gpa.alloc(u8, 1) catch blk: { break :blk bytes; };
        \\}
        \\fn optionalOwned(gpa: std.mem.Allocator) ?[]u8 {
        \\    return gpa.alloc(u8, 1) catch unreachable;
        \\}
        \\fn orelseOwned(gpa: std.mem.Allocator) []u8 {
        \\    return optionalOwned(gpa) orelse (gpa.alloc(u8, 2) catch unreachable);
        \\}
        \\fn orelseBorrowed(gpa: std.mem.Allocator, bytes: []u8) []u8 {
        \\    return optionalOwned(gpa) orelse bytes;
        \\}
        \\fn rebound(gpa: std.mem.Allocator, bytes: []u8) ![]u8 {
        \\    var own = try gpa.alloc(u8, bytes.len);
        \\    own = bytes;
        \\    return own;
        \\}
        \\fn copiedPointers(gpa: std.mem.Allocator, bytes: [][]const u8) ![][]const u8 {
        \\    const own = try gpa.alloc([]const u8, bytes.len);
        \\    @memcpy(own[0..][0..bytes.len], bytes);
        \\    return own;
        \\}
        \\fn unknownCall(gpa: std.mem.Allocator, make: *const fn (std.mem.Allocator) []u8) []u8 {
        \\    return make(gpa);
        \\}
        \\const AllocNamed = struct {
        \\    fn alloc(_: AllocNamed, bytes: []const u8) []const u8 { return bytes; }
        \\};
        \\fn customAlloc(bytes: []const u8) []const u8 {
        \\    return (AllocNamed{}).alloc(bytes);
        \\}
        \\fn claims(value: Source, gpa: std.mem.Allocator, bytes: []u8, graph: [][]const u8, make: *const fn (std.mem.Allocator) []u8) !void {
        \\    const annotated: Source = value;
        \\    _ = annotated.shallow();
        \\    _ = try annotated.unrelated();
        \\    _ = mimic(.{ .bytes = bytes }, bytes);
        \\    _ = try allocated(gpa, bytes);
        \\    _ = try shallowGraph(gpa, graph);
        \\    _ = try copiedGraph(gpa, graph);
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
        \\    _ = try fieldLive(gpa);
        \\    _ = try fieldFreed(gpa);
        \\    _ = try heapPage(3);
        \\    _ = try arenaOwned(gpa, 3);
        \\    _ = catchCopy(gpa, bytes);
        \\    _ = catchOwned(gpa);
        \\    _ = catchBorrowed(gpa, bytes);
        \\    _ = orelseOwned(gpa);
        \\    _ = orelseBorrowed(gpa, bytes);
        \\    _ = try rebound(gpa, bytes);
        \\    _ = try copiedPointers(gpa, graph);
        \\    _ = unknownCall(gpa, make);
        \\    _ = customAlloc(bytes);
        \\    _ = catchCalled(gpa, bytes);
        \\    _ = catchBlock(gpa, bytes);
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
        const independent = std.mem.eql(u8, name, "allocated") or std.mem.eql(u8, name, "heapPage") or
            std.mem.eql(u8, name, "errorDeferred") or std.mem.eql(u8, name, "aliasLive") or
            std.mem.eql(u8, name, "unrelatedDeferred") or std.mem.eql(u8, name, "unusedAllocator") or
            std.mem.eql(u8, name, "catchCopy") or std.mem.eql(u8, name, "catchOwned") or std.mem.eql(u8, name, "orelseOwned") or
            std.mem.eql(u8, name, "fieldLive");
        const borrowed = std.mem.eql(u8, name, "shallow") or std.mem.eql(u8, name, "unrelated") or
            std.mem.eql(u8, name, "mimic") or std.mem.eql(u8, name, "identity") or std.mem.eql(u8, name, "freed") or
            std.mem.eql(u8, name, "receiverBuffered") or std.mem.eql(u8, name, "frameBuffered") or
            std.mem.eql(u8, name, "deferred") or std.mem.eql(u8, name, "aliasDeferred") or
            std.mem.eql(u8, name, "forwardedBuffered") or std.mem.eql(u8, name, "forwardedReceiver") or
            std.mem.eql(u8, name, "shallowGraph") or std.mem.eql(u8, name, "copiedGraph") or
            std.mem.eql(u8, name, "arenaOwned") or std.mem.eql(u8, name, "catchBorrowed") or
            std.mem.eql(u8, name, "orelseBorrowed") or std.mem.eql(u8, name, "rebound") or
            std.mem.eql(u8, name, "copiedPointers") or std.mem.eql(u8, name, "unknownCall") or std.mem.eql(u8, name, "customAlloc") or
            std.mem.eql(u8, name, "catchCalled") or std.mem.eql(u8, name, "catchBlock") or std.mem.eql(u8, name, "fieldFreed");
        if (!independent and !borrowed) continue;
        const claim: fn_summary.FreshClaim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) };
        const verdict = try provesFreshStorage(&cache, claim, null);
        if (verdict != independent)
            std.debug.print("fresh storage case `{s}`: expected {any}, found {any}\n", .{ name, independent, verdict });
        try std.testing.expectEqual(independent, verdict);
    }
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

fn charge(remaining: ?*u32, tree: *const Ast, token: Ast.TokenIndex) FreshError!void {
    const allowance = remaining orelse return;
    if (allowance.* == 0) return locatedToken(tree, token, .fresh_storage_work, call_summary.actual_query_work_limit, call_summary.actual_query_work_limit);
    allowance.* -= 1;
}

/// Record that the shared work meter ran out while proving `node` fresh.
fn workFailure(tree: *const Ast, node: Ast.Node.Index) budget_mod.BudgetError {
    return located(tree, node, .fresh_storage_work, call_summary.actual_query_work_limit, call_summary.actual_query_work_limit);
}

/// Record a labelled budget failure anchored on `node`'s main token, naming
/// the enclosing function when there is one.
fn located(tree: *const Ast, node: Ast.Node.Index, limit: budget_mod.Limit, limit_value: u32, reached: u32) budget_mod.BudgetError {
    return locatedToken(tree, tree.nodeMainToken(node), limit, limit_value, reached);
}

fn locatedToken(tree: *const Ast, token: Ast.TokenIndex, limit: budget_mod.Limit, limit_value: u32, reached: u32) budget_mod.BudgetError {
    const byte = tree.tokenStart(token);
    const lc = budget_mod.lineCol(tree.source, byte);
    var name: budget_mod.NameBuf = .{};
    if (tokens.enclosingFnDecl(tree, token)) |decl| {
        var buffer: [1]Ast.Node.Index = undefined;
        if (tokens.fnProto(tree, &buffer, decl)) |proto| {
            if (proto.name_token) |name_token| name.set(tree.tokenSlice(name_token));
        }
    }
    return budget_mod.fail(.{
        .limit = limit,
        .limit_value = limit_value,
        .reached = reached,
        .byte = byte,
        .document = budget_mod.documentForTree(tree),
        .line = lc.line,
        .column = lc.column,
        .function = name,
    });
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
    budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, provesFreshStorage(&cache, claim.?, &remaining));
    const recorded = budget_mod.take().?;
    try std.testing.expectEqual(budget_mod.Limit.fresh_storage_work, recorded.limit);
    try std.testing.expectEqual(call_summary.actual_query_work_limit, recorded.limit_value);
    try std.testing.expectEqual(tree.tokenStart(claim.?.first), recorded.byte);
    try std.testing.expectEqualStrings("make", recorded.function.slice());
    try std.testing.expect(recorded.line != 0 and recorded.column != 0);
    try std.testing.expectEqual(@as(u32, 0), cache.fresh_storage.count());
    try std.testing.expect(try provesFreshStorage(&cache, claim.?, null));
    remaining = 1;
    try std.testing.expect(try provesFreshStorage(&cache, claim.?, &remaining));
    try std.testing.expectEqual(@as(u32, 0), remaining);
    try std.testing.expectError(error.AnalysisBudgetExceeded, provesFreshStorage(&cache, claim.?, &remaining));
}

test "invalid source aborts a fresh query without publishing a negative verdict" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "fn claim() void { _ = Missing{}; } fn broken(", .zig);
    defer tree.deinit(gpa);
    try std.testing.expect(tree.errors.len != 0);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    try std.testing.expectError(error.InvalidSyntax, resolveDeclaredType(&cache, "Missing", 0, null));
    var observed = false;
    for (tree.nodes.items(.tag), 0..) |_, raw_node| {
        const node: Ast.Node.Index = @enumFromInt(raw_node);
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = tree.fullStructInit(&buffer, node) orelse continue;
        const type_node = literal.ast.type_expr.unwrap() orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.firstToken(type_node)), "Missing")) continue;
        const claim: fn_summary.FreshClaim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) };
        try std.testing.expectError(error.InvalidSyntax, provesFreshStorage(&cache, claim, null));
        try std.testing.expectEqual(@as(u32, 0), cache.fresh_storage.count());
        observed = true;
    }
    try std.testing.expect(observed);
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
        \\        fn held(value: OwnedMap) OwnedMap { return value; }
        \\        fn indirect(value: OwnedMap) OwnedMap { return held(value); }
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
        \\    var h = Factory(u32, u32).indirect(shared);
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

const SuppliedListTest = struct {
    context: type_engine.TypeContext,
    resolver: type_engine.TypeResolver,

    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Alias = std.array_list.Managed(u8);
        \\var borrowed_bytes: [2]u8 = .{ 1, 2 };
        \\const Managed = struct {
        \\    items: []u8,
        \\    pub fn init(_: std.mem.Allocator) Managed { return .{ .items = &borrowed_bytes }; }
        \\    pub fn initCapacity(_: std.mem.Allocator, _: usize) !Managed { return init(undefined); }
        \\};
        \\fn claims(gpa: std.mem.Allocator) !void {
        \\    const direct_init = std.array_list.Managed(u8).init(gpa);
        \\    const direct_capacity = try std.array_list.Managed(u8).initCapacity(gpa, 4);
        \\    const alias_init = Alias.init(gpa);
        \\    const foreign_init = Managed.init(gpa);
        \\    const foreign_capacity = try Managed.initCapacity(gpa, 4);
        \\    const unresolved = Missing.init(gpa);
        \\    _ = direct_init; _ = direct_capacity; _ = alias_init;
        \\    _ = foreign_init; _ = foreign_capacity; _ = unresolved;
        \\}
        \\fn unsafeClaims() !void {
        \\    var bytes: [16]u8 = undefined;
        \\    var fba = std.heap.FixedBufferAllocator.init(&bytes);
        \\    const local_gpa = fba.allocator();
        \\    const unsafe_init = std.array_list.Managed(u8).init(local_gpa);
        \\    const unsafe_capacity = try std.array_list.Managed(u8).initCapacity(local_gpa, 4);
        \\    _ = unsafe_init; _ = unsafe_capacity;
        \\}
        \\fn Factory(comptime Collection: type) type {
        \\    return struct {
        \\        pub fn genericClaims(gpa: std.mem.Allocator) !void {
        \\            const LocalAlias = Collection;
        \\            const generic_init = Collection.init(gpa);
        \\            const generic_capacity = try Collection.initCapacity(gpa, 4);
        \\            const generic_alias = LocalAlias.init(gpa);
        \\            _ = generic_init; _ = generic_capacity; _ = generic_alias;
        \\        }
        \\    };
        \\}
        \\fn use(gpa: std.mem.Allocator) !void {
        \\    const sdk_invocation = try Factory(Alias).genericClaims(gpa);
        \\    const foreign_invocation = try Factory(Managed).genericClaims(gpa);
        \\    _ = sdk_invocation; _ = foreign_invocation;
        \\}
    ;

    fn init(gpa: std.mem.Allocator, text: [:0]const u8) !*SuppliedListTest {
        const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
        defer gpa.free(cwd);
        const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-supplied-list-frame-test.zig" });
        defer gpa.free(path);
        return initAt(gpa, path, text);
    }

    fn initAt(gpa: std.mem.Allocator, path: []const u8, text: [:0]const u8) !*SuppliedListTest {
        const self = try gpa.create(SuppliedListTest);
        errdefer gpa.destroy(self);
        try self.context.init(gpa, std.testing.io);
        errdefer self.context.deinit();
        try self.resolver.init(&self.context, gpa, path, text);
        errdefer self.resolver.deinit();
        try std.testing.expectEqual(@as(usize, 0), self.tree().errors.len);
        return self;
    }

    fn deinit(self: *SuppliedListTest, gpa: std.mem.Allocator) void {
        self.resolver.deinit();
        self.context.deinit();
        gpa.destroy(self);
    }

    fn tree(self: *SuppliedListTest) *const Ast {
        return &self.resolver.handle.document.tree;
    }

    fn cache(self: *SuppliedListTest, gpa: std.mem.Allocator) FileCache {
        var result = FileCache.init(gpa, self.tree());
        result.module_id = self.resolver.handle.module;
        return result;
    }
};

const SuppliedListSite = struct {
    node: Ast.Node.Index,
    body: Ast.Node.Index,
    binding_token: Ast.TokenIndex,
    claim: fn_summary.FreshClaim,
};

fn suppliedListSite(tree: *const Ast, function_name: []const u8, binding_name: []const u8) !SuppliedListSite {
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        if (raw == 0) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const declaration = tree.fullVarDecl(node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(declaration.ast.mut_token + 1), binding_name)) continue;
        const function = tokens.enclosingFnDecl(tree, tree.firstToken(node)) orelse continue;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, function) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(proto.name_token orelse continue), function_name)) continue;
        var value = declaration.ast.init_node.unwrap() orelse return error.TestExpectedInitializer;
        if (tree.nodeTag(value) == .@"try") value = tree.nodeData(value).node;
        return .{
            .node = value,
            .body = tokens.bodyOf(tree, function) orelse return error.TestExpectedBody,
            .binding_token = declaration.ast.mut_token + 1,
            .claim = .{ .first = tree.firstToken(value), .last = tree.lastToken(value) },
        };
    }
    return error.TestExpectedBinding;
}

fn suppliedListFrame(
    typed: *SuppliedListTest,
    cache: *FileCache,
    invocation_name: []const u8,
) !type_engine.TypeResolver.ResolutionFrame {
    const site = try suppliedListSite(typed.tree(), "use", invocation_name);
    var buffer: [1]Ast.Node.Index = undefined;
    const call = typed.tree().fullCall(&buffer, site.node) orelse return error.TestExpectedCall;
    const actual = (try cache.actualCallSummaryAt(calleeQueryToken(typed.tree(), call), typed.resolver.resolutionFrame())) orelse
        return error.TestExpectedCallee;
    return typed.resolver.frameForFunction(actual.callee.reference);
}

fn expectSuppliedListDeclaration(
    typed: *SuppliedListTest,
    cache: *FileCache,
    site: SuppliedListSite,
    frame: type_engine.TypeResolver.ResolutionFrame,
    name: []const u8,
    sdk: bool,
) !void {
    var buffer: [1]Ast.Node.Index = undefined;
    const call = typed.tree().fullCall(&buffer, site.node) orelse return error.TestExpectedCall;
    const actual = (try cache.actualCallSummaryAt(calleeQueryToken(typed.tree(), call), frame)) orelse
        return error.TestExpectedCallee;
    const tree = actual.callee.tree;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, actual.callee.declaration) orelse return error.TestExpectedFunction;
    try std.testing.expectEqualStrings(name, tree.tokenSlice(proto.name_token orelse return error.TestExpectedFunction));
    try std.testing.expect(actual.callee.caller_frame.?.resolver == &typed.resolver);
    const library = typed.resolver.ctx.store.toolchainRoot() orelse return error.TestExpectedToolchain;
    const path = try std.fs.path.join(std.testing.allocator, &.{ library, "std", "array_list.zig" });
    defer std.testing.allocator.free(path);
    const handle = try typed.context.sourceHandle(path, cache.module_id);
    try std.testing.expectEqual(sdk, tree == &handle.document.tree);
    try std.testing.expectEqual(sdk, try typed.resolver.declaredInToolchainFile(actual.callee.handle, "/std/array_list.zig"));
    if (!sdk) try std.testing.expect(tree == typed.tree());
    if (sdk) try std.testing.expect((try toolchainArrayListTree(cache, frame)).? == &handle.document.tree);
}

fn expectSuppliedListProjection(
    cache: *FileCache,
    site: SuppliedListSite,
    frame: type_engine.TypeResolver.ResolutionFrame,
) !void {
    var buffer: [1]Ast.Node.Index = undefined;
    const call = cache.tree.fullCall(&buffer, site.node) orelse return error.TestExpectedCall;
    const actual = (try cache.actualCallSummaryAt(calleeQueryToken(cache.tree, call), frame)) orelse
        return error.TestExpectedCallee;
    try std.testing.expect(try listConstructorProjection(cache, actual, &.{"items"}, null));
    try std.testing.expect(!try listConstructorProjection(cache, actual, &.{"allocator"}, null));
    try std.testing.expect(!try listConstructorProjection(cache, actual, &.{ "items", "ptr" }, null));
}

test "supplied frames authenticate actual SDK managed list constructors without an ambient resolver" {
    const gpa = std.testing.allocator;
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    var cache = typed.cache(gpa);
    defer cache.deinit();
    const frame = typed.resolver.resolutionFrame();
    inline for (.{
        .{ "direct_init", "init" },
        .{ "direct_capacity", "initCapacity" },
        .{ "alias_init", "init" },
    }) |case| {
        const site = try suppliedListSite(typed.tree(), "claims", case[0]);
        try expectSuppliedListDeclaration(typed, &cache, site, frame, case[1], true);
        const walk: FreshWalk = .{ .claim = site.claim, .depth = 0, .frame = frame };
        try std.testing.expect(try standardListConstructor(&cache, .{ .first = site.claim.first, .last = site.claim.last }, walk));
        try expectSuppliedListProjection(&cache, site, frame);
        try std.testing.expect(cache.zls == null);
    }
}

test "supplied SDK list frames reject borrowed same-name constructors and unresolved calls" {
    const gpa = std.testing.allocator;
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    var cache = typed.cache(gpa);
    defer cache.deinit();
    const frame = typed.resolver.resolutionFrame();
    inline for (.{ .{ "foreign_init", "init" }, .{ "foreign_capacity", "initCapacity" } }) |case| {
        const site = try suppliedListSite(typed.tree(), "claims", case[0]);
        try expectSuppliedListDeclaration(typed, &cache, site, frame, case[1], false);
        const walk: FreshWalk = .{ .claim = site.claim, .depth = 0, .frame = frame };
        try std.testing.expect(!try standardListConstructor(&cache, .{ .first = site.claim.first, .last = site.claim.last }, walk));
    }
    const unresolved = try suppliedListSite(typed.tree(), "claims", "unresolved");
    var buffer: [1]Ast.Node.Index = undefined;
    const call = typed.tree().fullCall(&buffer, unresolved.node).?;
    try std.testing.expect((try cache.actualCallSummaryAt(calleeQueryToken(typed.tree(), call), frame)) == null);
    try std.testing.expect(!try freshStorageAt(&cache, .{ .claim = unresolved.claim, .depth = 0, .frame = frame }));
}

test "supplied generic list frames bind parameter and alias names to each actual constructor" {
    const gpa = std.testing.allocator;
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    var cache = typed.cache(gpa);
    defer cache.deinit();
    const sdk_frame = try suppliedListFrame(typed, &cache, "sdk_invocation");
    const foreign_frame = try suppliedListFrame(typed, &cache, "foreign_invocation");
    try std.testing.expect(sdk_frame.actual_type != null);
    try std.testing.expect(foreign_frame.actual_type != null);
    inline for (.{
        .{ "generic_init", "init" },
        .{ "generic_capacity", "initCapacity" },
        .{ "generic_alias", "init" },
    }) |case| {
        const site = try suppliedListSite(typed.tree(), "genericClaims", case[0]);
        try expectSuppliedListDeclaration(typed, &cache, site, sdk_frame, case[1], true);
        try expectSuppliedListDeclaration(typed, &cache, site, foreign_frame, case[1], false);
        const range: TokenRange = .{ .first = site.claim.first, .last = site.claim.last };
        try std.testing.expect(try standardListConstructor(&cache, range, .{ .claim = site.claim, .depth = 0, .frame = sdk_frame }));
        try expectSuppliedListProjection(&cache, site, sdk_frame);
        try std.testing.expect(!try standardListConstructor(&cache, range, .{ .claim = site.claim, .depth = 0, .frame = foreign_frame }));
    }
    try std.testing.expect(cache.zls == null);
}

test "supplied list frames take precedence over an alien ambient SDK resolver and its toolchain root" {
    const gpa = std.testing.allocator;
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    const alien = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer alien.deinit(gpa);
    var cache = typed.cache(gpa);
    defer cache.deinit();
    cache.zls = &alien.resolver;
    const site = try suppliedListSite(typed.tree(), "claims", "direct_capacity");
    const frame = typed.resolver.resolutionFrame();
    try expectSuppliedListDeclaration(typed, &cache, site, frame, "initCapacity", true);
    const range: TokenRange = .{ .first = site.claim.first, .last = site.claim.last };
    const walk: FreshWalk = .{ .claim = site.claim, .depth = 0, .frame = frame };
    try std.testing.expect(try standardListConstructor(&cache, range, walk));
    const library = typed.context.store.config.zig_lib_dir;
    typed.context.store.config.zig_lib_dir = null;
    defer typed.context.store.config.zig_lib_dir = library;
    try std.testing.expect(typed.context.store.toolchainRoot() == null);
    try std.testing.expect(alien.context.store.toolchainRoot() != null);
    // A prior positive proof and a valid ambient SDK must not supply this root.
    try std.testing.expect((try toolchainArrayListTree(&cache, frame)) == null);
    try std.testing.expect(!try standardListConstructor(&cache, range, walk));
}

test "supplied SDK list constructor items have no canonical borrowed expression loans" {
    const gpa = std.testing.allocator;
    const typed = try SuppliedListTest.init(gpa,
        \\const std = @import("std");
        \\const Alias = std.array_list.Managed(u8);
        \\fn claims(gpa: std.mem.Allocator) !void {
        \\    const direct_init = std.array_list.Managed(u8).init(gpa);
        \\    const direct_capacity = try std.array_list.Managed(u8).initCapacity(gpa, 4);
        \\    const alias_init = Alias.init(gpa);
        \\    _ = direct_init; _ = direct_capacity; _ = alias_init;
        \\}
    );
    defer typed.deinit(gpa);
    var cache = typed.cache(gpa);
    defer cache.deinit();
    const returned = @import("return_storage.zig");
    inline for (.{ "direct_init", "direct_capacity", "alias_init" }) |name| {
        const site = try suppliedListSite(typed.tree(), "claims", name);
        var arena = std.heap.ArenaAllocator.init(gpa);
        defer arena.deinit();
        var query = returned.ExpressionLoanQuery.init(.{
            .cache = &cache,
            .body = site.body,
            .scratch = &arena,
            .context = .{ .frame = typed.resolver.resolutionFrame() },
        });
        const answer = try query.expressionLoansAt(.{
            .selection = .{ .node = site.node, .path = "items" },
            .horizon = typed.tree().firstToken(site.node),
        });
        try std.testing.expect(answer.complete);
        try std.testing.expectEqual(@as(usize, 0), answer.loans.len);
    }
}

test "supplied SDK list allocator projection retains its local fixed-buffer allocator cell" {
    const gpa = std.testing.allocator;
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    var cache = typed.cache(gpa);
    defer cache.deinit();
    const site = try suppliedListSite(typed.tree(), "unsafeClaims", "unsafe_init");
    const allocator_cell = try suppliedListSite(typed.tree(), "unsafeClaims", "fba");
    const frame = typed.resolver.resolutionFrame();
    try expectSuppliedListDeclaration(typed, &cache, site, frame, "init", true);
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const returned = @import("return_storage.zig");
    var query = returned.ExpressionLoanQuery.init(.{
        .cache = &cache,
        .body = site.body,
        .scratch = &arena,
        .context = .{ .frame = frame },
    });
    const answer = try query.expressionLoansAt(.{
        .selection = .{ .node = site.node, .path = "allocator" },
        .horizon = typed.tree().firstToken(site.node),
    });
    var found_allocator_cell = false;
    for (answer.loans) |loan| {
        if (loan.binding_token != allocator_cell.binding_token) continue;
        try std.testing.expectEqual(returned.ExpressionLoan.Origin.frame_cell, loan.origin);
        try std.testing.expectEqual(returned.ExpressionLoan.Derivation.propagated, loan.derivation);
        found_allocator_cell = true;
    }
    try std.testing.expect(found_allocator_cell);
    const walk: FreshWalk = .{ .claim = site.claim, .depth = 0, .frame = frame };
    try std.testing.expect(!try standardListConstructor(&cache, .{ .first = site.claim.first, .last = site.claim.last }, walk));
    try std.testing.expect(!try freshStorageAt(&cache, walk));
    try std.testing.expect(cache.zls == null);
}

test "supplied SDK list capacity items retain the local fixed-buffer backing" {
    const gpa = std.testing.allocator;
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    var cache = typed.cache(gpa);
    defer cache.deinit();
    const site = try suppliedListSite(typed.tree(), "unsafeClaims", "unsafe_capacity");
    const backing = try suppliedListSite(typed.tree(), "unsafeClaims", "bytes");
    const frame = typed.resolver.resolutionFrame();
    try expectSuppliedListDeclaration(typed, &cache, site, frame, "initCapacity", true);
    const walk: FreshWalk = .{ .claim = site.claim, .depth = 0, .frame = frame };
    try std.testing.expect(!try standardListConstructor(&cache, .{ .first = site.claim.first, .last = site.claim.last }, walk));
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const returned = @import("return_storage.zig");
    var query = returned.ExpressionLoanQuery.init(.{
        .cache = &cache,
        .body = site.body,
        .scratch = &arena,
        .context = .{ .frame = frame },
    });
    const answer = try query.expressionLoansAt(.{
        .selection = .{ .node = site.node, .path = "items" },
        .horizon = typed.tree().firstToken(site.node),
    });
    var found_backing = false;
    for (answer.loans) |loan| {
        if (loan.binding_token != backing.binding_token) continue;
        try std.testing.expectEqual(returned.ExpressionLoan.Origin.frame_cell, loan.origin);
        try std.testing.expectEqual(returned.ExpressionLoan.Derivation.propagated, loan.derivation);
        found_backing = true;
    }
    try std.testing.expect(found_backing);
    try std.testing.expect(cache.zls == null);
}

test "supplied SDK list frames propagate document-root load and broken-source failures" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.createDirPath(io, "std");
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    const site = try suppliedListSite(typed.tree(), "claims", "direct_capacity");
    const frame = typed.resolver.resolutionFrame();
    {
        var warm = typed.cache(gpa);
        defer warm.deinit();
        try expectSuppliedListDeclaration(typed, &warm, site, frame, "initCapacity", true);
    }
    const library = typed.context.store.config.zig_lib_dir;
    typed.context.store.config.zig_lib_dir = .{ .path = directory, .handle = .cwd() };
    defer typed.context.store.config.zig_lib_dir = library;
    const walk: FreshWalk = .{ .claim = site.claim, .depth = 0, .frame = frame };
    {
        var cache = typed.cache(gpa);
        defer cache.deinit();
        try std.testing.expectError(error.FileNotFound, freshStorageAt(&cache, walk));
    }
    try tmp.dir.writeFile(io, .{ .sub_path = "std/array_list.zig", .data = "pub fn broken(" });
    {
        var cache = typed.cache(gpa);
        defer cache.deinit();
        try std.testing.expectError(error.ImportInvalidSyntax, freshStorageAt(&cache, walk));
    }
}

test "configured missing SDK roots propagate load failures and allow same-cache semantic retry" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const directory = try tmp.dir.realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(directory);
    const missing_root = try std.fs.path.join(gpa, &.{ directory, "missing-sdk-root" });
    defer gpa.free(missing_root);
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    const site = try suppliedListSite(typed.tree(), "claims", "direct_capacity");
    const supplied = typed.resolver.resolutionFrame();
    const sdk_tree = sdk: {
        var warm = typed.cache(gpa);
        defer warm.deinit();
        try expectSuppliedListDeclaration(typed, &warm, site, supplied, "initCapacity", true);
        break :sdk (try toolchainArrayListTree(&warm, supplied)) orelse return error.TestExpectedToolchain;
    };
    const library = typed.context.store.config.zig_lib_dir;
    defer typed.context.store.config.zig_lib_dir = library;
    inline for (.{ true, false }) |provided| {
        var cache = typed.cache(gpa);
        defer cache.deinit();
        cache.zls = if (provided) null else &typed.resolver;
        const frame: ?type_engine.TypeResolver.ResolutionFrame = if (provided) supplied else null;
        typed.context.store.config.zig_lib_dir = .{ .path = missing_root, .handle = .cwd() };
        try std.testing.expectError(error.FileNotFound, toolchainArrayListTree(&cache, frame));
        const walk: FreshWalk = .{ .claim = site.claim, .depth = 0, .frame = frame };
        try std.testing.expectError(error.FileNotFound, freshStorageAt(&cache, walk));
        typed.context.store.config.zig_lib_dir = library;
        try std.testing.expect((try toolchainArrayListTree(&cache, frame)).? == sdk_tree);
        try std.testing.expect(try standardListConstructor(&cache, .{ .first = site.claim.first, .last = site.claim.last }, walk));
        if (provided) try std.testing.expect(cache.zls == null);
    }
}

fn coldSuppliedSdkRoot(
    gpa: std.mem.Allocator,
    directory: std.Io.Dir,
    library: []const u8,
    name: []const u8,
) ![]u8 {
    try directory.symLink(std.testing.io, library, name, .{ .is_directory = true });
    const absolute = try directory.realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(absolute);
    // Join the alias without resolving it; the query must perform that cold
    // canonicalization itself, rather than finding a previously admitted key.
    return std.fs.path.join(gpa, &.{ absolute, name });
}

test "configured SDK root canonicalization propagates allocation failure and permits same-cache retry" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    const supplied = typed.resolver.resolutionFrame();
    var warm = typed.cache(gpa);
    defer warm.deinit();
    const sdk_tree = (try toolchainArrayListTree(&warm, supplied)) orelse return error.TestExpectedToolchain;
    const library = typed.context.store.config.zig_lib_dir;
    defer typed.context.store.config.zig_lib_dir = library;
    const canonical_root = typed.context.store.toolchainRoot() orelse return error.TestExpectedToolchain;
    inline for (.{ true, false }) |provided| {
        const alias = try coldSuppliedSdkRoot(gpa, tmp.dir, canonical_root, if (provided) "provided-sdk" else "ambient-sdk");
        defer gpa.free(alias);
        var cache = typed.cache(gpa);
        defer cache.deinit();
        cache.zls = if (provided) null else &typed.resolver;
        const frame: ?type_engine.TypeResolver.ResolutionFrame = if (provided) supplied else null;
        typed.context.store.config.zig_lib_dir = .{ .path = alias, .handle = .cwd() };
        defer typed.context.store.config.zig_lib_dir = library;
        {
            // Only TypeContext.canonicalPath's cold root allocation can fail.
            // Cache path joins and the already loaded SDK documents keep gpa.
            var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = 0 });
            const allocator = typed.context.gpa;
            typed.context.gpa = failing.allocator();
            defer typed.context.gpa = allocator;
            try std.testing.expectError(error.OutOfMemory, toolchainArrayListTree(&cache, frame));
        }
        try std.testing.expect((try toolchainArrayListTree(&cache, frame)).? == sdk_tree);
        typed.context.store.config.zig_lib_dir = library;
        if (provided) try std.testing.expect(cache.zls == null);
    }
}

fn canceledSuppliedSdkRoot(
    cache: *FileCache,
    frame: ?type_engine.TypeResolver.ResolutionFrame,
    sdk_tree: *const Ast,
    gate: *std.Io.Mutex,
    io: std.Io,
) !void {
    // The caller holds this mutex until the future has retired. Consume the
    // real task cancellation here, then re-arm it for the filesystem query.
    try std.testing.expectError(error.Canceled, gate.lock(io));
    io.recancel();
    try std.testing.expectError(error.Canceled, toolchainArrayListTree(cache, frame));
    // Cancellation is one-shot. The identical configured root and cache must
    // resolve the actual SDK document once the request has been acknowledged.
    try std.testing.expect((try toolchainArrayListTree(cache, frame)).? == sdk_tree);
}

test "configured SDK root canonicalization propagates cancellation and permits same-cache retry" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    const supplied = typed.resolver.resolutionFrame();
    var warm = typed.cache(gpa);
    defer warm.deinit();
    const sdk_tree = (try toolchainArrayListTree(&warm, supplied)) orelse return error.TestExpectedToolchain;
    const library = typed.context.store.config.zig_lib_dir;
    defer typed.context.store.config.zig_lib_dir = library;
    const canonical_root = typed.context.store.toolchainRoot() orelse return error.TestExpectedToolchain;
    inline for (.{ true, false }) |provided| {
        const alias = try coldSuppliedSdkRoot(gpa, tmp.dir, canonical_root, if (provided) "provided-sdk" else "ambient-sdk");
        defer gpa.free(alias);
        var cache = typed.cache(gpa);
        defer cache.deinit();
        cache.zls = if (provided) null else &typed.resolver;
        const frame: ?type_engine.TypeResolver.ResolutionFrame = if (provided) supplied else null;
        typed.context.store.config.zig_lib_dir = .{ .path = alias, .handle = .cwd() };
        defer typed.context.store.config.zig_lib_dir = library;
        var gate: std.Io.Mutex = .init;
        gate.lockUncancelable(io);
        defer gate.unlock(io);
        var future = try io.concurrent(canceledSuppliedSdkRoot, .{ &cache, frame, sdk_tree, &gate, io });
        try future.cancel(io);
        typed.context.store.config.zig_lib_dir = library;
        if (provided) try std.testing.expect(cache.zls == null);
    }
}

test "supplied list frames propagate excluded constructor sources without publishing a negative proof" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{
        .sub_path = "remote.zig",
        .data = "pub fn init(bytes: []u8) []u8 { return bytes; }",
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    const remote = try std.fs.path.join(gpa, &.{ directory, "remote.zig" });
    defer gpa.free(remote);
    const typed = try SuppliedListTest.initAt(gpa, path,
        \\const remote = @import("remote.zig");
        \\fn claims(bytes: []u8) void {
        \\    const imported = remote.init(bytes);
        \\    _ = imported;
        \\}
    );
    defer typed.deinit(gpa);
    typed.context.store.source_policy = .{ .roots = &.{directory}, .excludes = &.{remote} };
    var cache = typed.cache(gpa);
    defer cache.deinit();
    const site = try suppliedListSite(typed.tree(), "claims", "imported");
    const walk: FreshWalk = .{ .claim = site.claim, .depth = 0, .frame = typed.resolver.resolutionFrame() };
    try std.testing.expectError(error.SourceExcluded, freshStorageAt(&cache, walk));
    typed.context.store.source_policy = .{ .roots = &.{directory} };
    try std.testing.expect(!try freshStorageAt(&cache, walk));
    try std.testing.expect(cache.zls == null);
}

fn allocationFailureSuppliedListFrame(gpa: std.mem.Allocator, typed: *SuppliedListTest) !void {
    // The original resolver and toolchain documents stay outside the failing
    // allocator. Each query must allocate its own SDK root path and cache data.
    var cache = typed.cache(gpa);
    defer cache.deinit();
    try std.testing.expect((try toolchainArrayListTree(&cache, typed.resolver.resolutionFrame())) != null);
    inline for (.{ "direct_init", "direct_capacity" }) |name| {
        const site = try suppliedListSite(typed.tree(), "claims", name);
        const walk: FreshWalk = .{ .claim = site.claim, .depth = 0, .frame = typed.resolver.resolutionFrame() };
        try std.testing.expect(try standardListConstructor(&cache, .{ .first = site.claim.first, .last = site.claim.last }, walk));
    }
    const unsafe_site = try suppliedListSite(typed.tree(), "unsafeClaims", "unsafe_init");
    try std.testing.expect(!try freshStorageAt(&cache, .{
        .claim = unsafe_site.claim,
        .depth = 0,
        .frame = typed.resolver.resolutionFrame(),
    }));
    try std.testing.expect(cache.zls == null);
}

test "supplied SDK list frame allocation failures propagate from query and document-root paths" {
    const gpa = std.testing.allocator;
    const typed = try SuppliedListTest.init(gpa, SuppliedListTest.source);
    defer typed.deinit(gpa);
    {
        var warm = typed.cache(gpa);
        defer warm.deinit();
        inline for (.{ .{ "direct_init", "init" }, .{ "direct_capacity", "initCapacity" } }) |case| {
            const site = try suppliedListSite(typed.tree(), "claims", case[0]);
            try expectSuppliedListDeclaration(typed, &warm, site, typed.resolver.resolutionFrame(), case[1], true);
        }
    }
    try std.testing.checkAllAllocationFailures(gpa, allocationFailureSuppliedListFrame, .{typed});
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
    try charge(walk.remaining, tree, tree.nodeMainToken(owner_node));
    const resolved_container = if (walk.frame) |frame| frame.containerOfNode(owner_node) else resolver.containerOfNode(owner_node);
    const container = (try resolved_container) orelse return false;
    const in_hash_map = try resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/hash_map.zig");
    const in_array_hash_map = try resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/array_hash_map.zig");
    const in_array_list = try resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/array_list.zig");
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
    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(expression));
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
    const owner_cache = (try actualSourceCache(cache, frame.handle, resolver)) orelse return false;
    for (declared.ast.members) |member| {
        try charge(walk.remaining, owner_tree, owner_tree.nodeMainToken(member));
        const field = owner_tree.fullContainerField(member) orelse continue;
        if (field.ast.tuple_like) return false;
        const type_node = field.ast.type_expr.unwrap() orelse return false;
        const name = owner_tree.tokenSlice(field.ast.main_token);
        var supplied: ?Ast.Node.Index = null;
        for (literal.ast.fields) |value| {
            try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(value));
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
            try charge(walk.remaining, owner_tree, owner_tree.nodeMainToken(type_node));
            const undefined_type = (try frame.typeOfNode(type_node)) orelse return false;
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
        try charge(walk.remaining, owner_tree, owner_tree.nodeMainToken(type_node));
        const field_type = try frame.typeOfNode(type_node);
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
    resolver: *type_engine.TypeResolver,
) FreshError!?*FileCache {
    if (&handle.document.tree == cache.tree and handle.module == cache.module_id) return cache;
    // A failed source open terminates the proof; it is not evidence that the
    // document is absent or that the selected storage is not fresh.
    const document = try grow_analysis.sourceDocument(cache, handle, resolver.ctx);
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

const AddressFreeKey = struct {
    resolver: *type_engine.TypeResolver,
    ty: type_engine.TypeResolver.ActualType,
};

const AddressFreeKeyContext = struct {
    pub fn hash(_: AddressFreeKeyContext, key: AddressFreeKey) u64 {
        var hasher: std.hash.Wyhash = .init(0);
        std.hash.autoHash(&hasher, key.resolver);
        std.hash.autoHash(&hasher, key.ty.hash64());
        return hasher.final();
    }

    pub fn eql(_: AddressFreeKeyContext, left: AddressFreeKey, right: AddressFreeKey) bool {
        return left.resolver == right.resolver and left.ty.eql(right.ty);
    }
};

/// Completed root structural proofs. Types borrow the query's original resolver.
/// All entries were proved at depth zero; depth-stopped and work-stopped walks
/// publish nothing. Neither a caller's expression nor its work allowance is a key.
/// The canonical container already carries its declaring document, module and
/// bound arguments. Field types are resolved in frameForContainer of that type,
/// never in the caller's frame; interned primitive identity belongs to resolver.
pub const AddressFreeMemo = struct {
    answers: std.HashMapUnmanaged(AddressFreeKey, bool, AddressFreeKeyContext, 80) = .empty,

    pub fn deinit(self: *AddressFreeMemo, gpa: std.mem.Allocator) void {
        self.answers.deinit(gpa);
    }

    pub fn proves(
        self: *AddressFreeMemo,
        gpa: std.mem.Allocator,
        frame: type_engine.TypeResolver.ResolutionFrame,
        ty: type_engine.TypeResolver.ActualType,
        node: Ast.Node.Index,
        remaining: ?*u32,
    ) FreshError!bool {
        const tree = &frame.handle.document.tree;
        try charge(remaining, tree, tree.nodeMainToken(node));
        const actual = (try frame.resolver.normalizedType(ty)) orelse return false;
        const key: AddressFreeKey = .{
            .resolver = frame.resolver,
            .ty = actual,
        };
        if (self.answers.get(key)) |answer| return answer;
        var depth_stopped = false;
        const answer = try actualTypeAddressFreeResolved(frame, actual, 0, remaining, &depth_stopped, tree, tree.nodeMainToken(node));
        if (!depth_stopped) try self.answers.put(gpa, key, answer);
        return answer;
    }
};

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
    var depth_stopped = false;
    const location_tree = &frame.handle.document.tree;
    const location_token = if (ty.data == .container)
        ty.data.container.scope_handle.handle.document.tree.nodeMainToken(ty.data.container.scope_handle.toNode())
    else if (frame.actual_type) |actual|
        if (actual.data == .function) actual.data.function.fn_token else 0
    else if (frame.container_type) |container|
        if (container.data == .container) location_tree.nodeMainToken(container.data.container.scope_handle.toNode()) else 0
    else
        0;
    return actualTypeAddressFreeInner(frame, ty, depth, remaining, &depth_stopped,
        if (ty.data == .container) &ty.data.container.scope_handle.handle.document.tree else location_tree, location_token);
}

fn actualTypeAddressFreeInner(
    frame: type_engine.TypeResolver.ResolutionFrame,
    ty: type_engine.TypeResolver.ActualType,
    depth: u8,
    remaining: ?*u32,
    depth_stopped: *bool,
    location_tree: *const Ast,
    location_token: Ast.TokenIndex,
) FreshError!bool {
    if (depth > type_query.max_element_depth) {
        depth_stopped.* = true;
        return false;
    }
    try charge(remaining, location_tree, location_token);
    // Structural wrapper children are instance types; intern-pool children
    // may already be type values. Normalize through the same resolver rather
    // than changing flags or losing the wrapper's address-bearing shape.
    const actual = (try frame.resolver.normalizedType(ty)) orelse return false;
    return actualTypeAddressFreeResolved(frame, actual, depth, remaining, depth_stopped, location_tree, location_token);
}

fn actualTypeAddressFreeResolved(
    frame: type_engine.TypeResolver.ResolutionFrame,
    actual: type_engine.TypeResolver.ActualType,
    depth: u8,
    remaining: ?*u32,
    depth_stopped: *bool,
    location_tree: *const Ast,
    location_token: Ast.TokenIndex,
) FreshError!bool {
    switch (actual.data) {
        .ip_index => {
            // The pool reports a tag it cannot name as null.  That is the same
            // "this walk could not read it" answer every other unresolved
            // question here gets — never a guessed kind — so an unnamed
            // interned type is not proved address-free.
            const index = actual.ipIndex() orelse return false;
            const tag = frame.resolver.ctx.ip.zigTypeTag(index) orelse return false;
            return switch (tag) {
                .int, .float, .bool, .@"enum", .void, .comptime_int, .comptime_float, .null => true,
                .array, .vector, .optional => blk: {
                    const child = frame.resolver.childType(actual) orelse return false;
                    break :blk try actualTypeAddressFreeInner(frame, child, depth + 1, remaining, depth_stopped, location_tree, location_token);
                },
                else => false,
            };
        },
        .array => |array| return actualTypeAddressFreeInner(frame, array.elem_ty.*, depth + 1, remaining, depth_stopped, location_tree, location_token),
        .union_tag => return true,
        .optional => |payload| return actualTypeAddressFreeInner(frame, payload.*, depth + 1, remaining, depth_stopped, location_tree, location_token),
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
                // Methods and constants are not stored in a struct instance.
                // Their bodies cannot affect whether its fields carry addresses.
                const field = tree.fullContainerField(member) orelse continue;
                try charge(remaining, tree, field.ast.main_token);
                const type_node = field.ast.type_expr.unwrap() orelse return false;
                try charge(remaining, tree, tree.nodeMainToken(type_node));
                const field_type = (try nested.typeOfNode(type_node)) orelse return false;
                if (!try actualTypeAddressFreeInner(nested, field_type, depth + 1, remaining, depth_stopped, tree, tree.nodeMainToken(type_node))) return false;
            }
            return true;
        },
        else => return false,
    }
}

fn expectAddressFreeWithoutDeclarationWork(pointer_field: bool, repeated: bool) !void {
    const gpa = std.testing.allocator;
    var text: std.Io.Writer.Allocating = .init(gpa);
    defer text.deinit();
    try text.writer.writeAll("const Value = struct {\n");
    for (0..64) |index| try text.writer.print("const irrelevant{d} = {d};\n", .{ index, index });
    try text.writer.writeAll(if (pointer_field) "payload: *u32,\n};\n" else "payload: u32,\n};\n");
    const source = try gpa.dupeZ(u8, text.written());
    defer gpa.free(source);
    var context: type_engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-fresh-declaration-budget-test.zig" });
    defer gpa.free(path);
    var resolver: type_engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const initializer = tree.fullVarDecl(tree.rootDecls()[0]).?.ast.init_node.unwrap().?;
    const frame = resolver.resolutionFrame();
    const actual = (try frame.typeOfNode(initializer)).?;
    var remaining: u32 = 4;
    budget_mod.clear();
    defer budget_mod.clear();
    var memo: AddressFreeMemo = .{};
    defer memo.deinit(gpa);
    if (repeated) {
        remaining = 1;
        try std.testing.expectError(error.AnalysisBudgetExceeded, memo.proves(gpa, frame, actual, initializer, &remaining));
        try std.testing.expectEqual(@as(u32, 0), memo.answers.count());
        const stop = budget_mod.take().?;
        try std.testing.expect(stop.byte != 0 and stop.line != 0 and stop.column != 0);
        remaining = 4;
    }
    try std.testing.expectEqual(!pointer_field, if (repeated)
        try memo.proves(gpa, frame, actual, initializer, &remaining)
    else
        try actualTypeAddressFree(frame, actual, 0, &remaining));
    try std.testing.expectEqual(@as(u32, 0), remaining);
    if (repeated) {
        remaining = 1;
        try std.testing.expectEqual(!pointer_field, try memo.proves(gpa, frame, actual, initializer, &remaining));
        try std.testing.expectEqual(@as(u32, 0), remaining);
    }
}

test "fresh storage address-free proof skips unrelated declarations within unchanged work" {
    try expectAddressFreeWithoutDeclarationWork(false, false);
}

test "fresh storage address-free proof still rejects pointers after unrelated declarations" {
    try expectAddressFreeWithoutDeclarationWork(true, false);
}

test "fresh storage address-free memo reuses completed scalar proofs within lookup allowance" {
    try expectAddressFreeWithoutDeclarationWork(false, true);
}

test "fresh storage address-free memo reuses completed pointer rejection without granting storage" {
    try expectAddressFreeWithoutDeclarationWork(true, true);
}

test "fresh storage address-free memo separates actual generic fields and never files depth stops" {
    const source: [:0]const u8 =
        \\fn Box(comptime T: type) type { return struct { payload: T }; }
        \\const scalar = Box(u32);
        \\const pointer = Box(*u32);
        \\const deep = struct { payload: [1][1][1][1][1]u32 };
    ;
    const gpa = std.testing.allocator;
    var context: type_engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", gpa);
    defer gpa.free(cwd);
    const path = try std.fs.path.join(gpa, &.{ cwd, "zbc-fresh-generic-budget-test.zig" });
    defer gpa.free(path);
    var resolver: type_engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const frame = resolver.resolutionFrame();
    var memo: AddressFreeMemo = .{};
    defer memo.deinit(gpa);
    for (tree.rootDecls()[1..], 0..) |declaration, index| {
        const node = tree.fullVarDecl(declaration).?.ast.init_node.unwrap().?;
        const actual = (try frame.typeOfNode(node)).?;
        var remaining: u32 = 32;
        const count = memo.answers.count();
        try std.testing.expectEqual(index == 0, try memo.proves(gpa, frame, actual, node, &remaining));
        try std.testing.expectEqual(count + @as(u32, if (index == 2) 0 else 1), memo.answers.count());
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
            try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(access[0]));
            const resolved = if (walk.frame) |frame| frame.containerOfNode(access[0]) else resolver.containerOfNode(access[0]);
            const receiver = (try resolved) orelse return null;
            const actual_receiver: type_engine.TypeResolver.ActualType = .{ .data = .{ .container = receiver }, .is_type_val = true };
            if (!expected.eql(actual_receiver)) return null;
            break :blk cache.tree.tokenSlice(access[1]);
        },
        else => return null,
    };
    const Analysis = @TypeOf(resolver.analyser);
    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(expression));
    const declaration = (try Analysis.lookupSymbolContainer(expected, member, .other)) orelse return null;
    if (!declaration.isConst()) return null;
    const node = switch (declaration.decl) {
        .ast_node => |node| node,
        else => return null,
    };
    const source = (try actualSourceCache(cache, declaration.handle, resolver)) orelse return null;
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
    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(owner_node));
    const resolved = if (walk.frame) |frame| frame.containerOfNode(owner_node) else resolver.containerOfNode(owner_node);
    const container = (try resolved) orelse return false;
    if (!try sdkMapDocument(resolver, container.scope_handle.handle)) return false;
    const expected: type_engine.TypeResolver.ActualType = .{ .data = .{ .container = container }, .is_type_val = true };
    const frame = resolver.frameForContainer(container);
    const Analysis = @TypeOf(resolver.analyser);
    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(expression));
    const count = (try Analysis.lookupSymbolContainer(expected, "count", .other)) orelse
        return false;
    const count_node = switch (count.decl) {
        .ast_node => |node| node,
        else => return false,
    };
    const source = (try actualSourceCache(cache, count.handle, resolver)) orelse return false;
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
    return (try resolver.declaredInToolchainFile(handle, "/std/hash_map.zig")) or
        (try resolver.declaredInToolchainFile(handle, "/std/array_hash_map.zig"));
}

fn sdkCountPath(cache: *FileCache, declaration: Ast.Node.Index, walk: FreshWalk, path: *SdkFieldPath, depth: u8) FreshError!bool {
    if (depth >= max_fresh_depth) return false;
    const tree = cache.tree;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
    var parameters = proto.iterate(tree);
    const receiver = (parameters.next() orelse return false).name_token orelse return false;
    if (parameters.next() != null) return false;
    const value = (try uniqueReturnedValue(cache, declaration, walk)) orelse return false;
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
    try charge(remaining, tree, tree.nodeMainToken(node));
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

fn uniqueReturnedValue(cache: *FileCache, declaration: Ast.Node.Index, walk: FreshWalk) FreshError!?Ast.Node.Index {
    const tree = cache.tree;
    const body = tokens.bodyOf(tree, declaration) orelse return null;
    var buffer: [2]Ast.Node.Index = undefined;
    const statements = tree.blockStatements(&buffer, body) orelse return null;
    const frame = walk.frame orelse (cache.zls orelse return null).resolutionFrame();
    for (statements, 0..) |statement, index| {
        try charge(walk.remaining, tree, tree.nodeMainToken(statement));
        if (tree.nodeTag(statement) == .@"return") {
            if (index + 1 != statements.len) return null;
            return tree.nodeData(statement).opt_node.unwrap();
        }
        // A bound SDK initializer can guard an invalid context layout before
        // returning its header. Skip only a branch positively not taken; no
        // assignment, runtime guard, or effects are silently discarded.
        const branch = tree.fullIf(statement) orelse return null;
        if (branch.payload_token != null or branch.ast.else_expr != .none) return null;
        try charge(walk.remaining, tree, tree.nodeMainToken(branch.ast.cond_expr));
        const condition = (try frame.boolValueOfNode(branch.ast.cond_expr)) orelse return null;
        if (condition) return null;
    }
    return null;
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
        var next = walk;
        next.frame = original.frameForFunction(canonical.callee.reference);
        const value = (try uniqueReturnedValue(declaring, canonical.callee.declaration, next)) orelse return false;
        next.claim = .{ .first = declaring.tree.firstToken(value), .last = declaring.tree.lastToken(value) };
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
        try charge(walk.remaining, owner_tree, owner_tree.nodeMainToken(member));
        const field = owner_tree.fullContainerField(member) orelse continue;
        if (!std.mem.eql(u8, owner_tree.tokenSlice(field.ast.main_token), path[0])) continue;
        var value: ?Ast.Node.Index = null;
        for (literal.ast.fields) |candidate| {
            try charge(walk.remaining, selected.cache.tree, selected.cache.tree.nodeMainToken(candidate));
            const token = selected.cache.tree.firstToken(candidate);
            if (token >= 2 and std.mem.eql(u8, selected.cache.tree.tokenSlice(token - 2), path[0])) value = candidate;
        }
        const value_cache = if (value != null) selected.cache else (try actualSourceCache(cache, frame.handle, resolver)) orelse return false;
        const actual_value = value orelse field.ast.value_expr.unwrap() orelse return false;
        if (path.len == 1) return numericValueIsZero(value_cache, actual_value, walk);
        const type_node = field.ast.type_expr.unwrap() orelse return false;
        try charge(walk.remaining, owner_tree, owner_tree.nodeMainToken(type_node));
        const field_type = (try frame.typeOfNode(type_node)) orelse return false;
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
    if (!(try resolver.declaredInToolchainFile(expected.data.container.scope_handle.handle, "/std/multi_array_list.zig"))) return false;
    return (try sdkPathIsZero(cache, expression, expected, walk, &.{"len"}, 0)) and
        (try sdkPathIsZero(cache, expression, expected, walk, &.{"capacity"}, 0));
}

/// The container a constructor's own declaration says it returns.
///
/// Read the declared result in the canonical callee's bound frame. A fallible
/// constructor returns an error union; only its payload names the header
/// whose fields the allocation intrinsic must prove independent.
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
        try charge(walk.remaining, canonical.callee.tree, canonical.callee.tree.nodeMainToken(returned));
        returned = canonical.callee.tree.nodeData(returned).node_and_node[1];
    }
    const resolver = if (canonical.callee.caller_frame) |caller|
        caller.resolver
    else
        cache.zls orelse return null;
    try charge(walk.remaining, canonical.callee.tree, canonical.callee.tree.nodeMainToken(returned));
    // `returned` is a node of the CALLEE's own document, so it is read in the
    // callee's own frame — the frame `listConstructorProjection` reads the
    // same declaration through.
    return try resolver.frameForFunction(canonical.callee.reference).containerOfNode(returned);
}

/// The SDK constructor intrinsic proves its newly allocated slice, not an
/// allocator/interface field captured by a managed header. Every other
/// declared field must independently be address-free.
fn standardListFieldsIndependent(cache: *FileCache, call: TokenRange, walk: FreshWalk) FreshError!bool {
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    try charge(walk.remaining, cache.tree, call.first);
    const container = (try constructorResultContainer(cache, call, walk)) orelse return false;
    const frame = resolver.frameForContainer(container);
    const tree = &frame.handle.document.tree;
    var buffer: [2]Ast.Node.Index = undefined;
    const declared = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return false;
    var slices: u32 = 0;
    for (declared.ast.members) |member| {
        try charge(walk.remaining, tree, tree.nodeMainToken(member));
        const field = tree.fullContainerField(member) orelse continue;
        const type_node = field.ast.type_expr.unwrap() orelse return false;
        const ty = (try frame.typeOfNode(type_node)) orelse return false;
        if (try actualTypeAddressFree(frame, ty, 0, walk.remaining)) continue;
        // An unnamed pointer size is not the one single-slice field this
        // constructor is allowed to leave shared, so it proves nothing here.
        if ((frame.resolver.pointerSize(ty) orelse return false) != .slice) return false;
        slices += 1;
    }
    return slices == 1;
}

fn numericValueIsZero(cache: *FileCache, value: Ast.Node.Index, walk: FreshWalk) FreshError!bool {
    const numeric_eval = @import("../flow/numeric_eval.zig");
    // With no cache, facts, or alias table the evaluator cannot leave this
    // expression. Its source tokens bound all AST work, prepaid against the
    // caller's meter. A bound that stops the evaluator, structural depth
    // included, is a failure and not the answer "not zero".
    const work = cache.tree.lastToken(value) - cache.tree.firstToken(value) + 1;
    if (walk.remaining) |remaining| {
        if (remaining.* < work) {
            remaining.* = 0;
            return workFailure(cache.tree, value);
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
    if (stopped) |stop| return budget_mod.fail(.{
        .limit = stop.limit,
        .limit_value = stop.cap,
        .reached = stop.cap,
        .document = budget_mod.documentForTree(cache.tree),
    });
    return value_range == .integer and value_range.integer.min == 0 and value_range.integer.max == 0;
}

/// Whether a canonical SDK `Allocator.create` call may return heap ownership.
///
/// The allocated object's fields do not affect this ownership fact. Unknown
/// allocator origins remain possible heap owners; only a proven SDK arena or
/// fixed-buffer origin rules heap ownership out.
pub fn sdkCreateMayOwnHeap(
    cache: *FileCache,
    canonical: FileCache.ActualCallSummary,
    walk: FreshWalk,
) FreshError!bool {
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    const callee = canonical.callee;
    if (!(try resolver.declaredInToolchainFile(callee.handle, "/std/mem/Allocator.zig"))) return false;
    if (callee.fn_token + 1 >= callee.tree.tokens.len or
        !std.mem.eql(u8, callee.tree.tokenSlice(callee.fn_token + 1), "create")) return false;
    var receiver_buffer: [2]Ast.Node.Index = undefined;
    const allocator = (try canonical.callArgumentFor(cache, &receiver_buffer, 0)) orelse return false;
    const allocator_type = if (walk.frame) |frame|
        frame.isStdAllocator(allocator)
    else
        resolver.isStdAllocator(allocator);
    if (!((try allocator_type) orelse false)) return false;
    return !(try allocatorOriginIsKnownNonHeap(cache, allocator, walk, 0));
}

/// Follow source-proved aliases to an SDK arena or fixed-buffer allocator.
/// Unknown and mixed origins remain potentially heap-owned.
fn allocatorOriginIsKnownNonHeap(
    cache: *FileCache,
    expression: Ast.Node.Index,
    walk: FreshWalk,
    depth: u8,
) FreshError!bool {
    if (depth >= max_fresh_depth) return false;
    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(expression));
    if (walk.frame == null and cache.zls == null) return false;
    const tree = cache.tree;
    switch (tree.nodeTag(expression)) {
        .identifier => {
            const token = tree.nodeMainToken(expression);
            const declaration = tokens.enclosingFnDecl(tree, token) orelse return false;
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
            const body = tokens.bodyOf(tree, declaration) orelse return false;
            try charge(walk.remaining, tree, token);
            const bindings = (try cache.localBindings(proto, body)).*;
            const binding = bindings.findAt(tree.tokenSlice(token), token) orelse return false;
            if (binding.origin == .param or !binding.is_const or
                !try plainLocalStillIndependent(cache, &bindings, binding, token, walk)) return false;
            // A const alias moves strictly backward in this function. Only
            // entering another accessor spends a provenance-call level.
            if (binding.rhs_first >= token) return false;
            const initializer = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
            return try allocatorOriginIsKnownNonHeap(cache, initializer, walk, depth);
        },
        .call, .call_comma, .call_one, .call_one_comma => {
            const call_range: TokenRange = .{
                .first = tree.firstToken(expression),
                .last = tree.lastToken(expression),
            };
            const canonical = (try canonicalCall(cache, call_range, walk)) orelse return false;
            const callee = canonical.callee;
            const name = if (callee.fn_token + 1 < callee.tree.tokens.len)
                callee.tree.tokenSlice(callee.fn_token + 1)
            else
                "";
            if (std.mem.eql(u8, name, "allocator") and
                try sdkHeapAllocatorMethodIsTemporary(cache, canonical, walk)) return true;
            return try allocatorCallReturnsKnownNonHeap(cache, canonical, walk, depth);
        },
        else => return false,
    }
}

fn allocatorCallReturnsKnownNonHeap(
    cache: *FileCache,
    canonical: FileCache.ActualCallSummary,
    walk: FreshWalk,
    depth: u8,
) FreshError!bool {
    if (depth >= max_fresh_depth) return false;
    const callee = canonical.callee;
    const declaring = (try canonical.declaringCache(cache)) orelse return false;
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    var next = walk;
    next.frame = resolver.frameForFunction(callee.reference);
    var returns: u32 = 0;
    for (declaring.tree.nodes.items(.tag), 0..) |tag, raw| {
        try charge(walk.remaining, declaring.tree, declaring.tree.nodeMainToken(@enumFromInt(raw)));
        if (tag != .@"return") continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const first = declaring.tree.firstToken(node);
        if ((tokens.enclosingFnDecl(declaring.tree, first) orelse callee.declaration) != callee.declaration) continue;
        const value = declaring.tree.nodeData(node).opt_node.unwrap() orelse return false;
        if (!try allocatorReturnValueKnownNonHeap(
            declaring,
            value,
            cache,
            canonical,
            next,
            depth + 1,
        )) return false;
        returns += 1;
    }
    return returns != 0;
}

fn allocatorReturnValueKnownNonHeap(
    declaring: *FileCache,
    value: Ast.Node.Index,
    caller: *FileCache,
    canonical: FileCache.ActualCallSummary,
    walk: FreshWalk,
    depth: u8,
) FreshError!bool {
    if (depth >= max_fresh_depth) return false;
    const tree = declaring.tree;
    if (tree.nodeTag(value) == .identifier) {
        const token = tree.nodeMainToken(value);
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const declaration = canonical.callee.declaration;
        const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
        const body = tokens.bodyOf(tree, declaration) orelse return false;
        try charge(walk.remaining, tree, token);
        const bindings = (try declaring.localBindings(proto, body)).*;
        const binding = bindings.findAt(tree.tokenSlice(token), token) orelse return false;
        if (binding.origin == .param) {
            var parameter_index: u32 = 0;
            var parameters = proto.iterate(tree);
            while (parameters.next()) |parameter| : (parameter_index += 1) {
                try charge(walk.remaining, tree, parameter.name_token orelse tree.nodeMainToken(declaration));
                if (parameter.name_token == null or parameter.name_token.? != binding.name_token) continue;
                var argument_buffer: [2]Ast.Node.Index = undefined;
                const argument = (try canonical.callArgumentFor(
                    caller,
                    &argument_buffer,
                    parameter_index,
                )) orelse return false;
                const caller_frame = if (canonical.callee.caller_frame) |frame|
                    frame
                else
                    (caller.zls orelse return false).resolutionFrame();
                const allocator_type = caller_frame.isStdAllocator(argument);
                if (!((try allocator_type) orelse false)) return false;
                var argument_walk = walk;
                argument_walk.frame = caller_frame;
                return try allocatorOriginIsKnownNonHeap(caller, argument, argument_walk, depth + 1);
            }
            return false;
        }
        if (!binding.is_const or
            !try plainLocalStillIndependent(declaring, &bindings, binding, token, walk)) return false;
        if (binding.rhs_first >= token) return false;
        const initializer = declaring.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
        return try allocatorReturnValueKnownNonHeap(
            declaring,
            initializer,
            caller,
            canonical,
            walk,
            depth,
        );
    }
    return try allocatorOriginIsKnownNonHeap(declaring, value, walk, depth);
}

/// Prove a temporary allocator from its declaring SDK source and receiver type.
fn sdkHeapAllocatorMethodIsTemporary(
    cache: *FileCache,
    canonical: FileCache.ActualCallSummary,
    walk: FreshWalk,
) FreshError!bool {
    const callee = canonical.callee;
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    const arena = try resolver.declaredInToolchainFile(
        callee.handle,
        "/std/heap/ArenaAllocator.zig",
    );
    const fixed = try resolver.declaredInToolchainFile(
        callee.handle,
        "/std/heap/FixedBufferAllocator.zig",
    );
    if (!arena and !fixed) return false;
    var receiver_buffer: [2]Ast.Node.Index = undefined;
    const receiver = (try canonical.callArgumentFor(cache, &receiver_buffer, 0)) orelse return false;
    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(receiver));
    const owner = if (walk.frame) |frame|
        frame.containerOfNode(receiver)
    else
        resolver.containerOfNode(receiver);
    const container = (try owner) orelse return false;
    return (arena and (try resolver.declaredInToolchainFile(
        container.scope_handle.handle,
        "/std/heap/ArenaAllocator.zig",
    ))) or
        (fixed and (try resolver.declaredInToolchainFile(
            container.scope_handle.handle,
            "/std/heap/FixedBufferAllocator.zig",
        )));
}

/// A copied allocation is independent only when its copied elements carry no
/// addresses. The resulting slice header remains address-bearing, even for `u8`.
fn sdkDuplicatedElementsAddressFree(
    cache: *FileCache,
    expression: Ast.Node.Index,
    walk: FreshWalk,
) FreshError!bool {
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    const frame = walk.frame orelse resolver.resolutionFrame();
    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(expression));
    var result = (try frame.typeOfNode(expression)) orelse return false;
    while (resolver.typeTag(result) == .error_union) {
        try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(expression));
        const payload = resolver.childType(result) orelse return false;
        result = (try resolver.normalizedType(payload)) orelse return false;
    }
    if (resolver.typeTag(result) != .pointer) return false;
    const elements = resolver.childType(result) orelse return false;
    return try actualTypeAddressFree(frame, elements, 0, walk.remaining);
}

/// An external allocator parameter is the allocator contract boundary; its
/// new allocations do not depend on this declaration's input payloads.
/// Explicitly constructed allocator headers are different: forwarding such a
/// header through a real SDK alloc method cannot erase its backing provenance.
pub fn allocatorOriginIsExternal(cache: *FileCache, expression: Ast.Node.Index, walk: FreshWalk, depth: u8) FreshError!bool {
    if (depth >= max_fresh_depth) return false;
    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(expression));
    const resolver = if (walk.frame) |frame| frame.resolver else cache.zls orelse return false;
    // `isStdAllocator` answers tri-state: `true` is the SDK allocator header,
    // `false` a resolved non-allocator, and null an identity this session
    // could not read.  Null proves nothing in either direction, so it reads
    // as "not an allocator" here and stops the route — never as a proof.
    const allocator_type = if (walk.frame) |frame| frame.isStdAllocator(expression) else resolver.isStdAllocator(expression);
    const is_std_allocator = (try allocator_type) orelse false;
    if (!is_std_allocator) return false;
    const tree = cache.tree;
    switch (tree.nodeTag(expression)) {
        .identifier => {
            const token = tree.nodeMainToken(expression);
            const declaration = tokens.enclosingFnDecl(tree, token) orelse return false;
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
            const body = tokens.bodyOf(tree, declaration) orelse return false;
            try charge(walk.remaining, tree, token);
            const bindings = (try cache.localBindings(proto, body)).*;
            const binding = bindings.findAt(tree.tokenSlice(token), token) orelse return false;
            if (binding.origin == .param) return true;
            if (!binding.is_const or !try plainLocalStillIndependent(cache, &bindings, binding, token, walk)) return false;
            const initializer = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
            return allocatorOriginIsExternal(cache, initializer, walk, depth + 1);
        },
        .field_access => {
            const access = tree.nodeData(expression).node_and_token;
            var root = access[0];
            while (tree.nodeTag(root) == .field_access or tree.nodeTag(root) == .deref) {
                try charge(walk.remaining, tree, tree.nodeMainToken(root));
                root = if (tree.nodeTag(root) == .deref) tree.nodeData(root).node else tree.nodeData(root).node_and_token[0];
            }
            if (tree.nodeTag(root) == .identifier) {
                const token = tree.nodeMainToken(root);
                if (tokens.enclosingFnDecl(tree, token)) |declaration| {
                    var buffer: [1]Ast.Node.Index = undefined;
                    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
                    const body = tokens.bodyOf(tree, declaration) orelse return false;
                    try charge(walk.remaining, tree, token);
                    const bindings = (try cache.localBindings(proto, body)).*;
                    if (bindings.findAt(tree.tokenSlice(token), token)) |binding| {
                        // A formal aggregate's allocator field has no external
                        // allocator contract. Its caller can supply a stack
                        // provider, or mutate it through a receiver alias.
                        // Keep this declaring-body requirement symbolic.
                        // return_storage binds the actual constructor/source
                        // cell at the call boundary before checking its origin;
                        // a formal field alone never supplies that contract.
                        if (binding.origin == .param) return false;
                    }
                }
            }
            // An immutable SDK heap-root allocator cannot capture a caller's
            // formal. This is the allocator independence boundary, not a
            // choice of provider branch or a proof of the provider's lifetime.
            try charge(walk.remaining, tree, tree.nodeMainToken(access[0]));
            const owner = if (walk.frame) |frame| frame.containerOfNode(access[0]) else resolver.containerOfNode(access[0]);
            const container = (try owner) orelse return false;
            if (container.scope_handle.scope != .root) return false;
            if (!(try resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/heap.zig"))) return false;
            const actual_owner: type_engine.TypeResolver.ActualType = .{ .data = .{ .container = container }, .is_type_val = true };
            const Analysis = @TypeOf(resolver.analyser);
            const member = tree.tokenSlice(access[1]);
            const global = (try Analysis.lookupSymbolContainer(actual_owner, member, .other)) orelse
                return false;
            if (!global.isConst() or !(try resolver.declaredInToolchainFile(global.handle, "/std/heap.zig"))) return false;
            // The actual type was authenticated above. Requiring a literal
            // initializer would reject a conditional SDK constant even though
            // none of its provider branches binds this caller's inputs.
            return true;
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
                try charge(walk.remaining, tree, tree.nodeMainToken(expression));
                if (summary.returnedParamDependency(@intCast(parameter)) != true) continue;
                var argument_buffer: [2]Ast.Node.Index = undefined;
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

/// File-model spelling locates candidate metadata; the actual instantiated
/// declaration must confirm its identity before that field list is trusted.
fn actualOwnerMatches(cache: *FileCache, range: TokenRange, owner: ResolvedType, walk: FreshWalk) FreshError!bool {
    const frame = walk.frame orelse return true;
    const node = cache.nodeForExactSpan(range.first, range.last) orelse return false;
    try charge(walk.remaining, cache.tree, cache.tree.nodeMainToken(node));
    const container = (try frame.containerOfNode(node)) orelse return false;
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
        try charge(remaining, tree, tree.nodeMainToken(current));
        switch (tree.nodeTag(current)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => scope_close = tree.lastToken(current),
            .@"errdefer" => return horizon < scope_close,
            else => {},
        }
        var children = Iterator.init(tree, current);
        var containing: ?Ast.Node.Index = null;
        while (children.next(tree)) |child| {
            try charge(remaining, tree, tree.nodeMainToken(child));
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
        try charge(walk.remaining, tree, tree.nodeMainToken(canonical.callee.call_node));
        var buffer: [2]Ast.Node.Index = undefined;
        const argument = (try canonical.callArgumentFor(cache, &buffer, @intCast(parameter))) orelse return false;
        const kind = if (walk.frame) |frame| frame.isStdAllocator(argument) else resolver.isStdAllocator(argument);
        const is_std_allocator = (try kind) orelse false;
        if (!is_std_allocator) continue;
        if (try allocatorOriginIsExternal(cache, argument, walk, 0)) continue;
        const summary = canonical.summary orelse return false;
        if (summary.returnedParamDependency(@intCast(parameter)) != false) return false;
        const effect = (try cache.callEffectAt(calleeQueryToken(tree, call), .{
            .parameter = .{ .param = @intCast(parameter), .read_only_only = true },
        }, .{ .frame = walk.frame, .remaining = walk.remaining })) orelse return false;
        if (effect != .read_only) return false;
    }
    return true;
}

test "a bound that stops the zero check is a failure, not the answer not-zero" {
    const gpa = std.testing.allocator;
    var text: std.ArrayListUnmanaged(u8) = .empty;
    defer text.deinit(gpa);
    try text.appendSlice(gpa, "const zero = 0;\nconst deep = ");
    for (0..70) |_| try text.appendSlice(gpa, "-(");
    try text.append(gpa, '0');
    for (0..70) |_| try text.append(gpa, ')');
    try text.appendSlice(gpa, ";\n");
    const source = try gpa.dupeZ(u8, text.items);
    defer gpa.free(source);
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const zero = tree.fullVarDecl(tree.rootDecls()[0]).?.ast.init_node.unwrap().?;
    const deep = tree.fullVarDecl(tree.rootDecls()[1]).?.ast.init_node.unwrap().?;
    const claim: fn_summary.FreshClaim = .{ .first = 0, .last = 0 };
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    try std.testing.expect(try numericValueIsZero(&cache, zero, FreshWalk.root(claim)));
    try std.testing.expectError(
        error.AnalysisBudgetExceeded,
        numericValueIsZero(&cache, deep, FreshWalk.root(claim)),
    );
    const stop = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_depth, stop.limit);
    try std.testing.expectEqual(@as(u32, 64), stop.limit_value);
}
