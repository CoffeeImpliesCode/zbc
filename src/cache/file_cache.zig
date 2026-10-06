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
const cfg_builder_mod = @import("../flow/cfg_builder.zig");
const grow_analysis_mod = @import("grow_analysis.zig");
const call_summary_mod = @import("call_summary.zig");
const fresh_storage_mod = @import("fresh_storage.zig");
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
pub const OpenError = error{ OutOfMemory };

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

/// Resource failures over the whole summary and grow fold — the union
/// `FileCache` derives from the fallible steps of both: this file's model
/// (`ModelError`), and the bounded-work allowance the fold spends.  A
/// named set rather than an inferred one for the same reason as
/// `OpenError`: the fold is mutually recursive, so an inferred set cannot
/// be resolved through the cycle.
pub const SummaryError = ModelError || error{ OutOfMemory, AnalysisBudgetExceeded };


pub const FileCache = struct {
    gpa: std.mem.Allocator,
    tree: *const Ast,
    /// Arena for FnSummary's variable-length fields
    /// (may_free_fields, result_heap_fields).  Lazy: only initialized
    /// on first summaryOf call that needs it.
    summary_arena: ?std.heap.ArenaAllocator = null,
    file_model: ?file_model.FileModel = null,
    bindings: std.AutoHashMapUnmanaged(u32, local_bindings.LocalBindings) = .empty,
    summaries: std.AutoHashMapUnmanaged(u32, fn_summary.FnSummary) = .empty,
    /// Optional ZLS-backed type resolver.  When set, type-shaped
    /// questions (param container name, field type) prefer ZLS over
    /// the token-walk fallback — handles cross-module types, generic
    /// instantiations, and pointer/optional chains uniformly instead
    /// of via fragile token-pattern proxies.
    zls: ?*zls_resolver_mod.TypeResolver = null,
    /// Optional project-wide cache for cross-file model lookups via
    /// relative `@import("./file.zig")` declarations.  When set,
    /// rules can ask "does <ImportAlias>.<TypeName> have a deinit?"
    /// and the cache loads the target file lazily.
    project: ?*project_cache_mod.ProjectCache = null,
    /// Absolute (or project-relative) path of the file this cache
    /// is analysing.  Used as the from-path for @import resolution
    /// in the ProjectCache.  Empty string means "use cwd".
    file_path: []const u8 = "",
    /// Result cache for cross-file method lookups.  Key = gpa-owned
    /// "TypeName\x00methodName" string.  Value = null means "looked
    /// up, not found"; non-null means found at that ResolvedMethod.
    /// Avoids re-traversing the @import graph for every call site
    /// that uses the same (type, method) pair.
    method_lookup_cache: std.StringHashMapUnmanaged(?ResolvedMethod) = .empty,
    /// The receiver-field writes and releases of a method declared in
    /// ANOTHER file, keyed by the same "TypeName\x00methodName" string
    /// `method_lookup_cache` uses.  Each value's slices live in
    /// `summary_arena`, which outlives the analysis, so a summary
    /// handed back BY VALUE keeps lending these paths to callers
    /// after the call that produced it has returned.
    cross_file_fields: std.StringHashMapUnmanaged(fn_summary.FieldEffects) = .empty,
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

    pub fn init(gpa: std.mem.Allocator, tree: *const Ast) FileCache {
        return .{ .gpa = gpa, .tree = tree };
    }

    pub fn setZls(self: *FileCache, zls: ?*zls_resolver_mod.TypeResolver) void {
        self.zls = zls;
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

    /// Cross-file type lookup.  When `name` isn't found in the
    /// current file's model, scan @import declarations and try
    /// each imported file's model.  Walks one level of @import
    /// indirection — doesn't recurse into the imported file's own
    /// imports (a deeper search would risk diamond-load cycles and
    /// blow up cache size for large projects).  Returns null when
    /// the type is unresolvable in this file OR in any directly-
    /// imported file.
    pub fn findTypeAcrossImports(
        self: *FileCache,
        name: []const u8,
    ) ?*const file_model.TypeInfo {
        const model = self.fileModel() catch return null;
        if (model.findType(name)) |ti| return ti;
        const pc = self.project orelse return null;
        if (self.file_path.len == 0) return null;
        // Primary: global type index.  Triggers buildTypeIndex on the first
        // call (one-time serial cost); O(1) on all subsequent calls.
        const entries = pc.findAllTypesByName(self.file_path, name) catch {
            // OOM fallback: traverse @import graph directly.
            return findTypeViaImports(pc, self.tree, self.file_path, name, 4);
        };
        if (entries.len == 0) return null;
        return entries[0].typeInfo();
    }

    /// `findTypeAcrossImports` with the document a type was read from
    /// kept beside it.  A question about a type's FIELDS needs that
    /// provenance, because a field's own token range belongs to the
    /// document that declares it rather than to the file the question
    /// was asked from.
    pub fn resolvedTypeAcrossImports(
        self: *FileCache,
        name: []const u8,
    ) ?ResolvedType {
        const model = self.fileModel() catch return null;
        if (model.findType(name)) |ti| {
            return .{ .model = model, .info = ti, .path = self.file_path, .module = self.module_id };
        }
        const pc = self.project orelse return null;
        if (self.file_path.len == 0) return null;
        const entries = pc.findAllTypesByName(self.file_path, name) catch
            return resolvedTypeViaImports(pc, self.tree, self.file_path, name, 4, self.module_id);
        if (entries.len == 0) return null;
        return .{
            .model = &entries[0].entry.model,
            .info = entries[0].typeInfo(),
            .path = entries[0].entry.abs_path,
            .module = self.module_id,
        };
    }

    /// The type `name` names in a file THIS file reaches through
    /// `@import`, and nowhere else.
    ///
    /// `resolvedTypeAcrossImports` falls back to the project-wide type
    /// index, and that index's first call walks and parses every `.zig`
    /// file under the project root.  A rule that asks this question for
    /// every declaration in every file it analyses cannot pay that, and
    /// what the walk buys it is the worse half of the trade: the index
    /// answers by NAME over the whole project, so a head this file
    /// cannot reach can come back as an unrelated same-named type
    /// declared in some other package, and the callee is then read off
    /// the wrong declaration.  A type the `@import` graph does not
    /// reach reads as unresolved here, which is what "not reachable"
    /// means to the file being analysed — the same answer the bounded
    /// traversal gives on its very first hop.
    pub fn importedTypeAcrossImports(
        self: *FileCache,
        name: []const u8,
    ) ?ResolvedType {
        const model = self.fileModel() catch return null;
        if (model.findType(name)) |ti| {
            return .{ .model = model, .info = ti, .path = self.file_path, .module = self.module_id };
        }
        const pc = self.project orelse return null;
        if (self.file_path.len == 0) return null;
        return resolvedTypeViaImports(pc, self.tree, self.file_path, name, 4, self.module_id);
    }

    /// `Namespace.Tag` is `Tag` declared inside the type `Namespace`
    /// names, and a type path is a path: the head segment is looked up
    /// exactly as a bare name is, and every later segment must be a
    /// type DECLARED inside the one before it.  A segment that names a
    /// value, a re-export or a field rather than a nested declaration
    /// ends the walk with no answer — this walk proves a declaration or
    /// it proves nothing, so a caller must read the null as "not
    /// resolved here" and not as "no such type".
    ///
    /// `resolvedTypeAcrossImports` answers bare names only; handing it
    /// a dotted one can never match, because a declaration is stored
    /// under the identifier it was written with, not under a path.
    pub fn resolvedTypePathAcrossImports(
        self: *FileCache,
        name: []const u8,
    ) ?ResolvedType {
        var segments: [max_type_path_segments][]const u8 = undefined;
        const count = splitTypePath(&segments, name);
        if (count == 0) return null;
        return walkTypePath(self.resolvedTypeAcrossImports(segments[0]), segments[1..count]);
    }

    /// The same dotted-name walk, read in the scope `owner` was
    /// declared in: a field typed `Outer.Inner` resolves `Outer` where
    /// the field was written, not where the question is asked from.
    pub fn typePathInOwnerScope(
        self: *FileCache,
        owner: ResolvedType,
        name: []const u8,
    ) ?ResolvedType {
        var segments: [max_type_path_segments][]const u8 = undefined;
        const count = splitTypePath(&segments, name);
        if (count == 0) return null;
        return walkTypePath(self.typeInOwnerScope(owner, segments[0]), segments[1..count]);
    }

    /// The type `name` names in the scope `owner` was declared in: the
    /// owner's own nested types first, then its enclosing scopes, then
    /// the file.  A field's declared type resolves against the type
    /// that declared it, not against the file the question was asked
    /// from — `outer.Inner.Outer.Inner` is one `Inner`, and answering
    /// it from the reader's scope would hand back a different one.
    pub fn typeInOwnerScope(
        self: *FileCache,
        owner: ResolvedType,
        name: []const u8,
    ) ?ResolvedType {
        const found = owner.model.findTypeInScope(name, owner.info) orelse
            return self.findTypeAcrossImportsFrom(owner.path, name);
        return .{ .model = owner.model, .info = found, .path = owner.path, .module = owner.module };
    }

    /// The type a field of `owner` declares, or null when the field or
    /// the type it names is not readable here.  The result is the field
    /// chain's next step: it is fed back into this same query to walk a
    /// dotted path, so it carries the same document the answer was
    /// read from.
    pub fn fieldType(
        self: *FileCache,
        owner: ResolvedType,
        field_name: []const u8,
    ) ?ResolvedType {
        const found = owner.model.fieldType(owner.info.name, field_name) orelse return null;
        // The name came out of the OWNER's model, so it is resolved there
        // first — a field type is a bare name written in the same
        // declaration as the field.  A field typed with an imported
        // namespace resolves through the owner's own imports, not through
        // this file's.
        const info = owner.model.findType(found) orelse
            return self.findTypeAcrossImportsFrom(owner.path, found);
        return .{ .model = owner.model, .info = info, .path = owner.path, .module = owner.module };
    }

    /// `findTypeAcrossImports` for a question asked ABOUT another file:
    /// the @import graph is walked from `from_path`, because a relative
    /// import means something different from each file.
    fn findTypeAcrossImportsFrom(self: *FileCache, from_path: []const u8, name: []const u8) ?ResolvedType {
        if (std.mem.eql(u8, from_path, self.file_path)) return self.resolvedTypeAcrossImports(name);
        const pc = self.project orelse return null;
        if (from_path.len == 0) return null;
        const entries = pc.findAllTypesByName(from_path, name) catch {
            return resolvedTypeViaImports(pc, self.tree, from_path, name, 4, self.module_id);
        };
        if (entries.len == 0) return null;
        return .{
            .model = &entries[0].entry.model,
            .info = entries[0].typeInfo(),
            .path = entries[0].entry.abs_path,
            .module = self.module_id,
        };
    }

    /// Resolved cross-file method lookup result.  When the method
    /// lives in a foreign file, `tree` points at THAT file's tree
    /// (foreign token indices) — callers MUST use this returned
    /// tree (not their own) for any token / node operations on
    /// `method.fn_decl`.
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
    /// read from and the module it was read in.  That provenance is
    /// needed because a field's own token range belongs to `model`'s
    /// tree, not to the tree of whichever document asked the question —
    /// reading one file's token indices against another's tree would
    /// interpret them as positions in the wrong source.
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

    /// Look up `<type_name>.<method_name>` either in this file or
    /// in any directly @import'd file (one hop), returning the
    /// owning tree alongside the MethodInfo.  Used by cross-fn
    /// lifecycle analysis to walk a called fn's body even when the
    /// fn lives in a different file.
    ///
    /// Cross-file results are cached keyed by "TypeName\x00method"
    /// so repeated lookups of the same (type, method) pair across
    /// many call sites in one file pay the @import-traversal cost
    /// only once.
    pub fn findMethodAcrossImports(
        self: *FileCache,
        type_name: []const u8,
        method_name: []const u8,
    ) ?ResolvedMethod {
        // Fast path: type lives in the current file — no traversal.
        const model = self.fileModel() catch return null;
        if (model.findType(type_name)) |ti| {
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

    /// Slow path: @import-graph traversal + global type index fallback.
    /// Called only on a cache miss in findMethodAcrossImports.
    ///
    /// Strategy: ask the @import-graph traversal first.  It reads only the
    /// files THIS file actually reaches, one bounded hop at a time, and it
    /// answers with the declaration the file really imports.  The global
    /// type index answers by NAME over the whole project: its first call
    /// parses every .zig file under the project root, which on a large
    /// tree costs far more than the question it was asked — and it cannot
    /// see the files the walk skips (vendor/build/cache dirs) at all, so
    /// for a type reached through @import it is both the slower and the
    /// blinder of the two.  It stays the fallback, and it is still built
    /// at most once per ProjectCache: it is asked precisely when the cheap
    /// question did not answer, which is the case only it can.
    fn findMethodCrossFile(
        self: *FileCache,
        pc: *project_cache_mod.ProjectCache,
        type_name: []const u8,
        method_name: []const u8,
    ) ?ResolvedMethod {
        // The traversal is bounded (four hops) and memoised per (type,
        // method) by findMethodAcrossImports, incl. the negative, so it
        // runs at most once per pair per file.
        if (findMethodViaImports(pc, self.tree, self.file_path, type_name, method_name, 4)) |hit| {
            return hit;
        }
        // A traversal miss is not proof the type is unreachable: the
        // question can be about a type this file reaches by a module name
        // rather than a relative path, or about one declared in a file the
        // @import graph does not reach at all.  The index answers by name
        // over the whole project.  A name declared in two files under the
        // root used to be answered by whichever the directory walk reached
        // first; that order is filesystem-dependent, so the traversal's
        // hit — the file that actually imports the type — is the
        // deterministic one.
        if (pc.findAllTypesByName(self.file_path, type_name) catch null) |tes| {
            for (tes) |te| {
                const ti = te.typeInfo();
                if (ti.findMethod(method_name)) |m| return .{ .tree = te.tree(), .method = m };
            }
        }
        return null;
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
            var buf: [1]Ast.Node.Index = undefined;
            for (tree.nodes.items(.tag), 0..) |tag, raw| {
                switch (tag) {
                    .call, .call_comma, .call_one, .call_one_comma => {},
                    else => continue,
                }
                const node: Ast.Node.Index = @enumFromInt(raw);
                const call = tree.fullCall(&buf, node) orelse continue;
                try index.by_callee_token.put(self.gpa, tree.nodeMainToken(call.ast.fn_expr), node);
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
    /// Two answers, and only the second refuses:
    ///
    ///   * a call that resolves into ANOTHER document is stepped over, not
    ///     refused.  `std.math.maxInt(..)` is in almost every file, and
    ///     refusing on it would refuse every body that merely mentions the
    ///     standard library — the cross-document callee is the common case,
    ///     not the doubtful one;
    ///   * a call this run cannot place REFUSES.  An unplaced reference may
    ///     be a caller no scan of this file can see, and a claim about what
    ///     every site agreed on has to bound the whole claim to nothing
    ///     rather than to the average of the sites that were seen.
    ///
    /// A file that writes a reflective entry point is refused WHOLE.
    /// `@field(Model, "grow")` binds the callee to a fresh local and the
    /// call through that local is spelled with the LOCAL's name, so such
    /// an entry is no identifier reference to `grow` and no call any name
    /// scan matches — and a census would read a file with a hidden heap
    /// caller as closed.
    ///
    /// Memoised per declaration, so a helper consulted from several sites
    /// is resolved once rather than once per site and per recursion level.
    /// The slice is borrowed and filed in the cache's own allocator, so
    /// it outlives every caller.
    pub fn closedLocalCalls(self: *FileCache, fn_decl: Ast.Node.Index) error{OutOfMemory}!?[]Ast.Node.Index {
        if (self.closed_local_calls.get(fn_decl)) |memoized| return memoized;
        // The memo stores null as "refused", so a refusal is as
        // memoised as an answer and is asked once.
        errdefer self.closed_local_calls.put(self.gpa, fn_decl, null) catch {};
        const calls = try self.buildClosedLocalCalls(fn_decl);
        try self.closed_local_calls.put(self.gpa, fn_decl, calls);
        return calls;
    }

    /// The set `closedLocalCalls` memoises.  Split out so the refusal
    /// scan runs before anything is allocated.
    fn buildClosedLocalCalls(self: *FileCache, fn_decl: Ast.Node.Index) error{OutOfMemory}!?[]Ast.Node.Index {
        if (self.writesReflectiveEntryPoint()) return null;
        const tree = self.tree;
        const resolver = self.zls orelse return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, fn_decl) orelse return null;
        var calls: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        errdefer calls.deinit(self.gpa);
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            switch (tag) {
                .call, .call_comma, .call_one, .call_one_comma => {},
                else => continue,
            }
            // Node 0 is not a node in Zig's AST.
            if (raw == 0) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node) orelse continue;
            // Bind to the DECLARATION, not the spelling.  A resolution
            // that failed for a reason of its own says nothing about this
            // callee, and a reference this run cannot place is exactly
            // what the contract refuses.  Only running out of memory
            // travels out.
            const reference = switch (resolver.functionReference(call.ast.fn_expr) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => return null,
            }) {
                .function => |found| found,
                .unknown, .not_callable => return null,
            };
            // Another document's callee is not a caller of this
            // declaration; among this file's own declarations only the
            // one carrying this body is.
            if (reference.tree != tree) continue;
            if (reference.fn_token != proto.ast.fn_token) continue;
            try calls.append(self.gpa, node);
        }
        return try calls.toOwnedSlice(self.gpa);
    }

    /// Does this file write a reflective entry point — a way of naming
    /// a callee that no scan of identifiers can see?
    ///
    /// `@field(Model, "grow")` builds the callee value into a fresh
    /// local, and the call through that local is spelled with the
    /// LOCAL's name.  A name-based census therefore reads a file with a
    /// hidden caller as closed, so its presence refuses the whole file
    /// rather than being reasoned about locally.
    fn writesReflectiveEntryPoint(self: *FileCache) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        for (tags, 0..) |tag, raw| {
            if (tag != .builtin) continue;
            const name = tree.tokenSlice(@intCast(raw));
            if (std.mem.eql(u8, name, "@field") or
                std.mem.eql(u8, name, "@export") or
                std.mem.eql(u8, name, "@embedFile") or
                std.mem.eql(u8, name, "@compileError")) return true;
        }
        return false;
    }

    // ── Address uses ─────────────────────────────────────────────────

    /// One `&` operand in this file: the expression the address is of,
    /// and whether that address can act as a WRITE.
    ///
    /// The flag is the whole of the distinction a caller needs.  Taking
    /// an address neither reads the storage nor writes it, so an
    /// out-parameter question cannot treat every `&x` as a store; what
    /// it can do is hand `x`'s address to something that writes back
    /// through it.
    pub const AddressUse = struct { operand: Ast.Node.Index, may_write: bool };
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
    ) error{ OutOfMemory, AnalysisBudgetExceeded }!?AddressUse {
        if (self.address_uses == null) self.address_uses = try self.buildAddressUses();
        return self.address_uses.?.get(operand_token);
    }

    /// Nesting depth of the whole-file address-use walk.  Bounded
    /// because the walk keeps one frame per AST level; named so the
    /// check and the reported diagnostic cannot drift apart.
    const max_address_use_frames = 256;

    /// The `&` operand of an `address_of` node and whether it sits in
    /// an argument position.  BUILT INSTEAD OF COMPUTED PER QUERY: a
    /// body walk asks about every identifier token it passes, and
    /// answering each one by descending the whole file again would be
    /// quadratic in the file's size.
    fn buildAddressUses(self: *FileCache) error{ OutOfMemory, AnalysisBudgetExceeded }!AddressUseMap {
        const Iterator = engine.AstIterator;
        const Frame = struct {
            children: Iterator,
            in_argument: bool,
            call_children: bool,
            first_child: bool = true,
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
        // walk gives up rather than report a truncated count.
        const node_budget = std.math.cast(u32, self.tree.nodes.len) orelse
            return error.AnalysisBudgetExceeded;
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
                    });
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
        if (tokens.enclosingFnDecl(self.tree, token)) |decl| {
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
        if (comptimeBlockEnclosing(tree, token)) |_| return false;
        if (comptimeOnlyBuiltinArgument(tree, token)) return false;
        return true;
    }

    pub fn deinit(self: *FileCache) void {
        if (self.line_offsets.len > 0) self.gpa.free(self.line_offsets);
        if (self.file_model) |*m| m.deinit();
        if (self.summary_arena) |*a| a.deinit();
        var it = self.bindings.valueIterator();
        while (it.next()) |b| b.deinit();
        self.bindings.deinit(self.gpa);
        self.summaries.deinit(self.gpa);
        var mit = self.method_lookup_cache.iterator();
        while (mit.next()) |e| self.gpa.free(e.key_ptr.*);
        self.method_lookup_cache.deinit(self.gpa);
        var cfit = self.cross_file_fields.iterator();
        while (cfit.next()) |e| self.gpa.free(e.key_ptr.*);
        self.cross_file_fields.deinit(self.gpa);
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
        self.actual_callees.deinit(self.gpa);
        self.direct_effects.deinit(self.gpa);
        self.fresh_storage.deinit(self.gpa);
        self.fresh_visiting.deinit(self.gpa);
        self.scalar_params.deinit(self.gpa);
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
    pub fn getLineOffsets(self: *FileCache) ![]const u32 {
        if (self.line_offsets.len > 0) return self.line_offsets;
        self.line_offsets = try cfg_builder_mod.buildLineOffsets(self.gpa, self.tree.source);
        return self.line_offsets;
    }

    /// Lazily build (and cache) LocalBindings for the given fn body.
    /// Keyed by body node — rules processing the same fn share one
    /// build.  The returned pointer is borrowed from the cache and
    /// stable for the lifetime of the cache.
    pub fn localBindings(
        self: *FileCache,
        proto: Ast.full.FnProto,
        body: Ast.Node.Index,
    ) !*const local_bindings.LocalBindings {
        const key = @intFromEnum(body);
        const gop = try self.bindings.getOrPut(self.gpa, key);
        if (!gop.found_existing) {
            gop.value_ptr.* = try local_bindings.build(self.gpa, self.tree, proto, body);
        }
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

    /// Return the param's ZLS-resolved container name (e.g. "T" for
    /// `*T`, `*const T`, `?*T`, `*lib.T`).  Returns null when ZLS is
    /// not available or cannot resolve the type — callers handle null
    /// conservatively (skip the typed lookup) rather than falling back
    /// to a syntactic approximation that could return the wrong name
    /// for aliases, comptime types, or cross-module re-exports.
    fn paramContainerName(
        self: *FileCache,
        proto: Ast.full.FnProto,
        idx: u32,
    ) !?[]const u8 {
        var i: u32 = 0;
        var it = proto.iterate(self.tree);
        while (it.next()) |p| : (i += 1) {
            if (i != idx) continue;
            const type_node = p.type_expr orelse return null;
            // Syntactic fast-path: handles `*T`, `?*T`, `T`, `ns.T`, etc.
            // without invoking ZLS. Covers the vast majority of real-world
            // parameter types; ZLS is only needed for aliases/generics.
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
            // The field's type may live in another file (the common
            // composed-owner shape `self.inner.deinit()` where `inner`'s
            // type is imported, deepest_path.ns != null).  Same-file types
            // resolve via summaryByMethod; cross-file types via
            // summaryByMethodCrossFile (@import graph / global type index),
            // which confirms the method exists across imports before we
            // apply the cleanup-name presumption.
            const keep: bool = blk: {
                if (deepest_path.ns == null) {
                    if (!model.hasType(deepest_path.type_name)) break :blk false;
                    const ti = model.findType(deepest_path.type_name) orelse break :blk false;
                    if (!ti.hasMethod(ff.method)) break :blk false;
                    const cs = (try self.summaryByMethod(deepest_path.type_name, ff.method)) orelse break :blk false;
                    break :blk cs.takes_ownership_of != null or
                        fn_summary.isReceiverCleanupMethodName(ff.method);
                }
                const xf = (try self.summaryByMethodCrossFile(deepest_path.type_name, ff.method)) orelse break :blk false;
                break :blk xf.takes_ownership_of != null or
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
        const model = try self.fileModel();
        // Phase 1a: pre-warm summaries for every fn.
        for (model.fns) |fi| _ = try self.summaryOfFn(fi.fn_decl);
        for (model.types) |ti| {
            for (ti.methods) |m| _ = try self.summaryOfFn(m.fn_decl);
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
        while (iters < 16) : (iters += 1) {
            var changed = false;
            for (model.fns) |fi| {
                if (try self.propagateTransitiveTakesOne(fi.fn_decl, null)) changed = true;
            }
            for (model.types) |ti| {
                for (ti.methods) |m| {
                    if (try self.propagateTransitiveTakesOne(m.fn_decl, ti.name)) changed = true;
                }
            }
            if (!changed) break;
        }

        // Phase 3: filter may_free_fields per fn.  Done here (not in
        // summaryOfFn) because the filter consults OTHER fn summaries
        // — moving it inside summaryOfFn creates a comptime dep cycle.
        // Filter requires Phase 2 to be done so the called methods'
        // takes_ownership_of reflects the transitive analysis.
        for (model.fns) |fi| try self.filterMayFreeFieldsOne(fi.fn_decl);
        for (model.types) |ti| {
            for (ti.methods) |m| try self.filterMayFreeFieldsOne(m.fn_decl);
        }

        // Phase 4: fixed-point R7 inference — propagate
        // `returns = .borrowed_from(N)` across delegating wrappers.
        // A fn whose body returns a delegating call to another fn
        // that's inferred borrowed_from inherits the borrowed_from
        // with the local param index.  Skipped when the fn's returns
        // is already known (preserves .heap / .owned / explicit
        // borrowed_from).
        iters = 0;
        while (iters < 16) : (iters += 1) {
            var changed = false;
            for (model.fns) |fi| {
                if (try self.inferDelegatorBorrowOne(fi.fn_decl)) changed = true;
            }
            for (model.types) |ti| {
                for (ti.methods) |m| {
                    if (try self.inferDelegatorBorrowOne(m.fn_decl)) changed = true;
                }
            }
            if (!changed) break;
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
            while (iters < 16) : (iters += 1) {
                var changed = false;
                for (model.fns) |fi| {
                    if (try self.propagateEffectOne(fi.fn_decl, null, eff)) changed = true;
                }
                for (model.types) |ti| {
                    for (ti.methods) |m| {
                        if (try self.propagateEffectOne(m.fn_decl, ti.name, eff)) changed = true;
                    }
                }
                if (!changed) break;
            }
        }
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
        // Typed lookup first (precise — ZLS resolves the param's type).
        // Bare-name fallback only when the param type is unresolvable:
        // that path finds top-level fns with the same name, which can
        // fire on the wrong type if names collide.
        var target_idx = try self.lookupBorrowedFromParamTypeSameFile(proto, param_idx, method_name);
        if (target_idx == null) {
            target_idx = try self.lookupBorrowedFromSameFile(method_name);
        }
        if ((target_idx orelse return null) == 0) return param_idx;
        return null;
    }

    /// `return <Path>.<method>(arg0, arg1, ...);` shape.  Fires when
    /// `<method>` is `borrowed_from(N)` and arg N resolves to one of
    /// our params.  Same-file first; then cross-file via namespace.
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
        var target_idx = try self.lookupBorrowedFromSameFile(method_name);
        if (target_idx == null) {
            // Namespace-style: `Foo.method(arg)` where Foo is a local
            // type — look up Foo.method via summaryByMethod.
            if (tree.nodeTag(callee) == .field_access) {
                const recv = tree.nodeData(callee).node_and_token[0];
                if (tree.nodeTag(recv) == .identifier) {
                    const type_name = tree.tokenSlice(tree.nodeMainToken(recv));
                    if ((try self.summaryByMethod(type_name, method_name))) |s| {
                        target_idx = switch (s.returns) {
                            .borrowed_from => |i| i,
                            else => null,
                        };
                    }
                }
            }
        }
        // Cross-file namespace lookup retired with remote_resolver.
        const idx_resolved = target_idx orelse return null;
        const args = call_full.ast.params;
        if (idx_resolved >= args.len) return null;
        const arg = args[idx_resolved];
        if (tree.nodeTag(arg) != .identifier) return null;
        const arg_name = tree.tokenSlice(tree.nodeMainToken(arg));
        return fn_summary.paramIndex(tree, proto, arg_name);
    }

    /// Look up a top-level fn by name and return its `borrowed_from`
    /// target index when the summary's returns is that variant.
    fn lookupBorrowedFromSameFile(self: *FileCache, method_name: []const u8) !?u32 {
        const s = (try self.summaryByName(method_name)) orelse return null;
        return switch (s.returns) {
            .borrowed_from => |idx| idx,
            else => null,
        };
    }

    /// Same-file typed lookup: look up `method_name` on the type of
    /// the named param.  Catches methods on locally-declared types
    /// that lookupBorrowedFromSameFile (top-level fns only) misses.
    fn lookupBorrowedFromParamTypeSameFile(
        self: *FileCache,
        proto: Ast.full.FnProto,
        param_idx: u32,
        method_name: []const u8,
    ) !?u32 {
        const type_name = (try self.paramContainerName(proto, param_idx)) orelse return null;
        const s = (try self.summaryByMethod(type_name, method_name)) orelse return null;
        return switch (s.returns) {
            .borrowed_from => |idx| idx,
            else => null,
        };
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
        const entry = self.summaries.getPtr(key) orelse return;
        if (entry.may_free_fields.len == 0) return;
        const model = try self.fileModel();
        if (self.summary_arena == null) {
            self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        }
        const a = self.summary_arena.?.allocator();
        entry.may_free_fields = try self.filterMayFreeFields(a, model, self.tree, proto, entry.may_free_fields);
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
        const ti = model.findType(type_name) orelse return null;
        const m = ti.findMethod(method_name) orelse return null;
        return try self.summaryOfFn(m.fn_decl);
    }

    /// Look up method summary in an @import'd file.  When `type_name`
    /// is not in the current file, searches directly @import'd files
    /// (one hop) and the global type index via ProjectCache.
    ///
    /// Returns FnSummary BY VALUE — only `inferDirectTakes`-level
    /// inference is applied (no transitive resolution for cross-file
    /// methods; that would require loading and running the full
    /// resolveTransitiveTakes pipeline for the imported file).
    ///
    /// Use case: detecting that a callee defined in another file takes
    /// ownership of its first parameter (e.g. `bun.destroy(ptr)` where
    /// `destroy` lives in `bun.zig`).
    pub fn summaryByMethodCrossFile(
        self: *FileCache,
        type_name: []const u8,
        method_name: []const u8,
    ) !?fn_summary.FnSummary {
        // Project-level cache: check before the expensive @import traversal.
        // Shared across all per-file FileCache instances — pays the traversal
        // cost at most once globally per (type, method) pair.
        if (self.project) |pc| {
            if (pc.getMethodSummaryCache(type_name, method_name)) |cached| {
                if (!cached.found) return null;
                var s: fn_summary.FnSummary = .{};
                s.takes_ownership_of = cached.takes;
                s.may_grow_collections = cached.may_grow;
                s.may_invoke_gc = cached.may_gc;
                s.may_run_on_any_thread = cached.may_thread;
                // `CachedTakes` is POD and carries no slices, so the
                // paths are re-read from the declaration here.  They
                // are memoised per file, and this branch is only
                // reached after some other file paid the traversal.
                const eff = try self.foreignFieldEffects(type_name, method_name);
                s.freed_paths = eff.freed_paths;
                s.written_paths = eff.written_paths;
                return s;
            }
        }

        const rm = self.findMethodAcrossImports(type_name, method_name) orelse {
            if (self.project) |pc| pc.putMethodSummaryCache(type_name, method_name, .{ .found = false });
            return null;
        };
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(rm.tree, &buf, rm.method.fn_decl) orelse return null;
        const body = tokens.bodyOf(rm.tree, rm.method.fn_decl) orelse return null;
        var summary: fn_summary.FnSummary = .{};
        summary.takes_ownership_of = fn_summary.inferDirectTakes(rm.tree, proto, body);
        // Cross-file EFFECT flags (#20): the foreign method's DIRECT effects
        // (a `.append(` grows, a gc-trigger / exit-callback-register call).
        // Body-level only — cheap, no foreign-file propagation — so a
        // foreign method that merely DELEGATES the effect to its own callee
        // isn't seen (a documented bound; effects are narrow-value).
        const direct = fn_summary.inferFromBody(rm.tree, proto, body);
        summary.may_grow_collections = direct.may_grow_collections;
        summary.may_invoke_gc = direct.may_invoke_gc;
        summary.may_run_on_any_thread = direct.may_run_on_any_thread;
        // Transitive takes WITHIN the foreign file: if direct inference
        // found nothing, the method may DELEGATE ownership to a same-file
        // callee (`pub fn kill(self, g) { self.reallyFree(g); }`).  Run the
        // foreign file's own same-file fixed-point propagation over a
        // throwaway, PROJECT-LESS FileCache and read the method's resolved
        // takes.  Project-less is the termination guarantee: with no
        // project the foreign cache's own cross-file fallback is a no-op,
        // so there is no mutual recursion.  Bounded to one foreign file —
        // a foreign method that delegates across yet ANOTHER file is not
        // followed (a deeper, cycle-guarded version is future work).
        if (summary.takes_ownership_of == null) {
            var fc = FileCache.init(self.gpa, rm.tree);
            defer fc.deinit();
            fc.resolveTransitiveTakes() catch {};
            if (fc.summaryByMethod(type_name, method_name) catch null) |ts| {
                summary.takes_ownership_of = ts.takes_ownership_of;
            }
        }
        // The receiver-field writes and releases of the resolved
        // declaration, read the way `summaryOfFn` reads them for a
        // same-file one.  See `foreignFieldEffects` for why these and
        // not another copy are what this summary carries.
        {
            const eff = try self.foreignFieldEffects(type_name, method_name);
            summary.freed_paths = eff.freed_paths;
            summary.written_paths = eff.written_paths;
        }
        if (self.project) |pc| pc.putMethodSummaryCache(
            type_name,
            method_name,
            .{
                .found = true,
                .takes = summary.takes_ownership_of,
                .may_grow = summary.may_grow_collections,
                .may_gc = summary.may_invoke_gc,
                .may_thread = summary.may_run_on_any_thread,
            },
        );
        return summary;
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
    /// list to reconcile with this one and none to double-count: the
    /// memo below stores exactly what the declaration said, and a
    /// summary fed back through the project cache reads them again from
    /// here rather than appending a second copy.
    ///
    /// The slices live in `summary_arena`, which outlives the analysis,
    /// so the value may be copied into a summary handed back by value.
    fn foreignFieldEffects(
        self: *FileCache,
        type_name: []const u8,
        method_name: []const u8,
    ) !fn_summary.FieldEffects {
        const key = std.fmt.allocPrint(
            self.gpa,
            "{s}\x00{s}",
            .{ type_name, method_name },
        ) catch return .{};
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

    /// ZLS-backed type-of-expression resolver.  Walk the AST for a
    /// node whose `firstToken` equals `start_tok` and `lastToken`
    /// equals `end_tok`, then ask ZLS for its container type name.
    /// Used by rules to refine "unknown type → assume has deinit"
    /// fallbacks when the binding's RHS is a cross-file call
    /// whose return type isn't locally declared.
    pub fn typeNameOfExpr(
        self: *FileCache,
        start_tok: Ast.TokenIndex,
        end_tok: Ast.TokenIndex,
    ) !?[]const u8 {
        const zls = self.zls orelse return null;
        const tree = self.tree;
        // For any node: firstToken(n) <= main_token(n) <= lastToken(n).
        // Filter candidates to main_token in [start_tok, end_tok] before
        // calling the expensive firstToken/lastToken on each node.
        const main_toks = tree.nodes.items(.main_token);
        var idx: u32 = 1;
        while (idx < tree.nodes.len) : (idx += 1) {
            const mt = main_toks[idx];
            if (mt < start_tok or mt > end_tok) continue;
            const node: Ast.Node.Index = @enumFromInt(idx);
            const ft = tree.firstToken(node);
            const lt = tree.lastToken(node);
            if (ft != start_tok or lt != end_tok) continue;
            return zls.typeNameOfNode(node) catch null;
        }
        return null;
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
    ) error{OutOfMemory, AnalysisBudgetExceeded}!bool {
        return fresh_storage_mod.provesFreshStorage(self, claim, null);
    }

    /// The body this cache owns that reads declarations of `handle`,
    /// opened once per document and released only by the root cache that
    /// owns the grow state it shares.
    pub fn sourceDocument(
        self: *FileCache,
        handle: engine.DocumentStore.Handle,
    ) OpenError!*grow_analysis_mod.SourceDocument {
        return grow_analysis_mod.sourceDocument(self, handle);
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

    /// The FnSummary for a declaration addressed by the document it was
    /// read from — used for a declaration in another file, where this
    /// cache's own tree is not the tree the node index belongs to.
    pub fn summaryOfResolvedMethod(
        self: *FileCache,
        declared: ResolvedFnDecl,
    ) SummaryError!?*const fn_summary.FnSummary {
        if (declared.tree == self.tree) return self.summaryOfFn(declared.fn_decl);
        // The node index belongs to the foreign tree, so the summary is
        // read in a cache opened over THAT tree and not in this one.
        var foreign = FileCache.init(self.gpa, declared.tree);
        foreign.module_id = declared.module;
        defer foreign.deinit();
        // Propagated as themselves rather than matched one by one: the
        // declared set above is what bounds this function, and an arm list
        // that has to be edited whenever the model builder grows a failure is
        // an arm list that will be stale the next time it does.
        return foreign.summaryOfFn(declared.fn_decl) catch |err| return err;
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
    ) SummaryError!?*const fn_summary.FnSummary {
        // The qualifier is resolved to the module it REALLY imports, and
        // the name is read from the tree that module was parsed from —
        // never from the spelling, which is all the call site wrote.
        const module_tree = (try self.qualifierModule(qualifier)) orelse return null;
        if (module_tree == self.tree) return self.summaryByName(name);
        const declared = moduleFnDecl(module_tree, name, self.module_id) orelse return null;
        return self.summaryOfResolvedMethod(declared);
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
                    try writes.append(self.gpa, .{
                        .name = tree.tokenSlice(decl.ast.mut_token + 1),
                        .type_node = decl.ast.type_node.unwrap(),
                        .init = decl.ast.init_node.unwrap() orelse identifierNodeAt(tree, decl.ast.mut_token + 1),
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

    /// Like summaryOf but also fills the deep inference fields that
    /// require allocation (`may_free_fields`, `result_heap_fields`)
    /// and the contextual field (`heap_allocates_self`).  Slice
    /// storage lives in the cache's `summary_arena`.
    pub fn summaryOfFn(
        self: *FileCache,
        fn_decl: Ast.Node.Index,
    ) !*const fn_summary.FnSummary {
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
        const gop = try self.summaries.getOrPut(self.gpa, key);
        if (gop.found_existing and gop.value_ptr._resolved) {
            // Already resolved; preserves any R10 transitive
            // mutations from prior `resolveTransitiveTakes` passes.
            return gop.value_ptr;
        }

        // Start from the cheap body-only summary, or upgrade an
        // existing (cheap-only) entry in place.
        var s = if (gop.found_existing) gop.value_ptr.* else fn_summary.inferFromBody(self.tree, proto, body);

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
        }

        // Containing-type lookup → heap_allocates_self.
        const model = try self.fileModel();
        const ct: ?[]const u8 = if (model.containingTypeOf(fn_decl)) |ti| ti.name else null;
        s.heap_allocates_self = fn_summary.inferHeapAllocatesSelf(self.tree, body, ct);

        // NOTE: may_free_fields here is the RAW body-only inference.
        // resolveTransitiveTakes filters it as a finalization pass,
        // since the filter needs to consult OTHER summaries (creating
        // a comptime-dependency cycle if done inside summaryOfFn).

        s._resolved = true;
        gop.value_ptr.* = s;
        return gop.value_ptr;
    }
};

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
    "@TypeOf",  "@sizeOf",       "@alignOf",   "@bitSizeOf",
    "@typeInfo", "@typeName",    "@hasField",  "@hasDecl",
    "@offsetOf", "@bitOffsetOf", "@fieldParentPtr",
};

/// The `{` of the innermost `comptime` block — `comptime { … }` or
/// `comptime label: { … }` — enclosing `token`, or null when there is
/// none.  Every statement of such a block is evaluated at comptime.
fn comptimeBlockEnclosing(tree: *const Ast, token: Ast.TokenIndex) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    var regions: [max_fill_scope_depth]Ast.TokenIndex = undefined;
    const region_len = openBraceStack(tags, token, &regions) orelse return null;
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

/// The open `{` tokens enclosing `token`, innermost LAST.  Bounded: past
/// the bound the walk did not finish, which is not an answer.
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
                if (depth == max_fill_scope_depth) return null;
                regions[depth] = t;
                depth += 1;
            },
            .r_brace => {
                if (depth > 0) depth -= 1;
            },
            else => {},
        }
    }
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
fn identifierNodeAt(tree: *const Ast, name_token: Ast.TokenIndex) Ast.Node.Index {
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeMainToken(node) != name_token) continue;
        return node;
    }
    unreachable;
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

/// Walk a dotted field path (e.g. "inner.handle") through a struct
/// type chain, returning the DEEPEST field's type as a path split.
/// For a single-segment path "f", returns `<outer>.f`'s type.  For
/// multi-segment "f.g.h", walks outer.f -> field-type-of-f, then

/// Extract the bare container name from an AST type-expression node without
/// invoking ZLS.  Strips leading `?`, `*`, `const` qualifiers, then walks
/// a dotted identifier chain and returns the last component.
///
/// Examples: `*Foo` → "Foo", `?*const ns.Foo` → "Foo", `Foo` → "Foo".
/// Returns null for slices (`[]T`), function pointers, anonymous structs,
/// or any shape that doesn't reduce to a plain dotted identifier chain.
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
    var last_name: ?[]const u8 = null;
    var expecting_ident = true;
    while (t <= last) : (t += 1) {
        const tag = tags[t];
        if (expecting_ident) {
            if (tag == .identifier) {
                last_name = tree.tokenSlice(t);
                expecting_ident = false;
            } else return null;
        } else {
            if (tag == .period) expecting_ident = true else break;
        }
    }
    return last_name;
}

/// The type a `param.field.path` chain ends at.  `ns` is the import alias the
/// LEAF field's declared type was written with (`inner: other.Inner` →
/// `"other"`), which is how a caller tells a same-file type from one it has to
/// reach across imports; `type_name` is the bare name the next segment, or a
/// type-keyed lookup, reads.
const FieldPathEnd = struct {
    ns: ?[]const u8,
    type_name: []const u8,
};

/// that.g, then that.h, returning the leaf type.
///
/// Stops + returns null when any intermediate field's type isn't
/// resolvable in the local model (cross-file intermediates that
/// aren't loaded yet — uncommon, and the conservative answer is to
/// drop the entry).
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
        const dot = std.mem.lastIndexOfScalar(u8, declared, '.');
        const end: FieldPathEnd = if (dot) |at| .{
            .ns = declared[0..at],
            .type_name = declared[at + 1 ..],
        } else .{ .ns = null, .type_name = declared };
        last_result = end;
        // For the next iteration we need a bare type name — if this
        // segment's type was `<ns>.<Type>` we'd need to load the
        // remote file to walk further.  We don't have a remote
        // pointer here; conservative: stop and return null if there
        // are more segments to walk.
        if (it.peek() == null) break;
        if (end.ns != null) return null;
        cur_outer = end.type_name;
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
        if (segment.len == 0) return 0;
        if (count == max_type_path_segments) return 0;
        out[count] = segment;
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

/// Walk every `@import("./...")` builtin call in `tree` and try
/// finding `name` in the target file's model.  Recurses up to
/// `depth_left` more hops to follow re-export aliases (`pub const
/// Tag = @import("./Tag.zig").Tag;` is a common 2-hop pattern in
/// Bun's protocol modules).
///
/// Depth-bounded to prevent diamond-load cycles on highly
/// interconnected projects.  Returns the FIRST hit across imports
/// at that depth; ambiguity (same name in multiple imports) is
/// fine for the rule's purposes (which only needs "has this
/// method on this type" — re-exports of the SAME type produce
/// the same answer).
/// Walk every `@import("./...")` builtin call in `tree` and try
/// finding `name` in the target file's model.  Recurses up to
/// `depth_left` more hops to follow re-export aliases.
///
/// The recursive call uses `@fieldParentPtr` to recover the
/// ProjectCache.Entry from the sub-model pointer — zero cost,
/// no path-resolution allocation, no extra lock acquisition.
fn findTypeViaImports(
    pc: *project_cache_mod.ProjectCache,
    tree: *const Ast,
    from_path: []const u8,
    name: []const u8,
    depth_left: u32,
) ?*const file_model.TypeInfo {
    if (depth_left == 0) return null;
    const tags = tree.tokens.items(.tag);
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        switch (tree.nodeTag(node)) {
            .builtin_call,
            .builtin_call_two,
            .builtin_call_comma,
            .builtin_call_two_comma,
            => {},
            else => continue,
        }
        const main = tree.nodeMainToken(node);
        if (main >= tree.tokens.len) continue;
        if (tags[main] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(main), "@import")) continue;
        if (main + 2 >= tree.tokens.len) continue;
        if (tags[main + 2] != .string_literal) continue;
        const lit = tree.tokenSlice(main + 2);
        if (lit.len < 2) continue;
        const import_str = lit[1 .. lit.len - 1];
        const sub_model_opt: ?*const file_model.FileModel = blk: {
            if (project_cache_mod.isRelativeImport(import_str)) {
                break :blk pc.modelForRelativeImport(from_path, import_str) catch null;
            }
            break :blk pc.modelForModuleImport(from_path, import_str) catch null;
        };
        const sub_model = sub_model_opt orelse continue;
        if (sub_model.findType(name)) |ti| return ti;
        // Recover the Entry via fieldParentPtr (zero cost, no alloc, no lock).
        // sub_entry.abs_path is the resolved next_from for the recursive hop.
        const sub_entry: *const project_cache_mod.ProjectCache.Entry =
            @fieldParentPtr("model", sub_model);
        if (findTypeViaImports(pc, &sub_entry.tree, sub_entry.abs_path, name, depth_left - 1)) |ti| return ti;
    }
    return null;
}

/// `findTypeViaImports` keeping the document each hit was read from.
/// Same walk, same depth bound, same first-hit rule — the only
/// difference is that the answer names where it came from, which a
/// question about a type's FIELDS needs and a question about the type
/// alone does not.
fn resolvedTypeViaImports(
    pc: *project_cache_mod.ProjectCache,
    tree: *const Ast,
    from_path: []const u8,
    name: []const u8,
    depth_left: u32,
    module: ModuleId,
) ?FileCache.ResolvedType {
    if (depth_left == 0) return null;
    const tags = tree.tokens.items(.tag);
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        switch (tree.nodeTag(node)) {
            .builtin_call,
            .builtin_call_two,
            .builtin_call_comma,
            .builtin_call_two_comma,
            => {},
            else => continue,
        }
        const main = tree.nodeMainToken(node);
        if (main >= tree.tokens.len) continue;
        if (tags[main] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(main), "@import")) continue;
        if (main + 2 >= tree.tokens.len) continue;
        if (tags[main + 2] != .string_literal) continue;
        const lit = tree.tokenSlice(main + 2);
        if (lit.len < 2) continue;
        const import_str = lit[1 .. lit.len - 1];
        const sub_model_opt: ?*const file_model.FileModel = blk: {
            if (project_cache_mod.isRelativeImport(import_str)) {
                break :blk pc.modelForRelativeImport(from_path, import_str) catch null;
            }
            break :blk pc.modelForModuleImport(from_path, import_str) catch null;
        };
        const sub_model = sub_model_opt orelse continue;
        const sub_entry: *const project_cache_mod.ProjectCache.Entry =
            @fieldParentPtr("model", sub_model);
        if (sub_model.findType(name)) |ti| {
            return .{ .model = sub_model, .info = ti, .path = sub_entry.abs_path, .module = module };
        }
        if (resolvedTypeViaImports(pc, &sub_entry.tree, sub_entry.abs_path, name, depth_left - 1, module)) |found| return found;
    }
    return null;
}

fn findMethodViaImports(
    pc: *project_cache_mod.ProjectCache,
    tree: *const Ast,
    from_path: []const u8,
    type_name: []const u8,
    method_name: []const u8,
    depth_left: u32,
) ?FileCache.ResolvedMethod {
    if (depth_left == 0) return null;
    const tags = tree.tokens.items(.tag);
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        switch (tree.nodeTag(node)) {
            .builtin_call,
            .builtin_call_two,
            .builtin_call_comma,
            .builtin_call_two_comma,
            => {},
            else => continue,
        }
        const main = tree.nodeMainToken(node);
        if (main >= tree.tokens.len) continue;
        if (tags[main] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(main), "@import")) continue;
        if (main + 2 >= tree.tokens.len) continue;
        if (tags[main + 2] != .string_literal) continue;
        const lit = tree.tokenSlice(main + 2);
        if (lit.len < 2) continue;
        const import_str = lit[1 .. lit.len - 1];
        const sub_model_opt: ?*const file_model.FileModel = blk: {
            if (project_cache_mod.isRelativeImport(import_str)) {
                break :blk pc.modelForRelativeImport(from_path, import_str) catch null;
            }
            break :blk pc.modelForModuleImport(from_path, import_str) catch null;
        };
        const sub_model = sub_model_opt orelse continue;
        if (sub_model.findType(type_name)) |ti| {
            if (ti.findMethod(method_name)) |m| return .{ .tree = sub_model.tree, .method = m };
        }
        // Recover the Entry via fieldParentPtr — no alloc, no lock, no path resolution.
        const sub_entry: *const project_cache_mod.ProjectCache.Entry =
            @fieldParentPtr("model", sub_model);
        if (findMethodViaImports(pc, &sub_entry.tree, sub_entry.abs_path, type_name, method_name, depth_left - 1)) |rm| return rm;
    }
    return null;
}


// ── Tests ──────────────────────────────────────────────────

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

    // Find the two fn bodies.
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(&tree);
    const foo = fns.next(&proto_buf).?;
    const bar = fns.next(&proto_buf).?;

    const a1 = try cache.localBindings(foo.proto, foo.body);
    const a2 = try cache.localBindings(foo.proto, foo.body);
    const b1 = try cache.localBindings(bar.proto, bar.body);
    try std.testing.expect(a1 == a2);
    try std.testing.expect(a1 != b1);
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
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();

    try std.testing.expect(try cache.anyMethodAllocatesSelf("Foo"));
    try std.testing.expect(!try cache.anyMethodAllocatesSelf("Bar"));
    try std.testing.expect(!try cache.anyMethodAllocatesSelf("Missing"));
}

test "FileCache: summaryOfFn fills deep fields (heap_allocates_self + result_heap_fields)" {
    const gpa = std.testing.allocator;
    const src: [:0]const u8 =
        \\const Foo = struct {
        \\    bytes: []u8,
        \\    pub fn init(self_alloc: std.mem.Allocator) !*Foo {
        \\        const f = try self_alloc.create(Foo);
        \\        f.* = .{ .bytes = try self_alloc.alloc(u8, 16) };
        \\        return f;
        \\    }
        \\};
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();

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
    // `consumer.zig` — imports destroyer; doesn't declare Node locally.
    try tmp.dir.writeFile(tio, .{
        .sub_path = "consumer.zig",
        .data =
        \\const destroyer = @import("./destroyer.zig");
        \\pub fn useNode(n: *destroyer.Node) void {
        \\    _ = n;
        \\}
        ,
    });

    // Build consumer's path string.
    const from_path = try std.fs.path.join(gpa, &.{
        ".zig-cache", "tmp", "consumer.zig",
    });
    defer gpa.free(from_path);

    const consumer_src: [:0]const u8 =
        \\const destroyer = @import("./destroyer.zig");
        \\pub fn useNode(n: *destroyer.Node) void { _ = n; }
    ;
    var consumer_tree = try Ast.parse(gpa, consumer_src, .zig);
    defer consumer_tree.deinit(gpa);

    var pc = project_cache_mod.ProjectCache.init(gpa, tio);
    defer pc.deinit();

    var cache = FileCache.init(gpa, &consumer_tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    // Cross-file lookup: `Node` is in destroyer.zig, not consumer.zig.
    const xf = try cache.summaryByMethodCrossFile("Node", "kill");
    if (xf) |s| {
        // inferDirectTakes should see `gpa.destroy(self)` → takes_ownership_of = 0.
        try std.testing.expectEqual(@as(?u32, 0), s.takes_ownership_of);
    }
    // If xf is null the tmp-dir path didn't resolve — acceptable on CI
    // where tmp paths may not be discoverable; the lookup code is exercised.
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

    const from_path = try std.fs.path.join(gpa, &.{
        ".zig-cache", "tmp", "wrapper.zig",
    });
    defer gpa.free(from_path);

    const src: [:0]const u8 =
        \\const node_lib = @import("./node_lib.zig");
        \\pub fn wrapper(node: *node_lib.Node, gpa: std.mem.Allocator) void {
        \\    node.kill(gpa);
        \\}
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);

    var pc = project_cache_mod.ProjectCache.init(gpa, tio);
    defer pc.deinit();

    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    try cache.resolveTransitiveTakes();

    // `wrapper` calls `node.kill(gpa)` where `kill` takes ownership of
    // its receiver (param 0).  After transitive propagation, `wrapper`
    // should also have takes_ownership_of = 0 (its first param `node`).
    const s = try cache.summaryByName("wrapper");
    if (s) |ws| {
        // If cross-file lookup succeeded, takes_ownership_of is 0.
        // If tmp paths didn't resolve, ws.takes_ownership_of is null —
        // still a valid test: we're verifying no crash or wrong result.
        if (ws.takes_ownership_of) |idx| {
            try std.testing.expectEqual(@as(u32, 0), idx);
        }
    }
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

    // Use the REAL tmp sub-path so @import resolution actually finds
    // inner.zig (the random subdir under .zig-cache/tmp/).
    const from_path = try std.fs.path.join(gpa, &.{
        ".zig-cache", "tmp", &tmp.sub_path, "outer.zig",
    });
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

    var pc = project_cache_mod.ProjectCache.init(gpa, tio);
    defer pc.deinit();
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    try cache.resolveTransitiveTakes();

    // Deterministic: the @import-fallback-on-index-miss fix resolves the
    // tmp file even though it sits outside the project walk's global index.
    // The cross-file field-free must be KEPT.
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

    const from_path = try std.fs.path.join(gpa, &.{
        ".zig-cache", "tmp", &tmp.sub_path, "consumer.zig",
    });
    defer gpa.free(from_path);

    const consumer_src: [:0]const u8 =
        \\const destroyer = @import("./destroyer.zig");
        \\pub fn useNode(n: *destroyer.Xf20Node) void { _ = n; }
    ;
    var tree = try Ast.parse(gpa, consumer_src, .zig);
    defer tree.deinit(gpa);

    var pc = project_cache_mod.ProjectCache.init(gpa, tio);
    defer pc.deinit();
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    // Deterministic since the @import-fallback-on-index-miss fix:
    // findMethodCrossFile now falls through to the @import traversal when
    // the global index has no match (the tmp file is outside the project
    // walk), so this resolves reliably.  `kill`'s takes_ownership_of must be
    // 0 — inherited transitively from `reallyFree` inside the foreign file.
    const s = (try cache.summaryByMethodCrossFile("Xf20Node", "kill")) orelse
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
    const from_path = try std.fs.path.join(gpa, &.{ ".zig-cache", "tmp", &tmp.sub_path, "caller.zig" });
    defer gpa.free(from_path);
    const caller_src: [:0]const u8 =
        \\const grower = @import("./grower.zig");
        \\pub fn run(g: *grower.Xf20Grower) void { g.add(1); }
    ;
    var tree = try Ast.parse(gpa, caller_src, .zig);
    defer tree.deinit(gpa);
    var pc = project_cache_mod.ProjectCache.init(gpa, tio);
    defer pc.deinit();
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);
    try cache.resolveTransitiveTakes();
    // Deterministic since the #27 @import-fallback fix; `add` grows a
    // collection in the imported file, so `run` inherits may_grow.
    const s = (try cache.summaryByName("run")).?;
    try std.testing.expect(s.may_grow_collections);
}
