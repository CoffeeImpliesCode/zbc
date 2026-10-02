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
const zls_resolver_mod = @import("../type_resolver.zig");
const project_cache_mod = @import("project_cache.zig");
const cfg_builder_mod = @import("../flow/cfg_builder.zig");
const budget_mod = @import("../budget.zig");

/// A declaration, addressed by the document that declares it and the
/// node inside it.  A tree pointer is the store's stable identity for a
/// document, so the pair names one declaration for as long as that
/// document is loaded — which is what lets a verdict computed for a
/// declaration in another file be cached and compared at all.
const DeclKey = struct { tree: *const Ast, declaration: Ast.Node.Index };

/// What opening a document's own analysis can fail at.  `SourceTooWide`
/// is the file's own limit — a document whose source exceeds the offsets
/// `std.zig.Ast` addresses it with cannot be analysed here either, and
/// saying so beats reading part of a file.
const OpenError = error{ OutOfMemory, SourceTooWide };

/// Where a declaration's reallocations land: the parameter-rooted paths
/// it can grow, and whether one of them reached storage no parameter of
/// it roots.  An empty `paths` with `unknown` set is the reading that
/// keeps a consumer conservative; the default is exactly that, because a
/// declaration whose analysis has not run cannot say less.
const GrowVerdict = struct {
    paths: []const fn_summary.GrowPath = &.{},
    unknown: bool = true,
};

/// A document this cache reads declarations from: the resolver that
/// types it, and the per-file state that analyses it.  Both are owned
/// until the root cache tears down, so a grow path borrowed from them
/// cannot dangle.  The resolver borrows the store's own handle, which is
/// what keeps the document's imports and toolchain sources resolving the
/// way they do for the file under analysis.
const SourceDocument = struct {
    resolver: *zls_resolver_mod.TypeResolver,
    cache: FileCache,

    /// Release what this document borrowed and built.  The
    /// `SourceDocument` itself belongs to whoever opened it.
    fn deinit(self: *SourceDocument) void {
        self.cache.deinit();
        self.resolver.deinit();
    }
};

/// The grow-analysis state one root cache shares with every source
/// document it opens.  Sharing it is what lets a cycle that crosses
/// documents be recognised: each end asks the same set what is being
/// computed right now, instead of opening a second analysis of a file
/// that is already on the stack.
const GrowState = struct {
    /// The root cache, which alone tears this down.
    owner: *FileCache,
    /// One per document, keyed by that document's own tree.
    documents: std.AutoHashMapUnmanaged(*const Ast, *SourceDocument) = .empty,
    /// Verdicts already computed, keyed by the declaration they answer.
    verdicts: std.AutoHashMapUnmanaged(DeclKey, GrowVerdict) = .empty,
    /// Declarations being computed right now.  Meeting one again is a
    /// cycle, and a cycle is charged by the caller — never read as a
    /// declaration that grows nothing.
    active: std.AutoHashMapUnmanaged(DeclKey, void) = .empty,

    fn deinit(self: *GrowState, gpa: std.mem.Allocator) void {
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

pub const FileCache = struct {
    gpa: std.mem.Allocator,
    tree: *const Ast,
    /// Arena for FnSummary's variable-length fields
    /// (may_free_fields, result_heap_fields, grow_paths).  Lazy: only
    /// initialized on first summaryOf call that needs it.
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
    /// Lazily-built sorted table of byte offsets where each source line
    /// starts.  Shared across all function analyses in this file so
    /// cfg_builder's buildLineOffsets() runs at most once per file.
    line_offsets: []const u32 = &.{},
    address_uses: ?AddressUseMap = null,
    /// Canonical direct grow effects, one entry per body.
    /// `inferGrowEffects` reads only the immutable AST, the proto, the
    /// body and the bindings — never a callee's summary — so every
    /// fixed-point round would otherwise re-walk the same body and
    /// re-allocate the same paths, calls and claims in the arena, 64
    /// times over for a source document's on-demand fold.  The slices
    /// are owned by `summary_arena`; the map holds only the views.
    direct_effects: std.AutoHashMapUnmanaged(u32, fn_summary.GrowEffects) = .empty,
    call_index: ?CallIndex = null,
    closed_callers: std.AutoHashMapUnmanaged(Ast.Node.Index, ?[]const Ast.Node.Index) = .empty,
    max_float_bits: std.AutoHashMapUnmanaged(Ast.TokenIndex, u16) = .empty,

    /// Verdicts of `provesFreshStorage`, keyed by the initializer's
    /// token range.  Phase 8 re-walks each fn until its paths settle,
    /// and asks the same initializer again on every pass.
    fresh_storage: std.AutoHashMapUnmanaged(u64, bool) = .empty,
    /// Constructor declarations whose returns are being read right
    /// now, so a constructor that reaches itself stops the walk
    /// instead of recursing forever.
    fresh_visiting: std.AutoHashMapUnmanaged(DeclKey, void) = .empty,
    /// The standard library's own list declarations, which live
    /// outside the project policy: they are read as DECLARATIONS, from
    /// the same document store the type engine resolves
    /// `@import("std")` through, and never from the names a file
    /// happens to spell.
    std_list_tree: StdListTree = .unknown,
    /// Grow analysis of declarations in OTHER documents — the callee a
    /// call actually reaches, read where it is declared.  One state per
    /// root cache, shared with every source document it opens so a
    /// cycle crossing documents is seen at both ends, and owned until
    /// deinit so no borrowed grow path outlives its source.
    grow_state: ?*GrowState = null,
    /// Set on a SOURCE document's own cache: nothing is iterating its
    /// Phase 8, so a callee it reaches is resolved on demand instead of
    /// read from a fixed point no one is driving.
    grow_on_demand: bool = false,
    /// What each call's callee expression actually names, resolved
    /// once per token.  A declaration is a property of the source
    /// snapshot, not of the pass folding it, so Phase 8's rounds do
    /// not re-type a call they already routed.
    actual_callees: std.AutoHashMapUnmanaged(Ast.TokenIndex, ?ActualCallee) = .empty,

    const CallIndex = struct {
        by_callee_token: std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index) = .empty,
        reflective: bool = false,
    };

    /// The declaration a call's callee expression reaches, checked
    /// against the document that declares it.  Null when the type
    /// engine cannot name it, or when the token is not the `fn`
    /// keyword of the declaration it points at.
    const ActualCallee = struct {
        /// The call node the callee token belongs to, so the caller
        /// does not look the same token up twice.
        call_node: Ast.Node.Index,
        tree: *const Ast,
        fn_token: Ast.TokenIndex,
        handle: *@import("type_engine").DocumentStore.Handle,
        declaration: Ast.Node.Index,
    };

    /// `unknown` until this session has looked for the toolchain's own
    /// `std/array_list.zig`, `known` once the document it read is
    /// carried here, `absent` when this session has no toolchain to
    /// read at all.  The `known` arm carries that document, so this is
    /// a tagged union and not a plain enum.
    const StdListTree = union(enum) { unknown, absent, known: *const Ast };

    /// A token range in one source snapshot, as the fresh-storage
    /// resolver passes them around.
    pub const TokenRange = fn_summary.TokenRange;

    /// All direct callers of a private, non-escaping declaration. Null is open or unknown.
    pub fn closedLocalCalls(self: *FileCache, declaration: Ast.Node.Index) error{OutOfMemory}!?[]const Ast.Node.Index {
        if (self.closed_callers.get(declaration)) |cached| return cached;
        const calls = try self.buildClosedLocalCalls(declaration);
        errdefer if (calls) |owned| self.gpa.free(owned);
        try self.closed_callers.put(self.gpa, declaration, calls);
        return calls;
    }

    fn getCallIndex(self: *FileCache) error{OutOfMemory}!*const CallIndex {
        if (self.call_index) |*index| return index;
        var index: CallIndex = .{};
        errdefer index.by_callee_token.deinit(self.gpa);
        for (self.tree.nodes.items(.tag), 0..) |tag, raw_node| {
            const node: Ast.Node.Index = @enumFromInt(raw_node);
            var buffer: [1]Ast.Node.Index = undefined;
            if (self.tree.fullCall(&buffer, node)) |call| {
                try index.by_callee_token.put(self.gpa, self.tree.lastToken(call.ast.fn_expr), node);
            }
            switch (tag) {
                .@"asm", .asm_simple => index.reflective = true,
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    if (std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(node)), "@field"))
                        index.reflective = true;
                },
                else => {},
            }
        }
        self.call_index = index;
        return &self.call_index.?;
    }

    fn isStandardSliceComparison(self: *FileCache, callee_token: Ast.TokenIndex) error{OutOfMemory}!bool {
        const resolver = self.zls orelse return false;
        const index = try self.getCallIndex();
        const node = index.by_callee_token.get(callee_token) orelse return false;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = self.tree.fullCall(&buffer, node) orelse return false;
        return resolver.stdMemEqlOf(call.ast.fn_expr, call.ast.params.len) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => false,
        };
    }

    fn buildClosedLocalCalls(self: *FileCache, declaration: Ast.Node.Index) error{OutOfMemory}!?[]const Ast.Node.Index {
        const resolver = self.zls orelse return null;
        const tree = self.tree;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
        if (proto.visib_token != null) return null;
        if (proto.extern_export_inline_token) |token| {
            if (tree.tokenTag(token) != .keyword_inline) return null;
        }
        const name = tree.tokenSlice(proto.name_token orelse return null);
        const index = try self.getCallIndex();
        if (index.reflective) return null;
        var calls: std.ArrayList(Ast.Node.Index) = .empty;
        defer calls.deinit(self.gpa);
        for (tree.nodes.items(.tag), 0..) |tag, raw_node| {
            const node: Ast.Node.Index = @enumFromInt(raw_node);
            const token = switch (tag) {
                .identifier => tree.nodeMainToken(node),
                .field_access => tree.nodeData(node).node_and_token[1],
                else => continue,
            };
            const spelling = tree.tokenSlice(token);
            // Quoted aliases must be resolved, not excluded by raw spelling.
            if (!std.mem.eql(u8, spelling, name) and spelling[0] != '@' and name[0] != '@') continue;
            const reference = (resolver.functionReference(node) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => return null,
            }) orelse return null;
            if (reference.tree != tree or reference.fn_token != proto.ast.fn_token) continue;
            const call = index.by_callee_token.get(token) orelse return null;
            try calls.append(self.gpa, call);
        }
        if (calls.items.len == 0) return null;
        return try calls.toOwnedSlice(self.gpa);
    }

    /// Maximum precision across closed generic instantiations, not an arithmetic format.
    pub fn maxFloatBitsOf(self: *FileCache, node: Ast.Node.Index, budget: *u32) ?u16 {
        return self.maxFloatBitsAtDepth(node, budget, 0);
    }

    fn maxFloatBitsAtDepth(self: *FileCache, node: Ast.Node.Index, budget: *u32, depth: u8) ?u16 {
        if (depth == 8 or budget.* == 0) return null;
        budget.* -= 1;
        const resolver = self.zls orelse return null;
        if (resolver.floatBits(node) catch null) |bits| return if (bits == 0) null else bits;
        const reference = (resolver.typeParameterReference(node) catch return null) orelse return null;
        if (reference.tree != self.tree) return null;
        if (self.max_float_bits.get(reference.token)) |bits| return bits;
        const declaration = tokens.enclosingFnDecl(self.tree, reference.token) orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &buffer, declaration) orelse return null;
        var parameters = proto.iterate(self.tree);
        var parameter_index: usize = 0;
        var found = false;
        while (parameters.next()) |parameter| {
            if (parameter.name_token == reference.token) {
                found = true;
                break;
            }
            parameter_index += 1;
        }
        if (!found) return null;
        const calls = (self.closedLocalCalls(declaration) catch return null) orelse return null;
        var maximum: u16 = 0;
        for (calls) |call| {
            const argument = (resolver.callArgument(call, parameter_index) catch return null) orelse return null;
            const bits = self.maxFloatBitsAtDepth(argument, budget, depth + 1) orelse return null;
            maximum = @max(maximum, bits);
        }
        if (maximum == 0) return null;
        self.max_float_bits.put(self.gpa, reference.token, maximum) catch return null;
        return maximum;
    }

    pub const AddressUse = struct { may_write: bool };
    const AddressUseMap = std.AutoHashMapUnmanaged(Ast.TokenIndex, AddressUse);

    /// Address operands, indexed once per file. Ordinary calls and memory
    /// builtins may write through arguments; taking an address does not write.
    pub fn addressUseAt(self: *FileCache, operand_token: Ast.TokenIndex) !?AddressUse {
        if (self.address_uses == null) self.address_uses = try self.buildAddressUses();
        return self.address_uses.?.get(operand_token);
    }

    /// Nesting depth of the whole-file address-use walk.  Bounded because
    /// the walk keeps one frame per AST level; named so the check and the
    /// reported diagnostic cannot drift apart.
    const max_address_use_frames = 256;

    fn buildAddressUses(self: *FileCache) !AddressUseMap {
        const Iterator = @import("type_engine").AstIterator;
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
        frames[0] = .{
            .children = .{ .array = .{ Ast.Node.Index.root.toOptional(), .none, .none, .none, .none } },
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
            const in_argument = frame.in_argument or (frame.call_children and !frame.first_child);
            frame.first_child = false;
            const tag = self.tree.nodeTag(node);
            if (tag == .address_of) {
                if (tokens.rootIdentifier(self.tree, self.tree.nodeData(node).node)) |operand| {
                    try result.put(self.gpa, self.tree.nodeMainToken(operand), .{ .may_write = in_argument });
                }
            }
            if (depth == frames.len) {
                return self.addressUseFailure(.address_use_depth, @intCast(frames.len), @intCast(depth), node);
            }
            frames[depth] = .{
                .children = Iterator.init(self.tree, node),
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

    /// zbc addresses everything it reports in `u32` bytes.  `std.zig.Ast`
    /// already works that way — every token start is a `u32` offset, and
    /// so is `source.len`, carried as the end-of-file token's start — and
    /// a reported line or column is a token's byte offset plus one, so a
    /// source shorter than `maxInt(u32)` bytes is what makes a position
    /// representable at all.  A wider one is the single input the whole
    /// position model cannot describe, so it is rejected here: this is
    /// the one construction point every analysis path passes through
    /// before any position is built, and rejecting it once means no
    /// later position has to re-check the bound or invent one.
    pub fn init(gpa: std.mem.Allocator, tree: *const Ast) error{SourceTooWide}!FileCache {
        if (tree.source.len >= std.math.maxInt(u32)) return error.SourceTooWide;
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

    /// True for floating-point types; null if type resolution is unavailable.
    pub fn isFloatType(self: *FileCache, node: std.zig.Ast.Node.Index) ?bool {
        const z = self.zls orelse return null;
        return z.isFloatType(node) catch null;
    }

    /// What `callee`, called with `arguments` written arguments, resolves to:
    /// std's single-element append, or `.no`.  Null only when the type engine
    /// is unavailable — a caller must then record nothing, never guess.
    pub fn stdCollectionAppendOf(
        self: *FileCache,
        callee: std.zig.Ast.Node.Index,
        arguments: usize,
    ) ?zls_resolver_mod.TypeResolver.StdCollectionAppend {
        const z = self.zls orelse return null;
        return z.stdCollectionAppendOf(callee, arguments) catch null;
    }

    /// Resolve the actual call spanning these tokens, including its written
    /// argument count. Unresolved declarations cannot prove a private append.
    pub fn stdCollectionAppendOfExpr(
        self: *FileCache,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) ?zls_resolver_mod.TypeResolver.StdCollectionAppend {
        if (self.zls == null) return null;
        const node = self.nodeForExactSpan(first, last) orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = self.tree.fullCall(&buffer, node) orelse return null;
        return self.stdCollectionAppendOf(call.ast.fn_expr, call.ast.params.len);
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

    pub fn setProject(
        self: *FileCache,
        project: ?*project_cache_mod.ProjectCache,
        file_path: []const u8,
    ) void {
        self.project = project;
        self.file_path = file_path;
    }

    pub const ResolvedType = struct {
        model: *const file_model.FileModel,
        info: *const file_model.TypeInfo,
    };

    pub fn findTypeAcrossImports(self: *FileCache, name: []const u8) ?ResolvedType {
        const model = self.fileModel() catch return null;
        const resolved = resolveNamed(self.gpa, self.project, model, self.file_path, name, 32) orelse return null;
        return .{ .model = resolved.model, .info = resolved.info orelse return null };
    }

    pub fn fieldType(self: *FileCache, owner: ResolvedType, field_name: []const u8) ?ResolvedType {
        if (owner.model.resolveFieldTypeQualifiedTi(owner.info, field_name)) |info| {
            return .{ .model = owner.model, .info = info };
        }
        const field = owner.info.findField(field_name) orelse return null;
        const name = tokens.typeNameFromTokens(owner.model.tree, field.type_first, field.type_last) orelse return null;
        const path = if (owner.model.tree == self.tree) self.file_path else (self.project orelse return null).pathForModel(owner.model);
        const resolved = resolveNamed(self.gpa, self.project, owner.model, path, name, 32) orelse return null;
        return .{ .model = resolved.model, .info = resolved.info orelse return null };
    }

    pub fn summaryForType(self: *FileCache, owner: ResolvedType, name: []const u8) !?fn_summary.FnSummary {
        const method = owner.info.findMethod(name) orelse return null;
        return self.summaryOfResolvedMethod(.{ .tree = owner.model.tree, .fn_decl = method.fn_decl });
    }

    pub const ResolvedMethod = struct {
        tree: *const Ast,
        fn_decl: Ast.Node.Index,
    };

    pub fn findMethodAcrossImports(self: *FileCache, type_name: []const u8, method_name: []const u8) ?ResolvedMethod {
        const model = self.fileModel() catch return null;
        const key = std.fmt.allocPrint(self.gpa, "{s}\x00{s}", .{ type_name, method_name }) catch return null;
        if (self.method_lookup_cache.get(key)) |cached| {
            self.gpa.free(key);
            return cached;
        }
        const result: ?ResolvedMethod = blk: {
            const resolved = resolveNamed(self.gpa, self.project, model, self.file_path, type_name, 32) orelse break :blk null;
            if (resolved.info) |info| {
                const method = info.findMethod(method_name) orelse break :blk null;
                break :blk .{ .tree = resolved.model.tree, .fn_decl = method.fn_decl };
            }
            const function = resolved.model.findFn(method_name) orelse break :blk null;
            break :blk .{ .tree = resolved.model.tree, .fn_decl = function.fn_decl };
        };
        self.method_lookup_cache.put(self.gpa, key, result) catch self.gpa.free(key);
        return result;
    }

    pub fn deinit(self: *FileCache) void {
        if (self.address_uses) |*uses| uses.deinit(self.gpa);
        if (self.call_index) |*index| index.by_callee_token.deinit(self.gpa);
        var callers = self.closed_callers.valueIterator();
        while (callers.next()) |calls| if (calls.*) |owned| self.gpa.free(owned);
        self.closed_callers.deinit(self.gpa);
        self.max_float_bits.deinit(self.gpa);
        self.fresh_storage.deinit(self.gpa);
        self.fresh_visiting.deinit(self.gpa);
        self.actual_callees.deinit(self.gpa);
        self.direct_effects.deinit(self.gpa);
        // Only the root cache owns the shared grow state; a source
        // document's cache points at the same state and must not tear
        // it down underneath the root that is still using it.
        if (self.grow_state) |state| {
            if (state.owner == self) state.deinit(self.gpa);
        }
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
        proto: ?Ast.full.FnProto,
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
            if (typeNameFromTypeNode(self.tree, type_node)) |name| {
                const model = try self.fileModel();
                if (model.containingTypeAtToken(proto.ast.fn_token)) |owner| {
                    if (std.mem.eql(u8, name, "Self")) return owner.qualified_name;
                    if (model.resolveTypeNameInScope(name, owner)) |resolved| return resolved.qualified_name;
                }
                return name;
            }
            const z = self.zls orelse return null;
            return z.typeReferenceOfNode(type_node) catch null;
        }
        return null;
    }

    /// Resolve each field and its method in the declaring source snapshot.
    fn filterMayFreeFields(
        self: *FileCache,
        arena: std.mem.Allocator,
        proto: Ast.full.FnProto,
        raw: []const fn_summary.FieldFree,
    ) ![]const fn_summary.FieldFree {
        if (raw.len == 0) return &.{};
        var out: std.ArrayListUnmanaged(fn_summary.FieldFree) = .empty;
        fields: for (raw) |field| {
            const param_type = (try self.paramContainerName(proto, field.param)) orelse continue;
            var owner = self.findTypeAcrossImports(param_type) orelse continue;
            var path = std.mem.splitScalar(u8, field.field, '.');
            while (path.next()) |part| {
                owner = self.fieldType(owner, part) orelse continue :fields;
            }
            const summary = (try self.summaryForType(owner, field.method)) orelse continue;
            if (summary.takes_ownership_of != @as(?u32, 0)) continue;
            try out.append(arena, field);
        }
        return out.toOwnedSlice(arena);
    }

    /// Resolve a name in `proto`'s param list to its 0-indexed
    /// position.  Local helper for the R10 transitive pass.
    fn paramIndexFor(tree: *const Ast, proto: Ast.full.FnProto, name: []const u8) ?u32 {
        var idx: u32 = 0;
        var it = proto.iterate(tree);
        while (it.next()) |p| : (idx += 1) {
            const name_tok = p.name_token orelse continue;
            if (std.mem.eql(u8, tree.tokenSlice(name_tok), name)) return idx;
        }
        return null;
    }

    /// The parameter's declared name — the `self`/`this` receiver
    /// fallback needs it when a method's receiver parameter does not
    /// name a container type.
    fn paramNameFor(self: *FileCache, proto: Ast.full.FnProto, idx: u32) ?[]const u8 {
        var i: u32 = 0;
        var it = proto.iterate(self.tree);
        while (it.next()) |p| : (i += 1) {
            if (i != idx) continue;
            const name_tok = p.name_token orelse return null;
            return self.tree.tokenSlice(name_tok);
        }
        return null;
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
                if (try self.propagateTransitiveTakesOne(fi.fn_decl)) changed = true;
            }
            for (model.types) |ti| {
                for (ti.methods) |m| {
                    if (try self.propagateTransitiveTakesOne(m.fn_decl)) changed = true;
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
                        if (try self.propagateEffectOne(m.fn_decl, ti.qualified_name, eff)) changed = true;
                    }
                }
                if (!changed) break;
            }
        }

        // Phase 8: WHICH storage each fn can grow.  Phase 5 answers
        // "can a reallocation happen at all"; this answers "whose
        // buffer moves", so a caller can tell a growing callee that
        // touches only unrelated storage from one that reaches the
        // loop's buffer.  Folded one call-hop at a time to a fixed
        // point, exactly like the boolean effects above.
        // A path set needs one more round than a boolean does: each
        // round folds exactly one call hop, and a chain of N hops
        // settles in N rounds.  A boolean that never changes stops the
        // loop on its own; a path set that is still arriving at the
        // boolean cap gets widened to "may grow anything" by
        // `widenUnconvergedGrowEffects`, which is a far larger lie
        // than running the rounds it needs.
        //
        // The same cap bounds a source document's on-demand folds, so
        // a declaration read from another file settles or widens on the
        // same terms as one read from this one.
        const rounds = max_grow_rounds;
        iters = 0;
        var grow_converged = false;
        while (iters < rounds) : (iters += 1) {
            var changed = false;
            for (model.fns) |fi| {
                if (try self.resolveGrowPathsOne(fi.fn_decl, null)) changed = true;
            }
            for (model.types) |ti| {
                for (ti.methods) |m| {
                    if (try self.resolveGrowPathsOne(m.fn_decl, ti.qualified_name)) changed = true;
                }
            }
            if (!changed) {
                grow_converged = true;
                break;
            }
        }
        // The cap was hit with effects still arriving, so at least one
        // fn's path set is an UNDER-approximation.  An empty set is the
        // most load-bearing answer here — "whatever this callee
        // reallocates, it owns" — so a set that never settled must not
        // be trusted: widen every growing fn to "may also grow storage
        // its paths never recorded" instead of reporting precision this
        // file never reached.
        if (!grow_converged) try self.widenUnconvergedGrowEffects();

        // Phase 9: carry Phase 8's verdicts back up through the coarse
        // grow flags, which ran before it.
        try self.propagateCoarseGrowAgain(model);
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
                const tn: []const u8 = recv_type orelse {
                    // `recv` names no container type, so `helpers.growNames(`
                    // may still be a free function in the module a file-level
                    // declaration names.  A longer chain (`a.b.c(`) is not
                    // one: there the qualifier is a field of something else.
                    if (t >= first + 3 and tags[t - 3] == .period) break :blk false;
                    // Only the growth leg reads across: it is the one
                    // whose precise paths (Phase 8) depend on this
                    // flag, and resolving every qualified call for the
                    // GC and thread flags would widen those for no gain.
                    if (e != .grow) break :blk false;
                    if (try self.summaryByQualifiedName(recv, method)) |qs| break :blk readEffect(&qs, e);
                    break :blk false;
                };
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
    fn directGrowEffects(
        self: *FileCache,
        proto: Ast.full.FnProto,
        body: Ast.Node.Index,
        bindings: *const local_bindings.LocalBindings,
    ) anyerror!fn_summary.GrowEffects {
        const key = @intFromEnum(body);
        if (self.direct_effects.get(key)) |cached| return cached;
        if (self.summary_arena == null) self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        const effects = try fn_summary.inferGrowEffects(
            self.summary_arena.?.allocator(),
            self.tree,
            proto,
            body,
            bindings,
        );
        try self.direct_effects.put(self.gpa, key, effects);
        return effects;
    }

    /// Fill one fn's `grow_paths` / `grows_unknown_path` from its own
    /// body plus every call site's folded effects.  Returns true iff
    /// this changed the stored answer, which is what Phase 8 iterates
    /// on.
    ///
    /// `receiver_type` is the enclosing type of a method, so a
    /// `self.`/`this.` receiver still reaches the type's own methods
    /// when its parameter's type expression names no container.
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
    /// This function, `foldActualGrow`, `growVerdictOf` and
    /// `resolveGrowPathsAt` spell their error set `anyerror`: the fold
    /// is mutually recursive — a declaration's paths come from the
    /// declarations it reaches, and a source document's fold is
    /// entered from one of them — so reading each other's inferred set
    /// is a dependency loop rather than a program.  The same break
    /// `resolveTransitiveTakes` makes, for the same reason.
    fn resolveGrowPathsOne(
        self: *FileCache,
        fn_decl: Ast.Node.Index,
        receiver_type: ?[]const u8,
    ) anyerror!bool {
        var pbuf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &pbuf, fn_decl) orelse return false;
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return false;
        const bindings = try self.localBindings(proto, body);
        if (self.summary_arena == null) {
            self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        }
        const arena = self.summary_arena.?.allocator();

        const direct = try self.directGrowEffects(proto, body, bindings);
        var paths: std.ArrayListUnmanaged(fn_summary.GrowPath) = .empty;
        for (direct.paths) |gp| try appendGrowPath(arena, &paths, gp);
        var unknown = direct.unknown;
        for (direct.claims) |claim| {
            // A claim the declarations cannot vouch for is storage
            // somebody else may still be walking.
            if (!try self.provesFreshStorage(claim)) unknown = true;
        }

        for (direct.calls) |call| {
            if (try self.isStandardSliceComparison(call.callee_token)) continue;
            // The declaration this call actually reaches, in the
            // document that declares it.  A name alone cannot say
            // which one that is: an alias reaches it, a same-named
            // declaration elsewhere does not, and a receiver this file
            // never declared may still be one.
            if (try self.foldActualGrow(proto, body, call, arena, &paths, &unknown)) continue;
            // A real call whose callee the type engine could not
            // connect to any declaration.  The invocation still
            // happens; only its identity is unreadable.
            const opaque = self.zls != null and self.isUnnamedCall(call.callee_token);
            const charged = paths.items.len;
            // Every summary lookup may insert into `self.summaries`
            // and invalidate earlier pointers, so each callee is read
            // before the next lookup happens.
            switch (call.kind) {
            case .bare: {
                if (try self.summaryByName(call.name)) |cs| {
                    if (cs.grows_unknown_path) unknown = true;
                    try foldGrowPaths(arena, &paths, call, cs.grow_paths, &unknown);
                } else {
                    // Unresolved, so nothing is known about what
                    // it does — but it can only reallocate what
                    // the call handed it, and that is exactly the
                    // path each argument was rooted at.
                    try self.chargeHandedStorage(proto, arena, &paths, &unknown, call, true);
                }
            },
            case .qualified: {
                if (self.qualifierModule(call.qualifier)) |module| {
                    if (try self.summaryOfModuleFn(module, call.name)) |cs| {
                        if (cs.grows_unknown_path) unknown = true;
                        try foldGrowPaths(arena, &paths, call, cs.grow_paths, &unknown);
                        break;
                    }
                    // The module is readable but the function in
                    // it is not: the same blind spot as a bare call.
                    try self.chargeHandedStorage(proto, arena, &paths, &unknown, call, true);
                    break;
                }
                // No readable module — no project, a qualifier that
                // is not an `@import` declaration, a module this
                // project cannot reach, or an import that failed
                // (whose failure the session reports, so it is
                // never a clean bill of health here).  Nothing is
                // known about the callee, but it was handed
                // storage this fn holds, and that storage may be
                // the one somebody is walking.
                try self.chargeHandedStorage(proto, arena, &paths, &unknown, call, false);
            },
            case .method: {
                // `argOwners` always prepends the receiver, but a
                // malformed call must not index past the end.
                if (call.args.len == 0) break;
                const owner: fn_summary.ParamPath = switch (call.args[0]) {
                    .unknown => break,
                    .param => |p| p,
                };
                const type_name: ?[]const u8 = blk: {
                    if (try self.receiverTypeName(proto, owner)) |name| break :blk name;
                    if (owner.path.len == 0) {
                        if (self.paramNameFor(proto, owner.param)) |pname| {
                            if (std.mem.eql(u8, pname, "self") or std.mem.eql(u8, pname, "this")) {
                                break :blk receiver_type;
                            }
                        }
                    }
                    break :blk null;
                };
                if (type_name) |tn| {
                    if (try self.summaryByMethod(tn, call.name)) |cs| {
                        if (cs.grows_unknown_path) unknown = true;
                        try foldGrowPaths(arena, &paths, call, cs.grow_paths, &unknown);
                        break;
                    }
                    if (try self.summaryByMethodCrossFile(tn, call.name)) |cs| {
                        // Cross-file summaries expose only the coarse
                        // flags (the project cache cannot carry the
                        // paths), so they stay conservative.
                        if (cs.grows_unknown_path) unknown = true;
                        try foldGrowPaths(arena, &paths, call, cs.grow_paths, &unknown);
                        break;
                    }
                }
                // Not resolved: the receiver type or the method is
                // out of this file's reach.  A grow-vocabulary
                // method never reaches here — it is attributed by
                // `inferGrowEffects`'s grow-site pass — but any
                // other name can still reallocate what the call
                // hands it, and only that.  The coarse flag
                // agrees: Phase 9 re-propagates it from here.
                try self.chargeHandedStorage(proto, arena, &paths, &unknown, call, false);
            },
            case .unresolved: {
                // A method on a receiver this fn was NOT
                // handed and cannot root on a
                // parameter.  Its name is a method name and must not be dispatched
                // to a file-level declaration that shares it, so
                // all that is left is what the call hands over.
                try self.chargeHandedStorage(proto, arena, &paths, &unknown, call, false);
            },
            }
            // An opaque callee that was handed nothing of this fn's is
            // not thereby harmless: an indirect invocation reaches
            // whatever it names on its own, including storage this fn
            // never held — a callback taking no collection, a function
            // pointer chosen at runtime.  One that WAS handed this
            // fn's own parameter is already charged at that path,
            // which is the reach a caller comparing its buffer needs.
            if (opaque and paths.items.len == charged) unknown = true;
        }

        const entry = self.summaries.getPtr(@intFromEnum(body)) orelse return false;
        // An effect nobody could place is still a reallocation, and so
        // is one this fn placed at a path: either has to reach the
        // coarse flag, or `may_grow` being false would hide exactly
        // the reallocation `grow_paths` / `grows_unknown_path` record.
        if (unknown or paths.items.len != 0) entry.may_grow_collections = true;
        if (entry.grows_unknown_path == unknown and growPathsEqual(entry.grow_paths, paths.items)) {
            return false;
        }
        entry.grows_unknown_path = unknown;
        entry.grow_paths = try paths.toOwnedSlice(arena);
        return true;
    }

    // ── Grow paths of the declaration a call actually reaches ──────
    //
    // A name in a body says nothing about which declaration it names.
    // An alias reaches one, a shadowing declaration reaches another,
    // and a container this file never declared has a whole API of its
    // own behind a spelling this file shares with someone else's.
    // So Phase 8 asks the type engine what the call RESOLVES to, and
    // reads that declaration where it is written.

    /// Rounds a grow-path fold may take to settle.  Each round folds
    /// exactly one call hop, so a chain of N hops settles in N rounds;
    /// a set still arriving at the cap is an under-approximation and
    /// is widened rather than reported at the precision it never
    /// reached.
    const max_grow_rounds: u32 = 64;

    /// A demand-driven fold is not depth-capped.  The shared cycle set
    /// is what bounds it: a declaration is entered once, so the walk
    /// terminates on the call graph rather than on a budget, and a
    /// cycle is recorded as an open question instead of an answer.

    fn growStateAlloc(self: *FileCache) error{OutOfMemory}!*GrowState {
        if (self.grow_state == null) {
            const state: GrowState = .{
                .owner = self,
                .documents = .empty,
                .verdicts = .empty,
                .active = .empty,
            };
            self.grow_state = try self.gpa.create(GrowState);
            self.grow_state.?.* = state;
        }
        return self.grow_state.?;
    }

    /// The per-file state that reads declarations of `handle`, opened
    /// once per document and owned until teardown.  Its resolver
    /// borrows the store's own handle for that document, so the
    /// document's imports and toolchain sources resolve exactly as they
    /// do for the file under analysis — no second reading of the file,
    /// and no path reconstructed from a name.
    fn sourceDocument(
        self: *FileCache,
        handle: *@import("type_engine").DocumentStore.Handle,
    ) OpenError!*SourceDocument {
        const state = try self.growStateAlloc();
        if (state.documents.get(&handle.tree)) |document| return document;
        // Heap-allocated before it is initialized: the analyser's
        // allocator points into the resolver's own arena, so the
        // resolver must not move once it holds one.
        const resolver = try self.gpa.create(zls_resolver_mod.TypeResolver);
        errdefer self.gpa.destroy(resolver);
        resolver.* = undefined;
        try resolver.initBorrowed(self.zls.?.ctx, self.gpa, handle);
        errdefer resolver.deinit();
        const document = try self.gpa.create(SourceDocument);
        errdefer self.gpa.destroy(document);
        document.* = .{ .resolver = resolver, .cache = undefined };
        // `FileCache.init` allocates nothing before it can fail, so a
        // failure here leaves `document` unbuilt rather than half-open.
        document.cache = try FileCache.init(self.gpa, &resolver.handle.tree);
        // Wired after the document is in its final place: the cache
        // borrows the resolver, and neither is ever moved.
        document.cache.zls = resolver;
        document.cache.grow_state = state;
        document.cache.grow_on_demand = true;
        try state.documents.put(self.gpa, &resolver.handle.tree, document);
        return document;
    }

    /// The declaration a call's callee expression reaches, resolved
    /// once per callee token.  Null when the type engine cannot name
    /// it, when the token belongs to no call, or when the token is not
    /// the `fn` keyword of the declaration it points at.
    fn actualCalleeOf(self: *FileCache, callee_token: Ast.TokenIndex) error{OutOfMemory}!?ActualCallee {
        const gop = try self.actual_callees.getOrPut(self.gpa, callee_token);
        if (!gop.found_existing) {
            gop.value_ptr.* = self.resolveActualCallee(callee_token) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => null,
            };
        }
        return gop.value_ptr.*;
    }

    /// True when this callee token really is an INVOCATION whose
    /// declaration the type engine could not name.  A token with no
    /// call node behind it is a type application or a spelled name, not
    /// something that runs, and must not be charged as one.
    ///
    /// Read only after `actualCalleeOf` has answered for this token,
    /// so the cached verdict is the one this pass is acting on.
    fn isUnnamedCall(self: *FileCache, callee_token: Ast.TokenIndex) bool {
        const index = self.getCallIndex() catch return false;
        if (index.by_callee_token.get(callee_token) == null) return false;
        return self.actual_callees.get(callee_token) == null;
    }

    fn resolveActualCallee(self: *FileCache, callee_token: Ast.TokenIndex) !?ActualCallee {
        const resolver = self.zls orelse return null;
        const index = try self.getCallIndex();
        const node = index.by_callee_token.get(callee_token) orelse return null;
        // `fullCall` borrows this buffer for the fixed-arity call
        // shapes, so the call is read here and never carried out.
        var buffer: [1]Ast.Node.Index = undefined;
        const call = self.tree.fullCall(&buffer, node) orelse return null;
        const reference = (try resolver.functionReference(call.ast.fn_expr)) orelse return null;
        // A reference whose token is not its own declaration's `fn`
        // keyword is not a declaration at all — a function TYPE has
        // one, and reading its syntax as a body would invent effects.
        const declaration = tokens.enclosingFnDecl(reference.tree, reference.fn_token) orelse return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(reference.tree, &proto_buffer, declaration) orelse return null;
        if (proto.ast.fn_token != reference.fn_token) return null;
        return .{
            .call_node = node,
            .tree = reference.tree,
            .fn_token = reference.fn_token,
            .handle = reference.handle,
            .declaration = declaration,
        };
    }

    /// Where `callee`'s own reallocations land, computed in the
    /// document that declares it.
    ///
    /// A declaration of the file under analysis reads the live summary
    /// the fixed point is still filling, so a pass sees what the
    /// earlier passes learned.  A declaration anywhere else is computed
    /// here, in its own document and with its own imports intact —
    /// transitively, because that document folds its callees the same
    /// way.  Null when the declaration is already being computed: a
    /// cycle is not an answer, and the caller charges it.
    fn growVerdictOf(self: *FileCache, callee: ActualCallee) anyerror!?GrowVerdict {
        if (callee.tree == self.tree and !self.grow_on_demand) {
            const summary = try self.summaryOfFn(callee.declaration);
            return .{ .paths = summary.grow_paths, .unknown = summary.grows_unknown_path };
        }
        if (callee.tree == self.tree) return self.demandVerdict(self.tree, self, callee.declaration);
        const document = try self.sourceDocument(callee.handle);
        return self.demandVerdict(callee.tree, &document.cache, callee.declaration);
    }

    /// Compute one declaration's verdict on demand, once per
    /// declaration, guarded against re-entering one already on the
    /// stack.  A cycle is not an answer: it reads as null so the caller
    /// charges, never as a declaration that grows nothing.
    fn demandVerdict(
        self: *FileCache,
        tree: *const Ast,
        document: *FileCache,
        fn_decl: Ast.Node.Index,
    ) anyerror!?GrowVerdict {
        const state = try self.growStateAlloc();
        const key: DeclKey = .{ .tree = tree, .declaration = fn_decl };
        if (state.verdicts.get(key)) |verdict| return verdict;
        // The cycle set is the only bound: entering one is an open
        // question, never an answer, and nothing incomplete is ever
        // cached as a declaration that grows nothing.
        if (state.active.contains(key)) return null;
        try state.active.put(self.gpa, key, {});
        defer _ = state.active.remove(key);
        const verdict = try document.resolveGrowPathsAt(fn_decl);
        try state.verdicts.put(self.gpa, key, verdict);
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
    fn resolveGrowPathsAt(self: *FileCache, fn_decl: Ast.Node.Index) anyerror!GrowVerdict {
        if (tokens.returnsType(self.tree, fn_decl)) return .{ .paths = &.{}, .unknown = false };
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buffer, fn_decl) orelse return .{};
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return .{};
        // Phase 8 writes through `summaries`, so the entry has to exist
        // before the first pass reads it back.
        _ = try self.summaryOfFn(fn_decl);
        const model = try self.fileModel();
        const receiver_type: ?[]const u8 = if (model.containingTypeAtToken(proto.ast.fn_token)) |owner|
            owner.qualified_name
        else
            null;
        var rounds: u32 = 0;
        while (rounds < max_grow_rounds) : (rounds += 1) {
            if (!try self.resolveGrowPathsOne(fn_decl, receiver_type)) return self.growVerdictStored(body);
        }
        // The cap was reached with paths still arriving, so this set is
        // an under-approximation.  Say so rather than report precision
        // this document never reached.
        const entry = self.summaries.getPtr(@intFromEnum(body)) orelse return .{};
        if (entry.may_grow_collections) entry.grows_unknown_path = true;
        return .{ .paths = entry.grow_paths, .unknown = entry.grows_unknown_path };
    }

    fn growVerdictStored(self: *FileCache, body: Ast.Node.Index) GrowVerdict {
        const entry = self.summaries.getPtr(@intFromEnum(body)) orelse return .{};
        return .{ .paths = entry.grow_paths, .unknown = entry.grows_unknown_path };
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
    ///   - `unknown` recorded when the fold could not finish: a cycle,
    ///     a document this session cannot read, an argument map the
    ///     declaration's own arity does not admit.  None of those is
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
    fn foldActualGrow(
        self: *FileCache,
        proto: Ast.full.FnProto,
        body: Ast.Node.Index,
        call: fn_summary.GrowCall,
        arena: std.mem.Allocator,
        paths: *std.ArrayListUnmanaged(fn_summary.GrowPath),
        unknown: *bool,
    ) anyerror!bool {
        if (self.zls == null) return false;
        const callee = (try self.actualCalleeOf(call.callee_token)) orelse return false;
        const resolver = self.zls.?;
        // One buffer backs both reads: the call's own argument storage
        // for the fixed-arity call shapes, so it outlives every node
        // taken from it here.
        var call_buffer: [1]Ast.Node.Index = undefined;
        const verdict = (try self.growVerdictOf(callee)) orelse {
            // The declaration is known and its analysis did not
            // finish.  That is an open question, not a negative one.
            unknown.* = true;
            return true;
        };
        if (verdict.unknown) unknown.* = true;
        if (verdict.paths.len == 0) return true;
        // Read here, not by the caller: `growVerdictOf` above may have
        // folded a declaration of THIS document, and every such fold
        // builds the bindings of another body in the same table — which
        // rehashes it and moves every pointer into it.
        const bindings = try self.localBindings(proto, body);
        // A verdict read from another document points into that
        // document's arena.  It is copied in rather than borrowed, so
        // the path this records survives independently of the source it
        // was read from.
        const own = callee.tree == self.tree;
        for (verdict.paths) |gp| {
            const argument = (resolver.callArgumentIn(&call_buffer, callee.call_node, gp.param) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => {
                    unknown.* = true;
                    continue;
                },
            }) orelse {
                // This declaration grows a parameter this call does not
                // hand it.  Where that storage came from is undecided.
                unknown.* = true;
                continue;
            };
            const first = self.tree.firstToken(argument);
            const last = self.tree.lastToken(argument);
            const field: []const u8 = if (own) gp.field else try arena.dupe(u8, gp.field);
            const rooted: ?fn_summary.ParamPath = blk: {
                switch (try fn_summary.ownerOfExpr(arena, self.tree, proto, bindings, first, last, 0)) {
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
                switch (try fn_summary.growBaseOfExpr(arena, self.tree, proto, bindings, first, last)) {
                    .unproven => |claim| {
                        if (!try self.provesFreshStorage(claim)) unknown.* = true;
                        break :blk null;
                    },
                    .storage => |storage| switch (storage) {
                        .unknown => {
                            unknown.* = true;
                            break :blk null;
                        },
                        .param => |pp| break :blk pp,
                    },
                }
            };
            const path = rooted orelse continue;
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
    fn widenUnconvergedGrowEffects(self: *FileCache) !void {
        var it = self.summaries.valueIterator();
        while (it.next()) |entry| {
            if (entry.may_grow_collections) entry.grows_unknown_path = true;
        }
    }

    // ── Phases 9 ───────────────────────────────────────────────
    //
    // Phase 8 settles WHERE a reallocation lands, and it settles that
    // after the coarse grow flags of Phase 5 have already propagated.
    // A grow Phase 8 could only record as unattributed still raises
    // `may_grow_collections` there, so the coarse pass runs once more
    // to carry that answer up to this fn's own callers.  Without it a
    // grandparent would read its callee as a fn that grows nothing.
    fn propagateCoarseGrowAgain(self: *FileCache, model: *const file_model.FileModel) !void {
        var iters: u32 = 0;
        while (iters < 16) : (iters += 1) {
            var changed = false;
            for (model.fns) |fi| {
                if (try self.propagateEffectOne(fi.fn_decl, null, .grow)) changed = true;
            }
            for (model.types) |ti| {
                for (ti.methods) |m| {
                    if (try self.propagateEffectOne(m.fn_decl, ti.qualified_name, .grow)) changed = true;
                }
            }
            if (!changed) break;
        }
    }

    // ── Fresh storage: does an initializer build storage no one
    // else holds? ────────────────────────────────────────────────
    //
    // `fn_summary` refuses to answer this from spelling: `Foo.init`
    // may return a global, and a struct literal may fill an omitted
    // field from a default that reads one.  The answer comes from
    // DECLARATIONS instead — the declaration a constructor call
    // resolves to, a project constructor's own returns, and the
    // type's own field list and those fields' defaults.  Everything
    // else stays unknown, and an unknown initializer is charged as
    // unattributed storage.

    /// Depth cap for the declaration walk: a constructor may build
    /// through another constructor, and each level costs another
    /// pass over a body.
    const max_fresh_depth = 4;

    /// Does `claim` provably build storage this fn built for itself?
    ///
    /// Proved for exactly these:
    ///   - `&[_]T{…}` / `&.{}` — memory this expression laid out;
    ///   - `<Type>.<ctor>(…)` whose resolved declaration is a
    ///     standard-library list constructor of this toolchain (see
    ///     `standardListConstructor`), or a method of a type this
    ///     project declares whose every `return` is proved fresh
    ///     here;
    ///   - `.{ … }` / `<Type>{ … }` whose every listed value is proved
    ///     fresh and whose every OMITTED field carries a default that
    ///     reads no name.
    ///
    /// A constructor declaration in ANOTHER project file is not read:
    /// the question would be a second-order one (that file's own
    /// aliases and imports), and an unproved answer must stay
    /// unknown.
    pub fn provesFreshStorage(
        self: *FileCache,
        claim: fn_summary.FreshClaim,
    ) error{OutOfMemory}!bool {
        return self.freshStorageAt(claim, 0);
    }

    /// The recursion below is mutual — a struct literal asks about
    /// each value it supplies, and a constructor asks about the
    /// returns of its own declaration — so the error set is spelled
    /// out here rather than inferred.  Only the verdicts' own
    /// bookkeeping allocates; every other question this walk asks is
    /// answered `false`, never propagated.
    fn freshStorageAt(
        self: *FileCache,
        claim: fn_summary.FreshClaim,
        depth: u8,
    ) error{OutOfMemory}!bool {
        if (claim.first > claim.last) return false;
        if (depth > max_fresh_depth) return false;
        const key = (@as(u64, claim.first) << 32) | @as(u64, claim.last);
        if (self.fresh_storage.get(key)) |cached| return cached;
        // Written only once the walk is done, so a claim that reaches
        // itself cannot read a half-finished verdict.
        const verdict = try self.resolveFreshStorage(claim, depth);
        try self.fresh_storage.put(self.gpa, key, verdict);
        return verdict;
    }

    fn resolveFreshStorage(self: *FileCache, claim: fn_summary.FreshClaim, depth: u8) !bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var first = claim.first;
        const last = claim.last;
        if (self.zls) |resolver| {
            if (self.nodeForExactSpan(first, last)) |node| {
                const type_node = if (claim.type_first) |type_first|
                    self.nodeForExactSpan(type_first, claim.type_last.?)
                else
                    null;
                if (resolver.stdCollectionEmptyOf(node, type_node) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => false,
                }) {
                    return (try self.toolchainArrayListTree()) != null;
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
        if (last == first + 3 and tags[first] == .builtin and
            std.mem.eql(u8, tree.tokenSlice(first), "@import") and
            tags[first + 2] == .string_literal)
        {
            return true;
        }
        if (tags[first] == .period) {
            // `.{ … }` names no type, so only the binding's own
            // declaration can say what it left out.
            if (first + 1 > last) return false;
            if (tags[first + 1] != .l_brace or tags[last] != .r_brace) return false;
            const declared: ?TokenRange = if (claim.type_first) |tf| .{
                .first = tf,
                .last = claim.type_last.?,
            } else null;
            return try self.literalBuildsFreshStorage(declared, first + 2, last - 1, depth);
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
                            return try self.constructorBuildsFreshStorage(
                                .{ .first = first, .last = t - 2 },
                                t,
                                .{ .first = first, .last = last },
                                depth,
                            );
                        }
                        t = rp;
                    }
                },
                .l_brace => {
                    if (tags[last] != .r_brace) return false;
                    return try self.literalBuildsFreshStorage(.{ .first = first, .last = t }, t + 2, last - 1, depth);
                },
                // Anything else ends the expression without naming
                // a constructor: a bare `name(…)` call on a name this
                // file did not declare as a type, a value this walk
                // cannot address, or trailing punctuation.  A
                // constructor declaration in ANOTHER project file is
                // not read either — see `provesFreshStorage`.
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
    fn constructorBuildsFreshStorage(
        self: *FileCache,
        type_path: TokenRange,
        ctor: Ast.TokenIndex,
        call: TokenRange,
        depth: u8,
    ) !bool {
        if (depth > max_fresh_depth) return false;
        if (try self.standardListConstructor(call)) return true;
        const type_name = (try self.typePathName(type_path.first, type_path.last)) orelse return false;
        const resolved = (try self.resolveDeclaredType(type_name, depth + 1)) orelse return false;
        // Only this file's own declarations are read; see the note on
        // `provesFreshStorage`.  A model that cannot be built leaves
        // the claim unproved, which is the direction this walk is
        // allowed to fail in: the caller charges unknown storage.
        const model = self.fileModel() catch return false;
        if (resolved.model != model) return false;
        const method = resolved.info.findMethod(self.tree.tokenSlice(ctor)) orelse return false;
        return self.declBuildsFreshStorage(resolved.model.tree, method.fn_decl, depth + 1);
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
    fn standardListConstructor(self: *FileCache, call: TokenRange) !bool {
        const resolver = self.zls orelse return false;
        const node = self.nodeForExactSpan(call.first, call.last) orelse return false;
        var buffer: [1]Ast.Node.Index = undefined;
        const resolved = self.tree.fullCall(&buffer, node) orelse return false;
        const reference = (resolver.functionReference(resolved.ast.fn_expr) catch return false) orelse return false;
        const tree = reference.tree;
        if (reference.fn_token + 1 >= tree.tokens.len) return false;
        const std_tree = (try self.toolchainArrayListTree()) orelse return false;
        if (tree != std_tree) return false;
        const name_token = reference.fn_token + 1;
        if (tree.tokenTag(name_token) != .identifier) return false;
        const name = tree.tokenSlice(name_token);
        if (!std.mem.eql(u8, name, "init") and !std.mem.eql(u8, name, "initCapacity")) return false;
        // Both of these are STATIC in this toolchain's
        // `std/array_list.zig` — `Managed.init(gpa: Allocator)` and
        // `Aligned.initCapacity(gpa: Allocator, num: usize)` declare
        // no receiver — so a call that reached one of them wrote
        // every parameter it declares.  A count that falls short
        // reaches no such declaration: `Aligned.initBuffer` wraps a
        // buffer the CALLER already owns, and a method passes its
        // receiver beside the written arguments rather than as one.
        // Crediting that declaration would vouch for a constructor
        // this call never made.
        const declaration = tokens.enclosingFnDecl(tree, reference.fn_token) orelse return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
        var declared: usize = 0;
        var parameters = proto.iterate(tree);
        while (parameters.next() != null) declared += 1;
        return declared == resolved.ast.params.len;
    }

    /// This toolchain's own `std/array_list.zig`, read through the
    /// same document store the analyser itself resolves `@import("std")`
    /// through.  `absent` records that this session has no toolchain to
    /// read, so the answer is sought once rather than per claim.
    fn toolchainArrayListTree(self: *FileCache) !?*const Ast {
        switch (self.std_list_tree) {
            .known => |tree| return tree,
            .absent => return null,
            .unknown => {},
        }
        const resolver = self.zls orelse return null;
        const library = resolver.ctx.toolchain.zig_lib orelse {
            self.std_list_tree = .absent;
            return null;
        };
        // `sourceHandle` addresses documents by absolute path; a
        // relative one is not a path this can read, not a toolchain.
        if (!std.fs.path.isAbsolute(library)) {
            self.std_list_tree = .absent;
            return null;
        }
        const path = try std.fs.path.join(self.gpa, &.{ library, "std", "array_list.zig" });
        defer self.gpa.free(path);
        // A document this store will not serve is recorded once, so
        // the answer is not re-sought per claim.  Running out of
        // memory is not that: caching it would leave every later
        // claim in this session unable to resolve a constructor for a
        // reason that has nothing to do with the code under analysis,
        // so it is reported instead.  The store's own error set is
        // open-ended, so the retry is named rather than propagated by
        // value.
        const handle = resolver.ctx.sourceHandle(path) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => {
                self.std_list_tree = .absent;
                return null;
            },
        };
        self.std_list_tree = .{ .known = &handle.tree };
        return &handle.tree;
    }

    /// `.{ … }` / `<Type>{ … }` over `[first, last]`.  `spelled` is the
    /// type the path named; an anonymous literal falls back to the
    /// type its binding declared.
    fn literalBuildsFreshStorage(
        self: *FileCache,
        spelled: ?TokenRange,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
        depth: u8,
    ) !bool {
        const type_range = spelled orelse return false;
        const type_name = (try self.typePathName(type_range.first, type_range.last)) orelse return false;
        const resolved = (try self.resolveDeclaredType(type_name, depth + 1)) orelse return false;
        return try self.literalFieldsFresh(resolved, first, last, depth);
    }

    /// Every listed value of a struct literal is proved fresh or is
    /// a value that reads no name, and every field of `resolved` the
    /// literal left out is one the type gives a default.  An EMPTY
    /// literal lists nothing at all, so its whole question is the
    /// fields the type leaves to its own defaults.
    fn literalFieldsFresh(
        self: *FileCache,
        resolved: ResolvedType,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
        depth: u8,
    ) !bool {
        if (first <= last) {
            const tags = self.tree.tokens.items(.tag);
            var item_first = first;
            var nesting: u32 = 0;
            var t = first;
            while (t <= last) : (t += 1) {
                switch (tags[t]) {
                    .l_paren, .l_bracket, .l_brace => nesting += 1,
                    .r_paren, .r_bracket, .r_brace => if (nesting > 0) {
                        nesting -= 1;
                    },
                    .comma => if (nesting == 0) {
                        if (!try self.literalValueIsFresh(item_first, t - 1, depth)) return false;
                        item_first = t + 1;
                    },
                    else => {},
                }
            }
            // A trailing comma leaves nothing after the last value.
            if (item_first <= last and !try self.literalValueIsFresh(item_first, last, depth)) return false;
        }
        for (resolved.info.fields) |field| {
            if (literalNamesField(self.tree, first, last, field.name)) continue;
            // A field with no default is not left behind: a struct
            // literal that omits it is a compile error, so a claim
            // resting on one was never a well-typed program to begin
            // with, and what it would have meant is undecidable.
            if (!field.has_default) return false;
            // A default that READS A NAME can hand back a global's
            // header, which is exactly the storage a literal must not
            // claim as this expression's own.
            const expr = fieldDefaultExpr(resolved.model.tree, field) orelse return false;
            if (!readsNoName(resolved.model.tree, expr.first, expr.last)) return false;
        }
        return true;
    }

    /// One `name = value` pair (or a positional value) of a struct
    /// literal.
    fn literalValueIsFresh(
        self: *FileCache,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
        depth: u8,
    ) !bool {
        if (first > last) return false;
        const tags = self.tree.tokens.items(.tag);
        var value = first;
        if (tags[value] == .period and value + 2 <= last and
            tags[value + 1] == .identifier and tags[value + 2] == .equal)
        {
            value += 3;
            if (value > last) return false;
        }
        if (try self.freshStorageAt(.{ .first = value, .last = last }, depth + 1)) return true;
        return readsNoName(self.tree, value, last);
    }

    /// Does every `return` of this declaration hand back storage this
    /// fn built?  A declaration with no return proves nothing: its
    /// result comes from wherever its caller cannot see.
    fn declBuildsFreshStorage(
        self: *FileCache,
        tree: *const Ast,
        fn_decl: Ast.Node.Index,
        depth: u8,
    ) !bool {
        if (depth > max_fresh_depth) return false;
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buf, fn_decl) orelse return false;
        _ = tokens.bodyOf(tree, fn_decl) orelse return false;
        // `return .{ … };` names no type, so the declaration's own
        // return type is what says which fields it filled in.
        const return_type = proto.ast.return_type.unwrap();
        const key: DeclKey = .{ .tree = tree, .declaration = fn_decl };
        if (self.fresh_visiting.contains(key)) return false;
        try self.fresh_visiting.put(self.gpa, key, {});
        defer _ = self.fresh_visiting.remove(key);
        var returns: u32 = 0;
        var node_idx: u32 = 1;
        while (node_idx < tree.nodes.len) : (node_idx += 1) {
            const node: Ast.Node.Index = @enumFromInt(node_idx);
            if (tree.nodeTag(node) != .@"return") continue;
            const value = tree.nodeData(node).opt_node.unwrap() orelse continue;
            const first = tree.firstToken(value);
            // A nested `fn`'s return is not this declaration's.
            if ((tokens.enclosingFnDecl(tree, first) orelse fn_decl) != fn_decl) continue;
            if (!try self.freshStorageAt(.{
                .first = first,
                .last = tree.lastToken(value),
                .type_first = if (return_type) |rt| tree.firstToken(rt) else null,
                .type_last = if (return_type) |rt| tree.lastToken(rt) else null,
            }, depth + 1)) {
                return false;
            }
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
    fn resolveDeclaredType(self: *FileCache, name: []const u8, depth: u8) !?ResolvedType {
        if (depth > max_fresh_depth) return null;
        if (self.findTypeAcrossImports(name)) |info| return info;
        const dot = std.mem.indexOfScalar(u8, name, '.');
        const head = if (dot) |at| name[0..at] else name;
        // A file-level declaration OWNS its name: follow it to what
        // it aliases, and answer nothing at all when it says nothing
        // this tool can read — a name that has an owner is not free
        // for some other declaration to claim.
        if (self.rootDeclInitRange(head)) |aliased| {
            const aliased_name = (try self.typePathName(aliased.first, aliased.last)) orelse return null;
            return try self.resolveDeclaredType(aliased_name, depth + 1);
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
        const model = self.fileModel() catch return null;
        var found: ?ResolvedType = null;
        for (model.types) |*ti| {
            if (!std.mem.eql(u8, ti.name, name)) continue;
            if (found != null) return null;
            found = .{ .model = model, .info = ti };
        }
        return found;
    }

    /// The dotted name of the type path in `[first, last]`, with
    /// generic argument groups dropped — `std.array_list.Managed(u32)`
    /// becomes "std.array_list.Managed" — and leading `?` / `*` /
    /// `const` qualifiers stripped.  Anything that is not an
    /// identifier path (a slice, a fn type, a call) has no name to
    /// resolve.  The result lives in the cache's summary arena.
    fn typePathName(self: *FileCache, first: Ast.TokenIndex, last: Ast.TokenIndex) !?[]const u8 {
        if (first > last) return null;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var t = first;
        while (t <= last) : (t += 1) {
            switch (tags[t]) {
                .question_mark, .asterisk, .asterisk_asterisk, .keyword_const, .keyword_volatile, .keyword_allowzero => {},
                .identifier => break,
                else => return null,
            }
        }
        if (t > last) return null;
        if (self.summary_arena == null) {
            self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        }
        var out: std.ArrayListUnmanaged(u8) = .empty;
        var wrote = false;
        while (t <= last) {
            switch (tags[t]) {
                .identifier => {
                    if (wrote) try out.append(self.summary_arena.?.allocator(), '.');
                    try out.appendSlice(self.summary_arena.?.allocator(), tree.tokenSlice(t));
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
        return try out.toOwnedSlice(self.summary_arena.?.allocator());
    }

    /// The initializer of the file-level declaration `name`, or null
    /// when the file declares no such name or no initializer.
    fn rootDeclInitRange(self: *FileCache, name: []const u8) ?TokenRange {
        const tree = self.tree;
        for (tree.rootDecls()) |node| {
            const decl = tree.fullVarDecl(node) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(decl.ast.mut_token + 1), name)) continue;
            const initializer = decl.ast.init_node.unwrap() orelse return null;
            return .{ .first = tree.firstToken(initializer), .last = tree.lastToken(initializer) };
        }
        return null;
    }

    // ── Free functions reached through an imported declaration ──

    /// The summary of a free function this file reaches through one of
    /// its own declarations — `helpers.growNames(…)` where
    /// `const helpers = @import("./helpers.zig")`.  Null when the
    /// qualifier is storage rather than a module, when the module is
    /// out of this project's reach, or when it declares no such
    /// function.  A module that fails to read records the failure the
    /// session reports, so an unreadable import is never mistaken for
    /// a clean bill of health.
    pub fn summaryByQualifiedName(
        self: *FileCache,
        qualifier: []const u8,
        name: []const u8,
    ) !?fn_summary.FnSummary {
        const module = self.qualifierModule(qualifier) orelse return null;
        return self.summaryOfModuleFn(module, name);
    }

    /// The module the file-level declaration `qualifier` names, or
    /// null when it names storage, a type, or a module this project
    /// cannot read.
    fn qualifierModule(self: *FileCache, qualifier: []const u8) ?*const file_model.FileModel {
        const pc = self.project orelse return null;
        const init_range = self.rootDeclInitRange(qualifier) orelse return null;
        const tree = self.tree;
        const first = init_range.first;
        const last = init_range.last;
        if (last != first + 3) return null;
        if (tree.tokenTag(first) != .builtin) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(first), "@import")) return null;
        if (tree.tokenTag(first + 2) != .string_literal) return null;
        const literal = tree.tokenSlice(first + 2);
        if (std.mem.indexOfScalar(u8, literal, '\\') != null) return null;
        const import_path = literal[1 .. literal.len - 1];
        const imported = (if (project_cache_mod.isRelativeImport(import_path))
            pc.modelForRelativeImport(self.file_path, import_path)
        else
            pc.modelForModuleImport(self.file_path, import_path)) catch |err| {
            pc.failure = err;
            return null;
        };
        return imported;
    }

    /// The summary of the top-level `name` of `module`, or null when
    /// it declares no such function.
    fn summaryOfModuleFn(
        self: *FileCache,
        module: *const file_model.FileModel,
        name: []const u8,
    ) !?fn_summary.FnSummary {
        const function = module.findFn(name) orelse return null;
        return self.summaryOfResolvedMethod(.{
            .tree = module.tree,
            .fn_decl = function.fn_decl,
        });
    }

    /// Type name of the container `owner` designates: the parameter's
    /// own container for a bare parameter, or the field chain's final
    /// struct.  Null when the chain's types do not resolve.
    fn receiverTypeName(
        self: *FileCache,
        proto: Ast.full.FnProto,
        owner: fn_summary.ParamPath,
    ) !?[]const u8 {
        const root = (try self.paramContainerName(proto, owner.param)) orelse return null;
        if (owner.path.len == 0) return root;
        var resolved = self.findTypeAcrossImports(root) orelse return null;
        var rest = owner.path;
        while (rest.len != 0) {
            const dot = std.mem.indexOfScalar(u8, rest, '.');
            const segment = if (dot) |at| rest[0..at] else rest;
            resolved = self.fieldType(resolved, segment) orelse return null;
            if (dot == null) break;
            rest = rest[dot.? + 1 ..];
        }
        return resolved.info.qualified_name;
    }

    /// Re-aim each of `callee_paths` at this fn's OWN parameters,
    /// through the argument that supplies them.  A callee path whose
    /// argument this file cannot trace leaves the answer unknown
    /// rather than being silently dropped.
    fn foldGrowPaths(
        arena: std.mem.Allocator,
        paths: *std.ArrayListUnmanaged(fn_summary.GrowPath),
        call: fn_summary.GrowCall,
        callee_paths: []const fn_summary.GrowPath,
        unknown: *bool,
    ) !void {
        for (callee_paths) |gp| {
            if (gp.param >= call.args.len) continue;
            switch (call.args[gp.param]) {
                .unknown => unknown.* = true,
                .param => |pp| try appendGrowPath(arena, paths, .{
                    .param = pp.param,
                    .field = try fn_summary.joinPath(arena, pp.path, gp.field),
                }),
            }
        }
    }

    /// Only declared narrow primitive values cannot carry an address.
    /// Unknown types and pointer-sized values retain storage effects.
    fn parameterIsNonAddressScalar(
        self: *FileCache,
        proto: Ast.full.FnProto,
        origin: fn_summary.ParamPath,
    ) error{OutOfMemory}!bool {
        if (origin.path.len != 0) return false;
        var parameters = proto.iterate(self.tree);
        var index: u32 = 0;
        while (parameters.next()) |parameter| : (index += 1) {
            if (index != origin.param) continue;
            const type_node = parameter.type_expr orelse return false;
            if (self.zls) |resolver| {
                if ((resolver.isBoolType(type_node) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => return false,
                }) == true) return true;
                if (resolver.intInfo(type_node) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => return false,
                }) |info|
                    return info.bits < @bitSizeOf(usize);
                if (resolver.floatBits(type_node) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => return false,
                }) |bits|
                    return bits < @bitSizeOf(usize);
                return false;
            }
            // In syntax-only mode, only unambiguous primitive declarations
            // prove a scalar. Aliases, wrappers and pointer-sized values do not.
            if (self.tree.nodeTag(type_node) != .identifier) return false;
            const name = self.tree.tokenSlice(self.tree.nodeMainToken(type_node));
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
    /// `charge_unplaced` records it as unattributed storage.  A
    /// method or a call through a named module never sets it: a
    /// constructor is routinely handed exactly such an argument
    /// (`std.heap.page_allocator`), and charging it would turn every
    /// locally built header into somebody else's buffer.  A bare call
    /// this file cannot resolve keeps the coarse reading — there, an
    /// unplaceable argument is all the evidence there is.
    fn chargeHandedStorage(
        self: *FileCache,
        proto: Ast.full.FnProto,
        arena: std.mem.Allocator,
        paths: *std.ArrayListUnmanaged(fn_summary.GrowPath),
        unknown: *bool,
        call: fn_summary.GrowCall,
        comptime charge_unplaced: bool,
    ) error{OutOfMemory}!void {
        for (call.args) |arg| {
            switch (arg) {
                .param => |pp| {
                    if (try self.parameterIsNonAddressScalar(proto, pp)) continue;
                    try appendGrowPath(arena, paths, .{
                        .param = pp.param,
                        .field = pp.path,
                    });
                },
                .unknown => if (charge_unplaced) {
                    unknown.* = true;
                },
            }
        }
    }

    /// Add `gp` unless the set already holds it.  Duplicates would grow
    /// without bound between two mutually recursive fns, each folding
    /// the other's paths back in on every pass, and Phase 8 would then
    /// never see a pass that learned nothing new.
    fn appendGrowPath(
        arena: std.mem.Allocator,
        paths: *std.ArrayListUnmanaged(fn_summary.GrowPath),
        gp: fn_summary.GrowPath,
    ) !void {
        for (paths.items) |existing| {
            if (existing.param == gp.param and std.mem.eql(u8, existing.field, gp.field)) return;
        }
        try paths.append(arena, gp);
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
        const type_name = (try self.paramContainerName(proto, param_idx)) orelse return null;
        var owner = self.findTypeAcrossImports(type_name) orelse return null;
        var field_tok = first + 2;
        while (field_tok < method_tok) : (field_tok += 2) {
            owner = self.fieldType(owner, tree.tokenSlice(field_tok)) orelse return null;
        }
        const summary = (try self.summaryForType(owner, method_name)) orelse return null;
        if (summary.returns == .borrowed_from and summary.returns.borrowed_from == 0) return param_idx;
        return null;
    }

    /// Resolve a namespace or lexical function declaration before propagating
    /// its borrowed argument. A leaf name is not a dispatch identity.
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
        const returns = result: {
            if (tree.nodeTag(callee) == .field_access) {
                const recv = tree.nodeData(callee).node_and_token[0];
                const type_name = typeNameFromTypeNode(tree, recv) orelse return null;
                const method = self.findMethodAcrossImports(type_name, method_name) orelse return null;
                const summary = (try self.summaryOfResolvedMethod(method)) orelse return null;
                break :result summary.returns;
            }
            const model = try self.fileModel();
            var scope: ?[]const u8 = if (model.containingTypeAtToken(proto.ast.fn_token)) |owner|
                owner.qualified_name
            else
                null;
            while (scope) |name| {
                const owner = model.findType(name) orelse break;
                if (owner.findMethod(method_name)) |method| {
                    break :result (try self.summaryOfFn(method.fn_decl)).returns;
                }
                scope = if (std.mem.lastIndexOfScalar(u8, name, '.')) |dot| name[0..dot] else null;
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
        const entry = self.summaries.getPtr(key) orelse return;
        if (entry.may_free_fields.len == 0) return;
        if (self.summary_arena == null) {
            self.summary_arena = std.heap.ArenaAllocator.init(self.gpa);
        }
        const a = self.summary_arena.?.allocator();
        const filtered = try self.filterMayFreeFields(a, proto, entry.may_free_fields);
        self.summaries.getPtr(key).?.may_free_fields = filtered;
    }

    /// Returns true iff the fn's summary's `takes_ownership_of` was
    /// updated by this call.  Scans body for `<param>.<method>()`
    /// chains; when method's cached summary takes arg 0, the outer
    /// fn takes the param.
    fn propagateTransitiveTakesOne(
        self: *FileCache,
        fn_decl: Ast.Node.Index,
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

            const type_name = (try self.paramContainerName(proto, pi)) orelse continue;
            const owner = self.findTypeAcrossImports(type_name) orelse continue;
            const summary = (try self.summaryForType(owner, method)) orelse continue;
            const callee_takes = summary.takes_ownership_of;
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
    /// Resolve first, then cache by immutable source snapshot and declaration.
    pub fn summaryByMethodCrossFile(
        self: *FileCache,
        type_name: []const u8,
        method_name: []const u8,
    ) !?fn_summary.FnSummary {
        const resolved = self.findMethodAcrossImports(type_name, method_name) orelse return null;
        return self.summaryOfResolvedMethod(resolved);
    }

    fn summaryOfResolvedMethod(self: *FileCache, resolved: ResolvedMethod) !?fn_summary.FnSummary {
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(resolved.tree, &buffer, resolved.fn_decl) orelse return null;
        const body = tokens.bodyOf(resolved.tree, resolved.fn_decl) orelse return null;
        if (resolved.tree == self.tree) return (try self.summaryOf(proto, body)).*;
        const project = self.project orelse return null;
        if (project.getMethodSummaryCache(resolved.tree, resolved.fn_decl)) |cached| {
            // The project cache carries only the coarse flags, so a
            // foreign method reports "it may grow, and I cannot say
            // whose buffer" rather than inventing paths.
            return .{
                .returns = cached.returns,
                .takes_ownership_of = cached.takes,
                .may_grow_collections = cached.may_grow,
                .may_invoke_gc = cached.may_gc,
                .may_run_on_any_thread = cached.may_thread,
                .grows_unknown_path = cached.may_grow,
            };
        }
        var foreign = try FileCache.init(self.gpa, resolved.tree);
        defer foreign.deinit();
        try foreign.resolveTransitiveTakes();
        const summary = try foreign.summaryOf(proto, body);
        const result: fn_summary.FnSummary = .{
            .returns = summary.returns,
            .takes_ownership_of = summary.takes_ownership_of,
            .may_grow_collections = summary.may_grow_collections,
            .may_invoke_gc = summary.may_invoke_gc,
            .may_run_on_any_thread = summary.may_run_on_any_thread,
            .grows_unknown_path = summary.may_grow_collections,
        };
        try project.putMethodSummaryCache(resolved.tree, resolved.fn_decl, .{
            .returns = result.returns,
            .takes = result.takes_ownership_of,
            .may_grow = result.may_grow_collections,
            .may_gc = result.may_invoke_gc,
            .may_thread = result.may_run_on_any_thread,
        });
        return result;
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
        const node = self.nodeForExactSpan(start_tok, end_tok) orelse return null;
        return zls.typeNameOfNode(node) catch null;
    }

    pub fn typeReferenceOfExpr(self: *FileCache, first: Ast.TokenIndex, last: Ast.TokenIndex) !?[]const u8 {
        const resolver = self.zls orelse return null;
        const node = self.nodeForExactSpan(first, last) orelse return null;
        return resolver.typeReferenceOfNode(node);
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
        const node = self.nodeForExactSpan(start_tok, end_tok) orelse return null;
        return zls.intInfo(node) catch null;
    }

    pub fn isEnumTypeOfExpr(
        self: *FileCache,
        start_tok: Ast.TokenIndex,
        end_tok: Ast.TokenIndex,
    ) ?bool {
        const zls = self.zls orelse return null;
        const node = self.nodeForExactSpan(start_tok, end_tok) orelse return null;
        return zls.isEnumType(node) catch null;
    }

    fn nodeForExactSpan(
        self: *const FileCache,
        start_tok: Ast.TokenIndex,
        end_tok: Ast.TokenIndex,
    ) ?Ast.Node.Index {
        const tree = self.tree;
        const main_toks = tree.nodes.items(.main_token);
        var idx: u32 = 1;
        while (idx < tree.nodes.len) : (idx += 1) {
            const mt = main_toks[idx];
            if (mt < start_tok or mt > end_tok) continue;
            const node: Ast.Node.Index = @enumFromInt(idx);
            if (tree.firstToken(node) == start_tok and tree.lastToken(node) == end_tok)
                return node;
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

/// The `= <expr>` a struct field declares, or null.  A field with no
/// default is left undefined when a struct literal omits it, which no
/// other binding is holding; a default that reads a NAME can hand back
/// a global's header, which is the case `.{}` must never claim as its
/// own.
fn fieldDefaultExpr(tree: *const Ast, field: file_model.FieldInfo) ?FileCache.TokenRange {
    if (field.type_last + 1 >= tree.tokens.len) return null;
    const tags = tree.tokens.items(.tag);
    var t = field.type_last + 1;
    var depth: u32 = 0;
    var equal: ?Ast.TokenIndex = null;
    while (t < tree.tokens.len) : (t += 1) {
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

/// Does a struct literal in `[first, last]` name `field`?
fn literalNamesField(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex, field: []const u8) bool {
    if (first > last) return false;
    const tags = tree.tokens.items(.tag);
    var t = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier or tags[t + 2] != .equal) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t + 1), field)) return true;
    }
    return false;
}

/// A value that reads no name: a number, a string, `null`, a
/// boolean, an enum member (`.tag`, whose identifier names a value
/// rather than storage), or punctuation-only compound arithmetic.
/// Anything else — a name, a call, a builtin — can hand back a header
/// somebody else is holding.
fn readsNoName(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    if (first > last) return false;
    const tags = tree.tokens.items(.tag);
    var previous: ?std.zig.Token.Tag = null;
    for (tags[first .. last + 1]) |tag| {
        switch (tag) {
            .identifier => if (previous != .period) return false,
            .builtin, .l_paren, .l_brace, .l_bracket => return false,
            else => {},
        }
        previous = tag;
    }
    return true;
}

/// Walk a dotted field path (e.g. "inner.handle") through a struct
/// type chain, returning the DEEPEST field's type as a path split.
/// For a single-segment path "f", returns `<outer>.f`'s type.  For
/// multi-segment "f.g.h", walks outer.f -> field-type-of-f, then
/// Extract the bare container name from an AST type-expression node without
/// invoking ZLS.  Strips leading `?`, `*`, `const` qualifiers, then walks
/// a dotted identifier chain and retains its namespace.
///
/// Examples: `*Foo` → "Foo", `?*const ns.Foo` → "ns.Foo".
/// Returns null for slices (`[]T`), function pointers, anonymous structs,
/// or any shape that doesn't reduce to a plain dotted identifier chain.
fn typeNameFromTypeNode(tree: *const Ast, type_node: Ast.Node.Index) ?[]const u8 {
    return tokens.typeNameFromTokens(tree, tree.firstToken(type_node), tree.lastToken(type_node));
}

const Namespace = struct {
    model: *const file_model.FileModel,
    info: ?*const file_model.TypeInfo = null,
};

fn resolveNamed(
    gpa: std.mem.Allocator,
    project: ?*project_cache_mod.ProjectCache,
    model: *const file_model.FileModel,
    from_path: []const u8,
    name: []const u8,
    depth: u32,
) ?Namespace {
    if (depth == 0) {
        if (project) |pc| pc.failure = error.ImportResolutionDepthExceeded;
        return null;
    }
    var path: [32][]const u8 = undefined;
    var segments = std.mem.splitScalar(u8, name, '.');
    var count: usize = 0;
    while (segments.next()) |segment| {
        if (count == path.len) return null;
        path[count] = std.mem.trim(u8, segment, &std.ascii.whitespace);
        count += 1;
    }
    if (model.findQualifiedType(path[0..count])) |info| {
        if (count != 1 or info.parent == null) return .{ .model = model, .info = info };
    }
    const first_dot = std.mem.indexOfScalar(u8, name, '.');
    const head = if (first_dot) |dot| name[0..dot] else name;
    const suffix = if (first_dot) |dot| name[dot + 1 ..] else "";
    for (model.tree.rootDecls()) |node| {
        const decl = model.tree.fullVarDecl(node) orelse continue;
        if (!std.mem.eql(u8, model.tree.tokenSlice(decl.ast.mut_token + 1), std.mem.trim(u8, head, &std.ascii.whitespace))) continue;
        const initializer = decl.ast.init_node.unwrap() orelse return null;
        return resolveExpression(gpa, project, model, from_path, initializer, suffix, depth - 1);
    }
    return null;
}

fn resolveExpression(
    gpa: std.mem.Allocator,
    project: ?*project_cache_mod.ProjectCache,
    model: *const file_model.FileModel,
    from_path: []const u8,
    node: Ast.Node.Index,
    suffix: []const u8,
    depth: u32,
) ?Namespace {
    if (depth == 0) {
        if (project) |pc| pc.failure = error.ImportResolutionDepthExceeded;
        return null;
    }
    const tree = model.tree;
    switch (tree.nodeTag(node)) {
        .identifier, .field_access => {
            const field = tree.nodeTag(node) == .field_access;
            const token = if (field) tree.nodeData(node).node_and_token[1] else tree.nodeMainToken(node);
            const segment = tree.tokenSlice(token);
            const name = if (suffix.len != 0) std.fmt.allocPrint(gpa, "{s}.{s}", .{ segment, suffix }) catch return null else segment;
            defer if (suffix.len != 0) gpa.free(name);
            if (field) return resolveExpression(gpa, project, model, from_path, tree.nodeData(node).node_and_token[0], name, depth - 1);
            return resolveNamed(gpa, project, model, from_path, name, depth - 1);
        },
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
            const pc = project orelse return null;
            const token = tree.nodeMainToken(node);
            if (!std.mem.eql(u8, tree.tokenSlice(token), "@import")) return null;
            if (tree.tokens.items(.tag)[token + 2] != .string_literal) return null;
            const literal = tree.tokenSlice(token + 2);
            if (std.mem.indexOfScalar(u8, literal, '\\') != null) return null;
            const import_path = literal[1 .. literal.len - 1];
            const imported = (if (project_cache_mod.isRelativeImport(import_path))
                pc.modelForRelativeImport(from_path, import_path)
            else
                pc.modelForModuleImport(from_path, import_path)) catch |err| {
                pc.failure = err;
                return null;
            };
            const target = imported orelse return null;
            if (suffix.len == 0) {
                for (target.types) |*info| {
                    if (info.body_first == 0) return .{ .model = target, .info = info };
                }
                return .{ .model = target };
            }
            return resolveNamed(gpa, pc, target, pc.pathForModel(target), suffix, depth - 1);
        },
        else => return null,
    }
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
    var cache = try FileCache.init(gpa, &tree);
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
    var cache = try FileCache.init(gpa, &tree);
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
    var cache = try FileCache.init(gpa, &tree);
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
    var cache = try FileCache.init(gpa, &tree);
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
    var cache = try FileCache.init(gpa, &tree);
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
    var cache = try FileCache.init(gpa, &tree);
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
        ".zig-cache", "tmp", &tmp.sub_path, "consumer.zig",
    });
    defer gpa.free(from_path);

    const consumer_src: [:0]const u8 =
        \\const destroyer = @import("./destroyer.zig");
        \\pub fn useNode(n: *destroyer.Node) void { _ = n; }
    ;
    var consumer_tree = try Ast.parse(gpa, consumer_src, .zig);
    defer consumer_tree.deinit(gpa);

    const project_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(project_root);
    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{project_root} });
    defer pc.deinit();

    var cache = try FileCache.init(gpa, &consumer_tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    const summary = (try cache.summaryByMethodCrossFile("destroyer.Node", "kill")).?;
    try std.testing.expectEqual(@as(?u32, 0), summary.takes_ownership_of);
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
        ".zig-cache", "tmp", &tmp.sub_path, "wrapper.zig",
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

    const project_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(project_root);
    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{project_root} });
    defer pc.deinit();

    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

    try cache.resolveTransitiveTakes();

    // `wrapper` calls `node.kill(gpa)` where `kill` takes ownership of
    // its receiver (param 0).  After transitive propagation, `wrapper`
    // should also have takes_ownership_of = 0 (its first param `node`).
    const summary = (try cache.summaryByName("wrapper")).?;
    try std.testing.expectEqual(@as(?u32, 0), summary.takes_ownership_of);
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
    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();
    try cache.resolveTransitiveTakes();

    // Inner has no `deinit` → the raw field-free entry is filtered out.
    const s = (try cache.summaryByMethod("Outer", "deinitOuter")).?;
    try std.testing.expectEqual(@as(usize, 0), s.may_free_fields.len);
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

    const project_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(project_root);
    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{project_root} });
    defer pc.deinit();
    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);

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
    var fc = try FileCache.init(gpa, &tree);
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
        \\    fn grow(self: *T, x: u32) void { self.list.append(std.heap.page_allocator, x) catch {}; }
        \\    fn outer(self: *T) void { self.grow(1); }
        \\};
    ;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var cache = try FileCache.init(gpa, &tree);
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
        \\    pub fn add(self: *Xf20Grower, x: u32) void { self.list.append(std.heap.page_allocator, x) catch {}; }
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
    const project_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(project_root);
    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{project_root} });
    defer pc.deinit();
    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&pc, from_path);
    try cache.resolveTransitiveTakes();
    // Deterministic since the #27 @import-fallback fix; `add` grows a
    // collection in the imported file, so `run` inherits may_grow.
    const s = (try cache.summaryByName("run")).?;
    try std.testing.expect(s.may_grow_collections);
}

test "qualified imports distinguish identical type and method names" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "owner.zig", .data =
        \\pub const Node = struct {
        \\    pub fn kill(self: *Node, allocator: anytype) void { allocator.destroy(self); }
        \\};
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "borrower.zig", .data =
        \\pub const Node = struct {
        \\    pub fn kill(self: *Node, allocator: anytype) void { _ = self; _ = allocator; }
        \\};
    });
    const src: [:0]const u8 =
        \\const owned = @import("owner.zig");
        \\const borrowed = @import("borrower.zig");
    ;
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    var project = project_cache_mod.ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
    defer project.deinit();
    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&project, path);
    const owner = (try cache.summaryByMethodCrossFile("owned.Node", "kill")) orelse
        return error.TestUnexpectedResult;
    const borrower = (try cache.summaryByMethodCrossFile("borrowed.Node", "kill")) orelse
        return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(?u32, 0), owner.takes_ownership_of);
    try std.testing.expectEqual(@as(?u32, null), borrower.takes_ownership_of);
    try std.testing.expect((try cache.summaryByMethodCrossFile("Node", "kill")) == null);
}

test "qualified fields retain the defining model through imported wrappers" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "leaf.zig", .data =
        \\pub const Space = struct {
        \\    pub const Item = struct {
        \\        bytes: []const u8,
        \\        pub fn view(self: *const Item) []const u8 { return self.bytes; }
        \\        pub fn kill(self: *Item, allocator: anytype) void { allocator.destroy(self); }
        \\    };
        \\};
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "holder.zig", .data =
        \\const Self = @This();
        \\const leaf = @import("leaf.zig");
        \\item: ?*leaf.Space.Item,
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    var tree = try Ast.parse(gpa,
        \\const Holder = @import("holder.zig");
        \\const Item = struct { pub fn kill(self: *Item, allocator: anytype) void { _ = self; _ = allocator; } };
    , .zig);
    defer tree.deinit(gpa);
    var project = project_cache_mod.ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
    defer project.deinit();
    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();
    cache.setProject(&project, path);
    const holder = cache.findTypeAcrossImports("Holder").?;
    const item = cache.fieldType(holder, "item").?;
    try std.testing.expectEqual(@as(?u32, 0), (try cache.summaryForType(item, "kill")).?.takes_ownership_of);
    for (0..2) |_| {
        const summary = (try cache.summaryForType(item, "view")).?;
        try std.testing.expect(summary.returns == .borrowed_from);
        try std.testing.expectEqual(@as(u32, 0), summary.returns.borrowed_from);
    }
    try std.testing.expectEqual(@as(?u32, null), (try cache.summaryByMethod("Item", "kill")).?.takes_ownership_of);
}

// ── Address-use walk budget ─────────────────────────────────

/// `orelse` nesting inside one expression.  Each level adds one walk
/// frame, so `depth` maps directly onto the walk's frame count.
const max_address_use_frames = FileCache.max_address_use_frames;

fn addressUseSource(gpa: std.mem.Allocator, depth: usize) ![]u8 {
    var text: std.ArrayListUnmanaged(u8) = .empty;
    errdefer text.deinit(gpa);
    try text.appendSlice(gpa, "fn nest() u32 {\n    var v: u32 = 0;\n    v = ");
    for (0..depth) |_| try text.appendSlice(gpa, "0 orelse ");
    try text.appendSlice(gpa, "1;\n    return v;\n}\n");
    return text.toOwnedSlice(gpa);
}

test "FileCache: address-use walk names the frame-depth limit and the function" {
    const gpa = std.testing.allocator;
    const source = try addressUseSource(gpa, max_address_use_frames + 4);
    defer gpa.free(source);
    const src_z = try gpa.dupeSentinel(u8, source, 0);
    defer gpa.free(src_z);
    var tree = try Ast.parse(gpa, src_z, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();

    budget_mod.clear();
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
    const src_z = try gpa.dupeSentinel(u8, source, 0);
    defer gpa.free(src_z);
    var tree = try Ast.parse(gpa, src_z, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();

    budget_mod.clear();
    // Below the cap the walk completes, so the lookup answers normally and
    // leaves no failure record behind.
    _ = try cache.addressUseAt(0);
    try std.testing.expect(budget_mod.peek() == null);
}
