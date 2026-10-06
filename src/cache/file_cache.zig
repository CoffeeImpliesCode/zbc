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
    /// Lazily-built sorted table of byte offsets where each source line
    /// starts.  Shared across all function analyses in this file so
    /// cfg_builder's buildLineOffsets() runs at most once per file.
    line_offsets: []const u32 = &.{},
    address_uses: ?AddressUseMap = null,
    call_index: ?CallIndex = null,
    closed_callers: std.AutoHashMapUnmanaged(Ast.Node.Index, ?[]const Ast.Node.Index) = .empty,
    max_float_bits: std.AutoHashMapUnmanaged(Ast.TokenIndex, u16) = .empty,

    const CallIndex = struct {
        by_callee: std.AutoHashMapUnmanaged(Ast.Node.Index, Ast.Node.Index) = .empty,
        reflective: bool = false,
    };

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
        errdefer index.by_callee.deinit(self.gpa);
        for (self.tree.nodes.items(.tag), 0..) |tag, raw_node| {
            const node: Ast.Node.Index = @enumFromInt(raw_node);
            var buffer: [1]Ast.Node.Index = undefined;
            if (self.tree.fullCall(&buffer, node)) |call| {
                try index.by_callee.put(self.gpa, call.ast.fn_expr, node);
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
            const call = index.by_callee.get(node) orelse return null;
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
        var frames: [256]Frame = undefined;
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
            if (visited == self.tree.nodes.len) return error.AnalysisBudgetExceeded;
            visited += 1;
            const in_argument = frame.in_argument or (frame.call_children and !frame.first_child);
            frame.first_child = false;
            const tag = self.tree.nodeTag(node);
            if (tag == .address_of) {
                if (tokens.rootIdentifier(self.tree, self.tree.nodeData(node).node)) |operand| {
                    try result.put(self.gpa, self.tree.nodeMainToken(operand), .{ .may_write = in_argument });
                }
            }
            if (depth == frames.len) return error.AnalysisBudgetExceeded;
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

    /// True for floating-point types; null if type resolution is unavailable.
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
        const path = if (owner.model.tree == self.tree) self.file_path else
            (self.project orelse return null).pathForModel(owner.model);
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
        if (self.call_index) |*index| index.by_callee.deinit(self.gpa);
        var callers = self.closed_callers.valueIterator();
        while (callers.next()) |calls| if (calls.*) |owned| self.gpa.free(owned);
        self.closed_callers.deinit(self.gpa);
        self.max_float_bits.deinit(self.gpa);
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
                owner.qualified_name else null;
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
            return .{
                .returns = cached.returns,
                .takes_ownership_of = cached.takes,
                .may_grow_collections = cached.may_grow,
                .may_invoke_gc = cached.may_gc,
                .may_run_on_any_thread = cached.may_thread,
            };
        }
        var foreign = FileCache.init(self.gpa, resolved.tree);
        defer foreign.deinit();
        try foreign.resolveTransitiveTakes();
        const summary = try foreign.summaryOf(proto, body);
        const result: fn_summary.FnSummary = .{
            .returns = summary.returns,
            .takes_ownership_of = summary.takes_ownership_of,
            .may_grow_collections = summary.may_grow_collections,
            .may_invoke_gc = summary.may_invoke_gc,
            .may_run_on_any_thread = summary.may_run_on_any_thread,
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
            else pc.modelForModuleImport(from_path, import_path)) catch |err| {
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

    var cache = FileCache.init(gpa, &consumer_tree);
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

    var cache = FileCache.init(gpa, &tree);
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
    var cache = FileCache.init(gpa, &tree);
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
    var cache = FileCache.init(gpa, &tree);
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
    const project_root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(project_root);
    var pc = project_cache_mod.ProjectCache.init(gpa, tio, .{ .roots = &.{project_root} });
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
    var cache = FileCache.init(gpa, &tree);
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
    var cache = FileCache.init(gpa, &tree);
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
