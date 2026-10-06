//! Type resolution engine for zbc — repo-wide deep static analysis.
//!
//! Wraps the extracted type-resolution machinery (DocumentStore +
//! InternPool + Analyser) behind a zbc-shaped API.
//!
//! TypeContext  — long-lived per-thread state.  Holds DocumentStore +
//!                InternPool so stdlib files are parsed and typed once
//!                per thread.  In-place init required (self-referential
//!                pointers).  Never move after init.
//!
//! TypeResolver — per-file state.  Borrows a TypeContext; owns only
//!                the per-file arena and Analyser.

const std = @import("std");
const builtin = @import("builtin");
const Ast = std.zig.Ast;

const DocumentStore = @import("document_store.zig");
const InternPool = @import("intern_pool.zig");
const Analyser = @import("analysis.zig");
const Uri = @import("uri.zig");
const DiagnosticsCollection = @import("diagnostics_collection.zig");
pub const SourcePolicy = @import("source_policy.zig").SourcePolicy;
pub const ParseFailure = @import("source_policy.zig").ParseFailure;
pub const CanonicalPaths = @import("source_policy.zig").CanonicalPaths;
pub const AstIterator = @import("ast.zig").Iterator;

// ── Toolchain discovery ───────────────────────────────────────────────

const ToolchainPaths = struct {
    zig_exe: ?[]const u8 = null,
    zig_lib: ?[]const u8 = null,
    build_runner: ?[]const u8 = null,
};

fn freeToolchain(gpa: std.mem.Allocator, paths: ToolchainPaths) void {
    if (paths.zig_exe) |path| gpa.free(path);
    if (paths.zig_lib) |path| gpa.free(path);
    if (paths.build_runner) |path| gpa.free(path);
}

fn queryToolchain(gpa: std.mem.Allocator, io: std.Io) !ToolchainPaths {
    const output = try runCapture(gpa, io, &.{ "zig", "env" });
    defer gpa.free(output);
    return parseToolchainEnv(gpa, output);
}

fn parseToolchainEnv(gpa: std.mem.Allocator, output: []const u8) !ToolchainPaths {
    const Environment = struct { zig_exe: []const u8, lib_dir: []const u8, version: []const u8 };
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const temporary = arena.allocator();
    const source = std.mem.trim(u8, output, &std.ascii.whitespace);
    const environment = if (std.mem.startsWith(u8, source, ".{"))
        try std.zon.parse.fromSliceAlloc(
            Environment,
            temporary,
            try temporary.dupeSentinel(u8, source, 0),
            null,
            .{ .ignore_unknown_fields = true },
        )
    else
        try std.json.parseFromSliceLeaky(Environment, temporary, source, .{ .ignore_unknown_fields = true });
    if (environment.zig_exe.len == 0 or environment.lib_dir.len == 0) return error.NotFound;
    if (!std.mem.eql(u8, environment.version, builtin.zig_version_string)) return error.IncompatibleZigVersion;
    const executable = try gpa.dupe(u8, environment.zig_exe);
    errdefer gpa.free(executable);
    return .{ .zig_exe = executable, .zig_lib = try gpa.dupe(u8, environment.lib_dir) };
}

fn runCapture(gpa: std.mem.Allocator, io: std.Io, argv: []const []const u8) ![]u8 {
    const result = std.process.run(gpa, io, .{ .argv = argv }) catch return error.NotFound;
    defer gpa.free(result.stderr);
    switch (result.term) {
        .exited => |code| if (code != 0) {
            gpa.free(result.stdout);
            return error.NotFound;
        },
        else => {
            gpa.free(result.stdout);
            return error.NotFound;
        },
    }
    if (result.stdout.len == 0) {
        gpa.free(result.stdout);
        return error.NotFound;
    }
    return result.stdout;
}

// ── TypeContext ───────────────────────────────────────────────────────

/// Long-lived per-thread type-resolution state.  The DocumentStore
/// and InternPool persist across files processed by the same thread,
/// so stdlib is parsed and its types interned once per thread.
///
/// In-place init required: self-referential pointers
/// (store.config.environ_map → &self.environ_map,
///  store.diagnostics_collection → &self.diagnostics).
/// Never move after init.
pub const TypeContext = struct {
    gpa: std.mem.Allocator,
    ip: InternPool,
    diagnostics: DiagnosticsCollection,
    environ_map: std.process.Environ.Map,
    store: DocumentStore,
    toolchain: ToolchainPaths,

    pub fn init(self: *TypeContext, gpa: std.mem.Allocator, io: std.Io) !void {
        self.gpa = gpa;

        self.ip = try InternPool.init(io, gpa);
        errdefer self.ip.deinit(gpa);

        self.diagnostics = .{ .io = io, .allocator = gpa };
        self.environ_map = .init(gpa);

        self.toolchain = try queryToolchain(gpa, io);
        errdefer freeToolchain(gpa, self.toolchain);
        const tc = self.toolchain;
        const zig_lib: ?std.Build.Cache.Directory = if (tc.zig_lib) |p|
            .{ .path = p, .handle = .cwd() }
        else
            null;

        self.store = .{
            .io = io,
            .allocator = gpa,
            .config = .{
                .environ_map = &self.environ_map,
                .zig_exe_path = tc.zig_exe,
                .zig_lib_dir = zig_lib,
                .build_runner_path = tc.build_runner,
                .builtin_path = null,
                .global_cache_dir = null,
                .wasi_preopens = {},
            },
            .diagnostics_collection = &self.diagnostics,
        };
    }

    /// Borrow a canonical path whose identity is fixed for this context.
    pub fn canonicalPath(self: *TypeContext, path: []const u8) ![]const u8 {
        return self.store.canonical_paths.resolve(self.gpa, self.store.io, path);
    }

    /// Borrow one immutable document. The caller supplies an absolute path.
    pub fn sourceHandle(self: *TypeContext, file_path: []const u8) !*DocumentStore.Handle {
        std.debug.assert(std.fs.path.isAbsolute(file_path));
        const uri: Uri = try .fromPath(self.gpa, file_path);
        defer uri.deinit(self.gpa);
        return (try self.store.getOrLoadHandle(uri)) orelse
            return self.store.source_failure orelse error.SourceExcluded;
    }

    pub fn deinit(self: *TypeContext) void {
        self.store.deinit();
        self.diagnostics.deinit();
        self.ip.deinit(self.gpa);
        self.environ_map.deinit();
        freeToolchain(self.gpa, self.toolchain);
    }
};

// ── TypeResolver ─────────────────────────────────────────────────────

/// Per-file type resolver.  Borrows a TypeContext (DocumentStore +
/// InternPool).  Per-file documents stay open for the thread's lifetime
/// so InternPool entries referencing them remain valid.
pub const TypeResolver = struct {
    gpa: std.mem.Allocator,
    ctx: *TypeContext,
    arena: std.heap.ArenaAllocator,
    handle: *DocumentStore.Handle,
    analyser: Analyser,

    pub fn init(
        self: *TypeResolver,
        ctx: *TypeContext,
        gpa: std.mem.Allocator,
        file_path: []const u8,
        source: ?[:0]const u8,
    ) !void {
        self.gpa = gpa;
        self.ctx = ctx;
        self.arena = std.heap.ArenaAllocator.init(gpa);
        errdefer self.arena.deinit();

        const aa = self.arena.allocator();
        const abs_path: []const u8 = if (std.fs.path.isAbsolute(file_path)) file_path else blk: {
            var buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
            const len = try std.Io.Dir.cwd().realPathFile(ctx.store.io, ".", &buffer);
            break :blk try std.fs.path.resolve(aa, &.{ buffer[0..len], file_path });
        };
        const handle_uri: Uri = try .fromPath(aa, abs_path);
        if (source) |text| {
            self.handle = ctx.store.getHandle(handle_uri) orelse blk: {
                try ctx.store.openLspSyncedDocument(handle_uri, text);
                break :blk ctx.store.getHandle(handle_uri) orelse
                    return ctx.store.source_failure orelse error.HandleMissing;
            };
            if (!std.mem.eql(u8, self.handle.tree.source, text)) return error.SourceSnapshotChanged;
        } else {
            self.handle = (try ctx.store.getOrLoadHandle(handle_uri)) orelse
                return ctx.store.source_failure orelse error.SourceExcluded;
        }

        self.analyser = Analyser.init(
            gpa,
            self.arena.allocator(),
            &ctx.store,
            &ctx.ip,
            self.handle,
        );
    }

    pub fn deinit(self: *TypeResolver) void {
        self.analyser.deinit();
        self.arena.deinit();
    }

    fn normalizedType(self: *TypeResolver, value: Analyser.Type) !?Analyser.Type {
        switch (value.data) {
            .type_parameter, .anytype_parameter, .either, .compile_error => return null,
            else => {},
        }
        const ty = if (value.is_type_val) value else try value.typeOf(&self.analyser);
        if (ty.data == .ip_index) {
            const index = ty.ipIndex() orelse return null;
            if (self.ctx.ip.zigTypeTag(index) == null) return null;
        }
        return ty;
    }

    fn typeOfNode(self: *TypeResolver, node: Ast.Node.Index) !?Analyser.Type {
        const value = (try self.analyser.resolveTypeOfNode(.of(node, self.handle))) orelse return null;
        return self.normalizedType(value);
    }

    pub const FunctionReference = struct {
        tree: *const Ast,
        fn_token: Ast.TokenIndex,
    };

    pub fn functionReference(self: *TypeResolver, node: Ast.Node.Index) !?FunctionReference {
        const value = (try self.analyser.resolveTypeOfNode(.of(node, self.handle))) orelse return null;
        const callable = (try self.analyser.resolveFuncProtoOfCallable(value)) orelse return null;
        if (callable.is_type_val) return null;
        const function = callable.data.function;
        return .{ .tree = &function.handle.tree, .fn_token = function.fn_token };
    }

    pub const TypeParameterReference = struct {
        tree: *const Ast,
        token: Ast.TokenIndex,
    };

    pub fn typeParameterReference(self: *TypeResolver, node: Ast.Node.Index) !?TypeParameterReference {
        const value = (try self.analyser.resolveTypeOfNode(.of(node, self.handle))) orelse return null;
        const parameter = switch (value.data) {
            .type_parameter => |reference| reference,
            else => return null,
        };
        return .{ .tree = &parameter.handle.tree, .token = parameter.token };
    }

    /// Map a declared parameter to its actual argument, including method receivers.
    pub fn callArgument(self: *TypeResolver, node: Ast.Node.Index, parameter: usize) !?Ast.Node.Index {
        const tree = &self.handle.tree;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse return null;
        const value = (try self.analyser.resolveTypeOfNode(.of(call.ast.fn_expr, self.handle))) orelse return null;
        const callable = (try self.analyser.resolveFuncProtoOfCallable(value)) orelse return null;
        if (callable.is_type_val or callable.data.function.has_varargs) return null;
        const receiver = try self.analyser.isInstanceCall(self.handle, call, callable);
        const offset: usize = @intFromBool(receiver);
        if (call.ast.params.len + offset != callable.data.function.parameters.len) return null;
        if (receiver and parameter == 0) return tree.nodeData(call.ast.fn_expr).node_and_token[0];
        if (parameter < offset or parameter - offset >= call.ast.params.len) return null;
        return call.ast.params[parameter - offset];
    }

    pub fn externUnionFloatFieldBits(self: *TypeResolver, node: Ast.Node.Index, field_name: []const u8) !?u16 {
        const ty = (try self.typeOfNode(node)) orelse return null;
        if (self.typeTag(ty) != .@"union" or ty.data != .container) return null;
        const scope = ty.data.container.scope_handle;
        const tree = &scope.handle.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const container = tree.fullContainerDecl(&buffer, scope.toNode()) orelse return null;
        if (tree.tokenTag(container.layout_token orelse return null) != .keyword_extern) return null;
        const declaration = (try Analyser.lookupSymbolContainer(ty, field_name, .field)) orelse return null;
        const value = (try declaration.resolveType(&self.analyser)) orelse return null;
        const field_type = (try self.normalizedType(value)) orelse return null;
        if (self.typeTag(field_type) != .float) return null;
        return self.ctx.ip.floatBits(field_type.ipIndex() orelse return null, builtin.target);
    }

    fn typeTag(self: *TypeResolver, ty: Analyser.Type) ?std.builtin.TypeId {
        std.debug.assert(ty.is_type_val);
        return switch (ty.data) {
            .ip_index => self.ctx.ip.zigTypeTag(ty.ipIndex() orelse return null),
            .pointer => .pointer,
            .array => .array,
            .optional => .optional,
            .error_union => .error_union,
            .tuple => .@"struct",
            .function => .@"fn",
            .union_tag => .@"enum",
            .container => |container| blk: {
                if (container.scope_handle.scope == .root) break :blk .@"struct";
                const tree = &container.scope_handle.handle.tree;
                break :blk switch (tree.tokenTag(tree.nodeMainToken(container.scope_handle.toNode()))) {
                    .keyword_struct => .@"struct",
                    .keyword_enum => .@"enum",
                    .keyword_union => .@"union",
                    .keyword_opaque => .@"opaque",
                    else => null,
                };
            },
            .type_parameter, .anytype_parameter, .either, .compile_error => null,
        };
    }

    fn childType(self: *TypeResolver, ty: Analyser.Type) ?Analyser.Type {
        std.debug.assert(ty.is_type_val);
        return switch (ty.data) {
            .pointer => |info| info.elem_ty.*,
            .array => |info| info.elem_ty.*,
            .optional => |payload| payload.*,
            .ip_index => blk: {
                const index = ty.ipIndex() orelse return null;
                const child = switch (self.ctx.ip.indexToKey(index)) {
                    .pointer_type => |info| info.elem_type,
                    .array_type => |info| info.child,
                    .optional_type => |info| info.payload_type,
                    else => return null,
                };
                break :blk Analyser.Type.fromIP(&self.analyser, .type_type, child);
            },
            else => null,
        };
    }

    fn pointerSize(self: *TypeResolver, ty: Analyser.Type) ?std.builtin.Type.Pointer.Size {
        std.debug.assert(ty.is_type_val);
        return switch (ty.data) {
            .pointer => |info| info.size,
            .ip_index => switch (self.ctx.ip.indexToKey(ty.ipIndex() orelse return null)) {
                .pointer_type => |info| info.flags.size,
                else => null,
            },
            else => null,
        };
    }

    fn containerOfNode(self: *TypeResolver, node: Ast.Node.Index) !?Analyser.Type.Data.Container {
        var ty = (try self.typeOfNode(node)) orelse return null;
        for (0..32) |_| {
            if (ty.data == .container) return ty.data.container;
            ty = (try self.normalizedType(self.childType(ty) orelse return null)) orelse return null;
        }
        return null;
    }

    /// Declaration name within the defining document, not a dispatch identity.
    pub fn typeNameOfNode(self: *TypeResolver, node: Ast.Node.Index) !?[]const u8 {
        const container = (try self.containerOfNode(node)) orelse return null;
        return containerName(self.arena.allocator(), container);
    }

    pub fn isStdAllocator(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const container = (try self.containerOfNode(node)) orelse return null;
        if (container.scope_handle.scope != .root) return false;
        const library = self.ctx.toolchain.zig_lib orelse return null;
        const path = try container.scope_handle.handle.uri.toFsPath(self.arena.allocator());
        const base = std.mem.trimEnd(u8, library, std.fs.path.sep_str);
        const suffix = "/std/mem/Allocator.zig";
        return path.len == base.len + suffix.len and
            std.mem.startsWith(u8, path, base) and std.mem.endsWith(u8, path, suffix);
    }

    /// Name usable for dispatch from this file. Never substitute a foreign
    /// declaration's leaf name for an unrelated local declaration.
    pub fn typeReferenceOfNode(self: *TypeResolver, node: Ast.Node.Index) !?[]const u8 {
        const container = (try self.containerOfNode(node)) orelse return null;
        const name = (try containerName(self.arena.allocator(), container)) orelse return null;
        if (container.scope_handle.handle == self.handle) return name;
        const tree = &self.handle.tree;
        for (tree.rootDecls()) |declaration| {
            const variable = tree.fullVarDecl(declaration) orelse continue;
            const initializer = variable.ast.init_node.unwrap() orelse continue;
            var buffer: [2]Ast.Node.Index = undefined;
            const args = tree.builtinCallParams(&buffer, initializer) orelse continue;
            if (args.len != 1) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(initializer)), "@import")) continue;
            if (tree.nodeTag(args[0]) != .string_literal) continue;
            const literal = tree.tokenSlice(tree.nodeMainToken(args[0]));
            const path = try std.zig.string_literal.parseAlloc(self.gpa, literal);
            defer self.gpa.free(path);
            var target = try self.ctx.store.uriFromImportStr(self.gpa, self.handle, path);
            defer target.deinit(self.gpa);
            if (target != .one or !target.one.eql(container.scope_handle.handle.uri)) continue;
            const alias = tree.tokenSlice(variable.ast.mut_token + 1);
            if (container.scope_handle.scope == .root) return alias;
            return try std.fmt.allocPrint(self.arena.allocator(), "{s}.{s}", .{ alias, name });
        }
        return null;
    }

    /// Predicates return null when the type is unresolved, not a proved false.
    pub fn resolvedTypeIsPointer(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.typeOfNode(node)) orelse return null;
        return (self.typeTag(ty) orelse return null) == .pointer;
    }

    pub fn optionalPayloadIsPointer(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.typeOfNode(node)) orelse return null;
        if ((self.typeTag(ty) orelse return null) != .optional) return false;
        const child = (try self.normalizedType(self.childType(ty) orelse return null)) orelse return null;
        return (self.typeTag(child) orelse return null) == .pointer;
    }

    pub fn isOptionalType(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.typeOfNode(node)) orelse return null;
        return (self.typeTag(ty) orelse return null) == .optional;
    }

    pub fn isRawSinglePointerType(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.typeOfNode(node)) orelse return null;
        if ((self.typeTag(ty) orelse return null) != .pointer) return false;
        return (self.pointerSize(ty) orelse return null) == .one;
    }

    pub fn typeRefIsPointerLike(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.typeOfNode(node)) orelse return null;
        const tag = self.typeTag(ty) orelse return null;
        return tag == .pointer or tag == .optional;
    }

    pub fn isBoolType(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.typeOfNode(node)) orelse return null;
        return self.typeTag(ty) == .bool;
    }

    pub fn isFloatType(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.typeOfNode(node)) orelse return null;
        const tag = self.typeTag(ty) orelse return null;
        return tag == .float or tag == .comptime_float;
    }

    pub fn floatBits(self: *TypeResolver, node: Ast.Node.Index) !?u16 {
        const ty = (try self.typeOfNode(node)) orelse return null;
        const tag = self.typeTag(ty) orelse return null;
        if (tag != .float and tag != .comptime_float) return null;
        return self.ctx.ip.floatBits(ty.ipIndex() orelse return null, builtin.target);
    }

    pub fn isEnumType(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        var ty = (try self.typeOfNode(node)) orelse return null;
        for (0..32) |_| {
            const tag = self.typeTag(ty) orelse return null;
            if (tag != .optional) return tag == .@"enum";
            ty = (try self.normalizedType(self.childType(ty) orelse return null)) orelse return null;
        }
        return null;
    }

    pub const IntInfo = struct { signed: bool, bits: u16 };

    /// Signedness and bit-width of `node`'s type when it resolves to an integer
    /// type, else null.  Used e.g. to tell signed subtraction (well-defined,
    /// can't "wrap to a huge value") from unsigned underflow.
    pub fn intInfo(self: *TypeResolver, node: Ast.Node.Index) !?IntInfo {
        const ty = (try self.typeOfNode(node)) orelse return null;
        if ((self.typeTag(ty) orelse return null) != .int) return null;
        const index = ty.ipIndex() orelse return null;
        const info = self.ctx.ip.intInfo(index, builtin.target);
        return .{ .signed = info.signedness == .signed, .bits = info.bits };
    }

    /// For `x.ptr` where `x`'s type resolves to a slice / many-pointer:
    /// returns whether the element type is byte-sized (1-byte alignment —
    /// `u8`/`i8`/`bool`/≤8-bit ints), i.e. `x` is a genuine byte slice whose
    /// `.ptr` is only 1-aligned (the `@alignCast`-on-byte-slice bug class).
    ///   true  → byte slice (align 1) — the cast may misalign.
    ///   false → element is wider (u16+/pointer) → `.ptr` already >1-aligned,
    ///           NOT a byte slice; this rule does not apply.
    ///   null  → unresolved, not a slice, or element of unknown alignment
    ///           (struct/array) — caller should fall back to syntax.
    pub fn sourcePtrElemByteSized(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.typeOfNode(node)) orelse return null;
        if ((self.pointerSize(ty) orelse return null) == .one) return null;
        const child = (try self.normalizedType(self.childType(ty) orelse return null)) orelse return null;
        const tag = self.typeTag(child) orelse return null;
        if (tag == .pointer) return false;
        if (tag == .bool) return true;
        if (tag != .int) return null;
        return self.ctx.ip.intInfo(child.ipIndex() orelse return null, builtin.target).bits <= 8;
    }

    /// Returns the compile-time element count of `node`'s type when it is a
    /// fixed-size array `[N]T`, a single-pointer to a fixed array `*[N]T` /
    /// `*const [N]T`, or an IP-backed array type.  Returns null for runtime
    /// slices (`[]T`), many-pointers, or any type whose length is not a
    /// compile-time constant.
    ///
    /// Sound for bounds reasoning: a non-null result is an exact, compiler-
    /// guaranteed length, so `arr[offset..]` is in-bounds iff offset <= N.
    pub fn fixedArrayLen(self: *TypeResolver, node: Ast.Node.Index) !?u64 {
        var ty = (try self.typeOfNode(node)) orelse return null;
        if (self.pointerSize(ty)) |size| {
            if (size != .one) return null;
            ty = (try self.normalizedType(self.childType(ty) orelse return null)) orelse return null;
        }
        return switch (ty.data) {
            .array => |info| info.elem_count,
            .ip_index => switch (self.ctx.ip.indexToKey(ty.ipIndex() orelse return null)) {
                .array_type => |info| info.len,
                else => null,
            },
            else => null,
        };
    }

    /// If `node` resolves to a comptime-known non-negative integer, return its
    /// value, else null.  A comptime-known index can never cause a *runtime*
    /// underflow/OOB: `CONST - 1` with `CONST == 0`, or an out-of-range constant
    /// subscript, is a COMPILE error (never ships).  So any successful
    /// resolution here means the access is comptime-verified safe.
    pub fn comptimeIntValue(self: *TypeResolver, node: Ast.Node.Index) !?u64 {
        return self.analyser.resolveIntegerLiteral(u64, .of(node, self.handle));
    }

};

fn containerName(arena: std.mem.Allocator, container: Analyser.Type.Data.Container) !?[]const u8 {
    const handle = container.scope_handle.handle;
    const tree = &handle.tree;
    if (container.scope_handle.scope == .root) {
        const path = try handle.uri.toFsPath(arena);
        const stem = std.fs.path.stem(path);
        return if (stem.len == 0) null else stem;
    }
    const scopes = try handle.getDocumentScope();
    var current = container.scope_handle.scope;
    var parts: [32][]const u8 = undefined;
    var count: usize = 0;
    while (current != .root and count < parts.len) {
        const node = scopes.getScopeAstNode(current) orelse return null;
        const parent = scopes.getScopeParent(current).unwrap() orelse return null;
        const name = declaration: {
            for (scopes.getScopeDeclarationsConst(parent)) |index| {
                const entry = scopes.declarations.get(@intFromEnum(index));
                const decl_node = switch (entry) {
                    .ast_node => |value| value,
                    else => continue,
                };
                const variable = tree.fullVarDecl(decl_node) orelse continue;
                if (variable.ast.init_node.unwrap() == node) {
                    break :declaration tree.tokenSlice(variable.ast.mut_token + 1);
                }
            }
            return null;
        };
        parts[count] = name;
        count += 1;
        if (scopes.getScopeTag(parent) != .container) return null;
        current = parent;
    }
    if (current != .root or count == 0) return null;
    if (count == 1) return parts[0];
    std.mem.reverse([]const u8, parts[0..count]);
    return try std.mem.join(arena, ".", parts[0..count]);
}

test "toolchain environment parses JSON paths and ignores extra fields" {
    const gpa = std.testing.allocator;
    const paths = try parseToolchainEnv(gpa,
        \\{"zig_exe":"/opt/zig/bin/zig","lib_dir":"/opt/zig/lib","version":"0.16.0","env":{}}
    );
    defer gpa.free(paths.zig_exe.?);
    defer gpa.free(paths.zig_lib.?);
    try std.testing.expectEqualStrings("/opt/zig/bin/zig", paths.zig_exe.?);
    try std.testing.expectEqualStrings("/opt/zig/lib", paths.zig_lib.?);
}

test "toolchain environment parses ZON paths and escaped characters" {
    const gpa = std.testing.allocator;
    const paths = try parseToolchainEnv(gpa,
        \\.{ .zig_exe = "/opt/zig/bin/zig", .lib_dir = "/opt/zig \"dev\"/lib", .version = "0.16.0", .env = .{} }
    );
    defer gpa.free(paths.zig_exe.?);
    defer gpa.free(paths.zig_lib.?);
    try std.testing.expectEqualStrings("/opt/zig/bin/zig", paths.zig_exe.?);
    try std.testing.expectEqualStrings("/opt/zig \"dev\"/lib", paths.zig_lib.?);
}

test "toolchain environment rejects missing and empty library paths" {
    const gpa = std.testing.allocator;
    try std.testing.expectError(error.MissingField, parseToolchainEnv(gpa,
        \\{"zig_exe":"/opt/zig/bin/zig"}
    ));
    try std.testing.expectError(error.NotFound, parseToolchainEnv(gpa,
        \\.{ .zig_exe = "/opt/zig/bin/zig", .lib_dir = "", .version = "0.16.0" }
    ));
}

test "stable double pointer parameters resolve as pointers" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-pointer-regression.zig",
        "pub fn borrow(p: **u8) **u8 { return p; }");
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    var index: u32 = 1;
    while (index < tree.nodes.len) : (index += 1) {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeTag(node) != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "p")) continue;
        try std.testing.expect((try resolver.resolvedTypeIsPointer(node)) == true);
        return;
    }
    return error.TestUnexpectedResult;
}

test "toolchain environment rejects a different compiler dialect" {
    try std.testing.expectError(error.IncompatibleZigVersion, parseToolchainEnv(std.testing.allocator,
        \\{"zig_exe":"/opt/zig/bin/zig","lib_dir":"/opt/zig/lib","version":"0.0.0-incompatible"}
    ));
}

fn testIdentifier(tree: *const Ast, name: []const u8) !Ast.Node.Index {
    for (1..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeTag(node) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name)) return node;
    }
    return error.TestUnexpectedResult;
}

test "type predicates classify denoted types and runtime values alike" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-type-normalization.zig",
        \\const Maybe = ?u8;
        \\const Pointer = *u8;
        \\const Float = f32;
        \\const Integer = u16;
        \\const Array = [7]u8;
        \\const Tag = enum { a, b };
        \\const Box = struct {};
        \\fn observe(optional: Maybe, pointer: Pointer, float: Float,
        \\           integer: Integer, array: Array, tag: ?Tag, box: ?*Box) void {
        \\    _ = optional; _ = pointer; _ = float; _ = integer;
        \\    _ = array; _ = tag; _ = box;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    for ([_][]const u8{ "Maybe", "optional" }) |name| {
        const actual: ?bool = try resolver.isOptionalType(try testIdentifier(tree, name));
        try std.testing.expectEqual(@as(?bool, true), actual);
    }
    for ([_][]const u8{ "Pointer", "pointer" }) |name| {
        const node = try testIdentifier(tree, name);
        try std.testing.expectEqual(@as(?bool, true), @as(?bool, try resolver.resolvedTypeIsPointer(node)));
        try std.testing.expectEqual(@as(?bool, true), @as(?bool, try resolver.isRawSinglePointerType(node)));
    }
    for ([_][]const u8{ "Float", "float" }) |name| {
        try std.testing.expectEqual(@as(?bool, true), @as(?bool, try resolver.isFloatType(try testIdentifier(tree, name))));
        try std.testing.expectEqual(@as(?u16, 32), try resolver.floatBits(try testIdentifier(tree, name)));
    }
    for ([_][]const u8{ "Integer", "integer" }) |name| {
        const info = (try resolver.intInfo(try testIdentifier(tree, name))).?;
        try std.testing.expectEqual(@as(u16, 16), info.bits);
        try std.testing.expect(!info.signed);
    }
    for ([_][]const u8{ "Array", "array" }) |name| {
        try std.testing.expectEqual(@as(?u64, 7), try resolver.fixedArrayLen(try testIdentifier(tree, name)));
    }
    for ([_][]const u8{ "Tag", "tag" }) |name| {
        try std.testing.expectEqual(@as(?bool, true), @as(?bool, try resolver.isEnumType(try testIdentifier(tree, name))));
    }
    try std.testing.expectEqualStrings("Box", (try resolver.typeNameOfNode(try testIdentifier(tree, "box"))).?);
    try std.testing.expectEqual(@as(?bool, false), @as(?bool, try resolver.isOptionalType(try testIdentifier(tree, "integer"))));
}

test "array repetition retains its compiler-derived element count" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-repetition-type.zig",
        \\const repeated = [_]u8{ 1, 2 } ** 3;
        \\fn observe() void { _ = repeated; }
    );
    defer resolver.deinit();
    try std.testing.expectEqual(@as(?u64, 6), try resolver.fixedArrayLen(try testIdentifier(&resolver.handle.tree, "repeated")));
}

test "type predicates retain unresolved and depth-limited answers" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const source = try std.fmt.allocPrintSentinel(gpa,
        "const Tag = enum {{ a }}; const Deep = {s}Tag;\n" ++
        "fn observe(deep: Deep, unknown: anytype, pptr: **[7]u8) void {{ _ = deep; _ = unknown; _ = pptr; }}",
        .{"?" ** 40}, 0);
    defer gpa.free(source);
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "virtual-type-boundary.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    const unknown = try testIdentifier(tree, "unknown");
    try std.testing.expectEqual(@as(?bool, null), try resolver.isOptionalType(unknown));
    try std.testing.expectEqual(@as(?bool, null), try resolver.resolvedTypeIsPointer(unknown));
    try std.testing.expectEqual(@as(?bool, null), try resolver.isFloatType(unknown));
    try std.testing.expectEqual(@as(?u16, null), try resolver.floatBits(unknown));
    try std.testing.expectEqual(@as(?bool, null), try resolver.isEnumType(unknown));
    const deep = try testIdentifier(tree, "deep");
    try std.testing.expectEqual(@as(?bool, true), try resolver.isOptionalType(deep));
    try std.testing.expectEqual(@as(?bool, null), try resolver.isEnumType(deep));
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(deep));
    try std.testing.expectEqual(@as(?u64, null), try resolver.fixedArrayLen(try testIdentifier(tree, "pptr")));
}

test "container names retain nested declaration qualification" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-qualified-containers.zig",
        \\const Box = struct {};
        \\const Namespace = struct { const Box = struct {}; };
        \\fn observe(value: ?*Namespace.Box) void { _ = value; }
    );
    defer resolver.deinit();
    try std.testing.expectEqualStrings("Namespace.Box",
        (try resolver.typeNameOfNode(try testIdentifier(&resolver.handle.tree, "value"))).?);
}

test "imported containers have distinct display names and dispatch references" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "remote.zig", .data =
        \\pub const Namespace = struct { pub const Box = struct {}; };
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    var context: TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, path,
        \\const remote = @import("remote.zig");
        \\const Box = struct {};
        \\fn observe(value: ?*remote.Namespace.Box) void { _ = value; }
    );
    defer resolver.deinit();
    const node = try testIdentifier(&resolver.handle.tree, "value");
    try std.testing.expectEqualStrings("Namespace.Box", (try resolver.typeNameOfNode(node)).?);
    try std.testing.expectEqualStrings("remote.Namespace.Box", (try resolver.typeReferenceOfNode(node)).?);
}

test "constant queries do not use mutable initializers as value facts" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-constant-mutation.zig",
        \\const known: usize = 4;
        \\const constants = struct { const limit = 4; };
        \\const State = struct { count: usize = 4 };
        \\fn observe(state: *State) void {
        \\    var changed: usize = 1;
        \\    changed = 0;
        \\    _ = changed;
        \\    _ = known;
        \\    _ = constants.limit;
        \\    _ = state.count;
        \\}
    );
    defer resolver.deinit();
    try std.testing.expectEqual(@as(?u64, null), try resolver.comptimeIntValue(try testIdentifier(&resolver.handle.tree, "changed")));
    try std.testing.expectEqual(@as(?u64, 4), try resolver.comptimeIntValue(try testIdentifier(&resolver.handle.tree, "known")));
    for (resolver.handle.tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const name = resolver.handle.tree.tokenSlice(resolver.handle.tree.nodeData(node).node_and_token[1]);
        const expected: ?u64 = if (std.mem.eql(u8, name, "limit")) 4 else null;
        try std.testing.expectEqual(std.mem.eql(u8, name, "limit"), (try resolver.intInfo(node)) == null);
        try std.testing.expectEqual(expected, try resolver.comptimeIntValue(node));
    }
}

test "numeric conversions resolve their declared and returned result types" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-numeric-context.zig",
        \\fn convert(value: f64, number: u64) u8 {
        \\    const integer: u16 = @intCast(number);
        \\    const small: f32 = @floatFromInt(integer);
        \\    const wide: f64 = @floatCast(small);
        \\    const bits: u64 = @bitCast(wide);
        \\    _ = bits;
        \\    return @intFromFloat(value);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    for ([_]struct { name: []const u8, bits: u16, float: bool }{
        .{ .name = "@intCast", .bits = 16, .float = false },
        .{ .name = "@floatFromInt", .bits = 32, .float = true },
        .{ .name = "@floatCast", .bits = 64, .float = true },
        .{ .name = "@bitCast", .bits = 64, .float = false },
        .{ .name = "@intFromFloat", .bits = 8, .float = false },
    }) |expected| {
        const node = for (tree.nodes.items(.tag), 0..) |tag, index| {
            if (tag != .builtin_call_two and tag != .builtin_call_two_comma) continue;
            const candidate: Ast.Node.Index = @enumFromInt(index);
            if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(candidate)), expected.name)) break candidate;
        } else return error.MissingConversion;
        if (expected.float) {
            try std.testing.expectEqual(@as(?u16, expected.bits), try resolver.floatBits(node));
        } else {
            const info = (try resolver.intInfo(node)) orelse return error.MissingIntegerType;
            try std.testing.expect(!info.signed);
            try std.testing.expectEqual(expected.bits, info.bits);
        }
    }
}

test "failed relative imports never resolve a different file beside the caller" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.createDirPath(io, "sub");
    try tmp.dir.writeFile(io, .{ .sub_path = "sub/package.zig", .data =
        \\pub const Target = @import("types.zig").Target;
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "sub/types.zig", .data = "pub const Target = struct { value: ; };" });
    try tmp.dir.writeFile(io, .{ .sub_path = "types.zig", .data = "pub const Target = struct { value: u8 };" });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    var context: TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, path,
        \\const package = @import("sub/package.zig");
        \\fn inspect(value: package.Target) void { _ = value; }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    const field = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .field_access) break @as(Ast.Node.Index, @enumFromInt(index));
    } else return error.MissingFieldAccess;
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(field));
    try std.testing.expectEqual(@as(?anyerror, error.ImportInvalidSyntax), context.store.source_failure);
}
