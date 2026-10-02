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

pub const DocumentStore = @import("document_store.zig");
const InternPool = @import("intern_pool.zig");
const Analyser = @import("analysis.zig");
const Uri = @import("uri.zig");
const DiagnosticsCollection = @import("diagnostics_collection.zig");
pub const SourcePolicy = @import("source_policy.zig").SourcePolicy;
pub const ParseFailure = @import("source_policy.zig").ParseFailure;
pub const CanonicalPaths = @import("source_policy.zig").CanonicalPaths;
/// Named-module wiring recovered from `build.zig` without executing it. Shared
/// with the project cache so both read build metadata through one parser.
pub const NamedModuleMap = DocumentStore.NamedModuleMap;
pub const AstIterator = @import("ast.zig").Iterator;
pub const AstWalker = @import("ast.zig").Walker;

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

    /// Bind to a document the store already serves, without reading a
    /// file again.  `handle` is the store's own immutable snapshot of a
    /// file some other document imports, so a resolver opened over it
    /// resolves that document's imports and toolchain sources exactly
    /// as one opened over the file under analysis does.  The store owns
    /// the document and outlives every resolver that borrows it.
    pub fn initBorrowed(
        self: *TypeResolver,
        ctx: *TypeContext,
        gpa: std.mem.Allocator,
        handle: *DocumentStore.Handle,
    ) !void {
        self.gpa = gpa;
        self.ctx = ctx;
        self.arena = std.heap.ArenaAllocator.init(gpa);
        errdefer self.arena.deinit();

        self.handle = handle;
        self.analyser = Analyser.init(
            gpa,
            self.arena.allocator(),
            &ctx.store,
            &ctx.ip,
            handle,
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

    /// How far a peer type's branches are chased before giving up.  A
    /// peer nests only through other peer types, so this only bounds
    /// pathological nesting; it is not an analysis budget.
    const max_peer_depth = 16;

    /// The type of `node` with a peer type narrowed to a single answer.
    ///
    /// `normalizedType` answers null for a peer type because a peer has
    /// no single type of its own.  That is the right answer for a
    /// question about WHICH type it is, and the wrong answer for a
    /// question that only asks whether every branch agrees: a value
    /// produced by `switch (u) { .tag => |p| p, else => return null }`
    /// IS `p`'s type, however the analyser had to spell it.
    fn peeredTypeOfNode(self: *TypeResolver, node: Ast.Node.Index) !?Analyser.Type {
        const value = (try self.analyser.resolveTypeOfNode(.of(node, self.handle))) orelse return null;
        return self.peeredType(value, 0);
    }

    /// Every branch that returns at all must agree.  A `noreturn`
    /// branch produces no value, so it cannot disagree; an unresolved
    /// or disagreeing branch still answers null.
    fn peeredType(self: *TypeResolver, value: Analyser.Type, depth: u32) !?Analyser.Type {
        if (value.data != .either) return self.normalizedType(value);
        if (depth == max_peer_depth) return null;
        var answer: ?Analyser.Type = null;
        for (value.data.either) |entry| {
            const branch: Analyser.Type = .{ .data = entry.type_data, .is_type_val = false };
            const candidate = (try self.peeredType(branch, depth + 1)) orelse return null;
            const tag = self.typeTag(candidate) orelse return null;
            if (tag == .noreturn) continue;
            if (answer) |previous| {
                if ((self.typeTag(previous) orelse return null) != tag) return null;
                continue;
            }
            answer = candidate;
        }
        return answer;
    }

    /// The declaration an expression names: the document that declares
    /// it, and the token its own `fn` keyword carries.  `handle` is that
    /// same document as the store holds it, borrowed — so a caller that
    /// needs the declaration's own source context opens a resolver over
    /// THIS handle instead of reading the name out of a file again.
    /// `tree` stays the document's identity for callers that only
    /// compare which file a declaration lives in.
    pub const FunctionReference = struct {
        tree: *const Ast,
        fn_token: Ast.TokenIndex,
        handle: *DocumentStore.Handle,
    };

    pub fn functionReference(self: *TypeResolver, node: Ast.Node.Index) !?FunctionReference {
        const value = (try self.analyser.resolveTypeOfNode(.of(node, self.handle))) orelse return null;
        const callable = (try self.analyser.resolveFuncProtoOfCallable(value)) orelse return null;
        if (callable.is_type_val) return null;
        const function = callable.data.function;
        return .{
            .tree = &function.handle.tree,
            .fn_token = function.fn_token,
            .handle = function.handle,
        };
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

    /// The declaration a call reaches and the arity this call actually
    /// uses.  `call` points into `buffer` for the fixed-arity call
    /// shapes, so it is valid only while that buffer lives and never
    /// escapes the function that read it.
    const ReachedCall = struct {
        call: Ast.full.Call,
        receiver: bool,
        declared: usize,
    };

    /// Every rule this snapshot applies to decide which declaration a
    /// call reaches: the callee's own type, the variadic rule, whether
    /// the call passes a receiver implicitly, and the arity.  One
    /// place decides them, so `callArgument` and `callArguments` cannot
    /// disagree about which expression a parameter received.
    fn reachedCall(
        self: *TypeResolver,
        buffer: *[1]Ast.Node.Index,
        node: Ast.Node.Index,
    ) !?ReachedCall {
        const tree = &self.handle.tree;
        const call = tree.fullCall(buffer, node) orelse return null;
        const value = (try self.analyser.resolveTypeOfNode(.of(call.ast.fn_expr, self.handle))) orelse return null;
        const callable = (try self.analyser.resolveFuncProtoOfCallable(value)) orelse return null;
        if (callable.is_type_val or callable.data.function.has_varargs) return null;
        const declared = callable.data.function.parameters.len;
        const receiver = try self.analyser.isInstanceCall(self.handle, call, callable);
        if (call.ast.params.len + @intFromBool(receiver) != declared) return null;
        return .{ .call = call, .receiver = receiver, .declared = declared };
    }

    /// Map a declared parameter to its actual argument, including method receivers.
    pub fn callArgument(self: *TypeResolver, node: Ast.Node.Index, parameter: usize) !?Ast.Node.Index {
        var buffer: [1]Ast.Node.Index = undefined;
        return self.callArgumentIn(&buffer, node, parameter);
    }

    /// The expression declared parameter `parameter` received, or null
    /// when this call does not map onto the declaration it reaches — a
    /// variadic callee, an arity it does not have, a callee this
    /// snapshot cannot name.  `buffer` backs the call's own argument
    /// storage for the fixed-arity call shapes, so it must outlive
    /// every node the caller reads back.
    pub fn callArgumentIn(
        self: *TypeResolver,
        buffer: *[1]Ast.Node.Index,
        node: Ast.Node.Index,
        parameter: usize,
    ) !?Ast.Node.Index {
        const reached = (try self.reachedCall(buffer, node)) orelse return null;
        if (parameter >= reached.declared) return null;
        if (reached.receiver and parameter == 0) {
            return self.handle.tree.nodeData(reached.call.ast.fn_expr).node_and_token[0];
        }
        return reached.call.ast.params[parameter - @intFromBool(reached.receiver)];
    }

    /// The call's own written arguments, plus the expression an
    /// instance call passes implicitly (`receiver`, null when the call
    /// writes every argument itself).
    ///
    /// Nothing is copied and nothing is bounded: `arguments` borrows
    /// the tree's own nodes — or, for the fixed-arity call shapes, the
    /// `buffer` this call was given — so a declaration with any number
    /// of parameters is read the same way as one with two.  The borrow
    /// lasts exactly as long as `buffer`.
    pub const CallArguments = struct {
        arguments: []const Ast.Node.Index,
        receiver: ?Ast.Node.Index,
    };

    pub fn callArgumentsOf(
        self: *TypeResolver,
        buffer: *[1]Ast.Node.Index,
        node: Ast.Node.Index,
    ) !?CallArguments {
        const reached = (try self.reachedCall(buffer, node)) orelse return null;
        const tree = &self.handle.tree;
        return .{
            .arguments = reached.call.ast.params,
            .receiver = if (reached.receiver)
                tree.nodeData(reached.call.ast.fn_expr).node_and_token[0]
            else
                null,
        };
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

    /// True when `handle`'s document is this toolchain's `zig_lib/<suffix>`.
    /// Declaring-document identity, never a leaf name: a same-named local
    /// declaration lives in another document and cannot match.
    fn declaredInToolchainFile(
        self: *TypeResolver,
        handle: *DocumentStore.Handle,
        suffix: []const u8,
    ) !bool {
        const library = self.ctx.toolchain.zig_lib orelse return false;
        const path = try handle.uri.toFsPath(self.arena.allocator());
        const base = std.mem.trimEnd(u8, library, std.fs.path.sep_str);
        return path.len == base.len + suffix.len and
            std.mem.startsWith(u8, path, base) and std.mem.endsWith(u8, path, suffix);
    }

    pub fn isStdAllocator(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const container = (try self.containerOfNode(node)) orelse return null;
        if (container.scope_handle.scope != .root) return false;
        const declared = try self.declaredInToolchainFile(container.scope_handle.handle, "/std/mem/Allocator.zig");
        return declared;
    }

    /// Prove the resolved std-list empty constant from its actual initializer.
    /// A same-named project constant or an omitted storage field is not proof.
    pub fn stdCollectionEmptyOf(
        self: *TypeResolver,
        node: Ast.Node.Index,
        declared_type: ?Ast.Node.Index,
    ) !bool {
        const tree = &self.handle.tree;
        const owner_node = switch (tree.nodeTag(node)) {
            .enum_literal => blk: {
                if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "empty")) return false;
                break :blk declared_type orelse return false;
            },
            .field_access => blk: {
                const access = tree.nodeData(node).node_and_token;
                if (!std.mem.eql(u8, tree.tokenSlice(access[1]), "empty")) return false;
                const owner = (try self.analyser.resolveTypeOfNode(.of(access[0], self.handle))) orelse return false;
                if (!owner.is_type_val) return false;
                break :blk access[0];
            },
            else => return false,
        };
        const ty = (try self.typeOfNode(owner_node)) orelse return false;
        if (ty.data != .container or self.typeTag(ty) != .@"struct") return false;
        if (!try self.declaredInToolchainFile(ty.data.container.scope_handle.handle, "/std/array_list.zig")) return false;
        const declaration = (try Analyser.lookupSymbolContainer(ty, "empty", .other)) orelse return false;
        if (!declaration.isConst()) return false;
        const declaration_node = switch (declaration.decl) {
            .ast_node => |value| value,
            else => return false,
        };
        const source = &declaration.handle.tree;
        const variable = source.fullVarDecl(declaration_node) orelse return false;
        const initializer = variable.ast.init_node.unwrap() orelse return false;
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = source.fullStructInit(&buffer, initializer) orelse return false;
        if (literal.ast.fields.len != 2) return false;
        const tags = source.tokens.items(.tag);
        var empty_items = false;
        var zero_capacity = false;
        for (literal.ast.fields) |field| {
            const first = source.firstToken(field);
            const last = source.lastToken(field);
            if (first < 3 or tags[first - 1] != .equal or tags[first - 2] != .identifier or tags[first - 3] != .period) return false;
            const name = source.tokenSlice(first - 2);
            if (std.mem.eql(u8, name, "items")) {
                if (last - first != 3 or tags[first] != .ampersand or tags[first + 1] != .period or
                    tags[first + 2] != .l_brace or tags[last] != .r_brace) return false;
                empty_items = true;
            } else if (std.mem.eql(u8, name, "capacity")) {
                if (first != last or tags[first] != .number_literal or !std.mem.eql(u8, source.tokenSlice(first), "0")) return false;
                zero_capacity = true;
            } else return false;
        }
        return empty_items and zero_capacity;
    }

    /// What a callee turned out to be, judged from its resolved declaration.
    pub const StdCollectionAppend = enum {
        /// Not the single-element append of a `std/array_list.zig` container —
        /// including a callee that does not resolve at all.  No length fact.
        no,
        /// `append`: exactly one item, stored only when the call succeeds.
        fallible,
        /// The same, but declared `void`, so one item on every edge out of it.
        infallible,
    };

    /// The single-element append of a `std/array_list.zig` container, proven
    /// from the compiler-resolved declaration: its own document, its own name
    /// and its own parameter count.  A local `append` never matches, and
    /// neither does the slice-taking `appendSlice`, which may be handed an
    /// empty slice and insert nothing.
    pub fn stdCollectionAppendOf(
        self: *TypeResolver,
        callee: Ast.Node.Index,
        arguments: usize,
    ) !StdCollectionAppend {
        const declaration = (try self.functionDeclOf(callee)) orelse return .no;
        if (!try self.declaredInToolchainFile(declaration.handle, "/std/array_list.zig")) return .no;
        const name = declaration.name orelse return .no;
        if (!std.mem.eql(u8, name, "append") and !std.mem.eql(u8, name, "appendAssumeCapacity")) return .no;
        // The declared receiver counts as one parameter, so a call shape the
        // single-item signature cannot match is not the single-item append.
        if (declaration.parameters.len != arguments + 1) return .no;
        const returned = declaration.return_value.*;
        const result = (try self.normalizedType(returned)) orelse return .fallible;
        return if (self.typeTag(result) == .void) .infallible else .fallible;
    }

    /// The compiler's own slice equality function only reads its operands.
    /// Resolve the declaration, so aliases match and project lookalikes do not.
    pub fn stdMemEqlOf(self: *TypeResolver, callee: Ast.Node.Index, arguments: usize) !bool {
        if (arguments != 3) return false;
        const declaration = (try self.functionDeclOf(callee)) orelse return false;
        if (declaration.parameters.len != 3) return false;
        const name = declaration.name orelse return false;
        if (!std.mem.eql(u8, name, "eql")) return false;
        return self.declaredInToolchainFile(declaration.handle, "/std/mem.zig");
    }

    fn functionDeclOf(self: *TypeResolver, node: Ast.Node.Index) !?Analyser.Type.Data.Function {
        const value = (try self.analyser.resolveTypeOfNode(.of(node, self.handle))) orelse return null;
        const callable = (try self.analyser.resolveFuncProtoOfCallable(value)) orelse return null;
        if (callable.is_type_val) return null;
        return callable.data.function;
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
    ///
    /// A peer type answers when every branch that returns at all yields
    /// a pointer (or, equally, yields none), so a value bound out of a
    /// `switch` / `orelse` is classified by what it can actually be.
    pub fn resolvedTypeIsPointer(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.peeredTypeOfNode(node)) orelse return null;
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
    try resolver.init(&context, gpa, "/tmp/zbc-pointer-regression.zig", "pub fn borrow(p: **u8) **u8 { return p; }");
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

/// The `<recv>.<field>` node whose receiver is the identifier `recv`.
/// An intermediate access of an address chain is a node of its own,
/// which is what the flow pass asks this resolver about.
fn testFieldAccess(tree: *const Ast, recv: []const u8) !Ast.Node.Index {
    for (1..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeTag(node) != .field_access) continue;
        const lhs = tree.nodeData(node).node_and_token[0];
        if (tree.nodeTag(lhs) != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(lhs)), recv)) continue;
        return node;
    }
    return error.TestUnexpectedResult;
}

test "an intermediate access settles where an address chain lands" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-address-chain.zig",
        \\const Leaf = struct { count: u32 };
        \\const Branch = struct { leaf: Leaf };
        \\const Trunk = struct { branch: Branch };
        \\const Descriptor = struct { branch: *Branch };
        \\fn borrowPointer(descriptor: Descriptor) *const u32 {
        \\    return &descriptor.branch.leaf.count;
        \\}
        \\fn borrowValues(trunk: Trunk) *const u32 {
        \\    return &trunk.branch.leaf.count;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    // `descriptor.branch` is the access the address is read through
    // past its first hop.  A pointer there means the address that
    // follows names the branch's storage, not the descriptor's frame.
    try std.testing.expectEqual(
        @as(?bool, true),
        @as(?bool, try resolver.resolvedTypeIsPointer(try testFieldAccess(tree, "descriptor"))),
    );
    // The same access on an all-by-value chain is not a pointer, so
    // that address really does sit in the parameter's own storage.
    try std.testing.expectEqual(
        @as(?bool, false),
        @as(?bool, try resolver.resolvedTypeIsPointer(try testFieldAccess(tree, "trunk"))),
    );
}

test "a value bound out of a switch answers the pointer question its branches agree on" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-peer-address-chain.zig",
        \\const Leaf = struct { count: u32 };
        \\const Node = struct { count: u32 };
        \\const Pointers = union(enum) { leaf: *Leaf, node: *Node };
        \\const Values = union(enum) { leaf: Leaf, node: Node };
        \\fn throughPointers(pointers: Pointers) *const u32 {
        \\    const held = switch (pointers) {
        \\        .leaf => |boxed| boxed,
        \\        .node => |boxed| boxed,
        \\    };
        \\    return &held.count;
        \\}
        \\fn throughValues(values: Values) *const u32 {
        \\    const held = switch (values) {
        \\        .leaf => |boxed| boxed,
        \\        .node => |boxed| boxed,
        \\    };
        \\    return &held.count;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    // Both branches hand out a pointer to storage this fn never owned,
    // so the intermediate the address is read through is a pointer
    // whichever branch ran.  The union has no single type, but it has
    // one answer to this question.  The by-value twin is spelled
    // identically and answers the opposite way.
    try std.testing.expectEqual(
        @as(?bool, true),
        @as(?bool, try resolver.resolvedTypeIsPointer(try testNthIdentifier(tree, "held", 0))),
    );
    try std.testing.expectEqual(
        @as(?bool, false),
        @as(?bool, try resolver.resolvedTypeIsPointer(try testNthIdentifier(tree, "held", 1))),
    );
}

/// The `occurrence`-th identifier node named `name`.  One source can
/// bind the same name in more than one function, and each binding is a
/// node of its own.
fn testNthIdentifier(tree: *const Ast, name: []const u8, occurrence: usize) !Ast.Node.Index {
    var seen: usize = 0;
    for (1..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeTag(node) != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name)) continue;
        if (seen == occurrence) return node;
        seen += 1;
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
    const source = try std.fmt.allocPrintSentinel(gpa, "const Tag = enum {{ a }}; const Deep = {s}Tag;\n" ++
        "fn observe(deep: Deep, unknown: anytype, pptr: **[7]u8) void {{ _ = deep; _ = unknown; _ = pptr; }}", .{"?" ** 40}, 0);
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
    try std.testing.expectEqualStrings("Namespace.Box", (try resolver.typeNameOfNode(try testIdentifier(&resolver.handle.tree, "value"))).?);
}

test "nested imported fields retain their integer domain" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-nested-field-domain.zig",
        \\const std = @import("std");
        \\const Shadow = struct {
        \\    const Nested = struct { payload_token: i32 };
        \\};
        \\fn observe(unsigned: std.zig.Ast.full.For, signed: Shadow.Nested) void {
        \\    _ = unsigned.payload_token;
        \\    _ = signed.payload_token;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    const unsigned = (try resolver.intInfo(try testFieldAccess(tree, "unsigned"))) orelse
        return error.MissingIntegerType;
    try std.testing.expect(!unsigned.signed);
    try std.testing.expectEqual(@as(u16, 32), unsigned.bits);
    const signed = (try resolver.intInfo(try testFieldAccess(tree, "signed"))) orelse
        return error.MissingIntegerType;
    try std.testing.expect(signed.signed);
    try std.testing.expectEqual(@as(u16, 32), signed.bits);
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

/// Writes a real project whose `build.zig` wires `"values"` to `root` and
/// returns the canonical project directory.
fn namedModuleProject(
    tmp: *std.testing.TmpDir,
    io: std.Io,
    gpa: std.mem.Allocator,
    build_zig: []const u8,
) ![]u8 {
    try tmp.dir.writeFile(io, .{ .sub_path = "build.zig", .data = build_zig });
    try tmp.dir.createDirPath(io, "src");
    try tmp.dir.writeFile(io, .{ .sub_path = "src/values.zig", .data =
        \\pub const Registry = struct {
        \\    entries: []const u32,
        \\    limit: u32,
        \\};
    });
    return tmp.dir.realPathFileAlloc(io, ".", gpa);
}

test "a named module import types its exported fields, slice length included" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const directory = try namedModuleProject(&tmp, io, gpa,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    _ = b.addModule("values", .{ .root_source_file = b.path("src/values.zig") });
        \\}
    );
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    var context: TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, path,
        \\const values = @import("values");
        \\fn observe(registry: values.Registry) void {
        \\    const wide: u64 = @intCast(registry.entries.len);
        \\    const narrow: u32 = @intCast(registry.entries.len);
        \\    _ = wide;
        \\    _ = narrow;
        \\    _ = registry.limit;
        \\}
    );
    defer resolver.deinit();
    // The slice length is a native 64-bit unsigned integer, so a `usize` to
    // `u64` conversion is a proven fit; the declared `u32` field is not, and
    // stays visible as a 32-bit integer for the narrowing rules to judge.
    const tree = &resolver.handle.tree;
    var seen_len = false;
    var seen_limit = false;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const name = tree.tokenSlice(tree.nodeData(node).node_and_token[1]);
        if (std.mem.eql(u8, name, "len")) {
            const info = (try resolver.intInfo(node)) orelse return error.MissingLengthType;
            try std.testing.expect(!info.signed);
            try std.testing.expectEqual(@as(u16, 64), info.bits);
            seen_len = true;
        } else if (std.mem.eql(u8, name, "limit")) {
            const info = (try resolver.intInfo(node)) orelse return error.MissingLimitType;
            try std.testing.expect(!info.signed);
            try std.testing.expectEqual(@as(u16, 32), info.bits);
            seen_limit = true;
        }
    }
    try std.testing.expect(seen_len);
    try std.testing.expect(seen_limit);
    // The pair an integer-narrowing rule reads: the same 64-bit source cast
    // to a 64-bit destination is a proven fit, and to a 32-bit one it is not.
    var casts: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .builtin_call_two and tag != .builtin_call_two_comma) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@intCast")) continue;
        var params_buf: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&params_buf, node) orelse return error.MissingCastOperand;
        if (params.len != 1) return error.MissingCastOperand;
        const source = (try resolver.intInfo(params[0])) orelse return error.MissingCastSourceType;
        const destination = (try resolver.intInfo(node)) orelse return error.MissingCastTargetType;
        try std.testing.expect(!source.signed);
        try std.testing.expect(!destination.signed);
        try std.testing.expectEqual(@as(u16, 64), source.bits);
        try std.testing.expectEqual(if (casts == 0) @as(u16, 64) else 32, destination.bits);
        casts += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), casts);
    try std.testing.expectEqual(@as(?anyerror, null), context.store.source_failure);
}

test "an unwired named import stays unknown instead of assuming a length type" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // The build wires the module under a different name than the source
    // imports, so `@import("values")` names nothing that exists.
    const directory = try namedModuleProject(&tmp, io, gpa,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    _ = b.addModule("other", .{ .root_source_file = b.path("src/values.zig") });
        \\}
    );
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    var context: TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, path,
        \\const values = @import("values");
        \\fn observe(registry: values.Registry) void {
        \\    const wide: u64 = @intCast(registry.entries.len);
        \\    _ = wide;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    const length = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (std.mem.eql(u8, tree.tokenSlice(tree.nodeData(node).node_and_token[1]), "len")) break node;
    } else return error.MissingFieldAccess;
    // Nothing is known about the module, so its slice length is not assumed
    // to be a `usize`: the answer stays unknown rather than becoming a type
    // that would silence a narrowing rule.
    try std.testing.expectEqual(@as(?TypeResolver.IntInfo, null), try resolver.intInfo(length));
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(length));
    try std.testing.expectEqual(@as(?anyerror, null), context.store.source_failure);
}

test "module wiring never reaches past the source policy" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "build.zig", .data =
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    _ = b.addModule("vendored", .{ .root_source_file = b.path("vendor/lib.zig") });
        \\}
    });
    try tmp.dir.createDirPath(io, "vendor");
    try tmp.dir.writeFile(io, .{ .sub_path = "vendor/lib.zig", .data =
        \\pub const Registry = struct { entries: []const u32 };
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
        \\const vendored = @import("vendored");
        \\fn observe(registry: vendored.Registry) void { _ = registry.entries; }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    const field = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .field_access) break @as(Ast.Node.Index, @enumFromInt(index));
    } else return error.MissingFieldAccess;
    try std.testing.expectEqual(@as(?TypeResolver.IntInfo, null), try resolver.intInfo(field));
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(field));
}
