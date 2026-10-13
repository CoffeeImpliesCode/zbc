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

test {
    // The engine test artifact is rooted here; reference the intern pool so
    // its type-coercion and peer-resolution tests run under `zig build test`.
    _ = InternPool;
}
pub const ModuleId = DocumentStore.ModuleId;
pub const ModuleRegistry = DocumentStore.ModuleRegistry;
pub const SourceDocument = DocumentStore.SourceDocument;
pub const ResolvedImport = DocumentStore.ResolvedImport;
pub const SourceLoadError = DocumentStore.SourceLoadError;
/// What a membership walk reads.  A session answers it from the store's
/// shared `SourceDocument` parses; a standalone project cache answers it
/// from its own AST pool.  Re-exported so neither has to import the store.
pub const RelativeEdges = DocumentStore.RelativeEdges;
/// A document's identity in this store.  Re-exported so a caller can name
/// one — `moduleForDocument` and `uriFromImportStr` both take it — without
/// reaching past this facade into the store's own module tree.
pub const Uri = @import("uri.zig");
const Analyser = @import("analysis.zig");
/// Stack a thread needs to run resolution to its depth limit in any build mode.
pub const resolve_stack_bytes = Analyser.resolve_stack_bytes;
const ast = @import("ast.zig");
const DiagnosticsCollection = @import("diagnostics_collection.zig");
const source_policy = @import("source_policy.zig");
pub const SourcePolicy = source_policy.SourcePolicy;
pub const ParseFailure = source_policy.ParseFailure;
pub const CanonicalPaths = source_policy.CanonicalPaths;
/// Named-module wiring recovered from `build.zig` without executing it. Shared
/// with the project cache so both read build metadata through one parser.
pub const NamedModuleMap = DocumentStore.NamedModuleMap;
pub const AstIterator = @import("ast.zig").Iterator;
pub const AstWalker = @import("ast.zig").Walker;

// ── Toolchain discovery ───────────────────────────────────────────────

const ToolchainPaths = struct {
    zig_exe: ?[]const u8 = null,
    zig_lib: ?[]const u8 = null,
};

fn freeToolchain(gpa: std.mem.Allocator, paths: ToolchainPaths) void {
    if (paths.zig_exe) |path| gpa.free(path);
    if (paths.zig_lib) |path| gpa.free(path);
}

/// Why `zig env` gave no usable toolchain.  Discovery fails with
/// `error.ZigToolchainUnavailable` or `error.IncompatibleZigVersion`;
/// this record says which step failed and carries the evidence a person
/// needs: the exit status and the first line the compiler wrote to
/// stderr.  Fixed buffers keep it allocation-free.
pub const ToolchainFailure = struct {
    pub const Reason = enum {
        /// The process could not be started; `detail` is the error name.
        spawn_failed,
        /// The process exited nonzero; `code` is the status.
        exited,
        /// The process was killed; `code` is the signal number.
        signaled,
        /// The process stopped or ended in a state with no exit status.
        ended_abnormally,
        /// Exit 0 with nothing on stdout.
        empty_output,
        /// Output was neither JSON nor ZON with the expected fields.
        malformed_output,
        /// `zig_exe` or `lib_dir` missing or empty.
        missing_paths,
        /// The compiler's version differs from the one zbc parses; `detail` is that version.
        incompatible_version,
    };

    reason: Reason = .spawn_failed,
    code: u32 = 0,
    detail_buffer: [200]u8 = undefined,
    detail_len: usize = 0,

    pub fn detail(self: *const ToolchainFailure) []const u8 {
        return self.detail_buffer[0..self.detail_len];
    }

    fn setDetail(self: *ToolchainFailure, text: []const u8) void {
        const len = @min(text.len, self.detail_buffer.len);
        @memcpy(self.detail_buffer[0..len], text[0..len]);
        self.detail_len = len;
    }

    fn setFirstLine(self: *ToolchainFailure, text: []const u8) void {
        var lines = std.mem.tokenizeAny(u8, text, "\r\n");
        while (lines.next()) |line| {
            const trimmed = std.mem.trim(u8, line, &std.ascii.whitespace);
            if (trimmed.len == 0) continue;
            self.setDetail(trimmed);
            return;
        }
    }

    /// One clause, without the command name: "exited with status 1: <first stderr line>".
    pub fn format(self: ToolchainFailure, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        const text = self.detail();
        switch (self.reason) {
            .spawn_failed => try writer.print("could not be started: {s}", .{text}),
            .exited => try writer.print("exited with status {d}", .{self.code}),
            .signaled => try writer.print("was terminated by signal {d}", .{self.code}),
            .ended_abnormally => try writer.writeAll("ended without an exit status"),
            .empty_output => try writer.writeAll("exited with status 0 and printed nothing on stdout"),
            .malformed_output => try writer.writeAll("printed output that is not a Zig environment (JSON or ZON)"),
            .missing_paths => try writer.writeAll("did not report non-empty `zig_exe` and `lib_dir`"),
            .incompatible_version => try writer.print(
                "reports Zig {s}, but zbc is built for Zig {s}",
                .{ text, builtin.zig_version_string },
            ),
        }
        switch (self.reason) {
            .exited, .signaled, .ended_abnormally => {
                if (text.len != 0) try writer.print(": {s}", .{text}) else try writer.writeAll(" (no stderr output)");
            },
            else => {},
        }
    }
};

pub const ToolchainError = error{ ZigToolchainUnavailable, IncompatibleZigVersion, OutOfMemory };

/// Runs `<zig_command> env`.  On failure `failure` says why.
fn queryToolchain(
    gpa: std.mem.Allocator,
    io: std.Io,
    zig_command: []const u8,
    failure: *ToolchainFailure,
) ToolchainError!ToolchainPaths {
    const output = try runCapture(gpa, io, &.{ zig_command, "env" }, failure);
    defer gpa.free(output);
    return parseToolchainEnv(gpa, output, failure);
}

fn parseToolchainEnv(gpa: std.mem.Allocator, output: []const u8, failure: *ToolchainFailure) ToolchainError!ToolchainPaths {
    const Environment = struct { zig_exe: []const u8, lib_dir: []const u8, version: []const u8 };
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const temporary = arena.allocator();
    const source = std.mem.trim(u8, output, &std.ascii.whitespace);
    const parsed: ?Environment = if (std.mem.startsWith(u8, source, ".{")) zon: {
        const terminated = try temporary.dupeSentinel(u8, source, 0);
        break :zon std.zon.parse.fromSliceAlloc(
            Environment,
            temporary,
            terminated,
            null,
            .{ .ignore_unknown_fields = true },
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.ParseZon => break :zon null,
        };
    } else json: {
        break :json std.json.parseFromSliceLeaky(Environment, temporary, source, .{ .ignore_unknown_fields = true }) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => break :json null,
        };
    };
    const environment = parsed orelse {
        failure.* = .{ .reason = .malformed_output };
        return error.ZigToolchainUnavailable;
    };
    if (environment.zig_exe.len == 0 or environment.lib_dir.len == 0) {
        failure.* = .{ .reason = .missing_paths };
        return error.ZigToolchainUnavailable;
    }
    if (!std.mem.eql(u8, environment.version, builtin.zig_version_string)) {
        failure.* = .{ .reason = .incompatible_version };
        failure.setDetail(environment.version);
        return error.IncompatibleZigVersion;
    }
    const executable = try gpa.dupe(u8, environment.zig_exe);
    errdefer gpa.free(executable);
    return .{ .zig_exe = executable, .zig_lib = try gpa.dupe(u8, environment.lib_dir) };
}

fn runCapture(
    gpa: std.mem.Allocator,
    io: std.Io,
    argv: []const []const u8,
    failure: *ToolchainFailure,
) ToolchainError![]u8 {
    const result = std.process.run(gpa, io, .{ .argv = argv }) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => {
            failure.* = .{ .reason = .spawn_failed };
            failure.setDetail(@errorName(err));
            return error.ZigToolchainUnavailable;
        },
    };
    defer gpa.free(result.stderr);
    errdefer gpa.free(result.stdout);
    switch (result.term) {
        .exited => |code| if (code != 0) {
            failure.* = .{ .reason = .exited, .code = code };
            failure.setFirstLine(result.stderr);
            return error.ZigToolchainUnavailable;
        },
        .signal => |signal| {
            failure.* = .{ .reason = .signaled, .code = @intFromEnum(signal) };
            failure.setFirstLine(result.stderr);
            return error.ZigToolchainUnavailable;
        },
        .stopped, .unknown => {
            failure.* = .{ .reason = .ended_abnormally };
            failure.setFirstLine(result.stderr);
            return error.ZigToolchainUnavailable;
        },
    }
    if (result.stdout.len == 0) {
        failure.* = .{ .reason = .empty_output };
        return error.ZigToolchainUnavailable;
    }
    return result.stdout;
}

/// Which side of a `Toolchain` a context's paths belong to.
///
/// A context that discovered its own answers may free them, and one that
/// borrowed them may not: two owners freeing one allocation is the one way
/// a shared answer can be made to fail.
const ToolchainOwnership = enum { owned, borrowed };

/// The compiler an analysis answers about, discovered once for a run.
///
/// `zig env` is a process spawn, and a run that analyses several files at
/// once must not pay it once per worker.  The run discovers it once and
/// lends the answer: every context opens over the same bytes and no
/// worker owns a copy.  The owner therefore has to outlive every context
/// that borrowed it, which is the run's to arrange — it joins its workers
/// and only then calls `deinit`.
///
/// `TypeContext.init` is the other way in, for a caller that has one
/// context and no run to share: it discovers and owns an answer of its own.
pub const Toolchain = struct {
    gpa: std.mem.Allocator,
    paths: ToolchainPaths,

    /// Runs `<zig_command> env`; `zig_command` is looked up on `PATH` unless it has a directory part.
    /// On error `failure` records which step failed and what the compiler said.
    pub fn init(
        gpa: std.mem.Allocator,
        io: std.Io,
        zig_command: []const u8,
        failure: *ToolchainFailure,
    ) ToolchainError!Toolchain {
        return .{ .gpa = gpa, .paths = try queryToolchain(gpa, io, zig_command, failure) };
    }

    pub fn deinit(self: *Toolchain) void {
        freeToolchain(self.gpa, self.paths);
        self.* = undefined;
    }
};

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
    /// Interned module identities for this session.  The store borrows it;
    /// a `ProjectCache` attached to this context borrows the same one, so
    /// one id means the same module everywhere in the session.
    modules: ModuleRegistry,
    store: DocumentStore,
    toolchain: ToolchainPaths,
    /// Whether `toolchain` is this context's to free.  It owns the paths
    /// exactly when it discovered them, and borrows them otherwise.
    owns_toolchain: bool,

    /// Discovers a toolchain for this context alone: one `zig env`, one
    /// answer this context owns and `deinit` frees.
    pub fn init(self: *TypeContext, gpa: std.mem.Allocator, io: std.Io) !void {
        var failure: ToolchainFailure = .{};
        const paths = try queryToolchain(gpa, io, "zig", &failure);
        try self.initWithPaths(gpa, io, paths, .owned);
    }

    /// Borrows a run's toolchain instead of discovering one.
    ///
    /// Every worker of one run learns the same compiler this way, so the
    /// paths are one allocation read many times rather than one copy and
    /// one process spawn per context.  `toolchain` must outlive this
    /// context: nothing here frees what it points at, so the owner frees it
    /// once, after every context that borrowed it is done.
    pub fn initWithToolchain(
        self: *TypeContext,
        gpa: std.mem.Allocator,
        io: std.Io,
        toolchain: *const Toolchain,
    ) !void {
        try self.initWithPaths(gpa, io, toolchain.paths, .borrowed);
    }

    /// One initialization, told only who owns the toolchain paths it is
    /// handed, so discovering and borrowing cannot drift into answering the
    /// same question differently.
    fn initWithPaths(
        self: *TypeContext,
        gpa: std.mem.Allocator,
        io: std.Io,
        paths: ToolchainPaths,
        ownership: ToolchainOwnership,
    ) !void {
        self.gpa = gpa;
        self.toolchain = paths;
        self.owns_toolchain = ownership == .owned;
        errdefer if (self.owns_toolchain) freeToolchain(gpa, self.toolchain);

        self.ip = try InternPool.init(io, gpa);
        errdefer self.ip.deinit(gpa);

        self.diagnostics = .{ .io = io, .allocator = gpa };
        self.environ_map = .init(gpa);

        const tc = self.toolchain;
        const zig_lib: ?std.Build.Cache.Directory = if (tc.zig_lib) |p|
            .{ .path = p, .handle = .cwd() }
        else
            null;
        self.modules = .init(gpa);
        errdefer self.modules.deinit();

        // The store borrows this registry rather than owning one: one
        // `TypeContext` is initialized in place and never moved, so the
        // address handed over here is the session's only module-id space
        // and an id from it means the same thing everywhere in the session.
        self.store = .{
            .io = io,
            .allocator = gpa,
            .modules = &self.modules,
            .config = .{
                .environ_map = &self.environ_map,
                .zig_exe_path = tc.zig_exe,
                .zig_lib_dir = zig_lib,
                .build_runner_path = null,
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

    /// Borrow one immutable document, read in `module`.
    ///
    /// The caller supplies an absolute path and the module the document
    /// belongs to.  A caller that has not proven a module passes
    /// `ModuleId.unscoped`, which resolves relative imports exactly and
    /// resolves a named import only when the declared modules agree.
    pub fn sourceHandle(self: *TypeContext, file_path: []const u8, module: ModuleId) SourceLoadError!DocumentStore.Handle {
        std.debug.assert(std.fs.path.isAbsolute(file_path));
        const uri: Uri = try .fromPath(self.gpa, file_path);
        defer uri.deinit(self.gpa);
        return (try self.store.getOrLoadHandle(uri, module)) orelse
            return self.store.failureSnapshot().source_failure orelse error.SourceExcluded;
    }

    /// The module a document belongs to, when this session has proven one:
    /// a declared module's own root is that module, and anything else is
    /// `.unscoped` until an import says otherwise.
    pub fn moduleForDocument(self: *TypeContext, uri: Uri) !ModuleId {
        return self.store.moduleForDocument(uri);
    }

    pub fn deinit(self: *TypeContext) void {
        self.store.deinit();
        self.diagnostics.deinit();
        self.ip.deinit(self.gpa);
        self.environ_map.deinit();
        self.modules.deinit();
        if (self.owns_toolchain) freeToolchain(self.gpa, self.toolchain);
    }
};

/// How a declaration site is hashed and compared: the document that declares
/// it, the module that document is read in, and the scope inside it.  This is
/// the identity the type pool keys container types by, so a memo keyed this
/// way cannot answer for a different declaration than the one asked about.
const ScopeKey = struct {
    const Context = struct {
        pub fn hash(_: Context, key: Analyser.ScopeWithHandle) u64 {
            var hasher: std.hash.Wyhash = .init(0);
            key.hashWithHasher(&hasher);
            return hasher.final();
        }

        pub fn eql(_: Context, a: Analyser.ScopeWithHandle, b: Analyser.ScopeWithHandle) bool {
            return a.eql(b);
        }
    };
};

// ── TypeResolver ─────────────────────────────────────────────────────

/// Per-file type resolver.  Borrows a TypeContext (DocumentStore +
/// InternPool).  Per-file documents stay open for the thread's lifetime
/// so InternPool entries referencing them remain valid.
pub const TypeResolver = struct {
    pub const CallOperands = Analyser.CallOperands;
    gpa: std.mem.Allocator,
    ctx: *TypeContext,
    arena: std.heap.ArenaAllocator,
    handle: DocumentStore.Handle,
    analyser: Analyser,

    /// Import aliases this document binds, keyed by what they name.
    ///
    /// An alias is document syntax — it lives in the shared immutable tree
    /// and means nothing outside the file that wrote it — but it only names
    /// a declaration *in one environment*, so the key is the target's
    /// canonical URI together with the module it is read in.  Two modules
    /// importing one file resolve their own alias for it, and neither sees
    /// the other's answer.  A resolver is owned by one file on one worker,
    /// so this needs no lock.
    alias_cache: std.HashMapUnmanaged(AliasKey, ?[]const u8, AliasKey.Context, std.hash_map.default_max_load_percentage) = .empty,

    /// Container names already settled, keyed by the declaration site they
    /// describe: which document, read in which module, which scope in it.
    ///
    /// A qualified name is a fact about one declaration in one environment,
    /// not about a query and not about a name — two namespaces may declare
    /// the same name, and one file read as two modules is two declarations —
    /// so the key is the identity the type pool already interns container
    /// types by.  Deriving one means reading every declaration of each
    /// enclosing scope, matching one of them, and joining what is left, so
    /// it is done once per site and a later question about the same
    /// declaration is a lookup.  A site with no provable name is settled
    /// too, because "this declaration has no name this document can prove"
    /// is an answer, not a reason to walk the same scopes for the rest of
    /// the file's analysis.
    ///
    /// The bytes are the arena's and are borrowed until `deinit`; the cache
    /// owns its entries and nothing else.
    name_cache: NameCache = .empty,

    /// The same answers as `name_cache`, spelled the way THIS document
    /// dispatches on them: its own name for a declaration it owns, and its
    /// own alias for the file the declaration lives in joined to the name
    /// otherwise.  Keyed the same way, because one resolver is one document
    /// asking about one declaration site, and that spelling is fixed for it.
    reference_cache: NameCache = .empty,

    /// Payload certificates belong to the complete lexical instantiation.
    literal_payload_cache: std.HashMapUnmanaged(
        LiteralPayloadKey,
        bool,
        LiteralPayloadKey.Context,
        std.hash_map.default_max_load_percentage,
    ) = .empty,

    const LiteralPayloadKey = struct {
        handle: DocumentStore.Handle,
        node: Ast.Node.Index,
        container_type: ?ActualType,
        actual_type: ?ActualTypeID,
        runtime_selectors: bool,
        depth: usize,

        fn optionalTypeEql(a: ?ActualType, b: ?ActualType) bool {
            return if (a) |left| if (b) |right| ActualType.eql(left, right) else false else b == null;
        }

        fn sameContext(a: LiteralPayloadKey, b: LiteralPayloadKey) bool {
            return a.handle.eql(b.handle) and a.node == b.node and
                optionalTypeEql(a.container_type, b.container_type) and
                optionalTypeEql(a.actual_type, b.actual_type) and
                a.runtime_selectors == b.runtime_selectors;
        }

        const Context = struct {
            pub fn hash(_: Context, key: LiteralPayloadKey) u64 {
                var hasher: std.hash.Wyhash = .init(0);
                std.hash.autoHash(&hasher, @intFromPtr(key.handle.document));
                std.hash.autoHash(&hasher, key.handle.module);
                std.hash.autoHash(&hasher, key.node);
                std.hash.autoHash(&hasher, key.container_type != null);
                if (key.container_type) |ty| ty.hashWithHasher(&hasher);
                std.hash.autoHash(&hasher, key.actual_type != null);
                if (key.actual_type) |ty| ty.hashWithHasher(&hasher);
                std.hash.autoHash(&hasher, key.runtime_selectors);
                std.hash.autoHash(&hasher, key.depth);
                return hasher.final();
            }

            pub fn eql(_: Context, a: LiteralPayloadKey, b: LiteralPayloadKey) bool {
                return a.depth == b.depth and a.sameContext(b);
            }
        };
    };

    /// What an alias names: the canonical URI of the target together with the
    /// module it is read in.  Byte equality and a byte hash, so a hit costs
    /// one comparison and no formatted key allocation.
    const AliasKey = struct {
        uri: []const u8,
        module: DocumentStore.ModuleId,

        const Context = struct {
            pub fn hash(_: Context, key: AliasKey) u64 {
                var hasher: std.hash.Wyhash = .init(0);
                hasher.update(key.uri);
                std.hash.autoHash(&hasher, key.module);
                return hasher.final();
            }

            pub fn eql(_: Context, a: AliasKey, b: AliasKey) bool {
                return a.module == b.module and std.mem.eql(u8, a.uri, b.uri);
            }
        };
    };

    /// Names per declaration site.  A key that is present is a question that
    /// has been answered, so "no name" is a stored answer rather than an
    /// absent key — an absent key means no answer has been kept, so the
    /// question is asked again, and a run that ran out of memory must not
    /// look like one that proved there is nothing to find.
    const NameCache = std.HashMapUnmanaged(
        Analyser.ScopeWithHandle,
        SettledName,
        ScopeKey.Context,
        std.hash_map.default_max_load_percentage,
    );

    /// One settled name for one declaration site.
    const SettledName = union(enum) {
        named: []const u8,
        unnamed,

        /// What the caller sees: the name, or the absence of one.
        fn answer(name: SettledName) ?[]const u8 {
            return switch (name) {
                .named => |text| text,
                .unnamed => null,
            };
        }
    };

    /// Open the resolver over the document `file_path` names, or over
    /// `source` read under that name when the caller hands the text over.
    ///
    /// A failed initialization owns nothing afterwards and is safe to
    /// `deinit`: the resources it began with are released and replaced, so
    /// a caller that walks away leaks nothing and a caller that releases
    /// anyway frees nothing twice.  It is not a resolver that can be
    /// queried — there is no document to ask about.
    pub fn init(
        self: *TypeResolver,
        ctx: *TypeContext,
        gpa: std.mem.Allocator,
        file_path: []const u8,
        source: ?[:0]const u8,
    ) !void {
        // Everything this resolver owns is live before the first statement
        // that can fail, and released again if one does: `initOwned` leaves
        // resources `deinit` may be called on, and `rollback` leaves those
        // released with nothing left to release.  The document is bound
        // once, below, when there is one to bind.
        self.initOwned(ctx, gpa, null);
        errdefer self.rollback();

        const aa = self.arena.allocator();
        const abs_path: []const u8 = try self.entryPath(file_path, source != null);
        const handle_uri: Uri = try .fromPath(aa, abs_path);
        // The entry file's module is whatever the build metadata proves
        // about this very file; a document that is not a declared module's
        // own root has none of its own, and stays unproven.
        const module = try ctx.store.moduleForDocument(handle_uri);
        if (source) |text| {
            self.handle = ctx.store.getHandle(handle_uri, module) orelse blk: {
                try ctx.store.openLspSyncedDocument(handle_uri, text);
                break :blk ctx.store.getHandle(handle_uri, module) orelse
                    return ctx.store.failureSnapshot().source_failure orelse error.HandleMissing;
            };
            if (!std.mem.eql(u8, self.handle.document.tree.source, text)) return error.SourceSnapshotChanged;
        } else {
            self.handle = (try ctx.store.getOrLoadHandle(handle_uri, module)) orelse
                return ctx.store.failureSnapshot().source_failure orelse error.SourceExcluded;
        }

        // The document this resolver answers about is bound once, here,
        // before anything can ask it a question: a query resolves from the
        // handle the request came in on, and until there is one the
        // analyser is bound to no document.
        self.analyser.root_handle = self.handle;
    }

    /// Give the resolver the resources it owns: the arena every name it
    /// answers with is built in, the analyser, and three empty memos.
    ///
    /// Aggregate initialization, not memberwise assignment: a defaulted
    /// field only takes its default when the whole value is built at once,
    /// and every defaulted cache — `alias_cache` and the name caches — must
    /// be `.empty` from the first statement because `deinit` frees them.
    /// Assigning fields one at a time leaves every field the caller did not
    /// mention holding whatever was in the caller's `undefined` — which is
    /// a fault waiting on the first field anyone adds later.
    ///
    /// The analyser is real from the first statement as well, which is what
    /// makes a failed `init` safe to `deinit`: `deinit` reads the analyser's
    /// caches, so an analyser left `undefined` there is not a resource held
    /// in reserve but a fault.  It is built bound to `bound` — no document
    /// at all, for a resolver that is still looking for one.
    ///
    /// The analyser borrows the final address of this resolver's arena.
    /// `Analyser.init` stores that pointer without reading the arena, so the
    /// aggregate can bind it directly before the arena value is installed.
    /// The resolver must stay at this address throughout its lifetime.
    fn initOwned(
        self: *TypeResolver,
        ctx: *TypeContext,
        gpa: std.mem.Allocator,
        bound: ?DocumentStore.Handle,
    ) void {
        self.* = .{
            .gpa = gpa,
            .ctx = ctx,
            .arena = std.heap.ArenaAllocator.init(gpa),
            // A resolver that has not found its document holds no handle,
            // and nothing that runs before it does read one.
            .handle = bound orelse undefined,
            .analyser = Analyser.init(gpa, &self.arena, &ctx.store, &ctx.ip, bound),
        };
    }

    /// The identity of the entry document: `file_path` as the kernel
    /// resolves it.
    ///
    /// A spelling that needs no folding is one question the kernel answers
    /// in a single call, and the store's own canonical table answers it —
    /// from the answer it already holds, when this spelling has been asked
    /// before.
    ///
    /// A spelling that walks back out of a directory is asked as one
    /// question too: `link/../src/main.zig` reaches the kernel whole, which
    /// meets `link` before it counts `..`, and the store keeps that spelling
    /// unfolded on the way in, so one document is not filed twice under two
    /// names.
    ///
    /// Absence is the one answer a caller that also handed over the text of
    /// the document may still be given a path for; every other failure is
    /// the filesystem refusing to answer, and is passed on rather than
    /// reinterpreted.
    fn entryPath(self: *TypeResolver, file_path: []const u8, source_provided: bool) ![]const u8 {
        const arena = self.arena.allocator();
        // Absolute, but not folded: the working directory's own realpath
        // beside the spelling the caller gave.  Folding `..` into the text
        // is the whole defect, so it happens nowhere above this line.
        const absolute = if (std.fs.path.isAbsolute(file_path))
            file_path
        else blk: {
            var buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
            const length = try std.Io.Dir.cwd().realPathFile(self.ctx.store.io, ".", &buffer);
            break :blk try std.fs.path.join(arena, &.{ buffer[0..length], file_path });
        };

        const canonical = self.ctx.canonicalPath(absolute) catch |err| switch (err) {
            error.FileNotFound, error.NotDir => {
                if (!source_provided) return std.fs.path.resolve(arena, &.{absolute});
                return self.absentEntryPath(absolute);
            },
            else => |other| return other,
        };
        return canonical;
    }

    /// The identity of an entry document the filesystem does not have, for
    /// a caller that handed over the text it holds.
    ///
    /// The longest prefix that does exist is still canonicalized, so the
    /// document lands in the directory every other document under it is
    /// named by, and a link in that prefix still reaches the one tree it
    /// points at.  The components past it stay the caller's own spelling:
    /// there is nothing there for the kernel to have an opinion about, and
    /// inventing one would be a second answer to which file this is.
    fn absentEntryPath(self: *TypeResolver, absolute: []const u8) ![]const u8 {
        const arena = self.arena.allocator();
        // `absolute` spells a real path out in full, so every shorter
        // candidate is one of its prefixes, and the root — the one prefix
        // that is always there — ends the walk.
        var cut: usize = absolute.len;
        while (cut > 1) {
            cut = std.mem.lastIndexOfScalar(u8, absolute[0..cut], std.fs.path.sep) orelse break;
            const prefix = if (cut == 0) absolute[0..1] else absolute[0..cut];
            const canonical = self.ctx.canonicalPath(prefix) catch |err| switch (err) {
                error.FileNotFound, error.NotDir => continue,
                else => |other| return other,
            };
            return std.fs.path.resolve(arena, &.{ canonical, absolute[cut + 1 ..] });
        }
        return std.fs.path.resolve(arena, &.{absolute});
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
        handle: DocumentStore.Handle,
    ) !void {
        // The document is known up front rather than looked for, and the
        // rollback is the same one `init` uses: this is still a fallible
        // contract, and a caller that handles the failure by calling
        // `deinit` must not be reaching for memory `errdefer` has already
        // released.
        self.initOwned(ctx, gpa, handle);
        errdefer self.rollback();
    }

    /// Release every resource this resolver owns and leave it as a fresh one
    /// is: three empty memos, a new arena, and an analyser that owns
    /// nothing and is bound to no document.
    ///
    /// This is what `init` and `initBorrowed` hand their failures to, so a
    /// failed initialization leaks nothing for the caller that walks away.
    /// EVERY resource `deinit` released is replaced, not only the arena and
    /// the analyser: a map is left `undefined` by `deinit` rather than
    /// empty, and an `undefined` map is what the caller's own `deinit` would
    /// then reach for.  REPLACING what was released is also what keeps an
    /// arena from being freed twice, since a released one has been freed
    /// once already.  `initOwned` is that reset: one aggregate, and nothing
    /// it does can fail.
    ///
    /// What is left owns memory and no document, so it is not something to
    /// query: a question needs the document this resolver never found, and
    /// would read its handle out of memory that is not there.
    fn rollback(self: *TypeResolver) void {
        const ctx = self.ctx;
        const gpa = self.gpa;
        self.deinit();
        self.initOwned(ctx, gpa, null);
    }

    /// Release the memos, the analyser and the arena.
    ///
    /// Safe to call on a resolver whose `init` failed: the failure rolled
    /// itself back to a state that owns nothing, so this releases nothing
    /// and frees nothing twice.  On every other resolver it is the one call
    /// that ends its life.
    pub fn deinit(self: *TypeResolver) void {
        self.alias_cache.deinit(self.gpa);
        // The names themselves are the arena's; freeing it below is what
        // releases them, and these two hold the entries that point at them.
        self.name_cache.deinit(self.gpa);
        self.reference_cache.deinit(self.gpa);
        self.literal_payload_cache.deinit(self.gpa);
        self.analyser.deinit();
        self.arena.deinit();
    }

    /// Convert a resolved value to its type without stripping address-bearing
    /// wrappers. Unresolved, ambiguous, or erroneous types answer null.
    pub fn normalizedType(self: *TypeResolver, value: ActualType) !?ActualType {
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

    /// The innermost function declaration enclosing this token. The document's
    /// existing scope index owns the lookup; function-type scopes are skipped.
    pub fn enclosingFunctionAt(self: *TypeResolver, token: Ast.TokenIndex) error{OutOfMemory}!?Ast.Node.Index {
        const tree = &self.handle.document.tree;
        const scopes = try self.handle.getDocumentScope();
        var scope = Analyser.innermostScopeAtIndex(scopes, tree.tokens.items(.start)[token]).toOptional();
        while (scope.unwrap()) |index| {
            if (scopes.getScopeTag(index) == .function) {
                const declaration = scopes.getScopeAstNode(index).?;
                if (tree.nodeTag(declaration) == .fn_decl) return declaration;
            }
            scope = scopes.scopes.items(.parent_scope)[@intFromEnum(index)];
        }
        return null;
    }

    /// Complete instantiated identity. Keys use `hash64` and `eql`, never
    /// pointer identity or the hash alone; nested storage borrows this arena.
    pub const ActualType = Analyser.Type;
    pub const ActualTypeID = ActualType;

    /// Borrowed lexical context for one query. Frames coexist across recursive
    /// foreign-document queries without installing mutable analyser context.
    pub const ResolutionFrame = struct {
        resolver: *TypeResolver,
        handle: DocumentStore.Handle,
        container_type: ?ActualType,
        /// Full callable identity for proof memos, borrowed from the original
        /// resolver. Ordinary and container-only queries have no callable.
        actual_type: ?ActualTypeID = null,

        fn options(self: ResolutionFrame, node: Ast.Node.Index) Analyser.ResolveOptions {
            return .{ .node_handle = .of(node, self.handle), .container_type = self.container_type };
        }

        pub fn resolveValueOfNode(self: ResolutionFrame, node: Ast.Node.Index) !?ActualType {
            const tree = &self.handle.document.tree;
            const value = if (tree.nodeTag(node) == .identifier) blk: {
                const token = tree.nodeMainToken(node);
                const declaration = (try self.resolver.analyser.lookupSymbolGlobal(
                    self.handle,
                    tree.tokenSlice(token),
                    tree.tokenStart(token),
                )) orelse break :blk try self.resolver.analyser.resolveTypeOfNode(self.options(node));
                const framed = try self.declarationInFrame(declaration);
                break :blk try framed.resolveType(&self.resolver.analyser);
            } else try self.resolver.analyser.resolveTypeOfNode(self.options(node));
            return try self.closeLiteralContext(node, value orelse return null);
        }

        /// A container literal written inside a factory captures that factory's
        /// actual arguments. Its lexical declaration alone has only placeholders.
        /// Close only this literal, never a type reached through another owner.
        fn closeLiteralContext(self: ResolutionFrame, node: Ast.Node.Index, value: ActualType) !ActualType {
            if (value.data != .container) return value;
            const tree = &self.handle.document.tree;
            switch (tree.nodeTag(node)) {
                .call, .call_comma, .call_one, .call_one_comma => {
                    // Close the returned literal under the exact factory call,
                    // not under the caller or its uninstantiated lexical owner.
                    const factory = switch (try self.functionReferenceOfCall(node)) {
                        .function => |reference| reference,
                        else => return value,
                    };
                    const literal = value.data.container;
                    if (!literal.scope_handle.handle.eql(factory.handle) or
                        literal.scope_handle.scope == .root) return value;
                    const literal_node = literal.scope_handle.toNode();
                    const frame = self.resolver.frameForFunction(factory);
                    const declaration = (try frame.functionDeclarationNode(factory)) orelse return value;
                    const factory_tree = &factory.handle.document.tree;
                    const scopes = try factory.handle.getDocumentScope();
                    const enclosing_scope = Analyser.innermostScopeAtIndexWithTag(
                        scopes,
                        factory_tree.tokenStart(factory_tree.nodeMainToken(literal_node)),
                        .initOne(.function),
                    ).unwrap() orelse return value;
                    if (scopes.getScopeAstNode(enclosing_scope) != declaration) return value;
                    return frame.closeLiteralContext(literal_node, value);
                },
                else => {},
            }
            const outer = self.container_type orelse return value;
            if (outer.data != .container) return value;
            const captured = outer.data.container;
            if (captured.bound_params.count() == 0 and captured.bound_values.count() == 0) return value;
            const literal = value.data.container;
            if (!literal.scope_handle.handle.eql(self.handle) or
                literal.scope_handle.toNode() != node or
                !captured.scope_handle.handle.eql(self.handle)) return value;
            const scopes = try self.handle.getDocumentScope();
            var scope = literal.scope_handle.scope;
            while (scope != captured.scope_handle.scope) {
                scope = scopes.getScopeParent(scope).unwrap() orelse return value;
            }
            var closed = literal;
            for (captured.bound_params.keys(), captured.bound_params.values()) |key, actual| {
                if (literal.bound_params.get(key)) |previous| {
                    if (previous.eql(actual)) continue;
                }
                closed.bound_params = try literal.bound_params.clone(self.resolver.analyser.arena.allocator());
                for (captured.bound_params.keys(), captured.bound_params.values()) |token, binding| {
                    try closed.bound_params.put(self.resolver.analyser.arena.allocator(), token, binding);
                }
                break;
            }
            for (captured.bound_values.keys(), captured.bound_values.values()) |key, actual| {
                if (literal.bound_values.get(key)) |previous| {
                    if (previous.eql(actual)) continue;
                }
                closed.bound_values = try literal.bound_values.clone(self.resolver.analyser.arena.allocator());
                for (captured.bound_values.keys(), captured.bound_values.values()) |token, binding| {
                    try closed.bound_values.put(self.resolver.analyser.arena.allocator(), token, binding);
                }
                break;
            }
            return .{ .data = .{ .container = closed }, .is_type_val = value.is_type_val };
        }

        /// Borrow the existing analyser's known string value. Unknown values
        /// remain null; any returned bytes borrow the original resolver/source.
        pub fn stringValueOfNode(self: ResolutionFrame, node: Ast.Node.Index) !?[]const u8 {
            return self.resolver.analyser.resolveStringLiteral(self.options(node));
        }

        /// Read only a boolean value established by the canonical analyser.
        /// An unresolved value or a boolean type alone is not a branch proof.
        pub fn boolValueOfNode(self: ResolutionFrame, node: Ast.Node.Index) !?bool {
            const value = (try self.resolveValueOfNode(node)) orelse return null;
            if (value.is_type_val or value.data != .ip_index) return null;
            return switch (value.data.ip_index.index orelse return null) {
                .bool_true => true,
                .bool_false => false,
                else => null,
            };
        }

        pub fn typeOfNode(self: ResolutionFrame, node: Ast.Node.Index) !?ActualType {
            const value = (try self.resolveValueOfNode(node)) orelse return null;
            return self.resolver.normalizedType(value);
        }

        /// The nearest source function body owning this token. Function-type
        /// prototypes are scopes, but do not own executable local storage.
        /// Uses the document's cached scope tree, including in foreign frames.
        pub fn enclosingFunctionAt(self: ResolutionFrame, token: Ast.TokenIndex) error{OutOfMemory}!?Ast.Node.Index {
            const tree = &self.handle.document.tree;
            const scopes = try self.handle.getDocumentScope();
            var current = Analyser.innermostScopeAtIndexWithTag(
                scopes, tree.tokenStart(token), .initOne(.function),
            ).unwrap();
            while (current) |scope| {
                if (scopes.getScopeTag(scope) == .function) {
                    const node = scopes.getScopeAstNode(scope).?;
                    if (tree.nodeTag(node) == .fn_decl) return node;
                }
                current = scopes.getScopeParent(scope).unwrap();
            }
            return null;
        }

        /// Expected expression type from its source ancestors in this exact
        /// instantiation. Missing context remains unknown.
        pub fn expectedTypeOfNode(self: ResolutionFrame, node: Ast.Node.Index) !?ActualType {
            const tree = &self.handle.document.tree;
            const lineage = try ast.nodesOverlappingIndex(
                self.resolver.analyser.arena.allocator(),
                tree,
                tree.tokenStart(tree.nodeMainToken(node)),
            );
            defer self.resolver.analyser.arena.allocator().free(lineage);
            if (lineage.len > 128) return null;
            const index = std.mem.findScalar(Ast.Node.Index, lineage, node) orelse return null;
            // These operators coerce their RHS to the LHS type. A shift's
            // RHS has a different, width-derived type, so it is not included.
            // Parentheses do not change this result-location relationship.
            var expression = node;
            for (lineage[index + 1 ..]) |ancestor| {
                switch (tree.nodeTag(ancestor)) {
                    .grouped_expression => expression = ancestor,
                    .call, .call_comma, .call_one, .call_one_comma => {
                        var buffer: [2]Ast.Node.Index = undefined;
                        const call = CallOperands.full(tree, &buffer, ancestor) orelse return null;
                        const argument = std.mem.findScalar(Ast.Node.Index, call.ast.params, expression) orelse break;
                        const reached = (try self.reachedCall(&buffer, ancestor)) orelse return null;
                        const parameter = argument + @intFromBool(reached.receiver);
                        if (parameter >= reached.parameters.len) return null;
                        // anytype does not supply a result-location type.
                        if (reached.parameters[parameter].type.data == .anytype_parameter) return null;
                        const callable = try Analyser.resolveFunctionTypeFromCall(
                            &self.resolver.analyser,
                            self.options(reached.call.ast.fn_expr),
                            reached.call,
                            reached.callable,
                        );
                        if (parameter >= callable.data.function.parameters.len) return null;
                        // Generic substitution can already yield an instance.
                        // Normalize that actual type, rather than requiring
                        // another type-value-to-instance conversion.
                        return self.resolver.normalizedType(callable.data.function.parameters[parameter].type);
                    },
                    .assign_mul,
                    .assign_div,
                    .assign_mod,
                    .assign_add,
                    .assign_sub,
                    .assign_bit_and,
                    .assign_bit_xor,
                    .assign_bit_or,
                    .assign_mul_wrap,
                    .assign_add_wrap,
                    .assign_sub_wrap,
                    .assign_mul_sat,
                    .assign_add_sat,
                    .assign_sub_sat,
                    => {
                        const lhs, const rhs = tree.nodeData(ancestor).node_and_node;
                        if (expression != rhs) return null;
                        return self.typeOfNode(lhs);
                    },
                    else => break,
                }
            }
            const value = (try self.resolver.analyser.resolveExpressionTypeFromAncestors(
                self.options(node),
                node,
                lineage[index + 1 ..],
            )) orelse return null;
            return self.resolver.normalizedType(value);
        }

        const max_returned_callable_depth = 32;

        fn declarationInFrame(
            self: ResolutionFrame,
            declaration: Analyser.DeclWithHandle,
        ) !Analyser.DeclWithHandle {
            if (declaration.container_type != null) return declaration;
            const context = self.container_type orelse return declaration;
            const container = switch (context.data) {
                .container => |container| container,
                else => return declaration,
            };
            const scope_handle = container.scope_handle;
            if (scope_handle.handle.module != declaration.handle.module or
                !scope_handle.handle.document.uri.eql(declaration.handle.document.uri))
            {
                return declaration;
            }

            const tree = &declaration.handle.document.tree;
            const scopes = try declaration.handle.getDocumentScope();
            const declaration_scope = Analyser.innermostScopeAtIndex(
                scopes,
                tree.tokens.items(.start)[declaration.nameToken()],
            );
            if (declaration.decl == .ast_node) {
                switch (tree.nodeTag(declaration.decl.ast_node)) {
                    .fn_decl, .fn_proto, .fn_proto_multi, .fn_proto_one, .fn_proto_simple => {
                        const owner = Analyser.innermostScopeAtIndexWithTag(
                            scopes,
                            tree.tokenStart(tree.nodeMainToken(declaration.decl.ast_node)),
                            .initOne(.container),
                        ).unwrap() orelse .root;
                        // A named callee belongs to its declaring namespace.
                        // Caller captures bind its arguments, not its owner.
                        if (scope_handle.scope != owner) return declaration;
                    },
                    else => {},
                }
            }
            if (scope_handle.scope != .root) {
                var enclosing_scope = scope_handle.scope;
                var enclosed = false;
                while (true) {
                    if (enclosing_scope == declaration_scope) {
                        enclosed = true;
                        break;
                    }
                    enclosing_scope = scopes.getScopeParent(enclosing_scope).unwrap() orelse break;
                }
                if (!enclosed) {
                    const parent = scopes.getScopeParent(declaration_scope).unwrap() orelse return declaration;
                    if (parent != scope_handle.scope) {
                        // Block-local aliases belong to this exact method,
                        // but a nested function must keep its own context.
                        const actual = self.actual_type orelse return declaration;
                        if (actual.data != .function or
                            !actual.data.function.handle.eql(declaration.handle)) return declaration;
                        const selected_scope = Analyser.innermostScopeAtIndexWithTag(
                            scopes,
                            tree.tokenStart(declaration.nameToken()),
                            .initOne(.function),
                        ).unwrap() orelse return declaration;
                        const enclosing = scopes.getScopeAstNode(selected_scope) orelse return declaration;
                        if (tree.nodeMainToken(enclosing) != actual.data.function.fn_token)
                            return declaration;
                    }
                }
            }

            var framed = declaration;
            framed.container_type = context;
            return framed;
        }

        fn frameForDeclaration(
            self: ResolutionFrame,
            declaration: Analyser.DeclWithHandle,
        ) !ResolutionFrame {
            const framed = try self.declarationInFrame(declaration);
            return .{
                .resolver = self.resolver,
                .handle = framed.handle,
                .container_type = framed.container_type,
                .actual_type = self.actual_type,
            };
        }

        const LiteralPayloadVisit = LiteralPayloadKey;

        /// Prove literal bytes, not a selector's definedness or its bounds.
        /// Runtime selectors are permitted only in the queried expression;
        /// declaration initializers must also have literal selectors.
        pub fn immutableLiteralPayloadOfNode(self: ResolutionFrame, node: Ast.Node.Index) Analyser.Error!bool {
            var visits: [max_returned_callable_depth]LiteralPayloadVisit = undefined;
            return self.immutableLiteralPayloadAtDepth(node, &visits, 0, true);
        }

        fn immutableLiteralPayloadAtDepth(
            self: ResolutionFrame,
            node: Ast.Node.Index,
            visits: *[max_returned_callable_depth]LiteralPayloadVisit,
            depth: usize,
            runtime_selectors: bool,
        ) Analyser.Error!bool {
            if (depth == visits.len) return false;
            const key: LiteralPayloadKey = .{
                .handle = self.handle,
                .node = node,
                .container_type = self.container_type,
                .actual_type = self.actual_type,
                .runtime_selectors = runtime_selectors,
                .depth = depth,
            };
            for (visits[0..depth]) |visit|
                if (visit.sameContext(key)) return false;
            visits[depth] = key;
            const tree = &self.handle.document.tree;
            // Literal leaves are cheaper to read than to hash and memoize.
            const memoize = switch (tree.nodeTag(node)) {
                .identifier,
                .field_access,
                .array_access,
                .array_init,
                .array_init_comma,
                .array_init_one,
                .array_init_one_comma,
                .array_init_dot,
                .array_init_dot_comma,
                .array_init_dot_two,
                .array_init_dot_two_comma,
                => true,
                else => false,
            };
            if (memoize) if (self.resolver.literal_payload_cache.get(key)) |known| return known;
            const defined = try self.immutableLiteralPayloadUncached(node, visits, depth, runtime_selectors);
            // Failed resolution or allocation never installs a certificate.
            if (memoize) try self.resolver.literal_payload_cache.put(self.resolver.gpa, key, defined);
            return defined;
        }

        fn immutableLiteralPayloadUncached(
            self: ResolutionFrame,
            node: Ast.Node.Index,
            visits: *[max_returned_callable_depth]LiteralPayloadVisit,
            depth: usize,
            runtime_selectors: bool,
        ) Analyser.Error!bool {
            const tree = &self.handle.document.tree;
            switch (tree.nodeTag(node)) {
                .number_literal,
                .char_literal,
                .string_literal,
                .multiline_string_literal,
                .enum_literal,
                .error_value,
                => return true,
                .identifier, .field_access => {
                    if (tree.nodeTag(node) == .identifier) {
                        const name = tree.tokenSlice(tree.nodeMainToken(node));
                        if (std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false") or
                            std.mem.eql(u8, name, "null")) return true;
                        if (std.mem.eql(u8, name, "undefined")) return false;
                    } else {
                        // Only namespace declarations are immutable aliases.
                        // An instance member or pointer's target is storage.
                        const owner = (try self.resolveValueOfNode(tree.nodeData(node).node_and_token[0])) orelse return false;
                        if (!owner.is_type_val or owner.data != .container) return false;
                    }
                    const declaration = (try self.declarationForCallableNode(node)) orelse return false;
                    if (!declaration.isConst()) return false;
                    const declaration_node = switch (declaration.decl) {
                        .ast_node => |found| found,
                        else => return false,
                    };
                    const source = &declaration.handle.document.tree;
                    const variable = source.fullVarDecl(declaration_node) orelse return false;
                    const initializer = variable.ast.init_node.unwrap() orelse return false;
                    const frame = try self.frameForDeclaration(declaration);
                    return frame.immutableLiteralPayloadAtDepth(initializer, visits, depth + 1, false);
                },
                .grouped_expression => return self.immutableLiteralPayloadAtDepth(
                    tree.nodeData(node).node_and_token[0],
                    visits,
                    depth + 1,
                    runtime_selectors,
                ),
                .negation, .bit_not, .bool_not => return self.immutableLiteralPayloadAtDepth(
                    tree.nodeData(node).node,
                    visits,
                    depth + 1,
                    runtime_selectors,
                ),
                .array_access => {
                    const base, const index = tree.nodeData(node).node_and_node;
                    if (!try self.immutableLiteralPayloadAtDepth(base, visits, depth + 1, runtime_selectors)) return false;
                    return runtime_selectors or try self.immutableLiteralPayloadAtDepth(index, visits, depth + 1, false);
                },
                .array_mult => {
                    const pattern, const count = tree.nodeData(node).node_and_node;
                    return try self.immutableLiteralPayloadAtDepth(pattern, visits, depth + 1, runtime_selectors) and
                        try self.immutableLiteralPayloadAtDepth(count, visits, depth + 1, false);
                },
                else => {},
            }
            var buffer: [2]Ast.Node.Index = undefined;
            if (tree.fullArrayInit(&buffer, node)) |literal| {
                for (literal.ast.elements) |element|
                    if (!try self.immutableLiteralPayloadAtDepth(element, visits, depth + 1, runtime_selectors)) return false;
                return true;
            }
            if (tree.builtinCallParams(&buffer, node)) |arguments| {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "@as") and arguments.len == 2)
                    return self.immutableLiteralPayloadAtDepth(arguments[1], visits, depth + 1, runtime_selectors);
                if (std.mem.eql(u8, name, "@splat") and arguments.len == 1)
                    return self.immutableLiteralPayloadAtDepth(arguments[0], visits, depth + 1, runtime_selectors);
            }
            return false;
        }

        fn unresolvedValue(self: ResolutionFrame, value: ActualType) !FunctionResolution {
            if (value.is_type_val) return .not_callable;
            if (value.data == .function) return .unknown;
            const ty = (try self.resolver.normalizedType(value)) orelse return .unknown;
            const tag = self.resolver.typeTag(ty) orelse return .unknown;
            return switch (tag) {
                .pointer, .optional, .error_union, .@"fn", .@"opaque" => .unknown,
                else => .not_callable,
            };
        }

        fn unresolvedNode(self: ResolutionFrame, node: Ast.Node.Index) !FunctionResolution {
            const value = (try self.resolveValueOfNode(node)) orelse return .unknown;
            return self.unresolvedValue(value);
        }

        fn referenceOfDeclaration(
            self: ResolutionFrame,
            declaration: Analyser.DeclWithHandle,
            depth: usize,
        ) !FunctionResolution {
            if (depth >= max_returned_callable_depth) return .unknown;
            const framed = try self.declarationInFrame(declaration);
            const frame = try self.frameForDeclaration(framed);
            switch (framed.decl) {
                .ast_node => |node| {
                    const tree = &framed.handle.document.tree;
                    switch (tree.nodeTag(node)) {
                        .fn_decl,
                        .fn_proto,
                        .fn_proto_multi,
                        .fn_proto_one,
                        .fn_proto_simple,
                        => {
                            const value = (try framed.resolveType(&self.resolver.analyser)) orelse
                                return .unknown;
                            if (value.data == .function) {
                                const reference = (try frame.authenticatedReferenceOfValue(value)) orelse
                                    return .unknown;
                                if (!sourceFunctionMatches(reference, framed)) return .unknown;
                                return .{ .function = reference };
                            }
                            return frame.referenceOfValue(value);
                        },
                        .global_var_decl,
                        .local_var_decl,
                        .aligned_var_decl,
                        .simple_var_decl,
                        => {
                            if (!framed.isConst()) {
                                const value = (try framed.resolveType(&self.resolver.analyser)) orelse
                                    return .unknown;
                                return frame.unresolvedValue(value);
                            }
                            const initializer = tree.fullVarDecl(node).?.ast.init_node.unwrap() orelse {
                                const value = (try framed.resolveType(&self.resolver.analyser)) orelse
                                    return .unknown;
                                return frame.unresolvedValue(value);
                            };
                            return frame.functionReferenceOfNode(initializer, depth + 1);
                        },
                        else => {
                            const value = (try framed.resolveType(&self.resolver.analyser)) orelse
                                return .unknown;
                            return frame.unresolvedValue(value);
                        },
                    }
                },
                else => {
                    const value = (try framed.resolveType(&self.resolver.analyser)) orelse
                        return .unknown;
                    return frame.referenceOfValue(value);
                },
            }
        }
        fn declarationForCallableNode(
            self: ResolutionFrame,
            node: Ast.Node.Index,
        ) Analyser.Error!?Analyser.DeclWithHandle {
            const tree = &self.handle.document.tree;
            switch (tree.nodeTag(node)) {
                .identifier => {
                    const token = tree.nodeMainToken(node);
                    return self.resolver.analyser.lookupSymbolGlobal(
                        self.handle,
                        tree.tokenSlice(token),
                        tree.tokens.items(.start)[token],
                    );
                },
                .field_access => {
                    const lhs_node, const field_token = tree.nodeData(node).node_and_token;
                    var owner = (try self.resolveValueOfNode(lhs_node)) orelse return null;
                    if (!owner.is_type_val) {
                        if (try self.resolver.analyser.resolveDerefType(owner)) |deref| {
                            owner = deref;
                        }
                        if (!owner.is_type_val and owner.data != .container) {
                            owner = try owner.typeOf(&self.resolver.analyser);
                        }
                    }
                    return owner.lookupSymbol(&self.resolver.analyser, tree.tokenSlice(field_token));
                },
                .enum_literal => {
                    // The analyser resolves declaration literals against the
                    // call site's expected container. Authenticate that source,
                    // not another container with the same member spelling.
                    const value = (try self.resolveValueOfNode(node)) orelse return null;
                    const reference = (try self.authenticatedReferenceOfValue(value)) orelse
                        return null;
                    const declaration = (try self.functionDeclarationNode(reference)) orelse
                        return null;
                    return .{
                        .decl = .{ .ast_node = declaration },
                        .handle = reference.handle,
                        .container_type = reference.actual_type.data.function.container_type.*,
                    };
                },
                else => return null,
            }
        }

        fn functionSourceDeclaration(
            self: ResolutionFrame,
            node: Ast.Node.Index,
            depth: usize,
        ) Analyser.Error!?Analyser.DeclWithHandle {
            if (depth >= max_returned_callable_depth) return null;
            const declaration = (try self.declarationForCallableNode(node)) orelse return null;
            const declaration_node = switch (declaration.decl) {
                .ast_node => |found| found,
                else => return null,
            };
            const tree = &declaration.handle.document.tree;
            switch (tree.nodeTag(declaration_node)) {
                .fn_decl,
                .fn_proto,
                .fn_proto_multi,
                .fn_proto_one,
                .fn_proto_simple,
                => {
                    var buffer: [1]Ast.Node.Index = undefined;
                    const proto = tree.fullFnProto(&buffer, declaration_node) orelse return null;
                    if (proto.name_token == null) return null;
                    return declaration;
                },
                .global_var_decl,
                .local_var_decl,
                .aligned_var_decl,
                .simple_var_decl,
                => {
                    if (!declaration.isConst()) return null;
                    const initializer = tree.fullVarDecl(declaration_node).?.ast.init_node.unwrap() orelse
                        return null;
                    const frame = try self.frameForDeclaration(declaration);
                    return frame.functionSourceDeclaration(initializer, depth + 1);
                },
                else => return null,
            }
        }

        /// Resolve a function value from its source declaration. A function
        /// signature on a call's declared return type is not the returned
        /// declaration, so follow const initializers and the factory body.
        fn functionReferenceOfNode(
            self: ResolutionFrame,
            node: Ast.Node.Index,
            depth: usize,
        ) Analyser.Error!FunctionResolution {
            if (depth >= max_returned_callable_depth) return .unknown;
            const tree = &self.handle.document.tree;
            switch (tree.nodeTag(node)) {
                .address_of, .deref => {
                    const value = (try self.resolveValueOfNode(node)) orelse return .unknown;
                    const callable = (try self.resolver.analyser.resolveFuncProtoOfCallable(value)) orelse
                        return self.unresolvedValue(value);
                    if (callable.is_type_val) return .not_callable;
                    return self.functionReferenceOfNode(tree.nodeData(node).node, depth + 1);
                },
                .grouped_expression => return self.functionReferenceOfNode(
                    tree.nodeData(node).node_and_token[0],
                    depth + 1,
                ),
                else => {},
            }
            const is_call = switch (tree.nodeTag(node)) {
                .call, .call_comma, .call_one, .call_one_comma => true,
                else => false,
            };
            const value = if (is_call) null else try self.resolveValueOfNode(node);
            if (!is_call) {
                if (value) |resolved| {
                    if (resolved.is_type_val) return .not_callable;
                    if (resolved.data == .function) {
                        if (try self.functionSourceDeclaration(node, depth + 1)) |source| {
                            if (try self.authenticatedReferenceOfValue(resolved)) |reference| {
                                if (sourceFunctionMatches(reference, source)) {
                                    return .{ .function = reference };
                                }
                            }
                        }
                    } else {
                        switch (tree.nodeTag(node)) {
                            .identifier, .field_access => {},
                            else => return self.referenceOfValue(resolved),
                        }
                    }
                }
            }
            switch (tree.nodeTag(node)) {
                .identifier => {
                    const name_token = tree.nodeMainToken(node);
                    const declaration = (try self.resolver.analyser.lookupSymbolGlobal(
                        self.handle,
                        tree.tokenSlice(name_token),
                        tree.tokens.items(.start)[name_token],
                    )) orelse return self.unresolvedNode(node);
                    return self.referenceOfDeclaration(declaration, depth + 1);
                },
                .field_access => {
                    const declaration = (try self.declarationForCallableNode(node)) orelse
                        return self.unresolvedNode(node);
                    return self.referenceOfDeclaration(declaration, depth + 1);
                },
                .call,
                .call_comma,
                .call_one,
                .call_one_comma,
                => {
                    const factory = switch (try self.functionReferenceOfCallAtDepth(node, depth + 1)) {
                        .function => |reference| reference,
                        .unknown => return .unknown,
                        .not_callable => return .not_callable,
                    };
                    return self.returnedFunctionValue(factory, depth + 1);
                },
                else => {},
            }
            const resolved = value orelse return .unknown;
            if (resolved.is_type_val) return .not_callable;
            if (resolved.data == .function) return .unknown;
            return self.referenceOfValue(resolved);
        }

        fn sameFunctionResolution(a: FunctionResolution, b: FunctionResolution) bool {
            return switch (a) {
                .unknown => b == .unknown,
                .not_callable => b == .not_callable,
                .function => |left| switch (b) {
                    .function => |right| left.fn_token == right.fn_token and
                        left.handle.eql(right.handle) and
                        ActualTypeID.eql(left.actual_type, right.actual_type),
                    else => false,
                },
            };
        }

        fn functionNodeForDeclaration(
            declaration: Analyser.DeclWithHandle,
            fn_token: Ast.TokenIndex,
        ) ?Ast.Node.Index {
            const node = switch (declaration.decl) {
                .ast_node => |node| node,
                else => return null,
            };
            const tree = &declaration.handle.document.tree;
            switch (tree.nodeTag(node)) {
                .fn_decl, .fn_proto, .fn_proto_multi, .fn_proto_one, .fn_proto_simple => {},
                else => return null,
            }
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tree.fullFnProto(&buffer, node) orelse return null;
            if (proto.name_token == null) return null;
            if (proto.ast.fn_token != fn_token) return null;
            return node;
        }
        fn sourceFunctionMatches(
            reference: FunctionReference,
            declaration: Analyser.DeclWithHandle,
        ) bool {
            const function = switch (reference.actual_type.data) {
                .function => |function| function,
                else => return false,
            };
            if (!reference.handle.eql(declaration.handle) or
                functionNodeForDeclaration(declaration, function.fn_token) == null)
            {
                return false;
            }
            if (declaration.container_type) |container| {
                if (!container.eql(function.container_type.*)) return false;
            }
            return true;
        }
        fn functionPrototypeMatches(
            self: ResolutionFrame,
            reference: FunctionReference,
            node: Ast.Node.Index,
        ) Analyser.Error!bool {
            const actual = switch (reference.actual_type.data) {
                .function => |function| function,
                else => return false,
            };
            if (!actual.handle.eql(reference.handle)) return false;

            const tree = &reference.handle.document.tree;
            const declaration: Analyser.DeclWithHandle = .{
                .decl = .{ .ast_node = node },
                .handle = reference.handle,
                .container_type = actual.container_type.*,
            };
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tree.fullFnProto(&buffer, node) orelse return false;
            const name_token = proto.name_token orelse return false;
            if (!std.mem.eql(u8, actual.name orelse return false, tree.tokenSlice(name_token))) return false;
            if (proto.ast.fn_token != actual.fn_token) return false;
            const owner = switch (actual.container_type.data) {
                .container => |container| container.scope_handle,
                else => return false,
            };
            if (!owner.handle.eql(reference.handle)) return false;
            const scopes = try reference.handle.getDocumentScope();
            const declared_owner = Analyser.innermostScopeAtIndexWithTag(
                scopes,
                tree.tokenStart(proto.ast.fn_token),
                .initOne(.container),
            ).unwrap() orelse .root;
            if (owner.scope != declared_owner) return false;
            var source_parameters = proto.iterate(tree);
            var parameter_index: usize = 0;
            var source_has_varargs = false;
            while (source_parameters.next()) |source_parameter| {
                if (source_has_varargs) return false;
                if (source_parameter.anytype_ellipsis3) |token| {
                    switch (tree.tokenTag(token)) {
                        .ellipsis3 => {
                            source_has_varargs = true;
                            continue;
                        },
                        .keyword_anytype => {},
                        else => return false,
                    }
                }
                if (parameter_index >= actual.parameters.len) return false;
                const actual_parameter = actual.parameters[parameter_index];
                parameter_index += 1;
                if (source_parameter.name_token != actual_parameter.name_token) return false;
                const source_modifier: ?Analyser.Type.Data.Parameter.Modifier =
                    if (source_parameter.comptime_noalias) |token|
                        switch (tree.tokenTag(token)) {
                            .keyword_comptime => .comptime_param,
                            .keyword_noalias => .noalias_param,
                            else => return false,
                        }
                    else
                        null;
                if (source_modifier != actual_parameter.modifier) return false;
            }
            if (parameter_index != actual.parameters.len or
                source_has_varargs != actual.has_varargs) return false;

            const resolved = (try declaration.resolveType(&self.resolver.analyser)) orelse return false;
            const source = switch (resolved.data) {
                .function => |function| function,
                else => return false,
            };
            if (source.fn_token != actual.fn_token or
                !source.handle.eql(actual.handle) or
                !source.container_type.eql(actual.container_type.*) or
                source.has_varargs != actual.has_varargs or
                source.parameters.len != actual.parameters.len or
                !source.return_value.eql(actual.return_value.*))
            {
                return false;
            }
            for (source.parameters, actual.parameters) |source_parameter, actual_parameter| {
                if (!source_parameter.type.eql(actual_parameter.type)) return false;
            }
            return true;
        }

        fn authenticatedReferenceOfValue(
            self: ResolutionFrame,
            value: ActualType,
        ) Analyser.Error!?FunctionReference {
            if (value.is_type_val or value.data != .function) return null;
            const reference = switch (referenceOfCallable(value)) {
                .function => |reference| reference,
                else => unreachable,
            };
            const node = (try self.functionDeclarationNode(reference)) orelse return null;
            if (!try self.functionPrototypeMatches(reference, node)) return null;
            return reference;
        }

        fn functionDeclarationNode(
            self: ResolutionFrame,
            reference: FunctionReference,
        ) !?Ast.Node.Index {
            const function = switch (reference.actual_type.data) {
                .function => |function| function,
                else => return null,
            };
            const tree = &reference.handle.document.tree;
            const name = function.name orelse return null;
            const source_index = tree.tokens.items(.start)[function.fn_token];
            if (try self.resolver.analyser.lookupSymbolGlobal(
                reference.handle,
                name,
                source_index,
            )) |decl| {
                if (functionNodeForDeclaration(decl, function.fn_token)) |node| return node;
            }

            var owner = function.container_type.*;
            if (!owner.is_type_val) owner = try owner.typeOf(&self.resolver.analyser);
            if (try owner.lookupSymbol(&self.resolver.analyser, name)) |decl| {
                if (functionNodeForDeclaration(decl, function.fn_token)) |node| return node;
            }

            const scopes = try reference.handle.getDocumentScope();
            const scope_index_type = @TypeOf(Analyser.innermostScopeAtIndex(scopes, 0));
            for (0..scopes.scopes.items(.parent_scope).len) |raw_index| {
                const index: scope_index_type = @enumFromInt(raw_index);
                if (scopes.getScopeTag(index) != .function) continue;
                const node = scopes.getScopeAstNode(index).?;
                if (functionNodeForDeclaration(.{
                    .decl = .{ .ast_node = node },
                    .handle = reference.handle,
                }, function.fn_token)) |found| return found;
            }
            return null;
        }

        fn returnedFunctionValue(
            self: ResolutionFrame,
            reference: FunctionReference,
            depth: usize,
        ) !FunctionResolution {
            if (depth >= max_returned_callable_depth) return .unknown;
            const function_node = (try self.functionDeclarationNode(reference)) orelse return .unknown;
            const tree = &reference.handle.document.tree;
            if (tree.nodeTag(function_node) != .fn_decl) return .unknown;
            const body = tree.nodeData(function_node).node_and_node[1];
            var walker = try AstWalker.init(self.resolver.gpa, tree, body);
            defer walker.deinit(self.resolver.gpa);
            const frame = self.resolver.frameForFunction(reference);
            var answer: ?FunctionResolution = null;

            while (try walker.next(self.resolver.gpa, tree)) |event| {
                switch (event) {
                    .open => |node| switch (tree.nodeTag(node)) {
                        .fn_decl => walker.skip(),
                        .@"return" => {
                            const expression = tree.nodeData(node).opt_node.unwrap() orelse return .not_callable;
                            const returned = try frame.functionReferenceOfNode(expression, depth + 1);
                            if (answer) |previous| {
                                if (!sameFunctionResolution(previous, returned)) return .unknown;
                            } else {
                                answer = returned;
                            }
                        },
                        else => {},
                    },
                    .close => {},
                }
            }
            return answer orelse .unknown;
        }

        fn referenceOfValue(self: ResolutionFrame, value: ActualType) !FunctionResolution {
            if (value.is_type_val) return .not_callable;
            if (value.data == .function) return .unknown;
            const ty = (try self.resolver.normalizedType(value)) orelse return .unknown;
            const tag = self.resolver.typeTag(ty) orelse return .unknown;
            return switch (tag) {
                .pointer, .optional, .error_union, .@"fn", .@"opaque" => .unknown,
                else => .not_callable,
            };
        }

        fn referenceOfCallable(callable: ActualType) FunctionResolution {
            const function = callable.data.function;
            return .{ .function = .{
                .tree = &function.handle.document.tree,
                .fn_token = function.fn_token,
                .handle = function.handle,
                .actual_type = callable,
            } };
        }

        pub fn functionReference(
            self: ResolutionFrame,
            node: Ast.Node.Index,
        ) !FunctionResolution {
            return self.functionReferenceOfNode(node, 0);
        }

        fn functionReferenceOfCallAtDepth(
            self: ResolutionFrame,
            node: Ast.Node.Index,
            depth: usize,
        ) Analyser.Error!FunctionResolution {
            var buffer: [2]Ast.Node.Index = undefined;
            const call = CallOperands.full(&self.handle.document.tree, &buffer, node) orelse return .unknown;
            const reference = switch (try self.functionReferenceOfNode(call.ast.fn_expr, depth + 1)) {
                .function => |reference| reference,
                .unknown => return .unknown,
                .not_callable => return .not_callable,
            };
            const reached = (try self.reachedCallable(call, reference.actual_type)) orelse return .unknown;
            const callable = try Analyser.resolveFunctionTypeFromCall(
                &self.resolver.analyser,
                self.options(call.ast.fn_expr),
                call,
                reached.callable,
            );
            return referenceOfCallable(callable);
        }

        /// Preserve the actual call's formal anytype/comptime bindings in
        /// the reached function, rather than resolving only its spelling.
        pub fn functionReferenceOfCall(
            self: ResolutionFrame,
            node: Ast.Node.Index,
        ) !FunctionResolution {
            return self.functionReferenceOfCallAtDepth(node, 0);
        }

        /// Resolve each iteration of a direct, type-valued inline tuple loop.
        /// The complete tuple supplies the census; merged payload types do not.
        /// Returned references borrow the resolver's arena.
        pub fn inlineTupleCallReferences(
            self: ResolutionFrame,
            node: Ast.Node.Index,
            remaining: *u32,
            instances_remaining: *usize,
        ) !?[]const FunctionReference {
            const tree = &self.handle.document.tree;
            var call_buffer: [2]Ast.Node.Index = undefined;
            const call = CallOperands.full(tree, &call_buffer, node) orelse return null;
            var has_loop_payload = false;
            for (call.ast.params) |argument| {
                if (remaining.* == 0) return error.InlineTupleStepsExceeded;
                remaining.* -= 1;
                if (tree.nodeTag(argument) != .identifier) continue;
                const argument_token = tree.nodeMainToken(argument);
                const declaration = (try self.resolver.analyser.lookupSymbolGlobal(
                    self.handle,
                    tree.tokenSlice(argument_token),
                    tree.tokenStart(argument_token),
                )) orelse continue;
                if (declaration.decl == .for_loop_payload) {
                    has_loop_payload = true;
                    break;
                }
            }
            if (!has_loop_payload) return null;
            const token = tree.nodeMainToken(node);
            var selected: ?Ast.Node.Index = null;
            var enclosing_function_token: Ast.TokenIndex = 0;
            for (tree.nodes.items(.tag), 0..) |tag, raw| {
                if (remaining.* == 0) return error.InlineTupleStepsExceeded;
                remaining.* -= 1;
                const candidate: Ast.Node.Index = @enumFromInt(raw);
                if (tag == .fn_decl or tag == .test_decl) {
                    if (tree.firstToken(candidate) <= token and token <= tree.lastToken(candidate))
                        enclosing_function_token = @max(enclosing_function_token, tree.firstToken(candidate));
                    continue;
                }
                if (tag != .@"for" and tag != .for_simple) continue;
                const loop = ast.fullFor(tree, candidate).?;
                if (token < tree.firstToken(loop.ast.then_expr) or token > tree.lastToken(loop.ast.then_expr)) continue;
                if (loop.inline_token == null or selected != null) return null;
                selected = candidate;
            }
            const loop_node = selected orelse return null;
            // A nested function is not an iteration of its enclosing loop.
            if (enclosing_function_token > tree.firstToken(loop_node)) return null;
            const loop = ast.fullFor(tree, loop_node).?;
            if (loop.ast.inputs.len != 1 or tree.tokenTag(loop.payload_token) != .identifier or
                tree.tokenTag(loop.payload_token + 1) != .pipe) return null;
            var tuple_buffer: [2]Ast.Node.Index = undefined;
            const tuple = tree.fullArrayInit(&tuple_buffer, loop.ast.inputs[0]) orelse return null;
            if (tuple.ast.type_expr != .none or tuple.ast.elements.len == 0) return null;
            // Enforce the caller's existing whole-query limits before allocating
            // references or resolving/cloning any iteration frame.
            if (tuple.ast.elements.len > instances_remaining.*) return error.InlineTupleCallersExceeded;
            if (tuple.ast.elements.len > remaining.*) return error.InlineTupleStepsExceeded;
            instances_remaining.* -= tuple.ast.elements.len;
            remaining.* -= @intCast(tuple.ast.elements.len);
            const arena = self.resolver.analyser.arena.allocator();
            const references = try arena.alloc(FunctionReference, tuple.ast.elements.len);
            for (tuple.ast.elements, references) |element, *reference| {
                const actual = (try self.resolveValueOfNode(element)) orelse return null;
                if (!actual.is_type_val) return null;
                var container: ActualType.Data.Container = if (self.container_type) |context|
                    if (context.data == .container) context.data.container else return null
                else
                    .{ .scope_handle = .{ .handle = self.handle, .scope = .root }, .bound_params = .empty };
                container.bound_params = try container.bound_params.clone(arena);
                try container.bound_params.put(arena, .{ .token = loop.payload_token, .handle = self.handle }, actual);
                var iteration = self;
                iteration.container_type = .{ .data = .{ .container = container }, .is_type_val = true };
                reference.* = switch (try iteration.functionReferenceOfCall(node)) {
                    .function => |found| found,
                    else => return null,
                };
            }
            return references;
        }

        pub fn typeParameterReference(self: ResolutionFrame, node: Ast.Node.Index) !?TypeParameterReference {
            const value = (try self.resolveValueOfNode(node)) orelse return null;
            const parameter = switch (value.data) {
                .type_parameter => |reference| reference,
                else => return null,
            };
            return .{ .tree = &parameter.handle.document.tree, .token = parameter.token };
        }

        fn reachedCall(self: ResolutionFrame, buffer: *[2]Ast.Node.Index, node: Ast.Node.Index) !?ReachedCall {
            const call = CallOperands.full(&self.handle.document.tree, buffer, node) orelse return null;
            if (try self.resolveValueOfNode(call.ast.fn_expr)) |value| {
                if (try self.resolver.analyser.resolveFuncProtoOfCallable(value)) |callable| {
                    if (try self.reachedCallable(call, callable)) |reached| return reached;
                }
            }
            // Raw expression resolution can lose a block-local alias's
            // instantiated owner. The canonical source reference retains it.
            // Type-only signatures still describe dynamic calls above.
            const reference = switch (try self.functionReference(call.ast.fn_expr)) {
                .function => |reference| reference,
                else => return null,
            };
            return self.reachedCallable(call, reference.actual_type);
        }

        fn reachedCallable(self: ResolutionFrame, call: CallOperands, callable: ActualType) !?ReachedCall {
            if (callable.is_type_val or callable.data.function.has_varargs) return null;
            const receiver = call.ast.params.len + 1 == callable.data.function.parameters.len and
                try self.resolver.analyser.isInstanceCall(self.options(call.ast.fn_expr), call, callable);
            if (call.ast.params.len + @intFromBool(receiver) != callable.data.function.parameters.len) return null;
            return .{ .call = call, .receiver = receiver, .parameters = callable.data.function.parameters, .callable = callable };
        }

        pub fn callArgument(self: ResolutionFrame, node: Ast.Node.Index, parameter: usize) !?Ast.Node.Index {
            var buffer: [2]Ast.Node.Index = undefined;
            return self.callArgumentIn(&buffer, node, parameter);
        }

        pub fn callArgumentIn(self: ResolutionFrame, buffer: *[2]Ast.Node.Index, node: Ast.Node.Index, parameter: usize) !?Ast.Node.Index {
            const reached = (try self.reachedCall(buffer, node)) orelse return null;
            if (parameter >= reached.parameters.len) return null;
            if (reached.receiver and parameter == 0)
                return self.handle.document.tree.nodeData(reached.call.ast.fn_expr).node_and_token[0];
            return reached.call.ast.params[parameter - @intFromBool(reached.receiver)];
        }

        pub fn callArgumentsOf(self: ResolutionFrame, buffer: *[2]Ast.Node.Index, node: Ast.Node.Index) !?CallArguments {
            const reached = (try self.reachedCall(buffer, node)) orelse return null;
            return .{
                .arguments = reached.call.ast.params,
                .receiver = if (reached.receiver)
                    self.handle.document.tree.nodeData(reached.call.ast.fn_expr).node_and_token[0]
                else
                    null,
            };
        }

        pub fn containerOfNode(self: ResolutionFrame, node: Ast.Node.Index) !?ActualType.Data.Container {
            var ty = (try self.typeOfNode(node)) orelse return null;
            for (0..32) |_| {
                if (ty.data == .container) return ty.data.container;
                ty = (try self.resolver.normalizedType(self.resolver.childType(ty) orelse return null)) orelse return null;
            }
            return null;
        }

        pub fn intInfo(self: ResolutionFrame, node: Ast.Node.Index) !?IntInfo {
            const tree = &self.handle.document.tree;
            var buffer: [2]Ast.Node.Index = undefined;
            if (tree.builtinCallParams(&buffer, node)) |params| {
                if (params.len == 1 and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@intFromEnum")) {
                    return self.resolver.enumTagIntInfoOfType((try self.typeOfNode(params[0])) orelse return null);
                }
            }
            return self.resolver.intInfoOfType((try self.typeOfNode(node)) orelse return null);
        }

        /// Integer result location under this exact actual frame, including
        /// optional and error-union payloads rather than their wrapper types.
        pub fn contextIntInfo(self: ResolutionFrame, node: Ast.Node.Index) !?IntInfo {
            var expected = (try self.expectedTypeOfNode(node)) orelse return null;
            for (0..128) |_| {
                switch (self.resolver.typeTag(expected) orelse return null) {
                    .optional, .error_union =>
                        expected = self.resolver.childType(expected) orelse return null,
                    else => return self.resolver.intInfoOfType(expected),
                }
            }
            return null;
        }

        pub fn floatBits(self: ResolutionFrame, node: Ast.Node.Index) !?u16 {
            const ty = (try self.typeOfNode(node)) orelse return null;
            const tag = self.resolver.typeTag(ty) orelse return null;
            if (tag != .float and tag != .comptime_float) return null;
            return self.resolver.ctx.ip.floatBits(ty.ipIndex() orelse return null, builtin.target);
        }

        pub fn isBoolType(self: ResolutionFrame, node: Ast.Node.Index) !?bool {
            const ty = (try self.typeOfNode(node)) orelse return null;
            return (self.resolver.typeTag(ty) orelse return null) == .bool;
        }

        pub fn isEnumType(self: ResolutionFrame, node: Ast.Node.Index) !?bool {
            var ty = (try self.typeOfNode(node)) orelse return null;
            for (0..32) |_| {
                const tag = self.resolver.typeTag(ty) orelse return null;
                if (tag != .optional) return tag == .@"enum";
                ty = (try self.resolver.normalizedType(self.resolver.childType(ty) orelse return null)) orelse return null;
            }
            return null;
        }

        pub fn typeRefIsPointerLike(self: ResolutionFrame, node: Ast.Node.Index) !?bool {
            const ty = (try self.typeOfNode(node)) orelse return null;
            const tag = self.resolver.typeTag(ty) orelse return null;
            return tag == .pointer or tag == .optional;
        }

        pub fn isStdAllocator(self: ResolutionFrame, node: Ast.Node.Index) !?bool {
            const container = (try self.containerOfNode(node)) orelse return null;
            if (container.scope_handle.scope != .root) return false;
            return try self.resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/mem/Allocator.zig");
        }

        /// Resolve the genuine SDK list constant in this lexical frame.
        pub fn stdCollectionEmptyOf(self: ResolutionFrame, node: Ast.Node.Index, declared_type: ?Ast.Node.Index) !bool {
            const tree = &self.handle.document.tree;
            const owner_node = switch (tree.nodeTag(node)) {
                .enum_literal => blk: {
                    if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "empty")) return false;
                    break :blk declared_type orelse return false;
                },
                .field_access => blk: {
                    const access = tree.nodeData(node).node_and_token;
                    if (!std.mem.eql(u8, tree.tokenSlice(access[1]), "empty")) return false;
                    const owner = (try self.resolveValueOfNode(access[0])) orelse return false;
                    if (!owner.is_type_val) return false;
                    break :blk access[0];
                },
                else => return false,
            };
            const ty = (try self.typeOfNode(owner_node)) orelse return false;
            if (ty.data != .container or self.resolver.typeTag(ty) != .@"struct") return false;
            if (!try self.resolver.declaredInToolchainFile(ty.data.container.scope_handle.handle, "/std/array_list.zig")) return false;
            const declaration = (try Analyser.lookupSymbolContainer(ty, "empty", .other)) orelse return false;
            if (!declaration.isConst()) return false;
            const declaration_node = switch (declaration.decl) {
                .ast_node => |value| value,
                else => return false,
            };
            const source = &declaration.handle.document.tree;
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

        pub fn stdCollectionAppendOf(self: ResolutionFrame, callee: Ast.Node.Index, arguments: usize) !StdCollectionAppend {
            const reference = switch (try self.functionReference(callee)) {
                .function => |reference| reference,
                else => return .no,
            };
            const declaration = reference.actual_type.data.function;
            if (!try self.resolver.declaredInToolchainFile(declaration.handle, "/std/array_list.zig")) return .no;
            const name = declaration.name orelse return .no;
            if (!std.mem.eql(u8, name, "append") and !std.mem.eql(u8, name, "appendAssumeCapacity")) return .no;
            if (declaration.parameters.len != arguments + 1) return .no;
            const result = (try self.resolver.normalizedType(declaration.return_value.*)) orelse return .fallible;
            return if (self.resolver.typeTag(result) == .void) .infallible else .fallible;
        }

        pub fn stdMemEqlOf(self: ResolutionFrame, callee: Ast.Node.Index, arguments: usize) !bool {
            if (arguments != 3) return false;
            const reference = switch (try self.functionReference(callee)) {
                .function => |reference| reference,
                else => return false,
            };
            const declaration = reference.actual_type.data.function;
            if (declaration.parameters.len != 3) return false;
            if (!std.mem.eql(u8, declaration.name orelse return false, "eql")) return false;
            return self.resolver.declaredInToolchainFile(declaration.handle, "/std/mem.zig");
        }

        pub fn stdTestingExpectOf(self: ResolutionFrame, callee: Ast.Node.Index, arguments: usize) !bool {
            if (arguments != 1) return false;
            const reference = switch (try self.functionReference(callee)) {
                .function => |reference| reference,
                else => return false,
            };
            const declaration = reference.actual_type.data.function;
            if (declaration.parameters.len != 1) return false;
            if (!std.mem.eql(u8, declaration.name orelse return false, "expect")) return false;
            return self.resolver.declaredInToolchainFile(declaration.handle, "/std/testing.zig");
        }
    };

    pub fn resolutionFrame(self: *TypeResolver) ResolutionFrame {
        return .{ .resolver = self, .handle = self.handle, .container_type = null };
    }

    pub fn frameForFunction(self: *TypeResolver, reference: FunctionReference) ResolutionFrame {
        const container = reference.actual_type.data.function.container_type.*;
        return .{
            .resolver = self,
            .handle = reference.handle,
            // Lexical @This() is a type value; the complete callable retains
            // its original instance flag for implicit-receiver resolution.
            .container_type = if (container.data == .container)
                .{ .data = container.data, .is_type_val = true }
            else
                container,
            .actual_type = reference.actual_type,
        };
    }

    pub fn frameForContainer(self: *TypeResolver, container: ActualType.Data.Container) ResolutionFrame {
        return .{
            .resolver = self,
            .handle = container.scope_handle.handle,
            .container_type = .{ .data = .{ .container = container }, .is_type_val = true },
        };
    }

    /// The reached declaration and complete instantiated function value.
    /// `handle` and `tree` borrow its immutable source document. `actual_type`
    /// borrows this resolver's arena, which must outlive all memo keys built
    /// from it. Use `frameForFunction` on the original resolver for body
    /// queries: opening a foreign document alone cannot restore its bindings.
    pub const FunctionReference = struct {
        tree: *const Ast,
        fn_token: Ast.TokenIndex,
        handle: DocumentStore.Handle,
        actual_type: ActualType,
    };

    /// Unknown references cannot close a caller set. A resolved non-callable
    /// value is different: it cannot refer to any function declaration.
    pub const FunctionResolution = union(enum) {
        unknown,
        not_callable,
        function: FunctionReference,
    };

    pub fn functionReference(self: *TypeResolver, node: Ast.Node.Index) !FunctionResolution {
        return self.resolutionFrame().functionReference(node);
    }

    pub fn functionReferenceOfCall(self: *TypeResolver, node: Ast.Node.Index) !FunctionResolution {
        return self.resolutionFrame().functionReferenceOfCall(node);
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
        return .{ .tree = &parameter.handle.document.tree, .token = parameter.token };
    }

    /// The declaration a call reaches and the parameters this call
    /// actually uses.  `call` points into `buffer` for the fixed-arity
    /// call shapes, so it is valid only while that buffer lives and
    /// never escapes the function that read it.
    const ReachedCall = struct {
        call: CallOperands,
        receiver: bool,
        /// The callee's own parameter list, borrowed from the resolved
        /// declaration.  The arity this call was proved against IS this
        /// slice's length, so every answer that maps a parameter to an
        /// argument indexes the same list the arity was checked against.
        parameters: []const Analyser.Type.Data.Parameter,
        callable: ActualType,
    };

    /// Every rule this snapshot applies to decide which declaration a
    /// call reaches: the callee's own type, the variadic rule, whether
    /// the call passes a receiver implicitly, and the arity.  One
    /// place decides them, so `callArgument` and `callArguments` cannot
    /// disagree about which expression a parameter received.
    fn reachedCall(
        self: *TypeResolver,
        buffer: *[2]Ast.Node.Index,
        node: Ast.Node.Index,
    ) !?ReachedCall {
        return self.resolutionFrame().reachedCall(buffer, node);
    }

    /// Map a declared parameter to its actual argument, including method receivers.
    pub fn callArgument(self: *TypeResolver, node: Ast.Node.Index, parameter: usize) !?Ast.Node.Index {
        var buffer: [2]Ast.Node.Index = undefined;
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
        buffer: *[2]Ast.Node.Index,
        node: Ast.Node.Index,
        parameter: usize,
    ) !?Ast.Node.Index {
        return self.resolutionFrame().callArgumentIn(buffer, node, parameter);
    }

    /// The call's own written arguments, plus the expression an
    /// instance call passes implicitly (`receiver`, null when the call
    /// writes every argument itself).
    ///
    /// Larger operand lists borrow immutable AST data. Small ordinary calls
    /// and literal `@call` tuples borrow the two-node caller scratch instead;
    /// no operand list is heap-allocated or truncated. The scratch must stay
    /// live until the caller finishes reading every borrowed node.
    pub const CallArguments = struct {
        arguments: []const Ast.Node.Index,
        receiver: ?Ast.Node.Index,
    };

    pub fn callArgumentsOf(
        self: *TypeResolver,
        buffer: *[2]Ast.Node.Index,
        node: Ast.Node.Index,
    ) !?CallArguments {
        return self.resolutionFrame().callArgumentsOf(buffer, node);
    }

    /// The declared type of the parameter an ACTUAL argument is passed as
    /// at the declaration this call reaches, the receiver counting when the
    /// call is an instance call.  Null on exactly the calls `callArgument`
    /// answers null for — a variadic callee, an arity the declaration does
    /// not have, a callee this snapshot cannot name.
    fn argumentParameterType(self: *TypeResolver, node: Ast.Node.Index, argument: usize) !?Analyser.Type {
        var buffer: [2]Ast.Node.Index = undefined;
        const reached = (try self.reachedCall(&buffer, node)) orelse return null;
        if (argument >= reached.call.ast.params.len) return null;
        // The arity `reachedCall` proved keeps this index inside the
        // declaration's own list: every written argument has a parameter
        // behind it, and the receiver shifts the index by one.
        return reached.parameters[argument + @intFromBool(reached.receiver)].type;
    }

    fn intInfoOfType(self: *TypeResolver, value: Analyser.Type) !?IntInfo {
        const resolved = (try self.normalizedType(value)) orelse return null;
        if ((self.typeTag(resolved) orelse return null) != .int) return null;
        const index = resolved.ipIndex() orelse return null;
        const info = self.ctx.ip.intInfo(index, builtin.target);
        return .{ .signed = info.signedness == .signed, .bits = info.bits };
    }

    /// Signedness and bit-width of the integer type an argument is coerced
    /// to by the parameter it is passed as.
    pub fn argumentIntInfo(self: *TypeResolver, node: Ast.Node.Index, argument: usize) !?IntInfo {
        const parameter = (try self.argumentParameterType(node, argument)) orelse return null;
        return self.intInfoOfType(parameter);
    }

    /// Integer result-location type in this node's exact source context.
    ///
    /// Read the nearest ancestor relationship, not an enclosing call's whole
    /// argument: a struct or union initializer contributes its selected field
    /// type, and @as fixes its operand before an outer call can coerce it.
    /// Optional and error-union result locations contribute their payload.
    /// Unknown contexts and other non-integer destinations remain unknown.
    pub fn contextIntInfo(self: *TypeResolver, node: Ast.Node.Index) !?IntInfo {
        return self.resolutionFrame().contextIntInfo(node);
    }

    pub fn externUnionFloatFieldBits(self: *TypeResolver, node: Ast.Node.Index, field_name: []const u8) !?u16 {
        const ty = (try self.typeOfNode(node)) orelse return null;
        if (self.typeTag(ty) != .@"union" or ty.data != .container) return null;
        const scope = ty.data.container.scope_handle;
        const tree = &scope.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const container = tree.fullContainerDecl(&buffer, scope.toNode()) orelse return null;
        if (tree.tokenTag(container.layout_token orelse return null) != .keyword_extern) return null;
        const declaration = (try Analyser.lookupSymbolContainer(ty, field_name, .field)) orelse return null;
        const value = (try declaration.resolveType(&self.analyser)) orelse return null;
        const field_type = (try self.normalizedType(value)) orelse return null;
        if (self.typeTag(field_type) != .float) return null;
        return self.ctx.ip.floatBits(field_type.ipIndex() orelse return null, builtin.target);
    }

    /// Classify a resolved type value from this resolver's actual context.
    /// Unknown types answer null; the caller must supply a type value.
    pub fn typeTag(self: *TypeResolver, ty: ActualType) ?std.builtin.TypeId {
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
                const tree = &container.scope_handle.handle.document.tree;
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

    /// Return one pointer, array, vector, optional child, or error-union payload.
    /// The child borrows the original resolver; non-wrapper types answer null.
    pub fn childType(self: *TypeResolver, ty: ActualType) ?ActualType {
        std.debug.assert(ty.is_type_val);
        return switch (ty.data) {
            .pointer => |info| info.elem_ty.*,
            .array => |info| info.elem_ty.*,
            .optional => |payload| payload.*,
            .error_union => |info| info.payload.*,
            .ip_index => blk: {
                const index = ty.ipIndex() orelse return null;
                const child = switch (self.ctx.ip.indexToKey(index)) {
                    .pointer_type => |info| info.elem_type,
                    .array_type => |info| info.child,
                    .vector_type => |info| info.child,
                    .optional_type => |info| info.payload_type,
                    .error_union_type => |info| info.payload_type,
                    else => return null,
                };
                break :blk Analyser.Type.fromIP(&self.analyser, .type_type, child);
            },
            else => null,
        };
    }

    /// Classify a resolved type value without unwrapping its pointee.
    /// Null means this type did not resolve to a pointer; `ty` must be a type
    /// value obtained through this resolver or one of its borrowed frames.
    pub fn pointerSize(self: *TypeResolver, ty: ActualType) ?std.builtin.Type.Pointer.Size {
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

    pub fn containerOfNode(self: *TypeResolver, node: Ast.Node.Index) !?Analyser.Type.Data.Container {
        return self.resolutionFrame().containerOfNode(node);
    }

    /// Declaration name within the defining document, not a dispatch identity.
    ///
    /// The bytes are the arena's and are borrowed until `deinit`; the caller
    /// neither owns nor frees them, which is what makes it safe to hand back
    /// the one answer a later question about the same declaration reuses.
    pub fn typeNameOfNode(self: *TypeResolver, node: Ast.Node.Index) !?[]const u8 {
        const container = (try self.containerOfNode(node)) orelse return null;
        return self.containerNameOf(container);
    }

    /// The name `container` has in the document that declares it, derived
    /// once per declaration site and read from the memo afterwards.
    ///
    /// Deriving the name is the question, and a scan that runs out of
    /// memory answers nothing: the retry answers from what it finds rather
    /// than from an unfinished question.  Writing the answer down is only
    /// what makes the next question about this site a lookup, so a memo
    /// that will not grow costs the NEXT question a walk — never this one
    /// its name, which is complete before the write is attempted.
    fn containerNameOf(self: *TypeResolver, container: Analyser.Type.Data.Container) !?[]const u8 {
        const key = container.scope_handle;
        if (self.name_cache.get(key)) |settled| return settled.answer();
        const scanned = try scanContainerName(self.arena.allocator(), container);
        self.name_cache.put(self.gpa, key, if (scanned) |text| .{ .named = text } else .unnamed) catch {};
        return scanned;
    }

    /// True when `handle`'s document is this toolchain's `zig_lib/<suffix>`.
    /// Declaring-document identity, never a leaf name: a same-named local
    /// declaration lives in another document and cannot match.
    ///
    /// Both sides are canonical.  `zig env` reports the library directory
    /// the compiler was reached through, which may contain a symlink,
    /// while every URI the store serves is canonicalized — comparing the
    /// two raw makes the whole standard library stop existing for the
    /// analysis, silently, with no diagnostic.
    pub fn declaredInToolchainFile(
        self: *TypeResolver,
        handle: DocumentStore.Handle,
        suffix: []const u8,
    ) !bool {
        const library = self.ctx.store.toolchainRoot() orelse return false;
        // The path is compared and dropped: asked per call, it must not
        // pile up in the arena.
        var scratch = std.heap.stackFallback(std.Io.Dir.max_path_bytes, self.gpa);
        const scratch_allocator = scratch.get();
        const path = try handle.document.uri.toFsPath(scratch_allocator);
        defer scratch_allocator.free(path);
        const base = std.mem.trimEnd(u8, library, std.fs.path.sep_str);
        return path.len == base.len + suffix.len and
            std.mem.startsWith(u8, path, base) and std.mem.endsWith(u8, path, suffix);
    }

    /// `declaredInToolchainFile` for a whole directory: true when `handle`
    /// is a document anywhere below `<toolchain library>/<directory>`
    /// (`"/std"` is the standard library).  Same canonical comparison, same
    /// identity rule: a project file that merely shares a spelling is not below it.
    pub fn declaredUnderToolchain(
        self: *TypeResolver,
        handle: DocumentStore.Handle,
        directory: []const u8,
    ) !bool {
        const library = self.ctx.store.toolchainRoot() orelse return false;
        var scratch = std.heap.stackFallback(std.Io.Dir.max_path_bytes, self.gpa);
        const scratch_allocator = scratch.get();
        const path = try handle.document.uri.toFsPath(scratch_allocator);
        defer scratch_allocator.free(path);
        const base = std.mem.trimEnd(u8, library, std.fs.path.sep_str);
        return path.len > base.len + directory.len and
            std.mem.startsWith(u8, path, base) and
            std.mem.startsWith(u8, path[base.len..], directory) and
            std.fs.path.isSep(path[base.len + directory.len]);
    }

    pub fn isStdAllocator(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        return self.resolutionFrame().isStdAllocator(node);
    }

    /// Prove the resolved std-list empty constant from its actual initializer.
    /// A same-named project constant or an omitted storage field is not proof.
    pub fn stdCollectionEmptyOf(
        self: *TypeResolver,
        node: Ast.Node.Index,
        declared_type: ?Ast.Node.Index,
    ) !bool {
        return self.resolutionFrame().stdCollectionEmptyOf(node, declared_type);
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
        return self.resolutionFrame().stdCollectionAppendOf(callee, arguments);
    }

    /// The compiler's own slice equality function only reads its operands.
    /// Resolve the declaration, so aliases match and project lookalikes do not.
    pub fn stdMemEqlOf(self: *TypeResolver, callee: Ast.Node.Index, arguments: usize) !bool {
        return self.resolutionFrame().stdMemEqlOf(callee, arguments);
    }

    /// Match standard testing assertions through their declaring toolchain document.
    pub fn stdTestingExpectOf(self: *TypeResolver, callee: Ast.Node.Index, arguments: usize) !bool {
        return self.resolutionFrame().stdTestingExpectOf(callee, arguments);
    }

    /// Name usable for dispatch from this file. Never substitute a foreign
    /// declaration's leaf name for an unrelated local declaration.
    ///
    /// Borrowing, as `typeNameOfNode` is: the joined spelling is the
    /// resolver's, is built once per declaration site, and stays readable
    /// until `deinit` however many questions are asked in between.
    ///
    /// Deriving the spelling is the question and running out of memory
    /// halfway through it answers nothing; writing it down is the
    /// accelerator, so a memo that will not grow costs the next question
    /// the derivation rather than this one the spelling it has already got.
    pub fn typeReferenceOfNode(self: *TypeResolver, node: Ast.Node.Index) !?[]const u8 {
        const container = (try self.containerOfNode(node)) orelse return null;
        const key = container.scope_handle;
        if (self.reference_cache.get(key)) |settled| return settled.answer();
        const spelled = try self.spellContainerReference(container);
        self.reference_cache.put(self.gpa, key, if (spelled) |text| .{ .named = text } else .unnamed) catch {};
        return spelled;
    }

    /// The spelling this document dispatches on: its own name for a
    /// declaration it owns, and its own alias for the file the declaration
    /// lives in joined to the name otherwise.  A file this document does not
    /// import is a file it cannot name, however its declaration is spelled
    /// where it is declared.
    fn spellContainerReference(
        self: *TypeResolver,
        container: Analyser.Type.Data.Container,
    ) !?[]const u8 {
        const name = (try self.containerNameOf(container)) orelse return null;
        if (container.scope_handle.handle.eql(self.handle)) return name;
        const alias = (try self.importAliasOf(
            container.scope_handle.handle.document.uri.raw,
            container.scope_handle.handle.module,
        )) orelse return null;
        if (container.scope_handle.scope == .root) return alias;
        return try std.fmt.allocPrint(self.arena.allocator(), "{s}.{s}", .{ alias, name });
    }

    /// The name this document binds `target_uri` in `module` under, if any.
    ///
    /// Resolution walks this document's own `@import` bindings once and then
    /// answers from the cache, so asking about a second declaration in the
    /// same imported file costs a hash lookup instead of re-reading every
    /// root declaration and re-resolving every import string.  A miss is
    /// cached as a miss, which is a real answer: this document does not
    /// name that file.
    ///
    /// `containerReferenceOf` memoizes the spelling this alias is joined
    /// into, so this answers at most once per target per resolver however
    /// many declarations in it are asked about.
    ///
    /// An alias that was read out of this document's own `@import` bindings
    /// is the caller's answer whether or not it can be written down: the
    /// memo saves the walk for the next question about the same target,
    /// and its own growth failing costs that walk, not this alias.
    fn importAliasOf(self: *TypeResolver, target_uri: []const u8, module: DocumentStore.ModuleId) !?[]const u8 {
        const key: AliasKey = .{ .uri = target_uri, .module = module };
        if (self.alias_cache.get(key)) |cached| return cached;
        const alias = try self.scanForImportAlias(target_uri, module);
        self.alias_cache.put(self.gpa, key, alias) catch {};
        return alias;
    }

    fn scanForImportAlias(self: *TypeResolver, target_uri: []const u8, module: DocumentStore.ModuleId) !?[]const u8 {
        const tree = &self.handle.document.tree;
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
            // The alias only names this declaration in this environment, so a
            // module that wires the same name elsewhere is not a match.
            switch (target) {
                .one => |resolved| {
                    if (!std.mem.eql(u8, resolved.uri.raw, target_uri)) continue;
                    if (resolved.module != module) continue;
                },
                else => continue,
            }
            return tree.tokenSlice(variable.ast.mut_token + 1);
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
        return self.resolutionFrame().typeRefIsPointerLike(node);
    }

    /// `true` when `node`'s type is `bool`, `false` when it resolved to
    /// anything else, and `null` when the type engine did not resolve it
    /// at all — an unresolved type is not a proved non-`bool`.
    pub fn isBoolType(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        return self.resolutionFrame().isBoolType(node);
    }

    pub fn isFloatType(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        const ty = (try self.typeOfNode(node)) orelse return null;
        const tag = self.typeTag(ty) orelse return null;
        return tag == .float or tag == .comptime_float;
    }

    pub fn floatBits(self: *TypeResolver, node: Ast.Node.Index) !?u16 {
        return self.resolutionFrame().floatBits(node);
    }

    pub fn isEnumType(self: *TypeResolver, node: Ast.Node.Index) !?bool {
        return self.resolutionFrame().isEnumType(node);
    }

    pub const IntInfo = struct { signed: bool, bits: u16 };

    /// Signedness and bit-width of the integer a cast into `node`'s type
    /// produces when that type is `?T`: the payload `T`, through nested
    /// optionals.  Null when the type is not an optional, or its payload is
    /// not an integer — a plain `u64` is `intInfo`'s answer, not this one's.
    pub fn optionalPayloadIntInfo(self: *TypeResolver, node: Ast.Node.Index) !?IntInfo {
        var ty = (try self.resolutionFrame().typeOfNode(node)) orelse return null;
        var depth: u8 = 0;
        while ((self.typeTag(ty) orelse return null) == .optional) : (depth += 1) {
            if (depth == 8) return null;
            ty = (try self.normalizedType(self.childType(ty) orelse return null)) orelse return null;
        }
        if (depth == 0) return null;
        return self.intInfoOfType(ty);
    }

    /// Signedness and bit-width of `node`'s type when it resolves to an integer
    /// type, else null.  Used e.g. to tell signed subtraction (well-defined,
    /// can't "wrap to a huge value") from unsigned underflow.
    pub fn intInfo(self: *TypeResolver, node: Ast.Node.Index) !?IntInfo {
        return self.resolutionFrame().intInfo(node);
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

    pub const EnumIntegerRange = struct { min: i128, max: i128 };

    /// Bounds of the actual declared tags of an exhaustive enum. Unknown
    /// tag values, non-exhaustive enums and non-enums do not supply proof.
    /// Resolve each initializer in its owning container, including imports
    /// and generic bindings, rather than interpreting names in this file.
    pub fn enumIntegerRange(self: *TypeResolver, node: Ast.Node.Index) !?EnumIntegerRange {
        const ty = (try self.typeOfNode(node)) orelse return null;
        return self.enumIntegerRangeOfType(ty);
    }

    /// The same exhaustive-tag proof for a canonical instantiated type.
    /// This preserves generic bindings when the consumer already resolved
    /// the type in a different declaration's context.
    pub fn enumIntegerRangeOfType(self: *TypeResolver, ty: ActualType) !?EnumIntegerRange {
        if (self.typeTag(ty) != .@"enum" or ty.data != .container) return null;
        const container = ty.data.container;
        const frame = self.frameForContainer(container);
        const tree = &frame.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return null;
        var range: ?EnumIntegerRange = null;
        var previous: ?i128 = null;
        for (declaration.ast.members) |member| {
            const field = tree.fullContainerField(member) orelse continue;
            if (std.mem.eql(u8, tree.tokenSlice(field.ast.main_token), "_")) return null;
            const value = if (field.ast.value_expr.unwrap()) |initializer|
                (try self.analyser.resolveIntegerLiteral(i128, frame.options(initializer))) orelse return null
            else if (previous) |last|
                std.math.add(i128, last, 1) catch return null
            else
                0;
            previous = value;
            if (range) |*bounds| {
                bounds.min = @min(bounds.min, value);
                bounds.max = @max(bounds.max, value);
            } else {
                range = .{ .min = value, .max = value };
            }
        }
        return range;
    }

    fn enumTagIntInfoOfType(self: *TypeResolver, ty: ActualType) !?IntInfo {
        if (self.typeTag(ty) != .@"enum" or ty.data != .container) return null;
        const container = ty.data.container;
        const frame = self.frameForContainer(container);
        const tree = &frame.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return null;
        if (declaration.ast.arg.unwrap()) |tag_type| {
            return self.intInfoOfType((try frame.typeOfNode(tag_type)) orelse return null);
        }
        const range = (try self.enumIntegerRangeOfType(ty)) orelse return null;
        if (range.min < 0) return null;
        const max: u128 = @intCast(range.max);
        return .{ .signed = false, .bits = if (max == 0) 0 else @intCast(128 - @clz(max)) };
    }
};

/// Read a container's qualified name out of the document that declares it.
/// This is the work behind `containerNameOf`'s memo: it walks out of the
/// declaration, matching each enclosing scope's declarations to find the one
/// that declared it, so a caller that asks about the same container again
/// should ask the memo rather than call this.
///
/// A container at the root of its file is the file: its name is the file's
/// own name with the `.zig` suffix taken off the end of it, which is a
/// suffix and not a stem — `foo.zig` is `foo`, and a file called `.zig` is
/// nothing at all, which is no name rather than a name of one dot.
///
/// The 32 enclosing scopes it will walk through is the same bound the
/// question has always had, and hitting it is an unknown name rather than a
/// truncated one.
fn scanContainerName(arena: std.mem.Allocator, container: Analyser.Type.Data.Container) !?[]const u8 {
    const handle = container.scope_handle.handle;
    const tree = &handle.document.tree;
    if (container.scope_handle.scope == .root) {
        const path = try handle.document.uri.toFsPath(arena);
        const basename = std.fs.path.basename(path);
        const name = if (std.mem.endsWith(u8, basename, ".zig"))
            basename[0 .. basename.len - ".zig".len]
        else
            basename;
        return if (name.len == 0) null else name;
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
    var failure: ToolchainFailure = .{};
    const paths = try parseToolchainEnv(gpa,
        \\{"zig_exe":"/opt/zig/bin/zig","lib_dir":"/opt/zig/lib","version":"0.16.0","env":{}}
    , &failure);
    defer gpa.free(paths.zig_exe.?);
    defer gpa.free(paths.zig_lib.?);
    try std.testing.expectEqualStrings("/opt/zig/bin/zig", paths.zig_exe.?);
    try std.testing.expectEqualStrings("/opt/zig/lib", paths.zig_lib.?);
}

test "toolchain environment parses ZON paths and escaped characters" {
    const gpa = std.testing.allocator;
    var failure: ToolchainFailure = .{};
    const paths = try parseToolchainEnv(gpa,
        \\.{ .zig_exe = "/opt/zig/bin/zig", .lib_dir = "/opt/zig \"dev\"/lib", .version = "0.16.0", .env = .{} }
    , &failure);
    defer gpa.free(paths.zig_exe.?);
    defer gpa.free(paths.zig_lib.?);
    try std.testing.expectEqualStrings("/opt/zig/bin/zig", paths.zig_exe.?);
    try std.testing.expectEqualStrings("/opt/zig \"dev\"/lib", paths.zig_lib.?);
}

test "toolchain environment rejects missing and empty library paths" {
    const gpa = std.testing.allocator;
    var failure: ToolchainFailure = .{};
    try std.testing.expectError(error.ZigToolchainUnavailable, parseToolchainEnv(gpa,
        \\{"zig_exe":"/opt/zig/bin/zig"}
    , &failure));
    try std.testing.expectEqual(ToolchainFailure.Reason.malformed_output, failure.reason);
    try std.testing.expectError(error.ZigToolchainUnavailable, parseToolchainEnv(gpa,
        \\.{ .zig_exe = "/opt/zig/bin/zig", .lib_dir = "", .version = "0.16.0" }
    , &failure));
    try std.testing.expectEqual(ToolchainFailure.Reason.missing_paths, failure.reason);
}

test "toolchain failure messages name status, stderr line and versions" {
    var buffer: [512]u8 = undefined;
    var failure: ToolchainFailure = .{ .reason = .exited, .code = 1 };
    failure.setFirstLine("\n  error: no build.zig.zon found\nsecond line\n");
    var writer: std.Io.Writer = .fixed(&buffer);
    try writer.print("{f}", .{failure});
    try std.testing.expectEqualStrings("exited with status 1: error: no build.zig.zon found", writer.buffered());

    failure = .{ .reason = .exited, .code = 1 };
    failure.setFirstLine("  \n");
    writer = .fixed(&buffer);
    try writer.print("{f}", .{failure});
    try std.testing.expectEqualStrings("exited with status 1 (no stderr output)", writer.buffered());

    failure = .{ .reason = .spawn_failed };
    failure.setDetail("FileNotFound");
    writer = .fixed(&buffer);
    try writer.print("{f}", .{failure});
    try std.testing.expectEqualStrings("could not be started: FileNotFound", writer.buffered());
}

test "toolchain discovery maps a missing compiler to ZigToolchainUnavailable" {
    var failure: ToolchainFailure = .{};
    try std.testing.expectError(
        error.ZigToolchainUnavailable,
        Toolchain.init(std.testing.allocator, std.testing.io, "/nonexistent/zbc-test-zig", &failure),
    );
    try std.testing.expectEqual(ToolchainFailure.Reason.spawn_failed, failure.reason);
    try std.testing.expectEqualStrings("FileNotFound", failure.detail());
}

test "stable double pointer parameters resolve as pointers" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-pointer-regression.zig", "pub fn borrow(p: **u8) **u8 { return p; }");
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
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
    var failure: ToolchainFailure = .{};
    try std.testing.expectError(error.IncompatibleZigVersion, parseToolchainEnv(std.testing.allocator,
        \\{"zig_exe":"/opt/zig/bin/zig","lib_dir":"/opt/zig/lib","version":"0.0.0-incompatible"}
    , &failure));
    try std.testing.expectEqualStrings("0.0.0-incompatible", failure.detail());
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
    const tree = &resolver.handle.document.tree;
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
    const tree = &resolver.handle.document.tree;
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
        \\const Flag = bool;
        \\fn observe(optional: Maybe, pointer: Pointer, float: Float,
        \\           integer: Integer, array: Array, tag: ?Tag, box: ?*Box,
        \\           flag: Flag, direct: bool) void {
        \\    _ = optional; _ = pointer; _ = float; _ = integer;
        \\    _ = array; _ = tag; _ = box;
        \\    _ = flag; _ = direct;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
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
    for ([_][]const u8{ "Flag", "flag", "direct" }) |name| {
        try std.testing.expectEqual(@as(?bool, true), @as(?bool, try resolver.isBoolType(try testIdentifier(tree, name))));
    }
    try std.testing.expectEqual(@as(?bool, false), @as(?bool, try resolver.isBoolType(try testIdentifier(tree, "integer"))));
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
    try std.testing.expectEqual(@as(?u64, 6), try resolver.fixedArrayLen(try testIdentifier(&resolver.handle.document.tree, "repeated")));
}

test "type predicates retain unresolved and depth-limited answers" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const source = try std.fmt.allocPrintSentinel(gpa, "const Tag = enum {{ a }}; const Deep = {s}Tag;\n" ++
        "fn observe(deep: Deep, unknown: anytype, pptr: **[7]u8) void {{ _ = deep; _ = unknown; _ = pptr; }}\n" ++
        "fn unbound() void {{ _ = nowhere; }}", .{"?" ** 40}, 0);
    defer gpa.free(source);
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "virtual-type-boundary.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const unknown = try testIdentifier(tree, "unknown");
    try std.testing.expectEqual(@as(?bool, null), try resolver.isOptionalType(unknown));
    try std.testing.expectEqual(@as(?bool, null), try resolver.resolvedTypeIsPointer(unknown));
    try std.testing.expectEqual(@as(?bool, null), try resolver.isFloatType(unknown));
    try std.testing.expectEqual(@as(?u16, null), try resolver.floatBits(unknown));
    try std.testing.expectEqual(@as(?bool, null), try resolver.isEnumType(unknown));
    try std.testing.expectEqual(@as(?bool, null), try resolver.isBoolType(unknown));
    const deep = try testIdentifier(tree, "deep");
    try std.testing.expectEqual(@as(?bool, true), try resolver.isOptionalType(deep));
    try std.testing.expectEqual(@as(?bool, null), try resolver.isEnumType(deep));
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(deep));
    try std.testing.expectEqual(@as(?u64, null), try resolver.fixedArrayLen(try testIdentifier(tree, "pptr")));
    // A name no declaration binds is an absent answer, not a non-`bool`.
    try std.testing.expectEqual(@as(?bool, null), try resolver.isBoolType(try testIdentifier(tree, "nowhere")));
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
    try std.testing.expectEqualStrings("Namespace.Box", (try resolver.typeNameOfNode(try testIdentifier(&resolver.handle.document.tree, "value"))).?);
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
    const tree = &resolver.handle.document.tree;
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
    const node = try testIdentifier(&resolver.handle.document.tree, "value");
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
    try std.testing.expectEqual(@as(?u64, null), try resolver.comptimeIntValue(try testIdentifier(&resolver.handle.document.tree, "changed")));
    try std.testing.expectEqual(@as(?u64, 4), try resolver.comptimeIntValue(try testIdentifier(&resolver.handle.document.tree, "known")));
    for (resolver.handle.document.tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const name = resolver.handle.document.tree.tokenSlice(resolver.handle.document.tree.nodeData(node).node_and_token[1]);
        const expected: ?u64 = if (std.mem.eql(u8, name, "limit")) 4 else null;
        try std.testing.expectEqual(std.mem.eql(u8, name, "limit"), (try resolver.intInfo(node)) == null);
        try std.testing.expectEqual(expected, try resolver.comptimeIntValue(node));
    }
}

test "imported integer constants retain exact values through aliases and shifts" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "limits.zig", .data =
        \\pub const base: usize = 4;
        \\pub const bound: usize = base << 2;
        \\pub var changing: usize = 16;
        \\pub const unknown = missing;
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
        \\const imported = @import("limits.zig");
        \\const alias = imported.bound;
        \\fn observe(runtime: usize) void {
        \\    _ = alias;
        \\    _ = imported.changing;
        \\    _ = imported.unknown;
        \\    _ = runtime;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(?u64, 16), try resolver.comptimeIntValue(try testIdentifier(tree, "alias")));
    try std.testing.expectEqual(@as(?u64, null), try resolver.comptimeIntValue(try testIdentifier(tree, "runtime")));
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const name = tree.tokenSlice(tree.nodeData(node).node_and_token[1]);
        const expected: ?u64 = if (std.mem.eql(u8, name, "bound")) 16 else null;
        try std.testing.expectEqual(expected, try resolver.comptimeIntValue(node));
    }
}

test "immutable literal payloads authenticate imported aliases and reject holes and opaque storage" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "tables.zig", .data =
        \\pub const leaf = [2]u8{ 3, 7 };
        \\pub const Namespace = struct {
        \\    pub const alias = leaf;
        \\    pub const nested = [2][2]u8{ alias, .{ 11, 13 } };
        \\    pub const holes = [2][2]u8{ alias, .{ 11, undefined } };
        \\};
        \\pub const selected = Namespace.nested[1];
        \\pub const bad_selector = Namespace.nested[undefined];
        \\pub const negatives = [2]f64{ -0.5, -0.125 };
        \\pub var mutable = [2]u8{ 3, 7 };
        \\pub const unknown = missing;
        \\extern fn opaqueValue() u8;
        \\pub const called = [2]u8{ opaqueValue(), 7 };
        \\pub const recursive = recursive;
        \\pub const pointed = (&leaf).*;
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
        \\const imported = @import("tables.zig");
        \\const safe = imported.Namespace.alias;
        \\const nested = imported.Namespace.nested;
        \\const selected = imported.selected;
        \\const negatives = imported.negatives;
        \\const bad_selector = imported.bad_selector;
        \\const holes = imported.Namespace.holes;
        \\const mutable = imported.mutable;
        \\const unknown = imported.unknown;
        \\const called = imported.called;
        \\const recursive = imported.recursive;
        \\const pointed = imported.pointed;
        \\fn observe(index: usize) void {
        \\    _ = safe;
        \\    _ = nested;
        \\    _ = selected;
        \\    _ = negatives;
        \\    _ = bad_selector;
        \\    _ = holes;
        \\    _ = mutable;
        \\    _ = unknown;
        \\    _ = called;
        \\    _ = recursive;
        \\    _ = pointed;
        \\    _ = nested[index][index];
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const frame = resolver.resolutionFrame();
    for ([_][]const u8{ "safe", "nested", "selected", "negatives" }) |name|
        try std.testing.expect(try frame.immutableLiteralPayloadOfNode(try testIdentifier(tree, name)));
    for ([_][]const u8{ "holes", "mutable", "unknown", "called", "recursive", "pointed", "bad_selector" }) |name|
        try std.testing.expect(!try frame.immutableLiteralPayloadOfNode(try testIdentifier(tree, name)));
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .array_access) continue;
        // Payload proof is independent of the runtime selector's bytes and
        // bounds. The CFG must retain the selector as a separate value input.
        try std.testing.expect(try frame.immutableLiteralPayloadOfNode(@enumFromInt(raw)));
    }
}

test "literal payload memo retries allocation failure and reuses a settled certificate" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-payload-memo.zig",
        \\const table = [2]u8{ 3, 7 };
        \\fn observe() void { _ = table; }
    );
    defer resolver.deinit();
    const node = try testIdentifier(&resolver.handle.document.tree, "table");
    const frame = resolver.resolutionFrame();
    var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = 0 });
    resolver.gpa = failing.allocator();
    defer resolver.gpa = gpa;
    try std.testing.expectError(error.OutOfMemory, frame.immutableLiteralPayloadOfNode(node));
    try std.testing.expectEqual(@as(usize, 0), resolver.literal_payload_cache.count());
    resolver.gpa = gpa;
    try std.testing.expect(try frame.immutableLiteralPayloadOfNode(node));
    const entries = resolver.literal_payload_cache.count();
    try std.testing.expect(entries > 0);
    try std.testing.expect(try frame.immutableLiteralPayloadOfNode(node));
    try std.testing.expectEqual(entries, resolver.literal_payload_cache.count());
}

test "enum integer ranges use exhaustive resolved tags and reject unknown values" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-enum-integer-range.zig",
        \\const Dense = enum { a, b, c };
        \\const Sparse = enum(i16) { a = -3, b = 17, c };
        \\const Open = enum(u8) { a = 1, _ };
        \\const Unknown = enum(u8) { a = missing, b };
        \\fn observe(dense: Dense, sparse: Sparse, open: Open, unknown: Unknown, other: anytype) void {
        \\    _ = dense; _ = sparse; _ = open; _ = unknown; _ = other;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(TypeResolver.EnumIntegerRange{ .min = 0, .max = 2 }, (try resolver.enumIntegerRange(try testIdentifier(tree, "dense"))).?);
    try std.testing.expectEqual(TypeResolver.EnumIntegerRange{ .min = -3, .max = 18 }, (try resolver.enumIntegerRange(try testIdentifier(tree, "sparse"))).?);
    for ([_][]const u8{ "open", "unknown", "other" }) |name| {
        try std.testing.expectEqual(@as(?TypeResolver.EnumIntegerRange, null), try resolver.enumIntegerRange(try testIdentifier(tree, name)));
    }
}

test "enum integer conversions expose inferred and explicit tag types" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-enum-tag-type.zig",
        \\const Dense = enum { a, b, c };
        \\const Wide = enum(u32) { a, b };
        \\fn observe(dense: Dense, wide: Wide, unknown: anytype) void {
        \\    _ = @intFromEnum(dense);
        \\    _ = @intFromEnum(wide);
        \\    _ = @intFromEnum(unknown);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var count: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .builtin_call_two and tag != .builtin_call_two_comma) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@intFromEnum")) continue;
        const expected: ?TypeResolver.IntInfo = switch (count) {
            0 => .{ .signed = false, .bits = 2 },
            1 => .{ .signed = false, .bits = 32 },
            else => null,
        };
        try std.testing.expectEqual(expected, try resolver.intInfo(node));
        count += 1;
    }
    try std.testing.expectEqual(@as(usize, 3), count);
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
    const tree = &resolver.handle.document.tree;
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

test "typed integer-to-float initializers resolve after either public query order" {
    const gpa = std.testing.allocator;
    for ([_]bool{ true, false }) |declaration_first| {
        var context: TypeContext = undefined;
        try context.init(gpa, std.testing.io);
        defer context.deinit();
        var resolver: TypeResolver = undefined;
        try resolver.init(&context, gpa, "/tmp/zbc-float-initializer-order.zig",
            \\fn convert(number: i128) void {
            \\    const wide: f128 = @floatFromInt(number);
            \\    const small: f32 = @floatFromInt(number);
            \\    _ = wide;
            \\    _ = small;
            \\}
        );
        defer resolver.deinit();
        const tree = &resolver.handle.document.tree;
        var seen: usize = 0;
        for (0..tree.nodes.len) |raw| {
            const declaration: Ast.Node.Index = @enumFromInt(raw);
            const variable = tree.fullVarDecl(declaration) orelse continue;
            const name = tree.tokenSlice(variable.ast.mut_token + 1);
            const width: u16 = if (std.mem.eql(u8, name, "wide")) 128 else if (std.mem.eql(u8, name, "small")) 32 else continue;
            const initializer = variable.ast.init_node.unwrap() orelse return error.MissingConversion;
            const first = if (declaration_first) declaration else initializer;
            const second = if (declaration_first) initializer else declaration;
            try std.testing.expectEqual(@as(?u16, width), try resolver.floatBits(first));
            try std.testing.expectEqual(@as(?u16, width), try resolver.floatBits(second));
            // Repeated consumer predicates must see the completed type, not a
            // null left by the initializer's recursive request for its parent.
            try std.testing.expectEqual(@as(?bool, true), try resolver.isFloatType(initializer));
            try std.testing.expectEqual(@as(?u16, width), try resolver.floatBits(initializer));
            try std.testing.expectEqual(@as(?u16, width), try resolver.floatBits(declaration));
            seen += 1;
        }
        try std.testing.expectEqual(@as(usize, 2), seen);
    }
}

test "inferred float arithmetic and builtin results resolve their result widths" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-inferred-float-results.zig",
        \\fn f(progress: f32, duration: u32, elapsed: f32) void {
        \\    const duration_sec: f32 = @floatFromInt(duration);
        \\    const clipped = @max(@as(f32, 0), @min(progress, duration_sec));
        \\    const minutes = elapsed / 60.0;
        \\    const remainder = @mod(elapsed, 60.0);
        \\    const sum = progress + 1.0;
        \\    const difference = progress - 1.0;
        \\    const product = progress * 60.0;
        \\    const rounded = @round(elapsed);
        \\    const floored = @floor(elapsed);
        \\    const ceiling = @ceil(elapsed);
        \\    const truncated = @trunc(elapsed);
        \\    const nested_minutes = clipped / 60.0;
        \\    const nested_remainder = @mod(clipped, 60.0);
        \\    const nested_rounded = @round(@max(@as(f32, 0), elapsed));
        \\    const min_many = @min(progress, elapsed, duration_sec);
        \\    const max_many = @max(progress, elapsed, duration_sec);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const expected_names = [_][]const u8{
        "duration_sec",
        "clipped",
        "minutes",
        "remainder",
        "sum",
        "difference",
        "product",
        "rounded",
        "floored",
        "ceiling",
        "truncated",
        "nested_minutes",
        "nested_remainder",
        "nested_rounded",
        "min_many",
        "max_many",
    };
    var seen = [_]bool{false} ** expected_names.len;
    var seen_count: usize = 0;
    for (0..tree.nodes.len) |raw| {
        const declaration: Ast.Node.Index = @enumFromInt(raw);
        const variable = tree.fullVarDecl(declaration) orelse continue;
        const name = tree.tokenSlice(variable.ast.mut_token + 1);
        const expected_index = for (expected_names, 0..) |expected_name, index| {
            if (std.mem.eql(u8, name, expected_name)) break index;
        } else continue;
        try std.testing.expect(!seen[expected_index]);
        seen[expected_index] = true;
        seen_count += 1;
        const initializer = variable.ast.init_node.unwrap() orelse return error.MissingInitializer;
        for (0..2) |_| {
            try std.testing.expectEqual(@as(?u16, 32), try resolver.floatBits(declaration));
            try std.testing.expectEqual(@as(?u16, 32), try resolver.floatBits(initializer));
        }
    }
    try std.testing.expectEqual(expected_names.len, seen_count);
    for (seen) |was_seen| try std.testing.expect(was_seen);
}

test "mixed float operands widen inferred builtin and arithmetic results" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-mixed-float-results.zig",
        \\fn f(small: f32, wide: f64) void {
        \\    const sum = small + wide;
        \\    const minimum = @min(small, wide);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const expected_names = [_][]const u8{ "sum", "minimum" };
    var seen = [_]bool{false} ** expected_names.len;
    var seen_count: usize = 0;
    for (0..tree.nodes.len) |raw| {
        const declaration: Ast.Node.Index = @enumFromInt(raw);
        const variable = tree.fullVarDecl(declaration) orelse continue;
        const name = tree.tokenSlice(variable.ast.mut_token + 1);
        const expected_index = for (expected_names, 0..) |expected_name, index| {
            if (std.mem.eql(u8, name, expected_name)) break index;
        } else continue;
        try std.testing.expect(!seen[expected_index]);
        seen[expected_index] = true;
        seen_count += 1;
        const initializer = variable.ast.init_node.unwrap() orelse return error.MissingInitializer;
        for (0..2) |_| {
            try std.testing.expectEqual(@as(?u16, 64), try resolver.floatBits(declaration));
            try std.testing.expectEqual(@as(?u16, 64), try resolver.floatBits(initializer));
        }
    }
    try std.testing.expectEqual(expected_names.len, seen_count);
    for (seen) |was_seen| try std.testing.expect(was_seen);
}

test "mismatched and unknown operands stay unknown for float inference" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-unknown-float-results.zig",
        \\fn f(value: f32, flag: bool, unknown: anytype) void {
        \\    const mismatch = @min(value, flag);
        \\    const unknown_min = @min(value, unknown);
        \\    const unknown_max = @max(value, unknown);
        \\    const unknown_mod = @mod(value, unknown);
        \\    const unknown_sum = value + unknown;
        \\    const unknown_round = @round(unknown);
        \\    const unknown_min_late = @min(value, 1.0, unknown);
        \\}
        \\fn generic(comptime T: type, value: f32, unknown: T) void {
        \\    const generic_min = @min(value, unknown);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const expected_names = [_][]const u8{
        "mismatch",
        "unknown_min",
        "unknown_max",
        "unknown_mod",
        "unknown_sum",
        "unknown_round",
        "unknown_min_late",
        "generic_min",
    };
    var seen = [_]bool{false} ** expected_names.len;
    var seen_count: usize = 0;
    for (0..tree.nodes.len) |raw| {
        const declaration: Ast.Node.Index = @enumFromInt(raw);
        const variable = tree.fullVarDecl(declaration) orelse continue;
        const name = tree.tokenSlice(variable.ast.mut_token + 1);
        const expected_index = for (expected_names, 0..) |expected_name, index| {
            if (std.mem.eql(u8, name, expected_name)) break index;
        } else continue;
        try std.testing.expect(!seen[expected_index]);
        seen[expected_index] = true;
        seen_count += 1;
        const initializer = variable.ast.init_node.unwrap() orelse return error.MissingInitializer;
        for (0..2) |_| {
            try std.testing.expectEqual(@as(?u16, null), try resolver.floatBits(declaration));
            try std.testing.expectEqual(@as(?u16, null), try resolver.floatBits(initializer));
        }
    }
    try std.testing.expectEqual(expected_names.len, seen_count);
    for (seen) |was_seen| try std.testing.expect(was_seen);
}

test "unbound generic conversions and recursive declarations remain unknown on retry" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-unresolved-binding-retry.zig",
        \\const cycle = cycle;
        \\fn openGeneric(comptime T: type, number: i128) void {
        \\    const unknown: T = @floatFromInt(number);
        \\    _ = unknown;
        \\    _ = cycle;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const conversion = for (0..tree.nodes.len) |raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.builtinCallParams(&buffer, node) == null) continue;
        if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@floatFromInt")) break node;
    } else return error.MissingConversion;
    const cycle = try testIdentifier(tree, "cycle");
    for (0..2) |_| {
        try std.testing.expectEqual(@as(?u16, null), try resolver.floatBits(conversion));
        try std.testing.expectEqual(@as(?bool, null), try resolver.isFloatType(conversion));
        try std.testing.expect((try resolver.resolutionFrame().typeOfNode(cycle)) == null);
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
    const tree = &resolver.handle.document.tree;
    const field = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .field_access) break @as(Ast.Node.Index, @enumFromInt(index));
    } else return error.MissingFieldAccess;
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(field));
    try std.testing.expectEqual(@as(?anyerror, error.ImportInvalidSyntax), context.store.failureSnapshot().source_failure);
    // Repeated public queries preserve the failure rather than treating an
    // unfinished source load as a resolved type.
    for (0..2) |_| {
        try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(field));
        try std.testing.expectEqual(@as(?anyerror, error.ImportInvalidSyntax), context.store.failureSnapshot().source_failure);
    }

    // Source documents are immutable within a session. Retry the corrected
    // source in an isolated session rather than replacing the failed snapshot
    // or resetting the first resolver's memo.
    try tmp.dir.writeFile(io, .{ .sub_path = "sub/types.zig", .data = "pub const Target = struct { value: u16 };" });
    var retry_context: TypeContext = undefined;
    try retry_context.init(gpa, io);
    defer retry_context.deinit();
    retry_context.store.source_policy = .{ .roots = &.{directory} };
    var retry_resolver: TypeResolver = undefined;
    try retry_resolver.init(&retry_context, gpa, path,
        \\const package = @import("sub/package.zig");
        \\fn inspect(value: package.Target) void { _ = value; }
    );
    defer retry_resolver.deinit();
    const retry_tree = &retry_resolver.handle.document.tree;
    const retry_field = for (retry_tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .field_access) break @as(Ast.Node.Index, @enumFromInt(index));
    } else return error.MissingFieldAccess;
    try std.testing.expect((try retry_resolver.resolutionFrame().typeOfNode(retry_field)) != null);
    try std.testing.expectEqual(@as(?anyerror, null), retry_context.store.failureSnapshot().source_failure);
    // The original failure remains isolated and still cannot become an answer.
    try std.testing.expectEqual(@as(?anyerror, error.ImportInvalidSyntax), context.store.failureSnapshot().source_failure);
}

/// Writes a real project whose `build.zig` wires `"values"` to `root` and
/// returns the canonical project directory.
fn namedModuleProject(
    tmp: *std.testing.TmpDir,
    io: std.Io,
    gpa: std.mem.Allocator,
    build_zig: []const u8,
) ![:0]u8 {
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
        \\    const values = b.createModule(.{ .root_source_file = b.path("src/values.zig") });
        \\    const main = b.addModule("main", .{ .root_source_file = b.path("main.zig") });
        \\    main.addImport("values", values);
        \\}
    );
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    const fixture_source: [:0]const u8 =
        \\const values = @import("values");
        \\fn observe(registry: values.Registry) void {
        \\    const wide: u64 = @intCast(registry.entries.len);
        \\    const narrow: u32 = @intCast(registry.entries.len);
        \\    _ = wide;
        \\    _ = narrow;
        \\    _ = registry.limit;
        \\}
    ;
    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data = fixture_source });
    var context: TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, path, fixture_source);
    defer resolver.deinit();
    // The slice length is a native 64-bit unsigned integer, so a `usize` to
    // `u64` conversion is a proven fit; the declared `u32` field is not, and
    // stays visible as a 32-bit integer for the narrowing rules to judge.
    const tree = &resolver.handle.document.tree;
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
    try std.testing.expectEqual(@as(?anyerror, null), context.store.failureSnapshot().source_failure);
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
    const tree = &resolver.handle.document.tree;
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
    try std.testing.expectEqual(@as(?anyerror, null), context.store.failureSnapshot().source_failure);
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
    const tree = &resolver.handle.document.tree;
    const field = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .field_access) break @as(Ast.Node.Index, @enumFromInt(index));
    } else return error.MissingFieldAccess;
    try std.testing.expectEqual(@as(?TypeResolver.IntInfo, null), try resolver.intInfo(field));
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(field));
}

// ── Toolchain library identity ─────────────────────────────────

/// What one spelling of the toolchain's library root makes of the standard
/// library: whether the store admits it, and whether a document under the
/// same root still identifies as part of the compiler's own sources.
///
/// Deliberately no URI text.  Two spellings of one compiler necessarily
/// produce different path strings, and comparing them would pin the
/// representation the store happens to use rather than anything a caller can
/// observe.  Admission and declaration identity are the user-visible facts,
/// and they are what this measures.
const StdAdmission = struct {
    admitted: bool,
    declared_in_toolchain: bool,

    fn deinit(self: *StdAdmission) void {
        self.* = undefined;
    }
};

/// Measure the store with `library_root` installed as the toolchain's library
/// root.  `DocumentStore.Config` is a plain public struct that any embedder
/// fills, so this is where the contract is pinned: whatever spelling a library
/// root arrives in, admission and identity have to be the canonical one.  The
/// root is installed for the duration of the measurement only, because
/// `uriFromImportStr` and `declaredInToolchainFile` read it from two different
/// fields and a real toolchain reports one path into both.
fn observeStdAdmission(
    gpa: std.mem.Allocator,
    context: *TypeContext,
    resolver: *TypeResolver,
    library_root: []const u8,
) !StdAdmission {
    const owned_root = try gpa.dupe(u8, library_root);
    defer gpa.free(owned_root);
    const previous = context.toolchain.zig_lib;
    defer context.toolchain.zig_lib = previous;
    context.toolchain.zig_lib = owned_root;
    context.store.config.zig_lib_dir = .{ .path = library_root, .handle = .cwd() };

    var imported = try context.store.uriFromImportStr(gpa, resolver.handle, "std");
    defer imported.deinit(gpa);
    switch (imported) {
        .one => {},
        .none => return error.UnresolvedStandardLibraryImport,
        .many => return error.AmbiguousStandardLibraryImport,
    }

    const allocator_path = try std.fs.path.join(gpa, &.{ library_root, "std/mem/Allocator.zig" });
    defer gpa.free(allocator_path);
    const allocator_uri = try Uri.fromPath(gpa, allocator_path);
    defer allocator_uri.deinit(gpa);

    const admitted = switch (imported) {
        .one => |target| (try context.store.getOrLoadHandle(target.uri, target.module)) != null,
        else => false,
    };
    var declared_in_toolchain = false;
    if (try context.store.getOrLoadHandle(allocator_uri, context.store.toolchainModule() catch .unscoped)) |handle| {
        declared_in_toolchain = try resolver.declaredInToolchainFile(handle, "/std/mem/Allocator.zig");
    }

    // A spelling that resolves no standard library at all is not an answer
    // this test can compare, so it fails here rather than looking identical.
    if (imported != .one) return error.UnresolvedStandardLibraryImport;
    return .{
        .admitted = admitted,
        .declared_in_toolchain = declared_in_toolchain,
    };
}

test "a symlinked Zig library root admits and identifies the standard library like the canonical root" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var context: TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();

    // One tree, two spellings: the compiler's own library path, and a symlink
    // that reaches exactly the same files.  Every document the store serves is
    // canonical, so a library root that is not itself canonical describes a
    // path the store never produces.
    const reported = context.toolchain.zig_lib orelse return error.MissingToolchainLibrary;
    var buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const canonical_length = try std.Io.Dir.cwd().realPathFile(io, reported, &buffer);
    const canonical = try gpa.dupe(u8, buffer[0..canonical_length]);
    defer gpa.free(canonical);
    try tmp.dir.symLink(io, reported, "lib", .{ .is_directory = true });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const linked = try std.fs.path.join(gpa, &.{ directory, "lib" });
    defer gpa.free(linked);
    try std.testing.expect(!std.mem.eql(u8, canonical, linked));

    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data = "pub const value: u8 = 7;\n" });
    const main_path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(main_path);
    // Neither library spelling lies under the project source root.
    context.store.source_policy = .{ .roots = &.{main_path} };

    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, main_path, null);
    defer resolver.deinit();

    var canonical_view = try observeStdAdmission(gpa, &context, &resolver, canonical);
    defer canonical_view.deinit();
    var linked_view = try observeStdAdmission(gpa, &context, &resolver, linked);
    defer linked_view.deinit();

    // The two spellings name one compiler, so they must answer identically.
    try std.testing.expectEqual(canonical_view.admitted, linked_view.admitted);
    try std.testing.expectEqual(canonical_view.declared_in_toolchain, linked_view.declared_in_toolchain);
    // Identical must not mean "no standard library": the canonical spelling
    // answers prove what the linked spelling has to answer too.
    try std.testing.expect(canonical_view.admitted);
    try std.testing.expect(canonical_view.declared_in_toolchain);
    try std.testing.expectEqual(@as(?anyerror, null), context.store.failureSnapshot().source_failure);
}

test "an entry walked out of a symlinked directory is the document the kernel names" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Two files, two answers, and one spelling that names both of them.
    // `link/../main.zig` is `elsewhere/src/main.zig` to the kernel and
    // `main.zig` to the text, and both of those exist here with different
    // widths, so an implementation that folds `..` into the text answers
    // confidently from the wrong file instead of failing.
    try tmp.dir.createDirPath(io, "elsewhere/src/deep");
    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data =
        \\pub const Box = struct { tag: u16 };
        \\fn observe(value: Box) void { _ = value.tag; }
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "elsewhere/src/main.zig", .data =
        \\pub const Box = struct { tag: u32 };
        \\fn observe(value: Box) void { _ = value.tag; }
    });
    try tmp.dir.symLink(io, "elsewhere/src/deep", "link", .{ .is_directory = true });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);

    var context: TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };

    const linked_entry = try std.fs.path.join(gpa, &.{ directory, "link/../main.zig" });
    defer gpa.free(linked_entry);
    const physical_entry = try std.fs.path.join(gpa, &.{ directory, "elsewhere/src/main.zig" });
    defer gpa.free(physical_entry);
    const folded_entry = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(folded_entry);

    var linked: TypeResolver = undefined;
    try linked.init(&context, gpa, linked_entry, null);
    defer linked.deinit();
    var physical: TypeResolver = undefined;
    try physical.init(&context, gpa, physical_entry, null);
    defer physical.deinit();

    // One file, so one document: two spellings of it are two handles onto
    // one snapshot rather than two parses that can drift apart.
    try std.testing.expect(linked.handle.document == physical.handle.document);

    // ...and it is the file the kernel named, proved by what the resolver
    // answers about a declaration only that file declares.
    const linked_bits = (try linked.intInfo(try testFieldAccess(&linked.handle.document.tree, "value"))) orelse
        return error.MissingIntegerType;
    try std.testing.expect(!linked_bits.signed);
    try std.testing.expectEqual(@as(u16, 32), linked_bits.bits);
    const physical_bits = (try physical.intInfo(try testFieldAccess(&physical.handle.document.tree, "value"))) orelse
        return error.MissingIntegerType;
    try std.testing.expect(!physical_bits.signed);
    try std.testing.expectEqual(@as(u16, 32), physical_bits.bits);

    // The file the text alone names is still a document of its own:
    // resolving the entry physically must not fold an unrelated file into
    // this one, nor let this one answer for it.
    var folded: TypeResolver = undefined;
    try folded.init(&context, gpa, folded_entry, null);
    defer folded.deinit();
    try std.testing.expect(folded.handle.document != linked.handle.document);
    const folded_bits = (try folded.intInfo(try testFieldAccess(&folded.handle.document.tree, "value"))) orelse
        return error.MissingIntegerType;
    try std.testing.expect(!folded_bits.signed);
    try std.testing.expectEqual(@as(u16, 16), folded_bits.bits);
}

test "an injected source the filesystem has no file for keeps the path its caller named" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var context: TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();

    // A caller holding the text of a document the filesystem does not have —
    // an editor buffer, a fixture — is still owed an analysis of that text,
    // under the path its own spelling names.  The directory it names is
    // real, so what it gets is that one path and not a reading of whatever
    // is nearest to it.
    const entry = "zbc-entry-not-on-disk/entry.zig";
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, entry, "pub fn borrow(p: **u8) **u8 { return p; }");
    defer resolver.deinit();

    const path = try resolver.handle.document.uri.toFsPath(resolver.arena.allocator());
    try std.testing.expect(std.fs.path.isAbsolute(path));
    try std.testing.expect(std.mem.endsWith(u8, path, entry));
    // Nothing was read to get here: that is the whole reason the text
    // beside the path is what gets analysed.
    try std.testing.expectError(error.FileNotFound, std.Io.Dir.cwd().access(io, path, .{}));

    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    try std.testing.expectEqual(@as(?bool, true), try resolver.resolvedTypeIsPointer(try testIdentifier(tree, "p")));
}

test "a resolver whose initialization runs out of memory owns nothing afterwards" {
    const gpa = std.testing.allocator;
    const entry = "/tmp/zbc-failed-initialization.zig";
    const source = "pub const Box = struct {};\n";

    // A failed `init` hands back no resolver: the caller cannot tell how far
    // it got, so it cannot know what it now owns.  Two refusals, and for
    // each of them two callers — one that walks away and one that releases
    // anyway.
    //
    // A FRESH context per run, sharing the resolver's own allocator, so what
    // is refused is a real allocation of that run rather than a count pinned
    // to whatever the store happened to do in an earlier one.  The first is
    // the resolver's own arena, and the one after it is an allocation made
    // once that arena is already holding a buffer — which is what makes the
    // rollback release something instead of closing an empty shell.
    for ([_]usize{ 0, 1 }) |after_arena| {
        for ([_]bool{ false, true }) |releases| {
            var memory: std.testing.FailingAllocator = .init(gpa, .{});
            var context: TypeContext = undefined;
            try context.init(memory.allocator(), std.testing.io);
            defer context.deinit();
            // The context is set up, so what is refused next belongs to this
            // run: `alloc_index` counts what has already been served.
            memory.fail_index = memory.alloc_index + after_arena;

            var resolver: TypeResolver = undefined;
            var built = false;
            // Whatever `init` did build is released either way: a fixture
            // that leaks on the paths that are NOT the failure under test
            // would hide the very leak it is here to look for.
            defer if (built) resolver.deinit();

            resolver.init(&context, memory.allocator(), entry, source) catch |err| {
                try std.testing.expectEqual(error.OutOfMemory, err);
                // The caller that releases anyway must not reach for memory
                // the rollback has already freed, which this allocator
                // reports as a double free on the line below.  The one that
                // walks away must not leak what the walk found, which the
                // testing allocator reports at the end of this test.
                if (releases) resolver.deinit();
                continue;
            };
            built = true;
        }
    }
}

/// Two modules that wire the same alias to different roots, plus one source
/// both of them reach by relative import.  That is issue #17's shape with
/// the shared file in place of the two importers, and it is the shape every
/// scoping rule below has to hold for: the alias is per module, the parse is
/// per file, and the identity is the pair.
fn writeTwoModuleProject(tmp: *std.testing.TmpDir, io: std.Io) !void {
    try tmp.dir.writeFile(io, .{ .sub_path = "build.zig", .data =
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\const std_dep = b.createModule(.{ .root_source_file = b.path("left_dep.zig") });
        \\const other_dep = b.createModule(.{ .root_source_file = b.path("right_dep.zig") });
        \\const left = b.addModule("left", .{ .root_source_file = b.path("left.zig") });
        \\left.addImport("dep", std_dep);
        \\const right = b.addModule("right", .{ .root_source_file = b.path("right.zig") });
        \\right.addImport("dep", other_dep);
        \\}
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "left.zig", .data = "const shared = @import(\"./shared.zig\");\npub const tag = shared.tag;\n" });
    try tmp.dir.writeFile(io, .{ .sub_path = "right.zig", .data = "const shared = @import(\"./shared.zig\");\npub const tag = shared.tag;\n" });
    try tmp.dir.writeFile(io, .{ .sub_path = "shared.zig", .data = "const dep = @import(\"dep\");\npub const tag = dep.tag;\n" });
    try tmp.dir.writeFile(io, .{ .sub_path = "left_dep.zig", .data = "pub const tag: u8 = 2;\n" });
    try tmp.dir.writeFile(io, .{ .sub_path = "right_dep.zig", .data = "pub const tag: u32 = 3;\n" });
}

test "two modules wire one alias differently, and a shared source is one parse and two identities" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try writeTwoModuleProject(&tmp, io);

    var context: TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    context.store.source_policy = .{ .roots = &.{directory} };

    const Path = struct {
        fn of(g: std.mem.Allocator, dir: []const u8, name: []const u8) !struct { path: []u8, uri: Uri } {
            const path = try std.fs.path.join(g, &.{ dir, name });
            errdefer g.free(path);
            return .{ .path = path, .uri = try Uri.fromPath(g, path) };
        }
    };
    const left = try Path.of(gpa, directory, "left.zig");
    defer gpa.free(left.path);
    defer left.uri.deinit(gpa);
    const right = try Path.of(gpa, directory, "right.zig");
    defer gpa.free(right.path);
    defer right.uri.deinit(gpa);
    const shared = try Path.of(gpa, directory, "shared.zig");
    defer gpa.free(shared.path);
    defer shared.uri.deinit(gpa);

    // Each importer's own root is its module, proven from build.zig alone.
    const left_module = try context.moduleForDocument(left.uri);
    const right_module = try context.moduleForDocument(right.uri);
    try std.testing.expect(left_module != .unscoped and right_module != .unscoped);
    try std.testing.expect(left_module != right_module);

    const left_handle = try context.sourceHandle(left.path, left_module);
    const right_handle = try context.sourceHandle(right.path, right_module);

    // Only a single proven target is an answer; `.none` and `.many` are
    // both "not proven", and the test must not quietly accept either.
    const Only = struct {
        fn of(result: DocumentStore.UriFromImportStringResult) !DocumentStore.ResolvedImport {
            return switch (result) {
                .one => |target| target,
                .none, .many => error.ImportTargetNotProven,
            };
        }
    };

    // A relative import stays relative to the importing document and carries
    // that document's module into the target.
    var left_shared = try context.store.uriFromImportStr(gpa, left_handle, "./shared.zig");
    defer left_shared.deinit(gpa);
    const left_shared_target = try Only.of(left_shared);
    var right_shared = try context.store.uriFromImportStr(gpa, right_handle, "./shared.zig");
    defer right_shared.deinit(gpa);
    const right_shared_target = try Only.of(right_shared);
    try std.testing.expect(left_shared_target.uri.eql(right_shared_target.uri));
    try std.testing.expect(left_shared_target.module == left_module);
    try std.testing.expect(right_shared_target.module == right_module);

    // One physical source, two environments: one parse, two semantic views.
    const left_view = try context.sourceHandle(shared.path, left_module);
    const right_view = try context.sourceHandle(shared.path, right_module);
    try std.testing.expect(left_view.document == right_view.document);
    try std.testing.expect(!left_view.eql(right_view));

    var left_resolver: TypeResolver = undefined;
    try left_resolver.initBorrowed(&context, gpa, left_view);
    defer left_resolver.deinit();
    var right_resolver: TypeResolver = undefined;
    try right_resolver.initBorrowed(&context, gpa, right_view);
    defer right_resolver.deinit();
    var queried = false;
    for (left_view.document.tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const right_info = (try right_resolver.intInfo(node)) orelse return error.MissingRightTagType;
        try std.testing.expectEqual(@as(u16, 32), right_info.bits);
        const left_info = (try left_resolver.intInfo(node)) orelse return error.MissingLeftTagType;
        try std.testing.expectEqual(@as(u16, 8), left_info.bits);
        queried = true;
    }
    try std.testing.expect(queried);
}

/// One project written into a temp directory, wired the way the acceptance
/// cases describe: declared modules, relative imports that reach a shared
/// file, and an alias only some of them wire.
const MembershipProject = struct {
    directory: [:0]u8,
    context: *TypeContext,
    policy_roots: []const []const u8,

    fn build(gpa: std.mem.Allocator, io: std.Io, tmp: *std.testing.TmpDir, build_zig: []const u8, sources: []const [2][]const u8) !MembershipProject {
        const script = try std.fmt.allocPrint(
            gpa,
            "const std = @import(\"std\");\npub fn build(b: *std.Build) void {{\n{s}\n}}\n",
            .{build_zig},
        );
        defer gpa.free(script);
        try tmp.dir.writeFile(io, .{ .sub_path = "build.zig", .data = script });
        for (sources) |source| {
            try tmp.dir.writeFile(io, .{ .sub_path = source[0], .data = source[1] });
        }
        const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
        errdefer gpa.free(directory);
        const context = try gpa.create(TypeContext);
        errdefer gpa.destroy(context);
        try context.init(gpa, io);
        errdefer context.deinit();
        const policy_roots = try gpa.dupe([]const u8, &.{directory});
        context.store.source_policy = .{ .roots = policy_roots };
        return .{ .directory = directory, .context = context, .policy_roots = policy_roots };
    }

    fn deinit(self: *MembershipProject, gpa: std.mem.Allocator) void {
        self.context.deinit();
        gpa.destroy(self.context);
        gpa.free(self.policy_roots);
        gpa.free(self.directory);
        self.* = undefined;
    }

    fn path(self: *MembershipProject, gpa: std.mem.Allocator, name: []const u8) ![]u8 {
        return std.fs.path.join(gpa, &.{ self.directory, name });
    }

    fn uri(self: *MembershipProject, gpa: std.mem.Allocator, name: []const u8) !Uri {
        const full_path = try self.path(gpa, name);
        defer gpa.free(full_path);
        return Uri.fromPath(gpa, full_path);
    }

    /// What `@import(name)` resolves to inside `file`, read the way the file
    /// under analysis reads it: through the store, with whatever module that
    /// file has actually been proven to belong to.
    fn resolveIn(
        self: *MembershipProject,
        gpa: std.mem.Allocator,
        file: []const u8,
        name: []const u8,
    ) !?DocumentStore.ResolvedImport {
        const full_path = try self.path(gpa, file);
        defer gpa.free(full_path);
        const document_uri = try Uri.fromPath(gpa, full_path);
        defer document_uri.deinit(gpa);
        const module = try self.context.store.moduleForDocument(document_uri);
        const handle = self.context.store.getOrLoadHandle(document_uri, module) catch |err| switch (err) {
            error.FileNotFound, error.NotDir => return null,
            error.Canceled => return error.Canceled,
            error.OutOfMemory => return error.OutOfMemory,
            error.SourceExcluded => return error.SourceExcluded,
        } orelse return null;
        var resolved = try self.context.store.uriFromImportStr(gpa, handle, name);
        return switch (resolved) {
            .one => |target| target,
            .none, .many => blk: {
                resolved.deinit(gpa);
                break :blk null;
            },
        };
    }
};

test "a file no module imports does not borrow another module's named import" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var project = try MembershipProject.build(gpa, io, &tmp,
        \\const left_dep = b.createModule(.{ .root_source_file = b.path("left_dep.zig") });
        \\const left = b.addModule("left", .{ .root_source_file = b.path("left.zig") });
        \\left.addImport("dep", left_dep);
    , &.{
        .{ "left.zig", "pub const tag: u8 = 1;\n" },
        .{ "left_dep.zig", "pub const tag: u8 = 2;\n" },
        .{ "standalone.zig", "pub const borrowed = @import(\"dep\");\n" },
    });
    defer project.deinit(gpa);

    // `left` genuinely wires `dep`, and `left.zig` resolves it.
    const wired = (try project.resolveIn(gpa, "left.zig", "dep")).?;
    defer wired.uri.deinit(gpa);
    try std.testing.expect(wired.module != .unscoped);

    // `standalone.zig` sits in the same directory and names the same alias,
    // and no module imports it.  Resolving it from `left`'s table would be a
    // guess about an environment this file has none of, so it stays unknown.
    const standalone_uri = try project.uri(gpa, "standalone.zig");
    defer standalone_uri.deinit(gpa);
    try std.testing.expectEqual(ModuleId.unscoped, try project.context.store.moduleForDocument(standalone_uri));
    try std.testing.expectEqual(@as(?DocumentStore.ResolvedImport, null), try project.resolveIn(gpa, "standalone.zig", "dep"));
}

test "a file a module really imports inherits that module's named import" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var project = try MembershipProject.build(gpa, io, &tmp,
        \\const left_dep = b.createModule(.{ .root_source_file = b.path("left_dep.zig") });
        \\const left = b.addModule("left", .{ .root_source_file = b.path("left.zig") });
        \\left.addImport("dep", left_dep);
    , &.{
        .{ "left.zig", "const helper = @import(\"./helper.zig\");\npub const tag: u8 = helper.tag;\n" },
        .{ "helper.zig", "pub const borrowed = @import(\"dep\");\n" },
        .{ "left_dep.zig", "pub const tag: u8 = 2;\n" },
    });
    defer project.deinit(gpa);

    // `left.zig` imports `helper.zig`, so exactly one environment owns it
    // and that membership is the whole of its identity.
    const helper_uri = try project.uri(gpa, "helper.zig");
    defer helper_uri.deinit(gpa);
    const helper_module = try project.context.store.moduleForDocument(helper_uri);
    try std.testing.expect(helper_module != ModuleId.unscoped);

    const resolved = (try project.resolveIn(gpa, "helper.zig", "dep")).?;
    defer resolved.uri.deinit(gpa);
    try std.testing.expect(resolved.module != .unscoped);
}

test "a file two modules import is answered only when both agree, and a missing alias vetoes" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;

    // Two modules import the same file and wire `dep` differently.
    {
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        var project = try MembershipProject.build(gpa, io, &tmp,
            \\const left_dep = b.createModule(.{ .root_source_file = b.path("left_dep.zig") });
            \\const right_dep = b.createModule(.{ .root_source_file = b.path("right_dep.zig") });
            \\const left = b.addModule("left", .{ .root_source_file = b.path("left.zig") });
            \\left.addImport("dep", left_dep);
            \\const right = b.addModule("right", .{ .root_source_file = b.path("right.zig") });
            \\right.addImport("dep", right_dep);
        , &.{
            .{ "left.zig", "const shared = @import(\"./shared.zig\");\npub const a = shared.borrowed;\n" },
            .{ "right.zig", "const shared = @import(\"./shared.zig\");\npub const b = shared.borrowed;\n" },
            .{ "shared.zig", "pub const borrowed = @import(\"dep\");\n" },
            .{ "left_dep.zig", "pub const tag: u8 = 1;\n" },
            .{ "right_dep.zig", "pub const tag: u32 = 2;\n" },
        });
        defer project.deinit(gpa);
        try std.testing.expectEqual(@as(?DocumentStore.ResolvedImport, null), try project.resolveIn(gpa, "shared.zig", "dep"));
    }

    // Two modules import the same file and only one wires the alias at all.
    {
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        var project = try MembershipProject.build(gpa, io, &tmp,
            \\const left_dep = b.createModule(.{ .root_source_file = b.path("left_dep.zig") });
            \\const left = b.addModule("left", .{ .root_source_file = b.path("left.zig") });
            \\left.addImport("dep", left_dep);
            \\const right = b.addModule("right", .{ .root_source_file = b.path("right.zig") });
        , &.{
            .{ "left.zig", "const shared = @import(\"./shared.zig\");\npub const a = shared.borrowed;\n" },
            .{ "right.zig", "const shared = @import(\"./shared.zig\");\npub const b = shared.borrowed;\n" },
            .{ "shared.zig", "pub const borrowed = @import(\"dep\");\n" },
            .{ "left_dep.zig", "pub const tag: u8 = 1;\n" },
        });
        defer project.deinit(gpa);
        // A candidate that does not wire the name says the name does not
        // exist in the environment it would resolve in.  That vetoes.
        try std.testing.expectEqual(@as(?DocumentStore.ResolvedImport, null), try project.resolveIn(gpa, "shared.zig", "dep"));
    }
}

test "one root declared by two modules is two identities, each resolved by its own handle" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var project = try MembershipProject.build(gpa, io, &tmp,
        \\const left_dep = b.createModule(.{ .root_source_file = b.path("left_dep.zig") });
        \\const right_dep = b.createModule(.{ .root_source_file = b.path("right_dep.zig") });
        \\const left = b.addModule("left", .{ .root_source_file = b.path("shared.zig") });
        \\left.addImport("dep", left_dep);
        \\const right = b.addModule("right", .{ .root_source_file = b.path("shared.zig") });
        \\right.addImport("dep", right_dep);
    , &.{
        .{ "shared.zig", "pub const borrowed = @import(\"dep\");\n" },
        .{ "left_dep.zig", "pub const tag: u8 = 1;\n" },
        .{ "right_dep.zig", "pub const tag: u32 = 2;\n" },
    });
    defer project.deinit(gpa);

    const shared_path = try project.path(gpa, "shared.zig");
    defer gpa.free(shared_path);
    const shared_uri = try Uri.fromPath(gpa, shared_path);
    defer shared_uri.deinit(gpa);

    // The entry that names only the file names neither compilation, so it
    // stays unproven rather than picking one.
    try std.testing.expectEqual(ModuleId.unscoped, try project.context.store.moduleForDocument(shared_uri));

    // Each declaration is still reached by its own id, and each resolves its
    // own wiring of the same file.
    const candidates = try project.context.store.candidateEnvironments(shared_path);
    defer project.context.gpa.free(candidates);
    try std.testing.expectEqual(@as(usize, 2), candidates.len);

    for (candidates) |identity| {
        const handle = try project.context.sourceHandle(shared_path, try project.context.modules.intern(identity));
        var resolved = try project.context.store.uriFromImportStr(gpa, handle, "dep");
        defer resolved.deinit(gpa);
        const target = switch (resolved) {
            .one => |value| value,
            .none, .many => return error.NamedImportDidNotResolve,
        };
        try std.testing.expect(std.mem.endsWith(u8, target.uri.raw, "left_dep.zig") or
            std.mem.endsWith(u8, target.uri.raw, "right_dep.zig"));
        // A relative import from this file keeps the same environment.
        var local = try project.context.store.uriFromImportStr(gpa, handle, "./left_dep.zig");
        defer local.deinit(gpa);
        try std.testing.expectEqual(handle.module, (switch (local) {
            .one => |value| value.module,
            .none, .many => return error.RelativeImportDidNotResolve,
        }));
    }
}

// ── Declaration names ───────────────────────────────────────────

test "two namespaces declaring the same leaf name answer with their own qualified names" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-name-memo.zig",
        \\const Namespace = struct { const Box = struct {}; };
        \\const Other = struct { const Box = struct {}; };
        \\fn observe(value: ?*Namespace.Box, sibling: ?*Other.Box) void {
        \\    _ = value;
        \\    _ = sibling;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const value = try testIdentifier(tree, "value");
    const sibling = try testIdentifier(tree, "sibling");

    // A name is the walk out of the declaration, joined with the containers
    // that declare it.  This one belongs to this file, so the spelling it is
    // dispatched on is that same name.
    try std.testing.expectEqualStrings("Namespace.Box", (try resolver.typeNameOfNode(value)).?);
    try std.testing.expectEqualStrings("Namespace.Box", (try resolver.typeReferenceOfNode(value)).?);

    // A second namespace declaring the same leaf name is a different
    // declaration, and it answers with the qualifier that belongs to it
    // rather than with the one that came first.
    try std.testing.expectEqualStrings("Other.Box", (try resolver.typeNameOfNode(sibling)).?);

    // Asking about either of them again is that same answer.
    try std.testing.expectEqualStrings("Namespace.Box", (try resolver.typeNameOfNode(value)).?);
    try std.testing.expectEqualStrings("Other.Box", (try resolver.typeNameOfNode(sibling)).?);
}

test "an imported container answers with its declared name and this file's alias for it" {
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
        \\fn observe(value: ?*remote.Namespace.Box, local: ?*Box) void { _ = value; _ = local; }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const value = try testIdentifier(tree, "value");

    // The name is the one the declaration has where it is declared.  The
    // reference is the one THIS document can dispatch on, so the alias this
    // file binds for the file it lives in leads it.
    const name = (try resolver.typeNameOfNode(value)).?;
    try std.testing.expectEqualStrings("Namespace.Box", name);
    const reference = (try resolver.typeReferenceOfNode(value)).?;
    try std.testing.expectEqualStrings("remote.Namespace.Box", reference);

    // The resolver's own allocations for a question it has already answered:
    // none, and no bytes.  The analyser and the arena hold the allocators
    // they were given, so this counts the resolver's own share.
    var counting: std.testing.FailingAllocator = .init(gpa, .{});
    const resolver_gpa = resolver.gpa;
    resolver.gpa = counting.allocator();
    defer resolver.gpa = resolver_gpa;
    try std.testing.expectEqualStrings("remote.Namespace.Box", (try resolver.typeReferenceOfNode(value)).?);
    try std.testing.expectEqual(@as(usize, 0), counting.allocations);
    try std.testing.expectEqual(@as(usize, 0), counting.allocated_bytes);
    // Back to the resolver's own allocator before the colder questions
    // below, which really do have answers to give for the first time.
    resolver.gpa = resolver_gpa;

    // Bytes already handed out are still readable, and still say the same
    // thing: an answer is never written over by a later question.
    try std.testing.expectEqualStrings("remote.Namespace.Box", reference);
    try std.testing.expectEqualStrings("Namespace.Box", name);

    // A declaration this very file owns needs no alias, and is its own site.
    const local = try testIdentifier(tree, "local");
    try std.testing.expectEqualStrings("Box", (try resolver.typeNameOfNode(local)).?);
    try std.testing.expectEqualStrings("Box", (try resolver.typeReferenceOfNode(local)).?);

    // The root of an imported file is a declaration as well, and the one
    // whose name costs the most to derive: turning the document's canonical
    // URI back into a path and a name.  A root container has no name of its
    // own to qualify, so the alias alone is what this document dispatches on.
    const imported_root = try testIdentifier(tree, "remote");
    try std.testing.expectEqualStrings("remote", (try resolver.typeNameOfNode(imported_root)).?);
    try std.testing.expectEqualStrings("remote", (try resolver.typeReferenceOfNode(imported_root)).?);
}

test "a declaration this file does not import has a name but no reference" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-unnamed-reference.zig",
        \\const std = @import("std");
        \\fn observe(value: ?*std.mem.Allocator) void { _ = value; }
    );
    defer resolver.deinit();
    const value = try testIdentifier(&resolver.handle.document.tree, "value");

    // The allocator is declared in the standard library, which this file
    // reaches through `std` and does not import itself.  It has a name where
    // it is declared — a file's root container is named after the file — and
    // none here, because this file binds no alias for the file that declares
    // it and so has no spelling of its own to dispatch on it with.
    try std.testing.expectEqualStrings("Allocator", (try resolver.typeNameOfNode(value)).?);
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeReferenceOfNode(value));
    // A second question is that same absence, not a fresh answer.
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeReferenceOfNode(value));
}

test "a declaration inside a function body has no qualified name" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-local-declaration.zig",
        \\fn observe() void {
        \\    const Local = struct { value: u32 };
        \\    var local: Local = .{ .value = 1 };
        \\    _ = local;
        \\}
    );
    defer resolver.deinit();
    // A declaration inside a function body has no qualified name to be
    // reached by: walking out of it reaches a block, which declares no
    // container, so this one is unknown.
    const local_type = try testIdentifier(&resolver.handle.document.tree, "Local");
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(local_type));
    // A reference has no name to qualify, so it is unknown in the same way.
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeReferenceOfNode(local_type));
    // And a second question is that same unknown.
    try std.testing.expectEqual(@as(?[]const u8, null), try resolver.typeNameOfNode(local_type));
}

test "a file's root container is named after the file with the Zig suffix taken off" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "remote.zig", .data =
        \\pub const Box = struct {};
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
        \\fn observe(remote_box: ?*remote.Box) void { _ = remote_box; }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;

    // The root of a file is the file itself: what an `@import` binds is that
    // file's `@This()`, and its name is the file's own name with the suffix
    // which says it is Zig source taken off the END of it.  `remote.zig` is
    // `remote`, which is also the alias this document binds it under, so the
    // name and the spelling agree.
    const remote_root = try testIdentifier(tree, "remote");
    try std.testing.expectEqualStrings("remote", (try resolver.typeNameOfNode(remote_root)).?);
    try std.testing.expectEqualStrings("remote", (try resolver.typeReferenceOfNode(remote_root)).?);

    // A file whose whole name IS that suffix has nothing left over to be
    // named by.  Admission is not the question here, so nothing in the
    // source policy is widened to reach one: this is the way an editor asks
    // about the file it is holding — an INDEPENDENT resolver, given the
    // document's text and the path it is filed under — and the root asked
    // about is the one the file denotes itself with `@This()`.
    var editor_context: TypeContext = undefined;
    try editor_context.init(gpa, io);
    defer editor_context.deinit();
    var editor_resolver: TypeResolver = undefined;
    try editor_resolver.init(&editor_context, gpa, "zbc-empty-root-name/.zig",
        \\const Root = @This();
        \\fn observe() void { _ = Root; }
    );
    defer editor_resolver.deinit();
    const empty_root = try testIdentifier(&editor_resolver.handle.document.tree, "Root");
    // Nothing is left of the name once the suffix is taken off, which is an
    // answer and not a question this document failed to read: a root with no
    // name is unknown as a name and as a spelling.
    try std.testing.expectEqual(@as(?[]const u8, null), try editor_resolver.typeNameOfNode(empty_root));
    try std.testing.expectEqual(@as(?[]const u8, null), try editor_resolver.typeReferenceOfNode(empty_root));
}

test "a name that was already derived is answered even when writing it down runs out of memory" {
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
        \\fn observe(value: ?*remote.Namespace.Box) void { _ = value; }
    );
    defer resolver.deinit();
    const value = try testIdentifier(&resolver.handle.document.tree, "value");

    // One warm run settles every allocation the question makes other than
    // writing its answer down: the parse, the type resolution, the document
    // scope, and this file's own import bindings.
    try std.testing.expectEqualStrings("remote.Namespace.Box", (try resolver.typeReferenceOfNode(value)).?);

    // Emptying an answer without freeing its capacity would make the write
    // below free of charge, which would prove nothing, so the cache is
    // released outright.  The arena is untouched: names derived from it are
    // still there, and no part of this resolver's own arena allocation can
    // fail, so the one allocation refused below is a memo and nothing else.
    resolver.reference_cache.deinit(gpa);
    resolver.reference_cache = .empty;
    var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = 0 });
    resolver.gpa = failing.allocator();
    defer resolver.gpa = gpa;

    // Only the spelling is written down here: the name for this declaration
    // site is settled already, so the refused allocation is the one the memo
    // of the answer THIS question asks about is made of.  The spelling was
    // derived before the write was attempted, and a memo that will not grow
    // is what the NEXT question pays for: the caller is told the name it
    // asked for.
    try std.testing.expectEqualStrings("remote.Namespace.Box", (try resolver.typeReferenceOfNode(value)).?);
    // And nothing was written down, so no half of a spelling is left
    // standing in the place of the derivation the next question must make.
    try std.testing.expectEqual(@as(usize, 0), resolver.reference_cache.count());

    resolver.gpa = gpa;
    // Asked again with an allocator that can answer, the derivation reaches
    // the same spelling ...
    try std.testing.expectEqualStrings("remote.Namespace.Box", (try resolver.typeReferenceOfNode(value)).?);
    // ... and this time it is kept, so a third question is that answer
    // rather than a second derivation that happened to agree.
    try std.testing.expectEqual(@as(usize, 1), resolver.reference_cache.count());
    try std.testing.expectEqualStrings("remote.Namespace.Box", (try resolver.typeReferenceOfNode(value)).?);

    // The name under the spelling is kept the same way.  With the whole
    // answer dropped, the refused allocation is the one that would have
    // recorded the name, and the question is still answered with it.
    resolver.name_cache.deinit(gpa);
    resolver.name_cache = .empty;
    resolver.reference_cache.deinit(gpa);
    resolver.reference_cache = .empty;
    resolver.gpa = failing.allocator();
    try std.testing.expectEqualStrings("remote.Namespace.Box", (try resolver.typeReferenceOfNode(value)).?);
    try std.testing.expectEqual(@as(usize, 0), resolver.name_cache.count());
    resolver.gpa = gpa;
    try std.testing.expectEqualStrings("remote.Namespace.Box", (try resolver.typeReferenceOfNode(value)).?);
    try std.testing.expectEqual(@as(usize, 1), resolver.name_cache.count());
    try std.testing.expectEqualStrings("remote.Namespace.Box", (try resolver.typeReferenceOfNode(value)).?);
}

test "borrowed generic frames resolve field types independently across reentrant queries" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-generic-query-frames.zig",
        \\fn Box(comptime T: type) type {
        \\    return struct {
        \\        value: T,
        \\        fn read(self: *const @This()) T { return self.value; }
        \\        fn unknown() void { missing(); }
        \\    };
        \\}
        \\fn use(wide: Box(u64), narrow: Box(u8)) void {
        \\    _ = wide;
        \\    _ = narrow;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const wide = (try resolver.containerOfNode(try testIdentifier(tree, "wide"))).?;
    const narrow = (try resolver.containerOfNode(try testIdentifier(tree, "narrow"))).?;
    const wide_frame = resolver.frameForContainer(wide);
    const narrow_frame = resolver.frameForContainer(narrow);
    const field = try testFieldAccess(tree, "self");
    try std.testing.expectEqual(@as(u16, 64), (try wide_frame.intInfo(field)).?.bits);
    try std.testing.expectEqual(@as(u16, 8), (try narrow_frame.intInfo(field)).?.bits);
    try std.testing.expectEqual(@as(u16, 64), (try wide_frame.intInfo(field)).?.bits);
    const unknown = try testIdentifier(tree, "missing");
    try std.testing.expect(try wide_frame.functionReference(unknown) == .unknown);
    try std.testing.expect(try narrow_frame.functionReference(unknown) == .unknown);
    try std.testing.expectEqual(@as(?TypeResolver.IntInfo, null), try resolver.intInfo(field));
}

test "inline tuple call frames enforce existing work and expanded caller limits" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-inline-tuple-call-limits.zig",
        \\fn checked(comptime T: type) T { return 0; }
        \\test "native" {
        \\    inline for (.{ u8, c_int, c_uint }) |T| {
        \\        _ = checked(T);
        \\    }
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const call = try testNthCallNamed(tree, "checked", 0);
    const frame = resolver.resolutionFrame();
    var caller_work: u32 = @intCast(tree.nodes.len + 4);
    var too_few_callers: usize = 2;
    try std.testing.expectError(error.InlineTupleCallersExceeded, frame.inlineTupleCallReferences(call, &caller_work, &too_few_callers));
    try std.testing.expectEqual(@as(usize, 2), too_few_callers);
    var too_few_steps: u32 = 1;
    var callers: usize = 3;
    try std.testing.expectError(error.InlineTupleStepsExceeded, frame.inlineTupleCallReferences(call, &too_few_steps, &callers));
    try std.testing.expectEqual(@as(u32, 0), too_few_steps);
    try std.testing.expectEqual(@as(usize, 3), callers);
}

test "test-local inline tuple frames retain each generic conversion destination" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-test-local-inline-tuple-destinations.zig",
        \\test "native" {
        \\    const Native = struct {
        \\        fn checked(comptime T: type, source: anytype) error{Bad}!T {
        \\            const value: f64 = @floatCast(source);
        \\            return @intFromFloat(value);
        \\        }
        \\    };
        \\    _ = Native.checked(u8, @as(f64, 0)) catch 0;
        \\    inline for (.{ u8, c_int, c_uint }) |T| {
        \\        _ = Native.checked(T, @as(f64, 0)) catch 0;
        \\    }
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const call = try testNthCallNamed(tree, "checked", 1);
    var conversion: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@intFromFloat")) {
            conversion = node;
            break;
        }
    }
    const conversion_node = conversion orelse return error.MissingConversion;
    // The uninstantiated declaration still has no concrete destination.
    try std.testing.expectEqual(
        @as(?TypeResolver.IntInfo, null),
        try resolver.contextIntInfo(conversion_node),
    );
    const direct = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "checked", 0),
    )) {
        .function => |reference| reference,
        else => return error.MissingDirectFrame,
    };
    const direct_frame = resolver.frameForFunction(direct);
    try std.testing.expectEqual(
        @as(?TypeResolver.IntInfo, null),
        try direct_frame.intInfo(conversion_node),
    );
    try std.testing.expectEqual(
        @as(?TypeResolver.IntInfo, .{ .bits = 8, .signed = false }),
        try direct_frame.contextIntInfo(conversion_node),
    );
    var work: u32 = 4096;
    var callers: usize = 3;
    const references = (try resolver.resolutionFrame().inlineTupleCallReferences(
        call, &work, &callers,
    )) orelse return error.MissingTupleFrames;
    try std.testing.expectEqual(@as(usize, 3), references.len);
    try std.testing.expectEqual(@as(usize, 0), callers);
    const expected = [_]TypeResolver.IntInfo{
        .{ .bits = 8, .signed = false },
        .{ .bits = 32, .signed = true },
        .{ .bits = 32, .signed = false },
    };
    for (references, expected) |reference, destination| {
        const frame = resolver.frameForFunction(reference);
        try std.testing.expectEqual(
            @as(?TypeResolver.IntInfo, destination),
            try frame.contextIntInfo(conversion_node),
        );
    }
}

test "actual method calls bind This pointer receivers on locals and fields" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-this-pointer-receivers.zig",
        \\const Other = struct { value: u8 };
        \\const Pair = struct {
        \\    known: u8,
        \\    runtime: [2]u8,
        \\    fn checked(out: *@This(), src: @This(), flag: bool) bool {
        \\        if (!flag) return false;
        \\        const saved = src;
        \\        out.* = saved;
        \\        return true;
        \\    }
        \\    fn mismatched(out: *Other, src: @This(), flag: bool) bool {
        \\        _ = out; _ = src; return flag;
        \\    }
        \\};
        \\const Holder = struct { pair: Pair, sibling: u8 };
        \\pub fn selected(flag: bool) void {
        \\    const src: Pair = .{ .known = 1, .runtime = .{ 2, undefined } };
        \\    var direct: Pair = undefined;
        \\    if (direct.checked(src, flag)) {
        \\        _ = direct.known;
        \\        _ = direct.runtime[1];
        \\    }
        \\    var holder: Holder = .{ .pair = undefined, .sibling = 9 };
        \\    if (holder.pair.checked(src, flag)) {
        \\        _ = holder.pair.known;
        \\        _ = holder.sibling;
        \\        _ = holder.pair.runtime[1];
        \\    }
        \\    _ = direct.mismatched(src, flag);
        \\    _ = holder.pair.mismatched(src, flag);
        \\}
        \\const callback = selected;
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    // Body queries precede call-summary queries during flow lowering.
    for (1..tree.nodes.len) |raw| {
        _ = try resolver.resolutionFrame().resolveValueOfNode(@enumFromInt(raw));
    }
    const selected = switch (try resolver.functionReference(try testIdentifier(tree, "selected"))) {
        .function => |reference| reference,
        else => return error.MissingCaller,
    };
    const frame = resolver.frameForFunction(selected);
    var checked_token: ?Ast.TokenIndex = null;
    for (0..2) |occurrence| {
        const node = try testNthCallNamed(tree, "checked", occurrence);
        try std.testing.expect(try resolver.functionReferenceOfCall(node) == .function);
        const checked = switch (try frame.functionReferenceOfCall(node)) {
            .function => |reference| reference,
            else => return error.MissingThisReceiver,
        };
        if (checked_token) |token| {
            try std.testing.expectEqual(token, checked.fn_token);
        } else {
            checked_token = checked.fn_token;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const arguments = (try frame.callArgumentsOf(&buffer, node)) orelse return error.MissingArguments;
        try std.testing.expect(arguments.receiver != null);
        try std.testing.expectEqual(@as(usize, 2), arguments.arguments.len);
        try std.testing.expectEqual(arguments.receiver, try frame.callArgument(node, 0));
        try std.testing.expectEqual(arguments.arguments[0], (try frame.callArgument(node, 1)).?);
        try std.testing.expectEqual(arguments.arguments[1], (try frame.callArgument(node, 2)).?);
        const mismatched = try testNthCallNamed(tree, "mismatched", occurrence);
        try std.testing.expect(try frame.functionReferenceOfCall(mismatched) == .unknown);
        try std.testing.expectEqual(@as(?TypeResolver.CallArguments, null), try frame.callArgumentsOf(&buffer, mismatched));
    }
}

fn testFieldExpression(tree: *const Ast, expression: []const u8, first: Ast.TokenIndex, last: Ast.TokenIndex) !Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const start = tree.firstToken(node);
        const end = tree.lastToken(node);
        if (start < first or end > last) continue;
        const source = tree.source[tree.tokenStart(start) .. tree.tokenStart(end) + tree.tokenSlice(end).len];
        if (std.mem.eql(u8, source, expression)) return node;
    }
    return error.MissingFieldAccess;
}

fn testFunctionDeclaration(reference: TypeResolver.FunctionReference) !Ast.Node.Index {
    const tree = reference.tree;
    var buffer: [1]Ast.Node.Index = undefined;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .fn_decl) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const proto = tree.fullFnProto(&buffer, node).?;
        if (proto.ast.fn_token == reference.fn_token) return node;
    }
    return error.MissingDeclaration;
}

test "actual allocating writer method frames retain the lexical Writer alias" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-actual-writer-method-frame.zig",
        \\const std = @import("std");
        \\const Buffer = []u8;
        \\fn copy(gpa: std.mem.Allocator, reader: []const u8) !Buffer {
        \\    var writer = std.Io.Writer.Allocating.init(gpa);
        \\    try writer.writer.writeAll(reader);
        \\    return writer.toOwnedSlice();
        \\}
        \\fn entry(gpa: std.mem.Allocator, reader: []const u8) !Buffer {
        \\    _ = std.Io.Writer.writeAll;
        \\    return copy(gpa, reader);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const copy = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "copy", 0))) {
        .function => |reference| reference,
        else => return error.MissingCopy,
    };
    const copy_frame = resolver.frameForFunction(copy);
    const owned = switch (try copy_frame.functionReferenceOfCall(try testNthCallNamed(tree, "toOwnedSlice", 0))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const owned_frame = resolver.frameForFunction(owned);
    const owned_tree = owned.tree;
    const owned_declaration = try testFunctionDeclaration(owned);
    const buffer = try testFieldExpression(owned_tree, "a.writer.buffer", owned_tree.firstToken(owned_declaration), owned_tree.lastToken(owned_declaration));
    const buffer_type = (try owned_frame.typeOfNode(buffer)) orelse return error.MissingBufferType;
    try std.testing.expectEqual(std.builtin.TypeId.pointer, resolver.typeTag(buffer_type).?);
    try std.testing.expectEqual(std.builtin.Type.Pointer.Size.slice, resolver.pointerSize(buffer_type).?);
    const expected_buffer = (try resolver.typeOfNode(try testIdentifier(tree, "Buffer"))) orelse return error.MissingExpectedBufferType;
    try std.testing.expect(TypeResolver.ActualTypeID.eql(expected_buffer, buffer_type));

    const written = switch (try copy_frame.functionReferenceOfCall(try testNthCallNamed(tree, "writeAll", 0))) {
        .function => |reference| reference,
        else => return error.MissingWriterMethod,
    };
    try std.testing.expect(written.handle.eql(owned.handle));
    try std.testing.expectEqualStrings("writeAll", written.actual_type.data.function.name.?);
    const sdk_method = try testFieldExpression(tree, "std.Io.Writer.writeAll", 0, @intCast(tree.tokens.len - 1));
    const expected_method = switch (try resolver.functionReference(sdk_method)) {
        .function => |reference| reference,
        else => return error.MissingCanonicalWriterMethod,
    };
    try std.testing.expect(written.handle.eql(expected_method.handle));
    try std.testing.expectEqual(expected_method.fn_token, written.fn_token);
    const writer_frame = resolver.frameForFunction(written);
    const write_declaration = try testFunctionDeclaration(written);
    const nested_write = try testFieldExpression(written.tree, "w.write", written.tree.firstToken(write_declaration), written.tree.lastToken(write_declaration));
    const nested = switch (try writer_frame.functionReference(nested_write)) {
        .function => |reference| reference,
        else => return error.MissingWriterBodyMethod,
    };
    try std.testing.expect(nested.handle.eql(written.handle));
    try std.testing.expectEqualStrings("write", nested.actual_type.data.function.name.?);
}

test "ancestor This aliases retain generic field types without becoming nested receivers" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-ancestor-this-alias.zig",
        \\fn Outer(comptime T: type) type {
        \\    return struct {
        \\        const Self = @This();
        \\        buffer: []T,
        \\        fn writeAll(w: *Self, reader: []const T) void { _ = w.buffer; _ = reader; }
        \\        const Allocating = struct {
        \\            writer: Self,
        \\            fn read(a: *@This()) T { return a.writer.buffer[0]; }
        \\            fn copy(a: *@This(), reader: []const T) void { a.writer.writeAll(reader); }
        \\        };
        \\    };
        \\}
        \\fn wide(a: *Outer(u64).Allocating) u64 { a.copy(&.{}); return a.read(); }
        \\fn narrow(a: *Outer(u8).Allocating) u8 { a.copy(&.{}); return a.read(); }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const read_field = try testFieldExpression(tree, "a.writer.buffer", 0, @intCast(tree.tokens.len - 1));
    for ([_]usize{ 0, 1, 0 }) |occurrence| {
        const read = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "read", occurrence))) {
            .function => |reference| reference,
            else => return error.MissingCallee,
        };
        const frame = resolver.frameForFunction(read);
        const field = (try frame.typeOfNode(read_field)) orelse return error.MissingBufferType;
        try std.testing.expectEqual(std.builtin.Type.Pointer.Size.slice, resolver.pointerSize(field).?);
        const element = resolver.childType(field) orelse return error.MissingElementType;
        try std.testing.expectEqual(@as(?u16, if (occurrence == 0) 64 else 8), try testUnsignedBitsOf(&resolver, element));
        const copy = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "copy", occurrence))) {
            .function => |reference| reference,
            else => return error.MissingCallee,
        };
        const written = switch (try (resolver.frameForFunction(copy)).functionReferenceOfCall(try testNthCallNamed(tree, "writeAll", 0))) {
            .function => |reference| reference,
            else => return error.MissingWriterMethod,
        };
        try std.testing.expectEqual(@as(?u16, if (occurrence == 0) 64 else 8), try testUnsignedBitsOf(&resolver, resolver.childType(written.actual_type.data.function.parameters[1].type).?));
    }
}

/// `Cache.run` is written once and calls the context's own `read` and `write`, so
/// which body a resolution reaches is decided by the instantiation, not by the
/// declaration.  The same body type-checks for both contexts.
const GenericContextFixture =
    \\const Reading = struct {
    \\    const Self = @This();
    \\    total: u64,
    \\    pub fn read(self: Self) u64 { return self.total; }
    \\    pub fn write(self: *Reading, value: u64) void { self.total = value; }
    \\};
    \\const Writing = struct {
    \\    const Self = @This();
    \\    slot: u8,
    \\    pub fn read(self: Self) u8 { return self.slot; }
    \\    pub fn write(self: *Writing, value: u8) void { self.slot = value; }
    \\};
    \\fn Cache(comptime T: type, comptime Context: type) type {
    \\    return struct {
    \\        context: Context,
    \\        pub fn run(self: *@This(), item: T) T {
    \\            const seen = self.context.read();
    \\            self.context.write(item);
    \\            return seen;
    \\        }
    \\    };
    \\}
    \\fn useReading(cache: *Cache(u64, Reading)) u64 { return cache.run(1); }
    \\fn useWriting(cache: *Cache(u8, Writing)) u8 { return cache.run(1); }
;

/// One generic body whose context one call site binds and another cannot.
const UnboundContextFixture =
    \\const Reading = struct {
    \\    total: u64,
    \\    pub fn read(self: *const Reading) u64 { return self.total; }
    \\};
    \\fn Cache(comptime Context: type) type {
    \\    return struct {
    \\        context: Context,
    \\        pub fn run(self: *@This()) void { _ = self.context.read(); }
    \\    };
    \\}
    \\fn through(cache: *Cache(Reading)) void { cache.run(); }
    \\fn unbound(cache: anytype) void { cache.run(); }
;

/// A plain generic whose `anytype` parameter is bound by the CALL rather than
/// inherited from a container: one declaration, two contexts, two callbacks.
const AnytypeCallbackFixture =
    \\const Reading = struct {
    \\    total: u64,
    \\    pub fn read(self: *const Reading) u64 { return self.total; }
    \\    pub fn write(self: *Reading, value: u64) void { self.total = value; }
    \\};
    \\const Writing = struct {
    \\    slot: u8,
    \\    pub fn read(self: *const Writing) u8 { return self.slot; }
    \\    pub fn write(self: *Writing, value: u8) void { self.slot = value; }
    \\};
    \\fn observe(context: anytype) void { _ = context.read(); }
    \\fn store(context: anytype, value: anytype) void { context.write(value); }
    \\fn useReading(context: *Reading) void { observe(context); store(context, 1); }
    \\fn useWriting(context: *Writing) void { observe(context); store(context, 1); }
;

/// The call whose callee is named `name` — an identifier, or a field access
/// ending in that name — `occurrence`-th in source order.  A context is chosen by
/// which call site is asked, never by rewriting the body.
fn testNthCallNamed(tree: *const Ast, name: []const u8, occurrence: usize) !Ast.Node.Index {
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        const callee = call.ast.fn_expr;
        const written = switch (tree.nodeTag(callee)) {
            .identifier => tree.nodeMainToken(callee),
            .field_access => tree.nodeData(callee).node_and_token[1],
            else => continue,
        };
        if (!std.mem.eql(u8, tree.tokenSlice(written), name)) continue;
        if (seen == occurrence) return node;
        seen += 1;
    }
    return error.TestUnexpectedResult;
}

/// The function type a reference actually resolved to: the callee as THIS call
/// instantiated it, which is what a rule asks about afterwards.
fn testActualFunction(reference: TypeResolver.FunctionReference) !Analyser.Type.Data.Function {
    switch (reference.actual_type.data) {
        .function => |info| return info,
        else => return error.NotAFunctionType,
    }
}

/// The container a callee's receiver denotes: the container its frame binds.
fn testReceiverContainerName(resolver: *TypeResolver, reference: TypeResolver.FunctionReference) ![]const u8 {
    const function = try testActualFunction(reference);
    if (function.parameters.len == 0) return error.MissingReceiver;
    var ty = (try resolver.normalizedType(function.parameters[0].type)) orelse return error.MissingReceiver;
    for (0..32) |_| {
        if (ty.data == .container) return (try resolver.containerNameOf(ty.data.container)) orelse error.MissingReceiver;
        ty = (try resolver.normalizedType(resolver.childType(ty) orelse return error.MissingReceiver)) orelse
            return error.MissingReceiver;
    }
    return error.MissingReceiver;
}

/// The width of a resolved unsigned integer type, else null: what a rule that
/// reads a callee asks.
fn testUnsignedBitsOf(resolver: *TypeResolver, value: Analyser.Type) !?u16 {
    const info = (try resolver.intInfoOfType(value)) orelse return null;
    if (info.signed) return error.SignedIntegerType;
    return info.bits;
}

test "one generic declaration reaches a different callback body per instantiation" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-generic-context.zig", GenericContextFixture);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;

    // Both call sites reach ONE declaration, written once in the generic
    // body, so its token and document cannot tell the two uses apart.
    const wide = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "run", 0))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const narrow = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "run", 1))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    try std.testing.expect(wide.fn_token == narrow.fn_token);
    try std.testing.expect(wide.handle.eql(narrow.handle));

    // What each call instantiated is not the declaration: a u64 map hands
    // `run` a 64-bit item and gets a 64-bit answer, a u8 map an 8-bit one.
    const held = try testActualFunction(wide);
    const held_narrow = try testActualFunction(narrow);
    try std.testing.expectEqual(@as(?u16, 64), try testUnsignedBitsOf(&resolver, held.parameters[1].type));
    try std.testing.expectEqual(@as(?u16, 8), try testUnsignedBitsOf(&resolver, held_narrow.parameters[1].type));
    try std.testing.expectEqual(@as(?u16, 64), try testUnsignedBitsOf(&resolver, held.return_value.*));
    try std.testing.expectEqual(@as(?u16, 8), try testUnsignedBitsOf(&resolver, held_narrow.return_value.*));
    try std.testing.expect(!TypeResolver.ActualTypeID.eql(wide.actual_type, narrow.actual_type));

    // One callback call node, asked in each context: two declarations in the
    // two contexts, each handing the container its own item width.
    const wide_frame = resolver.frameForFunction(wide);
    const narrow_frame = resolver.frameForFunction(narrow);
    for ([_][]const u8{ "read", "write" }) |method| {
        const node = try testNthCallNamed(tree, method, 0);
        const wide_body = switch (try wide_frame.functionReferenceOfCall(node)) {
            .function => |reference| reference,
            else => return error.MissingCallback,
        };
        const narrow_body = switch (try narrow_frame.functionReferenceOfCall(node)) {
            .function => |reference| reference,
            else => return error.MissingCallback,
        };
        try std.testing.expect(wide_body.fn_token != narrow_body.fn_token);
        try std.testing.expect(!TypeResolver.ActualTypeID.eql(wide_body.actual_type, narrow_body.actual_type));
        try std.testing.expectEqualStrings("Reading", try testReceiverContainerName(&resolver, wide_body));
        try std.testing.expectEqualStrings("Writing", try testReceiverContainerName(&resolver, narrow_body));
        if (std.mem.eql(u8, method, "read")) continue; // `write` returns nothing; only it takes the item.
        const wide_callback = try testActualFunction(wide_body);
        const narrow_callback = try testActualFunction(narrow_body);
        try std.testing.expectEqual(@as(?u16, 64), try testUnsignedBitsOf(&resolver, wide_callback.parameters[1].type));
        try std.testing.expectEqual(@as(?u16, 8), try testUnsignedBitsOf(&resolver, narrow_callback.parameters[1].type));
        try std.testing.expect((try resolver.intInfoOfType(wide_callback.return_value.*)) == null);
        try std.testing.expect((try resolver.intInfoOfType(narrow_callback.return_value.*)) == null);
    }
}

test "nongeneric method identity excludes sibling generic call bindings" {
    const source: [:0]const u8 =
        \\const Cell = struct {
        \\    value: u32,
        \\    fn poison(self: *Cell) void { self.value = undefined; }
        \\    fn forward(self: *Cell, value: anytype) void { _ = value; self.poison(); }
        \\    fn select(self: *Cell, comptime poison_value: bool) void {
        \\        if (poison_value) self.value = undefined;
        \\    }
        \\};
        \\fn use(cell: *Cell) void {
        \\    cell.forward(@as(u8, 1));
        \\    cell.forward(@as(u64, 2));
        \\    cell.select(false);
        \\    cell.select(true);
        \\}
    ;
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-sibling-callee-identity.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const narrow = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "forward", 0))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const wide = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "forward", 1))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    try std.testing.expect(!narrow.actual_type.eql(wide.actual_type));
    const poison_call = try testNthCallNamed(tree, "poison", 0);
    const narrow_poison = switch (try resolver.frameForFunction(narrow).functionReferenceOfCall(poison_call)) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const wide_poison = switch (try resolver.frameForFunction(wide).functionReferenceOfCall(poison_call)) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    try std.testing.expect(narrow_poison.actual_type.eql(wide_poison.actual_type));
    try std.testing.expectEqual(narrow_poison.actual_type.hash64(), wide_poison.actual_type.hash64());
    try std.testing.expectEqual(@as(usize, 0), narrow_poison.actual_type.data.function.container_type.data.container.bound_params.count());
    const quiet = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "select", 0))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const loud = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "select", 1))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    try std.testing.expect(!quiet.actual_type.eql(loud.actual_type));
}

test "method identity retains enclosing and transported factory bindings" {
    const source: [:0]const u8 =
        \\fn Cell(comptime T: type) type {
        \\    return struct {
        \\        value: T,
        \\        fn select(self: *@This(), next: T) void {
        \\            self.value = next;
        \\        }
        \\    };
        \\}
        \\fn Wrapped(comptime T: type) type { return Cell(T); }
        \\fn use(quiet: *Cell(u8), loud: *Cell(u64), wrapped_quiet: *Wrapped(u8), wrapped_loud: *Wrapped(u64)) void {
        \\    quiet.select(0);
        \\    loud.select(0);
        \\    wrapped_quiet.select(0);
        \\    wrapped_loud.select(0);
        \\}
    ;
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-enclosing-callee-identity.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var references: [4]TypeResolver.FunctionReference = undefined;
    for (&references, [_]u16{ 8, 64, 8, 64 }, 0..) |*reference, bits, index| {
        reference.* = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "select", index))) {
            .function => |function| function,
            else => return error.MissingCallee,
        };
        const container = reference.actual_type.data.function.container_type.data.container;
        try std.testing.expect(container.bound_params.count() != 0);
        const function = try testActualFunction(reference.*);
        try std.testing.expectEqual(@as(?u16, bits), try testUnsignedBitsOf(&resolver, function.parameters[1].type));
    }
    try std.testing.expect(!references[0].actual_type.eql(references[1].actual_type));
    try std.testing.expect(!references[2].actual_type.eql(references[3].actual_type));
}

test "an anytype parameter is bound by the call, so one declaration has two callbacks" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-anytype-callback.zig", AnytypeCallbackFixture);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;

    // Both generic functions are declarations written once.  What differs is
    // the `anytype` argument each call site passes, which is what a frame
    // carries; the declarations themselves are the same tokens both times.
    const observed = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "observe", 0))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const observed_narrow = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "observe", 1))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    try std.testing.expect(observed.fn_token == observed_narrow.fn_token);

    // Each body is read in the frame its OWN call site built: `store` is a
    // separate declaration from `observe` and inherits nothing from it.
    const stored = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "store", 0))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const stored_narrow = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "store", 1))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    try std.testing.expect(stored.fn_token == stored_narrow.fn_token);

    const read_call = try testNthCallNamed(tree, "read", 0);
    const write_call = try testNthCallNamed(tree, "write", 0);
    const wide_read = switch (try (resolver.frameForFunction(observed)).functionReferenceOfCall(read_call)) {
        .function => |reference| reference,
        else => return error.MissingCallback,
    };
    const narrow_read = switch (try (resolver.frameForFunction(observed_narrow)).functionReferenceOfCall(read_call)) {
        .function => |reference| reference,
        else => return error.MissingCallback,
    };
    const wide_write = switch (try (resolver.frameForFunction(stored)).functionReferenceOfCall(write_call)) {
        .function => |reference| reference,
        else => return error.MissingCallback,
    };
    const narrow_write = switch (try (resolver.frameForFunction(stored_narrow)).functionReferenceOfCall(write_call)) {
        .function => |reference| reference,
        else => return error.MissingCallback,
    };

    // One call node per generic body, two answers: the contexts each call
    // site passed, each with its own integer widths.
    try std.testing.expect(wide_read.fn_token != narrow_read.fn_token);
    try std.testing.expect(wide_write.fn_token != narrow_write.fn_token);
    try std.testing.expectEqualStrings("Reading", try testReceiverContainerName(&resolver, wide_read));
    try std.testing.expectEqualStrings("Writing", try testReceiverContainerName(&resolver, narrow_read));
    try std.testing.expectEqual(@as(?u16, 64), try testUnsignedBitsOf(&resolver, (try testActualFunction(wide_read)).return_value.*));
    try std.testing.expectEqual(@as(?u16, 8), try testUnsignedBitsOf(&resolver, (try testActualFunction(narrow_read)).return_value.*));
    try std.testing.expectEqual(@as(?u16, 64), try testUnsignedBitsOf(&resolver, (try testActualFunction(wide_write)).parameters[1].type));
    try std.testing.expectEqual(@as(?u16, 8), try testUnsignedBitsOf(&resolver, (try testActualFunction(narrow_write)).parameters[1].type));
    try std.testing.expect(!TypeResolver.ActualTypeID.eql(wide_read.actual_type, narrow_read.actual_type));
}

test "a callee nothing names is unknown, and a framed query leaves the root where it was" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-generic-context-unbound.zig", UnboundContextFixture);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;

    // A receiver of `anytype` names no declaration: the call has a shape and
    // no callee, and nothing else answers for it.
    switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "run", 1))) {
        .unknown => {},
        else => return error.ExpectedUnknown,
    }

    // The call site that DOES bind `Context` answers, and answers about the
    // declaration the unknown query could not: the unknown is a fact about
    // the query, not about the declaration.
    const reference = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "run", 0))) {
        .function => |found| found,
        else => return error.MissingCallee,
    };
    const callback = switch (try (resolver.frameForFunction(reference)).functionReferenceOfCall(
        try testNthCallNamed(tree, "read", 0),
    )) {
        .function => |found| found,
        else => return error.MissingCallback,
    };
    try std.testing.expectEqualStrings("Reading", try testReceiverContainerName(&resolver, callback));
    try std.testing.expectEqual(@as(?u16, 64), try testUnsignedBitsOf(&resolver, (try testActualFunction(callback)).return_value.*));

    // After that framed query the ordinary context is unchanged: the call
    // that binds nothing is still unknown, and the call that binds a context
    // is the same declaration with the same actual type.
    switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "run", 1))) {
        .unknown => {},
        else => return error.ExpectedUnknown,
    }
    const again = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "run", 0))) {
        .function => |found| found,
        else => return error.MissingCallee,
    };
    try std.testing.expect(again.fn_token == reference.fn_token);
    try std.testing.expect(TypeResolver.ActualTypeID.eql(again.actual_type, reference.actual_type));
}

test "a copied vector payload exposes its resolved scalar element type" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-vector-payload.zig",
        \\fn observe(value: @Vector(4, u64)) void { _ = value; }
    );
    defer resolver.deinit();
    const value = try testIdentifier(&resolver.handle.document.tree, "value");
    const vector = (try resolver.resolutionFrame().typeOfNode(value)).?;
    const element = resolver.childType(vector) orelse return error.MissingVectorElement;
    try std.testing.expectEqual(@as(u16, 64), (try resolver.intInfoOfType(element)).?.bits);
}

test "error-union child queries retain the allocated slice payload" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-error-union-child.zig",
        \\const std = @import("std");
        \\fn allocate(gpa: std.mem.Allocator) ![]u8 {
        \\    return gpa.alloc(u8, 1);
        \\}
        \\fn use(gpa: std.mem.Allocator) void { _ = allocate(gpa); }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const call = try testNthCallNamed(tree, "allocate", 0);
    const frame = resolver.resolutionFrame();
    const result = (try frame.typeOfNode(call)) orelse return error.MissingResultType;
    try std.testing.expectEqual(@as(?std.builtin.TypeId, .error_union), resolver.typeTag(result));
    const payload = resolver.childType(result) orelse return error.MissingErrorPayload;
    try std.testing.expectEqual(@as(?std.builtin.TypeId, .pointer), resolver.typeTag(payload));
    try std.testing.expectEqual(@as(?std.builtin.Type.Pointer.Size, .slice), resolver.pointerSize(payload));
    const element = resolver.childType(payload) orelse return error.MissingSliceElement;
    try std.testing.expectEqual(@as(?u16, 8), (try resolver.intInfoOfType(element)).?.bits);
}

test "comptime boolean call bindings keep branch decisions query-local" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-boolean-query-binding.zig",
        \\fn choose(comptime enabled: bool) void { _ = enabled; }
        \\fn observe() void { choose(true); choose(false); }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const yes = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "choose", 0))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const no = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "choose", 1))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const formal = try testIdentifier(tree, "enabled");
    try std.testing.expectEqual(@as(?bool, true), try resolver.frameForFunction(yes).boolValueOfNode(formal));
    try std.testing.expectEqual(@as(?bool, false), try resolver.frameForFunction(no).boolValueOfNode(formal));
    try std.testing.expectEqual(@as(?bool, true), try resolver.frameForFunction(yes).boolValueOfNode(formal));
    try std.testing.expect(!yes.actual_type.eql(no.actual_type));
}
test "returned callable values retain their declarations and factory bindings" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-returned-callable.zig",
        \\fn makeEql(comptime K: type, comptime Context: type) fn(Context, K, K) bool {
        \\    return struct {
        \\        fn eql(ctx: Context, a: K, b: K) bool {
        \\            _ = ctx;
        \\            return a == b;
        \\        }
        \\    }.eql;
        \\}
        \\fn AutoContext(comptime K: type) type {
        \\    return struct {
        \\        pub const eql = makeEql(K, @This());
        \\    };
        \\}
        \\fn invoke(context: anytype, value: anytype) bool {
        \\    return context.eql(undefined, value, value);
        \\}
        \\fn invokeImplicit(context: anytype, value: anytype) bool {
        \\    return context.eql(value, value);
        \\}
        \\fn useImplicitWide() bool { return invokeImplicit(AutoContext(u64){}, @as(u64, 1)); }
        \\fn useImplicitNarrow() bool { return invokeImplicit(AutoContext(u8){}, @as(u8, 1)); }
        \\fn useWide() bool { return invoke(AutoContext(u64){}, @as(u64, 1)); }
        \\fn useNarrow() bool { return invoke(AutoContext(u8){}, @as(u8, 1)); }
        \\fn dynamic(callback: *const fn(u64) bool, value: u64) bool {
        \\    return callback(value);
        \\}
        \\fn nonCallable(value: u64) void { _ = value(1); }
        \\fn chooseDifferent(flag: bool) fn(u64) bool {
        \\    if (flag) {
        \\        return struct {
        \\            fn left(value: u64) bool { return true; }
        \\        }.left;
        \\    }
        \\    return struct {
        \\        fn right(value: u64) bool { return false; }
        \\    }.right;
        \\}
        \\fn ambiguous(flag: bool, value: u64) bool {
        \\    const callback = chooseDifferent(flag);
        \\    return callback(value);
        \\}
        \\fn makeSameArity(comptime T: type, comptime flag: bool) fn(T, T) bool {
        \\    _ = flag;
        \\    return struct {
        \\        fn same(a: T, b: T) bool { return a == b; }
        \\    }.same;
        \\}
        \\fn useSameArity(value: u64) bool {
        \\    const callback = makeSameArity(u64, true);
        \\    return callback(value, value);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;

    const wide = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "invoke", 0),
    )) {
        .function => |reference| reference,
        else => return error.MissingWideFactoryFrame,
    };
    const narrow = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "invoke", 1),
    )) {
        .function => |reference| reference,
        else => return error.MissingNarrowFactoryFrame,
    };
    const callback_call = try testNthCallNamed(tree, "eql", 0);
    const wide_callback = switch (try resolver.frameForFunction(wide).functionReferenceOfCall(
        callback_call,
    )) {
        .function => |reference| reference,
        else => return error.MissingWideReturnedCallable,
    };
    const narrow_callback = switch (try resolver.frameForFunction(narrow).functionReferenceOfCall(
        callback_call,
    )) {
        .function => |reference| reference,
        else => return error.MissingNarrowReturnedCallable,
    };

    for ([_]TypeResolver.FunctionReference{ wide, narrow }, 0..) |caller, occurrence| {
        const context_type = caller.actual_type.data.function.parameters[0].type;
        if (context_type.data != .container) return error.MissingBoundContextType;
        const factory = switch (try resolver.frameForContainer(context_type.data.container).functionReferenceOfCall(
            try testNthCallNamed(tree, "makeEql", 0),
        )) {
            .function => |reference| reference,
            else => return error.MissingCanonicalFactory,
        };
        const actual_factory = try testActualFunction(factory);
        if (actual_factory.container_type.data != .container) return error.MissingFactoryOwner;
        const owner = actual_factory.container_type.data.container;
        try std.testing.expect(owner.scope_handle.scope == .root);
        const actual_context = owner.bound_params.get(.{
            .token = actual_factory.parameters[1].name_token.?,
            .handle = factory.handle,
        }) orelse return error.MissingFactoryContextBinding;
        try std.testing.expect(context_type.eql(actual_context));
        const actual_key = owner.bound_params.get(.{
            .token = actual_factory.parameters[0].name_token.?,
            .handle = factory.handle,
        }) orelse return error.MissingFactoryKeyBinding;
        try std.testing.expectEqual(
            @as(?u16, if (occurrence == 0) 64 else 8),
            try testUnsignedBitsOf(&resolver, actual_key),
        );
    }
    try std.testing.expect(wide_callback.handle.eql(resolver.handle));
    try std.testing.expect(wide_callback.fn_token == narrow_callback.fn_token);
    try std.testing.expect(!TypeResolver.ActualTypeID.eql(
        wide_callback.actual_type,
        narrow_callback.actual_type,
    ));
    const wide_function = try testActualFunction(wide_callback);
    const narrow_function = try testActualFunction(narrow_callback);
    try std.testing.expectEqualStrings("eql", wide_function.name.?);
    try std.testing.expectEqual(
        @as(?u16, 64),
        try testUnsignedBitsOf(&resolver, wide_function.parameters[1].type),
    );
    try std.testing.expectEqual(
        @as(?u16, 8),
        try testUnsignedBitsOf(&resolver, narrow_function.parameters[1].type),
    );

    const implicit_call = try testNthCallNamed(tree, "eql", 1);
    for (0..2) |occurrence| {
        const invoke = switch (try resolver.functionReferenceOfCall(
            try testNthCallNamed(tree, "invokeImplicit", occurrence),
        )) {
            .function => |reference| reference,
            else => return error.MissingImplicitFactoryFrame,
        };
        const frame = resolver.frameForFunction(invoke);
        const callback = switch (try frame.functionReferenceOfCall(implicit_call)) {
            .function => |reference| reference,
            else => return error.MissingImplicitReturnedCallable,
        };
        try std.testing.expectEqualStrings("eql", (try testActualFunction(callback)).name.?);
        try std.testing.expectEqual(
            @as(?u16, if (occurrence == 0) 64 else 8),
            try testUnsignedBitsOf(&resolver, (try testActualFunction(callback)).parameters[1].type),
        );
        var arguments_buffer: [2]Ast.Node.Index = undefined;
        const arguments = (try frame.callArgumentsOf(&arguments_buffer, implicit_call)) orelse
            return error.MissingImplicitReceiver;
        try std.testing.expect(arguments.receiver != null);
    }

    const same_factory = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "makeSameArity", 0),
    )) {
        .function => |reference| reference,
        else => return error.MissingSameArityFactory,
    };
    const same_callback = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "callback", 2),
    )) {
        .function => |reference| reference,
        else => return error.MissingSameArityReturnedCallable,
    };
    try std.testing.expect(same_factory.fn_token != same_callback.fn_token);
    try std.testing.expectEqualStrings("same", (try testActualFunction(same_callback)).name.?);
    const non_callable_call = try testNthCallNamed(tree, "value", 0);
    switch (try resolver.functionReferenceOfCall(non_callable_call)) {
        .not_callable => {},
        else => return error.KnownValueMustRemainNotCallable,
    }
    switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "callback", 0))) {
        .unknown => {},
        else => return error.RuntimeFunctionPointerMustRemainUnknown,
    }
    switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "callback", 1))) {
        .unknown => {},
        else => return error.DifferentReturnedValuesMustRemainUnknown,
    }
}
test "callable resolution preserves direct receiver and namespace bindings" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-direct-callable-bindings.zig",
        \\const std = @import("std");
        \\const Cell = struct {
        \\    value: u32,
        \\    fn make(default: u32) Cell { return .{ .value = default }; }
        \\    fn setValue(self: *Cell, next: u32) void { self.value = next; }
        \\};
        \\const Alias = Cell;
        \\fn throughAlias(seed: u32) Cell { return Alias.make(seed); }
        \\fn throughContainer(seed: u32) Cell { return Cell.make(seed); }
        \\fn throughReceiver(box: *Cell, next: u32) void { box.setValue(next); }
        \\fn throughQualifiedReceiver(box: *Cell, next: u32) void {
        \\    Alias.setValue(box, next);
        \\}
        \\const Namespace = struct {
        \\    fn add(value: u32) u32 { return value + 1; }
        \\};
        \\const NamespaceAlias = Namespace;
        \\fn throughNamespaceAlias(value: u32) u32 { return NamespaceAlias.add(value); }
        \\fn direct(value: u32) u32 { return value; }
        \\const FunctionAlias = direct;
        \\fn throughConstAlias(value: u32) u32 { return FunctionAlias(value); }
        \\fn sizeOwn(map: *std.AutoHashMap(u64, u64)) usize { return map.count(); }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;

    const alias_make = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "make", 0))) {
        .function => |reference| reference,
        else => return error.MissingAliasFactory,
    };
    const container_make = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "make", 1))) {
        .function => |reference| reference,
        else => return error.MissingContainerFactory,
    };
    try std.testing.expect(alias_make.fn_token == container_make.fn_token);
    try std.testing.expect(alias_make.handle.eql(container_make.handle));

    const implicit_receiver = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "setValue", 0))) {
        .function => |reference| reference,
        else => return error.MissingImplicitReceiverCall,
    };
    const explicit_receiver = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "setValue", 1))) {
        .function => |reference| reference,
        else => return error.MissingExplicitReceiverCall,
    };
    try std.testing.expect(implicit_receiver.fn_token == explicit_receiver.fn_token);
    try std.testing.expectEqual(
        @as(usize, 2),
        (try testActualFunction(implicit_receiver)).parameters.len,
    );
    try std.testing.expectEqual(
        @as(usize, 2),
        (try testActualFunction(explicit_receiver)).parameters.len,
    );
    try std.testing.expectEqualStrings("Cell", try testReceiverContainerName(&resolver, implicit_receiver));
    try std.testing.expectEqualStrings("Cell", try testReceiverContainerName(&resolver, explicit_receiver));

    const namespace_call = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "add", 0),
    )) {
        .function => |reference| reference,
        else => return error.MissingNamespaceAliasCall,
    };
    try std.testing.expectEqualStrings("add", (try testActualFunction(namespace_call)).name.?);

    const const_alias_call = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "FunctionAlias", 0),
    )) {
        .function => |reference| reference,
        else => return error.MissingImmutableFunctionAlias,
    };
    try std.testing.expectEqualStrings("direct", (try testActualFunction(const_alias_call)).name.?);

    const sdk_call = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "count", 0),
    )) {
        .function => |reference| reference,
        else => return error.MissingSdkReceiverCall,
    };
    try std.testing.expect(!sdk_call.handle.eql(resolver.handle));
}

test "bodyless factories do not authenticate their return signatures" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-bodyless-callable-factory.zig",
        \\extern fn makeCallback() *const fn(u8) bool;
        \\fn invoke(value: u8) bool {
        \\    const callback = makeCallback();
        \\    return callback(value);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const factory = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "makeCallback", 0),
    )) {
        .function => |reference| reference,
        else => return error.MissingBodylessFactory,
    };
    try std.testing.expectEqualStrings("makeCallback", (try testActualFunction(factory)).name.?);
    switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "callback", 0))) {
        .unknown => {},
        else => return error.BodylessFactoryMustNotAuthenticateReturnSignature,
    }
}

test "named variadic prototypes retain identity without fixed argument bindings" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-variadic-callable.zig",
        \\extern fn variadic(first: u8, ...) void;
        \\const VariadicAlias = variadic;
        \\fn invoke() void { VariadicAlias(1, 2); }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const call_node = try testNthCallNamed(tree, "VariadicAlias", 0);
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, call_node).?;
    const reference = switch (try resolver.functionReference(call.ast.fn_expr)) {
        .function => |reference| reference,
        else => return error.MissingVariadicDeclaration,
    };
    const function = try testActualFunction(reference);
    try std.testing.expectEqualStrings("variadic", function.name.?);
    try std.testing.expect(function.has_varargs);
    try std.testing.expectEqual(@as(usize, 1), function.parameters.len);
    try std.testing.expect(reference.handle.eql(resolver.handle));
    switch (try resolver.functionReferenceOfCall(call_node)) {
        .unknown => {},
        else => return error.VariadicArgumentsMustRemainUnbound,
    }
}

test "canonical receiver contexts preserve generic declaration literal arguments" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-canonical-receiver-context.zig",
        \\const Alignment = enum {
        \\    natural,
        \\    fn of(comptime T: type) Alignment { _ = T; return .natural; }
        \\};
        \\const Allocator = struct {
        \\    const Self = @This();
        \\    fn create(self: Self, comptime T: type) void {
        \\        self.useAlignment(.of(T));
        \\    }
        \\    fn useAlignment(self: Self, alignment: Alignment) void {
        \\        _ = self;
        \\        _ = alignment;
        \\    }
        \\};
        \\fn use(allocator: Allocator) void {
        \\    allocator.create(u8);
        \\    allocator.create(u64);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var literal_call: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node).?;
        if (tree.nodeTag(call.ast.fn_expr) == .enum_literal) literal_call = node;
    }
    const node = literal_call orelse return error.MissingDeclarationLiteral;
    var actuals: [2]TypeResolver.FunctionReference = undefined;
    for (&actuals, 0..) |*actual, index| {
        const create = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "create", index))) {
            .function => |reference| reference,
            else => return error.MissingGenericReceiver,
        };
        const frame = resolver.frameForFunction(create);
        actual.* = switch (try frame.functionReferenceOfCall(node)) {
            .function => |reference| reference,
            else => return error.MissingContextualDeclaration,
        };
        try std.testing.expectEqualStrings("of", (try testActualFunction(actual.*)).name.?);
    }
    try std.testing.expectEqual(actuals[0].fn_token, actuals[1].fn_token);
    try std.testing.expect(!actuals[0].actual_type.eql(actuals[1].actual_type));
}

test "contextual declaration calls authenticate their expected owner" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-contextual-callable-owner.zig",
        \\const Query = struct {
        \\    fn submit(value: *u8) Query { _ = value; return .{}; }
        \\};
        \\const Other = struct {
        \\    fn submit(value: *u8) Other { _ = value; return .{}; }
        \\};
        \\fn add(query: Query) void { _ = query; }
        \\fn invoke(value: *u8) void {
        \\    add(.submit(value));
        \\    add(Query.submit(value));
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const direct = switch (try resolver.functionReferenceOfCall(
        try testNthCallNamed(tree, "submit", 0),
    )) {
        .function => |reference| reference,
        else => return error.MissingDirectDeclaration,
    };
    var found = false;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = tree.fullCall(buffer[0..1], node).?;
        if (tree.nodeTag(call.ast.fn_expr) != .enum_literal) continue;
        const reached = switch (try resolver.functionReferenceOfCall(node)) {
            .function => |reference| reference,
            else => return error.MissingContextualDeclaration,
        };
        try std.testing.expect(reached.handle.eql(direct.handle));
        try std.testing.expectEqual(direct.fn_token, reached.fn_token);
        const arguments = (try resolver.callArgumentsOf(&buffer, node)).?;
        try std.testing.expect(arguments.receiver == null);
        try std.testing.expectEqual(@as(usize, 1), arguments.arguments.len);
        try std.testing.expectEqual(
            call.ast.params[0],
            (try resolver.callArgumentIn(&buffer, node, 0)).?,
        );
        found = true;
    }
    try std.testing.expect(found);
}

test "call intrinsic shares authentic generic identity and explicit argument mapping" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-call-intrinsic-operands.zig",
        \\const Owner = struct {
        \\    fn update(comptime T: type, value: *T) void { value.* = 0; }
        \\};
        \\fn run(value: *u8, callback: *const fn (*u8) void, args: struct { *u8 }) void {
        \\    @call(.always_inline, Owner.update, .{u8, value});
        \\    @call(.auto, callback, .{value});
        \\    @call(.auto, callback, args);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .builtin_call, .builtin_call_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@call")) continue;
        const operands = tree.extraDataSlice(tree.nodeData(node).extra_range, Ast.Node.Index);
        if (tree.nodeTag(operands[1]) == .field_access) {
            const reference = switch (try resolver.functionReferenceOfCall(node)) {
                .function => |reference| reference,
                else => return error.MissingIntrinsicDeclaration,
            };
            try std.testing.expectEqualStrings("update", (try testActualFunction(reference)).name.?);
            var buffer: [2]Ast.Node.Index = undefined;
            const arguments = (try resolver.callArgumentsOf(&buffer, node)) orelse return error.MissingIntrinsicArguments;
            try std.testing.expect(arguments.receiver == null);
            try std.testing.expectEqual(@as(usize, 2), arguments.arguments.len);
            try std.testing.expectEqualStrings("value", tree.tokenSlice(tree.nodeMainToken(
                (try resolver.callArgumentIn(&buffer, node, 1)).?,
            )));
        } else {
            try std.testing.expect((try resolver.functionReferenceOfCall(node)) == .unknown);
        }
        seen += 1;
    }
    try std.testing.expectEqual(@as(usize, 3), seen);
}

test "integer destination queries retain scalar contexts and stop at unrelated operands" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-integer-destination-context.zig",
        \\fn take(value: u16) void { _ = value; }
        \\fn wide(value: u64) void { _ = value; }
        \\fn scalar(value: u64, floating: f64) u32 {
        \\    _ = @as(u8, @intCast(value));
        \\    _ = @as(u64, @intCast(value));
        \\    take(@intCast(value));
        \\    wide(@intCast(value));
        \\    var narrow: u16 = 0;
        \\    narrow += (@intCast(value));
        \\    narrow -%= @intCast(value);
        \\    narrow *|= @intCast(value);
        \\    narrow &= @intCast(value);
        \\    narrow *= @intCast(value);
        \\    narrow /= @intCast(value);
        \\    narrow %= @intCast(value);
        \\    narrow -= @intCast(value);
        \\    narrow |= @intCast(value);
        \\    narrow ^= @intCast(value);
        \\    narrow *%= @intCast(value);
        \\    narrow +%= @intCast(value);
        \\    narrow +|= @intCast(value);
        \\    narrow -|= @intCast(value);
        \\    narrow <<= @intCast(value);
        \\    narrow <<|= @intCast(value);
        \\    narrow >>= @intCast(value);
        \\    take(@as(u64, @intCast(value)));
        \\    take(missing(@intCast(value)));
        \\    take(.{ .field = @intCast(value) });
        \\    return @intFromFloat(floating);
        \\}
    );
    defer resolver.deinit();
    const expected = [_]?u16{ 8, 64, 16, 64 } ++ ([_]?u16{16} ** 14) ++
        [_]?u16{ null, null, null, 64, null, null, 32 };
    const tree = &resolver.handle.document.tree;
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .builtin_call_two and tag != .builtin_call_two_comma) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const name = tree.tokenSlice(tree.nodeMainToken(node));
        if (!std.mem.eql(u8, name, "@intCast") and !std.mem.eql(u8, name, "@intFromFloat")) continue;
        try std.testing.expect(seen < expected.len);
        const info = try resolver.contextIntInfo(node);
        try std.testing.expectEqual(expected[seen], if (info) |integer| @as(?u16, integer.bits) else null);
        if (info) |integer| try std.testing.expect(!integer.signed);
        seen += 1;
    }
    try std.testing.expectEqual(expected.len, seen);
}

test "integer destination queries unwrap optional and error-union payloads only" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-wrapped-integer-destination.zig",
        \\fn optional(value: f64) ?u64 { return @intFromFloat(value); }
        \\fn fallible(value: f64) error{Bad}!i16 { return @intFromFloat(value); }
        \\fn both(value: u64) error{Bad}!?u8 { return @intCast(value); }
        \\fn explicit(value: u64) void { _ = @as(?u16, @intCast(value)); }
        \\fn pointer(value: u64) *u8 { return @intCast(value); }
        \\fn array(value: u64) [1]u8 { return @intCast(value); }
    );
    defer resolver.deinit();
    const expected = [_]?TypeResolver.IntInfo{
        .{ .signed = false, .bits = 64 },
        .{ .signed = true, .bits = 16 },
        .{ .signed = false, .bits = 8 },
        .{ .signed = false, .bits = 16 },
        null,
        null,
    };
    const tree = &resolver.handle.document.tree;
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .builtin_call_two and tag != .builtin_call_two_comma) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const name = tree.tokenSlice(tree.nodeMainToken(node));
        if (!std.mem.eql(u8, name, "@intCast") and !std.mem.eql(u8, name, "@intFromFloat")) continue;
        try std.testing.expect(seen < expected.len);
        try std.testing.expectEqual(expected[seen], try resolver.contextIntInfo(node));
        seen += 1;
    }
    try std.testing.expectEqual(expected.len, seen);
}

test "integer destination queries follow nested struct and union payloads in calls and returns" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-aggregate-integer-destination.zig",
        \\const Payload = struct { narrow: u8, wide: u64 };
        \\const Choice = union(enum) { payload: Payload, signed: i16 };
        \\const Outer = struct { choice: Choice };
        \\fn take(value: Outer) void { _ = value; }
        \\fn calls(value: u64) void {
        \\    take(.{ .choice = .{ .payload = .{
        \\        .narrow = @intCast(value), .wide = @intCast(value),
        \\    } } });
        \\    take(.{ .choice = .{ .signed = @intCast(value) } });
        \\}
        \\fn returned(value: u64) Outer {
        \\    return .{ .choice = .{ .payload = .{
        \\        .narrow = @intCast(value), .wide = @intCast(value),
        \\    } } };
        \\}
        \\fn unknown(value: u64) Missing {
        \\    return .{ .choice = .{ .payload = .{ .narrow = @intCast(value) } } };
        \\}
    );
    defer resolver.deinit();
    const expected = [_]?TypeResolver.IntInfo{
        .{ .signed = false, .bits = 8 },
        .{ .signed = false, .bits = 64 },
        .{ .signed = true, .bits = 16 },
        .{ .signed = false, .bits = 8 },
        .{ .signed = false, .bits = 64 },
        null,
    };
    const tree = &resolver.handle.document.tree;
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .builtin_call_two and tag != .builtin_call_two_comma) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@intCast")) continue;
        try std.testing.expect(seen < expected.len);
        try std.testing.expectEqual(expected[seen], try resolver.contextIntInfo(node));
        seen += 1;
    }
    try std.testing.expectEqual(expected.len, seen);
}

test "integer destination queries retain imported and generic concrete parameter types" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "destinations.zig", .data =
        \\pub const Payload = struct { small: u8, large: u64 };
        \\pub fn take(value: Payload) void { _ = value; }
        \\pub fn generic(comptime T: type, value: T) void { _ = value; }
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
        \\const imported = @import("destinations.zig");
        \\fn Box(comptime T: type) type { return struct { value: T }; }
        \\fn takeBox(comptime T: type, value: Box(T)) void { _ = value; }
        \\fn use(value: u64, floating: f64) void {
        \\    imported.take(.{ .small = @intCast(value), .large = @intCast(value) });
        \\    imported.generic(u8, @intFromFloat(floating));
        \\    imported.generic(u64, @intFromFloat(floating));
        \\    takeBox(u8, .{ .value = @intCast(value) });
        \\    takeBox(u64, .{ .value = @intCast(value) });
        \\}
        \\fn unbound(comptime T: type, value: u64) T { return @intCast(value); }
    );
    defer resolver.deinit();
    const expected = [_]?u16{ 8, 64, 8, 64, 8, 64, null };
    const tree = &resolver.handle.document.tree;
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .builtin_call_two and tag != .builtin_call_two_comma) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const name = tree.tokenSlice(tree.nodeMainToken(node));
        if (!std.mem.eql(u8, name, "@intCast") and !std.mem.eql(u8, name, "@intFromFloat")) continue;
        try std.testing.expect(seen < expected.len);
        const info = try resolver.contextIntInfo(node);
        try std.testing.expectEqual(expected[seen], if (info) |integer| @as(?u16, integer.bits) else null);
        seen += 1;
    }
    try std.testing.expectEqual(expected.len, seen);
}

test "float conversion destination follows resolved struct initializer fields" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-float-field-context.zig",
        \\const Pipeline = extern struct { bias: f32 };
        \\const Scratch = struct { rasterization: Pipeline = .{ .bias = 0 } };
        \\fn depthBias(value: i32) i32 { return value; }
        \\fn make(value: i32) Pipeline {
        \\    return .{ .bias = @floatFromInt(depthBias(value)) };
        \\}
        \\fn fill(scratch: *Scratch, value: i32) void {
        \\    scratch.rasterization = .{ .bias = @floatFromInt(depthBias(value)) };
        \\}
        \\fn unknown(value: i32) Missing {
        \\    return .{ .bias = @floatFromInt(value) };
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .builtin_call_two and tag != .builtin_call_two_comma) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@floatFromInt")) continue;
        try std.testing.expectEqual(if (seen < 2) @as(?u16, 32) else null, try resolver.resolutionFrame().floatBits(node));
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, node).?;
        const source = (try resolver.intInfo(params[0])) orelse return error.MissingSourceType;
        try std.testing.expect(source.signed);
        try std.testing.expectEqual(@as(u16, 32), source.bits);
        seen += 1;
    }
    try std.testing.expectEqual(@as(usize, 3), seen);
}

test "generic allocator metadata retains its bounded integer field type" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-generic-index-bound.zig",
        \\fn Allocator(comptime T: type) type {
        \\    return struct {
        \\        const Node = struct { index: u16 };
        \\        fn nodeFromObject(object: *T) *Node { _ = object; return undefined; }
        \\        fn offsetFrom(node: *Node, offset: isize) *Node { _ = offset; return node; }
        \\        fn deallocate(object: *T) void {
        \\            const node = nodeFromObject(object);
        \\            _ = offsetFrom(node, -@as(isize, @intCast(node.index)));
        \\        }
        \\    };
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const node = try testFieldAccess(tree, "node");
    try std.testing.expectEqual(TypeResolver.IntInfo{ .signed = false, .bits = 16 }, (try resolver.intInfo(node)).?);
}

test "imported generic iterator locals retain their method receiver identity" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "container.zig", .data =
        \\pub fn Collection(comptime T: type) type {
        \\    return struct {
        \\        const Self = @This();
        \\        pub const Cursor = CursorType(*Self, *T);
        \\        fn CursorType(comptime Owner: type, comptime Element: type) type {
        \\            return struct {
        \\                owner: Owner,
        \\                element: Element,
        \\                index: usize,
        \\                pub fn seek(cursor: *@This(), index: usize) void { cursor.index = index; }
        \\                pub fn wrong(cursor: *Self, index: usize) void { _ = cursor; _ = index; }
        \\            };
        \\        }
        \\        pub fn cursor(self: *Self, index: usize) Cursor {
        \\            var result: Cursor = undefined;
        \\            result.owner = self;
        \\            result.seek(index);
        \\            result.wrong(index);
        \\            var inferred = Cursor{ .owner = self, .element = undefined, .index = undefined };
        \\            inferred.seek(index);
        \\            return result;
        \\        }
        \\    };
        \\}
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
        \\const Collection = @import("container.zig").Collection;
        \\fn use(wide: *Collection(u64), narrow: *Collection(u8)) void {
        \\    _ = wide.cursor(1);
        \\    _ = narrow.cursor(2);
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var references: [2]TypeResolver.FunctionReference = undefined;
    for ([_]usize{ 0, 1, 0 }) |occurrence| {
        const factory = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "cursor", occurrence))) {
            .function => |reference| reference,
            else => return error.MissingCursorFactory,
        };
        const frame = resolver.frameForFunction(factory);
        const seek = switch (try frame.functionReferenceOfCall(try testNthCallNamed(factory.tree, "seek", 0))) {
            .function => |reference| reference,
            else => return error.MissingCursorMethod,
        };
        try std.testing.expect(seek.handle.eql(factory.handle));
        try std.testing.expectEqualStrings("seek", seek.actual_type.data.function.name.?);
        const declaration = try testFunctionDeclaration(seek);
        try std.testing.expectEqual(seek.fn_token, seek.tree.nodeMainToken(declaration));
        try std.testing.expectEqual(TypeResolver.FunctionResolution.unknown, try frame.functionReferenceOfCall(try testNthCallNamed(factory.tree, "wrong", 0)));
        const inferred = switch (try frame.functionReferenceOfCall(try testNthCallNamed(factory.tree, "seek", 1))) {
            .function => |reference| reference,
            else => return error.MissingInferredCursorMethod,
        };
        try std.testing.expect(seek.actual_type.eql(inferred.actual_type));
        references[occurrence] = seek;
    }
    try std.testing.expectEqual(references[0].fn_token, references[1].fn_token);
    try std.testing.expect(!references[0].actual_type.eql(references[1].actual_type));
}

test "framed enclosing functions skip type prototypes and retain nested ownership" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-enclosing-function-scope.zig",
        \\var outside: u8 = 0;
        \\fn outer() void {
        \\    var local: u8 = 0;
        \\    const Callback = fn (@TypeOf(local)) void;
        \\    const Nested = struct {
        \\        fn inner() void {
        \\            var inner_local: u8 = 0;
        \\            _ = &inner_local;
        \\        }
        \\    };
        \\    _ = &local;
        \\    _ = Callback;
        \\    Nested.inner();
        \\}
        \\pub fn run() void { outer(); }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var outer: ?Ast.Node.Index = null;
    var inner: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .fn_decl) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const name = tree.tokenSlice(tree.nodeMainToken(node) + 1);
        if (std.mem.eql(u8, name, "outer")) outer = node;
        if (std.mem.eql(u8, name, "inner")) inner = node;
    }
    const frame = resolver.resolutionFrame();
    for (tree.tokens.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        const token: Ast.TokenIndex = @intCast(index);
        const name = tree.tokenSlice(token);
        if (std.mem.eql(u8, name, "local"))
            try std.testing.expectEqual(outer.?, (try frame.enclosingFunctionAt(token)).?);
        if (std.mem.eql(u8, name, "inner_local"))
            try std.testing.expectEqual(inner.?, (try frame.enclosingFunctionAt(token)).?);
        if (std.mem.eql(u8, name, "outside"))
            try std.testing.expect((try frame.enclosingFunctionAt(token)) == null);
    }
}
