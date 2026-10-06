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
pub const ModuleId = DocumentStore.ModuleId;
pub const ModuleRegistry = DocumentStore.ModuleRegistry;
pub const SourceDocument = DocumentStore.SourceDocument;
pub const ResolvedImport = DocumentStore.ResolvedImport;
/// What a membership walk reads.  A session answers it from the store's
/// shared `SourceDocument` parses; a standalone project cache answers it
/// from its own AST pool.  Re-exported so neither has to import the store.
pub const RelativeEdges = DocumentStore.RelativeEdges;
/// A document's identity in this store.  Re-exported so a caller can name
/// one — `moduleForDocument` and `uriFromImportStr` both take it — without
/// reaching past this facade into the store's own module tree.
pub const Uri = @import("uri.zig");
const Analyser = @import("analysis.zig");
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

    pub fn init(gpa: std.mem.Allocator, io: std.Io) !Toolchain {
        return .{ .gpa = gpa, .paths = try queryToolchain(gpa, io) };
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
        const paths = try queryToolchain(gpa, io);
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
    pub fn sourceHandle(self: *TypeContext, file_path: []const u8, module: ModuleId) !DocumentStore.Handle {
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
    /// Its arena is this resolver's own, which the aggregate below cannot
    /// hand to it directly: an arena names its allocator by the arena's own
    /// address, and this assignment copies one into `self`, so an allocator
    /// taken from the value on the right-hand side would go on naming a
    /// local that is gone before anything is allocated.  It is built against
    /// `gpa` instead and pointed at `self.arena` by the very next statement,
    /// which changes nothing in between: `Analyser.init` only copies what it
    /// is given — it allocates nothing and holds no allocation — and
    /// nothing that can fail runs between the two.
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
            .analyser = Analyser.init(gpa, gpa, &ctx.store, &ctx.ip, bound),
        };
        self.analyser.arena = self.arena.allocator();
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
            return self.resolver.analyser.resolveTypeOfNode(self.options(node));
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

        fn referenceOfValue(self: ResolutionFrame, value: ActualType) !FunctionResolution {
            const callable = (try self.resolver.analyser.resolveFuncProtoOfCallable(value)) orelse {
                const ty = (try self.resolver.normalizedType(value)) orelse return .unknown;
                const tag = self.resolver.typeTag(ty) orelse return .unknown;
                return switch (tag) {
                    .pointer, .optional, .error_union, .@"fn", .@"opaque" => .unknown,
                    else => .not_callable,
                };
            };
            if (callable.is_type_val) return .not_callable;
            return referenceOfCallable(callable);
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

        pub fn functionReference(self: ResolutionFrame, node: Ast.Node.Index) !FunctionResolution {
            return self.referenceOfValue((try self.resolveValueOfNode(node)) orelse return .unknown);
        }

        /// Preserve the actual call's formal anytype/comptime bindings in
        /// the reached function, rather than resolving only its spelling.
        pub fn functionReferenceOfCall(self: ResolutionFrame, node: Ast.Node.Index) !FunctionResolution {
            var buffer: [1]Ast.Node.Index = undefined;
            const call = self.handle.document.tree.fullCall(&buffer, node) orelse return .unknown;
            const reference = switch (try self.functionReference(call.ast.fn_expr)) {
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

        pub fn typeParameterReference(self: ResolutionFrame, node: Ast.Node.Index) !?TypeParameterReference {
            const value = (try self.resolveValueOfNode(node)) orelse return null;
            const parameter = switch (value.data) {
                .type_parameter => |reference| reference,
                else => return null,
            };
            return .{ .tree = &parameter.handle.document.tree, .token = parameter.token };
        }

        fn reachedCall(self: ResolutionFrame, buffer: *[1]Ast.Node.Index, node: Ast.Node.Index) !?ReachedCall {
            const call = self.handle.document.tree.fullCall(buffer, node) orelse return null;
            const value = (try self.resolveValueOfNode(call.ast.fn_expr)) orelse return null;
            const callable = (try self.resolver.analyser.resolveFuncProtoOfCallable(value)) orelse return null;
            return self.reachedCallable(call, callable);
        }

        fn reachedCallable(self: ResolutionFrame, call: Ast.full.Call, callable: ActualType) !?ReachedCall {
            if (callable.is_type_val or callable.data.function.has_varargs) return null;
            const receiver = try self.resolver.analyser.isInstanceCall(self.options(call.ast.fn_expr), call, callable);
            if (call.ast.params.len + @intFromBool(receiver) != callable.data.function.parameters.len) return null;
            return .{ .call = call, .receiver = receiver, .parameters = callable.data.function.parameters, .callable = callable };
        }

        pub fn callArgument(self: ResolutionFrame, node: Ast.Node.Index, parameter: usize) !?Ast.Node.Index {
            var buffer: [1]Ast.Node.Index = undefined;
            return self.callArgumentIn(&buffer, node, parameter);
        }

        pub fn callArgumentIn(self: ResolutionFrame, buffer: *[1]Ast.Node.Index, node: Ast.Node.Index, parameter: usize) !?Ast.Node.Index {
            const reached = (try self.reachedCall(buffer, node)) orelse return null;
            if (parameter >= reached.parameters.len) return null;
            if (reached.receiver and parameter == 0)
                return self.handle.document.tree.nodeData(reached.call.ast.fn_expr).node_and_token[0];
            return reached.call.ast.params[parameter - @intFromBool(reached.receiver)];
        }

        pub fn callArgumentsOf(self: ResolutionFrame, buffer: *[1]Ast.Node.Index, node: Ast.Node.Index) !?CallArguments {
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
            return self.resolver.intInfoOfType((try self.typeOfNode(node)) orelse return null);
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
        call: Ast.full.Call,
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
        buffer: *[1]Ast.Node.Index,
        node: Ast.Node.Index,
    ) !?ReachedCall {
        return self.resolutionFrame().reachedCall(buffer, node);
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
        return self.resolutionFrame().callArgumentIn(buffer, node, parameter);
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
        return self.resolutionFrame().callArgumentsOf(buffer, node);
    }

    /// The declared type of the parameter an ACTUAL argument is passed as
    /// at the declaration this call reaches, the receiver counting when the
    /// call is an instance call.  Null on exactly the calls `callArgument`
    /// answers null for — a variadic callee, an arity the declaration does
    /// not have, a callee this snapshot cannot name.
    fn argumentParameterType(self: *TypeResolver, node: Ast.Node.Index, argument: usize) !?Analyser.Type {
        var buffer: [1]Ast.Node.Index = undefined;
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

    /// The integer type `node` is COERCED to when it has no type of its own.
    ///
    /// A conversion such as `@intCast(x)` takes the type of the context it
    /// is written in, so a cast in argument position has to be read against
    /// the parameter it is passed as rather than against itself.  The
    /// innermost call that takes it as an argument is the one whose
    /// coercion applies: an outer call coerces the whole argument
    /// expression, and the inner one has already fixed this node's type.
    pub fn contextIntInfo(self: *TypeResolver, node: Ast.Node.Index) !?IntInfo {
        const tree = &self.handle.document.tree;
        const target_first = tree.firstToken(node);
        const target_last = tree.lastToken(node);
        const Found = struct { call: Ast.Node.Index, argument: usize, first: Ast.TokenIndex };
        var best: ?Found = null;
        var buffer: [1]Ast.Node.Index = undefined;
        for (tree.nodes.items(.tag), 0..) |tag, index| {
            switch (tag) {
                .call, .call_comma, .call_one, .call_one_comma => {},
                else => continue,
            }
            const candidate: Ast.Node.Index = @enumFromInt(index);
            const first = tree.firstToken(candidate);
            if (target_first < first or target_last > tree.lastToken(candidate)) continue;
            if (best) |previous| if (first <= previous.first) continue;
            const call = tree.fullCall(&buffer, candidate) orelse continue;
            for (call.ast.params, 0..) |argument, position| {
                if (target_first < tree.firstToken(argument)) continue;
                if (target_last > tree.lastToken(argument)) continue;
                best = .{ .call = candidate, .argument = position, .first = first };
                break;
            }
        }
        const found = best orelse return null;
        return self.argumentIntInfo(found.call, found.argument);
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

    /// Return one pointer, array, vector, or optional child of a resolved type value.
    /// The child borrows the original resolver; non-wrapper types answer null.
    pub fn childType(self: *TypeResolver, ty: ActualType) ?ActualType {
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
                    .vector_type => |info| info.child,
                    .optional_type => |info| info.payload_type,
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
        const path = try handle.document.uri.toFsPath(self.arena.allocator());
        const base = std.mem.trimEnd(u8, library, std.fs.path.sep_str);
        return path.len == base.len + suffix.len and
            std.mem.startsWith(u8, path, base) and std.mem.endsWith(u8, path, suffix);
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

/// `Cache.run` is written once and calls the context's own `read` and `write`, so
/// which body a resolution reaches is decided by the instantiation, not by the
/// declaration.  The same body type-checks for both contexts.
const GenericContextFixture =
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

/// The first call the body of the declaration this `fn` keyword names writes.
fn testFirstCallInBody(tree: *const Ast, fn_token: Ast.TokenIndex) !Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .fn_decl) continue;
        const declaration: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeMainToken(declaration) != fn_token) continue;
        const body = tree.nodeData(declaration).node_and_node[1];
        const first = tree.firstToken(body);
        const last = tree.lastToken(body);
        for (tree.nodes.items(.tag), 0..) |body_tag, body_index| {
            switch (body_tag) {
                .call, .call_comma, .call_one, .call_one_comma => {},
                else => continue,
            }
            const node: Ast.Node.Index = @enumFromInt(body_index);
            if (tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
            return node;
        }
        return error.TestUnexpectedResult;
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

/// The value inside an optional result a rule must see through.
fn testOptionalPayload(resolver: *TypeResolver, value: Analyser.Type) !Analyser.Type {
    const ty = (try resolver.normalizedType(value)) orelse return error.UnresolvedType;
    if ((resolver.typeTag(ty) orelse return error.UnresolvedType) != .optional) return error.NotAnOptionalType;
    return (try resolver.normalizedType(resolver.childType(ty) orelse return error.UnresolvedType)) orelse
        error.UnresolvedType;
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

test "an SDK map method answers with the key and result its instantiation binds" {
    const gpa = std.testing.allocator;
    var context: TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-sdk-map-instantiation.zig",
        \\const std = @import("std");
        \\fn observe(map: *std.AutoHashMap(u64, u64)) void {
        \\    _ = map.get(1);
        \\    _ = map.count();
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const get = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "get", 0))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };
    const count = switch (try resolver.functionReferenceOfCall(try testNthCallNamed(tree, "count", 0))) {
        .function => |reference| reference,
        else => return error.MissingCallee,
    };

    // The compiler's own methods, reached through the `AutoHashMap` alias
    // and the defaults it spells, in the document that declares them.
    try std.testing.expect(!get.handle.eql(resolver.handle));
    try std.testing.expect(try resolver.declaredInToolchainFile(get.handle, "/std/hash_map.zig"));
    try std.testing.expect(try resolver.declaredInToolchainFile(count.handle, "/std/hash_map.zig"));

    // The key the lookup takes is the `K` this map was instantiated with and
    // its result the `V`, so a rule reading the callee learns 64 bits on both
    // sides instead of a bare `K` and `V` it cannot use.
    const get_function = try testActualFunction(get);
    var key: ?Analyser.Type = null;
    for (get_function.parameters[1..]) |parameter| {
        if (std.mem.eql(u8, parameter.name orelse "", "key")) key = parameter.type;
    }
    try std.testing.expectEqual(@as(?u16, 64), try testUnsignedBitsOf(&resolver, key orelse return error.MissingKeyParameter));
    try std.testing.expectEqual(@as(?u16, 64), try testUnsignedBitsOf(
        &resolver,
        try testOptionalPayload(&resolver, get_function.return_value.*),
    ));
    // `count` answers with the table's own `Size`: an integer whose width is
    // the SDK's to choose, so only "a known unsigned integer" is asserted.
    const counted = (try resolver.intInfoOfType((try testActualFunction(count)).return_value.*)) orelse
        return error.MissingCountType;
    try std.testing.expect(!counted.signed);

    // One hop further, in the SDK's own document and carrying the same
    // instantiation: whatever this lookup calls is a `/std/hash_map.zig`
    // declaration, and not one this file can name.
    const inner = switch (try (resolver.frameForFunction(get)).functionReferenceOfCall(
        try testFirstCallInBody(get.tree, get.fn_token),
    )) {
        .function => |reference| reference,
        else => return error.MissingTransitiveCallee,
    };
    try std.testing.expect(inner.fn_token != get.fn_token);
    try std.testing.expect(!inner.handle.eql(resolver.handle));
    try std.testing.expect(try resolver.declaredInToolchainFile(inner.handle, "/std/hash_map.zig"));
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
