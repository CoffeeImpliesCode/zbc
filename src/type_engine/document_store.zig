//! A thread-safe container for all document related state like zig source files including `build.zig`.

const std = @import("std");
const builtin = @import("builtin");
const Uri = @import("uri.zig");
const analysis = @import("analysis.zig");
const offsets = @import("offsets.zig");
const log = std.log.scoped(.store);
const Ast = std.zig.Ast;
const BuildAssociatedConfig = @import("build_associated_config.zig");
pub const BuildConfig = @import("build_runner_shared.zig").BuildConfig;
const tracy = @import("tracy_stub.zig");
const DocumentScope = @import("document_scope.zig");
const DiagnosticsCollection = @import("diagnostics_collection.zig");
// `policy_mod`, not `source_policy`: this file's struct has a field by
// that name, and a container decl sharing it would shadow it here.
const policy_mod = @import("source_policy.zig");
const SourcePolicy = policy_mod.SourcePolicy;
const CanonicalPaths = policy_mod.CanonicalPaths;
const ParseFailure = policy_mod.ParseFailure;
const within = policy_mod.within;

const DocumentStore = @This();

io: std.Io,
allocator: std.mem.Allocator,
source_policy: SourcePolicy = .{},
canonical_paths: CanonicalPaths = .{},
source_aliases: Uri.ArrayHashMap(Uri) = .empty,
/// The failure the most recent lookup published.  Written and read under
/// `mutex`, so a caller always sees one coherent (cause, position) pair
/// and never one half of a newer snapshot with the other half of an older.
source_failure: ?anyerror = null,
parse_failure: ?ParseFailure = null,
/// Interned module identities.  Owned here; a `TypeContext` borrows it.
modules: *ModuleRegistry,
/// the DocumentStore assumes that `config` is not modified while calling one of its functions.
config: Config,
mutex: std.Io.Mutex = .init,
wait_group: if (supports_build_system) std.Io.Group else void = if (supports_build_system) .init else {},
documents: Uri.ArrayHashMap(*SourceDocument.Future) = .empty,
build_files: if (supports_build_system) Uri.ArrayHashMap(*BuildFile) else void = if (supports_build_system) .empty else {},
diagnostics_collection: *DiagnosticsCollection,
builds_in_progress: std.atomic.Value(i32) = .init(0),
/// Named-module wiring recovered from `build.zig` without executing it.  No
/// build runner is ever spawned: running a project's `build.zig` runs that
/// project's code, so the wiring is read instead of run and only where the
/// source policy already admits the target file.
named_modules: ?NamedModuleMap = null,

lsp_capabilities: struct {
    supports_work_done_progress: bool = false,
    supports_semantic_tokens_refresh: bool = false,
    supports_inlay_hints_refresh: bool = false,
} = .{},

/// One declared module instance: one importer's compilation environment.
///
/// A module's identity is the canonical root source file *together with*
/// the declaration that created it, interned by `ModuleRegistry` as one
/// identity key.  The root alone is not an identity: two `addModule`
/// calls may create the same root in two separate compilations and wire
/// its imports differently, and those are two modules that happen to
/// share a file.  Collapsing them would answer both from one import
/// table, which is the collision this type exists to prevent.
///
/// The `addModule` name is a label and never part of identity either: two
/// unrelated modules may both be called `"left"`.
///
/// `.unscoped` is the environment of a document whose compilation this
/// session has not proven.  It resolves relative imports, which are
/// environment-independent, and resolves a named import only when every
/// candidate module that could own it agrees on one root.
pub const ModuleId = enum(u32) { unscoped = 0, _ };

/// Session-owned interning of module identities.
///
/// An id is stable for the lifetime of the registry and is never reused,
/// so a `ModuleId`, or the `key` bytes an id names, stays meaningful for
/// as long as the session that owns the registry.  Ids never cross
/// registry address spaces: a `TypeContext` owns one registry, and a
/// `ProjectCache` attached to it borrows it rather than making its own.
///
/// `.unscoped` is not an entry: it names no build script and no root, so it
/// costs no allocation and cannot be read back out of the table.  The first
/// interned identity is id 1.
/// Each session is owned by one worker, so the registry needs no lock of
/// its own; the `DocumentStore` that borrows it does not publish module
/// ids from behind a different owner's lock either.
pub const ModuleRegistry = struct {
    gpa: std.mem.Allocator,
    /// Owns every interned key and display name as one block.
    arena: std.heap.ArenaAllocator,
    entries: std.ArrayListUnmanaged(Entry) = .empty,
    by_key: std.StringHashMapUnmanaged(ModuleId) = .empty,

    /// One interned module identity: the key it is filed under, and the
    /// `addModule` name a governing `build.zig` declared it with, when one
    /// was proven.  `.unscoped` is not an entry — it is the absence of a
    /// module, so it has no key and no label.
    const Entry = struct {
        key: []const u8,
        name: ?[]const u8,
    };

    pub fn init(gpa: std.mem.Allocator) ModuleRegistry {
        return .{ .gpa = gpa, .arena = .init(gpa) };
    }

    pub fn deinit(self: *ModuleRegistry) void {
        self.by_key.deinit(self.gpa);
        self.entries.deinit(self.gpa);
        self.arena.deinit();
        self.* = undefined;
    }

    /// Interns `key`, the identity of one declared module instance: its
    /// canonical root source file together with the declaration that
    /// created it.  Two declarations of one root intern to two ids.
    ///
    /// OOM-safe: every allocation that can fail happens before anything is
    /// published, and a failed intern leaves the table exactly as it was.
    pub fn intern(self: *ModuleRegistry, identity_key: []const u8) error{OutOfMemory}!ModuleId {
        if (identity_key.len == 0) return .unscoped;
        if (self.by_key.get(identity_key)) |existing| return existing;
        const gpa = self.arena.allocator();
        const owned = try gpa.dupe(u8, identity_key);
        errdefer gpa.free(owned);
        try self.entries.append(self.gpa, .{ .key = owned, .name = null });
        errdefer _ = self.entries.pop();
        const id: ModuleId = @enumFromInt(self.entries.items.len);
        try self.by_key.put(self.gpa, owned, id);
        return id;
    }

    /// The entry an id names, or null for `.unscoped` and for any id this
    /// registry never handed out.
    fn entry(self: *const ModuleRegistry, id: ModuleId) ?*Entry {
        if (id == .unscoped) return null;
        const index = @as(usize, @intFromEnum(id)) - 1;
        if (index >= self.entries.items.len) return null;
        return &self.entries.items[index];
    }

    /// Records the name a governing `build.zig` declares `id` under.
    /// The first proven name wins: a name is a diagnostic label, and a
    /// second one proves nothing the first did not.  The bytes are copied
    /// before the field is written, so a reader never sees a name whose
    /// storage does not exist yet.
    pub fn setName(self: *ModuleRegistry, id: ModuleId, display_name: []const u8) error{OutOfMemory}!void {
        const record = self.entry(id) orelse return;
        if (record.name != null or display_name.len == 0) return;
        const owned = try self.arena.allocator().dupe(u8, display_name);
        record.name = owned;
    }

    /// The declared build.zig name, when one was proven.
    pub fn name(self: *const ModuleRegistry, id: ModuleId) ?[]const u8 {
        const record = self.entry(id) orelse return null;
        return record.name;
    }

    /// The interned identity key: stable bytes, valid until `deinit`.
    pub fn key(self: *const ModuleRegistry, id: ModuleId) []const u8 {
        const record = self.entry(id) orelse return "";
        return record.key;
    }
};

/// What a membership walk reads: the relative-import edges of one document.
///
/// This is deliberately the smallest thing membership needs, so the walk
/// can run over any syntax pool without dragging a store, a type engine or
/// a toolchain query along with it.  A session answers it from the shared
/// `SourceDocument` parses it already owns; a standalone project cache
/// answers it from the AST it already holds.  Neither side parses twice and
/// neither needs to know the other exists.
pub const RelativeEdges = struct {
    ctx: *const anyopaque,
    /// Appends the policy-admitted RELATIVE import edges of
    /// `canonical_path` to `edges`.
    ///
    /// `arena` is owned by the walk and discarded when it finishes, so a
    /// pool may dupe into it or append bytes it already owns; either is
    /// correct and nothing is freed per document.  Borrowed bytes are
    /// preferred: the pool already holds them.
    ///
    /// Returns false when the document is not admitted or not readable.
    /// That is absent evidence, not a failure — a denied or missing relative
    /// target must never become a failure of the file under analysis.
    /// Only allocation failure and cancellation propagate.
    ///
    /// Named imports must not be appended here.  An alias says nothing about
    /// which module owns a document, and following one is exactly the wrong
    /// file answer this whole design exists to eliminate.
    read: *const fn (
        ctx: *const anyopaque,
        arena: std.mem.Allocator,
        canonical_path: []const u8,
        edges: *std.ArrayList([]const u8),
    ) (error{OutOfMemory} || std.Io.Cancelable)!bool,
};

/// How many documents one instance's reachability walk will visit before it
/// gives up.  A module rooted in a directory tree walks that tree once; this
/// bounds a pathological graph without bounding a normal project.
const max_membership_documents = 4096;

pub const supports_build_system = std.process.can_spawn;

pub const Config = struct {
    environ_map: *const std.process.Environ.Map,
    zig_exe_path: ?[]const u8,
    zig_lib_dir: ?std.Build.Cache.Directory,
    build_runner_path: ?[]const u8,
    builtin_path: ?[]const u8,
    global_cache_dir: ?std.Build.Cache.Directory,
    wasi_preopens: switch (builtin.os.tag) {
        .wasi => std.process.Preopens,
        else => void,
    },
};

/// Represents a `build.zig`
pub const BuildFile = struct {
    uri: Uri,
    /// this build file may have an explicitly specified path to builtin.zig
    builtin_uri: ?Uri = null,
    /// config options extracted from zls.build.json
    build_associated_config: ?std.json.Parsed(BuildAssociatedConfig) = null,
    impl: struct {
        mutex: std.Io.Mutex = .init,
        build_runner_state: BuildRunnerState = .idle,
        version: u32 = 0,
        /// contains information extracted from running build.zig with a custom build runner
        /// e.g. include paths & packages
        /// TODO this field should not be nullable, callsites should await the build config to be resolved
        /// and then continue instead of dealing with missing information.
        config: ?std.json.Parsed(BuildConfig) = null,
    } = .{},

    const BuildRunnerState = enum {
        idle,
        running,
        running_but_already_invalidated,
    };

    pub fn tryLockConfig(self: *BuildFile, io: std.Io) ?BuildConfig {
        self.impl.mutex.lockUncancelable(io);
        return if (self.impl.config) |cfg| cfg.value else {
            self.impl.mutex.unlock(io);
            return null;
        };
    }

    pub fn unlockConfig(self: *BuildFile, io: std.Io) void {
        self.impl.mutex.unlock(io);
    }

    /// Returns whether the `Uri` is a dependency of the given `BuildFile`.
    /// May return `.unknown` to indicate an inconclusive result because
    /// the required build config has not been resolved yet.
    ///
    /// **Thread safe** takes an exclusive lock
    fn isAssociatedWith(
        build_file: *BuildFile,
        uri: Uri,
        store: *DocumentStore,
    ) error{ Canceled, OutOfMemory, SourceExcluded }!union(enum) {
        unknown,
        no,
        /// Stores the `root_source_file`. Caller owns returned memory.
        yes: []const u8,
    } {
        const tracy_zone = tracy.trace(@src());
        defer tracy_zone.end();

        const allocator = store.allocator;
        const io = store.io;

        var arena_allocator: std.heap.ArenaAllocator = .init(allocator);
        defer arena_allocator.deinit();

        const arena = arena_allocator.allocator();

        var module_root_source_file_paths: std.ArrayList([]const u8) = .empty;

        {
            const build_config = build_file.tryLockConfig(io) orelse return .unknown;
            defer build_file.unlockConfig(io);

            const module_paths = build_config.modules.map.keys();

            try module_root_source_file_paths.ensureUnusedCapacity(arena, module_paths.len);
            for (module_paths) |module_path| {
                module_root_source_file_paths.appendAssumeCapacity(try arena.dupe(u8, module_path));
            }
        }

        var found_uris: Uri.ArrayHashMap(void) = .empty;

        var i: usize = 0;

        for (module_root_source_file_paths.items) |root_source_file| {
            try found_uris.put(arena, try .fromPath(arena, root_source_file), {});

            while (i < found_uris.count()) : (i += 1) {
                const source_uri = found_uris.keys()[i];
                if (uri.eql(source_uri)) {
                    return .{ .yes = try allocator.dupe(u8, root_source_file) };
                }
                if (isInStd(source_uri)) continue;

                // Reachability is by relative import, which every module
                // shares, so the walk needs no module of its own.
                const handle = store.getOrLoadHandle(source_uri, .unscoped) catch |err| switch (err) {
                    error.FileNotFound, error.NotDir => continue,
                    error.Canceled => return error.Canceled,
                    error.OutOfMemory => return error.OutOfMemory,
                    error.SourceExcluded => return error.SourceExcluded,
                } orelse continue;

                try found_uris.ensureUnusedCapacity(arena, handle.document.file_imports.len);
                for (handle.document.file_imports) |import_uri| found_uris.putAssumeCapacity(try import_uri.dupe(arena), {});
            }
        }

        return .no;
    }

    fn deinit(self: *BuildFile, allocator: std.mem.Allocator) void {
        self.uri.deinit(allocator);
        if (self.impl.config) |cfg| cfg.deinit();
        if (self.builtin_uri) |builtin_uri| builtin_uri.deinit(allocator);
        if (self.build_associated_config) |cfg| cfg.deinit();
    }
};

/// One canonical URI's immutable syntax snapshot: the text, the tree
/// parsed from it, the relative imports it names, and the environment
/// independent scope structure collected from that tree.
///
/// Everything here is provable without knowing which compilation the
/// document belongs to, so every module that imports the same physical
/// file shares exactly one of these: one URI is read and parsed once per
/// session, whatever the number of environments it is imported from.
/// Everything a semantic answer depends on lives in `Handle`, beside it.
pub const SourceDocument = struct {
    uri: Uri,
    tree: Ast,
    /// List of every file that has been `@Import`ed. Does not include imported modules.
    file_imports: []const Uri,
    /// `true` if the document has been directly opened by the client i.e. with `textDocument/didOpen`
    /// `false` indicates the document only exists because it is a dependency of another document
    /// or has been closed with `textDocument/didClose`.
    lsp_synced: bool,
    document_scope: Lazy(DocumentScope, DocumentStoreContext) = .unset,

    /// private field
    impl: struct {
        store: *DocumentStore,
        lock: std.Io.Mutex = .init,
        has_tree_and_source: bool,

        associated_build_file: AssociatedBuildFile.State = .init,
        associated_compilation_units: GetAssociatedCompilationUnitsResult = .unresolved,
    },

    pub fn getDocumentScope(self: *Handle) error{OutOfMemory}!*const DocumentScope {
        return try self.document_scope.get(self);
    }

    pub const AssociatedBuildFile = union(enum) {
        /// The SourceDocument has no associated build file (build.zig).
        none,
        /// The associated build file (build.zig) has not been resolved yet.
        unresolved,
        /// The associated build file (build.zig) has been successfully resolved.
        resolved: Resolved,

        pub const Resolved = struct {
            build_file: *BuildFile,
            root_source_file: []const u8,
        };

        const State = union(enum) {
            /// The initial state. The associated build file (build.zig) is resolved lazily.
            init,
            /// The associated build file (build.zig) has been requested but has not yet been resolved.
            unresolved: struct {
                /// The build files are ordered in decreasing priority.
                potential_build_files: []const *BuildFile,
                /// to avoid checking build files multiple times, a bitset stores whether or
                /// not the build file should be skipped because it has previously been
                /// found to be "unassociated" with the handle.
                has_been_checked: std.DynamicBitSetUnmanaged,
            },
            /// The SourceDocument has no associated build file (build.zig).
            none,
            /// The associated build file (build.zig) has been successfully resolved.
            resolved: Resolved,

            fn deinit(state: *State, allocator: std.mem.Allocator) void {
                switch (state.*) {
                    .init, .none => {},
                    .unresolved => |*unresolved| {
                        allocator.free(unresolved.potential_build_files);
                        unresolved.has_been_checked.deinit(allocator);
                    },
                    .resolved => |resolved| {
                        allocator.free(resolved.root_source_file);
                    },
                }
                state.* = undefined;
            }
        };
    };

    /// Returns the associated build file (build.zig) of the document.
    ///
    /// `DocumentStore.build_files` is guaranteed to contain this Uri.
    /// Uri memory managed by its build_file
    pub fn getAssociatedBuildFile(self: *SourceDocument, document_store: *DocumentStore) error{ Canceled, OutOfMemory, SourceExcluded }!AssociatedBuildFile {
        comptime std.debug.assert(supports_build_system);

        try self.impl.lock.lock(document_store.io);
        defer self.impl.lock.unlock(document_store.io);

        const unresolved = switch (self.impl.associated_build_file) {
            .init => blk: {
                const potential_build_files = try document_store.collectPotentialBuildFiles(self.uri);
                errdefer document_store.allocator.free(potential_build_files);

                if (potential_build_files.len == 0) {
                    self.impl.associated_build_file = .none;
                    return .none;
                }

                var has_been_checked: std.DynamicBitSetUnmanaged = try .initEmpty(document_store.allocator, potential_build_files.len);
                errdefer has_been_checked.deinit(document_store.allocator);

                self.impl.associated_build_file = .{ .unresolved = .{
                    .has_been_checked = has_been_checked,
                    .potential_build_files = potential_build_files,
                } };

                break :blk &self.impl.associated_build_file.unresolved;
            },
            .unresolved => |*unresolved| unresolved,
            .none => return .none,
            .resolved => |resolved| return .{ .resolved = resolved },
        };

        var has_missing_build_config = false;

        var it = unresolved.has_been_checked.iterator(.{
            .kind = .unset,
            .direction = .reverse,
        });
        while (it.next()) |i| {
            const build_file = unresolved.potential_build_files[i];
            switch (try build_file.isAssociatedWith(self.uri, document_store)) {
                .unknown => {
                    has_missing_build_config = true;
                    continue;
                },
                .no => {
                    // the build file should be skipped in future calls.
                    unresolved.has_been_checked.set(i);
                    continue;
                },
                .yes => |root_source_file| {
                    // log.debug("Resolved build file of '{s}' as '{s}' root={s}", .{ self.uri.raw, build_file.uri.raw, root_source_file });
                    errdefer comptime unreachable;
                    self.impl.associated_build_file.deinit(document_store.allocator);
                    self.impl.associated_build_file = .{
                        .resolved = .{
                            .build_file = build_file,
                            .root_source_file = root_source_file,
                        },
                    };
                    return .{ .resolved = self.impl.associated_build_file.resolved };
                },
            }
        }

        if (has_missing_build_config) {
            // when build configs are missing we keep the state at .unresolved so that
            // future calls will retry until all build config are resolved.
            // Then will have a conclusive result on whether or not there is a associated build file.
            return .unresolved;
        }

        self.impl.associated_build_file.deinit(document_store.allocator);
        self.impl.associated_build_file = .none;
        return .none;
    }

    pub const GetAssociatedCompilationUnitsResult = union(enum) {
        /// The SourceDocument has no associated compilation unit.
        none,
        /// The associated compilation unit has not been resolved yet.
        unresolved,
        /// The SourceDocument has been successfully resolved to a list of root module.
        resolved: []const []const u8,

        fn deinit(result: *GetAssociatedCompilationUnitsResult, allocator: std.mem.Allocator) void {
            switch (result.*) {
                .none, .unresolved => {},
                .resolved => |root_source_files| {
                    allocator.free(root_source_files);
                },
            }
            result.* = undefined;
        }
    };

    /// Returns the root source file of the root module of the given document. Same as `@import("root")`.
    pub fn getAssociatedCompilationUnits(self: *SourceDocument, document_store: *DocumentStore) error{ Canceled, OutOfMemory, SourceExcluded }!GetAssociatedCompilationUnitsResult {
        const allocator = document_store.allocator;
        const io = document_store.io;

        const build_file, const target_root_source_file = switch (self.impl.associated_compilation_units) {
            else => return self.impl.associated_compilation_units,
            .unresolved => switch (try self.getAssociatedBuildFile(document_store)) {
                .none => return .none,
                .unresolved => return .unresolved,
                .resolved => |resolved| .{ resolved.build_file, resolved.root_source_file },
            },
        };

        const build_config = build_file.tryLockConfig(io) orelse return .none;
        defer build_file.unlockConfig(io);

        const modules = &build_config.modules.map;

        var visted: std.DynamicBitSetUnmanaged = try .initEmpty(allocator, modules.count());
        defer visted.deinit(allocator);

        var queue: std.ArrayList(usize) = try .initCapacity(allocator, 1);
        defer queue.deinit(allocator);

        const target_index = modules.getIndex(target_root_source_file).?;

        // We only care about the root source file of each root module so we convert them to a set.
        var root_modules: std.array_hash_map.String(void) = .empty;
        defer root_modules.deinit(allocator);

        try root_modules.ensureTotalCapacity(allocator, build_config.compilations.len);
        for (build_config.compilations) |compile| {
            root_modules.putAssumeCapacity(compile.root_module, {});
        }

        var results: std.ArrayList([]const u8) = .empty;
        defer results.deinit(allocator);

        // Do a graph search from root modules until we reach `root_source_file`
        for (root_modules.keys()) |root_module| {
            visted.unsetAll();
            queue.clearRetainingCapacity();
            queue.appendAssumeCapacity(modules.getIndex(root_module).?);

            while (queue.pop()) |index| {
                if (index == target_index) {
                    try results.append(allocator, root_module);
                    break;
                }

                if (visted.isSet(index)) continue;
                visted.set(index);

                const imported_modules = modules.values()[index].import_table.map.values();
                try queue.ensureUnusedCapacity(allocator, imported_modules.len);
                for (imported_modules) |root_source_file| {
                    queue.appendAssumeCapacity(modules.getIndex(root_source_file) orelse continue);
                }
            }
        }

        if (results.items.len == 0) {
            self.impl.associated_compilation_units = .none;
        } else {
            self.impl.associated_compilation_units = .{ .resolved = try results.toOwnedSlice(allocator) }; // zbc-disable-line: tagged-union-payload-early-exit — ZLS pattern; failure leaves impl in .none state set on the line above
        }
        return self.impl.associated_compilation_units;
    }

    fn refresh(
        document: *SourceDocument,
        /// Old state will be moved into this document to be deallocated after returning.
        old_document: *SourceDocument,
        /// Takes ownership.
        text: [:0]const u8,
        allocator: std.mem.Allocator,
    ) error{OutOfMemory}!void {
        const tracy_zone = tracy.traceNamed(@src(), "SourceDocument.refresh");
        defer tracy_zone.end();

        const mode: Ast.Mode = if (std.mem.eql(u8, std.Io.Dir.path.extension(document.uri.raw), ".zon")) .zon else .zig;
        var new_tree = try parseTree(allocator, text, mode);
        errdefer new_tree.deinit(allocator);

        var new_file_imports: std.ArrayList(Uri) = .empty;
        errdefer new_file_imports.deinit(allocator);

        try collectImports(
            allocator,
            document.uri,
            &new_tree,
            &new_file_imports,
        );

        const file_imports = try new_file_imports.toOwnedSlice(allocator);

        errdefer comptime unreachable;

        if (document.impl.has_tree_and_source) {
            old_document.tree = document.tree;
            old_document.impl.has_tree_and_source = true;
        }

        document.tree = new_tree;
        old_document.file_imports = document.file_imports;
        document.file_imports = file_imports;
        document.impl.has_tree_and_source = true;

        old_document.document_scope = document.document_scope;
        document.document_scope = .unset;
    }

    /// The source domain every reported position lives in.
    ///
    /// `Ast` keeps each token start as a `u32`, and `source.len` is
    /// carried in that same table as the end-of-file token's start, so a
    /// source of exactly `maxInt(u32)` bytes would still fit `Ast`'s own
    /// table.  A reported column is a byte offset *plus one*, though, so
    /// the last byte of such a source has no representable column: the
    /// domain is strictly shorter than `maxInt(u32)`.
    ///
    /// `error.OutOfMemory` is that address-space capacity failure, not a
    /// failed allocation — nothing has been allocated when this is
    /// reported.  It is surfaced rather than swallowed because a document
    /// too wide to address is exactly what the caller has to be told,
    /// and it is the existing error these entry points already carry.
    ///
    /// The number is shared with the read policy: `max_source_bytes` *is*
    /// `maxInt(u32)`, and `SourcePolicy.admitsSourceLength` applies exactly
    /// this exclusive test, so a source the filesystem read admits is a
    /// source this check admits and neither half of a refresh can end up
    /// owning an unparseable source.  What still differs is where the bytes
    /// came from and what a refusal is called.  A filesystem read learns the
    /// length from a `stat` and reports `error.SourceTooWide`, which names
    /// the width; client text arrives already in hand, capped by nothing, so
    /// the same refusal has to be reported as the address-space capacity
    /// failure these entry points already carry.  Both answer before the
    /// bytes are copied.
    fn requireAddressableSource(source: []const u8) error{OutOfMemory}!void {
        if (!SourcePolicy.admitsSourceLength(source.len)) return error.OutOfMemory;
    }

    fn parseTree(allocator: std.mem.Allocator, new_text: [:0]const u8, mode: Ast.Mode) error{OutOfMemory}!Ast {
        const tracy_zone = tracy.traceNamed(@src(), "Ast.parse");
        defer tracy_zone.end();

        try requireAddressableSource(new_text);

        var tree = try Ast.parse(allocator, new_text, mode);
        errdefer tree.deinit(allocator);

        // remove unused capacity
        var nodes = tree.nodes.toMultiArrayList();
        try nodes.setCapacity(allocator, nodes.len);
        tree.nodes = nodes.slice();

        // remove unused capacity
        var tokens = tree.tokens.toMultiArrayList();
        try tokens.setCapacity(allocator, tokens.len);
        tree.tokens = tokens.slice();
        return tree;
    }

    fn collectImports(
        allocator: std.mem.Allocator,
        uri: Uri,
        tree: *const Ast,
        file_imports: *std.ArrayList(Uri),
    ) error{OutOfMemory}!void {
        const tracy_zone = tracy.trace(@src());
        defer tracy_zone.end();

        const parsed_uri = uri.toStdUri();

        const node_tags = tree.nodes.items(.tag);
        for (node_tags, 0..) |tag, i| {
            const node: Ast.Node.Index = @enumFromInt(i);

            switch (tag) {
                .builtin_call,
                .builtin_call_comma,
                .builtin_call_two,
                .builtin_call_two_comma,
                => {},
                else => continue,
            }
            const name = offsets.tokenToSlice(tree, tree.nodeMainToken(node));

            if (std.mem.eql(u8, name, "@import")) {
                try file_imports.ensureUnusedCapacity(allocator, 1);

                var buffer: [2]Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&buffer, node).?;
                if (params.len < 1) continue;
                if (tree.nodeTag(params[0]) != .string_literal) continue;

                var import_string = offsets.tokenToSlice(tree, tree.nodeMainToken(params[0]));
                import_string = import_string[1 .. import_string.len - 1];

                if (!std.mem.endsWith(u8, import_string, ".zig")) continue;

                const import_uri = try Uri.resolveImport(allocator, uri, parsed_uri, import_string);
                file_imports.appendAssumeCapacity(import_uri);
                continue;
            }
        }
    }

    /// A document that can only be deallocated. Keep in sync with `deinit`.
    const dead: SourceDocument = .{
        .uri = undefined,
        .tree = undefined,
        .file_imports = &.{},
        .lsp_synced = undefined,
        .impl = .{
            .store = undefined,
            .has_tree_and_source = false,
        },
    };

    /// Caller must free `SourceDocument.uri` if needed.
    /// Keep in sync with `dead`.
    fn deinit(self: *SourceDocument, allocator: std.mem.Allocator) void {
        const tracy_zone = tracy.trace(@src());
        defer tracy_zone.end();

        if (self.impl.has_tree_and_source) {
            allocator.free(self.tree.source);
            self.tree.deinit(allocator);
        }
        self.document_scope.deinit(allocator);
        for (self.file_imports) |uri| uri.deinit(allocator);
        allocator.free(self.file_imports);

        self.impl.associated_build_file.deinit(allocator);
        self.impl.associated_compilation_units.deinit(allocator);

        self.* = undefined;
    }

    const Future = struct {
        /// Signalled when this entry's load finishes, so a second caller
        /// can await the one in flight instead of starting its own.
        event: std.Io.Event,
        document: SourceDocument,
        err: ?ReadFileError,

        pub fn await(f: *Future, io: std.Io) ReadFileError!*SourceDocument {
            try f.event.wait(io);
            return f.err orelse return &f.document;
        }
    };

    fn Lazy(comptime T: type, comptime Context: type) type {
        return struct {
            mutex: std.Io.Mutex,
            value: ?T,

            const LazyResource = @This();

            pub const unset: LazyResource = .{
                .mutex = .init,
                .value = null,
            };

            pub fn deinit(lazy: *LazyResource, allocator: std.mem.Allocator) void {
                const value: *T = if (lazy.value) |*value| value else return;
                Context.deinit(value, allocator);
                lazy.value = undefined;
            }

            pub fn get(lazy: *LazyResource, document: *SourceDocument) error{OutOfMemory}!*const T {
                const tracy_zone = tracy.traceNamed(@src(), "Lazy(" ++ @typeName(T) ++ ").get");
                defer tracy_zone.end();

                const store = document.impl.store;
                const io = store.io;

                lazy.mutex.lockUncancelable(io);
                defer lazy.mutex.unlock(io);
                if (lazy.value == null) {
                    lazy.value = try Context.create(document, store.allocator);
                }
                return &lazy.value.?;
            }

            pub fn getOrNull(lazy: *LazyResource, document: *SourceDocument) ?*const T {
                const tracy_zone = tracy.traceNamed(@src(), "Lazy(" ++ @typeName(T) ++ ").getOrNull");
                defer tracy_zone.end();

                const store = document.impl.store;
                const io = store.io;
                document.impl.lock.lockUncancelable(io);
                defer document.impl.lock.unlock(io);
                return if (lazy.value) |*value| value else null;
            }

            pub fn getCached(lazy: *LazyResource) *const T {
                return &lazy.value.?;
            }
        };
    }

    const DocumentStoreContext = struct {
        fn create(document: *SourceDocument, allocator: std.mem.Allocator) error{OutOfMemory}!DocumentScope {
            var document_scope: DocumentScope = try .init(allocator, &document.tree);
            errdefer document_scope.deinit(allocator);

            // remove unused capacity
            document_scope.extra.shrinkAndFree(allocator, document_scope.extra.items.len);
            try document_scope.declarations.setCapacity(allocator, document_scope.declarations.len);
            try document_scope.scopes.setCapacity(allocator, document_scope.scopes.len);

            return document_scope;
        }
        fn deinit(document_scope: *DocumentScope, allocator: std.mem.Allocator) void {
            document_scope.deinit(allocator);
        }
    };
};

/// One source read in one module: the shared syntax snapshot plus the
/// compilation environment its `@import`s resolve against.
///
/// A view is a value, not an owner.  It borrows the store's
/// `SourceDocument` and adds the module, so two modules that import the
/// same physical file share one parse and still get different answers.
/// Because the module is part of the view, every declaration, scope,
/// token, node and type derived from one carries the module with it.
pub const Handle = struct {
    document: *SourceDocument,
    module: ModuleId,

    /// The same source in the same module: the same semantic view.
    pub fn eql(a: Handle, b: Handle) bool {
        return a.module == b.module and a.document == b.document;
    }

    pub fn getDocumentScope(self: Handle) error{OutOfMemory}!*const DocumentScope {
        return try self.document.document_scope.get(self.document);
    }
};

/// Publishes the failure a lookup observed, and clears it when `null`.
/// Both halves are written under `mutex` so a reader can never see one
/// half of a newer snapshot beside the other half of an older one.
fn publishFailure(self: *DocumentStore, source_failure: ?anyerror, parse_failure: ?ParseFailure) void {
    self.mutex.lockUncancelable(self.io);
    defer self.mutex.unlock(self.io);
    self.source_failure = source_failure;
    self.parse_failure = parse_failure;
}

/// Forgets the last published failure.  One analysis sweeps every file it
/// owns through the same store, so the next lookup must not inherit the
/// previous file's cause.
pub fn clearFailure(self: *DocumentStore) void {
    self.publishFailure(null, null);
}

/// The cause and position of the last failure, read as one snapshot.
pub fn failureSnapshot(self: *DocumentStore) struct { source_failure: ?anyerror, parse_failure: ?ParseFailure } {
    self.mutex.lockUncancelable(self.io);
    defer self.mutex.unlock(self.io);
    return .{ .source_failure = self.source_failure, .parse_failure = self.parse_failure };
}

pub const HandleIterator = struct {
    store: *DocumentStore,
    i: usize = 0,

    /// Every document the store serves, read in the unscoped environment.
    pub fn next(it: *HandleIterator) ?Handle {
        it.store.mutex.lockUncancelable(it.store.io);
        defer it.store.mutex.unlock(it.store.io);
        while (true) {
            defer it.i += 1;
            switch (std.math.order(it.i, it.store.documents.count())) {
                .lt => {},
                .eq => return null,
                .gt => unreachable, // document count decreased
            }
            const document = it.store.documents.values()[it.i].await(it.store.io) catch continue;
            return .{ .document = document, .module = .unscoped };
        }
    }
};

pub const ErrorMessage = struct {
    loc: offsets.Loc,
    code: []const u8,
    message: []const u8,
};

pub fn deinit(self: *DocumentStore) void {
    if (supports_build_system) {
        self.wait_group.cancel(self.io);
    }

    for (self.documents.keys(), self.documents.values()) |uri, future| {
        if (future.await(self.io)) |document| document.deinit(self.allocator) else |_| {}
        uri.deinit(self.allocator);
        self.allocator.destroy(future);
    }
    self.documents.deinit(self.allocator);
    for (self.source_aliases.keys()) |uri| uri.deinit(self.allocator);
    self.source_aliases.deinit(self.allocator);
    self.canonical_paths.deinit(self.allocator);

    if (supports_build_system) {
        for (self.build_files.values()) |build_file| {
            build_file.deinit(self.allocator);
            self.allocator.destroy(build_file);
        }
        self.build_files.deinit(self.allocator);
    }

    if (self.named_modules) |*modules| modules.deinit();

    self.* = undefined;
}

/// Returns a handle to the given document, read in `module`.
/// **Thread safe** takes a shared lock
/// This function does not protect against data races from modifying the document
pub fn getHandle(self: *DocumentStore, uri: Uri, module: ModuleId) ?Handle {
    const document = self.documentFor(uri) orelse return null;
    return .{ .document = document, .module = module };
}

/// The document the store already serves for `uri`, or null when it has
/// none or the one it has failed. Missing and excluded documents publish
/// nothing; other failures retain their source attribution under the lock.
fn documentFor(self: *DocumentStore, uri: Uri) ?*SourceDocument {
    const future = future: {
        self.mutex.lockUncancelable(self.io);
        defer self.mutex.unlock(self.io);
        break :future self.documents.get(self.source_aliases.get(uri) orelse uri) orelse return null;
    };
    const document = future.await(self.io) catch |err| {
        switch (err) {
            error.SourceExcluded, error.FileNotFound, error.NotDir => {},
            else => self.publishFailure(err, null),
        }
        return null;
    };
    if (document.tree.errors.len != 0) {
        self.publishFailure(error.ImportInvalidSyntax, .fromTree(document.uri.raw, &document.tree));
        return null;
    }
    return document;
}

const ReadFileError = SourcePolicy.ReadSourceError || std.Io.Dir.RealPathFileError || error{SourceExcluded};

/// Must satisfy `uri.isFileScheme()`.
fn readFile(self: *DocumentStore, uri: Uri) ReadFileError![:0]u8 {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const file_path = uri.toFsPath(self.allocator) catch |err| switch (err) {
        error.UnsupportedScheme => unreachable,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer self.allocator.free(file_path);
    if (!self.allowsSourceAlias(file_path)) return error.SourceExcluded;
    const canonical = try self.canonical_paths.resolve(self.allocator, self.io, file_path);
    if (!self.allowsSource(canonical)) return error.SourceExcluded;

    const dir, const sub_path = blk: {
        if (builtin.target.cpu.arch.isWasm() and !builtin.link_libc) {
            for (self.config.wasi_preopens.map.keys()[3..], 3..) |name, i| {
                const preopen_dir: std.Io.Dir = .{ .handle = @intCast(i) };
                const preopen_path = std.mem.trimEnd(u8, name, "/");

                if (!std.mem.startsWith(u8, canonical, preopen_path)) continue;
                if (!std.mem.startsWith(u8, canonical[preopen_path.len..], "/")) continue;

                break :blk .{ preopen_dir, std.mem.trimStart(u8, canonical[preopen_path.len..], "/") };
            }
        }
        break :blk .{ std.Io.Dir.cwd(), canonical };
    };

    // The policy has already had its say on *which* file this is; the width
    // of what is inside it is the shared reader's one job, so an ordinary
    // load, a `build.zig` scan and a standalone cache's own load can never
    // disagree about it.
    return SourcePolicy.readSourceSentinel(self.io, dir, sub_path, self.allocator);
}

/// This store's relative-import edges, read from the shared `SourceDocument`
/// parses it already owns.
///
/// `file_imports` holds already-canonical absolute paths, borrowed from the
/// document, so this reads nothing and parses nothing: the session's walk
/// and every other module's walk share one parse per URI.
pub fn relativeEdges(self: *DocumentStore) RelativeEdges {
    return .{ .ctx = self, .read = readSourceDocumentEdges };
}

fn readSourceDocumentEdges(
    ctx: *const anyopaque,
    arena: std.mem.Allocator,
    canonical_path: []const u8,
    edges: *std.ArrayList([]const u8),
) (error{OutOfMemory} || std.Io.Cancelable)!bool {
    const store: *DocumentStore = @ptrCast(@alignCast(@constCast(ctx)));
    // Membership identity is the canonical path, exactly as it is for a
    // `SourceDocument`.  A caller may hand over a spelling that reaches the
    // same file through a symlink — a temporary directory under a linked
    // cache, say — and admitting or matching on that logical spelling puts
    // the walk's answer somewhere the store never looks, so every document
    // appears to reach nothing.
    //
    // `canonical_paths.resolve` returns bytes the table owns, so this borrows
    // them and frees nothing; the store's `deinit` releases the table.
    const canonical = store.canonical_paths.resolve(store.allocator, store.io, canonical_path) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Canceled => return error.Canceled,
        else => return false,
    };
    if (!store.source_policy.allowsAbsolutePath(canonical)) return false;
    const uri = Uri.fromPath(store.allocator, canonical) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer uri.deinit(store.allocator);

    // A denied or unreadable target is absent evidence, not a failure of
    // this document or of the file under analysis.
    // Distinct prongs returning literals rather than `return err`: a
    // captured error keeps the entire set of the operation it came from,
    // and that set includes `SourceExcluded`, which this function must
    // never raise.  Naming the two it does raise re-states them exactly.
    const handle = store.getOrLoadHandle(uri, .unscoped) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Canceled => return error.Canceled,
        error.SourceExcluded, error.FileNotFound, error.NotDir => return false,
    } orelse return false;

    for (handle.document.file_imports) |imported| {
        const path = imported.toFsPath(arena) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.UnsupportedScheme => continue,
        };
        const imported_path = store.canonical_paths.resolve(store.allocator, store.io, path) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Canceled => return error.Canceled,
            else => continue,
        };
        if (!store.source_policy.allowsAbsolutePath(imported_path)) continue;
        try edges.append(arena, imported_path);
    }
    return true;
}

/// Every declared module instance that reaches `path`, read through this
/// store's syntax pool.
///
/// `path` may be any spelling that reaches the file.  It is canonicalized
/// here rather than at each call site, because membership identity is the
/// physical path and it is not something every caller can be expected to
/// remember.
///
/// This is the session's spelling of the one shared membership walk: a
/// standalone project cache answers the same question with the same
/// algorithm through its own `RelativeEdges`, and neither holds a second
/// copy of the reachability graph logic.
///
/// The `build.zig` chain that declares those instances is read here rather
/// than left to the caller.  Membership is answered by iterating what a scan
/// declared, so a chain nobody has read yet yields an empty answer that reads
/// exactly like "no proven membership" — and whether it has been read
/// depends on which other question this store was asked first.  A named
/// import answered from that empty set is a wrong answer wearing the honest
/// one's shape.
pub fn candidateEnvironments(self: *DocumentStore, path: []const u8) (error{OutOfMemory} || std.Io.Cancelable)![]const []const u8 {
    const canonical = self.canonical_paths.resolve(self.allocator, self.io, path) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Canceled => return error.Canceled,
        else => return &.{},
    };
    if (std.fs.path.dirname(canonical)) |directory| {
        try self.namedModuleMap().scanInto(self.io, self.source_policy, directory);
    }
    return self.namedModuleMap().candidateEnvironments(self.relativeEdges(), self.allocator, canonical);
}

/// The toolchain's standard library, canonicalized at use.
///
/// `zig env` reports `lib_dir` as the path the compiler was reached
/// through, which may contain a symlink, while every URI the store
/// serves is canonicalized.  Comparing one against the other makes every
/// toolchain-declaration fact silently false — the standard library stops
/// existing as far as the analysis is concerned — so both sides are
/// canonicalized through one table.  This is derived on each use rather
/// than latched at init, because `config` may be replaced afterwards.
pub fn toolchainRoot(self: *DocumentStore) ?[]const u8 {
    const directory = self.config.zig_lib_dir orelse return null;
    const path = directory.path orelse return null;
    return self.canonical_paths.resolve(self.allocator, self.io, path) catch null;
}

/// Admit a path the analysis roots own, or one the toolchain owns.
///
/// The compiler's standard library is an admission exception rather than
/// an allowed root: it is fixed by the compiler this run is pinned to,
/// so it is admitted whole.  This is the one place a name in the skip
/// list does not apply, and it is stated here rather than implied.
fn allowsSource(self: *DocumentStore, path: []const u8) bool {
    if (self.source_policy.allowsAbsolutePath(path)) return true;
    const root = self.toolchainRoot() orelse return false;
    return within(root, path);
}

/// The pre-open check accepts the configured toolchain spelling.
/// Callers must check the canonical target with `allowsSource` afterwards.
fn allowsSourceAlias(self: *DocumentStore, path: []const u8) bool {
    if (self.allowsSource(path)) return true;
    const directory = self.config.zig_lib_dir orelse return false;
    return within(directory.path orelse return false, path);
}

fn canonicalUri(self: *DocumentStore, uri: Uri) ReadFileError!Uri {
    const path = uri.toFsPath(self.allocator) catch |err| switch (err) {
        error.UnsupportedScheme => unreachable,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer self.allocator.free(path);
    if (!self.allowsSourceAlias(path)) return error.SourceExcluded;
    const canonical = try self.canonical_paths.resolve(self.allocator, self.io, path);
    if (!self.allowsSource(canonical)) return error.SourceExcluded;
    return Uri.fromPath(self.allocator, canonical);
}

fn rememberSourceAlias(self: *DocumentStore, uri: Uri, canonical: Uri) !void {
    if (std.mem.eql(u8, uri.raw, canonical.raw)) return;
    try self.mutex.lock(self.io);
    defer self.mutex.unlock(self.io);
    if (self.source_aliases.contains(uri)) return;
    const key = try uri.dupe(self.allocator);
    errdefer key.deinit(self.allocator);
    try self.source_aliases.putNoClobber(self.allocator, key, canonical);
}

/// Turns a load failure into the outcome the caller reports.
///
/// Missing and excluded documents propagate their own cause without
/// publishing it as a failure of the file that imports them. A root caller
/// receives the exact error; a dependency caller may treat absence as unknown.
fn loadFailed(self: *DocumentStore, err: ReadFileError) error{ Canceled, OutOfMemory, SourceExcluded, FileNotFound, NotDir }!?Handle {
    switch (err) {
        error.Canceled => return error.Canceled,
        error.OutOfMemory => return error.OutOfMemory,
        error.SourceExcluded => return error.SourceExcluded,
        error.FileNotFound => return error.FileNotFound,
        error.NotDir => return error.NotDir,
        else => {
            self.publishFailure(err, null);
            return null;
        },
    }
}

/// Returns a handle to the given document, read in `module`.
/// Will load the document from disk if it hasn't been already.
/// **Thread safe** takes an exclusive lock
/// This function does not protect against data races from modifying the document
pub fn getOrLoadHandle(self: *DocumentStore, uri: Uri, module: ModuleId) error{ Canceled, OutOfMemory, SourceExcluded, FileNotFound, NotDir }!?Handle {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    if (!uri.isFileScheme()) return self.getHandle(uri, module);
    const known_uri, const cached = known: {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        const known = self.source_aliases.get(uri) orelse uri;
        break :known .{ known, self.documents.contains(known) };
    };
    const canonical: ?Uri = if (cached) null else self.canonicalUri(known_uri) catch |err| return self.loadFailed(err);
    defer if (canonical) |value| value.deinit(self.allocator);
    const document = self.createAndStoreDocument(
        canonical orelse known_uri,
        .uri,
        .{
            .lsp_synced = false,
            .override = false,
            .load_build_file_behaviour = .never,
        },
    ) catch |err| return self.loadFailed(err);
    try self.rememberSourceAlias(uri, document.uri);
    if (document.tree.errors.len != 0) {
        self.publishFailure(error.ImportInvalidSyntax, .fromTree(document.uri.raw, &document.tree));
        return null;
    }
    return .{ .document = document, .module = module };
}

/// **Thread safe** takes a shared lock
/// This function does not protect against data races from modifying the BuildFile
pub fn getBuildFile(self: *DocumentStore, uri: Uri) ?*BuildFile {
    comptime std.debug.assert(supports_build_system);
    self.mutex.lockUncancelable(self.io);
    defer self.mutex.unlock(self.io);
    return self.build_files.get(uri);
}

/// invalidates any pointers into `DocumentStore.build_files`
/// **Thread safe** takes an exclusive lock
/// This function does not protect against data races from modifying the BuildFile
fn getOrLoadBuildFile(self: *DocumentStore, uri: Uri) error{ Canceled, OutOfMemory }!*BuildFile {
    comptime std.debug.assert(supports_build_system);

    if (self.getBuildFile(uri)) |build_file| return build_file;

    const new_build_file: *BuildFile = blk: {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);

        const gop = try self.build_files.getOrPut(self.allocator, uri);
        if (gop.found_existing) return gop.value_ptr.*;
        errdefer self.build_files.swapRemoveAt(gop.index);

        gop.value_ptr.* = try self.allocator.create(BuildFile);
        errdefer self.allocator.destroy(gop.value_ptr.*);

        gop.value_ptr.*.* = try self.createBuildFile(uri);
        gop.key_ptr.* = gop.value_ptr.*.uri;
        break :blk gop.value_ptr.*;
    };

    // this code path is only reached when the build file is new

    self.invalidateBuildFile(new_build_file.uri);

    return new_build_file;
}

/// Opens a document that is synced over the LSP protocol (`textDocument/didOpen`).
/// **Not thread safe**
pub fn openLspSyncedDocument(self: *DocumentStore, uri: Uri, text: []const u8) error{ Canceled, OutOfMemory }!void {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    if (self.getHandle(uri, .unscoped)) |handle| {
        if (handle.document.lsp_synced) {
            log.warn("Document already open: {s}", .{uri.raw});
        }
    }

    // Client text is not capped by `SourcePolicy` the way file reads are,
    // so reject a source the engine cannot address before it is copied.
    try SourceDocument.requireAddressableSource(text);

    const duped_text = try self.allocator.dupeSentinel(u8, text, 0);
    _ = self.createAndStoreDocument(
        uri,
        .{ .text = duped_text },
        .{
            .lsp_synced = true,
            .override = true,
            .load_build_file_behaviour = .load_but_dont_update,
        },
    ) catch |err| switch (err) {
        error.Canceled, error.OutOfMemory => |e| return e,
        else => unreachable,
    };
}

/// Closes a document that has been synced over the LSP protocol (`textDocument/didClose`).
/// **Not thread safe**
pub fn closeLspSyncedDocument(self: *DocumentStore, uri: Uri) void {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const document_index = self.documents.getIndex(uri) orelse {
        log.warn("Document not found: {s}", .{uri.raw});
        return;
    };
    defer self.documents.swapRemoveAt(document_index);

    const document_uri = self.documents.keys()[document_index];
    defer document_uri.deinit(self.allocator);

    const document_future = self.documents.values()[document_index];
    defer self.allocator.destroy(document_future);

    if (document_future.await(self.io)) |document| {
        if (!document.lsp_synced) {
            log.warn("Document already closed: {s}", .{uri.raw});
        }
        document.deinit(self.allocator);
    } else |_| {}
}

/// Updates a document that is synced over the LSP protocol (`textDocument/didChange`).
/// Takes ownership of `new_text` which has to be allocated with this DocumentStore's allocator.
/// `new_text` is released, and the document left untouched, when it is
/// rejected — including by the source-domain check in `parseTree`.
/// **Not thread safe**
pub fn refreshLspSyncedDocument(self: *DocumentStore, uri: Uri, new_text: [:0]const u8) error{ Canceled, OutOfMemory }!void {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    if (self.getHandle(uri, .unscoped)) |old_handle| {
        if (!old_handle.document.lsp_synced) {
            log.warn("Document modified without being opened: {s}", .{uri.raw});
        }
    } else {
        log.warn("Document modified without being opened: {s}", .{uri.raw});
    }

    _ = self.createAndStoreDocument(
        uri,
        .{ .text = new_text },
        .{
            .lsp_synced = true,
            .override = true,
            .load_build_file_behaviour = .only_update,
        },
    ) catch |err| switch (err) {
        error.Canceled, error.OutOfMemory => |e| return e,
        else => unreachable,
    };
}

/// Refreshes a document from the file system, unless said document is synced over the LSP protocol.
/// **Not thread safe**
pub fn refreshDocumentFromFileSystem(self: *DocumentStore, uri: Uri, should_delete: bool) error{ Canceled, OutOfMemory }!bool {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    if (should_delete) {
        const index = self.documents.getIndex(uri) orelse return false;
        const document_future = self.documents.values()[index];
        const document = document_future.await(self.io) catch return false;
        if (document.lsp_synced) return false;
        self.documents.swapRemoveAt(index);
        document.uri.deinit(self.allocator);
        document.deinit(self.allocator);
        self.allocator.destroy(document_future);
    } else {
        if (self.getHandle(uri, .unscoped)) |handle| {
            if (handle.document.lsp_synced) return false;
        } else return false;
        if (uri.isFileScheme()) return false;
        _ = self.createAndStoreDocument(
            uri,
            .uri,
            .{
                .lsp_synced = false,
                .override = true,
                .load_build_file_behaviour = .only_update,
            },
        ) catch |err| switch (err) {
            error.Canceled, error.OutOfMemory => |e| return e,
            else => return false,
        };
    }

    return true;
}

/// Invalidates a build files.
/// **Thread safe** takes a shared lock
pub fn invalidateBuildFile(self: *DocumentStore, build_file_uri: Uri) void {
    comptime std.debug.assert(supports_build_system);

    // This path does not run in any session this repository builds, and that
    // is a property of the callers rather than of the code below: both
    // in-repo `Config` constructions pass `build_runner_path = null`, because
    // zbc never runs a project's build.zig — running one executes that
    // project's code — and reads the wiring from the file instead.  The
    // guards are therefore the whole contract today.
    //
    // They are kept, not deleted, because `Config` is exported: a caller that
    // does have a build runner must reach `invalidateBuildFileWorker`
    // unchanged rather than through a shim.  The worker, the build-config
    // loader and `BuildFile.impl.config` are unreachable today for that one
    // reason, and this is where a reader should learn it instead of
    // rediscovering it from a null field.

    if (self.config.zig_exe_path == null) return;
    if (self.config.build_runner_path == null) return;
    if (self.config.global_cache_dir == null) return;
    if (self.config.zig_lib_dir == null) return;

    const build_file = self.getBuildFile(build_file_uri) orelse return;

    self.wait_group.async(self.io, invalidateBuildFileWorker, .{ self, build_file });
}

fn invalidateBuildFileWorker(self: *DocumentStore, build_file: *BuildFile) std.Io.Cancelable!void {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    {
        try build_file.impl.mutex.lock(self.io);
        defer build_file.impl.mutex.unlock(self.io);

        switch (build_file.impl.build_runner_state) {
            .idle => build_file.impl.build_runner_state = .running,
            .running => {
                build_file.impl.build_runner_state = .running_but_already_invalidated;
                return;
            },
            .running_but_already_invalidated => return,
        }
    }

    while (true) {
        build_file.impl.version += 1;
        const new_version = build_file.impl.version;

        const build_config = loadBuildConfiguration(self, build_file.uri, new_version) catch |err| switch (err) {
            error.Canceled => return error.Canceled,
            else => |e| {
                if (e != error.RunFailed) { // already logged
                    log.err("Failed to load build configuration for {s} (error: {})", .{ build_file.uri.raw, e });
                }
                build_file.impl.mutex.lockUncancelable(self.io);
                defer build_file.impl.mutex.unlock(self.io);
                build_file.impl.build_runner_state = .idle;
                return;
            },
        };

        build_file.impl.mutex.lockUncancelable(self.io);
        switch (build_file.impl.build_runner_state) {
            .idle => unreachable,
            .running => {
                var old_config = build_file.impl.config;
                build_file.impl.config = build_config;
                build_file.impl.build_runner_state = .idle;
                build_file.impl.mutex.unlock(self.io);

                if (old_config) |*config| config.deinit();
                break;
            },
            .running_but_already_invalidated => {
                build_file.impl.build_runner_state = .running;
                build_file.impl.mutex.unlock(self.io);

                build_config.deinit();
                continue;
            },
        }
    }
}

pub fn isBuildFile(uri: Uri) bool {
    return std.mem.endsWith(u8, uri.raw, "/build.zig");
}

pub fn isBuiltinFile(uri: Uri) bool {
    return std.mem.endsWith(u8, uri.raw, "/builtin.zig");
}

pub fn isInStd(uri: Uri) bool {
    // TODO: Better logic for detecting std or subdirectories?
    return std.mem.find(u8, uri.raw, "/std/") != null;
}

// ── Static module wiring ───────────────────────────────────────────────

/// Module wiring recovered from the `build.zig` files that govern a source
/// tree, without executing any of them.
///
/// Wiring is recorded *per module*, keyed by the module's own root source
/// file, never by a flat name.  Two modules in the same build script may
/// wire the same alias to different roots — `left.addImport("dep", …)` and
/// `right.addImport("dep", …)` — and a flat map would answer "unknown" for
/// both.  Keying by the module each alias is declared in is what lets each
/// importer resolve its own, which is what the compiler does too.
///
/// Only unique, explicit wiring is evidence: a literal `addModule` /
/// `createModule` `root_source_file`, attributed to the module the alias
/// was written against.  Everything else stays unresolved on purpose,
/// because a wrong root is worse than no root — an unknown module yields an
/// unknown type, a guessed one yields a wrong type:
///   * a generated module (`b.addOptions().createModule()`) has no path in
///     the source tree;
///   * `dep.module("name")` is wired by the *dependency's* build.zig, which
///     the source policy does not admit;
///   * a module chosen by a runtime condition, a computed path, or a shadowed
///     module variable is not proof of anything;
///   * an alias wired to two different roots *inside one module* is
///     ambiguous, so it stays unknown;
///   * a root that is not a readable file right now (a path a build step
///     would still have to write) is not a source, so it stays unknown.
///
/// Every recorded root passes the caller's source policy and exists on disk,
/// so publishing wiring never widens which files the store may read and
/// never turns an unknown type into a failed file.
///
/// One store belongs to one session, so this map is worker-owned session
/// state and needs no lock of its own; reading and parsing `build.zig`
/// files happens outside every lock the store takes.
pub const NamedModuleMap = struct {
    gpa: std.mem.Allocator,
    /// Owns every recorded name and root; released as one block.
    arena: std.heap.ArenaAllocator,
    /// Declared module instance identity -> the wiring that instance declares.
    entries: std.StringArrayHashMapUnmanaged(ModuleWiring) = .empty,
    /// Canonical root source file -> the identities of every instance that
    /// creates it.  A root created twice is two instances, and this index
    /// is what records that rather than letting the second declaration
    /// overwrite the first.
    by_root: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,
    /// Directories whose `build.zig` chain has already been read.
    scanned_dirs: std.StringArrayHashMapUnmanaged(void) = .empty,
    /// Declared module instance identity -> the documents its own root
    /// reaches through relative imports.
    ///
    /// This is the membership evidence a named import needs: a module reaches
    /// a document only by actually importing it, never by sitting in the
    /// same directory or sharing a file name.  It lives here rather than on
    /// any one syntax pool so that a session and a standalone project cache
    /// share one walk algorithm and one memo, each supplying only its own
    /// `RelativeEdges`.  Built once per instance and published whole or not
    /// at all, so a cancelled or out-of-memory walk leaves nothing behind
    /// for a later lookup to read as complete.
    memberships: std.StringArrayHashMapUnmanaged(std.ArrayListUnmanaged([]const u8)) = .empty,

    pub const ModuleWiring = struct {
        /// The canonical root source file this instance was declared with.
        root: []const u8,
        /// The name `b.addModule` declared it under, when it was a literal.
        /// A label for diagnostics, never an identity: two unrelated
        /// modules may both be called "left".
        name: ?[]const u8,
        /// Alias -> the identity of the instance this one wires it to, or
        /// null when this one instance wires the alias ambiguously — two
        /// different targets, or a target the expression did not pin to a
        /// single declaration.
        imports: std.StringArrayHashMapUnmanaged(?[]const u8),
    };

    /// One proved import target: the instance to read it in, and the file.
    pub const Resolution = struct {
        identity: []const u8,
        root: []const u8,
    };

    pub fn init(gpa: std.mem.Allocator) NamedModuleMap {
        return .{ .gpa = gpa, .arena = .init(gpa) };
    }

    /// Releases every structure this map allocates from `gpa`.
    ///
    /// The split is deliberate and is the whole of the ownership here: map
    /// and list *storage* comes from `gpa`, while the keys and values they
    /// hold — identity strings, roots, names, aliases — are arena bytes that
    /// `arena.deinit` releases in one block below.  Freeing the storage is
    /// therefore this function's job alone; freeing the bytes twice would be
    /// the bug.  `scanned_dirs` is not listed because it is arena-allocated
    /// throughout, so the arena covers it.
    pub fn deinit(self: *NamedModuleMap) void {
        for (self.entries.values()) |*wiring| {
            wiring.imports.deinit(self.gpa);
        }
        self.entries.deinit(self.gpa);
        for (self.by_root.values()) |*instances| {
            instances.deinit(self.gpa);
        }
        self.by_root.deinit(self.gpa);
        for (self.memberships.values()) |*reached| {
            for (reached.items) |path| self.gpa.free(path);
            reached.deinit(self.gpa);
        }
        self.memberships.deinit(self.gpa);
        self.arena.deinit();
        self.* = undefined;
    }

    /// Declares one module instance rooted at `root` and created by
    /// `identity` (its root together with the declaration site that made
    /// it), under `name` when one was proven.
    ///
    /// Declaring the same root twice creates two instances rather than
    /// merging them: two separate compilations may share one root file and
    /// wire its imports differently, and merging them would answer both
    /// from one table.
    pub fn declareModule(self: *NamedModuleMap, identity: []const u8, root: []const u8, name: ?[]const u8) !void {
        if (self.entries.get(identity) != null) return;
        const arena = self.arena.allocator();
        const owned_identity = try arena.dupe(u8, identity);
        const owned_root = try arena.dupe(u8, root);
        const owned_name: ?[]const u8 = if (name) |declared| try arena.dupe(u8, declared) else null;

        // The reverse index is committed before the forward one, so every
        // failure below is undone by an errdefer that only touches work this
        // call made.  Leaving the two indexes disagreeing would make an
        // instance invisible to `instancesOfRoot` while still answering
        // `lookup`, which is worse than never having declared it.
        var created_root = false;
        const root_index = self.by_root.getIndex(root) orelse blk: {
            try self.by_root.put(self.gpa, owned_root, .empty);
            created_root = true;
            break :blk self.by_root.getIndex(root).?;
        };
        errdefer if (created_root) {
            self.by_root.values()[root_index].deinit(self.gpa);
            self.by_root.orderedRemoveAt(root_index);
        };

        try self.by_root.values()[root_index].append(self.gpa, owned_identity);
        errdefer _ = self.by_root.values()[root_index].pop();

        try self.entries.put(self.gpa, owned_identity, .{
            .root = owned_root,
            .name = owned_name,
            .imports = .empty,
        });
    }

    /// Records one module-local import alias on the instance `identity`.
    ///
    /// `target` is the identity of the instance the alias names, or null
    /// when the build script did not pin that alias to one declaration.  A
    /// null target is recorded as *unknown*, not skipped: an alias the
    /// build writes and this scan cannot attribute must not read as an
    /// alias the build never wrote.
    pub fn recordImport(self: *NamedModuleMap, identity: []const u8, alias: []const u8, target: ?[]const u8) !void {
        const index = self.entries.getIndex(identity) orelse return;
        const gpa = self.arena.allocator();
        const imports = &self.entries.values()[index].imports;
        if (imports.get(alias)) |known| {
            const previous = known orelse return;
            const next = target orelse {
                imports.getPtr(alias).?.* = null;
                return;
            };
            if (!std.mem.eql(u8, previous, next)) imports.getPtr(alias).?.* = null;
            return;
        }
        const owned_alias = try gpa.dupe(u8, alias);
        errdefer gpa.free(owned_alias);
        const owned_target: ?[]const u8 = if (target) |t| try gpa.dupe(u8, t) else null;
        try imports.put(self.gpa, owned_alias, owned_target);
    }

    /// The target the instance `identity` proves for `alias`.
    pub fn lookup(self: *const NamedModuleMap, identity: []const u8, alias: []const u8) ?Resolution {
        const wiring = self.entries.get(identity) orelse return null;
        const recorded = wiring.imports.get(alias) orelse return null;
        // The stored value is `?[]const u8`: null is an alias this instance
        // wires ambiguously, which is unknown rather than absent.
        const target = recorded orelse return null;
        return .{ .identity = target, .root = self.rootOf(target) orelse return null };
    }

    /// The canonical root source file the instance `identity` was declared
    /// with.
    pub fn rootOf(self: *const NamedModuleMap, identity: []const u8) ?[]const u8 {
        const wiring = self.entries.get(identity) orelse return null;
        return wiring.root;
    }

    /// The declared name of the instance `identity`.
    pub fn moduleName(self: *const NamedModuleMap, identity: []const u8) ?[]const u8 {
        const wiring = self.entries.get(identity) orelse return null;
        return wiring.name;
    }

    /// Every declared instance identity: the candidate set an unproven
    /// importer is answered from.  Two instances of one root are two
    /// candidates, which is how an unproven importer learns that a name
    /// wired one way in each of them is not an answer.
    pub fn declaredInstances(self: *const NamedModuleMap) []const []const u8 {
        return self.entries.keys();
    }

    /// The instance identities that create `root`.
    pub fn instancesOfRoot(self: *const NamedModuleMap, root: []const u8) []const []const u8 {
        const index = self.by_root.getIndex(root) orelse return &.{};
        return self.by_root.values()[index].items;
    }

    /// The one instance every candidate proves for `alias`, or null.
    ///
    /// Every candidate is a proven owner of the importing document, and a
    /// candidate that does not wire this alias says the name does not
    /// exist in the environment it would have to resolve in.  That is a
    /// veto, not an abstention: skipping it would let the one unrelated
    /// module that happens to spell the alias answer for a document it
    /// never imported.  The candidate set must already be narrowed to
    /// proven membership, because a candidate list widened to "everything
    /// the project declares" makes this rule far too strict to be useful.
    ///
    /// Agreement is on the *declaration*: two instances sharing one root are
    /// still two environments, and resolving to either of them is guessing.
    pub fn lookupAgreedAmongAll(
        self: *const NamedModuleMap,
        candidates: []const []const u8,
        alias: []const u8,
    ) ?Resolution {
        if (candidates.len == 0) return null;
        var agreed: ?Resolution = null;
        for (candidates) |identity| {
            const resolved = self.lookup(identity, alias) orelse return null;
            if (agreed) |previous| {
                if (!std.mem.eql(u8, previous.identity, resolved.identity)) return null;
            } else {
                agreed = resolved;
            }
        }
        return agreed;
    }

    /// Every declared module instance that reaches `canonical_path` through
    /// the relative-import edges `edges` reports.
    ///
    /// Membership is evidence of belonging, and it is the only evidence used
    /// here: a module reaches a file by importing it, never by sharing its
    /// directory or its file name.  A declared root is reached by the very
    /// declarations that create it, so a root created twice is reached twice
    /// and its own entry point stays unproven rather than picking one.
    ///
    /// Owns only the returned slice; the identities inside are arena bytes
    /// that outlive it.  `scanInto` must have run first, because the walk
    /// iterates the instances it declared.  An empty answer means "no proven
    /// membership" — never "the one module that happens to bind that name".
    pub fn candidateEnvironments(
        self: *NamedModuleMap,
        edges: RelativeEdges,
        gpa: std.mem.Allocator,
        canonical_path: []const u8,
    ) (error{OutOfMemory} || std.Io.Cancelable)![]const []const u8 {
        var candidates: std.ArrayList([]const u8) = .empty;
        errdefer candidates.deinit(gpa);
        for (self.declaredInstances()) |identity| {
            const reached = try self.membershipOf(edges, gpa, identity);
            for (reached) |member| {
                if (!std.mem.eql(u8, member, canonical_path)) continue;
                candidates.append(gpa, identity) catch |err| return err;
                break;
            }
        }
        return candidates.toOwnedSlice(gpa);
    }

    /// The documents the instance `identity` reaches, computed once and then
    /// reused for every later membership question.
    ///
    /// The walk follows relative-import edges only.  A named import is
    /// deliberately not followed: an alias says nothing about which module
    /// owns this document, and assuming it does is the wrong-file answer
    /// this whole design exists to eliminate.
    fn membershipOf(
        self: *NamedModuleMap,
        edges: RelativeEdges,
        gpa: std.mem.Allocator,
        identity: []const u8,
    ) (error{OutOfMemory} || std.Io.Cancelable)![]const []const u8 {
        if (self.memberships.get(identity)) |cached| return cached.items;
        const root = self.rootOf(identity) orelse return &.{};

        // Scratch lives in an arena this walk owns and discards, so a
        // cancelled or out-of-memory walk frees itself and publishes nothing.
        var scratch = std.heap.ArenaAllocator.init(gpa);
        defer scratch.deinit();
        const arena = scratch.allocator();

        // `pending` is the queue and its own visited set; `reached` is only
        // what the loader actually vouched for.  Keeping them apart is the
        // point: a document the loader refuses — outside the policy, or not
        // readable — is never counted as belonging to this module, so it can
        // never become a candidate.  Seeding `reached` with the root and
        // trusting it would have made "declared" mean "reached", which is
        // not the same thing once a policy can differ between the scan that
        // recorded a root and the query that asks about it.
        var pending: std.ArrayList([]const u8) = .empty;
        var reached: std.ArrayList([]const u8) = .empty;
        var cursor: usize = 0;
        try pending.append(arena, root);

        while (cursor < pending.items.len) {
            if (pending.items.len >= max_membership_documents) break;
            const current = pending.items[cursor];
            cursor += 1;

            // `false` here means this document is not admitted or not
            // readable.  That is no membership evidence at all, so the walk
            // does not count it and does not follow past it.
            var found: std.ArrayList([]const u8) = .empty;
            if (!try edges.read(edges.ctx, arena, current, &found)) continue;
            try reached.append(arena, current);

            for (found.items) |imported| {
                var already_seen = false;
                for (pending.items) |seen| {
                    if (std.mem.eql(u8, seen, imported)) {
                        already_seen = true;
                        break;
                    }
                }
                if (already_seen) continue;
                try pending.append(arena, imported);
            }
        }

        // The memo outlives the scratch, so the reachable set is copied into
        // the map's own allocator before the arena is discarded.
        const owned = try gpa.alloc([]const u8, reached.items.len);
        errdefer gpa.free(owned);
        for (owned, reached.items) |*slot, path| slot.* = try gpa.dupe(u8, path);
        errdefer for (owned) |path| gpa.free(path);
        // `fromOwnedSlice` takes the slice as it stands: no copy, no second
        // allocation, and `deinit` frees each path and the slice exactly as
        // the loop above expects.
        try self.memberships.put(gpa, identity, .fromOwnedSlice(owned));
        return owned;
    }

    /// Read every `build.zig` that governs `directory`, walking upwards and
    /// stopping at the first directory the source policy rejects.
    ///
    /// Every directory the walk visits is memoized, not just the one it
    /// started from: the whole chain between it and the policy boundary is
    /// read by the time the walk returns, so a later lookup that starts in a
    /// sibling subtree of the same project has nothing left to read.  A walk
    /// cut short by an error commits none of them, because the next caller
    /// has to stay free to finish it.
    ///
    /// That memo is also what lets the walk STOP at a directory it has
    /// already read instead of climbing past it: a directory is only
    /// recorded once its own chain is finished, so every ancestor of a
    /// recorded directory is recorded too and there is nothing above it left
    /// to learn.  Reading the same `build.zig` again for each new
    /// subdirectory is the whole cost this avoids, and nothing about the
    /// answer changes.
    pub fn scanInto(
        self: *NamedModuleMap,
        io: std.Io,
        policy: SourcePolicy,
        directory: []const u8,
    ) (error{OutOfMemory} || std.Io.Cancelable)!void {
        const gpa = self.arena.allocator();

        // `directory` is a directory, not a file path, so the walk starts at
        // the directory itself and then steps to its parent, and so on.  The
        // source policy ends the walk: a directory the policy rejects is not
        // source, and no build file above it describes this source either.
        var visited: std.ArrayListUnmanaged([]const u8) = .empty;
        defer visited.deinit(gpa);
        var dir_path: ?[]const u8 = directory;
        while (dir_path) |dir| : (dir_path = std.fs.path.dirname(dir)) {
            if (self.scanned_dirs.contains(dir)) break;
            if (!policy.allowsAbsolutePath(dir)) break;
            try visited.append(gpa, dir);
            if (!try buildDotZigExists(io, dir)) continue;
            const build_path = try std.Io.Dir.path.join(gpa, &.{ dir, "build.zig" });
            if (!policy.allowsAbsolutePath(build_path)) continue;
            try self.scanBuildZig(io, policy, build_path);
        }
        for (visited.items) |dir| {
            if (self.scanned_dirs.contains(dir)) continue;
            try self.scanned_dirs.put(gpa, try gpa.dupe(u8, dir), {});
        }
    }

    fn scanBuildZig(
        self: *NamedModuleMap,
        io: std.Io,
        policy: SourcePolicy,
        build_path: []const u8,
    ) (error{OutOfMemory} || std.Io.Cancelable)!void {
        const gpa = self.arena.allocator();
        // An unreadable or unparsable build.zig proves nothing.  That is an
        // honest "unknown", not a failure of the analysis itself — including
        // one too wide to read, which says nothing about the wiring either.
        const source = SourcePolicy.readSourceSentinel(io, .cwd(), build_path, gpa) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            // A cancelled read says nothing about the file.  Answering
            // "unknown" here would turn one cancellation into a permanently
            // missing root for every later lookup.
            error.Canceled => return error.Canceled,
            else => return,
        };
        var tree = Ast.parse(gpa, source, .zig) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return,
        };
        defer tree.deinit(gpa);
        if (tree.errors.len != 0) return;
        var scan: BuildModuleScan = .{
            .map = self,
            .gpa = gpa,
            .io = io,
            .tree = &tree,
            .policy = policy,
            .build_dir = std.fs.path.dirname(build_path) orelse return,
            .build_script = build_path,
        };
        try scan.run();
    }

    const BuildModuleScan = struct {
        map: *NamedModuleMap,
        gpa: std.mem.Allocator,
        io: std.Io,
        tree: *const Ast,
        policy: SourcePolicy,
        /// Directory holding the `build.zig` being read; `b.path` is relative to it.
        build_dir: []const u8,
        /// The `build.zig` this scan read.  Part of every instance identity,
        /// so one declaration site always names the same module and two
        /// scripts cannot collide on a declaration ordinal.
        build_script: []const u8,
        /// Declaration ordinal within this script.  Two `addModule` calls
        /// naming one root are two declarations, and this is what tells
        /// their instances apart.
        declared: usize = 0,
        /// Variable name -> the instance its initializer creates, or null
        /// when the name is bound more than once.  Scoped to this one
        /// `build.zig`: the same name in another file is a different name.
        variables: std.StringArrayHashMapUnmanaged(?[]const u8) = .empty,

        /// Call nodes already declared, so the initializer of a binding is
        /// not declared a second time when the node walk reaches that call
        /// on its own.  Without this, one `const left = b.createModule(…)`
        /// would become two modules differing only in identity.
        declared_calls: std.DynamicBitSetUnmanaged = .{},

        /// Two passes, so `module.addImport(...)` is attributed even when it
        /// is written before the `addModule` that creates `module`.
        /// Attribution is the whole point: without it every alias in a build
        /// script would land in one table, and any two of them sharing a name
        /// would collide.
        fn run(scan: *BuildModuleScan) !void {
            try scan.declareModules();
            try scan.recordModuleImports();
            scan.variables.deinit(scan.gpa);
        }

        /// Bind declarations before visiting unbound calls.  The parser stores
        /// an initializer call before the variable declaration that owns it.
        fn declareModules(scan: *BuildModuleScan) !void {
            defer scan.declared_calls.deinit(scan.gpa);
            try scan.declared_calls.resize(scan.gpa, scan.tree.nodes.len, false);
            var index: u32 = 1;
            while (index < scan.tree.nodes.len) : (index += 1) {
                const node: Ast.Node.Index = @enumFromInt(index);
                if (scan.tree.fullVarDecl(node)) |decl| {
                    const initializer = decl.ast.init_node.unwrap() orelse continue;
                    var call_buf: [1]Ast.Node.Index = undefined;
                    const call = scan.tree.fullCall(&call_buf, initializer) orelse continue;
                    if (try scan.declareInstance(call)) |identity| {
                        scan.declared_calls.set(@intFromEnum(initializer));
                        try scan.bindVariable(decl, identity);
                    }
                    continue;
                }
            }
            index = 1;
            while (index < scan.tree.nodes.len) : (index += 1) {
                const node: Ast.Node.Index = @enumFromInt(index);
                _ = try scan.declareInstanceAt(node);
            }
        }

        /// Declares the module `call` creates and returns its identity, or
        /// null when this call is not a literal module declaration.
        fn declareInstance(scan: *BuildModuleScan, call: Ast.full.Call) (error{OutOfMemory} || std.Io.Cancelable)!?[]const u8 {
            const method = callName(scan.tree, call) orelse return null;
            const is_create = std.mem.eql(u8, method, "createModule") and call.ast.params.len == 1;
            const is_add = std.mem.eql(u8, method, "addModule") and call.ast.params.len == 2;
            if (!is_create and !is_add) return null;
            const options = scan.moduleOptions(call) orelse return null;
            const root = try scan.moduleRootFromOptions(options) orelse return null;
            if (!try scan.admit(root)) return null;

            const identity = try scan.nextIdentity(root);
            try scan.map.declareModule(identity, root, if (is_add) stringLiteral(scan.tree, call.ast.params[0]) else null);
            if (is_add) try scan.recordImports(identity, options);
            return identity;
        }

        /// An inline module expression that no variable binds.
        fn declareInstanceAt(scan: *BuildModuleScan, node: Ast.Node.Index) (error{OutOfMemory} || std.Io.Cancelable)!?[]const u8 {
            if (scan.declared_calls.isSet(@intFromEnum(node))) return null;
            var call_buf: [1]Ast.Node.Index = undefined;
            const call = scan.tree.fullCall(&call_buf, node) orelse return null;
            return try scan.declareInstance(call);
        }

        /// A fresh identity for one declaration.  The root alone is not an
        /// identity: the same root declared twice is two modules, and only
        /// the declaration site tells them apart.
        fn nextIdentity(scan: *BuildModuleScan, root: []const u8) error{OutOfMemory}![]const u8 {
            scan.declared += 1;
            return std.fmt.allocPrint(scan.gpa, "{s}#{d}#{s}", .{ scan.build_script, scan.declared, root });
        }

        /// Binds a module variable to the declaration it was assigned, so
        /// `left.addImport(…)` can be attributed to it.  A name bound twice
        /// is shadowed and proves nothing.
        fn bindVariable(scan: *BuildModuleScan, decl: Ast.full.VarDecl, identity: []const u8) !void {
            const name = scan.tree.tokenSlice(decl.ast.mut_token + 1);
            if (scan.variables.get(name) != null) {
                scan.variables.getPtr(name).?.* = null;
                return;
            }
            try scan.variables.put(scan.gpa, name, identity);
        }

        fn recordModuleImports(scan: *BuildModuleScan) !void {
            var index: u32 = 1;
            while (index < scan.tree.nodes.len) : (index += 1) {
                var call_buf: [1]Ast.Node.Index = undefined;
                const call = scan.tree.fullCall(&call_buf, @enumFromInt(index)) orelse continue;
                const method = callName(scan.tree, call) orelse continue;
                if (!std.mem.eql(u8, method, "addImport") or call.ast.params.len != 2) continue;

                // `left.addImport("dep", …)` is a field access whose receiver
                // is the `left` identifier — reading the callee itself as an
                // identifier skips every ordinary method call, which is the
                // only shape a build script writes.
                if (scan.tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
                const receiver_node = scan.tree.nodeData(call.ast.fn_expr).node_and_token[0];
                if (scan.tree.nodeTag(receiver_node) != .identifier) continue;
                const receiver = scan.tree.tokenSlice(scan.tree.nodeMainToken(receiver_node));
                const owner = scan.variables.get(receiver) orelse continue;
                const alias = stringLiteral(scan.tree, call.ast.params[0]) orelse continue;
                const target = try scan.moduleTargetFromExpr(call.ast.params[1]) orelse continue;
                try scan.recordImport(owner orelse continue, alias, target);
            }
        }

        /// A root the policy does not admit, or that is not a readable file
        /// right now, is not a module.  Publishing it would turn an unknown
        /// type into a failed file, which is strictly worse.
        fn admit(scan: *BuildModuleScan, root: []const u8) error{Canceled}!bool {
            if (root.len == 0) return false;
            if (!scan.policy.allowsAbsolutePath(root)) return false;
            std.Io.Dir.cwd().access(scan.io, root, .{}) catch |err| switch (err) {
                error.Canceled => return error.Canceled,
                else => return false,
            };
            return true;
        }

        /// What one module expression names: the declaration it pins to, and
        /// the root behind it.
        const Target = struct {
            /// The instance the expression names, or null when it does not
            /// pin to one declaration.
            identity: ?[]const u8,
            root: []const u8,
        };

        fn moduleTargetFromExpr(scan: *BuildModuleScan, expr: Ast.Node.Index) error{OutOfMemory}!?Target {
            if (scan.tree.nodeTag(expr) == .identifier) {
                const name = scan.tree.tokenSlice(scan.tree.nodeMainToken(expr));
                if (scan.variables.get(name)) |bound| {
                    // A shadowed variable proves nothing, and saying so is
                    // the honest answer rather than picking one binding.
                    const identity = bound orelse return null;
                    const root = scan.map.rootOf(identity) orelse return null;
                    return .{ .identity = identity, .root = root };
                }
            }
            const root = try scan.moduleRootFromExpr(expr) orelse return null;
            // A root exactly one declaration creates can name that
            // declaration.  A root declared more than once cannot: which
            // one the build meant is not something the file says.
            const instances = scan.map.instancesOfRoot(root);
            return .{ .identity = if (instances.len == 1) instances[0] else null, .root = root };
        }

        fn recordImport(scan: *BuildModuleScan, owner: []const u8, alias: []const u8, target: Target) !void {
            if (alias.len == 0) return;
            if (!try scan.admit(target.root)) return;
            try scan.map.recordImport(owner, alias, target.identity);
        }

        /// `.{ .imports = &.{ .{ .name = "alias", .module = <module> }, ... } }`
        fn recordImports(scan: *BuildModuleScan, owner: []const u8, options: Ast.Node.Index) !void {
            var init_buf: [2]Ast.Node.Index = undefined;
            if (scan.tree.fullStructInit(&init_buf, options) == null) return;
            const imports = scan.fieldValue(options, "imports") orelse return;
            const array_node = if (scan.tree.nodeTag(imports) == .address_of)
                scan.tree.nodeData(imports).node
            else
                imports;
            var array_buf: [2]Ast.Node.Index = undefined;
            const array = scan.tree.fullArrayInit(&array_buf, array_node) orelse return;
            for (array.ast.elements) |element| {
                var entry_buf: [2]Ast.Node.Index = undefined;
                if (scan.tree.fullStructInit(&entry_buf, element) == null) continue;
                const name_node = scan.fieldValue(element, "name") orelse continue;
                const name = stringLiteral(scan.tree, name_node) orelse continue;
                const module = scan.fieldValue(element, "module") orelse continue;
                const target = try scan.moduleTargetFromExpr(module) orelse continue;
                try scan.recordImport(owner, name, target);
            }
        }

        /// The options literal a `createModule` / `addModule` call passes,
        /// or null for every other call.  One place decides, so a new
        /// module-constructing call cannot be read one way at declaration
        /// and another at an import site.
        fn moduleOptions(scan: *BuildModuleScan, call: Ast.full.Call) ?Ast.Node.Index {
            const method = callName(scan.tree, call) orelse return null;
            const is_create = std.mem.eql(u8, method, "createModule") and call.ast.params.len == 1;
            const is_add = std.mem.eql(u8, method, "addModule") and call.ast.params.len == 2;
            if (!is_create and !is_add) return null;
            return if (is_create) call.ast.params[0] else call.ast.params[1];
        }

        /// The root source file a module expression names, as an absolute path.
        fn moduleRootFromExpr(scan: *BuildModuleScan, expr: Ast.Node.Index) !?[]const u8 {
            var resolved = expr;
            if (scan.tree.nodeTag(expr) == .identifier) {
                resolved = scan.variableInitializer(expr) orelse return null;
            }
            var call_buf: [1]Ast.Node.Index = undefined;
            const call = scan.tree.fullCall(&call_buf, resolved) orelse return null;
            const options = scan.moduleOptions(call) orelse return null;
            return try scan.moduleRootFromOptions(options);
        }

        /// The `root_source_file` of a `createModule` / `addModule` options literal.
        fn moduleRootFromOptions(scan: *BuildModuleScan, options: Ast.Node.Index) !?[]const u8 {
            const root_source_file = scan.fieldValue(options, "root_source_file") orelse return null;
            const relative = scan.lazyPathText(root_source_file) orelse return null;
            if (relative.len == 0 or std.fs.path.isAbsolute(relative)) return null;
            // `relative` is known to be relative and `build_dir` to be the
            // absolute directory holding this `build.zig`, so the join is
            // the one step that is safe here.  It does not fold: a root that
            // walks back out through a link names the file the kernel
            // resolves it to, and this scan reads that same root back
            // through here, so both sides of every comparison carry `..`.
            return try std.fs.path.join(scan.gpa, &.{ scan.build_dir, relative });
        }

        /// `b.path("src/x.zig")`, `b.pathFromRoot("src/x.zig")`,
        /// `.{ .cwd_relative = "src/x.zig" }` or a bare relative literal.
        fn lazyPathText(scan: *BuildModuleScan, value: Ast.Node.Index) ?[]const u8 {
            var call_buf: [1]Ast.Node.Index = undefined;
            if (scan.tree.fullCall(&call_buf, value)) |call| {
                const method = callName(scan.tree, call) orelse return null;
                if (call.ast.params.len != 1) return null;
                if (!std.mem.eql(u8, method, "path") and !std.mem.eql(u8, method, "pathFromRoot")) return null;
                return stringLiteral(scan.tree, call.ast.params[0]);
            }
            var init_buf: [2]Ast.Node.Index = undefined;
            if (scan.tree.fullStructInit(&init_buf, value) != null) {
                const cwd_relative = scan.fieldValue(value, "cwd_relative") orelse return null;
                return stringLiteral(scan.tree, cwd_relative);
            }
            return stringLiteral(scan.tree, value);
        }

        /// The value node of a `.name = value` struct-init field.
        fn fieldValue(scan: *BuildModuleScan, struct_init: Ast.Node.Index, name: []const u8) ?Ast.Node.Index {
            var init_buf: [2]Ast.Node.Index = undefined;
            const initializer = scan.tree.fullStructInit(&init_buf, struct_init) orelse return null;
            for (initializer.ast.fields) |field| {
                const first = scan.tree.firstToken(field);
                if (first < 2) continue;
                if (!std.mem.eql(u8, scan.tree.tokenSlice(first - 2), name)) continue;
                return field;
            }
            return null;
        }

        /// The single initializer of the variable an identifier names. A name
        /// declared more than once is shadowed, so it proves nothing.
        fn variableInitializer(scan: *BuildModuleScan, identifier: Ast.Node.Index) ?Ast.Node.Index {
            const name = scan.tree.tokenSlice(scan.tree.nodeMainToken(identifier));
            var found: ?Ast.Node.Index = null;
            var index: u32 = 1;
            while (index < scan.tree.nodes.len) : (index += 1) {
                const decl = scan.tree.fullVarDecl(@enumFromInt(index)) orelse continue;
                if (!std.mem.eql(u8, scan.tree.tokenSlice(decl.ast.mut_token + 1), name)) continue;
                if (found != null) return null;
                found = decl.ast.init_node.unwrap();
            }
            return found;
        }
    };
};

fn stringLiteral(tree: *const Ast, node: Ast.Node.Index) ?[]const u8 {
    if (tree.nodeTag(node) != .string_literal) return null;
    const text = tree.tokenSlice(tree.nodeMainToken(node));
    if (text.len < 2 or std.mem.indexOfScalar(u8, text, '\\') != null) return null;
    return text[1 .. text.len - 1];
}

fn callName(tree: *const Ast, call: Ast.full.Call) ?[]const u8 {
    if (tree.nodeTag(call.ast.fn_expr) != .field_access) return null;
    return tree.tokenSlice(tree.nodeData(call.ast.fn_expr).node_and_token[1]);
}

/// looks for a `zls.build.json` file in the build file directory
/// has to be freed with `json_compat.parseFree`
fn loadBuildAssociatedConfiguration(io: std.Io, allocator: std.mem.Allocator, build_file: BuildFile) !std.json.Parsed(BuildAssociatedConfig) {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const build_file_path = try build_file.uri.toFsPath(allocator);
    defer allocator.free(build_file_path);
    const config_file_path = try std.Io.Dir.path.resolve(allocator, &.{ build_file_path, "..", "zls.build.json" });
    defer allocator.free(config_file_path);

    const file_buf = try std.Io.Dir.cwd().readFileAlloc(
        io,
        config_file_path,
        allocator,
        .limited(16 * 1024 * 1024),
    );
    defer allocator.free(file_buf);

    return try std.json.parseFromSlice(
        BuildAssociatedConfig,
        allocator,
        file_buf,
        .{ .ignore_unknown_fields = true, .allocate = .alloc_always },
    );
}

fn prepareBuildRunnerArgs(self: *DocumentStore, build_file_uri: Uri) error{OutOfMemory}![][]const u8 {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const base_args = &[_][]const u8{
        self.config.zig_exe_path.?,
        "build",
        "--build-runner",
        self.config.build_runner_path.?,
        "--zig-lib-dir",
        self.config.zig_lib_dir.?.path orelse ".",
    };

    var args: std.ArrayList([]const u8) = try .initCapacity(self.allocator, base_args.len);
    errdefer {
        for (args.items) |arg| self.allocator.free(arg);
        args.deinit(self.allocator);
    }

    for (base_args) |arg| {
        args.appendAssumeCapacity(try self.allocator.dupe(u8, arg));
    }

    if (self.getBuildFile(build_file_uri)) |build_file| blk: {
        const build_config = build_file.build_associated_config orelse break :blk;
        const build_options = build_config.value.build_options orelse break :blk;

        try args.ensureUnusedCapacity(self.allocator, build_options.len);
        for (build_options) |option| {
            args.appendAssumeCapacity(try option.formatParam(self.allocator));
        }
    }

    return try args.toOwnedSlice(self.allocator);
}

/// Runs the build.zig and extracts include directories and packages
fn loadBuildConfiguration(self: *DocumentStore, build_file_uri: Uri, build_file_version: u32) !std.json.Parsed(BuildConfig) {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    std.debug.assert(self.config.zig_exe_path != null);
    std.debug.assert(self.config.build_runner_path != null);
    std.debug.assert(self.config.global_cache_dir != null);
    std.debug.assert(self.config.zig_lib_dir != null);

    const build_file_path = try build_file_uri.toFsPath(self.allocator);
    defer self.allocator.free(build_file_path);

    const cwd = std.Io.Dir.path.dirname(build_file_path).?;

    const args = try self.prepareBuildRunnerArgs(build_file_uri);
    defer {
        for (args) |arg| self.allocator.free(arg);
        self.allocator.free(args);
    }

    const zig_run_result = blk: {
        const tracy_zone2 = tracy.trace(@src());
        defer tracy_zone2.end();
        break :blk try std.process.run(
            self.allocator,
            self.io,
            .{
                .argv = args,
                .cwd = .{ .path = cwd },
                .stderr_limit = .limited(16 * 1024 * 1024),
                .stdout_limit = .limited(16 * 1024 * 1024),
            },
        );
    };
    defer self.allocator.free(zig_run_result.stdout);
    defer self.allocator.free(zig_run_result.stderr);

    const is_ok = switch (zig_run_result.term) {
        .exited => |exit_code| exit_code == 0,
        else => false,
    };

    const diagnostic_tag: DiagnosticsCollection.Tag = tag: {
        var hasher: std.hash.Wyhash = .init(47); // Chosen by the following prompt: Pwease give a wandom nyumbew
        hasher.update(build_file_uri.raw);
        break :tag @enumFromInt(@as(u32, @truncate(hasher.final())));
    };

    if (!is_ok) {
        const joined = try std.mem.join(self.allocator, " ", args);
        defer self.allocator.free(joined);

        log.err(
            "Failed to execute build runner to collect build configuration, command:\ncd {s};{s}\nError: {s}",
            .{ cwd, joined, zig_run_result.stderr },
        );

        var error_bundle = std.zig.ErrorBundle.empty;
        defer error_bundle.deinit(self.allocator);

        try self.diagnostics_collection.pushErrorBundle(diagnostic_tag, build_file_version, cwd, error_bundle);
        try self.diagnostics_collection.publishDiagnostics();
        return error.RunFailed;
    } else {
        try self.diagnostics_collection.pushErrorBundle(diagnostic_tag, build_file_version, null, .empty);
        try self.diagnostics_collection.publishDiagnostics();
    }

    const parse_options: std.json.ParseOptions = .{
        // We ignore unknown fields so people can roll
        // their own build runners in libraries with
        // the only requirement being general adherence
        // to the BuildConfig type
        .ignore_unknown_fields = true,
        .allocate = .alloc_always,
    };

    return std.json.parseFromSlice(
        BuildConfig,
        self.allocator,
        zig_run_result.stdout,
        parse_options,
    ) catch return error.InvalidBuildConfig;
}

/// Checks if the build.zig file is accessible in dir.
fn buildDotZigExists(io: std.Io, dir_path: []const u8) std.Io.Cancelable!bool {
    var dir = std.Io.Dir.openDirAbsolute(io, dir_path, .{}) catch |err| switch (err) {
        error.Canceled => return error.Canceled,
        else => return false,
    };
    defer dir.close(io);
    dir.access(io, "build.zig", .{}) catch |err| switch (err) {
        error.Canceled => return error.Canceled,
        else => return false,
    };
    return true;
}

/// Walk down the tree towards the uri. When we hit `build.zig` files
/// add them to the list of potential build files.
/// `build.zig` files higher in the filesystem have precedence.
/// See `Handle.getAssociatedBuildFile`.
/// Caller owns returned memory.
fn collectPotentialBuildFiles(self: *DocumentStore, uri: Uri) error{ Canceled, OutOfMemory }![]*BuildFile {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    if (isInStd(uri)) return &.{};

    var potential_build_files: std.ArrayList(*BuildFile) = .empty;
    errdefer potential_build_files.deinit(self.allocator);

    const path = uri.toFsPath(self.allocator) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.UnsupportedScheme => return &.{},
    };
    defer self.allocator.free(path);

    var it = std.Io.Dir.path.componentIterator(path);
    _ = it.last();
    var did_check_root = false;
    while (true) {
        const dir_path = if (it.previous()) |comp| comp.path else blk: {
            if (did_check_root) break :blk null;
            did_check_root = true;
            break :blk it.root();
        } orelse break;
        if (!self.source_policy.allowsAbsolutePath(dir_path)) break;
        if (!try buildDotZigExists(self.io, dir_path)) continue;

        const build_path = try std.Io.Dir.path.join(self.allocator, &.{ dir_path, "build.zig" });
        defer self.allocator.free(build_path);

        try potential_build_files.ensureUnusedCapacity(self.allocator, 1);

        const build_file_uri: Uri = try .fromPath(self.allocator, build_path);
        defer build_file_uri.deinit(self.allocator);

        const build_file = try self.getOrLoadBuildFile(build_file_uri);
        potential_build_files.appendAssumeCapacity(build_file);
    }
    // The potential build files that come first should have higher priority.
    //
    // `build.zig` files that are higher up in the filesystem are more likely
    // to be the `build.zig` of the entire project/package instead of just a
    // sub-project/package.
    std.mem.reverse(*BuildFile, potential_build_files.items);

    return try potential_build_files.toOwnedSlice(self.allocator);
}

fn createBuildFile(self: *DocumentStore, uri: Uri) error{ Canceled, OutOfMemory }!BuildFile {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    var build_file: BuildFile = .{
        .uri = try uri.dupe(self.allocator),
    };

    errdefer build_file.deinit(self.allocator);

    if (loadBuildAssociatedConfiguration(self.io, self.allocator, build_file)) |cfg| {
        build_file.build_associated_config = cfg;

        if (cfg.value.relative_builtin_path) |relative_builtin_path| blk: {
            const build_file_path = build_file.uri.toFsPath(self.allocator) catch break :blk;
            const absolute_builtin_path = try std.Io.Dir.path.resolve(self.allocator, &.{ build_file_path, "..", relative_builtin_path });
            defer self.allocator.free(absolute_builtin_path);
            build_file.builtin_uri = try .fromPath(self.allocator, absolute_builtin_path);
        }
    } else |err| switch (err) {
        error.Canceled => return error.Canceled,
        error.FileNotFound => {},
        else => {
            log.debug("Failed to load config associated with build file {s} (error: {})", .{ build_file.uri.raw, err });
        },
    }

    log.info("Loaded build file '{s}'", .{build_file.uri.raw});

    return build_file;
}

const FileSource = union(enum) {
    text: [:0]const u8,
    /// Must satisfy `uri.isFileScheme()`.
    uri,
};

const CreateAndStoreOptions = struct {
    lsp_synced: bool,
    override: bool,
    load_build_file_behaviour: enum { load_but_dont_update, only_update, never },
};

/// **Thread safe** takes an exclusive lock
fn createAndStoreDocument(
    store: *DocumentStore,
    uri: Uri,
    /// Takes ownership.
    /// `file_source == .text` implies `options.lsp_synced == true`.
    file_source: FileSource,
    options: CreateAndStoreOptions,
) ReadFileError!*SourceDocument {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    std.debug.assert(!(options.lsp_synced and !options.override));
    std.debug.assert(!(options.lsp_synced and file_source == .uri));

    switch (file_source) {
        .text => {},
        .uri => std.debug.assert(uri.isFileScheme()),
    }
    errdefer switch (file_source) {
        .text => |text| store.allocator.free(text),
        .uri => {},
    };

    if (supports_build_system and options.lsp_synced and isBuildFile(uri) and !isInStd(uri)) {
        switch (options.load_build_file_behaviour) {
            .load_but_dont_update => {
                _ = try store.getOrLoadBuildFile(uri);
            },
            .only_update => {
                store.invalidateBuildFile(uri);
            },
            .never => {},
        }
    }

    const document_future: *SourceDocument.Future = document_future: {
        try store.mutex.lock(store.io);
        defer store.mutex.unlock(store.io);

        const gop = try store.documents.getOrPut(store.allocator, uri);

        var previous_err: ?ReadFileError = null;
        if (gop.found_existing) {
            if (gop.value_ptr.*.await(store.io)) |old_document| {
                if (!options.override) return old_document;
                gop.value_ptr.*.event.reset();
            } else |err| {
                const retry = switch (err) {
                    error.Canceled => true,
                    else => file_source == .text,
                };
                if (options.override and !retry) return err;
                previous_err = err;
                // A re-read of an entry whose load failed is the same
                // replacement an override is, and the snapshot that failed
                // load kept is still the one a reader is holding.
                gop.value_ptr.*.event.reset();
            }
        } else {
            errdefer store.documents.swapRemoveAt(gop.index);

            gop.key_ptr.* = try uri.dupe(store.allocator);
            errdefer gop.key_ptr.*.deinit(store.allocator);

            gop.value_ptr.* = try store.allocator.create(SourceDocument.Future);
            errdefer store.allocator.destroy(gop.value_ptr.*);
        }
        if (!gop.found_existing) {
            gop.value_ptr.*.* = .{
                .event = .unset,
                .document = .{
                    .uri = gop.key_ptr.*,
                    .tree = undefined,
                    .file_imports = &.{},
                    .lsp_synced = options.lsp_synced,
                    .impl = .{
                        .store = store,
                        .has_tree_and_source = false,
                    },
                },
                .err = previous_err,
            };
        } else {
            // The document this entry already holds is left exactly where it
            // is.  `SourceDocument.refresh` moves the text, tree, imports and
            // scope a reader already has aside precisely because the
            // replacement has parsed by the time it does so, and this load
            // frees that `old_document` on the way out.  Rebuilding the
            // document here instead drops all of it before the replacement
            // exists: leaked when the load succeeds, and the client's only
            // snapshot lost outright when the load is rejected — which is
            // the one case the surrounding contract promises keeps it.
            gop.value_ptr.*.err = previous_err;
            // These two are answered from the source being replaced, and
            // `refresh` does not move them aside with the rest, so they are
            // released here rather than carried into a snapshot whose text
            // they were never asked about.
            gop.value_ptr.*.document.impl.associated_build_file.deinit(store.allocator);
            gop.value_ptr.*.document.impl.associated_build_file = .init;
            gop.value_ptr.*.document.impl.associated_compilation_units.deinit(store.allocator);
            gop.value_ptr.*.document.impl.associated_compilation_units = .unresolved;
        }
        break :document_future gop.value_ptr.*;
    };
    defer document_future.event.set(store.io);

    // What a reader already has, and what it keeps if this load is
    // rejected.  `SourceDocument.refresh` only moves the previous tree
    // aside once a replacement has parsed, so the snapshot is still
    // intact at the point of failure and has to be *left* intact:
    // dropping it would leak its text, tree and imports, and would dangle
    // every view already handed out for this document.
    const had_snapshot = document_future.document.impl.has_tree_and_source;

    const text: [:0]const u8 = switch (file_source) {
        .text => |text| text,
        .uri => store.readFile(uri) catch |err| {
            const should_log = err != error.Canceled and err != error.FileNotFound and err != error.SourceExcluded;
            if (should_log) log.err("failed to read document '{s}': {}", .{ uri.raw, err });
            if (!had_snapshot) {
                document_future.document.deinit(store.allocator);
                document_future.err = err;
            }
            return err;
        },
    };

    var old_document: SourceDocument = .dead;
    SourceDocument.refresh(
        &document_future.document,
        &old_document,
        text,
        store.allocator,
    ) catch |err| switch (err) {
        error.OutOfMemory => {
            // Propagate allocation failure to the caller that reports it.
            // A rejection leaves the open document exactly as it was; see
            // `refreshLspSyncedDocument`.
            if (!had_snapshot) {
                document_future.document.deinit(store.allocator);
                document_future.err = err;
            }
            return err;
        },
    };
    old_document.deinit(store.allocator);
    document_future.document.lsp_synced = options.lsp_synced;

    document_future.err = null;
    return &document_future.document;
}

/// One resolved import target: the file, and the module it is read in.
///
/// The module travels with the URI because a target is only meaningful in
/// an environment: the same file entered from two modules resolves its own
/// named imports differently.  A caller that keeps only the URI would
/// silently answer for whichever environment happened to be asked first.
pub const ResolvedImport = struct {
    uri: Uri,
    module: ModuleId,
};

pub const UriFromImportStringResult = union(enum) {
    none,
    one: ResolvedImport,
    many: []const ResolvedImport,

    pub fn deinit(result: *UriFromImportStringResult, allocator: std.mem.Allocator) void {
        switch (result.*) {
            .none => {},
            .one => |resolved| resolved.uri.deinit(allocator),
            .many => |resolved| {
                for (resolved) |import| import.uri.deinit(allocator);
                allocator.free(resolved);
            },
        }
    }
};

/// Takes the string inside a `@import()` node (without the quotation marks)
/// and returns the file it names, together with the module that file is to
/// be read in.  Caller owns the returned memory.
pub fn uriFromImportStr(
    self: *DocumentStore,
    allocator: std.mem.Allocator,
    handle: Handle,
    import_str: []const u8,
) error{ Canceled, OutOfMemory, SourceExcluded }!UriFromImportStringResult {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    // A relative import means the same thing in every module: it is
    // resolved against the importing document, and the importing module
    // is inherited unchanged.
    if (std.mem.endsWith(u8, import_str, ".zig") or std.mem.endsWith(u8, import_str, ".zon")) {
        const parsed_uri = handle.document.uri.toStdUri();
        return .{ .one = .{
            .uri = try Uri.resolveImport(allocator, handle.document.uri, parsed_uri, import_str),
            .module = handle.module,
        } };
    }

    // The toolchain is its own proven environment: its wiring is fixed by
    // the compiler this run is pinned to, so `std` and `builtin` share one
    // module rather than pretending to belong to whoever imported them.
    if (std.mem.eql(u8, import_str, "std")) {
        const zig_lib_dir = self.config.zig_lib_dir orelse return .none;

        const std_path = try zig_lib_dir.join(allocator, &.{ "std", "std.zig" });
        defer allocator.free(std_path);

        const module = try self.toolchainModule();
        return .{ .one = .{
            .uri = try .fromPath(allocator, std_path),
            .module = module,
        } };
    }

    if (std.mem.eql(u8, import_str, "builtin")) {
        if (supports_build_system) {
            switch (try handle.document.getAssociatedBuildFile(self)) {
                .none, .unresolved => {},
                .resolved => |resolved| {
                    if (resolved.build_file.builtin_uri) |builtin_uri| {
                        const module = try self.toolchainModule();
                        return .{ .one = .{
                            .uri = try builtin_uri.dupe(allocator),
                            .module = module,
                        } };
                    }
                },
            }
        }
        if (self.config.builtin_path) |builtin_path| {
            const module = try self.toolchainModule();
            return .{ .one = .{
                .uri = try .fromPath(allocator, builtin_path),
                .module = module,
            } };
        }
        return .none;
    }

    if (!supports_build_system) return .none;

    if (std.mem.eql(u8, import_str, "root")) {
        const root_source_files = switch (try handle.document.getAssociatedCompilationUnits(self)) {
            .none, .unresolved => return .none,
            .resolved => |root_source_files| root_source_files,
        };
        var resolved: std.ArrayList(ResolvedImport) = try .initCapacity(allocator, root_source_files.len);
        defer {
            for (resolved.items) |import| import.uri.deinit(allocator);
            resolved.deinit(allocator);
        }
        for (root_source_files) |root_source_file| {
            resolved.appendAssumeCapacity(.{
                .uri = try .fromPath(allocator, root_source_file),
                .module = try self.modules.intern(root_source_file),
            });
        }
        return .{ .many = try resolved.toOwnedSlice(allocator) };
    }

    if (isBuildFile(handle.document.uri)) blk: {
        const build_file = self.getBuildFile(handle.document.uri) orelse break :blk;
        const build_config = build_file.tryLockConfig(self.io) orelse break :blk;
        defer build_file.unlockConfig(self.io);

        if (build_config.dependencies.map.get(import_str)) |path| {
            return .{ .one = .{
                .uri = try .fromPath(allocator, path),
                .module = handle.module,
            } };
        }
        return .none;
    }

    // A real `build.zig` run is authoritative when one is available, because
    // it knows the wiring a build-time condition actually selected.
    switch (try handle.document.getAssociatedBuildFile(self)) {
        .none, .unresolved => {},
        .resolved => |resolved| {
            if (resolved.build_file.tryLockConfig(self.io)) |build_config| {
                defer resolved.build_file.unlockConfig(self.io);
                if (build_config.modules.map.get(resolved.root_source_file)) |module| {
                    if (module.import_table.map.get(import_str)) |imported_root_source_file| {
                        return .{ .one = .{
                            .uri = try .fromPath(allocator, imported_root_source_file),
                            .module = try self.modules.intern(imported_root_source_file),
                        } };
                    }
                }
            }
        },
    }

    if (try self.namedModuleImport(allocator, handle, import_str)) |import| return .{ .one = import };
    return .none;
}

/// The one module the toolchain's own sources are read in, interned from the
/// canonical library root so it is a single identity for the session.
pub fn toolchainModule(self: *DocumentStore) error{OutOfMemory}!ModuleId {
    const root = self.toolchainRoot() orelse return .unscoped;
    return self.modules.intern(root);
}

/// The module a document belongs to, when this session has proven one.
///
/// Membership comes from relative-import reachability, never from a shared
/// directory or file name: the environments are the declared instances
/// whose own roots actually import this document.  Exactly one such
/// instance proves this document is that module's, and its id becomes the
/// document's identity.  Two candidates — a root created twice, or a file
/// reached by two modules — name neither, so the document stays `.unscoped`
/// and each owner reaches it by its own id instead.  No proven member means
/// no module, which is the honest answer for a standalone file.
pub fn moduleForDocument(self: *DocumentStore, uri: Uri) (error{OutOfMemory} || std.Io.Cancelable)!ModuleId {
    const path = uri.toFsPath(self.allocator) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.UnsupportedScheme => return .unscoped,
    };
    defer self.allocator.free(path);
    // No directory means no `build.zig` chain above it, so nothing can
    // declare it a member of anything.
    if (std.fs.path.dirname(path) == null) return .unscoped;
    // `candidateEnvironments` reads the chain that declares the instances
    // it walks, so this asks one question rather than two.
    const candidates = try self.candidateEnvironments(path);
    defer self.allocator.free(candidates);
    if (candidates.len != 1) return .unscoped;
    return self.modules.intern(candidates[0]);
}

/// The worker-owned named-module map.  One store belongs to one session,
/// so this is created on first use rather than behind a lock.
///
/// Published so the one consumer outside this file answers named imports
/// from the SAME wiring this store does.  Two maps reading the same
/// `build.zig` can only agree by accident — whichever scan ran first
/// decides whether an identity is present — and an alias answered from an
/// instance the other map never declared is a missing module.  The bytes
/// belong to the map's arena and outlive the borrow.
pub fn namedModuleMap(self: *DocumentStore) *NamedModuleMap {
    if (self.named_modules) |*existing| return existing;
    self.named_modules = .init(self.allocator);
    return &self.named_modules.?;
}

/// The file the project's own `build.zig` gives to a named import, and the
/// module that file is to be read in.
///
/// This is the fallback for when no build configuration exists, which is the
/// normal state here: zbc never spawns a build runner, because running a
/// project's `build.zig` executes that project's code.  The wiring is read
/// from the file instead, and only a root the source policy already admits
/// is ever published, so this cannot widen what the store may read.
///
/// A *proven* importer is answered from its own module's table and from
/// nowhere else.  An *unproven* one is answered only from the environments
/// that actually import it — every candidate must bind the alias and every
/// candidate must agree on the same declaration.  A candidate that does not
/// bind the name vetoes, because in that environment the name does not
/// exist; a set of candidates that disagrees stays unknown; and a document
/// no module imports resolves nothing, even when exactly one unrelated
/// module in the project spells the alias.  This is the whole of the
/// unscoped contract: never fall back to a root that merely exists.
fn namedModuleImport(
    self: *DocumentStore,
    allocator: std.mem.Allocator,
    handle: Handle,
    import_str: []const u8,
) (error{OutOfMemory} || std.Io.Cancelable)!?ResolvedImport {
    const path = handle.document.uri.toFsPath(allocator) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.UnsupportedScheme => return null,
    };
    defer allocator.free(path);
    // Both routes below read the declaring chain from the file's own
    // directory, so a document with no directory has nothing to read.
    if (std.fs.path.dirname(path) == null) return null;

    const modules = self.namedModuleMap();
    const resolution = if (handle.module != .unscoped) blk: {
        // The reader is a proven member: its own instance's wiring is the
        // only environment this spelling was written in, so it answers on
        // its own and nowhere else.  The chain that declared it is read
        // here rather than assumed from whoever proved the membership:
        // an unscanned table answers nothing, and "nothing" here would be
        // indistinguishable from "this module binds no such alias".
        if (std.fs.path.dirname(path)) |directory| {
            try modules.scanInto(self.io, self.source_policy, directory);
        }
        break :blk modules.lookup(self.modules.key(handle.module), import_str) orelse return null;
    } else blk: {
        const candidates = try self.candidateEnvironments(path);
        defer self.allocator.free(candidates);
        break :blk modules.lookupAgreedAmongAll(candidates, import_str) orelse return null;
    };

    return .{
        .uri = try Uri.fromPath(allocator, resolution.root),
        .module = try self.modules.intern(resolution.identity),
    };
}

// ── Tests ───────────────────────────────────────────────────────

fn testStore(gpa: std.mem.Allocator, io: std.Io, modules: *ModuleRegistry, diagnostics: *DiagnosticsCollection, environ: *std.process.Environ.Map) DocumentStore {
    return .{
        .io = io,
        .allocator = gpa,
        .modules = modules,
        .config = .{
            .environ_map = environ,
            .zig_exe_path = null,
            .zig_lib_dir = null,
            .build_runner_path = null,
            .builtin_path = null,
            .global_cache_dir = null,
            .wasi_preopens = {},
        },
        .diagnostics_collection = diagnostics,
    };
}

/// A rejected refresh leaves the open document exactly as
/// `refreshLspSyncedDocument` promises: `new_text` is released and the
/// document is left untouched, so the snapshot a client already has stays
/// reachable through `getHandle` and keeps the source it had.
///
/// The rejection is provoked by failing one allocation at a time rather than
/// by source text, because the LSP store deliberately retains whatever text a
/// client sends: an unparsable body parses into a tree with errors and is kept,
/// so it never rejects anything.  Allocation failure is the rejection this
/// contract is actually written for, and it is the one the addressable-source
/// check in `parseTree` raises.
fn rejectedRefreshKeepsTheOpenDocument(
    gpa: std.mem.Allocator,
    io: std.Io,
    old_text: []const u8,
    new_text: []const u8,
    initial_lsp_synced: bool,
) !void {
    var environ: std.process.Environ.Map = .init(gpa);
    defer environ.deinit();
    var diagnostics: DiagnosticsCollection = .{ .io = io, .allocator = gpa };
    var modules: ModuleRegistry = .init(gpa);
    defer modules.deinit();
    var store: DocumentStore = testStore(gpa, io, &modules, &diagnostics, &environ);
    defer store.deinit();

    const uri = try Uri.fromPath(gpa, "/project/main.zig");
    defer uri.deinit(gpa);

    try store.openLspSyncedDocument(uri, old_text);
    const opened = store.getHandle(uri, .unscoped) orelse return error.DocumentNotOpened;
    try std.testing.expect(std.mem.eql(u8, old_text, opened.document.tree.source));
    // Filesystem documents start unsynced; both modes own the same snapshot.
    opened.document.lsp_synced = initial_lsp_synced;

    store.refreshLspSyncedDocument(uri, try gpa.dupeSentinel(u8, new_text, 0)) catch |err| {
        try std.testing.expectEqual(error.OutOfMemory, err);
        // Rejected: the document the client already has is still there, still
        // reachable through the store, and still reports the source it had.
        // A store that dropped it would also leak its tree, source and
        // imports, which the testing allocator reports as a second failure.
        const kept = store.getHandle(uri, .unscoped) orelse return error.RejectedRefreshDroppedDocument;
        try std.testing.expect(std.mem.eql(u8, old_text, kept.document.tree.source));
        try std.testing.expectEqual(initial_lsp_synced, kept.document.lsp_synced);
        try std.testing.expectEqual(@as(?anyerror, null), store.failureSnapshot().source_failure);
        return err;
    };

    // Accepted: the store serves the snapshot the client sent.
    const updated = store.getHandle(uri, .unscoped) orelse return error.DocumentDropped;
    try std.testing.expect(std.mem.eql(u8, new_text, updated.document.tree.source));
    try std.testing.expect(updated.document.lsp_synced);
}

test "a rejected LSP refresh keeps the stored document source and original sync mode" {
    for ([_]bool{ false, true }) |initial_lsp_synced| {
        try std.testing.checkAllAllocationFailures(
            std.testing.allocator,
            rejectedRefreshKeepsTheOpenDocument,
            .{
                std.testing.io,
                "pub const value: u8 = 7;\n",
                "pub const value: u8 = 9;\n",
                initial_lsp_synced,
            },
        );
    }
}

// A reader and a writer of the same snapshot must never see one half of a
// newer failure beside the other half of an older one.  The publisher
// holds `mutex` across both fields, and this exercises that against real
// concurrent readers rather than trusting the lock's presence.
test "a published failure is read as one snapshot under concurrency" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var environ: std.process.Environ.Map = .init(gpa);
    defer environ.deinit();
    var diagnostics: DiagnosticsCollection = .{ .io = io, .allocator = gpa };
    var modules: ModuleRegistry = .init(gpa);
    defer modules.deinit();
    var store: DocumentStore = testStore(gpa, io, &modules, &diagnostics, &environ);
    defer store.deinit();

    const Writer = struct {
        fn run(target: *DocumentStore, thread_io: std.Io) void {
            _ = thread_io;
            for (0..512) |round| {
                // Each round publishes ONE consistent snapshot: a syntax
                // failure with its position, or a cleared one with neither
                // half.  Publishing the halves separately is what a reader
                // must never be able to observe.
                if (round % 2 == 0) {
                    target.publishFailure(error.ImportInvalidSyntax, .{
                        .source_path = "/project/broken.zig",
                        .position = .{ .line = 3, .column = 5, .byte = 42 },
                        .reason = "expected_semi_after_decl",
                    });
                } else {
                    target.publishFailure(null, null);
                }
            }
        }
    };
    const Reader = struct {
        fn run(target: *DocumentStore, thread_io: std.Io, observed: *std.atomic.Value(bool)) void {
            _ = thread_io;
            for (0..512) |_| {
                const snapshot = target.failureSnapshot();
                // A syntax failure is always published WITH its position, and
                // a cleared snapshot carries neither half.  Seeing the
                // failure alone, or the position alone, means the reader was
                // handed one field of a newer pair beside one field of an
                // older one.
                const is_syntax = if (snapshot.source_failure) |err|
                    err == error.ImportInvalidSyntax
                else
                    false;
                const only_failure = is_syntax and snapshot.parse_failure == null;
                const only_position = !is_syntax and snapshot.source_failure == null and
                    snapshot.parse_failure != null;
                if (only_failure or only_position) observed.store(true, .release);
            }
        }
    };

    var torn: std.atomic.Value(bool) = .init(false);
    const writer = try std.Thread.spawn(.{}, Writer.run, .{ &store, io });
    const reader = try std.Thread.spawn(.{}, Reader.run, .{ &store, io, &torn });
    writer.join();
    reader.join();
    try std.testing.expect(!torn.load(.acquire));
}

test "an exclusion reports itself instead of another document's published failure" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var environ: std.process.Environ.Map = .init(gpa);
    defer environ.deinit();
    var diagnostics: DiagnosticsCollection = .{ .io = io, .allocator = gpa };
    var modules: ModuleRegistry = .init(gpa);
    defer modules.deinit();
    var store: DocumentStore = testStore(gpa, io, &modules, &diagnostics, &environ);
    defer store.deinit();
    // An empty source scope admits nothing, so every lookup is an exclusion.
    store.source_policy = .{ .roots = &.{} };

    const uri = try Uri.fromPath(gpa, "/elsewhere/other.zig");
    defer uri.deinit(gpa);
    try std.testing.expectError(error.SourceExcluded, store.getOrLoadHandle(uri, .unscoped));
    // The exclusion named itself; it did not publish a cause, so a later
    // reader cannot attribute one to this file.
    try std.testing.expectEqual(@as(?anyerror, null), store.failureSnapshot().source_failure);
}

test "an excluded lookup reports its own error without erasing a malformed source" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var environ: std.process.Environ.Map = .init(gpa);
    defer environ.deinit();
    var diagnostics: DiagnosticsCollection = .{ .io = io, .allocator = gpa };
    var modules: ModuleRegistry = .init(gpa);
    defer modules.deinit();
    var store: DocumentStore = testStore(gpa, io, &modules, &diagnostics, &environ);
    defer store.deinit();
    // An empty source scope admits nothing, so every lookup is an exclusion.
    store.source_policy = .{ .roots = &.{} };

    const broken = try Uri.fromPath(gpa, "/earlier/broken.zig");
    defer broken.deinit(gpa);
    try store.openLspSyncedDocument(broken, "pub const Value = struct { field: ; };\n");
    try std.testing.expect(store.getHandle(broken, .unscoped) == null);
    const previous = store.failureSnapshot();
    try std.testing.expectEqual(@as(?anyerror, error.ImportInvalidSyntax), previous.source_failure);
    try std.testing.expectEqualStrings(broken.raw, previous.parse_failure.?.source_path.?);

    const uri = try Uri.fromPath(gpa, "/elsewhere/other.zig");
    defer uri.deinit(gpa);
    try std.testing.expectError(error.SourceExcluded, store.getOrLoadHandle(uri, .unscoped));

    const current = store.failureSnapshot();
    try std.testing.expectEqual(@as(?anyerror, error.ImportInvalidSyntax), current.source_failure);
    try std.testing.expectEqualStrings(broken.raw, current.parse_failure.?.source_path.?);
}

test "a toolchain alias admits its library but not an escaping library symlink" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.createDir(io, "lib", .default_dir);
    try tmp.dir.writeFile(io, .{ .sub_path = "lib/good.zig", .data = "pub const value = 1;\n" });
    try tmp.dir.writeFile(io, .{ .sub_path = "outside.zig", .data = "pub const secret = 2;\n" });
    try tmp.dir.symLink(io, "lib", "alias", .{ .is_directory = true });
    try tmp.dir.symLink(io, "../outside.zig", "lib/escape.zig", .{});
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const alias = try std.fs.path.join(gpa, &.{ directory, "alias" });
    defer gpa.free(alias);
    var environ: std.process.Environ.Map = .init(gpa);
    defer environ.deinit();
    var diagnostics: DiagnosticsCollection = .{ .io = io, .allocator = gpa };
    var modules: ModuleRegistry = .init(gpa);
    defer modules.deinit();
    var store = testStore(gpa, io, &modules, &diagnostics, &environ);
    defer store.deinit();
    store.source_policy = .{ .roots = &.{} };
    store.config.zig_lib_dir = .{ .path = alias, .handle = .cwd() };
    const good_path = try std.fs.path.join(gpa, &.{ alias, "good.zig" });
    defer gpa.free(good_path);
    const good = try Uri.fromPath(gpa, good_path);
    defer good.deinit(gpa);
    const handle = (try store.getOrLoadHandle(good, .unscoped)) orelse return error.LibraryNotLoaded;
    try std.testing.expectEqualStrings("pub const value = 1;\n", handle.document.tree.source);
    const escape_path = try std.fs.path.join(gpa, &.{ alias, "escape.zig" });
    defer gpa.free(escape_path);
    const escape = try Uri.fromPath(gpa, escape_path);
    defer escape.deinit(gpa);
    try std.testing.expectError(error.SourceExcluded, store.getOrLoadHandle(escape, .unscoped));
}

test "module identities are interned once, never reused, and keep two declarations of one root distinct" {
    const gpa = std.testing.allocator;
    var modules: ModuleRegistry = .init(gpa);
    defer modules.deinit();

    // An absent module is not an entry: it costs nothing and cannot be read
    // back, so `.unscoped` can never be mistaken for a real identity.
    try std.testing.expectEqual(ModuleId.unscoped, modules.intern(""));
    try std.testing.expectEqual(@as(?[]const u8, null), modules.name(.unscoped));
    try std.testing.expectEqualStrings("", modules.key(.unscoped));

    const left = try modules.intern("build.zig#1#/project/left.zig");
    const again = try modules.intern("build.zig#1#/project/left.zig");
    // The same root declared by two different declarations is two modules,
    // even though the file behind both is the same one.
    const second_declaration = try modules.intern("build.zig#2#/project/left.zig");
    try std.testing.expectEqual(left, again);
    try std.testing.expect(left != second_declaration);
    try std.testing.expect(again != second_declaration);

    // Two modules may share a declared label without sharing an identity,
    // and the first proven label wins: a second proves nothing the first did
    // not.
    try modules.setName(left, "shared");
    try modules.setName(second_declaration, "shared");
    try modules.setName(left, "other");
    try std.testing.expectEqualStrings("shared", modules.name(left).?);
    try std.testing.expectEqualStrings("shared", modules.name(second_declaration).?);
}
