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
const SourcePolicy = @import("source_policy.zig").SourcePolicy;

const DocumentStore = @This();

io: std.Io,
allocator: std.mem.Allocator,
source_policy: @import("source_policy.zig").SourcePolicy = .{},
canonical_paths: @import("source_policy.zig").CanonicalPaths = .{},
source_aliases: Uri.ArrayHashMap(Uri) = .empty,
source_failure: ?anyerror = null,
parse_failure: ?@import("source_policy.zig").ParseFailure = null,
/// the DocumentStore assumes that `config` is not modified while calling one of its functions.
config: Config,
mutex: std.Io.Mutex = .init,
wait_group: if (supports_build_system) std.Io.Group else void = if (supports_build_system) .init else {},
handles: Uri.ArrayHashMap(*Handle.Future) = .empty,
build_files: if (supports_build_system) Uri.ArrayHashMap(*BuildFile) else void = if (supports_build_system) .empty else {},
diagnostics_collection: *DiagnosticsCollection,
builds_in_progress: std.atomic.Value(i32) = .init(0),
/// Named-module wiring recovered from `build.zig` without executing it.  No
/// build runner is ever spawned: running a project's `build.zig` runs that
/// project's code, so the wiring is read instead of run and only where the
/// source policy already admits the target file.
named_modules: ?NamedModuleMap = null,
named_modules_mutex: std.Io.Mutex = .init,
lsp_capabilities: struct {
    supports_work_done_progress: bool = false,
    supports_semantic_tokens_refresh: bool = false,
    supports_inlay_hints_refresh: bool = false,
} = .{},

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
    ) error{ Canceled, OutOfMemory }!union(enum) {
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

                const handle = try store.getOrLoadHandle(source_uri) orelse continue;

                try found_uris.ensureUnusedCapacity(arena, handle.file_imports.len);
                for (handle.file_imports) |import_uri| found_uris.putAssumeCapacity(try import_uri.dupe(arena), {});
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

/// Represents a Zig source file.
pub const Handle = struct {
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
        /// The Handle has no associated build file (build.zig).
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
            /// The Handle has no associated build file (build.zig).
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

    /// Returns the associated build file (build.zig) of the handle.
    ///
    /// `DocumentStore.build_files` is guaranteed to contain this Uri.
    /// Uri memory managed by its build_file
    pub fn getAssociatedBuildFile(self: *Handle, document_store: *DocumentStore) error{ Canceled, OutOfMemory }!AssociatedBuildFile {
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
        /// The Handle has no associated compilation unit.
        none,
        /// The associated compilation unit has not been resolved yet.
        unresolved,
        /// The associated compilation unit has been successfully resolved to a list of root module.
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

    /// Returns the root source file of the root module of the given handle. Same as `@import("root")`.
    pub fn getAssociatedCompilationUnits(self: *Handle, document_store: *DocumentStore) error{ Canceled, OutOfMemory }!GetAssociatedCompilationUnitsResult {
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
        handle: *Handle,
        /// Old state will be moved into this handle to be deallocated after returning.
        old_handle: *Handle,
        /// Takes ownership.
        text: [:0]const u8,
        allocator: std.mem.Allocator,
    ) error{OutOfMemory}!void {
        const tracy_zone = tracy.traceNamed(@src(), "Handle.refresh");
        defer tracy_zone.end();

        const mode: Ast.Mode = if (std.mem.eql(u8, std.Io.Dir.path.extension(handle.uri.raw), ".zon")) .zon else .zig;
        var new_tree = try parseTree(allocator, text, mode);
        errdefer new_tree.deinit(allocator);

        var new_file_imports: std.ArrayList(Uri) = .empty;
        errdefer new_file_imports.deinit(allocator);

        try collectImports(
            allocator,
            handle.uri,
            &new_tree,
            &new_file_imports,
        );

        const file_imports = try new_file_imports.toOwnedSlice(allocator);
        errdefer file_imports.deinit(allocator);

        errdefer comptime unreachable;

        if (handle.impl.has_tree_and_source) {
            old_handle.tree = handle.tree;
            old_handle.impl.has_tree_and_source = true;
        }

        handle.tree = new_tree;
        old_handle.file_imports = handle.file_imports;
        handle.file_imports = file_imports;
        handle.impl.has_tree_and_source = true;

        old_handle.document_scope = handle.document_scope;
        handle.document_scope = .unset;
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
    fn requireAddressableSource(source: []const u8) error{OutOfMemory}!void {
        if (source.len >= std.math.maxInt(u32)) return error.OutOfMemory;
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

    /// A handle that can only be deallocated. Keep in sync with `deinit`.
    const dead: Handle = .{
        .uri = undefined,
        .tree = undefined,
        .file_imports = &.{},
        .lsp_synced = undefined,
        .impl = .{
            .store = undefined,
            .has_tree_and_source = false,
        },
    };

    /// Caller must free `Handle.uri` if needed.
    /// Keep in sync with `dead`.
    fn deinit(self: *Handle, allocator: std.mem.Allocator) void {
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
        event: std.Io.Event,
        handle: Handle,
        err: ?ReadFileError,

        pub fn await(f: *Future, io: std.Io) ReadFileError!*Handle {
            try f.event.wait(io);
            return f.err orelse return &f.handle;
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

            pub fn get(lazy: *LazyResource, handle: *Handle) error{OutOfMemory}!*const T {
                const tracy_zone = tracy.traceNamed(@src(), "Lazy(" ++ @typeName(T) ++ ").get");
                defer tracy_zone.end();

                const store = handle.impl.store;
                const io = store.io;

                lazy.mutex.lockUncancelable(io);
                defer lazy.mutex.unlock(io);
                if (lazy.value == null) {
                    lazy.value = try Context.create(handle, store.allocator);
                }
                return &lazy.value.?;
            }

            pub fn getOrNull(lazy: *LazyResource, handle: *Handle) ?*const T {
                const tracy_zone = tracy.traceNamed(@src(), "Lazy(" ++ @typeName(T) ++ ").getOrNull");
                defer tracy_zone.end();

                const store = handle.impl.store;
                const io = store.io;
                handle.impl.lock.lockUncancelable(io);
                defer handle.impl.lock.unlock(io);
                return if (lazy.value) |*value| value else null;
            }

            pub fn getCached(lazy: *LazyResource) *const T {
                return &lazy.value.?;
            }
        };
    }

    const DocumentStoreContext = struct {
        fn create(handle: *Handle, allocator: std.mem.Allocator) error{OutOfMemory}!DocumentScope {
            var document_scope: DocumentScope = try .init(allocator, &handle.tree);
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

pub const HandleIterator = struct {
    store: *DocumentStore,
    i: usize = 0,

    pub fn next(it: *HandleIterator) ?*Handle {
        it.store.mutex.lockUncancelable(it.store.io);
        defer it.store.mutex.unlock(it.store.io);
        while (true) {
            defer it.i += 1;
            switch (std.math.order(it.i, it.store.handles.count())) {
                .lt => {},
                .eq => return null,
                .gt => unreachable, // handle count decreased
            }
            return it.store.handles.values()[it.i].await(it.store.io) catch continue;
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

    for (self.handles.keys(), self.handles.values()) |uri, future| {
        if (future.await(self.io)) |handle| handle.deinit(self.allocator) else |_| {}
        uri.deinit(self.allocator);
        self.allocator.destroy(future);
    }
    self.handles.deinit(self.allocator);
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

/// Returns a handle to the given document
/// **Thread safe** takes a shared lock
/// This function does not protect against data races from modifying the Handle
pub fn getHandle(self: *DocumentStore, uri: Uri) ?*Handle {
    const future = future: {
        self.mutex.lockUncancelable(self.io);
        defer self.mutex.unlock(self.io);
        break :future self.handles.get(self.source_aliases.get(uri) orelse uri) orelse return null;
    };
    const handle = future.await(self.io) catch |err| {
        if (err != error.SourceExcluded) {
            self.source_failure = err;
            self.parse_failure = null;
        }
        return null;
    };
    if (handle.tree.errors.len != 0) {
        self.source_failure = error.ImportInvalidSyntax;
        self.parse_failure = .fromTree(handle.uri.raw, &handle.tree);
        return null;
    }
    return handle;
}

const ReadFileError = std.mem.Allocator.Error || std.Io.Cancelable || std.Io.File.OpenError ||
    std.Io.File.Reader.Error || std.Io.Dir.RealPathFileError || error{ StreamTooLong, SourceExcluded };

/// Must satisfy `uri.isFileScheme()`.
fn readFile(self: *DocumentStore, uri: Uri) ReadFileError![:0]u8 {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    const file_path = uri.toFsPath(self.allocator) catch |err| switch (err) {
        error.UnsupportedScheme => unreachable,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer self.allocator.free(file_path);
    if (!self.allowsSource(file_path)) return error.SourceExcluded;
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

    return try dir.readFileAllocOptions(
        self.io,
        sub_path,
        self.allocator,
        .limited(@import("source_policy.zig").SourcePolicy.max_source_bytes),
        .of(u8),
        0,
    );
}

fn allowsSource(self: *const DocumentStore, path: []const u8) bool {
    if (self.source_policy.allowsAbsolutePath(path)) return true;
    const zig_lib = self.config.zig_lib_dir orelse return false;
    const root = zig_lib.path orelse return false;
    return @import("source_policy.zig").within(root, path);
}

fn canonicalUri(self: *DocumentStore, uri: Uri) ReadFileError!Uri {
    const path = uri.toFsPath(self.allocator) catch |err| switch (err) {
        error.UnsupportedScheme => unreachable,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer self.allocator.free(path);
    if (!self.allowsSource(path)) return error.SourceExcluded;
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

fn loadFailed(self: *DocumentStore, err: ReadFileError) error{ Canceled, OutOfMemory }!?*Handle {
    switch (err) {
        error.Canceled, error.OutOfMemory => |e| return e,
        error.SourceExcluded => return null,
        else => {
            self.source_failure = err;
            self.parse_failure = null;
            return null;
        },
    }
}

/// Returns a handle to the given document
/// Will load the document from disk if it hasn't been already
/// **Thread safe** takes an exclusive lock
/// This function does not protect against data races from modifying the Handle
pub fn getOrLoadHandle(self: *DocumentStore, uri: Uri) error{ Canceled, OutOfMemory }!?*Handle {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    if (!uri.isFileScheme()) return self.getHandle(uri);
    const known_uri, const cached = known: {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        const known = self.source_aliases.get(uri) orelse uri;
        break :known .{ known, self.handles.contains(known) };
    };
    const canonical: ?Uri = if (cached) null else self.canonicalUri(known_uri) catch |err| return self.loadFailed(err);
    defer if (canonical) |value| value.deinit(self.allocator);
    const handle = self.createAndStoreDocument(
        canonical orelse known_uri,
        .uri,
        .{
            .lsp_synced = false,
            .override = false,
            .load_build_file_behaviour = .never,
        },
    ) catch |err| return self.loadFailed(err);
    try self.rememberSourceAlias(uri, handle.uri);
    if (handle.tree.errors.len != 0) {
        self.source_failure = error.ImportInvalidSyntax;
        self.parse_failure = .fromTree(handle.uri.raw, &handle.tree);
        return null;
    }
    return handle;
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

    if (self.getHandle(uri)) |handle| {
        if (handle.lsp_synced) {
            log.warn("Document already open: {s}", .{uri.raw});
        }
    }

    // Client text is not capped by `SourcePolicy` the way file reads are,
    // so reject a source the engine cannot address before it is copied.
    try Handle.requireAddressableSource(text);

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

    const handle_index = self.handles.getIndex(uri) orelse {
        log.warn("Document not found: {s}", .{uri.raw});
        return;
    };
    defer self.handles.swapRemoveAt(handle_index);

    const handle_uri = self.handles.keys()[handle_index];
    defer handle_uri.deinit(self.allocator);

    const handle_future = self.handles.values()[handle_index];
    defer self.allocator.destroy(handle_future);

    if (handle_future.await(self.io)) |handle| {
        if (!handle.lsp_synced) {
            log.warn("Document already closed: {s}", .{uri.raw});
        }
        handle.deinit(self.allocator);
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

    if (self.getHandle(uri)) |old_handle| {
        if (!old_handle.lsp_synced) {
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
        const index = self.handles.getIndex(uri) orelse return false;
        const handle_future = self.handles.values()[index];
        const handle = handle_future.await(self.io) catch return false;
        if (handle.lsp_synced) return false;
        self.handles.swapRemoveAt(index);
        handle.uri.deinit(self.allocator);
        handle.deinit(self.allocator);
        self.allocator.destroy(handle_future);
    } else {
        if (self.getHandle(uri)) |handle| {
            if (handle.lsp_synced) return false;
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

/// Named-module wiring recovered from the `build.zig` files that govern a
/// source tree, without executing any of them.
///
/// Only unique, explicit wiring is evidence: a literal `addModule` /
/// `createModule` `root_source_file` reached through a literal `.imports`
/// entry or a literal `addImport` alias.  Everything else stays unresolved on
/// purpose, because a wrong root is worse than no root — an unknown module
/// yields an unknown type, a guessed one yields a wrong type:
///   * a generated module (`b.addOptions().createModule()`) has no path in
///     the source tree;
///   * `dep.module("name")` is wired by the *dependency's* build.zig, which
///     the source policy does not admit;
///   * a module chosen by a runtime condition, a computed path, or a shadowed
///     module variable is not proof of anything;
///   * a name wired to two different roots is ambiguous, so it stays unknown;
///   * a root that is not a readable file right now (a path a build step would
///     still have to write) is not a source, so it stays unknown.
///
/// Every recorded root passes the caller's source policy and exists on disk,
/// so publishing wiring never widens which files the store may read and never
/// turns an unknown type into a failed file.
pub const NamedModuleMap = struct {
    gpa: std.mem.Allocator,
    /// Owns every recorded name and root; released as one block.
    arena: std.heap.ArenaAllocator,
    /// import name -> root source file, or null when the name is ambiguous.
    entries: std.StringArrayHashMapUnmanaged(?[]const u8) = .empty,
    /// Directories whose `build.zig` chain has already been read.
    scanned_dirs: std.StringArrayHashMapUnmanaged(void) = .empty,

    pub fn init(gpa: std.mem.Allocator) NamedModuleMap {
        return .{ .gpa = gpa, .arena = .init(gpa) };
    }

    pub fn deinit(self: *NamedModuleMap) void {
        self.arena.deinit();
        self.* = undefined;
    }

    /// The root source file proven for `name`, or null when the name is
    /// unknown, ambiguous, or not yet scanned.
    pub fn lookup(self: *const NamedModuleMap, name: []const u8) ?[]const u8 {
        return self.entries.get(name) orelse null;
    }

    fn put(self: *NamedModuleMap, name: []const u8, root_source_file: []const u8) !void {
        if (self.entries.get(name)) |known| {
            const previous = known orelse return;
            if (!std.mem.eql(u8, previous, root_source_file)) self.entries.getPtr(name).?.* = null;
            return;
        }
        const gpa = self.arena.allocator();
        try self.entries.put(gpa, try gpa.dupe(u8, name), try gpa.dupe(u8, root_source_file));
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
    pub fn scanInto(
        self: *NamedModuleMap,
        io: std.Io,
        policy: SourcePolicy,
        directory: []const u8,
    ) (error{OutOfMemory} || std.Io.Cancelable)!void {
        const gpa = self.arena.allocator();
        if (self.scanned_dirs.contains(directory)) return;

        // `directory` is a directory, not a file path, so the walk starts at
        // the directory itself and then steps to its parent, and so on.  The
        // source policy ends the walk: a directory the policy rejects is not
        // source, and no build file above it describes this source either.
        var visited: std.ArrayListUnmanaged([]const u8) = .empty;
        defer visited.deinit(gpa);
        var dir_path: ?[]const u8 = directory;
        while (dir_path) |dir| : (dir_path = std.fs.path.dirname(dir)) {
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
        // honest "unknown", not a failure of the analysis itself.
        const source = std.Io.Dir.cwd().readFileAllocOptions(
            io,
            build_path,
            gpa,
            .limited(SourcePolicy.max_source_bytes),
            .of(u8),
            0,
        ) catch |err| switch (err) {
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

        /// Every module expression in a build.zig is either an inline call or a
        /// variable bound to one, so one pass over the nodes sees all wiring.
        fn run(scan: *BuildModuleScan) !void {
            var index: u32 = 1;
            while (index < scan.tree.nodes.len) : (index += 1) {
                var call_buf: [1]Ast.Node.Index = undefined;
                const call = scan.tree.fullCall(&call_buf, @enumFromInt(index)) orelse continue;
                const method = callName(scan.tree, call) orelse continue;
                if (std.mem.eql(u8, method, "addModule") and call.ast.params.len == 2) {
                    // A module with an unprovable root can still name provable
                    // imports, so the import table is read either way.
                    try scan.recordImports(call.ast.params[1]);
                    const name = stringLiteral(scan.tree, call.ast.params[0]) orelse continue;
                    const root = try scan.moduleRootFromOptions(call.ast.params[1]) orelse continue;
                    try scan.record(name, root);
                } else if (std.mem.eql(u8, method, "createModule") and call.ast.params.len == 1) {
                    try scan.recordImports(call.ast.params[0]);
                } else if (std.mem.eql(u8, method, "addImport") and call.ast.params.len == 2) {
                    const name = stringLiteral(scan.tree, call.ast.params[0]) orelse continue;
                    const root = try scan.moduleRootFromExpr(call.ast.params[1]) orelse continue;
                    try scan.record(name, root);
                }
            }
        }

        fn record(scan: *BuildModuleScan, name: []const u8, root_source_file: []const u8) !void {
            if (name.len == 0) return;
            if (!scan.policy.allowsAbsolutePath(root_source_file)) return;
            // A path a previous build step would have generated is real build
            // metadata but not a readable source.  Publishing it would turn an
            // unknown type into a failed file, which is strictly worse.
            std.Io.Dir.cwd().access(scan.io, root_source_file, .{}) catch |err| switch (err) {
                error.Canceled => return error.Canceled,
                else => return,
            };
            try scan.map.put(name, root_source_file);
        }

        /// `.{ .imports = &.{ .{ .name = "alias", .module = <module> }, ... } }`
        fn recordImports(scan: *BuildModuleScan, options: Ast.Node.Index) !void {
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
                const root = try scan.moduleRootFromExpr(module) orelse continue;
                try scan.record(name, root);
            }
        }

        /// The root source file a module expression names, as an absolute path.
        fn moduleRootFromExpr(scan: *BuildModuleScan, expr: Ast.Node.Index) !?[]const u8 {
            const options = scan.moduleOptions(expr) orelse return null;
            return try scan.moduleRootFromOptions(options);
        }

        /// The options literal a `createModule` / `addModule` expression passes,
        /// or null for every other expression.
        fn moduleOptions(scan: *BuildModuleScan, expr: Ast.Node.Index) ?Ast.Node.Index {
            var resolved = expr;
            if (scan.tree.nodeTag(expr) == .identifier) {
                resolved = scan.variableInitializer(expr) orelse return null;
            }
            var call_buf: [1]Ast.Node.Index = undefined;
            const call = scan.tree.fullCall(&call_buf, resolved) orelse return null;
            const method = callName(scan.tree, call) orelse return null;
            if (std.mem.eql(u8, method, "createModule") and call.ast.params.len == 1) return call.ast.params[0];
            if (std.mem.eql(u8, method, "addModule") and call.ast.params.len == 2) return call.ast.params[1];
            return null;
        }

        /// The `root_source_file` of a `createModule` / `addModule` options literal.
        fn moduleRootFromOptions(scan: *BuildModuleScan, options: Ast.Node.Index) !?[]const u8 {
            const root_source_file = scan.fieldValue(options, "root_source_file") orelse return null;
            const relative = scan.lazyPathText(root_source_file) orelse return null;
            if (relative.len == 0 or std.fs.path.isAbsolute(relative)) return null;
            return try std.fs.path.resolve(scan.gpa, &.{ scan.build_dir, relative });
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
) ReadFileError!*Handle {
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

    const handle_future: *Handle.Future = handle_future: {
        try store.mutex.lock(store.io);
        defer store.mutex.unlock(store.io);

        const gop = try store.handles.getOrPut(store.allocator, uri);

        var previous_err: ?ReadFileError = null;
        if (gop.found_existing) {
            if (gop.value_ptr.*.await(store.io)) |old_handle| {
                if (!options.override) return old_handle;
                gop.value_ptr.*.event.reset();
                old_handle.lsp_synced = options.lsp_synced;
                break :handle_future gop.value_ptr.*;
            } else |err| {
                const retry = switch (err) {
                    error.Canceled => true,
                    else => file_source == .text,
                };
                if (options.override and !retry) return err;
                previous_err = err;
            }
        } else {
            errdefer store.handles.swapRemoveAt(gop.index);

            gop.key_ptr.* = try uri.dupe(store.allocator);
            errdefer gop.key_ptr.*.deinit(store.allocator);

            gop.value_ptr.* = try store.allocator.create(Handle.Future);
            errdefer store.allocator.destroy(gop.value_ptr.*);
        }
        gop.value_ptr.*.* = .{
            .event = .unset,
            .handle = .{
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
        break :handle_future gop.value_ptr.*;
    };
    defer handle_future.event.set(store.io);

    const text: [:0]const u8 = switch (file_source) {
        .text => |text| text,
        .uri => store.readFile(uri) catch |err| {
            const should_log = err != error.Canceled and err != error.FileNotFound and err != error.SourceExcluded;
            if (should_log) log.err("failed to read document '{s}': {}", .{ uri.raw, err });
            handle_future.handle = undefined;
            handle_future.err = err;
            return err;
        },
    };

    var old_handle: Handle = .dead;
    Handle.refresh(
        &handle_future.handle,
        &old_handle,
        text,
        store.allocator,
    ) catch |err| switch (err) {
        error.OutOfMemory => {
            log.err("failed to read document '{s}': {}", .{ uri.raw, err });
            handle_future.handle = undefined;
            handle_future.err = err;
            return err;
        },
    };
    old_handle.deinit(store.allocator);

    handle_future.err = null;
    return &handle_future.handle;
}

pub const UriFromImportStringResult = union(enum) {
    none,
    one: Uri,
    many: []const Uri,

    pub fn deinit(result: *UriFromImportStringResult, allocator: std.mem.Allocator) void {
        switch (result.*) {
            .none => {},
            .one => |uri| uri.deinit(allocator),
            .many => |uris| {
                for (uris) |uri| uri.deinit(allocator);
                allocator.free(uris);
            },
        }
    }
};

/// takes the string inside a @import() node (without the quotation marks)
/// and returns it's uri
/// caller owns the returned memory
/// **Thread safe** takes a shared lock
pub fn uriFromImportStr(
    self: *DocumentStore,
    allocator: std.mem.Allocator,
    handle: *Handle,
    import_str: []const u8,
) error{ Canceled, OutOfMemory }!UriFromImportStringResult {
    const tracy_zone = tracy.trace(@src());
    defer tracy_zone.end();

    if (std.mem.endsWith(u8, import_str, ".zig") or std.mem.endsWith(u8, import_str, ".zon")) {
        const parsed_uri = handle.uri.toStdUri();
        return .{ .one = try Uri.resolveImport(allocator, handle.uri, parsed_uri, import_str) };
    }

    if (std.mem.eql(u8, import_str, "std")) {
        const zig_lib_dir = self.config.zig_lib_dir orelse return .none;

        const std_path = try zig_lib_dir.join(allocator, &.{ "std", "std.zig" });
        defer allocator.free(std_path);

        return .{ .one = try .fromPath(allocator, std_path) };
    }

    if (std.mem.eql(u8, import_str, "builtin")) {
        if (supports_build_system) {
            switch (try handle.getAssociatedBuildFile(self)) {
                .none, .unresolved => {},
                .resolved => |resolved| {
                    if (resolved.build_file.builtin_uri) |builtin_uri| {
                        return .{ .one = try builtin_uri.dupe(allocator) };
                    }
                },
            }
        }
        if (self.config.builtin_path) |builtin_path| {
            return .{ .one = try .fromPath(allocator, builtin_path) };
        }
        return .none;
    }

    if (!supports_build_system) return .none;

    if (std.mem.eql(u8, import_str, "root")) {
        const root_source_files = switch (try handle.getAssociatedCompilationUnits(self)) {
            .none, .unresolved => return .none,
            .resolved => |root_source_files| root_source_files,
        };
        var uris: std.ArrayList(Uri) = try .initCapacity(allocator, root_source_files.len);
        defer {
            for (uris.items) |uri| uri.deinit(allocator);
            uris.deinit(allocator);
        }
        for (root_source_files) |root_source_file| {
            uris.appendAssumeCapacity(try .fromPath(allocator, root_source_file));
        }
        return .{ .many = try uris.toOwnedSlice(allocator) };
    }

    if (isBuildFile(handle.uri)) blk: {
        const build_file = self.getBuildFile(handle.uri) orelse break :blk;
        const build_config = build_file.tryLockConfig(self.io) orelse break :blk;
        defer build_file.unlockConfig(self.io);

        if (build_config.dependencies.map.get(import_str)) |path| {
            return .{ .one = try .fromPath(allocator, path) };
        }
        return .none;
    }

    // A real `build.zig` run is authoritative when one is available, because
    // it knows the wiring a build-time condition actually selected.
    switch (try handle.getAssociatedBuildFile(self)) {
        .none, .unresolved => {},
        .resolved => |resolved| {
            if (resolved.build_file.tryLockConfig(self.io)) |build_config| {
                defer resolved.build_file.unlockConfig(self.io);
                if (build_config.modules.map.get(resolved.root_source_file)) |module| {
                    if (module.import_table.map.get(import_str)) |imported_root_source_file| {
                        return .{ .one = try .fromPath(allocator, imported_root_source_file) };
                    }
                }
            }
        },
    }

    if (try self.namedModuleUri(allocator, handle, import_str)) |uri| return .{ .one = uri };
    return .none;
}

/// The root source file the project's own `build.zig` gives to a named import.
///
/// This is the fallback for when no build configuration exists, which is the
/// normal state here: zbc never spawns a build runner, because running a
/// project's `build.zig` executes that project's code.  The wiring is read
/// from the file instead, and only a root the source policy already admits is
/// ever published, so this cannot widen what the store may read.
fn namedModuleUri(
    self: *DocumentStore,
    allocator: std.mem.Allocator,
    handle: *const Handle,
    import_str: []const u8,
) (error{OutOfMemory} || std.Io.Cancelable)!?Uri {
    const path = handle.uri.toFsPath(allocator) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.UnsupportedScheme => return null,
    };
    defer allocator.free(path);
    const directory = std.fs.path.dirname(path) orelse return null;

    try self.named_modules_mutex.lock(self.io);
    defer self.named_modules_mutex.unlock(self.io);
    const modules = if (self.named_modules) |*existing| existing else blk: {
        self.named_modules = .init(self.allocator);
        break :blk &self.named_modules.?;
    };
    try modules.scanInto(self.io, self.source_policy, directory);
    const root_source_file = modules.lookup(import_str) orelse return null;
    return try Uri.fromPath(allocator, root_source_file);
}
