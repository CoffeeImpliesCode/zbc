//! Canonical, policy-admitted source models for one analysis snapshot.
//! Session models borrow the type engine's original AST pool. Standalone
//! models own their source and tree. Source text is never rewritten.
const std = @import("std");
const Ast = std.zig.Ast;
const engine = @import("type_engine");
const model_mod = @import("../model/file_model.zig");
const SourcePolicy = engine.SourcePolicy;
const ParseFailure = engine.ParseFailure;

pub const ProjectCache = struct {
    gpa: std.mem.Allocator,
    io: std.Io,
    policy: SourcePolicy,
    type_context: ?*engine.TypeContext = null,
    canonical_paths: engine.CanonicalPaths = .{},
    modules: engine.NamedModuleMap,
    entries: std.StringHashMapUnmanaged(*Entry) = .empty,
    failure: ?anyerror = null,
    parse_failure: ?ParseFailure = null,
    /// Distinct (importing file, import string) pairs for which no admitted
    /// target was proved. Toolchain names (`std`, `builtin`) are not project
    /// lookups and never count; a pair counts once however often it is asked.
    unresolved_imports: usize = 0,
    /// Keys of the pairs already counted: `from ++ "\x00" ++ import string`.
    unresolved_seen: std.StringHashMapUnmanaged(void) = .empty,

    pub const Entry = struct {
        abs_path: []const u8,
        source: ?[:0]u8 = null,
        owned_tree: ?Ast = null,
        tree: *const Ast,
        model: model_mod.FileModel,
    };

    pub fn init(gpa: std.mem.Allocator, io: std.Io, policy: SourcePolicy) ProjectCache {
        return .{ .gpa = gpa, .io = io, .policy = policy, .modules = .init(gpa) };
    }

    pub fn deinit(self: *ProjectCache) void {
        var values = self.entries.valueIterator();
        while (values.next()) |value| {
            const entry = value.*;
            entry.model.deinit();
            if (entry.owned_tree) |*tree| tree.deinit(self.gpa);
            if (entry.source) |source| self.gpa.free(source);
            self.gpa.destroy(entry);
        }
        self.entries.deinit(self.gpa);
        var seen = self.unresolved_seen.keyIterator();
        while (seen.next()) |key| self.gpa.free(key.*);
        self.unresolved_seen.deinit(self.gpa);
        self.modules.deinit();
        self.canonical_paths.deinit(self.gpa);
        self.* = undefined;
    }

    /// Borrow from exactly one canonical-path owner, never a map copy.
    pub fn sourcePath(self: *ProjectCache, path: []const u8) ![]const u8 {
        if (self.policy.excludesPath(path)) return error.SourceExcluded;
        const paths = if (self.type_context) |context| &context.store.canonical_paths else &self.canonical_paths;
        const canonical = try paths.resolve(self.gpa, self.io, path);
        if (!self.policy.allowsAbsolutePath(canonical)) return error.SourceExcluded;
        return canonical;
    }

    fn publishFailure(self: *ProjectCache, cause: anyerror, position: ?ParseFailure) void {
        if (self.failure != null) return;
        self.failure = cause;
        self.parse_failure = position;
    }

    pub fn modelForPath(self: *ProjectCache, path: []const u8) !?*const model_mod.FileModel {
        const canonical = self.sourcePath(path) catch |err| switch (err) {
            error.SourceExcluded, error.FileNotFound, error.NotDir => return null,
            else => {
                self.publishFailure(err, null);
                return err;
            },
        };
        if (std.mem.endsWith(u8, canonical, ".zon")) return null;
        if (self.entries.get(canonical)) |entry| return &entry.model;
        const entry = try self.gpa.create(Entry);
        errdefer self.gpa.destroy(entry);
        entry.* = .{ .abs_path = canonical, .tree = undefined, .model = undefined };
        errdefer {
            if (entry.owned_tree) |*tree| tree.deinit(self.gpa);
            if (entry.source) |source| self.gpa.free(source);
        }
        if (self.type_context) |context| {
            const uri = try engine.Uri.fromPath(self.gpa, canonical);
            defer uri.deinit(self.gpa);
            const handle = context.store.getOrLoadHandle(uri, .unscoped) catch |err| {
                self.publishFailure(err, null);
                return err;
            } orelse {
                const snapshot = context.store.failureSnapshot();
                if (snapshot.source_failure) |cause| {
                    self.publishFailure(cause, snapshot.parse_failure);
                    return cause;
                }
                self.gpa.destroy(entry);
                return null;
            };
            entry.tree = &handle.document.tree;
        } else {
            entry.source = SourcePolicy.readSourceSentinel(self.io, .cwd(), canonical, self.gpa) catch |err| switch (err) {
                error.FileNotFound, error.NotDir => {
                    self.gpa.destroy(entry);
                    return null;
                },
                else => {
                    self.publishFailure(err, null);
                    return err;
                },
            };
            entry.owned_tree = try Ast.parse(self.gpa, entry.source.?, .zig);
            entry.tree = &entry.owned_tree.?;
        }
        if (entry.tree.errors.len != 0) {
            self.publishFailure(error.ImportInvalidSyntax, .fromTree(canonical, entry.tree));
            return error.ImportInvalidSyntax;
        }
        entry.model = try model_mod.buildWithPath(self.gpa, entry.tree, canonical);
        errdefer entry.model.deinit();
        try self.entries.put(self.gpa, canonical, entry);
        return &entry.model;
    }

    pub fn treeForPath(self: *ProjectCache, path: []const u8) !?*const Ast {
        const model = (try self.modelForPath(path)) orelse return null;
        return model.tree;
    }

    pub fn modelForRelativeImport(self: *ProjectCache, from_file_path: []const u8, import_str: []const u8) !?*const model_mod.FileModel {
        if (!isRelativeImport(import_str)) return null;
        const from = self.sourcePath(from_file_path) catch |err| switch (err) {
            error.SourceExcluded, error.FileNotFound, error.NotDir => return null,
            else => return err,
        };
        const dir = std.fs.path.dirname(from) orelse return null;
        const joined = try std.fs.path.join(self.gpa, &.{ dir, import_str });
        defer self.gpa.free(joined);
        // The kernel resolves symlinks before '..'; lexical folding changes identity.
        return self.importModel(joined, from, import_str);
    }

    pub fn modelForModuleImport(self: *ProjectCache, from_file_path: []const u8, module_name: []const u8) !?*const model_mod.FileModel {
        if (module_name.len == 0 or std.mem.indexOfAny(u8, module_name, "/\\.\x00") != null) return null;
        // The toolchain owns `std` and `builtin`; the session reads them through
        // the type engine, never as project sources, so they are not lookups
        // this cache can fail.
        if (isToolchainImport(module_name)) return null;
        const from = self.sourcePath(from_file_path) catch |err| switch (err) {
            error.SourceExcluded, error.FileNotFound, error.NotDir => return null,
            else => return err,
        };
        if (self.type_context) |context| {
            const candidates = try context.store.candidateEnvironments(from);
            defer self.gpa.free(candidates);
            const target = context.store.namedModuleMap().lookupAgreedAmongAll(candidates, module_name) orelse {
                try self.noteUnresolved(from, module_name);
                return null;
            };
            return self.importModel(target.root, from, module_name);
        }
        try self.modules.scanInto(self.io, self.policy, std.fs.path.dirname(from) orelse return null);
        const candidates = try self.modules.candidateEnvironments(.{ .ctx = self, .read = readEdges }, self.gpa, from);
        defer self.gpa.free(candidates);
        const target = self.modules.lookupAgreedAmongAll(candidates, module_name) orelse {
            try self.noteUnresolved(from, module_name);
            return null;
        };
        return self.importModel(target.root, from, module_name);
    }

    fn importModel(self: *ProjectCache, path: []const u8, from: []const u8, import_str: []const u8) !?*const model_mod.FileModel {
        const model = try self.modelForPath(path);
        // ZON is data: it never becomes a declaration model, so it is not a
        // lookup that failed.
        if (model == null and !std.mem.endsWith(u8, path, ".zon")) try self.noteUnresolved(from, import_str);
        return model;
    }

    /// Count one (importing file, import string) pair, once.
    fn noteUnresolved(self: *ProjectCache, from: []const u8, import_str: []const u8) std.mem.Allocator.Error!void {
        const key = try self.gpa.alloc(u8, from.len + 1 + import_str.len);
        @memcpy(key[0..from.len], from);
        key[from.len] = 0;
        @memcpy(key[from.len + 1 ..], import_str);
        const slot = self.unresolved_seen.getOrPut(self.gpa, key) catch |err| {
            self.gpa.free(key);
            return err;
        };
        if (slot.found_existing) {
            self.gpa.free(key);
            return;
        }
        self.unresolved_imports += 1;
    }

    fn readEdges(ctx: *const anyopaque, arena: std.mem.Allocator, path: []const u8, edges: *std.ArrayList([]const u8)) (error{OutOfMemory} || std.Io.Cancelable)!bool {
        const self: *ProjectCache = @ptrCast(@alignCast(@constCast(ctx)));
        const model = self.modelForPath(path) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Canceled => return error.Canceled,
            else => return false,
        } orelse return false;
        const dir = std.fs.path.dirname(path) orelse return false;
        for (model.relative_imports) |imported| {
            const joined = try std.fs.path.join(arena, &.{ dir, imported });
            const canonical = self.sourcePath(joined) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Canceled => return error.Canceled,
                else => continue,
            };
            try edges.append(arena, canonical);
        }
        return true;
    }
};

pub fn isRelativeImport(import_str: []const u8) bool {
    return std.mem.endsWith(u8, import_str, ".zig") or std.mem.endsWith(u8, import_str, ".zon");
}

/// `std` and `builtin` name toolchain modules, not project modules.
pub fn isToolchainImport(import_str: []const u8) bool {
    return std.mem.eql(u8, import_str, "std") or std.mem.eql(u8, import_str, "builtin");
}

test "ZON data does not become a Zig declaration model" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "data.zon", .data = ".{ .value = 3 }" });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const importer = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(importer);
    var project = ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
    defer project.deinit();
    try std.testing.expectEqual(null, try project.modelForRelativeImport(importer, "data.zon"));
    try std.testing.expectEqual(null, project.failure);
}

test "toolchain imports are not counted as unresolved lookups" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data = "const std = @import(\"std\");\n" });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const importer = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(importer);
    var project = ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
    defer project.deinit();
    for (0..3) |_| {
        try std.testing.expectEqual(null, try project.modelForModuleImport(importer, "std"));
        try std.testing.expectEqual(null, try project.modelForModuleImport(importer, "builtin"));
    }
    try std.testing.expectEqual(0, project.unresolved_imports);
}

test "an unresolved lookup counts once per importing file and import string" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "a.zig", .data = "" });
    try tmp.dir.writeFile(io, .{ .sub_path = "b.zig", .data = "" });
    try tmp.dir.writeFile(io, .{ .sub_path = "data.zon", .data = ".{}" });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const a = try std.fs.path.join(gpa, &.{ directory, "a.zig" });
    defer gpa.free(a);
    const b = try std.fs.path.join(gpa, &.{ directory, "b.zig" });
    defer gpa.free(b);
    var project = ProjectCache.init(gpa, io, .{ .roots = &.{directory} });
    defer project.deinit();

    for (0..4) |_| {
        try std.testing.expectEqual(null, try project.modelForModuleImport(a, "nosuch"));
        try std.testing.expectEqual(null, try project.modelForRelativeImport(a, "gone.zig"));
    }
    try std.testing.expectEqual(2, project.unresolved_imports);

    try std.testing.expectEqual(null, try project.modelForModuleImport(b, "nosuch"));
    try std.testing.expectEqual(3, project.unresolved_imports);

    // ZON is data, not a failed lookup.
    try std.testing.expectEqual(null, try project.modelForRelativeImport(a, "data.zon"));
    try std.testing.expectEqual(3, project.unresolved_imports);
}
