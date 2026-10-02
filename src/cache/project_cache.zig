//! Worker-owned immutable source snapshots. Only imports inside the explicit
//! first-party source policy can be loaded. No project traversal or global index.
const std = @import("std");
const Ast = std.zig.Ast;
const model_mod = @import("../model/file_model.zig");
const SourcePolicy = @import("type_engine").SourcePolicy;
const NamedModuleMap = @import("type_engine").NamedModuleMap;
const ParseFailure = @import("type_engine").ParseFailure;

pub const CachedMethod = struct {
    returns: @import("../model/fn_summary.zig").Returns = .unknown,
    takes: ?u32 = null,
    may_grow: bool = false,
    may_gc: bool = false,
    may_thread: bool = false,
};

pub const ProjectCache = struct {
    gpa: std.mem.Allocator,
    io: std.Io,
    policy: SourcePolicy,
    /// Session documents own shared ASTs. Null permits standalone model analysis.
    type_context: ?*@import("type_engine").TypeContext = null,
    canonical_paths: @import("type_engine").CanonicalPaths = .{},
    entries: std.StringHashMapUnmanaged(*Entry) = .empty,
    imports: std.StringHashMapUnmanaged(ImportResult) = .empty,
    summaries: std.AutoHashMapUnmanaged(MethodKey, CachedMethod) = .empty,
    failure: ?anyerror = null,
    parse_failure: ?ParseFailure = null,
    parse_failures: std.StringHashMapUnmanaged(ParseFailure) = .empty,
    /// Build metadata read through the same parser the type engine uses, so a
    /// named import resolves identically for declaration models and for types.
    named_modules: ?NamedModuleMap = null,
    unresolved_imports: usize = 0,

    const MethodKey = struct { tree: *const Ast, declaration: Ast.Node.Index };
    const ImportResult = union(enum) {
        model: ?*const model_mod.FileModel,
        failed: struct { err: anyerror, parse_failure: ?ParseFailure },
    };
    const Entry = struct {
        abs_path: []const u8,
        source: Source,
        model: model_mod.FileModel,
    };

    const Source = union(enum) {
        owned: struct { bytes: [:0]u8, tree: Ast },
        borrowed: *const Ast,

        fn ast(self: *const Source) *const Ast {
            return switch (self.*) {
                .owned => |*source| &source.tree,
                .borrowed => |tree| tree,
            };
        }

        fn deinit(self: *Source, gpa: std.mem.Allocator) void {
            switch (self.*) {
                .owned => |*source| {
                    source.tree.deinit(gpa);
                    gpa.free(source.bytes);
                },
                .borrowed => {},
            }
        }
    };

    pub fn init(gpa: std.mem.Allocator, io: std.Io, policy: SourcePolicy) ProjectCache {
        return .{ .gpa = gpa, .io = io, .policy = policy };
    }

    pub fn deinit(self: *ProjectCache) void {
        self.summaries.deinit(self.gpa);
        var imports = self.imports.keyIterator();
        while (imports.next()) |key| self.gpa.free(key.*);
        self.imports.deinit(self.gpa);
        var parse_paths = self.parse_failures.keyIterator();
        while (parse_paths.next()) |path| self.gpa.free(path.*);
        self.parse_failures.deinit(self.gpa);
        var entries = self.entries.valueIterator();
        while (entries.next()) |value| {
            const entry = value.*;
            entry.model.deinit();
            entry.source.deinit(self.gpa);
            self.gpa.free(entry.abs_path);
            self.gpa.destroy(entry);
        }
        self.entries.deinit(self.gpa);
        self.canonical_paths.deinit(self.gpa);
        if (self.named_modules) |*modules| modules.deinit();
        self.* = undefined;
    }

    pub fn getMethodSummaryCache(self: *const ProjectCache, tree: *const Ast, declaration: Ast.Node.Index) ?CachedMethod {
        return self.summaries.get(.{ .tree = tree, .declaration = declaration });
    }

    pub fn putMethodSummaryCache(self: *ProjectCache, tree: *const Ast, declaration: Ast.Node.Index, summary: CachedMethod) !void {
        try self.summaries.put(self.gpa, .{ .tree = tree, .declaration = declaration }, summary);
    }

    /// The model must be a snapshot returned by this cache.
    pub fn pathForModel(self: *const ProjectCache, model: *const model_mod.FileModel) []const u8 {
        const entry: *const Entry = @fieldParentPtr("model", model);
        std.debug.assert(self.entries.get(entry.abs_path).? == entry);
        return entry.abs_path;
    }

    pub fn modelForRelativeImport(self: *ProjectCache, from_path: []const u8, import_str: []const u8) !?*const model_mod.FileModel {
        if (!isRelativeImport(import_str)) return null;
        return self.modelForImport(from_path, import_str);
    }

    pub fn modelForModuleImport(self: *ProjectCache, from_path: []const u8, import_str: []const u8) !?*const model_mod.FileModel {
        if (containsBadChar(import_str) or import_str.len == 0) return null;
        return self.modelForImport(from_path, import_str);
    }

    fn modelForImport(self: *ProjectCache, from_path: []const u8, import_str: []const u8) !?*const model_mod.FileModel {
        const key = try std.fmt.allocPrint(self.gpa, "{s}\x00{s}", .{ from_path, import_str });
        errdefer self.gpa.free(key);
        if (self.imports.get(key)) |cached| {
            self.gpa.free(key);
            return self.importResult(cached);
        }
        const model = self.loadImport(from_path, import_str) catch |err| {
            const result: ImportResult = .{ .failed = .{
                .err = err,
                .parse_failure = if (err == error.ImportInvalidSyntax) self.parse_failure else null,
            } };
            try self.imports.put(self.gpa, key, result);
            return self.importResult(result);
        };
        try self.imports.put(self.gpa, key, .{ .model = model });
        if (model == null) self.unresolved_imports += 1;
        return model;
    }

    fn importResult(self: *ProjectCache, result: ImportResult) ?*const model_mod.FileModel {
        return switch (result) {
            .model => |model| model,
            .failed => |failed| blk: {
                self.failure = failed.err;
                self.parse_failure = failed.parse_failure;
                break :blk null;
            },
        };
    }

    fn loadImport(self: *ProjectCache, from_path: []const u8, import_str: []const u8) !?*const model_mod.FileModel {
        const from_absolute = if (std.fs.path.isAbsolute(from_path))
            from_path
        else
            try self.canonicalPath(from_path);
        if (!self.policy.allowsAbsolutePath(from_absolute)) return null;
        const root = self.policy.rootFor(from_absolute) orelse return null;
        if (isRelativeImport(import_str)) {
            const parent = std.fs.path.dirname(from_absolute) orelse return null;
            const path = try std.fs.path.resolve(self.gpa, &.{ parent, import_str });
            defer self.gpa.free(path);
            return self.modelForAbsolutePath(path);
        }
        const path = (try self.discoverModulePath(root, import_str)) orelse return null;
        defer self.gpa.free(path);
        return self.modelForAbsolutePath(path);
    }

    /// The root source file that `root`'s own `build.zig` wires to
    /// `module_name`.  Wiring the source policy does not admit, wiring that
    /// is ambiguous, and wiring only a real build run could settle all stay
    /// unresolved: an unresolved module is an unknown type, a guessed one is
    /// a wrong type.
    fn discoverModulePath(self: *ProjectCache, root: []const u8, module_name: []const u8) !?[]u8 {
        const modules = if (self.named_modules) |*existing| existing else blk: {
            self.named_modules = .init(self.gpa);
            break :blk &self.named_modules.?;
        };
        try modules.scanInto(self.io, self.policy, root);
        const root_source_file = modules.lookup(module_name) orelse return null;
        return try self.gpa.dupe(u8, root_source_file);
    }

    fn canonicalPath(self: *ProjectCache, path: []const u8) ![]const u8 {
        if (self.type_context) |context| return context.canonicalPath(path);
        return self.canonical_paths.resolve(self.gpa, self.io, path);
    }

    fn modelForAbsolutePath(self: *ProjectCache, path: []const u8) !?*const model_mod.FileModel {
        if (std.mem.endsWith(u8, path, ".zon")) return null;
        if (!self.policy.allowsAbsolutePath(path)) return null;
        const canonical = try self.canonicalPath(path);
        if (!self.policy.allowsAbsolutePath(canonical)) return null;
        if (self.entries.get(canonical)) |entry| return &entry.model;
        const entry = try self.gpa.create(Entry);
        errdefer self.gpa.destroy(entry);
        entry.source = try self.loadSource(canonical);
        errdefer entry.source.deinit(self.gpa);
        const owned_path = try self.gpa.dupe(u8, canonical);
        errdefer self.gpa.free(owned_path);
        entry.abs_path = owned_path;
        entry.model = try model_mod.buildWithPath(self.gpa, entry.source.ast(), owned_path);
        errdefer entry.model.deinit();
        try self.entries.put(self.gpa, owned_path, entry);
        return &entry.model;
    }

    fn loadSource(self: *ProjectCache, path: []const u8) !Source {
        if (self.type_context) |context| {
            const handle = context.sourceHandle(path) catch |err| {
                if (err == error.ImportInvalidSyntax) self.parse_failure = context.store.parse_failure;
                return err;
            };
            return .{ .borrowed = &handle.tree };
        }
        if (self.parse_failures.get(path)) |failure| {
            self.parse_failure = failure;
            return error.ImportInvalidSyntax;
        }
        const bytes = try std.Io.Dir.cwd().readFileAllocOptions(
            self.io,
            path,
            self.gpa,
            .limited(SourcePolicy.max_source_bytes),
            .of(u8),
            0,
        );
        errdefer self.gpa.free(bytes);
        var tree = try Ast.parse(self.gpa, bytes, .zig);
        errdefer tree.deinit(self.gpa);
        if (tree.errors.len != 0) {
            try self.rememberParseFailure(path, &tree);
            return error.ImportInvalidSyntax;
        }
        return .{ .owned = .{ .bytes = bytes, .tree = tree } };
    }

    fn rememberParseFailure(self: *ProjectCache, path: []const u8, tree: *const Ast) !void {
        if (self.parse_failures.get(path)) |failure| {
            self.parse_failure = failure;
            return;
        }
        const owned_path = try self.gpa.dupe(u8, path);
        errdefer self.gpa.free(owned_path);
        const failure = ParseFailure.fromTree(owned_path, tree);
        try self.parse_failures.put(self.gpa, owned_path, failure);
        self.parse_failure = failure;
    }
};

fn containsBadChar(s: []const u8) bool {
    for (s) |c| if (c == '/' or c == '\\' or c == '.' or c == 0) return true;
    return false;
}

pub fn isRelativeImport(path: []const u8) bool {
    return std.mem.endsWith(u8, path, ".zig") or std.mem.endsWith(u8, path, ".zon");
}

// ── Tests ──────────────────────────────────────────────────────

test "ProjectCache: loads sibling .zig file" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(tio, .{
        .sub_path = "lib.zig",
        .data =
        \\pub const Foo = struct {
        \\    x: u32,
        \\};
        \\
        ,
    });
    try tmp.dir.writeFile(tio, .{
        .sub_path = "main.zig",
        .data =
        \\const lib = @import("./lib.zig");
        \\pub fn main() void { _ = lib.Foo; }
        \\
        ,
    });
    const root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(root);
    const from_path = try std.fs.path.join(gpa, &.{ root, "main.zig" });
    defer gpa.free(from_path);
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{root} });
    defer pc.deinit();
    const model = (try pc.modelForRelativeImport(from_path, "./lib.zig")).?;
    try std.testing.expectEqual(model_mod.TypeKind.struct_, model.findType("Foo").?.kind);
}

test "ProjectCache: module-name imports return null" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var pc = ProjectCache.init(gpa, tio, .{});
    defer pc.deinit();
    const fm = try pc.modelForRelativeImport("/anywhere/x.zig", "std");
    try std.testing.expect(fm == null);
}

fn writeTmpBuildZig(tmp: *std.testing.TmpDir, tio: std.Io, data: []const u8) !void {
    try tmp.dir.writeFile(tio, .{ .sub_path = "build.zig", .data = data });
}

/// Creates `src/<name>` for each name, so a build.zig can wire a root that
/// really exists: a root that is absent is unresolved for a different reason.
fn writeTmpSources(tmp: *std.testing.TmpDir, tio: std.Io, gpa: std.mem.Allocator, names: []const []const u8) !void {
    try tmp.dir.createDirPath(tio, "src");
    for (names) |name| {
        const sub_path = try std.fs.path.join(gpa, &.{ "src", name });
        defer gpa.free(sub_path);
        try tmp.dir.writeFile(tio, .{ .sub_path = sub_path, .data = "pub const Value = u8;" });
    }
}

test "discoverModulePath: imports arrays, module variables and addImport aliases resolve" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try writeTmpSources(&tmp, tio, gpa, &.{ "root.zig", "platform.zig" });
    // The wiring shapes real build.zig files use: a declared module name that
    // differs from the @import alias, an `.imports` array on a module, and a
    // module expression bound to a variable.
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const platform = b.addModule("platform", .{
        \\        .root_source_file = b.path("src/platform.zig"),
        \\        .imports = &.{},
        \\    });
        \\    const mod = b.addModule("skript", .{
        \\        .root_source_file = b.path("src/root.zig"),
        \\        .imports = &.{
        \\            .{ .name = "platform", .module = platform },
        \\            .{ .name = "options", .module = b.addOptions().createModule() },
        \\        },
        \\    });
        \\    const exe = b.addExecutable(.{
        \\        .name = "x",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("src/main.zig"),
        \\            .imports = &.{.{ .name = "skript", .module = mod }},
        \\        }),
        \\    });
        \\    exe.root_module.addImport("alias", platform);
        \\}
    );
    const root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(root);
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{root} });
    defer pc.deinit();
    for ([_]struct { name: []const u8, sub_path: []const u8 }{
        .{ .name = "skript", .sub_path = "src/root.zig" },
        .{ .name = "platform", .sub_path = "src/platform.zig" },
        .{ .name = "alias", .sub_path = "src/platform.zig" },
    }) |expected| {
        const found = (try pc.discoverModulePath(root, expected.name)).?;
        defer gpa.free(found);
        const want = try std.fs.path.join(gpa, &.{ root, expected.sub_path });
        defer gpa.free(want);
        try std.testing.expectEqualStrings(want, found);
    }
    // A generated options module has no path in the source tree.
    try std.testing.expect((try pc.discoverModulePath(root, "options")) == null);
}

test "discoverModulePath: unprovable wiring stays unresolved" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try writeTmpSources(&tmp, tio, gpa, &.{ "a.zig", "b.zig", "c.zig", "first.zig", "second.zig" });
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    // two roots under one name: the alias is ambiguous
        \\    _ = b.addModule("shared", .{ .root_source_file = b.path("src/a.zig") });
        \\    _ = b.addModule("shared", .{ .root_source_file = b.path("src/b.zig") });
        \\    // the same name wired twice to the same root is not ambiguous
        \\    _ = b.addModule("stable", .{ .root_source_file = b.path("src/c.zig") });
        \\    _ = b.createModule(.{ .root_source_file = b.path("src/c.zig") });
        \\    // one module variable declared twice: which one is meant is unknown
        \\    {
        \\        const mod = b.createModule(.{ .root_source_file = b.path("src/first.zig") });
        \\        _ = mod;
        \\    }
        \\    {
        \\        const mod = b.createModule(.{ .root_source_file = b.path("src/second.zig") });
        \\        _ = b.addImport("shadowed", mod);
        \\    }
        \\    // a path computed at build time proves nothing
        \\    _ = b.addModule("computed", .{
        \\        .root_source_file = b.pathJoin(&.{ "src", "gen.zig" }),
        \\    });
        \\    // a path no build step has written yet is not a readable source
        \\    _ = b.addModule("absent", .{ .root_source_file = b.path("src/never-written.zig") });
        \\    // a module the dependency's own build.zig owns
        \\    const dep = b.dependency("dep", .{});
        \\    _ = b.addImport("depmod", dep.module("dep"));
        \\}
    );
    const root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(root);
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{root} });
    defer pc.deinit();
    for ([_][]const u8{ "shared", "shadowed", "computed", "depmod", "absent" }) |ambiguous| {
        try std.testing.expect((try pc.discoverModulePath(root, ambiguous)) == null);
    }
    const stable = (try pc.discoverModulePath(root, "stable")).?;
    defer gpa.free(stable);
    const want = try std.fs.path.join(gpa, &.{ root, "src/c.zig" });
    defer gpa.free(want);
    try std.testing.expectEqualStrings(want, stable);
}

test "discoverModulePath: wiring into an excluded tree is not published" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try writeTmpSources(&tmp, tio, gpa, &.{"kept.zig"});
    try tmp.dir.createDirPath(tio, "vendor");
    try tmp.dir.writeFile(tio, .{ .sub_path = "vendor/lib.zig", .data = "pub const Value = u8;" });
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    _ = b.addModule("vendored", .{ .root_source_file = b.path("vendor/lib.zig") });
        \\    _ = b.addModule("kept", .{ .root_source_file = b.path("src/kept.zig") });
        \\}
    );
    const root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(root);
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{root} });
    defer pc.deinit();
    try std.testing.expect((try pc.discoverModulePath(root, "vendored")) == null);
    const kept = try pc.discoverModulePath(root, "kept") orelse return error.TestUnexpectedResult;
    defer gpa.free(kept);
    try std.testing.expect(std.mem.endsWith(u8, kept, "src/kept.zig"));
}

test "discoverModulePath: the build file above the directory still governs it" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try writeTmpSources(&tmp, tio, gpa, &.{"lib.zig"});
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    _ = b.addModule("lib", .{ .root_source_file = b.path("src/lib.zig") });
        \\}
    );
    const project = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(project);
    const nested = try std.fs.path.join(gpa, &.{ project, "src" });
    defer gpa.free(nested);
    // Nothing in the nested root wires `lib`: the build file that wires it is
    // the project's, one directory up, and both are first-party roots.
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{ nested, project } });
    defer pc.deinit();
    const found = (try pc.discoverModulePath(nested, "lib")).?;
    defer gpa.free(found);
    const want = try std.fs.path.join(gpa, &.{ project, "src/lib.zig" });
    defer gpa.free(want);
    try std.testing.expectEqualStrings(want, found);
}

test "discoverModulePath: an unreadable build.zig proves nothing" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try writeTmpBuildZig(&tmp, tio, "pub fn build(b: *std.Build) void { this is not zig");
    const root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(root);
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{root} });
    defer pc.deinit();
    try std.testing.expect((try pc.discoverModulePath(root, "bun")) == null);
}

test "discoverModulePath: build.zig present blocks layout guessing (#20 gating)" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // build.zig present but does NOT declare `bun`; a bun.zig sits at root.
    // The gating must NOT guess it (a known-but-unparsed build => no guess).
    try writeTmpBuildZig(&tmp, tio,
        \\pub fn build(b: *@import("std").Build) void { _ = b; }
    );
    try tmp.dir.writeFile(tio, .{ .sub_path = "bun.zig", .data = "pub const X = 1;" });
    const root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(root);
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{root} });
    defer pc.deinit();
    const r = try pc.discoverModulePath(root, "bun");
    defer if (r) |x| gpa.free(x);
    try std.testing.expect(r == null);
}

test "discoverModulePath: absent build wiring cannot prove a module" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(tio, .{ .sub_path = "bun.zig", .data = "pub const X = 1;" });
    const root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(root);
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{root} });
    defer pc.deinit();
    const r = try pc.discoverModulePath(root, "bun");
    defer if (r) |x| gpa.free(x);
    try std.testing.expect(r == null);
}

test "modelForModuleImport: the audit's directory plus governing file resolves a named module" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.createDirPath(tio, "src");
    try tmp.dir.writeFile(tio, .{ .sub_path = "src/engine.zig", .data =
        \\pub const Registry = struct {
        \\    entries: []const u32,
        \\};
        \\
    });
    try tmp.dir.writeFile(tio, .{ .sub_path = "src/consumer.zig", .data =
        \\const engine = @import("engine");
        \\pub fn observe(registry: engine.Registry) usize {
        \\    return registry.entries.len;
        \\}
        \\
    });
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const engine = b.addModule("engine", .{
        \\        .root_source_file = b.path("src/engine.zig"),
        \\    });
        \\    _ = b.addModule("skript", .{
        \\        .root_source_file = b.path("src/consumer.zig"),
        \\        .imports = &.{.{ .name = "engine", .module = engine }},
        \\    });
        \\}
    );
    const project = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(project);
    const source_root = try std.fs.path.join(gpa, &.{ project, "src" });
    defer gpa.free(source_root);
    const consumer = try std.fs.path.join(gpa, &.{ source_root, "consumer.zig" });
    defer gpa.free(consumer);
    const build_path = try std.fs.path.join(gpa, &.{ project, "build.zig" });
    defer gpa.free(build_path);
    // Exactly what `zbc <project>/src/ <project>/build.zig` selects: the
    // directory argument is one root, and the explicitly named governing file
    // makes its parent a second, so the walk out of `src` reaches that file.
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{ source_root, project } });
    defer pc.deinit();
    const model = (try pc.modelForModuleImport(consumer, "engine")).?;
    // The consumer's import is answered by the wired root's own declarations
    // instead of staying unknown: the struct crossed the module boundary.
    const registry = model.findType("Registry") orelse return error.MissingModuleType;
    try std.testing.expectEqual(model_mod.TypeKind.struct_, registry.kind);
    try std.testing.expectEqual(@as(usize, 1), registry.fields.len);
    try std.testing.expectEqualStrings("entries", registry.fields[0].name);
    // The governing file is a root in its own right, so a lookup from its own
    // directory resolves the same wiring to the same root, not a second copy.
    const same = (try pc.modelForModuleImport(build_path, "engine")).?;
    try std.testing.expect(model == same);
    try std.testing.expectEqual(@as(?anyerror, null), pc.failure);
}

test "modelForModuleImport: denied, generated, ambiguous and unwired stay unresolved" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.createDirPath(tio, "src");
    try tmp.dir.writeFile(tio, .{ .sub_path = "src/a.zig", .data = "pub const Marker = struct { value: u32 };" });
    try tmp.dir.writeFile(tio, .{ .sub_path = "src/b.zig", .data = "pub const Other = struct { value: u32 };" });
    try tmp.dir.writeFile(tio, .{ .sub_path = "src/consumer.zig", .data =
        \\const wired = @import("wired");
        \\pub fn observe(marker: wired.Marker) u32 {
        \\    return marker.value;
        \\}
        \\
    });
    // `vendor/` holds a real root, so the policy is the only thing that can
    // keep its wiring unresolved.
    try tmp.dir.createDirPath(tio, "vendor");
    try tmp.dir.writeFile(tio, .{ .sub_path = "vendor/lib.zig", .data = "pub const Vendored = struct { value: u32 };" });
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    // one name, two roots: ambiguous
        \\    _ = b.addModule("ambiguous", .{ .root_source_file = b.path("src/a.zig") });
        \\    _ = b.addModule("ambiguous", .{ .root_source_file = b.path("src/b.zig") });
        \\    // a root no build step has written yet
        \\    _ = b.addModule("generated", .{ .root_source_file = b.path("src/never-written.zig") });
        \\    // a root the selected sources do not admit
        \\    _ = b.addModule("denied", .{ .root_source_file = b.path("vendor/lib.zig") });
        \\    // the one that is admitted and really wired
        \\    _ = b.addModule("wired", .{ .root_source_file = b.path("src/a.zig") });
        \\}
    );
    const project = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(project);
    const source_root = try std.fs.path.join(gpa, &.{ project, "src" });
    defer gpa.free(source_root);
    const consumer = try std.fs.path.join(gpa, &.{ source_root, "consumer.zig" });
    defer gpa.free(consumer);
    var pc = ProjectCache.init(gpa, tio, .{ .roots = &.{ source_root, project } });
    defer pc.deinit();
    for ([_][]const u8{ "ambiguous", "generated", "denied", "unwired" }) |name| {
        try std.testing.expect((try pc.modelForModuleImport(consumer, name)) == null);
        // An unresolved module is an unknown type, never a failed file.
        try std.testing.expectEqual(@as(?anyerror, null), pc.failure);
    }
    // Admitted wiring in the same governing file still resolves, so the
    // unresolved answers above come from the wiring and not the selection.
    const model = (try pc.modelForModuleImport(consumer, "wired")).?;
    try std.testing.expectEqual(model_mod.TypeKind.struct_, (model.findType("Marker") orelse return error.MissingModuleType).kind);
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
