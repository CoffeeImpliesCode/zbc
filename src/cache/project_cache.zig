//! Worker-owned immutable source snapshots. Only imports inside the explicit
//! first-party source policy can be loaded. No project traversal or global index.
const std = @import("std");
const Ast = std.zig.Ast;
const model_mod = @import("../model/file_model.zig");
const SourcePolicy = @import("type_engine").SourcePolicy;
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

    fn discoverModulePath(self: *ProjectCache, root: []const u8, module_name: []const u8) !?[]u8 {
        const build_path = try std.fs.path.join(self.gpa, &.{ root, "build.zig" });
        defer self.gpa.free(build_path);
        if (!self.policy.allowsAbsolutePath(build_path)) return null;
        const canonical = self.canonicalPath(build_path) catch |err| switch (err) {
            error.FileNotFound => return null,
            else => return err,
        };
        if (!self.policy.allowsAbsolutePath(canonical)) return null;
        const relative = (try parseBuildZigModulePath(self, canonical, module_name)) orelse return null;
        defer self.gpa.free(relative);
        const path = try std.fs.path.resolve(self.gpa, &.{ root, relative });
        if (self.policy.allowsAbsolutePath(path)) return path;
        self.gpa.free(path);
        return null;
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
            self.io, path, self.gpa, .limited(SourcePolicy.max_source_bytes), .of(u8), 0,
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

/// Only unique, explicit module wiring is evidence. Computed paths, shadowed
/// module variables and conflicting target aliases remain unresolved.
fn parseBuildZigModulePath(cache: *ProjectCache, path: []const u8, name: []const u8) !?[]u8 {
    const gpa = cache.gpa;
    var source = try cache.loadSource(path);
    defer source.deinit(gpa);
    const tree = source.ast();
    if (tree.source.len > 1024 * 1024) return error.StreamTooLong;
    var matched: ?[]const u8 = null;
    var alias_seen = false;
    var index: u32 = 1;
    while (index < tree.nodes.len) : (index += 1) {
        var buf: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buf, @enumFromInt(index)) orelse continue;
        const method = callName(tree, call) orelse continue;
        if (!std.mem.eql(u8, method, "addImport") or call.ast.params.len != 2) continue;
        const alias = stringLiteral(tree, call.ast.params[0]) orelse continue;
        if (!std.mem.eql(u8, alias, name)) continue;
        alias_seen = true;
        const module_node = resolveModuleVariable(tree, call.ast.params[1]) orelse return null;
        const candidate = moduleRootPath(tree, module_node) orelse return null;
        if (matched) |previous| if (!std.mem.eql(u8, previous, candidate)) return null;
        matched = candidate;
    }
    if (alias_seen) return if (matched) |p| try gpa.dupe(u8, p) else null;
    index = 1;
    while (index < tree.nodes.len) : (index += 1) {
        var buf: [1]Ast.Node.Index = undefined;
        const node: Ast.Node.Index = @enumFromInt(index);
        const call = tree.fullCall(&buf, node) orelse continue;
        const method = callName(tree, call) orelse continue;
        if (!std.mem.eql(u8, method, "addModule") or call.ast.params.len != 2) continue;
        const alias = stringLiteral(tree, call.ast.params[0]) orelse continue;
        if (!std.mem.eql(u8, alias, name)) continue;
        const candidate = moduleRootPath(tree, node) orelse return null;
        if (matched) |previous| if (!std.mem.eql(u8, previous, candidate)) return null;
        matched = candidate;
    }
    return if (matched) |p| try gpa.dupe(u8, p) else null;
}

fn resolveModuleVariable(tree: *const Ast, node: Ast.Node.Index) ?Ast.Node.Index {
    if (tree.nodeTag(node) != .identifier) return node;
    const name = tree.tokenSlice(tree.nodeMainToken(node));
    var found: ?Ast.Node.Index = null;
    var index: u32 = 1;
    while (index < tree.nodes.len) : (index += 1) {
        const decl = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(decl.ast.mut_token + 1), name)) continue;
        if (found != null) return null;
        found = decl.ast.init_node.unwrap();
    }
    return found;
}

fn moduleRootPath(tree: *const Ast, node: Ast.Node.Index) ?[]const u8 {
    var call_buf: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buf, node) orelse return null;
    const name = callName(tree, call) orelse return null;
    const options = if (std.mem.eql(u8, name, "createModule") and call.ast.params.len == 1)
        call.ast.params[0]
    else if (std.mem.eql(u8, name, "addModule") and call.ast.params.len == 2)
        call.ast.params[1]
    else return null;
    var init_buf: [2]Ast.Node.Index = undefined;
    const initializer = tree.fullStructInit(&init_buf, options) orelse return null;
    for (initializer.ast.fields) |field| {
        const token = tree.firstToken(field);
        if (token < 2 or !std.mem.eql(u8, tree.tokenSlice(token - 2), "root_source_file")) continue;
        var path_buf: [1]Ast.Node.Index = undefined;
        const path_call = tree.fullCall(&path_buf, field) orelse return null;
        if (path_call.ast.params.len != 1) return null;
        const path_name = callName(tree, path_call) orelse return null;
        if (!std.mem.eql(u8, path_name, "path")) return null;
        return stringLiteral(tree, path_call.ast.params[0]);
    }
    return null;
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

test "parseBuildZigModulePath: @import alias via createModule var (#20)" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // @import("bun") is wired through addImport("bun", foo), and foo is a
    // createModule whose root file is src/foo.zig — the decoupled-alias
    // pattern the old direct-name match could not follow.
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const foo = b.createModule(.{ .root_source_file = b.path("src/foo.zig") });
        \\    const exe = b.addExecutable(.{ .name = "x", .root_module = b.createModule(.{}) });
        \\    exe.root_module.addImport("bun", foo);
        \\}
    );
    const p = try std.fs.path.join(gpa, &.{ ".zig-cache", "tmp", &tmp.sub_path, "build.zig" });
    defer gpa.free(p);
    var cache = ProjectCache.init(gpa, tio, .{});
    defer cache.deinit();
    const rel = try parseBuildZigModulePath(&cache, p, "bun");
    defer if (rel) |r| gpa.free(r);
    try std.testing.expect(rel != null);
    try std.testing.expectEqualStrings("src/foo.zig", rel.?);
}

test "parseBuildZigModulePath: @import alias via addModule var (#20)" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // Declared module name ("internal") differs from the @import alias ("bun").
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const foo = b.addModule("internal", .{ .root_source_file = b.path("src/foo.zig") });
        \\    const exe = b.addExecutable(.{ .name = "x", .root_module = b.createModule(.{}) });
        \\    exe.root_module.addImport("bun", foo);
        \\}
    );
    const p = try std.fs.path.join(gpa, &.{ ".zig-cache", "tmp", &tmp.sub_path, "build.zig" });
    defer gpa.free(p);
    var cache = ProjectCache.init(gpa, tio, .{});
    defer cache.deinit();
    const rel = try parseBuildZigModulePath(&cache, p, "bun");
    defer if (rel) |r| gpa.free(r);
    try std.testing.expect(rel != null);
    try std.testing.expectEqualStrings("src/foo.zig", rel.?);
}

test "parseBuildZigModulePath: direct addModule(name) still resolves (#20)" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    _ = b.addModule("bun", .{ .root_source_file = b.path("lib/bun.zig") });
        \\}
    );
    const p = try std.fs.path.join(gpa, &.{ ".zig-cache", "tmp", &tmp.sub_path, "build.zig" });
    defer gpa.free(p);
    var cache = ProjectCache.init(gpa, tio, .{});
    defer cache.deinit();
    const rel = try parseBuildZigModulePath(&cache, p, "bun");
    defer if (rel) |r| gpa.free(r);
    try std.testing.expect(rel != null);
    try std.testing.expectEqualStrings("lib/bun.zig", rel.?);
}

test "parseBuildZigModulePath: undeclared module returns null (#20)" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try writeTmpBuildZig(&tmp, tio,
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const foo = b.createModule(.{ .root_source_file = b.path("src/foo.zig") });
        \\    _ = foo;
        \\}
    );
    const p = try std.fs.path.join(gpa, &.{ ".zig-cache", "tmp", &tmp.sub_path, "build.zig" });
    defer gpa.free(p);
    var cache = ProjectCache.init(gpa, tio, .{});
    defer cache.deinit();
    const rel = try parseBuildZigModulePath(&cache, p, "bun");
    defer if (rel) |r| gpa.free(r);
    try std.testing.expect(rel == null);
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
