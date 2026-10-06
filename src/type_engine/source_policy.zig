const std = @import("std");

pub const ParseFailure = struct {
    /// Borrowed canonical path or file URI; null denotes the input file.
    source_path: ?[]const u8,
    position: struct { line: u32, column: u32, byte: u32 },
    reason: []const u8,

    pub fn fromTree(source_path: ?[]const u8, tree: *const std.zig.Ast) ParseFailure {
        std.debug.assert(tree.errors.len != 0);
        const failure = tree.errors[0];
        const location = tree.tokenLocation(0, failure.token);
        return .{
            .source_path = source_path,
            .position = .{
                .line = @intCast(location.line + 1),
                .column = @intCast(location.column + 1),
                .byte = tree.tokenStart(failure.token),
            },
            .reason = @tagName(failure.tag),
        };
    }
};

/// Canonical source identities remain fixed until the next analysis sweep.
/// Every value borrows an owned key. Filesystem work stays outside the lock.
pub const CanonicalPaths = struct {
    entries: std.StringHashMapUnmanaged([]const u8) = .empty,
    mutex: std.Io.Mutex = .init,

    pub fn deinit(self: *CanonicalPaths, gpa: std.mem.Allocator) void {
        var keys = self.entries.keyIterator();
        while (keys.next()) |key| gpa.free(key.*);
        self.entries.deinit(gpa);
        self.* = undefined;
    }

    fn lookup(self: *CanonicalPaths, io: std.Io, path: []const u8) ?[]const u8 {
        self.mutex.lockUncancelable(io);
        defer self.mutex.unlock(io);
        return self.entries.get(path);
    }

    pub fn resolve(self: *CanonicalPaths, gpa: std.mem.Allocator, io: std.Io, path: []const u8) ![]const u8 {
        if (std.fs.path.isAbsolute(path)) {
            if (self.lookup(io, path)) |known| return known;
        }
        var cwd_buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
        const cwd = if (std.fs.path.isAbsolute(path)) "" else
            cwd_buffer[0..try std.Io.Dir.cwd().realPathFile(io, ".", &cwd_buffer)];
        const lexical = try std.fs.path.resolve(gpa, &.{ cwd, path });
        errdefer gpa.free(lexical);
        if (self.lookup(io, lexical)) |known| {
            gpa.free(lexical);
            return known;
        }
        var canonical_buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
        const length = try std.Io.Dir.cwd().realPathFile(io, lexical, &canonical_buffer);
        const canonical = try gpa.dupe(u8, canonical_buffer[0..length]);
        errdefer gpa.free(canonical);
        try self.mutex.lock(io);
        defer self.mutex.unlock(io);
        if (self.entries.get(lexical)) |known| {
            gpa.free(lexical);
            gpa.free(canonical);
            return known;
        }
        try self.entries.ensureUnusedCapacity(gpa, 2);
        if (self.entries.get(canonical)) |known| {
            gpa.free(canonical);
            self.entries.putAssumeCapacityNoClobber(lexical, known);
            return known;
        }
        self.entries.putAssumeCapacityNoClobber(canonical, canonical);
        if (std.mem.eql(u8, lexical, canonical)) {
            gpa.free(lexical);
        } else {
            self.entries.putAssumeCapacityNoClobber(lexical, canonical);
        }
        return canonical;
    }
};

/// Borrowed canonical roots for one immutable analysis sweep.
/// Exclusions are absolute paths or basenames and always take precedence.
pub const SourcePolicy = struct {
    roots: []const []const u8 = &.{},
    excludes: []const []const u8 = &.{},
    pub const isExcludedBasename = skipBasename;
    pub const max_source_bytes = 16 * 1024 * 1024;

    pub fn rootFor(self: SourcePolicy, path: []const u8) ?[]const u8 {
        var selected: ?[]const u8 = null;
        for (self.roots) |root| {
            if (!within(root, path)) continue;
            if (selected == null or root.len > selected.?.len) selected = root;
        }
        return selected;
    }

    pub fn allowsAbsolutePath(self: SourcePolicy, path: []const u8) bool {
        if (!std.fs.path.isAbsolute(path)) return false;
        var root = self.rootFor(path) orelse return false;
        // A nested allowed root cannot re-admit an excluded subtree.
        for (self.roots) |candidate| {
            if (candidate.len < root.len and within(candidate, path)) root = candidate;
        }
        if (self.excludesPath(root) or self.excludesPath(path)) return false;
        var parts = std.mem.tokenizeAny(u8, path[root.len..], "/\\");
        while (parts.next()) |part| {
            if (self.excludesName(part)) return false;
        }
        return true;
    }

    /// Check input roots before canonicalization or directory traversal.
    pub fn excludesPath(self: SourcePolicy, path: []const u8) bool {
        for (self.excludes) |excluded| {
            if (std.fs.path.isAbsolute(excluded) and within(excluded, path)) return true;
        }
        const name = std.fs.path.basename(path);
        return name.len != 0 and self.excludesName(name);
    }

    fn excludesName(self: SourcePolicy, name: []const u8) bool {
        if (skipBasename(name)) return true;
        for (self.excludes) |excluded| {
            if (std.mem.eql(u8, excluded, name)) return true;
        }
        return false;
    }
};

pub fn within(root: []const u8, path: []const u8) bool {
    if (!std.mem.startsWith(u8, path, root)) return false;
    return path.len == root.len or (root.len > 0 and root[root.len - 1] == '/') or
        path[root.len] == '/';
}

pub fn skipBasename(name: []const u8) bool {
    if (name.len == 0 or name[0] == '.') return true;
    const excluded = [_][]const u8{
        "deps", "dependencies", "third_party", "third-party", "vendor", "vendored",
        "node_modules", "zig-pkg", "zig-cache", "zig-out", "build", "target", "out", "dist",
    };
    for (excluded) |part| {
        if (std.mem.eql(u8, name, part)) return true;
    }
    return false;
}

test "source boundaries reject dependencies and sibling-prefix escapes" {
    const policy: SourcePolicy = .{ .roots = &.{"/project"}, .excludes = &.{"/project/generated", "scratch"} };
    try std.testing.expect(policy.allowsAbsolutePath("/project/src/main.zig"));
    try std.testing.expect(!policy.allowsAbsolutePath("/project-other/main.zig"));
    try std.testing.expect(!policy.allowsAbsolutePath("/project/src/../secret.zig"));
    try std.testing.expect(!policy.allowsAbsolutePath("/project/generated/main.zig"));
    try std.testing.expect(!policy.allowsAbsolutePath("/project/src/scratch/main.zig"));
    for ([_][]const u8{ "deps", "third_party", "vendor", "zig-pkg", ".zig-cache", "zig-out" }) |dir| {
        const path = try std.fmt.allocPrint(std.testing.allocator, "/project/{s}/bad.zig", .{dir});
        defer std.testing.allocator.free(path);
        try std.testing.expect(!policy.allowsAbsolutePath(path));
    }
}

test "empty source scope cannot read an unrelated project" {
    const empty: SourcePolicy = .{};
    try std.testing.expect(!empty.allowsAbsolutePath("/tmp/main.zig"));
    const policy: SourcePolicy = .{ .roots = &.{"/tmp/.fixtures/test"} };
    try std.testing.expect(policy.allowsAbsolutePath("/tmp/.fixtures/test/main.zig"));
}

test "explicit and nested roots cannot override exclusions" {
    const nested: SourcePolicy = .{ .roots = &.{ "/project", "/project/vendor", "/project/vendor/generated" } };
    try std.testing.expect(!nested.allowsAbsolutePath("/project/vendor/generated/file.zig"));
    const explicit: SourcePolicy = .{ .roots = &.{"/project/vendor"} };
    try std.testing.expect(!explicit.allowsAbsolutePath("/project/vendor"));
    const named: SourcePolicy = .{ .roots = &.{"/project/generated"}, .excludes = &.{"generated"} };
    try std.testing.expect(!named.allowsAbsolutePath("/project/generated/file.zig"));
}
