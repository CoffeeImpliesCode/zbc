const std = @import("std");
const builtin = @import("builtin");

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
        const cwd = if (std.fs.path.isAbsolute(path)) "" else cwd_buffer[0..try std.Io.Dir.cwd().realPathFile(io, ".", &cwd_buffer)];
        // The spelling reaches the kernel whole, because this table's whole
        // claim is that one value names one file.
        //
        // `std.fs.path.resolve` folds `..` into the text before returning
        // (`std/fs/path.zig:1126` pops the component before it) and says so
        // itself (`std/fs/path.zig:1104`): it performs no syscall, so it
        // folds a link it never looked at as if the link were the directory
        // it names.  `<dir>/link/../main.zig` then becomes `<dir>/main.zig`,
        // and the answer is whichever of those two files happens to exist.
        //
        // `Dir.cwd().realPathFile` makes no such fold on any backend: it is
        // `realpath(3)` where libc is linked (`std/Io/Threaded.zig:6685`,
        // `std/Io/Dispatch.zig:2802`); otherwise the whole spelling goes to
        // `openat` and the answer comes back from `/proc/self/fd`
        // (`std/Io/Threaded.zig:6721`, `:6762`, `:6839`); and on Windows an
        // `OpenFile` answered by `GetFinalPathNameByHandle`
        // (`std/Io/Threaded.zig:6080`, `:6108`).  Each is the operating
        // system's own walk of the spelling, which resolves a link before it
        // counts a `..` back out of what the link names — and not one of them
        // rewrites the spelling first, which is the whole difference.
        //
        // So an absolute spelling is handed over exactly as it was written,
        // and a relative one is only *made* absolute — joined, never folded
        // — because that is the one step no syscall can do for us.
        const lexical = if (cwd.len == 0)
            try gpa.dupe(u8, path)
        else
            try std.fs.path.join(gpa, &.{ cwd, path });
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
    /// Borrowed exact canonical absolute build.zig paths, immutable for the
    /// Session lifetime. Empty by default: libraries get no metadata-only
    /// permission. These grants never admit sources or module targets.
    build_files: []const []const u8 = &.{},
    /// The exclusive width bound on a source this policy reads off the
    /// filesystem, in bytes.  A file whose length is *at or past* this
    /// number is refused as `error.SourceTooWide`, and it is refused from
    /// the descriptor's own size, before a single data byte is copied.
    ///
    /// This is `std.zig.Ast`'s own addressable domain rather than a number
    /// chosen for this policy: token starts are `u32`, and a reported
    /// column is a byte offset *plus one*, so the last byte of a source of
    /// exactly `maxInt(u32)` bytes has no representable column and the
    /// parser's domain stops one byte short of it.  A narrower read cap
    /// would reject sources the parser can represent; a wider one would
    /// admit sources it cannot.
    pub const max_source_bytes = std.math.maxInt(u32);

    /// Whether a source of `length` bytes is inside `max_source_bytes`.
    ///
    /// Exclusive and exact, so the largest admitted source is
    /// `max_source_bytes - 1` bytes — the same length client text is
    /// admitted at.  The bound and this test are stated once, here, so the
    /// filesystem read and the client text cannot drift into answering two
    /// different questions about one file.
    pub fn admitsSourceLength(length: u64) bool {
        return length < max_source_bytes;
    }

    /// What one source read off the filesystem can fail at, before any
    /// caller-specific admission has had a say.  `StatError` is here because
    /// the size is consulted before it is acted on; a descriptor that cannot
    /// answer its own size cannot answer whether it is admissible.
    pub const ReadSourceError = std.mem.Allocator.Error || std.Io.Cancelable ||
        std.Io.File.OpenError || std.Io.File.StatError || std.Io.File.Reader.Error ||
        error{SourceTooWide};

    /// Reads `sub_path` as one null-terminated source, refusing a file the
    /// policy cannot admit before its size is turned into a buffer.
    ///
    /// This is the single place an ordinary document load, a `build.zig` scan
    /// and a standalone cache's own load read their bytes, so the width rule
    /// cannot hold for one and not for the others.  Two steps, in this order,
    /// on one descriptor:
    ///
    ///  1. Open, then `stat` the descriptor just opened.  Consulting the size
    ///     here is what makes a refused source cost one syscall instead of an
    ///     allocation, a read and a hash all sized by it: a four-gigabyte
    ///     file is rejected without one of its bytes being touched.  Stat'ing
    ///     the descriptor rather than the path also keeps the answer about
    ///     the file the bytes will actually come from, rather than about
    ///     whatever the name resolves to a second later.
    ///  2. Stream the rest through a reader bounded by the *same* exclusive
    ///     bound.  The `stat` is a snapshot, not a promise: a file that grows
    ///     past the bound while it is being read still stops at the bound,
    ///     and is refused under the same name as one that was already too
    ///     wide.
    pub fn readSourceSentinel(
        io: std.Io,
        dir: std.Io.Dir,
        sub_path: []const u8,
        gpa: std.mem.Allocator,
    ) ReadSourceError![:0]u8 {
        var file = try dir.openFile(io, sub_path, .{
            // Parity with `Dir.readFileAllocOptions`: on Windows this makes a
            // directory report `error.IsDir` at open rather than at read.
            .allow_directory = if (builtin.os.tag == .windows) false else true,
        });
        defer file.close(io);

        if (!admitsSourceLength((try file.stat(io)).size)) return error.SourceTooWide;

        var file_reader = file.reader(io, &.{});
        return readBoundedSourceSentinel(
            &file_reader.interface,
            gpa,
            max_source_bytes,
        ) catch |err| switch (err) {
            error.SourceTooWide => error.SourceTooWide,

            // The reader knows only that a read failed; the descriptor knows
            // why, and that is the error the caller is handed.
            error.ReadFailed => file_reader.err.?,

            // Allocating the read is the only way this can run out of memory,
            // and that failure is about the allocator, not about the width.
            error.OutOfMemory => error.OutOfMemory,
        };
    }

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

    /// Allows an ordinary in-root build.zig or an exact metadata-only grant.
    /// Explicit grants cannot override excluded ancestors. Rejects noncanonical
    /// path spellings without I/O; callers must resolve filesystem identities.
    pub fn allowsBuildFile(self: SourcePolicy, path: []const u8) bool {
        if (!isCanonicalBuildPath(path)) return false;
        if (self.allowsAbsolutePath(path)) return true;
        if (self.excludesPath(path)) return false;
        var parts = std.mem.tokenizeAny(u8, path, "/\\");
        while (parts.next()) |part| {
            if (self.excludesName(part)) return false;
        }
        for (self.build_files) |build_file| {
            if (std.mem.eql(u8, build_file, path)) return true;
        }
        return false;
    }

    fn isCanonicalBuildPath(path: []const u8) bool {
        if (!std.fs.path.isAbsolute(path)) return false;
        if (!std.mem.eql(u8, std.fs.path.basename(path), "build.zig")) return false;
        // Skip only the filesystem prefix, not empty interior components.
        const start: usize = if (builtin.os.tag == .windows and
            (std.mem.startsWith(u8, path, "\\\\") or std.mem.startsWith(u8, path, "//")))
            2
        else if (path[0] == '/' or path[0] == '\\')
            1
        else
            0;
        var parts = std.mem.splitAny(u8, path[start..], "/\\");
        while (parts.next()) |part| {
            if (part.len == 0 or std.mem.eql(u8, part, ".") or
                std.mem.eql(u8, part, "..")) return false;
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
        if (isPrunedDirectoryName(name)) return true;
        for (self.excludes) |excluded| {
            if (std.mem.eql(u8, excluded, name)) return true;
        }
        return false;
    }
};

/// Keep the exclusive source bound separate from `Io.Limit`'s unlimited
/// sentinel. Finite chunks preserve the growth guard on 32-bit targets too.
fn readBoundedSourceSentinel(
    reader: *std.Io.Reader,
    gpa: std.mem.Allocator,
    bound: u64,
) (std.mem.Allocator.Error || error{ ReadFailed, SourceTooWide })![:0]u8 {
    var output: std.Io.Writer.Allocating = .init(gpa);
    defer output.deinit();
    var remaining = bound;
    while (remaining != 0) {
        const chunk: usize = @intCast(@min(remaining, std.math.maxInt(usize) - 1));
        const n = reader.stream(&output.writer, .limited(chunk)) catch |err| switch (err) {
            error.EndOfStream => return output.toOwnedSliceSentinel(0),
            error.WriteFailed => return error.OutOfMemory,
            error.ReadFailed => return error.ReadFailed,
        };
        remaining -= n;
    }
    return error.SourceTooWide;
}

pub fn within(root: []const u8, path: []const u8) bool {
    if (!std.mem.startsWith(u8, path, root)) return false;
    return path.len == root.len or (root.len > 0 and root[root.len - 1] == '/') or
        path[root.len] == '/';
}

pub fn isPrunedDirectoryName(name: []const u8) bool {
    if (name.len == 0 or name[0] == '.') return true;
    const excluded = [_][]const u8{
        "deps",         "dependencies", "third_party", "third-party", "vendor", "vendored",
        "node_modules", "zig-pkg",      "zig-cache",   "zig-out",     "build",  "target",
        "out",          "dist",
    };
    for (excluded) |part| {
        if (std.mem.eql(u8, name, part)) return true;
    }
    return false;
}

test "source width admission includes the last valid length only" {
    const bound: u64 = SourcePolicy.max_source_bytes;
    try std.testing.expect(SourcePolicy.admitsSourceLength(0));
    try std.testing.expect(SourcePolicy.admitsSourceLength(bound - 1));
    try std.testing.expect(!SourcePolicy.admitsSourceLength(bound));
    try std.testing.expect(!SourcePolicy.admitsSourceLength(bound + 1));
    try std.testing.expect(!SourcePolicy.admitsSourceLength(std.math.maxInt(u64)));
}

test "source boundaries reject dependencies and sibling-prefix escapes" {
    const policy: SourcePolicy = .{ .roots = &.{"/project"}, .excludes = &.{ "/project/generated", "scratch" } };
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

// A sparse file exercises the real width boundary without reading 4 GiB.
// A failing allocator distinguishes stat refusal from an attempted read.
test "a source at the width bound is refused from its own stat, before any data is allocated" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    {
        var wide = try tmp.dir.createFile(io, "wide.zig", .{ .read = true });
        defer wide.close(io);
        try wide.setLength(io, SourcePolicy.max_source_bytes);
    }
    try std.testing.expectEqual(
        @as(u64, SourcePolicy.max_source_bytes),
        (try tmp.dir.statFile(io, "wide.zig", .{})).size,
    );

    var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = 0 });
    try std.testing.expectError(
        error.SourceTooWide,
        SourcePolicy.readSourceSentinel(io, tmp.dir, "wide.zig", failing.allocator()),
    );
}

// A source above the old 16 MiB cap still fits the parser's offset domain.
test "a source the policy admits is read whole" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    const admitted = 16 * 1024 * 1024 + 26;
    const prefix = "pub const Value = u32;\n";

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    {
        var file = try tmp.dir.createFile(io, "large.zig", .{ .read = true });
        defer file.close(io);
        try file.writeStreamingAll(io, prefix);
        try file.setLength(io, admitted);
    }

    const source = try SourcePolicy.readSourceSentinel(io, tmp.dir, "large.zig", gpa);
    defer gpa.free(source);
    // Every byte the `stat` admitted, and the sentinel a parser needs after
    // them — neither shortened by the bound on the way in.
    try std.testing.expectEqual(@as(usize, admitted), source.len);
    try std.testing.expectEqualStrings(prefix, source[0..prefix.len]);
    try std.testing.expectEqual(@as(u8, 0), source[source.len]);
}

test "source streaming admits the last valid length and refuses growth to the bound" {
    const gpa = std.testing.allocator;
    const bytes = "pub const Value = u32;\n";

    var exact = std.Io.Reader.fixed(bytes);
    try std.testing.expectError(
        error.SourceTooWide,
        readBoundedSourceSentinel(&exact, gpa, bytes.len),
    );

    var one_wider = std.Io.Reader.fixed(bytes);
    const source = try readBoundedSourceSentinel(&one_wider, gpa, bytes.len + 1);
    defer gpa.free(source);
    try std.testing.expectEqualStrings(bytes, source);
    try std.testing.expectEqual(@as(u8, 0), source[source.len]);
}

test "build metadata exact grants do not widen source admission" {
    const policy: SourcePolicy = .{
        .roots = &.{"/project/src"},
        .build_files = &.{"/project/build.zig"},
    };
    try std.testing.expect(policy.allowsBuildFile("/project/build.zig"));
    try std.testing.expect(policy.allowsBuildFile("/project/src/build.zig"));
    try std.testing.expect(!policy.allowsAbsolutePath("/project/build.zig"));
    try std.testing.expect(policy.rootFor("/project/build.zig") == null);
    try std.testing.expect(!policy.allowsAbsolutePath("/project/secret.zig"));
    try std.testing.expect(!policy.allowsBuildFile("/project-other/build.zig"));
    try std.testing.expect(!policy.allowsBuildFile("/project/build.zig/child/build.zig"));
    try std.testing.expect(!policy.allowsBuildFile("/project/src/main.zig"));
    const default: SourcePolicy = .{ .roots = policy.roots };
    try std.testing.expectEqual(@as(usize, 0), default.build_files.len);
    try std.testing.expect(!default.allowsBuildFile("/project/build.zig"));
    const metadata_only: SourcePolicy = .{ .build_files = policy.build_files };
    try std.testing.expect(metadata_only.allowsBuildFile("/project/build.zig"));
    try std.testing.expect(!metadata_only.allowsAbsolutePath("/project/build.zig"));
}

test "build metadata rejects malformed exact grants" {
    const paths = [_][]const u8{
        "build.zig",
        "project/build.zig",
        "/project/src/../build.zig",
        "/project/./build.zig",
        "/project//build.zig",
        "/project/main.zig",
        "/project/build.zig.zon",
        "/project/build.zig/",
    };
    for (paths) |path| {
        const policy: SourcePolicy = .{ .roots = &.{"/project"}, .build_files = &.{path} };
        try std.testing.expect(!policy.allowsBuildFile(path));
    }
}

test "build metadata exclusions precede ordinary and exact admission" {
    const cases = [_]struct { path: []const u8, excluded: []const u8 }{
        .{ .path = "/project/build.zig", .excluded = "build.zig" },
        .{ .path = "/project/build.zig", .excluded = "/project/build.zig" },
        .{ .path = "/project/build.zig", .excluded = "/project" },
        .{ .path = "/project/generated/deep/build.zig", .excluded = "generated" },
        .{ .path = "/project/generated/deep/build.zig", .excluded = "/project/generated" },
    };
    for (cases) |case| {
        const policy: SourcePolicy = .{
            .roots = &.{"/project"},
            .build_files = &.{case.path},
            .excludes = &.{case.excluded},
        };
        try std.testing.expect(!policy.allowsBuildFile(case.path));
    }
    const sibling: SourcePolicy = .{
        .build_files = &.{"/project/generated-other/build.zig"},
        .excludes = &.{"/project/generated"},
    };
    try std.testing.expect(sibling.allowsBuildFile("/project/generated-other/build.zig"));
}

test "build metadata rejects implicit excluded ancestors" {
    for ([_][]const u8{ ".hidden", "vendor", "zig-pkg", "build", "deps", "target" }) |name| {
        const path = try std.fmt.allocPrint(
            std.testing.allocator,
            "/project/{s}/nested/build.zig",
            .{name},
        );
        defer std.testing.allocator.free(path);
        const policy: SourcePolicy = .{
            .roots = &.{"/project"},
            .build_files = &.{path},
        };
        try std.testing.expect(!policy.allowsBuildFile(path));
    }
}

test "ordinary build metadata preserves the existing source root boundary" {
    const policy: SourcePolicy = .{ .roots = &.{"/tmp/.fixtures/project"} };
    try std.testing.expect(policy.allowsBuildFile("/tmp/.fixtures/project/build.zig"));
    const explicit: SourcePolicy = .{
        .roots = &.{"/tmp/.fixtures/project/src"},
        .build_files = &.{"/tmp/.fixtures/project/build.zig"},
    };
    try std.testing.expect(!explicit.allowsBuildFile("/tmp/.fixtures/project/build.zig"));
}
