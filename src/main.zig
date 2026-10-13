//! zbc CLI — thin shell over the public analysis API.
//! It analyzes selected Zig files with one Session per worker and emits
//! findings even when another selected input fails.
//!
//! Usage:
//!   zbc [options] <file.zig|directory>...
//!
//! Options:
//!   --enable=<list>      Comma-separated invariant names to enable.
//!   --disable=<list>     Comma-separated invariant names to disable.
//!   --arena-init=<csv>   Source patterns that mint a fresh arena.
//!   --arena-kill=<csv>   Source patterns that kill the receiver arena.
//!   --format=<format>    rich, compact, json, or sarif.
//!   --exclude=<path>     Prune a path or basename before opening it.
//!   --jobs=<n>           Worker count (default: CPU count).
//!   --no-color           Disable ANSI color in rich output.
//!   --list-invariants    Print known invariant names.
//!   --list-rules         Print every rule id and title.
//!   --explain <id>       Print the full explainer for one rule.
//!   -h / --help          Print usage and exit 0.
//!
//! JSON and SARIF reports go to stdout. Diagnostics and coverage go to
//! stderr. Exit status is 0 clean, 1 findings, or 2 for an incomplete run.

const std = @import("std");
const lib = @import("lib.zig");
const budget_mod = @import("budget.zig");
const engine = @import("type_engine");

/// Silence ZLS's std.log info/debug output — zbc uses ZLS as a type
/// oracle, not as a language server, so its informational messages
/// ("Loaded build file ...", etc.) are pure noise on stderr that
/// pollutes grep-friendly sweeps.  Only ZLS warnings and errors
/// surface; zbc's own logs are unaffected (they use the default
/// scope).
pub const std_options: std.Options = .{
    .log_scope_levels = &.{
        .{ .scope = .analysis, .level = .warn },
        .{ .scope = .completions, .level = .warn },
        .{ .scope = .config, .level = .warn },
        .{ .scope = .diag, .level = .warn },
        .{ .scope = .goto, .level = .warn },
        .{ .scope = .inlay_hint, .level = .warn },
        .{ .scope = .main, .level = .warn },
        .{ .scope = .server, .level = .warn },
        .{ .scope = .store, .level = .warn },
    },
};

pub fn main(init: std.process.Init) void {
    const status = run(init) catch |err| {
        std.debug.print("zbc: {s}\n", .{@errorName(err)});
        std.process.exit(2);
    };
    std.process.exit(status);
}

fn run(init: std.process.Init) !u8 {
    const gpa = init.gpa;
    const io = init.io;

    var arg_it = try std.process.Args.Iterator.initAllocator(init.minimal.args, gpa);
    defer arg_it.deinit();
    _ = arg_it.next(); // argv[0]

    var paths: std.ArrayListUnmanaged([]const u8) = .empty;
    defer paths.deinit(gpa);
    var enabled: std.ArrayListUnmanaged(lib.Invariant) = .empty;
    defer enabled.deinit(gpa);
    try enabled.appendSlice(gpa, &lib.all_invariants);
    var enabled_explicit = false;
    var format: Format = .rich;
    var color_off = false;
    var jobs: ?usize = null;
    var zig_command: []const u8 = "zig";
    var allow_partial = false;
    var exclusions: std.ArrayListUnmanaged([]const u8) = .empty;
    defer exclusions.deinit(gpa);

    var arena_init_patterns: []const []const u8 = lib.DefaultConfig.arena_init_patterns;
    var arena_kill_patterns: []const []const u8 = lib.DefaultConfig.arena_kill_patterns;
    var pattern_allocations: std.ArrayListUnmanaged([]const []const u8) = .empty;
    defer {
        for (pattern_allocations.items) |slice| gpa.free(slice);
        pattern_allocations.deinit(gpa);
    }

    while (arg_it.next()) |arg| {
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) {
            printUsage();
            return 0;
        }
        if (std.mem.eql(u8, arg, "--list-invariants")) {
            inline for (@typeInfo(lib.Invariant).@"enum".fields) |field| {
                std.debug.print("{s}\n", .{field.name});
            }
            return 0;
        }
        if (std.mem.eql(u8, arg, "--list-rules")) {
            for (lib.rule_catalog) |rule| {
                std.debug.print("{s} — {s}\n", .{ rule.id, rule.title });
            }
            return 0;
        }
        if (std.mem.startsWith(u8, arg, "--explain=")) {
            return explain(arg["--explain=".len..]);
        }
        if (std.mem.eql(u8, arg, "--explain")) {
            const id = arg_it.next() orelse {
                std.debug.print("zbc: --explain requires a rule id (see --list-rules)\n", .{});
                return 2;
            };
            return explain(id);
        }
        if (std.mem.startsWith(u8, arg, "--enable=")) {
            if (!enabled_explicit) {
                enabled.clearRetainingCapacity();
                enabled_explicit = true;
            }
            try parseInvariantList(gpa, arg["--enable=".len..], &enabled, .add);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--disable=")) {
            try parseInvariantList(gpa, arg["--disable=".len..], &enabled, .remove);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--arena-init=")) {
            const slice = try splitCsv(gpa, arg["--arena-init=".len..]);
            try pattern_allocations.append(gpa, slice);
            arena_init_patterns = slice;
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--arena-kill=")) {
            const slice = try splitCsv(gpa, arg["--arena-kill=".len..]);
            try pattern_allocations.append(gpa, slice);
            arena_kill_patterns = slice;
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--format=")) {
            const value = arg["--format=".len..];
            if (std.mem.eql(u8, value, "text") or std.mem.eql(u8, value, "rich")) {
                format = .rich;
            } else if (std.mem.eql(u8, value, "compact")) {
                format = .compact;
            } else if (std.mem.eql(u8, value, "json")) {
                format = .json;
            } else if (std.mem.eql(u8, value, "sarif")) {
                format = .sarif;
            } else {
                std.debug.print("zbc: unknown format `{s}` (expected rich, compact, json, or sarif)\n", .{value});
                return 2;
            }
            continue;
        }
        if (std.mem.eql(u8, arg, "--no-color")) {
            color_off = true;
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--trace=")) {
            const value = arg["--trace=".len..];
            if (std.mem.eql(u8, value, "*")) {
                lib.trace.all_rules = true;
            } else {
                lib.trace.active_rule = value;
            }
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--jobs=")) {
            const value = arg["--jobs=".len..];
            const count = std.fmt.parseInt(usize, value, 10) catch {
                std.debug.print("zbc: invalid --jobs value `{s}` (expected a positive integer)\n", .{value});
                return 2;
            };
            if (count == 0) {
                std.debug.print("zbc: invalid --jobs value `{s}` (expected a positive integer)\n", .{value});
                return 2;
            }
            jobs = count;
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--zig=")) {
            zig_command = arg["--zig=".len..];
            if (zig_command.len == 0) {
                std.debug.print("zbc: --zig requires a non-empty path to a Zig 0.16.0 executable\n", .{});
                return 2;
            }
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--exclude=")) {
            const path = arg["--exclude=".len..];
            if (path.len == 0) {
                std.debug.print("zbc: --exclude requires a non-empty path or name\n", .{});
                return 2;
            }
            try exclusions.append(gpa, path);
            continue;
        }
        if (std.mem.eql(u8, arg, "--allow-partial")) {
            allow_partial = true;
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--")) {
            std.debug.print("zbc: unknown flag: {s}\n", .{arg});
            printUsage();
            return 2;
        }
        try paths.append(gpa, arg);
    }

    if (paths.items.len == 0) {
        printUsage();
        return 2;
    }

    var selection = SourceSelection.init(gpa, io, exclusions.items);
    defer selection.deinit();
    try selection.collect(paths.items);
    const selected_paths = selection.files.keys();
    var failed: usize = selection.failures.items.len;
    for (selection.failures.items) |failure| {
        if (failure.excluded_by) |exclusion| {
            std.debug.print("zbc: cannot select {s}: excluded by --exclude={s}\n", .{ failure.path, exclusion });
        } else {
            std.debug.print("zbc: cannot select {s}: {s}\n", .{ failure.path, @errorName(failure.err) });
        }
    }

    const config: lib.Config = .{
        .arena_init_patterns = arena_init_patterns,
        .arena_kill_patterns = arena_kill_patterns,
        .enabled = enabled.items,
    };
    const tasks = try gpa.alloc(Task, selected_paths.len);
    defer gpa.free(tasks);
    for (selected_paths, tasks) |path, *task| {
        task.* = .{
            .path = path,
            .config = &config,
            .analysis = .{ .problems = &.{}, .incomplete = &.{} },
            .err = null,
            .parse_failure = null,
            .budget = null,
            .unresolved_imports = 0,
        };
    }
    defer for (tasks) |*task| {
        lib.freeAnalysis(gpa, task.analysis);
        if (task.parse_failure) |failure| {
            if (failure.source_path) |path| gpa.free(path);
        }
        if (task.budget) |*diagnostic| diagnostic.deinit(gpa);
    };

    // A toolchain failure is a property of the run, not of any file: it is
    // reported once here, and every selected file counts as failed without
    // a line of its own.
    var toolchain_failed = false;
    if (tasks.len != 0) {
        var toolchain_failure: lib.ToolchainFailure = .{};
        var toolchain: ?lib.Toolchain = lib.Toolchain.init(gpa, io, zig_command, &toolchain_failure) catch |err| blk: {
            std.debug.print(
                "zbc: cannot discover the Zig toolchain ({s}): `{s} env` {f}\n" ++
                    "zbc: zbc runs `zig env` from PATH (or --zig=<path>) and needs Zig {s}\n",
                .{ @errorName(err), zig_command, toolchain_failure, @import("builtin").zig_version_string },
            );
            toolchain_failed = true;
            for (tasks) |*task| task.err = err;
            break :blk null;
        };
        defer if (toolchain) |*shared| shared.deinit();
        if (toolchain) |*shared| {
            analyzeTasks(gpa, io, tasks, selection.policy(), jobs, shared) catch |err| {
                for (tasks) |*task| {
                    if (task.err == null) task.err = err;
                }
            };
        }
    }

    var all_problems: std.ArrayListUnmanaged(IndexedProblem) = .empty;
    defer all_problems.deinit(gpa);
    var analysis_failed: usize = 0;
    var partial: usize = 0;
    var unresolved_imports: usize = 0;
    for (tasks) |*task| {
        unresolved_imports += task.unresolved_imports;
        if (task.err) |err| {
            analysis_failed += 1;
            if (toolchain_failed) {
                failed += 1;
                continue;
            }
            if (task.parse_failure) |failure| {
                if (failure.source_path) |source_path| {
                    if (!std.mem.eql(u8, source_path, task.path)) {
                        std.debug.print("zbc: analysis incomplete for {s}: imported source failed\n", .{task.path});
                    }
                }
                std.debug.print("{s}:{}:{}: parse error: {s} (Zig {s})\n", .{
                    failure.source_path orelse task.path,
                    failure.position.line,
                    failure.position.column,
                    failure.reason,
                    @import("builtin").zig_version_string,
                });
            } else if (task.budget) |info| {
                std.debug.print("zbc: cannot analyze {s}: {s} — {s} limit {d} reached {d}", .{
                    task.path, @errorName(err), info.limit.label(), info.limit_value, info.reached,
                });
                if (info.function.slice().len != 0) {
                    std.debug.print(" in fn `{s}`", .{info.function.slice()});
                }
                printBudgetPosition(info);
            } else if (err == error.AnalysisBudgetExceeded) {
                std.debug.print(
                    "zbc: cannot analyze {s}: analysis budget exhausted without a recorded limit — the walk that gave up did not report which cap it hit\n",
                    .{task.path},
                );
            } else {
                std.debug.print("zbc: cannot analyze {s}: {s}\n", .{ task.path, @errorName(err) });
            }
            failed += 1;
            continue;
        }
        if (task.analysis.incomplete.len != 0) {
            partial += 1;
            for (task.analysis.incomplete) |part| printIncomplete(task.path, part);
        }
        for (task.analysis.problems) |problem| {
            try all_problems.append(gpa, .{ .path = task.path, .problem = problem });
        }
    }

    std.mem.sort(IndexedProblem, all_problems.items, {}, indexedProblemLess);
    // Each selected file lands in exactly one of analyzed, partial, failed.
    const analyzed = tasks.len - analysis_failed - partial;
    const selected = analyzed + partial + failed;
    const findings = all_problems.items.len;
    const use_color = !color_off and (std.Io.File.stderr().isTty(io) catch false);
    var src_cache: SourceCache = .{ .gpa = gpa, .io = io };
    defer src_cache.deinit();

    var stdout_buffer: [64 * 1024]u8 = undefined;
    var stdout_file = std.Io.File.stdout().writer(io, &stdout_buffer);
    const stdout = &stdout_file.interface;
    switch (format) {
        .json => {
            try stdout.writeByte('[');
            var first = true;
            for (all_problems.items) |item| try printOneProblemJson(stdout, item.path, item.problem, &first);
            if (!first) try stdout.writeByte('\n');
            try stdout.writeAll("]\n");
        },
        .sarif => try printSarif(gpa, stdout, all_problems.items, failed == 0 and partial == 0),
        .compact => {
            for (all_problems.items) |item| printOneProblemCompact(item.path, item.problem);
        },
        .rich => {
            for (all_problems.items) |item| printOneProblemRich(&src_cache, item.path, item.problem, use_color);
        },
    }
    try stdout.flush();
    std.debug.print("zbc: selected={} analyzed={} partial={} failed={} findings={} parser=Zig-{s} unresolved-import-lookups={}\n", .{
        selected,
        analyzed,
        partial,
        failed,
        findings,
        @import("builtin").zig_version_string,
        unresolved_imports,
    });
    // A budget-partial file keeps its findings; only an opted-in caller may
    // let partial coverage alone pass. Failed files always fail the run.
    if (failed != 0 or (partial != 0 and !allow_partial)) return 2;
    return if (findings != 0) 1 else 0;
}

fn splitCsv(gpa: std.mem.Allocator, csv: []const u8) ![]const []const u8 {
    var out: std.ArrayListUnmanaged([]const u8) = .empty;
    errdefer out.deinit(gpa);
    var it = std.mem.splitScalar(u8, csv, ',');
    while (it.next()) |raw| {
        const trimmed = std.mem.trim(u8, raw, " \t");
        if (trimmed.len == 0) continue;
        try out.append(gpa, trimmed);
    }
    return out.toOwnedSlice(gpa);
}

/// Selects and deduplicates explicit files and walked source roots.
/// Every exclusion decision uses SourcePolicy before a source can be read.
const SourceSelection = struct {
    gpa: std.mem.Allocator,
    io: std.Io,
    arena: std.heap.ArenaAllocator,
    roots: std.StringArrayHashMapUnmanaged(void) = .empty,
    files: std.StringArrayHashMapUnmanaged(void) = .empty,
    failures: std.ArrayListUnmanaged(Failure) = .empty,
    excludes: []const []const u8,

    const Failure = struct {
        path: []const u8,
        err: anyerror,
        excluded_by: ?[]const u8 = null,
    };
    const Input = struct { path: []const u8, directory: bool };

    fn init(gpa: std.mem.Allocator, io: std.Io, excludes: []const []const u8) SourceSelection {
        return .{ .gpa = gpa, .io = io, .arena = .init(gpa), .excludes = excludes };
    }

    fn deinit(self: *SourceSelection) void {
        self.failures.deinit(self.gpa);
        self.files.deinit(self.gpa);
        self.roots.deinit(self.gpa);
        self.arena.deinit();
    }

    fn policy(self: *const SourceSelection) lib.SourcePolicy {
        return .{ .roots = self.roots.keys(), .excludes = self.excludes };
    }
    fn containsParentTraversal(path: []const u8) bool {
        var components = std.mem.tokenizeAny(u8, path, "/\\\\");
        while (components.next()) |component| {
            if (std.mem.eql(u8, component, "..")) return true;
        }
        return false;
    }

    fn filesystemRoot(path: []const u8) []const u8 {
        var root = path;
        while (std.fs.path.dirname(root)) |parent| {
            if (parent.len == root.len) break;
            root = parent;
        }
        return root;
    }

    fn allowsPath(self: *const SourceSelection, root: []const u8, path: []const u8) bool {
        const source_policy: lib.SourcePolicy = .{
            .roots = &.{root},
            .excludes = self.excludes,
        };
        return source_policy.allowsAbsolutePath(path);
    }

    fn configuredExclusion(self: *const SourceSelection, path: []const u8) ?[]const u8 {
        const root = filesystemRoot(path);
        const baseline: lib.SourcePolicy = .{ .roots = &.{root} };
        if (!baseline.allowsAbsolutePath(path)) return null;
        for (self.excludes) |excluded| {
            const source_policy: lib.SourcePolicy = .{
                .roots = &.{root},
                .excludes = &.{excluded},
            };
            if (!source_policy.allowsAbsolutePath(path)) return excluded;
        }
        return null;
    }

    fn recordFailure(
        self: *SourceSelection,
        path: []const u8,
        err: anyerror,
        excluded_by: ?[]const u8,
    ) !void {
        const saved_path = try self.arena.allocator().dupe(u8, path);
        try self.failures.append(self.gpa, .{
            .path = saved_path,
            .err = err,
            .excluded_by = excluded_by,
        });
    }

    fn fail(self: *SourceSelection, path: []const u8, err: anyerror) !void {
        try self.recordFailure(path, err, null);
    }

    fn failExcludedPath(self: *SourceSelection, original: []const u8, path: []const u8) !void {
        if (self.configuredExclusion(path)) |excluded| {
            try self.recordFailure(original, error.SourceExcluded, excluded);
        } else {
            try self.fail(original, error.SourceExcluded);
        }
    }

    fn canonical(self: *SourceSelection, path: []const u8) ![]const u8 {
        var buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
        const len = try std.Io.Dir.cwd().realPathFile(self.io, path, &buffer);
        return self.arena.allocator().dupe(u8, buffer[0..len]);
    }

    fn normalizeExclusions(self: *SourceSelection, cwd: []const u8) !void {
        const arena = self.arena.allocator();
        var normalized: std.ArrayListUnmanaged([]const u8) = .empty;
        defer normalized.deinit(arena);
        for (self.excludes) |excluded| {
            if (excluded.len == 0) return error.InvalidExclusion;
            if (std.mem.indexOfAny(u8, excluded, "/\\\\") == null) {
                try normalized.append(arena, excluded);
                continue;
            }

            const lexical = try std.fs.path.resolve(arena, &.{ cwd, excluded });
            try normalized.append(arena, lexical);
            const canonical_path = self.canonical(lexical) catch |err| {
                if (err == error.OutOfMemory) return err;
                continue;
            };
            if (!std.mem.eql(u8, lexical, canonical_path)) {
                try normalized.append(arena, canonical_path);
            }
        }
        self.excludes = try normalized.toOwnedSlice(arena);
    }

    fn collect(self: *SourceSelection, paths: []const []const u8) !void {
        const cwd = try self.canonical(".");
        try self.normalizeExclusions(cwd);

        var inputs: std.ArrayListUnmanaged(Input) = .empty;
        defer inputs.deinit(self.gpa);
        for (paths) |path| {
            const raw_absolute = if (std.fs.path.isAbsolute(path))
                path
            else
                try std.fs.path.join(self.arena.allocator(), &.{ cwd, path });
            if (containsParentTraversal(raw_absolute)) {
                try self.failExcludedPath(path, raw_absolute);
                continue;
            }
            const lexical = if (std.fs.path.isAbsolute(path))
                try std.fs.path.resolve(self.arena.allocator(), &.{path})
            else
                try std.fs.path.resolve(self.arena.allocator(), &.{ cwd, path });
            const cwd_policy: lib.SourcePolicy = .{ .roots = &.{cwd} };
            const boundary = if (!std.fs.path.isAbsolute(path) or cwd_policy.rootFor(lexical) != null)
                cwd
            else
                filesystemRoot(lexical);
            if (!self.allowsPath(boundary, lexical)) {
                try self.failExcludedPath(path, lexical);
                continue;
            }
            const absolute = self.canonical(lexical) catch |err| {
                try self.fail(path, err);
                continue;
            };
            if (!self.allowsPath(boundary, absolute)) {
                try self.failExcludedPath(path, absolute);
                continue;
            }
            const stat = std.Io.Dir.cwd().statFile(self.io, absolute, .{}) catch |err| {
                try self.fail(path, err);
                continue;
            };
            const directory = stat.kind == .directory;
            if (!directory and !std.mem.endsWith(u8, absolute, ".zig")) {
                try self.fail(path, error.UnsupportedSourceFile);
                continue;
            }
            if (directory) try self.roots.put(self.gpa, absolute, {});
            try inputs.append(self.gpa, .{ .path = absolute, .directory = directory });
        }

        std.mem.sort(Input, inputs.items, {}, struct {
            fn less(_: void, a: Input, b: Input) bool {
                const left = if (a.directory) a.path else std.fs.path.dirname(a.path).?;
                const right = if (b.directory) b.path else std.fs.path.dirname(b.path).?;
                return std.mem.lessThan(u8, left, right);
            }
        }.less);
        for (inputs.items) |input| {
            if (input.directory) continue;
            const parent = std.fs.path.dirname(input.path).?;
            if (self.policy().rootFor(parent) == null) {
                try self.roots.put(self.gpa, parent, {});
            }
        }
        for (inputs.items) |input| {
            if (!self.policy().allowsAbsolutePath(input.path)) {
                try self.failExcludedPath(input.path, input.path);
                continue;
            }
            if (input.directory) {
                try self.walk(input.path);
            } else {
                _ = try self.files.put(self.gpa, input.path, {});
            }
        }
    }

    fn walk(self: *SourceSelection, root: []const u8) !void {
        var pending: std.ArrayListUnmanaged([]const u8) = .empty;
        defer {
            for (pending.items) |path| self.gpa.free(path);
            pending.deinit(self.gpa);
        }
        try pending.ensureUnusedCapacity(self.gpa, 1);
        pending.appendAssumeCapacity(try self.gpa.dupe(u8, root));
        while (pending.pop()) |dir_path| {
            defer self.gpa.free(dir_path);
            const source_policy = self.policy();
            if (!source_policy.allowsAbsolutePath(dir_path)) {
                continue;
            }
            var dir = std.Io.Dir.cwd().openDir(self.io, dir_path, .{ .iterate = true }) catch |err| {
                try self.fail(dir_path, err);
                continue;
            };
            defer dir.close(self.io);
            var iterator = dir.iterate();
            while (true) {
                const entry = iterator.next(self.io) catch |err| {
                    try self.fail(dir_path, err);
                    break;
                } orelse break;
                if (entry.kind == .directory) {
                    const joined = try std.fs.path.join(self.arena.allocator(), &.{ dir_path, entry.name });
                    if (!source_policy.allowsAbsolutePath(joined)) continue;
                    const absolute = self.canonical(joined) catch |err| {
                        try self.fail(joined, err);
                        continue;
                    };
                    if (source_policy.allowsAbsolutePath(absolute)) {
                        try pending.ensureUnusedCapacity(self.gpa, 1);
                        pending.appendAssumeCapacity(try self.gpa.dupe(u8, absolute));
                    }
                    continue;
                }
                if (entry.kind != .file or !std.mem.endsWith(u8, entry.name, ".zig")) continue;
                const full = try std.fs.path.join(self.arena.allocator(), &.{ dir_path, entry.name });
                if (!source_policy.allowsAbsolutePath(full)) continue;
                const absolute = self.canonical(full) catch |err| {
                    try self.fail(full, err);
                    continue;
                };
                if (source_policy.allowsAbsolutePath(absolute) and !self.files.contains(absolute)) {
                    _ = try self.files.put(self.gpa, absolute, {});
                }
            }
        }
    }
};

const Format = enum { rich, compact, json, sarif };
const Op = enum { add, remove };

fn parseInvariantList(
    gpa: std.mem.Allocator,
    csv: []const u8,
    list: *std.ArrayListUnmanaged(lib.Invariant),
    op: Op,
) !void {
    var it = std.mem.splitScalar(u8, csv, ',');
    while (it.next()) |raw| {
        const name = std.mem.trim(u8, raw, " \t");
        if (name.len == 0) continue;
        const inv = lib.invariantFromName(name) orelse {
            std.debug.print("zbc: unknown invariant `{s}`; --list-invariants for valid names\n", .{name});
            std.process.exit(2);
        };
        switch (op) {
            .add => {
                if (!containsInvariant(list.items, inv)) try list.append(gpa, inv);
            },
            .remove => {
                var i: usize = 0;
                while (i < list.items.len) {
                    if (list.items[i] == inv) {
                        _ = list.orderedRemove(i);
                    } else i += 1;
                }
            },
        }
    }
}

fn containsInvariant(slice: []const lib.Invariant, inv: lib.Invariant) bool {
    for (slice) |e| if (e == inv) return true;
    return false;
}

fn explain(id: []const u8) u8 {
    if (lib.lookupRule(id)) |rule| {
        std.debug.print("{s}", .{rule.body});
        return 0;
    }
    std.debug.print("zbc: no rule named `{s}` (see --list-rules)\n", .{id});
    return 2;
}

fn printUsage() void {
    std.debug.print(
        \\usage: zbc [options] <file.zig>...
        \\
        \\Escape analysis: flags slices borrowed from a function-local
        \\arena that are returned past the arena's death, plus a battery
        \\of pattern-detector rules for memory-lifetime bug classes.
        \\
        \\options:
        \\  --enable=a,b,c        Enable only these invariants.
        \\  --disable=a,b         Disable these invariants from the set.
        \\  --arena-init=A,B      Patterns that mint a fresh arena
        \\                        (default: ArenaAllocator.init).
        \\  --arena-kill=A,B      Patterns that kill the receiver arena
        \\                        (default: .deinit().
        \\  --format=rich|compact|json|sarif
        \\                        Output format.  Default `rich` shows
        \\                        gcc/clang-style header (path:line:col:
        \\                        error(rule-id): message) plus a
        \\                        Rust-style source-context block.
        \\                        `compact` is single-line grep-friendly.
        \\                        `json` is a flat array; `sarif` is
        \\                        SARIF 2.1.0 (GitHub code scanning etc.).
        \\  --exclude=<path>     Prune a path or basename from traversal.
        \\  --jobs=<n>           Worker count.  Default is the CPU count.
        \\  --zig=<path>         Zig 0.16.0 executable whose `zig env` locates
        \\                        the std library.  Default: `zig` from PATH.
        \\  --no-color            Disable ANSI color in `rich` output.
        \\  --allow-partial       Do not exit 2 only because a file was
        \\                        partially analyzed (budget exhausted).
        \\                        Findings still exit 1; failed files and
        \\                        operational errors still exit 2.
        \\  --list-invariants     Print known invariant names and exit.
        \\  --list-rules          Print every rule id and one-line title
        \\                        and exit.
        \\  --explain <id>        Print the full explainer for one rule
        \\                        (use --list-rules for valid ids).
        \\  -h, --help            Print this help.
        \\
    , .{});
}

const Task = struct {
    path: []const u8,
    config: *const lib.Config,
    analysis: lib.Analysis,
    err: ?anyerror,
    parse_failure: ?lib.ParseFailure,
    budget: ?budget_mod.OwnedDiagnostic,
    unresolved_imports: usize,
};

const IndexedProblem = struct {
    path: []const u8,
    problem: lib.Problem,
};

fn indexedProblemLess(_: void, a: IndexedProblem, b: IndexedProblem) bool {
    const path_cmp = std.mem.order(u8, a.path, b.path);
    if (path_cmp != .eq) return path_cmp == .lt;
    if (a.problem.start.line != b.problem.start.line)
        return a.problem.start.line < b.problem.start.line;
    return a.problem.start.column < b.problem.start.column;
}

const WorkerCtx = struct {
    tasks: []Task,
    next: *std.atomic.Value(usize),
    gpa: std.mem.Allocator,
    io: std.Io,
    toolchain: *const lib.Toolchain,
    policy: lib.SourcePolicy,
};

fn analyzeTasks(
    gpa: std.mem.Allocator,
    io: std.Io,
    tasks: []Task,
    policy: lib.SourcePolicy,
    jobs: ?usize,
    toolchain: *const lib.Toolchain,
) !void {
    if (tasks.len == 0) return;
    const cpu_count = std.Thread.getCpuCount() catch 4;
    const worker_count = jobs orelse cpu_count;
    const n_workers = @max(1, @min(worker_count, tasks.len));
    // `--jobs=N` runs exactly N sessions, each on a spawned worker; the
    // calling thread only joins them (see the stack note below).
    const workers = try gpa.alloc(std.Thread, n_workers);
    defer gpa.free(workers);
    var next_task: std.atomic.Value(usize) = .init(0);
    const ctx: WorkerCtx = .{
        .tasks = tasks,
        .next = &next_task,
        .gpa = gpa,
        .io = io,
        .toolchain = toolchain,
        .policy = policy,
    };

    // Resolution recurses deeply, and a Debug frame of the type engine is
    // hundreds of KiB, so the 16 MiB `std.Thread` default overflows on a
    // legitimate chain. The main thread's stack is smaller still (the
    // process rlimit), so it runs analysis only when no worker could start.
    var spawned: usize = 0;
    for (workers) |*worker| {
        worker.* = std.Thread.spawn(
            .{ .stack_size = engine.resolve_stack_bytes },
            workerLoop,
            .{ctx},
        ) catch break;
        spawned += 1;
    }
    if (spawned == 0) workerLoop(ctx);
    for (workers[0..spawned]) |worker| worker.join();
}

fn workerLoop(ctx: WorkerCtx) void {
    var session: lib.Session = undefined;
    session.initWithToolchain(ctx.gpa, ctx.io, ctx.policy, ctx.toolchain) catch |err| {
        while (true) {
            const index = ctx.next.fetchAdd(1, .monotonic);
            if (index >= ctx.tasks.len) return;
            ctx.tasks[index].err = err;
        }
    };
    defer session.deinit();

    while (true) {
        const index = ctx.next.fetchAdd(1, .monotonic);
        if (index >= ctx.tasks.len) return;
        runOne(&ctx.tasks[index], ctx.gpa, &session);
    }
}

fn ownParseFailure(gpa: std.mem.Allocator, failure: lib.ParseFailure) !lib.ParseFailure {
    var owned = failure;
    if (failure.source_path) |path| owned.source_path = try gpa.dupe(u8, path);
    return owned;
}

fn unresolvedDelta(after: usize, before: usize) usize {
    return if (after >= before) after - before else after;
}

fn runOne(t: *Task, gpa: std.mem.Allocator, session: *lib.Session) void {
    const unresolved_before = session.project.unresolved_imports;
    const analysis = lib.analyzeEscape(session, t.path, t.config) catch |err| {
        t.err = err;
        t.unresolved_imports = unresolvedDelta(session.project.unresolved_imports, unresolved_before);
        if (err == error.InvalidSyntax) {
            if (session.parse_failure) |failure| {
                t.parse_failure = ownParseFailure(gpa, failure) catch {
                    t.err = error.OutOfMemory;
                    return;
                };
            }
        } else if (err == error.AnalysisBudgetExceeded) {
            if (budget_mod.take()) |diagnostic| {
                t.budget = diagnostic.owned(gpa) catch {
                    t.err = error.OutOfMemory;
                    return;
                };
            }
        }
        return;
    };
    t.analysis = analysis;
    t.unresolved_imports = unresolvedDelta(session.project.unresolved_imports, unresolved_before);
}

/// One stderr line per part of a file that gave up on an analysis budget.
fn printIncomplete(path: []const u8, part: lib.Incomplete) void {
    // A failed summary pass names the same function a failed lowering would.
    const kind = switch (part.kind) {
        .function, .summary => "fn",
        .rule => "rule",
    };
    std.debug.print("zbc: incomplete {s}: {s} {s}", .{ path, kind, part.name });
    const info = part.budget orelse {
        std.debug.print(" — analysis budget exhausted without a recorded limit\n", .{});
        return;
    };
    std.debug.print(" — {s} limit {d} reached {d}", .{ info.limit.label(), info.limit_value, info.reached });
    printBudgetPosition(info);
}

/// Unknown source identity must not turn foreign coordinates into input sites.
fn printBudgetPosition(info: budget_mod.OwnedDiagnostic) void {
    const document = if (info.document.len != 0) info.document else "<unknown>";
    if (info.line != 0) {
        std.debug.print(" at {s}:{d}:{d}\n", .{ document, info.line, info.column });
    } else {
        std.debug.print(" at {s}+{d}\n", .{ document, info.byte });
    }
}

fn printOneProblemCompact(path: []const u8, p: lib.Problem) void {
    // gcc/clang-style header — path:line:col first, then
    // `severity(rule-id):`, then message.  Grep-friendly because the
    // file:line:col leads, and the rule_id is parenthesised inline.
    std.debug.print("{s}:{}:{}: {s}({s}): {s}", .{
        path,
        p.start.line,
        p.start.column,
        severityName(p.severity),
        p.rule_id,
        p.message,
    });
    // Tack each note's location and label onto the same line so the
    // single-line shape stays grep-friendly while still carrying the
    // related-event spans.
    for (p.notes) |n| {
        std.debug.print(" ({s} at {s}:{}:{})", .{
            n.label, path, n.start.line, n.start.column,
        });
    }
    std.debug.print("\n", .{});
}

// ── Rich renderer (gcc/clang header + Rust source-context block) ─────

const SourceCache = struct {
    gpa: std.mem.Allocator,
    io: std.Io,
    entries: std.StringHashMapUnmanaged([]u8) = .empty,

    fn get(self: *SourceCache, path: []const u8) ?[]const u8 {
        if (self.entries.get(path)) |s| return s;
        const bytes = std.Io.Dir.cwd().readFileAlloc(
            self.io,
            path,
            self.gpa,
            std.Io.Limit.limited(16 * 1024 * 1024),
        ) catch return null;
        const key = self.gpa.dupe(u8, path) catch {
            self.gpa.free(bytes);
            return null;
        };
        self.entries.put(self.gpa, key, bytes) catch {
            self.gpa.free(bytes);
            self.gpa.free(key);
            return null;
        };
        return bytes;
    }

    fn deinit(self: *SourceCache) void {
        var it = self.entries.iterator();
        while (it.next()) |e| {
            self.gpa.free(e.key_ptr.*);
            self.gpa.free(e.value_ptr.*);
        }
        self.entries.deinit(self.gpa);
    }
};

const Ansi = struct {
    reset: []const u8,
    bold: []const u8,
    red: []const u8,
    yellow: []const u8,
    blue: []const u8,
    cyan: []const u8,

    fn pick(use_color: bool) Ansi {
        return if (use_color) .{
            .reset = "\x1b[0m",
            .bold = "\x1b[1m",
            .red = "\x1b[31m",
            .yellow = "\x1b[33m",
            .blue = "\x1b[34m",
            .cyan = "\x1b[36m",
        } else .{
            .reset = "",
            .bold = "",
            .red = "",
            .yellow = "",
            .blue = "",
            .cyan = "",
        };
    }
};

fn printOneProblemRich(
    cache: *SourceCache,
    path: []const u8,
    p: lib.Problem,
    use_color: bool,
) void {
    const c = Ansi.pick(use_color);
    const sev_color = switch (p.severity) {
        .@"error" => c.red,
        .warning => c.yellow,
        .off => c.cyan,
    };

    // Header:  path:line:col: error(heap-use-after-free): use of `x` after free
    //
    // gcc/clang-style: file location leads, then `severity(rule-id):`,
    // then the message.  Editors / `grep -E` patterns / IDE jump-to-
    // diagnostic tooling all parse `path:line:col` at the start of
    // the line, so the rich format keeps the same shape as compact —
    // just with source context underneath.
    std.debug.print("{s}:{}:{}: ", .{ path, p.start.line, p.start.column });
    std.debug.print("{s}{s}{s}{s}", .{ c.bold, sev_color, severityName(p.severity), c.reset });
    std.debug.print("({s}{s}{s})", .{ c.cyan, p.rule_id, c.reset });
    std.debug.print(": {s}{s}{s}\n", .{ c.bold, p.message, c.reset });

    // Source-context block — no separate `--> path:line:col` line,
    // since the gcc/clang-style header already carries it.
    const src_opt = cache.get(path);
    const gutter_width = pickGutterWidth(p);

    if (src_opt) |src| {
        // Blank gutter row before the primary span.
        pad(gutter_width);
        std.debug.print(" {s}|{s}\n", .{ c.blue, c.reset });

        renderSpan(src, p.start, p.end, "", sev_color, '^', c, gutter_width);

        for (p.notes) |n| {
            // For notes in the SAME file, render with the same gutter
            // alignment so the eye can connect them.  External files
            // (none today, but cheap to support) would print their own
            // path lines.
            pad(gutter_width);
            std.debug.print(" {s}|{s}\n", .{ c.blue, c.reset });
            renderSpan(src, n.start, n.end, n.label, c.blue, '-', c, gutter_width);
        }
    } else {
        // Source unavailable — fall back to printing the note locations
        // textually so we don't drop the info.
        for (p.notes) |n| {
            pad(gutter_width);
            std.debug.print(" {s}={s} {s} at {s}:{}:{}\n", .{
                c.blue, c.reset, n.label, path, n.start.line, n.start.column,
            });
        }
    }

    // = help: footer — point at the catalog when the rule is in it.
    // Matches Rustc's `= help: for more information about this error,
    // try \`rustc --explain E0382\`.` line.  Only print when the rule
    // actually has an explainer; suppress otherwise so internal /
    // experimental rules don't promise docs that don't exist.
    if (lib.lookupRule(p.rule_id) != null) {
        pad(gutter_width);
        std.debug.print(" {s}={s} {s}help{s}: for more information, run `zbc --explain {s}`\n", .{
            c.blue, c.reset, c.bold, c.reset, p.rule_id,
        });
    }

    std.debug.print("\n", .{});
}

/// Number of digits in the widest line number we'll print for this
/// problem — primary span + notes.  Gutter width = max digits + 1
/// space, matching Rustc.
fn pickGutterWidth(p: lib.Problem) usize {
    var max_line: u32 = p.start.line;
    for (p.notes) |n| {
        if (n.start.line > max_line) max_line = n.start.line;
    }
    return countDigits(max_line);
}

fn countDigits(n: u32) usize {
    if (n == 0) return 1;
    var v = n;
    var d: usize = 0;
    while (v > 0) : (v /= 10) d += 1;
    return d;
}

fn pad(width: usize) void {
    var i: usize = 0;
    while (i < width) : (i += 1) std.debug.print(" ", .{});
}

fn renderSpan(
    src: []const u8,
    start: lib.Pos,
    end: lib.Pos,
    label: []const u8,
    label_color: []const u8,
    caret_char: u8,
    c: Ansi,
    gutter_width: usize,
) void {
    // Find the byte range of `start.line` in src.
    const line_text = sliceLine(src, start.byte);
    // Print the source line:  NNN | <text>
    const line_str_buf: [16]u8 = @splat(0);
    var buf = line_str_buf;
    const ln_str = std.fmt.bufPrint(&buf, "{}", .{start.line}) catch "?";
    const lead = if (gutter_width > ln_str.len) gutter_width - ln_str.len else 0;
    pad(lead);
    std.debug.print("{s}{s} |{s} {s}\n", .{ c.blue, ln_str, c.reset, line_text });
    // Underline row.  Columns are 1-indexed.
    pad(gutter_width);
    std.debug.print(" {s}|{s} ", .{ c.blue, c.reset });
    // Pad to start column.
    if (start.column > 1) {
        var i: u32 = 1;
        while (i < start.column) : (i += 1) std.debug.print(" ", .{});
    }
    // Caret length: end.column - start.column on same line; otherwise
    // 1 (multi-line spans are rare here).
    var caret_len: u32 = 1;
    if (end.line == start.line and end.column > start.column) {
        caret_len = end.column - start.column;
    }
    std.debug.print("{s}", .{label_color});
    var i: u32 = 0;
    while (i < caret_len) : (i += 1) std.debug.print("{c}", .{caret_char});
    if (label.len > 0) {
        std.debug.print(" {s}", .{label});
    }
    std.debug.print("{s}\n", .{c.reset});
}

/// Slice `src` to the line containing `byte_offset` (without the
/// newline).  If `byte_offset` is past EOF, returns an empty slice.
fn sliceLine(src: []const u8, byte_offset: u32) []const u8 {
    if (byte_offset >= src.len) return "";
    var ls: usize = byte_offset;
    while (ls > 0 and src[ls - 1] != '\n') ls -= 1;
    var le: usize = byte_offset;
    while (le < src.len and src[le] != '\n') le += 1;
    return src[ls..le];
}

fn printOneProblemJson(
    writer: *std.Io.Writer,
    path: []const u8,
    p: lib.Problem,
    first: *bool,
) !void {
    if (first.*) {
        try writer.writeAll("\n  ");
        first.* = false;
    } else {
        try writer.writeAll(",\n  ");
    }
    try writer.writeAll("{\"path\":\"");
    try writeJsonEscaped(writer, path);
    try writer.print(
        "\",\"rule_id\":\"{s}\",\"severity\":\"{s}\"," ++
            "\"start\":{{\"line\":{},\"column\":{},\"byte\":{}}}," ++
            "\"end\":{{\"line\":{},\"column\":{},\"byte\":{}}}," ++
            "\"message\":\"",
        .{
            p.rule_id,
            severityName(p.severity),
            p.start.line,
            p.start.column,
            p.start.byte,
            p.end.line,
            p.end.column,
            p.end.byte,
        },
    );
    try writeJsonEscaped(writer, p.message);
    try writer.writeAll("\",\"notes\":[");
    for (p.notes, 0..) |note, i| {
        if (i > 0) try writer.writeByte(',');
        try writer.print(
            "{{\"start\":{{\"line\":{},\"column\":{},\"byte\":{}}}," ++
                "\"end\":{{\"line\":{},\"column\":{},\"byte\":{}}}," ++
                "\"label\":\"",
            .{
                note.start.line, note.start.column, note.start.byte,
                note.end.line,   note.end.column,   note.end.byte,
            },
        );
        try writeJsonEscaped(writer, note.label);
        try writer.writeAll("\"}");
    }
    try writer.print("],\"verdict\":\"{s}\",\"witness\":", .{verdictName(p.verdict)});
    if (p.witness) |witness| {
        try writer.writeByte('"');
        try writeJsonEscaped(writer, witness);
        try writer.writeByte('"');
    } else {
        try writer.writeAll("null");
    }
    try writer.writeByte('}');
}

fn verdictName(v: lib.Verdict) []const u8 {
    return switch (v) {
        .unknown => "unknown",
        .confirmed => "confirmed",
        .refuted => "refuted",
    };
}

/// SARIF 2.1.0 severity level for a zbc severity. SARIF levels are
/// none|note|warning|error.
fn sarifLevel(s: lib.Severity) []const u8 {
    return switch (s) {
        .@"error" => "error",
        .warning => "warning",
        .off => "none",
    };
}

fn printSarifRegion(writer: *std.Io.Writer, start: lib.Pos, end: lib.Pos) !void {
    const byte_len: u32 = if (end.byte >= start.byte) end.byte - start.byte else 0;
    try writer.print(
        "{{\"startLine\":{},\"startColumn\":{},\"endLine\":{},\"endColumn\":{}," ++
            "\"byteOffset\":{},\"byteLength\":{}}}",
        .{ start.line, start.column, end.line, end.column, start.byte, byte_len },
    );
}

fn writeSarifUri(writer: *std.Io.Writer, path: []const u8) !void {
    const hex = "0123456789ABCDEF";
    try writer.writeAll("file://");
    for (path) |byte| {
        const allowed = (byte >= 'a' and byte <= 'z') or
            (byte >= 'A' and byte <= 'Z') or
            (byte >= '0' and byte <= '9') or
            std.mem.indexOfScalar(u8, "-._~/!$&'()*+,;=:@", byte) != null;
        if (allowed) {
            try writer.writeByte(byte);
        } else {
            try writer.writeByte('%');
            try writer.writeByte(hex[@as(usize, byte >> 4)]);
            try writer.writeByte(hex[@as(usize, byte & 0x0f)]);
        }
    }
}

fn printSarif(
    gpa: std.mem.Allocator,
    writer: *std.Io.Writer,
    items: []const IndexedProblem,
    execution_successful: bool,
) !void {
    try writer.writeAll(
        "{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\"," ++
            "\"version\":\"2.1.0\",\"runs\":[{\"tool\":{\"driver\":{" ++
            "\"name\":\"zbc\",\"informationUri\":\"https://github.com/ericsssan/zbc\"," ++
            "\"rules\":[",
    );

    var seen: std.StringHashMapUnmanaged(void) = .empty;
    defer seen.deinit(gpa);
    var first_rule = true;
    for (items) |item| {
        const id = item.problem.rule_id;
        if (seen.contains(id)) continue;
        try seen.put(gpa, id, {});
        if (!first_rule) try writer.writeByte(',');
        first_rule = false;
        try writer.writeAll("{\"id\":\"");
        try writeJsonEscaped(writer, id);
        try writer.writeAll("\",\"name\":\"");
        try writeJsonEscaped(writer, id);
        try writer.writeAll("\",\"shortDescription\":{\"text\":\"");
        if (lib.lookupRule(id)) |rule| {
            try writeJsonEscaped(writer, rule.title);
        } else {
            try writeJsonEscaped(writer, id);
        }
        try writer.writeAll("\"}}");
    }

    try writer.writeAll("]}},\"invocations\":[{\"executionSuccessful\":");
    try writer.writeAll(if (execution_successful) "true" else "false");
    try writer.writeAll("}],\"results\":[");
    for (items, 0..) |item, index| {
        const problem = item.problem;
        if (index > 0) try writer.writeByte(',');
        try writer.writeAll("{\"ruleId\":\"");
        try writeJsonEscaped(writer, problem.rule_id);
        try writer.print(
            "\",\"level\":\"{s}\",\"kind\":\"fail\",\"message\":{{\"text\":\"",
            .{sarifLevel(problem.severity)},
        );
        try writeJsonEscaped(writer, problem.message);
        try writer.writeAll("\"},\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"");
        try writeSarifUri(writer, item.path);
        try writer.writeAll("\"},\"region\":");
        try printSarifRegion(writer, problem.start, problem.end);
        try writer.writeAll("}}]");

        if (problem.notes.len != 0) {
            try writer.writeAll(",\"relatedLocations\":[");
            for (problem.notes, 0..) |note, note_index| {
                if (note_index != 0) try writer.writeByte(',');
                try writer.writeAll("{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"");
                try writeSarifUri(writer, item.path);
                try writer.writeAll("\"},\"region\":");
                try printSarifRegion(writer, note.start, note.end);
                try writer.writeAll("},\"message\":{\"text\":\"");
                try writeJsonEscaped(writer, note.label);
                try writer.writeAll("\"}}");
            }
            try writer.writeByte(']');
        }

        if (problem.verdict == .refuted) {
            try writer.writeAll(
                ",\"suppressions\":[{\"kind\":\"external\",\"status\":\"accepted\"," ++
                    "\"justification\":\"refuted by sound static analysis\"}]",
            );
        }

        try writer.print(",\"properties\":{{\"verdict\":\"{s}\"", .{verdictName(problem.verdict)});
        if (problem.witness) |witness| {
            try writer.writeAll(",\"witness\":\"");
            try writeJsonEscaped(writer, witness);
            try writer.writeByte('"');
        }
        try writer.writeAll("}}");
    }
    try writer.writeAll("]}]}\n");
}

fn severityName(s: lib.Severity) []const u8 {
    return switch (s) {
        .@"error" => "error",
        .warning => "warning",
        .off => "off",
    };
}

fn writeJsonEscaped(writer: *std.Io.Writer, text: []const u8) !void {
    for (text) |byte| {
        switch (byte) {
            '"' => try writer.writeAll("\\\""),
            '\\' => try writer.writeAll("\\\\"),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            0...0x08, 0x0b, 0x0c, 0x0e...0x1f => try writer.print("\\u{x:0>4}", .{byte}),
            else => try writer.writeByte(byte),
        }
    }
}

fn jsonEscapeToBuf(gpa: std.mem.Allocator, s: []const u8) ![]u8 {
    var list: std.ArrayListUnmanaged(u8) = .empty;
    errdefer list.deinit(gpa);
    for (s) |c| {
        switch (c) {
            '"' => try list.appendSlice(gpa, "\\\""),
            '\\' => try list.appendSlice(gpa, "\\\\"),
            '\n' => try list.appendSlice(gpa, "\\n"),
            '\r' => try list.appendSlice(gpa, "\\r"),
            '\t' => try list.appendSlice(gpa, "\\t"),
            0...0x08, 0x0b, 0x0c, 0x0e...0x1f => {
                var buf: [6]u8 = undefined;
                const hex = try std.fmt.bufPrint(&buf, "\\u{x:0>4}", .{c});
                try list.appendSlice(gpa, hex);
            },
            else => try list.append(gpa, c),
        }
    }
    return list.toOwnedSlice(gpa);
}

// ── Tests ──────────────────────────────────────────────────

test "parseInvariantList: add single" {
    const gpa = std.testing.allocator;
    var list: std.ArrayListUnmanaged(lib.Invariant) = .empty;
    defer list.deinit(gpa);
    try parseInvariantList(gpa, "arena_escape", &list, .add);
    try std.testing.expectEqual(@as(usize, 1), list.items.len);
    try std.testing.expectEqual(lib.Invariant.arena_escape, list.items[0]);
}

test "parseInvariantList: add dedupes" {
    const gpa = std.testing.allocator;
    var list: std.ArrayListUnmanaged(lib.Invariant) = .empty;
    defer list.deinit(gpa);
    try parseInvariantList(gpa, "arena_escape,arena_escape", &list, .add);
    try std.testing.expectEqual(@as(usize, 1), list.items.len);
}

test "parseInvariantList: remove from a set" {
    const gpa = std.testing.allocator;
    var list: std.ArrayListUnmanaged(lib.Invariant) = .empty;
    defer list.deinit(gpa);
    try list.appendSlice(gpa, &lib.all_invariants);
    try parseInvariantList(gpa, "arena_escape", &list, .remove);
    try std.testing.expect(!containsInvariant(list.items, .arena_escape));
}

test "splitCsv: basic comma-separated" {
    const gpa = std.testing.allocator;
    const out = try splitCsv(gpa, "a,b,c");
    defer gpa.free(out);
    try std.testing.expectEqual(@as(usize, 3), out.len);
    try std.testing.expectEqualStrings("a", out[0]);
    try std.testing.expectEqualStrings("c", out[2]);
}

test "splitCsv: trims whitespace, drops empties" {
    const gpa = std.testing.allocator;
    const out = try splitCsv(gpa, "  Foo.parse , , Bar.make ,");
    defer gpa.free(out);
    try std.testing.expectEqual(@as(usize, 2), out.len);
    try std.testing.expectEqualStrings("Foo.parse", out[0]);
    try std.testing.expectEqualStrings("Bar.make", out[1]);
}

test "jsonEscapeToBuf: passes ASCII through unchanged" {
    const gpa = std.testing.allocator;
    const s = try jsonEscapeToBuf(gpa, "hello, world (idx=42)");
    defer gpa.free(s);
    try std.testing.expectEqualStrings("hello, world (idx=42)", s);
}

test "jsonEscapeToBuf: escapes quote, backslash, common control chars" {
    const gpa = std.testing.allocator;
    const s = try jsonEscapeToBuf(gpa, "a\"b\\c\nd\te");
    defer gpa.free(s);
    try std.testing.expectEqualStrings("a\\\"b\\\\c\\nd\\te", s);
}

test "jsonEscapeToBuf: low control bytes become \\uXXXX" {
    const gpa = std.testing.allocator;
    const s = try jsonEscapeToBuf(gpa, &[_]u8{ 'x', 0x01, 'y', 0x1f, 'z' });
    defer gpa.free(s);
    try std.testing.expectEqualStrings("x\\u0001y\\u001fz", s);
}

test {
    _ = lib;
    std.testing.refAllDecls(@This());
}
