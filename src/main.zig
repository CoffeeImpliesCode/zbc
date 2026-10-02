//! zbc CLI — thin shell over the lib.zig library API.
//! Walks the .zig files passed on argv, runs escape analysis on each,
//! prints any Problems found in a grep-friendly format, and exits 0 if
//! all-clean / 1 if any problems.
//!
//! Usage:
//!   zbc [options] <file.zig>...
//!
//! Drop-in: run zbc on any Zig source; lifetime inference + the
//! pattern-detector rules fire without annotation requirements.
//!
//! Options:
//!   --enable=<list>      Comma-separated invariant names to enable.
//!   --disable=<list>     Comma-separated invariant names to disable.
//!   --arena-init=<csv>   Source-text patterns that mint a fresh
//!                        arena (default: ArenaAllocator.init).
//!   --arena-kill=<csv>   Source-text patterns that kill the receiver
//!                        arena (default: .deinit().
//!   --format=text|json   Output format (default: text).
//!   --list-invariants    Print known invariant names and exit 0.
//!   --list-rules         Print every rule id + title and exit 0.
//!   --explain <id>       Print the full explainer for one rule.
//!   -h / --help          Print usage and exit 0.

const std = @import("std");
const lib = @import("lib.zig");
const budget_mod = @import("budget.zig");

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
    var exclusions: std.ArrayListUnmanaged([]const u8) = .empty;
    defer exclusions.deinit(gpa);

    var arena_init_patterns: []const []const u8 = lib.DefaultConfig.arena_init_patterns;
    var arena_kill_patterns: []const []const u8 = lib.DefaultConfig.arena_kill_patterns;
    var pattern_allocations: std.ArrayListUnmanaged([]const []const u8) = .empty;
    defer {
        for (pattern_allocations.items) |slice| gpa.free(slice);
        pattern_allocations.deinit(gpa);
    }

    while (arg_it.next()) |a| {
        if (std.mem.eql(u8, a, "-h") or std.mem.eql(u8, a, "--help")) {
            printUsage();
            return 0;
        }
        if (std.mem.eql(u8, a, "--list-invariants")) {
            inline for (@typeInfo(lib.Invariant).@"enum".fields) |field| {
                std.debug.print("{s}\n", .{field.name});
            }
            return 0;
        }
        if (std.mem.eql(u8, a, "--list-rules")) {
            for (lib.rule_catalog) |r| {
                std.debug.print("{s} — {s}\n", .{ r.id, r.title });
            }
            return 0;
        }
        if (std.mem.startsWith(u8, a, "--explain=")) {
            return explain(a["--explain=".len..]);
        }
        if (std.mem.eql(u8, a, "--explain")) {
            const id = arg_it.next() orelse {
                std.debug.print("zbc: --explain requires a rule id (see --list-rules)\n", .{});
                return 2;
            };
            return explain(id);
        }
        if (std.mem.startsWith(u8, a, "--enable=")) {
            if (!enabled_explicit) {
                enabled.clearRetainingCapacity();
                enabled_explicit = true;
            }
            try parseInvariantList(gpa, a["--enable=".len..], &enabled, .add);
            continue;
        }
        if (std.mem.startsWith(u8, a, "--disable=")) {
            try parseInvariantList(gpa, a["--disable=".len..], &enabled, .remove);
            continue;
        }
        if (std.mem.startsWith(u8, a, "--arena-init=")) {
            const slice = try splitCsv(gpa, a["--arena-init=".len..]);
            try pattern_allocations.append(gpa, slice);
            arena_init_patterns = slice;
            continue;
        }
        if (std.mem.startsWith(u8, a, "--arena-kill=")) {
            const slice = try splitCsv(gpa, a["--arena-kill=".len..]);
            try pattern_allocations.append(gpa, slice);
            arena_kill_patterns = slice;
            continue;
        }
        if (std.mem.startsWith(u8, a, "--format=")) {
            const v = a["--format=".len..];
            if (std.mem.eql(u8, v, "text") or std.mem.eql(u8, v, "rich")) {
                format = .rich;
            } else if (std.mem.eql(u8, v, "compact")) {
                format = .compact;
            } else if (std.mem.eql(u8, v, "json")) {
                format = .json;
            } else if (std.mem.eql(u8, v, "sarif")) {
                format = .sarif;
            } else {
                std.debug.print("zbc: unknown format `{s}` (expected rich, compact, json, or sarif)\n", .{v});
                return 2;
            }
            continue;
        }
        if (std.mem.eql(u8, a, "--no-color")) {
            color_off = true;
            continue;
        }
        if (std.mem.startsWith(u8, a, "--trace=")) {
            const v = a["--trace=".len..];
            if (std.mem.eql(u8, v, "*")) {
                lib.trace.all_rules = true;
            } else {
                lib.trace.active_rule = v;
            }
            continue;
        }
        if (std.mem.startsWith(u8, a, "--jobs=")) {
            const count = std.fmt.parseInt(usize, a["--jobs=".len..], 10) catch return error.InvalidWorkerCount;
            if (count == 0) return error.InvalidWorkerCount;
            jobs = count;
            continue;
        }
        if (std.mem.startsWith(u8, a, "--exclude=")) {
            const path = a["--exclude=".len..];
            if (path.len == 0) return error.EmptyExclusion;
            try exclusions.append(gpa, path);
            continue;
        }
        if (std.mem.startsWith(u8, a, "--")) {
            std.debug.print("zbc: unknown flag: {s}\n", .{a});
            printUsage();
            return 2;
        }
        try paths.append(gpa, a);
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
        std.debug.print("zbc: cannot select {s}: {s}\n", .{ failure.path, @errorName(failure.err) });
    }

    const config: lib.Config = .{
        .arena_init_patterns = arena_init_patterns,
        .arena_kill_patterns = arena_kill_patterns,
        .enabled = enabled.items,
    };

    const tasks = try gpa.alloc(Task, selected_paths.len);
    defer gpa.free(tasks);
    for (selected_paths, tasks) |path, *t| {
        t.* = .{
            .path = path,
            .config = &config,
            .problems = &.{},
            .err = null,
        };
    }

    defer for (tasks) |task| {
        lib.freeProblems(gpa, task.problems);
        if (task.parse_failure) |failure| {
            if (failure.source_path) |path| gpa.free(path);
        }
    };
    try analyzeTasks(gpa, io, tasks, selection.policy(), jobs);

    var all_problems: std.ArrayListUnmanaged(IndexedProblem) = .empty;
    defer all_problems.deinit(gpa);
    var unresolved_imports: usize = 0;
    for (tasks) |*t| {
        unresolved_imports += t.unresolved_imports;
        if (t.err) |err| {
            if (t.parse_failure) |failure| {
                if (failure.source_path != null)
                    std.debug.print("zbc: analysis incomplete for {s}: imported source failed\n", .{t.path});
                std.debug.print("{s}:{}:{}: parse error: {s} (Zig {s})\n", .{
                    failure.source_path orelse t.path, failure.position.line,                 failure.position.column,
                    failure.reason,                    @import("builtin").zig_version_string,
                });
            } else if (t.budget) |info| {
                std.debug.print("zbc: cannot analyze {s}: {s} — {s} limit {d} reached {d}", .{
                    t.path, @errorName(err), info.limit.label(), info.limit_value, info.reached,
                });
                if (info.function.slice().len != 0) {
                    std.debug.print(" in fn `{s}`", .{info.function.slice()});
                }
                // Producers that hold a line table report one; the rest
                // still get a byte offset, which locates the site exactly.
                if (info.line != 0) {
                    std.debug.print(" at {s}:{d}:{d}\n", .{ t.path, info.line, info.column });
                } else {
                    std.debug.print(" at {s}+{d}\n", .{ t.path, info.byte });
                }
            } else if (err == error.AnalysisBudgetExceeded) {
                // Every bounded walk records which cap it hit before
                // propagating the error.  Reaching here means one gave
                // up without recording a limit, so the CLI can name the
                // file but not the cause.  Say that instead of folding
                // it into the generic line — a missing record is a
                // reportable defect, not a detail to swallow.
                std.debug.print(
                    "zbc: cannot analyze {s}: analysis budget exhausted without a recorded limit — the walk that gave up did not report which cap it hit\n",
                    .{t.path},
                );
            } else std.debug.print("zbc: cannot analyze {s}: {s}\n", .{ t.path, @errorName(err) });
            failed += 1;
            continue;
        }
        for (t.problems) |p| {
            try all_problems.append(gpa, .{ .path = t.path, .problem = p });
        }
    }

    std.mem.sort(IndexedProblem, all_problems.items, {}, indexedProblemLess);

    const use_color = !color_off and (std.Io.File.stderr().isTty(io) catch false);
    var src_cache: SourceCache = .{ .gpa = gpa, .io = io };
    defer src_cache.deinit();
    var stdout_buffer: [64 * 1024]u8 = undefined;
    var stdout = std.Io.File.stdout().writer(io, &stdout_buffer);
    const writer = &stdout.interface;
    switch (format) {
        .json => {
            var json: std.json.Stringify = .{ .writer = writer };
            try json.beginArray();
            for (all_problems.items) |ip| try printOneProblemJson(&json, ip.path, ip.problem);
            try json.endArray();
            try writer.writeByte('\n');
        },
        .sarif => try printSarif(gpa, writer, all_problems.items, failed == 0),
        .compact => {
            for (all_problems.items) |ip| {
                printOneProblemCompact(ip.path, ip.problem);
            }
        },
        .rich => {
            for (all_problems.items) |ip| {
                printOneProblemRich(&src_cache, ip.path, ip.problem, use_color);
            }
        },
    }
    try writer.flush();
    std.debug.print("zbc: selected={} analyzed={} failed={} findings={} parser=Zig-{s} unresolved-import-lookups={}\n", .{
        tasks.len + selection.failures.items.len, tasks.len - (failed - selection.failures.items.len),
        failed,                                   all_problems.items.len,
        @import("builtin").zig_version_string,    unresolved_imports,
    });
    if (failed != 0) return 2;
    return if (all_problems.items.len != 0) 1 else 0;
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

const SourceSelection = struct {
    gpa: std.mem.Allocator,
    io: std.Io,
    arena: std.heap.ArenaAllocator,
    roots: std.StringArrayHashMapUnmanaged(void) = .empty,
    files: std.StringArrayHashMapUnmanaged(void) = .empty,
    directories: std.StringHashMapUnmanaged(void) = .empty,
    failures: std.ArrayListUnmanaged(Failure) = .empty,
    excludes: []const []const u8,
    visited_entries: usize = 0,

    const Failure = struct { path: []const u8, err: anyerror };
    const Input = struct { path: []const u8, directory: bool };

    fn init(gpa: std.mem.Allocator, io: std.Io, excludes: []const []const u8) SourceSelection {
        return .{ .gpa = gpa, .io = io, .arena = .init(gpa), .excludes = excludes };
    }

    fn deinit(self: *SourceSelection) void {
        self.failures.deinit(self.gpa);
        self.directories.deinit(self.gpa);
        self.files.deinit(self.gpa);
        self.roots.deinit(self.gpa);
        self.arena.deinit();
    }

    fn policy(self: *const SourceSelection) lib.SourcePolicy {
        return .{ .roots = self.roots.keys(), .excludes = self.excludes };
    }

    fn fail(self: *SourceSelection, path: []const u8, err: anyerror) !void {
        try self.failures.append(self.gpa, .{ .path = try self.arena.allocator().dupe(u8, path), .err = err });
    }

    fn canonical(self: *SourceSelection, path: []const u8) ![]const u8 {
        var buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
        const len = try std.Io.Dir.cwd().realPathFile(self.io, path, &buffer);
        return self.arena.allocator().dupe(u8, buffer[0..len]);
    }

    fn normalizeExclusions(self: *SourceSelection, cwd: []const u8) !void {
        const arena = self.arena.allocator();
        const normalized = try arena.alloc([]const u8, self.excludes.len);
        for (self.excludes, normalized) |excluded, *result| {
            if (excluded.len == 0) return error.InvalidExclusion;
            result.* = if (std.mem.indexOfAny(u8, excluded, "/\\") != null)
                try std.fs.path.resolve(arena, &.{ cwd, excluded })
            else
                excluded;
        }
        self.excludes = normalized;
    }

    fn collect(self: *SourceSelection, paths: []const []const u8) !void {
        const cwd = try self.canonical(".");
        try self.normalizeExclusions(cwd);
        var inputs: std.ArrayListUnmanaged(Input) = .empty;
        defer inputs.deinit(self.gpa);
        for (paths) |path| {
            const lexical = try std.fs.path.resolve(self.arena.allocator(), &.{ cwd, path });
            if (self.policy().excludesPath(lexical)) continue;
            const absolute = self.canonical(lexical) catch |err| {
                try self.fail(path, err);
                continue;
            };
            if (self.policy().excludesPath(absolute)) continue;
            const stat = std.Io.Dir.cwd().statFile(self.io, absolute, .{}) catch |err| {
                try self.fail(path, err);
                continue;
            };
            if (stat.kind != .file and stat.kind != .directory) {
                try self.fail(path, error.UnsupportedSourceKind);
                continue;
            }
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
            if (self.policy().rootFor(parent) == null) try self.roots.put(self.gpa, parent, {});
        }
        for (inputs.items) |input| {
            if (!self.policy().allowsAbsolutePath(input.path)) continue;
            if (input.directory) try self.walk(input.path) else try self.files.put(self.gpa, input.path, {});
        }
    }

    fn walk(self: *SourceSelection, root: []const u8) !void {
        var pending: std.ArrayListUnmanaged([]const u8) = .empty;
        defer pending.deinit(self.gpa);
        try pending.append(self.gpa, root);
        while (pending.pop()) |path| {
            const seen = try self.directories.getOrPut(self.gpa, path);
            if (seen.found_existing) continue;
            var directory = std.Io.Dir.cwd().openDir(self.io, path, .{ .iterate = true }) catch |err| {
                try self.fail(path, err);
                continue;
            };
            defer directory.close(self.io);
            var entries = directory.iterate();
            while (true) {
                const entry = (entries.next(self.io) catch |err| {
                    try self.fail(path, err);
                    break;
                }) orelse break;
                if (self.visited_entries == 1_000_000) {
                    try self.fail(path, error.SourceScanBudgetExceeded);
                    return;
                }
                self.visited_entries += 1;
                if (lib.SourcePolicy.isExcludedBasename(entry.name)) continue;
                if (entry.kind != .directory and !std.mem.endsWith(u8, entry.name, ".zig")) continue;
                const full = try std.fs.path.join(self.arena.allocator(), &.{ path, entry.name });
                if (!self.policy().allowsAbsolutePath(full)) continue;
                switch (entry.kind) {
                    .directory => try pending.append(self.gpa, full),
                    .file => try self.files.put(self.gpa, full, {}),
                    .sym_link => try self.addLinkedFile(full),
                    else => {},
                }
            }
        }
    }

    fn addLinkedFile(self: *SourceSelection, path: []const u8) !void {
        const target = self.canonical(path) catch |err| {
            try self.fail(path, err);
            return;
        };
        if (!self.policy().allowsAbsolutePath(target)) return;
        const stat = std.Io.Dir.cwd().statFile(self.io, target, .{}) catch |err| {
            try self.fail(path, err);
            return;
        };
        if (stat.kind == .file) try self.files.put(self.gpa, target, {});
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
            return error.UnknownInvariant;
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
    if (lib.lookupRule(id)) |r| {
        std.debug.print("{s}", .{r.body});
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
        \\  --no-color            Disable ANSI color in `rich` output.
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
    problems: []lib.Problem,
    err: ?anyerror,
    /// Which analysis budget ran out, when `err` is
    /// `AnalysisBudgetExceeded`.  Claimed on the worker thread that hit
    /// it, so it is available even though the report loop runs on the
    /// main thread after the pool joins.
    budget: ?budget_mod.Diagnostic = null,
    parse_failure: ?lib.ParseFailure = null,
    unresolved_imports: usize = 0,
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
    if (a.problem.start.column != b.problem.start.column) return a.problem.start.column < b.problem.start.column;
    const rule_cmp = std.mem.order(u8, a.problem.rule_id, b.problem.rule_id);
    if (rule_cmp != .eq) return rule_cmp == .lt;
    return std.mem.lessThan(u8, a.problem.message, b.problem.message);
}

const WorkerCtx = struct {
    tasks: []Task,
    next: *std.atomic.Value(usize),
    gpa: std.mem.Allocator,
    io: std.Io,
    policy: lib.SourcePolicy,
};

fn analyzeTasks(gpa: std.mem.Allocator, io: std.Io, tasks: []Task, policy: lib.SourcePolicy, jobs: ?usize) !void {
    if (tasks.len == 0) return;
    const cpu_count = jobs orelse (std.Thread.getCpuCount() catch 1);
    const worker_count = @max(1, @min(cpu_count, tasks.len));
    const workers = try gpa.alloc(std.Thread, worker_count - 1);
    defer gpa.free(workers);
    var next: std.atomic.Value(usize) = .init(0);
    const ctx: WorkerCtx = .{ .tasks = tasks, .next = &next, .gpa = gpa, .io = io, .policy = policy };
    var spawned: usize = 0;
    for (workers) |*worker| {
        worker.* = std.Thread.spawn(.{}, workerLoop, .{ctx}) catch break;
        spawned += 1;
    }
    workerLoop(ctx);
    for (workers[0..spawned]) |worker| worker.join();
}

fn workerLoop(ctx: WorkerCtx) void {
    var session: lib.Session = undefined;
    session.init(ctx.gpa, ctx.io, ctx.policy) catch |err| {
        while (true) {
            const i = ctx.next.fetchAdd(1, .monotonic);
            if (i >= ctx.tasks.len) return;
            ctx.tasks[i].err = err;
        }
    };
    defer session.deinit();
    while (true) {
        const i = ctx.next.fetchAdd(1, .monotonic);
        if (i >= ctx.tasks.len) return;
        runOne(&ctx.tasks[i], &session);
    }
}

fn runOne(task: *Task, session: *lib.Session) void {
    const unresolved_before = session.project.unresolved_imports;
    defer task.unresolved_imports = session.project.unresolved_imports - unresolved_before;
    // Each file starts with no pending budget failure, so a worker that
    // just succeeded cannot leak its predecessor's record into this one.
    budget_mod.clear();
    task.problems = lib.analyzeEscape(session, task.path, task.config) catch |err| {
        task.err = err;
        task.budget = if (err == error.AnalysisBudgetExceeded) budget_mod.take() else null;
        task.parse_failure = session.parse_failure;
        if (task.parse_failure) |*failure| {
            if (failure.source_path) |path| {
                failure.source_path = session.gpa.dupe(u8, path) catch {
                    task.err = error.OutOfMemory;
                    task.parse_failure = null;
                    return;
                };
            }
        }
        return;
    };
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

fn printOneProblemJson(json: *std.json.Stringify, path: []const u8, problem: lib.Problem) !void {
    try json.write(.{
        .path = path,
        .rule_id = problem.rule_id,
        .severity = problem.severity,
        .start = problem.start,
        .end = problem.end,
        .message = problem.message,
        .notes = problem.notes,
        .verdict = problem.verdict,
        .witness = problem.witness,
    });
}

/// SARIF 2.1.0 severity level for a zbc severity.  SARIF levels are
/// none|note|warning|error.
fn sarifLevel(s: lib.Severity) []const u8 {
    return switch (s) {
        .@"error" => "error",
        .warning => "warning",
        .off => "none",
    };
}

const SarifRegion = struct {
    startLine: u32,
    startColumn: u32,
    endLine: u32,
    endColumn: u32,
    byteOffset: u32,
    byteLength: u32,
};
const SarifPhysicalLocation = struct {
    artifactLocation: struct { uri: []const u8 },
    region: SarifRegion,
};

fn sarifLocation(uri: []const u8, start: lib.Pos, end: lib.Pos) SarifPhysicalLocation {
    return .{
        .artifactLocation = .{ .uri = uri },
        .region = .{
            .startLine = start.line,
            .startColumn = start.column,
            .endLine = end.line,
            .endColumn = end.column,
            .byteOffset = start.byte,
            .byteLength = end.byte -| start.byte,
        },
    };
}

fn printSarif(gpa: std.mem.Allocator, writer: *std.Io.Writer, items: []const IndexedProblem, complete: bool) !void {
    try writer.writeAll("{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\",\"version\":\"2.1.0\",\"runs\":[{\"tool\":{\"driver\":{\"name\":\"zbc\",\"informationUri\":\"https://github.com/ericsssan/zbc\",\"rules\":[");
    var seen: std.StringHashMapUnmanaged(void) = .empty;
    defer seen.deinit(gpa);
    for (items) |item| {
        const id = item.problem.rule_id;
        if (seen.contains(id)) continue;
        if (seen.count() != 0) try writer.writeByte(',');
        try seen.put(gpa, id, {});
        const title = if (lib.lookupRule(id)) |rule| rule.title else id;
        try std.json.Stringify.value(.{ .id = id, .name = id, .shortDescription = .{ .text = title } }, .{}, writer);
    }
    try writer.writeAll("]}},\"invocations\":[");
    try std.json.Stringify.value(.{ .executionSuccessful = complete }, .{}, writer);
    try writer.writeAll("],\"results\":[");
    for (items, 0..) |item, index| {
        if (index != 0) try writer.writeByte(',');
        try printSarifResult(writer, item);
    }
    try writer.writeAll("]}]}\n");
}

fn printSarifResult(writer: *std.Io.Writer, item: IndexedProblem) !void {
    var uri_buffer: [3 * std.Io.Dir.max_path_bytes + 8]u8 = undefined;
    var encoded: std.Io.Writer = .fixed(&uri_buffer);
    try encoded.writeAll("file://");
    try (std.Uri.Component{ .raw = item.path }).formatPath(&encoded);
    const uri = encoded.buffered();
    const problem = item.problem;
    var json: std.json.Stringify = .{ .writer = writer };
    try json.beginObject();
    try json.objectField("ruleId");
    try json.write(problem.rule_id);
    try json.objectField("level");
    try json.write(sarifLevel(problem.severity));
    try json.objectField("kind");
    try json.write("fail");
    try json.objectField("message");
    try json.write(.{ .text = problem.message });
    try json.objectField("locations");
    try json.write(.{.{ .physicalLocation = sarifLocation(uri, problem.start, problem.end) }});
    if (problem.notes.len != 0) {
        try json.objectField("relatedLocations");
        try json.beginArray();
        for (problem.notes) |note| try json.write(.{
            .physicalLocation = sarifLocation(uri, note.start, note.end),
            .message = .{ .text = note.label },
        });
        try json.endArray();
    }
    if (problem.verdict == .refuted) {
        try json.objectField("suppressions");
        try json.write(.{.{ .kind = "external", .status = "accepted", .justification = "refuted by sound static analysis" }});
    }
    try json.objectField("properties");
    try json.write(.{ .verdict = problem.verdict, .witness = problem.witness });
    try json.endObject();
}

fn severityName(s: lib.Severity) []const u8 {
    return switch (s) {
        .@"error" => "error",
        .warning => "warning",
        .off => "off",
    };
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

test {
    _ = lib;
    std.testing.refAllDecls(@This());
}
