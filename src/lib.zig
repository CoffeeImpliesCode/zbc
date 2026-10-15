//! Public library API for the zbc escape analyzer.

const std = @import("std");
const Ast = std.zig.Ast;

const cfg_mod = @import("flow/cfg.zig");
const cfg_builder = @import("flow/cfg_builder.zig");
const worklist = @import("flow/worklist.zig");
const config_mod = @import("config.zig");
const problem_mod = @import("problem.zig");
const rule_catalog_mod = @import("rule_catalog.zig");
const file_cache_mod = @import("cache/file_cache.zig");
const suppressions_mod = @import("suppressions.zig");
const zls_resolver_mod = @import("type_resolver.zig");
const budget_mod = @import("budget.zig");
const tokens = @import("ast/tokens.zig");
const project_cache_mod = @import("cache/project_cache.zig");

pub const Config = config_mod.Config;
pub const DefaultConfig = config_mod.Default;
pub const Invariant = config_mod.Invariant;
pub const all_invariants = config_mod.all_invariants;
pub const isEnabled = config_mod.isEnabled;
pub const invariantFromName = config_mod.invariantFromName;
pub const Problem = problem_mod.Problem;
pub const Incomplete = problem_mod.Incomplete;
pub const Note = problem_mod.Note;
pub const Pos = problem_mod.Pos;
pub const Severity = problem_mod.Severity;
pub const Verdict = problem_mod.Verdict;
pub const Rule = rule_catalog_mod.Rule;
pub const rule_catalog = rule_catalog_mod.all;
pub const lookupRule = rule_catalog_mod.lookup;
pub const SourcePolicy = @import("type_engine").SourcePolicy;
/// Borrowed parser details; Session owns a copy of its optional source path.
pub const ParseFailure = @import("type_engine").ParseFailure;
pub const Toolchain = zls_resolver_mod.Toolchain;
pub const ToolchainFailure = zls_resolver_mod.ToolchainFailure;
pub const trace = @import("trace.zig");
/// Budget limits and diagnostics carried by `Incomplete`.
pub const budget = budget_mod;
/// One worker and one immutable source snapshot.
///
/// ProjectCache models borrow ASTs from TypeContext. Initialize in place;
/// do not move or share the value. Policy slices, allocator, and I/O
/// provider must remain valid until `deinit`.
pub const Session = struct {
    gpa: std.mem.Allocator,
    io: std.Io,
    project: project_cache_mod.ProjectCache,
    type_context: zls_resolver_mod.TypeContext,
    /// Details from the last syntax failure; valid until next analysis/deinit.
    /// The optional path is copied and owned by this session.
    parse_failure: ?ParseFailure = null,

    /// `policy.roots` must be canonical absolute paths. Empty roots deny all.
    pub fn init(self: *Session, gpa: std.mem.Allocator, io: std.Io, policy: SourcePolicy) !void {
        self.* = .{
            .gpa = gpa,
            .io = io,
            .project = project_cache_mod.ProjectCache.init(gpa, io, policy),
            .type_context = undefined,
        };
        errdefer self.project.deinit();
        try self.type_context.init(gpa, io);
        self.type_context.store.source_policy = policy;
        self.project.type_context = &self.type_context;
    }

    /// The borrowed `toolchain` must outlive this session.
    /// `policy.roots` must be canonical absolute paths. Empty roots deny all.
    pub fn initWithToolchain(
        self: *Session,
        gpa: std.mem.Allocator,
        io: std.Io,
        policy: SourcePolicy,
        toolchain: *const Toolchain,
    ) !void {
        self.* = .{
            .gpa = gpa,
            .io = io,
            .project = project_cache_mod.ProjectCache.init(gpa, io, policy),
            .type_context = undefined,
        };
        errdefer self.project.deinit();
        try self.type_context.initWithToolchain(gpa, io, toolchain);
        self.type_context.store.source_policy = policy;
        self.project.type_context = &self.type_context;
    }

    /// Drop models before their borrowed ASTs, then release context state.
    pub fn deinit(self: *Session) void {
        self.clearParseFailure();
        self.project.deinit();
        self.type_context.deinit();
        self.* = undefined;
    }

    fn clearParseFailure(self: *Session) void {
        if (self.parse_failure) |failure| {
            if (failure.source_path) |path| self.gpa.free(path);
        }
        self.parse_failure = null;
    }

    fn recordParseFailure(self: *Session, failure: ?ParseFailure, source_path: ?[]const u8) !void {
        self.clearParseFailure();
        const value = failure orelse return;
        const owned_path = if (source_path) |path| try self.gpa.dupe(u8, path) else null;
        self.parse_failure = .{
            .source_path = owned_path,
            .position = value.position,
            .reason = value.reason,
        };
    }

    fn captureCurrentParseFailure(self: *Session, source_is_input: bool) !void {
        const failure = self.project.parse_failure orelse self.type_context.store.failureSnapshot().parse_failure;
        const source_path = if (source_is_input)
            null
        else if (failure) |value|
            value.source_path
        else
            null;
        try self.recordParseFailure(failure, source_path);
    }
};

/// Findings of one analyzed file plus the parts that gave up.
///
/// `incomplete` is empty when the whole file was analyzed. Otherwise every
/// listed function, summary, or rule exhausted an analysis budget and
/// contributed no findings; all other parts completed and their findings
/// are in `problems`. Release with `freeAnalysis`.
/// Incomplete records hold OwnedDiagnostic paths copied by appendIncomplete,
/// not borrowed from Session. freeAnalysis releases those copies.
pub const Analysis = struct {
    problems: []Problem,
    incomplete: []Incomplete,
};

/// Analyze one source admitted by the session's policy.
///
/// Uses the original source tree. `path` and `config` are borrowed for the
/// call. A successful Analysis does not borrow from Session and may outlive
/// it while the allocator remains valid; release it with `freeAnalysis`.
/// Only `error.AnalysisBudgetExceeded` raised inside one function, one
/// function's summary, or one pattern rule is absorbed into
/// `Analysis.incomplete`; that part reports no findings and the rest of the
/// file is still analyzed. Every other error fails the whole call.
/// Syntax errors set `session.parse_failure`.
/// Source-load errors propagate even when type resolution returned unknown.
/// A failed load retains no source snapshot, so a later analysis can retry it.
/// The caller reports returned errors; source loading emits no duplicate diagnostic.
pub fn analyzeEscape(session: *Session, path: []const u8, config: *const Config) !Analysis {
    const source_scope = budget_mod.SourceScope.begin(&session.type_context.store);
    defer source_scope.end();
    const gpa = session.gpa;
    session.clearParseFailure();
    session.project.failure = null;
    session.project.parse_failure = null;
    session.type_context.store.clearFailure();

    const canonical = try session.project.sourcePath(path);
    trace.setFile(canonical);
    const maybe_model = session.project.modelForPath(canonical) catch |err|
        return remapImportSyntaxError(session, err, true);
    const model = maybe_model orelse return error.FileNotFound;
    const tree = model.tree;

    var resolver: zls_resolver_mod.TypeResolver = undefined;
    resolver.init(&session.type_context, gpa, canonical, tree.source) catch |err|
        return remapImportSyntaxError(session, err, false);
    defer resolver.deinit();
    const zls_ptr: ?*zls_resolver_mod.TypeResolver = &resolver;

    var rule_cache = file_cache_mod.FileCache.init(gpa, tree);
    defer rule_cache.deinit();
    rule_cache.setZls(zls_ptr);
    rule_cache.setProject(&session.project, canonical);

    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    errdefer freeProblemsArrayList(gpa, &problems);
    var incomplete: std.ArrayListUnmanaged(Incomplete) = .empty;
    errdefer freeIncompleteArrayList(gpa, &incomplete);

    var summary_failures: std.ArrayListUnmanaged(file_cache_mod.SummaryFailure) = .empty;
    defer summary_failures.deinit(gpa);
    budget_mod.clear();
    rule_cache.resolveTransitiveTakesCollecting(&summary_failures) catch |err|
        return remapImportSyntaxError(session, err, false);
    for (summary_failures.items) |failure| {
        try problem_mod.appendIncomplete(gpa, &incomplete, .summary, fnName(tree, failure.fn_decl), failure.budget);
    }

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const before = problems.items.len;
        budget_mod.clear();
        analyzeFunction(gpa, tree, node, config, &rule_cache, zls_ptr, canonical, &problems) catch |err| {
            if (err != error.AnalysisBudgetExceeded) return remapImportSyntaxError(session, err, false);
            problem_mod.truncateProblems(gpa, &problems, before);
            const diagnostic = budget_mod.take();
            // The summary pass already named this function.
            if (!summaryFailed(summary_failures.items, node)) {
                try problem_mod.appendIncomplete(gpa, &incomplete, .function, fnName(tree, node), diagnostic);
            }
        };
    }

    rule_catalog_mod.runEscape(gpa, tree, &rule_cache, config, &problems, &incomplete) catch |err|
        return remapImportSyntaxError(session, err, false);
    if (session.project.failure) |failure|
        return remapImportSyntaxError(session, failure, false);
    if (session.type_context.store.failureSnapshot().source_failure) |failure|
        return remapImportSyntaxError(session, failure, false);

    var supp = try suppressions_mod.parse(gpa, tree.source);
    defer supp.deinit();
    const incomplete_owned = try incomplete.toOwnedSlice(gpa);
    errdefer freeIncomplete(gpa, incomplete_owned);
    const kept = try filterSuppressed(gpa, &problems, &supp);
    return .{ .problems = kept, .incomplete = incomplete_owned };
}

/// Lower one function and run the flow check on it, appending Problems.
fn analyzeFunction(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    node: Ast.Node.Index,
    config: *const Config,
    rule_cache: *file_cache_mod.FileCache,
    zls_ptr: ?*zls_resolver_mod.TypeResolver,
    path: []const u8,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    var cfg = (try cfg_builder.lowerFunctionFullWithZls(
        gpa,
        tree,
        node,
        config,
        rule_cache,
        zls_ptr,
    )) orelse return;
    defer cfg.deinit(gpa);
    try worklist.check(gpa, &cfg, .{ .path = path, .config = config }, problems);
}

fn summaryFailed(failures: []const file_cache_mod.SummaryFailure, node: Ast.Node.Index) bool {
    for (failures) |failure| {
        if (failure.fn_decl == node) return true;
    }
    return false;
}

fn fnName(tree: *const Ast, node: Ast.Node.Index) []const u8 {
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, node) orelse return "";
    const name_token = proto.name_token orelse return "";
    return tree.tokenSlice(name_token);
}

fn remapImportSyntaxError(session: *Session, err: anyerror, source_is_input: bool) anyerror {
    if (err != error.ImportInvalidSyntax) return err;
    session.captureCurrentParseFailure(source_is_input) catch |capture_err| return capture_err;
    return error.InvalidSyntax;
}

/// Drop Problems whose start.line matches an active suppression.
/// Frees dropped Problems and returns the owned survivors.
fn filterSuppressed(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    supp: *const suppressions_mod.Suppressions,
) ![]Problem {
    if (supp.entries.len == 0) return problems.toOwnedSlice(gpa);
    // Compact in place so error cleanup owns only surviving Problems.
    var kept_len: usize = 0;
    for (problems.items) |problem| {
        if (supp.isSuppressed(problem.rule_id, problem.start.line)) {
            var dead = problem;
            dead.deinit(gpa);
            continue;
        }
        problems.items[kept_len] = problem;
        kept_len += 1;
    }
    problems.items.len = kept_len;
    return problems.toOwnedSlice(gpa);
}
/// Releases an Analysis with the same allocator passed to `Session.init`.
pub fn freeAnalysis(gpa: std.mem.Allocator, analysis: Analysis) void {
    for (analysis.problems) |*p| p.deinit(gpa);
    gpa.free(analysis.problems);
    freeIncomplete(gpa, analysis.incomplete);
}

fn freeIncomplete(gpa: std.mem.Allocator, slice: []Incomplete) void {
    for (slice) |*part| part.deinit(gpa);
    gpa.free(slice);
}

fn freeIncompleteArrayList(gpa: std.mem.Allocator, list: *std.ArrayListUnmanaged(Incomplete)) void {
    for (list.items) |*part| part.deinit(gpa);
    list.deinit(gpa);
}

fn freeProblemsArrayList(gpa: std.mem.Allocator, list: *std.ArrayListUnmanaged(Problem)) void {
    for (list.items) |*p| p.deinit(gpa);
    list.deinit(gpa);
}

// ── Tests ───────────────────────────────────────────────────────

test "lib API: analyzeEscape end-to-end flags arena escape" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.writeFile(tio, .{ .sub_path = "foo.zig", .data =
        \\const std = @import("std");
        \\const Arena = struct {
        \\    inner: std.heap.ArenaAllocator,
        \\    bytes: []const u8 = "",
        \\    pub fn text(self: *const Arena) []const u8 { return self.bytes; }
        \\};
        \\pub fn foo() []const u8 {
        \\    var arena = Arena{ .inner = std.heap.ArenaAllocator.init(undefined) };
        \\    return arena.text();
        \\}
        \\
    });

    const base_dir = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(base_dir);
    const path = try std.fs.path.join(gpa, &.{ base_dir, "foo.zig" });
    defer gpa.free(path);

    var session: Session = undefined;
    try session.init(gpa, tio, .{ .roots = &.{base_dir} });
    defer session.deinit();
    const analysis = try analyzeEscape(&session, path, &DefaultConfig);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);

    var found = false;
    for (analysis.problems) |p| {
        if (std.mem.indexOf(u8, p.message, "function-local arena") != null) found = true;
    }
    try std.testing.expect(found);
}

test "lib API: canonical imported enum tag values prove complete lookup tables" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(tio, .{
        .sub_path = "ops.zig",
        .data =
        \\pub const Op = enum(u8) { entry = 0, add, exit };
        \\pub const Sparse = enum(u8) { entry = 0, add = 2, exit = 3 };
        ,
    });
    const source =
        \\const std = @import("std");
        \\const ops = @import("ops.zig");
        \\const Alias = ops.Op;
        \\pub fn complete() [std.meta.fields(ops.Op).len]u8 {
        \\    var result: [std.meta.fields(ops.Op).len]u8 = undefined;
        \\    inline for (std.meta.fields(ops.Op)) |field| {
        \\        const op: ops.Op = @enumFromInt(field.value);
        \\        result[field.value] = hooksForOp(op);
        \\    }
        \\    return result;
        \\}
        \\pub fn aliasComplete() [std.meta.fields(Alias).len]u8 {
        \\    var result: [std.meta.fields(Alias).len]u8 = undefined;
        \\    inline for (std.meta.fields(Alias)) |field| result[field.value] = 1;
        \\    return result;
        \\}
        \\pub fn hole() [std.meta.fields(ops.Sparse).len]u8 {
        \\    var result: [std.meta.fields(ops.Sparse).len]u8 = undefined;
        \\    inline for (std.meta.fields(ops.Sparse)) |field| result[field.value] = 1;
        \\    return result;
        \\}
        \\pub fn selected() u8 {
        \\    const result = hole();
        \\    return result[1];
        \\}
        \\pub fn written() u8 {
        \\    const result = complete();
        \\    return result[0];
        \\}
        \\fn hooksForOp(op: ops.Op) u8 { return @intFromEnum(op); }
    ;
    try tmp.dir.writeFile(tio, .{ .sub_path = "consumer.zig", .data = source });
    const root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(root);
    const path = try std.fs.path.join(gpa, &.{ root, "consumer.zig" });
    defer gpa.free(path);
    var session: Session = undefined;
    try session.init(gpa, tio, .{ .roots = &.{root} });
    defer session.deinit();
    const analysis = try analyzeEscape(&session, path, &DefaultConfig);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    for ([_]struct { function: []const u8, warns: bool }{
        .{ .function = "pub fn complete()", .warns = false },
        .{ .function = "pub fn aliasComplete()", .warns = false },
        .{ .function = "pub fn hole()", .warns = false },
    }) |case| {
        const function = std.mem.indexOf(u8, source, case.function).?;
        const returned = std.mem.indexOfPos(u8, source, function, "return result").?;
        const end = returned + "return result".len;
        var reported = false;
        for (analysis.problems) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                problem.start.byte >= returned and problem.start.byte < end) reported = true;
        }
        try std.testing.expectEqual(case.warns, reported);
    }
    for ([_]struct { needle: []const u8, warns: bool }{
        .{ .needle = "return result[1]", .warns = true },
        .{ .needle = "return result[0]", .warns = false },
    }) |case| {
        const start = std.mem.indexOf(u8, source, case.needle).?;
        var reported = false;
        for (analysis.problems) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                problem.start.byte >= start and problem.start.byte < start + case.needle.len) reported = true;
        }
        try std.testing.expectEqual(case.warns, reported);
    }
}

test "lib API: imported enum fields fix runtime array fill extent" {
    const gpa = std.testing.allocator;
    const tio = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(tio, .{
        .sub_path = "icons.zig",
        .data =
        \\pub const widget = struct {
        \\    pub const Icon = enum(u8) { a = 2, b = 9, c = 17 };
        \\};
        ,
    });
    const source =
        \\const icons = @import("icons.zig");
        \\const Icon = icons.widget.Icon;
        \\const count = @typeInfo(Icon).@"enum".fields.len;
        \\const documents = [_]u8{ 1, 2, 3 };
        \\pub fn complete() [count]u8 {
        \\    var values: [count]u8 = undefined;
        \\    for (documents, 0..) |document, i| values[i] = document;
        \\    return values;
        \\}
        \\pub fn hole() [count]u8 {
        \\    var values: [count]u8 = undefined;
        \\    for (documents[0..2], 0..) |document, i| values[i] = document;
        \\    return values;
        \\}
        \\pub fn selected() u8 {
        \\    const result = hole();
        \\    _ = result[0];
        \\    return result[2];
        \\}
    ;
    try tmp.dir.writeFile(tio, .{ .sub_path = "consumer.zig", .data = source });
    const root = try tmp.dir.realPathFileAlloc(tio, ".", gpa);
    defer gpa.free(root);
    const path = try std.fs.path.join(gpa, &.{ root, "consumer.zig" });
    defer gpa.free(path);
    var session: Session = undefined;
    try session.init(gpa, tio, .{ .roots = &.{root} });
    defer session.deinit();
    const analysis = try analyzeEscape(&session, path, &DefaultConfig);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    for ([_]struct { needle: []const u8, ordinal: usize = 0, warns: bool }{
        .{ .needle = "return values", .warns = false },
        .{ .needle = "return values", .ordinal = 1, .warns = false },
        .{ .needle = "_ = result[0]", .warns = false },
        .{ .needle = "return result[2]", .warns = true },
    }) |case| {
        var start: usize = 0;
        for (0..case.ordinal + 1) |_| start = std.mem.indexOfPos(u8, source, start, case.needle).? + case.needle.len;
        start -= case.needle.len;
        var reported = false;
        for (analysis.problems) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                problem.start.byte >= start and problem.start.byte < start + case.needle.len) reported = true;
        }
        try std.testing.expectEqual(case.warns, reported);
    }
}

test "lib API: an imported source width failure cannot return a clean result" {
    // A sparse import reaches the real reader's width refusal without
    // allocating its contents. The next analysis must not inherit its failure.
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    {
        var wide = try tmp.dir.createFile(io, "wide.zig", .{ .read = true });
        defer wide.close(io);
        try wide.setLength(io, SourcePolicy.max_source_bytes);
    }
    try tmp.dir.writeFile(io, .{
        .sub_path = "main.zig",
        .data =
        \\const wide = @import("wide.zig");
        \\pub fn use() void { const value = wide.value; _ = value; }
        ,
    });
    try tmp.dir.writeFile(io, .{
        .sub_path = "clean.zig",
        .data = "pub fn clean() void {}",
    });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const main_path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(main_path);
    const clean_path = try std.fs.path.join(gpa, &.{ directory, "clean.zig" });
    defer gpa.free(clean_path);
    var session: Session = undefined;
    try session.init(gpa, io, .{ .roots = &.{directory} });
    defer session.deinit();
    for (0..2) |_| {
        try std.testing.expectError(error.SourceTooWide, analyzeEscape(
            &session,
            main_path,
            &DefaultConfig,
        ));
        try std.testing.expect(session.parse_failure == null);
        try std.testing.expectEqual(
            @as(?anyerror, error.SourceTooWide),
            session.type_context.store.failureSnapshot().source_failure,
        );
    }
    const analysis = try analyzeEscape(&session, clean_path, &DefaultConfig);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.problems.len);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    try std.testing.expectEqual(
        @as(?anyerror, null),
        session.type_context.store.failureSnapshot().source_failure,
    );

    // A failed import owns no source snapshot. Once it becomes readable,
    // the same session must load it instead of reusing a failed reservation.
    try tmp.dir.writeFile(io, .{
        .sub_path = "wide.zig",
        .data = "pub const value: u8 = 7;",
    });
    const retried = try analyzeEscape(&session, main_path, &DefaultConfig);
    defer freeAnalysis(gpa, retried);
    try std.testing.expectEqual(@as(usize, 0), retried.problems.len);
    try std.testing.expectEqual(@as(usize, 0), retried.incomplete.len);
    try std.testing.expect(session.parse_failure == null);
    try std.testing.expectEqual(
        @as(?anyerror, null),
        session.type_context.store.failureSnapshot().source_failure,
    );
}

// ── Suppression integration tests ───────────────────────────────
//
// These tests run the full analyzeEscape pipeline on real files to
// verify that filterSuppressed correctly removes or keeps problems
// based on // zbc-disable-line / // zbc-disable-next-line directives.
// They use ptrfromint-zero as the trigger — easy to place and the
// finding lands on a predictable source line.

fn analyzeSrc(
    gpa: std.mem.Allocator,
    io: std.Io,
    tmp: *std.testing.TmpDir,
    src: []const u8,
) !Analysis {
    const name = "check.zig";
    try tmp.dir.writeFile(io, .{ .sub_path = name, .data = src });
    const base_dir = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(base_dir);
    const path = try std.fs.path.join(gpa, &.{ base_dir, name });
    defer gpa.free(path);
    var session: Session = undefined;
    try session.init(gpa, io, .{ .roots = &.{base_dir} });
    defer session.deinit();
    return analyzeEscape(&session, path, &DefaultConfig);
}

fn countByRule(problems: []const Problem, rule_id: []const u8) usize {
    var n: usize = 0;
    for (problems) |p| {
        if (std.mem.eql(u8, p.rule_id, rule_id)) n += 1;
    }
    return n;
}

test "suppression: zbc-disable-line drops the finding on the same line" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Without directive: @ptrFromInt(0) on line 2 → 1 problem.
    // With directive on the same line: 0 problems.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    return @ptrFromInt(0); // zbc-disable-line: ptrfromint-zero
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "ptrfromint-zero"));
}

test "suppression: without directive the finding is not dropped" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    return @ptrFromInt(0);
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expect(countByRule(analysis.problems, "ptrfromint-zero") >= 1);
}

test "suppression: zbc-disable-next-line drops the finding on the following line" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    // zbc-disable-next-line: ptrfromint-zero
        \\    return @ptrFromInt(0);
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "ptrfromint-zero"));
}

test "suppression: wildcard zbc-disable-line: * drops any rule" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    return @ptrFromInt(0); // zbc-disable-line: *
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "ptrfromint-zero"));
}

test "suppression: wrong rule id leaves the finding" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Directive targets a different rule → ptrfromint-zero still fires.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    return @ptrFromInt(0); // zbc-disable-line: some-other-rule
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expect(countByRule(analysis.problems, "ptrfromint-zero") >= 1);
}

test "suppression: directive only suppresses its own line, not others" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Two @ptrFromInt(0) calls on different lines.
    // Only the first has a directive — second still fires.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn a() *anyopaque {
        \\    return @ptrFromInt(0); // zbc-disable-line: ptrfromint-zero
        \\}
        \\fn b() *anyopaque {
        \\    return @ptrFromInt(0);
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 1), countByRule(analysis.problems, "ptrfromint-zero"));
}

// ── Partial-result tests ────────────────────────────────────────

/// A function whose flow check exhausts the per-block path-state limit: ten
/// independent conditions leave 2^10 distinguishable states at the join.
/// It also double-frees early, so a finding the aborted function had already
/// produced would show up in the result if it were kept.
fn manyPathsFn(gpa: std.mem.Allocator) ![]u8 {
    var text: std.ArrayListUnmanaged(u8) = .empty;
    errdefer text.deinit(gpa);
    try text.appendSlice(gpa, "const std = @import(\"std\");\nfn many(a: std.mem.Allocator");
    for (0..10) |i| try text.print(gpa, ", f{d}: bool", .{i});
    try text.appendSlice(gpa, ") void {\n    const q = a.alloc(u8, 1) catch return;\n    a.free(q);\n    a.free(q);\n");
    for (0..10) |i| try text.print(gpa, "    const p{d} = a.alloc(u8, 1) catch return;\n", .{i});
    for (0..10) |i| try text.print(gpa, "    if (f{d}) a.free(p{d});\n", .{ i, i });
    try text.appendSlice(gpa, "}\n");
    return text.toOwnedSlice(gpa);
}

test "partial: an exhausted function keeps the findings of the others" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const many = try manyPathsFn(gpa);
    defer gpa.free(many);
    const src = try std.mem.concat(gpa, u8, &.{
        many,
        "pub fn bad() *u8 { var x: u8 = 1; return &x; }\n",
        "pub fn fine() u8 { return 1; }\n",
    });
    defer gpa.free(src);

    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, src);
    defer freeAnalysis(gpa, analysis);

    try std.testing.expectEqual(@as(usize, 1), countByRule(analysis.problems, "stack-escape"));
    // The aborted function contributes nothing, not even what it found first.
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "heap-double-free"));
    try std.testing.expectEqual(@as(usize, 1), analysis.incomplete.len);
    const part = analysis.incomplete[0];
    try std.testing.expectEqual(Incomplete.Kind.function, part.kind);
    try std.testing.expectEqualStrings("many", part.name);
    const diagnostic = part.budget orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.path_states, diagnostic.limit);
    try std.testing.expectEqual(@as(u32, 64), diagnostic.limit_value);
    try std.testing.expect(diagnostic.line != 0);
    // analyzeSrc already destroyed its Session. The exported path must survive.
    const expected_path = try tmp.dir.realPathFileAlloc(std.testing.io, "check.zig", gpa);
    defer gpa.free(expected_path);
    try std.testing.expectEqualStrings(expected_path, diagnostic.document);
}

test "partial: the same function alone, within budget, reports its finding" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\fn few(a: std.mem.Allocator) void {
        \\    const q = a.alloc(u8, 1) catch return;
        \\    a.free(q);
        \\    a.free(q);
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 1), countByRule(analysis.problems, "heap-double-free"));
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
}

test "partial: a summary-pass failure names the function and keeps the rest" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Past the normal-cleanup depth limit the summary of `too_deep` gives up.
    var src: std.ArrayListUnmanaged(u8) = .empty;
    defer src.deinit(gpa);
    try src.appendSlice(gpa, "fn too_deep(flag: bool) bool { return ");
    for (0..70) |_| try src.append(gpa, '(');
    try src.appendSlice(gpa, "flag");
    for (0..70) |_| try src.append(gpa, ')');
    try src.appendSlice(gpa, "; }\npub fn bad() *u8 { var x: u8 = 1; return &x; }\n");

    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, src.items);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 1), countByRule(analysis.problems, "stack-escape"));
    // Listed once even though lowering `too_deep` may fail again.
    try std.testing.expectEqual(@as(usize, 1), analysis.incomplete.len);
    const part = analysis.incomplete[0];
    try std.testing.expectEqual(Incomplete.Kind.summary, part.kind);
    try std.testing.expectEqualStrings("too_deep", part.name);
    const diagnostic = part.budget orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.normal_cleanup_depth, diagnostic.limit);
}

test "partial: a caller of a failed summary root is incomplete and reports no finding" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // `too_deep` exhausts the normal-cleanup depth during the summary pass.
    // `caller` reads that summary. Answering from a body-only recomputation
    // would present an unfinished fold as a finished one and report the
    // escape below; the failure must instead make `caller` incomplete.
    var src: std.ArrayListUnmanaged(u8) = .empty;
    defer src.deinit(gpa);
    try src.appendSlice(gpa, "fn too_deep(flag: bool) bool { return ");
    for (0..70) |_| try src.append(gpa, '(');
    try src.appendSlice(gpa, "flag");
    for (0..70) |_| try src.append(gpa, ')');
    try src.appendSlice(gpa,
        \\; }
        \\pub fn caller(flag: bool) *u8 {
        \\    var x: u8 = 1;
        \\    _ = too_deep(flag);
        \\    return &x;
        \\}
        \\pub fn control() *u8 { var y: u8 = 1; return &y; }
        \\
    );

    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, src.items);
    defer freeAnalysis(gpa, analysis);
    // Only the control, which reads no failed summary, still reports.
    try std.testing.expectEqual(@as(usize, 1), countByRule(analysis.problems, "stack-escape"));
    try std.testing.expect(std.mem.indexOf(u8, analysis.problems[0].message, "`y`") != null);
    // `caller` reads the failed summary while its own summary is built, so
    // the summary pass records it (kind `.summary`) and the per-function
    // pass does not list it again. Either kind makes it incomplete; it must
    // be listed exactly once and carry the budget that stopped it.
    var caller_entries: usize = 0;
    for (analysis.incomplete) |part| {
        if (!std.mem.eql(u8, part.name, "caller")) continue;
        try std.testing.expect(part.kind == .summary or part.kind == .function);
        try std.testing.expect(part.budget != null);
        caller_entries += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), caller_entries);
}

test "partial: a claimed budget record does not leak into the next file" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const many = try manyPathsFn(gpa);
    defer gpa.free(many);
    const first = try analyzeSrc(gpa, std.testing.io, &tmp, many);
    defer freeAnalysis(gpa, first);
    try std.testing.expectEqual(@as(usize, 1), first.incomplete.len);
    try std.testing.expect(budget_mod.peek() == null);

    const second = try analyzeSrc(gpa, std.testing.io, &tmp, "pub fn fine() u8 { return 1; }\n");
    defer freeAnalysis(gpa, second);
    try std.testing.expectEqual(@as(usize, 0), second.incomplete.len);
}

// ── Comptime-exhaustive field initialization ─────────────────────
//
// `var x: T = undefined;` followed by
// `inline for (@typeInfo(T).@"struct".fields) |f| { … @field(x, f.name) = …; }`
// leaves every semantic field of T written before the loop's normal
// exit, so returning x is not a leak of `undefined`.  The generic CFG
// models any loop as possibly running zero times, so these pin the
// narrow proof that closes that gap — and, just as importantly, pin
// the near-miss shapes it must still diagnose.
//
// The positives assert ZERO `use-undefined` diagnostics.  The near-misses
// count REPORTED SITES (`countRuleLines`), not diagnostics: handing back
// one undefined value is diagnosed twice — once for reading it, once for
// the value leaving the function — and how many ways a single leak gets
// phrased is not the contract here.  What they pin is WHICH leaks the
// proof must still let through.

/// Distinct source lines carrying `rule_id`.
fn countRuleLines(problems: []const Problem, rule_id: []const u8) usize {
    var n: usize = 0;
    for (problems, 0..) |p, i| {
        if (!std.mem.eql(u8, p.rule_id, rule_id)) continue;
        var repeats = false;
        for (problems[0..i]) |earlier| {
            if (!std.mem.eql(u8, earlier.rule_id, rule_id)) continue;
            if (earlier.start.line != p.start.line) continue;
            repeats = true;
            break;
        }
        if (!repeats) n += 1;
    }
    return n;
}

/// Every `rule_id` finding sits on `line`, and at least one exists.  A
/// near-miss must report its leak where the undefined value leaves the
/// function, not merely report SOMETHING: a count alone would let a
/// spurious report on the store line stand in for a missed leak.
fn expectRuleOnlyAtLine(problems: []const Problem, rule_id: []const u8, line: u32) !void {
    var seen = false;
    for (problems) |p| {
        if (!std.mem.eql(u8, p.rule_id, rule_id)) continue;
        try std.testing.expectEqual(line, p.start.line);
        seen = true;
    }
    try std.testing.expect(seen);
}

test "inline field enumeration over the declared type clears the undefined seed" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn pack(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    var i: u32 = 0;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        const item = base + i;
        \\        i += 1;
        \\        @field(result, field.name) = switch (field.type) {
        \\            u32 => item,
        \\            else => @compileError("unexpected field type"),
        \\        };
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "use-undefined"));
}

test "a zero-field struct is safe through the same enumeration" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // Instantiated with `const Empty = struct {};` the field tuple is
    // empty: the unrolled loop writes nothing, and `T` is zero-sized,
    // so there are no bytes left undefined.  `base` keeps the fn off
    // the all-comptime skip path so it is actually analysed.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\pub fn empty(comptime T: type, base: u8) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        @field(result, field.name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "use-undefined"));
}

test "a copy of the filled local is defined past the loop, not just the return" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // Nothing here reads the target directly — the copy carries its
    // origin, so without the proof this return leaks `undefined`.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn spill(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        @field(result, field.name) = base;
        \\    }
        \\    const copy: T = result;
        \\    return copy;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "use-undefined"));
}

test "a field write behind a conditional does not prove the whole struct" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // The lvalue is no longer a top-level statement of the body, so
    // some fields can skip it entirely.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn guarded(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        if (field.name.len == 1) {
        \\            @field(result, field.name) = base;
        \\        }
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try expectRuleOnlyAtLine(problems, "use-undefined", 9);
}

test "enumerating a hand-written name subset does not prove the struct" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn subset(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (.{ "left" }) |name| {
        \\        @field(result, name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try expectRuleOnlyAtLine(problems, "use-undefined", 7);
}

test "an unlabeled break out of the enumeration does not prove the struct" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn early(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        if (base == 0) break;
        \\        @field(result, field.name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try expectRuleOnlyAtLine(problems, "use-undefined", 8);
}

test "an unlabeled continue in the enumeration does not prove the struct" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn skipped(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        if (base == 0) continue;
        \\        @field(result, field.name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try expectRuleOnlyAtLine(problems, "use-undefined", 8);
}

test "enumerating another struct's fields does not prove the target" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // The descriptor names `Other`, so `right` is never enumerated.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\const Other = struct { left: u32 };
        \\pub fn crossed(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(Other).@"struct".fields) |field| {
        \\        @field(result, field.name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try expectRuleOnlyAtLine(problems, "use-undefined", 8);
}

test "a body-local shadow of the target does not prove the outer local" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn shadowed(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        var result: T = undefined;
        \\        @field(result, field.name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try expectRuleOnlyAtLine(problems, "use-undefined", 8);
}

test "an undefined right-hand side does not define the field it writes" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // The write happens; the VALUE is still undefined.  Claiming the
    // struct is initialized here would hide a real use-undefined.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn undefRhs(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        @field(result, field.name) = undefined;
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try expectRuleOnlyAtLine(problems, "use-undefined", 7);
}

test "storing a local seeded undefined does not define the field" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // The write target is right, but every field receives `src`'s
    // undefined bytes.  Two sites stay diagnosed: the read of `src`
    // itself, and the returned struct a synthetic "now defined" claim
    // would otherwise have silenced (that second site reports twice —
    // see the section header).
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn undefSource(comptime T: type, base: u32) T {
        \\    var src: u32 = undefined;
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        @field(result, field.name) = src;
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try std.testing.expectEqual(@as(usize, 2), countRuleLines(problems, "use-undefined"));
}

test "a comptime var type value is not the immutable parameter binding" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // `T` here is a mutable comptime local, not a `comptime T: type`
    // parameter, and the target is declared `Pair` — so `Other`'s
    // single field says nothing about `Pair`'s two.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\const Other = struct { left: u32 };
        \\pub fn mutableType(base: u32) Pair {
        \\    var result: Pair = undefined;
        \\    comptime var T = Other;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        @field(result, field.name) = base;
        \\    }
        \\    return result;
        \\}
        \\pub fn selected(base: u32) u32 {
        \\    const result = mutableType(base);
        \\    return result.right;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try expectRuleOnlyAtLine(problems, "use-undefined", 13);
}

test "the same enumeration without inline is still a runtime zero-trip hazard" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // `inline` is load-bearing: a runtime `for` over the same field
    // tuple may run zero times, leaving every field undefined.
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn runtimeLoop(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    for (@typeInfo(T).@"struct".fields) |field| {
        \\        @field(result, field.name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try expectRuleOnlyAtLine(problems, "use-undefined", 7);
}

test "a live child does not make its freed owner field readable" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Owner = struct { child: *u8 };
        \\pub fn readFreedOwner(gpa: std.mem.Allocator) !u8 {
        \\    const child = try gpa.create(u8);
        \\    defer gpa.destroy(child);
        \\    child.* = 7;
        \\    const owner = try gpa.create(Owner);
        \\    owner.child = child;
        \\    gpa.destroy(owner);
        \\    return owner.child.*;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    var witnessed = false;
    for (problems) |problem| {
        if (!std.mem.eql(u8, problem.rule_id, "heap-use-after-free")) continue;
        if (problem.start.line != 10) continue;
        for (problem.notes) |note| {
            if (note.start.line == 9) witnessed = true;
        }
    }
    try std.testing.expect(witnessed);
}

// ── Borrowed storage versus copied scalars ───────────────────────
//
// `defer child.deinit()` frees what the local owns, but a metric
// read out of that local is a COPY: the out-param's own storage
// holds it, and nothing in it points at the freed bytes.  A slice or
// a pointer read out of the same local still addresses them.  The
// twins below differ only in the type of the value that crosses the
// boundary, so they pin that distinction rather than a name.

test "a metric copied out of a deferred local is not a dangling out-param" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Stop = struct { limit: u8 = 0, cap: u32 = 0 };
        \\const Child = struct {
        \\    stopped: ?Stop = null,
        \\    bytes: []u8 = &.{},
        \\    pub fn deinit(self: *Child, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\    }
        \\};
        \\const Parent = struct { stopped: ?Stop = null };
        \\pub fn adopt(parent: *Parent, gpa: std.mem.Allocator) void {
        \\    var child: Child = .{};
        \\    defer child.deinit(gpa);
        \\    parent.stopped = parent.stopped orelse child.stopped;
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "borrowed-slice-into-out-param"));
}

test "a slice copied out of a deferred local is still a dangling out-param" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Child = struct {
        \\    bytes: []u8 = &.{},
        \\    pub fn deinit(self: *Child, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\    }
        \\};
        \\const Parent = struct { text: []const u8 = "" };
        \\pub fn adopt(parent: *Parent, gpa: std.mem.Allocator) void {
        \\    var child: Child = .{};
        \\    defer child.deinit(gpa);
        \\    parent.text = child.bytes;
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    const problems = analysis.problems;
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "borrowed-slice-into-out-param"));
}

test {
    _ = cfg_mod;
    _ = worklist;
    _ = config_mod;
    _ = problem_mod;
    _ = @import("flow/abstract_state.zig");
    _ = @import("flow/cfg_transfer.zig");
    _ = @import("flow/value_range.zig");
    // Pattern rules are registered in rule_catalog_mod alongside the
    // catalog metadata; pulling it in refAllDecls'es every rule
    // module so inline tests run.
    _ = rule_catalog_mod;
    _ = file_cache_mod;
    _ = suppressions_mod;
    _ = @import("model/fn_summary.zig");
    _ = @import("type_resolver.zig");
    _ = @import("ast/tokens.zig");
    _ = @import("ast/scope_iter.zig");
    _ = @import("model/method_names.zig");
    _ = @import("testing.zig");
    _ = @import("model/file_model.zig");
    _ = @import("trace.zig");
    _ = @import("model/local_bindings.zig");
    _ = @import("ast/token_query.zig");
    _ = @import("model/model_query.zig");
    _ = @import("cache/project_cache.zig");
    std.testing.refAllDecls(@This());
}

test "catch-noreturn payload: std debug panic preserves the defined success value" {
    // Exercise the imported decoder and the typed panic fallback from SIMD.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Result = struct { codepoint: u21, width: usize };
        \\pub fn decode(first: u16, second: u16) !Result {
        \\    if (!std.unicode.utf16IsHighSurrogate(first)) return error.InvalidFirst;
        \\    if (!std.unicode.utf16IsLowSurrogate(second)) return error.InvalidSecond;
        \\    const pair = [_]u16{ first, second };
        \\    const codepoint = std.unicode.utf16DecodeSurrogatePair(&pair) catch |err| {
        \\        std.debug.panic("validated pair failed: {s}", .{@errorName(err)});
        \\    };
        \\    return .{ .codepoint = codepoint, .width = 12 };
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "use-undefined"));
}

test "catch-noreturn payload: typed alias diverges on every fallback branch" {
    // The callee type, not a standard-library name, proves divergence.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn halt() noreturn { @panic("halt"); }
        \\fn load(value: u21) !u21 {
        \\    if (value == 0) return error.Empty;
        \\    return value;
        \\}
        \\pub fn decode(value: u21, flag: bool) u21 {
        \\    const stop = halt;
        \\    const codepoint = load(value) catch if (flag) stop() else halt();
        \\    return codepoint;
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "use-undefined"));
}

test "catch-noreturn payload: one value-yielding branch retains undefined findings" {
    // A divergent sibling cannot certify a fallback that yields undefined.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn halt() noreturn { @panic("halt"); }
        \\fn load(value: u21) !u21 {
        \\    if (value == 0) return error.Empty;
        \\    return value;
        \\}
        \\pub fn decode(value: u21, flag: bool) u21 {
        \\    const codepoint = load(value) catch blk: {
        \\        if (flag) halt();
        \\        break :blk @as(u21, undefined);
        \\    };
        \\    return codepoint;
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    try std.testing.expect(countByRule(analysis.problems, "use-undefined") > 0);
}

test "catch-noreturn payload: panic lookalike with a returning type remains conservative" {
    // A matching API name does not establish a noreturn return type.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const debug = struct { fn panic() u21 { return undefined; } };
        \\fn load(value: u21) !u21 {
        \\    if (value == 0) return error.Empty;
        \\    return value;
        \\}
        \\pub fn decode(value: u21) u21 {
        \\    const codepoint = load(value) catch debug.panic();
        \\    return codepoint;
        \\}
        \\
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    var reported_at_return = false;
    for (analysis.problems) |problem| {
        if (std.mem.eql(u8, problem.rule_id, "use-undefined") and problem.start.line == 8) {
            reported_at_return = true;
        }
    }
    try std.testing.expect(reported_at_return);
}

test "catch-noreturn payload: exit lookalike retains its returning fallback" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source =
        \\const process = struct { fn exit() u21 { return undefined; } };
        \\fn load(value: u21) !u21 {
        \\    if (value == 0) return error.Empty;
        \\    return value;
        \\}
        \\pub fn decode(value: u21) u21 {
        \\    const codepoint = load(value) catch process.exit();
        \\    return codepoint;
        \\}
        \\
    ;
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, source);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    var reported_codepoint = false;
    const caller_start = std.mem.indexOf(u8, source, "pub fn decode").?;
    for (analysis.problems) |problem| {
        if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
            problem.start.byte >= caller_start) reported_codepoint = true;
    }
    try std.testing.expect(reported_codepoint);
}

test "replay undefined: physical prefix survives unrelated receiver effects" {
    // Successful stores replace negative bytes without certifying opaque values.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source =
        \\extern fn get(index: usize) u32;
        \\extern fn release(receiver: *usize) void;
        \\extern fn emit(receiver: *usize, value: u32) void;
        \\pub fn copy(receiver: *usize, count: u8) void {
        \\    var values: [256]u32 = undefined;
        \\    for (0..count) |offset| values[offset] = get(offset);
        \\    release(receiver);
        \\    receiver.* = 0;
        \\    for (0..count) |offset| emit(receiver, values[offset]);
        \\}
    ;
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, source);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "use-undefined"));
}

test "replay undefined: counted stack transports selected union fields" {
    // Every reachable stack slot is assigned before its active payload is read.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Item = union(enum) { pair: struct { a: u32, b: u32 }, done: void };
        \\extern fn next(value: u32) u32;
        \\pub fn walk(value: u32) u32 {
        \\    var pending: [8]Item = undefined;
        \\    var length: usize = 1;
        \\    pending[0] = .{ .pair = .{ .a = value, .b = 0 } };
        \\    while (length > 0) {
        \\        length -= 1;
        \\        switch (pending[length]) {
        \\            .done => return 0,
        \\            .pair => |pair| {
        \\                if (pair.a == 0) return pair.b;
        \\                if (length >= 8) return 0;
        \\                pending[length] = .{ .pair = .{ .a = next(pair.a), .b = pair.b } };
        \\                length += 1;
        \\            },
        \\        }
        \\    }
        \\    return 0;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "use-undefined"));
}

test "replay undefined: aliased scalar stores defeat only their old negative bytes" {
    // Unknown arithmetic remains unknown after a definite physical output store.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\extern fn fused(a: f64, b: f64, c: f64) f64;
        \\fn multiply(arg_h: [*c]f64, arg_l: [*c]f64, a: f64, b: f64) void {
        \\    var h = arg_h;
        \\    _ = &h;
        \\    var l = arg_l;
        \\    _ = &l;
        \\    h.* = a * b;
        \\    l.* = fused(a, b, -h.*);
        \\}
        \\fn sum(a: f64, b: f64, low: *f64) f64 {
        \\    const high = a + b;
        \\    low.* = b - (high - a);
        \\    return high;
        \\}
        \\pub fn polynomial(a: f64, b: f64) f64 {
        \\    var high: f64 = undefined;
        \\    var low: f64 = undefined;
        \\    multiply(&high, &low, a, b);
        \\    high = sum(high, low, &low);
        \\    return high + low;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "use-undefined"));
}

test "replay undefined: repeated immutable guard restores a selected value" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn attempt(receiver: *usize) !void {
        \\    if (receiver.* == 0) return error.Empty;
        \\    receiver.* -= 1;
        \\}
        \\pub fn restore(receiver: *usize, index: usize, input: []const u32) !u32 {
        \\    const saved_length = input.len;
        \\    var saved: u32 = undefined;
        \\    if (index < saved_length) saved = input[index];
        \\    attempt(receiver) catch |err| {
        \\        receiver.* = saved_length;
        \\        if (index < saved_length) return saved;
        \\        return err;
        \\    };
        \\    return 0;
        \\}
    );
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    try std.testing.expectEqual(@as(usize, 0), countByRule(analysis.problems, "use-undefined"));
}

test "replay undefined: genuine holes conditional writes and zero trips remain reports" {
    // A skipped store and an untouched suffix retain independent negative evidence.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source =
        \\pub fn skipped(count: u8, write: bool) u32 {
        \\    var values: [256]u32 = undefined;
        \\    for (0..count) |offset| if (write) { values[offset] = 1; };
        \\    return values[0];
        \\}
        \\pub fn suffix(count: u8) u32 {
        \\    var values: [256]u32 = undefined;
        \\    for (0..count) |offset| values[offset] = 1;
        \\    return values[255];
        \\}
        \\pub fn zero(count: usize) u8 {
        \\    var value: u8 = undefined;
        \\    for (0..count) |_| value = 1;
        \\    return value;
        \\}
        \\pub fn poison() u32 {
        \\    var values: [4]u32 = undefined;
        \\    for (&values) |*value| value.* = undefined;
        \\    return values[0];
        \\}
    ;
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, source);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    for ([_][]const u8{ "pub fn skipped", "pub fn suffix", "pub fn zero", "pub fn poison" }) |function| {
        const start = std.mem.indexOf(u8, source, function).?;
        const returned = std.mem.indexOfPos(u8, source, start, "return ").?;
        const end = std.mem.indexOfPos(u8, source, returned, ";").?;
        var reported = false;
        for (analysis.problems) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                problem.start.byte >= returned and problem.start.byte < end) reported = true;
        }
        try std.testing.expect(reported);
    }
}

test "replay undefined scalar exact: translated sum overwrites unknown temporary before low store" {
    // Match erfd's mutable argument copies and addressed undefined temporary.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source =
        \\extern fn opaqueInput() f64;
        \\fn sum(arg_hi: [*c]f64, arg_lo: [*c]f64, arg_a: f64, arg_b: f64) void {
        \\    var hi = arg_hi;
        \\    _ = &hi;
        \\    var lo = arg_lo;
        \\    _ = &lo;
        \\    var a = arg_a;
        \\    _ = &a;
        \\    var b = arg_b;
        \\    _ = &b;
        \\    var e: f64 = undefined;
        \\    _ = &e;
        \\    hi.* = a + b;
        \\    e = hi.* - a;
        \\    lo.* = b - e;
        \\}
        \\pub fn physical() f64 {
        \\    var high: f64 = undefined;
        \\    var low: f64 = undefined;
        \\    sum(&high, &low, opaqueInput(), 1.0);
        \\    sum(&high, &low, high, 2.0);
        \\    return high + low;
        \\}
        \\pub fn selected() f64 {
        \\    var high: f64 = undefined;
        \\    var low: f64 = undefined;
        \\    sum(&high, &low, opaqueInput(), 1.0);
        \\    return low;
        \\}
        \\pub fn poison() f64 {
        \\    var high: f64 = undefined;
        \\    var low: f64 = undefined;
        \\    sum(&high, &low, opaqueInput(), 1.0);
        \\    low = undefined;
        \\    return low;
        \\}
        \\pub fn sibling() f64 {
        \\    var high: f64 = undefined;
        \\    var low: f64 = undefined;
        \\    var spare: f64 = undefined;
        \\    _ = &spare;
        \\    sum(&high, &low, opaqueInput(), 1.0);
        \\    return spare;
        \\}
    ;
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, source);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    for ([_]struct { function: []const u8, warns: bool }{
        .{ .function = "pub fn physical", .warns = false },
        .{ .function = "pub fn selected", .warns = false },
        .{ .function = "pub fn poison", .warns = true },
        .{ .function = "pub fn sibling", .warns = true },
    }) |case| {
        const start = std.mem.indexOf(u8, source, case.function).?;
        const returned = std.mem.indexOfPos(u8, source, start, "return ").?;
        const end = std.mem.indexOfPos(u8, source, returned, ";").?;
        var reported = false;
        for (analysis.problems) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                problem.start.byte >= returned and problem.start.byte < end) reported = true;
        }
        try std.testing.expectEqual(case.warns, reported);
    }
}

test "replay undefined prefix precise: capture discharge retains actual RHS poison" {
    // A source-authenticated poison return cannot become a written-value proof.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source =
        \\extern fn unknown(index: usize) u32;
        \\fn poison(index: usize) u32 { _ = index; return undefined; }
        \\pub fn unknownPrefix(count: u8) u32 {
        \\    var values: [256]u32 = undefined;
        \\    for (0..count) |offset| values[offset] = unknown(offset);
        \\    if (count == 0) return 0;
        \\    return values[count - 1];
        \\}
        \\pub fn poisonedPrefix(count: u8) u32 {
        \\    var values: [256]u32 = undefined;
        \\    for (0..count) |offset| values[offset] = poison(offset);
        \\    if (count == 0) return 0;
        \\    return values[count - 1];
        \\}
        \\pub fn poisonedOperand(count: u8) u32 {
        \\    var input: u32 = undefined;
        \\    var values: [256]u32 = undefined;
        \\    for (0..count) |offset| values[offset] = input + @as(u32, @intCast(offset));
        \\    if (count == 0) return 0;
        \\    return values[count - 1];
        \\}
    ;
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, source);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    for ([_]struct { function: []const u8, warns: bool }{
        .{ .function = "pub fn unknownPrefix", .warns = false },
        .{ .function = "pub fn poisonedPrefix", .warns = true },
        .{ .function = "pub fn poisonedOperand", .warns = true },
    }) |case| {
        const start = std.mem.indexOf(u8, source, case.function).?;
        const returned = std.mem.indexOfPos(u8, source, start, "return values").?;
        const end = std.mem.indexOfPos(u8, source, returned, ";").?;
        var reported = false;
        for (analysis.problems) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                problem.start.byte >= returned and problem.start.byte < end) reported = true;
        }
        try std.testing.expectEqual(case.warns, reported);
    }
}

test "replay undefined prefix precise: physical getter prefix retains aggregate child holes" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source =
        \\const Pair = struct { a: u32, b: u32 };
        \\fn poison(index: usize) Pair { _ = index; return undefined; }
        \\fn partial(index: usize) Pair { _ = index; return .{ .a = 1, .b = undefined }; }
        \\pub fn allPoison(count: u8) u32 {
        \\    var values: [256]Pair = undefined;
        \\    for (0..count) |offset| values[offset] = poison(offset);
        \\    if (count == 0) return 0;
        \\    return values[count - 1].a;
        \\}
        \\pub fn selectedWritten(count: u8) u32 {
        \\    var values: [256]Pair = undefined;
        \\    for (0..count) |offset| values[offset] = partial(offset);
        \\    if (count == 0) return 0;
        \\    return values[count - 1].a;
        \\}
        \\pub fn selectedHole(count: u8) u32 {
        \\    var values: [256]Pair = undefined;
        \\    for (0..count) |offset| values[offset] = partial(offset);
        \\    if (count == 0) return 0;
        \\    return values[count - 1].b;
        \\}
    ;
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, source);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    for ([_]struct { function: []const u8, warns: bool }{
        .{ .function = "pub fn allPoison", .warns = true },
        .{ .function = "pub fn selectedWritten", .warns = false },
        .{ .function = "pub fn selectedHole", .warns = true },
    }) |case| {
        const start = std.mem.indexOf(u8, source, case.function).?;
        const returned = std.mem.indexOfPos(u8, source, start, "return values").?;
        const end = std.mem.indexOfPos(u8, source, returned, ";").?;
        var reported = false;
        for (analysis.problems) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                problem.start.byte >= returned and problem.start.byte < end) reported = true;
        }
        try std.testing.expectEqual(case.warns, reported);
    }
}

test "replay undefined prefix precise: negative child deposits respect seeds alternatives and overwrites" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source =
        \\const Pair = struct { a: u32, b: u32 };
        \\extern fn unknownScalar() u32;
        \\extern fn mutate(*[256]Pair) void;
        \\fn partial(index: usize) Pair { _ = index; return .{ .a = 1, .b = undefined }; }
        \\fn oneSafe(index: usize) Pair {
        \\    if (index == 0) return .{ .a = 1, .b = 9 };
        \\    return .{ .a = 1, .b = undefined };
        \\}
        \\fn oneUnknown(index: usize) Pair {
        \\    if (index == 0) return .{ .a = 1, .b = unknownScalar() };
        \\    return .{ .a = 1, .b = undefined };
        \\}
        \\pub fn priorChild(count: u8) u32 {
        \\    var values: [256]Pair = undefined;
        \\    values[255].b = 9;
        \\    for (0..count) |offset| values[offset] = partial(offset);
        \\    if (count != 0) return 0;
        \\    return values[255].b;
        \\}
        \\pub fn safeArm(count: u8) u32 {
        \\    var values: [256]Pair = undefined;
        \\    for (0..count) |offset| values[offset] = oneSafe(offset);
        \\    if (count == 0) return 0;
        \\    return values[0].b;
        \\}
        \\pub fn unknownArm(count: u8) u32 {
        \\    var values: [256]Pair = undefined;
        \\    for (0..count) |offset| values[offset] = oneUnknown(offset);
        \\    if (count == 0) return 0;
        \\    return values[0].b;
        \\}
        \\pub fn laterChild(count: u8) u32 {
        \\    var values: [256]Pair = undefined;
        \\    for (0..count) |offset| values[offset] = partial(offset);
        \\    values[0].b = 7;
        \\    return values[0].b;
        \\}
        \\pub fn priorAlias(count: u8) u32 {
        \\    var values: [256]Pair = undefined;
        \\    mutate(&values);
        \\    for (0..count) |offset| values[offset] = partial(offset);
        \\    return values[255].b;
        \\}
        \\pub fn laterAlias(count: u8) u32 {
        \\    var values: [256]Pair = undefined;
        \\    for (0..count) |offset| values[offset] = partial(offset);
        \\    mutate(&values);
        \\    return values[255].b;
        \\}
    ;
    const analysis = try analyzeSrc(gpa, std.testing.io, &tmp, source);
    defer freeAnalysis(gpa, analysis);
    try std.testing.expectEqual(@as(usize, 0), analysis.incomplete.len);
    for ([_][]const u8{
        "pub fn priorChild", "pub fn safeArm", "pub fn unknownArm",
        "pub fn laterChild", "pub fn priorAlias", "pub fn laterAlias",
    }) |function| {
        const start = std.mem.indexOf(u8, source, function).?;
        const returned = std.mem.indexOfPos(u8, source, start, "return values").?;
        const end = std.mem.indexOfPos(u8, source, returned, ";").?;
        var reported = false;
        for (analysis.problems) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "use-undefined") and
                problem.start.byte >= returned and problem.start.byte < end) reported = true;
        }
        try std.testing.expect(!reported);
    }
}
