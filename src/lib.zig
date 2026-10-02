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
const project_cache_mod = @import("cache/project_cache.zig");

pub const Config = config_mod.Config;
pub const DefaultConfig = config_mod.Default;
pub const Invariant = config_mod.Invariant;
pub const all_invariants = config_mod.all_invariants;
pub const isEnabled = config_mod.isEnabled;
pub const invariantFromName = config_mod.invariantFromName;
pub const Problem = problem_mod.Problem;
pub const Note = problem_mod.Note;
pub const Pos = problem_mod.Pos;
pub const Severity = problem_mod.Severity;
pub const Verdict = problem_mod.Verdict;
pub const Rule = rule_catalog_mod.Rule;
pub const rule_catalog = rule_catalog_mod.all;
pub const lookupRule = rule_catalog_mod.lookup;
pub const trace = @import("trace.zig");
pub const SourcePolicy = @import("type_engine").SourcePolicy;

pub const ParseFailure = @import("type_engine").ParseFailure;

/// One worker and one source snapshot. Initialize in place; never share or move.
pub const Session = struct {
    gpa: std.mem.Allocator,
    io: std.Io,
    project: project_cache_mod.ProjectCache,
    type_context: zls_resolver_mod.TypeContext,
    parse_failure: ?ParseFailure = null,

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

    pub fn deinit(self: *Session) void {
        self.project.deinit();
        self.type_context.deinit();
        self.* = undefined;
    }

    fn sourcePath(self: *Session, path: []const u8) ![]const u8 {
        var cwd_buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
        const cwd = if (std.fs.path.isAbsolute(path)) "" else cwd_buffer[0..try std.Io.Dir.cwd().realPathFile(self.io, ".", &cwd_buffer)];
        const lexical = try std.fs.path.resolve(self.gpa, &.{ cwd, path });
        defer self.gpa.free(lexical);
        if (!self.project.policy.allowsAbsolutePath(lexical)) return error.SourceExcluded;
        const canonical = try self.type_context.canonicalPath(lexical);
        if (!self.project.policy.allowsAbsolutePath(canonical)) return error.SourceExcluded;
        return canonical;
    }
};

pub fn analyzeEscape(
    session: *Session,
    path: []const u8,
    config: *const Config,
) ![]Problem {
    const gpa = session.gpa;
    session.parse_failure = null;
    session.project.failure = null;
    session.project.parse_failure = null;
    session.type_context.store.source_failure = null;
    session.type_context.store.parse_failure = null;
    const canonical = try session.sourcePath(path);
    trace.setFile(path);

    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    errdefer freeProblemsArrayList(gpa, &problems);

    var resolver: zls_resolver_mod.TypeResolver = undefined;
    resolver.init(&session.type_context, gpa, canonical, null) catch |err| {
        if (err == error.ImportInvalidSyntax) {
            session.parse_failure = session.type_context.store.parse_failure;
            if (session.parse_failure) |*failure| failure.source_path = null;
            return error.InvalidSyntax;
        }
        return err;
    };
    defer resolver.deinit();
    const zls_ptr = &resolver;
    const tree = &resolver.handle.tree;
    if (tree.mode != .zig) return error.UnsupportedSourceLanguage;
    const src = tree.source;

    // Per-file shared cache, used by both flow analysis (cfg) and
    // pattern rules.  Amortizes FileModel + LocalBindings + FnSummary
    // across every consumer.
    var rule_cache = try file_cache_mod.FileCache.init(gpa, tree);
    defer rule_cache.deinit();
    rule_cache.setZls(zls_ptr);
    rule_cache.setProject(&session.project, canonical);
    try rule_cache.resolveTransitiveTakes();

    // Flow analysis — per-fn CFG + worklist fixed-point.
    // Iterate raw fn_decls (incl. type-builders) — lowerFunctionFull
    // decides per-fn whether to lower (returns null to skip).
    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        var cfg = (try cfg_builder.lowerFunctionFullWithZls(
            gpa,
            tree,
            node,
            config,
            &rule_cache,
            zls_ptr,
        )) orelse continue;
        defer cfg.deinit(gpa);
        // Budget failures are per-function; without the name the CLI
        // can only report a byte offset into a file the reader has to
        // open by hand.  The name is a borrow from `tree.source`,
        // which outlives this loop.  A fn_decl without a readable proto
        // yields "" and the diagnostic falls back to the offset.
        var proto_buf: [1]Ast.Node.Index = undefined;
        const fn_name: []const u8 = if (tree.fullFnProto(&proto_buf, node)) |proto|
            if (proto.name_token) |name_tok| tree.tokenSlice(name_tok) else ""
        else
            "";
        try worklist.check(gpa, &cfg, .{
            .path = path,
            .config = config,
            .fn_name = fn_name,
        }, &problems);
    }

    // Pattern detectors — dispatched via the comptime registry so
    // adding a rule is a one-file change (see rule_catalog.zig).
    try rule_catalog_mod.runEscape(gpa, tree, &rule_cache, config, &problems);
    if (session.project.failure) |failure| {
        session.parse_failure = session.project.parse_failure;
        return failure;
    }
    if (session.type_context.store.source_failure) |failure| {
        session.parse_failure = session.type_context.store.parse_failure;
        return failure;
    }

    // Apply per-line suppressions parsed from `// zbc-disable-line` /
    // `// zbc-disable-next-line` source comments.  Filter happens at
    // the boundary so individual rules don't need to know about it.
    var supp = try suppressions_mod.parse(gpa, src);
    defer supp.deinit();
    return try filterSuppressed(gpa, &problems, &supp);
}

/// Drop any Problems whose start.line matches an active suppression.
/// Frees dropped problems immediately; the caller still owns the
/// returned slice and the surviving problems' message storage.
fn filterSuppressed(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    supp: *const suppressions_mod.Suppressions,
) ![]Problem {
    if (supp.entries.len == 0) return problems.toOwnedSlice(gpa);
    var kept: std.ArrayListUnmanaged(Problem) = .empty;
    errdefer freeProblemsArrayList(gpa, &kept);
    for (problems.items) |p| {
        if (supp.isSuppressed(p.rule_id, p.start.line)) {
            var dead = p;
            dead.deinit(gpa);
            continue;
        }
        try kept.append(gpa, p);
    }
    problems.deinit(gpa);
    return kept.toOwnedSlice(gpa);
}

pub fn freeProblems(gpa: std.mem.Allocator, slice: []Problem) void {
    for (slice) |*p| p.deinit(gpa);
    gpa.free(slice);
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
    const problems = try analyzeEscape(&session, path, &DefaultConfig);
    defer freeProblems(gpa, problems);

    var found = false;
    for (problems) |p| {
        if (std.mem.indexOf(u8, p.message, "function-local arena") != null) found = true;
    }
    try std.testing.expect(found);
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
) ![]Problem {
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
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    return @ptrFromInt(0); // zbc-disable-line: ptrfromint-zero
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "ptrfromint-zero"));
}

test "suppression: without directive the finding is not dropped" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    return @ptrFromInt(0);
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expect(countByRule(problems, "ptrfromint-zero") >= 1);
}

test "suppression: zbc-disable-next-line drops the finding on the following line" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    // zbc-disable-next-line: ptrfromint-zero
        \\    return @ptrFromInt(0);
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "ptrfromint-zero"));
}

test "suppression: wildcard zbc-disable-line: * drops any rule" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    return @ptrFromInt(0); // zbc-disable-line: *
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "ptrfromint-zero"));
}

test "suppression: wrong rule id leaves the finding" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Directive targets a different rule → ptrfromint-zero still fires.
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn zero_ptr() *anyopaque {
        \\    return @ptrFromInt(0); // zbc-disable-line: some-other-rule
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expect(countByRule(problems, "ptrfromint-zero") >= 1);
}

test "suppression: directive only suppresses its own line, not others" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    // Two @ptrFromInt(0) calls on different lines.
    // Only the first has a directive — second still fires.
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\fn a() *anyopaque {
        \\    return @ptrFromInt(0); // zbc-disable-line: ptrfromint-zero
        \\}
        \\fn b() *anyopaque {
        \\    return @ptrFromInt(0);
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "ptrfromint-zero"));
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

test "invalid source is not a clean analysis" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try std.testing.expectError(error.InvalidSyntax, analyzeSrc(
        std.testing.allocator,
        std.testing.io,
        &tmp,
        "pub fn broken( {",
    ));
}

test "stable array repetition is analyzed without rewriting source" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(
        std.testing.allocator,
        std.testing.io,
        &tmp,
        "pub const values = [_]u8{0} ** 4;",
    );
    defer freeProblems(std.testing.allocator, problems);
    try std.testing.expectEqual(@as(usize, 0), problems.len);
}

test "extreme ceiling offset does not corrupt analysis" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(std.testing.allocator, std.testing.io, &tmp,
        \\fn ceil(x: u64) u64 {
        \\    return (x + 18446744073709551615) / 2;
        \\}
        \\pub fn f(x: u64, bytes: []const u8) u8 {
        \\    if (x != 0) {
        \\        const n = ceil(x);
        \\        return bytes[n - 1];
        \\    }
        \\    return 0;
        \\}
    );
    defer freeProblems(std.testing.allocator, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "index-minus-one-without-zero-guard"));
}

test "a scalar write invalidates the index guard in public analysis" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(std.testing.allocator, std.testing.io, &tmp,
        \\fn mutate(p: *usize) void { p.* = 0; }
        \\pub fn f(initial: usize, bytes: []const u8) u8 {
        \\    var i = initial;
        \\    if (i != 0) {
        \\        mutate(&i);
        \\        return bytes[i - 1];
        \\    }
        \\    return 0;
        \\}
    );
    defer freeProblems(std.testing.allocator, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "index-minus-one-without-zero-guard"));
}

test "a fresh session sees repaired imports and a live snapshot does not" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data =
        \\const dep = @import("dep.zig");
        \\pub fn copy(value: dep.Box) f32 { return @floatFromInt(value.value); }
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "dep.zig", .data = "// dependency\npub const Box = struct { value: ; };" });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    var session: Session = undefined;
    try session.init(gpa, io, .{ .roots = &.{directory} });
    defer session.deinit();
    try std.testing.expectEqual(null, try session.project.modelForRelativeImport(path, "dep.zig"));
    try std.testing.expectEqual(error.ImportInvalidSyntax, session.project.failure.?);
    try std.testing.expectEqual(@as(u32, 2), session.project.parse_failure.?.position.line);
    try std.testing.expectError(error.ImportInvalidSyntax, analyzeEscape(&session, path, &DefaultConfig));
    try std.testing.expect(session.parse_failure != null);
    try std.testing.expectEqual(@as(u32, 2), session.parse_failure.?.position.line);
    try std.testing.expectEqualStrings("dep.zig", std.fs.path.basename(session.parse_failure.?.source_path.?));
    try tmp.dir.writeFile(io, .{ .sub_path = "dep.zig", .data = "pub const Box = struct { value: u8 };" });
    session.project.failure = null;
    session.project.parse_failure = null;
    try std.testing.expectEqual(null, try session.project.modelForRelativeImport(path, "dep.zig"));
    try std.testing.expectEqual(error.ImportInvalidSyntax, session.project.failure.?);
    try std.testing.expectEqual(@as(u32, 2), session.project.parse_failure.?.position.line);
    try std.testing.expectError(error.ImportInvalidSyntax, analyzeEscape(&session, path, &DefaultConfig));
    try std.testing.expectEqual(@as(u32, 2), session.parse_failure.?.position.line);
    var fresh: Session = undefined;
    try fresh.init(gpa, io, .{ .roots = &.{directory} });
    defer fresh.deinit();
    const findings = try analyzeEscape(&fresh, path, &DefaultConfig);
    defer freeProblems(gpa, findings);
    try std.testing.expectEqual(@as(usize, 0), findings.len);
}

test "library analysis enforces the session source boundary" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "denied.zig", .data = "pub fn broken( {" });
    const path = try tmp.dir.realPathFileAlloc(io, "denied.zig", gpa);
    defer gpa.free(path);
    var session: Session = undefined;
    try session.init(gpa, io, .{});
    defer session.deinit();
    try std.testing.expectError(error.SourceExcluded, analyzeEscape(&session, path, &DefaultConfig));
}

test "an optional output slot may hold an optional value" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(std.testing.allocator, std.testing.io, &tmp,
        \\pub fn report(out: ?*?u32) void {
        \\    if (out) |p| p.* = null;
        \\}
    );
    defer freeProblems(std.testing.allocator, problems);
    try std.testing.expectEqual(@as(usize, 0), problems.len);
}

test "a no-op child cleanup does not consume its borrowed pointer" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(std.testing.allocator, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Child = struct {
        \\    value: u8,
        \\    fn deinit(self: *Child) void { _ = self; }
        \\};
        \\const Parent = struct {
        \\    child: *Child,
        \\    fn deinit(self: *Parent) void { self.child.deinit(); }
        \\};
        \\pub fn use(gpa: std.mem.Allocator) !u8 {
        \\    const child = try gpa.create(Child);
        \\    child.* = .{ .value = 7 };
        \\    var parent = Parent{ .child = child };
        \\    parent.deinit();
        \\    const result = child.value;
        \\    gpa.destroy(child);
        \\    return result;
        \\}
    );
    defer freeProblems(std.testing.allocator, problems);
    try std.testing.expectEqual(@as(usize, 0), problems.len);
}

test "same-file and imported destructors still expose a double free" {
    const child_source =
        \\pub const Child = struct {
        \\    gpa: @import("std").mem.Allocator,
        \\    pub fn deinit(self: *Child) void { self.gpa.destroy(self); }
        \\};
        \\
    ;
    const consumer =
        \\const Parent = struct {
        \\    child: *Child,
        \\    fn deinit(self: *Parent) void { self.child.deinit(); }
        \\};
        \\pub fn use(gpa: @import("std").mem.Allocator) !void {
        \\    const child = try gpa.create(Child);
        \\    child.* = .{ .gpa = gpa };
        \\    var parent = Parent{ .child = child };
        \\    parent.deinit();
        \\    gpa.destroy(child);
        \\}
    ;
    for ([_][]const u8{
        child_source ++ consumer,
        "const Child = @import(\"child.zig\").Child;\n" ++ consumer,
    }) |source| {
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        try tmp.dir.writeFile(std.testing.io, .{ .sub_path = "child.zig", .data = child_source });
        const problems = try analyzeSrc(std.testing.allocator, std.testing.io, &tmp, source);
        defer freeProblems(std.testing.allocator, problems);
        try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "heap-double-free"));
    }
}

test "an imported namespace callee keeps its first declared parameter" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(std.testing.io, .{ .sub_path = "lib.zig", .data =
        \\const std = @import("std");
        \\pub const Problem = struct {
        \\    bytes: []u8,
        \\    pub fn deinit(self: *Problem, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\pub fn freeProblems(gpa: std.mem.Allocator, slice: []Problem) void {
        \\    for (slice) |*p| p.deinit(gpa);
        \\    gpa.free(slice);
        \\}
        \\
    });
    // `lib` is a namespace, not an instance: declared param 0 is the
    // FIRST ARGUMENT.  Reading it as a method receiver frees the
    // allocator here and condemns every later use of it.
    const findings = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const lib = @import("lib.zig");
        \\
        \\pub fn run(gpa: std.mem.Allocator) !void {
        \\    const problems = try gpa.alloc(lib.Problem, 1);
        \\    lib.freeProblems(gpa, problems);
        \\    const tail = try gpa.alloc(u8, 4);
        \\    gpa.free(tail);
        \\    if (problems[0].bytes.len == 0) return;
        \\}
        \\
    );
    defer freeProblems(gpa, findings);
    // The transferred value is the slice passed as param 1 — so the
    // only use-after-free is the read of its first element's payload
    // on line 9, and the allocator passed as param 0 stays live
    // through lines 7 and 8.
    var use_after_free: usize = 0;
    for (findings) |finding| {
        if (!std.mem.eql(u8, finding.rule_id, "heap-use-after-free")) continue;
        use_after_free += 1;
        try std.testing.expectEqual(@as(u32, 9), finding.start.line);
    }
    try std.testing.expectEqual(@as(usize, 1), use_after_free);
    try std.testing.expectEqual(@as(usize, 0), countByRule(findings, "heap-double-free"));
}

test "an instance method still spends its receiver on declared parameter zero" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(std.testing.allocator, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Item = struct { value: u8 };
        \\const Holder = struct {
        \\    gpa: std.mem.Allocator,
        \\    pub fn dispose(self: *Holder, gpa: std.mem.Allocator, item: *Item) void { gpa.destroy(item); }
        \\};
        \\pub fn run(gpa: std.mem.Allocator) !void {
        \\    var holder = Holder{ .gpa = gpa };
        \\    const item = try gpa.create(Item);
        \\    holder.dispose(gpa, item);
        \\    if (item.value == 0) return;
        \\}
        \\
    );
    defer freeProblems(std.testing.allocator, problems);
    // Declared param 2 lands on args[1]: `holder` holds param 0 and
    // `gpa` holds param 1, so the destroyed `item` is still diagnosed.
    // `self` is deliberately unused — an instance receiver spends param 0
    // on being a receiver, whether or not the body touches it.
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "heap-use-after-free"));
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "heap-double-free"));
}

test "Marker and Node ownership stays import-scoped in either project order" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.createDirPath(io, "a");
    try tmp.dir.createDirPath(io, "b");
    const resources = [_][]const u8{
        \\const Allocator = @import("std").mem.Allocator;
        \\pub const Marker = struct {
        \\    gpa: Allocator,
        \\    pub fn deinit(self: *Marker) void { self.gpa.destroy(self); }
        \\};
        \\pub const Node = struct {
        \\    gpa: Allocator,
        \\    pub fn deinit(self: *Node) void { self.gpa.destroy(self); }
        \\};
        ,
        \\const Allocator = @import("std").mem.Allocator;
        \\pub const Marker = struct {
        \\    gpa: Allocator,
        \\    pub fn deinit(self: *Marker) void { _ = self; }
        \\};
        \\pub const Node = struct {
        \\    gpa: Allocator,
        \\    pub fn release(self: *Node) void { self.gpa.destroy(self); }
        \\};
        ,
    };
    const bodies =
        \\pub fn use(gpa: @import("std").mem.Allocator) !void {
        \\    const marker = try gpa.create(leaf.Marker);
        \\    errdefer gpa.destroy(marker);
        \\    marker.* = .{ .gpa = gpa };
        \\    const node = try gpa.create(leaf.Node);
        \\    node.* = .{ .gpa = gpa };
        \\    var parent = Parent{ .marker = marker, .node = node };
        \\    parent.deinit();
        \\    gpa.destroy(marker);
        \\    gpa.destroy(node);
        \\}
    ;
    const consumers = [_][]const u8{
        "const leaf = @import(\"resource.zig\");\n" ++
            "const Parent = struct { marker: *leaf.Marker, node: *leaf.Node,\n" ++
            "fn deinit(self: *Parent) void { self.marker.deinit(); self.node.deinit(); } };\n" ++ bodies,
        "const leaf = @import(\"resource.zig\");\n" ++
            "const Parent = struct { marker: *leaf.Marker, node: *leaf.Node,\n" ++
            "fn deinit(self: *Parent) void { self.marker.deinit(); self.node.release(); } };\n" ++ bodies,
    };
    try tmp.dir.writeFile(io, .{ .sub_path = "a/resource.zig", .data = resources[0] });
    try tmp.dir.writeFile(io, .{ .sub_path = "b/resource.zig", .data = resources[1] });
    try tmp.dir.writeFile(io, .{ .sub_path = "a/main.zig", .data = consumers[0] });
    try tmp.dir.writeFile(io, .{ .sub_path = "b/main.zig", .data = consumers[1] });
    const a = try tmp.dir.realPathFileAlloc(io, "a", gpa);
    defer gpa.free(a);
    const b = try tmp.dir.realPathFileAlloc(io, "b", gpa);
    defer gpa.free(b);
    const main_a = try tmp.dir.realPathFileAlloc(io, "a/main.zig", gpa);
    defer gpa.free(main_a);
    const main_b = try tmp.dir.realPathFileAlloc(io, "b/main.zig", gpa);
    defer gpa.free(main_b);
    const paths = [_][]const u8{ main_a, main_b };
    const expected = [_]usize{ 2, 1 };
    for ([_][2]usize{ .{ 0, 1 }, .{ 1, 0 } }) |order| {
        var session: Session = undefined;
        try session.init(gpa, io, .{ .roots = &.{ a, b } });
        defer session.deinit();
        for (order) |index| {
            const problems = try analyzeEscape(&session, paths[index], &DefaultConfig);
            defer freeProblems(gpa, problems);
            try std.testing.expectEqual(expected[index], countByRule(problems, "heap-double-free"));
            var locations: u8 = 0;
            for (problems) |finding| {
                if (!std.mem.eql(u8, finding.rule_id, "heap-double-free")) continue;
                locations |= switch (finding.start.line) {
                    12 => @as(u8, 1),
                    13 => @as(u8, 2),
                    else => return error.UnexpectedFreeLocation,
                };
            }
            try std.testing.expectEqual(@as(u8, if (index == 0) 3 else 2), locations);
        }
    }
}

test "root source stays immutable until a fresh session" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "root.zig", .data = "pub const answer = 1;" });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try tmp.dir.realPathFileAlloc(io, "root.zig", gpa);
    defer gpa.free(path);
    var snapshot: Session = undefined;
    try snapshot.init(gpa, io, .{ .roots = &.{directory} });
    defer snapshot.deinit();
    const original = try analyzeEscape(&snapshot, path, &DefaultConfig);
    defer freeProblems(gpa, original);
    try tmp.dir.writeFile(io, .{ .sub_path = "root.zig", .data = "pub fn broken( {" });
    const unchanged = try analyzeEscape(&snapshot, path, &DefaultConfig);
    defer freeProblems(gpa, unchanged);
    try std.testing.expectEqual(@as(usize, 0), unchanged.len);
    var fresh: Session = undefined;
    try fresh.init(gpa, io, .{ .roots = &.{directory} });
    defer fresh.deinit();
    try std.testing.expectError(error.InvalidSyntax, analyzeEscape(&fresh, path, &DefaultConfig));
    try tmp.dir.deleteFile(io, "root.zig");
    const retained = try analyzeEscape(&snapshot, path, &DefaultConfig);
    defer freeProblems(gpa, retained);
    try std.testing.expectEqual(@as(usize, 0), retained.len);
}

test "root and imported models use the same source snapshot" {
    try checkSharedSourceSnapshot(false);
}

test "symlink imports retain the same source snapshot" {
    try checkSharedSourceSnapshot(true);
}

fn checkSharedSourceSnapshot(import_alias: bool) !void {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const declaration =
        \\pub const Count = u8;
        \\pub const Node = struct {
        \\    gpa: @import("std").mem.Allocator,
        \\
    ;
    try tmp.dir.writeFile(io, .{ .sub_path = "resource.zig", .data = declaration ++
        "pub fn deinit(self: *Node) void { _ = self; }\n};" });
    const consumer_source =
        \\const Node = @import("resource.zig").Node;
        \\const Parent = struct {
        \\    node: *Node,
        \\    fn deinit(self: *Parent) void { self.node.deinit(); }
        \\};
        \\pub fn use(gpa: @import("std").mem.Allocator) !void {
        \\    const node = try gpa.create(Node);
        \\    node.* = .{ .gpa = gpa };
        \\    var parent = Parent{ .node = node };
        \\    parent.deinit();
        \\    gpa.destroy(node);
        \\}
    ;
    try tmp.dir.writeFile(io, .{ .sub_path = "consumer.zig", .data = consumer_source });
    if (import_alias) {
        try tmp.dir.symLink(io, "resource.zig", "alias.zig", .{});
        try tmp.dir.writeFile(io, .{ .sub_path = "probe.zig", .data =
            \\pub fn probe(value: @import("alias.zig").Count) f32 {
            \\    return @floatFromInt(value);
            \\}
        });
    }
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const first_path = try tmp.dir.realPathFileAlloc(io, if (import_alias) "probe.zig" else "resource.zig", gpa);
    defer gpa.free(first_path);
    const consumer = try tmp.dir.realPathFileAlloc(io, "consumer.zig", gpa);
    defer gpa.free(consumer);
    var snapshot: Session = undefined;
    try snapshot.init(gpa, io, .{ .roots = &.{directory} });
    defer snapshot.deinit();
    const original = try analyzeEscape(&snapshot, first_path, &DefaultConfig);
    defer freeProblems(gpa, original);
    try tmp.dir.writeFile(io, .{ .sub_path = "resource.zig", .data = declaration ++
        "pub fn deinit(self: *Node) void { self.gpa.destroy(self); }\n};" });
    const unchanged = try analyzeEscape(&snapshot, consumer, &DefaultConfig);
    defer freeProblems(gpa, unchanged);
    try std.testing.expectEqual(@as(usize, 0), countByRule(unchanged, "heap-double-free"));
    var fresh: Session = undefined;
    try fresh.init(gpa, io, .{ .roots = &.{directory} });
    defer fresh.deinit();
    const changed = try analyzeEscape(&fresh, consumer, &DefaultConfig);
    defer freeProblems(gpa, changed);
    try std.testing.expectEqual(@as(usize, 1), countByRule(changed, "heap-double-free"));
    try tmp.dir.writeFile(io, .{ .sub_path = "after_delete.zig", .data = consumer_source });
    const after_delete = try tmp.dir.realPathFileAlloc(io, "after_delete.zig", gpa);
    defer gpa.free(after_delete);
    try tmp.dir.deleteFile(io, "resource.zig");
    const retained = try analyzeEscape(&snapshot, after_delete, &DefaultConfig);
    defer freeProblems(gpa, retained);
    try std.testing.expectEqual(@as(usize, 0), countByRule(retained, "heap-double-free"));
}

test "borrowed-return summaries do not cross declaration scopes" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const gpa = std.testing.allocator;
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Buffer = struct {
        \\    bytes: [1]u8,
        \\    fn slice(_: *const Buffer) []const u8 { return "static"; }
        \\};
        \\fn slice(b: *const Buffer) []const u8 { return b.bytes[0..]; }
        \\const Ns = struct { fn slice(_: *const Buffer) []const u8 { return "static"; } };
        \\fn viaMethod(b: *const Buffer) []const u8 { return b.slice(); }
        \\fn viaNamespace(b: *const Buffer) []const u8 { return Ns.slice(b); }
        \\pub fn safeMethod() []const u8 {
        \\    var b = Buffer{ .bytes = .{0} };
        \\    const p = &b;
        \\    const result = viaMethod(p);
        \\    return result;
        \\}
        \\pub fn safeNamespace() []const u8 {
        \\    var b = Buffer{ .bytes = .{0} };
        \\    const p = &b;
        \\    const result = viaNamespace(p);
        \\    return result;
        \\}
        \\pub fn bad() []const u8 {
        \\    var b = Buffer{ .bytes = .{0} };
        \\    const p = &b;
        \\    const result = slice(p);
        \\    return result;
        \\}
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "stack-escape"));
    for (problems) |problem| {
        if (std.mem.eql(u8, problem.rule_id, "stack-escape")) {
            try std.testing.expectEqual(@as(u32, 25), problem.start.line);
        }
    }
}

test "generic arguments do not inherit the enclosing receiver destructor" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const gpa = std.testing.allocator;
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Allocator = @import("std").mem.Allocator;
        \\const Borrowed = struct {
        \\    value: u8,
        \\    fn deinit(_: *Borrowed) void {}
        \\};
        \\const Owner = struct {
        \\    gpa: Allocator,
        \\    fn deinit(self: *Owner) void { self.gpa.destroy(self); }
        \\    fn clean(self: *Owner, other: anytype) void {
        \\        _ = self;
        \\        other.deinit();
        \\    }
        \\};
        \\pub fn safe(gpa: Allocator) !void {
        \\    const other = try gpa.create(Borrowed);
        \\    other.* = .{ .value = 1 };
        \\    var owner = Owner{ .gpa = gpa };
        \\    owner.clean(other);
        \\    gpa.destroy(other);
        \\}
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "heap-double-free"));
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

test "inline field enumeration over the declared type clears the undefined seed" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
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
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\pub fn empty(comptime T: type, base: u8) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        @field(result, field.name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "use-undefined"));
}

test "a copy of the filled local is defined past the loop, not just the return" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // Nothing here reads the target directly — the copy carries its
    // origin, so without the proof this return leaks `undefined`.
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "use-undefined"));
}

test "a field write behind a conditional does not prove the whole struct" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // The lvalue is no longer a top-level statement of the body, so
    // some fields can skip it entirely.
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countRuleLines(problems, "use-undefined"));
}

test "enumerating a hand-written name subset does not prove the struct" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn subset(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (.{ "left" }) |name| {
        \\        @field(result, name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countRuleLines(problems, "use-undefined"));
}

test "an unlabeled break out of the enumeration does not prove the struct" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countRuleLines(problems, "use-undefined"));
}

test "an unlabeled continue in the enumeration does not prove the struct" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countRuleLines(problems, "use-undefined"));
}

test "enumerating another struct's fields does not prove the target" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // The descriptor names `Other`, so `right` is never enumerated.
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countRuleLines(problems, "use-undefined"));
}

test "a body-local shadow of the target does not prove the outer local" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countRuleLines(problems, "use-undefined"));
}

test "an undefined right-hand side does not define the field it writes" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // The write happens; the VALUE is still undefined.  Claiming the
    // struct is initialized here would hide a real use-undefined.
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn undefRhs(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    inline for (@typeInfo(T).@"struct".fields) |field| {
        \\        @field(result, field.name) = undefined;
        \\    }
        \\    return result;
        \\}
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countRuleLines(problems, "use-undefined"));
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
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 2), countRuleLines(problems, "use-undefined"));
}

test "a comptime var type value is not the immutable parameter binding" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // `T` here is a mutable comptime local, not a `comptime T: type`
    // parameter, and the target is declared `Pair` — so `Other`'s
    // single field says nothing about `Pair`'s two.
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countRuleLines(problems, "use-undefined"));
}

test "the same enumeration without inline is still a runtime zero-trip hazard" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    // `inline` is load-bearing: a runtime `for` over the same field
    // tuple may run zero times, leaving every field undefined.
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const Pair = struct { left: u32, right: u32 };
        \\pub fn runtimeLoop(comptime T: type, base: u32) T {
        \\    var result: T = undefined;
        \\    for (@typeInfo(T).@"struct".fields) |field| {
        \\        @field(result, field.name) = base;
        \\    }
        \\    return result;
        \\}
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countRuleLines(problems, "use-undefined"));
}

test "a live child does not make its freed owner field readable" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "heap-use-after-free"));
    for (problems) |problem| {
        if (!std.mem.eql(u8, problem.rule_id, "heap-use-after-free")) continue;
        try std.testing.expectEqual(@as(u32, 10), problem.start.line);
    }
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
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "borrowed-slice-into-out-param"));
}

test "a slice copied out of a deferred local is still a dangling out-param" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
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
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "borrowed-slice-into-out-param"));
}

// ── Loop iteration versus a growing callee ──────────────────────
//
// Collection growth is disjoint only when allocation provenance proves it.
// Different parameters or embedded header fields can share one buffer.
// Const wrappers and copied headers do not establish independent ownership.

test "a growing callee behind a const view leaves the loop pointer alive" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Tally = struct { entries: std.ArrayList(u32) };
        \\fn growOwnList(tally: *const Tally, entry: u32) void {
        \\    var scratch: std.array_list.Managed(u32) = std.array_list.Managed(u32).init(std.heap.page_allocator);
        \\    defer scratch.deinit();
        \\    scratch.append(entry) catch {};
        \\    _ = tally;
        \\}
        \\pub fn walk(tally: *const Tally) void {
        \\    for (tally.entries.items) |entry| {
        \\        growOwnList(tally, entry);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a growing callee handed the mutable owner invalidates the loop pointer" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Tally = struct { entries: std.ArrayList(u32) };
        \\fn growOwnList(tally: *Tally, entry: u32) void {
        \\    tally.entries.append(std.heap.page_allocator, entry) catch {};
        \\}
        \\pub fn walk(tally: *Tally) void {
        \\    for (tally.entries.items) |entry| {
        \\        growOwnList(tally, entry);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a growing callee that only reads a field leaves the loop pointer alive" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Tree = struct { nodes: std.ArrayList(u32) };
        \\fn firstIndex(tree: *Tree) usize {
        \\    return tree.nodes.items.len;
        \\}
        \\fn record(index: usize, node: u32) void {
        \\    var scratch: std.array_list.Managed(u32) = std.array_list.Managed(u32).init(std.heap.page_allocator);
        \\    defer scratch.deinit();
        \\    scratch.append(node) catch {};
        \\    _ = index;
        \\}
        \\pub fn walk(tree: *Tree) void {
        \\    for (tree.nodes.items) |node| {
        \\        record(firstIndex(tree), node);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a callee growing an embedded header can invalidate its copied peer" {
    // The two fields are distinct headers over the same allocation.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Oracle = struct {
        \\    tree: std.ArrayList(u32),
        \\    aliases: std.ArrayList(u32),
        \\};
        \\fn recordAlias(oracle: *Oracle, value: u32) void {
        \\    oracle.aliases.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(oracle: *Oracle) void {
        \\    for (oracle.tree.items) |node| {
        \\        recordAlias(oracle, node);
        \\    }
        \\}
        \\pub fn aliased(oracle: *Oracle) void {
        \\    oracle.aliases = oracle.tree;
        \\    walk(oracle);
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a callee that grows the iterated field of the same owner invalidates the loop pointer" {
    // Same owner, same parameter as the safe case above, but the grow
    // lands on `oracle.tree` — the buffer being walked.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Oracle = struct {
        \\    tree: std.ArrayList(u32),
        \\    aliases: std.ArrayList(u32),
        \\};
        \\fn recordNode(oracle: *Oracle, value: u32) void {
        \\    oracle.tree.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(oracle: *Oracle) void {
        \\    for (oracle.tree.items) |node| {
        \\        recordNode(oracle, node);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a const wrapper around a mutable list invalidates the loop pointer" {
    // `*const View` freezes the wrapper, not the list it points at.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const View = struct { entries: *std.ArrayList(u32) };
        \\fn growThroughView(view: *const View, value: u32) void {
        \\    view.entries.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(view: *const View) void {
        \\    for (view.entries.items) |item| {
        \\        growThroughView(view, item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a copied list header invalidates the loop pointer" {
    // The callee copies the ArrayList HEADER, not its buffer, then
    // appends: the shared allocation can be reallocated and freed out
    // from under the loop.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn growCopy(list: *List, value: u32) void {
        \\    var copy: List = list.*;
        \\    copy.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *List) void {
        \\    for (list.items) |item| {
        \\        growCopy(list, item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "an alias reached through a delegating callee invalidates the loop pointer" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn appendInner(list: *List, value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\fn appendOuter(list: *List, value: u32) void {
        \\    appendInner(list, value);
        \\}
        \\pub fn walk(list: *List) void {
        \\    for (list.items) |item| {
        \\        appendOuter(list, item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "an argument whose aliasing is unresolved invalidates the loop pointer" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn growList(list: *List, value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *List, view: *const List) void {
        \\    for (list.items) |item| {
        \\        growList(@constCast(view), item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a growing callee can reach the iterated list through another parameter" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Tree = struct { nodes: std.ArrayList(u32) };
        \\fn growInto(list: *std.ArrayList(u32), value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(tree: *Tree, other: *std.ArrayList(u32)) void {
        \\    for (tree.nodes.items) |node| {
        \\        growInto(other, node);
        \\    }
        \\}
        \\pub fn aliased(tree: *Tree) void { walk(tree, &tree.nodes); }
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a callee that grows a header copied from a file-level list is not proof of safety" {
    // `var copy = shared;` names no parameter and no local of the
    // callee, yet the copy shares a file-level list's buffer — and
    // nothing stops that list from being the one the loop walks.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\var shared: std.ArrayList(u32) = undefined;
        \\fn growShared(value: u32) void {
        \\    var copy: std.ArrayList(u32) = shared;
        \\    copy.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growShared(item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a callee that grows a header returned by a call is not proof of safety" {
    // One call deeper: the header comes out of a function this file
    // cannot place, so the grow lands on storage somebody else may
    // still be walking.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\var shared: std.ArrayList(u32) = undefined;
        \\fn currentShared() std.ArrayList(u32) { return shared; }
        \\fn growShared(value: u32) void {
        \\    var copy: std.ArrayList(u32) = currentShared();
        \\    copy.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growShared(item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "an unresolved callee handed the iterated list is not treated as disjoint" {
    // `keepName` is an opaque function pointer this file has no
    // declaration to read behind, and its name says nothing about
    // growth.  What decides this is that the file cannot resolve it
    // AND the call hands it the list the loop walks, so not resolving
    // it is a blind spot, not a clean bill of health.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Keep = *const fn (*List, u32) void;
        \\fn grow(list: *List, value: u32, keepName: Keep) void {
        \\    keepName(list, value);
        \\}
        \\pub fn walk(list: *List, keepName: Keep) void {
        \\    for (list.items) |item| {
        \\        grow(list, item, keepName);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "two pointer fields of one owner may hold the same list" {
    // `a` and `b` are different fields, but each points at a list, so
    // the callee's append can move the buffer the loop is walking.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Pair = struct {
        \\    a: *std.ArrayList(u32),
        \\    b: *std.ArrayList(u32),
        \\};
        \\fn growA(pair: *Pair, value: u32) void {
        \\    pair.a.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(pair: *Pair) void {
        \\    for (pair.b.items) |item| {
        \\        growA(pair, item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a callee that builds its own list leaves the loop pointer alive" {
    // The control for the two cases above: this header is built by the
    // callee's own call, so growing it moves nothing the caller handed
    // over.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn recordOwn(value: u32) !void {
        \\    var scratch: List = try List.initCapacity(std.heap.page_allocator, 0);
        \\    defer scratch.deinit(std.heap.page_allocator);
        \\    scratch.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *List) void {
        \\    for (list.items) |item| {
        \\        recordOwn(item) catch {};
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "an imported free function handed the iterated list invalidates the loop pointer" {
    // `helpers.growName(...)` lives in another file and its name says
    // nothing about growth — but the module IS readable, so its
    // effects are read rather than guessed, and the list it appends to
    // is the one the loop walks.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(std.testing.io, .{
        .sub_path = "helpers.zig",
        .data =
        \\const std = @import("std");
        \\pub fn growName(list: *std.ArrayList(u32), value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        ,
    });
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const helpers = @import("./helpers.zig");
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        helpers.growName(list, item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a callee whose own constructor builds the list leaves the loop pointer alive" {
    // `Real.init` returns a list it just constructed, so the header the
    // callee grows is its own.  The name of the method is no evidence;
    // its declaration is.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Real = struct {
        \\    list: std.array_list.Managed(u32),
        \\    pub fn init(gpa: std.mem.Allocator) Real {
        \\        return .{ .list = std.array_list.Managed(u32).init(gpa) };
        \\    }
        \\};
        \\fn growOwnList(value: u32) void {
        \\    var copy: Real = Real.init(std.heap.page_allocator);
        \\    defer copy.list.deinit();
        \\    copy.list.append(value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growOwnList(item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a constructor that returns a copied global is not proof of safety" {
    // The mirror of the case above, and the reason a constructor name
    // proves nothing on its own: this `init` returns a file-level
    // list's header, which somebody else may be walking.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\var shared: std.ArrayList(u32) = undefined;
        \\const Fake = struct {
        \\    list: std.ArrayList(u32),
        \\    pub fn init(_: void) Fake {
        \\        return .{ .list = shared };
        \\    }
        \\};
        \\fn growShared(value: u32) void {
        \\    var copy: Fake = Fake.init({});
        \\    copy.list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growShared(item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "an imported free function that grows a list of its own is charged to its caller" {
    // `record` hands `helpers.note` a NUMBER, not storage, so
    // nothing the call hands over is charged from the argument
    // list alone.  What the imported declaration says is that its
    // own `pending` list grows, and this file cannot place that
    // allocation from another file — so the reach is still
    // undecided and the loop pointer is not safe.  Reading the
    // import's declaration is the whole point: a call reached by
    // NAME alone would charge only what it was handed and would
    // miss this entirely.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(std.testing.io, .{
        .sub_path = "helpers.zig",
        .data =
        \\const std = @import("std");
        \\var pending: std.ArrayList(u32) = undefined;
        \\pub fn note(value: u32) void {
        \\    pending.append(std.heap.page_allocator, value) catch {};
        \\}
        ,
    });
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const helpers = @import("./helpers.zig");
        \\var next: u32 = 0;
        \\fn record() void {
        \\    helpers.note(next);
        \\    next += 1;
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        record();
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a constructor nested in a container of this file still builds its own list" {
    // The type is addressed from the outside as `Registry.Bag` and
    // from inside its own declaration as bare `Bag`.  A resolver
    // that only answers the qualified spelling cannot read the
    // `return .{ .list = … }` this constructor is judged by, and
    // would charge a list the constructor plainly built for itself.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Registry = struct {
        \\    pub const Bag = struct {
        \\        list: std.array_list.Managed(u32),
        \\        pub fn init(gpa: std.mem.Allocator) Bag {
        \\            return .{ .list = std.array_list.Managed(u32).init(gpa) };
        \\        }
        \\    };
        \\};
        \\fn growOwnList(value: u32) void {
        \\    var copy: Registry.Bag = Registry.Bag.init(std.heap.page_allocator);
        \\    defer copy.list.deinit();
        \\    copy.list.append(value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growOwnList(item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a parameter handed to a method on a freshly built owner is still charged" {
    // `own` is provably built here — the literal supplies the one
    // storage field and the type leaves no other — so growing
    // `own.entries` moves nothing the caller holds.  The METHOD on
    // it is a different question: it is handed the caller's list,
    // and nothing about the receiver being fresh says the callee
    // leaves its arguments alone.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Holder = struct {
        \\    entries: std.array_list.Managed(u32),
        \\    pub fn absorb(self: *Holder, other: *std.ArrayList(u32)) void {
        \\        self.entries.appendSlice(other.items) catch {};
        \\    }
        \\};
        \\fn grow(list: *std.ArrayList(u32), value: u32) void {
        \\    var own: Holder = .{ .entries = std.array_list.Managed(u32).init(std.heap.page_allocator) };
        \\    defer own.entries.deinit();
        \\    own.entries.append(value) catch {};
        \\    own.absorb(list);
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        grow(list, item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a writable owner address whose callee grows only its own list leaves the loop pointer alive" {
    // The mirror of "the address of a value owner reaches the
    // iterated list": the address is what decides that the callee
    // could reach the owner at all, and here it reaches it to grow a
    // header of its own instead.  `owner` is a MUTABLE local
    // because `&owner` is what a callee taking `*Tally` needs; a
    // `const` binding would make this program not compile, which
    // would say nothing about the rule.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Tally = struct { entries: std.array_list.Managed(u32) };
        \\fn collect(source: *Tally, entry: u32) void {
        \\    var scratch: std.array_list.Managed(u32) = std.array_list.Managed(u32).init(std.heap.page_allocator);
        \\    defer scratch.deinit();
        \\    scratch.append(entry) catch {};
        \\    _ = source;
        \\}
        \\pub fn walk(source: Tally) void {
        \\    var owner: Tally = source;
        \\    defer owner.entries.deinit();
        \\    for (owner.entries.items) |item| {
        \\        collect(&owner, item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a namespace callee this file cannot read as a module is charged what it is handed" {
    // `helpers` is a namespace this analyser has no import
    // declaration for, so the free function behind `keepName` is
    // undecided — and it is handed the very list the loop walks.
    // Not seeing it is a blind spot, not evidence that it leaves
    // the buffer alone.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const helpers = struct {
        \\    pub fn keepName(list: *std.ArrayList(u32), value: u32) void {
        \\        _ = list;
        \\        _ = value;
        \\    }
        \\};
        \\fn grow(list: *std.ArrayList(u32), value: u32) void {
        \\    helpers.keepName(list, value);
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        grow(list, item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a struct literal that omits a field the type defaults to a name-free value builds fresh" {
    // `count` is left out, and the type gives it a default that
    // reads no name — so the one field the literal DOES supply is
    // the whole question, and it is a header this expression built.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Pair = struct {
        \\    own: std.array_list.Managed(u32),
        \\    count: usize = 0,
        \\};
        \\fn growOwn(value: u32) void {
        \\    var copy: Pair = .{ .own = std.array_list.Managed(u32).init(std.heap.page_allocator) };
        \\    defer copy.own.deinit();
        \\    copy.own.append(value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growOwn(item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 0), countByRule(problems, "slice-loop-reentrant-grow"));
}

test "a struct literal that omits a field whose default reads a name is charged" {
    // The mirror of the case above.  `spare`'s default happens to be
    // an empty list, but the resolver reads the DECLARATION and
    // declines to read anything out of it: a default that names
    // something is not proved to be this expression's own, so the
    // grow it did prove is still charged.  Trusting the spelling
    // here is exactly what a struct field default must never get.
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(gpa, std.testing.io, &tmp,
        \\const std = @import("std");
        \\const Pair = struct {
        \\    own: std.array_list.Managed(u32),
        \\    spare: std.ArrayList(u32) = std.ArrayList(u32).empty,
        \\};
        \\fn growOwn(value: u32) void {
        \\    var copy: Pair = .{ .own = std.array_list.Managed(u32).init(std.heap.page_allocator) };
        \\    defer copy.own.deinit();
        \\    copy.own.append(value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growOwn(item);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, problems);
    try std.testing.expectEqual(@as(usize, 1), countByRule(problems, "slice-loop-reentrant-grow"));
}
