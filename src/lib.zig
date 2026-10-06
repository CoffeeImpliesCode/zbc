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
            .gpa = gpa, .io = io,
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
        const cwd = if (std.fs.path.isAbsolute(path)) "" else
            cwd_buffer[0..try std.Io.Dir.cwd().realPathFile(self.io, ".", &cwd_buffer)];
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
    var rule_cache = file_cache_mod.FileCache.init(gpa, tree);
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
        try worklist.check(gpa, &cfg, .{ .path = path, .config = config }, &problems);
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
        std.testing.allocator, std.testing.io, &tmp, "pub fn broken( {",
    ));
}

test "stable array repetition is analyzed without rewriting source" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const problems = try analyzeSrc(
        std.testing.allocator, std.testing.io, &tmp, "pub const values = [_]u8{0} ** 4;",
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
