//! Test helpers for rule tests.
//!
//! Rule tests import this from their directory:
//!
//!     const testing = @import("../../testing.zig");
//!
//!     test "..." {
//!         try testing.expectFires(check, "rule-id", src);
//!     }
//!
//! Replaces the ~30-line `runOn(src) + freeProblems(p)` boilerplate
//! that every rule file used to copy at the bottom.

const std = @import("std");
const Ast = std.zig.Ast;

const config_mod = @import("config.zig");
const problem = @import("problem.zig");
const file_cache = @import("cache/file_cache.zig");
const type_engine = @import("type_engine");

const Problem = problem.Problem;
const FileCache = file_cache.FileCache;

/// Signature every rule's `check` fn satisfies.  `cache` provides
/// amortized per-file state (FileModel, per-fn LocalBindings); rules
/// that don't need it can ignore the parameter.
pub const CheckFn = *const fn (
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) anyerror!void;

/// Duplicate `src` with the sentinel `Ast.parse` needs, refusing input
/// the engine cannot address.
///
/// `Ast` carries every token start — and `source.len`, as the
/// end-of-file token's start — as a `u32`, so a source of exactly
/// `maxInt(u32)` bytes would still fit its own table.  The column of
/// that last byte is one past it and does not, so the addressable
/// domain is strictly shorter than `maxInt(u32)`.  Wider input is
/// refused before the copy, not merely before the parse.
fn dupeSource(gpa: std.mem.Allocator, src: []const u8) (error{ OutOfMemory, SourceTooWide })![:0]u8 {
    if (src.len >= std.math.maxInt(u32)) return error.SourceTooWide;
    return gpa.dupeSentinel(u8, src, 0);
}

/// Run `check_fn` against an already-parsed tree and hand the findings
/// to the caller, who owns the list — pass it to `freeProblems`.  The
/// entry points below differ only in how the tree is produced, so the
/// refusal of an unparsable tree, the cache, and the ownership handoff
/// are written once.  `zls` is the resolver that produced `tree`, or
/// null when the tree was parsed directly and carries no type identity.
fn runParsed(
    gpa: std.mem.Allocator,
    check_fn: CheckFn,
    tree: *const Ast,
    zls: ?*type_engine.TypeResolver,
    config: *const config_mod.Config,
) !std.ArrayListUnmanaged(Problem) {
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = FileCache.init(gpa, tree);
    cache.setZls(zls);
    defer cache.deinit();
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    errdefer freeProblems(gpa, &problems);
    try check_fn(gpa, tree, &cache, config, &problems);
    return problems;
}

/// Parse `src` and run `check_fn` against the default config.
/// Caller owns the returned list — pass to `freeProblems` to
/// release.  Returns an empty list if the rule fires no problems.
pub fn runRule(
    gpa: std.mem.Allocator,
    check_fn: CheckFn,
    src: []const u8,
) !std.ArrayListUnmanaged(Problem) {
    return runRuleWithConfig(gpa, check_fn, src, &config_mod.Default);
}

/// Run `check_fn` against `src` with a custom config.  Used by
/// the handful of rules that need to test non-default settings.
pub fn runRuleWithConfig(
    gpa: std.mem.Allocator,
    check_fn: CheckFn,
    src: []const u8,
    config: *const config_mod.Config,
) !std.ArrayListUnmanaged(Problem) {
    const src_z = try dupeSource(gpa, src);
    defer gpa.free(src_z);
    var tree = try Ast.parse(gpa, src_z, .zig);
    defer tree.deinit(gpa);
    return runParsed(gpa, check_fn, &tree, null, config);
}

/// Exercise rules whose contract depends on declaration and type identity.
/// Owns a default context with no project target or builtin configuration;
/// discovering the SDK does not prove the target of the fixture.
pub fn runRuleTyped(
    gpa: std.mem.Allocator,
    check_fn: CheckFn,
    src: []const u8,
) !std.ArrayListUnmanaged(Problem) {
    var context: type_engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    return runRuleTypedWithContext(gpa, check_fn, src, &context);
}

/// Run a typed fixture with a caller-configured context and the default rule
/// config. Borrows `context` in place; the caller owns its configuration and
/// teardown. The context retains the synthetic document at the native absolute
/// path `zbc-typed-rule.zig` under the working directory, without writing it.
/// Reusing that identity with different source returns SourceSnapshotChanged.
/// The returned problems own their text independently of the context; release
/// them with `freeProblems(gpa, ...)`. All allocation and query errors propagate.
pub fn runRuleTypedWithContext(
    gpa: std.mem.Allocator,
    check_fn: CheckFn,
    src: []const u8,
    context: *type_engine.TypeContext,
) !std.ArrayListUnmanaged(Problem) {
    const source = try dupeSource(gpa, src);
    defer gpa.free(source);
    // Give the virtual document a native absolute identity. No file is written.
    var document_path: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const directory_len = try std.Io.Dir.cwd().realPathFile(std.testing.io, ".", &document_path);
    const separator = if (std.mem.endsWith(u8, document_path[0..directory_len], std.fs.path.sep_str)) "" else std.fs.path.sep_str;
    const document_name = try std.fmt.bufPrint(document_path[directory_len..], "{s}zbc-typed-rule.zig", .{separator});
    var resolver: type_engine.TypeResolver = undefined;
    try resolver.init(context, gpa, document_path[0 .. directory_len + document_name.len], source);
    defer resolver.deinit();
    return runParsed(gpa, check_fn, &resolver.handle.document.tree, &resolver, &config_mod.Default);
}

/// Free a list of Problems and the list itself.  Each problem owns
/// its `message`, `notes[].label`, and `notes` slice — they get
/// released by `Problem.deinit`.
pub fn freeProblems(gpa: std.mem.Allocator, list: *std.ArrayListUnmanaged(Problem)) void {
    for (list.items) |*p| p.deinit(gpa);
    list.deinit(gpa);
}

// ── High-level test assertions ─────────────────────────────
//
// These collapse the parse/run/defer/assert ceremony into a
// single call per test.  A passing test is one line:
//
//     test "foo doesn't fire on correct usage" {
//         try expectNoFire(check, "fn f() void {}");
//     }
//
//     test "foo fires on the bug" {
//         try expectFires(check, "rule-id",
//             \\const std = @import("std");
//             \\...
//         );
//     }
//
// Every helper below uses `std.testing.allocator` (leak-detecting)
// and `std.testing.failingAllocator` is NOT used — tests assume
// allocation succeeds.  The `Typed` pair runs the rule against the
// synthetic document whose native absolute identity survives the
// type resolver; the untyped trio hands the rule a directly parsed
// source.  The runners differ; the assertion they reach does not.

/// List what the rule actually reported, so a failed assertion names
/// the findings it saw instead of only their count.
fn dumpProblems(list: []const Problem) void {
    for (list, 0..) |p, i| {
        std.debug.print("  [{d}] {s}: {s}\n", .{ i, p.rule_id, p.message });
    }
}

/// What one helper demands of a finished run, and how it names itself
/// in a failure: `expectFires(missing-deinit)` when the caller named a
/// rule, bare `expectNoFire` when it only demanded silence.
const Expectation = struct {
    caller: []const u8,
    /// Exact number of findings required.
    count: usize,
    /// The rule every finding must carry; null where no finding may be
    /// reported, because then there is nothing to compare it against.
    rule_id: ?[]const u8,

    pub fn format(self: Expectation, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        if (self.rule_id) |rule_id| {
            try writer.print("{s}({s})", .{ self.caller, rule_id });
        } else {
            try writer.writeAll(self.caller);
        }
    }
};

/// The single owner of every assertion below: the cardinality check, the
/// rule-id check, and the diagnostic a failure prints.  Each helper runs
/// its own entry point, frees what it owns, and hands the findings here.
fn assertProblems(want: Expectation, problems: []const Problem) !void {
    if (problems.len != want.count) {
        std.debug.print("{f}: wanted {d} problem{s}, got {d}\n", .{
            want,
            want.count,
            if (want.count == 1) "" else "s",
            problems.len,
        });
        dumpProblems(problems);
        return error.TestUnexpectedProblemCount;
    }
    const rule_id = want.rule_id orelse return;
    for (problems) |p| try std.testing.expectEqualStrings(rule_id, p.rule_id);
}

/// Assert the rule reports EXACTLY one problem with `rule_id`.
/// Most common assertion: a fixture that demonstrates a bug.
pub fn expectFires(check_fn: CheckFn, rule_id: []const u8, src: []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try runRule(gpa, check_fn, src);
    defer freeProblems(gpa, &problems);
    try assertProblems(.{ .caller = "expectFires", .count = 1, .rule_id = rule_id }, problems.items);
}

/// `expectFires` for rules whose contract depends on declaration and
/// type identity, run against the synthetic document.
pub fn expectFiresTyped(check_fn: CheckFn, rule_id: []const u8, src: []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try runRuleTyped(gpa, check_fn, src);
    defer freeProblems(gpa, &problems);
    try assertProblems(.{ .caller = "expectFiresTyped", .count = 1, .rule_id = rule_id }, problems.items);
}

/// Assert the rule reports zero problems on `src`.
pub fn expectNoFire(check_fn: CheckFn, src: []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try runRule(gpa, check_fn, src);
    defer freeProblems(gpa, &problems);
    try assertProblems(.{ .caller = "expectNoFire", .count = 0, .rule_id = null }, problems.items);
}

/// `expectNoFire` for rules whose contract depends on declaration and
/// type identity, run against the synthetic document.
pub fn expectNoFireTyped(check_fn: CheckFn, src: []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try runRuleTyped(gpa, check_fn, src);
    defer freeProblems(gpa, &problems);
    try assertProblems(.{ .caller = "expectNoFireTyped", .count = 0, .rule_id = null }, problems.items);
}

/// Assert the rule reports exactly `n` problems (all with `rule_id`).
/// Used by the handful of fixtures that exercise multiple sites.
pub fn expectCount(check_fn: CheckFn, rule_id: []const u8, n: usize, src: []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try runRule(gpa, check_fn, src);
    defer freeProblems(gpa, &problems);
    try assertProblems(.{ .caller = "expectCount", .count = n, .rule_id = rule_id }, problems.items);
}

// ── Tests ──────────────────────────────────────────────────

test "invalid rule fixtures cannot pass silently" {
    // A real detector rather than a stand-in: this is the refusal every
    // rule fixture depends on, and it must hold on both entry points.
    const truncate_rule = @import("rules/misc/truncate_len_to_narrow_int.zig");
    const malformed = "pub fn broken( {";
    try std.testing.expectError(error.InvalidSyntax, runRule(
        std.testing.allocator,
        truncate_rule.check,
        malformed,
    ));
    try std.testing.expectError(error.InvalidSyntax, runRuleWithConfig(
        std.testing.allocator,
        truncate_rule.check,
        malformed,
        &config_mod.Default,
    ));
}

test "typed context runner propagates source allocation failure" {
    const truncate_rule = @import("rules/misc/truncate_len_to_narrow_int.zig");
    const gpa = std.testing.allocator;
    var context: type_engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var failing = std.testing.FailingAllocator.init(gpa, .{ .fail_index = 0 });
    try std.testing.expectError(error.OutOfMemory, runRuleTypedWithContext(
        failing.allocator(),
        truncate_rule.check,
        "fn run() void {}",
        &context,
    ));
    try std.testing.expect(failing.has_induced_failure);
}

test "typed context runner findings outlive the borrowed context" {
    const iterator_rule = @import("rules/misc/forced_unwrap_iterator_next.zig");
    const gpa = std.testing.allocator;
    var problems = blk: {
        var context: type_engine.TypeContext = undefined;
        try context.init(gpa, std.testing.io);
        defer context.deinit();
        break :blk try runRuleTypedWithContext(
            gpa,
            iterator_rule.check,
            "fn run(it: *Cursor) u8 { return it.next().?; }",
            &context,
        );
    };
    defer freeProblems(gpa, &problems);
    try assertProblems(.{
        .caller = "runRuleTypedWithContext",
        .count = 1,
        .rule_id = "forced-unwrap-iterator-next",
    }, problems.items);
    try std.testing.expect(problems.items[0].message.len != 0);
}

test "typed context runner refuses replacing a retained source snapshot" {
    const iterator_rule = @import("rules/misc/forced_unwrap_iterator_next.zig");
    const gpa = std.testing.allocator;
    var context: type_engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var problems = try runRuleTypedWithContext(
        gpa,
        iterator_rule.check,
        "fn run(it: *Cursor) u8 { return it.next().?; }",
        &context,
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectError(error.SourceSnapshotChanged, runRuleTypedWithContext(
        gpa,
        iterator_rule.check,
        "fn run() void {}",
        &context,
    ));
}
