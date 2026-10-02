//! Test helpers for rule tests.
//!
//! Each rule file is expected to import this directly:
//!
//!     const testing = @import("../analysis/testing.zig");
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

/// Parse `src` and run `check_fn` against the default config.
/// Caller owns the returned list — pass to `freeProblems` to
/// release.  Returns an empty list if the rule fires no problems.
pub fn runRule(
    gpa: std.mem.Allocator,
    check_fn: CheckFn,
    src: []const u8,
) !std.ArrayListUnmanaged(Problem) {
    const src_z = try dupeSource(gpa, src);
    defer gpa.free(src_z);
    var tree = try Ast.parse(gpa, src_z, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    errdefer freeProblems(gpa, &problems);
    try check_fn(gpa, &tree, &cache, &config_mod.Default, &problems);
    return problems;
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
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = try FileCache.init(gpa, &tree);
    defer cache.deinit();
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    errdefer freeProblems(gpa, &problems);
    try check_fn(gpa, &tree, &cache, config, &problems);
    return problems;
}

/// Exercise rules whose contract depends on actual declaration and type identity.
pub fn runRuleTyped(
    gpa: std.mem.Allocator,
    check_fn: CheckFn,
    src: []const u8,
) !std.ArrayListUnmanaged(Problem) {
    const engine = @import("type_engine");
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    const source = try dupeSource(gpa, src);
    defer gpa.free(source);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-typed-rule.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = try FileCache.init(gpa, tree);
    cache.zls = &resolver;
    defer cache.deinit();
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    errdefer freeProblems(gpa, &problems);
    try check_fn(gpa, tree, &cache, &config_mod.Default, &problems);
    return problems;
}

pub fn expectNoFireTyped(check_fn: CheckFn, src: []const u8) !void {
    var problems = try runRuleTyped(std.testing.allocator, check_fn, src);
    defer freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

pub fn expectFiresTyped(check_fn: CheckFn, rule_id: []const u8, src: []const u8) !void {
    var problems = try runRuleTyped(std.testing.allocator, check_fn, src);
    defer freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(rule_id, problems.items[0].rule_id);
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
// These collapse the parse/run/defer/expectEqual ceremony into a
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
// All three helpers use `std.testing.allocator` (leak-detecting)
// and `std.testing.failingAllocator` is NOT used — tests assume
// allocation succeeds.

/// Assert the rule reports EXACTLY one problem with `rule_id`.
/// Most common assertion: a fixture that demonstrates a bug.
pub fn expectFires(check_fn: CheckFn, rule_id: []const u8, src: []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try runRule(gpa, check_fn, src);
    defer freeProblems(gpa, &problems);
    if (problems.items.len != 1) {
        std.debug.print("expectFires({s}): wanted 1 problem, got {d}\n", .{ rule_id, problems.items.len });
        for (problems.items, 0..) |p, i| {
            std.debug.print("  [{d}] {s}: {s}\n", .{ i, p.rule_id, p.message });
        }
        return error.TestExpectedExactlyOneProblem;
    }
    try std.testing.expectEqualStrings(rule_id, problems.items[0].rule_id);
}

/// Assert the rule reports zero problems on `src`.
pub fn expectNoFire(check_fn: CheckFn, src: []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try runRule(gpa, check_fn, src);
    defer freeProblems(gpa, &problems);
    if (problems.items.len != 0) {
        std.debug.print("expectNoFire: wanted 0 problems, got {d}\n", .{problems.items.len});
        for (problems.items, 0..) |p, i| {
            std.debug.print("  [{d}] {s}: {s}\n", .{ i, p.rule_id, p.message });
        }
        return error.TestExpectedNoProblems;
    }
}

/// Assert the rule reports exactly `n` problems (all with `rule_id`).
/// Used by the handful of fixtures that exercise multiple sites.
pub fn expectCount(check_fn: CheckFn, rule_id: []const u8, n: usize, src: []const u8) !void {
    const gpa = std.testing.allocator;
    var problems = try runRule(gpa, check_fn, src);
    defer freeProblems(gpa, &problems);
    if (problems.items.len != n) {
        std.debug.print("expectCount({s}): wanted {d}, got {d}\n", .{ rule_id, n, problems.items.len });
        for (problems.items, 0..) |p, i| {
            std.debug.print("  [{d}] {s}: {s}\n", .{ i, p.rule_id, p.message });
        }
        return error.TestExpectedNProblems;
    }
    for (problems.items) |p| try std.testing.expectEqualStrings(rule_id, p.rule_id);
}

// ── Tests ──────────────────────────────────────────────────

const test_rule_fires = struct {
    fn check(
        gpa: std.mem.Allocator,
        tree: *const Ast,
        _: *FileCache,
        _: *const config_mod.Config,
        problems: *std.ArrayListUnmanaged(Problem),
    ) !void {
        _ = tree;
        try problems.append(gpa, .{
            .rule_id = "test-rule",
            .severity = .@"error",
            .start = .{ .line = 1, .column = 1, .byte = 0 },
            .end = .{ .line = 1, .column = 1, .byte = 0 },
            .message = try gpa.dupe(u8, "hello"),
        });
    }
}.check;

const test_rule_silent = struct {
    fn check(
        _: std.mem.Allocator,
        _: *const Ast,
        _: *FileCache,
        _: *const config_mod.Config,
        _: *std.ArrayListUnmanaged(Problem),
    ) !void {}
}.check;

test "expectFires passes when rule reports 1" {
    try expectFires(test_rule_fires, "test-rule", "fn f() void {}");
}

test "expectNoFire passes when rule reports 0" {
    try expectNoFire(test_rule_silent, "fn f() void {}");
}

test "invalid rule fixtures cannot pass silently" {
    try std.testing.expectError(error.InvalidSyntax, runRule(
        std.testing.allocator,
        test_rule_silent,
        "pub fn broken( {",
    ));
}
