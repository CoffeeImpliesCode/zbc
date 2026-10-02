//! Fuzz harness for the full AST + CFG + pattern-rule pipeline.
//!
//! Three entry points, all backed by the same `analyzeBytes` core:
//!
//!   1. `test "fuzz smoke"` — runs each seed once under `zig build test`.
//!      No server, no instrumentation, just crash-free confirmation.
//!
//!   2. `pub fn main()` — reads stdin and analyses it.  Used with AFL++:
//!        afl-fuzz -i corpus/ -o findings/ -- ./fuzz-zbc
//!      Build:  zig build fuzz
//!
//!   3. `LLVMFuzzerTestOneInput` export — libfuzzer entry point.
//!      Build:  zig build fuzz-libfuzzer   (links -fsanitize=fuzzer)
//!      Run:    ./fuzz-zbc-libfuzzer corpus/
//!
//! The harness omits the ZLS type engine (needs a file path + project
//! context) and falls through to AST-only analysis — the dominant path.

const std = @import("std");
const Ast = std.zig.Ast;

const cfg_builder = @import("flow/cfg_builder.zig");
const worklist = @import("flow/worklist.zig");
const rule_catalog = @import("rule_catalog.zig");
const config_mod = @import("config.zig");
const file_cache_mod = @import("cache/file_cache.zig");
const problem_mod = @import("problem.zig");

// ── Seeds ─────────────────────────────────────────────────────────────
// Representative Zig snippets covering the major rule classes.
// Used as the smoke-test corpus and as AFL++ / libfuzzer seed inputs.
pub const seeds: []const []const u8 = &.{
    "fn f() void {}",
    \\fn g(i: usize, buf: []const u8) u8 {
    \\    if (i > 0) return buf[i - 1];
    \\    return 0;
    \\}
    ,
    \\const std = @import("std");
    \\fn leak(a: std.mem.Allocator) ![]u8 {
    \\    var arena = std.heap.ArenaAllocator.init(a);
    \\    defer arena.deinit();
    \\    return try arena.allocator().alloc(u8, 16);
    \\}
    ,
    \\fn run() void {
    \\    var grid = Grid.init();
    \\    defer grid.deinit();
    \\    var log = Log.init(&grid);
    \\    defer log.deinit();
    \\}
    ,
    \\const std = @import("std");
    \\fn make(a: std.mem.Allocator) !Pair {
    \\    return .{
    \\        .a = try a.dupe(u8, "hello"),
    \\        .b = try a.dupe(u8, "world"),
    \\    };
    \\}
    ,
    "fn fmt(ns: i64) u64 { return @as(u64, @intCast(-ns)); }",
    "fn f() u8 { var x: u8 = undefined; return x; }",
    // Pathological inputs
    "",
    "   \n\t  ",
    "this is not zig at all !!!",
    "fn f() void { { { { { { { { { {} } } } } } } } } }",
};

// ── Core ───────────────────────────────────────────────────────────────
/// Run the full analysis pipeline on `raw` bytes.  Returns without
/// reporting findings — caller only cares whether the pipeline crashes.
pub fn analyzeBytes(gpa: std.mem.Allocator, raw: []const u8) !void {
    if (raw.len == 0) return;

    // The pipeline reports positions as a byte offset plus one over a
    // `u32`-addressed source.  `Ast` would tolerate a source of exactly
    // `maxInt(u32)` bytes — its end-of-file token carries `source.len` as
    // a `u32` start — but the column of that last byte would not fit, so
    // refuse anything wider here, ahead of the sentinel copy below.
    if (raw.len >= std.math.maxInt(u32)) return error.SourceTooWide;

    // Ast.parse requires a null-terminated sentinel string.
    const src = try gpa.allocSentinel(u8, raw.len, 0);
    defer gpa.free(src);
    @memcpy(src[0..raw.len], raw);

    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;

    const config = &config_mod.Default;
    var problems: std.ArrayListUnmanaged(problem_mod.Problem) = .empty;
    defer {
        for (problems.items) |*problem| problem.deinit(gpa);
        problems.deinit(gpa);
    }

    var cache = try file_cache_mod.FileCache.init(gpa, &tree);
    defer cache.deinit();

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const cfg = (try cfg_builder.lowerFunctionFull(
            gpa,
            &tree,
            node,
            config,
            &cache,
        )) orelse continue;
        var cfg_mut = cfg;
        defer cfg_mut.deinit(gpa);
        try worklist.check(gpa, &cfg_mut, .{ .path = "<fuzz>", .config = config }, &problems);
    }

    try rule_catalog.runEscape(gpa, &tree, &cache, config, &problems);
}

// ── Entry point 1: smoke test ──────────────────────────────────────────
test "fuzz smoke: seeds do not crash the analysis pipeline" {
    const gpa = std.testing.allocator;
    for (seeds) |seed| {
        var arena = std.heap.ArenaAllocator.init(gpa);
        defer arena.deinit();
        analyzeBytes(arena.allocator(), seed) catch |err| switch (err) {
            error.OutOfMemory, error.InvalidSyntax, error.AnalysisBudgetExceeded => {},
            else => return err,
        };
    }
}

// ── Entry point 2: stdin reader (AFL++ / honggfuzz / manual) ───────────
// Compile with `zig build fuzz`, then:
//   afl-fuzz -i corpus/ -o findings/ -- ./fuzz-zbc
//   honggfuzz --input corpus/ -- ./fuzz-zbc
pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const io = init.io;

    // AFL++ / honggfuzz write their mutated input to stdin.
    var buf: [65536]u8 = undefined;
    var stdin_reader = std.Io.File.stdin().readerStreaming(io, &buf);
    const raw = stdin_reader.interface.allocRemaining(gpa, .limited(4 * 1024 * 1024)) catch |err| switch (err) {
        error.OutOfMemory, error.StreamTooLong => return,
        else => return err,
    };
    defer gpa.free(raw);

    analyzeBytes(gpa, raw) catch |err| switch (err) {
        error.OutOfMemory, error.InvalidSyntax, error.AnalysisBudgetExceeded => return,
        else => return err,
    };
}

// ── Entry point 3: libfuzzer (AFL++ with -fsanitize=fuzzer) ────────────
// Compile with `zig build fuzz-libfuzzer`, then:
//   ./fuzz-zbc-libfuzzer corpus/
//   # or with AFL++LLVM mode: afl-fuzz -i corpus -o out -- ./fuzz-zbc-libfuzzer @@
export fn LLVMFuzzerTestOneInput(data: [*]const u8, size: usize) callconv(.c) i32 {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    analyzeBytes(arena.allocator(), data[0..size]) catch {};
    return 0;
}
