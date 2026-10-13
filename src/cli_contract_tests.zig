//! CLI subprocess contract tests.
//!
//! Each test spawns the executable this build emitted — the path arrives
//! through the `cli_contract_options` module — and asserts on its actual
//! stdout, stderr and exit status. Nothing is mocked and nothing is
//! reconstructed from source text.
//!
//! Fixtures are written into `std.testing.tmpDir` trees and every
//! invocation runs with its working directory set to that tree, so
//! relative operands resolve inside the fixture.
//!
//! The contract under test: JSON and SARIF go to stdout, operational
//! messages and the coverage summary go to stderr, exit is 0 for a clean
//! run, 1 for findings, and 2 when the run could not finish everything it
//! was handed — 2 outranking 1.

const std = @import("std");
const builtin = @import("builtin");

const cli_contract_options = @import("cli_contract_options");

/// The engine the CLI itself resolves types through.
/// `ParseFailure.fromTree` is the one function that turns a tree error
/// into the coordinates the CLI prints, so deriving an expectation
/// through it derives it from the shipped parser rather than from a
/// number typed here.
const type_engine = @import("type_engine");

const io = std.testing.io;
const gpa = std.testing.allocator;

// ── Fixtures ─────────────────────────────────────────────────

/// Returns a pointer to a function-local stack variable.
const stack_escape_one_line =
    \\pub fn bad() *u8 { var x: u8 = 1; return &x; }
    \\
;

/// The same shape across several lines so a span can be pinned exactly:
/// `return &x;` is line 3.
const stack_escape_multiline =
    \\pub fn bad() *u8 {
    \\    var x: u8 = 1;
    \\    return &x;
    \\}
    \\
;

const clean_value = "pub const value = 1;\n";

/// Array repetition the declared 0.16.0 parser accepts. A clean report
/// for it shows the shipped parser holds the line as written.
const clean_repeat = "pub const values = [_]u8{0} ** 4;\n";

/// A consumer of both shipped arena pattern defaults: the arena is minted
/// by `std.heap.ArenaAllocator.init`, which the default `--arena-init`
/// names, and killed by `defer … .deinit(`, which the default
/// `--arena-kill` names. The returned slice is a real allocation taken
/// from that arena, not a wrapper struct standing in for one.
/// The escape is on line 6.
const arena_escape_src =
    \\const std = @import("std");
    \\pub fn foo() []const u8 {
    \\    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    \\    defer arena.deinit();
    \\    const out = arena.allocator().dupe(u8, "arena") catch unreachable;
    \\    return out;
    \\}
    \\
;

/// A consumer of the shipped arena-kill default on its own: the arena is
/// killed explicitly and a byte of a genuine allocation from it is then
/// dereferenced. The use is a real read of the arena's memory, not a
/// borrow handed to a helper, and the returned value is a scalar so no
/// borrow escapes through the return. The read is line 6.
const arena_use_after_kill_src =
    \\const std = @import("std");
    \\pub fn foo() u8 {
    \\    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    \\    const buf = arena.allocator().dupe(u8, "arena") catch unreachable;
    \\    arena.deinit();
    \\    return buf[0];
    \\}
    \\
;

const malformed_root = "pub fn broken( {\n";

/// A root that parses and names a type from a broken import, so the
/// failure belongs to a document the operator never named.
const imports_broken_dep =
    \\const dep = @import("dep.zig");
    \\pub fn copy(value: dep.Box) f32 { return @floatFromInt(value.value); }
    \\
;
const malformed_dep =
    \\// dependency
    \\pub const Box = struct { value: ; };
    \\
;

/// The multiline shape pushed down by two lines, so several files in one
/// run carry a finding at a genuinely different line. The escape is on
/// line 5.
const stack_escape_line5 =
    \\// a leading comment
    \\
    \\pub fn bad() *u8 {
    \\    var x: u8 = 1;
    \\    return &x;
    \\}
    \\
;

/// One function whose flow check exhausts the per-block path-state limit
/// (ten independent conditions leave 2^10 states at the join, the limit is
/// 64), next to a function with a real finding. `many` also double-frees
/// early; the exhausted function must report nothing, not even that.
/// `many` starts on line 2; the stack escape in `bad` is on line 27.
const exhausted_function_src =
    \\const std = @import("std");
    \\fn many(a: std.mem.Allocator, f0: bool, f1: bool, f2: bool, f3: bool, f4: bool, f5: bool, f6: bool, f7: bool, f8: bool, f9: bool) void {
    \\    const q = a.alloc(u8, 1) catch return;
    \\    a.free(q);
    \\    a.free(q);
    \\    const p0 = a.alloc(u8, 1) catch return;
    \\    const p1 = a.alloc(u8, 1) catch return;
    \\    const p2 = a.alloc(u8, 1) catch return;
    \\    const p3 = a.alloc(u8, 1) catch return;
    \\    const p4 = a.alloc(u8, 1) catch return;
    \\    const p5 = a.alloc(u8, 1) catch return;
    \\    const p6 = a.alloc(u8, 1) catch return;
    \\    const p7 = a.alloc(u8, 1) catch return;
    \\    const p8 = a.alloc(u8, 1) catch return;
    \\    const p9 = a.alloc(u8, 1) catch return;
    \\    if (f0) a.free(p0);
    \\    if (f1) a.free(p1);
    \\    if (f2) a.free(p2);
    \\    if (f3) a.free(p3);
    \\    if (f4) a.free(p4);
    \\    if (f5) a.free(p5);
    \\    if (f6) a.free(p6);
    \\    if (f7) a.free(p7);
    \\    if (f8) a.free(p8);
    \\    if (f9) a.free(p9);
    \\}
    \\pub fn bad() *u8 { var x: u8 = 1; return &x; }
    \\
;

/// A filename carrying both a space and a percent sign. `std.Uri`'s path
/// component escapes neither, so the SARIF URI for this file has to come
/// back percent-encoded.
const encoded_finding_file = "bad space%pct.zig";

// ── Subprocess plumbing ──────────────────────────────────────

const Run = struct {
    code: u8,
    stdout: []u8,
    stderr: []u8,

    fn deinit(self: *Run) void {
        gpa.free(self.stdout);
        gpa.free(self.stderr);
    }
};

/// Runs the emitted CLI in `cwd` over `args`.
///
/// A child that ended on a signal never produced the contract these tests
/// assert, so that is an error here rather than a fabricated exit code.
fn zbc(cwd: []const u8, args: []const []const u8) !Run {
    // Build-cache artifact paths can be relative to the test process.
    // Resolve before the child switches to the fixture's working directory.
    const exe_path = try std.Io.Dir.cwd().realPathFileAlloc(io, cli_contract_options.zbc_exe, gpa);
    defer gpa.free(exe_path);

    // Test argv storage. Sized for the widest invocation in this file.
    var argv: [16][]const u8 = undefined;
    std.debug.assert(args.len < argv.len);
    argv[0] = exe_path;
    @memcpy(argv[1..][0..args.len], args);

    const result = try std.process.run(gpa, io, .{
        .argv = argv[0 .. args.len + 1],
        .cwd = .{ .path = cwd },
    });
    switch (result.term) {
        .exited => |code| return .{
            .code = code,
            .stdout = result.stdout,
            .stderr = result.stderr,
        },
        else => |term| {
            gpa.free(result.stdout);
            gpa.free(result.stderr);
            std.debug.print("zbc subprocess ended by {any}\n", .{term});
            return error.ZbcSubprocessDidNotExit;
        },
    }
}

/// A throwaway tree plus its absolute canonical path, which is what the
/// CLI reports — so tests compare against it, not against the spelling
/// they typed.
const Fixture = struct {
    tmp: std.testing.TmpDir,
    dir: [:0]u8,

    fn init() !Fixture {
        var tmp = std.testing.tmpDir(.{});
        errdefer tmp.cleanup();
        return .{ .tmp = tmp, .dir = try tmp.dir.realPathFileAlloc(io, ".", gpa) };
    }

    fn deinit(self: *Fixture) void {
        gpa.free(self.dir);
        self.tmp.cleanup();
    }

    fn write(self: *Fixture, sub_path: []const u8, data: []const u8) !void {
        if (std.fs.path.dirname(sub_path)) |parent| {
            if (!std.mem.eql(u8, parent, ".")) try self.tmp.dir.createDirPath(io, parent);
        }
        try self.tmp.dir.writeFile(io, .{ .sub_path = sub_path, .data = data });
    }

    fn pathOf(self: *Fixture, sub_path: []const u8) ![]u8 {
        return std.fs.path.join(gpa, &.{ self.dir, sub_path });
    }
};

// ── Stream helpers ───────────────────────────────────────────

/// The line of `text` holding `needle`. Attribution claims are line
/// claims, so they are asserted against whole lines.
fn lineContaining(text: []const u8, needle: []const u8) ![]const u8 {
    const at = std.mem.indexOf(u8, text, needle) orelse {
        std.debug.print("no line holds `{s}`; stderr was:\n{s}", .{ needle, text });
        return error.DiagnosticMissing;
    };
    const start = if (std.mem.lastIndexOfScalar(u8, text[0..at], '\n')) |nl| nl + 1 else 0;
    const rest = text[start..];
    const end = if (std.mem.indexOfScalar(u8, rest, '\n')) |nl| nl else rest.len;
    return rest[0..end];
}

/// The `<line>:<column>` a diagnostic points at, read from just past the
/// path it names. A diagnostic that names a file without locating a
/// position inside it has located nothing, so both numbers must parse as
/// real 1-based coordinates. Whether they are the RIGHT ones is
/// `expectParseError`'s claim, not this one's.
fn diagnosticCoordinates(diagnostic: []const u8, path_len: usize) !struct { line: u32, column: u32 } {
    if (diagnostic.len <= path_len or diagnostic[path_len] != ':') return error.NoCoordinate;
    var it = std.mem.splitScalar(u8, diagnostic[path_len..], ':');
    _ = it.next(); // the separator that follows the path
    const line = std.fmt.parseInt(u32, it.next() orelse return error.NoCoordinate, 10) catch
        return error.NoCoordinate;
    const column = std.fmt.parseInt(u32, it.next() orelse return error.NoCoordinate, 10) catch
        return error.NoCoordinate;
    if (line == 0 or column == 0) return error.NoCoordinate;
    return .{ .line = line, .column = column };
}

/// Where the shipped parser puts a failure in `source`, and what it calls
/// that failure.
///
/// Derived, never typed in: the fixture is parsed here with the same
/// `std` the emitted CLI was built against, and the answer is read
/// through the same `ParseFailure.fromTree` the CLI reads it through. A
/// fixture that parses clean has no failure to locate and cannot check
/// one, so that is an error here rather than a comparison against a
/// placeholder.
const ParserSite = struct {
    line: u32,
    column: u32,
    reason: []const u8,
};

fn parserSite(source: []const u8) !ParserSite {
    const terminated = try gpa.dupeZ(u8, source);
    defer gpa.free(terminated);
    var tree = try std.zig.Ast.parse(gpa, terminated, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len == 0) {
        std.debug.print("fixture parses clean, so it has no failure to locate:\n{s}", .{source});
        return error.NoParserFailure;
    }
    const failure = type_engine.ParseFailure.fromTree(null, &tree);
    return .{
        .line = failure.position.line,
        .column = failure.position.column,
        .reason = failure.reason,
    };
}

/// The whole parse-failure claim about one document: the diagnostic
/// names `identity` and nothing else, points at exactly the coordinates
/// the shipped parser gives `source`, and carries that parser error's own
/// name.
///
/// A diagnostic that stopped one byte short of the failure, or that
/// named a cause of its own choosing, is a different claim from the one
/// the CLI makes, so the coordinate is compared to the parser's answer
/// and not merely required to be a position. Both numbers are 1-based,
/// which is what `tokenLocation` already reports.
fn expectParseError(diagnostic: []const u8, identity: []const u8, source: []const u8) !void {
    const expected = try parserSite(source);
    try std.testing.expect(std.mem.startsWith(u8, diagnostic, identity));

    const at = try diagnosticCoordinates(diagnostic, identity.len);
    try std.testing.expectEqual(expected.line, at.line);
    try std.testing.expectEqual(expected.column, at.column);

    // The cause is the tag the parser gave this tree error, carried with
    // the compiler that answered it. Phrasing is not pinned; the parser's
    // identity for this failure is.
    try expectContains(diagnostic, expected.reason);
    try expectContains(diagnostic, builtin.zig_version_string);
}

fn lineCount(text: []const u8) usize {
    if (text.len == 0) return 0;
    var n: usize = 1;
    for (text) |c| {
        if (c == '\n') n += 1;
    }
    // A trailing newline ends the last line; it does not open another.
    return if (text[text.len - 1] == '\n') n - 1 else n;
}

fn expectContains(text: []const u8, needle: []const u8) !void {
    if (std.mem.indexOf(u8, text, needle) == null) {
        std.debug.print("`{s}` absent from:\n{s}", .{ needle, text });
        return error.ExpectedTextMissing;
    }
}

fn expectAbsent(text: []const u8, needle: []const u8) !void {
    if (std.mem.indexOf(u8, text, needle) != null) {
        std.debug.print("`{s}` unexpectedly present in:\n{s}", .{ needle, text });
        return error.UnexpectedTextPresent;
    }
}

/// Asserts the coverage summary reports exactly these counts, together
/// with the parser version the run used. The counts are written out
/// separately because none stands in for another: a refused input is
/// selected and never analyzed, a file whose analysis failed is counted
/// as selected but never as analyzed either, and a partial file (some
/// part gave up on a budget, the rest reported) is neither analyzed nor
/// failed.
fn expectSummary(run: *const Run, selected: usize, analyzed: usize, partial: usize, failed: usize, findings: usize) !void {
    const needle = try std.fmt.allocPrint(
        gpa,
        "zbc: selected={d} analyzed={d} partial={d} failed={d} findings={d} parser=Zig-{s} unresolved-import-lookups=",
        .{ selected, analyzed, partial, failed, findings, builtin.zig_version_string },
    );
    defer gpa.free(needle);
    if (std.mem.indexOf(u8, run.stderr, needle) == null) {
        std.debug.print("summary `{s}` absent; stderr was:\n{s}", .{ needle, run.stderr });
        return error.SummaryMismatch;
    }
}

/// A rejected flag answers with exactly one line and returns before
/// source selection, so nothing was selected and there is nothing to
/// account for. `identifies` picks the line out of stderr. Every token
/// in `required` must appear in it — the flag, the value it was given,
/// and what the flag wanted — and at least one token in `one_of` must,
/// which is how a diagnostic that offers a choice is checked without
/// pinning one phrasing of it.
fn expectSingleFlagDiagnostic(
    run: *const Run,
    identifies: []const u8,
    required: []const []const u8,
    one_of: []const []const u8,
) !void {
    try std.testing.expectEqual(@as(u8, 2), run.code);
    try std.testing.expectEqualStrings("", run.stdout);
    try std.testing.expectEqual(@as(usize, 1), lineCount(run.stderr));
    const line = try lineContaining(run.stderr, identifies);
    for (required) |token| try expectContains(line, token);
    if (one_of.len != 0) {
        var offered = false;
        for (one_of) |token| {
            if (std.mem.indexOf(u8, line, token) != null) offered = true;
        }
        if (!offered) {
            std.debug.print("no alternative present in: {s}", .{line});
            return error.ExpectedTextMissing;
        }
    }
    try expectAbsent(run.stderr, "selected=");
}

// ── Report shapes ────────────────────────────────────────────
//
// Mirrors what the JSON and SARIF writers actually emit. Unknown fields
// are ignored so a format that gains one does not break these reads.

const JsonPos = struct { line: u32, column: u32, byte: u32 };

const JsonProblem = struct {
    path: []const u8,
    rule_id: []const u8,
    severity: []const u8,
    start: JsonPos,
    end: JsonPos,
    message: []const u8,
};

const sarif_json = struct {
    const Region = struct {
        startLine: u32,
        startColumn: u32,
        endLine: u32,
        endColumn: u32,
        byteOffset: u32,
        byteLength: u32,
    };
    const PhysicalLocation = struct {
        artifactLocation: struct { uri: []const u8 },
        region: Region,
    };
    const Result = struct {
        ruleId: []const u8,
        level: []const u8,
        kind: []const u8,
        message: struct { text: []const u8 },
        locations: []const struct { physicalLocation: PhysicalLocation },
    };
    const Log = struct {
        version: []const u8,
        runs: []const struct {
            tool: struct {
                driver: struct {
                    name: []const u8,
                    rules: []const struct { id: []const u8, name: []const u8 },
                },
            },
            invocations: []const struct { executionSuccessful: bool },
            results: []const Result,
        },
    };
};

fn parseProblems(stdout: []const u8) !std.json.Parsed([]JsonProblem) {
    return std.json.parseFromSlice([]JsonProblem, gpa, stdout, .{
        .ignore_unknown_fields = true,
    });
}

fn parseSarif(stdout: []const u8) !std.json.Parsed(sarif_json.Log) {
    return std.json.parseFromSlice(sarif_json.Log, gpa, stdout, .{
        .ignore_unknown_fields = true,
    });
}

/// stdout is a bare JSON array even when nothing was found, so a
/// consumer never has to tell an empty report from an error envelope.
/// Parsing into an array type IS the schema check — an object or scalar
/// would not parse, and the length carries the emptiness. Whitespace
/// around the document is not the contract, so it is not pinned.
fn expectEmptyBareArray(run: *const Run) !void {
    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();
    try std.testing.expectEqual(@as(usize, 0), parsed.value.len);
}

/// `--enable` narrows the enabled set to one rule, so a fixture's finding
/// count is a claim about that rule rather than an at-least-one.
const only_stack_escape = "--enable=stack_escape";
const only_arena_escape = "--enable=arena_escape";
const only_arena_use_after_kill = "--enable=arena_use_after_kill";

// ── Clean inputs ─────────────────────────────────────────────

test "cli json: a clean source exits 0 and reports an empty bare array" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("clean.zig", clean_value);

    var run = try zbc(fx.dir, &.{ "--format=json", "clean.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 0), run.code);
    try expectEmptyBareArray(&run);
    try expectSummary(&run, 1, 1, 0, 0, 0);
}

test "cli json: the version-compatibility consumer analyses clean on the compiled parser" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("repeat.zig", clean_repeat);

    var run = try zbc(fx.dir, &.{ "--format=json", "repeat.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 0), run.code);
    try expectEmptyBareArray(&run);
    try expectSummary(&run, 1, 1, 0, 0, 0);
}

// ── Findings ─────────────────────────────────────────────────

test "cli json: a finding exits 1 and reports rule, severity, span and canonical path" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("escape.zig", stack_escape_one_line);
    const abs = try fx.pathOf("escape.zig");
    defer gpa.free(abs);

    var run = try zbc(fx.dir, &.{ "--format=json", only_stack_escape, "escape.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 1), run.code);

    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 1), parsed.value.len);
    const finding = parsed.value[0];
    try std.testing.expectEqualStrings("stack-escape", finding.rule_id);
    try std.testing.expectEqualStrings("error", finding.severity);
    try std.testing.expect(finding.message.len > 0);
    // A span into the source that was read, not a defaulted position.
    try std.testing.expectEqual(@as(u32, 1), finding.start.line);
    try std.testing.expect(finding.start.column > 0);
    try std.testing.expect(finding.end.byte > finding.start.byte);
    // The canonical path of the file the CLI opened.
    try std.testing.expectEqualStrings(abs, finding.path);

    try expectSummary(&run, 1, 1, 0, 0, 1);
}

test "cli json: the default arena patterns let a real arena allocation escape" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("arena.zig", arena_escape_src);
    const abs = try fx.pathOf("arena.zig");
    defer gpa.free(abs);

    // No --arena-init and no --arena-kill: this run is the shipped
    // default pair, so a consumer of those defaults is what the test
    // actually exercises.
    var run = try zbc(fx.dir, &.{ "--format=json", only_arena_escape, "arena.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 1), run.code);

    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 1), parsed.value.len);
    const finding = parsed.value[0];
    try std.testing.expectEqualStrings("arena-escape", finding.rule_id);
    try std.testing.expectEqualStrings("error", finding.severity);
    try std.testing.expectEqualStrings(abs, finding.path);
    try std.testing.expectEqual(@as(u32, 6), finding.start.line);

    try expectSummary(&run, 1, 1, 0, 0, 1);
}

test "cli json: --arena-init that names no arena removes the finding" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("arena.zig", arena_escape_src);

    // Same bytes, same enabled set, one pattern changed. An arena is
    // registered only when a call matches an --arena-init pattern, and
    // the arena-escape report is reachable only from an arena origin —
    // so with no arena registered the rule cannot speak at all.
    var run = try zbc(fx.dir, &.{
        "--format=json",
        only_arena_escape,
        "--arena-init=NoSuchAllocator.init",
        "arena.zig",
    });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 0), run.code);
    try expectEmptyBareArray(&run);
    try expectSummary(&run, 1, 1, 0, 0, 0);
}

test "cli json: reading a real arena allocation after its deinit is reported" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("kill.zig", arena_use_after_kill_src);
    const abs = try fx.pathOf("kill.zig");
    defer gpa.free(abs);

    // No borrow escapes through the return: a single byte is read from
    // the arena's own storage after the arena is killed. Only the
    // post-kill invariant is enabled, so the count is a claim about that
    // rule rather than about the escape rule.
    var run = try zbc(fx.dir, &.{ "--format=json", only_arena_use_after_kill, "kill.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 1), run.code);

    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 1), parsed.value.len);
    const finding = parsed.value[0];
    try std.testing.expectEqualStrings("arena-use-after-kill", finding.rule_id);
    try std.testing.expectEqualStrings("error", finding.severity);
    try std.testing.expect(finding.message.len > 0);
    try std.testing.expectEqualStrings(abs, finding.path);
    try std.testing.expectEqual(@as(u32, 6), finding.start.line);
    try std.testing.expect(finding.start.column > 0);

    try expectSummary(&run, 1, 1, 0, 0, 1);
}

test "cli json: --arena-kill that names no deinit leaves the arena live" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("kill.zig", arena_use_after_kill_src);

    // Same bytes, same enabled set, one kill pattern changed. The arena
    // is marked dead only where a call matches a kill pattern, so a
    // pattern that names no deinit leaves it live and the post-kill
    // rule has nothing to report. That makes the kill default a consumer
    // in its own right, separate from the escape rule.
    var run = try zbc(fx.dir, &.{
        "--format=json",
        only_arena_use_after_kill,
        "--arena-kill=NoSuchAllocator.deinit",
        "kill.zig",
    });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 0), run.code);
    try expectEmptyBareArray(&run);
    try expectSummary(&run, 1, 1, 0, 0, 0);
}

// ── Selection and parse failures ─────────────────────────────

test "cli json: a missing input exits 2 and still reports a bare array" {
    var fx = try Fixture.init();
    defer fx.deinit();

    var run = try zbc(fx.dir, &.{ "--format=json", "missing.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);
    try expectEmptyBareArray(&run);

    // The refusal names the operand as it was written and the reason the
    // run could not select it.
    const refusal = try lineContaining(run.stderr, "cannot select");
    try expectContains(refusal, "missing.zig");
    try expectSummary(&run, 1, 0, 0, 1, 0);
}

/// A toolchain failure belongs to the run, not to a file: it is reported
/// on one line before analysis, names the command and what it said, and
/// is not repeated as a per-file `cannot analyze` line.
fn expectSingleToolchainDiagnostic(run: *const Run, command: []const u8, reason: []const u8) !void {
    try std.testing.expectEqual(@as(u8, 2), run.code);
    const line = try lineContaining(run.stderr, "cannot discover the Zig toolchain");
    try expectContains(line, "ZigToolchainUnavailable");
    try expectContains(line, command);
    try expectContains(line, reason);
    try expectAbsent(run.stderr, "cannot analyze");
    try expectAbsent(run.stderr, ": NotFound");
    try expectContains(run.stderr, "--zig=<path>");
    try expectSummary(run, 1, 0, 0, 1, 0);
}

test "cli json: a missing zig executable is one toolchain error and a bare array" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("clean.zig", "pub fn f() void {}\n");

    var run = try zbc(fx.dir, &.{ "--format=json", "--zig=/nonexistent/zbc-test-zig", "clean.zig", "clean.zig" });
    defer run.deinit();

    try expectEmptyBareArray(&run);
    try expectSingleToolchainDiagnostic(&run, "`/nonexistent/zbc-test-zig env`", "could not be started: FileNotFound");
}

test "cli sarif: a missing zig executable reports an unsuccessful invocation" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("clean.zig", "pub fn f() void {}\n");

    var run = try zbc(fx.dir, &.{ "--format=sarif", "--zig=/nonexistent/zbc-test-zig", "clean.zig" });
    defer run.deinit();

    const log = try parseSarif(run.stdout);
    defer log.deinit();
    try std.testing.expect(!log.value.runs[0].invocations[0].executionSuccessful);
    try std.testing.expectEqual(@as(usize, 0), log.value.runs[0].results.len);
    try expectSingleToolchainDiagnostic(&run, "`/nonexistent/zbc-test-zig env`", "could not be started");
}

test "cli json: a zig that exits nonzero reports its status and first stderr line once" {
    if (builtin.os.tag == .windows) return error.SkipZigTest;
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("clean.zig", "pub fn f() void {}\n");
    try fx.tmp.dir.writeFile(io, .{
        .sub_path = "fake-zig",
        .data = "#!/bin/sh\necho 'error: no build.zig.zon found' >&2\necho 'second line' >&2\nexit 3\n",
        .flags = .{ .permissions = .executable_file },
    });
    const fake = try fx.pathOf("fake-zig");
    defer gpa.free(fake);
    const flag = try std.fmt.allocPrint(gpa, "--zig={s}", .{fake});
    defer gpa.free(flag);

    var run = try zbc(fx.dir, &.{ "--format=json", flag, "clean.zig" });
    defer run.deinit();

    try expectEmptyBareArray(&run);
    try expectSingleToolchainDiagnostic(&run, fake, "exited with status 3: error: no build.zig.zon found");
    try expectAbsent(run.stderr, "second line");
}

test "cli: an empty --zig value answers once and accounts for nothing" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("clean.zig", "pub fn f() void {}\n");

    var run = try zbc(fx.dir, &.{ "--zig=", "clean.zig" });
    defer run.deinit();

    try expectSingleFlagDiagnostic(&run, "--zig", &.{ "--zig", "non-empty" }, &.{});
}

test "cli json: malformed root source is attributed to the root with no imported hint" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("broken.zig", malformed_root);
    const abs = try fx.pathOf("broken.zig");
    defer gpa.free(abs);

    var run = try zbc(fx.dir, &.{ "--format=json", "broken.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);
    try expectEmptyBareArray(&run);

    // The failure is the root's own, so no import is blamed.
    try expectAbsent(run.stderr, "imported source failed");
    const diagnostic = try lineContaining(run.stderr, "parse error:");
    // The exact site the parser reports for these bytes, and the parser's
    // own name for the failure — not a line that merely exists.
    try expectParseError(diagnostic, abs, malformed_root);

    try expectSummary(&run, 1, 0, 0, 1, 0);
}

test "cli json: a malformed import is attributed to the imported path" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("main.zig", imports_broken_dep);
    try fx.write("dep.zig", malformed_dep);
    const root_abs = try fx.pathOf("main.zig");
    defer gpa.free(root_abs);
    const dep_abs = try fx.pathOf("dep.zig");
    defer gpa.free(dep_abs);

    var run = try zbc(fx.dir, &.{ "--format=json", "main.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);
    try expectEmptyBareArray(&run);

    // The root parsed, so the run says the analysis is incomplete and
    // points at the document that actually failed — not at the operand.
    const hint = try lineContaining(run.stderr, "imported source failed");
    try expectContains(hint, root_abs);

    const diagnostic = try lineContaining(run.stderr, "parse error:");
    // The failure is attributed to the imported document, which is
    // named as a file URI because that is the identity the store holds
    // it under. The fixture path is plain, so the URI is the scheme
    // followed by the filesystem path and nothing is escaped.
    const dep_uri = try std.fmt.allocPrint(gpa, "file://{s}", .{dep_abs});
    defer gpa.free(dep_uri);
    try std.testing.expect(!std.mem.startsWith(u8, diagnostic, root_abs));
    // Located where the parser puts the failure in the dependency's own
    // bytes: a diagnostic that pointed into the importer, or one byte off
    // the offending token, names a different site and fails here.
    try expectParseError(diagnostic, dep_uri, malformed_dep);

    try expectSummary(&run, 1, 0, 0, 1, 0);
}

test "cli json: a mixed run reports its findings and counts each input separately" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("clean.zig", clean_value);
    try fx.write("finding.zig", stack_escape_multiline);
    try fx.write("broken.zig", malformed_root);
    const finding_abs = try fx.pathOf("finding.zig");
    defer gpa.free(finding_abs);

    // Four inputs: three the walk yields and one that is not there.
    var run = try zbc(fx.dir, &.{ "--format=json", only_stack_escape, ".", "missing.zig" });
    defer run.deinit();

    // The run could not finish what it was handed, so it is not a 1.
    try std.testing.expectEqual(@as(u8, 2), run.code);

    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();

    // The findings that were established still reach the consumer.
    try std.testing.expectEqual(@as(usize, 1), parsed.value.len);
    try std.testing.expectEqualStrings(finding_abs, parsed.value[0].path);
    try std.testing.expectEqualStrings("stack-escape", parsed.value[0].rule_id);
    try std.testing.expectEqual(@as(u32, 3), parsed.value[0].start.line);

    // Four counts, none standing in for another.
    try expectSummary(&run, 4, 2, 0, 2, 1);

    const refusal = try lineContaining(run.stderr, "cannot select");
    try expectContains(refusal, "missing.zig");
    try expectAbsent(run.stderr, "imported source failed");
}

// ── SARIF ────────────────────────────────────────────────────

test "cli sarif: a clean run reports a successful invocation and no results" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("clean.zig", clean_value);

    var run = try zbc(fx.dir, &.{ "--format=sarif", "clean.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 0), run.code);

    const log = try parseSarif(run.stdout);
    defer log.deinit();

    try std.testing.expectEqualStrings("2.1.0", log.value.version);
    try std.testing.expectEqual(@as(usize, 1), log.value.runs.len);
    const sarif_run = log.value.runs[0];
    try std.testing.expectEqualStrings("zbc", sarif_run.tool.driver.name);
    // Completeness, not verdict: a clean run completed.
    try std.testing.expectEqual(@as(usize, 1), sarif_run.invocations.len);
    try std.testing.expect(sarif_run.invocations[0].executionSuccessful);
    try std.testing.expectEqual(@as(usize, 0), sarif_run.results.len);
    try std.testing.expectEqual(@as(usize, 0), sarif_run.tool.driver.rules.len);

    try expectSummary(&run, 1, 1, 0, 0, 0);
}

test "cli sarif: a finding reports rule, region and a percent-encoded file uri" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write(encoded_finding_file, stack_escape_one_line);

    var run = try zbc(fx.dir, &.{ "--format=sarif", only_stack_escape, encoded_finding_file });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 1), run.code);

    const log = try parseSarif(run.stdout);
    defer log.deinit();

    const sarif_run = log.value.runs[0];
    try std.testing.expect(sarif_run.invocations[0].executionSuccessful);
    try std.testing.expectEqual(@as(usize, 1), sarif_run.results.len);

    const result = sarif_run.results[0];
    try std.testing.expectEqualStrings("stack-escape", result.ruleId);
    try std.testing.expectEqualStrings("error", result.level);
    try std.testing.expectEqualStrings("fail", result.kind);
    try std.testing.expect(result.message.text.len > 0);

    try std.testing.expectEqual(@as(usize, 1), result.locations.len);
    const physical = result.locations[0].physicalLocation;
    // The whole canonical identity, derived from the fixture path rather
    // than from a suffix. The fixture directory is plain, so the URI is
    // the scheme plus that absolute path, and the only bytes needing an
    // escape are the space and the percent sign in the filename. A raw
    // splice of the path would leave both unescaped and fail here.
    const expected_uri = try std.fmt.allocPrint(gpa, "file://{s}/bad%20space%25pct.zig", .{fx.dir});
    defer gpa.free(expected_uri);
    try std.testing.expectEqualStrings(expected_uri, physical.artifactLocation.uri);
    try std.testing.expect(std.mem.indexOfScalar(u8, physical.artifactLocation.uri, ' ') == null);

    const region = physical.region;
    try std.testing.expectEqual(@as(u32, 1), region.startLine);
    try std.testing.expect(region.startColumn > 0);
    try std.testing.expectEqual(region.startLine, region.endLine);
    try std.testing.expect(region.byteLength > 0);

    // The driver carries a descriptor for the rule it reported.
    try std.testing.expectEqual(@as(usize, 1), sarif_run.tool.driver.rules.len);
    try std.testing.expectEqualStrings("stack-escape", sarif_run.tool.driver.rules[0].id);

    try expectSummary(&run, 1, 1, 0, 0, 1);
}

test "cli sarif: every result keeps its own file's uri and position" {
    var fx = try Fixture.init();
    defer fx.deinit();
    // One rule, three files, three findings. The names have three
    // different lengths and the escapes sit on three different lines,
    // because the log is serialized one result at a time into a single
    // scratch buffer: a result that kept a neighbour's bytes, or a
    // neighbour's length, is only visible when the three differ.
    try fx.write("a.zig", stack_escape_one_line);
    try fx.write("bb.zig", stack_escape_multiline);
    try fx.write("ccc.zig", stack_escape_line5);

    var run = try zbc(fx.dir, &.{
        "--format=sarif",
        only_stack_escape,
        "a.zig",
        "bb.zig",
        "ccc.zig",
    });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 1), run.code);

    const log = try parseSarif(run.stdout);
    defer log.deinit();

    const sarif_run = log.value.runs[0];
    try std.testing.expect(sarif_run.invocations[0].executionSuccessful);
    try std.testing.expectEqual(@as(usize, 3), sarif_run.results.len);

    // Findings are ordered by path, so each slot has exactly one file it
    // is allowed to name. The uri is rebuilt from the fixture path here
    // rather than read back from the log, so a serialization that copied
    // the previous result's path cannot agree with it.
    const expected = [_]struct { name: []const u8, line: u32 }{
        .{ .name = "a.zig", .line = 1 },
        .{ .name = "bb.zig", .line = 3 },
        .{ .name = "ccc.zig", .line = 5 },
    };
    for (sarif_run.results, expected) |result, want| {
        try std.testing.expectEqualStrings("stack-escape", result.ruleId);
        try std.testing.expectEqual(@as(usize, 1), result.locations.len);

        const uri = try std.fmt.allocPrint(gpa, "file://{s}/{s}", .{ fx.dir, want.name });
        defer gpa.free(uri);
        try std.testing.expectEqualStrings(uri, result.locations[0].physicalLocation.artifactLocation.uri);

        // The span is that file's own, not the first file's carried
        // forward, and it is a real span inside the bytes that were read.
        const region = result.locations[0].physicalLocation.region;
        try std.testing.expectEqual(want.line, region.startLine);
        try std.testing.expect(region.startColumn > 0);
        try std.testing.expectEqual(region.startLine, region.endLine);
        try std.testing.expect(region.byteLength > 0);
    }

    // One rule reported, so the driver carries one descriptor however
    // many results name it.
    try std.testing.expectEqual(@as(usize, 1), sarif_run.tool.driver.rules.len);
    try std.testing.expectEqualStrings("stack-escape", sarif_run.tool.driver.rules[0].id);

    try expectSummary(&run, 3, 3, 0, 0, 3);
}

test "cli sarif: a missing input reports an unsuccessful invocation" {
    var fx = try Fixture.init();
    defer fx.deinit();

    var run = try zbc(fx.dir, &.{ "--format=sarif", "missing.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);

    const log = try parseSarif(run.stdout);
    defer log.deinit();

    // An input that could not be selected is an incomplete run, even
    // though a well-formed log with no results was still emitted.
    try std.testing.expect(!log.value.runs[0].invocations[0].executionSuccessful);
    try std.testing.expectEqual(@as(usize, 0), log.value.runs[0].results.len);

    const refusal = try lineContaining(run.stderr, "cannot select");
    try expectContains(refusal, "missing.zig");
    try expectSummary(&run, 1, 0, 0, 1, 0);
}

test "cli sarif: malformed root source is attributed to the root with no imported hint" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("broken.zig", malformed_root);
    const abs = try fx.pathOf("broken.zig");
    defer gpa.free(abs);

    var run = try zbc(fx.dir, &.{ "--format=sarif", "broken.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);

    const log = try parseSarif(run.stdout);
    defer log.deinit();

    try std.testing.expect(!log.value.runs[0].invocations[0].executionSuccessful);
    try std.testing.expectEqual(@as(usize, 0), log.value.runs[0].results.len);

    try expectAbsent(run.stderr, "imported source failed");
    const diagnostic = try lineContaining(run.stderr, "parse error:");
    // Same claim as the JSON run makes, checked the same way: the exact
    // site the parser reports for these bytes.
    try expectParseError(diagnostic, abs, malformed_root);

    try expectSummary(&run, 1, 0, 0, 1, 0);
}

test "cli sarif: a malformed import is attributed to the imported path" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("main.zig", imports_broken_dep);
    try fx.write("dep.zig", malformed_dep);
    const root_abs = try fx.pathOf("main.zig");
    defer gpa.free(root_abs);
    const dep_abs = try fx.pathOf("dep.zig");
    defer gpa.free(dep_abs);

    var run = try zbc(fx.dir, &.{ "--format=sarif", "main.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);

    const log = try parseSarif(run.stdout);
    defer log.deinit();

    try std.testing.expect(!log.value.runs[0].invocations[0].executionSuccessful);
    try std.testing.expectEqual(@as(usize, 0), log.value.runs[0].results.len);

    const hint = try lineContaining(run.stderr, "imported source failed");
    try expectContains(hint, root_abs);
    const diagnostic = try lineContaining(run.stderr, "parse error:");
    const dep_uri = try std.fmt.allocPrint(gpa, "file://{s}", .{dep_abs});
    defer gpa.free(dep_uri);
    // The dependency's own bytes are parsed here, so the coordinate
    // compared against is the one the parser gave that document.
    try expectParseError(diagnostic, dep_uri, malformed_dep);

    try expectSummary(&run, 1, 0, 0, 1, 0);
}

test "cli sarif: a mixed run keeps results while the invocation is unsuccessful" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("clean.zig", clean_value);
    try fx.write("finding.zig", stack_escape_multiline);
    try fx.write("broken.zig", malformed_root);

    var run = try zbc(fx.dir, &.{ "--format=sarif", only_stack_escape, ".", "missing.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);

    const log = try parseSarif(run.stdout);
    defer log.deinit();

    const sarif_run = log.value.runs[0];
    // Both halves of the run's state at once: it did not finish, and the
    // finding it did establish is still delivered.
    try std.testing.expect(!sarif_run.invocations[0].executionSuccessful);
    try std.testing.expectEqual(@as(usize, 1), sarif_run.results.len);
    try std.testing.expectEqualStrings("stack-escape", sarif_run.results[0].ruleId);

    try expectSummary(&run, 4, 2, 0, 2, 1);
}

// ── Partial analysis ─────────────────────────────────────────

test "cli json: an exhausted function keeps the others' findings, is listed, and exits 2" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("partial.zig", exhausted_function_src);
    const partial_abs = try fx.pathOf("partial.zig");
    defer gpa.free(partial_abs);

    var run = try zbc(fx.dir, &.{ "--format=json", "partial.zig" });
    defer run.deinit();

    // Incomplete outranks a finding: the run did not finish the file.
    try std.testing.expectEqual(@as(u8, 2), run.code);

    // stdout stays a bare array holding exactly the finished function's finding.
    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();
    try std.testing.expectEqual(@as(usize, 1), parsed.value.len);
    try std.testing.expectEqualStrings(partial_abs, parsed.value[0].path);
    try std.testing.expectEqualStrings("stack-escape", parsed.value[0].rule_id);
    try std.testing.expectEqual(@as(u32, 27), parsed.value[0].start.line);
    try expectAbsent(run.stdout, "heap-double-free");

    // One stderr line names the file, the function and the limit that tripped.
    const incomplete = try lineContaining(run.stderr, "zbc: incomplete");
    try expectContains(incomplete, partial_abs);
    try expectContains(incomplete, "fn many");
    try expectContains(incomplete, "path states per block limit 64 reached 64");
    try expectContains(incomplete, " at ");
    try expectAbsent(run.stderr, "cannot analyze");

    // Neither analyzed nor failed: its own bucket.
    try expectSummary(&run, 1, 0, 1, 0, 1);
}

test "cli sarif: a partial file keeps its results and the invocation is unsuccessful" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("partial.zig", exhausted_function_src);

    var run = try zbc(fx.dir, &.{ "--format=sarif", "partial.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);
    const log = try parseSarif(run.stdout);
    defer log.deinit();
    const sarif_run = log.value.runs[0];
    try std.testing.expect(!sarif_run.invocations[0].executionSuccessful);
    try std.testing.expectEqual(@as(usize, 1), sarif_run.results.len);
    try std.testing.expectEqualStrings("stack-escape", sarif_run.results[0].ruleId);
    try expectSummary(&run, 1, 0, 1, 0, 1);
}

test "cli json: partial, failed and complete files are counted apart" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("clean.zig", clean_value);
    try fx.write("partial.zig", exhausted_function_src);
    try fx.write("broken.zig", malformed_root);

    var run = try zbc(fx.dir, &.{ "--format=json", "." });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);
    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();
    try std.testing.expectEqual(@as(usize, 1), parsed.value.len);
    // selected = analyzed + partial + failed.
    try expectSummary(&run, 3, 1, 1, 1, 1);
    try expectContains(run.stderr, "zbc: incomplete");
}

test "cli json: --allow-partial lets partial coverage pass but keeps findings and failures decisive" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("partial.zig", exhausted_function_src);
    try fx.write("broken.zig", malformed_root);

    // The finished function's finding still fails the run.
    var finding = try zbc(fx.dir, &.{ "--format=json", "--allow-partial", "partial.zig" });
    defer finding.deinit();
    try std.testing.expectEqual(@as(u8, 1), finding.code);
    try expectSummary(&finding, 1, 0, 1, 0, 1);
    try expectContains(finding.stderr, "zbc: incomplete");

    // Partial coverage alone passes; the summary still counts it.
    var quiet = try zbc(fx.dir, &.{ "--format=json", "--allow-partial", "--disable=stack_escape", "partial.zig" });
    defer quiet.deinit();
    try std.testing.expectEqual(@as(u8, 0), quiet.code);
    try expectSummary(&quiet, 1, 0, 1, 0, 0);
    try expectContains(quiet.stderr, "zbc: incomplete");

    // A failed file is never covered by the flag.
    var failed = try zbc(fx.dir, &.{ "--format=json", "--allow-partial", "--disable=stack_escape", "partial.zig", "broken.zig" });
    defer failed.deinit();
    try std.testing.expectEqual(@as(u8, 2), failed.code);
    try expectSummary(&failed, 2, 0, 1, 1, 0);
}

// ── Flags ────────────────────────────────────────────────────

test "cli: a rejected --jobs value answers once and accounts for nothing" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("escape.zig", stack_escape_one_line);

    // Argument parsing answers and returns before selection runs, so
    // nothing was selected and there is no summary to print.
    var run = try zbc(fx.dir, &.{ "--jobs=zero", "escape.zig" });
    defer run.deinit();

    try expectSingleFlagDiagnostic(&run, "--jobs", &.{ "--jobs", "zero", "positive", "integer" }, &.{});
}

test "cli: an unknown invariant answers once and accounts for nothing" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("escape.zig", stack_escape_one_line);

    // The invariant parser prints its own diagnostic and the caller turns
    // that into exit 2 without adding a second, contentless line.
    var run = try zbc(fx.dir, &.{ "--enable=not_an_invariant", "escape.zig" });
    defer run.deinit();

    try expectSingleFlagDiagnostic(&run, "not_an_invariant", &.{ "not_an_invariant", "--list-invariants" }, &.{});
}

test "cli: an empty --exclude value answers once and accounts for nothing" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("escape.zig", stack_escape_one_line);

    var run = try zbc(fx.dir, &.{ "--exclude=", "escape.zig" });
    defer run.deinit();

    try expectSingleFlagDiagnostic(&run, "--exclude", &.{ "--exclude", "non-empty" }, &.{ "name", "path" });
}

test "cli: --help prints usage and exits 0" {
    var fx = try Fixture.init();
    defer fx.deinit();

    var run = try zbc(fx.dir, &.{"--help"});
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 0), run.code);
    try std.testing.expectEqualStrings("", run.stdout);
    try expectContains(run.stderr, "usage: zbc");
    // Asking for help is not a run, so nothing is accounted for.
    try expectAbsent(run.stderr, "selected=");
}

test "cli: no operand prints usage and accounts for nothing" {
    var fx = try Fixture.init();
    defer fx.deinit();

    var run = try zbc(fx.dir, &.{"--format=json"});
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);
    try std.testing.expectEqualStrings("", run.stdout);
    try expectContains(run.stderr, "usage: zbc");
    try expectAbsent(run.stderr, "selected=");
}

// ── Exclusions: named versus walked ──────────────────────────

test "cli json: a named pruned-tree input is refused by the default rule" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("vendor/hidden.zig", malformed_root);
    try fx.write("keep.zig", stack_escape_one_line);

    // A named excluded source is a failed selection, not a parse attempt.
    // Its allowed peer must still be analyzed and reported.
    var run = try zbc(fx.dir, &.{ "--format=json", only_stack_escape, "vendor/hidden.zig", "keep.zig" });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);
    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();
    try std.testing.expectEqual(@as(usize, 1), parsed.value.len);
    const kept = try fx.pathOf("keep.zig");
    defer gpa.free(kept);
    try std.testing.expectEqualStrings(kept, parsed.value[0].path);
    try expectAbsent(run.stderr, "parse error:");
    try expectSummary(&run, 2, 1, 0, 1, 1);
}

test "cli json: a named --exclude input is refused by the configured rule" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("skipme/hidden.zig", stack_escape_one_line);

    // Prove the source is analyzable without the configured exclusion.
    var included = try zbc(fx.dir, &.{ "--format=json", only_stack_escape, "skipme/hidden.zig" });
    defer included.deinit();
    try std.testing.expectEqual(@as(u8, 1), included.code);
    const included_problems = try parseProblems(included.stdout);
    defer included_problems.deinit();
    try std.testing.expectEqual(@as(usize, 1), included_problems.value.len);
    const hidden = try fx.pathOf("skipme/hidden.zig");
    defer gpa.free(hidden);
    try std.testing.expectEqualStrings(hidden, included_problems.value[0].path);
    try expectSummary(&included, 1, 1, 0, 0, 1);

    var run = try zbc(fx.dir, &.{
        "--format=json",
        only_stack_escape,
        "--exclude=skipme",
        "skipme/hidden.zig",
    });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 2), run.code);
    try expectEmptyBareArray(&run);

    try expectSummary(&run, 1, 0, 0, 1, 0);

    var directory = try zbc(fx.dir, &.{ "--format=json", only_stack_escape, "--exclude=skipme", "skipme" });
    defer directory.deinit();
    try std.testing.expectEqual(@as(u8, 2), directory.code);
    try expectEmptyBareArray(&directory);
    try expectSummary(&directory, 1, 0, 0, 1, 0);

    if (builtin.os.tag != .windows) {
        try fx.tmp.dir.symLink(io, "skipme/hidden.zig", "alias.zig", .{});
        var alias = try zbc(fx.dir, &.{ "--format=json", only_stack_escape, "--exclude=skipme", "alias.zig" });
        defer alias.deinit();
        try std.testing.expectEqual(@as(u8, 2), alias.code);
        try expectEmptyBareArray(&alias);
        try expectSummary(&alias, 1, 0, 0, 1, 0);

        var outside = try Fixture.init();
        defer outside.deinit();
        try outside.write("broken.zig", malformed_root);
        const target = try outside.pathOf("broken.zig");
        defer gpa.free(target);
        try fx.tmp.dir.symLink(io, target, "outside.zig", .{});
        try fx.tmp.dir.symLink(io, outside.dir, "outside", .{ .is_directory = true });
        var escaped = try zbc(fx.dir, &.{ "--format=json", only_stack_escape, "outside.zig", "outside" });
        defer escaped.deinit();
        try std.testing.expectEqual(@as(u8, 2), escaped.code);
        try expectEmptyBareArray(&escaped);
        try expectAbsent(escaped.stderr, "parse error:");
        try expectSummary(&escaped, 2, 0, 0, 2, 0);
    }
}

test "cli json: a pruned child of a requested walk is silent" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("keep/hidden.zig", stack_escape_one_line);
    try fx.write("vendor/hidden.zig", malformed_root);
    try fx.write("skipme/deep/broken.zig", malformed_root);
    try fx.write("skipme/live.zig", clean_value);

    // Prune default and configured subtrees without losing an allowed sibling.
    // A malformed pruned source must never become a parse failure.
    var run = try zbc(fx.dir, &.{ "--format=json", only_stack_escape, "--exclude=skipme/deep", "." });
    defer run.deinit();

    try std.testing.expectEqual(@as(u8, 1), run.code);

    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 1), parsed.value.len);
    const kept = try fx.pathOf("keep/hidden.zig");
    defer gpa.free(kept);
    try std.testing.expectEqualStrings(kept, parsed.value[0].path);

    // Pruning is neither a failure nor a report: the pruned name appears
    // on no channel, and the counts describe only what the walk yielded.
    try expectAbsent(run.stderr, "vendor");
    try expectAbsent(run.stderr, "cannot select");
    try expectAbsent(run.stderr, "parse error:");
    try expectSummary(&run, 2, 2, 0, 0, 1);
}

// ── Determinism ──────────────────────────────────────────────

test "cli json: operand order and --jobs do not change the report" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("a.zig", stack_escape_one_line);
    try fx.write("b.zig", stack_escape_one_line);
    try fx.write("c.zig", stack_escape_one_line);

    // One worker in one order against three workers in the reverse one.
    // Neither argv spelling nor worker count may reach the report.
    var one = try zbc(fx.dir, &.{
        "--format=json",
        only_stack_escape,
        "--jobs=1",
        "a.zig",
        "b.zig",
        "c.zig",
    });
    defer one.deinit();
    var many = try zbc(fx.dir, &.{
        "--format=json",
        only_stack_escape,
        "--jobs=3",
        "c.zig",
        "b.zig",
        "a.zig",
    });
    defer many.deinit();

    try std.testing.expectEqual(@as(u8, 1), one.code);
    try std.testing.expectEqual(@as(u8, 1), many.code);
    if (!std.mem.eql(u8, one.stdout, many.stdout)) {
        std.debug.print("jobs=1 a,b,c:\n{s}\njobs=3 c,b,a:\n{s}", .{ one.stdout, many.stdout });
        return error.ReportOrderDependedOnInvocation;
    }

    const parsed = try parseProblems(one.stdout);
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 3), parsed.value.len);
    for (parsed.value[1..], parsed.value[0 .. parsed.value.len - 1]) |later, earlier| {
        try std.testing.expect(std.mem.lessThan(u8, earlier.path, later.path));
    }

    try expectSummary(&one, 3, 3, 0, 0, 3);
    try expectSummary(&many, 3, 3, 0, 0, 3);
}

// ── Channels ─────────────────────────────────────────────────

test "cli: the report and the summary never share a channel" {
    var fx = try Fixture.init();
    defer fx.deinit();
    try fx.write("escape.zig", stack_escape_one_line);

    var run = try zbc(fx.dir, &.{ "--format=json", only_stack_escape, "escape.zig" });
    defer run.deinit();

    // The run really did report a finding, so the channel split below is
    // asserted on a run that carries a report and not on a clean one.
    try std.testing.expectEqual(@as(u8, 1), run.code);

    // stdout carries the document and no operational message, so a
    // consumer parsing it keeps working when the run reports problems.
    // Parsing into an array type is the shape check; leading whitespace
    // is not the contract, so it is not pinned.
    const parsed = try parseProblems(run.stdout);
    defer parsed.deinit();
    try std.testing.expectEqual(@as(usize, 1), parsed.value.len);
    try expectAbsent(run.stdout, "zbc:");

    // stderr carries the operations and no report document.
    try std.testing.expect(std.mem.startsWith(u8, run.stderr, "zbc: "));
    try expectAbsent(run.stderr, "[{");

    try expectSummary(&run, 1, 1, 0, 0, 1);
}
