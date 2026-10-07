//! Detects `.next().?` — a forced unwrap of an iterator's optional result.
//!
//! Standard Zig iterators return `?T`: `null` signals exhaustion.  Calling
//! `.next().?` asserts at runtime that the iterator has a remaining element.
//! When the iterator is already exhausted (e.g. the caller passed fewer items
//! than the code expects), this panics in debug/safe builds and invokes UB in
//! ReleaseFast.
//!
//! The safe idiom is `iter.next() orelse <handle-end>` or the `while`-loop
//! form `while (iter.next()) |val| { … }`.
//!
//! Real-world shapes:
//!   oven-sh/bun#27415 — `seq` builtin called `.next().?` after consuming all
//!     flags; when only flags were provided (no numeric args) the iterator was
//!     already empty → panic.
//!   oven-sh/bun#27316 — `cmds_array.next().?` on a JS-supplied argument list;
//!     empty array caused unconditional panic.
//!
//! Detection (Tier 1, token walk):
//!   6-token pattern:
//!     t+0: period   t+1: identifier("next")   t+2: l_paren
//!     t+3: r_paren  t+4: period               t+5: question_mark
//!   Fire at the `identifier("next")` token (t+1).
//!
//!   Suppression: findings inside a `test { … }` declaration body are
//!   suppressed.  Test code force-unwraps iterators over hard-coded, known
//!   inputs as a deliberate assertion; a panic there is a test failure, not a
//!   production crash.  This rule targets production input-handling code where
//!   the iterator may be empty at runtime.  (Token-level `keyword_test`
//!   brace-matching — see `collectTestRanges`.)

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "forced-unwrap-iterator-next";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .forced_unwrap_iterator_next)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var test_ranges: std.ArrayListUnmanaged(Range) = .empty;
    defer test_ranges.deinit(gpa);
    try collectTestRanges(gpa, tree, tags, &test_ranges);

    var t: Ast.TokenIndex = 0;
    while (t + 5 <= last_tok) : (t += 1) {
        // Pattern: . next ( ) . ?
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "next")) continue;
        if (tags[t + 2] != .l_paren) continue;
        if (tags[t + 3] != .r_paren) continue;
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] != .question_mark) continue;

        if (isInTestRange(test_ranges.items, t + 1)) continue;

        // Suppress `assert(RECV.next().?)` — the forced-unwrap is an
        // invariant assertion (programmer-verified that the element exists);
        // it behaves like a test assertion and a panic is a code bug, not
        // user input reaching an unchecked path.
        // Pattern (from t): t-2 = l_paren, t-3 = identifier("assert").
        if (t >= 3 and
            tags[t - 2] == .l_paren and
            tags[t - 3] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t - 3), "assert")) continue;

        // Suppress the FIRST `.next()` on a `std.mem.split*` iterator: split
        // iterators always yield at least one element (even for empty input),
        // so the first `.next()` is guaranteed non-null and the `.?` cannot
        // panic.  Subsequent `.next().?` calls on the same iterator are NOT
        // covered — they depend on the input having enough fields.
        if (t >= 1 and tags[t - 1] == .identifier and
            isFirstNextOnSplitIterator(tree, tags, t, tree.tokenSlice(t - 1))) continue;

        try report(gpa, problems, tree, t + 1);
    }
}

/// Token span of a `test { … }` declaration, from the `keyword_test` token
/// through its body's closing `r_brace` (inclusive).
const Range = struct { start: Ast.TokenIndex, end: Ast.TokenIndex };

/// Collects the token range of every `test` declaration and every `fn testXxx`
/// test-utility function in the file.  Covers:
///   `KEYWORD_test (STRINGLITERAL / IDENTIFIER)? Block`  — test declarations
///   `KEYWORD_fn IDENTIFIER(testXxx...) PARAMS RETTYPE Block` — test helpers
/// where `testXxx` means the name starts with lowercase "test" followed by an
/// uppercase letter (camelCase convention for Zig test utilities).
/// Ranges are pairwise disjoint (tests cannot nest), so a linear containment
/// check suffices.
fn collectTestRanges(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    out: *std.ArrayListUnmanaged(Range),
) !void {
    // `lastToken` returns a `TokenIndex` — a `u32` — so the scan bound
    // is the width every index below already uses, with no conversion
    // of the token count to re-narrow.
    const last_tok = tree.lastToken(.root);
    var i: Ast.TokenIndex = 0;
    while (i <= last_tok) : (i += 1) {
        const is_test_decl = tags[i] == .keyword_test;
        const is_test_fn = blk: {
            if (tags[i] != .keyword_fn) break :blk false;
            if (i + 1 > last_tok or tags[i + 1] != .identifier) break :blk false;
            const name = tree.tokenSlice(i + 1);
            // Match fn names that start with "test" (lowercase) followed by
            // an uppercase letter — the Zig convention for test helper fns.
            if (name.len < 5) break :blk false;
            if (!std.mem.startsWith(u8, name, "test")) break :blk false;
            break :blk std.ascii.isUpper(name[4]);
        };
        if (!is_test_decl and !is_test_fn) continue;

        // Find the body's opening `l_brace` (skipping header tokens).
        var j = i + 1;
        while (j <= last_tok and tags[j] != .l_brace) : (j += 1) {
            // Defensive: a well-formed header has no `;`/`}` before `{`.
            if (tags[j] == .semicolon or tags[j] == .r_brace) break;
        }
        if (j > last_tok or tags[j] != .l_brace) continue;

        // Brace-match forward from the opening brace.
        var depth: u32 = 0;
        var k = j;
        while (k <= last_tok) : (k += 1) {
            if (tags[k] == .l_brace) {
                depth += 1;
            } else if (tags[k] == .r_brace) {
                depth -= 1;
                if (depth == 0) break;
            }
        }
        if (k > last_tok) break; // unbalanced — only possible on a malformed tree

        try out.append(gpa, .{ .start = i, .end = k });
        i = k; // resume past this body
    }
}

/// True when `tok` falls within any collected `test { … }` range.
fn isInTestRange(ranges: []const Range, tok: Ast.TokenIndex) bool {
    for (ranges) |r| {
        if (tok >= r.start and tok <= r.end) return true;
    }
    return false;
}

/// True iff `recv` is declared (within a bounded backward window) as a
/// `std.mem.split*` iterator AND the `.next()` at `next_period` is the FIRST
/// `.next()` call on `recv` since that declaration.
///
/// `std.mem.splitScalar/splitSequence/splitAny` (and their `Backwards`
/// variants) are documented to always return at least one item, so the first
/// `.next()` cannot be null.  `tokenize*` is deliberately excluded — it can
/// return null on its first call for empty / all-delimiter input.
fn isFirstNextOnSplitIterator(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    next_period: Ast.TokenIndex,
    recv: []const u8,
) bool {
    const window: Ast.TokenIndex = 500;
    const lo: Ast.TokenIndex = if (next_period >= window) next_period - window else 0;

    // Find the nearest `(const|var) recv` declaration scanning backward.
    var decl: ?Ast.TokenIndex = null;
    var k = next_period;
    while (k > lo) {
        k -= 1;
        if (tags[k] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k), recv)) continue;
        if (k == 0) break;
        if (tags[k - 1] == .keyword_const or tags[k - 1] == .keyword_var) {
            decl = k;
            break;
        }
    }
    const decl_tok = decl orelse return false;

    // The RHS (decl .. semicolon) must name an iterator constructor whose first
    // `.next()` is guaranteed non-null: a `split*` constructor, or a
    // `std.process.args()` / `argsWithAllocator()` ArgIterator (argv[0], the
    // program name, is always present).
    var has_split = false;
    var j = decl_tok + 1;
    while (j < next_period and tags[j] != .semicolon) : (j += 1) {
        if (tags[j] != .identifier) continue;
        const nm = tree.tokenSlice(j);
        // `argsWithAllocator` is distinctive; bare `args` only counts when it is
        // the `process.args` method (preceded by `process .`) to avoid matching
        // unrelated `.args` fields.
        if (isSplitConstructor(nm) or
            std.mem.eql(u8, nm, "argsWithAllocator") or
            (std.mem.eql(u8, nm, "args") and j >= 2 and
                tags[j - 1] == .period and tags[j - 2] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(j - 2), "process")))
        {
            has_split = true;
            break;
        }
    }
    if (!has_split) return false;

    // First-next check: no earlier `recv . next (` between the decl and this use.
    var i = decl_tok + 1;
    while (i + 2 < next_period) : (i += 1) {
        if (tags[i] != .identifier or !std.mem.eql(u8, tree.tokenSlice(i), recv)) continue;
        if (tags[i + 1] == .period and
            tags[i + 2] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(i + 2), "next")) return false; // an earlier next() exists
    }
    return true;
}

fn isSplitConstructor(name: []const u8) bool {
    return std.mem.eql(u8, name, "split") or
        std.mem.eql(u8, name, "splitScalar") or
        std.mem.eql(u8, name, "splitSequence") or
        std.mem.eql(u8, name, "splitAny") or
        std.mem.eql(u8, name, "splitBackwards") or
        std.mem.eql(u8, name, "splitBackwardsScalar") or
        std.mem.eql(u8, name, "splitBackwardsSequence") or
        std.mem.eql(u8, name, "splitBackwardsAny");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    next_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`.next().?` force-unwraps the iterator result — if the iterator is exhausted, this panics (debug/safe) or invokes undefined behaviour (ReleaseFast); use `.next() orelse <handler>` or the `while (iter.next()) |val|` loop form instead",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, next_tok),
        .end = try Pos.fromTokenEnd(tree, next_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "forced-unwrap-iterator-next: basic fires" {
    try testing.expectFires(check, R,
        \\fn readFirst(iter: anytype) u32 {
        \\    return iter.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: orelse does not fire" {
    try testing.expectNoFire(check,
        \\fn readFirst(iter: anytype) ?u32 {
        \\    return iter.next() orelse null;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: while loop does not fire" {
    try testing.expectNoFire(check,
        \\fn processAll(iter: anytype) void {
        \\    while (iter.next()) |val| {
        \\        _ = val;
        \\    }
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: next with arg does not fire" {
    try testing.expectNoFire(check,
        \\fn readFirst(iter: anytype) u32 {
        \\    return iter.next(1);
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: first next on splitScalar does not fire" {
    try testing.expectNoFire(check,
        \\fn firstField(text: []const u8) []const u8 {
        \\    var parts = std.mem.splitScalar(u8, text, ',');
        \\    return parts.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: second next on splitScalar still fires" {
    try testing.expectFires(check, R,
        \\fn secondField(text: []const u8) []const u8 {
        \\    var parts = std.mem.splitScalar(u8, text, ',');
        \\    const a = parts.next().?;
        \\    _ = a;
        \\    return parts.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: first next on tokenize still fires" {
    try testing.expectFires(check, R,
        \\fn firstTok(text: []const u8) []const u8 {
        \\    var it = std.mem.tokenizeScalar(u8, text, ',');
        \\    return it.next().?;
        \\}
        \\
    );
}

// ── Test-block suppression ──────────────────────────────────

test "forced-unwrap-iterator-next: suppressed inside named test block" {
    try testing.expectNoFire(check,
        \\test "iterates" {
        \\    var it = makeIter();
        \\    const first = it.next().?;
        \\    _ = first;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: suppressed inside anonymous test block" {
    try testing.expectNoFire(check,
        \\test {
        \\    var it = makeIter();
        \\    _ = it.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: suppressed inside nested braces of a test" {
    try testing.expectNoFire(check,
        \\test "nested" {
        \\    {
        \\        var it = makeIter();
        \\        _ = it.next().?;
        \\    }
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: still fires in fn after a test block" {
    try testing.expectFires(check, R,
        \\test "setup" {
        \\    var it = makeIter();
        \\    _ = it.next().?;
        \\}
        \\fn parse(iter: anytype) u32 {
        \\    return iter.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: still fires in fn before a test block" {
    try testing.expectFires(check, R,
        \\fn parse(iter: anytype) u32 {
        \\    return iter.next().?;
        \\}
        \\test "after" {
        \\    var it = makeIter();
        \\    _ = it.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: assert context suppressed" {
    try testing.expectNoFire(check,
        \\fn checkInvariant(it: *SomeIterator) void {
        \\    assert(it.next().? == expected_first);
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: non-assert call still fires" {
    try testing.expectFires(check, R,
        \\fn process(it: *SomeIterator) void {
        \\    log(it.next().?);
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: fn testXxx body suppressed" {
    try testing.expectNoFire(check,
        \\fn testParse(params: []const u16) Attribute {
        \\    var p: Parser = .{ .params = params };
        \\    return p.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: fn not starting with test still fires" {
    try testing.expectFires(check, R,
        \\fn parse(p: *Parser) Attribute {
        \\    return p.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: first next on std.process.args suppressed" {
    try testing.expectNoFire(check,
        \\fn run() void {
        \\    var args = std.process.args();
        \\    const exe = args.next().?;
        \\    _ = exe;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: second next on args still fires" {
    try testing.expectFires(check, R,
        \\fn run() void {
        \\    var args = std.process.args();
        \\    _ = args.next();
        \\    const second = args.next().?;
        \\    _ = second;
        \\}
        \\
    );
}
