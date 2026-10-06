//! Detects `someCall(...).assert()` — chaining `.assert()` on the result of
//! another call.  In bun's codebase, `bun.sys.Maybe(T).assert()` unpacks the
//! `.result` value OR calls `bun.Output.panic(...)` when the variant is `.err`.
//! Converting a fallible I/O operation into a panic silently turns every OS
//! error into a process crash, which is a reliability and DoS hazard for any
//! code path reachable by user-controlled inputs.
//!
//! Real-world instances:
//!   - oven-sh/bun#23344: `subprocess.stdin.buffer.start().assert()` — panicked
//!     when libuv returned UV_ENOTCONN after a Windows long-path CWD workaround.
//!   - oven-sh/bun#23520, #23935: identical pattern in stdout/stderr pipe start.
//!     Fix: check the Maybe result and propagate the error instead of asserting.
//!
//! Detection (Tier 1, flat token walk):
//!   Pattern: `r_paren period identifier("assert") l_paren r_paren` — 5 tokens.
//!   Fire at the `assert` identifier token.
//!   `bun.assert(cond)` (static function call) has shape
//!   `identifier period identifier l_paren` and does NOT match.
//!   Only the chained method form — result of a call `.assert()` — fires.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "maybe-assert-panics";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .maybe_assert_panics)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 4 <= last_tok) : (t += 1) {
        // Pattern: ) . assert ( )
        if (tags[t] != .r_paren) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "assert")) continue;
        if (tags[t + 3] != .l_paren) continue;
        if (tags[t + 4] != .r_paren) continue;

        try report(gpa, problems, tree, t + 2);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    assert_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`.assert()` on a `Maybe(T)` call result — `.assert()` panics when the variant is `.err`, converting every OS error into a process crash; check the result explicitly and propagate the error instead",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, assert_tok - 2),
        .end = Pos.fromTokenEnd(tree, assert_tok + 2),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "maybe-assert-panics: chained assert fires" {
    try testing.expectFires(check, R,
        \\fn startPipe(proc: *Process) void {
        \\    proc.stdin.buffer.start().assert();
        \\}
        \\
    );
}

test "maybe-assert-panics: bun.assert does not fire" {
    try testing.expectNoFire(check,
        \\fn check(cond: bool) void {
        \\    bun.assert(cond);
        \\}
        \\
    );
}

test "maybe-assert-panics: standalone identifier assert does not fire" {
    try testing.expectNoFire(check,
        \\fn check(val: bool) void {
        \\    assert(val);
        \\}
        \\
    );
}

test "maybe-assert-panics: asserting on field does not fire" {
    try testing.expectNoFire(check,
        \\fn check(maybe: Maybe(T)) T {
        \\    maybe.assert();
        \\    return maybe.result;
        \\}
        \\
    );
}
