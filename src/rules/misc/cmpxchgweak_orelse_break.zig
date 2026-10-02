//! Detects `cmpxchgWeak(...) orelse break/return/continue` — a logic inversion.
//! In Zig, `@cmpxchgWeak` (and `Atomic.cmpxchgWeak`) returns `?T` where:
//!   - `null`   = **success** — the exchange was performed
//!   - `Some(T)` = **failure** — the exchange was NOT performed (returns current value)
//! An `orelse break/return/continue` exits when the result is `null`, i.e. on
//! **success**, which is almost always the opposite of the intent.  The typical
//! CAS loop retries on failure and proceeds (spawns a thread, does work) on
//! success — using `orelse` to exit on success silently skips the success path.
//!
//! Real-world instance:
//!   - oven-sh/bun#28940 (ThreadPool): `sync.cmpxchgWeak(...) orelse break` exited
//!     the spawn loop on **success**, so threads were never spawned.  The phantom
//!     slot was counted but no thread was started.  Fix: check `if (result) |current|
//!     { sync = current; continue; }` (retry on failure) and fall through on success.
//!
//! Detection (Tier 1, paren-balanced token walk):
//!   Pattern: `cmpxchgWeak ( ... ) orelse ( break | return | continue )`
//!   — find `cmpxchgWeak` identifier followed by `(`, skip to matching `)`,
//!   then check for `keyword_orelse` followed by `keyword_break`, `keyword_return`,
//!   or `keyword_continue`.  Fire at `orelse`.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "cmpxchgweak-orelse-break";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .cmpxchgweak_orelse_break)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 6) return;
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 2 <= last_tok) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "cmpxchgWeak")) continue;
        if (tags[t + 1] != .l_paren) continue;

        // Skip the argument list (depth-balanced)
        var i = t + 2;
        var depth: u32 = 1;
        while (i <= last_tok and depth > 0) : (i += 1) {
            switch (tags[i]) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => depth -= 1,
                else => {},
            }
        }
        if (depth != 0) continue;
        // i is now one past the closing ')'

        // Check for orelse followed by break/return/continue
        if (i > last_tok) continue;
        if (tags[i] != .keyword_orelse) continue;
        if (i + 1 > last_tok) continue;
        switch (tags[i + 1]) {
            .keyword_break, .keyword_return, .keyword_continue => {},
            else => continue,
        }

        try report(gpa, problems, tree, i, tags[i + 1]);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    orelse_tok: Ast.TokenIndex,
    action_tag: std.zig.Token.Tag,
) !void {
    const action = switch (action_tag) {
        .keyword_break => "break",
        .keyword_return => "return",
        .keyword_continue => "continue",
        else => unreachable,
    };
    const msg = try std.fmt.allocPrint(
        gpa,
        "`cmpxchgWeak(...) orelse {s}` exits on CAS **success** (null = success in Zig); the `orelse` branch runs when the exchange succeeded, not when it failed — use `if (cmpxchgWeak(...)) |current| {{ ... retry ... }}` and fall through on success",
        .{action},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, orelse_tok),
        .end = Pos.fromTokenEnd(tree, orelse_tok + 1),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "cmpxchgweak-orelse-break: fires on cmpxchgWeak orelse break" {
    try testing.expectFires(check, R,
        \\fn spawnLoop(self: *Self) void {
        \\    var sync = self.sync.load(.monotonic);
        \\    while (true) {
        \\        const new_sync = sync.with(.{ .spawning = true });
        \\        sync = @as(Sync, @bitCast(self.sync.cmpxchgWeak(
        \\            @as(u32, @bitCast(sync)),
        \\            @as(u32, @bitCast(new_sync)),
        \\            .release,
        \\            .monotonic,
        \\        ) orelse break));
        \\    }
        \\}
        \\
    );
}

test "cmpxchgweak-orelse-break: fires on orelse return" {
    try testing.expectFires(check, R,
        \\fn trySwap(atomic: *Atomic(u32), old: u32, new: u32) void {
        \\    atomic.cmpxchgWeak(old, new, .seq_cst, .seq_cst) orelse return;
        \\}
        \\
    );
}

test "cmpxchgweak-orelse-break: fires on orelse continue" {
    try testing.expectFires(check, R,
        \\fn spinLoop(a: *Atomic(u32)) void {
        \\    while (true) {
        \\        const cur = a.load(.monotonic);
        \\        a.cmpxchgWeak(cur, cur + 1, .release, .monotonic) orelse continue;
        \\    }
        \\}
        \\
    );
}

test "cmpxchgweak-orelse-break: if-capture form does not fire" {
    try testing.expectNoFire(check,
        \\fn casLoop(a: *Atomic(u32), old: u32, new: u32) void {
        \\    while (true) {
        \\        if (a.cmpxchgWeak(old, new, .acq_rel, .monotonic)) |current| {
        \\            _ = current;
        \\            continue;
        \\        }
        \\        break;
        \\    }
        \\}
        \\
    );
}

test "cmpxchgweak-orelse-break: cmpxchgStrong orelse does not fire" {
    try testing.expectNoFire(check,
        \\fn strongSwap(a: *Atomic(u32), old: u32, new: u32) bool {
        \\    return a.cmpxchgStrong(old, new, .seq_cst, .seq_cst) == null;
        \\}
        \\
    );
}
