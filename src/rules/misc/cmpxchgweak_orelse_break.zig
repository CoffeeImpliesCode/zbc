//! Detects `cmpxchgWeak(...) orelse break/return/continue` — a logic inversion.
//! In Zig, `@cmpxchgWeak` (and `Atomic.cmpxchgWeak`) returns `?T` where:
//!   - `null`   = **success** — the exchange was performed
//!   - `Some(T)` = **failure** — the exchange was NOT performed (returns current value)
//! An `orelse break/return/continue` runs when the result is null: success.
//! A bounded maximum-update loop can deliberately break there. It retries
//! each non-null mismatch, including spurious failure, with the returned value.
//! Other forms can skip required success work (for example thread creation).
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
//!
//! The structural exception requires the entire body of `while (seen < value)`
//! to be `seen = atomic.cmpxchgWeak(seen, value, ..., ...) orelse break`.
//! It proves only this exit/retry relationship, not the atomic object's type,
//! ordering validity, initialization, or safety of code outside that loop.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");
const AstIterator = @import("type_engine").AstIterator;

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
    var remaining: usize = 50_000;

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

        if (tags[i + 1] == .keyword_break and try isMaximumRetry(tree, i, &remaining)) continue;
        try report(gpa, problems, tree, i, tags[i + 1]);
    }
}

/// All identifier uses are in one condition/assignment scope. The single
/// statement body cannot shadow a binding, change the desired bound, perform
/// skipped success work, or terminate after a spurious failure.
fn isMaximumRetry(tree: *const Ast, orelse_token: Ast.TokenIndex, remaining: *usize) !bool {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (remaining.* == 0) return error.AnalysisBudgetExceeded;
        remaining.* -= 1;
        switch (tag) {
            .while_simple, .while_cont, .@"while" => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const loop = tree.fullWhile(node) orelse continue;
        if (loop.label_token != null or loop.payload_token != null or
            loop.ast.cont_expr != .none or loop.ast.else_expr != .none) continue;
        if (tree.nodeTag(loop.ast.cond_expr) != .less_than) continue;
        const seen, const target = tree.nodeData(loop.ast.cond_expr).node_and_node;
        if (tree.nodeTag(seen) != .identifier or tree.nodeTag(target) != .identifier) continue;
        const seen_name = tree.tokenSlice(tree.nodeMainToken(seen));
        const target_name = tree.tokenSlice(tree.nodeMainToken(target));
        if (std.mem.eql(u8, seen_name, target_name)) continue;
        switch (tree.nodeTag(loop.ast.then_expr)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {},
            else => continue,
        }
        var statements = AstIterator.init(tree, loop.ast.then_expr);
        const assignment = statements.next(tree) orelse continue;
        if (statements.next(tree) != null or tree.nodeTag(assignment) != .assign) continue;
        const destination, const value = tree.nodeData(assignment).node_and_node;
        if (!identifierIs(tree, destination, seen_name) or tree.nodeTag(value) != .@"orelse" or
            tree.nodeMainToken(value) != orelse_token) continue;
        const call_node, const exit = tree.nodeData(value).node_and_node;
        if (tree.nodeTag(exit) != .@"break" or tree.firstToken(exit) != tree.lastToken(exit)) continue;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, call_node) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access or call.ast.params.len != 4) continue;
        const receiver, const method = tree.nodeData(call.ast.fn_expr).node_and_token;
        if (!std.mem.eql(u8, tree.tokenSlice(method), "cmpxchgWeak")) continue;
        // Only a stable identifier/field path is read as the atomic receiver.
        // A call in this position could mutate either loop operand.
        var path = receiver;
        var stable_receiver = false;
        for (0..64) |_| {
            if (remaining.* == 0) return error.AnalysisBudgetExceeded;
            remaining.* -= 1;
            if (tree.nodeTag(path) == .identifier) {
                stable_receiver = true;
                break;
            }
            if (tree.nodeTag(path) != .field_access) break;
            path = tree.nodeData(path).node_and_token[0];
        } else return error.AnalysisBudgetExceeded;
        if (!stable_receiver) continue;
        if (!identifierIs(tree, call.ast.params[0], seen_name) or
            !identifierIs(tree, call.ast.params[1], target_name)) continue;
        if (tree.nodeTag(call.ast.params[2]) != .enum_literal or
            tree.nodeTag(call.ast.params[3]) != .enum_literal) continue;
        return true;
    }
    return false;
}

fn identifierIs(tree: *const Ast, node: Ast.Node.Index, name: []const u8) bool {
    return tree.nodeTag(node) == .identifier and
        std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name);
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
        .start = try Pos.fromTokenStart(tree, orelse_tok),
        .end = try Pos.fromTokenEnd(tree, orelse_tok + 1),
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

test "cmpxchgweak-orelse-break: maximum retries mismatch and exits on success" {
    try testing.expectNoFire(check,
        \\fn enter(self: *Inside) void {
        \\    const here = self.now.fetchAdd(1, .acq_rel) + 1;
        \\    var seen = self.peak.load(.acquire);
        \\    while (seen < here) {
        \\        seen = self.peak.cmpxchgWeak(seen, here, .acq_rel, .acquire) orelse break;
        \\    }
        \\}
    );
}

test "cmpxchgweak-orelse-break: maximum must store the returned current value" {
    try testing.expectFires(check, R,
        \\fn enter(self: *Inside, here: u32) void {
        \\    var seen = self.peak.load(.acquire);
        \\    while (seen < here) {
        \\        _ = self.peak.cmpxchgWeak(seen, here, .acq_rel, .acquire) orelse break;
        \\    }
        \\}
    );
}

test "cmpxchgweak-orelse-break: maximum desired value must match the bound" {
    try testing.expectFires(check, R,
        \\fn enter(self: *Inside, here: u32, other: u32) void {
        \\    var seen = self.peak.load(.acquire);
        \\    while (seen < here) {
        \\        seen = self.peak.cmpxchgWeak(seen, other, .acq_rel, .acquire) orelse break;
        \\    }
        \\}
    );
}

test "cmpxchgweak-orelse-break: maximum expected value must match retry storage" {
    try testing.expectFires(check, R,
        \\fn enter(self: *Inside, here: u32, other: u32) void {
        \\    var seen = self.peak.load(.acquire);
        \\    while (seen < here) {
        \\        seen = self.peak.cmpxchgWeak(other, here, .acq_rel, .acquire) orelse break;
        \\    }
        \\}
    );
}

test "cmpxchgweak-orelse-break: success must not skip work after the exchange" {
    try testing.expectFires(check, R,
        \\fn enter(self: *Inside, here: u32) void {
        \\    var seen = self.peak.load(.acquire);
        \\    while (seen < here) {
        \\        seen = self.peak.cmpxchgWeak(seen, here, .acq_rel, .acquire) orelse break;
        \\        self.startWorker();
        \\    }
        \\}
    );
}

test "cmpxchgweak-orelse-break: labelled exit does not prove maximum-loop exit" {
    try testing.expectFires(check, R,
        \\fn enter(self: *Inside, here: u32) void {
        \\    outer: while (true) {
        \\        var seen = self.peak.load(.acquire);
        \\        while (seen < here) {
        \\            seen = self.peak.cmpxchgWeak(seen, here, .acq_rel, .acquire) orelse break :outer;
        \\        }
        \\    }
        \\}
    );
}

test "cmpxchgweak-orelse-break: failure must not terminate on a spurious mismatch" {
    try testing.expectFires(check, R,
        \\fn enter(self: *Inside, here: u32) void {
        \\    var seen = self.peak.load(.acquire);
        \\    while (seen < here) {
        \\        seen = self.peak.cmpxchgWeak(seen, here, .acq_rel, .acquire) orelse break;
        \\        break;
        \\    }
        \\}
    );
}
