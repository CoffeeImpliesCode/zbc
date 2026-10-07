//! Optional-fallback-wrong-side detector — `self.remoteSettings orelse
//! self.localSettings` uses the wrong fallback direction.  When the
//! left-hand field is a peer-advertised value and the right-hand field
//! is a locally-configured limit, the `orelse` silently relaxes a
//! security check when the peer hasn't sent SETTINGS yet (null).
//!
//! Real-world: oven-sh/bun#31129, h2_frame_parser.zig — HTTP/2 frame
//! validation used `self.remoteSettings orelse self.localSettings`
//! instead of `self.localSettings` (or a properly guarded fallback).
//!
//! Detection (Tier 1 naming heuristic):
//!   Token pattern:
//!     t+0: identifier (recv)
//!     t+1: period
//!     t+2: identifier (field_A)
//!     t+3: keyword_orelse
//!     t+4: identifier (recv2, same as recv)
//!     t+5: period
//!     t+6: identifier (field_B)
//!   where:
//!     - recv == recv2 (same receiver on both sides)
//!     - field_A and field_B have opposing semantic-pole prefixes
//!       (remote/local, peer/own, client/server, external/internal,
//!        advertised/configured)
//!
//! Note: in Zig `orelse` is tokenized as `.keyword_orelse`, not as
//! an identifier.  `true`/`false`/`null` are identifiers.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

const R = "optional-fallback-wrong-side";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .optional_fallback_wrong_side)) return;
    _ = cache;
    try checkBody(gpa, tree, problems);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    // The last token index is already a `TokenIndex` — a `u32` — so the
    // scan bound needs no conversion of the token count to re-narrow.
    // The pattern spans seven tokens, so a file with fewer than that
    // holds none.
    const last = tree.lastToken(.root);
    if (last < 6) return;

    // Pure token-pattern scan over the entire file.  No fn-body
    // scoping needed — the pattern is unambiguous enough that false
    // positives from crossing fn boundaries are negligible, and
    // skipping nested-fn bodies would miss all hits (since the
    // pattern lives inside fn bodies).
    var t: Ast.TokenIndex = 0;
    while (t + 6 <= last) : (t += 1) {
        // Pattern:
        //   t+0: identifier  (recv)
        //   t+1: period
        //   t+2: identifier  (field_A)
        //   t+3: keyword_orelse
        //   t+4: identifier  (recv2)
        //   t+5: period
        //   t+6: identifier  (field_B)
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .keyword_orelse) continue;
        if (tags[t + 4] != .identifier) continue;
        if (tags[t + 5] != .period) continue;
        if (tags[t + 6] != .identifier) continue;

        const recv = tree.tokenSlice(t);
        const field_a = tree.tokenSlice(t + 2);
        const recv2 = tree.tokenSlice(t + 4);
        const field_b = tree.tokenSlice(t + 6);

        // Both sides must use the same receiver.
        if (!std.mem.eql(u8, recv, recv2)) continue;

        // Field names must have opposing poles.
        if (!isOpposingPoles(field_a, field_b)) continue;

        try reportProblem(gpa, problems, tree, t, recv, field_a, field_b);
    }
}

/// True iff `a` and `b` have semantically opposing pole prefixes —
/// one side is peer/remote/advertised and the other is local/own/configured.
fn isOpposingPoles(a: []const u8, b: []const u8) bool {
    return (hasPole(a, "remote") and hasPole(b, "local")) or
        (hasPole(a, "local") and hasPole(b, "remote")) or
        (hasPole(a, "peer") and hasPole(b, "own")) or
        (hasPole(a, "own") and hasPole(b, "peer")) or
        (hasPole(a, "client") and hasPole(b, "server")) or
        (hasPole(a, "server") and hasPole(b, "client")) or
        (hasPole(a, "external") and hasPole(b, "internal")) or
        (hasPole(a, "internal") and hasPole(b, "external")) or
        (hasPole(a, "advertised") and hasPole(b, "configured")) or
        (hasPole(a, "configured") and hasPole(b, "advertised"));
}

/// Case-insensitive prefix check: true iff `name` starts with `pole`.
fn hasPole(name: []const u8, pole: []const u8) bool {
    if (name.len < pole.len) return false;
    for (name[0..pole.len], pole) |nc, pc| {
        if (std.ascii.toLower(nc) != pc) return false;
    }
    return true;
}

fn reportProblem(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    start_tok: Ast.TokenIndex,
    recv: []const u8,
    field_a: []const u8,
    field_b: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s} orelse {s}.{s}` uses the wrong fallback — `{s}` is likely a peer-advertised value; when absent, the fallback should be the locally-configured limit, not another peer field; verify the `orelse` direction",
        .{ recv, field_a, recv, field_b, field_a },
    );
    errdefer gpa.free(msg);

    // Highlight the full `recv.field_A orelse recv.field_B` span.
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, start_tok),
        .end = try Pos.fromTokenEnd(tree, start_tok + 6),
        .message = msg,
    });
}

// ── Tests ────────────────────────────────────────────────────

test "optional-fallback-wrong-side: remote orelse local fires" {
    try testing.expectFires(check, R,
        \\pub fn validate(self: anytype, frame_size: u32) bool {
        \\    const limit = self.remoteSettings orelse self.localSettings;
        \\    return frame_size <= limit;
        \\}
        \\
    );
}

test "optional-fallback-wrong-side: peer orelse own fires" {
    try testing.expectFires(check, R,
        \\pub fn maxFrame(self: anytype) u32 {
        \\    return self.peerMaxFrameSize orelse self.ownMaxFrameSize;
        \\}
        \\
    );
}

test "optional-fallback-wrong-side: client orelse server fires" {
    try testing.expectFires(check, R,
        \\pub fn timeout(conn: anytype) u64 {
        \\    return conn.clientTimeout orelse conn.serverTimeout;
        \\}
        \\
    );
}

test "optional-fallback-wrong-side: no pole mismatch does not fire" {
    try testing.expectNoFire(check,
        \\pub fn value(self: anytype) u32 {
        \\    return self.optionalField orelse self.defaultField;
        \\}
        \\
    );
}

test "optional-fallback-wrong-side: different receiver on RHS does not fire" {
    try testing.expectNoFire(check,
        \\pub fn setting(self: anytype, default: u32) u32 {
        \\    return self.remoteMaxFrameSize orelse default;
        \\}
        \\
    );
}

test "optional-fallback-wrong-side: advertised orelse configured fires" {
    try testing.expectFires(check, R,
        \\pub fn windowSize(self: anytype) u32 {
        \\    return self.advertisedWindowSize orelse self.configuredWindowSize;
        \\}
        \\
    );
}

test "optional-fallback-wrong-side: external orelse internal fires" {
    try testing.expectFires(check, R,
        \\pub fn limit(ctx: anytype) u32 {
        \\    return ctx.externalLimit orelse ctx.internalLimit;
        \\}
        \\
    );
}
