//! Detects `.allocator().free(X)` — calling `.free()` on an allocator obtained
//! from an arena via `.allocator()`.  `ArenaAllocator` (and similar arena-like
//! allocators) do not implement per-allocation freeing: the `free` call is a
//! no-op at runtime, giving a false impression that the memory was released.
//! The memory is only reclaimed when the arena itself is deinitialized.
//!
//! Real-world instance:
//!   - oven-sh/bun#29380: `this.arena.allocator().free(name_matched_path)` — the
//!     free call was a no-op; a subsequent log still read the "freed" buffer.
//!     Fix: removed the no-op `.free()` call.
//!
//! Detection (Tier 1, flat token walk):
//!   Pattern: `. allocator ( ) . free`  — 6 tokens.
//!   Fire at the `allocator` identifier token.
//!   Catches chained `.allocator().free(...)` regardless of the arena's field
//!   name or nesting depth.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "arena-allocator-free-noop";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .arena_allocator_free_noop)) return;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 6) return;
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 5 <= last_tok) : (t += 1) {
        // Pattern: . allocator ( ) . free
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "allocator")) continue;
        if (tags[t + 2] != .l_paren) continue;
        if (tags[t + 3] != .r_paren) continue;
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 5), "free")) continue;

        // The receiver of `.allocator()` is the dotted path ending at t-1.
        // SEMANTIC decision: resolve the receiver's TYPE and fire iff it is an
        // arena-style allocator whose `.free()` is a no-op.  `.allocator()` is
        // also exposed by general-purpose allocators / wrapper structs, whose
        // `.free()` is perfectly valid — those must not fire regardless of how
        // the receiver is named.  When the type engine is unavailable
        // (token-only mode / unit tests), fall back to the name proxy
        // (receiver name contains "arena"); a non-identifier receiver
        // (call/index result) fires conservatively as before.
        if (t >= 1 and tags[t - 1] == .identifier) {
            const recv_last = t - 1;
            var recv_first = recv_last;
            while (recv_first >= 2 and
                tags[recv_first - 1] == .period and
                tags[recv_first - 2] == .identifier) : (recv_first -= 2)
            {}
            if (cache.typeNameOfExpr(recv_first, recv_last) catch null) |tyname| {
                // Type resolved — decide on the real type, ignore the name.
                if (!isNoopFreeAllocatorType(tyname)) continue;
            } else {
                // Unresolved — fall back to the syntactic name proxy.
                if (std.ascii.findIgnoreCase(tree.tokenSlice(recv_last), "arena") == null) continue;
            }
        }

        try report(gpa, problems, tree, t + 1);
    }
}

/// Allocator types whose `.free()` is a no-op (memory is reclaimed only by
/// the allocator's own teardown/reset), so calling `.free()` on a value
/// obtained from one is misleading dead code.
fn isNoopFreeAllocatorType(type_name: []const u8) bool {
    return std.mem.eql(u8, type_name, "ArenaAllocator");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    allocator_tok: Ast.TokenIndex,
) !void {
    const msg = try gpa.dupe(
        u8,
        "`.allocator().free(...)` is a no-op on arena-style allocators — `ArenaAllocator` does not free individual allocations; memory is reclaimed only when the arena itself is deinitialized via `.deinit()`",
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, allocator_tok),
        .end = Pos.fromTokenEnd(tree, allocator_tok + 4),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "arena-allocator-free-noop: fires on .allocator().free(x)" {
    try testing.expectFires(check, R,
        \\fn cleanup(self: *Self) void {
        \\    self.arena.allocator().free(self.buffer);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: fires on chained form" {
    try testing.expectFires(check, R,
        \\fn cleanup(arena: *Arena) void {
        \\    arena.allocator().free(slice);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: direct allocator.free does not fire" {
    try testing.expectNoFire(check,
        \\fn cleanup(allocator: Allocator) void {
        \\    allocator.free(slice);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: arena.deinit does not fire" {
    try testing.expectNoFire(check,
        \\fn cleanup(self: *Self) void {
        \\    self.arena.deinit();
        \\}
        \\
    );
}

test "arena-allocator-free-noop: .allocator().alloc does not fire" {
    try testing.expectNoFire(check,
        \\fn alloc(self: *Self, n: usize) ![]u8 {
        \\    return self.arena.allocator().alloc(u8, n);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: non-arena receiver does not fire" {
    try testing.expectNoFire(check,
        \\fn cleanup(dev: *DevServer) void {
        \\    dev.allocator().free(dev.buffer);
        \\}
        \\
    );
}

test "arena-allocator-free-noop: gpa receiver does not fire" {
    try testing.expectNoFire(check,
        \\fn cleanup(gpa: *std.heap.GeneralPurposeAllocator(.{})) void {
        \\    gpa.allocator().free(slice);
        \\}
        \\
    );
}
