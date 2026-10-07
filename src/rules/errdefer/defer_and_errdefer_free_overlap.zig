//! Defer-and-errdefer-free-overlap detector — `defer <alloc>.free(X);`
//! (unconditional cleanup) AND an `errdefer { ... <field> = X; ... }`
//! (error path: write `X` into a field) AND a subsequent `try`.
//! On the error path:
//!   1. errdefer fires: frees `self.<field>` (the NEW), sets
//!      `self.<field> = X` (the OLD).
//!   2. defer fires: frees `X` — the value just stored.
//!   → `self.<field>` is now a dangling pointer to freed memory.
//!
//! Real-world: ghostty-org/ghostty#8249 (`Atlas.grow`) — swap-and-
//! resurrect pattern where the defer's free and the errdefer's
//! field-restore land on the same name, leaking through the
//! errdefer's resurrected pointer.
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Skip comptime type-builder fns.
//!   2. Collect `defer <alloc>.free(<X>);` — track `<X>` names.
//!   3. Look for `errdefer { ... <lhs> = <X>; ... }` blocks
//!      where `<X>` is one of the deferred names AND the
//!      errdefer body also contains a free of a different
//!      receiver (the "free new, restore old" shape).
//!   4. Confirm a `try` appears between the errdefer and the end
//!      of the fn — that's the fallible op that triggers the
//!      double-fire.
//!   5. Fire at the errdefer site.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

const hasTokenInRange = tokens.hasTokenInRange;
const matchBrace = tokens.matchBrace;
const skipNestedFn = tokens.skipNestedFn;

const query = @import("../../ast/token_query.zig");
const Atom = query.Atom;

// `defer <alloc>.free(<X>...)` — captures the freed arg into slot 0.
const defer_free_pattern = &[_]Atom{
    .{ .tok = .keyword_defer },
    .{ .tok = .identifier },
    .{ .tok = .period },
    .{ .text = "free" },
    .{ .tok = .l_paren },
    .{ .capture = 0 },
};

// `.<free|destroy>(` — used to check errdefer body contains a free.
const free_or_destroy_call = &[_]Atom{
    .{ .tok = .period },
    .{ .pred = isAllocPairCleanupName },
    .{ .tok = .l_paren },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .defer_and_errdefer_free_overlap)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Collect `defer <alloc>.free(<X>);` matches — names referenced
    // directly from the match captures (no intermediate copy).
    const defer_matches = try query.findAllInBody(gpa, tree, defer_free_pattern, first, last);
    defer gpa.free(defer_matches);
    if (defer_matches.len == 0) return;

    // Walk for `errdefer { ... }` blocks that contain an
    // assignment `<lhs> = <deferred-name>;` AND a free call
    // (different receiver).
    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_errdefer) continue;
        const body_start: Ast.TokenIndex = t + 1;
        if (body_start > last or tags[body_start] != .l_brace) {
            // Inline form: a single statement.  This rule
            // requires a block form (free + restore is 2+
            // statements).
            continue;
        }
        const body_end = matchBrace(tags, body_start, last) orelse continue;
        const restored = errdeferRestoresDeferredName(tree, body_start + 1, body_end - 1, defer_matches) orelse {
            t = body_end;
            continue;
        };
        if (!query.anyMatchAnywhere(tree, free_or_destroy_call, body_start + 1, body_end - 1, null)) {
            t = body_end;
            continue;
        }
        // Confirm a `try` exists between errdefer and end of fn.
        if (!hasTokenInRange(tags, body_end + 1, last, .keyword_try)) {
            t = body_end;
            continue;
        }
        try report(gpa, problems, tree, t, restored);
        t = body_end;
    }
}

/// True iff the errdefer body contains an assignment
/// `<lhs> = <deferred-name>;` — restoring the to-be-freed name
/// into a field/local.
fn errdeferRestoresDeferredName(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    deferred: []const query.Match,
) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var t: Ast.TokenIndex = start;
    while (t + 1 <= end) : (t += 1) {
        if (tags[t] != .equal) continue;
        if (t + 1 > end or tags[t + 1] != .identifier) continue;
        const name = tree.tokenSlice(t + 1);
        for (deferred) |m| {
            const d = m.captureText(tree, 0).?;
            if (std.mem.eql(u8, d, name)) return d;
        }
    }
    return null;
}

fn isAllocPairCleanupName(name: []const u8) bool {
    return std.mem.eql(u8, name, "free") or std.mem.eql(u8, name, "destroy");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    errdefer_tok: Ast.TokenIndex,
    restored_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`errdefer` body frees the NEW value and restores `{s}` (the OLD value) into a field — but a prior `defer alloc.free({s});` will then ALSO free `{s}` at scope exit, leaving the restored field as a dangling pointer.  Remove the unconditional `defer` and free OLD only on the success path (or move the free into the errdefer body explicitly)",
        .{ restored_name, restored_name, restored_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "defer-and-errdefer-free-overlap",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, errdefer_tok),
        .end = try Pos.fromTokenEnd(tree, errdefer_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "defer-and-errdefer-free-overlap: Atlas.grow pattern fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    data: []u8,
        \\    nodes: std.ArrayList(u8),
        \\    pub fn grow(self: *Self, alloc: std.mem.Allocator) !void {
        \\        const data_old = self.data;
        \\        self.data = try alloc.alloc(u8, 64);
        \\        defer alloc.free(data_old);
        \\        errdefer {
        \\            alloc.free(self.data);
        \\            self.data = data_old;
        \\        }
        \\        try self.nodes.append(alloc, 0);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
    try std.testing.expectEqualStrings("defer-and-errdefer-free-overlap", problems.items[0].rule_id);
}

test "defer-and-errdefer-free-overlap: errdefer that doesn't restore doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    data: []u8,
        \\    pub fn grow(self: *Self, alloc: std.mem.Allocator) !void {
        \\        const data_old = self.data;
        \\        self.data = try alloc.alloc(u8, 64);
        \\        defer alloc.free(data_old);
        \\        errdefer alloc.free(self.data);
        \\        _ = try fallible();
        \\    }
        \\};
        \\fn fallible() !void {}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "defer-and-errdefer-free-overlap: no subsequent try doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    data: []u8,
        \\    pub fn grow(self: *Self, alloc: std.mem.Allocator) void {
        \\        const data_old = self.data;
        \\        self.data = alloc.alloc(u8, 64) catch return;
        \\        defer alloc.free(data_old);
        \\        errdefer {
        \\            alloc.free(self.data);
        \\            self.data = data_old;
        \\        }
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "defer-and-errdefer-free-overlap: restore of different name doesn't fire" {
    // The errdefer restores `other_buf` but the deferred free targets `data_old`.
    // Because the names differ, the rule correctly does NOT fire.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    data: []u8,
        \\    extra: []u8,
        \\    pub fn grow(self: *Self, alloc: std.mem.Allocator) !void {
        \\        const data_old = self.data;
        \\        const extra_old = self.extra;
        \\        self.data = try alloc.alloc(u8, 64);
        \\        defer alloc.free(data_old);
        \\        errdefer {
        \\            alloc.free(self.data);
        \\            self.extra = extra_old;
        \\        }
        \\        try self.populate();
        \\    }
        \\    fn populate(self: *Self) !void { _ = self; }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "defer-and-errdefer-free-overlap: errdefer block with no free inside doesn't fire" {
    // Restore without a paired free inside the errdefer body — the rule
    // requires both a restore AND a free inside the errdefer block.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    data: []u8,
        \\    pub fn grow(self: *Self, alloc: std.mem.Allocator) !void {
        \\        const data_old = self.data;
        \\        self.data = try alloc.alloc(u8, 64);
        \\        defer alloc.free(data_old);
        \\        errdefer {
        \\            self.data = data_old;
        \\        }
        \\        try self.populate();
        \\    }
        \\    fn populate(self: *Self) !void { _ = self; }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "defer-and-errdefer-free-overlap: destroy in errdefer body also fires" {
    // `destroy` is also a paired-cleanup name — the swap-and-resurrect bug
    // applies equally when the errdefer uses destroy instead of free.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    node: *Node,
        \\    pub fn grow(self: *Self, alloc: std.mem.Allocator) !void {
        \\        const old_node = self.node;
        \\        self.node = try alloc.create(Node);
        \\        defer alloc.free(old_node);
        \\        errdefer {
        \\            alloc.destroy(self.node);
        \\            self.node = old_node;
        \\        }
        \\        try self.link();
        \\    }
        \\    fn link(self: *Self) !void { _ = self; }
        \\};
        \\const Node = struct {};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
    try std.testing.expectEqualStrings("defer-and-errdefer-free-overlap", problems.items[0].rule_id);
}
