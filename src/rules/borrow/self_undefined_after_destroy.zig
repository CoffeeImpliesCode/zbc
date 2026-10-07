//! `<alloc>.destroy(<X>);` immediately followed by a write through
//! `<X>` — `<X>.* = ...;` or `<X>.<field> = ...;`.  Inverted
//! TigerStyle invariant: correct order is overwrite-THEN-free.
//!
//! Real-world: tigerbeetle/tigerbeetle#2687.
//!
//! Rewritten via the query DSL: declarative bind-then-write-via-X
//! pattern, scoped to skip defer/errdefer.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const query = @import("../../ast/token_query.zig");
const problem = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const Atom = query.Atom;
const R = "self-undefined-after-destroy";

// Pattern: `.destroy($X)` or `.free($X)` — preceded by `.` so we
// require the receiver-method shape, slot 0 captures X.
const destroy_or_free = &[_]Atom{
    .{ .tok = .period },
    .{ .pred = isDestroyOrFree },
    .{ .tok = .l_paren },
    .{ .capture = 0 },
    .{ .tok = .r_paren },
};

// Pattern: write through X — `$X.* = ...` or `$X.<field> = ...`.
// Disjunction expresses the two write forms in a single pattern.
const write_through_x = &[_]Atom{
    .{ .ref = 0 },
    .{ .any_of = &[_][]const Atom{
        &[_]Atom{ .{ .tok = .period_asterisk }, .{ .tok = .equal } },
        &[_]Atom{ .{ .tok = .period }, .{ .tok = .identifier }, .{ .tok = .equal } },
    } },
};

// Pattern: rebinding of X — stops the scan.  `$X = ...` (no leading `.`).
const rebind_x = &[_]Atom{
    .{ .ref = 0 },
    .{ .tok = .equal },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    if (!config_mod.isEnabled(config, .self_undefined_after_destroy)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    const destroys = try query.findAllInBodySkippingDefer(gpa, tree, destroy_or_free, first, last);
    defer gpa.free(destroys);

    for (destroys) |d| {
        // Defensive: skip `<X>.destroy(<X>)` nonsense — receiver
        // identifier just before the `.` equals the capture.
        if (d.start >= 1) {
            const before = d.start - 1;
            const tags = tree.tokens.items(.tag);
            if (tags[before] == .identifier and
                std.mem.eql(u8, tree.tokenSlice(before), tree.tokenSlice(d.captures[0].?)))
                continue;
        }
        // Look for `<X>.* = ...` or `<X>.<field> = ...` (single
        // disjunction pattern), OR a rebinding `<X> = ...` that
        // ends the scan.
        const after = d.end + 1;
        const reb = query.findInSameScope(tree, rebind_x, after, last, &d);
        const write = query.findInSameScope(tree, write_through_x, after, last, &d) orelse continue;
        // If the rebind is BEFORE the write, treat as rebinding → no fire.
        if (reb) |r| if (r.start < write.start) continue;
        try report(gpa, problems, tree, write.start, d.captures[0].?, d.start + 1);
    }
}

fn isDestroyOrFree(name: []const u8) bool {
    return std.mem.eql(u8, name, "destroy") or std.mem.eql(u8, name, "free");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(problem.Problem),
    tree: *const Ast,
    write_tok: query.TokenIndex,
    x_tok: query.TokenIndex,
    method_tok: query.TokenIndex,
) !void {
    const x_name = tree.tokenSlice(x_tok);
    const method = tree.tokenSlice(method_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "write through `{s}` after `<alloc>.{s}({s})` — the write hits freed memory.  The TigerStyle invariant is overwrite-THEN-free: `{s}.* = undefined; <alloc>.{s}({s});` (not the other order)",
        .{ x_name, method, x_name, x_name, method, x_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try problem.Pos.fromTokenStart(tree, write_tok),
        .end = try problem.Pos.fromTokenEnd(tree, write_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "TigerBeetle inspect.zig pattern fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Inspector = struct {
        \\    allocator: std.mem.Allocator,
        \\    pub fn deinit(inspector: *Inspector) void {
        \\        inspector.allocator.destroy(inspector);
        \\        inspector.* = undefined;
        \\    }
        \\};
    );
}

test "correct order (undefined THEN destroy) doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Inspector = struct {
        \\    allocator: std.mem.Allocator,
        \\    pub fn deinit(inspector: *Inspector) void {
        \\        inspector.* = undefined;
        \\        inspector.allocator.destroy(inspector);
        \\    }
        \\};
    );
}

test "field write after destroy fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const T = struct {
        \\    flag: bool = false,
        \\    pub fn release(self: *T, alloc: std.mem.Allocator) void {
        \\        alloc.destroy(self);
        \\        self.flag = true;
        \\    }
        \\};
    );
}

test "reassignment of X stops the scan" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const T = struct {
        \\    pub fn rebind(self: *T, alloc: std.mem.Allocator) !void {
        \\        alloc.destroy(self);
        \\        var self_new = try alloc.create(T);
        \\        _ = self_new;
        \\    }
        \\};
    );
}

test "destroy inside defer is skipped" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const T = struct {
        \\    pub fn work(self: *T, alloc: std.mem.Allocator) void {
        \\        defer alloc.destroy(self);
        \\        self.* = .{};
        \\    }
        \\};
    );
}
