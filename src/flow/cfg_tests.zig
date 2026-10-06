//! Tests for cfg.zig (extracted to keep cfg.zig itself navigable).
//!
//! Owns the parseAndLower scaffolding because the test bundle's
//! TestBundle struct wraps the source-z buffer + tree + cfg lifetime —
//! production code never needs these.

const std = @import("std");
const Ast = std.zig.Ast;

const cfg_mod = @import("cfg.zig");
const cfg_builder = @import("cfg_builder.zig");

const Cfg = cfg_mod.Cfg;
const BlockId = cfg_mod.BlockId;
const LocalId = cfg_mod.LocalId;
const SrcPos = cfg_mod.SrcPos;
const StmtKind = cfg_mod.StmtKind;
const ExprKind = cfg_mod.ExprKind;
const lowerFunction = cfg_builder.lowerFunction;

// ── Tests ──────────────────────────────────────────────────

/// Test bundle returned by `parseAndLower`.  Owns src_z so name
/// slices in cfg.locals (which point into tree.source = src_z) stay
/// valid for the bundle's lifetime.  Pre-phase-20 src_z was freed
/// on parseAndLower's return, which dangled the names — tests that
/// inspected names saw garbage.
const TestBundle = struct {
    src_z: [:0]u8,
    tree: Ast,
    cfg: ?Cfg,

    fn deinit(self: *TestBundle, gpa: std.mem.Allocator) void {
        if (self.cfg) |*c| c.deinit(gpa);
        self.tree.deinit(gpa);
        gpa.free(self.src_z);
    }
};

fn parseAndLower(gpa: std.mem.Allocator, src: []const u8) !TestBundle {
    const src_z = try gpa.dupeSentinel(u8, src, 0);
    errdefer gpa.free(src_z);
    var tree = try Ast.parse(gpa, src_z, .zig);
    errdefer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) == .fn_decl) {
            const cfg = try lowerFunction(gpa, &tree, node);
            return .{ .src_z = src_z, .tree = tree, .cfg = cfg };
        }
    }
    return .{ .src_z = src_z, .tree = tree, .cfg = null };
}

test "lower trivial fn — entry block + return" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // 2 blocks: entry (with ret) and the dead post-return block.
    try std.testing.expectEqual(@as(usize, 2), cfg.blocks.len);
    try std.testing.expectEqual(@as(usize, 1), cfg.blocks[0].stmts.len);
    try std.testing.expect(cfg.blocks[0].stmts[0].kind == .ret);
}

test "lower fn with var decl + arena init + deinit" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\const std = @import("std");
        \\pub fn foo() void {
        \\    var arena = std.heap.ArenaAllocator.init(undefined);
        \\    arena.deinit();
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // 2 blocks (entry + dead post-return); entry has 3 stmts: decl,
    // arena_kill, ret.
    try std.testing.expectEqual(@as(usize, 2), cfg.blocks.len);
    const stmts = cfg.blocks[0].stmts;
    try std.testing.expectEqual(@as(usize, 3), stmts.len);

    try std.testing.expect(stmts[0].kind == .decl);
    try std.testing.expect(stmts[0].kind.decl.init_kind == .arena_init);

    try std.testing.expect(stmts[1].kind == .arena_kill);
    // Receiver local should be the same as the declared local.
    try std.testing.expectEqual(stmts[0].kind.decl.local, stmts[1].kind.arena_kill.arena_local);

    try std.testing.expect(stmts[2].kind == .ret);
}

test "lower fn with return of borrowed identifier" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() u32 {
        \\    var x = bar();
        \\    return x;
        \\}
        \\fn bar() u32 { return 0; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    const stmts = cfg.blocks[0].stmts;
    // decl x, use x (emitted before the ret), ret x.
    try std.testing.expectEqual(@as(usize, 3), stmts.len);
    try std.testing.expect(stmts[0].kind == .decl);
    try std.testing.expect(stmts[1].kind == .use);
    try std.testing.expect(stmts[2].kind == .ret);
    try std.testing.expect(stmts[2].kind.ret.value_kind == .copy_of);
    try std.testing.expectEqual(stmts[0].kind.decl.local, stmts[2].kind.ret.value_kind.copy_of);
    try std.testing.expectEqual(stmts[0].kind.decl.local, stmts[1].kind.use.local);
}

test "if-statement creates fork: 3 blocks (entry, then, merge)" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) void {
        \\    if (x) return;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Entry, then-branch, merge.  No else (single-armed if).
    try std.testing.expect(cfg.blocks.len >= 3);
    // Entry block has 2 successors (then + merge).
    try std.testing.expectEqual(@as(usize, 2), cfg.blocks[0].successors.len);
}

test "if-else creates fork: 4 blocks (entry, then, else, merge)" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) void {
        \\    if (x) return else return;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    try std.testing.expect(cfg.blocks.len >= 4);
    try std.testing.expectEqual(@as(usize, 2), cfg.blocks[0].successors.len);
}

test "for loop creates back-edge: body → header" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(items: []const u32) void {
        \\    for (items) |x| { _ = x; }
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;
    // entry, header, body, merge (minimum 4 blocks).
    try std.testing.expect(cfg.blocks.len >= 4);
}

test "switch creates N-way fork (3 cases → 4+ blocks)" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: u32) void {
        \\    switch (x) {
        \\        0 => return,
        \\        1 => return,
        \\        else => return,
        \\    }
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;
    // entry + 3 case-blocks + merge = 5 blocks min.
    try std.testing.expect(cfg.blocks.len >= 5);
    // entry has 3 successors (one per case).
    try std.testing.expectEqual(@as(usize, 3), cfg.blocks[0].successors.len);
}

test "while loop creates back-edge: body → header" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) void {
        \\    while (x) {}
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // header block has 2 successors (body, merge); body block has 1
    // successor (back to header).  At minimum we expect 4 blocks:
    // entry, header, body, merge.
    try std.testing.expect(cfg.blocks.len >= 4);
}

test "errdefer kill doesn't pollute success-return defer flush" {
    // errdefer arena.deinit() must NOT fire on a plain `return` —
    // otherwise the (returned-value) origin check would see arena
    // already-killed and wrongly flag the return.
    //
    // NOTE: parseAndLower picks the FIRST fn_decl, so `foo` must lead.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var arena = Arena.init(0);
        \\    errdefer arena.deinit();
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Scan every block's stmts: no `.arena_kill` should appear before
    // the `.ret`.  (Without the defer/errdefer split, errdefer's kill
    // would have been replayed at the return site.)
    var saw_kill_before_ret = false;
    var saw_ret = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            switch (s.kind) {
                .arena_kill => if (!saw_ret) {
                    saw_kill_before_ret = true;
                },
                .ret => saw_ret = true,
                else => {},
            }
        }
    }
    try std.testing.expect(!saw_kill_before_ret);
}

test "plain defer DOES fire on return — kill visible before ret stmt" {
    // Symmetric to the errdefer test: a normal `defer` must still
    // replay at every return so the analyzer sees its side effects.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var arena = Arena.init(0);
        \\    defer arena.deinit();
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_kill = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) saw_kill = true;
        }
    }
    try std.testing.expect(saw_kill);
}

test "errdefer DOES fire on `return err` from a catch capture" {
    // `errdefer arena.deinit()` must be replayed when the function
    // returns an error value — here `return err` re-raises the captured
    // error from `catch |err|`.  Before the fix, only literal
    // `return error.X` was recognised, so this `.arena_kill` was
    // silently dropped (the errdefer-double-free-on-error-return FN).
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() !void {
        \\    var arena = Arena.init(0);
        \\    errdefer arena.deinit();
        \\    sideEffect() catch |err| {
        \\        return err;
        \\    };
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\pub fn sideEffect() !void {}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // The errdefer's `arena.deinit()` (→ .arena_kill) must be replayed
    // on the `return err` path.  The trailing `return;` is a success
    // return and must NOT replay it — so exactly one kill appears.
    var kill_count: usize = 0;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) kill_count += 1;
        }
    }
    try std.testing.expectEqual(@as(usize, 1), kill_count);
}

test "errdefer does NOT fire on a non-error `return` from a catch arm" {
    // Symmetric guard against a false positive: a catch arm that
    // returns a NON-error value (a literal here) is a success return,
    // so the errdefer must stay silent — no `.arena_kill` anywhere.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() !u32 {
        \\    var arena = Arena.init(0);
        \\    errdefer arena.deinit();
        \\    const v: u32 = compute() catch |err| {
        \\        _ = err;
        \\        return 0;
        \\    };
        \\    return v;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\pub fn compute() !u32 { return 1; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_kill = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) saw_kill = true;
        }
    }
    try std.testing.expect(!saw_kill);
}

test "try at statement position creates error-exit sink with defers replayed" {
    // `try call();` — adds an error-exit block reachable from cur.
    // The sink should contain whatever defers were active (here:
    // arena.deinit() from `defer`) and a terminating ret.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() !void {
        \\    var arena = Arena.init(0);
        \\    defer arena.deinit();
        \\    try sideEffect();
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\pub fn sideEffect() !void {}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // After `try`, at least one block must have BOTH an arena_kill
    // (the defer'd deinit) AND a ret — that's the err_exit sink.
    var found_err_sink = false;
    for (cfg.blocks) |b| {
        var has_kill = false;
        var has_ret = false;
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) has_kill = true;
            if (s.kind == .ret) has_ret = true;
        }
        if (has_kill and has_ret) found_err_sink = true;
    }
    try std.testing.expect(found_err_sink);
}

test "catch at statement position forks: success + catch body merge" {
    // `expr catch BODY;` — two paths join at a merge block.  Minimum
    // block count: entry + catch + merge = 3.  (entry also acts as
    // the success-edge source via direct edge to merge.)
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    sideEffect() catch {};
        \\    return;
        \\}
        \\pub fn sideEffect() !void {}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    try std.testing.expect(cfg.blocks.len >= 3);

    // The entry block must have ≥2 successors after catch lowering
    // (one to catch_block, one to merge).
    var multi_succ = false;
    for (cfg.blocks) |b| {
        if (b.successors.len >= 2) multi_succ = true;
    }
    try std.testing.expect(multi_succ);
}

test "catch body side effects visible at merge (kill in catch reaches downstream)" {
    // Arena killed only inside the catch body — at the merge point
    // it should be in the "either-killed-or-alive" state.  The
    // analyzer's join semantics (dead-on-either-side wins) means
    // downstream uses would be flagged.  Here we just verify the
    // arena_kill ends up in some non-entry block.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var arena = Arena.init(0);
        \\    sideEffect() catch { arena.deinit(); };
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\pub fn sideEffect() !void {}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Find an arena_kill — should appear in a non-entry block (the
    // catch_block specifically, but we don't care which).
    var kill_in_non_entry = false;
    for (cfg.blocks, 0..) |b, i| {
        if (i == 0) continue;
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) kill_in_non_entry = true;
        }
    }
    try std.testing.expect(kill_in_non_entry);
}

test "var-decl init `try foo()` adds error-exit sink with defer replayed" {
    // Same shape as the statement-position try test, but the `try`
    // hides inside a var-decl init.  Pre-phase-10 the sink wasn't
    // emitted in this position.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() !void {
        \\    var arena = Arena.init(0);
        \\    defer arena.deinit();
        \\    const x = try sideEffect();
        \\    _ = x;
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\pub fn sideEffect() !u32 { return 0; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var found_err_sink = false;
    for (cfg.blocks) |b| {
        var has_kill = false;
        var has_ret = false;
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) has_kill = true;
            if (s.kind == .ret) has_ret = true;
        }
        if (has_kill and has_ret) found_err_sink = true;
    }
    try std.testing.expect(found_err_sink);
}

test "var-decl init `foo() catch BODY` forks: catch body's kill visible downstream" {
    // `const x = foo() catch { arena.deinit(); 0 };` — the catch
    // body's arena_kill must reach a non-entry block so the join at
    // the post-decl merge sees the kill on one incoming edge.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var arena = Arena.init(0);
        \\    const x = sideEffect() catch blk: {
        \\        arena.deinit();
        \\        break :blk 0;
        \\    };
        \\    _ = x;
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\pub fn sideEffect() !u32 { return 0; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var kill_in_non_entry = false;
    for (cfg.blocks, 0..) |b, i| {
        if (i == 0) continue;
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) kill_in_non_entry = true;
        }
    }
    try std.testing.expect(kill_in_non_entry);
}

test "return position `return try foo()` adds error-exit sink with defer replayed" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() !u32 {
        \\    var arena = Arena.init(0);
        \\    defer arena.deinit();
        \\    return try sideEffect();
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\pub fn sideEffect() !u32 { return 0; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Two distinct blocks should each contain an arena_kill + ret:
    //   - the success-path return block (defer flushed inline)
    //   - the err-exit sink (errdefer + defer flushed)
    var sink_count: u32 = 0;
    for (cfg.blocks) |b| {
        var has_kill = false;
        var has_ret = false;
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) has_kill = true;
            if (s.kind == .ret) has_ret = true;
        }
        if (has_kill and has_ret) sink_count += 1;
    }
    try std.testing.expect(sink_count >= 2);
}

test "return position `return foo() catch BODY` forks and merges into ret" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() u32 {
        \\    return sideEffect() catch 0;
        \\}
        \\pub fn sideEffect() !u32 { return 0; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Catch fork: entry → catch_block + entry → merge; catch_block →
    // merge; merge contains the ret.  At least one block has ≥2
    // successors AND there exists a ret somewhere.
    var multi_succ = false;
    var has_ret_anywhere = false;
    for (cfg.blocks) |b| {
        if (b.successors.len >= 2) multi_succ = true;
        for (b.stmts) |s| {
            if (s.kind == .ret) has_ret_anywhere = true;
        }
    }
    try std.testing.expect(multi_succ);
    try std.testing.expect(has_ret_anywhere);
}

test "assign to known local emits .assign with classified rhs" {
    // `x = src;` — must emit .assign (not lowering_gap) so the analyzer
    // can update x's origin to copy_of(src).  Pre-phase-12 this was a
    // stubbed gap, conservatively collapsing both locals to .plain.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var x: u32 = 0;
        \\    var src: u32 = 1;
        \\    x = src;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var found_assign_copy_of = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .assign and s.kind.assign.rhs_kind == .copy_of) {
                found_assign_copy_of = true;
            }
        }
    }
    try std.testing.expect(found_assign_copy_of);
}

test "assign rhs `try foo()` emits err-exit sink alongside .assign" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() !void {
        \\    var arena = Arena.init(0);
        \\    defer arena.deinit();
        \\    var x: u32 = 0;
        \\    x = try sideEffect();
        \\    _ = x;
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\pub fn sideEffect() !u32 { return 0; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var found_err_sink = false;
    for (cfg.blocks) |b| {
        var has_kill = false;
        var has_ret = false;
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) has_kill = true;
            if (s.kind == .ret) has_ret = true;
        }
        if (has_kill and has_ret) found_err_sink = true;
    }
    try std.testing.expect(found_err_sink);
}

test "assign to field (obj.x = src) emits .field_assign" {
    // Field assignment now goes through .field_assign so the
    // field's origin is tracked separately from the parent local.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var obj: Obj = .{ .x = 0 };
        \\    var src: u32 = 1;
        \\    obj.x = src;
        \\    return;
        \\}
        \\const Obj = struct { x: u32 };
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var found_field_assign = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .field_assign and
                std.mem.eql(u8, s.kind.field_assign.name, "x"))
                found_field_assign = true;
        }
    }
    try std.testing.expect(found_field_assign);
}

test "break inside while adds edge from body to merge" {
    // Without phase 13, `break` fell through to lowering_gap and the
    // body just continued to its back-edge — the analyzer never saw a
    // direct body→merge edge that bypasses the header check.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) void {
        \\    while (x) {
        \\        if (x) break;
        \\    }
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // The merge block exists.  Count how many blocks have an edge to
    // the merge block — pre-phase-13 it was 1 (header→merge only);
    // now it should be ≥2 (header→merge AND a body-side→merge).
    // We don't know merge's exact ID, so iterate: find blocks with
    // ≥2 successors targeting any non-header block, OR count edges
    // landing on each block and assert max ≥2 (header → merge AND
    // break-block → merge).
    var max_incoming: u32 = 0;
    var incoming = try gpa.alloc(u32, cfg.blocks.len);
    defer gpa.free(incoming);
    @memset(incoming, 0);
    for (cfg.blocks) |b| {
        for (b.successors) |s| {
            incoming[@intFromEnum(s)] += 1;
        }
    }
    for (incoming) |c| {
        if (c > max_incoming) max_incoming = c;
    }
    // Header gets ≥2 incoming (entry + body back-edge).  Merge gets
    // ≥2 now (header→merge + break-block→merge).  So we expect at
    // least TWO different blocks with ≥2 incoming edges.
    var ge2_count: u32 = 0;
    for (incoming) |c| if (c >= 2) {
        ge2_count += 1;
    };
    try std.testing.expect(ge2_count >= 2);
}

test "continue inside for adds back-edge from body-mid to header" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(xs: []const u32) void {
        \\    for (xs) |x| {
        \\        if (x == 0) continue;
        \\    }
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Header should have ≥3 incoming edges now: entry, body back-edge,
    // continue back-edge.  Pre-phase-13 it was 2.
    var incoming = try gpa.alloc(u32, cfg.blocks.len);
    defer gpa.free(incoming);
    @memset(incoming, 0);
    for (cfg.blocks) |b| {
        for (b.successors) |s| incoming[@intFromEnum(s)] += 1;
    }
    var max_in: u32 = 0;
    for (incoming) |c| if (c > max_in) {
        max_in = c;
    };
    try std.testing.expect(max_in >= 3);
}

test "break outside loop emits gap (defensive — Zig wouldn't compile)" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    break;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var found = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap and
                std.mem.eql(u8, s.kind.lowering_gap.note, "break-outside-loop"))
                found = true;
        }
    }
    try std.testing.expect(found);
}

test "labeled break: `break :outer` from inner loop targets outer's merge" {
    // Without label resolution, inner break would just exit the inner
    // loop; outer's merge wouldn't get the extra incoming edge.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) void {
        \\    outer: while (x) {
        \\        while (x) {
        \\            if (x) break :outer;
        \\        }
        \\    }
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Find the block reached by `break :outer` — it should be the
    // OUTER merge, which is downstream from outer header.  Heuristic:
    // there must exist a path of length 1 from some block (the break
    // emitter) directly to outer's merge, AND that merge must NOT be
    // the inner header.  Easier check: count blocks with ≥2 incoming
    // edges.  Pre-fix: outer header had 2 (entry + body); outer merge
    // had 1 (header→merge).  Post-fix: outer merge has 2 (header→merge
    // + labeled-break→merge).  So ≥2 blocks with ≥2 incoming.
    var incoming = try gpa.alloc(u32, cfg.blocks.len);
    defer gpa.free(incoming);
    @memset(incoming, 0);
    for (cfg.blocks) |b| {
        for (b.successors) |s| incoming[@intFromEnum(s)] += 1;
    }
    var ge2: u32 = 0;
    for (incoming) |c| if (c >= 2) {
        ge2 += 1;
    };
    // Outer header (≥2), inner header (≥2), outer merge (≥2 only with
    // the labeled-break fix).  Expect at least 3.
    try std.testing.expect(ge2 >= 3);
}

test "labeled continue: `continue :outer` from inner loop targets outer's header" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) void {
        \\    outer: while (x) {
        \\        while (x) {
        \\            if (x) continue :outer;
        \\        }
        \\    }
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Outer header should now have ≥3 incoming: entry + inner-body
    // back-edge through outer body + labeled-continue back-edge.
    var incoming = try gpa.alloc(u32, cfg.blocks.len);
    defer gpa.free(incoming);
    @memset(incoming, 0);
    for (cfg.blocks) |b| {
        for (b.successors) |s| incoming[@intFromEnum(s)] += 1;
    }
    var max_in: u32 = 0;
    for (incoming) |c| if (c > max_in) {
        max_in = c;
    };
    try std.testing.expect(max_in >= 3);
}

test "labeled break to unknown label emits gap (not crash, no false match)" {
    // `break :nope;` inside a loop with no matching label — walks
    // the loop stack, finds nothing, must emit a gap rather than
    // accidentally targeting the innermost loop or crashing.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) void {
        \\    while (x) {
        \\        if (x) break :nope;
        \\    }
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var found = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap and
                std.mem.eql(u8, s.kind.lowering_gap.note, "labeled-break-no-loop"))
                found = true;
        }
    }
    try std.testing.expect(found);
}

test "for-loop capture registered: use of `item` resolves to a tracked local" {
    // Pre-phase-15 `item` was an unknown identifier; the .assign rhs
    // would classify as .unknown.  After capture registration, `item`
    // is a known local and `x = item` should classify as copy_of.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(xs: []const u32) void {
        \\    var x: u32 = 0;
        \\    for (xs) |item| {
        \\        x = item;
        \\    }
        \\    _ = x;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_copy_of = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .assign and s.kind.assign.rhs_kind == .copy_of) {
                saw_copy_of = true;
            }
        }
    }
    try std.testing.expect(saw_copy_of);
}

test "for-loop multiple captures `|item, idx|` both registered" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(xs: []const u32) void {
        \\    var a: u32 = 0;
        \\    var b: usize = 0;
        \\    for (xs, 0..) |item, idx| {
        \\        a = item;
        \\        b = idx;
        \\    }
        \\    _ = a; _ = b;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var copy_of_count: u32 = 0;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .assign and s.kind.assign.rhs_kind == .copy_of) {
                copy_of_count += 1;
            }
        }
    }
    // Both `a = item` and `b = idx` should classify as copy_of.
    try std.testing.expect(copy_of_count >= 2);
}

test "discard capture `|_|` is NOT registered as a local" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(xs: []const u32) void {
        \\    for (xs) |_| {}
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    for (cfg.locals) |l| {
        try std.testing.expect(!std.mem.eql(u8, l.name, "_"));
    }
}

test "while-with-payload `while (opt) |val|` registers capture" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(it: anytype) void {
        \\    var x: u32 = 0;
        \\    while (it.next()) |val| {
        \\        x = val;
        \\    }
        \\    _ = x;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_copy_of = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .assign and s.kind.assign.rhs_kind == .copy_of) {
                saw_copy_of = true;
            }
        }
    }
    try std.testing.expect(saw_copy_of);
}

test "if-optional payload `if (opt) |val|` registers capture" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(opt: ?u32) void {
        \\    var x: u32 = 0;
        \\    if (opt) |val| {
        \\        x = val;
        \\    }
        \\    _ = x;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_copy_of = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .assign and s.kind.assign.rhs_kind == .copy_of) {
                saw_copy_of = true;
            }
        }
    }
    try std.testing.expect(saw_copy_of);
}

test "if-error-union payload `else |err|` registers capture" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(r: anyerror!u32) void {
        \\    var e: anyerror = error.None;
        \\    if (r) |_| {} else |err| {
        \\        e = err;
        \\    }
        \\    _ = e;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_copy_of = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .assign and s.kind.assign.rhs_kind == .copy_of) {
                saw_copy_of = true;
            }
        }
    }
    try std.testing.expect(saw_copy_of);
}

test "switch case payload `.tag => |val|` registers capture" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\const U = union(enum) { a: u32, b: u32 };
        \\pub fn foo(u: U) void {
        \\    var x: u32 = 0;
        \\    switch (u) {
        \\        .a => |val| { x = val; },
        \\        .b => |val| { x = val; },
        \\    }
        \\    _ = x;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var copy_of_count: u32 = 0;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .assign and s.kind.assign.rhs_kind == .copy_of) {
                copy_of_count += 1;
            }
        }
    }
    try std.testing.expect(copy_of_count >= 2);
}

test "switch case payload emits reset_capture to suppress back-edge double-free FPs" {
    // When a switch is inside a while loop, stale field state from a
    // prior iteration would fire spurious double-free/UAF on loop-local
    // resources freed via defer inside the arm.  The fix: emit a
    // reset_capture stmt at the start of each case block, just like
    // while/for loops do for their payload captures.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\const Msg = union(enum) { item: struct { ptr: *u8 } };
        \\pub fn drain(alloc: std.mem.Allocator) !void {
        \\    while (nextMsg()) |msg| {
        \\        switch (msg) {
        \\            .item => |it| {
        \\                defer alloc.destroy(it.ptr);
        \\                try process(it.ptr);
        \\            },
        \\        }
        \\    }
        \\}
        \\fn nextMsg() ?Msg { return null; }
        \\fn process(_: *u8) !void {}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var reset_count: u32 = 0;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .reset_capture) reset_count += 1;
        }
    }
    // Expect at least one reset_capture — one for the switch arm payload `it`,
    // plus one from the while-loop payload `msg`.
    try std.testing.expect(reset_count >= 2);
}

test "catch payload `catch |err|` registers capture (stmt position)" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var e: anyerror = error.None;
        \\    sideEffect() catch |err| { e = err; };
        \\    _ = e;
        \\    return;
        \\}
        \\pub fn sideEffect() !void {}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_copy_of = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .assign and s.kind.assign.rhs_kind == .copy_of) {
                saw_copy_of = true;
            }
        }
    }
    try std.testing.expect(saw_copy_of);
}

test "statement-position labeled block: `break :blk` resolves to block merge" {
    // `blk: { ...; if (x) break :blk; ...; }` — the labeled break
    // must add an edge to the block's merge, not be a no-op gap.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) void {
        \\    blk: {
        \\        if (x) break :blk;
        \\        // some non-trivial body so block isn't elided
        \\        var y: u32 = 0;
        \\        _ = y;
        \\    }
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // The block merge should have ≥2 incoming edges: the break path
    // AND the natural fallthrough from end-of-body.  Pre-phase-17
    // the break emitted a "labeled-break-no-loop" gap and no edge,
    // so merge had at most 1 incoming.
    var incoming = try gpa.alloc(u32, cfg.blocks.len);
    defer gpa.free(incoming);
    @memset(incoming, 0);
    for (cfg.blocks) |b| {
        for (b.successors) |s| incoming[@intFromEnum(s)] += 1;
    }
    var max_in: u32 = 0;
    for (incoming) |c| if (c > max_in) {
        max_in = c;
    };
    try std.testing.expect(max_in >= 2);

    // And NO labeled-break-no-loop gap should remain.
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap) {
                try std.testing.expect(!std.mem.eql(
                    u8,
                    s.kind.lowering_gap.note,
                    "labeled-break-no-loop",
                ));
            }
        }
    }
}

test "labeled block inside loop: break :blk doesn't escape the loop" {
    // `while (x) { blk: { ... break :blk; }; more; }` — break :blk
    // exits ONLY the block, not the loop.  Verify that the loop
    // merge isn't reached by the labeled break.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) void {
        \\    while (x) {
        \\        blk: {
        \\            if (x) break :blk;
        \\            var y: u32 = 0;
        \\            _ = y;
        \\        }
        \\        // this stmt is reachable from the block break.
        \\        var z: u32 = 0;
        \\        _ = z;
        \\    }
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Confirm we built a non-trivial CFG and there's no leftover
    // labeled-break-no-loop gap.
    try std.testing.expect(cfg.blocks.len >= 5);
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap) {
                try std.testing.expect(!std.mem.eql(
                    u8,
                    s.kind.lowering_gap.note,
                    "labeled-break-no-loop",
                ));
            }
        }
    }
}

test "expression-position labeled block: var-decl init `const x = blk: {...}` lowers body" {
    // Side effect inside the labeled-block init (arena.deinit() here)
    // must reach a CFG block — pre-phase-18 the init was opaque, so
    // the deinit call was invisible to the analyzer.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var arena = Arena.init(0);
        \\    const r = blk: {
        \\        arena.deinit();
        \\        break :blk 0;
        \\    };
        \\    _ = r;
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_kill = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) saw_kill = true;
        }
    }
    try std.testing.expect(saw_kill);
}

test "expression-position labeled block: return `return blk: {...}` lowers body" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() u32 {
        \\    var arena = Arena.init(0);
        \\    return blk: {
        \\        arena.deinit();
        \\        break :blk 0;
        \\    };
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_kill = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) saw_kill = true;
        }
    }
    try std.testing.expect(saw_kill);
}

test "expression-position labeled block: `break :blk val` adds edge to merge" {
    // The block has two exit edges — `break :blk 1` and natural
    // fallthrough.  Merge should have ≥2 incoming.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo(x: bool) u32 {
        \\    const r = blk: {
        \\        if (x) break :blk 1;
        \\        break :blk 0;
        \\    };
        \\    return r;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var incoming = try gpa.alloc(u32, cfg.blocks.len);
    defer gpa.free(incoming);
    @memset(incoming, 0);
    for (cfg.blocks) |b| {
        for (b.successors) |s| incoming[@intFromEnum(s)] += 1;
    }
    var max_in: u32 = 0;
    for (incoming) |c| if (c > max_in) {
        max_in = c;
    };
    try std.testing.expect(max_in >= 2);
    // No leftover labeled-break-no-loop gaps.
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap) {
                try std.testing.expect(!std.mem.eql(
                    u8,
                    s.kind.lowering_gap.note,
                    "labeled-break-no-loop",
                ));
            }
        }
    }
}

test "expression-position labeled block: assign `x = blk: {...}` lowers body" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var arena = Arena.init(0);
        \\    var x: u32 = 0;
        \\    x = blk: {
        \\        arena.deinit();
        \\        break :blk 1;
        \\    };
        \\    _ = x;
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var saw_kill = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) saw_kill = true;
        }
    }
    try std.testing.expect(saw_kill);
}

test "destructuring var-decl `const a, const b = pair()` registers both locals" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    const a, const b = pair();
        \\    _ = a; _ = b;
        \\    return;
        \\}
        \\pub fn pair() struct { u32, u32 } { return .{ 0, 1 }; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // TestBundle now owns src_z (phase 20 fix) — name slices stay
    // valid until result.deinit, so we can assert on names directly.
    var saw_a = false;
    var saw_b = false;
    for (cfg.locals) |l| {
        if (std.mem.eql(u8, l.name, "a")) saw_a = true;
        if (std.mem.eql(u8, l.name, "b")) saw_b = true;
    }
    try std.testing.expect(saw_a and saw_b);

    var decl_count: u32 = 0;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .decl) decl_count += 1;
        }
    }
    try std.testing.expect(decl_count >= 2);
}

test "name slices live for the test bundle's lifetime (phase 20 dangle fix)" {
    // Regression guard for the parseAndLower → src_z dangle bug.
    // Pre-phase-20, this assertion saw garbage UTF-8 because the
    // helper freed src_z on return.  If TestBundle ever loses its
    // src_z ownership, this will start printing `name=�...` again.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var unique_local_name_xyz: u32 = 0;
        \\    _ = unique_local_name_xyz;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var found = false;
    for (cfg.locals) |l| {
        if (std.mem.eql(u8, l.name, "unique_local_name_xyz")) found = true;
    }
    try std.testing.expect(found);
}

test "destructuring assign `a, b = pair()` emits .assign for each target" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var a: u32 = 0;
        \\    var b: u32 = 0;
        \\    a, b = pair();
        \\    _ = a; _ = b;
        \\    return;
        \\}
        \\pub fn pair() struct { u32, u32 } { return .{ 0, 1 }; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var assign_count: u32 = 0;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .assign) assign_count += 1;
        }
    }
    // At least 2 from the destructure (could be more from the initial
    // `var a: u32 = 0` decls, but those are .decl not .assign).
    try std.testing.expect(assign_count >= 2);

    // No leftover assign_destructure gap.
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap) {
                try std.testing.expect(!std.mem.eql(
                    u8,
                    s.kind.lowering_gap.note,
                    "assign_destructure",
                ));
            }
        }
    }
}

test "destructure rhs `try pair()` adds err-exit sink" {
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() !void {
        \\    var arena = Arena.init(0);
        \\    defer arena.deinit();
        \\    const a, const b = try pair();
        \\    _ = a; _ = b;
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\pub fn pair() !struct { u32, u32 } { return .{ 0, 1 }; }
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    var found_err_sink = false;
    for (cfg.blocks) |b| {
        var has_kill = false;
        var has_ret = false;
        for (b.stmts) |s| {
            if (s.kind == .arena_kill) has_kill = true;
            if (s.kind == .ret) has_ret = true;
        }
        if (has_kill and has_ret) found_err_sink = true;
    }
    try std.testing.expect(found_err_sink);
}

test "try unwraps inner expression: copy_of(src) preserved through try" {
    // `const y = try src;` — y's origin should be copy_of(src), not
    // .unknown.  Validates classifyExpr's .@\"try\" recursion.
    // (Use a local — fn params aren't registered in name_to_local.)
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() anyerror!u32 {
        \\    const src: anyerror!u32 = 1;
        \\    const y = try src;
        \\    return y;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // Find the decl for `y` and assert its init_kind is .copy_of.
    var found_copy_of = false;
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .decl and s.kind.decl.init_kind == .copy_of) {
                found_copy_of = true;
            }
        }
    }
    try std.testing.expect(found_copy_of);
}

// ── Divergent builtins ─────────────────────────────────────────────────────

test "@panic as statement: creates dead continuation block, no lowering_gap" {
    // The builder replaces `cur` with a fresh block on @panic so subsequent
    // (unreachable) stmts don't pollute the pre-panic abstract state.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    @panic("nope");
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // @panic creates a fresh dead block, so we get entry + dead-continuation
    // (with ret) + dead-post-ret = at least 3 blocks.  Without divergent
    // handling we'd only get 2 (entry has the lowering_gap, then dead-post-ret).
    try std.testing.expect(cfg.blocks.len >= 3);

    // @panic must NOT produce a lowering_gap — it's handled as divergent.
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap) {
                const note = s.kind.lowering_gap.note;
                const is_builtin = std.mem.startsWith(u8, note, "builtin_call");
                try std.testing.expect(!is_builtin);
            }
        }
    }
}

test "@trap as statement: creates dead continuation block, no lowering_gap" {
    // Same divergent treatment as @panic — @trap is listed alongside it
    // in builtinIsDivergent.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    @trap();
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    try std.testing.expect(cfg.blocks.len >= 3);

    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap) {
                const note = s.kind.lowering_gap.note;
                try std.testing.expect(!std.mem.startsWith(u8, note, "builtin_call"));
            }
        }
    }
}

test "unreachable literal: creates dead continuation block, no lowering_gap" {
    // `.unreachable_literal` is handled identically to @panic/@trap:
    // cur is replaced with a fresh block.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    unreachable;
        \\    return;
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    try std.testing.expect(cfg.blocks.len >= 3);

    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap) {
                try std.testing.expect(!std.mem.eql(u8, s.kind.lowering_gap.note, "unreachable_literal"));
            }
        }
    }
}

// ── Nested unlabeled blocks ────────────────────────────────────────────────

test "nested unlabeled block fires scope-bound defer before outer continuation" {
    // A `defer` inside `{ ... }` must fire when the inner block exits,
    // not at the function return.  Concretely: the arena_kill from
    // `defer x.deinit()` inside the nested block appears in the stmt
    // list BETWEEN x's declaration and y's declaration.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn foo() void {
        \\    var x = Arena.init(0);
        \\    {
        \\        defer x.deinit();
        \\    }
        \\    var y = Arena.init(0);
        \\    _ = y;
        \\    return;
        \\}
        \\const Arena = struct {
        \\    pub fn init(_: u32) Arena { return .{}; }
        \\    pub fn deinit(_: *Arena) void {}
        \\};
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // In the (only) non-branching block: decl(x) … arena_kill(x) … decl(y) … ret.
    const stmts = cfg.blocks[0].stmts;
    var first_decl: ?usize = null;
    var kill_pos: ?usize = null;
    var second_decl: ?usize = null;
    for (stmts, 0..) |s, i| {
        switch (s.kind) {
            .decl => {
                if (first_decl == null) first_decl = i else second_decl = i;
            },
            .arena_kill => kill_pos = i,
            else => {},
        }
    }
    // All three must be present.
    try std.testing.expect(first_decl != null);
    try std.testing.expect(kill_pos != null);
    try std.testing.expect(second_decl != null);
    // kill must be between the two decls — fired at inner-block exit, not at fn return.
    try std.testing.expect(kill_pos.? > first_decl.?);
    try std.testing.expect(kill_pos.? < second_decl.?);
}

// ── else-if chains ─────────────────────────────────────────────────────────

test "else-if chain: multi-branch CFG, no lowering_gap for if constructs" {
    // `if/else if/else` is a nested if in the else arm.  lowerIf recurses
    // correctly, producing more blocks than a plain if/else and no lowering_gap.
    const gpa = std.testing.allocator;
    var result = try parseAndLower(gpa,
        \\pub fn classify(x: u32) u32 {
        \\    if (x == 0) {
        \\        return 1;
        \\    } else if (x == 1) {
        \\        return 2;
        \\    } else {
        \\        return 3;
        \\    }
        \\}
        \\
    );
    defer result.deinit(gpa);
    const cfg = result.cfg.?;

    // entry + then_1 + else_1 + merge_1 + then_2 + else_2 + merge_2 = 7,
    // plus dead blocks created at each return.  Conservative lower bound: 6.
    try std.testing.expect(cfg.blocks.len >= 6);

    // Entry must fork into exactly 2 successors (outer if condition).
    try std.testing.expectEqual(@as(usize, 2), cfg.blocks[0].successors.len);

    // No lowering_gap with an "if"-related note — the else-if arm is
    // lowered via recursive lowerIf, not treated as an unknown node.
    for (cfg.blocks) |b| {
        for (b.stmts) |s| {
            if (s.kind == .lowering_gap) {
                const note = s.kind.lowering_gap.note;
                try std.testing.expect(!std.mem.startsWith(u8, note, "if"));
            }
        }
    }
}
