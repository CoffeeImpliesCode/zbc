//! Arena-slice-into-heap-container detector — a slice allocated
//! through a function-local arena's allocator is passed as data
//! into a container call whose allocator is NOT the arena.  When
//! the arena dies at fn exit (via `defer <A>.deinit()`), the
//! container is left holding a dangling slice into freed memory.
//!
//! Real-world shape:
//!   var arena = std.heap.ArenaAllocator.init(self.gpa);
//!   defer arena.deinit();
//!   const arena_alloc = arena.allocator();
//!   const tokens = try tokenize(arena_alloc, input);  // arena-owned
//!   try self.token_cache.appendSlice(self.gpa, tokens); // ← stored into
//!                                                       //   heap container
//!
//! Complements zbc's existing `arena_escape` rule (caught via
//! return) and `arena_use_after_kill` (caught via post-deinit
//! read).  This rule catches the third escape path: STORE into a
//! longer-lived container during the arena's lifetime.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const query = @import("../../ast/token_query.zig");
const method_names = @import("../../model/method_names.zig");
const problem_mod = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const Atom = query.Atom;
const R = "slice-of-arena-into-heap";

// ── Patterns ────────────────────────────────────────────────

// `ArenaAllocator.init(...)` — appears somewhere in the binding's
// RHS (we don't care about the prefix `std.heap.` etc.).
const arena_init_pattern = &[_]Atom{
    .{ .text = "ArenaAllocator" },
    .{ .tok = .period },
    .{ .text = "init" },
    .paren_args,
};

// `<arena>.allocator()` — exact match (no chain after).  $0 = arena name.
const allocator_call_exact = &[_]Atom{
    .{ .capture = 0 },
    .{ .tok = .period },
    .{ .text = "allocator" },
    .{ .tok = .l_paren },
    .{ .tok = .r_paren },
};

// Store call: `<recv>.<storeMethod>(...)`.
const store_call = &[_]Atom{
    .{ .capture = 0 },
    .{ .tok = .period },
    .{ .capture = 1 },
    .{ .tok = .l_paren },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .slice_of_arena_into_heap)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

const ArenaVar = struct {
    name: []const u8,
};

const AllocHandle = struct {
    name: []const u8,
    arena_name: []const u8,
};

const ArenaSlice = struct {
    name: []const u8,
    arena_name: []const u8,
    name_token: Ast.TokenIndex,
};

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const body_first = tree.firstToken(body);
    const body_last = tree.lastToken(body);

    // Cheap pre-scan: skip fns that don't even mention ArenaAllocator.
    // Avoids the per-fn local.build cost on the long tail of fns
    // that have no arena.
    if (!tokens.hasIdentInRange(tree, body_first, body_last, "ArenaAllocator")) return;

    const bindings = try cache.localBindings(proto, body);

    // Fused pass: classify each binding as arena / handle / slice.
    var arenas: std.ArrayListUnmanaged(ArenaVar) = .empty;
    defer arenas.deinit(gpa);
    var handles: std.ArrayListUnmanaged(AllocHandle) = .empty;
    defer handles.deinit(gpa);
    var slices: std.ArrayListUnmanaged(ArenaSlice) = .empty;
    defer slices.deinit(gpa);

    // Classification precedence (mutually exclusive by early-continue):
    //   Arena   — RHS contains `ArenaAllocator.init(`
    //   Handle  — RHS is exactly `<arena>.allocator()`
    //   Slice   — single call `<handle>.<allocMethod>(...)` OR chained
    //             call `<arena>.allocator().<allocMethod>(...)`.  Both
    //             collapse via CallInfo.lastMethod + isChained.
    for (bindings.items) |b| {
        if (b.origin == .param) continue;
        const rhs_start = b.rhsFirstAfterTry(tags);

        if (query.anyMatchAnywhere(tree, arena_init_pattern, b.rhs_first, b.rhs_last, null)) {
            try arenas.append(gpa, .{ .name = b.name });
            continue;
        }

        if (query.matchExact(tree, allocator_call_exact, rhs_start, b.rhs_last, null)) |m| {
            const arena_name = m.captureText(tree, 0).?;
            if (findArena(arenas.items, arena_name) != null) {
                try handles.append(gpa, .{ .name = b.name, .arena_name = arena_name });
                continue;
            }
        }

        // Slice classification: the outermost method in a chained
        // method-call must be in the alloc-method set.  Receiver is
        // either a known handle (single call) or a known arena
        // (chained `<arena>.allocator().<allocMethod>()`).
        const c = b.asCall() orelse continue;
        const last_method = c.lastMethod() orelse continue;
        if (!method_names.isAllocMethodName(last_method)) continue;
        const arena_name: ?[]const u8 = blk: {
            if (c.isChained()) {
                // Chained: must be `.allocator().<alloc>(...)` on an arena.
                if (c.method == null or !std.mem.eql(u8, c.method.?, "allocator")) break :blk null;
                if (findArena(arenas.items, c.receiver)) |a| break :blk a.name;
                break :blk null;
            }
            // Single call: receiver must be a known handle.
            if (findHandle(handles.items, c.receiver)) |h| break :blk h.arena_name;
            break :blk null;
        };
        if (arena_name) |an| {
            try slices.append(gpa, .{
                .name = b.name,
                .arena_name = an,
                .name_token = b.name_token,
            });
        }
    }

    if (slices.items.len == 0) return;

    // Store calls: scan body for `<recv>.<storeMethod>(...)` whose
    // receiver isn't an arena/handle, and whose later args reference
    // an arena slice.
    const calls = try query.findAllInBody(gpa, tree, store_call, body_first, body_last);
    defer gpa.free(calls);

    var args_buf: std.ArrayListUnmanaged(tokens.ArgRange) = .empty;
    defer args_buf.deinit(gpa);

    for (calls) |c| {
        const method_tok = c.captures[1].?;
        if (!method_names.isContainerStoreMethodName(tree.tokenSlice(method_tok))) continue;
        const recv_name = c.captureText(tree, 0).?;
        if (findArena(arenas.items, recv_name) != null) continue;
        if (findHandle(handles.items, recv_name) != null) continue;
        const lp = method_tok + 1; // l_paren is right after method_tok
        const rp = tokens.matchParen(tags, lp, body_last) orelse continue;
        args_buf.clearRetainingCapacity();
        tokens.splitCallArgs(gpa, tags, lp, rp, &args_buf) catch continue;
        if (args_buf.items.len < 2) continue;
        if (firstArgIsArenaAllocator(tree, args_buf.items[0].start, args_buf.items[0].end, arenas.items, handles.items)) continue;
        var i: usize = 1;
        while (i < args_buf.items.len) : (i += 1) {
            const arg = args_buf.items[i];
            var u: Ast.TokenIndex = arg.start;
            while (u <= arg.end) : (u += 1) {
                if (tags[u] != .identifier) continue;
                const s = findSlice(slices.items, tree.tokenSlice(u)) orelse continue;
                try report(gpa, problems, tree, method_tok, u, s);
                break;
            }
        }
    }
}

fn findArena(arenas: []const ArenaVar, name: []const u8) ?ArenaVar {
    for (arenas) |a| if (std.mem.eql(u8, a.name, name)) return a;
    return null;
}

fn findHandle(handles: []const AllocHandle, name: []const u8) ?AllocHandle {
    for (handles) |h| if (std.mem.eql(u8, h.name, name)) return h;
    return null;
}

fn findSlice(slices: []const ArenaSlice, name: []const u8) ?ArenaSlice {
    for (slices) |s| if (std.mem.eql(u8, s.name, name)) return s;
    return null;
}

fn firstArgIsArenaAllocator(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    arenas: []const ArenaVar,
    handles: []const AllocHandle,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start > end) return false;
    // Bare handle name — `<H>` alone.
    if (start == end and tags[start] == .identifier and
        findHandle(handles, tree.tokenSlice(start)) != null) return true;
    // Inline form — `<A>.allocator()`.
    if (query.matchExact(tree, allocator_call_exact, start, end, null)) |m| {
        return findArena(arenas, m.captureText(tree, 0).?) != null;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    method_tok: Ast.TokenIndex,
    arg_tok: Ast.TokenIndex,
    s: ArenaSlice,
) !void {
    const method = tree.tokenSlice(method_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` (allocated through arena `{s}`) is being stored via `.{s}(...)` into a container whose allocator is NOT the arena — when `{s}` is deinit'd at scope exit, the container will hold a dangling slice",
        .{ s.name, s.arena_name, method, s.arena_name },
    );
    errdefer gpa.free(msg);

    const note_label = try std.fmt.allocPrint(
        gpa,
        "allocated through arena `{s}` here",
        .{s.arena_name},
    );
    errdefer gpa.free(note_label);

    var notes = try gpa.alloc(problem_mod.Note, 1);
    errdefer gpa.free(notes);
    notes[0] = .{
        .start = try Pos.fromTokenStart(tree, s.name_token),
        .end = try Pos.fromTokenEnd(tree, s.name_token),
        .label = note_label,
    };

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, arg_tok),
        .end = try Pos.fromTokenEnd(tree, arg_tok),
        .message = msg,
        .notes = notes,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "arena slice stored into heap container fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    cache: std.ArrayList(u8),
        \\    pub fn parse(self: *Self) !void {
        \\        var arena = std.heap.ArenaAllocator.init(self.gpa);
        \\        defer arena.deinit();
        \\        const arena_alloc = arena.allocator();
        \\        const tokens = try arena_alloc.alloc(u8, 16);
        \\        try self.cache.appendSlice(self.gpa, tokens);
        \\    }
        \\};
    );
}

test "stored into ARENA sub-container doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(gpa: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(gpa);
        \\    defer arena.deinit();
        \\    const arena_alloc = arena.allocator();
        \\    const tokens = try arena_alloc.alloc(u8, 16);
        \\    var sub_list = std.ArrayList(u8).empty;
        \\    try sub_list.appendSlice(arena_alloc, tokens);
        \\}
    );
}

test "inline arena.allocator() form caught" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    cache: std.ArrayList(u8),
        \\    pub fn parse(self: *Self) !void {
        \\        var arena = std.heap.ArenaAllocator.init(self.gpa);
        \\        defer arena.deinit();
        \\        const tokens = try arena.allocator().alloc(u8, 16);
        \\        try self.cache.appendSlice(self.gpa, tokens);
        \\    }
        \\};
    );
}

test "no arena in fn → no work" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(gpa: std.mem.Allocator) !void {
        \\    const tokens = try gpa.alloc(u8, 16);
        \\    var cache = std.ArrayList(u8).empty;
        \\    try cache.appendSlice(gpa, tokens);
        \\}
    );
}

test "dupe through arena handle counts as alloc method" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    names: std.ArrayList([]const u8),
        \\    pub fn parse(self: *Self, input: []const u8) !void {
        \\        var arena = std.heap.ArenaAllocator.init(self.gpa);
        \\        defer arena.deinit();
        \\        const a = arena.allocator();
        \\        const dup = try a.dupe(u8, input);
        \\        try self.names.append(self.gpa, dup);
        \\    }
        \\};
    );
}
