//! ArrayList items-slice rehash detector — `const <X> = <list>.items;`
//! borrows a slice over the list's heap-backed storage.  A
//! subsequent receiver-matched `<list>.<mutate>(...)` call may
//! reallocate the backing storage (when the new length exceeds
//! capacity) — `<X>.ptr` then dangles into freed memory.  A later
//! read or write through `<X>` is a UAF against list storage.
//!
//! Same family as [[hashmap-getptr-rehash]] — the borrow-then-
//! mutate pattern, this time against `std.ArrayList` / `ArrayListUnmanaged`
//! / `BoundedArray`-shaped APIs.  ArrayList's docs explicitly warn
//! that the `.items` slice is invalidated by any capacity-modifying
//! call.
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Skip comptime type-builder fns.
//!   2. Walk the fn body for `const <X> = <recv>.items;` bindings
//!      where `<recv>` is a single identifier.  `const` only; var
//!      allows reassignment we don't track.
//!   3. From the binding's `;`, scan forward for the first
//!      `<recv>.<mutate-method>(` at the SAME lexical block depth,
//!      skipping nested blocks (catch/if/loop bodies — they don't
//!      always execute) and `defer`/`errdefer` statements
//!      (deferred, not inline).
//!   4. After the mutate, scan for the first use of `<X>` in the
//!      binding's enclosing scope and fire on the use site.
//!
//! Mutate-method allowlist (definitely or likely reallocates):
//!   append / appendSlice / appendNTimes / insert / insertSlice /
//!   addOne / addManyAsSlice / addManyAsArray / resize /
//!   clearAndFree / deinit.
//!
//! Deliberately omitted:
//!   - All `*AssumeCapacity` variants — explicit no-realloc contract.
//!   - `ensureTotalCapacity*` / `ensureUnusedCapacity` — typically
//!     pre-allocation idiom (called BEFORE borrow); FPs would
//!     outweigh real-bug yield.
//!   - `swapRemove` / `orderedRemove` / `pop` — don't reallocate.
//!     The borrowed slice's `.ptr` remains valid (only `.len`
//!     becomes stale, which doesn't UAF).
//!   - `clearRetainingCapacity` — no realloc.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const testing = @import("../../testing.zig");
const skipDeferStmt = tokens.skipDeferStmt;
const matchBrace = tokens.matchBrace;
const findStmtSemicolon = tokens.findStmtSemicolon;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .arraylist_items_slice)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

const Borrow = struct {
    x_name: []const u8,
    recv_name: []const u8,
    name_token: Ast.TokenIndex,
    /// Token of the binding's terminating `;`.
    end_token: Ast.TokenIndex,
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
    const last = tree.lastToken(body);

    const bindings = try cache.localBindings(proto, body);

    var borrows: std.ArrayListUnmanaged(Borrow) = .empty;
    defer borrows.deinit(gpa);

    // Find `const X = <recv>.items;` bindings.  local.zig classifies
    // `<recv>.<field>` (no parens after) as .field_access when the
    // RHS is exactly that 2-segment chain — perfect fit.  Single-
    // identifier receiver enforced by chain_len == 2 (i.e. only one
    // period between receiver and field) implicit in .field_access.
    for (bindings.items) |b| {
        if (!b.is_const) continue;
        if (b.origin == .param) continue;
        const fa = switch (b.origin) {
            .field_access => |x| x,
            else => continue,
        };
        if (!std.mem.eql(u8, fa.field, "items")) continue;
        try borrows.append(gpa, .{
            .x_name = b.name,
            .recv_name = fa.receiver,
            .name_token = b.name_token,
            .end_token = b.rhs_last + 1, // the `;`
        });
    }

    for (borrows.items) |b| {
        const mutate_tok = findReceiverMutate(tree, b.end_token + 1, last, b.recv_name) orelse continue;
        const after_mutate = findStmtSemicolon(tags, mutate_tok, last) orelse continue;
        const use_tok = findIdentUse(tree, after_mutate + 1, last, b.x_name) orelse continue;
        try report(gpa, problems, tree, b, mutate_tok, use_tok);
    }
}

fn isMutateMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "append") or
        std.mem.eql(u8, name, "appendSlice") or
        std.mem.eql(u8, name, "appendNTimes") or
        std.mem.eql(u8, name, "insert") or
        std.mem.eql(u8, name, "insertSlice") or
        std.mem.eql(u8, name, "addOne") or
        std.mem.eql(u8, name, "addManyAsSlice") or
        std.mem.eql(u8, name, "addManyAsArray") or
        std.mem.eql(u8, name, "resize") or
        std.mem.eql(u8, name, "clearAndFree") or
        std.mem.eql(u8, name, "deinit");
}

/// Scan `[start, last]` for the first `<recv>.<mutate-method>(` at
/// the binding's lexical scope.  Stops at the enclosing scope's
/// closing `}`; skips nested blocks (deeper-scope mutates don't
/// always execute); skips `defer`/`errdefer` statements (deferred).
fn findReceiverMutate(
    tree: *const Ast,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    recv: []const u8,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (start > last) return null;
    var t: Ast.TokenIndex = start;
    while (t + 3 <= last) : (t += 1) {
        if (tags[t] == .l_brace) {
            t = matchBrace(tags, t, last) orelse return null;
            continue;
        }
        if (tags[t] == .r_brace) return null;
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            t = skipDeferStmt(tags, t, last) orelse return null;
            continue;
        }
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        if (isMutateMethodName(tree.tokenSlice(t + 2))) return t + 2;
    }
    return null;
}

/// Find the first identifier whose text equals `name` within the
/// binding's enclosing scope (bounded by the scope's closing `}`).
const findIdentUse = tokens.findIdentInScope;

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    b: Borrow,
    mutate_tok: Ast.TokenIndex,
    use_tok: Ast.TokenIndex,
) !void {
    const mutate_method = tree.tokenSlice(mutate_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "use of `{s}` after `{s}.{s}(...)` — the slice borrowed from `{s}.items` was invalidated; the call may have reallocated the list's backing storage",
        .{ b.x_name, b.recv_name, mutate_method, b.recv_name },
    );
    errdefer gpa.free(msg);

    const note_label = try std.fmt.allocPrint(
        gpa,
        "borrowed here via `{s}.items`",
        .{b.recv_name},
    );
    errdefer gpa.free(note_label);

    var notes = try gpa.alloc(problem_mod.Note, 1);
    errdefer gpa.free(notes);
    notes[0] = .{
        .start = try Pos.fromTokenStart(tree, b.name_token),
        .end = try Pos.fromTokenEnd(tree, b.name_token),
        .label = note_label,
    };

    try problems.append(gpa, .{
        .rule_id = "arraylist-items-slice",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, use_tok),
        .end = try Pos.fromTokenEnd(tree, use_tok),
        .message = msg,
        .notes = notes,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "arraylist-items-slice: items then append then use fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn buggy(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const items = list.items;
        \\    try list.append(gpa, 1);
        \\    items[0] = 99;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("arraylist-items-slice", problems.items[0].rule_id);
}

test "arraylist-items-slice: use before append doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn ok(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const items = list.items;
        \\    items[0] = 99;
        \\    try list.append(gpa, 1);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "arraylist-items-slice: different receiver doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn ok(a: *std.ArrayList(u32), b: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const items = a.items;
        \\    try b.append(gpa, 1);
        \\    items[0] = 99;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "arraylist-items-slice: appendSlice / insert variants caught" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn buggy(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const items = list.items;
        \\    try list.appendSlice(gpa, &.{ 1, 2, 3 });
        \\    items[0] = 99;
        \\}
        \\pub fn buggy2(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const items = list.items;
        \\    try list.insert(gpa, 0, 99);
        \\    items[0] = 99;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 2), problems.items.len);
}

test "arraylist-items-slice: appendAssumeCapacity does NOT fire (no realloc by contract)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn ok(list: *std.ArrayList(u32)) void {
        \\    const items = list.items;
        \\    list.appendAssumeCapacity(99);
        \\    items[0] = 99;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "arraylist-items-slice: ensureUnusedCapacity does NOT fire (pre-alloc idiom)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn ok(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const items = list.items;
        \\    try list.ensureUnusedCapacity(gpa, 10);
        \\    items[0] = 99;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "arraylist-items-slice: mutate inside errdefer is skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn ok(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const items = list.items;
        \\    errdefer list.deinit(gpa);
        \\    items[0] = 99;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "arraylist-items-slice: mutate inside catch block is skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn ok(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const items = list.items;
        \\    doSomething() catch {
        \\        list.deinit(gpa);
        \\        return;
        \\    };
        \\    items[0] = 99;
        \\}
        \\fn doSomething() !void {}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "arraylist-items-slice: shadowed loop capture in sibling scope doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn ok(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    while (list.items.len > 0) {
        \\        const items = list.items;
        \\        _ = items[0];
        \\        try list.append(gpa, 1);
        \\    }
        \\    var arr: [3]u32 = .{ 1, 2, 3 };
        \\    for (arr[0..]) |items| {
        \\        _ = items;
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
