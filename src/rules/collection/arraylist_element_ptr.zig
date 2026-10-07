//! ArrayList element-pointer invalidation detector —
//! `const <X> = &<list>.items[<idx>];` borrows a pointer to a specific
//! element in the list's heap-backed storage.  A subsequent
//! receiver-matched `<list>.<mutate>(...)` call may reallocate the
//! backing storage — `<X>` then dangles into freed memory.  A later
//! use of `<X>` (dereference, pass to function, etc.) is a UAF.
//!
//! Same family as [[arraylist-items-slice]] (full-slice borrow) and
//! [[hashmap-getptr-rehash]] — the borrow-then-grow pattern, this time
//! for individual element pointers into ArrayList storage.
//!
//! Real-world: oven-sh/bun#29483 — `enqueueDependencyToRoot` held
//! `&lockfile.buffers.dependencies.items[dep_id]` across a call to
//! `enqueueDependencyWithMainAndSuccessFn`, which internally called
//! `Lockfile.Package.fromNPM` → `buffers.dependencies.ensureUnusedCapacity`.
//! The reallocation freed the old backing buffer; the `dependency.behavior`
//! read that followed was a use-after-poison (ASAN verified).
//! Fix: copy the element to the stack before taking its address.
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Skip comptime type-builder fns and nested fn declarations.
//!   2. Walk the fn body for `const <X> = &<recv>.items[<idx>];`
//!      bindings where `<recv>` is a single identifier.  `const` only;
//!      `var` allows reassignment we don't track.
//!   3. From the binding's `;`, scan forward for the first
//!      `<recv>.<mutate-method>(` at the SAME lexical block depth,
//!      skipping nested blocks and `defer`/`errdefer` statements.
//!   4. After the mutate, scan for the first use of `<X>` in the
//!      binding's enclosing scope and fire on the use site.
//!
//! Mutate-method allowlist (definitely or likely reallocates):
//!   append / appendSlice / appendNTimes / insert / insertSlice /
//!   addOne / addManyAsSlice / addManyAsArray / resize /
//!   clearAndFree / deinit.
//!
//! Deliberately omitted (no-realloc contract):
//!   All `*AssumeCapacity` variants, `ensureTotalCapacity*`,
//!   `ensureUnusedCapacity`, `swapRemove`, `orderedRemove`, `pop`,
//!   `clearRetainingCapacity`.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const skipDeferStmt = tokens.skipDeferStmt;
const matchBrace = tokens.matchBrace;
const matchBracket = tokens.matchBracket;
const findStmtSemicolon = tokens.findStmtSemicolon;
const skipNestedFn = tokens.skipNestedFn;
const findIdentInScope = tokens.findIdentInScope;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .arraylist_element_ptr)) return;
    _ = cache;
    try tokens.forEachFnBody(gpa, tree, problems, checkBody);
}

const Borrow = struct {
    x_name: []const u8,
    recv_name: []const u8,
    name_token: Ast.TokenIndex,
    end_token: Ast.TokenIndex,
};

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var borrows: std.ArrayListUnmanaged(Borrow) = .empty;
    defer borrows.deinit(gpa);

    // Scan for `const X = &recv.items[...]` bindings.
    // Token pattern (8 tokens minimum):
    //   keyword_const  identifier(X)  equal  ampersand
    //   identifier(recv)  period  identifier(items)  l_bracket
    var t: Ast.TokenIndex = first;
    while (t + 7 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_const) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .ampersand) continue;
        if (tags[t + 4] != .identifier) continue;
        if (tags[t + 5] != .period) continue;
        if (tags[t + 6] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 6), "items")) continue;
        if (tags[t + 7] != .l_bracket) continue;

        const x_name = tree.tokenSlice(t + 1);
        const recv_name = tree.tokenSlice(t + 4);

        // Skip to matching `]`; the statement `;` must follow immediately.
        const r_bracket = matchBracket(tags, t + 7, last) orelse continue;
        if (r_bracket + 1 > last) continue;
        if (tags[r_bracket + 1] != .semicolon) continue;

        try borrows.append(gpa, .{
            .x_name = x_name,
            .recv_name = recv_name,
            .name_token = t + 1,
            .end_token = r_bracket + 1,
        });
    }

    for (borrows.items) |b| {
        const mutate_tok = findReceiverMutate(tree, b.end_token + 1, last, b.recv_name) orelse continue;
        const after_semi = findStmtSemicolon(tags, mutate_tok, last) orelse continue;
        const use_tok = findIdentInScope(tree, after_semi + 1, last, b.x_name) orelse continue;
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
        "use of `{s}` after `{s}.{s}(...)` — the element pointer borrowed from `{s}.items[...]` is invalidated; the call may have reallocated the list's backing storage.  Copy the element to the stack before taking its address: `const elem = {s}.items[idx]; const {s} = &elem;`",
        .{ b.x_name, b.recv_name, mutate_method, b.recv_name, b.recv_name, b.x_name },
    );
    errdefer gpa.free(msg);

    const note_label = try std.fmt.allocPrint(
        gpa,
        "element pointer borrowed here from `{s}.items[...]`",
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
        .rule_id = "arraylist-element-ptr",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, use_tok),
        .end = try Pos.fromTokenEnd(tree, use_tok),
        .message = msg,
        .notes = notes,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "arraylist-element-ptr: element ptr then append then use fires" {
    // Pattern from oven-sh/bun#29483: take &list.items[i], then the list
    // grows (invalidating the pointer), then the pointer is used.
    try testing.expectFires(check, "arraylist-element-ptr",
        \\const std = @import("std");
        \\pub fn buggy(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const ptr = &list.items[0];
        \\    try list.append(gpa, 99);
        \\    _ = ptr.*;
        \\}
    );
}

test "arraylist-element-ptr: element ptr used before append does NOT fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const ptr = &list.items[0];
        \\    _ = ptr.*;
        \\    try list.append(gpa, 99);
        \\}
    );
}

test "arraylist-element-ptr: different receiver does NOT fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(a: *std.ArrayList(u32), b: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const ptr = &a.items[0];
        \\    try b.append(gpa, 99);
        \\    _ = ptr.*;
        \\}
    );
}

test "arraylist-element-ptr: insert variant fires" {
    try testing.expectFires(check, "arraylist-element-ptr",
        \\const std = @import("std");
        \\pub fn buggy(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const ptr = &list.items[list.items.len - 1];
        \\    try list.insert(gpa, 0, 42);
        \\    _ = ptr.*;
        \\}
    );
}

test "arraylist-element-ptr: appendAssumeCapacity does NOT fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(list: *std.ArrayList(u32)) void {
        \\    const ptr = &list.items[0];
        \\    list.appendAssumeCapacity(99);
        \\    _ = ptr.*;
        \\}
    );
}

test "arraylist-element-ptr: grow inside errdefer does NOT fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn ok(list: *std.ArrayList(u32), gpa: std.mem.Allocator) !void {
        \\    const ptr = &list.items[0];
        \\    errdefer list.deinit(gpa);
        \\    _ = ptr.*;
        \\}
    );
}
