//! `<local>.<field> = &<local>;` then `return <local>;` — the
//! self-referential struct is COPIED on return; the field still
//! holds the original stack address, which is invalid both during
//! and after the copy.  Even when the caller stores the returned
//! value into another `var`, the field points at a now-dead
//! frame.
//!
//! Same family as [[stack-escape]] which catches the canonical
//! `return &local` and `out.field = &local through *T param`
//! shapes.  This rule targets the more subtle "self-pointer set
//! before return-by-value" shape, common when porting C/Rust code
//! where intrusive self-pointers are routine.
//!
//! Detection (per-fn token walk):
//!   1. Skip comptime type-builder fns and fns that don't return.
//!   2. Walk for `<local>.<field> = & <local>;` assignments where
//!      both `<local>` references are the SAME local (a `var` /
//!      `const` declared earlier in this fn — NOT a parameter or
//!      caller-supplied pointer).
//!   3. Find a subsequent `return <local>;` (return-by-value
//!      of the same local).
//!   4. Fire at the self-borrow assignment with a note pointing
//!      at the return site.
//!
//! Conservative: requires the LHS and RHS receivers to be the same
//! single identifier (no `<x>.field.subfield = &<x>` chains; no
//! `out.* = ...` shapes; no transitive self-borrow through a
//! helper).

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

const skipNestedFn = tokens.skipNestedFn;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .self_pointer_in_returned_value)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

const SelfBorrow = struct {
    local_name: []const u8,
    field_name: []const u8,
    /// Token of the `=` in `<local>.<field> = &<local>`.
    eq_token: Ast.TokenIndex,
    /// Token of the local-name in the LHS.
    lhs_name_token: Ast.TokenIndex,
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
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Build the set of fn-local names — params are excluded since
    // `&<param>` is a borrow into caller storage, not a stack
    // self-borrow that dies with this frame.
    const bindings = try cache.localBindings(proto, body);
    var fn_locals: std.StringHashMapUnmanaged(void) = .empty;
    defer fn_locals.deinit(gpa);
    for (bindings.items) |b| {
        if (b.origin == .param) continue;
        try fn_locals.put(gpa, b.name, {});
    }

    var self_borrows: std.ArrayListUnmanaged(SelfBorrow) = .empty;
    defer self_borrows.deinit(gpa);

    // Pass 1: find `<local>.<field> = &<local>;` assignments.
    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Match `<id> . <field> = & <id> ;` — same id on both
        // sides.  Optional leading word boundary.
        if (tags[t] != .identifier) continue;
        if (t > 0 and tags[t - 1] == .period) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .equal) continue;
        if (tags[t + 4] != .ampersand) continue;
        if (t + 5 > last or tags[t + 5] != .identifier) continue;
        const lhs_name = tree.tokenSlice(t);
        const rhs_name = tree.tokenSlice(t + 5);
        if (!std.mem.eql(u8, lhs_name, rhs_name)) continue;
        // Reject if the RHS continues with `.field` — that would
        // be `&<x>.<field>`, a borrow into a sub-field, not the
        // canonical self-borrow.
        if (t + 6 <= last and tags[t + 6] == .period) continue;
        // Reject compound assignments (`==`, `<=`, etc. — the
        // single `=` already excludes those by tag, defensive).
        if (!fn_locals.contains(lhs_name)) continue;
        try self_borrows.append(gpa, .{
            .local_name = lhs_name,
            .field_name = tree.tokenSlice(t + 2),
            .eq_token = t + 3,
            .lhs_name_token = t,
        });
    }

    // Pass 2: for each self-borrow, find a subsequent
    // `return <local>;` of the same local.
    for (self_borrows.items) |sb| {
        const ret_tok = findReturnOfLocal(tags, tree, sb.eq_token + 1, last, sb.local_name) orelse continue;
        try report(gpa, problems, tree, sb, ret_tok);
    }
}

/// Scan `[start, end]` for `return <local> ;` — the bare return-
/// by-value of the named local.  Skips `return &<local>` (that's
/// handled by stack-escape) and `return f(<local>)` (call passes
/// it; not a return-by-value).
fn findReturnOfLocal(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) ?Ast.TokenIndex {
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, end);
            continue;
        }
        if (tags[t] != .keyword_return) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), name)) continue;
        // Must be a bare `return <name>;` — next token is `;` or `,`.
        const after = t + 2;
        if (after > end) continue;
        if (tags[after] != .semicolon and tags[after] != .comma) continue;
        return t + 1;
    }
    return null;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    sb: SelfBorrow,
    ret_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s} = &{s};` sets a self-pointer in a stack-allocated local, then `return {s};` copies `{s}` by value to the caller — the copied struct's `.{s}` field still points at THIS frame's `{s}` (now dead), which the caller will read as a dangling pointer.  Heap-allocate `{s}` (`alloc.create(...)`) so its identity is stable across the return, or restructure to set `self` AFTER the move (e.g. in a separate `bind` step the caller invokes)",
        .{ sb.local_name, sb.field_name, sb.local_name, sb.local_name, sb.local_name, sb.field_name, sb.local_name, sb.local_name },
    );
    errdefer gpa.free(msg);
    const note_label = try std.fmt.allocPrint(gpa, "returned by value here", .{});
    errdefer gpa.free(note_label);
    const ret_start = try Pos.fromTokenStart(tree, ret_tok);
    const ret_end = try Pos.fromTokenEnd(tree, ret_tok);
    const notes_slice = try gpa.alloc(problem_mod.Note, 1);
    errdefer gpa.free(notes_slice);
    notes_slice[0] = .{ .start = ret_start, .end = ret_end, .label = note_label };
    try problems.append(gpa, .{
        .rule_id = "self-pointer-in-returned-value",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, sb.lhs_name_token),
        .end = try Pos.fromTokenEnd(tree, sb.eq_token),
        .message = msg,
        .notes = notes_slice,
    });
}

// ── Tests ──────────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "self-pointer-in-returned-value: canonical self-ref + return fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Foo = struct { val: u32, self: ?*Foo = null };
        \\pub fn make() Foo {
        \\    var f = Foo{ .val = 5 };
        \\    f.self = &f;
        \\    return f;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("self-pointer-in-returned-value", problems.items[0].rule_id);
}

test "self-pointer-in-returned-value: heap-allocated self-ref does NOT fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Foo = struct { val: u32, self: ?*Foo = null };
        \\pub fn make(alloc: std.mem.Allocator) !*Foo {
        \\    const f = try alloc.create(Foo);
        \\    f.* = .{ .val = 5 };
        \\    f.self = f;
        \\    return f;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // `f.self = f` (not `&f`) — RHS is the heap pointer
    // directly, not the address of the local pointer.  No fire.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "self-pointer-in-returned-value: self-ref then no return does NOT fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Foo = struct { val: u32, self: ?*Foo = null };
        \\pub fn configure(out: *Foo) void {
        \\    var f = Foo{ .val = 5 };
        \\    f.self = &f;
        \\    out.* = f;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // The rule's pattern requires `return f;` (bare return-by-value).
    // Out-param assignment via deref is a different shape — left
    // to stack-escape / composite-borrow detection.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "self-pointer-in-returned-value: different locals don't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Foo = struct { val: u32, other: ?*Foo = null };
        \\pub fn link(a: *Foo, b: *Foo) Foo {
        \\    var f = Foo{ .val = 5 };
        \\    _ = a;
        \\    f.other = b;
        \\    return f;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
