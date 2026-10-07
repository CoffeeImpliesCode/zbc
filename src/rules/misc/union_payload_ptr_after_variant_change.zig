//! Union-payload pointer used after the union variant is changed.
//!
//! A pointer is taken into a union's active-variant payload, then the union
//! is reassigned to a different variant, then the pointer is used.  After the
//! reassignment the storage the pointer referenced belongs to the new variant,
//! so the old pointer is dangling / points into repurposed memory.
//!
//! Real-world shape: oven-sh/bun#29977
//!
//!   const pending = &this.state.pending;   // pointer into union payload
//!   this.state = .err;                     // active variant switched
//!   if (pending.dev_server) |server| { … } // UAF: reads repurposed memory
//!
//! Fix: copy the needed fields into locals before reassigning the union:
//!
//!   const dev_server = pending.dev_server;
//!   this.state = .err;
//!   if (dev_server) |server| { … }
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Find `const/var <ptr> = & <recv> . <field1> . <field2>` — a pointer
//!      binding into a union payload (at least 3 levels: recv → field1 → field2,
//!      where field1 is the union field).
//!      Token sequence (t+0..t+8):
//!        keyword_const/var, identifier(ptr), equal, ampersand,
//!        identifier(recv), period, identifier(field1), period, identifier(field2)
//!   2. Find the `;` ending this declaration.
//!   3. From `;+1` to body_end, scan for `identifier(recv) period
//!      identifier(field1) equal` — the variant reassignment.  The `=` is
//!      `.equal` (Zig tokenises `==` as `.equal_equal`), so no extra guard
//!      is needed.  Return the `equal` token.
//!   4. Find the `;` ending the variant assignment.
//!   5. From that `;+1` to body_end, find any identifier use of `ptr`.
//!   6. Fire at the use token.
//!
//! FP suppression: skip when `ptr_name == recv` or when `field1 == field2`.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const findStmtSemicolon = tokens.findStmtSemicolon;
const findIdentInScope = tokens.findIdentInScope;
const skipFnDecl = tokens.skipFnDecl;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "union-payload-ptr-after-variant-change";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .union_payload_ptr_after_variant_change)) return;
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

    var t: Ast.TokenIndex = first;
    while (t + 8 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipFnDecl(tags, t, last);
            continue;
        }

        // Pattern: `const/var <ptr> = & <recv> . <field1> . <field2>`
        //   t+0: keyword_const / keyword_var
        //   t+1: identifier(ptr)
        //   t+2: equal
        //   t+3: ampersand
        //   t+4: identifier(recv)
        //   t+5: period
        //   t+6: identifier(field1)
        //   t+7: period
        //   t+8: identifier(field2)
        if (tags[t] != .keyword_const and tags[t] != .keyword_var) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .ampersand) continue;
        if (tags[t + 4] != .identifier) continue;
        if (tags[t + 5] != .period) continue;
        if (tags[t + 6] != .identifier) continue;
        if (tags[t + 7] != .period) continue;
        if (tags[t + 8] != .identifier) continue;

        const ptr_name = tree.tokenSlice(t + 1);
        const recv = tree.tokenSlice(t + 4);
        const field1 = tree.tokenSlice(t + 6);
        const field2 = tree.tokenSlice(t + 8);

        // FP suppression: skip self-referential or degenerate cases.
        if (std.mem.eql(u8, ptr_name, recv)) continue;
        if (std.mem.eql(u8, field1, field2)) continue;

        // Find the `;` that ends this declaration.
        const decl_sc = findStmtSemicolon(tags, t + 9, last) orelse continue;

        // From decl_sc+1 to last, look for `recv . field1 =` (variant reassignment).
        const assign_eq = findVariantAssign(tree, decl_sc + 1, last, recv, field1) orelse continue;

        // Find the `;` ending the variant assignment.
        const assign_sc = findStmtSemicolon(tags, assign_eq + 1, last) orelse continue;

        // From assign_sc+1 to last, find any use of `ptr`.
        const use_tok = findIdentInScope(tree, assign_sc + 1, last, ptr_name) orelse continue;

        try report(gpa, problems, tree, use_tok, ptr_name, recv, field1, field2);
    }
}

/// Scan `[start, end]` for `recv . field1 =` (plain assignment, not `==`).
/// Returns the `=` token, or null.
fn findVariantAssign(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: []const u8,
    field1: []const u8,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var t: Ast.TokenIndex = start;
    while (t + 3 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field1)) continue;
        // `.equal` is `=`; `.equal_equal` is `==`.  Only match plain `=`.
        if (tags[t + 3] != .equal) continue;
        return t + 3;
    }
    return null;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    use_tok: Ast.TokenIndex,
    ptr_name: []const u8,
    recv: []const u8,
    field1: []const u8,
    field2: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` borrows into `{s}.{s}.{s}` — after `{s}.{s}` is reassigned to a different variant, the payload storage `{s}` points into is repurposed; use of `{s}` is a use-after-free",
        .{ ptr_name, recv, field1, field2, recv, field1, ptr_name, ptr_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, use_tok),
        .end = try Pos.fromTokenEnd(tree, use_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "union-payload-ptr-after-variant-change: pointer then variant change then use fires" {
    try testing.expectFires(check, R,
        \\const Pending = struct { dev_server: ?u32 = null };
        \\const State = union(enum) { pending: Pending, err: u32 };
        \\const Self = struct { state: State };
        \\pub fn buggy(this: *Self) void {
        \\    const pending = &this.state.pending;
        \\    this.state = .{ .err = 1 };
        \\    if (pending.dev_server) |_| {}
        \\}
        \\
    );
}

test "union-payload-ptr-after-variant-change: use before variant change doesn't fire" {
    try testing.expectNoFire(check,
        \\const Pending = struct { dev_server: ?u32 = null };
        \\const State = union(enum) { pending: Pending, err: u32 };
        \\const Self = struct { state: State };
        \\pub fn safe(this: *Self) void {
        \\    const pending = &this.state.pending;
        \\    if (pending.dev_server) |_| {}
        \\    this.state = .{ .err = 1 };
        \\}
        \\
    );
}

test "union-payload-ptr-after-variant-change: no variant change doesn't fire" {
    try testing.expectNoFire(check,
        \\const Pending = struct { dev_server: ?u32 = null };
        \\const State = union(enum) { pending: Pending, err: u32 };
        \\const Self = struct { state: State };
        \\pub fn ok(this: *Self) void {
        \\    const pending = &this.state.pending;
        \\    if (pending.dev_server) |_| {}
        \\}
        \\
    );
}

test "union-payload-ptr-after-variant-change: different field path doesn't fire" {
    try testing.expectNoFire(check,
        \\const Pending = struct { dev_server: ?u32 = null };
        \\const State = union(enum) { pending: Pending, err: u32 };
        \\const Other = union(enum) { x: u32, y: u32 };
        \\const Self = struct { state: State, other: Other };
        \\pub fn ok(this: *Self) void {
        \\    const pending = &this.state.pending;
        \\    this.other = .{ .y = 2 };
        \\    if (pending.dev_server) |_| {}
        \\}
        \\
    );
}
