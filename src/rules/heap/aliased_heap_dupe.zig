//! oven-sh/bun#29910 detector — bitwise-copy "dupe" patterns that alias the
//! source's heap-owned fields.
//!
//! A function returning `T` by value via `var dup = <ptr>.*; ... return
//! dup;` produces a destination that bitwise-aliases the source for
//! every field, including any heap-owned slice/pointer.  When `T` has
//! a flag-paired ownership pattern — a `<X>_allocated: bool` sibling
//! of a slice/pointer field `<X>` — both copies now hold the same
//! heap pointer with `<X>_allocated == true`.  Whichever side's
//! destructor (or in-place free path) runs first turns the other
//! side's `<X>` into a dangling reference; the second destructor
//! double-frees.
//!
//! Detection is purely syntactic — token-walk the fn body for the
//! `var dup = … .*` shape and the `return dup;` shape, then check
//! each flag-owned field of `T` for either a `dup.<X>_allocated =
//! false` reset or a `dup.<X> = …` reassignment.  Unremediated
//! fields fire a diagnostic at the `var dup = …` site.

const std = @import("std");
const Ast = std.zig.Ast;

const file_model = @import("../../model/file_model.zig");
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const testing = @import("../../testing.zig");
const fnProto = tokens.fnProto;
const bodyOf = tokens.bodyOf;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

/// Run the aliased-heap-dupe detector over every fn_decl in `tree`
/// and append any findings to `problems`.  No-op when the invariant
/// is disabled in `config`.
pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .aliased_heap_dupe)) return;

    const model = try cache.fileModel();
    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        try checkFn(gpa, tree, cache, model, node, problems);
    }
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    fn_decl: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    var buf: [1]Ast.Node.Index = undefined;
    const fn_proto = fnProto(tree, &buf, fn_decl) orelse return;
    const return_type = fn_proto.ast.return_type.unwrap() orelse return;
    const self_type: ?[]const u8 = if (model.containingTypeOf(fn_decl)) |ti| ti.name else null;
    const T = stripReturnType(tree, return_type, self_type) orelse return;

    // Collect flag-owned field names on T via inference (any field
    // `X` with a sibling `X_allocated: bool`).  No entries → nothing
    // to check; the dupe pattern isn't hazardous for plain value
    // types.
    const flag_fields = try model.flagOwnedFields(gpa, T);
    defer gpa.free(flag_fields);
    if (flag_fields.len == 0) return;

    const body = bodyOf(tree, fn_decl) orelse return;
    try checkBody(gpa, tree, cache, fn_proto, T, flag_fields, body, problems);
}

/// Upper bound on the `var <dst> = <src>.*` bindings phase 1 records
/// for a single fn body, and therefore on the parallel "was this
/// dup returned?" flags phase 2 fills in.  Bodies with more bitwise
/// copies than this are truncated at the cap; keeping the window
/// fixed-size keeps the whole scan on the stack.
const max_dup_candidates = 8;

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    type_name: []const u8,
    flag_fields: []const []const u8,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);

    // Phase 1: find every `var <dst> = …; … .*;` binding whose RHS
    // ends in `.*` — a bitwise copy from a pointer.  Iterates over
    // local.zig's pre-built bindings instead of re-parsing the
    // var/=/; sequence by hand.
    const bindings = try cache.localBindings(proto, body);
    var dups_buf: [max_dup_candidates]Dup = undefined;
    var dup_count: usize = 0;
    for (bindings.items) |b| {
        if (b.is_const) continue;
        if (b.origin == .param) continue;
        if (tags[b.rhs_last] != .period_asterisk) continue;
        if (dup_count >= dups_buf.len) break;
        // Source identifier when the RHS is a BARE `<ident>.*` —
        // exactly two tokens, identifier then period_asterisk.  Only
        // this shape has an identifiable "source local" we can match
        // against the `<src>.* = undefined` ownership-transfer check.
        const src_name: ?[]const u8 = if (b.rhs_first + 1 == b.rhs_last and
            tags[b.rhs_first] == .identifier)
            tree.tokenSlice(b.rhs_first)
        else
            null;
        // decl_token points at the `var` keyword (one before the name).
        dups_buf[dup_count] = .{
            .dst_name = b.name,
            .src_name = src_name,
            .decl_token = b.name_token - 1,
        };
        dup_count += 1;
    }
    if (dup_count == 0) return;

    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Phase 2: confirm at least one `dup` is RETURNED (the dst name
    // appears immediately after a `return` keyword in the body, with
    // an optional `.<...>` field chain accepted — `return dup;` and
    // `return dup;` only for v1, no `return wrap(dup);` style).
    var returned_buf: [max_dup_candidates]bool = @splat(false);
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] != .keyword_return) continue;
        if (t + 1 > last or tags[t + 1] != .identifier) continue;
        if (t + 2 > last or tags[t + 2] != .semicolon) continue;
        const ret_name = tree.tokenSlice(t + 1);
        for (dups_buf[0..dup_count], 0..) |dup, idx| {
            if (std.mem.eql(u8, dup.dst_name, ret_name)) {
                returned_buf[idx] = true;
            }
        }
    }

    // Phase 3: for each returned dup, check whether each flag-owned
    // field is remediated.  Remediation patterns:
    //   `<dst>.<X>_allocated = false`
    //   `<dst>.<X> = …` (reassign the heap-owning field)
    // Token form: `<ident:dst> period <ident:X or X_allocated> equal`.
    for (dups_buf[0..dup_count], 0..) |dup, idx| {
        if (!returned_buf[idx]) continue;
        // Ownership-transfer remediation: `<src>.* = undefined;` (or
        // explicit `<src>.* = .{}` reset) immediately invalidates the
        // source so the bitwise dupe is a MOVE, not an alias.  The
        // canonical Zig pattern for `takeOwnership(self)`-style
        // functions.  Skip if seen anywhere in the body.
        if (dup.src_name) |src| {
            if (sourceInvalidated(tree, body, src)) continue;
        }
        for (flag_fields) |field| {
            if (fieldRemediated(tree, body, dup.dst_name, field)) continue;
            try report(gpa, problems, tree, dup.decl_token, dup.dst_name, type_name, field);
        }
    }
}

/// True iff the body contains `<src>.* = undefined;` or `<src>.* =
/// <some-other-blank-init>;` somewhere — the explicit ownership-
/// transfer pattern that invalidates the source's fields after a
/// bitwise dupe.  Token form: `identifier(src) period_asterisk equal …`.
fn sourceInvalidated(tree: *const Ast, body: Ast.Node.Index, src_name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), src_name)) continue;
        if (t + 2 > last) continue;
        if (tags[t + 1] != .period_asterisk) continue;
        if (tags[t + 2] != .equal) continue;
        return true;
    }
    return false;
}

fn fieldRemediated(
    tree: *const Ast,
    body: Ast.Node.Index,
    dst_name: []const u8,
    field: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), dst_name)) continue;
        if (t + 3 > last) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        const ident = tree.tokenSlice(t + 2);
        // `<dst>.<field> = …` reassigns the slice/pointer half.
        if (std.mem.eql(u8, ident, field)) {
            if (tags[t + 3] == .equal) return true;
            continue;
        }
        // `<dst>.<field>_allocated = false` clears the flag.
        if (std.mem.startsWith(u8, ident, field) and
            std.mem.endsWith(u8, ident, "_allocated") and
            ident.len == field.len + "_allocated".len)
        {
            if (tags[t + 3] == .equal) return true;
        }
    }
    return false;
}

const Dup = struct {
    dst_name: []const u8,
    /// Source identifier on the RHS, when `var dst = <ident>.*;` was
    /// a bare `<ident>` deref.  Null for more complex RHS shapes
    /// (`var dst = somefn().*;` etc.).  Used to detect ownership-
    /// transfer remediation `<src>.* = undefined;`.
    src_name: ?[]const u8,
    decl_token: Ast.TokenIndex,
};

/// Return the base type name of a function's return type, peeling
/// `?`, `const`, and an error-union prefix (`SomeErrSet!T` → `T`).
/// Returns null for slices / pointers / unrecognised shapes — the
/// dupe pattern only matters for *value-typed* returns (those whose
/// destination must hold its own copy of the source's heap fields).
fn stripReturnType(
    tree: *const Ast,
    type_node: Ast.Node.Index,
    self_type: ?[]const u8,
) ?[]const u8 {
    const first = tree.firstToken(type_node);
    const last = tree.lastToken(type_node);
    const tags = tree.tokens.items(.tag);

    // If the return type is an error union `E!T`, skip past the `!`
    // and resume parsing from there.  The error-set side can be
    // arbitrary (`anyerror`, named set, dotted chain like
    // `bun.JSError`), so we scan for the first top-level `!` and
    // start over after it.
    var start: Ast.TokenIndex = first;
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] == .bang) {
            start = t + 1;
            break;
        }
    }

    t = start;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .keyword_const => continue,
            .l_bracket, .asterisk => return null,
            .identifier, .builtin => break,
            else => return null,
        }
    }
    if (t > last) return null;
    var last_name: ?[]const u8 = null;
    var expecting_ident = true;
    while (t <= last) : (t += 1) {
        const tag = tags[t];
        if (expecting_ident) {
            if (tag == .identifier) {
                const n = tree.tokenSlice(t);
                last_name = if (std.mem.eql(u8, n, "Self")) self_type else n;
                expecting_ident = false;
            } else if (tag == .builtin) {
                const n = tree.tokenSlice(t);
                if (std.mem.eql(u8, n, "@This")) {
                    last_name = self_type;
                    expecting_ident = false;
                } else return null;
            } else return null;
        } else {
            if (tag == .period) {
                expecting_ident = true;
            } else break;
        }
    }
    return last_name;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    tok: Ast.TokenIndex,
    dst_name: []const u8,
    type_name: []const u8,
    field: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "bitwise copy `var {s} = …` aliases `{s}.{s}` (heap-owned per the `{s}_allocated` flag); without an independent dupe of `{s}` or clearing `{s}.{s}_allocated`, both sides will free the same pointer",
        .{ dst_name, type_name, field, field, field, dst_name, field },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "aliased-heap-dupe",
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, tok),
        .end = Pos.fromTokenEnd(tree, tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "aliased-heap-dupe: shallow dupe of flag-paired struct fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Blob = struct {
        \\    content_type: []const u8 = "",
        \\    content_type_allocated: bool = false,
        \\    pub fn dupe(this: *const Blob) Blob {
        \\        var d = this.*;
        \\        return d;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("aliased-heap-dupe", problems.items[0].rule_id);
}

test "aliased-heap-dupe: clearing the flag is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Blob = struct {
        \\    content_type: []const u8 = "",
        \\    content_type_allocated: bool = false,
        \\    pub fn dupe(this: *const Blob) Blob {
        \\        var d = this.*;
        \\        d.content_type_allocated = false;
        \\        return d;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "aliased-heap-dupe: re-allocating the field is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Blob = struct {
        \\    content_type: []const u8 = "",
        \\    content_type_allocated: bool = false,
        \\    pub fn dupe(this: *const Blob, a: std.mem.Allocator) Blob {
        \\        var d = this.*;
        \\        d.content_type = a.dupe(u8, this.content_type) catch unreachable;
        \\        return d;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "aliased-heap-dupe: type without flag-pair fields doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Plain = struct {
        \\    a: u32 = 0,
        \\    b: u32 = 0,
        \\    pub fn dupe(this: *const Plain) Plain {
        \\        var d = this.*;
        \\        return d;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "aliased-heap-dupe: `<src>.* = undefined` ownership transfer is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Blob = struct {
        \\    content_type: []const u8 = "",
        \\    content_type_allocated: bool = false,
        \\    pub fn takeOwnership(self: *Blob) Blob {
        \\        var result = self.*;
        \\        self.* = undefined;
        \\        return result;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
