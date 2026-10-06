//! oven-sh/bun#29879 detector — `for (list.items) |h| { h.deinit(); }`
//! inside a destructor where the per-item destroy is missing.
//! When `list` holds heap-allocated pointers (`(*T)`-typed list
//! elements minted via `allocator.create(T)`), the per-iteration
//! `h.deinit()` reclaims the item's fields but the item's own
//! heap descriptor is never freed — every list item leaks.
//!
//! Detection (per fn in {deinit, finalize, destroy} only):
//!   1. Find `for (<expr>) |<h>|` loops (optionally with second
//!      capture for index).
//!   2. Check the loop body has exactly `<h>.deinit();` and NO
//!      `<allocator>.destroy(<h>)` or `.free(<h>)` call.
//!   3. Verify the iterated list's element type is a pointer by
//!      scanning the file source for a field decl whose type
//!      expression contains `(*`.
//!   4. Fire at the loop header.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .destroy_after_deinit_in_loop)) return;

    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |fn_entry| {
        if (!isDestructorName(tree.tokenSlice(fn_entry.name_token))) continue;
        try checkFn(gpa, tree, cache, fn_entry.proto, fn_entry.body, problems);
    }
}

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

    for (bindings.items) |b| {
        if (b.origin != .loop_capture) continue;
        // Find the closing `|` of the capture clause (after name_token,
        // possibly past comma-separated extra captures).
        var v: Ast.TokenIndex = b.name_token + 1;
        while (v <= last and tags[v] != .pipe) : (v += 1) {}
        if (v > last) continue;
        const body_start = v + 1;
        const body_end = findLoopBodyEnd(tags, body_start, last) orelse continue;

        if (!bodyHasDeinit(tree, body_start, body_end, b.name)) continue;
        if (bodyHasDestroyOrFree(tree, body_start, body_end, b.name)) continue;

        // List-shape gate: the iterable expression's trailing identifier
        // (e.g. `element_handlers` in `this.element_handlers.items`) is
        // the name of a pointer-list field.  Binding.rhs_last is the
        // last token of the iterable; the `)` is at rhs_last + 1.
        const list_field_name = lastFieldIdentBefore(tree, b.rhs_last + 1) orelse continue;
        if (!isPointerListField(tree, list_field_name)) continue;
        // Self-destroying deinit skip: if the element type's `deinit`
        // body ALREADY calls `bun.destroy(<self>)` /
        // `<allocator>.destroy(<self>)`, the per-iteration deinit
        // already reclaims the heap descriptor.  Rule's prescription
        // (add an outer destroy) would cause a double-free.
        if (elementTypeDeinitSelfDestroys(tree, cache, list_field_name)) continue;

        // Report at the `for` keyword.  Walk back from name_token to
        // find the enclosing `keyword_for`.
        const for_tok = findEnclosingFor(tags, b.name_token) orelse continue;
        try report(gpa, problems, tree, for_tok, b.name, list_field_name);
    }
}

/// Walk back from a capture-name token to find the enclosing
/// `keyword_for` / `keyword_while` / `keyword_if`.  Stops at the
/// nearest one.
fn findEnclosingFor(tags: []const std.zig.Token.Tag, name_token: Ast.TokenIndex) ?Ast.TokenIndex {
    if (name_token == 0) return null;
    var t: Ast.TokenIndex = name_token - 1;
    while (t > 0) : (t -= 1) {
        if (tags[t] == .keyword_for) return t;
        if (tags[t] == .keyword_while or tags[t] == .keyword_if) return t;
    }
    return null;
}

/// Walk tokens at `start` to find the end of a for-loop's body.
/// If the body opens with `{`, find the matching `}`.  Otherwise
/// find the terminating `;` at our current paren/brace depth.
fn findLoopBodyEnd(
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?Ast.TokenIndex {
    if (start > last) return null;
    if (tags[start] == .l_brace) {
        var depth: u32 = 1;
        var t: Ast.TokenIndex = start + 1;
        while (t <= last) : (t += 1) {
            switch (tags[t]) {
                .l_brace => depth += 1,
                .r_brace => {
                    depth -= 1;
                    if (depth == 0) return t;
                },
                else => {},
            }
        }
        return null;
    }
    var paren: u32 = 0;
    var brace: u32 = 0;
    var bracket: u32 = 0;
    var t: Ast.TokenIndex = start;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_paren => paren += 1,
            .r_paren => if (paren > 0) {
                paren -= 1;
            },
            .l_brace => brace += 1,
            .r_brace => if (brace > 0) {
                brace -= 1;
            },
            .l_bracket => bracket += 1,
            .r_bracket => if (bracket > 0) {
                bracket -= 1;
            },
            .semicolon => if (paren == 0 and brace == 0 and bracket == 0) return t,
            else => {},
        }
    }
    return null;
}

/// True iff the token range `[start, end]` contains a
/// `<capture>.deinit(` call (or related destruction call).
fn bodyHasDeinit(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    capture: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t + 3 <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), capture)) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        const m = tree.tokenSlice(t + 2);
        if (std.mem.eql(u8, m, "deinit") or std.mem.eql(u8, m, "finalize")) return true;
    }
    return false;
}

/// True iff the token range contains a `<x>.destroy(<capture>)`,
/// `<x>.free(<capture>)`, `<x>.destroy(<capture>)` style call.
fn bodyHasDestroyOrFree(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    capture: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t + 4 <= end) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        const m = tree.tokenSlice(t + 1);
        if (!std.mem.eql(u8, m, "destroy") and
            !std.mem.eql(u8, m, "free")) continue;
        if (tags[t + 2] != .l_paren) continue;
        if (tags[t + 3] != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t + 3), capture)) return true;
    }
    return false;
}

/// Walk back from a token to find the most recent `<identifier>`
/// that immediately precedes a `.items` / `.values` / similar
/// projection.  This gives the list field name on a `<obj>.<field>.items`
/// iterable.  Returns null when the shape doesn't match.
fn lastFieldIdentBefore(tree: *const Ast, close_paren: Ast.TokenIndex) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    if (close_paren < 4) return null;
    // The iterable looks like `…<field>.items` (or `.values`,
    // `.slice()`, etc.) — last 3 tokens before `)` should be
    // `<field>` `.` `items`/`.values`.
    if (tags[close_paren - 1] != .identifier) return null;
    if (tags[close_paren - 2] != .period) return null;
    if (tags[close_paren - 3] != .identifier) return null;
    const proj = tree.tokenSlice(close_paren - 1);
    if (!std.mem.eql(u8, proj, "items") and
        !std.mem.eql(u8, proj, "values") and
        !std.mem.eql(u8, proj, "keys")) return null;
    return tree.tokenSlice(close_paren - 3);
}

/// Heuristic: scan the file source for a `<field>:` declaration
/// whose type expression contains `(*` — i.e. the list's element
/// type is a pointer.  Loose but accurate for the canonical
/// `field: std.ArrayListUnmanaged(*T) = .{}` pattern.
/// True iff the field named `field_name` is declared with a list
/// element type whose `deinit` body itself calls
/// `bun.destroy(<self>)` / `<allocator>.destroy(<self>)` — i.e. the
/// deinit is self-destroying.  Adding an outer destroy in the caller
/// would double-free.
///
/// Resolution: scan the field's type expression for the element-
/// type identifier inside the LAST `(...)` (e.g.
/// `ArrayListUnmanaged(*H2.PendingConnect)` → `PendingConnect`).
/// Then use the cross-file project index to find that type's
/// `deinit` method and walk its body for the destroy call.
fn elementTypeDeinitSelfDestroys(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    field_name: []const u8,
) bool {
    const elem_name = elementTypeNameOfField(tree, field_name) orelse return false;
    const rm = cache.findMethodAcrossImports(elem_name, "deinit") orelse return false;
    return methodBodyContainsSelfDestroy(rm.tree, rm.fn_decl);
}

/// Extract the element-type identifier from a field whose type is a
/// list/managed-list/etc. parameterised with a pointer element.
/// Source-scan-based: find the `<field>: ` decl, peel its bounded
/// type-expression slice, return the LAST identifier inside the
/// innermost `(...)` whose preceding `(*` confirms pointer shape.
fn elementTypeNameOfField(tree: *const Ast, field_name: []const u8) ?[]const u8 {
    const src = tree.source;
    var pat_buf: [256]u8 = undefined;
    if (field_name.len + 2 > pat_buf.len) return null;
    @memcpy(pat_buf[0..field_name.len], field_name);
    pat_buf[field_name.len] = ':';
    pat_buf[field_name.len + 1] = ' ';
    const pat = pat_buf[0 .. field_name.len + 2];
    var idx: usize = 0;
    while (std.mem.indexOfPos(u8, src, idx, pat)) |found| {
        if (found > 0 and isIdentByte(src[found - 1])) {
            idx = found + 1;
            continue;
        }
        const type_start = found + pat.len;
        const type_end = fieldTypeExprEnd(src, type_start);
        const slice = src[type_start..type_end];
        // Find a `(*` then walk forward to the next non-ident-non-dot
        // boundary; the LAST identifier in that span is the element
        // type name (handles `*T`, `*lib.T`).
        const star_pos = std.mem.indexOf(u8, slice, "(*") orelse return null;
        var k: usize = star_pos + 2;
        var last_ident_start: usize = 0;
        var in_ident: bool = false;
        var cur_start: usize = 0;
        while (k < slice.len) : (k += 1) {
            const c = slice[k];
            if (isIdentByte(c)) {
                if (!in_ident) {
                    cur_start = k;
                    in_ident = true;
                }
                continue;
            }
            if (in_ident) {
                last_ident_start = cur_start;
                in_ident = false;
                if (c != '.') break;
            }
        }
        const last_ident_end = blk: {
            var j = last_ident_start;
            while (j < slice.len and isIdentByte(slice[j])) : (j += 1) {}
            break :blk j;
        };
        if (last_ident_end <= last_ident_start) return null;
        return slice[last_ident_start..last_ident_end];
    }
    return null;
}

/// True iff the method's body contains `bun.destroy(<self>)` or
/// `<x>.destroy(<self>)` / `<x>.free(<self>)` / `<x>.destroy(@self)`
/// where `<self>` is the method's receiver parameter name.
fn methodBodyContainsSelfDestroy(
    tree: *const Ast,
    declaration: Ast.Node.Index,
) bool {
    const tags = tree.tokens.items(.tag);
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
    var params = proto.iterate(tree);
    const receiver = params.next() orelse return false;
    const recv_name = tree.tokenSlice(receiver.name_token orelse return false);
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    var t = tree.firstToken(body);
    const end = tree.lastToken(body);
    while (t + 3 <= end) : (t += 1) {
        // Pattern A: `bun.destroy(<recv>)` — identifier `bun`,
        // period, `destroy`, `(`, identifier `<recv>`, `)`.
        if (tags[t] == .identifier and t + 4 <= end and
            tags[t + 1] == .period and tags[t + 2] == .identifier and
            tags[t + 3] == .l_paren and tags[t + 4] == .identifier)
        {
            const m = tree.tokenSlice(t + 2);
            if ((std.mem.eql(u8, m, "destroy") or std.mem.eql(u8, m, "free")) and
                std.mem.eql(u8, tree.tokenSlice(t + 4), recv_name))
            {
                return true;
            }
        }
    }
    return false;
}

fn isPointerListField(tree: *const Ast, field_name: []const u8) bool {
    const src = tree.source;
    var pat_buf: [256]u8 = undefined;
    if (field_name.len + 2 > pat_buf.len) return true;
    @memcpy(pat_buf[0..field_name.len], field_name);
    pat_buf[field_name.len] = ':';
    pat_buf[field_name.len + 1] = ' ';
    const pat = pat_buf[0 .. field_name.len + 2];
    var idx: usize = 0;
    while (std.mem.indexOfPos(u8, src, idx, pat)) |found| {
        // Word-boundary check: the byte BEFORE the match must not be
        // an identifier continuation char.  Otherwise `entries: ` would
        // match inside `extra_execution_entries: `, picking up the
        // outer field's type expression instead of the named field's.
        if (found > 0 and isIdentByte(src[found - 1])) {
            idx = found + 1;
            continue;
        }
        // Examine ONLY the bytes belonging to this field's type
        // expression — bounded by the next `,` or `=` (default) or
        // newline at brace-depth 0.  Without the bound, a 120-byte
        // window leaked into adjacent field decls (`entries: ...,
        // afterAll: Managed(*ExecutionEntry),` — the `(*` belongs
        // to afterAll, not entries).
        const type_start = found + pat.len;
        const type_end = fieldTypeExprEnd(src, type_start);
        const slice = src[type_start..type_end];
        if (std.mem.indexOf(u8, slice, "(*") != null) return true;
        if (std.mem.indexOf(u8, slice, "[]*") != null) return true;
        idx = type_start;
    }
    return false;
}

const isIdentByte = tokens.isIdentByte;

/// Find the end of a field's type expression starting at `start`.
/// Stops at the first `,` or `=` at brace/paren/bracket depth 0
/// (the field's own depth — the type expression itself may open
/// parens for generic args like `Managed(T)`).  Caps at 256 bytes
/// so a malformed file doesn't blow the scan out.
fn fieldTypeExprEnd(src: []const u8, start: usize) usize {
    var depth: u32 = 0;
    const limit = @min(start + 256, src.len);
    var i: usize = start;
    while (i < limit) : (i += 1) {
        switch (src[i]) {
            '(', '[', '{' => depth += 1,
            ')', ']', '}' => if (depth > 0) {
                depth -= 1;
            } else return i,
            ',', '=' => if (depth == 0) return i,
            else => {},
        }
    }
    return limit;
}

fn isDestructorName(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "finalize") or
        std.mem.eql(u8, name, "destroy");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    for_tok: Ast.TokenIndex,
    capture: []const u8,
    list_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "loop calls `{s}.deinit()` per element of pointer-list `{s}` but never `<allocator>.destroy({s})` — each item's heap descriptor leaks; add `<allocator>.destroy({s});` after the `.deinit()` call",
        .{ capture, list_name, capture, capture },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "destroy-after-deinit-in-loop",
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, for_tok),
        .end = Pos.fromTokenEnd(tree, for_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "destroy-after-deinit-in-loop: pointer-list loop without destroy fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Handler = struct { pub fn deinit(_: *Handler) void {} };
        \\const Ctx = struct {
        \\    handlers: std.ArrayListUnmanaged(*Handler) = .{},
        \\    pub fn deinit(this: *Ctx) void {
        \\        for (this.handlers.items) |h| {
        \\            h.deinit();
        \\        }
        \\        this.handlers.deinit(std.heap.page_allocator);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("destroy-after-deinit-in-loop", problems.items[0].rule_id);
}

test "destroy-after-deinit-in-loop: loop body includes destroy is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Handler = struct { pub fn deinit(_: *Handler) void {} };
        \\const Ctx = struct {
        \\    handlers: std.ArrayListUnmanaged(*Handler) = .{},
        \\    pub fn deinit(this: *Ctx) void {
        \\        for (this.handlers.items) |h| {
        \\            h.deinit();
        \\            std.heap.page_allocator.destroy(h);
        \\        }
        \\        this.handlers.deinit(std.heap.page_allocator);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "destroy-after-deinit-in-loop: value-typed list is OK (no `(*` in decl)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Handler = struct { pub fn deinit(_: *Handler) void {} };
        \\const Ctx = struct {
        \\    handlers: std.ArrayListUnmanaged(Handler) = .{},
        \\    pub fn deinit(this: *Ctx) void {
        \\        for (this.handlers.items) |*h| {
        \\            h.deinit();
        \\        }
        \\        this.handlers.deinit(std.heap.page_allocator);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "destroy-after-deinit-in-loop: non-destructor fn is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Handler = struct { pub fn deinit(_: *Handler) void {} };
        \\const Ctx = struct {
        \\    handlers: std.ArrayListUnmanaged(*Handler) = .{},
        \\    pub fn cleanupSome(this: *Ctx) void {
        \\        for (this.handlers.items) |h| {
        \\            h.deinit();
        \\        }
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
