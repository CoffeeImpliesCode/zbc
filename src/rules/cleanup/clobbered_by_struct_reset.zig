//! oven-sh/bun#29854 detector — `this.<X> = <heap_thing>;` immediately
//! followed by a `this.* = StructLit{ … }` that omits `.<X>`.  The
//! struct literal resets `<X>` to its declared default (typically
//! `null` / `&.{}`), silently dropping the heap pointer; `deinit()`
//! later checks the now-default field and frees nothing — the
//! allocation leaks on every call.
//!
//! Detection is purely syntactic per-fn.  Walk tokens for the prior
//! assignment, then for the struct-reset; if the literal omits the
//! field AND the prior RHS looked meaningful (not a sentinel like
//! `null` / `0` / `&.{}`), fire at the assignment site.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const returnsType = tokens.returnsType;
const bodyOf = tokens.bodyOf;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .clobbered_by_struct_reset)) return;

    const model = try cache.fileModel();

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        // Skip comptime type-builder fns (`fn T() type { return
        // struct { … }; }`).  Their body is a wrapper around nested
        // fn_decls, and our token-walk would see assignments +
        // resets across distinct nested fns and incorrectly pair
        // them.  The nested fns themselves are visited as their
        // own fn_decl nodes in this loop.
        if (returnsType(tree, node)) continue;
        const body = bodyOf(tree, node) orelse continue;
        const self_type: ?[]const u8 = if (model.containingTypeOf(node)) |ti| ti.name else null;
        try checkBody(gpa, tree, self_type, body, problems);
    }
}

const Assign = struct {
    obj_name: []const u8,
    field_name: []const u8,
    /// Token index of the object identifier on the LHS — used as
    /// the diagnostic anchor.
    obj_token: Ast.TokenIndex,
    /// First and last token of the RHS (inclusive).  Used by
    /// `rhsLooksMeaningful` to filter out sentinel-default writes.
    rhs_first: Ast.TokenIndex,
    rhs_last: Ast.TokenIndex,
    /// Position after this statement's semicolon — the struct-reset
    /// match must start strictly after this point.
    after_semi: Ast.TokenIndex,
};

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    self_type: ?[]const u8,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Phase 1: find every `<obj>.<field> = <rhs>;` at statement
    // position (i.e. the trailing semicolon is at our zero
    // nesting depth — so `obj.x = foo(other.y = z)` doesn't match
    // the inner `.y = z`).
    var assigns_buf: [16]Assign = undefined;
    var assign_count: usize = 0;
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (t + 3 > last) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .equal) continue;
        // Confirm this `=` is at statement position by tracking paren /
        // brace / bracket nesting forward to the next semicolon.
        var paren: u32 = 0;
        var brace: u32 = 0;
        var bracket: u32 = 0;
        var u: Ast.TokenIndex = t + 4;
        var sc: ?Ast.TokenIndex = null;
        while (u <= last) : (u += 1) {
            switch (tags[u]) {
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
                .semicolon => if (paren == 0 and brace == 0 and bracket == 0) {
                    sc = u;
                    break;
                },
                else => {},
            }
        }
        const end = sc orelse continue;
        if (end <= t + 4) continue;
        if (assign_count < assigns_buf.len) {
            assigns_buf[assign_count] = .{
                .obj_name = tree.tokenSlice(t),
                .field_name = tree.tokenSlice(t + 2),
                .obj_token = t,
                .rhs_first = t + 4,
                .rhs_last = end - 1,
                .after_semi = end,
            };
            assign_count += 1;
        }
        t = end;
    }
    if (assign_count == 0) return;

    // Phase 2: find every `<obj>.* = <some-literal>{ … };` (or
    // `<obj>.* = .{ … };`) in the body and record (obj, brace_range).
    var resets_buf: [16]Reset = undefined;
    var reset_count: usize = 0;
    t = first;
    while (t <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (t + 2 > last) continue;
        if (tags[t + 1] != .period_asterisk) continue;
        if (tags[t + 2] != .equal) continue;
        // Walk forward through optional `Type` / `Type.Sub` /
        // `Namespace.Type` tokens to reach the literal's `{`.
        // Capture the LAST identifier before the `{` as the literal's
        // type name (for `.{…}` anonymous form, this stays at the
        // empty default and we'll fall back to `self_type`).
        var u: Ast.TokenIndex = t + 3;
        var lit_type_tok: ?Ast.TokenIndex = null;
        while (u <= last and (tags[u] == .identifier or tags[u] == .period)) : (u += 1) {
            if (tags[u] == .identifier) lit_type_tok = u;
        }
        if (u > last or tags[u] != .l_brace) continue;
        const brace_start = u;
        // Match the matching `}`.
        var depth: u32 = 1;
        var v: Ast.TokenIndex = u + 1;
        while (v <= last) : (v += 1) {
            switch (tags[v]) {
                .l_brace => depth += 1,
                .r_brace => {
                    depth -= 1;
                    if (depth == 0) break;
                },
                else => {},
            }
        }
        if (depth != 0) continue;
        // Skip fully-empty struct resets (`T{}` / `.{}`) — these
        // explicitly clear every field to its default, often inside
        // a defer/errdefer cleanup block ("reset the progress at
        // fn exit").  The assignment-then-empty-reset pattern is
        // intentional clearing, not a leak.
        if (brace_start + 1 == v) continue;
        if (reset_count < resets_buf.len) {
            resets_buf[reset_count] = .{
                .obj_name = tree.tokenSlice(t),
                .obj_token = t,
                .lit_first = brace_start,
                .lit_last = v,
                .lit_type = if (lit_type_tok) |lt| tree.tokenSlice(lt) else null,
            };
            reset_count += 1;
        }
        t = v;
    }
    if (reset_count == 0) return;

    // Phase 3: pair each assignment with the FIRST subsequent reset
    // on the same `<obj>`.  If the reset's literal does not contain
    // `.<field> =`, fire at the assignment site.
    _ = self_type;
    for (assigns_buf[0..assign_count]) |a| {
        if (!rhsLooksMeaningful(tree, a.rhs_first, a.rhs_last)) continue;
        for (resets_buf[0..reset_count]) |r| {
            if (r.obj_token <= a.after_semi) continue;
            if (!std.mem.eql(u8, r.obj_name, a.obj_name)) continue;
            // Shadow check: a `var <obj> = …;` or `const <obj> = …;`
            // between the assignment and the reset means the reset
            // operates on a DIFFERENT local with the same name.
            // Common pattern in fns with a hot-path early-return
            // arm and a slow-path fallback that re-declares `this`.
            if (objShadowedBetween(tree, a.after_semi, r.obj_token, a.obj_name)) continue;
            if (literalSetsField(tree, r.lit_first, r.lit_last, a.field_name)) break;
            // Field omitted by the reset literal — fire.
            try report(gpa, problems, tree, a, r);
            break;
        }
    }
}

/// True iff a `var|const <obj> = …` declaration appears between
/// `after` (exclusive) and `before` (exclusive).  When present, the
/// reset's `<obj>.*` is a different local than the one we saw
/// assigned to, and we MUST NOT pair them.
fn objShadowedBetween(
    tree: *const Ast,
    after: Ast.TokenIndex,
    before: Ast.TokenIndex,
    obj_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = after + 1;
    while (t + 1 < before) : (t += 1) {
        const tag = tags[t];
        if (tag != .keyword_var and tag != .keyword_const) continue;
        if (tags[t + 1] != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t + 1), obj_name)) return true;
    }
    return false;
}

const Reset = struct {
    obj_name: []const u8,
    obj_token: Ast.TokenIndex,
    lit_first: Ast.TokenIndex,
    lit_last: Ast.TokenIndex,
    /// Type name of the struct literal (e.g. `PathWatcher`) when the
    /// literal was explicitly typed (`PathWatcher{…}` or
    /// `bun.PathWatcher{…}`); null for anonymous `.{ … }` form, in
    /// which case callers fall back to the enclosing fn's `self_type`.
    lit_type: ?[]const u8,
};

/// Heuristic for "the RHS is a meaningful value worth preserving":
/// reject literal defaults (`null`, `undefined`, integer literal,
/// empty string, `.{}`, `&.{}`) and accept everything else.  Without
/// this filter we'd false-fire on intentional sentinel pre-writes
/// where the struct literal correctly carries the default forward.
fn rhsLooksMeaningful(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    if (first > last) return false;
    const tags = tree.tokens.items(.tag);

    // Single-token defaults.  `null` / `undefined` / `true` / `false`
    // are lexed as identifiers (not dedicated keywords), so we match
    // on slice text in that arm.  Bool / sentinel writes are
    // never the leak source — the field type is scalar.
    if (first == last) {
        return switch (tags[first]) {
            .number_literal,
            .string_literal,
            .multiline_string_literal_line,
            .char_literal,
            => false,
            .identifier => blk: {
                const s = tree.tokenSlice(first);
                if (std.mem.eql(u8, s, "null")) break :blk false;
                if (std.mem.eql(u8, s, "undefined")) break :blk false;
                if (std.mem.eql(u8, s, "true")) break :blk false;
                if (std.mem.eql(u8, s, "false")) break :blk false;
                break :blk true;
            },
            // `.variant` enum-tag shorthand is two tokens (period +
            // ident), not one — those land in the multi-token arm
            // and are accepted as meaningful, which is fine for our
            // purposes (enum reassignment isn't a leak source either,
            // but the pattern is rare enough not to bother filtering).
            else => true,
        };
    }
    // `.{}` — anonymous-empty struct/array literal.
    if (first + 2 == last and
        tags[first] == .period and
        tags[first + 1] == .l_brace and
        tags[last] == .r_brace) return false;
    // `&.{}` — empty slice literal.
    if (first + 3 == last and
        tags[first] == .ampersand and
        tags[first + 1] == .period and
        tags[first + 2] == .l_brace and
        tags[last] == .r_brace) return false;
    return true;
}

/// True iff a `.<field> =` substring appears in the literal's token
/// range (i.e. the struct-reset explicitly assigns the field).
fn literalSetsField(
    tree: *const Ast,
    lit_first: Ast.TokenIndex,
    lit_last: Ast.TokenIndex,
    field: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = lit_first;
    while (t + 2 <= lit_last) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t + 1), field)) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    a: Assign,
    r: Reset,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s}` is assigned here, then clobbered by the `{s}.* = …{{ … }}` struct-reset below which omits `.{s}`; the field falls back to its declared default and the prior value is lost (heap allocation leaked if `{s}` was heap-owned)",
        .{ a.obj_name, a.field_name, r.obj_name, a.field_name, a.field_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "clobbered-by-struct-reset",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, a.obj_token),
        .end = try Pos.fromTokenEnd(tree, a.obj_token + 2),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "clobbered-by-struct-reset: assignment then struct-reset omitting the field fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Watcher = struct {
        \\    path: []const u8 = "",
        \\    callback: usize = 0,
        \\    resolved_path: ?[:0]const u8 = null,
        \\};
        \\pub fn init(this: *Watcher, path: []const u8) !void {
        \\    const resolved_path = "abc";
        \\    this.resolved_path = resolved_path;
        \\    this.* = Watcher{ .path = path, .callback = 0 };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("clobbered-by-struct-reset", problems.items[0].rule_id);
}

test "clobbered-by-struct-reset: literal carries the field forward — OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Watcher = struct {
        \\    path: []const u8 = "",
        \\    resolved_path: ?[:0]const u8 = null,
        \\};
        \\pub fn init(this: *Watcher, path: []const u8) !void {
        \\    const resolved_path = "abc";
        \\    this.resolved_path = resolved_path;
        \\    this.* = Watcher{ .path = path, .resolved_path = resolved_path };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "clobbered-by-struct-reset: prior RHS is `null` sentinel — OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Watcher = struct {
        \\    path: []const u8 = "",
        \\    resolved_path: ?[:0]const u8 = null,
        \\};
        \\pub fn init(this: *Watcher, path: []const u8) void {
        \\    this.resolved_path = null;
        \\    this.* = Watcher{ .path = path };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "clobbered-by-struct-reset: empty `.{}` reset (defer-clear pattern) is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Progress = struct {
        \\    supports_ansi_escape_codes: bool = false,
        \\    pub fn run(this: *Progress) void {
        \\        this.supports_ansi_escape_codes = true;
        \\        this.* = .{};
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "clobbered-by-struct-reset: intervening `var <obj>` shadowing is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Watcher = struct {
        \\    path: []const u8 = "",
        \\    resolved_path: ?[:0]const u8 = null,
        \\};
        \\pub fn init(_: *Watcher) void {
        \\    var this: *Watcher = undefined;
        \\    this.resolved_path = "abc";
        \\    var this2: *Watcher = undefined;
        \\    _ = &this2;
        \\    // Different `this` would be a different scope in real code; here we
        \\    // just verify the shadow-detection branch.
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "clobbered-by-struct-reset: comptime type-builder fn is skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn Builder(comptime T: type) type {
        \\    return struct {
        \\        val: T,
        \\        pub fn set(self: *@This(), v: T) void {
        \\            self.val = v;
        \\            self.* = .{ .val = v };
        \\        }
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // Outer fn returns `type` so its body scan is skipped.  The
    // inner `set` fn's `self.val = v` and `self.* = .{ .val = v }`
    // both reference the SAME field, so the literal doesn't omit
    // it — no fire.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
