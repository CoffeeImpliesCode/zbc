//! Multi-step in-place struct-builder pattern that acquires a
//! resource via `try <out>.<field>.<acquire>(...);` (where `<out>`
//! is a local that will be returned, like `result` or `out`), but
//! has a later `try` with no `errdefer` registered to release the
//! acquired field on error.
//!
//! Real-world: ghostty-org/ghostty#10401 — `SharedGrid.init` did
//!
//!   try result.codepoints.ensureTotalCapacity(alloc, 128);
//!   try result.glyphs.ensureTotalCapacity(alloc, 128);
//!   try result.reloadMetrics();           // ← fallible; codepoints
//!                                          //   and glyphs leak on err
//!   return result;
//!
//! The fix interleaves errdefers:
//!
//!   try result.codepoints.ensureTotalCapacity(alloc, 128);
//!   errdefer result.codepoints.deinit(alloc);
//!   try result.glyphs.ensureTotalCapacity(alloc, 128);
//!   errdefer result.glyphs.deinit(alloc);
//!   try result.reloadMetrics();
//!
//! Complements `missing-errdefer-between-tries` (binding-and-leak
//! `const X = try Type.method()` shape) — this rule covers the
//! in-place struct-builder variant where the acquired resource
//! lives in `<out>.<field>` rather than a freshly-bound local.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const query = @import("../../ast/token_query.zig");
const problem_mod = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const method_names = @import("../../model/method_names.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const Atom = query.Atom;
const R = "missing-errdefer-on-out-param";

// `try <out>.<field>.<acquire>(` — predicates filter on `<out>`
// and `<acquire>`; both are captured (slots 1/2) alongside `<field>`
// (slot 0) so the report site uses stable capture indices instead of
// fragile `m.start + N` offset arithmetic.
const acquire_pattern = &[_]Atom{
    .{ .tok = .keyword_try },
    .{ .pred_at = .{ .slot = 1, .pred = isCanonicalOutName } }, // out
    .{ .tok = .period },
    .{ .capture = 0 }, // field
    .{ .tok = .period },
    .{ .pred_at = .{ .slot = 2, .pred = isAcquireMethodName } }, // method
    .{ .tok = .l_paren },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .missing_errdefer_on_out_param)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

const Acquire = struct {
    out_name: []const u8,
    field_name: []const u8,
    method_tok: Ast.TokenIndex,
    /// Token of the `;` that ends the acquire statement.
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
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Cheap pre-scan: no `try` → no leak path → nothing to do.
    if (!tokens.hasTokenInRange(tags, first, last, .keyword_try)) return;

    // Find var-declared canonical-out locals.  Hashed for the
    // per-acquire membership test below.
    const bindings = try cache.localBindings(proto, body);
    var var_outs: std.StringHashMapUnmanaged(void) = .empty;
    defer var_outs.deinit(gpa);
    for (bindings.items) |b| {
        if (b.origin == .param) continue;
        if (b.is_const) continue;
        if (!isCanonicalOutName(b.name)) continue;
        try var_outs.put(gpa, b.name, {});
    }
    if (var_outs.count() == 0) return;

    // Match the acquire pattern; keep only acquires whose `<out>` is
    // one of the var-declared canonical-out locals.
    const all_acquires = try query.findAllInBody(gpa, tree, acquire_pattern, first, last);
    defer gpa.free(all_acquires);
    var acquires: std.ArrayListUnmanaged(Acquire) = .empty;
    defer acquires.deinit(gpa);
    for (all_acquires) |m| {
        const out_name = m.captureText(tree, 1).?;
        if (!var_outs.contains(out_name)) continue;
        const sc = tokens.findStmtSemicolon(tags, m.end + 1, last) orelse continue;
        try acquires.append(gpa, .{
            .out_name = out_name,
            .field_name = m.captureText(tree, 0).?,
            .method_tok = m.captures[2].?,
            .end_token = sc,
        });
    }
    if (acquires.items.len == 0) return;

    // A whole-fn errdefer (`errdefer result.deinit();`) protects all
    // acquires — detect once and use as a cheap suppressor.
    const has_whole_fn_errdefer = bodyHasErrdeferOn(tree, first, last);
    if (has_whole_fn_errdefer) return;

    for (acquires.items) |a| {
        var u: Ast.TokenIndex = a.end_token + 1;
        var has_errdefer = false;
        var has_next_try = false;
        while (u <= last) : (u += 1) {
            if (tags[u] == .keyword_errdefer) {
                if (errdeferReferences(tree, u, last, a.out_name)) {
                    has_errdefer = true;
                    break;
                }
            }
            if (tags[u] == .keyword_try) {
                has_next_try = true;
                break;
            }
        }
        if (has_next_try and !has_errdefer) {
            try report(gpa, problems, tree, a);
        }
    }
}

/// True iff `[first, last]` contains any `errdefer` mentioning a
/// canonical out-name within ~16 tokens after the keyword.  Used
/// to suppress for fns that have a whole-struct cleanup registered.
fn bodyHasErrdeferOn(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] != .keyword_errdefer) continue;
        const limit: Ast.TokenIndex = if (t + 16 > last) last else t + 16;
        var u: Ast.TokenIndex = t + 1;
        while (u <= limit) : (u += 1) {
            if (tags[u] != .identifier) continue;
            if (isCanonicalOutName(tree.tokenSlice(u))) return true;
        }
    }
    return false;
}

const isCanonicalOutName = method_names.isCanonicalOutName;

fn isAcquireMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "ensureTotalCapacity") or
        std.mem.eql(u8, name, "ensureUnusedCapacity") or
        std.mem.eql(u8, name, "initCapacity") or
        std.mem.eql(u8, name, "init") or
        std.mem.eql(u8, name, "append") or
        std.mem.eql(u8, name, "appendSlice") or
        std.mem.eql(u8, name, "put") or
        std.mem.eql(u8, name, "clone") or
        std.mem.eql(u8, name, "dupe") or
        std.mem.eql(u8, name, "alloc") or
        std.mem.eql(u8, name, "create");
}

/// True iff the errdefer at `kw` mentions `out` in its (inline or
/// block) body.  Loose match — any appearance of `out` as an
/// identifier counts as protection (covers whole-struct and
/// field-specific deinit forms).
fn errdeferReferences(
    tree: *const Ast,
    kw: Ast.TokenIndex,
    last: Ast.TokenIndex,
    out: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (kw + 1 > last) return false;
    var scan_start: Ast.TokenIndex = kw + 1;
    if (tags[scan_start] == .pipe) {
        var p: Ast.TokenIndex = scan_start + 1;
        while (p <= last and tags[p] != .pipe) : (p += 1) {}
        if (p > last) return false;
        scan_start = p + 1;
    }
    if (scan_start > last) return false;
    const range_end = if (tags[scan_start] == .l_brace)
        (tokens.matchBrace(tags, scan_start, last) orelse last)
    else
        (tokens.findStmtSemicolon(tags, scan_start, last) orelse last);
    var t: Ast.TokenIndex = scan_start;
    while (t <= range_end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t), out)) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    a: Acquire,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`try {s}.{s}.<acquire>(...)` populated `{s}.{s}`, but a later `try` in this fn has no `errdefer {s}.{s}.deinit(...)` between them — `{s}.{s}` leaks every time the next `try` propagates an error",
        .{ a.out_name, a.field_name, a.out_name, a.field_name, a.out_name, a.field_name, a.out_name, a.field_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, a.method_tok),
        .end = try Pos.fromTokenEnd(tree, a.method_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "SharedGrid.init pattern fires" {
    // Both `codepoints` and `glyphs` acquires lack errdefer covering
    // the subsequent try.
    try testing.expectCount(check, R, 2,
        \\const std = @import("std");
        \\const Self = struct {
        \\    codepoints: std.AutoHashMap(u32, u32),
        \\    glyphs: std.AutoHashMap(u32, u32),
        \\    pub fn init(alloc: std.mem.Allocator) !Self {
        \\        var result: Self = .{
        \\            .codepoints = .empty,
        \\            .glyphs = .empty,
        \\        };
        \\        try result.codepoints.ensureTotalCapacity(alloc, 128);
        \\        try result.glyphs.ensureTotalCapacity(alloc, 128);
        \\        try reloadMetrics();
        \\        return result;
        \\    }
        \\};
        \\fn reloadMetrics() !void {}
    );
}

test "with errdefer per acquire doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    codepoints: std.AutoHashMap(u32, u32),
        \\    glyphs: std.AutoHashMap(u32, u32),
        \\    pub fn init(alloc: std.mem.Allocator) !Self {
        \\        var result: Self = .{ .codepoints = .empty, .glyphs = .empty };
        \\        try result.codepoints.ensureTotalCapacity(alloc, 128);
        \\        errdefer result.codepoints.deinit(alloc);
        \\        try result.glyphs.ensureTotalCapacity(alloc, 128);
        \\        errdefer result.glyphs.deinit(alloc);
        \\        try reloadMetrics();
        \\        return result;
        \\    }
        \\};
        \\fn reloadMetrics() !void {}
    );
}

test "no later try doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    codepoints: std.AutoHashMap(u32, u32),
        \\    pub fn init(alloc: std.mem.Allocator) !Self {
        \\        var result: Self = .{ .codepoints = .empty };
        \\        try result.codepoints.ensureTotalCapacity(alloc, 128);
        \\        return result;
        \\    }
        \\};
    );
}

test "non-canonical out-name (xyz) doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn build(alloc: std.mem.Allocator) !void {
        \\    var xyz: std.ArrayList(u8) = .empty;
        \\    try xyz.ensureTotalCapacity(alloc, 8);
        \\    _ = try otherFallible();
        \\}
        \\fn otherFallible() !void {}
    );
}

test "out and r canonical names also work" {
    try testing.expectCount(check, R, 2,
        \\const std = @import("std");
        \\const Self = struct {
        \\    list: std.ArrayList(u8),
        \\    pub fn buildOut(alloc: std.mem.Allocator) !Self {
        \\        var out: Self = .{ .list = .empty };
        \\        try out.list.ensureTotalCapacity(alloc, 8);
        \\        _ = try otherFallible();
        \\        return out;
        \\    }
        \\    pub fn buildR(alloc: std.mem.Allocator) !Self {
        \\        var r: Self = .{ .list = .empty };
        \\        try r.list.ensureTotalCapacity(alloc, 8);
        \\        _ = try otherFallible();
        \\        return r;
        \\    }
        \\};
        \\fn otherFallible() !void {}
    );
}
