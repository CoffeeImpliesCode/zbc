//! Sentinel-strip-free-size-mismatch detector — `<alloc>.free(
//! <X>.ptr[0..<X>.len])` (or `<X>.ptr.?[0..<X>.len]`) hand-rolls
//! a `[]u8` slice from a many-item-pointer and slices it to
//! `<X>.len`.  If `<X>` is a sentinel-terminated slice
//! (`[:0]const u8` produced by `dupeZ`, `allocSentinel`, string
//! literals, etc.) the underlying allocation is `len + 1` bytes
//! — but the freed slice is only `len` bytes.  The allocator's
//! free-size check trips with `Allocation size N+1 does not
//! match free size N`.
//!
//! Even when there's no sentinel, the shape is redundant — you
//! should just pass `<X>` to `free` directly.  Either
//! interpretation is a bug.
//!
//! Real-world: ghostty-org/ghostty#8886
//! (`ghostty_string_free` in src/main_c.zig).
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Skip comptime type-builder fns.
//!   2. Find `.free(` calls preceded by `.` (allocator method).
//!   3. Match the single argument against the pattern
//!      `<X> . ptr (.?)? [ <expr> . . <X> . len ]`.
//!   4. Fire on the `.free` call.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const query = @import("../../ast/token_query.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const Atom = query.Atom;

// `.free(<X>.ptr (.?)? [<lo>..<X>.len])` — the sentinel-strip shape.
// Capture slots:
//   $0 = X (slice binding name); trailing `<X>.len` ref-matches it
//   $1 = `free` method token (used as the report site)
// Range slot 0 captures the `<lo>` expression between `[` and `..`.
const sentinel_strip = &[_]Atom{
    .{ .tok = .period },
    .{ .text_at = .{ .slot = 1, .text = "free" } },
    .{ .tok = .l_paren },
    .{ .capture = 0 },
    .{ .tok = .period },
    .{ .text = "ptr" },
    .{ .opt = &[_]Atom{ .{ .tok = .period }, .{ .tok = .question_mark } } },
    .{ .tok = .l_bracket },
    .{ .capture_until = .{ .slot = 0, .stops = &.{.ellipsis2} } },
    .{ .tok = .ellipsis2 },
    .{ .ref = 0 },
    .{ .tok = .period },
    .{ .text = "len" },
    .{ .tok = .r_bracket },
    .{ .tok = .r_paren },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .sentinel_strip_free_size_mismatch)) return;
    const Ctx = struct {
        cache: *file_cache_mod.FileCache,
        pub fn check(
            ctx: *@This(),
            inner_gpa: std.mem.Allocator,
            inner_tree: *const Ast,
            inner_body: Ast.Node.Index,
            inner_problems: *std.ArrayListUnmanaged(Problem),
        ) !void {
            const first = inner_tree.firstToken(inner_body);
            const last = inner_tree.lastToken(inner_body);
            const matches = try query.findAllInBody(inner_gpa, inner_tree, sentinel_strip, first, last);
            defer inner_gpa.free(matches);
            for (matches) |m| {
                if (xPtrFieldIsNonSentinel(inner_tree, ctx.cache, m.captures[0].?)) continue;
                try report(inner_gpa, inner_problems, inner_tree, m.captures[1].?);
            }
        }
    };
    var ctx: Ctx = .{ .cache = cache };
    _ = &ctx;
    // Reuse the original token-scan: forEachFnBody handles fn iteration.
    // We bypass that here since we now need the cache; do the iteration manually.
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |fn_entry| {
        try ctx.check(gpa, tree, fn_entry.body, problems);
    }
}

/// True iff `<X>`'s type has a `ptr` field declared as a non-
/// sentinel many-item pointer (`[*]T`).  Sentinel-terminated
/// pointers (`[*:0]T`, `[*:S]T`) return false — the rule's
/// warning applies to those.  Returns false when the type can't
/// be resolved (conservatively keep the warning).
fn xPtrFieldIsNonSentinel(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    x_token: Ast.TokenIndex,
) bool {
    // `<X>` is the capture's name token — its sliced text is the
    // local's identifier.
    const tags = tree.tokens.items(.tag);
    if (tags[x_token] != .identifier) return false;
    const x_name = tree.tokenSlice(x_token);
    // Resolve the binding to find its declared type.  For method
    // receivers (`this`, `self`), use the enclosing fn's containing
    // type as the type name.
    const fn_decl = enclosingFnDecl(tree, x_token) orelse return false;
    const model = cache.fileModel() catch return false;
    const type_name = bindingTypeName(tree, model, fn_decl, x_name) orelse return false;
    const resolved = cache.findTypeAcrossImports(type_name) orelse return false;
    const ptr_field = resolved.info.findField("ptr") orelse return false;
    const field_tags = resolved.model.tree.tokens.items(.tag);
    // Sentinel check: type tokens start with `[` `*`.  If the next
    // token is `:`, it's sentinel-terminated.  If it's `]`, it's
    // non-sentinel.  Anything else (numeric arrays etc.) doesn't
    // match the rule's pattern anyway — let the rule fire.
    const t = ptr_field.type_first;
    if (t + 2 > ptr_field.type_last) return false;
    if (field_tags[t] != .l_bracket) return false;
    if (field_tags[t + 1] != .asterisk) return false;
    return field_tags[t + 2] == .r_bracket;
}

/// Find the fn_decl AST node enclosing a given token by walking
/// the file model's fn list / type methods.
const enclosingFnDecl = tokens.enclosingFnDecl;

/// Return the type identifier of the local named `name` inside
/// `fn_decl`.  Resolves method receivers (`this`/`self` typed as
/// `*Self`/`*@This()`) to the enclosing type's name.  Returns null
/// when the binding can't be located or its type isn't a simple
/// identifier.
fn bindingTypeName(
    tree: *const Ast,
    model: *const @import("../../model/file_model.zig").FileModel,
    fn_decl: Ast.Node.Index,
    name: []const u8,
) ?[]const u8 {
    var proto_buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return null;
    var it = proto.iterate(tree);
    while (it.next()) |p| {
        const nt = p.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(nt), name)) continue;
        const type_node = p.type_expr orelse return null;
        return baseTypeNameOfNode(tree, model, type_node);
    }
    return null;
}

/// Preserve the entire declared name and its lexical owner.
fn baseTypeNameOfNode(
    tree: *const Ast,
    model: *const @import("../../model/file_model.zig").FileModel,
    type_node: Ast.Node.Index,
) ?[]const u8 {
    const first = tree.firstToken(type_node);
    const last = tree.lastToken(type_node);
    const owner = model.containingTypeOf(type_node);
    const name = tokens.typeNameFromTokens(tree, first, last) orelse {
        if (owner) |scope| {
            if (last >= first + 2 and tree.tokenTag(last - 2) == .builtin and
                std.mem.eql(u8, tree.tokenSlice(last - 2), "@This")) return scope.qualified_name;
        }
        return null;
    };
    if (owner) |scope| {
        if (std.mem.eql(u8, name, "Self")) return scope.qualified_name;
        if (model.resolveTypeNameInScope(name, scope)) |resolved| return resolved.qualified_name;
    }
    return name;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    free_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`<alloc>.free(<X>.ptr[0..<X>.len])` hand-rolls a non-sentinel slice from a many-item-pointer.  If `<X>` is `[:0]const u8` or another sentinel-terminated slice, the underlying allocation is len+1 bytes — the allocator's free-size check trips.  Either pass `<X>` directly to `free`, or include the sentinel: `<alloc>.free(<X>.ptr.?[0..<X>.len :0])`",
        .{},
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "sentinel-strip-free-size-mismatch",
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, free_tok),
        .end = Pos.fromTokenEnd(tree, free_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "sentinel-strip-free-size-mismatch: ghostty_string_free pattern fires" {
    const gpa = std.testing.allocator;
    // Sentinel-terminated ptr — the canonical bug shape from
    // ghostty#8886.  `[*:0]const u8` means the allocation is
    // len+1 bytes; freeing `[0..len]` trips the allocator's
    // size check.
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Str = struct { ptr: ?[*:0]const u8, len: usize };
        \\pub fn ghostty_string_free(str: Str, alloc: std.mem.Allocator) void {
        \\    alloc.free(str.ptr.?[0..str.len]);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("sentinel-strip-free-size-mismatch", problems.items[0].rule_id);
}

test "sentinel-strip-free-size-mismatch: bare .ptr[0..len] variant also fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Str = struct { ptr: [*:0]u8, len: usize };
        \\pub fn release(str: Str, alloc: std.mem.Allocator) void {
        \\    alloc.free(str.ptr[0..str.len]);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "sentinel-strip-free-size-mismatch: non-sentinel [*]u8 ptr does NOT fire" {
    const gpa = std.testing.allocator;
    // Non-sentinel `[*]u8` ptr field — the `.ptr[0..len]` shape
    // is the canonical way to free a manually-managed slice (no
    // sentinel byte = allocation is exactly len bytes).  Bun's
    // RefCountedStr uses this shape.
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Str = struct { ptr: [*]u8, len: usize };
        \\pub fn release(str: Str, alloc: std.mem.Allocator) void {
        \\    alloc.free(str.ptr[0..str.len]);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "sentinel-strip-free-size-mismatch: alloc.free(slice) directly doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn release(slice: []u8, alloc: std.mem.Allocator) void {
        \\    alloc.free(slice);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "sentinel-strip-free-size-mismatch: alloc.free(slice[0..N]) doesn't fire (not .ptr-based)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn release(slice: []u8, alloc: std.mem.Allocator) void {
        \\    alloc.free(slice[0..10]);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}
