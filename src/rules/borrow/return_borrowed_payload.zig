//! `return switch (<expr>) { ... };` where one arm returns the
//! captured payload bare (`.<Tag> => |v| v`) while a sibling arm
//! clones / allocates a fresh value (`alloc.dupe(...)`, `.clone(...)`,
//! etc.).  The bare arm returns a slice/pointer borrowed from the
//! caller's input — which may be freed while the return value is
//! still in use.
//!
//! Sibling-arm asymmetry is the strongest signal: when one arm
//! goes to the trouble of `alloc.dupe(...)` the author clearly
//! intends the returned value to be owned by the caller's
//! allocator.  An adjacent arm that returns `|v| v` raw is almost
//! always an oversight.
//!
//! Real-world: ghostty-org/ghostty#8358 ("terminal: fix use-after-
//! free in exec") and #7711 (open() accepted arena, returned slice
//! into it that outlived arena).
//!
//! Detection (purely syntactic, per-fn token walk):
//!   1. Skip comptime type-builder fns.
//!   2. Walk for `return switch (` in fn body.
//!   3. Find arms `.<Tag> => |v| <body>` where `<body>` is either
//!      bare `v,` (bare capture return) OR contains an allocator
//!      method call (`<X>.dupe(...)`, `.clone(...)`, etc.).
//!   4. If both a bare-return arm AND a clone arm exist in the
//!      same switch, fire on each bare-return arm.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const resolver_mod = @import("../../type_resolver.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const matchBrace = tokens.matchBrace;
const matchParen = tokens.matchParen;
const skipNestedFn = tokens.skipNestedFn;
const returnsType = tokens.returnsType;
const fnProto = tokens.fnProto;
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
    if (!config_mod.isEnabled(config, .return_borrowed_payload)) return;

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        if (returnsType(tree, node)) continue;
        const body = bodyOf(tree, node) orelse continue;
        try checkBody(gpa, tree, cache, body, problems);
    }
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var t: Ast.TokenIndex = first;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_return) continue;
        if (tags[t + 1] != .keyword_switch) continue;
        if (tags[t + 2] != .l_paren) continue;
        const cp = matchParen(tags, t + 2, last) orelse continue;
        if (cp + 1 > last or tags[cp + 1] != .l_brace) continue;
        const sw_body_start = cp + 1;
        const sw_body_end = matchBrace(tags, sw_body_start, last) orelse continue;
        // Resolve the scrutinee's union type (if same-file or
        // resolvable cross-file) so bare-return arms can be filtered
        // by payload-type: pointer-payload arms return the cached
        // pointer (not a borrow into the input), so they're safe.
        const scrut_union = scrutineeUnionType(tree, cache, t + 3, cp - 1);
        try checkSwitchArms(gpa, tree, cache, scrut_union, sw_body_start + 1, sw_body_end - 1, problems);
        t = sw_body_end;
    }
}

const ArmInfo = struct {
    /// Token of the `.<Tag>` identifier (anchor for diagnostic).
    tag_tok: Ast.TokenIndex,
    is_bare_return: bool,
    has_clone: bool,
};

/// Resolve the scrutinee expression `switch (<expr>)` (token range
/// [start, end] = inside the parens) to a union ResolvedType when:
///   - the expression is a single identifier (a local) whose
///     binding chain we can follow, OR
///   - the expression is `<ident>.*` / `<ident>.<field>` shapes
///     where the leaf type is a union.
/// Returns null when unresolvable.  Used by the rule to filter
/// pointer-payload arms.
fn scrutineeUnionType(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) ?file_cache_mod.FileCache.ResolvedType {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    // Handle `<ident>.*` (deref).  Zig lexes `.*` as one token,
    // so the shape is `<ident>` `.*` (token tag `period_asterisk`).
    if (end == start + 1 and
        tags[start] == .identifier and
        tags[start + 1] == .period_asterisk)
    {
        const ident = tree.tokenSlice(start);
        return resolveLocalTypeAsUnion(tree, cache, start, ident);
    }
    // Handle bare `<ident>` — usually a method receiver `this`/`self`.
    if (start == end and tags[start] == .identifier) {
        const ident = tree.tokenSlice(start);
        return resolveLocalTypeAsUnion(tree, cache, start, ident);
    }
    return null;
}

/// Find the local named `ident` in the enclosing fn's prototype,
/// extract the base type identifier, look it up via file model +
/// cross-file index.  Return the type only if it's a union.  The
/// result carries its owning model: variant token ranges belong to
/// `resolved.model.tree`, not to `tree`.
fn resolveLocalTypeAsUnion(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    ident_tok: Ast.TokenIndex,
    ident: []const u8,
) ?file_cache_mod.FileCache.ResolvedType {
    const fn_decl = enclosingFnDecl(tree, ident_tok) orelse return null;
    var proto_buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return null;
    var it = proto.iterate(tree);
    while (it.next()) |p| {
        const nt = p.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(nt), ident)) continue;
        const type_node = p.type_expr orelse return null;
        const type_name = baseTypeNameOfNode(tree, type_node) orelse return null;
        const resolved = cache.resolvedTypeAcrossImports(type_name) orelse return null;
        if (resolved.info.kind != .union_) return null;
        return resolved;
    }
    return null;
}

const enclosingFnDecl = tokens.enclosingFnDecl;

fn baseTypeNameOfNode(tree: *const Ast, type_node: Ast.Node.Index) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(type_node);
    const last = tree.lastToken(type_node);
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .asterisk, .keyword_const => continue,
            .l_bracket => {
                var d: u32 = 1;
                t += 1;
                while (t <= last and d > 0) : (t += 1) {
                    if (tags[t] == .l_bracket) d += 1;
                    if (tags[t] == .r_bracket) d -= 1;
                }
                if (t > last) return null;
                t -= 1;
            },
            .identifier, .builtin => break,
            else => return null,
        }
    }
    if (t > last) return null;
    var last_name: ?[]const u8 = null;
    var expecting_ident: bool = true;
    while (t <= last) : (t += 1) {
        if (expecting_ident) {
            if (tags[t] == .identifier) {
                last_name = tree.tokenSlice(t);
                expecting_ident = false;
            } else return last_name;
        } else {
            if (tags[t] == .period) {
                expecting_ident = true;
            } else break;
        }
    }
    return last_name;
}

/// True iff the union variant `tag_name`'s declared payload type
/// is a pointer (`*T` / `?*T`).  Pointer payloads in a switch arm
/// `.tag => |v| v` are STABLE — `v` IS the pointer, returning it
/// doesn't borrow from any caller input.  `tree` MUST be the tree
/// that owns `un_ti`.
fn unionVariantHasPointerPayload(
    tree: *const Ast,
    un_ti: *const @import("../../model/file_model.zig").TypeInfo,
    tag_name: []const u8,
) bool {
    const field = un_ti.findField(tag_name) orelse return false;
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = field.type_first;
    while (t <= field.type_last) : (t += 1) {
        if (tags[t] == .question_mark) continue;
        return tags[t] == .asterisk;
    }
    return false;
}

/// True for scalar and enum payloads that are copied by value.  Slices,
/// structs, and unknown types stay conservative and are not filtered.
/// Only unions of the requesting file are judged: `cache` resolves
/// token ranges of its own tree.
fn unionVariantHasImmediateValuePayload(
    cache: *file_cache_mod.FileCache,
    union_type: file_cache_mod.FileCache.ResolvedType,
    tag_name: []const u8,
) bool {
    const model = cache.fileModel() catch return false;
    if (union_type.model != model) return false;
    const un_ti = union_type.info;
    const tree = model.tree;
    const field = un_ti.findField(tag_name) orelse return false;
    if (cache.isEnumTypeOfExpr(field.type_first, field.type_last) == true) return true;
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = field.type_first;
    while (t <= field.type_last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .keyword_const => continue,
            .asterisk, .l_bracket => return false,
            .identifier => {
                if (t != field.type_last) return false;
                const name = tree.tokenSlice(t);
                if (isImmediateBuiltin(name)) return true;
                const type_info = model.findType(name) orelse return false;
                return type_info.kind == .enum_;
            },
            else => return false,
        }
    }
    return false;
}

fn isImmediateBuiltin(name: []const u8) bool {
    return std.mem.eql(u8, name, "bool") or
        std.mem.eql(u8, name, "usize") or
        std.mem.eql(u8, name, "isize") or
        std.mem.eql(u8, name, "void") or
        std.mem.eql(u8, name, "f16") or
        std.mem.eql(u8, name, "f32") or
        std.mem.eql(u8, name, "f64") or
        std.mem.eql(u8, name, "f80") or
        std.mem.eql(u8, name, "f128") or
        std.mem.eql(u8, name, "u8") or
        std.mem.eql(u8, name, "u16") or
        std.mem.eql(u8, name, "u32") or
        std.mem.eql(u8, name, "u64") or
        std.mem.eql(u8, name, "u128") or
        std.mem.eql(u8, name, "i8") or
        std.mem.eql(u8, name, "i16") or
        std.mem.eql(u8, name, "i32") or
        std.mem.eql(u8, name, "i64") or
        std.mem.eql(u8, name, "i128");
}

/// Token window covered by one switch arm's body.  A block arm
/// (`.tag => { ... }`) is scanned between its braces; an inline arm
/// (`.tag => expr`) is scanned from its first token through
/// `end_inclusive`.
const ArmBodySpan = struct {
    end_inclusive: Ast.TokenIndex,
    scan_start: Ast.TokenIndex,
    scan_end: Ast.TokenIndex,
};

/// Resolve the span of an arm body starting at `body_start`, looking
/// no further than `end`.  Strips the braces of a block arm so the
/// span holds only the arm's own tokens.  Null when a block arm's
/// braces never close within `end`.
fn armBodySpan(
    tags: []const std.zig.Token.Tag,
    body_start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) ?ArmBodySpan {
    const body_is_block = tags[body_start] == .l_brace;
    const end_inclusive = if (body_is_block)
        (matchBrace(tags, body_start, end) orelse return null)
    else
        (findArmEndInclusive(tags, body_start, end) orelse return null);
    return .{
        .end_inclusive = end_inclusive,
        .scan_start = if (body_is_block) body_start + 1 else body_start,
        .scan_end = if (body_is_block) end_inclusive - 1 else end_inclusive,
    };
}

fn checkSwitchArms(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    scrut_union: ?file_cache_mod.FileCache.ResolvedType,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    var arms: std.ArrayListUnmanaged(ArmInfo) = .empty;
    defer arms.deinit(gpa);

    var t: Ast.TokenIndex = start;
    while (t + 3 <= end) : (t += 1) {
        // Find arm start `.<Tag>` (skip `else`).
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        const tag_tok = t + 1;
        // Find `=>`.
        var fa: Ast.TokenIndex = tag_tok + 1;
        while (fa <= end and tags[fa] != .equal_angle_bracket_right) : (fa += 1) {}
        if (fa > end) break;
        // Optional capture `|v|`.
        var capture_name: ?[]const u8 = null;
        var body_start: Ast.TokenIndex = fa + 1;
        if (body_start <= end and tags[body_start] == .pipe) {
            var p: Ast.TokenIndex = body_start + 1;
            if (p <= end and tags[p] == .asterisk) p += 1;
            if (p <= end and tags[p] == .identifier) {
                capture_name = tree.tokenSlice(p);
            }
            while (p <= end and tags[p] != .pipe) : (p += 1) {}
            if (p > end) break;
            body_start = p + 1;
        }
        if (body_start > end) break;
        // Arm body — block or inline.
        const span = armBodySpan(tags, body_start, end) orelse break;
        const scan_start = span.scan_start;
        const scan_end = span.scan_end;

        const tag_name = tree.tokenSlice(tag_tok);
        var is_bare = if (capture_name) |cap|
            armIsBareReturn(tree, scan_start, scan_end, cap)
        else
            false;
        // Pointer-payload skip: when the union variant's declared
        // payload type is `*T` / `?*T`, the captured `v` IS a
        // pointer.  Returning it bare doesn't borrow from any
        // caller input — it returns the cached heap pointer.
        if (is_bare and scrut_union != null and
            unionVariantHasPointerPayload(scrut_union.?.model.tree, scrut_union.?.info, tag_name))
        {
            is_bare = false;
        }
        if (is_bare and scrut_union != null and
            unionVariantHasImmediateValuePayload(cache, scrut_union.?, tag_name))
        {
            is_bare = false;
        }
        const has_clone = armHasClone(tree, scan_start, scan_end, capture_name);
        try arms.append(gpa, .{
            .tag_tok = tag_tok,
            .is_bare_return = is_bare,
            .has_clone = has_clone,
        });
        t = span.end_inclusive;
    }

    // If ANY arm has clone AND there's a bare-return arm, fire on
    // each bare-return arm.
    var any_clone = false;
    for (arms.items) |a| {
        if (a.has_clone) any_clone = true;
    }
    if (!any_clone) return;
    for (arms.items) |a| {
        if (a.is_bare_return) try report(gpa, problems, tree, a.tag_tok);
    }
}

/// True iff the arm's body is JUST `<capture>` (with optional
/// trailing tokens like `,`).  Empty bodies don't count.
fn armIsBareReturn(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    capture: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start > end) return false;
    if (tags[start] != .identifier) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(start), capture)) return false;
    // Allow `<capture>` followed by nothing OR by `,` only.
    var t: Ast.TokenIndex = start + 1;
    while (t <= end) : (t += 1) {
        if (tags[t] == .comma) continue;
        // Any other non-trivial token (period, paren, etc.) means
        // there's more going on — not a bare return.
        return false;
    }
    return true;
}

/// True iff the arm contains a clone/allocate method call or a named
/// free helper that consumes the captured payload.
fn armHasClone(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    capture: ?[]const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] == .period and tags[t + 1] == .identifier and tags[t + 2] == .l_paren) {
            if (isAllocOrCloneMethodName(tree.tokenSlice(t + 1))) return true;
            continue;
        }
        if (tags[t] != .identifier or tags[t + 1] != .l_paren) continue;
        if (t > start and tags[t - 1] == .period) continue;
        if (!isAllocOrCloneFunctionName(tree.tokenSlice(t))) continue;
        const close = matchParen(tags, t + 1, end) orelse continue;
        const cap = capture orelse continue;
        var arg = t + 2;
        while (arg < close) : (arg += 1) {
            if (tags[arg] != .identifier or !std.mem.eql(u8, tree.tokenSlice(arg), cap)) continue;
            if (arg == t + 2 or tags[arg - 1] != .period) return true;
        }
        t = close;
    }
    return false;
}

fn isAllocOrCloneFunctionName(name: []const u8) bool {
    return std.mem.startsWith(u8, name, "clone") or
        std.mem.startsWith(u8, name, "copy") or
        std.mem.startsWith(u8, name, "dupe") or
        std.mem.startsWith(u8, name, "alloc") or
        std.mem.startsWith(u8, name, "owned");
}

fn isAllocOrCloneMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "dupe") or
        std.mem.eql(u8, name, "dupeZ") or
        std.mem.eql(u8, name, "alloc") or
        std.mem.eql(u8, name, "allocSentinel") or
        std.mem.eql(u8, name, "create") or
        std.mem.eql(u8, name, "clone") or
        std.mem.eql(u8, name, "cloneWith") or
        std.mem.eql(u8, name, "allocPrint") or
        std.mem.eql(u8, name, "allocPrintZ") or
        std.mem.eql(u8, name, "toOwnedSlice") or
        std.mem.eql(u8, name, "toOwnedSliceSentinel");
}

fn findArmEndInclusive(
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?Ast.TokenIndex {
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
            } else return t - 1,
            .l_bracket => bracket += 1,
            .r_bracket => if (bracket > 0) {
                bracket -= 1;
            },
            .comma => if (paren == 0 and brace == 0 and bracket == 0) return t - 1,
            else => {},
        }
    }
    return null;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    tag_tok: Ast.TokenIndex,
) !void {
    const tag = tree.tokenSlice(tag_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`return switch (...) {{ .{s} => |v| v, ... }}` returns the captured payload bare while a sibling arm clones / allocates — the caller's input may be freed while this return value is still in use.  Clone the payload too (e.g. `alloc.dupe(u8, v)` / `try v.clone(alloc)`)",
        .{tag},
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "return-borrowed-payload",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, tag_tok),
        .end = try Pos.fromTokenEnd(tree, tag_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "return-borrowed-payload: sibling-arm asymmetry fires on bare return" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Cmd = union(enum) {
        \\    direct: []const u8,
        \\    shell: []const u8,
        \\};
        \\pub fn extract(cmd: Cmd, alloc: std.mem.Allocator) ![]const u8 {
        \\    return switch (cmd) {
        \\        .direct => |v| v,
        \\        .shell => |v| try alloc.dupe(u8, v),
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("return-borrowed-payload", problems.items[0].rule_id);
}

test "return-borrowed-payload: all arms clone — no fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Cmd = union(enum) { a: []const u8, b: []const u8 };
        \\pub fn extract(cmd: Cmd, alloc: std.mem.Allocator) ![]const u8 {
        \\    return switch (cmd) {
        \\        .a => |v| try alloc.dupe(u8, v),
        \\        .b => |v| try alloc.dupe(u8, v),
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "return-borrowed-payload: all arms bare — no fire (no sibling asymmetry signal)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Cmd = union(enum) { a: []const u8, b: []const u8 };
        \\pub fn extract(cmd: Cmd) []const u8 {
        \\    return switch (cmd) {
        \\        .a => |v| v,
        \\        .b => |v| v,
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "return-borrowed-payload: clone via .clone(alloc) also recognized" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Payload = struct {
        \\    pub fn clone(_: *const Payload, _: std.mem.Allocator) !Payload { return .{}; }
        \\};
        \\const Cmd = union(enum) { a: Payload, b: Payload };
        \\pub fn extract(cmd: Cmd, alloc: std.mem.Allocator) !Payload {
        \\    return switch (cmd) {
        \\        .a => |v| v,
        \\        .b => |v| try v.clone(alloc),
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "skript regression: enum payload copy is not a borrowed slice" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const ValueId = enum { invalid, valid };
        \\const Choice = union(enum) { residual: ValueId, generated: ValueId };
        \\fn cloneValue(value: ValueId) ValueId { return value; }
        \\pub fn extract(choice: Choice) ValueId {
        \\    return switch (choice) {
        \\        .residual => |value| value,
        \\        .generated => |value| cloneValue(value),
        \\    };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "skript regression: slice payload still requires ownership copy" {
    try testing.expectFires(check, "return-borrowed-payload",
        \\const Choice = union(enum) { residual: []const u8, generated: []const u8 };
        \\fn cloneBytes(value: []const u8) []const u8 { return value; }
        \\pub fn extract(choice: Choice) []const u8 {
        \\    return switch (choice) {
        \\        .residual => |value| value,
        \\        .generated => |value| cloneBytes(value),
        \\    };
        \\}
        \\
    );
}

test "qualified enum payloads are resolved by their declared type" {
    const source: [:0]const u8 =
        \\const Code = struct { pub const ValueId = enum(u32) { invalid, valid }; };
        \\const Choice = union(enum) { residual: Code.ValueId, generated: Code.ValueId };
        \\fn cloneValue(value: Code.ValueId) Code.ValueId { return value; }
        \\pub fn extract(choice: Choice) Code.ValueId {
        \\    return switch (choice) {
        \\        .residual => |value| value,
        \\        .generated => |value| cloneValue(value),
        \\    };
        \\}
        \\
    ;
    try expectTypedPayloadProblems(source, 0);
}

test "qualified enum namespace does not make a slice payload scalar" {
    const source: [:0]const u8 =
        \\const Code = enum { tag, pub const ValueId = []const u8; };
        \\const Choice = union(enum) { residual: Code.ValueId, generated: Code.ValueId };
        \\fn cloneValue(value: Code.ValueId) Code.ValueId { return value; }
        \\pub fn extract(choice: Choice) Code.ValueId {
        \\    return switch (choice) {
        \\        .residual => |value| value,
        \\        .generated => |value| cloneValue(value),
        \\    };
        \\}
        \\
    ;
    try expectTypedPayloadProblems(source, 1);
}

fn expectTypedPayloadProblems(source: [:0]const u8, expected: usize) !void {
    const gpa = std.testing.allocator;
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-qualified-enum-regression.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer testing.freeProblems(gpa, &problems);
    try check(gpa, tree, &cache, &config_mod.Default, &problems);
    try std.testing.expectEqual(expected, problems.items.len);
}
