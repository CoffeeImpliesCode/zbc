//! Detects two or more `.field = try <expr>` inside the same struct literal (or
//! initializer).  If the first `try` succeeds but the second `try` propagates an
//! error, the allocation made by the first `try` leaks — `errdefer` cannot be
//! placed inside a struct literal expression.
//!
//! Real-world instance:
//!   - ziglang/zig#23285 (std.zig.Ast.parse):
//!       return Ast{
//!           .extra_data = try parser.extra_data.toOwnedSlice(gpa),  // succeeds
//!           .errors     = try parser.errors.toOwnedSlice(gpa),       // fails → leak
//!       };
//!     Fix: bind each to a local with `errdefer`, then build the struct literal
//!     from the locals.
//!
//! Detection (Tier 1, token walk with paren-skip):
//!   Pattern: `. identifier = keyword_try ... , . identifier = keyword_try`
//!   — find the first `.field = try` 4-token prefix, skip to the next `,` at
//!   depth 0, then check whether the following tokens are `. identifier = try`.
//!   Fire at the second `.` token (the start of the second field assignment).
//!
//!   The leak only matters if the FIRST `try` actually allocates an owned
//!   resource (the second `try` failing is what leaks the first's allocation).
//!   So the first try-expression must contain an allocation signal —
//!   `alloc`, `dupe`, `clone`, `create`, or `toOwnedSlice`.  Decoder/parser
//!   tries (`read_int`, `read_enum`, `parseUnsigned`) return value types and
//!   leak nothing, so they are suppressed.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");
const file_model = @import("../../model/file_model.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "struct-literal-multiple-try";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .struct_literal_multiple_try)) return;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 8) return;
    const last_tok: Ast.TokenIndex = @intCast(tree.tokens.len -| 1);

    // Map identifier-reference nodes by main token, so the first-try
    // expression's operands can be resolved to their types (e.g. is an operand
    // a `std.mem.Allocator`?).  Empty/unused when the type engine is absent.
    var ident_nodes: std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index) = .empty;
    defer ident_nodes.deinit(gpa);
    {
        var ni: u32 = 0;
        while (ni < tree.nodes.len) : (ni += 1) {
            const node: Ast.Node.Index = @enumFromInt(ni);
            if (tree.nodeTag(node) == .identifier) {
                try ident_nodes.put(gpa, tree.nodeMainToken(node), node);
            }
        }
    }

    var t: Ast.TokenIndex = 0;
    while (t + 7 <= last_tok) : (t += 1) {
        // First field: . identifier = try
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .keyword_try) continue;

        // Skip to ',' at depth 0 (end of this field's initializer)
        var i = t + 4;
        var depth: u32 = 0;
        while (i <= last_tok) : (i += 1) {
            switch (tags[i]) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => {
                    if (depth == 0) break; // closing delimiter of the struct literal
                    depth -= 1;
                },
                .comma => if (depth == 0) break,
                else => {},
            }
        }
        if (i > last_tok) continue;
        if (tags[i] != .comma) continue; // hit a closing delimiter — skip

        // The first try-expression (t+4 .. comma) must allocate an owned
        // resource — otherwise nothing leaks when a later try fails.  The
        // SEMANTIC signal (`firstTryUsesAllocator`) recognizes that the call
        // takes/uses a `std.mem.Allocator` value (the type-based ownership
        // signal — `gpa.alloc`, `list.toOwnedSlice(gpa)`, `el.deepClone(alloc)`
        // all reference an Allocator; a borrowed `getView()` does not).  The
        // syntactic name proxy still catches internal-alloc calls with no
        // visible allocator operand (`x.clone()`).
        if (!firstTryUsesAllocator(cache, &ident_nodes, tags, t + 4, i) and
            !tryExprAllocates(tree, tags, t + 4, i)) continue;
        if (firstTryReturnsValue(tree, cache, t + 4, i)) continue;
        if (firstTryUsesScopedArena(tree, cache, t + 4, i)) continue;

        // If the surrounding function uses an arena-backed allocator (i.e.
        // there is a `const X = ARENA.allocator()` within 200 tokens before
        // this struct literal, or the first-try expression passes an
        // "arena"-named argument directly, or the enclosing function has
        // `errdefer ARENA.deinit()`), every allocation is freed when the
        // arena resets — no per-field leak is possible even if a later
        // `try` fails.
        if (nearbyArenaAllocator(tree, tags, t)) continue;
        if (tryExprPassesArena(tree, tags, t + 4, i)) continue;
        if (enclosingFnHasArenaErrdefer(tree, tags, t)) continue;

        // Check the next field starts with . identifier = try
        const next = i + 1;
        if (next + 3 > last_tok) continue;
        if (tags[next] != .period) continue;
        if (tags[next + 1] != .identifier) continue;
        if (tags[next + 2] != .equal) continue;
        if (tags[next + 3] != .keyword_try) continue;

        const field1 = tree.tokenSlice(t + 1);
        const field2 = tree.tokenSlice(next + 1);

        try report(gpa, problems, tree, next, field1, field2);
    }
}

fn firstTryReturnsValue(tree: *const Ast, cache: *file_cache_mod.FileCache, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    if (start + 1 >= end or tree.tokenTag(start) != .identifier or tree.tokenTag(start + 1) != .l_paren) return false;
    const model = cache.fileModel() catch return false;
    const function = model.findFn(tree.tokenSlice(start)) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&buffer, function.fn_decl) orelse return false;
    var result_type = proto.ast.return_type.unwrap() orelse return false;
    if (tree.nodeTag(result_type) == .error_union) result_type = tree.nodeData(result_type).node_and_node[1];
    if (tree.nodeTag(result_type) != .identifier) return false;
    return isValueOnlyType(tree, model, tree.tokenSlice(tree.nodeMainToken(result_type)), 0);
}

fn isValueOnlyType(tree: *const Ast, model: *const file_model.FileModel, name: []const u8, depth: u8) bool {
    if (depth >= 16) return false;
    if (std.mem.eql(u8, name, "bool") or std.mem.eql(u8, name, "void") or
        std.mem.eql(u8, name, "usize") or std.mem.eql(u8, name, "isize")) return true;
    if (name.len > 1 and (name[0] == 'u' or name[0] == 'i' or name[0] == 'f')) {
        if (std.fmt.parseInt(u16, name[1..], 10)) |_| return true else |_| {}
    }
    const info = model.findType(name) orelse {
        for (tree.rootDecls()) |node| {
            const decl = tree.fullVarDecl(node) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(decl.ast.mut_token + 1), name)) continue;
            const initializer = decl.ast.init_node.unwrap() orelse return false;
            if (tree.nodeTag(initializer) != .identifier) return false;
            return isValueOnlyType(tree, model, tree.tokenSlice(tree.nodeMainToken(initializer)), depth + 1);
        }
        return false;
    };
    if (info.hasMethod("deinit") or info.hasMethod("close") or info.hasMethod("destroy") or
        info.hasMethod("free") or info.hasMethod("release")) return false;
    if (info.kind == .enum_) return true;
    if (info.kind != .struct_ or info.fields.len == 0) return false;
    for (info.fields) |field| {
        if (field.type_first != field.type_last or tree.tokenTag(field.type_first) != .identifier) return false;
        if (!isValueOnlyType(tree, model, tree.tokenSlice(field.type_first), depth + 1)) return false;
    }
    return true;
}

fn firstTryUsesScopedArena(tree: *const Ast, cache: *file_cache_mod.FileCache, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    if (start + 2 >= end or tree.tokenTag(start) != .identifier or tree.tokenTag(start + 1) != .period) return false;
    const model = cache.fileModel() catch return false;
    for (model.fns) |function| {
        if (start < function.body_first or start > function.body_last) continue;
        if (function.is_pub) return false;
        if (function.name_token >= 2 and tree.tokenTag(function.name_token - 2) == .keyword_export) return false;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buffer, function.fn_decl) orelse return false;
        var params = proto.iterate(tree);
        var index: usize = 0;
        while (params.next()) |param| : (index += 1) {
            const name_token = param.name_token orelse continue;
            if (std.mem.eql(u8, tree.tokenSlice(name_token), tree.tokenSlice(start))) {
                return allCallsUseScopedArena(tree, function, index);
            }
        }
        return false;
    }
    return false;
}

fn allCallsUseScopedArena(tree: *const Ast, function: file_model.FnInfo, parameter: usize) bool {
    var references: usize = 0;
    for (tree.tokens.items(.tag), 0..) |tag, index| {
        const token: Ast.TokenIndex = @intCast(index);
        if (tag == .builtin and (std.mem.eql(u8, tree.tokenSlice(token), "@field") or
            std.mem.eql(u8, tree.tokenSlice(token), "@export"))) return false;
        if (tag != .identifier or token == function.name_token) continue;
        if (std.mem.eql(u8, tree.tokenSlice(token), function.name)) references += 1;
    }
    var calls: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(index)) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(call.ast.fn_expr)), function.name)) continue;
        if (parameter >= call.ast.params.len or !argumentHasArenaCleanup(tree, call.ast.params[parameter])) return false;
        calls += 1;
    }
    return calls != 0 and calls == references;
}

fn argumentHasArenaCleanup(tree: *const Ast, argument: Ast.Node.Index) bool {
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, argument) orelse return false;
    if (call.ast.params.len != 0 or tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
    const access = tree.nodeData(call.ast.fn_expr).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(access[1]), "allocator") or tree.nodeTag(access[0]) != .identifier) return false;
    const receiver = tree.tokenSlice(tree.nodeMainToken(access[0]));
    const anchor = tree.firstToken(argument);
    const body_start = enclosingBodyStart(tree, anchor) orelse return false;
    var declaration: ?Ast.full.VarDecl = null;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const candidate = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
        const name_token = candidate.ast.mut_token + 1;
        if (name_token < body_start or name_token >= anchor) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), receiver)) continue;
        if (declaration) |previous| {
            if (previous.ast.mut_token > candidate.ast.mut_token) continue;
        }
        declaration = candidate;
    }
    const decl = declaration orelse return false;
    const initializer = decl.ast.init_node.unwrap() orelse return false;
    const init_call = tree.fullCall(&buffer, initializer) orelse return false;
    if (tree.nodeTag(init_call.ast.fn_expr) != .field_access) return false;
    const init_access = tree.nodeData(init_call.ast.fn_expr).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(init_access[1]), "init")) return false;
    if (!std.mem.eql(u8, tree.getNodeSource(init_access[0]), "std.heap.ArenaAllocator")) return false;
    if (!importsStandardLibrary(tree)) return false;
    return hasImmediateCleanup(tree, tree.lastToken(initializer) + 1, anchor, receiver);
}

fn enclosingBodyStart(tree: *const Ast, anchor: Ast.TokenIndex) ?Ast.TokenIndex {
    var result: ?Ast.TokenIndex = null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .fn_decl) continue;
        const body = tree.nodeData(@enumFromInt(index)).node_and_node[1];
        const start = tree.firstToken(body);
        if (start > anchor or tree.lastToken(body) < anchor) continue;
        if (result == null or start > result.?) result = start;
    }
    return result;
}

fn importsStandardLibrary(tree: *const Ast) bool {
    for (tree.rootDecls()) |node| {
        const decl = tree.fullVarDecl(node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(decl.ast.mut_token + 1), "std")) continue;
        const initializer = decl.ast.init_node.unwrap() orelse return false;
        return std.mem.eql(u8, tree.getNodeSource(initializer), "@import(\"std\")");
    }
    return false;
}

fn hasImmediateCleanup(tree: *const Ast, start: Ast.TokenIndex, anchor: Ast.TokenIndex, receiver: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    if (start + 7 >= anchor) return false;
    if (tags[start] != .semicolon or tags[start + 1] != .keyword_defer or
        tags[start + 2] != .identifier or tags[start + 3] != .period or
        tags[start + 4] != .identifier or tags[start + 5] != .l_paren or
        tags[start + 6] != .r_paren or tags[start + 7] != .semicolon) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(start + 2), receiver) or
        !std.mem.eql(u8, tree.tokenSlice(start + 4), "deinit")) return false;
    var token = start + 8;
    while (token < anchor) : (token += 1) {
        if (tags[token] == .l_brace or tags[token] == .r_brace) return false;
        if (tags[token] == .identifier and std.mem.eql(u8, tree.tokenSlice(token), receiver)) return false;
    }
    return true;
}

/// SEMANTIC allocation signal: returns true iff some identifier operand in the
/// first-try expression `[start, end)` resolves to type `std.mem.Allocator`
/// AND is in receiver position (followed by `.`).  Requiring receiver position
/// avoids signalling on pool/builder patterns like `pool.put(allocator, bytes)`
/// where the allocator is passed as an argument — the allocation goes into
/// the pool's internal buffer, not directly to the caller, so there is no
/// individual per-field leak from the struct-literal failure.
/// No-op (false) when the type engine is absent.
fn firstTryUsesAllocator(
    cache: *file_cache_mod.FileCache,
    ident_nodes: *const std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index),
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    var t = start;
    while (t < end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        const node = ident_nodes.get(t) orelse continue;
        const tyname = cache.typeNameOfNode(node) orelse continue;
        if (!std.mem.eql(u8, tyname, "Allocator")) continue;
        // Allocator must be in receiver position (followed by '.') — e.g.
        // `gpa.alloc(T, n)`.  If followed by ',' or ')' the allocator is
        // an argument to a pool/builder and does not individually leak.
        if (t + 1 < end and tags[t + 1] == .period) return true;
    }
    return false;
}

/// Returns true iff the token range [start, end) contains an identifier or
/// builtin whose slice (case-insensitively) contains an allocation signal:
/// `alloc`, `dupe`, `clone`, `create`, or `ownedslice` (covers
/// `toOwnedSlice`).  These are the calls that hand back an owned resource a
/// failing later `try` would leak.  Decoders/parsers (`read_*`, `parse*`)
/// return value types and match no signal, so they are suppressed.
///
/// Precision rules to avoid over-signalling:
///   - "alloc" in any form (the common allocator variable name, allocPrint,
///     allocate, …) only signals when in method-call position (preceded by
///     `.`) or direct-call position (followed by `(`).  Bare `allocator`
///     passed as an argument to a pool or builder — e.g.
///     `pool.put(allocator, bytes)` — does NOT signal because the
///     allocation goes into the pool's internal buffer, not to the caller.
///   - "create" only signals for method calls (preceded by `.`).
///   - "dupe", "clone", "ownedslice" signal in any position.
fn tryExprAllocates(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    var t = start;
    while (t < end) : (t += 1) {
        if (tags[t] != .identifier and tags[t] != .builtin) continue;
        const s = tree.tokenSlice(t);
        if (containsIgnoreCase(s, "dupe") or
            containsIgnoreCase(s, "clone") or
            containsIgnoreCase(s, "ownedslice")) return true;
        // "alloc" in any form: require method-call (preceded by '.') or
        // direct-call (followed by '(') position to exclude allocator
        // variable names passed as arguments.
        if (containsIgnoreCase(s, "alloc")) {
            const before_is_dot = t > start and tags[t - 1] == .period;
            const after_is_paren = t + 1 < end and tags[t + 1] == .l_paren;
            if (before_is_dot or after_is_paren) return true;
        }
        // "create": only signal for method calls (preceded by '.')
        if (containsIgnoreCase(s, "create") and t > start and tags[t - 1] == .period) return true;
    }
    return false;
}

/// Returns true if within 100 tokens before `anchor` there is a declaration
/// of the form `IDENT_ARENA . allocator ( )`, indicating the function is
/// using an arena-backed allocator.  In that case every allocation in this
/// scope is freed when the arena resets, so no per-field leak is possible.
fn nearbyArenaAllocator(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    anchor: Ast.TokenIndex,
) bool {
    const back: Ast.TokenIndex = 200;
    const start: Ast.TokenIndex = if (anchor >= back) anchor - back else 0;
    var k = start;
    while (k + 4 < anchor) : (k += 1) {
        if (tags[k] != .identifier) continue;
        if (std.ascii.findIgnoreCase(tree.tokenSlice(k), "arena") == null) continue;
        if (tags[k + 1] != .period) continue;
        if (tags[k + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k + 2), "allocator")) continue;
        if (tags[k + 3] != .l_paren) continue;
        if (tags[k + 4] != .r_paren) continue;
        return true;
    }
    return false;
}

/// Returns true if within the backward scan from `anchor` (up to 1000 tokens)
/// there is an `errdefer IDENT_ARENA . deinit` pattern.  Long function bodies
/// can place `errdefer arena.deinit()` hundreds of tokens before the struct
/// literal, beyond the 200-token window of `nearbyArenaAllocator`.  When such
/// an errdefer exists, all arena-backed allocations in the function are cleaned
/// up on error, so no per-field leak is possible.
fn enclosingFnHasArenaErrdefer(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    anchor: Ast.TokenIndex,
) bool {
    const back: Ast.TokenIndex = 1000;
    const start: Ast.TokenIndex = if (anchor >= back) anchor - back else 0;
    var k = start;
    while (k + 4 < anchor) : (k += 1) {
        if (tags[k] != .keyword_errdefer) continue;
        if (tags[k + 1] != .identifier) continue;
        if (std.ascii.findIgnoreCase(tree.tokenSlice(k + 1), "arena") == null) continue;
        if (tags[k + 2] != .period) continue;
        if (tags[k + 3] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k + 3), "deinit")) continue;
        return true;
    }
    return false;
}

/// Returns true if the first-try expression `[start, end)` passes an
/// "arena"-named identifier as a CALL ARGUMENT (in argument position,
/// i.e. preceded by `(` or `,`).  This covers the common pattern of
/// passing an arena allocator parameter directly — e.g.
/// `pool.toOwnedSlice(arena)` — where `arena: std.mem.Allocator` is a
/// function parameter rather than derived from `arena.allocator()`.
/// In that case, allocations go into the arena and are freed as a unit
/// when the caller destroys the arena, so no individual field leaks.
fn tryExprPassesArena(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    if (start >= end) return false;
    var t = start;
    while (t < end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (std.ascii.findIgnoreCase(tree.tokenSlice(t), "arena") == null) continue;
        // Require argument position: preceded by '(' or ','.
        if (t == start) continue; // first token, no predecessor
        const prev = tags[t - 1]; // zbc-disable-line: index-minus-one-without-zero-guard — t==start is skipped above; t>start>=1 in fall-through
        if (prev == .l_paren or prev == .comma) return true;
    }
    return false;
}

/// Case-insensitive substring test (`needle` must be lowercase).
fn containsIgnoreCase(haystack: []const u8, needle: []const u8) bool {
    if (needle.len == 0 or haystack.len < needle.len) return false;
    var i: usize = 0;
    outer: while (i + needle.len <= haystack.len) : (i += 1) {
        var j: usize = 0;
        while (j < needle.len) : (j += 1) {
            if (std.ascii.toLower(haystack[i + j]) != needle[j]) continue :outer;
        }
        return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    second_tok: Ast.TokenIndex,
    field1: []const u8,
    field2: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`.{s} = try ...` followed by `.{s} = try ...` in the same initializer — if the second `try` fails, the allocation from the first leaks because `errdefer` cannot appear inside a struct literal; bind each to a local with `errdefer` first",
        .{ field1, field2 },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, second_tok),
        .end = Pos.fromTokenEnd(tree, second_tok + 3),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "struct-literal-multiple-try: fires on two try fields" {
    try testing.expectFires(check, R,
        \\fn parse(gpa: Allocator, parser: *Parser) !Ast {
        \\    return Ast{
        \\        .extra_data = try parser.extra_data.toOwnedSlice(gpa),
        \\        .errors     = try parser.errors.toOwnedSlice(gpa),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: single try field does not fire" {
    try testing.expectNoFire(check,
        \\fn parse(gpa: Allocator, parser: *Parser) !Ast {
        \\    return Ast{
        \\        .extra_data = try parser.extra_data.toOwnedSlice(gpa),
        \\        .errors     = &.{},
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: non-try second field does not fire" {
    try testing.expectNoFire(check,
        \\fn build() Foo {
        \\    return Foo{
        \\        .a = compute(),
        \\        .b = 42,
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: fires in return with named init" {
    try testing.expectFires(check, R,
        \\fn makeNode(gpa: Allocator) !Node {
        \\    return Node{
        \\        .name  = try gpa.dupe(u8, "hello"),
        \\        .value = try gpa.dupe(u8, "world"),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: decoder tries (no allocation) do not fire" {
    try testing.expectNoFire(check,
        \\fn readHeader(self: *Decoder) !FrameHeader {
        \\    return .{
        \\        .type = try self.read_enum(FrameType),
        \\        .channel = try self.read_enum(Channel),
        \\        .size = try self.read_int(u32),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: parseUnsigned tries do not fire" {
    try testing.expectNoFire(check,
        \\fn parseVersion(arg_major: []const u8, arg_minor: []const u8) !Version {
        \\    return .{
        \\        .major = try std.fmt.parseUnsigned(u8, arg_major, 10),
        \\        .minor = try std.fmt.parseUnsigned(u8, arg_minor, 10),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: alloc.alloc tries fire" {
    try testing.expectFires(check, R,
        \\fn makeLexer(alloc: Allocator, n_words: usize) !Lexer {
        \\    return .{
        \\        .ident      = try alloc.alloc(u64, n_words),
        \\        .newline    = try alloc.alloc(u64, n_words),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: deepClone tries fire" {
    try testing.expectFires(check, R,
        \\fn cloneIf(allocator: Allocator, el: *If) !If {
        \\    return .{
        \\        .test_ = try el.test_.deepClone(allocator),
        \\        .yes = try el.yes.deepClone(allocator),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: try in nested call args does not fire" {
    try testing.expectNoFire(check,
        \\fn callFn(a: u8, b: u8) void {
        \\    process(a, b);
        \\}
        \\
    );
}

test "struct-literal-multiple-try: factory fn (create prefix) does not fire" {
    try testing.expectNoFire(check,
        \\fn buildStep(b: *Build) !GhosttyI18n {
        \\    return .{
        \\        .update_step = try createUpdateStep(b),
        \\        .steps = try steps.toOwnedSlice(b.allocator),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: arena allocator does not fire" {
    try testing.expectNoFire(check,
        \\fn deriveFontConfig(arena: ArenaAllocator, config: *const Config) !FontConfig {
        \\    const alloc = arena.allocator();
        \\    return .{
        \\        .@"font-family" = try config.@"font-family".clone(alloc),
        \\        .@"font-style"  = try config.@"font-style".clone(alloc),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: method .create fires" {
    try testing.expectFires(check, R,
        \\fn makeNode(gpa: Allocator) !Node {
        \\    return .{
        \\        .left  = try gpa.create(LeftNode),
        \\        .right = try gpa.create(RightNode),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: arena parameter passed to toOwnedSlice does not fire" {
    // When the arena allocator is passed directly as a parameter — e.g.
    // `fn f(arena: std.mem.Allocator)` — and the first-try expression is
    // `try x.toOwnedSlice(arena)`, the allocation is arena-backed and freed
    // as a unit; no individual per-field leak is possible.
    try testing.expectNoFire(check,
        \\fn writeRecord(arena: Allocator, out: *ArrayList(u8), map: *ArrayList(u32)) !Result {
        \\    return Result{
        \\        .bytes = try out.toOwnedSlice(arena),
        \\        .source_offsets = try map.toOwnedSlice(arena),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: pool.put(allocator, bytes) does not fire" {
    // pool.put(allocator, bytes) passes the allocator as an ARGUMENT to a
    // pool/builder — all puts go into the pool's internal buffer and are freed
    // as a unit when the pool is destroyed.  The `allocator` variable name
    // contains "alloc" but is NOT in receiver position, so neither the
    // type-based nor name-based allocation signals should fire.
    try testing.expectNoFire(check,
        \\fn writeRecord(allocator: Allocator, pool: *PoolBuilder, ln: Line) !Record {
        \\    return Record{
        \\        .source = try pool.put(allocator, ln.source),
        \\        .tokens = try pool.put(allocator, ln.tokens),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: errdefer arena.deinit() in enclosing fn suppresses" {
    // Long function bodies place `errdefer arena.deinit()` hundreds of tokens
    // before the struct literal — beyond the nearbyArenaAllocator window.
    // The enclosingFnHasArenaErrdefer check covers this case.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const ArenaAllocator = std.heap.ArenaAllocator;
        \\const ArrayList = std.ArrayListUnmanaged;
        \\fn buildModel(gpa: std.mem.Allocator, count: usize) !Model {
        \\    var arena = ArenaAllocator.init(gpa);
        \\    errdefer arena.deinit();
        \\    const a = arena.allocator();
        \\    var names: ArrayList([]const u8) = .empty;
        \\    var fns: ArrayList([]const u8) = .empty;
        \\    var i: usize = 0;
        \\    while (i < count) : (i += 1) {
        \\        try names.append(a, "x");
        \\        try fns.append(a, "y");
        \\    }
        \\    return .{
        \\        .names = try names.toOwnedSlice(a),
        \\        .fns = try fns.toOwnedSlice(a),
        \\    };
        \\}
        \\const Model = struct { names: [][]const u8, fns: [][]const u8 };
        \\
    );
}

test "struct-literal-multiple-try: no errdefer arena still fires" {
    // Control: without errdefer arena.deinit(), the rule must still fire
    // so the suppressor is not inadvertently always-true.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn buildPair(gpa: std.mem.Allocator) !Pair {
        \\    return Pair{
        \\        .a = try gpa.alloc(u8, 4),
        \\        .b = try gpa.alloc(u8, 4),
        \\    };
        \\}
        \\const Pair = struct { a: []u8, b: []u8 };
        \\
    );
}

test "skript residual: private copy helper uses caller-owned arena" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn run(gpa: std.mem.Allocator) !void {
        \\    var scope = std.heap.ArenaAllocator.init(gpa);
        \\    defer scope.deinit();
        \\    const pair = try duplicate(scope.allocator());
        \\    _ = pair;
        \\}
    );
}

test "skript residual: private copy helper also called with owned allocator" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn run(gpa: std.mem.Allocator) !Pair {
        \\    var scope = std.heap.ArenaAllocator.init(gpa);
        \\    defer scope.deinit();
        \\    _ = try duplicate(scope.allocator());
        \\    return duplicate(gpa);
        \\}
    );
}

test "skript residual: cloned range values do not own allocations" {
    try testing.expectNoFire(check,
        \\const Range = struct { start: u32, len: u32 };
        \\const RangeAlias = Range;
        \\const Pair = struct { first: Range, second: Range };
        \\fn cloneRange(start: u32) !RangeAlias {
        \\    return .{ .start = start, .len = 1 };
        \\}
        \\pub fn run() !Pair {
        \\    return .{
        \\        .first = try cloneRange(0),
        \\        .second = try cloneRange(1),
        \\    };
        \\}
    );
}

test "skript residual: cloned buffer values still own allocations" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Buffer = struct { bytes: []u8 };
        \\const Pair = struct { first: Buffer, second: Buffer };
        \\fn cloneBuffer(memory: std.mem.Allocator) !Buffer {
        \\    return .{ .bytes = try memory.dupe(u8, "buffer") };
        \\}
        \\pub fn run(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try cloneBuffer(memory),
        \\        .second = try cloneBuffer(memory),
        \\    };
        \\}
    );
}
