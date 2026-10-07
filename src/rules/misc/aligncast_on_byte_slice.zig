//! Detects `@alignCast(expr.ptr)` — asserting alignment on a raw byte pointer
//! derived from a `[]const u8` or `[]u8` slice.  The alignment of `.ptr` from a
//! byte slice is determined by the allocator, not the element type; for network
//! buffers, file content, or serialised binary data the pointer can land at any
//! byte offset.  The runtime alignment check in `@alignCast` panics in Safe
//! builds when the offset is not a multiple of the target alignment.
//!
//! Real-world instances (all Zig):
//!   - oven-sh/bun#27082 (Postgres binary arrays): `@ptrCast(@alignCast(@constCast(bytes.ptr)))`
//!     on network-received data; panicked non-deterministically on odd-offset packets.
//!   - oven-sh/bun#27281 (sourcemap deserialisation): `@ptrCast(@alignCast(raw.ptr))`
//!     on a memory-mapped file; panicked on unaligned mmap regions.
//!   - oven-sh/bun#27384 (tagged-pointer sockets): `@alignCast(data.ptr)` producing an
//!     assumed-4-byte-aligned pointer into a tagged-pointer arena.
//!   - oven-sh/bun#27290 (HTTP response parsing): `@alignCast(@constCast(bytes.ptr))`.
//!     Fix in all cases: use `std.mem.readInt` / `@memcpy` into a local aligned struct.
//!
//! Detection (Tier 1, flat token walk):
//!   Form A: `@alignCast ( identifier . identifier("ptr") )` — 6 tokens
//!   Form B: `@alignCast ( @constCast ( identifier . identifier("ptr") ) )` — 9 tokens
//!   Fire at the `@alignCast` builtin token.
//!   `@alignCast(align1_ptr)` on explicitly `align(1)` pointers (common in readInt
//!   helpers) would also fire — acceptable since those should use `align(1)` casts
//!   without `@alignCast`, which is the safe idiom.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const file_model = @import("../../model/file_model.zig");
const std_types = @import("../../model/std_type_query.zig");
const tokens = @import("../../ast/tokens.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "aligncast-on-byte-slice";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .aligncast_on_byte_slice)) return;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    // Map identifier-reference nodes by main token, so the `.ptr` receiver can
    // be resolved to its slice element type (is it actually a BYTE slice?).
    // Empty/unused when the type engine is absent.
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
    while (t + 5 <= last_tok) : (t += 1) {
        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@alignCast")) continue;
        if (tags[t + 1] != .l_paren) continue;

        // Form A: @alignCast ( identifier . identifier("ptr") )
        if (tags[t + 2] == .identifier and
            tags[t + 3] == .period and
            tags[t + 4] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 4), "ptr") and
            tags[t + 5] == .r_paren)
        {
            // SEMANTIC: suppress when the receiver resolves to a slice whose
            // element is NOT byte-sized (`[]u32`, `[]Struct`, …) — its `.ptr`
            // is already >1-aligned, so this is not the byte-slice bug class
            // (true to the rule's name).  Byte slices (`[]u8`/`[]const u8`,
            // element align 1) and unresolved receivers fall through.
            if (sliceElemNotByteSized(cache, &ident_nodes, t + 2)) continue;
            // SEMANTIC: suppress only a guarded std.mem.Allocator context cast.
            if (try receiverIsAllocator(tree, cache, &ident_nodes, t, t + 2)) continue;
            if (receiverAlignmentProven(tree, cache, t, t + 2)) continue;
            try report(gpa, problems, tree, t, t + 5);
            continue;
        }

        // Form B: @alignCast ( @constCast ( identifier . identifier("ptr") ) )
        if (t + 8 <= last_tok and
            tags[t + 2] == .builtin and
            std.mem.eql(u8, tree.tokenSlice(t + 2), "@constCast") and
            tags[t + 3] == .l_paren and
            tags[t + 4] == .identifier and
            tags[t + 5] == .period and
            tags[t + 6] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 6), "ptr") and
            tags[t + 7] == .r_paren and
            tags[t + 8] == .r_paren)
        {
            if (sliceElemNotByteSized(cache, &ident_nodes, t + 4)) continue;
            if (try receiverIsAllocator(tree, cache, &ident_nodes, t, t + 4)) continue;
            if (receiverAlignmentProven(tree, cache, t, t + 4)) continue;
            try report(gpa, problems, tree, t, t + 8);
            continue;
        }
    }
}

/// Placement storage is safe only with a proof about this address and this
/// target. Neither an allocation method's spelling nor unrelated `align`
/// tokens establish that proof.
fn receiverAlignmentProven(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    anchor: Ast.TokenIndex,
    recv_tok: Ast.TokenIndex,
) bool {
    const body = bodyContaining(tree, anchor) orelse return false;
    const target = castTargetTypeName(tree, anchor) orelse return false;
    const name = tree.tokenSlice(recv_tok);
    const target_alignment = castTargetAlignment(tree, anchor);
    if (target_alignment == null) {
        // An unsupported aligned pointer shape is unknown, not a request
        // for the element's natural alignment.
        const range = castTargetTypeRange(tree, anchor) orelse return false;
        var t = range.first;
        while (t <= range.last) : (t += 1) {
            if (tree.tokenTag(t) == .keyword_align) return false;
        }
    }
    if (validatedAddressAlignment(tree, cache, body, anchor, name, target, target_alignment)) return true;
    if (receiverMutatedAfter(tree, body.first, body.first, anchor, name)) return false;
    if (receiverAddressEscapedBefore(tree, body.first, anchor, name)) return false;
    if (localTypeNodeBefore(tree, name, anchor, body.first)) |type_node| {
        if (alignedSliceType(tree, cache, type_node, target, target_alignment)) return true;
    }
    const fn_decl = tokens.enclosingFnDecl(tree, anchor) orelse return false;
    var proto_buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return false;
    var it = proto.iterate(tree);
    while (it.next()) |param| {
        const nt = param.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(nt), name)) continue;
        if (param.type_expr) |type_node|
            return alignedSliceType(tree, cache, type_node, target, target_alignment);
        return false;
    }
    // The allocator's element alignment alone cannot prove an explicitly
    // stronger pointer alignment.
    if (target_alignment != null) return false;
    const rhs = std_types.aliasInitializer(cache, tree, recv_tok) orelse return false;
    const tags = tree.tokens.items(.tag);
    const first = rhs.first + @as(u32, if (tags[rhs.first] == .keyword_try) 1 else 0);
    // The binding must be the real std.mem.Allocator, not a duck-typed
    // method that happens to be named alignedAlloc.
    if (first + 8 > rhs.last or tags[first] != .identifier or
        tags[first + 1] != .period or
        !std.mem.eql(u8, tree.tokenSlice(first + 2), "alignedAlloc") or
        tags[first + 3] != .l_paren or
        !receiverTypeIsAllocator(tree, cache, first) or
        !std.mem.eql(u8, tree.tokenSlice(first + 4), "u8") or
        tags[first + 5] != .comma) return false;
    const alignment_first = first + 6;
    var alignment_last = alignment_first;
    while (alignment_last < rhs.last and tags[alignment_last] != .comma) : (alignment_last += 1) {
        if (tags[alignment_last] == .l_paren)
            alignment_last = tokens.matchParen(tags, alignment_last, rhs.last) orelse return false;
    }
    if (alignment_last >= rhs.last) return false;
    if (alignment_first + 5 == alignment_last and
        tags[alignment_first] == .period and
        std.mem.eql(u8, tree.tokenSlice(alignment_first + 1), "of") and
        tags[alignment_first + 2] == .l_paren and
        tags[alignment_first + 4] == .r_paren and
        std.mem.eql(u8, tree.tokenSlice(alignment_first + 3), target))
        return true;
    return false;
}

fn alignedSliceType(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    node: Ast.Node.Index,
    target: []const u8,
    target_alignment: ?std_types.Range,
) bool {
    const first = tree.firstToken(node);
    const last = tree.lastToken(node);
    const tags = tree.tokens.items(.tag);
    if (first + 5 > last or tags[first] != .l_bracket or tags[first + 1] != .r_bracket or
        tags[first + 2] != .keyword_align or tags[first + 3] != .l_paren) return false;
    const end = tokens.matchParen(tags, first + 3, last) orelse return false;
    if (target_alignment) |required|
        return sameAlignmentValue(tree, cache, .{ .first = first + 4, .last = end - 1 }, required);
    return alignmentExpr(tree, cache, first + 4, end - 1, target, 0).covers_target;
}

const AlignmentProof = struct { power_of_two: bool = false, covers_target: bool = false };

/// @max of two known alignment values remains a multiple of each. Arbitrary
/// numeric lower bounds do not: max(3, alignOf(u16)) is not aligned to u16.
fn alignmentExpr(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    target: []const u8,
    depth: u8,
) AlignmentProof {
    if (first > last or depth == 8) return .{};
    const tags = tree.tokens.items(.tag);
    if (first == last and tags[first] == .identifier) {
        const rhs = std_types.aliasInitializer(cache, tree, first) orelse return .{};
        return alignmentExpr(tree, cache, rhs.first, rhs.last, target, depth + 1);
    }
    if (first == last and tags[first] == .number_literal) {
        const value = std.fmt.parseInt(u64, tree.tokenSlice(first), 0) catch return .{};
        return .{ .power_of_two = value != 0 and value & (value - 1) == 0 };
    }
    if (tags[first] != .builtin or first + 3 > last or tags[first + 1] != .l_paren or tags[last] != .r_paren)
        return .{};
    if (std.mem.eql(u8, tree.tokenSlice(first), "@alignOf")) {
        return .{ .power_of_two = true, .covers_target = first + 3 == last and
            std.mem.eql(u8, tree.tokenSlice(first + 2), target) };
    }
    if (!std.mem.eql(u8, tree.tokenSlice(first), "@max")) return .{};
    var comma = first + 2;
    while (comma < last and tags[comma] != .comma) : (comma += 1) {
        if (tags[comma] == .l_paren)
            comma = tokens.matchParen(tags, comma, last) orelse return .{};
    }
    if (comma >= last) return .{};
    const left = alignmentExpr(tree, cache, first + 2, comma - 1, target, depth + 1);
    const right = alignmentExpr(tree, cache, comma + 1, last - 1, target, depth + 1);
    return .{ .power_of_two = left.power_of_two and right.power_of_two, .covers_target = left.power_of_two and right.power_of_two and
        (left.covers_target or right.covers_target) };
}

/// Compare constant alignment values by their binding, not their spelling.
/// An explicit pointer alignment is a comptime alignment by Zig's type
/// contract. Opaque calls and mutable bindings still give no identity here.
fn sameAlignmentValue(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    left: std_types.Range,
    right: std_types.Range,
) bool {
    const lhs = alignmentValue(tree, cache, left, 0) orelse return false;
    const rhs = alignmentValue(tree, cache, right, 0) orelse return false;
    if (lhs.first == rhs.first and lhs.last == rhs.last) return true;
    if (lhs.first == lhs.last and rhs.first == rhs.last and
        tree.tokenTag(lhs.first) == .number_literal and tree.tokenTag(rhs.first) == .number_literal)
    {
        const a = std.fmt.parseInt(u64, tree.tokenSlice(lhs.first), 0) catch return false;
        const b = std.fmt.parseInt(u64, tree.tokenSlice(rhs.first), 0) catch return false;
        return a == b;
    }
    const a = std_types.declaration(cache, tree, lhs.first, lhs.last, .{}) orelse return false;
    const b = std_types.declaration(cache, tree, rhs.first, rhs.last, .{}) orelse return false;
    return std.mem.eql(u8, a.module, b.module) and std.mem.eql(u8, a.name, b.name);
}

fn alignmentValue(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    written: std_types.Range,
    depth: u8,
) ?std_types.Range {
    if (depth == 8 or written.first > written.last) return null;
    var range = written;
    if (tree.tokenTag(range.first) == .keyword_comptime) range.first += 1;
    if (range.first > range.last) return null;
    if (range.first == range.last and tree.tokenTag(range.first) == .identifier) {
        const rhs = std_types.aliasInitializer(cache, tree, range.first) orelse return null;
        return alignmentValue(tree, cache, rhs, depth + 1);
    }
    if (alignmentExpr(tree, cache, range.first, range.last, "", 0).power_of_two)
        return range;
    const declaration = std_types.declaration(cache, tree, range.first, range.last, .{}) orelse return null;
    if (declaration.name.len == 0) return null;
    return range;
}

fn validatedAddressAlignment(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    body: BodyRange,
    before: Ast.TokenIndex,
    name: []const u8,
    target: []const u8,
    target_alignment: ?std_types.Range,
) bool {
    const tags = tree.tokens.items(.tag);
    var cast_scope = ScopeStack.init(tree, body.first);
    cast_scope.advanceTo(before);
    var scope = ScopeStack.init(tree, body.first);
    var t = body.first;
    while (t + 12 < before) : (t += 1) {
        scope.advanceTo(t);
        if (!beginsStatement(tree, t) or !sameScope(scope.current(), cast_scope.current())) continue;
        var condition: Ast.TokenIndex = undefined;
        var close: Ast.TokenIndex = undefined;
        const is_rejection = tags[t] == .keyword_if and tags[t + 1] == .l_paren;
        if (is_rejection) {
            condition = t + 2;
            close = tokens.matchParen(tags, t + 1, before) orelse continue;
        } else {
            // Resolve the assertion's declaration. A custom std.debug.assert
            // function is not a validation operation.
            var lp = t;
            while (lp < before and tags[lp] != .l_paren and tags[lp] != .semicolon) : (lp += 1) {}
            if (lp == before or tags[lp] != .l_paren or
                !std_types.isType(cache, tree, t, lp - 1, "debug", "assert", .{})) continue;
            condition = lp + 1;
            close = tokens.matchParen(tags, lp, before) orelse continue;
        }
        if (condition + 10 > close or tags[condition] != .builtin or
            !std.mem.eql(u8, tree.tokenSlice(condition), "@intFromPtr") or
            tags[condition + 1] != .l_paren or
            !std.mem.eql(u8, tree.tokenSlice(condition + 2), name) or
            tags[condition + 3] != .period or
            !std.mem.eql(u8, tree.tokenSlice(condition + 4), "ptr") or
            tags[condition + 5] != .r_paren or tags[condition + 6] != .percent) continue;
        const comparison = close - 2;
        if (tags[comparison] != (if (is_rejection) std.zig.Token.Tag.bang_equal else .equal_equal) or
            !std.mem.eql(u8, tree.tokenSlice(close - 1), "0")) continue;
        const modulus: std_types.Range = .{ .first = condition + 7, .last = comparison - 1 };
        // With an explicit alignment, proving only the element's natural
        // alignment is too weak. Match the exact constant used by the type.
        if (target_alignment) |required| {
            if (!sameAlignmentValue(tree, cache, modulus, required)) continue;
        } else if (!alignmentExpr(tree, cache, modulus.first, modulus.last, target, 0).covers_target) continue;
        const end = if (is_rejection)
            guardFailureEnd(tree, close, before) orelse continue
        else if (close + 1 < before and tags[close + 1] == .semicolon)
            close + 1
        else
            continue;
        if (receiverMutatedAfter(tree, body.first, end, before, name) or
            receiverAddressEscapedBefore(tree, body.first, before, name)) continue;
        return true;
    }
    return false;
}

/// True iff the receiver identifier at `recv_tok` resolves to a slice whose
/// element is provably wider than a byte (≥2-byte alignment) — so its `.ptr`
/// is already aligned and this is NOT a byte-slice `@alignCast`.  False for
/// byte slices, unresolved receivers, or unknown element alignment (the rule
/// then proceeds with its syntactic checks).
fn sliceElemNotByteSized(
    cache: *file_cache_mod.FileCache,
    ident_nodes: *const std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index),
    recv_tok: Ast.TokenIndex,
) bool {
    const node = ident_nodes.get(recv_tok) orelse return false;
    const byte_sized = cache.sourcePtrElemByteSized(node) orelse return false;
    return !byte_sized;
}

const BodyRange = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

/// True only for a guarded allocator-context recovery.  The receiver must
/// resolve to the actual std.mem.Allocator type, the cast target must be a
/// declared type, and the matching vtable check must dominate the cast.
fn receiverIsAllocator(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    ident_nodes: *const std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index),
    align_tok: Ast.TokenIndex,
    recv_tok: Ast.TokenIndex,
) !bool {
    _ = ident_nodes.get(recv_tok) orelse return false;
    if (!receiverTypeIsAllocator(tree, cache, recv_tok)) return false;
    const target_name = castTargetTypeName(tree, align_tok) orelse return false;
    const model = cache.fileModel() catch return false;
    if (model.findType(target_name) == null) return false;
    const body = bodyContaining(tree, align_tok) orelse return false;
    const recv_name = tree.tokenSlice(recv_tok);
    if (hasDirectVtableGuard(tree, model, body, align_tok, recv_name, target_name, false, false))
        return true;
    return hasHelperVtableGuard(tree, model, cache, body, align_tok, recv_name, target_name);
}

fn receiverTypeIsAllocator(tree: *const Ast, cache: *file_cache_mod.FileCache, recv_tok: Ast.TokenIndex) bool {
    const body = bodyContaining(tree, recv_tok) orelse return false;
    const recv_name = tree.tokenSlice(recv_tok);
    if (localTypeNodeBefore(tree, recv_name, recv_tok, body.first)) |type_node|
        return allocatorTypeNode(tree, cache, type_node);

    const fn_decl = tokens.enclosingFnDecl(tree, recv_tok) orelse return false;
    var proto_buf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return false;
    var it = proto.iterate(tree);
    while (it.next()) |param| {
        const name_tok = param.name_token orelse continue;
        if (name_tok != recv_tok and
            !std.mem.eql(u8, tree.tokenSlice(name_tok), recv_name))
            continue;
        const type_node = param.type_expr orelse return false;
        return allocatorTypeNode(tree, cache, type_node);
    }
    return false;
}

fn localTypeNodeBefore(
    tree: *const Ast,
    name: []const u8,
    before: Ast.TokenIndex,
    body_first: Ast.TokenIndex,
) ?Ast.Node.Index {
    const tags = tree.tokens.items(.tag);
    var best: ?Ast.Node.Index = null;
    var best_tok: Ast.TokenIndex = 0;
    var at_use = ScopeStack.init(tree, body_first);
    at_use.advanceTo(before);
    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        switch (tree.nodeTag(node)) {
            .global_var_decl, .local_var_decl, .simple_var_decl, .aligned_var_decl => {},
            else => continue,
        }
        const decl = tree.fullVarDecl(node) orelse continue;
        const name_tok = decl.ast.mut_token + 1;
        if (name_tok < body_first or name_tok >= before or
            name_tok >= tree.tokens.len or tags[name_tok] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(name_tok), name))
            continue;
        var at_decl = ScopeStack.init(tree, body_first);
        at_decl.advanceTo(name_tok);
        if (!sameScope(at_decl.current(), at_use.current())) continue;
        if (name_tok > best_tok) {
            best = decl.ast.type_node.unwrap();
            best_tok = name_tok;
        }
    }
    return best;
}

fn allocatorTypeNode(tree: *const Ast, cache: *file_cache_mod.FileCache, node: Ast.Node.Index) bool {
    return std_types.isType(cache, tree, tree.firstToken(node), tree.lastToken(node), "mem", "Allocator", .{});
}

fn castTargetTypeName(tree: *const Ast, align_tok: Ast.TokenIndex) ?[]const u8 {
    const range = castTargetTypeRange(tree, align_tok) orelse return null;
    var last_name: ?Ast.TokenIndex = null;
    var t = range.first;
    while (t <= range.last) : (t += 1) {
        if (tree.tokenTag(t) == .identifier) last_name = t;
    }
    return if (last_name) |name_tok| tree.tokenSlice(name_tok) else null;
}

fn castTargetAlignment(tree: *const Ast, align_tok: Ast.TokenIndex) ?std_types.Range {
    const range = castTargetTypeRange(tree, align_tok) orelse return null;
    const tags = tree.tokens.items(.tag);
    var t = range.first;
    if (tags[t] == .question_mark) t += 1;
    if (t > range.last) return null;
    if (tags[t] == .asterisk) {
        t += 1;
    } else if (t + 2 <= range.last and tags[t] == .l_bracket and
        tags[t + 1] == .asterisk and tags[t + 2] == .r_bracket)
    {
        t += 3;
    } else return null;
    if (t + 3 > range.last or tags[t] != .keyword_align or tags[t + 1] != .l_paren) return null;
    const close = tokens.matchParen(tags, t + 1, range.last) orelse return null;
    return .{ .first = t + 2, .last = close - 1 };
}

fn castTargetTypeRange(tree: *const Ast, align_tok: Ast.TokenIndex) ?std_types.Range {
    const tags = tree.tokens.items(.tag);
    var eq: ?Ast.TokenIndex = null;
    var t = align_tok;
    while (t > 0) {
        t -= 1;
        if (tags[t] == .semicolon or tags[t] == .l_brace or
            tags[t] == .r_brace or tags[t] == .keyword_return)
            break;
        if (tags[t] == .equal) {
            eq = t;
            break;
        }
    }
    const equal = eq orelse return null;
    var colon: ?Ast.TokenIndex = null;
    var k = equal;
    while (k > 0) {
        k -= 1;
        if (tags[k] == .semicolon or tags[k] == .l_brace or
            tags[k] == .r_brace or tags[k] == .keyword_return)
            break;
        if (tags[k] == .colon) {
            colon = k;
            break;
        }
    }
    const colon_tok = colon orelse return null;
    if (colon_tok + 1 >= equal) return null;
    return .{ .first = colon_tok + 1, .last = equal - 1 };
}

fn bodyContaining(tree: *const Ast, tok: Ast.TokenIndex) ?BodyRange {
    var best: ?BodyRange = null;
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |entry| {
        const first = tree.firstToken(entry.body);
        const last = tree.lastToken(entry.body);
        if (tok < first or tok > last) continue;
        if (best == null or first >= best.?.first) best = .{ .first = first, .last = last };
    }
    return best;
}

fn sameDeclaredType(model: *const file_model.FileModel, left: []const u8, right: []const u8) bool {
    const left_type = model.findType(left) orelse return false;
    const right_type = model.findType(right) orelse return false;
    return left_type == right_type;
}

fn hasDirectVtableGuard(
    tree: *const Ast,
    model: *const file_model.FileModel,
    body: BodyRange,
    before: Ast.TokenIndex,
    recv_name: []const u8,
    target_name: []const u8,
    requireNoEarlierReturn: bool,
    require_false_on_mismatch: bool,
) bool {
    const tags = tree.tokens.items(.tag);
    // One pass reads the block structure up to the cast; a second, kept
    // beside the scan, answers the scope of each candidate guard without
    // re-reading the prefix once per token.
    var at_cast = ScopeStack.init(tree, body.first);
    at_cast.advanceTo(before);
    const cast_scope = at_cast.current();

    var at_guard = ScopeStack.init(tree, body.first);
    var t = body.first;
    while (t + 10 <= before and t + 10 <= body.last) : (t += 1) {
        at_guard.advanceTo(t);
        if (!beginsStatement(tree, t)) continue;
        if (tags[t] != .keyword_if or tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(t + 2), recv_name) or
            tags[t + 3] != .period or
            !std.mem.eql(u8, tree.tokenSlice(t + 4), "vtable") or
            tags[t + 5] != .bang_equal or
            tags[t + 6] != .ampersand or
            tags[t + 7] != .identifier or
            tags[t + 8] != .period or
            !std.mem.eql(u8, tree.tokenSlice(t + 9), "vtable") or
            tags[t + 10] != .r_paren)
            continue;
        if (requireNoEarlierReturn and hasReturnBefore(tree, body.first, t)) continue;
        if (!sameDeclaredType(model, tree.tokenSlice(t + 7), target_name)) continue;
        if (!sameScope(at_guard.current(), cast_scope)) continue;
        const end = guardFailureEnd(tree, t + 10, body.last) orelse continue;
        if (require_false_on_mismatch and
            !guardReturnsExactlyFalse(tree, t + 11, end)) continue;
        if (receiverMutatedAfter(tree, body.first, end, before, recv_name)) continue;
        if (receiverAddressEscapedBefore(tree, body.first, end, recv_name)) continue;
        return true;
    }
    return false;
}

fn hasReturnBefore(tree: *const Ast, first: Ast.TokenIndex, before: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    var t = first;
    while (t < before) : (t += 1) {
        if (tags[t] == .keyword_return) return true;
    }
    return false;
}

fn guardFailureEnd(
    tree: *const Ast,
    close: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (close + 1 > last) return null;
    if (tags[close + 1] == .keyword_return) {
        return tokens.findStmtSemicolon(tags, close + 1, last) orelse close + 1;
    }
    if (tags[close + 1] != .l_brace) return null;
    const end = tokens.matchBrace(tags, close + 1, last) orelse return null;
    if (close + 2 >= end or tags[close + 2] != .keyword_return) return null;
    return end;
}

/// The innermost `{` enclosing a token, or null when the token is not
/// inside any block at all.  `known` is false when the brace stack
/// outgrew its fixed bound: past that point the block structure is
/// unknown, and a caller must REFUSE the guard instead of reading
/// "outside any block" and matching that unknown answer against another
/// unknown one.  Two unknowns are not evidence of a shared scope.
const Scope = struct {
    enclosing: ?Ast.TokenIndex,
    known: bool,
};

/// Brace stack over one token range, advanced forward as the caller
/// walks.  Answering the scope of every token the walk reaches costs one
/// traversal in total, where a per-token rescan re-read the whole prefix.
const ScopeStack = struct {
    /// `{` tokens opened and not yet closed; the last is the innermost.
    open: [128]Ast.TokenIndex = undefined,
    depth: usize = 0,
    overflowed: bool = false,
    next: Ast.TokenIndex,
    tags: []const std.zig.Token.Tag,

    fn init(tree: *const Ast, first: Ast.TokenIndex) ScopeStack {
        return .{
            .next = first,
            .tags = tree.tokens.items(.tag),
        };
    }

    /// Consume tokens up to (not including) `target`.  Targets must not
    /// move backwards; the callers below walk their range forward.
    fn advanceTo(self: *ScopeStack, target: Ast.TokenIndex) void {
        if (target <= self.next) return;
        while (self.next < target) : (self.next += 1) {
            switch (self.tags[self.next]) {
                .l_brace => {
                    if (self.depth == self.open.len) {
                        self.overflowed = true;
                    } else {
                        self.open[self.depth] = self.next;
                        self.depth += 1;
                    }
                },
                .r_brace => {
                    if (self.depth > 0) self.depth -= 1;
                },
                else => {},
            }
        }
    }

    fn current(self: *const ScopeStack) Scope {
        if (self.overflowed) return .{ .enclosing = null, .known = false };
        const enclosing: ?Ast.TokenIndex = if (self.depth == 0)
            null
        else
            self.open[self.depth - 1];
        return .{ .enclosing = enclosing, .known = true };
    }
};

/// True only when both answers are known and name the same `{`.  A guard
/// proves the cast only inside the block the guard itself guards, so an
/// unknown scope on either side fails the comparison closed.
fn sameScope(guard: Scope, cast: Scope) bool {
    return guard.known and cast.known and guard.enclosing == cast.enclosing;
}

fn receiverUsedAfter(
    tree: *const Ast,
    first: Ast.TokenIndex,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv_name: []const u8,
) bool {
    if (start >= end) return false;
    const tags = tree.tokens.items(.tag);
    var t = start + 1;
    while (t < end) : (t += 1) {
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), recv_name))
            continue;
        if (t > first and tags[t - 1] == .period) continue;
        return true;
    }
    return false;
}

fn receiverMutatedAfter(
    tree: *const Ast,
    first: Ast.TokenIndex,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv_name: []const u8,
) bool {
    if (receiverAddressEscapedBefore(tree, start, end, recv_name)) return true;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .assign and tag != .assign_destructure) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const begin = tree.firstToken(node);
        if (begin <= start or begin >= end) continue;
        const operator = tree.nodeMainToken(node);
        if (tree.tokenTag(begin) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(begin), recv_name))
            return true;
        if (receiverUsedAfter(tree, first, begin, operator, recv_name)) return true;
    }
    return false;
}

fn receiverAddressEscapedBefore(
    tree: *const Ast,
    first: Ast.TokenIndex,
    before: Ast.TokenIndex,
    recv_name: []const u8,
) bool {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .address_of) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const start = tree.firstToken(node);
        const end = tree.lastToken(node);
        if (start < first or end >= before) continue;
        if (receiverUsedAfter(tree, first, start, end + 1, recv_name)) return true;
    }
    return false;
}

fn hasHelperVtableGuard(
    tree: *const Ast,
    model: *const file_model.FileModel,
    cache: *file_cache_mod.FileCache,
    body: BodyRange,
    before: Ast.TokenIndex,
    recv_name: []const u8,
    target_name: []const u8,
) !bool {
    const tags = tree.tokens.items(.tag);
    // One pass reads the block structure up to the cast; a second, kept
    // beside the scan, answers the scope of each candidate guard without
    // re-reading the prefix once per token.
    var at_cast = ScopeStack.init(tree, body.first);
    at_cast.advanceTo(before);
    const cast_scope = at_cast.current();

    var at_guard = ScopeStack.init(tree, body.first);
    var t = body.first;
    while (t + 7 <= before and t + 7 <= body.last) : (t += 1) {
        at_guard.advanceTo(t);
        if (!beginsStatement(tree, t)) continue;
        if (tags[t] != .keyword_if or tags[t + 1] != .l_paren or
            tags[t + 2] != .bang or tags[t + 3] != .identifier or
            tags[t + 4] != .l_paren or tags[t + 5] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(t + 5), recv_name) or
            tags[t + 6] != .r_paren or tags[t + 7] != .r_paren)
            continue;
        const end = guardFailureEnd(tree, t + 7, body.last) orelse continue;
        if (!sameScope(at_guard.current(), cast_scope)) continue;
        if (receiverMutatedAfter(tree, body.first, end, before, recv_name)) continue;
        if (receiverAddressEscapedBefore(tree, body.first, end, recv_name)) continue;
        // The helper's prototype views this buffer; it must outlive the
        // guard check below, so it belongs to this frame.
        var helper_proto_buf: [1]Ast.Node.Index = undefined;
        const helper = (try boundHelperDecl(tree, model, cache, t + 3, &helper_proto_buf)) orelse continue;
        if (declarationEstablishesGuard(tree, model, cache, helper, target_name)) return true;
    }
    return false;
}

/// The declaration the bare call at `callee_tok` actually reaches.
///
/// A spelling is not a declaration.  The same name can be a member of
/// another container, a local or parameter that hides the file-scope
/// function, a name bound by a further-out frame, or a function of a
/// module this file never declares, and reading the guard off any of
/// those answers a question nobody asked.
///
/// A typed run asks the compiler's own resolver, and its answer is the
/// binding — including one it declines to give, which this rule treats
/// as no proof rather than re-deriving from the name.  Without a
/// resolver the fallback is deliberately NARROW: it matches the name
/// only against the file's own function declarations, and only when no
/// enclosing frame binds the name.  That is a lexical base, not the
/// compiler's own binding, and anything it cannot place — a member, a
/// name this file never declares, a duplicate — is refused.
/// The returned entry's `proto` views `proto_buf`, which the caller owns.
fn boundHelperDecl(
    tree: *const Ast,
    model: *const file_model.FileModel,
    cache: *file_cache_mod.FileCache,
    callee_tok: Ast.TokenIndex,
    proto_buf: *[1]Ast.Node.Index,
) !?tokens.FnDeclIter.Entry {
    if (cache.zls != null) return typedCalleeDecl(tree, cache, callee_tok, proto_buf);

    const name = tree.tokenSlice(callee_tok);
    // The scan reuses one scratch buffer per declaration, so only the
    // node of the match is kept; its prototype is rebuilt into the
    // caller's buffer once the scan has settled on it.
    var scan_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    var bound: ?Ast.Node.Index = null;
    while (fns.next(&scan_buf)) |entry| {
        if (!std.mem.eql(u8, tree.tokenSlice(entry.name_token), name)) continue;
        // A declaration inside another function's body is that
        // function's own local; no other frame reaches it by name.
        if (insideFnBody(tree, tree.firstToken(entry.node))) continue;
        if (!isFileScopeDecl(model, entry.node)) continue;
        // Two declarations of one name in file scope are a duplicate
        // the compiler rejects; nothing here may pick one.
        if (bound != null) return null;
        bound = entry.node;
    }
    const helper = bound orelse return null;
    if (try shadowedAt(cache, tree, callee_tok, name)) return null;
    return declEntryAt(tree, helper, proto_buf);
}

/// The declaration the compiler's own resolver names for the call
/// spelled at `callee_tok`, when this run has one and it answers.  It
/// is found by scanning the tree for the call node whose callee is
/// that token: the same call the resolver is then asked about, so the
/// proof keeps the resolver's own binding rather than a re-derived
/// one.
///
/// The resolver reads the call's `fn_expr`, and it separates the two
/// ways a reference fails: `unknown` is a reference this run cannot
/// place, while `not_callable` is one that names no function at all.
/// Neither is a callee, so neither is a proof, and there is no
/// name-based fallback here that could turn one into a declaration.  A
/// declaration living in another document is refused too — this rule
/// reads bodies from the tree it was handed.
fn typedCalleeDecl(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    callee_tok: Ast.TokenIndex,
    proto_buf: *[1]Ast.Node.Index,
) !?tokens.FnDeclIter.Entry {
    const resolver = cache.zls orelse return null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        var call_buf: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buf, node) orelse continue;
        if (tree.nodeMainToken(call.ast.fn_expr) != callee_tok) continue;
        const reference = switch (try resolver.functionReference(call.ast.fn_expr)) {
            .function => |ref| ref,
            .unknown, .not_callable => return null,
        };
        if (reference.tree != tree) return null;
        const fn_decl = tokens.enclosingFnDecl(reference.tree, reference.fn_token) orelse return null;
        return declEntryAt(reference.tree, fn_decl, proto_buf);
    }
    return null;
}

/// The entry's `proto` views `proto_buf`, which the caller owns.
fn declEntryAt(tree: *const Ast, fn_decl: Ast.Node.Index, proto_buf: *[1]Ast.Node.Index) ?tokens.FnDeclIter.Entry {
    const proto = tokens.fnProto(tree, proto_buf, fn_decl) orelse return null;
    const name_token = proto.name_token orelse return null;
    const body = tokens.bodyOf(tree, fn_decl) orelse return null;
    return .{ .node = fn_decl, .name_token = name_token, .body = body, .proto = proto };
}

/// True when this declaration belongs to the file itself rather than to
/// some other container.
///
/// This answers what the fallback can SEE, not which binding the
/// compiler picks for a bare name.  A run with a resolver has already
/// read the call's own binding before reaching this; a run without one
/// matches the name only against the file's own function declarations
/// and refuses everything else — a container member, a duplicate —
/// rather than guessing at one.
fn isFileScopeDecl(model: *const file_model.FileModel, fn_decl: Ast.Node.Index) bool {
    const owner = model.containingTypeOf(fn_decl) orelse return true;
    return owner.body_first == 0;
}

/// True when any function enclosing `use_token` binds `name`.
///
/// The innermost frame is where a reference normally lands, but a
/// declaration written further out still binds this name at the
/// reference's position, and consulting only the innermost would let it
/// pass for the file-scope declaration of the same spelling.
fn shadowedAt(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    use_token: Ast.TokenIndex,
    name: []const u8,
) !bool {
    var enclosing = tokens.enclosingFnDecl(tree, use_token);
    while (enclosing) |fn_decl| {
        var proto_buf: [1]Ast.Node.Index = undefined;
        // An unreadable prototype declines like an unreadable body: the
        // shadow question is unanswerable, so the name is refused rather
        // than read as the file-scope helper.
        const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return true;
        const body = tokens.bodyOf(tree, fn_decl) orelse return true;
        const bindings = try cache.localBindings(proto, body);
        if (bindings.findAt(name, use_token) != null) return true;
        enclosing = enclosingFnDeclExcept(tree, tree.firstToken(fn_decl), fn_decl);
    }
    return false;
}

/// The function whose declaration covers `tok`, other than `exclude` —
/// the next frame outward from a declaration written inside `exclude`.
fn enclosingFnDeclExcept(
    tree: *const Ast,
    tok: Ast.TokenIndex,
    exclude: Ast.Node.Index,
) ?Ast.Node.Index {
    var idx: u32 = 1;
    var best: ?Ast.Node.Index = null;
    var best_first: Ast.TokenIndex = 0;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (node == exclude or tree.nodeTag(node) != .fn_decl) continue;
        const first = tree.firstToken(node);
        if (tok < first or tok > tree.lastToken(node)) continue;
        if (best == null or first > best_first) {
            best = node;
            best_first = first;
        }
    }
    return best;
}

/// True when the `if` at `t` is a statement in its own right.
///
/// A guard that runs on one branch only — the `if` of an `else if`,
/// one under `defer`, one forming another's condition — proves nothing
/// about the statements written after it, and the failure it returns
/// never happens there.  A statement is introduced by the end of the
/// one before it (`;`), by the block holding it (`{`), or by the block
/// it closes (`}`); every other predecessor is a conditional position,
/// `keyword_else` and `keyword_defer` among them.
fn beginsStatement(tree: *const Ast, t: Ast.TokenIndex) bool {
    if (t == 0) return false;
    return switch (tree.tokens.items(.tag)[t - 1]) {
        .semicolon, .l_brace, .r_brace => true,
        else => false,
    };
}

/// True when the failure branch in `[first..end]` returns the literal
/// `false` and nothing else.
///
/// `if (!helper(alloc)) return …` proves the cast only when the
/// helper's own mismatch branch answers `false`, so `return true`,
/// `return false and x` and `return false orelse …` are all refusals:
/// the token after `return` must BE `false` and must be the whole
/// expression.  Only the branch itself is read — a `false` written
/// later in the body is not this return's value.
fn guardReturnsExactlyFalse(
    tree: *const Ast,
    first: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    var t = first;
    while (t <= end) : (t += 1) {
        if (tags[t] != .keyword_return) continue;
        if (t + 2 > end) return false;
        if (tags[t + 1] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(t + 1), "false")) return false;
        return tags[t + 2] == .semicolon or tags[t + 2] == .r_brace;
    }
    return false;
}

/// True when `tok` sits inside some function body, where a declaration
/// is that function's own local rather than a container member.
fn insideFnBody(tree: *const Ast, tok: Ast.TokenIndex) bool {
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |entry| {
        if (tok > tree.firstToken(entry.body) and tok < tree.lastToken(entry.body))
            return true;
    }
    return false;
}

/// The guard proof for one declaration: it must answer `bool`, take the
/// allocator as its first parameter, guard that parameter's vtable
/// before its own body can be read, and answer `false` when that guard
/// fails — the last is what lets a NEGATED call at the call site mean
/// "the vtable matched" rather than "the helper said so".
fn declarationEstablishesGuard(
    tree: *const Ast,
    model: *const file_model.FileModel,
    cache: *file_cache_mod.FileCache,
    entry: tokens.FnDeclIter.Entry,
    target_name: []const u8,
) bool {
    const return_type = entry.proto.ast.return_type.unwrap() orelse return false;
    const rt_first = tree.firstToken(return_type);
    const rt_last = tree.lastToken(return_type);
    if (rt_first != rt_last or
        tree.tokens.items(.tag)[rt_first] != .identifier or
        !std.mem.eql(u8, tree.tokenSlice(rt_first), "bool"))
        return false;
    var params = entry.proto.iterate(tree);
    const param = params.next() orelse return false;
    const param_name_tok = param.name_token orelse return false;
    const param_type = param.type_expr orelse return false;
    if (!allocatorTypeNode(tree, cache, param_type)) return false;
    const helper_body = BodyRange{
        .first = tree.firstToken(entry.body),
        .last = tree.lastToken(entry.body),
    };
    return hasDirectVtableGuard(
        tree,
        model,
        helper_body,
        helper_body.last,
        tree.tokenSlice(param_name_tok),
        target_name,
        true,
        true,
    );
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    start_tok: Ast.TokenIndex,
    end_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`@alignCast(expr.ptr)` — asserting alignment on a raw byte-slice pointer is unsafe; for network/file/serialised data the pointer offset is arbitrary and the runtime check panics when misaligned; use `std.mem.readInt` or copy into a local aligned struct with `@memcpy` instead",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, start_tok),
        .end = try Pos.fromTokenEnd(tree, end_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "aligncast-on-byte-slice: form A fires" {
    try testing.expectFires(check, R,
        \\fn parseHeader(bytes: []const u8) *Header {
        \\    return @alignCast(bytes.ptr);
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: form B fires" {
    try testing.expectFires(check, R,
        \\fn parseHeader(bytes: []const u8) *Header {
        \\    return @alignCast(@constCast(bytes.ptr));
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: alignCast on plain identifier does not fire" {
    try testing.expectNoFire(check,
        \\fn cast(p: *anyopaque) *Header {
        \\    return @alignCast(p);
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: alignCast on field (non-ptr) does not fire" {
    try testing.expectNoFire(check,
        \\fn cast(s: SomeStruct) *Header {
        \\    return @alignCast(s.data);
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: explicit align param suppressed" {
    try testing.expectNoFire(check,
        \\const Header = struct { value: u64 };
        \\pub fn place(mem: []align(@alignOf(Header)) u8) *Header {
        \\    const h: *Header = @ptrCast(@alignCast(mem.ptr));
        \\    return h;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: alignedAlloc receiver suppressed" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Header = struct { value: u64 };
        \\fn makeHeader(alloc: std.mem.Allocator) !*Header {
        \\    const buf = try alloc.alignedAlloc(u8, .of(Header), @sizeOf(Header));
        \\    const h: *Header = @ptrCast(@alignCast(buf.ptr));
        \\    return h;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: unaligned alloc still fires" {
    try testing.expectFires(check, R,
        \\fn makeHeader(alloc: Allocator) !*Header {
        \\    const buf = try alloc.alloc(u8, @sizeOf(Header));
        \\    return @alignCast(buf.ptr);
        \\}
        \\
    );
}

test "skript residual: allocator alias direct vtable guard suppresses context cast" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    );
}

test "skript residual: allocator alias helper vtable guard suppresses context cast" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    return true;
        \\}
        \\fn accountsCurrentContext(alloc: MemAllocator) bool {
        \\    if (!accountsValues(alloc)) return false;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    );
}

test "allocator context: unrelated initializer nodes do not spend the type query budget" {
    const src =
        "const ballast = [_]u8{" ++ "0," ** 8192 ++ "};\n" ++
        \\const std = @import("std");
        \\const Allocator = std.mem.Allocator;
        \\const Context = struct {
        \\    const vtable: Allocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recognizes(alloc: Allocator) bool {
        \\    if (alloc.vtable != &Context.vtable) return false;
        \\    const context: *const Context = @ptrCast(@alignCast(alloc.ptr));
        \\    return context.active;
        \\}
        \\fn recover(alloc: Allocator) ?*const Context {
        \\    if (!recognizes(alloc)) return null;
        \\    const context: *const Context = @ptrCast(@alignCast(alloc.ptr));
        \\    return context;
        \\}
        \\fn unchecked(alloc: Allocator) *const Context {
        \\    const context: *const Context = @ptrCast(@alignCast(alloc.ptr));
        \\    return context;
        \\}
        ;
    try testing.expectCount(check, R, 1, src);
}

test "skript residual: allocator alias context cast without vtable guard still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct { active: bool };
        \\fn accountsValues(alloc: MemAllocator) bool {
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    );
}

test "skript residual: mismatched allocator vtable guard still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\const OtherAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\};
        \\fn accountsValues(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &OtherAllocator.vtable) return false;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    );
}

test "allocator vtable guard with conditional exit still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(alloc: MemAllocator, reject: bool) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) {
        \\        if (reject) return false;
        \\    }
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    );
}

test "allocator vtable proof invalidated by receiver mutation" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(initial: MemAllocator, replacement: MemAllocator) bool {
        \\    var alloc = initial;
        \\    if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    alloc = replacement;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    );
}

test "allocator helper with conditional failure exit still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn isAccountAllocator(alloc: MemAllocator, reject: bool) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) {
        \\        if (reject) return false;
        \\    }
        \\    return true;
        \\}
        \\fn accountsValues(alloc: MemAllocator, reject: bool) bool {
        \\    if (!isAccountAllocator(alloc, reject)) return false;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    );
}

test "allocator guard on only one branch cannot prove a later cast" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(alloc: MemAllocator, check_guard: bool) bool {
        \\    if (check_guard) {
        \\        if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    }
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    );
}

test "allocator helper may inspect its guarded context" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\    if (!accountsValues(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: a later declaration does not overwrite the helper's parameter" {
    // Every one-parameter prototype in this file is read into a one-slot
    // buffer.  `count` is declared after the helper, so a scan that kept
    // the helper's prototype in a reused buffer would read `count: usize`
    // as the helper's parameter and lose the allocator guard.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    return true;
        \\}
        \\fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\    if (!accountsValues(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\fn count(items: usize) usize {
        \\    return items;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: a guard past the scope depth bound cannot prove a later cast" {
    // The guard below only runs inside `check_guard`'s branch, so it does not
    // dominate the cast.  Both tokens also sit past the fixed 128-entry brace
    // stack of the scope resolution, and a scope the stack cannot hold is
    // UNKNOWN rather than "outside any block" — two unknown scopes are not
    // evidence of a shared one, so the guard must not be read as proving this
    // cast.  The second function is the ordinary same-scope guard, which must
    // stay suppressed.
    const deep_open = "if (true) {" ** 130;
    const deep_close = "}" ** 130;
    const src: [:0]const u8 =
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(alloc: MemAllocator, check_guard: bool) bool {
    ++ deep_open ++
        \\    if (check_guard) {
        \\        if (alloc.vtable != &AccountAllocator.vtable) { return false; }
        \\    }
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
    ++ deep_close ++
        \\}
        \\fn accountsCurrent(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) { return false; }
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    ;
    try testing.expectCount(check, R, 1, src);
}

test "aligncast-on-byte-slice: a guarded helper does not speak for an unguarded same-named one" {
    // `Vtable.accountsValues` really does check the vtable; the file-scope
    // `accountsValues` that `recover` actually calls does not.  A proof read
    // off the first declaration of a name is not a proof about the second.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\const Vtable = struct {
        \\    fn accountsValues(alloc: MemAllocator) bool {
        \\        if (alloc.vtable != &AccountAllocator.vtable) { return false; }
        \\        return true;
        \\    }
        \\};
        \\fn accountsValues(alloc: MemAllocator) bool {
        \\    _ = alloc;
        \\    return true;
        \\}
        \\fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\    if (!accountsValues(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: the helper a bare call reaches keeps its guard when another type spells the same name" {
    // `recover` calls `recognizes` by a bare name, and the only
    // declaration of that spelling this run can match the call against
    // is the file-scope one — which really does check the vtable.
    // `Other.recognizes` shares the spelling, but it is a container
    // member rather than that declaration, so its unguarded body must
    // not cancel the proof the real callee earns.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\const Other = struct {
        \\    fn recognizes(alloc: MemAllocator) bool {
        \\        _ = alloc;
        \\        return true;
        \\    }
        \\};
        \\fn recognizes(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    return true;
        \\}
        \\fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\    if (!recognizes(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: the same pair with the guard on the member the call never reaches still fires" {
    // The pair above with the two bodies exchanged: the file-scope
    // `recognizes` is now the unguarded one, so the bare call is matched
    // against a body that never compares vtables and the cast is
    // reported.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\const Other = struct {
        \\    fn recognizes(alloc: MemAllocator) bool {
        \\        if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\        return true;
        \\    }
        \\};
        \\fn recognizes(alloc: MemAllocator) bool {
        \\    _ = alloc;
        \\    return true;
        \\}
        \\fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\    if (!recognizes(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: a local function value cannot borrow a declaration's proof" {
    // Zig forbids a local from shadowing a file-scope declaration, so no
    // real source can put the two under one spelling.  Here the call
    // names `probe`, a value `recover` bound to an unguarded member: the
    // guarded `recognizes` in this file is a different name, and a proof
    // is read off the declaration a call NAMES — which for a value there
    // is none of.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recognizes(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    return true;
        \\}
        \\const passes = struct {
        \\    fn recognizes(alloc: MemAllocator) bool {
        \\        _ = alloc;
        \\        return true;
        \\    }
        \\};
        \\fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\    const probe = passes.recognizes;
        \\    if (!probe(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: a caller-supplied helper cannot borrow a declaration's proof" {
    // The callee arrives as a `probe` parameter, under a name of its own
    // for the shadowing reason given above, and `dispatch` hands it an
    // unguarded member.  The caller picks the callee, so the guarded
    // `recognizes` written in this file is not what the call reaches.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recognizes(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    return true;
        \\}
        \\const passes = struct {
        \\    fn recognizes(alloc: MemAllocator) bool {
        \\        _ = alloc;
        \\        return true;
        \\    }
        \\};
        \\fn recover(alloc: MemAllocator, probe: *const fn (MemAllocator) bool) ?*const AccountAllocator {
        \\    if (!probe(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\fn dispatch(alloc: MemAllocator) ?*const AccountAllocator {
        \\    return recover(alloc, passes.recognizes);
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: a helper this file does not declare cannot prove the cast" {
    // The callee is another module's function, re-exported here as a
    // value.  This file binds the NAME, but no `fn` declaration with a
    // body is written in it, and this rule reads bodies out of the tree
    // it was handed — so the guard the module does write is not
    // evidence here, and the cast stands.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const checks = @import("account_checks.zig");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\const recognizes = checks.recognizes;
        \\fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\    if (!recognizes(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: an else-if vtable guard does not dominate the cast after the branch" {
    // When `reject` holds, the `if` branch falls straight through to the
    // cast with nothing compared — the `else if` guard never ran.  It is
    // written in the same block, with the same `{`, and its `return false`
    // is a real statement, so only the fact that it is a BRANCH position
    // separates this from a proof.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(alloc: MemAllocator, reject: bool) bool {
        \\    if (reject) {
        \\        std.debug.assert(true);
        \\    } else if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account.active;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: a deferred vtable guard runs after the cast, not before it" {
    // `defer` runs its block when the scope exits, which is after the
    // cast written below it has already been taken.  The `if` inside that
    // block is a statement in its own right, but it belongs to the
    // defer's own braces rather than to the block holding the cast, so it
    // cannot dominate it.  A `defer` needs that block: `defer if (c)
    // matched = false;` is not a statement form Zig accepts.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn accountsValues(alloc: MemAllocator) bool {
        \\    var matched = true;
        \\    defer { if (alloc.vtable != &AccountAllocator.vtable) matched = false; }
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    _ = account;
        \\    return matched;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: a helper that answers true on a vtable mismatch cannot prove the cast" {
    // The call site negates: `if (!isForeign(alloc))`.  A helper that
    // returns TRUE when the vtable differs makes that fall through
    // exactly when the allocator is foreign.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn isForeign(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return true;
        \\    return false;
        \\}
        \\fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\    if (!isForeign(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: a mismatch branch that only computes false is refused" {
    // `@as(bool, false)` IS false, but the proof is the token after
    // `return` being `false` itself.  Anything else is a shape this rule
    // reads as unknown, and unknown is charged.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recognizes(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return @as(bool, false);
        \\    return true;
        \\}
        \\fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\    if (!recognizes(alloc)) return null;
        \\    const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\    return account;
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: a file-scope helper guards a call written inside a method" {
    // `Runner.recover` calls `recognizes` by a bare name.  A run with a
    // resolver reads that call's own binding; a run without one matches
    // the name only against the file's own function declarations, and the
    // guarded one is the only candidate — so the proof holds from inside
    // the method exactly as it does from a plain function.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recognizes(alloc: MemAllocator) bool {
        \\    if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\    return true;
        \\}
        \\const Runner = struct {
        \\    fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\        if (!recognizes(alloc)) return null;
        \\        const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\        return account;
        \\    }
        \\};
        \\
    );
}

test "aligncast-on-byte-slice: a member's guard does not speak for a bare call made in the same struct" {
    // `Runner.recover` calls the file-scope `recognizes`, which never
    // compares vtables.  `Runner`'s own `probes` method does compare
    // them, but the bare call is not that method.  The member carries a
    // different name on purpose: a bare call sitting beside a same-named
    // member is ambiguous in Zig, so no real source can spell the member
    // directly there and the spelling this test would need does not
    // exist.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const AccountAllocator = struct {
        \\    const vtable: MemAllocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recognizes(alloc: MemAllocator) bool {
        \\    _ = alloc;
        \\    return true;
        \\}
        \\const Runner = struct {
        \\    fn probes(alloc: MemAllocator) bool {
        \\        if (alloc.vtable != &AccountAllocator.vtable) return false;
        \\        return true;
        \\    }
        \\    fn recover(alloc: MemAllocator) ?*const AccountAllocator {
        \\        if (!recognizes(alloc)) return null;
        \\        const account: *const AccountAllocator = @ptrCast(@alignCast(alloc.ptr));
        \\        return account;
        \\    }
        \\};
        \\
    );
}

test "aligncast-on-byte-slice: direct std import binds the guarded allocator type" {
    try testing.expectNoFire(check,
        \\const Context = struct {
        \\    const vtable: @import("std").mem.Allocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recover(memory: @import("std").mem.Allocator) bool {
        \\    if (memory.vtable != &Context.vtable) return false;
        \\    const context: *const Context = @ptrCast(@alignCast(memory.ptr));
        \\    return context.active;
        \\}
    );
}

test "aligncast-on-byte-slice: namespace and type aliases retain the guarded allocator declaration" {
    try testing.expectNoFire(check,
        \\const standard = @import("std");
        \\const memory_namespace = standard.mem;
        \\const Allocation = memory_namespace.Allocator;
        \\const Context = struct {
        \\    const vtable: Allocation.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recover(memory: Allocation) bool {
        \\    if (memory.vtable != &Context.vtable) return false;
        \\    const context: *const Context = @ptrCast(@alignCast(memory.ptr));
        \\    return context.active;
        \\}
    );
}

test "aligncast-on-byte-slice: a custom allocator namespace cannot establish a std context proof" {
    try testing.expectFires(check, R,
        \\const std = struct {
        \\    const mem = struct {
        \\        const Allocator = struct { ptr: *anyopaque, vtable: *const u8 };
        \\    };
        \\};
        \\const Context = struct { const vtable: u8 = 0; active: bool };
        \\fn recover(memory: std.mem.Allocator) bool {
        \\    if (memory.vtable != &Context.vtable) return false;
        \\    const context: *const Context = @ptrCast(@alignCast(memory.ptr));
        \\    return context.active;
        \\}
    );
}

test "aligncast-on-byte-slice: a std type parameter is not a standard-library import" {
    try testing.expectFires(check, R,
        \\const Context = struct { const vtable: u8 = 0; active: bool };
        \\fn recover(comptime std: type, memory: std.mem.Allocator) bool {
        \\    if (memory.vtable != &Context.vtable) return false;
        \\    const context: *const Context = @ptrCast(@alignCast(memory.ptr));
        \\    return context.active;
        \\}
    );
}

test "aligncast-on-byte-slice: a local standard allocator alias keeps its declaration context" {
    try testing.expectNoFire(check,
        \\const standard = @import("std");
        \\const Context = struct {
        \\    const vtable: standard.mem.Allocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recover(memory: standard.mem.Allocator) bool {
        \\    const Allocation = standard.mem.Allocator;
        \\    const copy: Allocation = memory;
        \\    if (copy.vtable != &Context.vtable) return false;
        \\    const context: *const Context = @ptrCast(@alignCast(copy.ptr));
        \\    return context.active;
        \\}
    );
}

test "aligncast-on-byte-slice: a local custom std namespace does not inherit a different import" {
    try testing.expectFires(check, R,
        \\const standard = @import("std");
        \\const Context = struct { const vtable: u8 = 0; active: bool };
        \\fn recover(pointer: *anyopaque) bool {
        \\    const std = struct {
        \\        const mem = struct {
        \\            const Allocator = struct { ptr: *anyopaque, vtable: *const u8 };
        \\        };
        \\    };
        \\    const memory: std.mem.Allocator = .{ .ptr = pointer, .vtable = &Context.vtable };
        \\    if (memory.vtable != &Context.vtable) return false;
        \\    const context: *const Context = @ptrCast(@alignCast(memory.ptr));
        \\    return context.active;
        \\}
        \\comptime { _ = standard; }
    );
}

test "aligncast-on-byte-slice: a container's allocator alias is read in its declaring scope" {
    try testing.expectNoFire(check,
        \\const Context = struct {
        \\    const vtable: @import("std").mem.Allocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\const Recovery = struct {
        \\    const Allocation = @import("std").mem.Allocator;
        \\    fn recover(memory: Allocation) bool {
        \\        if (memory.vtable != &Context.vtable) return false;
        \\        const context: *const Context = @ptrCast(@alignCast(memory.ptr));
        \\        return context.active;
        \\    }
        \\};
    );
}

test "aligncast-on-byte-slice: a type factory's comptime allocator alias retains its declaration" {
    try testing.expectNoFire(check,
        \\const Context = struct {
        \\    const vtable: @import("std").mem.Allocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn Recovery() type {
        \\    const memory_api = @import("std").mem;
        \\    return struct {
        \\        fn recover(memory: memory_api.Allocator) bool {
        \\            if (memory.vtable != &Context.vtable) return false;
        \\            const context: *const Context = @ptrCast(@alignCast(memory.ptr));
        \\            return context.active;
        \\        }
        \\    };
        \\}
    );
}

test "placement storage: rejecting a misaligned address proves the target alignment" {
    try testing.expectNoFire(check,
        \\const Link = struct { next: ?*Link };
        \\fn place(block: []u8) !*Link {
        \\    if (@intFromPtr(block.ptr) % @alignOf(Link) != 0) {
        \\        return error.Misaligned;
        \\    }
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
}

test "placement storage: standard assertion with a resolved maximum alignment proves the target" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Link = struct { next: ?*Link };
        \\const other_alignment = @max(@alignOf(u64), @alignOf(u32));
        \\const storage_alignment = @max(other_alignment, @alignOf(Link));
        \\fn place(block: []u8) *Link {
        \\    std.debug.assert(@intFromPtr(block.ptr) % storage_alignment == 0);
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
}

test "placement storage: branch-only alignment validation does not prove a later cast" {
    try testing.expectFires(check, R,
        \\const Link = struct { next: ?*Link };
        \\fn place(block: []u8, validate: bool) !*Link {
        \\    if (validate) {
        \\        if (@intFromPtr(block.ptr) % @alignOf(Link) != 0) return error.Misaligned;
        \\    }
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
}

test "placement storage: alignment validation cannot survive replacing the slice" {
    try testing.expectFires(check, R,
        \\const Link = struct { next: ?*Link };
        \\fn place(input: []u8, replacement: []u8) !*Link {
        \\    var block = input;
        \\    if (@intFromPtr(block.ptr) % @alignOf(Link) != 0) return error.Misaligned;
        \\    block = replacement;
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
}

test "placement storage: weaker alignment and lookalike allocators remain unknown" {
    try testing.expectFires(check, R,
        \\const Link = struct { next: ?*Link };
        \\fn place(alloc: FakeAllocator) !*Link {
        \\    const block = try alloc.unalignedAlloc(u8, @sizeOf(Link));
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
    try testing.expectFires(check, R,
        \\const Link = struct { next: ?*Link };
        \\fn place(block: []align(1) u8) *Link {
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
}

test "placement storage: a counterfeit assert and arbitrary modulus cannot prove alignment" {
    try testing.expectFires(check, R,
        \\const std = struct { const debug = struct { fn assert(_: bool) void {} }; };
        \\const Link = struct { next: ?*Link };
        \\fn place(block: []u8) *Link {
        \\    std.debug.assert(@intFromPtr(block.ptr) % @alignOf(Link) == 0);
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Link = struct { next: ?*Link };
        \\const storage_alignment = @max(3, @alignOf(Link));
        \\fn place(block: []u8) *Link {
        \\    std.debug.assert(@intFromPtr(block.ptr) % storage_alignment == 0);
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
}

/// Shared null proof for the forced-unwrap rule. Reject unknown scopes,
/// branch-only guards, reassignments, and address escapes.
pub fn nullRejectedBefore(tree: *const Ast, before: Ast.TokenIndex, name: []const u8) bool {
    const body = bodyContaining(tree, before) orelse return false;
    const tags = tree.tokens.items(.tag);
    var at_cast = ScopeStack.init(tree, body.first);
    at_cast.advanceTo(before);
    var at_guard = ScopeStack.init(tree, body.first);
    var t = body.first;
    while (t + 6 < before) : (t += 1) {
        at_guard.advanceTo(t);
        if (!beginsStatement(tree, t) or !sameScope(at_guard.current(), at_cast.current())) continue;
        if (tags[t] != .keyword_if or tags[t + 1] != .l_paren or
            tags[t + 2] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t + 2), name) or
            tags[t + 3] != .equal_equal or tags[t + 4] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t + 4), "null") or
            tags[t + 5] != .r_paren) continue;
        const end = guardFailureEnd(tree, t + 5, before) orelse continue;
        if (receiverMutatedAfter(tree, body.first, end, before, name) or
            receiverAddressEscapedBefore(tree, body.first, before, name)) continue;
        return true;
    }
    return false;
}

test "placement storage: method name and an unrelated aligned declaration cannot supply proof" {
    try testing.expectFires(check, R,
        \\const Link = struct { next: ?*Link };
        \\fn place(alloc: FakeAllocator) !*Link {
        \\    const block = try alloc.alignedAlloc(u8, .of(Link), @sizeOf(Link));
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
    try testing.expectFires(check, R,
        \\const Link = struct { next: ?*Link };
        \\fn place(input: []u8) *Link {
        \\    { const block: []align(@alignOf(Link)) u8 = undefined; _ = block; }
        \\    const block = input;
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
}

test "placement storage: type factory alignment constants prove the nested slab target" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn Pool(comptime T: type) type {
        \\    return struct {
        \\        const Link = struct { next: ?*Link };
        \\        const Slab = struct { next: ?*Slab, bytes: []u8 };
        \\        const object_alignment = @max(@alignOf(T), @alignOf(Link));
        \\        const allocation_alignment = @max(object_alignment, @alignOf(Slab));
        \\        fn place(bytes: []u8) *Slab {
        \\            std.debug.assert(@intFromPtr(bytes.ptr) % allocation_alignment == 0);
        \\            const slab: *Slab = @ptrCast(@alignCast(bytes.ptr));
        \\            return slab;
        \\        }
        \\    };
        \\}
    );
}

test "placement storage: validating a different target or allocating weaker alignment still fires" {
    try testing.expectFires(check, R,
        \\const Link = struct { next: ?*Link };
        \\fn place(block: []u8) !*Link {
        \\    if (@intFromPtr(block.ptr) % @alignOf(u8) != 0) return error.Misaligned;
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Link = struct { next: ?*Link };
        \\fn place(allocator: std.mem.Allocator) !*Link {
        \\    const block = try allocator.alignedAlloc(u8, .of(u8), @sizeOf(Link));
        \\    const node: *Link = @ptrCast(@alignCast(block.ptr));
        \\    return node;
        \\}
    );
}

test "page mapping: address assertion proves the explicit pointer alignment after type erasure" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Store = struct {
        \\    memory: []u8,
        \\    fn init(length: usize) !Store {
        \\        return .{ .memory = try std.posix.mmap(null, length, .{ .READ = true, .WRITE = true }, .{ .TYPE = .PRIVATE, .ANONYMOUS = true }, -1, 0) };
        \\    }
        \\    fn unmap(memory: []u8) void {
        \\        const pg = comptime std.heap.page_size_min;
        \\        std.debug.assert(@intFromPtr(memory.ptr) % pg == 0);
        \\        const ptr: [*]align(pg) u8 = @alignCast(memory.ptr);
        \\        std.posix.munmap(ptr[0..memory.len]);
        \\    }
        \\    fn deinit(self: *Store) void { unmap(self.memory); }
        \\};
    );
}

test "page mapping: an erased mapping field without an address proof remains conservative" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Store = struct {
        \\    memory: []u8,
        \\    fn init(length: usize) !Store {
        \\        return .{ .memory = try std.posix.mmap(null, length, .{ .READ = true, .WRITE = true }, .{ .TYPE = .PRIVATE, .ANONYMOUS = true }, -1, 0) };
        \\    }
        \\    fn unmap(memory: []u8) void {
        \\        const ptr: [*]align(std.heap.page_size_min) u8 = @alignCast(memory.ptr);
        \\        std.posix.munmap(ptr[0..memory.len]);
        \\    }
        \\    fn deinit(self: *Store) void { unmap(self.memory); }
        \\};
    );
}

test "explicit pointer alignment: a different modulus does not prove the target" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn recover(memory: []u8) void {
        \\    const pg = comptime std.heap.page_size_min;
        \\    const other_alignment = 1;
        \\    std.debug.assert(@intFromPtr(memory.ptr) % other_alignment == 0);
        \\    const ptr: [*]align(pg) u8 = @alignCast(memory.ptr);
        \\    _ = ptr;
        \\}
    );
}

test "explicit pointer alignment: validation cannot survive moving the base address" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn recover(input: []u8) void {
        \\    var memory = input;
        \\    const pg = comptime std.heap.page_size_min;
        \\    std.debug.assert(@intFromPtr(memory.ptr) % pg == 0);
        \\    memory = memory[1..];
        \\    const ptr: [*]align(pg) u8 = @alignCast(memory.ptr);
        \\    _ = ptr;
        \\}
    );
}

test "explicit pointer alignment: natural byte alignment is not enough" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn recover(memory: []align(@alignOf(u8)) u8) void {
        \\    std.debug.assert(@intFromPtr(memory.ptr) % @alignOf(u8) == 0);
        \\    const ptr: [*]align(std.heap.page_size_min) u8 = @alignCast(memory.ptr);
        \\    _ = ptr;
        \\}
    );
}

test "explicit pointer alignment: opaque alignment calls do not provide a proof" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const foreign = @import("alignment.zig");
        \\fn recover(memory: []u8) void {
        \\    const pg = comptime foreign.alignment();
        \\    std.debug.assert(@intFromPtr(memory.ptr) % pg == 0);
        \\    const ptr: [*]align(pg) u8 = @alignCast(memory.ptr);
        \\    _ = ptr;
        \\}
    );
}

test "allocator context: typed helper lookup uses the callee token, not the call parenthesis" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    const vtable: std.mem.Allocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recognizes(alloc: std.mem.Allocator) bool {
        \\    if (alloc.vtable != &Context.vtable) return false;
        \\    return true;
        \\}
        \\fn recover(alloc: std.mem.Allocator) ?*const Context {
        \\    if (!recognizes(alloc)) return null;
        \\    const context: *const Context = @ptrCast(@alignCast(alloc.ptr));
        \\    return context;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Context = struct {
        \\    const vtable: std.mem.Allocator.VTable = undefined;
        \\    active: bool,
        \\};
        \\fn recognizes(alloc: std.mem.Allocator) bool {
        \\    _ = alloc;
        \\    return true;
        \\}
        \\fn recover(alloc: std.mem.Allocator) ?*const Context {
        \\    if (!recognizes(alloc)) return null;
        \\    const context: *const Context = @ptrCast(@alignCast(alloc.ptr));
        \\    return context;
        \\}
    );
}

test "page mapping: a lookalike mmap method is not an alignment contract" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Fake = struct { fn mmap(bytes: []u8) []u8 { return bytes; } };
        \\fn recover(bytes: []u8) void {
        \\    const memory = Fake.mmap(bytes);
        \\    const ptr: [*]align(std.heap.page_size_min) u8 = @alignCast(memory.ptr);
        \\    _ = ptr;
        \\}
    );
}
