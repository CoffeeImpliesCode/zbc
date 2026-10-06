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
    const last_tok: Ast.TokenIndex = @intCast(tree.tokens.len -| 1);

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
            if (receiverIsAllocator(tree, cache, &ident_nodes, t, t + 2)) continue;
            // Suppress when the receiver was declared with an explicit alignment
            // annotation (`recv: []align(N) u8`) or via `alignedAlloc` — in those
            // cases the alignment is guaranteed by construction and the @alignCast
            // assertion is always safe.
            if (!receiverHasUnknownAlignment(tree, tags, t, tree.tokenSlice(t + 2)))
                continue;
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
            if (receiverIsAllocator(tree, cache, &ident_nodes, t, t + 4)) continue;
            if (!receiverHasUnknownAlignment(tree, tags, t, tree.tokenSlice(t + 4)))
                continue;
            try report(gpa, problems, tree, t, t + 8);
            continue;
        }
    }
}

/// Returns true (fire) when the receiver's alignment is UNKNOWN (the common
/// unsafe case), false (suppress) when the receiver is explicitly aligned:
///   - Parameter with `align(N)` type annotation: `recv: []align(N) u8`
///   - Local variable from `alignedAlloc(...)` or similar
/// Scans backward 300 tokens, finds the first non-field-access declaration
/// of `recv_name`, then checks the 20 tokens after it for `keyword_align`
/// or an identifier containing "alignedalloc" (case-insensitive).
fn receiverHasUnknownAlignment(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    anchor: Ast.TokenIndex,
    recv_name: []const u8,
) bool {
    const back: Ast.TokenIndex = 300;
    const start: Ast.TokenIndex = if (anchor >= back) anchor - back else 0;

    var k = start;
    while (k < anchor) : (k += 1) {
        if (tags[k] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k), recv_name)) continue;
        if (k > 0 and tags[k - 1] == .period) continue; // field access, skip

        // Check 20 tokens after the receiver name for alignment signals.
        const check_end = @min(k + 20, anchor);
        var j = k + 1;
        while (j < check_end) : (j += 1) {
            if (tags[j] == .keyword_align) return false; // explicit alignment
            if (tags[j] == .identifier) {
                const s = tree.tokenSlice(j);
                if (std.ascii.findIgnoreCase(s, "alignedalloc") != null or
                    std.ascii.findIgnoreCase(s, "alignalloc") != null)
                    return false; // alignedAlloc call in RHS
            }
        }
    }
    return true; // no alignment guarantee found → unknown alignment
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
) bool {
    _ = ident_nodes.get(recv_tok) orelse return false;
    if (!receiverTypeIsAllocator(tree, recv_tok)) return false;
    const target_name = castTargetTypeName(tree, align_tok) orelse return false;
    const model = cache.fileModel() catch return false;
    if (model.findType(target_name) == null) return false;
    const body = bodyContaining(tree, align_tok) orelse return false;
    const recv_name = tree.tokenSlice(recv_tok);
    if (hasDirectVtableGuard(tree, model, body, align_tok, recv_name, target_name, false))
        return true;
    return hasHelperVtableGuard(tree, model, body, align_tok, recv_name, target_name);
}

fn receiverTypeIsAllocator(tree: *const Ast, recv_tok: Ast.TokenIndex) bool {
    const body = bodyContaining(tree, recv_tok) orelse return false;
    const recv_name = tree.tokenSlice(recv_tok);
    if (localTypeNodeBefore(tree, recv_name, recv_tok, body.first)) |type_node|
        return allocatorTypeNode(tree, type_node, 0);

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
        return allocatorTypeNode(tree, type_node, 0);
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
        const type_node = decl.ast.type_node.unwrap() orelse continue;
        if (best == null or name_tok > best_tok) {
            best = type_node;
            best_tok = name_tok;
        }
    }
    return best;
}

fn allocatorTypeNode(tree: *const Ast, node: Ast.Node.Index, depth: u8) bool {
    return allocatorTypeRange(tree, tree.firstToken(node), tree.lastToken(node), depth);
}

fn allocatorTypeRange(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    depth: u8,
) bool {
    if (depth >= 8 or first > last) return false;
    const tags = tree.tokens.items(.tag);
    var names: [8][]const u8 = undefined;
    var count: usize = 0;
    var t = first;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .identifier => {
                if (count == names.len) return false;
                names[count] = tree.tokenSlice(t);
                count += 1;
            },
            .period, .keyword_const => {},
            else => return false,
        }
    }
    if (count == 3 and std.mem.eql(u8, names[1], "mem") and
        std.mem.eql(u8, names[2], "Allocator"))
    {
        return std.mem.eql(u8, names[0], "std") and
            isStdImportAlias(tree, names[0], first);
    }
    if (count != 1) return false;
    const init = findConstInitializer(tree, names[0], first) orelse return false;
    return allocatorTypeNode(tree, init, depth + 1);
}

fn isStdImportAlias(tree: *const Ast, name: []const u8, before: Ast.TokenIndex) bool {
    const init = findConstInitializer(tree, name, before) orelse return false;
    const source = std.mem.trim(u8, tree.getNodeSource(init), " \t\r\n");
    return std.mem.eql(u8, source, "@import(\"std\")");
}

fn findConstInitializer(
    tree: *const Ast,
    name: []const u8,
    before: Ast.TokenIndex,
) ?Ast.Node.Index {
    const tags = tree.tokens.items(.tag);
    var best: ?Ast.Node.Index = null;
    var best_tok: Ast.TokenIndex = 0;
    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        switch (tree.nodeTag(node)) {
            .global_var_decl, .local_var_decl, .simple_var_decl, .aligned_var_decl => {},
            else => continue,
        }
        const decl = tree.fullVarDecl(node) orelse continue;
        if (tags[decl.ast.mut_token] != .keyword_const) continue;
        const name_tok = decl.ast.mut_token + 1;
        if (name_tok >= tree.tokens.len or tags[name_tok] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_tok), name) or name_tok >= before) continue;
        const init = decl.ast.init_node.unwrap() orelse continue;
        if (best == null or name_tok > best_tok) {
            best = init;
            best_tok = name_tok;
        }
    }
    return best;
}

fn castTargetTypeName(tree: *const Ast, align_tok: Ast.TokenIndex) ?[]const u8 {
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
    var last_name: ?Ast.TokenIndex = null;
    k = colon_tok + 1;
    while (k < equal) : (k += 1) {
        if (tags[k] == .identifier) last_name = k;
    }
    return if (last_name) |name_tok| tree.tokenSlice(name_tok) else null;
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
) bool {
    const tags = tree.tokens.items(.tag);
    var t = body.first;
    while (t + 10 <= before and t + 10 <= body.last) : (t += 1) {
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
        if (scopeAtToken(tree, body.first, t) != scopeAtToken(tree, body.first, before)) continue;
        const end = guardFailureEnd(tree, t + 10, body.last) orelse continue;
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

fn scopeAtToken(
    tree: *const Ast,
    first: Ast.TokenIndex,
    token: Ast.TokenIndex,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    var stack: [128]Ast.TokenIndex = undefined;
    var depth: usize = 0;
    var t = first;
    while (t < token) : (t += 1) {
        switch (tags[t]) {
            .l_brace => {
                if (depth == stack.len) return null;
                stack[depth] = t;
                depth += 1;
            },
            .r_brace => {
                if (depth > 0) depth -= 1;
            },
            else => {},
        }
    }
    return if (depth == 0) null else stack[depth - 1];
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
    body: BodyRange,
    before: Ast.TokenIndex,
    recv_name: []const u8,
    target_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t = body.first;
    while (t + 7 <= before and t + 7 <= body.last) : (t += 1) {
        if (tags[t] != .keyword_if or tags[t + 1] != .l_paren or
            tags[t + 2] != .bang or tags[t + 3] != .identifier or
            tags[t + 4] != .l_paren or tags[t + 5] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(t + 5), recv_name) or
            tags[t + 6] != .r_paren or tags[t + 7] != .r_paren)
            continue;
        const end = guardFailureEnd(tree, t + 7, body.last) orelse continue;
        if (scopeAtToken(tree, body.first, t) != scopeAtToken(tree, body.first, before))
            continue;
        if (receiverMutatedAfter(tree, body.first, end, before, recv_name)) continue;
        if (receiverAddressEscapedBefore(tree, body.first, end, recv_name)) continue;
        if (helperEstablishesGuard(tree, model, tree.tokenSlice(t + 3), target_name))
            return true;
    }
    return false;
}

fn helperEstablishesGuard(
    tree: *const Ast,
    model: *const file_model.FileModel,
    helper_name: []const u8,
    target_name: []const u8,
) bool {
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |entry| {
        if (!std.mem.eql(u8, tree.tokenSlice(entry.name_token), helper_name)) continue;
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
        if (!allocatorTypeNode(tree, param_type, 0)) return false;
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
        );
    }
    return false;
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
        .start = Pos.fromTokenStart(tree, start_tok),
        .end = Pos.fromTokenEnd(tree, end_tok),
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
        \\pub fn free(mem: []align(std.heap.page_size_min) u8) void {
        \\    windows.VirtualFree(@ptrCast(@alignCast(mem.ptr)), 0, windows.MEM_RELEASE);
        \\}
        \\
    );
}

test "aligncast-on-byte-slice: alignedAlloc receiver suppressed" {
    try testing.expectNoFire(check,
        \\fn makeHeader(alloc: Allocator) !*Header {
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
