//! Detects `for (<recv>.items) |...| { ... call() ... }` where `call`
//! transitively invokes an ArrayList-grow method (append, resize, etc.),
//! potentially reallocating the backing buffer mid-iteration.  After the
//! reallocation, the for-loop's implicit slice pointer — captured at the
//! start of the first iteration — dangles into freed memory.
//!
//! Real-world shape: oven-sh/bun#29981 — iterating
//! `globalObject.m_pendingNapiModules` while `executePendingNapiModule`
//! can append to it; oven-sh/bun#29483 — `for (dependencies.items)`
//! while `enqueueDependency` can grow the slice.
//!
//! Complements `arraylist-items-slice` (which catches direct same-fn
//! grow calls) and `iterator-invalidation-mutation` (HashMap variant).
//!
//! Detection:
//!   1. For each `for ( <expr> ) |...|` loop, find a backing `.items`
//!      view at the iterable root, not a view used to compute an index.
//!   2. Resolve grow receivers and growth-bearing call arguments through
//!      their binding origins. Different pointer parameters and copied
//!      list headers can share a buffer. Proved private fresh storage is
//!      independent; unknown provenance remains possibly shared.
//!   3. Use the callee's canonical growth paths for indirect calls.
//!   4. Fire at the call token.
//!
//! A by-value capture (`|item|`) is detached from the list, so a grow that
//! is immediately followed by `return` (optionally `catch {}` and `;`)
//! performs no further iteration and is not reported.  A pointer capture
//! (`|*item|`) stays reported.
//!
//! A callee reached as `helpers.fn(...)` through one of this file's own
//! `@import` declarations is resolved with `FileCache.summaryByQualifiedName`.
//! A qualifier that is a parameter or a local is a value, not a module.
//!
//! Requires `FileCache.resolveTransitiveTakes()` to have run so that
//! `may_grow_collections` is transitively propagated through same-file
//! call chains.  `check()` calls it automatically.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const budget_mod = @import("../../budget.zig");
const grow_mod = @import("../../cache/grow_analysis.zig");
const method_names = @import("../../model/method_names.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const fn_summary = @import("../../model/fn_summary.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const matchBrace = tokens.matchBrace;
const matchParen = tokens.matchParen;
const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "slice-loop-reentrant-grow";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .slice_loop_reentrant_grow)) return;
    try cache.resolveTransitiveTakes();
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
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
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    // A view of the binding table, not a pointer into the cache's map: the
    // summary queries below can grow that map while this walk is reading it.
    const scope: Scope = .{
        .proto = proto,
        .bindings = (try cache.localBindings(proto, body)).*,
        .first = first,
        .last = last,
    };

    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_for) continue;
        if (tags[t + 1] != .l_paren) continue;

        const rp = matchParen(tags, t + 1, last) orelse continue;

        // Only an iterable's backing view is borrowed. An `.items` used
        // inside a call or subscript merely computes that iterable.
        const recv = findItemsRecv(tree, t + 2, rp - 1) orelse continue;

        // Find the loop body `{...}` after the capture `|...|`.
        const body_start = findLoopBody(tags, rp + 1, last) orelse continue;
        const body_end = matchBrace(tags, body_start, last) orelse continue;

        // Scan the loop body for calls that may grow collections.
        const capture_by_value = loopCaptureByValue(tags, rp + 1, body_start);
        try checkLoopBody(gpa, tree, cache, scope, body_start + 1, body_end - 1, recv, capture_by_value, problems);
    }
}

/// Find `<recv>.items` inside `[start, end]`.  Returns the receiver
/// (its last identifier plus the whole `a.b.c` chain), or null if not
/// found.
fn findItemsRecv(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) ?Recv {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var depth: usize = 0;
    var input_first = start;
    var s: Ast.TokenIndex = start;
    while (s <= end) : (s += 1) {
        switch (tags[s]) {
            .l_paren, .l_bracket, .l_brace => {
                depth += 1;
                continue;
            },
            .r_paren, .r_bracket, .r_brace => {
                if (depth > 0) depth -= 1;
                continue;
            },
            .comma => {
                if (depth == 0) input_first = s + 1;
                continue;
            },
            else => {},
        }
        if (depth != 0 or s + 2 > end or tags[s] != .identifier or
            tags[s + 1] != .period or tags[s + 2] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(s + 2), "items")) continue;
        const receiver = recvAt(tree, s);
        if (receiver.first != input_first) continue;
        return receiver;
    }
    return null;
}

/// The receiver of a method or field access: `name` is the identifier
/// at `last`, `first` is where its `a.b.c` chain starts.  `chained` is
/// true when something other than a plain identifier chain (a call
/// result, an index, a dereference) feeds that chain, so its object
/// cannot be named by tokens.
const Recv = struct {
    name: []const u8,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    chained: bool,
};

fn recvAt(tree: *const Ast, last: Ast.TokenIndex) Recv {
    const tags = tree.tokens.items(.tag);
    var first = last;
    while (first >= 2 and tags[first - 1] == .period and tags[first - 2] == .identifier) first -= 2;
    const chained = first >= 1 and switch (tags[first - 1]) {
        .period, .period_asterisk, .r_paren, .r_bracket => true,
        else => false,
    };
    return .{ .name = tree.tokenSlice(last), .first = first, .last = last, .chained = chained };
}

/// The fn body the walk is in, and what its locals are.
const Scope = struct {
    proto: Ast.full.FnProto,
    bindings: local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

/// Resolve aliases through the shared binding-origin walk. Different
/// parameter numbers are not disjointness: both pointers (or copied headers)
/// can name the same buffer. Only private fresh storage proves independence.
fn namesOtherObject(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    scope: Scope,
    iterated: Recv,
    grown: Recv,
    horizon: Ast.TokenIndex,
) !bool {
    if (iterated.chained or grown.chained) return false;
    const arena = if (cache.summary_arena) |*summary_arena| summary_arena.allocator() else return false;
    const a = try fn_summary.growBaseOfExpr(arena, tree, scope.proto, &scope.bindings, iterated.first, iterated.last);
    const b = try fn_summary.growBaseOfExpr(arena, tree, scope.proto, &scope.bindings, grown.first, grown.last);
    if (a == .unproven and b == .unproven and
        a.unproven.first == b.unproven.first and a.unproven.last == b.unproven.last) return false;
    if (a == .storage and b == .storage and a.storage == .param and b.storage == .param and
        a.storage.param.param == b.storage.param.param)
    {
        const ap = a.storage.param.path;
        const bp = b.storage.param.path;
        return !grow_mod.growFieldCovers(ap, bp) and !grow_mod.growFieldCovers(bp, ap) and
            !try headerWrittenBefore(cache, tree, scope, a.storage.param.param, ap, bp, horizon);
    }
    return try independentRoot(cache, tree, scope, a, tree.tokenSlice(grown.first), horizon) or
        try independentRoot(cache, tree, scope, b, tree.tokenSlice(iterated.first), horizon) or
        try callbackBackingSeparate(cache, tree, scope, iterated, grown, horizon);
}

/// Field layout does not prove independent backing after a header store.
/// Resolve each target through the same binding-origin walk as receivers.
fn headerWrittenBefore(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    scope: Scope,
    parameter: u32,
    a: []const u8,
    b: []const u8,
    horizon: Ast.TokenIndex,
) !bool {
    const tags = tree.tokens.items(.tag);
    const arena = if (cache.summary_arena) |*summary_arena| summary_arena.allocator() else return true;
    var t = scope.first;
    while (t < horizon) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, scope.last);
            continue;
        }
        if (tags[t] != .identifier or (t > scope.first and tags[t - 1] == .period)) continue;
        var last = t;
        while (last + 2 < horizon and tags[last + 1] == .period and tags[last + 2] == .identifier) last += 2;
        var next = last + 1;
        if (next < horizon and tags[next] == .period_asterisk) next += 1;
        if (next >= horizon or tags[next] != .equal) continue;
        const target = try fn_summary.growBaseOfExpr(arena, tree, scope.proto, &scope.bindings, t, last);
        if (target != .storage or target.storage != .param or target.storage.param.param != parameter) continue;
        const path = target.storage.param.path;
        if (grow_mod.growFieldCovers(path, a) or grow_mod.growFieldCovers(a, path) or
            grow_mod.growFieldCovers(path, b) or grow_mod.growFieldCovers(b, path)) return true;
    }
    return false;
}

fn independentRoot(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    scope: Scope,
    base: fn_summary.GrowBase,
    other: []const u8,
    horizon: Ast.TokenIndex,
) !bool {
    if (base != .unproven) return false;
    const claim = base.unproven;
    const binding = for (scope.bindings.items) |*candidate| {
        if (candidate.rhs_first == claim.first and candidate.rhs_last == claim.last and
            candidate.origin != .param) break candidate;
    } else return false;
    if (!try isPrivateLocal(cache, tree, scope, binding, other, horizon)) return false;
    return try cache.provesFreshStorage(claim, null);
}
/// The neutral callback census supplies every registration and transport,
/// never storage safety. Prove a private fresh input at every leaf dispatch.
/// A NULL context, a copied header, an escaped dispatcher, or any unclosed
/// transport refuses the certificate. Casts only locate the context formal.
fn callbackBackingSeparate(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    scope: Scope,
    iterated: Recv,
    grown: Recv,
    horizon: Ast.TokenIndex,
) !bool {
    const provenance = @import("../../model/callback_provenance.zig");
    if (cache.zls == null) return false;
    if (iterated.first != iterated.last or grown.first == grown.last) return false;
    const input_binding = scope.bindings.findAt(tree.tokenSlice(iterated.first), iterated.first) orelse return false;
    if (input_binding.origin != .param) return false;
    const input_parameter = file_cache_mod.paramIndexFor(tree, scope.proto, tree.tokenSlice(iterated.first)) orelse return false;
    const context_binding = scope.bindings.findAt(tree.tokenSlice(grown.first), grown.first) orelse return false;
    if (!context_binding.is_const or context_binding.origin == .param) return false;
    // This exact adapter shape preserves the context value; its alignment
    // says nothing about which collection allocation that value can reach.
    const tags = tree.tokens.items(.tag);
    const first = context_binding.rhs_first;
    const last = context_binding.rhs_last;
    if (last != first + 8 or tags[first] != .builtin or
        !std.mem.eql(u8, tree.tokenSlice(first), "@ptrCast") or tags[first + 1] != .l_paren or
        tags[first + 2] != .builtin or !std.mem.eql(u8, tree.tokenSlice(first + 2), "@alignCast") or
        tags[first + 3] != .l_paren or tags[first + 4] != .identifier or
        tags[first + 5] != .period or tags[first + 6] != .question_mark or
        tags[first + 7] != .r_paren or tags[first + 8] != .r_paren) return false;
    const context_parameter = file_cache_mod.paramIndexFor(tree, scope.proto, tree.tokenSlice(first + 4)) orelse return false;
    const context_formal = scope.bindings.findAt(tree.tokenSlice(first + 4), first + 4) orelse return false;
    if (context_formal.origin != .param) return false;
    // No assignment may replace a header through either incoming route.
    if (try headerWrittenBefore(cache, tree, scope, context_parameter, "", "", horizon) or
        try headerWrittenBefore(cache, tree, scope, input_parameter, "", "", horizon)) return false;
    const fresh = @import("../../cache/fresh_storage.zig");
    const frame = cache.zls.?.resolutionFrame();
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (raw == 0 or tree.firstToken(node) < scope.first or tree.lastToken(node) >= horizon) continue;
        switch (tag) {
            .assign => {
                const target = tree.nodeData(node).node_and_node[0];
                if (tree.nodeTag(target) == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(target)), "_")) continue;
                const ty = (try frame.typeOfNode(target)) orelse return false;
                if (!try fresh.actualTypeAddressFree(frame, ty, 0, null)) return false;
            },
            .assign_destructure => return false,
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (!std.mem.eql(u8, name, "@ptrCast") and !std.mem.eql(u8, name, "@alignCast")) return false;
            },
            .call, .call_comma, .call_one, .call_one_comma => {
                var call_buffer: [1]Ast.Node.Index = undefined;
                const call = tree.fullCall(&call_buffer, node) orelse return false;
                if (!try privatePopulation(cache, tree.nodeMainToken(call.ast.fn_expr))) return false;
            },
            else => {},
        }
    }
    // The actual leaf must be authenticated SDK growth, not a same-named
    // project operation that may publish or substitute the selected header.
    if (!try privatePopulation(cache, grown.last + 1)) return false;
    const declaration = tokens.enclosingFnDecl(tree, scope.proto.ast.fn_token) orelse return false;
    var census = try provenance.closedDispatchCensus(cache, declaration, context_parameter, cache.gpa);
    defer census.deinit(cache.gpa);
    if (census != .complete or census.complete.len == 0) return false;
    for (census.complete) |dispatch| {
        if (input_parameter >= dispatch.arguments.len or context_parameter >= dispatch.arguments.len) return false;
        const context = dispatch.context;
        const context_type = (try context.frame.typeOfNode(context.node)) orelse return false;
        if (context.frame.resolver.pointerSize(context_type) != .one) return false;
        if (!try privateDispatchInput(cache, dispatch, input_parameter)) return false;
    }
    return true;
}

fn privateDispatchInput(
    root: *file_cache_mod.FileCache,
    dispatch: @import("../../model/callback_provenance.zig").CallbackDispatch,
    input_parameter: usize,
) !bool {
    const fresh = @import("../../cache/fresh_storage.zig");
    const point = dispatch.arguments[input_parameter];
    const tree = &point.frame.handle.document.tree;
    // A direct address of the fresh local list is an allocation identity,
    // unlike a field read, a copied header, or a conditional pointer.
    if (tree.nodeTag(point.node) != .address_of) return false;
    const operand = tree.nodeData(point.node).node;
    if (tree.nodeTag(operand) != .identifier) return false;
    const document = try grow_mod.sourceDocument(root, point.frame.handle, point.frame.resolver.ctx);
    const cache = &document.cache;
    const declaration = tokens.enclosingFnDecl(tree, tree.firstToken(point.node)) orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
    const scope: Scope = .{
        .proto = proto,
        .bindings = (try cache.localBindings(proto, body)).*,
        .first = tree.firstToken(body),
        .last = tree.lastToken(body),
    };
    const token = tree.nodeMainToken(operand);
    const binding = scope.bindings.findAt(tree.tokenSlice(token), token) orelse return false;
    if (binding.origin == .param) return false;
    const horizon = tree.firstToken(dispatch.invocation.node);
    if (!try isPrivateLocal(cache, tree, scope, binding, "", horizon)) return false;
    if (!try fresh.freshStorageAt(cache, .{
        .claim = .{ .first = binding.rhs_first, .last = binding.rhs_last },
        .depth = 0,
        .frame = point.frame,
    })) return false;
    // No paired operand can hand the same local back as the context. This
    // also covers a nested expression evaluated within the invocation.
    for (dispatch.arguments, 0..) |argument, index| {
        if (index == input_parameter) continue;
        if (!argument.frame.handle.eql(point.frame.handle)) continue;
        var use = tree.firstToken(argument.node);
        while (use <= tree.lastToken(argument.node)) : (use += 1) {
            if (tree.tokenTag(use) == .identifier and aliasesBinding(tree, scope, use, binding)) return false;
        }
    }
    // Check all transport edges, not one selected caller. A source edge in
    // another frame cannot access a private local born inside this frame;
    // an edge in this frame must not already have transported that local.
    for (dispatch.edges) |edge| {
        if (!edge.caller.frame.handle.eql(point.frame.handle)) continue;
        if (tokens.enclosingFnDecl(tree, tree.firstToken(edge.caller.node)) != declaration) continue;
        for (edge.actuals) |actual| {
            if (!actual.actual.frame.handle.eql(point.frame.handle)) return false;
            var use = tree.firstToken(actual.actual.node);
            while (use <= tree.lastToken(actual.actual.node)) : (use += 1) {
                if (tree.tokenTag(use) == .identifier and aliasesBinding(tree, scope, use, binding)) return false;
            }
        }
    }
    return true;
}


/// A simple immutable alias may transport an address or a list header. It
/// does not create a new storage identity. Mutable aliases and assignments
/// are deliberately refused by the privacy scan.
fn aliasesBinding(
    tree: *const Ast,
    scope: Scope,
    use: Ast.TokenIndex,
    target: *const local_bindings.Binding,
) bool {
    const tags = tree.tokens.items(.tag);
    var current = use;
    var visited: usize = 0;
    // Every initializer refers to an earlier visible declaration. Walk
    // iteratively so a long chain cannot consume the native call stack.
    while (visited < scope.bindings.items.len) : (visited += 1) {
        const binding = scope.bindings.findAt(tree.tokenSlice(current), current) orelse return false;
        if (binding.name_token == target.name_token) return true;
        if (!binding.is_const) return false;
        switch (binding.origin) {
            .alias, .addr_of, .field_access => {},
            else => return false,
        }
        var first = binding.rhs_first;
        if (tags[first] == .ampersand) first += 1;
        if (first > binding.rhs_last or tags[first] != .identifier) return false;
        current = first;
    }
    return false;
}

/// Before this grow, no write, stored address, unknown handover, or header
/// copy may connect the fresh local (including its immutable aliases) to
/// the other root. Later returns do not retroactively alias an earlier loop.
fn isPrivateLocal(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    scope: Scope,
    binding: *const local_bindings.Binding,
    other: []const u8,
    horizon: Ast.TokenIndex,
) !bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = binding.name_token + 1;
    while (t < horizon) : (t += 1) {
        if (tags[t] != .identifier or tags[t - 1] == .period or
            !aliasesBinding(tree, scope, t, binding)) continue;
        const named = scope.bindings.findAt(tree.tokenSlice(t), t) orelse return false;
        if (named.name_token == t) continue;
        var alias_initializer = false;
        for (scope.bindings.items) |*candidate| {
            if (!candidate.is_const or candidate.name_token <= binding.name_token) continue;
            if (candidate.origin != .alias and candidate.origin != .addr_of and candidate.origin != .field_access) continue;
            if (candidate.rhs_first <= t and t <= candidate.rhs_last and
                aliasesBinding(tree, scope, candidate.name_token, binding))
            {
                alias_initializer = true;
                break;
            }
        }
        if (alias_initializer) continue;
        if (tags[t - 1] == .ampersand) {
            if (!try addressIsPlainCallArgument(cache, tree, tags, scope, t - 1, other)) return false;
            continue;
        }
        if (t + 1 > scope.last or tags[t + 1] != .period) return false;
        var end = t;
        while (end + 2 <= scope.last and tags[end + 1] == .period and tags[end + 2] == .identifier) end += 2;
        const next = if (end + 1 <= scope.last) tags[end + 1] else .semicolon;
        if (next == .l_paren) {
            if (end < horizon and !try privatePopulation(cache, end - 1)) return false;
            continue;
        }
        if (next == .equal) {
            var rhs = end + 2;
            const literal = rhs <= scope.last and tags[rhs] == .identifier and isPrimitiveValue(tree.tokenSlice(rhs));
            const path_start = !literal and rhs <= scope.last and tags[rhs] == .identifier;
            while (path_start and rhs + 2 <= scope.last and tags[rhs + 1] == .period and tags[rhs + 2] == .identifier) rhs += 2;
            if (path_start and rhs + 1 <= scope.last and tags[rhs + 1] == .semicolon) return false;
            continue;
        }
        const terminal = tree.tokenSlice(end);
        if (std.mem.eql(u8, terminal, "items") or std.mem.eql(u8, terminal, "len") or
            std.mem.eql(u8, terminal, "capacity")) continue;
        switch (tags[t - 1]) {
            .equal, .comma, .l_paren, .keyword_return, .colon => return false,
            else => {},
        }
    }
    return true;
}

/// True when the `&` at `amp` is an argument of a call — `f(.., &x, ..)` or
/// `a.f(.., &x.y, ..)` — that stands alone as a statement (`f(..);`,
/// `try f(..);`, or `if (condition) try f(..);`), so the call's result is
/// dropped and cannot carry the address on, and neither its condition,
/// callee expression nor any argument names `other`. Anything else — an
/// address stored, returned, nested in another call or expression — may
/// keep it.
fn addressIsPlainCallArgument(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    scope: Scope,
    amp: Ast.TokenIndex,
    other: []const u8,
) !bool {
    if (amp < 1) return false;
    if (tags[amp - 1] != .l_paren and tags[amp - 1] != .comma) return false;
    // The `(` that opens the enclosing call's argument list.
    var depth: usize = 0;
    var lp = amp - 1;
    while (true) : (lp -= 1) {
        switch (tags[lp]) {
            .r_paren, .r_bracket, .r_brace => depth += 1,
            .l_bracket, .l_brace => {
                if (depth == 0) return false;
                depth -= 1;
            },
            .l_paren => {
                if (depth == 0) break;
                depth -= 1;
            },
            else => {},
        }
        if (lp <= scope.first) return false;
    }
    if (lp < 1 or tags[lp - 1] != .identifier) return false;
    const rp = matchParen(tags, lp, scope.last) orelse return false;
    if (rp + 1 > scope.last or tags[rp + 1] != .semicolon) return false;
    // The callee expression: `<id>(.<id>)*` back to the statement start.
    var first = lp - 1;
    while (first >= scope.first + 2 and tags[first - 1] == .period and tags[first - 2] == .identifier) first -= 2;
    if (first > scope.first and tags[first - 1] == .keyword_try) first -= 1;
    // A call used as the body of a standalone `if` also drops its result.
    // Peel only complete `if (...)` prefixes, then require the same
    // statement boundary as an unconditional call. An initializer such as
    // `const kept = if (...) f(&x) else ...` cannot pass that boundary.
    while (first > scope.first and tags[first - 1] == .r_paren) {
        var condition_lp = first - 1;
        var condition_depth: usize = 1;
        while (condition_lp > scope.first) {
            condition_lp -= 1;
            switch (tags[condition_lp]) {
                .r_paren => condition_depth += 1,
                .l_paren => {
                    condition_depth -= 1;
                    if (condition_depth == 0) break;
                },
                else => {},
            }
        }
        if (condition_depth != 0 or condition_lp <= scope.first or
            tags[condition_lp - 1] != .keyword_if) return false;
        first = condition_lp - 1;
    }
    if (first <= scope.first) return false;
    switch (tags[first - 1]) {
        .semicolon, .l_brace, .r_brace => {},
        else => return false,
    }
    if (identAppearsIn(tree, tags, first, rp, other)) return false;
    const callee_token = if (lp >= 2 and tags[lp - 2] == .period) lp - 2 else lp - 1;
    return privatePopulation(cache, callee_token);
}

/// A handover can preserve privacy only with a readable canonical body.
/// Accept scalar stores and authenticated SDK list growth. Refuse header
/// stores, opaque calls, and computed builtin writes rather than assuming
/// that a helper cannot acquire the other list through another route.
fn privatePopulation(cache: *file_cache_mod.FileCache, callee_token: Ast.TokenIndex) !bool {
    const fresh = @import("../../cache/fresh_storage.zig");
    const actual = (try cache.actualCallSummaryAt(callee_token, null)) orelse return false;
    const resolver = if (actual.callee.caller_frame) |frame| frame.resolver else cache.zls orelse return false;
    const frame = resolver.frameForFunction(actual.callee.reference);
    const declaring = (try actual.declaringCache(cache)) orelse return false;
    const tree = actual.callee.tree;
    const std_tree = (try fresh.toolchainArrayListTree(declaring, frame)) orelse return false;
    if (tree == std_tree) {
        const name = tree.tokenSlice(actual.callee.fn_token + 1);
        return method_names.isArrayListGrowMethodName(name) or
            try grow_mod.isStandardListLifecycleCall(cache, callee_token);
    }
    const body = tokens.bodyOf(tree, actual.callee.declaration) orelse return false;
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (index == 0 or tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
        switch (tag) {
            .assign => {
                const target = tree.nodeData(node).node_and_node[0];
                if (tree.nodeTag(target) == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(target)), "_")) continue;
                const ty = (try frame.typeOfNode(target)) orelse return false;
                if (!try fresh.actualTypeAddressFree(frame, ty, 0, null)) return false;
            },
            .assign_destructure => return false,
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => return false,
            else => {},
        }
    }
    const index = try declaring.getCallIndex();
    var calls = index.by_callee_token.iterator();
    while (calls.next()) |call| {
        const node = call.value_ptr.*;
        if (tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
        const child = (try declaring.actualCallSummaryAt(call.key_ptr.*, frame)) orelse return false;
        if (child.callee.tree != std_tree) return false;
        const name = std_tree.tokenSlice(child.callee.fn_token + 1);
        if (!method_names.isArrayListGrowMethodName(name)) return false;
    }
    return true;
}

fn isPrimitiveValue(name: []const u8) bool {
    return std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false") or
        std.mem.eql(u8, name, "null") or std.mem.eql(u8, name, "undefined");
}

/// Find the `{` that opens the loop body.  Skips the capture `|...|`
/// (including optional second index capture) and optional `else`.
fn findLoopBody(
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?Ast.TokenIndex {
    var s: Ast.TokenIndex = start;
    while (s <= last) : (s += 1) {
        if (tags[s] == .l_brace) return s;
        if (tags[s] == .semicolon) return null;
    }
    return null;
}

/// Return true for a by-value first loop capture (`|item|`), not
/// pointer capture (`|*item|`). Only the former is detached before
/// a collection growth operation.
fn loopCaptureByValue(
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    body_start: Ast.TokenIndex,
) bool {
    var s = start;
    while (s < body_start and tags[s] != .pipe) : (s += 1) {}
    if (s >= body_start) return false;
    s += 1;
    return s < body_start and tags[s] == .identifier;
}

/// Scan `[start, end]` (the loop body interior) for calls that may
/// grow a collection.  `recv` is the list being iterated.
fn checkLoopBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    scope: Scope,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: Recv,
    capture_by_value: bool,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (start > end) return;
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    while (t + 1 <= end) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, end);
            continue;
        }

        // Direct grow: `recv.growMethod(` on the same receiver chain.
        if (tags[t] == .identifier and
            t + 3 <= end and
            tags[t + 1] == .period and
            tags[t + 2] == .identifier and
            tags[t + 3] == .l_paren)
        {
            const callee = tree.tokenSlice(t + 2);
            if (method_names.isArrayListGrowMethodName(callee) and
                !try namesOtherObject(cache, tree, scope, recv, recvAt(tree, t), t + 2))
            {
                if (!(capture_by_value and callImmediatelyReturns(tags, t + 3, end))) {
                    try report(gpa, problems, tree, t + 2, callee, recv.name);
                }
                t += 3;
                continue;
            }
        }

        // A call: either `fnName(` or `helpers.fnName(` — a free function
        // reached through one of this file's own `@import` declarations.
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_paren) continue;

        const callee = tree.tokenSlice(t);
        // A summary that exhausted its budget is not "no summary": it is an
        // unfinished answer, so the error must reach the caller.
        const Reading = struct { may_grow: bool, verdict: grow_mod.GrowVerdict };
        const reading: Reading = blk: {
            if (t > start and tags[t - 1] == .period) {
                if (t < start + 2 or tags[t - 2] != .identifier) continue;
                // `a.b.fn(` qualifies a field of something else, not a
                // module.
                if (t >= start + 3 and tags[t - 3] == .period) continue;
                const qualifier = tree.tokenSlice(t - 2);
                // Storage this fn holds reaches its methods through a
                // parameter or a local; those are not modules.
                if (file_cache_mod.paramIndexFor(tree, scope.proto, qualifier) != null) continue;
                if (scope.bindings.find(qualifier) != null) continue;
                const imported = (try cache.summaryByQualifiedName(qualifier, callee)) orelse continue;
                break :blk .{ .may_grow = imported.may_grow_collections, .verdict = grow_mod.summaryGrowVerdict(&imported) };
            }
            const local = (try cache.summaryByName(callee)) orelse continue;
            break :blk .{ .may_grow = local.may_grow_collections, .verdict = grow_mod.summaryGrowVerdict(local) };
        };
        if (!reading.may_grow) continue;

        // Resolve the storage of each growth-bearing argument below; an
        // absent receiver spelling does not prove absent aliases.
        const call_rp = matchParen(tags, t + 1, end) orelse {
            try reportCallee(gpa, problems, tree, t, callee, recv.name);
            continue;
        };

        // The callee's own verdict says WHICH storage it reallocates.  The
        // declaration the call really reaches (the type engine's answer, which
        // also reads an imported module) is preferred; a call it cannot
        // connect is read by name in this document, and failing that keeps
        // the summary's conservative default.
        const named = t == start or tags[t - 1] != .period;
        const verdict = (try grow_mod.calleeGrowVerdict(cache, if (named) t else t - 1)) orelse
            (if (named) try grow_mod.ownFnGrowVerdict(cache, callee) else null) orelse reading.verdict;
        if (!try verdictReachesIterated(cache, tree, tags, scope, t + 1, call_rp, recv, verdict)) {
            t = call_rp;
            continue;
        }

        if (!(capture_by_value and callImmediatelyReturns(tags, t + 1, end))) {
            try reportCallee(gpa, problems, tree, t, callee, recv.name);
        }
        t = call_rp;
    }
}

/// True when a call, with at most an empty catch block, immediately returns.
fn callImmediatelyReturns(
    tags: []const std.zig.Token.Tag,
    lp: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    if (lp > end or tags[lp] != .l_paren) return false;
    const rp = matchParen(tags, lp, end) orelse return false;
    var next = rp + 1;
    if (next + 2 <= end and
        tags[next] == .keyword_catch and
        tags[next + 1] == .l_brace and
        tags[next + 2] == .r_brace)
    {
        next += 3;
    }
    if (next <= end and tags[next] == .semicolon) next += 1;
    return next <= end and tags[next] == .keyword_return;
}

const TokenSpan = struct { first: Ast.TokenIndex, last: Ast.TokenIndex };

/// The tokens of argument `index` of the call whose parentheses are `lp` and
/// `rp`, or null when the call passes no such argument.
fn argumentSpan(
    tags: []const std.zig.Token.Tag,
    lp: Ast.TokenIndex,
    rp: Ast.TokenIndex,
    index: u32,
) ?TokenSpan {
    var arg_index: u32 = 0;
    var first = lp + 1;
    var depth: usize = 0;
    var s = lp + 1;
    while (s <= rp) : (s += 1) {
        switch (tags[s]) {
            .l_paren, .l_bracket, .l_brace => {
                depth += 1;
                continue;
            },
            .r_paren, .r_bracket, .r_brace => {
                if (depth > 0) {
                    depth -= 1;
                    continue;
                }
            },
            .comma => if (depth > 0) continue,
            else => continue,
        }
        // An argument ends at a top-level `,` or at the call's own `)`.
        if (arg_index == index) return if (s > first) .{ .first = first, .last = s - 1 } else null;
        arg_index += 1;
        first = s + 1;
    }
    return null;
}

const path_capacity = 512;

/// The dotted field text of the plain identifier chain `[first, last]`
/// (`a.b.c` -> `a.b.c`), written into `buffer`; null when it is not such a
/// chain or does not fit.
fn chainText(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    buffer: []u8,
) ?[]const u8 {
    var len: usize = 0;
    var s = first;
    while (s <= last) : (s += 2) {
        if (tags[s] != .identifier) return null;
        if (s != first) {
            if (tags[s - 1] != .period or len == buffer.len) return null;
            buffer[len] = '.';
            len += 1;
        }
        const name = tree.tokenSlice(s);
        if (len + name.len > buffer.len) return null;
        @memcpy(buffer[len..][0..name.len], name);
        len += name.len;
    }
    if (s != last + 2) return null;
    return buffer[0..len];
}


/// Every complete growth path must be separate from the iterated backing.
/// Constness restricts writes through one pointer, not aliases of its buffer.
fn verdictReachesIterated(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    scope: Scope,
    lp: Ast.TokenIndex,
    rp: Ast.TokenIndex,
    recv: Recv,
    verdict: grow_mod.GrowVerdict,
) !bool {
    if (verdict.unknown) return true;
    const root = tree.tokenSlice(recv.first);
    if (verdict.unplaced.len != 0) return true;
    if (verdict.paths.len == 0) return false;
    var iterated_buffer: [path_capacity]u8 = undefined;
    var arg_buffer: [path_capacity]u8 = undefined;
    var full_buffer: [2 * path_capacity + 1]u8 = undefined;
    for (verdict.paths) |gp| {
        const arg = argumentSpan(tags, lp, rp, gp.param) orelse return true;
        if (recv.chained) return true;
        const iterated: []const u8 = if (recv.first == recv.last)
            ""
        else
            chainText(tree, tags, recv.first + 2, recv.last, &iterated_buffer) orelse return true;
        // The argument must be exactly `[&]root(.field)*`.
        var s = arg.first;
        if (tags[s] == .ampersand) s += 1;
        if (s > arg.last or tags[s] != .identifier) return true;
        const grown = recvAt(tree, arg.last);
        // The complete growth paths, private caller storage and canonical
        // header-preserving leaf suffice; a generic write summary also
        // charges legitimate SDK growth as a header write.
        if (grown.first == s and try namesOtherObject(cache, tree, scope, recv, grown, lp - 1) and
            try privatePopulation(cache, lp - 1)) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(s), root)) return true;
        if (s != arg.last and (s + 2 > arg.last or tags[s + 1] != .period)) return true;
        const arg_path: []const u8 = if (s == arg.last)
            ""
        else
            chainText(tree, tags, s + 2, arg.last, &arg_buffer) orelse return true;
        const full: []const u8 = if (arg_path.len == 0)
            gp.field
        else if (gp.field.len == 0)
            arg_path
        else
            std.fmt.bufPrint(&full_buffer, "{s}.{s}", .{ arg_path, gp.field }) catch return true;
        if (grow_mod.growFieldCovers(iterated, full) or grow_mod.growFieldCovers(full, iterated)) return true;
        const arena = if (cache.summary_arena) |*summary_arena| summary_arena.allocator() else return true;
        const base = try fn_summary.growBaseOfExpr(arena, tree, scope.proto, &scope.bindings, recv.first, recv.first);
        if (base != .storage or base.storage != .param) return true;
        if (try headerWrittenBefore(cache, tree, scope, base.storage.param.param, iterated, full, lp - 1)) return true;
    }
    return false;
}


fn identAppearsIn(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) bool {
    if (start > end) return false;
    var s: Ast.TokenIndex = start;
    while (s <= end) : (s += 1) {
        if (tags[s] == .identifier and std.mem.eql(u8, tree.tokenSlice(s), name)) return true;
    }
    return false;
}

/// Append one finding for `call_tok`.  Takes ownership of `msg` on
/// success; frees it if the append fails.
fn appendProblem(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    call_tok: Ast.TokenIndex,
    msg: []u8,
) !void {
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, call_tok),
        .end = try Pos.fromTokenEnd(tree, call_tok),
        .message = msg,
    });
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    call_tok: Ast.TokenIndex,
    callee: []const u8,
    recv: []const u8,
) !void {
    try appendProblem(gpa, problems, tree, call_tok, try std.fmt.allocPrint(
        gpa,
        "`{s}.{s}` inside `for ({s}.items)` may reallocate the backing buffer — the loop's implicit slice pointer is invalidated; move the call outside the loop or capture needed data before growing",
        .{ recv, callee, recv },
    ));
}

fn reportCallee(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    call_tok: Ast.TokenIndex,
    callee: []const u8,
    recv: []const u8,
) !void {
    try appendProblem(gpa, problems, tree, call_tok, try std.fmt.allocPrint(
        gpa,
        "`{s}(...)` inside `for ({s}.items)` may grow a collection — if it reallocates the iterated slice, the loop's implicit pointer is invalidated; ensure `{s}` cannot grow `{s}` during iteration",
        .{ callee, recv, callee, recv },
    ));
}

// ── Tests ──────────────────────────────────────────────────

test "slice-loop-reentrant-grow: direct grow on iterated list fires" {
    try testing.expectFires(check, R,
        \\const List = std.ArrayList(u32);
        \\pub fn buggy(list: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        list.append(99) catch {};
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: bare callee with may_grow fires" {
    try testing.expectFires(check, R,
        \\const List = std.ArrayList(u32);
        \\fn grow(list: *List) void {
        \\    list.append(1) catch {};
        \\}
        \\pub fn buggy(list: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        grow(list);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: grow outside loop doesn't fire" {
    try testing.expectNoFire(check,
        \\const List = std.ArrayList(u32);
        \\pub fn safe(list: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\    }
        \\    list.append(99) catch {};
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: different pointer parameters can name the same list" {
    try testing.expectFires(check, R,
        \\const List = std.ArrayList(u32);
        \\pub fn safe(a: *List, b: *List) void {
        \\    for (a.items) |item| {
        \\        _ = item;
        \\        b.append(99) catch {};
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a callee handed another pointer parameter can grow the same list" {
    try testing.expectFires(check, R,
        \\const List = std.ArrayList(u32);
        \\fn growOther(other: *List) void {
        \\    other.append(1) catch {};
        \\}
        \\pub fn safe(list: *List, other: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        growOther(other);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: may_grow callee passed recv fires" {
    try testing.expectFires(check, R,
        \\const List = std.ArrayList(u32);
        \\fn mayGrow(list: *List, x: u32) void {
        \\    _ = x;
        \\    list.append(1) catch {};
        \\}
        \\pub fn buggy(list: *List) void {
        \\    for (list.items) |item| {
        \\        mayGrow(list, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: same field name on another object doesn't fire" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\pub fn forward(gpa: std.mem.Allocator, output: *Output) !void {
        \\    var origin: Output = .{};
        \\    for (origin.allocations.items) |requirement| {
        \\        try output.allocations.append(gpa, requirement);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a growing callee can reach a nested receiver through its owner" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Tally = struct { entries: std.ArrayList(u32) };
        \\fn grow(tally: *Tally, entry: u32) void {
        \\    tally.entries.append(std.heap.page_allocator, entry) catch {};
        \\}
        \\fn add(tally: *Tally) void {
        \\    for (tally.entries.items) |entry| {
        \\        grow(tally, entry);
        \\    }
        \\}
        \\
    );
}

test "skript regression: by-value reentrant grow returns before next iteration" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\pub fn take(list: *List) u32 {
        \\    for (list.items) |item| {
        \\        list.append(std.heap.page_allocator, item) catch {};
        \\        return item;
        \\    }
        \\    return 0;
        \\}
        \\
    );
}

test "skript regression: pointer reentrant grow remains unsafe after return" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\pub fn take(list: *List) u32 {
        \\    for (list.items) |*item| {
        \\        list.append(std.heap.page_allocator, item.*) catch {};
        \\        return item.*;
        \\    }
        \\    return 0;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: by-value capture with a growing callee that returns right after does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn grow(list: *List, value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn take(list: *List) u32 {
        \\    for (list.items) |item| {
        \\        grow(list, item);
        \\        return item;
        \\    }
        \\    return 0;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: pointer capture with a growing callee that returns right after still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn grow(list: *List, value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn take(list: *List) u32 {
        \\    for (list.items) |*item| {
        \\        grow(list, item.*);
        \\        return item.*;
        \\    }
        \\    return 0;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: same field path on the iterated object fires" {
    try testing.expectFires(check, R,
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\pub fn forward(gpa: std.mem.Allocator, output: *Output) !void {
        \\    for (output.allocations.items) |requirement| {
        \\        try output.allocations.append(gpa, requirement);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a local that shares the grown list's buffer still fires" {
    try testing.expectFires(check, R,
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\pub fn forward(gpa: std.mem.Allocator, output: *Output) !void {
        \\    var origin: Output = .{};
        \\    origin.allocations = output.allocations;
        \\    for (origin.allocations.items) |requirement| {
        \\        try output.allocations.append(gpa, requirement);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a local whose address escapes still fires" {
    try testing.expectFires(check, R,
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty, view: ?*Output = null };
        \\pub fn forward(gpa: std.mem.Allocator, output: *Output) !void {
        \\    var origin: Output = .{};
        \\    output.view = &origin;
        \\    for (origin.allocations.items) |requirement| {
        \\        try output.allocations.append(gpa, requirement);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a pointer alias of the iterated list still fires" {
    try testing.expectFires(check, R,
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\pub fn forward(gpa: std.mem.Allocator, self: *Output) !void {
        \\    const output = self;
        \\    for (output.allocations.items) |requirement| {
        \\        try self.allocations.append(gpa, requirement);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a local only a callee fills through its address does not fire" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\const Query = struct {
        \\    scratch: std.mem.Allocator,
        \\    fn origin(self: *Query, out: *Output) !void {
        \\        try out.allocations.append(self.scratch, 1);
        \\    }
        \\    pub fn copy(self: *Query, output: *Output) !void {
        \\        var parent: Output = .{};
        \\        try self.origin(&parent);
        \\        for (parent.allocations.items) |requirement| {
        \\            try output.allocations.append(self.scratch, requirement);
        \\        }
        \\    }
        \\};
        \\
    );
}

test "slice-loop-reentrant-grow: conditional private local population does not fire" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty, complete: bool = true };
        \\const Query = struct {
        \\    scratch: std.mem.Allocator,
        \\    fn expression(self: *Query, out: *Output) !void {
        \\        try out.allocations.append(self.scratch, 1);
        \\    }
        \\    pub fn copy(self: *Query, output: *Output) !void {
        \\        var parent: Output = .{};
        \\        try self.expression(&parent);
        \\        if (parent.allocations.items.len == 0 and parent.complete)
        \\            try self.expression(&parent);
        \\        for (parent.allocations.items) |requirement| {
        \\            try output.allocations.append(self.scratch, requirement);
        \\        }
        \\    }
        \\};
        \\
    );
}

test "slice-loop-reentrant-grow: conditional callee copying the grown list still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\const Query = struct {
        \\    scratch: std.mem.Allocator,
        \\    fn expression(self: *Query, local: *Output, other: *Output) void {
        \\        _ = self;
        \\        local.allocations = other.allocations;
        \\    }
        \\    pub fn copy(self: *Query, output: *Output) !void {
        \\        var parent: Output = .{};
        \\        if (parent.allocations.items.len == 0)
        \\            self.expression(&parent, output);
        \\        for (parent.allocations.items) |requirement| {
        \\            try output.allocations.append(self.scratch, requirement);
        \\        }
        \\    }
        \\};
        \\
    );
}

test "slice-loop-reentrant-grow: conditional list header assignment still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\pub fn copy(gpa: std.mem.Allocator, output: *Output) !void {
        \\    var parent: Output = .{};
        \\    if (parent.allocations.items.len == 0)
        \\        parent.allocations = output.allocations;
        \\    for (parent.allocations.items) |requirement| {
        \\        try output.allocations.append(gpa, requirement);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: conditional address-returning initializer still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\fn keep(local: *Output) *Output {
        \\    return local;
        \\}
        \\pub fn copy(gpa: std.mem.Allocator, output: *Output, condition: bool) !void {
        \\    var parent: Output = .{};
        \\    const alias = if (condition) keep(&parent) else output;
        \\    for (parent.allocations.items) |requirement| {
        \\        try alias.allocations.append(gpa, requirement);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a local handed to a callee together with the grown list still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\const Query = struct {
        \\    scratch: std.mem.Allocator,
        \\    fn share(self: *Query, local: *Output, other: *Output) void {
        \\        _ = self;
        \\        local.allocations = other.allocations;
        \\    }
        \\    pub fn copy(self: *Query, output: *Output) !void {
        \\        var parent: Output = .{};
        \\        self.share(&parent, output);
        \\        for (parent.allocations.items) |requirement| {
        \\            try output.allocations.append(self.scratch, requirement);
        \\        }
        \\    }
        \\};
        \\
    );
}

test "slice-loop-reentrant-grow: a local whose address a call keeps still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty, view: ?*Output = null };
        \\pub fn forward(gpa: std.mem.Allocator, output: *Output) !void {
        \\    var origin: Output = .{};
        \\    const kept = keep(&origin, output);
        \\    _ = kept;
        \\    for (origin.allocations.items) |requirement| {
        \\        try output.allocations.append(gpa, requirement);
        \\    }
        \\}
        \\fn keep(origin: *Output, output: *Output) *Output {
        \\    output.view = origin;
        \\    return origin;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a callee that grows a sibling field of the iterated owner does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const KeySet = struct { keys: std.ArrayListUnmanaged([]const u8) = .empty };
        \\const Oracle = struct {
        \\    gpa: std.mem.Allocator,
        \\    pointer_roots: KeySet = .{},
        \\    minted_paths: std.ArrayListUnmanaged([]const u8) = .empty,
        \\};
        \\fn mint(o: *Oracle, text: []const u8) !void {
        \\    try o.minted_paths.append(o.gpa, text);
        \\}
        \\pub fn dropAll(o: *Oracle) !void {
        \\    for (o.pointer_roots.keys.items) |other| {
        \\        try mint(o, other);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a callee that grows the iterated field of the same owner still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Oracle = struct {
        \\    gpa: std.mem.Allocator,
        \\    minted_paths: std.ArrayListUnmanaged([]const u8) = .empty,
        \\};
        \\fn mint(o: *Oracle, text: []const u8) !void {
        \\    try o.minted_paths.append(o.gpa, text);
        \\}
        \\pub fn dropAll(o: *Oracle) !void {
        \\    for (o.minted_paths.items) |other| {
        \\        try mint(o, other);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a callee that grows an owner of the iterated field still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const KeySet = struct { keys: std.ArrayListUnmanaged([]const u8) = .empty };
        \\const Oracle = struct { gpa: std.mem.Allocator, pointer_roots: KeySet = .{} };
        \\fn mint(o: *Oracle, text: []const u8) !void {
        \\    try o.pointer_roots.keys.append(o.gpa, text);
        \\}
        \\pub fn dropAll(o: *Oracle) !void {
        \\    for (o.pointer_roots.keys.items) |other| {
        \\        try mint(o, other);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a callee that grows only a local list of its own does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Bag = struct {
        \\    n: u32 = 0,
        \\    fn append(self: *Bag, value: u32) void {
        \\        self.n += value;
        \\    }
        \\};
        \\const Index = struct { nodes: std.ArrayListUnmanaged(u32) = .empty };
        \\fn tally(index: *Index) u32 {
        \\    var out: Bag = .{};
        \\    out.append(1);
        \\    return out.n + @as(u32, @intCast(index.nodes.items.len));
        \\}
        \\pub fn scan(index: *Index) u32 {
        \\    var total: u32 = 0;
        \\    for (index.nodes.items) |node| {
        \\        total += tally(index) + node;
        \\    }
        \\    return total;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: consumer supplies fresh output beside a const tree" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Ast = std.zig.Ast;
        \\const Problem = struct { line: u32 };
        \\fn report(gpa: std.mem.Allocator, problems: *std.ArrayListUnmanaged(Problem), node: u32) !void {
        \\    try problems.append(gpa, .{ .line = node });
        \\}
        \\pub fn collect(gpa: std.mem.Allocator, tree: *const Ast) !void {
        \\    var problems: std.ArrayListUnmanaged(Problem) = .empty;
        \\    defer problems.deinit(gpa);
        \\    for (tree.nodes.items(.tag), 0..) |tag, index| {
        \\        _ = tag;
        \\        try report(gpa, &problems, @intCast(index));
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: consumer supplies actually shared backing beside a const tree" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Problem = u32;
        \\const Tree = struct { nodes: std.ArrayListUnmanaged(Problem) = .empty };
        \\fn report(gpa: std.mem.Allocator, problems: *std.ArrayListUnmanaged(Problem), node: u32) !void {
        \\    try problems.append(gpa, node);
        \\}
        \\pub fn collect(gpa: std.mem.Allocator, tree: *const Tree) !void {
        \\    var problems = tree.nodes;
        \\    for (tree.nodes.items) |node| {
        \\        try report(gpa, &problems, node);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: a callee summary that exhausts its budget fails the rule" {
    const gpa = std.testing.allocator;
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    try source.appendSlice(gpa, "const List = std.ArrayList(u32);\nfn grow(list: *List) void {\n");
    for (0..80) |_| try source.appendSlice(gpa, "{");
    try source.appendSlice(gpa, "list.append(1) catch {};");
    for (0..80) |_| try source.appendSlice(gpa, "}");
    try source.appendSlice(gpa,
        \\
        \\}
        \\pub fn buggy(list: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        grow(list);
        \\    }
        \\}
        \\
    );
    const text = try gpa.dupeZ(u8, source.items);
    defer gpa.free(text);
    var tree = try Ast.parse(gpa, text, .zig);
    defer tree.deinit(gpa);
    var cache = file_cache_mod.FileCache.init(gpa, &tree);
    defer cache.deinit();
    budget_mod.clear();
    defer budget_mod.clear();
    // The summary pass finishes with `grow` recorded as failed. `buggy`
    // reads that summary while its own is built, so it fails with it; a
    // reader of a failed root is never published as complete. The rule
    // then asks for the summary again and must see the failure, not an
    // absent callee.
    var failures: std.ArrayListUnmanaged(file_cache_mod.SummaryFailure) = .empty;
    defer failures.deinit(gpa);
    try cache.resolveTransitiveTakesCollecting(&failures);
    var grow_failed = false;
    for (failures.items) |failure| {
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(&tree, &buffer, failure.fn_decl) orelse continue;
        const name_token = proto.name_token orelse continue;
        if (std.mem.eql(u8, tree.tokenSlice(name_token), "grow")) grow_failed = true;
    }
    try std.testing.expect(grow_failed);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer testing.freeProblems(gpa, &problems);
    try std.testing.expectError(
        error.AnalysisBudgetExceeded,
        check(gpa, &tree, &cache, &config_mod.Default, &problems),
    );
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "slice-loop-reentrant-grow: collection identity fresh output aliases stay separate" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Owner = struct { list: List = .empty };
        \\fn copy(gpa: std.mem.Allocator, input: *Owner) !void {
        \\    var output: Owner = .{};
        \\    const destination = &output;
        \\    for (input.list.items) |value| {
        \\        try destination.list.append(gpa, value);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity fresh constructor output stays separate" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Owner = struct {
        \\    list: List = .empty,
        \\    fn begin() Owner { return .{}; }
        \\};
        \\fn copy(gpa: std.mem.Allocator, input: *Owner) !void {
        \\    var output = Owner.begin();
        \\    for (input.list.items) |value| {
        \\        try output.list.append(gpa, value);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity empty list does not alias owner field" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Owner = struct { list: List = .empty };
        \\fn copy(gpa: std.mem.Allocator, input: *Owner) !void {
        \\    var list = List.empty;
        \\    for (input.list.items) |value| {
        \\        try list.append(gpa, value);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity index queue is not the iterated backing" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn walk(gpa: std.mem.Allocator, successors: []const []const u32, queue: *std.ArrayList(u32)) !void {
        \\    var head: usize = 0;
        \\    while (head < queue.items.len) : (head += 1) {
        \\        for (successors[queue.items[head]]) |target| {
        \\            try queue.append(gpa, target);
        \\        }
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity completed nested borrow does not cover outer append" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn pins(gpa: std.mem.Allocator, rows: *std.ArrayList(u32), names: []const u32) !void {
        \\    for (names) |name| {
        \\        for (rows.items) |row| { _ = row; }
        \\        try rows.append(gpa, name);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity helper grows fresh output through alias" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn add(gpa: std.mem.Allocator, output: *List, input: *List, value: u32) !void {
        \\    _ = input.items.len;
        \\    try output.append(gpa, value);
        \\}
        \\fn copy(gpa: std.mem.Allocator, input: *List) !void {
        \\    var output: List = .empty;
        \\    const destination = &output;
        \\    for (input.items) |value| {
        \\        try add(gpa, destination, input, value);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity helper owned allocation does not grow input" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn build(gpa: std.mem.Allocator, input: *List) !List {
        \\    var output: List = .empty;
        \\    try output.appendSlice(gpa, input.items);
        \\    return output;
        \\}
        \\fn scan(gpa: std.mem.Allocator, input: *List) !void {
        \\    for (input.items) |_| {
        \\        var output = try build(gpa, input);
        \\        output.deinit(gpa);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity copied list header appendSlice remains unsafe" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn grow(gpa: std.mem.Allocator, input: *std.ArrayList(u32)) !void {
        \\    var output = input.*;
        \\    for (input.items) |value| {
        \\        try output.appendSlice(gpa, &.{value});
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity pointer rebind remains unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn grow(gpa: std.mem.Allocator, input: *std.ArrayList(u32)) !void {
        \\    var output: std.ArrayList(u32) = .empty;
        \\    var destination = &output;
        \\    destination = input;
        \\    for (input.items) |value| {
        \\        try destination.appendSlice(gpa, &.{value});
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity two owner pointer parameters remain unsafe" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Owner = struct { list: std.ArrayList(u32) = .empty };
        \\fn grow(gpa: std.mem.Allocator, input: *const Owner, output: *Owner) !void {
        \\    for (input.list.items) |value| {
        \\        try output.list.appendSlice(gpa, &.{value});
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity unknown growth remains unsafe" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\var shared: List = .empty;
        \\fn unknown(input: *List) void {
        \\    _ = input;
        \\    shared.append(std.heap.page_allocator, 1) catch {};
        \\}
        \\fn scan(input: *List) void {
        \\    for (input.items) |_| { unknown(input); }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity actual nested iterated borrow remains unsafe" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn walk(gpa: std.mem.Allocator, names: []const u32, queue: *std.ArrayList(u32)) !void {
        \\    for (names) |_| {
        \\        for (queue.items) |target| {
        \\            try queue.appendSlice(gpa, &.{target});
        \\        }
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity shared sibling header remains unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    source: std.ArrayList(u32) = .empty,
        \\    output: std.ArrayList(u32) = .empty,
        \\};
        \\fn grow(gpa: std.mem.Allocator, owner: *Owner) !void {
        \\    owner.output = owner.source;
        \\    for (owner.source.items) |value| {
        \\        try owner.output.appendSlice(gpa, &.{value});
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: collection identity helper replacing fresh header remains unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn replaceAndGrow(gpa: std.mem.Allocator, output: *List, input: *List, value: u32) !void {
        \\    output.* = input.*;
        \\    try output.appendSlice(gpa, &.{value});
        \\}
        \\fn scan(gpa: std.mem.Allocator, input: *List) !void {
        \\    var output: List = .empty;
        \\    for (input.items) |value| {
        \\        try replaceAndGrow(gpa, &output, input, value);
        \\    }
        \\}
    );
}

const callback_backing_source =
    \\const std = @import("std");
    \\const List = std.ArrayList(u32);
    \\const Error = error{OutOfMemory};
    \\const ReferenceSink = struct {
    \\    context: ?*anyopaque,
    \\    references: *const fn (?*anyopaque, *List) Error!void,
    \\};
    \\const Captured = struct {
    \\    list: List = .empty,
    \\    allocator: std.mem.Allocator,
    \\    sink: ReferenceSink = undefined,
    \\    fn bind(self: *Captured) *const ReferenceSink {
    \\        self.sink = .{ .context = self, .references = capture };
    \\        return &self.sink;
    \\    }
    \\    fn capture(context: ?*anyopaque, list: *List) Error!void {
    \\        const self: *Captured = @ptrCast(@alignCast(context.?));
    \\        for (list.items) |reference| {
    \\            try self.list.append(self.allocator, reference);
    \\        }
    \\    }
    \\};
    \\const ViewVerifier = struct {
    \\    allocator: std.mem.Allocator,
    \\    references: ?*const ReferenceSink = null,
    \\    fn verify(self: *ViewVerifier) Error!void {
    \\        var collected: List = .empty;
    \\        defer collected.deinit(self.allocator);
    \\        try collected.append(self.allocator, 1);
    \\        if (self.references) |sink| try sink.references(sink.context, &collected);
    \\    }
    \\};
    \\
;

test "slice-loop-reentrant-grow: callback backing census distinct collected output stays quiet" {
    try testing.expectNoFireTyped(check, callback_backing_source ++
        \\fn selected(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    defer captured.list.deinit(allocator);
        \\    var verifier: ViewVerifier = .{ .allocator = allocator, .references = captured.bind() };
        \\    try verifier.verify();
        \\}
    );
}

test "slice-loop-reentrant-grow: callback backing census all distinct callers stay quiet" {
    try testing.expectNoFireTyped(check, callback_backing_source ++
        \\fn first(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    defer captured.list.deinit(allocator);
        \\    var verifier: ViewVerifier = .{ .allocator = allocator, .references = captured.bind() };
        \\    try verifier.verify();
        \\}
        \\fn second(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    defer captured.list.deinit(allocator);
        \\    var verifier: ViewVerifier = .{ .allocator = allocator, .references = captured.bind() };
        \\    try verifier.verify();
        \\}
    );
}

test "slice-loop-reentrant-grow: callback backing census same object remains unsafe" {
    try testing.expectFiresTyped(check, R, callback_backing_source ++
        \\fn selected(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    defer captured.list.deinit(allocator);
        \\    try captured.list.append(allocator, 1);
        \\    const sink = captured.bind();
        \\    try sink.references(sink.context, &captured.list);
        \\}
    );
}

test "slice-loop-reentrant-grow: callback backing census copied header remains unsafe" {
    try testing.expectFiresTyped(check, R, callback_backing_source ++
        \\fn selected(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    defer captured.list.deinit(allocator);
        \\    try captured.list.append(allocator, 1);
        \\    var copied = captured.list;
        \\    const sink = captured.bind();
        \\    try sink.references(sink.context, &copied);
        \\}
    );
}

test "slice-loop-reentrant-grow: callback backing census escaped dispatcher remains unknown" {
    try testing.expectFiresTyped(check, R, callback_backing_source ++
        \\pub fn selected(allocator: std.mem.Allocator) !*const ReferenceSink {
        \\    const captured = try allocator.create(Captured);
        \\    captured.* = .{ .allocator = allocator };
        \\    return captured.bind();
        \\}
    );
}

test "slice-loop-reentrant-grow: callback backing census additional aliasing caller remains unsafe" {
    try testing.expectFiresTyped(check, R, callback_backing_source ++
        \\fn separate(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    defer captured.list.deinit(allocator);
        \\    var verifier: ViewVerifier = .{ .allocator = allocator, .references = captured.bind() };
        \\    try verifier.verify();
        \\}
        \\fn aliases(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    defer captured.list.deinit(allocator);
        \\    try captured.list.append(allocator, 1);
        \\    const sink = captured.bind();
        \\    try sink.references(sink.context, &captured.list);
        \\}
    );
}

test "slice-loop-reentrant-grow: callback backing census every inline actual remains unsafe" {
    try testing.expectFiresTyped(check, R, callback_backing_source ++
        \\fn selected(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    defer captured.list.deinit(allocator);
        \\    try captured.list.append(allocator, 1);
        \\    var collected: List = .empty;
        \\    defer collected.deinit(allocator);
        \\    try collected.append(allocator, 2);
        \\    const sink = captured.bind();
        \\    inline for (.{ false, true }) |shared| {
        \\        const list = if (shared) &captured.list else &collected;
        \\        try sink.references(sink.context, list);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: const view alias same-object mutable actual remains unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Owner = struct { list: List = .empty };
        \\fn append(gpa: std.mem.Allocator, output: *Owner, view: *const Owner, value: u32) !void {
        \\    _ = view.list.items.len;
        \\    try output.list.append(gpa, value);
        \\}
        \\fn scan(gpa: std.mem.Allocator, view: *const Owner, output: *Owner) !void {
        \\    for (view.list.items) |value| {
        \\        try append(gpa, output, view, value);
        \\    }
        \\}
        \\fn sameObject(gpa: std.mem.Allocator) !void {
        \\    var owner: Owner = .{};
        \\    defer owner.list.deinit(gpa);
        \\    try owner.list.append(gpa, 1);
        \\    try scan(gpa, &owner, &owner);
        \\}
    );
}

test "slice-loop-reentrant-grow: const view alias copied header mutable actual remains unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Owner = struct { list: List = .empty };
        \\fn append(gpa: std.mem.Allocator, output: *List, view: *const Owner, value: u32) !void {
        \\    _ = view.list.items.len;
        \\    try output.appendSlice(gpa, &.{value});
        \\}
        \\fn scan(gpa: std.mem.Allocator, view: *const Owner) !void {
        \\    var copied = view.list;
        \\    for (view.list.items) |value| {
        \\        try append(gpa, &copied, view, value);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: callback backing header copied after registration remains unsafe" {
    try testing.expectFiresTyped(check, R, callback_backing_source ++
        \\fn selected(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    var input: Captured = .{ .allocator = allocator };
        \\    defer input.list.deinit(allocator);
        \\    try input.list.append(allocator, 1);
        \\    const sink = captured.bind();
        \\    captured.list = input.list;
        \\    try sink.references(sink.context, &input.list);
        \\}
    );
}

test "slice-loop-reentrant-grow: callback backing fresh local published after registration remains unsafe" {
    try testing.expectFiresTyped(check, R, callback_backing_source ++
        \\fn selected(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{ .allocator = allocator };
        \\    var collected: List = .empty;
        \\    defer collected.deinit(allocator);
        \\    try collected.append(allocator, 1);
        \\    const sink = captured.bind();
        \\    captured.list = collected;
        \\    try sink.references(sink.context, &collected);
        \\}
    );
}
