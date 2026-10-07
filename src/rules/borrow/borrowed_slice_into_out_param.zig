//! Borrowed-slice-into-out-param detector — `defer <X>.deinit()`
//! (or `defer alloc.free(<X>)`) registers cleanup for a local
//! buffer / arena, and a later write `<out>.* = ...<X>...` (or
//! `<out>.field = ...<X>...`) pushes a view of `<X>` into a
//! caller-visible out-parameter.  When the defer fires on
//! function return, the out-param holds a dangling slice.
//! Canonical returned-storage proofs distinguish independently owned snapshots
//! from fresh outer allocations that still retain deferred storage.
//!
//! Real-world: oven-sh/bun#30151 (`query_string.* =
//! ZigString.init(result.query_string)` where
//! `result.query_string` was sliced from `specifier_utf8`, which
//! `defer specifier_utf8.deinit()` would free on return),
//! #30223 (same fn, sibling out-param), #25563 (`install.ca = .{
//! .str = str }` borrowing parser-arena memory freed by
//! `defer parser.deinit()`).

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const query = @import("../../ast/token_query.zig");
const problem_mod = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const return_storage = @import("../../cache/return_storage.zig");
const storage_alias = @import("../../cache/storage_alias.zig");
const call_summary = @import("../../cache/call_summary.zig");
const type_query = @import("../../model/type_query.zig");
const fresh_storage = @import("../../cache/fresh_storage.zig");
const type_engine = @import("type_engine");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const Atom = query.Atom;
const R = "borrowed-slice-into-out-param";

// `defer <X>.<deinit|close>(...)` — $0 = X (the cleanup receiver,
// which is what becomes invalid after the defer fires).
const defer_cleanup = &[_]Atom{
    .{ .tok = .keyword_defer },
    .{ .capture = 0 },
    .{ .tok = .period },
    .{ .pred = isDeinitOrClose },
    .{ .tok = .l_paren },
};

// `defer <_>.free(<X>...)` — the freed thing is the FIRST ARG,
// not the receiver.  $0 = the freed name.
const defer_free = &[_]Atom{
    .{ .tok = .keyword_defer },
    .{ .tok = .identifier },
    .{ .tok = .period },
    .{ .text = "free" },
    .{ .tok = .l_paren },
    .{ .capture = 0 },
};

// `<out>.* = ...` OR `<out>.<field> = ...` — $0 = out.
const write_via_out = &[_]Atom{
    .{ .capture = 0 },
    .{ .any_of = &[_][]const Atom{
        &[_]Atom{ .{ .tok = .period_asterisk }, .{ .tok = .equal } },
        &[_]Atom{ .{ .tok = .period }, .{ .tok = .identifier }, .{ .tok = .equal } },
    } },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .borrowed_slice_into_out_param)) return;
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |fn_entry| {
        try checkFn(gpa, tree, cache, fn_entry.node, fn_entry.proto, fn_entry.body, problems);
    }
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    fn_decl: Ast.Node.Index,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Cheap pre-scan: any `defer` keyword at all?  Without one the
    // rule can never fire, so skip the binding-walk cost.
    if (!tokens.hasTokenInRange(tags, first, last, .keyword_defer)) return;

    const bindings = try cache.localBindings(proto, body);

    // Keep the complete parameter declaration and its lexical owner.
    // A terminal name cannot distinguish nested or imported type graphs.
    const model = try cache.fileModel();
    const owner: ?file_cache_mod.FileCache.ResolvedType = if (model.containingTypeOf(fn_decl)) |ti|
        .{ .model = model, .info = ti, .path = cache.file_path, .module = cache.module_id }
    else
        null;

    var pointer_params: std.ArrayListUnmanaged(PointerParam) = .empty;
    defer pointer_params.deinit(gpa);
    for (bindings.items) |b| {
        if (b.origin != .param) continue;
        if (!isPointerType(tags, b.rhs_first, b.rhs_last)) continue;
        try pointer_params.append(gpa, .{
            .name = b.name,
            .declared = .{ .tree = tree, .first = b.rhs_first, .last = b.rhs_last, .owner = owner, .allow_array_length_expr = true },
        });
    }
    if (pointer_params.items.len == 0) return;

    // Deferred names registered for cleanup, with their lexical
    // scope.  A `defer X.deinit()` in `else { ... }` does NOT
    // register when control passes through the sibling `if` branch
    // — pairing it with a write in that branch is a false alarm.
    // Track each defer's enclosing scope so writes outside that
    // scope are excluded.  Skips nested fn bodies so a `defer`
    // inside `const f = struct { fn g() void { defer ... } }`
    // doesn't pollute the outer fn's deferred-name set.
    var deferred: std.ArrayListUnmanaged(DeferredItem) = .empty;
    defer deferred.deinit(gpa);
    var t: Ast.TokenIndex = first;
    while (t <= last) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            t = if (t < last) t + 1 else last + 1;
            continue;
        }
        if (tags[t] != .keyword_defer) {
            t += 1;
            continue;
        }
        if (query.matchAt(tree, defer_cleanup, t, last, null)) |m| {
            const name = m.captureText(tree, 0).?;
            // Skip module/namespace identifiers (e.g. `defer posix.close(fd)`
            // where `posix` is `std.posix`) — they are not local variables.
            if (bindings.find(name) != null) {
                const range = enclosingScope(tags, t, first, last);
                try deferred.append(gpa, .{
                    .name = name,
                    .token = t,
                    .scope_open = range.open,
                    .scope_close = range.close,
                });
            }
            t = m.end + 1;
            continue;
        }
        if (query.matchAt(tree, defer_free, t, last, null)) |m| {
            const range = enclosingScope(tags, t, first, last);
            try deferred.append(gpa, .{
                .name = m.captureText(tree, 0).?,
                .token = t,
                .scope_open = range.open,
                .scope_close = range.close,
            });
            t = m.end + 1;
            continue;
        }
        t += 1;
    }
    if (deferred.items.len == 0) return;

    // Find writes through pointer params; check RHS for any deferred name.
    try scanWrites(gpa, tree, cache, write_via_out, first, last, pointer_params.items, deferred.items, problems);
}

fn scanWrites(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    atoms: []const Atom,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    pointer_params: []const PointerParam,
    deferred: []const DeferredItem,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const writes = try query.findAllInBody(gpa, tree, atoms, first, last);
    defer gpa.free(writes);
    for (writes) |w| {
        const out_name = w.captureText(tree, 0).?;
        const pp = findPointerParam(out_name, pointer_params) orelse continue;
        const sc = tokens.findStmtSemicolon(tags, w.end + 1, last) orelse continue;
        if (sc <= w.end + 1) continue;
        const dn = rhsMentionsDeferred(tree, w.start, w.end, sc, first, last, deferred) orelse continue;
        // A copied value is independent only if its entire retained graph
        // carries no address. Resolve actual expressions in this document;
        // the shared proof reads each nested field in its declaring frame.
        // Integer representations of addresses still retain those addresses.
        if (!rhsHasAddressBits(tree, w.end + 1, sc - 1)) {
            if (try expressionIsAddressFree(cache, w.start, w.end - 1) or
                try expressionIsAddressFree(cache, w.end + 1, sc - 1) or
                (cache.zls == null and declaredFieldIsAddressFree(cache, pp, w.start, w.end - 1))) continue;
        }
        // RHS-shape check: when the assigned value comes from a
        // `*.toOwnedSlice(*)` / `*.dupe(*)` / `*.clone(*)` call, the
        // value is OWNED (newly-allocated by the call's allocator
        // arg), not a borrow of the deferred local.  The deferred
        // cleanup happens AFTER the copy is made; out-param holds
        // a valid allocation.
        if (rhsContainsCopyingCall(tree, w.end + 1, sc - 1)) continue;
        // RHS contains `<X>.create(... allocator ... <slice> ...)`
        // — the call is an allocator-backed constructor that
        // canonically dupes its non-allocator args (Bun's
        // `Type.create(global, allocator, ..., slice)` pattern,
        // body does `allocator.dupe(u8, slice)`).  The out-param
        // receives the new owned copy, not a borrow.
        if (rhsContainsAllocatorConstructor(tree, w.end + 1, sc - 1)) continue;
        // The canonical returned-storage proof checks the complete retained
        // graph, including fields stored through a freshly allocated pointer.
        // A fresh outer allocation alone cannot discharge a borrowed payload.
        if (try rhsCallDoesNotBorrowDeferred(tree, cache, w.end + 1, sc - 1, dn)) continue;
        // Switch-scrutinee-only skip: when the RHS is
        // `switch (<expr-mentioning-deferred>) { <arms-not-mentioning-it> }`,
        // the deferred slice is consumed by the expression that the
        // switch is BRANCHING on; the arms build the result from the
        // unpacked union payloads, not from the slice.  Common shape
        // around connect/dispatch APIs:
        //   `this.socket = switch (group.connect(..., hostz, ...)) {
        //        .failed => return error..., .socket => |s| ..., }`
        // Net effect: the deferred slice is transient (lives only
        // through the call), and the out-param holds independent
        // bytes (the unpacked Socket).
        if (deferredOnlyInSwitchScrutinee(tree, w.end + 1, sc - 1, dn)) continue;
        try report(gpa, problems, tree, w.start, out_name, dn);
    }
}

const PointerParam = struct { name: []const u8, declared: type_query.TypeRef };

/// A `defer X.deinit()` / `defer alloc.free(X)` paired with the
/// lexical `{ ... }` it was declared inside.  Writes outside that
/// scope cannot see the registered cleanup — the defer hasn't
/// executed when control passes a sibling branch.
const DeferredItem = struct {
    name: []const u8,
    /// The `defer` keyword that registered the cleanup.
    token: Ast.TokenIndex,
    scope_open: Ast.TokenIndex,
    scope_close: Ast.TokenIndex,
};

const ScopeRange = struct { open: Ast.TokenIndex, close: Ast.TokenIndex };

/// Walk braces around `tok` to find the immediate enclosing
/// `{ ... }` pair.  Fall back to the fn body range when the defer
/// sits at the function-top scope.
fn enclosingScope(
    tags: []const std.zig.Token.Tag,
    tok: Ast.TokenIndex,
    fn_first: Ast.TokenIndex,
    fn_last: Ast.TokenIndex,
) ScopeRange {
    var open: Ast.TokenIndex = fn_first;
    var depth: i32 = 0;
    var t: Ast.TokenIndex = tok;
    while (t > fn_first) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => depth += 1,
            .l_brace => {
                if (depth == 0) {
                    open = t;
                    break;
                }
                depth -= 1;
            },
            else => {},
        }
    }
    var close: Ast.TokenIndex = fn_last;
    depth = 1;
    t = open + 1;
    while (t <= fn_last) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => {
                depth -= 1;
                if (depth == 0) {
                    close = t;
                    break;
                }
            },
            else => {},
        }
    }
    return .{ .open = open, .close = close };
}

fn findPointerParam(name: []const u8, params: []const PointerParam) ?PointerParam {
    for (params) |p| if (std.mem.eql(u8, p.name, name)) return p;
    return null;
}

/// Unknown and address-bearing types both refuse the shared deep proof.
/// The SDK frame, not a local token spelling, owns every actual field type.
fn expressionIsAddressFree(
    cache: *file_cache_mod.FileCache,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) !bool {
    const resolver = cache.zls orelse return false;
    const node = cache.nodeForExactSpan(first, last) orelse return false;
    const frame = resolver.resolutionFrame();
    const actual = (try frame.typeOfNode(node)) orelse return false;
    return actualTypeIsAddressFree(frame, actual, 0);
}

/// Extend the shared scalar/struct proof to unions. Every possible payload
/// must carry no address, not just the tag or the currently selected member.
fn actualTypeIsAddressFree(
    frame: type_engine.TypeResolver.ResolutionFrame,
    ty: type_engine.TypeResolver.ActualType,
    depth: u8,
) file_cache_mod.SummaryError!bool {
    if (depth > type_query.max_element_depth) return false;
    const actual = (try frame.resolver.normalizedType(ty)) orelse return false;
    switch (actual.data) {
        .array => |array| return actualTypeIsAddressFree(frame, array.elem_ty.*, depth + 1),
        .optional => |payload| return actualTypeIsAddressFree(frame, payload.*, depth + 1),
        .ip_index => {
            const index = actual.ipIndex() orelse return false;
            switch (frame.resolver.ctx.ip.zigTypeTag(index) orelse return false) {
                .array, .vector, .optional => {
                    const child = frame.resolver.childType(actual) orelse return false;
                    return actualTypeIsAddressFree(frame, child, depth + 1);
                },
                else => {},
            }
        },
        .container => |container| {
            const declaring = frame.resolver.frameForContainer(container);
            const tree = &declaring.handle.document.tree;
            const node = container.scope_handle.toNode();
            const kind = tree.tokenTag(tree.nodeMainToken(node));
            switch (kind) {
                .keyword_struct, .keyword_union => {},
                else => return fresh_storage.actualTypeAddressFree(frame, actual, depth, null),
            }
            var buffer: [2]Ast.Node.Index = undefined;
            const declaration = tree.fullContainerDecl(&buffer, node) orelse return false;
            for (declaration.ast.members) |member| {
                const field = tree.fullContainerField(member) orelse continue;
                const type_node = field.ast.type_expr.unwrap() orelse {
                    // A payloadless union member is void, not an unknown type.
                    if (kind == .keyword_union) continue;
                    return false;
                };
                const field_type = (try declaring.typeOfNode(type_node)) orelse return false;
                if (!try actualTypeIsAddressFree(declaring, field_type, depth + 1)) return false;
            }
            return true;
        },
        else => {},
    }
    return fresh_storage.actualTypeAddressFree(frame, actual, depth, null);
}

/// Declaration fallback for runs without the SDK. Never look up a leaf
/// name globally, or inspect a foreign field through the caller's tree.
fn declaredFieldIsAddressFree(
    cache: *file_cache_mod.FileCache,
    param: PointerParam,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    const tree = param.declared.tree;
    const tags = tree.tokens.items(.tag);
    if (last != first + 2 or tags[first + 1] != .period or tags[last] != .identifier) return false;
    var base = type_query.stripPointers(param.declared);
    while (base.first <= base.last and tags[base.first] == .keyword_const) base.first += 1;
    if (base.first > base.last) return false;
    const owner = if (tags[base.first] == .builtin and
        std.mem.eql(u8, tree.tokenSlice(base.first), "@This") and base.last == base.first + 2)
        base.owner orelse return false
    else blk: {
        var buffer: [256]u8 = undefined;
        const name = type_query.typePathName(&buffer, base) orelse return false;
        break :blk if (base.owner) |scope|
            cache.typePathInOwnerScope(scope, name) orelse return false
        else
            cache.resolvedTypePathAcrossImports(name) orelse return false;
    };
    const field = owner.info.findField(tree.tokenSlice(last)) orelse return false;
    return type_query.typeRangeIsAddressFree(cache, .{
        .tree = owner.model.tree,
        .first = field.type_first,
        .last = field.type_last,
        .owner = owner,
        .allow_array_length_expr = true,
    }, 0);
}

fn rhsHasAddressBits(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    var t = first;
    while (t <= last) : (t += 1) {
        if (tags[t] != .builtin) continue;
        const name = tree.tokenSlice(t);
        if (std.mem.eql(u8, name, "@intFromPtr") or std.mem.eql(u8, name, "@ptrFromInt") or
            std.mem.eql(u8, name, "@bitCast")) return true;
    }
    return false;
}

fn rhsContainsCopyingCall(tree: *const Ast, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    if (start + 2 > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        const m = tree.tokenSlice(t + 1);
        if (isCopyingMethodName(m)) return true;
        // Singleton-store .append pattern: `<X>.<...>.instance.append(`
        // — Bun's `FileSystem.DirnameStore.instance.append(T, slice)`
        // dupes the slice into the static store.  Recognising the
        // `.instance.append(` shape catches the canonical case
        // without broadening `.append` (which is also used by
        // ArrayList for non-duping appends).
        if (std.mem.eql(u8, m, "append") and t >= 2 and
            tags[t - 2] == .period and
            tags[t - 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t - 1), "instance")) return true;
    }
    return false;
}

fn isCopyingMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "toOwnedSlice") or
        std.mem.eql(u8, name, "toOwnedSliceSentinel") or
        std.mem.eql(u8, name, "toOwned") or
        std.mem.eql(u8, name, "intoOwned") or
        std.mem.eql(u8, name, "dupe") or
        std.mem.eql(u8, name, "dupeZ") or
        std.mem.eql(u8, name, "clone") or
        std.mem.eql(u8, name, "cloneZ") or
        std.mem.eql(u8, name, "copyFrom") or
        std.mem.eql(u8, name, "copyForwards") or
        std.mem.eql(u8, name, "copyBackwards");
}

/// An unresolved callee, incomplete storage set, or possible alias refuses
/// independence. All semantic and source errors propagate to the caller.
fn rhsCallDoesNotBorrowDeferred(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    deferred_name: []const u8,
) file_cache_mod.SummaryError!bool {
    const tags = tree.tokens.items(.tag);
    var first = start;
    if (first <= end and tags[first] == .keyword_try) first += 1;
    if (first > end) return false;
    const node = cache.nodeForExactSpan(first, end) orelse return false;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, node) orelse return false;
    const token = fresh_storage.calleeQueryToken(tree, call);
    var remaining: u32 = call_summary.actual_query_work_limit;
    const context: storage_alias.QueryContext = .{ .remaining = &remaining };
    const returned = try return_storage.returnedStorageAt(cache, token, context);
    if (!returned.complete) return false;
    if (returned.alternatives.len == 0) return true;
    const actual = (try cache.actualCallSummaryAt(token, null)) orelse return false;
    var saw_deferred = false;
    var t = first;
    while (t <= end) : (t += 1) {
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), deferred_name)) continue;
        if (t > first and tags[t - 1] == .period) continue;
        saw_deferred = true;
        const deferred_node = cache.nodeForExactSpan(t, t) orelse return false;
        for (returned.alternatives) |alternative| {
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const selected = (try return_storage.mappedStorageAt(
                cache,
                actual,
                alternative,
                &argument_buffer,
            )) orelse return false;
            if (try storage_alias.mayShareStorageAt(
                cache,
                node,
                selected,
                .{ .node = deferred_node },
                .reachable_storage,
                context,
            )) return false;
        }
    }
    return saw_deferred;
}

/// True iff the RHS at `[start..end]` is a `switch (...) { ... }`
/// expression whose `<deferred_name>` mentions appear ONLY inside
/// the switch's scrutinee `(...)` — i.e., never inside the arms
/// block `{ ... }`.  When the deferred slice is consumed by the
/// expression the switch branches on, and the arms build the
/// result from unpacked union payloads (not from the slice), the
/// slice is transient and can't reach the out-param.
fn deferredOnlyInSwitchScrutinee(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    deferred_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    // Peel optional leading `try`.
    var t: Ast.TokenIndex = start;
    if (t <= end and tags[t] == .keyword_try) t += 1;
    if (t > end or tags[t] != .keyword_switch) return false;
    // Scrutinee starts at the next `(`.
    var p = t + 1;
    while (p <= end and tags[p] != .l_paren) : (p += 1) {}
    if (p > end or tags[p] != .l_paren) return false;
    const scrut_end = matchParenEnd(tags, p, end) orelse return false;
    if (scrut_end + 1 > end or tags[scrut_end + 1] != .l_brace) return false;
    const arms_open: Ast.TokenIndex = scrut_end + 1;
    const arms_close = matchBraceEnd(tags, arms_open, end) orelse return false;
    // Walk RHS; ensure all deferred-name mentions land in
    // (p, scrut_end) and NONE land in (arms_open, arms_close].
    var saw_in_scrut = false;
    var k: Ast.TokenIndex = start;
    while (k <= end) : (k += 1) {
        if (tags[k] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k), deferred_name)) continue;
        if (k > p and k < scrut_end) {
            saw_in_scrut = true;
        } else if (k > arms_open and k <= arms_close) {
            // Mention in the arm block — slice CAN reach the result.
            return false;
        } else {
            // Mention outside both — unexpected shape, bail.
            return false;
        }
    }
    return saw_in_scrut;
}

const matchBraceEnd = tokens.matchBrace;
const matchParenEnd = tokens.matchParen;

fn rhsContainsAllocatorConstructor(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start + 2 > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        const m = tree.tokenSlice(t + 1);
        const is_ctor = std.mem.eql(u8, m, "create") or
            std.mem.eql(u8, m, "init") or
            std.mem.eql(u8, m, "new") or
            std.mem.eql(u8, m, "from") or
            std.mem.eql(u8, m, "fromJS") or
            std.mem.eql(u8, m, "fromUTF8") or
            std.mem.eql(u8, m, "make");
        if (!is_ctor) continue;
        // Walk arg tokens balanced to the matching `)`, checking
        // for an allocator name.
        var depth: u32 = 1;
        var u: Ast.TokenIndex = t + 3;
        while (u <= end and depth > 0) : (u += 1) {
            switch (tags[u]) {
                .l_paren => depth += 1,
                .r_paren => {
                    depth -= 1;
                    if (depth == 0) break;
                },
                .identifier => {
                    const id = tree.tokenSlice(u);
                    if (std.mem.eql(u8, id, "allocator") or
                        std.mem.eql(u8, id, "alloc") or
                        std.mem.eql(u8, id, "gpa") or
                        std.mem.endsWith(u8, id, "_allocator") or
                        std.mem.endsWith(u8, id, "Allocator"))
                        return true;
                },
                else => {},
            }
        }
    }
    return false;
}

/// True iff the type expression starts with a pointer, including the
/// lexer's combined `**` token and an optional pointer qualifier.
fn isPointerType(tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    if (first > last) return false;
    var t: Ast.TokenIndex = first;
    if (tags[t] == .question_mark) {
        if (t + 1 > last) return false;
        t += 1;
    }
    return tags[t] == .asterisk or tags[t] == .asterisk_asterisk;
}

fn isDeinitOrClose(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or std.mem.eql(u8, name, "close");
}

/// Return a deferred local used by the RHS. An address of a local is
/// still a borrow; transient call arguments require a callee proof.
/// `write_first`/`write_eq` span the written place and its `=`; `stmt_end`
/// is the write's `;`.  A cleanup that a later clearing defer outruns is
/// not a registered cleanup for this write (see `clearedBeforeCleanup`).
fn rhsMentionsDeferred(
    tree: *const Ast,
    write_first: Ast.TokenIndex,
    write_eq: Ast.TokenIndex,
    stmt_end: Ast.TokenIndex,
    fn_first: Ast.TokenIndex,
    fn_last: Ast.TokenIndex,
    deferred: []const DeferredItem,
) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    const start = write_eq + 1;
    const end = stmt_end - 1;
    if (start > end) return null;
    var t: Ast.TokenIndex = start;
    while (t <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        // Skip `<recv>.<deferred>` — a field/method named the
        // same as a deferred local isn't the local itself.
        // Without this, `ctx.body` matches a `body` local on the
        // post-`.` identifier.
        if (t > 0 and tags[t - 1] == .period) continue;
        const name = tree.tokenSlice(t);
        for (deferred) |d| {
            if (!std.mem.eql(u8, d.name, name)) continue;
            // A defer in a sibling branch (or any block that doesn't
            // contain the write) hasn't executed when the write
            // runs — it can't have registered cleanup.  Only count
            // defers whose enclosing scope encloses this write.
            if (t < d.scope_open or t > d.scope_close) continue;
            if (clearedBeforeCleanup(tree, d, write_first, write_eq, stmt_end, fn_first, fn_last)) continue;
            return d.name;
        }
    }
    return null;
}

/// True when the written place is reset by a `defer <place> = <literal>;`
/// that runs before the cleanup `cleanup` registered.  Defers unwind
/// last-in-first-out, so a clearing defer in the cleanup's own scope and
/// registered after it runs first; the out-param never holds the freed
/// storage when the cleanup fires.  The clearing defer must be in force on
/// every exit that follows the write: registered before the write, or as
/// the statement right after it (no `try`/`return` can run in between).
/// The reset value must be a literal, which names no local and so
/// borrows nothing.
fn clearedBeforeCleanup(
    tree: *const Ast,
    cleanup: DeferredItem,
    write_first: Ast.TokenIndex,
    write_eq: Ast.TokenIndex,
    stmt_end: Ast.TokenIndex,
    fn_first: Ast.TokenIndex,
    fn_last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    const place_len = write_eq - write_first;
    const write_scope = enclosingScope(tags, write_first, fn_first, fn_last);
    const write_in_cleanup_scope = write_scope.open == cleanup.scope_open and write_scope.close == cleanup.scope_close;
    var t: Ast.TokenIndex = cleanup.token + 1;
    while (t + place_len + 2 <= cleanup.scope_close) : (t += 1) {
        if (tags[t] != .keyword_defer) continue;
        // After the write only the very next statement is guaranteed to
        // be registered on every path that leaves the scope.
        if (t > write_first and !(write_in_cleanup_scope and t == stmt_end + 1)) continue;
        var i: Ast.TokenIndex = 0;
        while (i < place_len) : (i += 1) {
            if (tags[t + 1 + i] != tags[write_first + i]) break;
            if (!std.mem.eql(u8, tree.tokenSlice(t + 1 + i), tree.tokenSlice(write_first + i))) break;
        }
        if (i != place_len or tags[t + 1 + place_len] != .equal) continue;
        const clearing_scope = enclosingScope(tags, t, fn_first, fn_last);
        if (clearing_scope.open != cleanup.scope_open or clearing_scope.close != cleanup.scope_close) continue;
        var value = t + 2 + place_len;
        var literal = value <= cleanup.scope_close;
        while (literal and tags[value] != .semicolon) : (value += 1) {
            literal = value < cleanup.scope_close and switch (tags[value]) {
                .period, .l_brace, .r_brace, .ampersand, .string_literal, .number_literal => true,
                .identifier => tags[value - 1] == .period or std.mem.eql(u8, tree.tokenSlice(value), "null"),
                else => false,
            };
        }
        if (literal) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    write_tok: Ast.TokenIndex,
    out_name: []const u8,
    deferred_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "write into out-param `{s}` uses `{s}` — `{s}` is registered for cleanup via `defer ... .deinit()`/`.free()`, so the out-param holds a dangling slice once the fn returns and the defer fires.  Clone the value with the caller's allocator before assigning",
        .{ out_name, deferred_name, deferred_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, write_tok),
        .end = try Pos.fromTokenEnd(tree, write_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "defer arena.deinit + out-param write using arena fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const ZigString = struct {
        \\    raw: u64 = 0,
        \\    // Returns a borrow of `s` — captures it into the
        \\    // result, so the result's lifetime is tied to `s`.
        \\    pub fn init(s: anytype) ZigString { return .{ .raw = s }; }
        \\};
        \\pub fn parse(out: *ZigString, gpa_alloc: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(gpa_alloc);
        \\    defer arena.deinit();
        \\    out.* = ZigString.init(arena);
        \\}
    );
}

test "defer alloc.free(X) + out-param write using X fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Str = struct { ptr: usize };
        \\pub fn parse(install: *Str, alloc: std.mem.Allocator) !void {
        \\    const str = try alloc.alloc(u8, 4);
        \\    defer alloc.free(str);
        \\    install.* = .{ .ptr = @intFromPtr(str.ptr) };
        \\}
    );
}

test "out-param not pointer doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn parse(name: []const u8) !void {
        \\    var buf = name;
        \\    defer _ = buf;
        \\}
    );
}

test "no defer doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn parse(out: *[]const u8, src: []const u8) !void {
        \\    out.* = src;
        \\}
    );
}

test "primitive-typed out field doesn't fire" {
    // `this.count = fn(deferred, ...)` — count is usize, can't hold
    // a borrowed slice.  The deferred name appears in args only.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Outer = struct {
        \\    count: u32 = 0,
        \\    pub fn doIt(this: *Outer, alloc: std.mem.Allocator) !void {
        \\        const buf = try alloc.alloc(u8, 4);
        \\        defer alloc.free(buf);
        \\        this.count = doWork(buf);
        \\    }
        \\};
        \\fn doWork(_: []u8) u32 { return 0; }
    );
}

test "RHS with toOwnedSlice copy doesn't fire" {
    // `out.* = blk: { ... break :blk try tmp.toOwnedSlice(allocator); };`
    // The break value is OWNED via toOwnedSlice using the caller's
    // allocator.  defer tmp.deref() doesn't invalidate the copy.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Wrapper = struct {
        \\    pub fn deref(_: Wrapper) void {}
        \\    pub fn toOwnedSlice(_: Wrapper, _: std.mem.Allocator) ![]const u8 {
        \\        return "";
        \\    }
        \\};
        \\fn makeTmp() Wrapper { return .{}; }
        \\pub fn parse(out: *[]const u8, allocator: std.mem.Allocator) !void {
        \\    const tmp = makeTmp();
        \\    defer tmp.deref();
        \\    out.* = try tmp.toOwnedSlice(allocator);
        \\}
    );
}

test "*@This() pointer param resolves field type via containing struct" {
    // The declared parameter scope binds `@This()` to its container.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const PI = struct {
        \\    file_count: u32 = 0,
        \\    pub fn install(this: *@This(), alloc: std.mem.Allocator) !void {
        \\        var subdir: std.fs.Dir = undefined;
        \\        defer subdir.close();
        \\        this.file_count = copyFiles(subdir, alloc);
        \\    }
        \\};
        \\fn copyFiles(_: std.fs.Dir, _: std.mem.Allocator) u32 { return 0; }
    );
}

test "self-recursive fn: param only in recursive return — does NOT fire" {
    // Mirrors the ghostty/bun pattern where a fn like `transpileSourceCode`
    // tail-recurses passing `referrer` along:
    //   `return transpileSourceCode(... referrer ...)`
    // The non-recursive returns don't embed `referrer` in the result.
    // `result_independent_of_args` used to return false because it saw
    // `referrer` in the recursive-return expression; now self-recursive
    // returns are skipped, so the rule correctly suppresses the finding.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Result = struct { code: []const u8 };
        \\pub fn transpile(
        \\    allocator: std.mem.Allocator,
        \\    source: []const u8,
        \\    referrer: []const u8,
        \\    ret: *Result,
        \\) error{Invalid}!void {
        \\    var slice = std.ArrayList(u8).init(allocator);
        \\    defer slice.deinit();
        \\    if (source.len == 0) {
        \\        return transpile(allocator, referrer, referrer, ret);
        \\    }
        \\    ret.* = Result{ .code = "ok" };
        \\}
    );
}

test "deferred arg not embedded even when other param is — does NOT fire" {
    // The retained parameter is disjoint from the private copied buffer.
    // Canonical returned-storage facts, not scalar dependencies, own this proof.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Result = struct { label: []const u8 };
        \\fn transpile(
        \\    referrer: []const u8,
        \\    other: []const u8,
        \\) Result {
        \\    _ = referrer;
        \\    return Result{ .label = other };
        \\}
        \\pub fn caller(
        \\    alloc: std.mem.Allocator,
        \\    raw: []const u8,
        \\    other: []const u8,
        \\    ret: *Result,
        \\) !void {
        \\    const slice = try alloc.dupe(u8, raw);
        \\    defer alloc.free(slice);
        \\    ret.* = transpile(slice, other);
        \\}
    );
}

test "deferred arg IS the embedded param — fires" {
    // Sanity check: when the deferred arg maps to a param that IS
    // embedded in the called function's return, we must still fire.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Result = struct { label: []const u8 };
        \\fn transpile(
        \\    referrer: []const u8,
        \\    other: []const u8,
        \\) Result {
        \\    _ = other;
        \\    // `referrer` IS embedded in the return.
        \\    return Result{ .label = referrer };
        \\}
        \\pub fn caller(
        \\    alloc: std.mem.Allocator,
        \\    other: []const u8,
        \\    ret: *Result,
        \\) !void {
        \\    const slice = try alloc.dupe(u8, "borrowed");
        \\    defer alloc.free(slice);
        \\    ret.* = transpile(slice, other);
        \\}
    );
}

test "namespace defer (defer posix.close) is not tracked as local — does NOT fire" {
    // `posix` is `std.posix` (module namespace), not a local variable.
    // `defer posix.close(fd)` must not register `posix` as a deferred name.
    try testing.expectNoFire(check,
        \\const posix = std.posix;
        \\pub fn setupSocket(client: *posix.socket_t) !void {
        \\    const listener = posix.socket(posix.AF.INET, posix.SOCK.STREAM, 0) catch unreachable;
        \\    defer posix.close(listener);
        \\    client.* = posix.socket(posix.AF.INET, posix.SOCK.STREAM, 0) catch unreachable;
        \\}
        \\
    );
}

test "typed optional aggregate out copy retains no address" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const budget_mod = struct {
        \\    pub const Limit = enum { nodes, time };
        \\    pub const Stop = struct { limit: Limit, cap: u32 };
        \\};
        \\const Stop = budget_mod.Stop;
        \\const Oracle = struct {
        \\    stopped: ?Stop = null,
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Oracle) void { self.allocator.free(self.bytes); }
        \\    fn merge(o: *Oracle, seed: Stop) !void {
        \\        var child: Oracle = .{ .stopped = seed, .allocator = o.allocator, .bytes = try o.allocator.alloc(u8, 1) };
        \\        defer child.deinit();
        \\        o.stopped = o.stopped orelse child.stopped;
        \\    }
        \\};
    );
}

test "typed optional aggregate out copy retains nullable pointer" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const budget_mod = struct {
        \\    pub const Limit = enum { nodes, time };
        \\    pub const Stop = struct { limit: Limit, cap: u32, detail: ?*u8 };
        \\};
        \\const Stop = budget_mod.Stop;
        \\const Oracle = struct {
        \\    stopped: ?Stop = null,
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Oracle) void { self.allocator.free(self.bytes); }
        \\    fn merge(o: *Oracle) !void {
        \\        const bytes = try o.allocator.alloc(u8, 1);
        \\        var child: Oracle = .{
        \\            .stopped = .{ .limit = .nodes, .cap = 1, .detail = &bytes[0] },
        \\            .allocator = o.allocator,
        \\            .bytes = bytes,
        \\        };
        \\        defer child.deinit();
        \\        o.stopped = o.stopped orelse child.stopped;
        \\    }
        \\};
    );
}

test "typed numeric union returned from deferred state retains no address" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const ranges = struct {
        \\    pub const Range = union(enum) {
        \\        unknown,
        \\        integer: struct { min: i128, max: i128 },
        \\        floating: struct { min: f64, max: f64 },
        \\    };
        \\};
        \\const Range = ranges.Range;
        \\const State = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *State) void { self.allocator.free(self.bytes); }
        \\    fn rangeOf(self: *const State, name: []const u8) ?Range {
        \\        _ = name;
        \\        return .{ .integer = .{ .min = 0, .max = @intCast(self.bytes.len) } };
        \\    }
        \\};
        \\const Output = struct { range: Range = .unknown };
        \\pub fn copy(out: *Output, allocator: std.mem.Allocator) !void {
        \\    var state: State = .{ .allocator = allocator, .bytes = try allocator.alloc(u8, 1) };
        \\    defer state.deinit();
        \\    out.range = state.rangeOf("") orelse .unknown;
        \\}
    );
}

test "typed slice-bearing union returned from deferred state retains an address" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const ranges = struct {
        \\    pub const Range = union(enum) {
        \\        unknown,
        \\        integer: struct { min: i128, max: i128 },
        \\        floating: struct { min: f64, max: f64, bytes: []const u8 },
        \\    };
        \\};
        \\const Range = ranges.Range;
        \\const State = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *State) void { self.allocator.free(self.bytes); }
        \\    fn rangeOf(self: *const State, name: []const u8) ?Range {
        \\        _ = name;
        \\        return .{ .floating = .{ .min = 0, .max = 1, .bytes = self.bytes } };
        \\    }
        \\};
        \\const Output = struct { range: Range = .unknown };
        \\pub fn copy(out: *Output, allocator: std.mem.Allocator) !void {
        \\    var state: State = .{ .allocator = allocator, .bytes = try allocator.alloc(u8, 1) };
        \\    defer state.deinit();
        \\    out.range = state.rangeOf("") orelse .unknown;
        \\}
    );
}

test "typed nested address-bearing aggregate is not a scalar suffix" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Payload = struct { data: []const u8 };
        \\const Status = struct { tag: u32, nested: [1]Payload };
        \\const Scratch = struct {
        \\    width: Status,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.width.nested[0].data); }
        \\};
        \\const Output = struct { value: Status };
        \\pub fn copy(out: *Output, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    var scratch: Scratch = .{ .allocator = allocator, .width = .{ .tag = 1, .nested = .{.{ .data = bytes }} } };
        \\    defer scratch.deinit();
        \\    out.value = scratch.width;
        \\}
    );
}

test "typed scalar projection of address-bearing source retains no address" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Scratch = struct {
        \\    score: ?u32,
        \\    bytes: []const u8,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.bytes); }
        \\};
        \\pub fn copy(out: *?u32, allocator: std.mem.Allocator) !void {
        \\    var scratch: Scratch = .{ .score = 7, .bytes = try allocator.alloc(u8, 1), .allocator = allocator };
        \\    defer scratch.deinit();
        \\    out.* = scratch.score;
        \\}
    );
}

test "typed scalar graph does not erase explicit address bits" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Output = struct { value: usize };
        \\pub fn copy(out: *Output, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    defer allocator.free(bytes);
        \\    out.value = @intFromPtr(bytes.ptr);
        \\}
    );
}

test "typed address of deferred slice header still escapes" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Scratch = struct {
        \\    bytes: []u8,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.bytes); }
        \\};
        \\pub fn copy(out: **[]u8, allocator: std.mem.Allocator) !void {
        \\    var scratch: Scratch = .{ .bytes = try allocator.alloc(u8, 1), .allocator = allocator };
        \\    defer scratch.deinit();
        \\    out.* = &scratch.bytes;
        \\}
    );
}

test "typed double pointer can retain an independent slice header" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn copy(out: **[]u8, stable: *[]u8, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    defer allocator.free(bytes);
        \\    out.* = stable;
        \\}
    );
}

test "typed array copy retains borrowed element pointers" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Scratch = struct {
        \\    slots: [1]*u8,
        \\    bytes: []u8,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.bytes); }
        \\};
        \\pub fn copy(out: *[1]*u8, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    var scratch: Scratch = .{ .slots = .{&bytes[0]}, .bytes = bytes, .allocator = allocator };
        \\    defer scratch.deinit();
        \\    out.* = scratch.slots[0..1].*;
        \\}
    );
}

test "later defer clearing the out-param before the cleanup doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Capture) void { _ = self; }
        \\};
        \\const Oracle = struct { capture: ?*Capture = null };
        \\pub fn after(o: *Oracle, gpa: std.mem.Allocator) !void {
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    o.capture = &exits;
        \\    defer o.capture = null;
        \\}
        \\pub fn before(o: *Oracle, gpa: std.mem.Allocator) !void {
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    defer o.capture = null;
        \\    o.capture = &exits;
        \\}
    );
}

test "clearing defer registered before the cleanup still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Capture) void { _ = self; }
        \\};
        \\const Oracle = struct { capture: ?*Capture = null };
        \\pub fn run(o: *Oracle, gpa: std.mem.Allocator) !void {
        \\    defer o.capture = null;
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    o.capture = &exits;
        \\}
    );
}

test "clearing defer registered after a possible early exit still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Capture) void { _ = self; }
        \\};
        \\const Oracle = struct { capture: ?*Capture = null };
        \\fn step() !void {}
        \\pub fn run(o: *Oracle, gpa: std.mem.Allocator) !void {
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    o.capture = &exits;
        \\    try step();
        \\    defer o.capture = null;
        \\}
    );
}

test "defer resetting the out-param to a local doesn't count as clearing" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Capture) void { _ = self; }
        \\};
        \\const Oracle = struct { capture: ?*Capture = null };
        \\pub fn run(o: *Oracle, gpa: std.mem.Allocator, other: *Capture) !void {
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    o.capture = &exits;
        \\    defer o.capture = other;
        \\}
    );
}

test "deferred module owning snapshot is independent of its source storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Snapshot = struct { bytes: []u8 };
        \\const Module = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Module) void { self.allocator.free(self.bytes); }
        \\    fn snapshotData(self: *const Module, gpa: std.mem.Allocator) !*Snapshot {
        \\        const snapshot = try gpa.create(Snapshot);
        \\        errdefer gpa.destroy(snapshot);
        \\        snapshot.* = .{ .bytes = try gpa.dupe(u8, self.bytes) };
        \\        return snapshot;
        \\    }
        \\};
        \\const Fixture = struct { data: ?*Snapshot = null };
        \\pub fn init(out: *Fixture, gpa: std.mem.Allocator) !void {
        \\    var module: Module = .{
        \\        .allocator = gpa, .bytes = try gpa.dupe(u8, "owned"),
        \\    };
        \\    defer module.deinit();
        \\    out.data = try module.snapshotData(gpa);
        \\}
    );
}

test "fresh snapshot allocation retaining deferred module bytes still escapes" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Snapshot = struct { bytes: []u8 };
        \\const Module = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Module) void { self.allocator.free(self.bytes); }
        \\    fn snapshotData(self: *const Module, gpa: std.mem.Allocator) !*Snapshot {
        \\        const snapshot = try gpa.create(Snapshot);
        \\        snapshot.* = .{ .bytes = self.bytes };
        \\        return snapshot;
        \\    }
        \\};
        \\const Fixture = struct { data: ?*Snapshot = null };
        \\pub fn init(out: *Fixture, gpa: std.mem.Allocator) !void {
        \\    var module: Module = .{
        \\        .allocator = gpa, .bytes = try gpa.dupe(u8, "borrowed"),
        \\    };
        \\    defer module.deinit();
        \\    out.data = try module.snapshotData(gpa);
        \\}
    );
}

test "deferred module borrowed return cannot inherit a same named owning summary" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Owning = struct {
        \\    fn snapshotData(gpa: std.mem.Allocator) ![]u8 {
        \\        return gpa.dupe(u8, "independent");
        \\    }
        \\};
        \\const Module = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Module) void { self.allocator.free(self.bytes); }
        \\    fn snapshotData(self: *const Module) []u8 { return self.bytes; }
        \\};
        \\pub fn init(out: *[]u8, gpa: std.mem.Allocator) !void {
        \\    var module: Module = .{
        \\        .allocator = gpa, .bytes = try gpa.dupe(u8, "borrowed"),
        \\    };
        \\    defer module.deinit();
        \\    out.* = module.snapshotData();
        \\}
    );
}

test "snapshot copied into a deferred local arena still escapes" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Module = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Module) void { self.allocator.free(self.bytes); }
        \\    fn snapshotData(self: *const Module, gpa: std.mem.Allocator) ![]u8 {
        \\        var arena = std.heap.ArenaAllocator.init(gpa);
        \\        defer arena.deinit();
        \\        return arena.allocator().dupe(u8, self.bytes);
        \\    }
        \\};
        \\pub fn init(out: *[]u8, gpa: std.mem.Allocator) !void {
        \\    var module: Module = .{
        \\        .allocator = gpa, .bytes = try gpa.dupe(u8, "borrowed"),
        \\    };
        \\    defer module.deinit();
        \\    out.* = try module.snapshotData(gpa);
        \\}
    );
}
