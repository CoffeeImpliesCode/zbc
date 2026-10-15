//! Owned-field-no-outer-cleanup detector — a struct `Outer` has a
//! value-typed field whose type (same file) exposes a cleanup
//! method (`deinit` / `close` / `destroy` / `free` / `stop` /
//! `finalize` / `dispose` / `release`). But `Outer` itself exposes NO cleanup
//! method.  Users who treat `Outer` as a plain value silently leak
//! the inner's owned non-memory resource (file handle, socket,
//! ref, mmap) when the outer goes out of scope.
//! A by-value mark whose cleanup only clears external boolean flags is
//! borrowed state, not an owned resource. Unknown cleanup stays conservative.
//!
//! Complement to `missing-deinit-on-composed-owner`: that rule
//! fires when `Outer.deinit` EXISTS but FORGETS to call
//! `<self>.<field>.deinit(...)`; this rule fires when `Outer.deinit`
//! is missing ENTIRELY.
//!
//! Rewritten via the AST-level model_query DSL.

const std = @import("std");
const Ast = std.zig.Ast;

const file_model = @import("../../model/file_model.zig");
const mq = @import("../../model/model_query.zig");
const problem = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const trace = @import("../../trace.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const method_names = @import("../../model/method_names.zig");
const tokens = @import("../../ast/tokens.zig");
const fn_summary = @import("../../model/fn_summary.zig");

const R = "owned-field-no-outer-cleanup";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(problem.Problem),
) !void {
    if (!config_mod.isEnabled(config, .owned_field_no_outer_cleanup)) return;

    const model = try cache.fileModel();

    // Find all structs that lack ANY cleanup method.  The
    // missing-deinit-on-composed-owner rule covers the case where
    // a cleanup method DOES exist but forgets the field.
    const outers = try mq.findTypes(gpa, model, .{
        .kind = .struct_,
        .no_method = .{ .name_pred = isCleanupName },
    });
    defer gpa.free(outers);

    for (outers) |outer| {
        if (cache.zls != null and privateTypeHasNoUses(tree, outer)) continue;
        // HashMap-context skip: a type whose only methods are
        // `hash` / `eql` is a comparison-key shape, not an owner.
        // Fields are values used for comparison (FD-as-key, etc.),
        // not allocations to free.
        if (isHashContextType(outer)) continue;
        // Linked-list node skip: if the type has a `next: ?*Self`
        // (or `prev: ?*Self`) field, it's a node in an external
        // intrusive container — the container's deinit walks the
        // chain and cleans entries.  Common in Bun's queues.
        if (isLinkedListNode(tree, outer)) continue;
        // Queue/Fifo container declaration: a type whose body
        // declares `pub const Queue = bun.LinearFifo(Self, ...)` /
        // `bun.UnboundedQueue(Self, ...)` / similar is entries-only;
        // the queue owns the lifecycle of its entries.
        if (typeIsQueueEntry(tree, outer)) continue;
        // Bun convention skip: `pub const new = bun.TrivialNew(T);`
        // (or `bun.New(T)`) declares the type as heap-allocated and
        // owned by a parent — the parent's deinit handles the
        // teardown, so absence of a deinit on T isn't a leak.  This
        // is a strong signal in Bun's codebase and orthogonal to
        // the "plain value type" case the rule targets.
        if (hasNewFactoryDecl(tree, outer)) continue;
        // Same convention via init-shape: `init(...) !*@This()` /
        // `init(...) *Self` means the struct is heap-allocated and
        // owned by an external caller — cleanup happens at the
        // owner's hand, not via a fn on the value.
        if (hasPointerReturningInit(tree, outer)) continue;
        // Find the first value-typed field whose type has a NON-TRIVIAL
        // cleanup method.  If the inner type's `deinit` (or whichever
        // cleanup method) has an empty / discard-only body, it does
        // nothing on drop — skipping the outer is harmless.  Common
        // for CSS/value-type uniform-API conformance: `pub fn deinit
        // (_: *@This(), _: Allocator) void {}`.
        const fields = try mq.findFields(gpa, model, tree, outer, .{
            .value_typed = true,
            .type_matches = .{ .has_method = .{ .name_pred = isCleanupName } },
        });
        defer gpa.free(fields);

        // Outer has no allocator/arena field?  Then it can't pass
        // one to an inner cleanup that requires it — the inner type
        // is meant to be cleaned by a CALLER that holds the
        // allocator, not by the outer struct.  Common in Bun's CSS
        // value types (`deinit(self, allocator: Allocator)`).
        const outer_has_allocator = outerHasAllocatorField(tree, outer);
        var hit: ?usize = null;
        for (fields, 0..) |f, i| {
            // Optional-null-default skip: `<field>: ?T = null`
            // only holds a non-null T when explicitly assigned.
            // A missing outer cleanup doesn't leak when the field
            // stays null — common for "lazy/optional sub-state".
            if (model.fieldIsOptionalNullDefault(outer.qualified_name, f.name)) continue;
            // Caller-supplied skip: the type's constructor takes a
            // parameter of the same name as `f`.  The field is
            // borrowed in from the caller's value; cleanup is
            // their responsibility, not ours.  Same heuristic as
            // composed-owner uses.
            if (fieldIsCallerSupplied(tree, outer, f.name)) continue;
            // Nested-type-owned-by-parent skip: when `outer` is a
            // nested type whose ENCLOSING type has a cleanup
            // method, the parent owns the entries.  Common Bun
            // pattern:
            //     pub const FSWatchTask = struct {
            //         entries: [8]Entry = undefined,
            //         pub const Entry = struct { event: Event, ... };
            //         pub fn deinit(this: *FSWatchTask) void { this.cleanEntries(); ... }
            //     };
            if (outerIsNestedInsideCleanupType(model, outer)) continue;
            const inner_ti = mq.resolveFieldTypeScoped(tree, model, outer, f) orelse continue;
            if (!hasReceiverResourceCleanup(tree, inner_ti)) continue;
            if (try hasCanonicalFieldCleanup(cache, tree, outer, f, inner_ti)) continue;
            if (try hasEquivalentFieldCleanup(cache, tree, outer, f, inner_ti)) continue;
            if (!anyNonTrivialCleanup(tree, inner_ti)) continue;
            if (cleanupOnlyClearsBorrowedFlags(tree, model, inner_ti)) continue;
            if (!outer_has_allocator and allCleanupMethodsNeedExtraArg(tree, inner_ti)) continue;
            // Tagged-union with ALL non-owned variants: dropping
            // the field never leaks regardless of the variant
            // held, so a missing inline cleanup is harmless.
            if (allUnionVariantsNonOwned(model, inner_ti)) continue;
            // File-scan: if the field's default is a non-owned
            // variant AND no assignment in this file ever writes
            // an OWNED variant to `<recv>.<field>`, the field
            // never holds an owned value — drop is safe.
            if (fieldStaysNonOwnedAcrossFile(tree, model, outer, f, inner_ti)) continue;
            hit = i;
            break;
        }
        const idx = hit orelse continue;
        const field = fields[idx];
        const inner = mq.resolveFieldTypeScoped(tree, model, outer, field).?;
        trace.match(R, tree, field.name_token, "owned field with no outer cleanup");
        try report(gpa, problems, tree, outer.name, field.name_token, field.name, inner.name);
    }
}

/// A private declaration with no references cannot construct an abandoned
/// instance. Reflection or namespace exposure prevents closing this census.
/// Untyped fixtures retain the declaration-only diagnostic contract.
fn privateTypeHasNoUses(tree: *const Ast, owner: *const file_model.TypeInfo) bool {
    const tags = tree.tokens.items(.tag);
    const name = owner.name_token;
    if (name < 1 or tags[name - 1] != .keyword_const) return false;
    if (name >= 2 and tags[name - 2] == .keyword_pub) return false;
    for (tags, 0..) |tag, raw| {
        const token: Ast.TokenIndex = @intCast(raw);
        if (tag == .identifier and token != name and std.mem.eql(u8, tree.tokenSlice(token), owner.name)) return false;
        if (tag == .builtin) {
            const builtin = tree.tokenSlice(token);
            if (std.mem.eql(u8, builtin, "@field") or std.mem.eql(u8, builtin, "@typeInfo") or
                std.mem.eql(u8, builtin, "@This") or std.mem.eql(u8, builtin, "@hasDecl") or
                std.mem.eql(u8, builtin, "@export")) return false;
        }
    }
    return true;
}

/// Static allocator callbacks are not receiver destructors. A reset-only
/// interface releases no resource; scalar handle mutations remain obligations.
fn hasReceiverResourceCleanup(tree: *const Ast, inner: *const file_model.TypeInfo) bool {
    for (inner.methods) |method| {
        const receiver = method.receiver orelse continue;
        if (!isCleanupName(method.name) or tokens.isTrivialBody(tree, method.body_first, method.body_last)) continue;
        const tags = tree.tokens.items(.tag);
        const first = method.body_first + 1;
        if (first + 5 == method.body_last and
            tags[first] == .identifier and std.mem.eql(u8, tree.tokenSlice(first), receiver.name) and
            tags[first + 1] == .period_asterisk and tags[first + 2] == .equal and
            tags[first + 3] == .identifier and std.mem.eql(u8, tree.tokenSlice(first + 3), "undefined") and
            tags[first + 4] == .semicolon) continue;
        if (cleanupOnlyMarksClosed(tree, inner, method)) continue;
        return true;
    }
    return false;
}

/// An accounting close that checks counters and sets a boolean does not release
/// storage. Calls, arithmetic writes and indirect stores refuse this proof.
fn cleanupOnlyMarksClosed(tree: *const Ast, inner: *const file_model.TypeInfo, method: file_model.MethodInfo) bool {
    const receiver = method.receiver orelse return false;
    const tags = tree.tokens.items(.tag);
    var saw_store = false;
    var t = method.body_first + 1;
    while (t < method.body_last) : (t += 1) {
        if (tags[t] == .l_paren and t > method.body_first and
            (tags[t - 1] == .identifier or tags[t - 1] == .builtin)) return false;
        switch (tags[t]) {
            .equal => {
                if (t < 3 or tags[t - 3] != .identifier or
                    !std.mem.eql(u8, tree.tokenSlice(t - 3), receiver.name) or
                    tags[t - 2] != .period or tags[t - 1] != .identifier) return false;
                const field = inner.findField(tree.tokenSlice(t - 1)) orelse return false;
                if (field.type_first != field.type_last or !std.mem.eql(u8, tree.tokenSlice(field.type_first), "bool")) return false;
                if (t + 2 >= method.body_last or tags[t + 1] != .identifier or tags[t + 2] != .semicolon) return false;
                const value = tree.tokenSlice(t + 1);
                if (!std.mem.eql(u8, value, "true") and !std.mem.eql(u8, value, "false")) return false;
                saw_store = true;
            },
            .plus_equal, .minus_equal, .asterisk_equal, .slash_equal,
            .period_asterisk, .ampersand,
            => return false,
            else => {},
        }
    }
    return saw_store;
}

/// A cleanup entry point can live on the actual owner rather than on its row.
/// Authenticate the receiver container and called declaration, not their names.
fn hasCanonicalFieldCleanup(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    outer: *const file_model.TypeInfo,
    field: *const file_model.FieldInfo,
    inner: *const file_model.TypeInfo,
) !bool {
    const resolver = cache.zls orelse return false;
    const frame = resolver.resolutionFrame();
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    const index = try cache.getCallIndex();
    var calls = index.by_callee_token.iterator();
    while (calls.next()) |entry| {
        const node = entry.value_ptr.*;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
        const callee_access = tree.nodeData(call.ast.fn_expr).node_and_token;
        const receiver = callee_access[0];
        if (tree.nodeTag(receiver) != .field_access) continue;
        const access = tree.nodeData(receiver).node_and_token;
        if (!std.mem.eql(u8, tree.tokenSlice(access[1]), field.name)) continue;
        const method = inner.findMethod(tree.tokenSlice(callee_access[1])) orelse continue;
        if (method.receiver == null or !isCleanupName(method.name)) continue;
        try cache.chargeNormalCleanup(node);
        const container = (try frame.containerOfNode(access[0])) orelse continue;
        const scope = container.scope_handle;
        if (&scope.handle.document.tree != tree or scope.scope == .root or
            tree.lastToken(scope.toNode()) != outer.body_last) continue;
        const canonical = (try cache.actualCallSummaryAt(entry.key_ptr.*, frame)) orelse continue;
        if (canonical.callee.tree != tree or canonical.callee.declaration != method.fn_decl) continue;
        if (!try cleanupHasOwnerScope(cache, tree, node, access[0], field.name, method.fn_decl)) continue;
        return true;
    }
    return false;
}

/// Formal-rooted cleanup is an owner entry point. A local temporary instead
/// needs an active defer, or paired error and normal cleanup in the same body.
/// An error-arm call alone says nothing about a successful handoff.
fn cleanupHasOwnerScope(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    call_node: Ast.Node.Index,
    base: Ast.Node.Index,
    field_name: []const u8,
    destructor: Ast.Node.Index,
) !bool {
    const token = tree.firstToken(call_node);
    var functions = tokens.iterFnDecls(tree);
    var declaration: ?Ast.Node.Index = null;
    var body_node: ?Ast.Node.Index = null;
    var width: usize = std.math.maxInt(usize);
    var function_buffer: [1]Ast.Node.Index = undefined;
    while (functions.next(&function_buffer)) |candidate| {
        const body = candidate.body;
        const first = tree.firstToken(body);
        const last = tree.lastToken(body);
        if (first < token and token < last and last - first < width) {
            declaration = candidate.node;
            body_node = body;
            width = last - first;
        }
    }
    const body = body_node orelse return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration.?) orelse return false;
    const bindings = (try cache.localBindings(proto, body)).*;
    var arena = std.heap.ArenaAllocator.init(cache.gpa);
    defer arena.deinit();
    const owner = try fn_summary.ownerOfExpr(arena.allocator(), tree, proto, &bindings,
        tree.firstToken(base), tree.lastToken(base), 0);
    const tags = tree.tokens.items(.tag);
    var prior = tree.firstToken(body) + 1;
    while (prior + 2 < token) : (prior += 1) {
        if (tags[prior] == .identifier and tags[prior + 1] == .period_asterisk and tags[prior + 2] == .equal and
            std.mem.eql(u8, tree.tokenSlice(prior), tree.tokenSlice(tree.firstToken(base)))) return false;
    }
    if (owner == .param) return true;
    const resolver = cache.zls orelse return false;
    const index = try cache.getCallIndex();
    var calls = index.by_callee_token.iterator();
    var error_cleanup: ?Ast.TokenIndex = null;
    var normal_cleanup: ?Ast.TokenIndex = null;
    while (calls.next()) |entry| {
        const node = entry.value_ptr.*;
        const first = tree.firstToken(node);
        if (first <= tree.firstToken(body) or first >= tree.lastToken(body)) continue;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
        const access = tree.nodeData(call.ast.fn_expr).node_and_token;
        if (tree.nodeTag(access[0]) != .field_access) continue;
        const receiver = tree.nodeData(access[0]).node_and_token;
        if (!std.mem.eql(u8, tree.tokenSlice(receiver[1]), field_name) or
            !std.mem.eql(u8, tree.getNodeSource(receiver[0]), tree.getNodeSource(base))) continue;
        const actual = (try cache.actualCallSummaryAt(entry.key_ptr.*, resolver.resolutionFrame())) orelse continue;
        if (actual.callee.tree != tree or actual.callee.declaration != destructor) continue;
        if (first > 0 and tags[first - 1] == .keyword_defer) return true;
        if (first > 0 and tags[first - 1] == .keyword_errdefer) {
            error_cleanup = first;
            continue;
        }
        var depth: usize = 0;
        var t = tree.firstToken(body);
        while (t < first) : (t += 1) {
            if (tags[t] == .l_brace) depth += 1;
            if (tags[t] == .r_brace) depth -= 1;
        }
        if (depth == 1) normal_cleanup = first;
    }
    const error_token = error_cleanup orelse return false;
    const normal_token = normal_cleanup orelse return false;
    if (error_token >= normal_token) return false;
    var t = error_token;
    while (t < normal_token) : (t += 1) {
        if (tags[t] == .keyword_return and tags[t + 1] != .keyword_error) return false;
    }
    return true;
}

/// Match an entire small destructor, not an arbitrary subset of its fields:
/// one authenticated call followed by at most an undefined whole-value reset.
fn hasEquivalentFieldCleanup(
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    outer: *const file_model.TypeInfo,
    field: *const file_model.FieldInfo,
    inner: *const file_model.TypeInfo,
) !bool {
    const resolver = cache.zls orelse return false;
    const tags = tree.tokens.items(.tag);
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    var arena = std.heap.ArenaAllocator.init(cache.gpa);
    defer arena.deinit();
    for (inner.methods) |cleanup| {
        const receiver = cleanup.receiver orelse continue;
        if (!isCleanupName(cleanup.name)) continue;
        const inner_call = (try firstStatementCall(cache, tree, cleanup)) orelse continue;
        const tail = tree.lastToken(inner_call.node) + 2;
        if (tail != cleanup.body_last) {
            if (tail + 5 != cleanup.body_last or tags[tail] != .identifier or
                !std.mem.eql(u8, tree.tokenSlice(tail), receiver.name) or
                tags[tail + 1] != .period_asterisk or tags[tail + 2] != .equal or
                !std.mem.eql(u8, tree.tokenSlice(tail + 3), "undefined") or tags[tail + 4] != .semicolon) continue;
        }
        var inner_buffer: [1]Ast.Node.Index = undefined;
        const inner_proto = tokens.fnProto(tree, &inner_buffer, cleanup.fn_decl) orelse continue;
        const inner_bindings = (try cache.localBindings(inner_proto, cleanup.body)).*;
        const expected = (try cache.actualCallSummaryAt(inner_call.token, resolver.resolutionFrame())) orelse continue;
        var callee_buffer: [1]Ast.Node.Index = undefined;
        const callee_proto = tokens.fnProto(expected.callee.tree, &callee_buffer, expected.callee.declaration) orelse continue;
        for (outer.methods) |candidate| {
            if (candidate.receiver == null) continue;
            const outer_call = (try firstStatementCall(cache, tree, candidate)) orelse continue;
            const actual = (try cache.actualCallSummaryAt(outer_call.token, resolver.resolutionFrame())) orelse continue;
            if (actual.callee.tree != expected.callee.tree or actual.callee.declaration != expected.callee.declaration or
                !actual.callee.reference.actual_type.eql(expected.callee.reference.actual_type)) continue;
            var outer_buffer: [1]Ast.Node.Index = undefined;
            const outer_proto = tokens.fnProto(tree, &outer_buffer, candidate.fn_decl) orelse continue;
            const outer_bindings = (try cache.localBindings(outer_proto, candidate.body)).*;
            var parameters = callee_proto.iterate(expected.callee.tree);
            var position: u32 = 0;
            var matched = true;
            while (parameters.next()) |_| : (position += 1) {
                var first_buffer: [2]Ast.Node.Index = undefined;
                var second_buffer: [2]Ast.Node.Index = undefined;
                const first = (try expected.callArgumentFor(cache, &first_buffer, position)) orelse { matched = false; break; };
                const second = (try actual.callArgumentFor(cache, &second_buffer, position)) orelse { matched = false; break; };
                const source = try fn_summary.ownerOfExpr(arena.allocator(), tree, inner_proto, &inner_bindings,
                    tree.firstToken(first), tree.lastToken(first), 0);
                const destination = try fn_summary.ownerOfExpr(arena.allocator(), tree, outer_proto, &outer_bindings,
                    tree.firstToken(second), tree.lastToken(second), 0);
                if (source != .param or destination != .param or source.param.param != 0 or destination.param.param != 0 or
                    !prefixedFieldPath(destination.param.path, field.name, source.param.path)) {
                    matched = false;
                    break;
                }
            }
            if (matched and position != 0) return true;
        }
    }
    return false;
}

fn prefixedFieldPath(actual: []const u8, prefix: []const u8, suffix: []const u8) bool {
    if (!std.mem.startsWith(u8, actual, prefix)) return false;
    if (suffix.len == 0) return actual.len == prefix.len;
    return actual.len == prefix.len + suffix.len + 1 and actual[prefix.len] == '.' and
        std.mem.eql(u8, actual[prefix.len + 1 ..], suffix);
}

const StatementCall = struct { node: Ast.Node.Index, token: Ast.TokenIndex };

fn firstStatementCall(cache: *file_cache_mod.FileCache, tree: *const Ast, method: file_model.MethodInfo) !?StatementCall {
    const first = method.body_first + 1;
    const end = tokens.findStmtSemicolon(tree.tokens.items(.tag), first, method.body_last) orelse return null;
    var entries = (try cache.getCallIndex()).by_callee_token.iterator();
    while (entries.next()) |entry| {
        const node = entry.value_ptr.*;
        if (tree.firstToken(node) == first and tree.lastToken(node) + 1 == end) {
            try cache.chargeNormalCleanup(node);
            return .{ .node = node, .token = entry.key_ptr.* };
        }
    }
    return null;
}

/// True iff the type's only methods are the HashMap-context
/// shape (`hash` and `eql`).  Such types are comparison keys —
/// fields hold VALUES (often FDs, IDs, etc.) used for hashing/
/// equality, not owned allocations.  Common in Bun's hashmap
/// adapters.
fn isHashContextType(ti: *const file_model.TypeInfo) bool {
    if (ti.methods.len == 0) return false;
    var saw_hash = false;
    var saw_eql = false;
    for (ti.methods) |m| {
        if (std.mem.eql(u8, m.name, "hash")) {
            saw_hash = true;
        } else if (std.mem.eql(u8, m.name, "eql")) {
            saw_eql = true;
        } else {
            return false;
        }
    }
    return saw_hash and saw_eql;
}

/// True iff the type's body declares a `pub const <Name> =
/// bun.LinearFifo(<Self>, ...)` / `bun.UnboundedQueue(<Self>, ...)`
/// — strong signal the type is an entry in an external queue.
/// The queue's container manages the entries' lifecycles; the
/// entry doesn't need its own deinit.
fn typeIsQueueEntry(tree: *const Ast, ti: *const file_model.TypeInfo) bool {
    const tags = tree.tokens.items(.tag);
    if (ti.body_first >= ti.body_last) return false;
    var t: Ast.TokenIndex = ti.body_first;
    while (t + 4 < ti.body_last) : (t += 1) {
        // Match `[pub] const <id> = bun . <CallName> (`.
        var k: Ast.TokenIndex = t;
        if (tags[k] == .keyword_pub) k += 1;
        if (tags[k] != .keyword_const) continue;
        if (tags[k + 1] != .identifier) continue;
        if (tags[k + 2] != .equal) continue;
        // RHS shape: identifier `bun`, `.`, identifier (call name), `(`.
        const r: Ast.TokenIndex = k + 3;
        if (r + 4 > ti.body_last) continue;
        if (tags[r] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(r), "bun")) continue;
        if (tags[r + 1] != .period) continue;
        if (tags[r + 2] != .identifier) continue;
        const fname = tree.tokenSlice(r + 2);
        if (!std.mem.eql(u8, fname, "LinearFifo") and
            !std.mem.eql(u8, fname, "UnboundedQueue") and
            !std.mem.eql(u8, fname, "FIFO") and
            !std.mem.eql(u8, fname, "Fifo")) continue;
        if (tags[r + 3] != .l_paren) continue;
        return true;
    }
    return false;
}

/// True iff the type has a `next: ?*Self` (or `next: ?*<TypeName>` /
/// `prev: ?*Self`) field — strong signal that the type is a node
/// in an intrusive linked list / queue.  The container's deinit
/// walks the chain and frees the entries; the node type doesn't
/// need its own deinit.  Skip the rule for such nodes.
fn isLinkedListNode(tree: *const Ast, ti: *const file_model.TypeInfo) bool {
    const tags = tree.tokens.items(.tag);
    for (ti.fields) |f| {
        if (!std.mem.eql(u8, f.name, "next") and
            !std.mem.eql(u8, f.name, "prev")) continue;
        // Type must be `?*<Self|TypeName>`.
        const t = f.type_first;
        if (t > f.type_last) continue;
        if (tags[t] != .question_mark) continue;
        if (t + 1 > f.type_last) continue;
        if (tags[t + 1] != .asterisk) continue;
        if (t + 2 > f.type_last) continue;
        if (tags[t + 2] != .identifier) continue;
        const tname = tree.tokenSlice(t + 2);
        if (std.mem.eql(u8, tname, "Self") or
            std.mem.eql(u8, tname, ti.name)) return true;
    }
    return false;
}

/// True iff:
///   - the field's declared type is a tagged union,
///   - the field's default value is a non-owned variant,
///   - no `<recv>.<field> = .{ .<owned_variant> = ... };` or
///     `<recv>.<field> = .<owned_variant>;` assignment appears
///     anywhere in this file (other writes use non-owned variants
///     or sentinels).
///
/// When all three hold, the field never holds an owned payload
/// at runtime — a missing outer cleanup can't leak.  Catches the
/// canonical "optional config: TaggedUnion = .none" pattern
/// where the owned variant is only set by code in a DIFFERENT
/// file that owns the value via other means.
/// TypeInfo-anchored variant of `fieldDefaultUnionTag`.  Bypasses
/// the `findType(name)` lookup that would land on the wrong
/// nested-type collision (e.g. `Writable.Pending` vs
/// `Result.Pending` — same name, different fields).  Caller
/// passes the resolved outer TypeInfo directly.
fn fieldDefaultUnionTagTi(
    tree: *const Ast,
    outer: *const file_model.TypeInfo,
    field: *const file_model.FieldInfo,
) ?[]const u8 {
    _ = outer;
    if (!field.has_default) return null;
    const tags = tree.tokens.items(.tag);
    var eq: Ast.TokenIndex = field.type_last + 1;
    while (eq < tags.len and tags[eq] != .equal) : (eq += 1) {}
    if (eq + 1 >= tags.len) return null;
    const dv = eq + 1;
    // Bare `. <tag>` not followed by `{` / `(` / `.`.
    if (dv + 1 < tags.len and tags[dv] == .period and tags[dv + 1] == .identifier) {
        const next = dv + 2;
        if (next < tags.len) {
            switch (tags[next]) {
                .l_brace, .l_paren, .period => {},
                else => return tree.tokenSlice(dv + 1),
            }
        } else return tree.tokenSlice(dv + 1);
    }
    // Struct-init form: `. { . <tag> = ... }`.
    if (dv + 3 < tags.len and
        tags[dv] == .period and
        tags[dv + 1] == .l_brace and
        tags[dv + 2] == .period and
        tags[dv + 3] == .identifier)
    {
        return tree.tokenSlice(dv + 3);
    }
    return null;
}

fn fieldStaysNonOwnedAcrossFile(
    tree: *const Ast,
    model: *const file_model.FileModel,
    outer: *const file_model.TypeInfo,
    field: *const file_model.FieldInfo,
    inner_ti: *const file_model.TypeInfo,
) bool {
    if (!model.isTaggedUnion(inner_ti.qualified_name)) return false;
    // Field default must be a non-owned variant tag.  Use the
    // outer TypeInfo DIRECTLY (not by name) to avoid the
    // findType collision when multiple types in the file share
    // a name (`Writable.Pending` vs `Result.Pending`).
    const default_tag = fieldDefaultUnionTagTi(tree, outer, field) orelse return false;
    const default_owned = model.unionVariantIsOwnedTi(inner_ti, default_tag) orelse return false;
    if (default_owned) return false;
    // Scan the WHOLE FILE for assignments to `<recv>.<field_name>`.
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = 0;
    while (t + 5 < tree.tokens.len) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), field.name)) continue;
        if (tags[t + 3] != .equal) continue;
        // Get the RHS variant tag — accept `.{ .<tag> = ... }` and
        // `.<tag>` forms.
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] == .identifier) {
            // Form: `<recv>.<field> = .<tag>;` — bare variant.
            const tag_name = tree.tokenSlice(t + 5);
            if (model.unionVariantIsOwnedTi(inner_ti, tag_name) orelse true) return false;
            continue;
        }
        if (t + 7 < tree.tokens.len and
            tags[t + 4] == .period and
            tags[t + 5] == .l_brace and
            tags[t + 6] == .period and
            tags[t + 7] == .identifier)
        {
            const tag_name = tree.tokenSlice(t + 7);
            if (model.unionVariantIsOwnedTi(inner_ti, tag_name) orelse true) return false;
            continue;
        }
        // Unknown RHS shape (call, identifier) — assume owned.
        return false;
    }
    return true;
}

/// True iff `ti` is a tagged union (`union(enum)`) AND every
/// variant's payload is non-owned — empty (`.pending,`) or
/// primitive (`.kind: u32`).  Dropping the field never leaks
/// regardless of the variant held, so a missing inline cleanup
/// on the outer is harmless.  Uses model.unionVariantIsOwned per
/// variant; bails on the first owned variant found.
fn allUnionVariantsNonOwned(model: *const file_model.FileModel, ti: *const file_model.TypeInfo) bool {
    if (!model.isTaggedUnion(ti.qualified_name)) return false;
    const tree = model.tree;
    const tags = tree.tokens.items(.tag);
    // Walk variant identifiers between `{` and `}`.
    var t = ti.body_first + 1;
    while (t < ti.body_last) : (t += 1) {
        // Skip past method / const decls.
        if (tags[t] == .keyword_fn or tags[t] == .keyword_pub or
            tags[t] == .keyword_const or tags[t] == .keyword_var)
        {
            t = skipPastDecl(tags, t, ti.body_last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        const name = tree.tokenSlice(t);
        if (model.unionVariantIsOwned(ti.qualified_name, name)) |is_owned| {
            if (is_owned) return false;
        }
        // Skip past this variant's payload (if any) to the comma.
        const after = t + 1;
        if (after < ti.body_last and tags[after] == .colon) {
            t = skipToNextComma(tags, after + 1, ti.body_last);
        } else if (after < ti.body_last and tags[after] == .comma) {
            // empty variant — t will increment past comma on next iter
        }
    }
    return true;
}

fn skipPastDecl(tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, last: Ast.TokenIndex) Ast.TokenIndex {
    var t = start;
    var brace: i32 = 0;
    var paren: i32 = 0;
    while (t < last) : (t += 1) {
        switch (tags[t]) {
            .l_brace => brace += 1,
            .r_brace => {
                brace -= 1;
                if (brace == 0 and paren == 0) return t;
            },
            .l_paren => paren += 1,
            .r_paren => paren -= 1,
            .semicolon => if (brace == 0 and paren == 0) return t,
            else => {},
        }
    }
    return last;
}

fn skipToNextComma(tags: []const std.zig.Token.Tag, start: Ast.TokenIndex, last: Ast.TokenIndex) Ast.TokenIndex {
    var t = start;
    var pd: i32 = 0;
    while (t < last) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket, .l_brace => pd += 1,
            .r_paren, .r_bracket, .r_brace => pd -= 1,
            .comma => if (pd == 0) return t,
            else => {},
        }
    }
    return last;
}

/// True iff the type has an `init` / `create` / `new` method whose
/// return type is `*Self` (after stripping `!` and `?`).  Pointer-
/// returning constructors mark the type as heap-allocated and
/// owned by an external caller — common in Bun's JSC bridge
/// (`globalThis.allocator().create(@This())`).  The outer's
/// missing inline cleanup isn't a leak because the owning caller
/// is responsible for teardown.
fn hasPointerReturningInit(tree: *const Ast, ti: *const file_model.TypeInfo) bool {
    const tags = tree.tokens.items(.tag);
    for (ti.methods) |m| {
        if (!std.mem.eql(u8, m.name, "init") and
            !std.mem.eql(u8, m.name, "create") and
            !std.mem.eql(u8, m.name, "new") and
            !std.mem.eql(u8, m.name, "start")) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buf, m.fn_decl) orelse continue;
        const rt = proto.ast.return_type.unwrap() orelse continue;
        const first = tree.firstToken(rt);
        if (tags[first] == .asterisk) return true;
        // `?*T`: `?` then `*` next.
        if (tags[first] == .question_mark and first + 1 < tree.tokens.len and tags[first + 1] == .asterisk) return true;
    }
    return false;
}

/// True iff the type body declares a `pub const new = ...` (or
/// `const new = ...`) initializer that names a heap-factory call —
/// `bun.TrivialNew(T)` / `bun.New(T)`.  Bun convention: such types
/// are heap-allocated and owned by a parent struct that's
/// responsible for cleanup, so a missing inline `deinit` on `T`
/// isn't a leak.  Token-scan over the type body for the prefix.
/// True iff `outer` is a NESTED type (declared inside another
/// type's body) AND the enclosing parent has a cleanup method.
/// Parent-owns-children pattern — the parent's deinit is
/// responsible for tearing down nested-type instances; a
/// missing inline cleanup on the nested type is harmless.
fn outerIsNestedInsideCleanupType(
    model: *const file_model.FileModel,
    outer: *const file_model.TypeInfo,
) bool {
    const parent_idx = outer.parent orelse return false;
    if (parent_idx >= model.types.len) return false;
    const parent_ti = &model.types[parent_idx];
    return parent_ti.hasMethod("deinit") or
        parent_ti.hasMethod("destroy") or
        parent_ti.hasMethod("finalize") or
        parent_ti.hasMethod("close") or
        parent_ti.hasMethod("free");
}

/// True iff the type has an `init` / `create` / `from*` method
/// that takes a parameter of the same name as `field_name` —
/// evidence that the field is initialised from a caller-supplied
/// value (BORROWED in, not owned by this struct).  Same heuristic
/// as the composed-owner rule.
fn fieldIsCallerSupplied(
    tree: *const Ast,
    outer: *const file_model.TypeInfo,
    field_name: []const u8,
) bool {
    for (outer.methods) |m| {
        const is_constructor = std.mem.eql(u8, m.name, "init") or
            std.mem.eql(u8, m.name, "create") or
            std.mem.startsWith(u8, m.name, "from") or
            std.mem.eql(u8, m.name, "new") or
            std.mem.eql(u8, m.name, "start") or
            std.mem.eql(u8, m.name, "setup");
        if (!is_constructor) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buf, m.fn_decl) orelse continue;
        var it = proto.iterate(tree);
        while (it.next()) |p| {
            const name_tok = p.name_token orelse continue;
            const name = tree.tokenSlice(name_tok);
            if (std.mem.eql(u8, name, field_name)) return true;
        }
    }
    return false;
}

fn hasNewFactoryDecl(tree: *const Ast, ti: *const file_model.TypeInfo) bool {
    const tags = tree.tokens.items(.tag);
    if (ti.body_first >= ti.body_last) return false;
    var t: Ast.TokenIndex = ti.body_first;
    while (t + 4 < ti.body_last) : (t += 1) {
        // Match `[pub] const new =`.
        var k: Ast.TokenIndex = t;
        if (tags[k] == .keyword_pub) k += 1;
        if (tags[k] != .keyword_const) continue;
        if (tags[k + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k + 1), "new")) continue;
        if (tags[k + 2] != .equal) continue;
        // RHS must be a call expression — common factory shapes:
        // `bun.TrivialNew(T)`, `bun.New(T)`.  Look at next few
        // tokens for an identifier (or `bun.<id>`) followed by `(`.
        var r: Ast.TokenIndex = k + 3;
        while (r < ti.body_last and (tags[r] == .identifier or tags[r] == .period)) : (r += 1) {}
        if (r < ti.body_last and tags[r] == .l_paren) return true;
    }
    return false;
}

/// True iff the outer struct has a field whose type/name looks
/// like an allocator handle the outer could pass to inner cleanup
/// methods.  Heuristic via name (`allocator` / `alloc`) — the
/// CSS-value-type cluster names theirs differently, so we miss a
/// few, but the false-negative direction is preferred over
/// false-firing.
fn outerHasAllocatorField(tree: *const Ast, ti: *const file_model.TypeInfo) bool {
    for (ti.fields) |f| {
        if (std.mem.eql(u8, f.name, "allocator") or
            std.mem.eql(u8, f.name, "alloc") or
            std.mem.eql(u8, f.name, "gpa") or
            std.mem.eql(u8, f.name, "arena")) return true;
        // Or by type name: field type ends with `Allocator` /
        // `ArenaAllocator`.
        const tags = tree.tokens.items(.tag);
        var t = f.type_first;
        var last_id: ?[]const u8 = null;
        while (t <= f.type_last) : (t += 1) {
            if (tags[t] == .identifier) last_id = tree.tokenSlice(t);
        }
        if (last_id) |n| {
            if (std.mem.endsWith(u8, n, "Allocator") or
                std.mem.endsWith(u8, n, "Arena")) return true;
        }
    }
    return false;
}

/// True iff EVERY cleanup-named method on `ti` requires more
/// parameters than just the receiver — i.e. there's no inline
/// `deinit(self)` shape, only `deinit(self, allocator)` /
/// `deinit(self, ctx)` / etc.  The outer struct can't pass that
/// extra arg without holding it — so a missing inline cleanup on
/// the outer is consistent with the cleanup being a caller's
/// responsibility, not the outer's.
fn allCleanupMethodsNeedExtraArg(tree: *const Ast, ti: *const file_model.TypeInfo) bool {
    if (ti.methods.len == 0) return false;
    var saw_cleanup = false;
    for (ti.methods) |m| {
        if (!isCleanupName(m.name)) continue;
        saw_cleanup = true;
        if (cleanupTakesOnlySelf(tree, m)) return false;
    }
    return saw_cleanup;
}

/// True iff the method's prototype has exactly one parameter (the
/// receiver).  Used to detect `pub fn deinit(self: *T) void` vs
/// `pub fn deinit(self: *T, alloc: Allocator) void`.
fn cleanupTakesOnlySelf(tree: *const Ast, m: file_model.MethodInfo) bool {
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&buf, m.fn_decl) orelse return false;
    var it = proto.iterate(tree);
    var count: u32 = 0;
    while (it.next()) |_| count += 1;
    return count == 1;
}

/// True iff `ti` has at least one cleanup-named method whose body is
/// non-trivial — i.e. contains something other than `_ = <expr>;`
/// discards.  An empty `{}` or all-discards body means the method
/// does nothing on drop, so a missing outer cleanup is harmless.
const anyNonTrivialCleanup = mq.anyNonTrivialCleanup;

/// A by-value token that only resets borrowed boolean flags has no owned
/// resource to drop. Prove this narrow body shape; calls, arithmetic updates,
/// pointer receivers, and unresolved field types retain the cleanup obligation.
fn cleanupOnlyClearsBorrowedFlags(
    tree: *const Ast,
    model: *const file_model.FileModel,
    ti: *const file_model.TypeInfo,
) bool {
    const tags = tree.tokens.items(.tag);
    // No embedded aggregate, slice, opaque pointer, or unresolved storage.
    for (ti.fields) |*field| {
        if (isPlainScalarField(tree, field, false)) continue;
        if (field.type_last != field.type_first + 1 or
            tags[field.type_first] != .asterisk or tags[field.type_last] != .identifier) return false;
        const state = model.findTypeInScope(tree.tokenSlice(field.type_last), ti) orelse return false;
        if (state.kind != .struct_) return false;
        for (state.fields) |*scalar| if (!isPlainScalarField(tree, scalar, false)) return false;
    }
    var saw_reset = false;
    for (ti.methods) |m| {
        if (!isCleanupName(m.name)) continue;
        if (tokens.isTrivialBody(tree, m.body_first, m.body_last)) continue;
        const receiver = m.receiver orelse return false;
        if (receiver.is_ptr or !cleanupTakesOnlySelf(tree, m)) return false;
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buf, m.fn_decl) orelse return false;
        const rt = proto.ast.return_type.unwrap() orelse return false;
        if (!std.mem.eql(u8, tree.getNodeSource(rt), "void")) return false;
        var t = m.body_first + 1;
        while (t < m.body_last) {
            if (tags[t] == .keyword_if) {
                if (tags[t + 1] != .l_paren) return false;
                const close = tokens.matchParen(tags, t + 1, m.body_last) orelse return false;
                var c = t + 2;
                while (c < close) {
                    if (tags[c] == .identifier) {
                        const text = tree.tokenSlice(c);
                        if (std.mem.eql(u8, text, "true") or std.mem.eql(u8, text, "false")) {
                            c += 1;
                        } else {
                            c = borrowedScalarPathEnd(tree, model, ti, receiver.name, c, close, false) orelse return false;
                        }
                    } else switch (tags[c]) {
                        .bang,
                        .bang_equal,
                        .equal_equal,
                        .angle_bracket_left,
                        .angle_bracket_right,
                        .angle_bracket_left_equal,
                        .angle_bracket_right_equal,
                        .keyword_and,
                        .keyword_or,
                        .number_literal,
                        => c += 1,
                        else => return false,
                    }
                }
                if (close + 2 >= m.body_last or tags[close + 1] != .keyword_return or
                    tags[close + 2] != .semicolon) return false;
                t = close + 3;
                continue;
            }
            const end = borrowedScalarPathEnd(tree, model, ti, receiver.name, t, m.body_last, true) orelse return false;
            if (end + 2 >= m.body_last or tags[end] != .equal or
                tags[end + 1] != .identifier or !std.mem.eql(u8, tree.tokenSlice(end + 1), "false") or
                tags[end + 2] != .semicolon) return false;
            saw_reset = true;
            t = end + 3;
        }
    }
    return saw_reset;
}

/// Resolve `receiver.scalar` reads and `receiver.pointer.scalar` reads/resets.
/// Only a direct pointer to a same-file type is accepted, never an alias or
/// unresolved resource type. Writes must target a boolean in borrowed storage.
fn borrowedScalarPathEnd(
    tree: *const Ast,
    model: *const file_model.FileModel,
    ti: *const file_model.TypeInfo,
    receiver: []const u8,
    start: Ast.TokenIndex,
    limit: Ast.TokenIndex,
    writing: bool,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (start + 2 >= limit or tags[start] != .identifier or
        !std.mem.eql(u8, tree.tokenSlice(start), receiver) or
        tags[start + 1] != .period or tags[start + 2] != .identifier) return null;
    const field = ti.findField(tree.tokenSlice(start + 2)) orelse return null;
    if (start + 3 >= limit or tags[start + 3] != .period) {
        if (writing or !isPlainScalarField(tree, field, false)) return null;
        return start + 3;
    }
    if (start + 4 >= limit or tags[start + 4] != .identifier or
        field.type_last != field.type_first + 1 or
        tags[field.type_first] != .asterisk or tags[field.type_last] != .identifier) return null;
    const pointee = model.findTypeInScope(tree.tokenSlice(field.type_last), ti) orelse return null;
    const scalar = pointee.findField(tree.tokenSlice(start + 4)) orelse return null;
    if (!isPlainScalarField(tree, scalar, writing)) return null;
    return start + 5;
}

fn isPlainScalarField(tree: *const Ast, field: *const file_model.FieldInfo, bool_only: bool) bool {
    if (field.type_first != field.type_last) return false;
    const name = tree.tokenSlice(field.type_first);
    if (std.mem.eql(u8, name, "bool")) return true;
    if (bool_only) return false;
    if (std.mem.eql(u8, name, "usize") or std.mem.eql(u8, name, "isize")) return true;
    if (name.len < 2 or (name[0] != 'u' and name[0] != 'i')) return false;
    for (name[1..]) |ch| if (!std.ascii.isDigit(ch)) return false;
    return true;
}

const isCleanupName = method_names.isCleanupMethodName;

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(problem.Problem),
    tree: *const Ast,
    outer_name: []const u8,
    field_tok: Ast.TokenIndex,
    field_name: []const u8,
    type_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s}: {s}` owns a resource (`{s}` exposes `deinit`/`close`/etc.), but `{s}` itself has no cleanup method — dropping a `{s}` value silently leaks the inner's file handle / socket / ref / mmap.  Add `pub fn deinit(self: *{s}) void {{ self.{s}.deinit(); }}` (or equivalent)",
        .{ outer_name, field_name, type_name, type_name, outer_name, outer_name, outer_name, field_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try problem.Pos.fromTokenStart(tree, field_tok),
        .end = try problem.Pos.fromTokenEnd(tree, field_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "outer has no deinit + owned field fires" {
    try testing.expectFires(check, R,
        \\const Inner = struct {
        \\    fd: i32 = 0,
        \\    pub fn deinit(self: *Inner) void { self.fd = -1; }
        \\};
        \\const Outer = struct {
        \\    inner: Inner,
        \\};
    );
}

test "outer has deinit (composed-owner covers it) — no fire" {
    try testing.expectNoFire(check,
        \\const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\const Outer = struct {
        \\    inner: Inner,
        \\    pub fn deinit(self: *Outer) void { _ = self; }
        \\};
    );
}

test "outer has close (alternate cleanup) — no fire" {
    try testing.expectNoFire(check,
        \\const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\const Outer = struct {
        \\    inner: Inner,
        \\    pub fn close(self: *Outer) void { _ = self; }
        \\};
    );
}

test "field type has no cleanup method — no fire" {
    try testing.expectNoFire(check,
        \\const Plain = struct { x: u32 };
        \\const Outer = struct {
        \\    p: Plain,
        \\};
    );
}

test "pointer field (likely borrow) — no fire" {
    try testing.expectNoFire(check,
        \\const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\const Outer = struct {
        \\    inner: *Inner,
        \\};
    );
}

test "optional value field (?Inner) fires" {
    try testing.expectFires(check, R,
        \\const Inner = struct {
        \\    fd: i32 = 0,
        \\    pub fn deinit(self: *Inner) void { self.fd = -1; }
        \\};
        \\const Outer = struct {
        \\    inner: ?Inner,
        \\};
    );
}

test "multiple owned fields fires once (not per-field)" {
    try testing.expectFires(check, R,
        \\const Inner = struct {
        \\    fd: i32 = 0,
        \\    pub fn deinit(self: *Inner) void { self.fd = -1; }
        \\};
        \\const Outer = struct {
        \\    a: Inner,
        \\    b: Inner,
        \\    c: Inner,
        \\};
    );
}

test "Inner with finalize/dispose also counts as cleanup" {
    try testing.expectFires(check, R,
        \\const Inner = struct {
        \\    fd: i32 = 0,
        \\    pub fn dispose(self: *Inner) void { self.fd = -1; }
        \\};
        \\const Outer = struct {
        \\    inner: Inner,
        \\};
    );
}

test "Inner with empty deinit body (no-op trait conformance) — no fire" {
    // Common for CSS/value-type uniform-API conformance: deinit
    // exists for trait-method-call uniformity but does nothing.
    // Missing outer deinit doesn't leak anything.
    try testing.expectNoFire(check,
        \\const Inner = struct {
        \\    pub fn deinit(_: *Inner, _: Allocator) void {}
        \\};
        \\const Allocator = struct {};
        \\const Outer = struct {
        \\    inner: Inner,
        \\};
    );
}

test "Inner with discard-only deinit body — no fire" {
    // `pub fn deinit(self: *T) void { _ = self; }` — placeholder
    // pattern.  Same as empty body: does nothing on drop.
    try testing.expectNoFire(check,
        \\const Inner = struct {
        \\    pub fn deinit(self: *Inner) void { _ = self; }
        \\};
        \\const Outer = struct {
        \\    inner: Inner,
        \\};
    );
}

test "borrowed value cleanup only clears external boolean state — no fire" {
    try testing.expectNoFire(check,
        \\const State = struct { active: bool = false, claimed: bool = false, generation: u64 = 0 };
        \\const Lease = struct {
        \\    state: *State,
        \\    generation: u64,
        \\    fn release(self: Lease) void {
        \\        if (!self.state.active) return;
        \\        if (self.state.generation != self.generation) return;
        \\        self.state.active = false;
        \\        self.state.claimed = false;
        \\    }
        \\};
        \\const Guard = struct { lease: Lease, expected_position: usize = 0 };
    );
}

test "borrowed pointer cleanup decrements a reference — fires" {
    try testing.expectFires(check, R,
        \\const State = struct { refs: usize = 1, active: bool = true };
        \\const Lease = struct {
        \\    state: *State,
        \\    fn release(self: Lease) void {
        \\        self.state.active = false;
        \\        self.state.refs -= 1;
        \\    }
        \\};
        \\const Guard = struct { lease: Lease };
    );
}

test "borrowed pointer cleanup calls unresolved resource release — fires" {
    try testing.expectFires(check, R,
        \\const State = struct { active: bool = true };
        \\const Lease = struct {
        \\    state: *State,
        \\    fn release(self: Lease) void {
        \\        self.state.active = false;
        \\        releaseResource(self.state);
        \\    }
        \\};
        \\const Guard = struct { lease: Lease };
    );
}

test "boolean cleanup with unresolved pointee stays conservative — fires" {
    try testing.expectFires(check, R,
        \\const Lease = struct {
        \\    state: *ExternalState,
        \\    fn release(self: Lease) void { self.state.active = false; }
        \\};
        \\const Guard = struct { lease: Lease };
    );
}

test "boolean cleanup does not hide embedded resource storage — fires" {
    try testing.expectFires(check, R,
        \\const State = struct { active: bool = true };
        \\const Lease = struct {
        \\    state: *State,
        \\    bytes: []u8,
        \\    fn release(self: Lease) void { self.state.active = false; }
        \\};
        \\const Guard = struct { lease: Lease };
    );
}

// Selected replay rows: ocean 78,220,384,699,859,1226,1228,1488,
// 1548,1549,1762,1854,1858; nogui 106,124,138,159,175,221.
// These exercise owner-specific entry points, non-owning destructors and
// borrowed copies, rather than accepting a cleanup-like spelling.
test "owner cleanup census uses the declared field and exact owner" {
    try testing.expectNoFireTyped(check,
        \\const Resource = struct {
        \\    fd: i32,
        \\    fn close(self: *Resource) void { self.fd = -1; }
        \\};
        \\const Carrier = struct { resource: Resource };
        \\fn retire(carrier: *Carrier) void { carrier.resource.close(); }
        \\pub fn run(carrier: *Carrier) void { retire(carrier); }
    );
    try testing.expectFiresTyped(check, R,
        \\const Resource = struct {
        \\    fd: i32,
        \\    fn close(self: *Resource) void { self.fd = -1; }
        \\};
        \\const Carrier = struct { resource: Resource };
        \\const Other = struct { resource: Resource };
        \\fn retire(other: *Other) void { other.resource.close(); }
        \\pub fn run(carrier: *Carrier, other: *Other) void { _ = carrier; retire(other); }
    );
}

test "owner cleanup census recognizes nonstandard self methods without name credit" {
    try testing.expectNoFireTyped(check,
        \\const Resource = struct {
        \\    fd: i32,
        \\    fn close(self: *Resource) void { self.fd = -1; }
        \\};
        \\const Carrier = struct {
        \\    resource: Resource,
        \\    fn finish(self: *Carrier) void { self.resource.close(); }
        \\};
        \\pub fn run(carrier: *Carrier) void { carrier.finish(); }
    );
    try testing.expectFiresTyped(check, R,
        \\const Resource = struct {
        \\    fd: i32,
        \\    fn close(self: *Resource) void { self.fd = -1; }
        \\};
        \\const Carrier = struct {
        \\    resource: Resource,
        \\    fn finish(self: *Carrier) void { inspect(self.resource); }
        \\};
        \\pub fn run(carrier: *Carrier) void { carrier.finish(); }
    );
}

test "owner cleanup census excludes allocator callbacks and reset-only views" {
    try testing.expectNoFireTyped(check,
        \\const Accounting = struct {
        \\    fn free(ctx: *anyopaque, bytes: []u8) void { consume(ctx, bytes); }
        \\};
        \\const View = struct {
        \\    token: usize,
        \\    fn deinit(self: *View) void { self.* = undefined; }
        \\};
        \\const Carrier = struct { accounting: Accounting, view: View };
        \\pub fn run(carrier: *Carrier) void { _ = carrier; }
    );
}

test "owner cleanup census keeps partial resource cleanup" {
    try testing.expectFiresTyped(check, R,
        \\const Resource = struct {
        \\    first: i32, second: i32,
        \\    fn close(self: *Resource) void { self.first = -1; self.second = -1; }
        \\};
        \\const Carrier = struct {
        \\    resource: Resource,
        \\    fn finish(self: *Carrier) void { self.resource.first = -1; }
        \\};
        \\pub fn run(carrier: *Carrier) void { carrier.finish(); }
    );
}

test "owner cleanup census distinguishes complete inline destruction from a subset" {
    try testing.expectNoFireTyped(check,
        \\const Buffer = struct {
        \\    fd: i32,
        \\    fn release(self: *Buffer) void { self.fd = -1; }
        \\};
        \\const Field = struct {
        \\    text: Buffer,
        \\    fn deinit(self: *Field) void { self.text.release(); self.* = undefined; }
        \\};
        \\const Run = struct {
        \\    field: Field,
        \\    fn releaseReadback(self: *Run) void { self.field.text.release(); }
        \\};
        \\pub fn run(self: *Run) void { self.releaseReadback(); }
    );
    try testing.expectFiresTyped(check, R,
        \\const Buffer = struct {
        \\    fd: i32,
        \\    fn release(self: *Buffer) void { self.fd = -1; }
        \\};
        \\const Field = struct {
        \\    first: Buffer, second: Buffer,
        \\    fn deinit(self: *Field) void { self.first.release(); self.second.release(); self.* = undefined; }
        \\};
        \\const Run = struct {
        \\    field: Field,
        \\    fn releaseReadback(self: *Run) void { self.field.first.release(); }
        \\};
        \\pub fn run(self: *Run) void { self.releaseReadback(); }
    );
}

test "owner cleanup census closes only unused private nonreflective declarations" {
    try testing.expectNoFireTyped(check,
        \\const Resource = struct {
        \\    fd: i32,
        \\    fn close(self: *Resource) void { self.fd = -1; }
        \\};
        \\const Prepared = struct { resource: Resource };
    );
    try testing.expectFiresTyped(check, R,
        \\const Resource = struct {
        \\    fd: i32,
        \\    fn close(self: *Resource) void { self.fd = -1; }
        \\};
        \\pub const Prepared = struct { resource: Resource };
    );
}

test "owner cleanup census does not borrow error-only cleanup for normal exits" {
    try testing.expectFiresTyped(check, R,
        \\const Resource = struct {
        \\    fd: i32,
        \\    fn close(self: *Resource) void { self.fd = -1; }
        \\};
        \\const Carrier = struct { resource: Resource };
        \\pub fn run() !void {
        \\    var carrier: Carrier = .{ .resource = .{ .fd = 3 } };
        \\    errdefer carrier.resource.close();
        \\    try unknownStep();
        \\}
    );
}

test "owner cleanup census rejects whole-owner reset before destructor" {
    try testing.expectFiresTyped(check, R,
        \\const Resource = struct {
        \\    fd: i32,
        \\    fn close(self: *Resource) void { self.fd = -1; }
        \\};
        \\const Carrier = struct { resource: Resource };
        \\fn retire(carrier: *Carrier) void { carrier.* = undefined; carrier.resource.close(); }
        \\pub fn run(carrier: *Carrier) void { retire(carrier); }
    );
}
