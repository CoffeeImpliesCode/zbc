//! A struct has both `deinit` and `reset` methods.  `deinit` calls
//! release/free/destroy/close/deinit on owned handles (typically
//! pool slots or external resources).  `reset` either does nothing
//! for those handles or just zeroes the struct.  State is logically
//! "freed" after `reset` but the pool / sub-allocator still
//! considers slots held → leak.
//!
//! Real-world: tigerbeetle/tigerbeetle#3436 (`SegmentedArray.reset`
//! forgot to release pool nodes that `deinit` does release;
//! callers expected reset to free pool capacity) and
//! tigerbeetle/tigerbeetle#1734 (`scan_buffer_pool` — same shape).
//!
//! Detection (token-walk per file):
//!   1. Walk for `keyword_struct` followed by `{` to find struct
//!      bodies.
//!   2. Within each struct body, find `pub fn deinit(` and
//!      `pub fn reset(` decls.
//!   3. For each, collect the set of `<obj>.<cleanup>(` calls
//!      where cleanup ∈ {`release`, `free`, `destroy`, `close`,
//!      `deinit`, `unref`, `deref`}.
//!   4. If `deinit` calls any `<obj>.<cleanup>` that `reset`
//!      doesn't, fire on the `reset` fn name.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const type_query = @import("../../model/type_query.zig");
const std_type_query = @import("../../model/std_type_query.zig");
const testing = @import("../../testing.zig");
const matchBrace = tokens.matchBrace;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

/// Returns `SourceTooWide` if the source or token count exceeds the AST position domain.
pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .reset_skips_pooled_resource_release)) return;
    const model = try cache.fileModel();

    if (tree.source.len >= std.math.maxInt(u32)) return error.SourceTooWide;
    const tok_count = std.math.cast(u32, tree.tokens.len) orelse return error.SourceTooWide;
    const tags = tree.tokens.items(.tag);
    if (tok_count == 0) return;
    const last: Ast.TokenIndex = tok_count - 1;

    var t: Ast.TokenIndex = 0;
    while (t < last and last - t > 1) : (t += 1) {
        if (tags[t] != .keyword_struct) continue;
        if (tags[t + 1] != .l_brace) continue;
        const body_start = t + 1;
        const body_end = matchBrace(tags, body_start, last) orelse continue;
        try checkStruct(gpa, tree, cache, model, body_start + 1, body_end - 1, problems);
        t = body_end;
    }
}

const FnInfo = struct {
    name_tok: Ast.TokenIndex,
    body_start: Ast.TokenIndex,
    body_end: Ast.TokenIndex,
};

fn checkStruct(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    model: *const @import("../../model/file_model.zig").FileModel,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    var deinit_fn: ?FnInfo = null;
    var reset_fn: ?FnInfo = null;

    // Cross-fn analysis input: bodies of all non-lifecycle methods
    // (everything that isn't init/deinit/reset/clear).  If one of
    // these methods re-acquires the resource, then it's per-cycle
    // and reset MUST release.  If no non-lifecycle method touches
    // the resource, the resource is pool-lifetime and reset's
    // omission is intentional.
    var other_fns: std.ArrayListUnmanaged(FnInfo) = .empty;
    defer other_fns.deinit(gpa);

    var t: Ast.TokenIndex = start;
    while (t <= end and end - t >= 2) : (t += 1) {
        if (tags[t] == .l_brace) {
            t = matchBrace(tags, t, end) orelse break;
            continue;
        }
        if (tags[t] != .keyword_fn) continue;
        if (tags[t + 1] != .identifier) continue;
        const name = tree.tokenSlice(t + 1);
        const is_deinit = std.mem.eql(u8, name, "deinit");
        const is_reset = std.mem.eql(u8, name, "reset");
        const is_init = std.mem.eql(u8, name, "init");
        const is_clear = std.mem.eql(u8, name, "clear") or
            std.mem.eql(u8, name, "clearRetainingCapacity") or
            std.mem.eql(u8, name, "clearAndFree");
        // Find the body `{` for this fn.
        var u: Ast.TokenIndex = t + 2;
        while (u <= end and tags[u] != .l_brace) : (u += 1) {}
        if (u > end) break;
        const fn_body_end = matchBrace(tags, u, end) orelse break;
        const info: FnInfo = .{
            .name_tok = t + 1,
            .body_start = u + 1,
            .body_end = fn_body_end - 1,
        };
        if (is_deinit and deinit_fn == null) deinit_fn = info;
        if (is_reset and reset_fn == null) reset_fn = info;
        if (!is_deinit and !is_reset and !is_init and !is_clear) {
            try other_fns.append(gpa, info);
        }
        t = fn_body_end;
    }

    if (deinit_fn == null or reset_fn == null) return;

    var deinit_cleanups: std.ArrayListUnmanaged(Cleanup) = .empty;
    defer deinit_cleanups.deinit(gpa);
    try collectCleanups(gpa, tree, deinit_fn.?.body_start, deinit_fn.?.body_end, &deinit_cleanups);

    var reset_cleanups: std.ArrayListUnmanaged(Cleanup) = .empty;
    defer reset_cleanups.deinit(gpa);
    try collectCleanups(gpa, tree, reset_fn.?.body_start, reset_fn.?.body_end, &reset_cleanups);

    // Find cleanups in deinit that aren't in reset.  Match by
    // RECEIVER only — `cache.deinit(alloc)` in deinit and
    // `cache.reset()` / `cache.clearRetainingCapacity()` in reset
    // both qualify as "cleanup on the same receiver".
    //
    // Suppression layers (semantic signals):
    //  (1) Receiver-matched cleanup in reset → suppress.
    //  (2) Reset is a PARTIAL CLEAR — it already does ≥1 cleanup
    //      but doesn't touch this receiver → suppress.  The author
    //      has demonstrated cleanup-awareness; receivers they
    //      didn't touch are intentionally persistent (e.g.,
    //      IncrementalGraph.reset clears current-chunk state but
    //      intentionally leaves graph state alone).
    //  (3) Cross-fn analysis — only run when reset is a MINIMAL
    //      reset (no cleanups at all).  If a non-lifecycle method
    //      re-acquires the receiver → per-cycle leak (fire).  If
    //      not → pool-lifetime (suppress).
    const reset_has_any_cleanup = reset_cleanups.items.len > 0;
    for (deinit_cleanups.items) |dc| {
        if (try cleanupOnlyReleasesBackingStorage(tree, cache, model, dc)) continue;
        var matched_in_reset = false;
        for (reset_cleanups.items) |rc| {
            if (std.mem.eql(u8, dc.recv, rc.recv)) {
                matched_in_reset = true;
                break;
            }
        }
        if (matched_in_reset) continue;
        // Layer 2: partial-clear suppression.  Reset has cleanup
        // logic but intentionally skipped this receiver — author
        // was aware of cleanup duties and chose to leave this
        // resource alone (canonical pattern: state-machine reset
        // clears current-cycle state, leaves persistent state).
        if (reset_has_any_cleanup) continue;
        // Layer 3: cross-fn analysis for minimal resets (no
        // cleanups at all).  If a non-lifecycle method re-acquires
        // the receiver → per-cycle leak (fire).  If not →
        // pool-lifetime (suppress).
        if (!receiverReacquiredElsewhere(tree, other_fns.items, dc.recv)) continue;
        try report(gpa, problems, tree, reset_fn.?.name_tok, dc);
    }
}

/// True iff some non-lifecycle method body contains a call
/// `<recv>.<acquire-method>(` matching the cleanup's receiver.
/// `<acquire-method>` allowlist: methods that conventionally take a
/// fresh ref / pool slot, paired with the cleanup-release methods.
fn receiverReacquiredElsewhere(
    tree: *const Ast,
    others: []const FnInfo,
    recv: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    for (others) |fn_info| {
        var t: Ast.TokenIndex = fn_info.body_start;
        while (t <= fn_info.body_end and fn_info.body_end - t >= 3) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
            if (tags[t + 1] != .period) continue;
            if (tags[t + 2] != .identifier) continue;
            if (tags[t + 3] != .l_paren) continue;
            const m = tree.tokenSlice(t + 2);
            if (isAcquireMethodName(m)) return true;
        }
    }
    return false;
}

fn isAcquireMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "acquire") or
        std.mem.eql(u8, name, "reference") or
        std.mem.eql(u8, name, "retain") or
        std.mem.eql(u8, name, "addRef") or
        std.mem.eql(u8, name, "addref") or
        std.mem.eql(u8, name, "ref") or
        std.mem.eql(u8, name, "take") or
        std.mem.eql(u8, name, "grab") or
        std.mem.eql(u8, name, "request") or
        std.mem.eql(u8, name, "alloc") or
        std.mem.eql(u8, name, "create") or
        std.mem.eql(u8, name, "init") or
        std.mem.eql(u8, name, "get_block") or
        std.mem.eql(u8, name, "get_node") or
        std.mem.eql(u8, name, "get_buffer") or
        std.mem.eql(u8, name, "append") or
        std.mem.eql(u8, name, "appendSlice");
}

const Cleanup = struct {
    recv: []const u8,
    method: []const u8,
    receiver_first: Ast.TokenIndex,
    receiver_last: Ast.TokenIndex,
    call_token: Ast.TokenIndex,
};

fn collectCleanups(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    out: *std.ArrayListUnmanaged(Cleanup),
) !void {
    const tags = tree.tokens.items(.tag);
    if (start > end) return;
    var t: Ast.TokenIndex = start;
    while (t <= end and end - t >= 3) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        const method = tree.tokenSlice(t + 2);
        if (!isCleanupMethodName(method)) continue;
        const recv = tree.tokenSlice(t);
        // Skip allocator-ish receivers — `alloc.free(self.nodes)`
        // in deinit is freeing the BACKING STORAGE, which `reset`
        // legitimately keeps (reset's whole point is to keep
        // capacity).  The bug shape this rule targets is missing
        // POOL-slot releases — external resources owned by a pool /
        // refcount helper, not the struct's own heap memory.
        if (isAllocatorishName(recv)) continue;
        // Dedup.
        var already = false;
        for (out.items) |c| {
            if (std.mem.eql(u8, c.recv, recv) and std.mem.eql(u8, c.method, method)) {
                already = true;
                break;
            }
        }
        if (!already) {
            var receiver_first = t;
            while (receiver_first >= 2 and tags[receiver_first - 1] == .period and tags[receiver_first - 2] == .identifier)
                receiver_first -= 2;
            try out.append(gpa, .{
                .recv = recv,
                .method = method,
                .receiver_first = receiver_first,
                .receiver_last = t,
                .call_token = t + 2,
            });
        }
    }
}

/// An address-free standard list owns only its backing allocation. Appending
/// observations does not acquire a pool slot that a logical reset must release.
/// Both the declaration and its element are proved; an opaque element or a
/// look-alike container is not an exemption.
fn cleanupOnlyReleasesBackingStorage(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    model: *const @import("../../model/file_model.zig").FileModel,
    cleanup: Cleanup,
) !bool {
    if (!std.mem.eql(u8, cleanup.method, "deinit")) return false;
    if (cleanup.receiver_first + 2 != cleanup.receiver_last) return false;
    const owner = blk: {
        for (model.types) |*candidate| {
            if (candidate.body_first < cleanup.call_token and candidate.body_last > cleanup.call_token)
                if (candidate.findField(cleanup.recv) != null) break :blk candidate;
        }
        return false;
    };
    const field = owner.findField(cleanup.recv) orelse return false;
    if (!std_type_query.isType(cache, tree, field.type_first, field.type_last, "", "ArrayList", .{ .allow_type_call = true }) and
        !std_type_query.isType(cache, tree, field.type_first, field.type_last, "", "ArrayListUnmanaged", .{ .allow_type_call = true }))
        return false;
    const element = type_query.elementTypeRef(cache, .{
        .tree = tree,
        .first = field.type_first,
        .last = field.type_last,
    }, 0) orelse return false;
    const resolver = cache.zls orelse return false;
    const element_node = cache.nodeForExactSpan(element.first, element.last) orelse return false;
    const frame = resolver.resolutionFrame();
    const element_type = (try frame.typeOfNode(element_node)) orelse return false;
    if (!try @import("../../cache/fresh_storage.zig").actualTypeAddressFree(frame, element_type, 0, null))
        return false;
    const callee = cache.nodeForExactSpan(cleanup.receiver_first, cleanup.call_token) orelse return false;
    const actual = (try cache.actualCallSummaryAt(tree.nodeMainToken(callee), null)) orelse return false;
    var argument_buffer: [2]Ast.Node.Index = undefined;
    const receiver = (try actual.callArgumentFor(cache, &argument_buffer, 0)) orelse return false;
    if (tree.firstToken(receiver) != cleanup.receiver_first or tree.lastToken(receiver) != cleanup.receiver_last)
        return false;
    if (!try standardListReleasesOnlyBacking(cache, actual)) return false;
    // The call must actually dispatch on that field, not on a same-spelled
    // parameter of some other object inside the method.
    var fn_buffer: [1]Ast.Node.Index = undefined;
    var functions = tokens.iterFnDecls(tree);
    while (functions.next(&fn_buffer)) |entry| {
        if (tree.firstToken(entry.body) >= cleanup.call_token or tree.lastToken(entry.body) <= cleanup.call_token) continue;
        const bindings = try cache.localBindings(entry.proto, entry.body);
        const root = bindings.findAt(tree.tokenSlice(cleanup.receiver_first), cleanup.call_token) orelse return false;
        if (root.origin != .param) return false;
        const name = tokens.typeNameFromTokens(tree, root.rhs_first, root.rhs_last) orelse return false;
        if (model.resolveTypeNameInScope(name, owner) != owner) return false;
        return true;
    }
    return false;
}

/// A selected-storage certificate, not a claim that allocator callbacks have
/// no global effects. Read every statement of the actual SDK destructor and
/// its actual slice projection in their instantiated source frames.
fn standardListReleasesOnlyBacking(
    cache: *file_cache_mod.FileCache,
    actual: file_cache_mod.FileCache.ActualCallSummary,
) !bool {
    const resolver = cache.zls orelse return false;
    if (!try resolver.declaredInToolchainFile(actual.callee.handle, "/std/array_list.zig")) return false;
    const declaring = (try actual.declaringCache(cache)) orelse return false;
    const tree = actual.callee.tree;
    const frame = resolver.frameForFunction(actual.callee.reference);
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, actual.callee.declaration) orelse return false;
    const self_name = declaring.paramNameFor(proto, 0) orelse return false;
    const allocator_name = declaring.paramNameFor(proto, 1) orelse return false;
    if (declaring.paramNameFor(proto, 2) != null) return false;
    const body = tokens.bodyOf(tree, actual.callee.declaration) orelse return false;
    var statement_buffer: [2]Ast.Node.Index = undefined;
    const statements = tree.blockStatements(&statement_buffer, body) orelse return false;
    if (statements.len != 2) return false;

    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    try cache.chargeNormalCleanupAt(tree, body);
    try cache.chargeNormalCleanupAt(tree, statements[0]);
    try cache.chargeNormalCleanupAt(tree, statements[1]);
    // The only operation after release clears the same list header.
    if (tree.nodeTag(statements[1]) != .assign) return false;
    const clear = tree.nodeData(statements[1]).node_and_node;
    if (tree.nodeTag(clear[0]) != .deref or
        !identifierIs(tree, tree.nodeData(clear[0]).node, self_name) or
        !identifierIs(tree, clear[1], "undefined")) return false;

    var call_buffer: [1]Ast.Node.Index = undefined;
    const release = tree.fullCall(&call_buffer, statements[0]) orelse return false;
    if (release.ast.params.len != 1 or tree.nodeTag(release.ast.fn_expr) != .field_access) return false;
    const release_access = tree.nodeData(release.ast.fn_expr).node_and_token;
    if (!identifierIs(tree, release_access[0], allocator_name)) return false;
    const release_actual = (try declaring.actualCallSummaryAt(tree.nodeMainToken(release.ast.fn_expr), frame)) orelse return false;
    if (!try resolver.declaredInToolchainFile(release_actual.callee.handle, "/std/mem/Allocator.zig")) return false;
    var release_proto_buffer: [1]Ast.Node.Index = undefined;
    const release_proto = tokens.fnProto(release_actual.callee.tree, &release_proto_buffer, release_actual.callee.declaration) orelse return false;
    if (!std.mem.eql(u8, release_actual.callee.tree.tokenSlice(release_proto.name_token orelse return false), "free")) return false;
    if ((try frame.isStdAllocator(release_access[0])) != true) return false;

    // The release argument must be the exact list's canonical projection.
    const projection_node = release.ast.params[0];
    try cache.chargeNormalCleanupAt(tree, projection_node);
    var projection_buffer: [1]Ast.Node.Index = undefined;
    const projection = tree.fullCall(&projection_buffer, projection_node) orelse return false;
    if (projection.ast.params.len != 0 or tree.nodeTag(projection.ast.fn_expr) != .field_access) return false;
    if (!identifierIs(tree, tree.nodeData(projection.ast.fn_expr).node_and_token[0], self_name)) return false;
    const projected = (try declaring.actualCallSummaryAt(tree.nodeMainToken(projection.ast.fn_expr), frame)) orelse return false;
    if (projected.callee.tree != tree) return false;
    const projection_cache = (try projected.declaringCache(cache)) orelse return false;
    const projection_tree = projected.callee.tree;
    var projection_proto_buffer: [1]Ast.Node.Index = undefined;
    const projection_proto = tokens.fnProto(projection_tree, &projection_proto_buffer, projected.callee.declaration) orelse return false;
    const projection_self = projection_cache.paramNameFor(projection_proto, 0) orelse return false;
    if (projection_cache.paramNameFor(projection_proto, 1) != null) return false;
    const projection_body = tokens.bodyOf(projection_tree, projected.callee.declaration) orelse return false;
    var returns_buffer: [2]Ast.Node.Index = undefined;
    const returns = projection_tree.blockStatements(&returns_buffer, projection_body) orelse return false;
    if (returns.len != 1 or projection_tree.nodeTag(returns[0]) != .@"return") return false;
    try cache.chargeNormalCleanupAt(projection_tree, projection_body);
    try cache.chargeNormalCleanupAt(projection_tree, returns[0]);
    const value = projection_tree.nodeData(returns[0]).opt_node.unwrap() orelse return false;
    const slice = projection_tree.fullSlice(value) orelse return false;
    if (slice.ast.sentinel != .none) return false;
    if (projection_tree.nodeTag(slice.ast.start) != .number_literal or
        !std.mem.eql(u8, projection_tree.tokenSlice(projection_tree.nodeMainToken(slice.ast.start)), "0")) return false;
    const end = slice.ast.end.unwrap() orelse return false;
    if (!fieldOfIdentifier(projection_tree, end, projection_self, "capacity")) return false;
    if (projection_tree.nodeTag(slice.ast.sliced) != .field_access) return false;
    const pointer = projection_tree.nodeData(slice.ast.sliced).node_and_token;
    if (!std.mem.eql(u8, projection_tree.tokenSlice(pointer[1]), "ptr") or
        !fieldOfIdentifier(projection_tree, pointer[0], projection_self, "items")) return false;
    const projection_frame = resolver.frameForFunction(projected.callee.reference);
    const slice_type = (try projection_frame.typeOfNode(value)) orelse return false;
    if (resolver.pointerSize(slice_type) != .slice) return false;
    return true;
}

fn identifierIs(tree: *const Ast, node: Ast.Node.Index, name: []const u8) bool {
    return tree.nodeTag(node) == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name);
}

fn fieldOfIdentifier(tree: *const Ast, node: Ast.Node.Index, root: []const u8, field: []const u8) bool {
    if (tree.nodeTag(node) != .field_access) return false;
    const access = tree.nodeData(node).node_and_token;
    return identifierIs(tree, access[0], root) and std.mem.eql(u8, tree.tokenSlice(access[1]), field);
}

const isAllocatorishName = method_names.isAllocatorishName;

fn isCleanupMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "release") or
        std.mem.eql(u8, name, "free") or
        std.mem.eql(u8, name, "destroy") or
        std.mem.eql(u8, name, "close") or
        std.mem.eql(u8, name, "deinit") or
        std.mem.eql(u8, name, "unref") or
        std.mem.eql(u8, name, "deref") or
        // Reset-side equivalents: receiver-matching against these
        // counts as "reset cleans up this resource."  Includes
        // common variants across std and project-specific naming
        // (`clearAndRetainCapacity` is Ghostty's variant).
        std.mem.eql(u8, name, "reset") or
        std.mem.eql(u8, name, "clear") or
        std.mem.eql(u8, name, "clearRetainingCapacity") or
        std.mem.eql(u8, name, "clearAndRetainCapacity") or
        std.mem.eql(u8, name, "clearAndFree") or
        std.mem.eql(u8, name, "shrinkRetainingCapacity") or
        std.mem.eql(u8, name, "shrinkAndFree");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    reset_name_tok: Ast.TokenIndex,
    missing: Cleanup,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`reset` is missing `{s}.{s}(...)` — `deinit` releases this resource but `reset` doesn't, so callers using `reset` to free the struct will leak the pool / sub-allocator slot",
        .{ missing.recv, missing.method },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "reset-skips-pooled-resource-release",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, reset_name_tok),
        .end = try Pos.fromTokenEnd(tree, reset_name_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "reset-skips: deinit releases pool, reset doesn't, AND per-cycle acquire elsewhere — fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const NodePool = struct {
        \\    pub fn acquire(_: *NodePool) *u8 { return undefined; }
        \\    pub fn release(_: *NodePool, _: anytype) void {}
        \\};
        \\const SegmentedArray = struct {
        \\    nodes: []*u8,
        \\    node_count: usize,
        \\    pub fn deinit(self: *SegmentedArray, alloc: std.mem.Allocator, node_pool: *NodePool) void {
        \\        for (self.nodes[0..self.node_count]) |node| node_pool.release(node);
        \\        alloc.free(self.nodes);
        \\    }
        \\    pub fn reset(self: *SegmentedArray) void {
        \\        self.node_count = 0;
        \\    }
        \\    pub fn grow(self: *SegmentedArray, node_pool: *NodePool) void {
        \\        self.nodes[self.node_count] = node_pool.acquire();
        \\        self.node_count += 1;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
    try std.testing.expectEqualStrings("reset-skips-pooled-resource-release", problems.items[0].rule_id);
}

test "reset-skips: partial-clear (reset does some cleanup) suppresses non-touched receivers" {
    // Real-world IncrementalGraph pattern — reset clears only the
    // current-chunk state (intentionally) while deinit tears down
    // the entire graph including persistent fields.  The presence
    // of ANY cleanup in reset signals the author was aware; the
    // fields they didn't touch are intentionally persistent.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Pool = struct {
        \\    pub fn release(_: *Pool, _: anytype) void {}
        \\    pub fn acquire(_: *Pool) *u8 { return undefined; }
        \\};
        \\const G = struct {
        \\    bundled_files: std.ArrayList(u8),
        \\    current_chunk: std.ArrayList(u8),
        \\    nodes: []*u8,
        \\    node_count: usize,
        \\    pub fn deinit(g: *G, alloc: std.mem.Allocator, pool: *Pool) void {
        \\        g.bundled_files.deinit(alloc);
        \\        g.current_chunk.deinit(alloc);
        \\        for (g.nodes[0..g.node_count]) |n| pool.release(n);
        \\    }
        \\    pub fn reset(g: *G) void {
        \\        g.current_chunk.clearRetainingCapacity();
        \\    }
        \\    pub fn use(g: *G, pool: *Pool) void {
        \\        g.nodes[g.node_count] = pool.acquire();
        \\        g.node_count += 1;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    // `reset` clears `current_chunk` and intentionally leaves
    // `bundled_files` and `pool` (graph state) alone.  Even though
    // `use` re-acquires from `pool` (per-cycle signal), the
    // partial-clear heuristic suppresses the fire.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: pool-lifetime asymmetry (no non-init acquire) is suppressed" {
    // Canonical ScanBufferPool shape — resources are acquired once
    // in init, released in deinit; reset just zeros the counter.
    // No other method re-acquires, so the asymmetry is intentional
    // and must NOT fire.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Grid = struct { pub fn block_unref(_: *Grid, _: anytype) void {} };
        \\const ScanBuffer = struct {
        \\    index_block: u32,
        \\    pub fn init(self: *ScanBuffer, _: *Grid) void { self.* = .{ .index_block = 0 }; }
        \\    pub fn deinit(self: *ScanBuffer, grid: *Grid) void { grid.block_unref(self.index_block); }
        \\};
        \\const ScanBufferPool = struct {
        \\    scan_buffers: [4]ScanBuffer,
        \\    scan_buffer_used: u8,
        \\    pub fn init(self: *ScanBufferPool, grid: *Grid) void {
        \\        self.scan_buffer_used = 0;
        \\        for (&self.scan_buffers) |*sb| sb.init(grid);
        \\    }
        \\    pub fn deinit(self: *ScanBufferPool, grid: *Grid) void {
        \\        for (&self.scan_buffers) |*sb| sb.deinit(grid);
        \\    }
        \\    pub fn reset(self: *ScanBufferPool) void {
        \\        self.scan_buffer_used = 0;
        \\    }
        \\    pub fn acquire(self: *ScanBufferPool) *ScanBuffer {
        \\        const r = &self.scan_buffers[self.scan_buffer_used];
        \\        self.scan_buffer_used += 1;
        \\        return r;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: deinit and reset both release — doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const NodePool = struct {
        \\    pub fn release(_: *NodePool, _: anytype) void {}
        \\};
        \\const SegmentedArray = struct {
        \\    nodes: []*u8,
        \\    node_count: usize,
        \\    pub fn deinit(self: *SegmentedArray, alloc: std.mem.Allocator, node_pool: *NodePool) void {
        \\        for (self.nodes[0..self.node_count]) |node| node_pool.release(node);
        \\        alloc.free(self.nodes);
        \\    }
        \\    pub fn reset(self: *SegmentedArray, node_pool: *NodePool) void {
        \\        for (self.nodes[0..self.node_count]) |node| node_pool.release(node);
        \\        self.node_count = 0;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: no deinit/reset pair doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct {
        \\    pub fn deinit(_: *T) void {}
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: pool-release in deinit only — fires (allocator-only deinit doesn't)" {
    // Allocator-only deinit (`gpa.free(self.x)`, `alloc.destroy(...)`)
    // is intentionally NOT a trigger — reset legitimately keeps
    // backing storage.  Only POOL / EXTERNAL-resource releases
    // missing from reset count as bugs.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const T = struct {
        \\    pub fn deinit(self: *T, gpa: std.mem.Allocator) void {
        \\        gpa.destroy(self);
        \\    }
        \\    pub fn reset(self: *T) void {
        \\        self.* = .{};
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    // allocator-only cleanup: NOT a bug per rule scope.
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "reset-skips: pool-release in deinit with per-cycle reference() elsewhere — fires" {
    // Per-cycle: another method calls `rc.reference()`, so the
    // resource is acquired per-cycle and reset must release it.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Refcount = struct {
        \\    pub fn reference(_: *Refcount) void {}
        \\    pub fn release(_: *Refcount) void {}
        \\};
        \\const T = struct {
        \\    rc: *Refcount,
        \\    pub fn deinit(self: *T) void { self.rc.release(); }
        \\    pub fn reset(self: *T) void { _ = self; }
        \\    pub fn use(self: *T) void { self.rc.reference(); }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expect(problems.items.len >= 1);
}

test "reset-skips: address-free event storage is not a per-cycle resource" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Observation = struct { kind: enum { read, write }, id: u64, committed: bool };
        \\const Port = struct {
        \\    memory: std.mem.Allocator,
        \\    events: std.ArrayList(Observation) = .empty,
        \\    reset_next: bool = false,
        \\    fn deinit(self: *Port) void { self.events.deinit(self.memory); }
        \\    fn reset(self: *Port) void { self.reset_next = true; }
        \\    fn record(self: *Port, row: Observation) !void { try self.events.append(self.memory, row); }
        \\};
    );
}

test "reset-skips: pooled elements are not an event-storage exemption" {
    try testing.expectFiresTyped(check, "reset-skips-pooled-resource-release",
        \\const std = @import("std");
        \\const Lease = struct { bytes: []u8 };
        \\const Pool = struct {
        \\    memory: std.mem.Allocator,
        \\    fn acquire(self: *Pool) !Lease { return .{ .bytes = try self.memory.alloc(u8, 1) }; }
        \\    fn release(self: *Pool, lease: Lease) void { self.memory.free(lease.bytes); }
        \\};
        \\const Port = struct {
        \\    leases: [4]Lease,
        \\    used: usize = 0,
        \\    fn deinit(self: *Port, pool: *Pool) void {
        \\        for (self.leases[0..self.used]) |lease| pool.release(lease);
        \\    }
        \\    fn reset(self: *Port) void { self.used = 0; }
        \\    fn record(self: *Port, pool: *Pool) !void {
        \\        self.leases[self.used] = try pool.acquire();
        \\        self.used += 1;
        \\    }
        \\};
    );
}

test "reset-skips: address-carrying list elements do not prove a nonpool lifetime" {
    try testing.expectFiresTyped(check, "reset-skips-pooled-resource-release",
        \\const std = @import("std");
        \\const Port = struct {
        \\    memory: std.mem.Allocator,
        \\    leases: std.ArrayList([]u8) = .empty,
        \\    fn deinit(self: *Port) void { self.leases.deinit(self.memory); }
        \\    fn reset(self: *Port) void { _ = self; }
        \\    fn record(self: *Port, bytes: []u8) !void { try self.leases.append(self.memory, bytes); }
        \\};
    );
}

test "reset-skips: standard-looking user container does not prove backing-only release" {
    try testing.expectFiresTyped(check, "reset-skips-pooled-resource-release",
        \\const std = @import("std");
        \\const ArrayList = struct {
        \\    memory: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *ArrayList) void { self.memory.free(self.bytes); }
        \\    fn append(self: *ArrayList) !void { self.bytes = try self.memory.alloc(u8, 1); }
        \\};
        \\const Port = struct {
        \\    events: ArrayList,
        \\    fn deinit(self: *Port) void { self.events.deinit(); }
        \\    fn reset(self: *Port) void { _ = self; }
        \\    fn record(self: *Port) !void { try self.events.append(); }
        \\};
    );
}
