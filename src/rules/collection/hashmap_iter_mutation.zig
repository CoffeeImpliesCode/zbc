//! HashMap iterator-invalidation-via-mutation detector.
//!
//! `var iter = <map>.<iter-method>();`
//! `while (iter.next()) |...| { ... <map>.<mutate>(...) ... }`
//!
//! Structural changes to a HashMap can invalidate its active iterator.
//! A source-proven same-key, no-growth replacement changes only the value.
//! Unknown dispatch and changes to occupancy or backing retain the warning.
//!
//! Complementary to [[iterator-invalidation-mutation]] which detects
//! the `for (list.items)` / ArrayList variant.
//!
//! Detection (per-fn token walk):
//!   1. Find `const/var <iter> = <recv>.<iter-method>()` bindings
//!      where iter-method ∈ {iterator, keyIterator, valueIterator}.
//!      Match a bare receiver or one field of a receiver.
//!   2. After the binding `;`, scan for `while (<iter>.next()) [|…|]`
//!      loop headers.
//!   3. Scan the while loop body for `<recv>.<mutate>(` calls at the
//!      SAME lexical block depth (nested blocks are skipped since they
//!      don't always execute).
//!   4. Exclude a canonical SDK integer-key AutoContext replacement only when
//!      the current capture supplies the unchanged key and no effect interferes.
//!      Fire at the remaining mutation call site.
//!
//! Mutate-method allowlist:
//!   put / putAssumeCapacity / putNoClobber / putNoClobberAssumeCapacity
//!   remove / removeByPtr / fetchPut / fetchRemove / swapRemove /
//!   clearAndFree / clearRetainingCapacity.
//!
//! Suppression: mutations inside `defer`/`errdefer` are skipped
//! (deferred, not inline), consistent with other rules.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const effect_scan = @import("../../cache/call_effects.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const matchBrace = tokens.matchBrace;
const matchParen = tokens.matchParen;
const skipNestedFn = tokens.skipNestedFn;
const skipDeferStmt = tokens.skipDeferStmt;
const findStmtSemicolon = tokens.findStmtSemicolon;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .hashmap_iter_mutation)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkBody);
}

fn isIteratorMethod(s: []const u8) bool {
    return std.mem.eql(u8, s, "iterator") or
        std.mem.eql(u8, s, "keyIterator") or
        std.mem.eql(u8, s, "valueIterator");
}

fn isMutateMethod(s: []const u8) bool {
    return std.mem.eql(u8, s, "put") or
        std.mem.eql(u8, s, "putAssumeCapacity") or
        std.mem.eql(u8, s, "putNoClobber") or
        std.mem.eql(u8, s, "putNoClobberAssumeCapacity") or
        std.mem.eql(u8, s, "remove") or
        std.mem.eql(u8, s, "removeByPtr") or
        std.mem.eql(u8, s, "fetchPut") or
        std.mem.eql(u8, s, "fetchRemove") or
        std.mem.eql(u8, s, "swapRemove") or
        std.mem.eql(u8, s, "clearAndFree") or
        std.mem.eql(u8, s, "ensureTotalCapacity") or
        std.mem.eql(u8, s, "ensureUnusedCapacity") or
        std.mem.eql(u8, s, "rehash") or
        std.mem.eql(u8, s, "clearRetainingCapacity");
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    _ = proto;
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Track open-brace depth so iterator bindings inside nested blocks
    // (`if`/`errdefer`/etc.) only trigger searches within that block,
    // preventing cross-boundary matches when a same-named variable in
    // an outer scope is mutated after the inner block closes.
    var brace_depth: u32 = 0;
    var t: Ast.TokenIndex = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] == .l_brace) {
            brace_depth += 1;
            continue;
        }
        if (tags[t] == .r_brace) {
            if (brace_depth > 0) brace_depth -= 1;
            continue;
        }
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        // Match `<recv> . <iter-method> ( )`:
        // iterator bindings are: `const/var iter = [try] <recv>.<iter-method>()`
        // We detect at the position of the method name.
        if (tags[t] != .identifier) continue;
        if (!isIteratorMethod(tree.tokenSlice(t))) continue;
        if (t == 0 or tags[t - 1] != .period) continue;
        if (t + 1 > last or tags[t + 1] != .l_paren) continue;
        if (t + 2 > last or tags[t + 2] != .r_paren) continue;

        // Walk backward from `t-2` (the `.`) to find the binding `const/var iter =`.
        // Also extract the receiver name (the identifier before the `.`).
        const dot_pos: Ast.TokenIndex = t - 1;
        if (dot_pos == 0) continue;
        // The receiver is the identifier at `t-2`.
        if (tags[t - 2] != .identifier) continue;
        const recv_name = tree.tokenSlice(t - 2);
        // Check for a compound receiver `prefix.recv_name.iter()`.
        // When the token at t-3 is `.` and t-4 is an identifier, the iterator
        // source is `prefix.recv_name`, not just `recv_name`.  Storing the prefix
        // allows findReceiverMutate to distinguish `self.map.iterator()` from a
        // bare `map.iterator()`, preventing false-positive fires when a different
        // variable named `map` is mutated inside the loop body.
        const recv_prefix: ?[]const u8 = if (t >= 4 and
            tags[t - 3] == .period and
            tags[t - 4] == .identifier)
            tree.tokenSlice(t - 4)
        else
            null;

        // Walk backward from after the recv to find `= [try] recv_prefix?.recv .` and
        // then `const/var iter =`.  Adjust starting position based on prefix presence.
        const assign_search_start: Ast.TokenIndex = if (recv_prefix != null) t - 5 else t - 3;
        if (assign_search_start == 0) continue;
        var i: Ast.TokenIndex = assign_search_start;
        // Walk past any `try` keyword.
        if (tags[i] == .keyword_try) {
            if (i == 0) continue;
            i -= 1;
        }
        // Now `i` should be at `=`.
        if (tags[i] != .equal) continue;
        if (i == 0) continue;
        const j = i - 1; // should be the iter name
        if (tags[j] != .identifier) continue;
        const iter_name = tree.tokenSlice(j);
        if (j == 0) continue;
        const before_iter = tags[j - 1];
        if (before_iter != .keyword_const and before_iter != .keyword_var) continue;

        // `iter_name` is the iterator variable, `recv_name`/`recv_prefix` identify the map.
        // Find the `;` that ends the iterator binding statement.
        const semi = findStmtSemicolon(tags, t, last) orelse continue;

        // Determine the scope boundary for the iterator.  When the binding is
        // inside a nested block (brace_depth > 0), the search must not cross
        // the block's closing `}` — otherwise an outer variable with the same
        // name would be flagged.
        const scope_end: Ast.TokenIndex = blk: {
            if (brace_depth == 0) break :blk last;
            // Find the `}` that closes the current block.
            var depth_left = brace_depth;
            var s = semi + 1;
            while (s <= last) : (s += 1) {
                if (tags[s] == .l_brace) depth_left += 1 else if (tags[s] == .r_brace) {
                    depth_left -= 1;
                    if (depth_left < brace_depth) break :blk s - 1;
                }
            }
            break :blk last;
        };

        // Scan from `semi+1` to `scope_end` for `while (<iter_name>.next())`.
        try scanForWhileLoop(gpa, tree, cache, tags, iter_name, t, recv_prefix, recv_name, semi + 1, scope_end, problems);
    }
}

/// Scan from `scan_start` to `last` for `while (<iter>.next()) |...| { ... <recv>.<mutate> ... }`.
fn scanForWhileLoop(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    iter_name: []const u8,
    iterator_token: Ast.TokenIndex,
    recv_prefix: ?[]const u8,
    recv_name: []const u8,
    scan_start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    var t: Ast.TokenIndex = scan_start;
    while (t + 7 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }

        if (tags[t] != .keyword_while) continue;
        if (t + 1 > last or tags[t + 1] != .l_paren) continue;

        const cond_lp = t + 1;
        const cond_rp = matchParen(tags, cond_lp, last) orelse continue;

        // The condition must be exactly `(<iter>.next())`.
        // Tokens inside: iter . next ( )  → 5 tokens → cond_rp = cond_lp + 6.
        if (cond_rp != cond_lp + 6) continue;
        if (tags[cond_lp + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(cond_lp + 1), iter_name)) continue;
        if (tags[cond_lp + 2] != .period) continue;
        if (tags[cond_lp + 3] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(cond_lp + 3), "next")) continue;
        if (tags[cond_lp + 4] != .l_paren) continue;
        if (tags[cond_lp + 5] != .r_paren) continue;

        // After cond_rp, skip optional `: (continue_expr)` then optional `|capture|`.
        var body_start = cond_rp + 1;
        if (body_start <= last and tags[body_start] == .colon) {
            if (body_start + 1 <= last and tags[body_start + 1] == .l_paren) {
                const cont_rp = matchParen(tags, body_start + 1, last) orelse continue;
                body_start = cont_rp + 1;
            }
        }
        var capture: ?Ast.TokenIndex = null;
        if (body_start <= last and tags[body_start] == .pipe) {
            if (body_start + 2 <= last and tags[body_start + 1] == .identifier and tags[body_start + 2] == .pipe)
                capture = body_start + 1;
            body_start += 1;
            while (body_start <= last and tags[body_start] != .pipe) : (body_start += 1) {}
            if (body_start > last) continue;
            body_start += 1;
        }
        if (body_start > last or tags[body_start] != .l_brace) continue;
        const body_end = matchBrace(tags, body_start, last) orelse continue;

        // Scan the while body for `<recv>.<mutate>(` at depth 0.
        const mutate_tok = (try findReceiverMutate(tree, cache, tags, body_start + 1, body_end - 1, iterator_token, cond_lp + 3, capture, recv_prefix, recv_name)) orelse continue;

        // Fire.
        const display_recv = if (recv_prefix) |pfx| blk: {
            const buf = try gpa.alloc(u8, pfx.len + 1 + recv_name.len);
            @memcpy(buf[0..pfx.len], pfx);
            buf[pfx.len] = '.';
            @memcpy(buf[pfx.len + 1 ..], recv_name);
            break :blk buf;
        } else try gpa.dupe(u8, recv_name);
        defer gpa.free(display_recv);
        const msg = try std.fmt.allocPrint(
            gpa,
            "`{s}.{s}(...)` modifies the map while `{s}` is iterating over it — the iterator cursor is now undefined.  Collect items to change into a separate list first.",
            .{ display_recv, tree.tokenSlice(mutate_tok), iter_name },
        );
        errdefer gpa.free(msg);
        try problems.append(gpa, .{
            .rule_id = "hashmap-iter-mutation",
            .severity = .@"error",
            .start = try Pos.fromTokenStart(tree, mutate_tok),
            .end = try Pos.fromTokenEnd(tree, mutate_tok),
            .message = msg,
        });
        // One report per while loop is enough.
        t = body_end;
    }
}

/// Scan `[start, last]` for `<recv>.<mutate>(` at the top-level block
/// depth (lexical nesting 0).  Skips nested `{...}` blocks, `defer`/
/// `errdefer` statements, and `fn` bodies.  Returns the token index
/// of the mutate method name on success.
fn findReceiverMutate(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    last: Ast.TokenIndex,
    iterator_token: Ast.TokenIndex,
    next_token: Ast.TokenIndex,
    capture: ?Ast.TokenIndex,
    recv_prefix: ?[]const u8,
    recv: []const u8,
) !?Ast.TokenIndex {
    if (start > last) return null;
    var t: Ast.TokenIndex = start;
    while (t + 3 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] == .l_brace) {
            t = matchBrace(tags, t, last) orelse return null;
            continue;
        }
        if (tags[t] == .r_brace) return null;
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            t = skipDeferStmt(tags, t, last) orelse return null;
            continue;
        }
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), recv)) continue;
        // For a compound receiver (prefix.recv), the token before `recv` must
        // be `.` and the token before that must be `prefix`.  Without this check,
        // a bare `recv.mutate(...)` would match `prefix.recv.iterator()`, producing
        // a false positive when `recv` is a distinct variable.
        if (recv_prefix) |pfx| {
            if (t < 2 or tags[t - 1] != .period) continue;
            if (tags[t - 2] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t - 2), pfx)) continue;
            // Reject if `pfx` is itself part of a longer chain: `other.pfx.recv.mutate()`.
            // In that case the root object differs from the iterator's receiver.
            if (t >= 4 and tags[t - 3] == .period) continue;
        }
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .l_paren) continue;
        if (isMutateMethod(tree.tokenSlice(t + 2))) {
            if (try stableCurrentKeyReplacement(cache, iterator_token, next_token, capture, last, t + 2)) continue;
            return t + 2;
        }
    }
    return null;
}

/// The SDK's assumed-capacity replacement changes only an existing value when
/// its key is the current entry's unchanged key. Ordinary `put` can grow before
/// looking up that key, and no-clobber insertion is not a replacement contract.
/// Unknown/custom methods keep the warning even if they use familiar names.
fn stableCurrentKeyReplacement(
    cache: *file_cache_mod.FileCache,
    iterator_token: Ast.TokenIndex,
    next_token: Ast.TokenIndex,
    capture: ?Ast.TokenIndex,
    loop_end: Ast.TokenIndex,
    method_token: Ast.TokenIndex,
) !bool {
    const entry = capture orelse return false;
    const resolver = cache.zls orelse return false;
    const tree = cache.tree;
    // Call-index keys are the callee expression's main token: the field dot.
    const iterator = (try cache.actualCallSummaryAt(iterator_token - 1, null)) orelse return false;
    const mutation = (try cache.actualCallSummaryAt(method_token - 1, null)) orelse return false;
    if (!try resolver.declaredInToolchainFile(iterator.callee.handle, "/std/hash_map.zig") or
        !try resolver.declaredInToolchainFile(mutation.callee.handle, "/std/hash_map.zig")) return false;
    if (!std.mem.eql(u8, iterator.callee.tree.tokenSlice(iterator.callee.fn_token + 1), "iterator") or
        !std.mem.eql(u8, mutation.callee.tree.tokenSlice(mutation.callee.fn_token + 1), "putAssumeCapacity")) return false;
    if (!try standardIntegerContext(cache, mutation)) return false;
    const next = (try cache.actualCallSummaryAt(next_token - 1, null)) orelse return false;
    if (!try resolver.declaredInToolchainFile(next.callee.handle, "/std/hash_map.zig") or
        !std.mem.eql(u8, next.callee.tree.tokenSlice(next.callee.fn_token + 1), "next")) return false;

    // Map formal coordinates through the exact callee, including a managed
    // map's implicit receiver and an unmanaged map's explicit allocator.
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(mutation.callee.tree, &proto_buffer, mutation.callee.declaration) orelse return false;
    var parameters = proto.iterate(mutation.callee.tree);
    var parameter: u32 = 0;
    var key: ?Ast.Node.Index = null;
    while (parameters.next()) |formal| : (parameter += 1) {
        const name = formal.name_token orelse return false;
        if (!std.mem.eql(u8, mutation.callee.tree.tokenSlice(name), "key")) continue;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        key = try mutation.callArgumentFor(cache, &argument_buffer, parameter);
        break;
    }
    const key_node = key orelse return false;
    const first = tree.firstToken(key_node);
    const last = tree.lastToken(key_node);
    if (last != first + 3 or tree.tokenTag(first) != .identifier or
        !std.mem.eql(u8, tree.tokenSlice(first), tree.tokenSlice(entry)) or
        tree.tokenTag(first + 1) != .period or tree.tokenTag(first + 2) != .identifier or
        !std.mem.eql(u8, tree.tokenSlice(first + 2), "key_ptr") or
        tree.tokenTag(first + 3) != .period_asterisk) return false;

    // No intervening call, store, rebind, or opaque expression may invalidate
    // either the table or the captured key, including mutation arguments.
    const declaration = tokens.enclosingFnDecl(tree, method_token) orelse return false;
    var enclosing_buffer: [1]Ast.Node.Index = undefined;
    const enclosing = tokens.fnProto(tree, &enclosing_buffer, declaration) orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    const bindings = (try cache.localBindings(enclosing, body)).*;
    const key_binding = bindings.findAt(tree.tokenSlice(first), first) orelse return false;
    if (key_binding.name_token != entry) return false;
    var receiver_buffer: [2]Ast.Node.Index = undefined;
    const iterator_receiver = (try iterator.callArgumentFor(cache, &receiver_buffer, 0)) orelse return false;
    const iterator_root = tree.firstToken(iterator_receiver);
    const iterator_binding = bindings.findAt(tree.tokenSlice(iterator_root), iterator_root) orelse return false;
    const mutation_receiver = (try mutation.callArgumentFor(cache, &receiver_buffer, 0)) orelse return false;
    const mutation_root = tree.firstToken(mutation_receiver);
    const mutation_binding = bindings.findAt(tree.tokenSlice(mutation_root), mutation_root) orelse return false;
    if (iterator_binding.name_token != mutation_binding.name_token) return false;
    const horizon = loop_end;
    var scan = effect_scan.Scan.init(tree, declaration, &bindings);
    while (try scan.next()) |event| {
        const node = switch (event) {
            .node, .call, .write_or_unknown => |node| node,
            .write => |write| write.node,
        };
        const token = tree.nodeMainToken(node);
        if (token < iterator_token or token > horizon) continue;
        switch (event) {
            .node => switch (tree.nodeTag(node)) {
                .assign, .assign_mul, .assign_div, .assign_mod, .assign_add, .assign_sub,
                .assign_shl, .assign_shl_sat, .assign_shr, .assign_bit_and, .assign_bit_xor,
                .assign_bit_or, .assign_mul_wrap, .assign_add_wrap, .assign_sub_wrap,
                .assign_mul_sat, .assign_add_sat, .assign_sub_sat, .assign_destructure,
                => return false,
                else => {},
            },
            .call => if (node != iterator.callee.call_node and node != next.callee.call_node and
                node != mutation.callee.call_node) return false,
            .write, .write_or_unknown => return false,
        }
    }
    return true;
}

/// AutoContext on an integer key has no project-defined hash/equality callback.
/// The generic bindings and the context factory's declaring SDK document are
/// both required: an SDK HashMap instantiated with a custom Context is unknown.
fn standardIntegerContext(cache: *file_cache_mod.FileCache, actual: file_cache_mod.FileCache.ActualCallSummary) !bool {
    const resolver = cache.zls orelse return false;
    const function = actual.callee.reference.actual_type.data.function;
    const owner = function.container_type.*;
    if (owner.data != .container or function.parameters.len != 3) return false;
    const container = owner.data.container;
    const map_handle = container.scope_handle.handle;
    if (!map_handle.eql(actual.callee.handle)) return false;
    const map_tree = &map_handle.document.tree;
    const map_factory = tokens.enclosingFnDecl(map_tree, map_tree.firstToken(container.scope_handle.toNode())) orelse return false;
    var map_buffer: [1]Ast.Node.Index = undefined;
    const map_proto = tokens.fnProto(map_tree, &map_buffer, map_factory) orelse return false;
    var map_parameters = map_proto.iterate(map_tree);
    const key_parameter = map_parameters.next() orelse return false;
    _ = map_parameters.next() orelse return false; // V
    const context_parameter = map_parameters.next() orelse return false;
    const key = container.bound_params.get(.{
        .token = key_parameter.name_token orelse return false,
        .handle = map_handle,
    }) orelse return false;
    const key_type = (try resolver.normalizedType(key)) orelse return false;
    if (resolver.typeTag(key_type) != .int) return false;
    const formal_key = (try resolver.normalizedType(function.parameters[1].type)) orelse return false;
    if (!key_type.eql(formal_key)) return false;
    const context_value = container.bound_params.get(.{
        .token = context_parameter.name_token orelse return false,
        .handle = map_handle,
    }) orelse return false;
    const context_type = (try resolver.normalizedType(context_value)) orelse return false;
    if (context_type.data != .container) return false;
    const context = context_type.data.container;
    const context_handle = context.scope_handle.handle;
    if (!context_handle.eql(map_handle)) return false;
    const context_tree = &context_handle.document.tree;
    const factory = tokens.enclosingFnDecl(context_tree, context_tree.firstToken(context.scope_handle.toNode())) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(context_tree, &buffer, factory) orelse return false;
    if (!std.mem.eql(u8, context_tree.tokenSlice(proto.name_token orelse return false), "AutoContext")) return false;
    var context_parameters = proto.iterate(context_tree);
    const context_key_parameter = context_parameters.next() orelse return false;
    const context_key = context.bound_params.get(.{
        .token = context_key_parameter.name_token orelse return false,
        .handle = context_handle,
    }) orelse return false;
    const context_key_type = (try resolver.normalizedType(context_key)) orelse return false;
    return key_type.eql(context_key_type);
}

// ── Tests ──────────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "hashmap-iter-mutation: remove during iteration fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype) void {
        \\    var iter = map.iterator();
        \\    while (iter.next()) |entry| {
        \\        if (entry.value_ptr.* == 0)
        \\            _ = map.remove(entry.key_ptr.*);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("hashmap-iter-mutation", problems.items[0].rule_id);
}

test "hashmap-iter-mutation: put during iteration fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype) !void {
        \\    var iter = map.iterator();
        \\    while (iter.next()) |entry| {
        \\        try map.put(entry.key_ptr.*, entry.value_ptr.* + 1);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "hashmap-iter-mutation: read-only iteration does NOT fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype) u32 {
        \\    var sum: u32 = 0;
        \\    var iter = map.iterator();
        \\    while (iter.next()) |entry| {
        \\        sum += entry.value_ptr.*;
        \\    }
        \\    return sum;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "hashmap-iter-mutation: mutation on different map does NOT fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype, other: anytype) void {
        \\    var iter = map.iterator();
        \\    while (iter.next()) |entry| {
        \\        _ = other.remove(entry.key_ptr.*);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "hashmap-iter-mutation: errdefer-scoped iterator + outer map mutation — does NOT fire" {
    // `var it = map.iterator()` inside errdefer block; outer code mutates `map`
    // via a DIFFERENT while loop — must not fire because the iterator's scope
    // is limited to the errdefer block.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn clone(self: anytype, alloc: anytype) !@TypeOf(self.map) {
        \\    var map = @TypeOf(self.map){};
        \\    errdefer {
        \\        var it = map.iterator();
        \\        while (it.next()) |entry| {
        \\            alloc.free(entry.key_ptr.*);
        \\        }
        \\        map.deinit(alloc);
        \\    }
        \\    var it = self.map.iterator();
        \\    while (it.next()) |entry| {
        \\        map.putAssumeCapacity(entry.key_ptr.*, entry.value_ptr.*);
        \\    }
        \\    return map;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "hashmap-iter-mutation: self.map iterator + map mutation — different vars, does NOT fire" {
    // Iterator on self.map, but body mutates a bare `map` variable (different object).
    // This is the copy-into-new-map pattern; it must NOT fire.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn clone(self: anytype, alloc: anytype) !@TypeOf(self.map) {
        \\    var map = @TypeOf(self.map){};
        \\    try map.ensureTotalCapacity(alloc, self.map.count());
        \\    var it = self.map.iterator();
        \\    while (it.next()) |entry| {
        \\        map.putAssumeCapacity(entry.key_ptr.*, entry.value_ptr.*);
        \\    }
        \\    return map;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "hashmap-iter-mutation: self.map iterator + self.map mutation — same field, fires" {
    // Iterator on self.map AND mutation of self.map — real bug.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(self: anytype, k: anytype, v: anytype) void {
        \\    var it = self.map.iterator();
        \\    while (it.next()) |_| {
        \\        self.map.putAssumeCapacity(k, v);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "hashmap-iter-mutation: outer.recv.map mutation vs recv.map iterator — does NOT fire" {
    // Iterator is on `lockfile.workspace_paths`; mutation is on
    // `manager.lockfile.workspace_paths` — same two-token suffix but a
    // different root object.  The old code matched on the `lockfile` prefix
    // alone and fired a false positive; the fix checks that `lockfile` is NOT
    // itself preceded by `.`, which would indicate a deeper chain.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn migrate(manager: anytype, lockfile: anytype) void {
        \\    manager.lockfile.workspace_paths.clearRetainingCapacity();
        \\    var iter = lockfile.workspace_paths.iterator();
        \\    while (iter.next()) |entry| {
        \\        manager.lockfile.workspace_paths.putAssumeCapacity(entry.key_ptr.*, entry.value_ptr.*);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "hashmap-iter-mutation: clearAndFree during iteration fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\pub fn foo(map: anytype, alloc: anytype) void {
        \\    var iter = map.keyIterator();
        \\    while (iter.next()) |key| {
        \\        _ = key;
        \\        map.clearAndFree(alloc);
        \\    }
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "hashmap-iter-mutation: three native index maps replace their current keys" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Slot = struct { index: u32, width: u32 };
        \\const Builder = struct {
        \\    gpa: std.mem.Allocator,
        \\    values: std.AutoHashMapUnmanaged(u32, Slot),
        \\    pinned_regs: std.AutoHashMapUnmanaged(u32, u32),
        \\    frames: std.AutoHashMapUnmanaged(u32, u32),
        \\};
        \\fn remap(builder: *Builder, permutation: []const u32) void {
        \\    var iterator = builder.values.iterator();
        \\    while (iterator.next()) |entry| {
        \\        const rewritten: Slot = .{
        \\            .index = permutation[entry.value_ptr.index],
        \\            .width = entry.value_ptr.width,
        \\        };
        \\        builder.values.putAssumeCapacity(entry.key_ptr.*, rewritten);
        \\    }
        \\    var pins = builder.pinned_regs.iterator();
        \\    while (pins.next()) |entry| {
        \\        builder.pinned_regs.putAssumeCapacity(entry.key_ptr.*, permutation[entry.value_ptr.*]);
        \\    }
        \\    var frames = builder.frames.iterator();
        \\    while (frames.next()) |entry| {
        \\        builder.frames.putAssumeCapacity(entry.key_ptr.*, permutation[entry.value_ptr.*]);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: SDK map aliases preserve stable replacement" {
    try testing.expectNoFireTyped(check,
        \\const library = @import("std");
        \\const Table = library.AutoHashMap(u32, u32);
        \\fn rewrite(table: *Table) void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        table.putAssumeCapacity(row.key_ptr.*, row.value_ptr.* + 1);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: assumed capacity does not prove an arbitrary key present" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const std = @import("std");
        \\fn insert(table: *std.AutoHashMap(u32, u32), key: u32) void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        table.putAssumeCapacity(key, row.value_ptr.*);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: growing put of the current key remains warned" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const std = @import("std");
        \\fn rewrite(table: *std.AutoHashMap(u32, u32)) !void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        try table.put(row.key_ptr.*, row.value_ptr.* + 1);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: same named custom replacement is not an SDK contract" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const Entry = struct { key_ptr: *u32, value_ptr: *u32 };
        \\const Cursor = struct {
        \\    extern fn next(self: *Cursor) ?Entry;
        \\};
        \\const Table = struct {
        \\    extern fn iterator(self: *Table) Cursor;
        \\    extern fn putAssumeCapacity(self: *Table, key: u32, value: u32) void;
        \\};
        \\fn rewrite(table: *Table) void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        table.putAssumeCapacity(row.key_ptr.*, row.value_ptr.*);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: replacement cannot hide later removal" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const std = @import("std");
        \\fn rewrite(table: *std.AutoHashMap(u32, u32)) void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        table.putAssumeCapacity(row.key_ptr.*, row.value_ptr.*);
        \\        _ = table.remove(row.key_ptr.*);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: a mutated key is not a stable replacement" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const std = @import("std");
        \\fn rewrite(table: *std.AutoHashMap(u32, u32)) void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        row.key_ptr.* += 1;
        \\        table.putAssumeCapacity(row.key_ptr.*, row.value_ptr.*);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: unknown argument effects cannot certify replacement" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const std = @import("std");
        \\extern fn change(table: *std.AutoHashMap(u32, u32)) u32;
        \\fn rewrite(table: *std.AutoHashMap(u32, u32)) void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        table.putAssumeCapacity(row.key_ptr.*, change(table));
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: custom hash context cannot borrow the SDK replacement proof" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const std = @import("std");
        \\const Context = struct {
        \\    extern fn hash(self: Context, key: u32) u64;
        \\    extern fn eql(self: Context, left: u32, right: u32) bool;
        \\};
        \\const Table = std.HashMap(u32, u32, Context, 80);
        \\fn rewrite(table: *Table) void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        table.putAssumeCapacity(row.key_ptr.*, row.value_ptr.*);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: receiver rebinding invalidates current-key proof" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const std = @import("std");
        \\const Table = std.AutoHashMap(u32, u32);
        \\fn rewrite(original: *Table, other: *Table) void {
        \\    var table = original;
        \\    var cursor = table.iterator();
        \\    table = other;
        \\    while (cursor.next()) |row| {
        \\        table.putAssumeCapacity(row.key_ptr.*, row.value_ptr.*);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: later opaque mutation keeps replacement unknown" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const std = @import("std");
        \\const Table = std.AutoHashMap(u32, u32);
        \\extern fn change(table: *Table) void;
        \\fn rewrite(table: *Table) void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        table.putAssumeCapacity(row.key_ptr.*, row.value_ptr.*);
        \\        change(table);
        \\    }
        \\}
    );
}

test "hashmap-iter-mutation: explicit rehash during iteration remains warned" {
    try testing.expectFiresTyped(check, "hashmap-iter-mutation",
        \\const std = @import("std");
        \\fn grow(table: *std.AutoHashMap(u32, u32)) !void {
        \\    var cursor = table.iterator();
        \\    while (cursor.next()) |row| {
        \\        _ = row;
        \\        try table.ensureTotalCapacity(1024);
        \\    }
        \\}
    );
}
