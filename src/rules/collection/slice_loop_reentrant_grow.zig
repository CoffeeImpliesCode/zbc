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
//!   1. For each `for ( <expr> ) |...|` loop, check if the iterated
//!      expression contains `<recv>.items`.
//!   2. Inside the loop body, scan for:
//!      a. Direct grow: `<recv>.<growMethod>(` on the same recv — fire.
//!      b. Call: `<fn>( ` or `<decl>.<fn>( ` — read the callee's
//!         FnSummary; if `may_grow_collections`, fire, but only when
//!         the callee's `grow_paths` reach the ITERATED storage once
//!         mapped through this call's arguments
//!         (`calleeMayReallocateReceiver`).  The `<decl>.` form is a
//!         free function in another module, and its summary is read
//!         from that module.
//!   3. Fire at the call token.
//!
//! `may_grow_collections` alone is not evidence: a callee that grows only
//! declaration-proved fresh storage cannot move the caller's buffer. Copied
//! ArrayList headers, pointer aliases and unresolved storage remain charged.
//!
//! So neither a `*const` root nor a by-value header proves safety:
//! `*const View` with a `list: *ArrayList(T)` field is mutable, and a
//! copied header still shares its buffer.  The decision is made from
//! `FnSummary.grow_paths` — the parameter-rooted paths a callee can
//! grow — mapped through the call's arguments onto the path the loop
//! captured.  Unknown paths and unknown arguments stay conservative.
//! A name this fn did not introduce is shared state (a container
//! `var`, a threadlocal) that any callee can name on its own, so
//! reaching its name anywhere in the call keeps reporting.
//!
//! A LOCAL is private only when its initializer proves fresh storage and
//! intervening uses do not publish or replace it. An opaque constructor can
//! return a global even without arguments. Local names and constructor names
//! alone never establish allocation ownership.
//!
//! Disjointness is a claim about an ALLOCATION, not a field path. Different
//! parameters can receive the same pointer, and different embedded list
//! headers can share one allocation after a copy.
//!
//! A callee's OWN list is not the loop's storage — but only when the
//! DECLARATIONS prove it built one: a constructor call whose resolved
//! declaration is this toolchain's `std/array_list.zig` list
//! constructor (`std.ArrayList(u32).initCapacity(gpa, n)` for the
//! unmanaged list, `std.array_list.Managed(u32).init(gpa)` for the
//! managed one, and every spelling that reaches the same
//! declaration), or a project constructor whose every
//! `return` is proved the same way.  The NAME proves nothing
//! (`Foo.init` may hand back a global's header), so anything the
//! declarations do not settle is charged as a grow this file cannot
//! place, and reports.
//!
//! A callee this file CANNOT resolve at all — an unreadable module, a
//! method the receiver's type does not declare, a method on a
//! receiver this fn cannot root — is charged the storage the call
//! HANDS IT, at the path each argument was rooted at.  What such a
//! callee does is undecided, and only what it was given can be
//! reallocated; naming WHERE that was is what lets a caller tell it
//! apart from the storage it is walking.
//!
//! A FREE function imported from another file is reached through a
//! declaration of this one — `helpers.growNames(…)` with
//! `const helpers = @import("./helpers.zig")` — and its summary comes
//! from that module.  The project cache carries method summaries
//! without paths, so an imported callee reports "it may grow, and I
//! cannot say whose buffer": that is a reach this file cannot trace
//! rather than one it disproved, so it reports.  What stays invisible
//! is a module this project cannot read at all.  That gap is
//! visibility, not evidence — no consumer may read the silence as a
//! safety proof.
//!
//! Requires `FileCache.resolveTransitiveTakes()` to have run so that
//! `may_grow_collections` and `grow_paths` are transitively propagated
//! through same-file call chains.  `check()` calls it automatically.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const method_names = @import("../../model/method_names.zig");
const fn_summary = @import("../../model/fn_summary.zig");
const AstWalker = @import("type_engine").AstWalker;
const local_bindings = @import("../../model/local_bindings.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

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

    // Path joins made while matching a call against the callee's grow
    // paths are throwaway; one arena per fn keeps them off `gpa`.
    var scratch = std.heap.ArenaAllocator.init(gpa);
    defer scratch.deinit();

    var walker = try AstWalker.init(gpa, tree, body);
    defer walker.deinit(gpa);
    while (try walker.nextIgnoreClose(gpa, tree)) |node| {
        switch (tree.nodeTag(node)) {
            .fn_decl,
            .container_decl,
            .container_decl_trailing,
            .container_decl_two,
            .container_decl_two_trailing,
            .container_decl_arg,
            .container_decl_arg_trailing,
            => {
                walker.skip();
                continue;
            },
            else => {},
        }
        const loop = tree.fullFor(node) orelse continue;
        var receiver: ?Receiver = null;
        for (loop.ast.inputs) |input| {
            receiver = findItemsRecv(tree, tree.firstToken(input), tree.lastToken(input));
            if (receiver != null) break;
        }
        const recv = receiver orelse continue;
        const body_start = tree.firstToken(loop.ast.then_expr);
        const body_end = tree.lastToken(loop.ast.then_expr);
        const capture_by_value = loopCaptureByValue(tags, loop.payload_token - 1, body_start);

        const bindings = try cache.localBindings(proto, body);
        // Scan the loop body for calls that may grow collections.
        try checkLoopBody(
            gpa,
            tree,
            cache,
            scratch.allocator(),
            proto,
            body,
            bindings,
            body_start,
            body_end,
            recv,
            capture_by_value,
            problems,
        );
    }
}

const Receiver = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,

    fn text(self: Receiver, tree: *const Ast) []const u8 {
        const starts = tree.tokens.items(.start);
        return tree.source[starts[self.first] .. starts[self.last] + tree.tokenSlice(self.last).len];
    }

    fn matches(self: Receiver, tree: *const Ast, other: Receiver) bool {
        if (self.last - self.first != other.last - other.first) return false;
        for (0..self.last - self.first + 1) |offset| {
            const index: Ast.TokenIndex = @intCast(offset);
            if (!std.mem.eql(u8, tree.tokenSlice(self.first + index), tree.tokenSlice(other.first + index))) return false;
        }
        return true;
    }
};

fn receiverEndingAt(tree: *const Ast, end: Ast.TokenIndex, lower: Ast.TokenIndex) Receiver {
    const tags = tree.tokens.items(.tag);
    var first = end;
    while (first >= lower + 2 and tags[first - 1] == .period and tags[first - 2] == .identifier) {
        first -= 2;
    }
    return .{ .first = first, .last = end };
}

/// Match the complete dotted receiver before `.items`, not just its last field.
fn findItemsRecv(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) ?Receiver {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var s: Ast.TokenIndex = start;
    while (s + 2 <= end) : (s += 1) {
        if (tags[s] != .identifier) continue;
        if (tags[s + 1] != .period) continue;
        if (tags[s + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(s + 2), "items")) continue;
        return receiverEndingAt(tree, s, start);
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
/// grow a collection. `recv` is the list being iterated.
fn checkLoopBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    scratch: std.mem.Allocator,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    bindings: *const local_bindings.LocalBindings,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    recv: Receiver,
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

        // Direct grow can invalidate a differently named receiver when both
        // headers share one allocation. Names and field paths are not proof.
        if (tags[t] == .identifier and
            t + 3 <= end and
            tags[t + 1] == .period and
            tags[t + 2] == .identifier and
            tags[t + 3] == .l_paren)
        {
            const method = tree.tokenSlice(t + 2);
            if (method_names.isArrayListGrowMethodName(method)) {
                const grown = receiverEndingAt(tree, t, start);
                const until = (matchParen(tags, t + 3, end) orelse end) + 1;
                const same = recv.matches(tree, grown);
                // A private grow receiver is useful only when this is the
                // actual std append, not a same-named method growing globals.
                const private_append = !same and blk: {
                    const append = cache.stdCollectionAppendOfExpr(grown.first, until - 1) orelse break :blk false;
                    if (append == .no) break :blk false;
                    break :blk try receiverOwner(tree, cache, bindings, body, recv, until) == .private or
                        try receiverOwner(tree, cache, bindings, body, grown, until) == .private;
                };
                const may_alias = same or !private_append;
                if (may_alias and !(capture_by_value and callImmediatelyReturns(tags, t + 3, end))) {
                    try report(gpa, problems, tree, t + 2, grown.text(tree), recv.text(tree), method);
                }
                t += 3;
                continue;
            }
        }

        // A call: either `fnName(` or `helpers.fnName(` — a free
        // function reached through one of this file's own declarations,
        // which is storage the loop does not own.
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_paren) continue;

        const callee = tree.tokenSlice(t);
        const summary: fn_summary.FnSummary = blk: {
            if (t > start and tags[t - 1] == .period) {
                if (t < start + 2 or tags[t - 2] != .identifier) continue;
                // `a.b.fn(` qualifies a field of something else, not a
                // module.
                if (t >= start + 3 and tags[t - 3] == .period) continue;
                const qualifier = tree.tokenSlice(t - 2);
                // Storage this fn holds reaches its methods through a
                // parameter or a local; those are not modules.
                if (fn_summary.paramIndex(tree, proto, qualifier) != null) continue;
                if (bindings.find(qualifier) != null) continue;
                const imported = (try cache.summaryByQualifiedName(qualifier, callee)) orelse continue;
                break :blk imported;
            }
            const local = (try cache.summaryByName(callee)) orelse continue;
            break :blk local.*;
        };
        if (!summary.may_grow_collections) continue;

        // A growing callee only invalidates the loop's pointer when it
        // reaches the ITERATED storage.  Disjoint effects — its own
        // list, an unrelated field of the same owner — move nothing.
        const call_rp = matchParen(tags, t + 1, end) orelse {
            try reportCallee(gpa, problems, tree, t, callee, recv.text(tree));
            continue;
        };
        if (!try calleeMayReallocateReceiver(
            scratch,
            tree,
            cache,
            proto,
            body,
            recv,
            &summary,
            t + 2,
            call_rp - 1,
        )) {
            t = call_rp;
            continue;
        }

        if (!(capture_by_value and callImmediatelyReturns(tags, t + 1, end))) {
            try reportCallee(gpa, problems, tree, t, callee, recv.text(tree));
        }
        t = call_rp;
    }
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

/// A local is private only when its initializer proves fresh storage and
/// no intervening use can publish or replace that storage.
const ReceiverRoot = union(enum) {
    private,
    shared,
};

/// Reading an integer field by value cannot publish the containing storage.
/// Addresses and assignment targets are not reads, even through grouping.
fn integerFieldReadEnd(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    token: Ast.TokenIndex,
) !?Ast.TokenIndex {
    const resolver = cache.zls orelse return null;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(node) != token) continue;
        const info = resolver.intInfo(node) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => null,
        };
        if (info == null) continue;
        const end = tree.lastToken(node);
        for (tree.nodes.items(.tag), 0..) |parent_tag, parent_raw| {
            const parent: Ast.Node.Index = @enumFromInt(parent_raw);
            const operand = switch (parent_tag) {
                .address_of => tree.nodeData(parent).node,
                .assign_destructure => parent,
                else => if (std.mem.startsWith(u8, @tagName(parent_tag), "assign"))
                    tree.nodeData(parent).node_and_node[0]
                else
                    continue,
            };
            if (tree.firstToken(operand) <= token and tree.lastToken(operand) >= end) return null;
        }
        return end;
    }
    return null;
}

fn localStorageIsPrivate(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    body: Ast.Node.Index,
    binding: *const local_bindings.Binding,
    recv: Receiver,
    until: Ast.TokenIndex,
) !bool {
    if (binding.name_token < tree.firstToken(body) or binding.rhs_last >= recv.first) return false;
    var claim: fn_summary.FreshClaim = .{
        .first = binding.rhs_first,
        .last = binding.rhs_last,
    };
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        const declaration = tree.fullVarDecl(node) orelse continue;
        if (declaration.ast.mut_token + 1 != binding.name_token) continue;
        if (declaration.ast.type_node.unwrap()) |type_node| {
            claim.type_first = tree.firstToken(type_node);
            claim.type_last = tree.lastToken(type_node);
        }
        break;
    }
    if (!try cache.provesFreshStorage(claim)) return false;

    const tags = tree.tokens.items(.tag);
    // A receiver borrowed by the current loop must not publish element
    // addresses through a pointer capture. A different grow receiver is not
    // the loop input and has no capture to inspect here.
    if (tags[recv.last + 1] == .period and tags[recv.last + 2] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(recv.last + 2), "items"))
    {
        var capture = recv.last + 3;
        while (capture < until and tags[capture] != .pipe) : (capture += 1) {}
        if (capture == until) return false;
        capture += 1;
        while (capture < until and tags[capture] != .pipe) : (capture += 1) {
            if (tags[capture] == .asterisk) return false;
        }
        if (capture == until) return false;
    }
    var token = binding.rhs_last + 1;
    while (token < until) : (token += 1) {
        if (tags[token] != .identifier or !std.mem.eql(u8, tree.tokenSlice(token), binding.name)) continue;
        if (token > 0 and tags[token - 1] == .period) continue;
        // The original loop condition borrows the buffer; it does not publish it.
        if (token == recv.first and tags[recv.last + 2] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(recv.last + 2), "items"))
        {
            token = recv.last + 2;
            continue;
        }
        if (try integerFieldReadEnd(tree, cache, token)) |end| {
            token = end;
            continue;
        }
        // Only declaration-proved single-element appends keep the storage
        // private. Header copies, field writes and opaque calls do not.
        var private_use = false;
        for (tree.nodes.items(.tag), 0..) |_, raw| {
            const node: Ast.Node.Index = @enumFromInt(raw);
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node) orelse continue;
            if (tree.firstToken(call.ast.fn_expr) != token) continue;
            if (cache.stdCollectionAppendOf(call.ast.fn_expr, call.ast.params.len)) |append| {
                if (append != .no) {
                    private_use = true;
                    break;
                }
            }
            // Deferred std-list cleanup is not publication. An arbitrary
            // method named deinit carries no such proof.
            if (token == 0 or (tags[token - 1] != .keyword_defer and tags[token - 1] != .keyword_errdefer)) continue;
            const resolver = cache.zls orelse continue;
            const reference = (resolver.functionReference(call.ast.fn_expr) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => return false,
            }) orelse continue;
            const std_tree = switch (cache.std_list_tree) {
                .known => |known| known,
                else => continue,
            };
            if (reference.tree != std_tree) continue;
            if (!std.mem.eql(u8, std_tree.tokenSlice(reference.fn_token + 1), "deinit")) continue;
            private_use = true;
            break;
        }
        if (!private_use) return false;
    }
    return true;
}

fn receiverOwner(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    bindings: *const local_bindings.LocalBindings,
    body: Ast.Node.Index,
    recv: Receiver,
    until: Ast.TokenIndex,
) !ReceiverRoot {
    const root = tree.tokenSlice(recv.first);
    const binding = bindings.find(root) orelse return .shared;
    if (try localStorageIsPrivate(tree, cache, body, binding, recv, until)) return .private;
    return .shared;
}

/// Can the callee reallocate the buffer `for (recv.items)` walks?
///
/// Parameter names and embedded header-field paths do not prove different
/// allocations: callers can pass the same pointer twice or copy a list header.
/// Only an unpublished, declaration-proved fresh allocation is private.
///
/// An unproved initializer may return shared storage, including through an
/// opaque call with no arguments. Private storage requires an actual fresh
/// initializer and no intervening publication or rebinding.
fn calleeMayReallocateReceiver(
    scratch: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    recv: Receiver,
    summary: *const fn_summary.FnSummary,
    arg_start: Ast.TokenIndex,
    arg_end: Ast.TokenIndex,
) !bool {
    const tags = tree.tokens.items(.tag);
    const root = tree.tokenSlice(recv.first);
    const bindings = try cache.localBindings(proto, body);
    const owner = try receiverOwner(tree, cache, bindings, body, recv, arg_start);
    // Every grow is attributed to a parameter, and the list is empty:
    // whatever this callee reallocates, it owns.
    if (!summary.grows_unknown_path and summary.grow_paths.len == 0) return false;
    // A grow attributed to no parameter at all may be storage this
    // file followed only part of the way — including the storage an
    // untraceable local holds.
    if (summary.grows_unknown_path) return true;
    const args = try fn_summary.argOwners(scratch, tree, proto, bindings, null, arg_start, arg_end);
    switch (owner) {
        .private => {
            if (identAppearsIn(tree, tags, arg_start, arg_end, root)) return true;
            for (summary.grow_paths) |grown| {
                if (grown.param >= args.len) continue;
                if (args[grown.param] == .unknown) return true;
            }
            return false;
        },
        .shared => return true,
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

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    call_tok: Ast.TokenIndex,
    recv: []const u8,
    iterated: []const u8,
    method: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}.{s}` inside `for ({s}.items)` may reallocate the backing buffer — the loop's implicit slice pointer is invalidated; move the call outside the loop or capture needed data before growing",
        .{ recv, method, iterated },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, call_tok),
        .end = Pos.fromTokenEnd(tree, call_tok),
        .message = msg,
    });
}

fn reportCallee(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    call_tok: Ast.TokenIndex,
    callee: []const u8,
    recv: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}(...)` inside `for ({s}.items)` may grow a collection — if it reallocates the iterated slice, the loop's implicit pointer is invalidated; ensure `{s}` cannot grow `{s}` during iteration",
        .{ callee, recv, callee, recv },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, call_tok),
        .end = Pos.fromTokenEnd(tree, call_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "slice-loop-reentrant-grow: direct grow on iterated list fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\pub fn buggy(list: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        list.append(std.heap.page_allocator, 99) catch {};
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: bare callee with may_grow fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn grow(list: *List) void {
        \\    list.append(std.heap.page_allocator, 1) catch {};
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
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\pub fn safe(list: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\    }
        \\    list.append(std.heap.page_allocator, 99) catch {};
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: direct append through an aliased parameter fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\pub fn walk(a: *List, b: *List) void {
        \\    for (a.items) |item| {
        \\        b.append(std.heap.page_allocator, item) catch {};
        \\    }
        \\}
        \\pub fn aliased(list: *List) void { walk(list, list); }
        \\
    );
}

test "slice-loop-reentrant-grow: direct append through a copied field header fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Pair = struct { input: List, output: List };
        \\pub fn walk(pair: *Pair) void {
        \\    for (pair.input.items) |item| {
        \\        pair.output.append(std.heap.page_allocator, item) catch {};
        \\    }
        \\}
        \\pub fn aliased(list: List) void {
        \\    var pair = Pair{ .input = list, .output = list };
        \\    walk(&pair);
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: direct append to a fresh private output is safe" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\pub fn copy(input: *const List) !List {
        \\    var output: List = .empty;
        \\    for (input.items) |item| {
        \\        try output.append(std.heap.page_allocator, item);
        \\    }
        \\    return output;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a private receiver's named append can grow globals" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\var shared: List = .empty;
        \\const Trap = struct {
        \\    items: []u32,
        \\    capacity: usize,
        \\    fn append(self: *Trap, gpa: std.mem.Allocator, value: u32) !void {
        \\        _ = self;
        \\        try shared.append(gpa, value);
        \\    }
        \\};
        \\pub fn walk() !void {
        \\    var output = Trap{ .items = &.{}, .capacity = 0 };
        \\    for (shared.items) |item| {
        \\        try output.append(std.heap.page_allocator, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a standard slice comparison does not grow borrowed storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList([]const u8);
        \\fn matches(a: []const u8, b: []const u8) bool {
        \\    return std.mem.eql(u8, a, b);
        \\}
        \\pub fn contains(list: *const List, needle: []const u8) bool {
        \\    for (list.items) |item| {
        \\        if (matches(item, needle)) return true;
        \\    }
        \\    return false;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a renamed standard comparator retains its declaration effect" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList([]const u8);
        \\const compare = std.mem.eql;
        \\fn matches(a: []const u8, b: []const u8) bool {
        \\    return compare(u8, a, b);
        \\}
        \\pub fn contains(list: *const List, needle: []const u8) bool {
        \\    for (list.items) |item| {
        \\        if (matches(item, needle)) return true;
        \\    }
        \\    return false;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a project comparator can grow shared storage" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList([]const u8);
        \\var shared: List = .empty;
        \\const fake = struct {
        \\    const mem = struct {
        \\        fn eql(comptime T: type, a: []const T, b: []const T) bool {
        \\            shared.append(std.heap.page_allocator, "changed") catch {};
        \\            return a.len == b.len;
        \\        }
        \\    };
        \\};
        \\fn matches(a: []const u8, b: []const u8) bool {
        \\    return fake.mem.eql(u8, a, b);
        \\}
        \\pub fn contains(needle: []const u8) bool {
        \\    for (shared.items) |item| {
        \\        if (matches(item, needle)) return true;
        \\    }
        \\    return false;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: reading a private list length does not publish storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\pub fn copy(input: *const List) !List {
        \\    var output: List = .empty;
        \\    if (output.items.len == 0) {
        \\        for (input.items) |item| {
        \\            try output.append(std.heap.page_allocator, item);
        \\        }
        \\    }
        \\    return output;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: deferred error cleanup does not publish a private list" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\pub fn copy(input: *const List) !List {
        \\    var output: List = .empty;
        \\    errdefer output.deinit(std.heap.page_allocator);
        \\    for (input.items) |item| {
        \\        try output.append(std.heap.page_allocator, item);
        \\    }
        \\    return output;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a grouped scalar field address can publish its list header" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn link(capacity: *usize, input: *const List) void {
        \\    const output: *List = @fieldParentPtr("capacity", capacity);
        \\    output.* = input.*;
        \\}
        \\pub fn copy(input: *const List) !List {
        \\    var output: List = .empty;
        \\    link(&((output.capacity)), input);
        \\    for (input.items) |item| {
        \\        try output.append(std.heap.page_allocator, item);
        \\    }
        \\    return output;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a compiler-owned root getter preserves token storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn isIdentifier(tree: *const std.zig.Ast, token: std.zig.Ast.TokenIndex) bool {
        \\    return tree.tokenTag(token) == .identifier;
        \\}
        \\pub fn count(tree: *const std.zig.Ast) usize {
        \\    var total: usize = 0;
        \\    for (tree.tokens.items(.tag), 0..) |_, index| {
        \\        if (isIdentifier(tree, @intCast(index))) total += 1;
        \\    }
        \\    return total;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an aliased compiler getter preserves node storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const nodeTag = std.zig.Ast.nodeTag;
        \\fn isIdentifier(tree: *const std.zig.Ast, node: std.zig.Ast.Node.Index) bool {
        \\    return nodeTag(tree, node) == .identifier;
        \\}
        \\pub fn count(tree: *const std.zig.Ast) usize {
        \\    var total: usize = 0;
        \\    for (tree.nodes.items(.tag), 0..) |_, index| {
        \\        if (isIdentifier(tree, @enumFromInt(index))) total += 1;
        \\    }
        \\    return total;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: indirect builtin invocation retains callback growth" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Callback = *const fn (*List, u32) void;
        \\fn invoke(list: *List, value: u32, callback: Callback) void {
        \\    @call(.auto, callback, .{ list, value });
        \\}
        \\pub fn walk(list: *List, callback: Callback) void {
        \\    for (list.items) |value| {
        \\        invoke(list, value, callback);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a named argument tuple retains callback growth" {
    // The tuple is a binding, not a literal in the `@call`, and a
    // binding that names a list says nothing about what the callee
    // does with it.  The invocation is still an invocation.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Callback = *const fn (*List, u32) void;
        \\fn invoke(list: *List, value: u32, callback: Callback) void {
        \\    const args = .{ list, value };
        \\    @call(.auto, callback, args);
        \\}
        \\pub fn walk(list: *List, callback: Callback) void {
        \\    for (list.items) |value| {
        \\        invoke(list, value, callback);
        \\        }
        \\    }
        \\
    );
}

test "slice-loop-reentrant-grow: a grouped callback expression retains callback growth" {
    // Parentheses around the callee change nothing about who runs.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Callback = *const fn (*List, u32) void;
        \\fn invoke(list: *List, value: u32, callback: Callback) void {
        \\    (callback)(list, value);
        \\}
        \\pub fn walk(list: *List, callback: Callback) void {
        \\    for (list.items) |value| {
        \\        invoke(list, value, callback);
        \\        }
        \\    }
        \\
    );
}

test "slice-loop-reentrant-grow: a reflected callback choice retains callback growth" {
    // `@field` picks the callee at runtime, so the name the call site
    // spells is a binding, not a declaration: nothing about the
    // storage the callee receives can be read off this syntax.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Callback = *const fn (*List, u32) void;
        \\fn invoke(list: *List, value: u32, callback: Callback) void {
        \\    const holder = .{ .apply = callback };
        \\    const apply = @field(holder, "apply");
        \\    apply(list, value);
        \\}
        \\pub fn walk(list: *List, callback: Callback) void {
        \\    for (list.items) |value| {
        \\        invoke(list, value, callback);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an argument-less callback still reaches hidden storage" {
    // Nothing is handed over, and that is not the same as nothing
    // happening: the callee is opaque and may append to `shared`.  An
    // empty argument list must not read as proof that the loop's own
    // buffer is untouched.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\var shared: List = .empty;
        \\const Sinker = *const fn () void;
        \\fn invoke(sink: Sinker) void {
        \\    @call(.auto, sink, .{});
        \\}
        \\pub fn walk(list: *List, sink: Sinker) void {
        \\    for (list.items) |value| {
        \\        _ = value;
        \\        invoke(sink);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a grouped callback with no arguments still reaches hidden storage" {
    // The same shape without `@call`: a runtime-chosen callee handed
    // nothing.  Charging only the function-pointer parameter would say
    // the invocation touches this fn's own storage and nothing else,
    // and `shared` is exactly the buffer it can move.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\var shared: List = .empty;
        \\const Sinker = *const fn () void;
        \\fn invoke(sink: Sinker) void {
        \\    (sink)();
        \\}
        \\pub fn walk(list: *List, sink: Sinker) void {
        \\    for (list.items) |value| {
        \\        _ = value;
        \\        invoke(sink);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an actual callee that grows a global is still reached" {
    // Resolving the callee to its real declaration must not read as
    // "this call grows nothing": the declaration grows `shared`, which
    // is storage this caller never handed over and this loop never
    // walks — and a fn that can move a buffer is still a fn that can
    // move one.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\var shared: List = .empty;
        \\fn helper(list: *List, value: u32) void {
        \\    shared.append(std.heap.page_allocator, value) catch {};
        \\    _ = list;
        \\}
        \\pub fn walk(list: *List) void {
        \\    for (list.items) |value| {
        \\        helper(list, value);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an implicitly passed receiver maps onto the caller's list" {
    // `grow` receives its receiver implicitly, so its parameter zero is
    // the receiver EXPRESSION, not the first written argument.  Reading
    // it any other way would aim the growth at `value`.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn grow(self: *List, value: u32) void {
        \\    self.append(std.heap.page_allocator, value) catch {};
        \\}
        \\fn relay(list: *List, value: u32) void {
        \\    grow(list, value);
        \\}
        \\pub fn walk(list: *List) void {
        \\    for (list.items) |value| {
        \\        relay(list, value);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a copied header handed to an actual callee still reaches the loop" {
    // The declaration is real, but the storage it is handed is a COPY
    // of this fn's own header: it shares the buffer, so the growth
    // lands on the one the loop walks.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn grow(list: *List, value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *List) void {
        \\    var copy = list.*;
        \\    for (copy.items) |value| {
        \\        grow(&copy, value);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an actual callee on proven fresh storage stays private" {
    // The mirror of the copied header: `mine` is proved built here, so
    // the same real declaration moves nothing this fn was handed.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn grow(list: *List, value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(gpa: std.mem.Allocator) !void {
        \\    var mine = try List.initCapacity(gpa, 1);
        \\    defer mine.deinit(gpa);
        \\    for (mine.items) |value| {
        \\        grow(&mine, value);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an uncalled declaration and a grouped conditional do not fire" {
    // A declaration this file declares but never calls grows nothing
    // on this path, and a parenthesised `if` is an expression, not an
    // invocation.  Neither reaches the buffer the loop walks.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn neverCalled(list: *List, value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn count(tree: *const std.zig.Ast) usize {
        \\    var total: usize = 0;
        \\    for (tree.tokens.items(.tag), 0..) |_, index| {
        \\        total += (if (index == 0) @as(usize, 1) else @as(usize, 0));
        \\    }
        \\    return total;
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: different parameters can hold the same list" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn growOther(other: *List) void {
        \\    other.append(std.heap.page_allocator, 1) catch {};
        \\}
        \\pub fn safe(list: *List, other: *List) void {
        \\    for (list.items) |item| {
        \\        _ = item;
        \\        growOther(other);
        \\    }
        \\}
        \\pub fn aliased(list: *List) void { safe(list, list); }
        \\
    );
}

test "slice-loop-reentrant-grow: may_grow callee passed recv fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn mayGrow(list: *List, x: u32) void {
        \\    _ = x;
        \\    list.append(std.heap.page_allocator, 1) catch {};
        \\}
        \\pub fn buggy(list: *List) void {
        \\    for (list.items) |item| {
        \\        mayGrow(list, item);
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

test "slice-loop-reentrant-grow: matching nested receivers ignore token whitespace" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Tally = struct { entries: std.ArrayList(u32) };
        \\fn add(tally: *Tally) void {
        \\    for (tally . entries . items) |entry| {
        \\        tally.entries.append(std.heap.page_allocator, entry) catch {};
        \\    }
        \\}
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
    );
}

test "slice-loop-reentrant-grow: a const view of the owner cannot reallocate the iterated list" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Tally = struct { entries: std.ArrayList(u32) };
        \\fn growOwnList(tally: *const Tally, entry: u32) void {
        \\    var scratch: std.array_list.Managed(u32) = std.array_list.Managed(u32).init(std.heap.page_allocator);
        \\    defer scratch.deinit();
        \\    scratch.append(entry) catch {};
        \\    _ = tally;
        \\}
        \\pub fn walk(tally: *const Tally, entry: u32) void {
        \\    for (tally.entries.items) |item| {
        \\        growOwnList(tally, item + entry);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a mutable owner handed to the same callee still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Tally = struct { entries: std.ArrayList(u32) };
        \\fn growOwnList(tally: *Tally, entry: u32) void {
        \\    tally.entries.append(std.heap.page_allocator, entry) catch {};
        \\}
        \\pub fn walk(tally: *Tally) void {
        \\    for (tally.entries.items) |item| {
        \\        growOwnList(tally, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a value copy of the owner grows only its own list" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Tally = struct { entries: std.array_list.Managed(u32) };
        \\fn collect(source: Tally, entry: u32) void {
        \\    var sink: Tally = .{ .entries = std.array_list.Managed(u32).init(std.heap.page_allocator) };
        \\    defer sink.entries.deinit();
        \\    sink.entries.append(@intCast(source.entries.items.len)) catch {};
        \\    _ = entry;
        \\}
        \\pub fn walk(source: Tally) void {
        \\    for (source.entries.items) |item| {
        \\        collect(source, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: the address of a value owner reaches the iterated list" {
    // `owner` is this fn's own copy of the header it was handed: it
    // shares the buffer, so growing through `&owner` reallocates what
    // the loop walks.  A by-value owner is a copy, not a safety proof
    // — and `&source` on an immutable parameter would not even be the
    // mutable pointer the callee takes.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Tally = struct { entries: std.ArrayList(u32) };
        \\fn collect(source: *Tally, entry: u32) void {
        \\    source.entries.append(std.heap.page_allocator, entry) catch {};
        \\}
        \\pub fn walk(source: Tally) void {
        \\    var owner: Tally = source;
        \\    for (owner.entries.items) |item| {
        \\        collect(&owner, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: reading a field of the owner aliases nothing" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Tree = struct { nodes: std.ArrayList(u32) };
        \\fn record(count: usize, node: u32) void {
        \\    var scratch: std.array_list.Managed(u32) = std.array_list.Managed(u32).init(std.heap.page_allocator);
        \\    defer scratch.deinit();
        \\    scratch.append(node) catch {};
        \\    _ = count;
        \\}
        \\pub fn walk(tree: *Tree) void {
        \\    for (tree.nodes.items) |node| {
        \\        record(tree.nodes.items.len, node);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a computed argument reaches no owner storage" {
    // `firstIndex(tree)` evaluates to a number; the callee is handed
    // no address of the list, so growing anything it owns leaves the
    // iterated buffer in place.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Tree = struct { nodes: std.ArrayList(u32) };
        \\fn firstIndex(tree: *Tree) usize { return tree.nodes.items.len; }
        \\fn record(index: usize, node: u32) void {
        \\    var scratch: std.array_list.Managed(u32) = std.array_list.Managed(u32).init(std.heap.page_allocator);
        \\    defer scratch.deinit();
        \\    scratch.append(node) catch {};
        \\    _ = index;
        \\}
        \\pub fn walk(tree: *Tree) void {
        \\    for (tree.nodes.items) |node| {
        \\        record(firstIndex(tree), node);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: the iterated list's own header address still fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Tree = struct { nodes: std.ArrayList(u32) };
        \\fn record(list: *std.ArrayList(u32), node: u32) void {
        \\    list.append(std.heap.page_allocator, node) catch {};
        \\}
        \\pub fn walk(tree: *Tree) void {
        \\    for (tree.nodes.items) |node| {
        \\        record(&tree.nodes, node);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: shared state handed to the callee still fires" {
    // The receiver root is a container-level `var`, not a binding of
    // this fn, so the argument is what carries the alias.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\var pending: std.ArrayList(u32) = undefined;
        \\fn drain(list: *std.ArrayList(u32), entry: u32) void {
        \\    list.append(std.heap.page_allocator, entry) catch {};
        \\}
        \\pub fn walk() void {
        \\    for (pending.items) |item| {
        \\        drain(&pending, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a copied list header still reallocates the shared buffer" {
    // `var copy = list.*` copies the ArrayList header, not its buffer.
    // Appending through the copy can reallocate — and free — the very
    // allocation the loop is walking, so a by-value copy is not a
    // safety proof.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn growCopy(list: *List, value: u32) void {
        \\    var copy: List = list.*;
        \\    copy.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *List) void {
        \\    for (list.items) |item| {
        \\        growCopy(list, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a const wrapper holding a mutable list still fires" {
    // `*const View` freezes the wrapper, not what it points at: the
    // callee appends through `view.entries`, which reallocates the
    // buffer the loop walks.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const View = struct { entries: *std.ArrayList(u32) };
        \\fn growThroughView(view: *const View, value: u32) void {
        \\    view.entries.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(view: *const View) void {
        \\    for (view.entries.items) |item| {
        \\        growThroughView(view, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an alias reached through a delegating callee fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn appendInner(list: *List, value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\fn appendOuter(list: *List, value: u32) void {
        \\    appendInner(list, value);
        \\}
        \\pub fn walk(list: *List) void {
        \\    for (list.items) |item| {
        \\        appendOuter(list, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an argument with unresolved aliasing is not treated as unrelated" {
    // `@constCast` hands the callee a pointer this file cannot trace
    // back to the iterated list, so the grow is not proven disjoint.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn growList(list: *List, value: u32) void {
        \\    list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *List, view: *const List) void {
        \\    for (list.items) |item| {
        \\        growList(@constCast(view), item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: embedded headers can hold the same allocation" {
    // Copying the header does not create an independent buffer.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Oracle = struct {
        \\    tree: std.ArrayList(u32),
        \\    aliases: std.ArrayList(u32),
        \\};
        \\fn recordAlias(oracle: *Oracle, value: u32) void {
        \\    oracle.aliases.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(oracle: *Oracle) void {
        \\    for (oracle.tree.items) |node| {
        \\        recordAlias(oracle, node);
        \\    }
        \\}
        \\pub fn aliased(oracle: *Oracle) void {
        \\    oracle.aliases = oracle.tree;
        \\    walk(oracle);
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: growing the iterated field of the same owner fires" {
    // The mirror of the case above: same owner, same parameter, but
    // the grow lands on the field the loop is walking.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Oracle = struct {
        \\    tree: std.ArrayList(u32),
        \\    aliases: std.ArrayList(u32),
        \\};
        \\fn recordNode(oracle: *Oracle, value: u32) void {
        \\    oracle.tree.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(oracle: *Oracle) void {
        \\    for (oracle.tree.items) |node| {
        \\        recordNode(oracle, node);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: two pointer fields may hold the same list" {
    // `a` and `b` are different FIELDS, but each points at a list, and
    // nothing here says they point at different ones: the callee's
    // append can move the buffer the loop is walking.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Pair = struct {
        \\    a: *std.ArrayList(u32),
        \\    b: *std.ArrayList(u32),
        \\};
        \\fn growA(pair: *Pair, value: u32) void {
        \\    pair.a.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(pair: *Pair) void {
        \\    for (pair.b.items) |item| {
        \\        growA(pair, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a header copied from a file-level list is not owned" {
    // `var copy = shared;` names neither a parameter nor a local of the
    // callee, yet the copy shares a file-level list's buffer — and that
    // list may be the very list a caller is walking.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\var shared: std.ArrayList(u32) = undefined;
        \\fn growShared(value: u32) void {
        \\    var copy: std.ArrayList(u32) = shared;
        \\    copy.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growShared(item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a header returned by a call is not owned" {
    // Same shape, one call deeper: `currentShared()` returns a header
    // this file cannot place, so growing the copy grows storage that
    // somebody else can still be walking.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\var shared: std.ArrayList(u32) = undefined;
        \\fn currentShared() std.ArrayList(u32) { return shared; }
        \\fn growShared(value: u32) void {
        \\    var copy: std.ArrayList(u32) = currentShared();
        \\    copy.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growShared(item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a literal of a constructor's result keeps its own growth" {
    // The mirror of the two above: every field the literal supplies is
    // a header this very expression built, so growing it moves nothing
    // the caller holds.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Bag = struct { items: std.ArrayList(u32) };
        \\fn recordOwn(value: u32) !void {
        \\    var scratch: Bag = .{ .items = try std.ArrayList(u32).initCapacity(std.heap.page_allocator, 0) };
        \\    defer scratch.items.deinit(std.heap.page_allocator);
        \\    scratch.items.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        recordOwn(item) catch {};
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an unresolved callee handed the iterated list is not disjoint" {
    // `keepName` is an opaque function pointer this file has no
    // declaration to read behind, and its name says nothing about
    // growth.  What decides this is that the file cannot resolve it
    // AND the call hands it the very list the loop walks.  An
    // arbitrary function can grow what it is given, so not seeing it
    // is not proof that it will not.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Keep = *const fn (*List, u32) void;
        \\fn grow(list: *List, value: u32, keepName: Keep) void {
        \\    keepName(list, value);
        \\}
        \\pub fn walk(list: *List, keepName: Keep) void {
        \\    for (list.items) |item| {
        \\        grow(list, item, keepName);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a callee behind a qualifier this file cannot read is not disjoint" {
    // `helpers` is a namespace with no `@import` declaration behind
    // it, so the free function at `helpers.keepName` is a name this
    // file has no declaration to resolve — and the call hands it the
    // very list the loop walks.  Not seeing it is a blind spot, not
    // evidence that it leaves the buffer alone.  The case where the
    // qualifier IS a readable module is covered end to end against a
    // real second file in lib.zig.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const helpers = struct {
        \\    pub fn keepName(list: *std.ArrayList(u32), value: u32) void {
        \\        _ = list;
        \\        _ = value;
        \\    }
        \\};
        \\fn grow(list: *std.ArrayList(u32), value: u32) void {
        \\    helpers.keepName(list, value);
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        grow(list, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a type whose init returns a global is not proof of safety" {
    // The name is the one a real container constructor has, and the
    // result is a copy of a file-level list's header — so growing it
    // can still move a buffer somebody else is walking.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\var shared: std.ArrayList(u32) = undefined;
        \\const Fake = struct {
        \\    list: std.ArrayList(u32),
        \\    pub fn init(_: void) Fake {
        \\        return .{ .list = shared };
        \\    }
        \\};
        \\fn growShared(value: u32) void {
        \\    var copy: Fake = Fake.init({});
        \\    copy.list.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growShared(item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a type whose init builds its own list is proof of safety" {
    // The mirror of the case above: this `init` returns a header it
    // just constructed, so growing it moves nothing the caller holds.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Real = struct {
        \\    list: std.array_list.Managed(u32),
        \\    pub fn init(gpa: std.mem.Allocator) Real {
        \\        return .{ .list = std.array_list.Managed(u32).init(gpa) };
        \\    }
        \\};
        \\fn growOwnList(value: u32) void {
        \\    var copy: Real = Real.init(std.heap.page_allocator);
        \\    defer copy.list.deinit();
        \\    copy.list.append(value) catch {};
        \\}
        \\pub fn walk(list: *std.ArrayList(u32)) void {
        \\    for (list.items) |item| {
        \\        growOwnList(item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a growing callee does not reach a local's own list" {
    // The resolved constructor allocates private storage. Passing only an
    // unrelated header and a scalar leaves that allocation unreachable.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(gpa: std.mem.Allocator, out: *List) !void {
        \\    var mine = try List.initCapacity(gpa, 1);
        \\    defer mine.deinit(gpa);
        \\    mine.append(gpa, 1) catch {};
        \\    for (mine.items) |item| {
        \\        record(out, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a callee handed the local itself still fires" {
    // The mirror of the case above: the call names the local, so the
    // callee holds the header the loop is walking.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(gpa: std.mem.Allocator) void {
        \\    var mine: List = .empty;
        \\    defer mine.deinit(gpa);
        \\    mine.append(gpa, 1) catch {};
        \\    for (mine.items) |item| {
        \\        record(&mine, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a local built from a parameter keeps that parameter reachable" {
    // `mine` is a header this file cannot trace, but the call that
    // produced it was handed `backing` — so a callee that grows
    // `backing` moves the very buffer the loop walks.  Naming the
    // sources the initializer reached is what keeps this firing.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn viewOf(backing: *List) *List { return backing; }
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(backing: *List) void {
        \\    const mine = viewOf(backing);
        \\    for (mine.items) |item| {
        \\        record(backing, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: a local built from a file-level list keeps reporting" {
    // Shared state: `view` holds a global's header, which any callee
    // can name on its own — no argument has to carry it.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\var shared: List = undefined;
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(out: *List) void {
        \\    var view: List = shared;
        \\    for (view.items) |item| {
        \\        record(out, item);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an unresolved callee handed another list is disjoint" {
    // An opaque callback can reach its arguments, but not an unpublished
    // allocation created by this function.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn record(out: *List, value: u32, keepName: *const fn (*List, u32) void) void {
        \\    keepName(out, value);
        \\}
        \\pub fn walk(gpa: std.mem.Allocator, out: *List, keepName: *const fn (*List, u32) void) !void {
        \\    var mine = try List.initCapacity(gpa, 1);
        \\    defer mine.deinit(gpa);
        \\    mine.append(gpa, 1) catch {};
        \\    for (mine.items) |item| {
        \\        record(out, item, keepName);
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: an opaque constructor may return shared storage" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\var shared: List = .empty;
        \\fn acquire() *List { return &shared; }
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(out: *List) void {
        \\    const view = acquire();
        \\    for (view.items) |item| {
        \\        record(out, item);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: publishing a fresh header before the call retains alias risk" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(gpa: std.mem.Allocator, out: *List) !void {
        \\    var mine = try List.initCapacity(gpa, 1);
        \\    defer mine.deinit(gpa);
        \\    mine.append(gpa, 1) catch {};
        \\    for (mine.items) |item| {
        \\        out.* = mine;
        \\        record(out, item);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: replacing a fresh buffer field retains alias risk" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(gpa: std.mem.Allocator, out: *List) !void {
        \\    var mine = try List.initCapacity(gpa, 1);
        \\    mine.items = out.items;
        \\    mine.capacity = out.capacity;
        \\    for (mine.items) |item| {
        \\        record(out, item);
        \\    }
        \\}
    );
}

test "slice-loop-reentrant-grow: declared std empty storage stays private after append" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(gpa: std.mem.Allocator, out: *List) void {
        \\    var mine: List = .empty;
        \\    defer mine.deinit(gpa);
        \\    mine.append(gpa, 1) catch {};
        \\    for (mine.items) |item| record(out, item);
        \\}
    );
}

test "slice-loop-reentrant-grow: an empty-named project constant may hold a shared header" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\const Factory = struct { pub var empty: List = .empty; };
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(out: *List) void {
        \\    const mine: List = Factory.empty;
        \\    for (mine.items) |item| record(out, item);
        \\}
    );
}

test "slice-loop-reentrant-grow: an element pointer can publish a fresh allocation" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const List = std.ArrayList(u32);
        \\fn record(out: *List, value: u32) void {
        \\    out.append(std.heap.page_allocator, value) catch {};
        \\}
        \\pub fn walk(gpa: std.mem.Allocator, out: *List) !void {
        \\    var mine = try List.initCapacity(gpa, 1);
        \\    defer mine.deinit(gpa);
        \\    mine.appendAssumeCapacity(1);
        \\    for (mine.items) |*item| {
        \\        out.* = .{ .items = @as(*[1]u32, @ptrCast(item))[0..], .capacity = 1 };
        \\        record(out, item.*);
        \\    }
        \\}
    );
}
