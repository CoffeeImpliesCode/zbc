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
//!      expression contains `<path>.items`, where `<path>` is the whole
//!      receiver chain (`origin.allocations`), not just its last field.
//!   2. Inside the loop body, scan for:
//!      a. Direct grow: `<path>.<growMethod>(` on the same receiver
//!         chain — fire.  A grown chain that spells a different object
//!         (`output.allocations` vs `origin.allocations`) is another
//!         list that merely shares a field name — skip.
//!      b. Bare call: `<fn>( ` (not preceded by `.`) — look up callee
//!         FnSummary; if `may_grow_collections`, fire.
//!   3. Fire at the call token.
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

        // Look for `<recv>.items` inside the for-condition parens.
        const recv = findItemsRecv(tree, t + 2, rp - 1) orelse continue;

        // Find the loop body `{...}` after the capture `|...|`.
        const body_start = findLoopBody(tags, rp + 1, last) orelse continue;
        const body_end = matchBrace(tags, body_start, last) orelse continue;

        // Scan the loop body for calls that may grow collections.
        const capture_by_value = loopCaptureByValue(tags, rp + 1, body_start);
        try checkLoopBody(gpa, tree, cache, scope, body_start + 1, body_end - 1, recv, capture_by_value, problems);

        // Skip past the loop body to avoid re-scanning its contents.
        t = body_end;
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
    var s: Ast.TokenIndex = start;
    while (s + 2 <= end) : (s += 1) {
        if (tags[s] != .identifier) continue;
        if (tags[s + 1] != .period) continue;
        if (tags[s + 2] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(s + 2), "items")) continue;
        return recvAt(tree, s);
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

/// True when `grown` is provably another object than the iterated
/// `iterated`: both chains are plain identifier paths with different roots,
/// and each root is a name nothing else can reach this body's other root
/// through — a parameter, or a local this body built from `.{}` and never
/// let go of (`isPrivateLocal`).  A shared field name proves nothing about
/// the object that owns it.  Anything else — chains fed by a call, index or
/// dereference, one root spelled twice, a local that may be an alias — stays
/// possibly-equal.
fn namesOtherObject(tree: *const Ast, scope: Scope, iterated: Recv, grown: Recv) bool {
    if (iterated.chained or grown.chained) return false;
    const iterated_root = tree.tokenSlice(iterated.first);
    const grown_root = tree.tokenSlice(grown.first);
    if (std.mem.eql(u8, iterated_root, grown_root)) return false;
    return independentRoot(tree, scope, iterated.first, grown_root) and
        independentRoot(tree, scope, grown.first, iterated_root);
}

/// `other` is the root of the list this one is compared with: a call that
/// is handed this root's address AND `other` could copy one list header
/// into the other, so such a call keeps the pair possibly-equal.
fn independentRoot(tree: *const Ast, scope: Scope, root: Ast.TokenIndex, other: []const u8) bool {
    const binding = scope.bindings.findAt(tree.tokenSlice(root), root) orelse return false;
    return switch (binding.origin) {
        .param => true,
        .literal => isPrivateLocal(tree, scope, binding, other),
        else => false,
    };
}

/// A local declared as exactly `.{}` whose storage no other name can hold:
/// its address is never kept (taking it as a call argument is allowed when
/// that call is not handed `other` — it can write the local, but has nothing
/// to copy the other list's header from), it is never named as a bare value
/// (a copy of a list header shares the buffer), and no field of it is
/// overwritten with a copy of another path.  Reads that cannot copy a list
/// header — a method call, `.items`, `.len`, `.capacity`, a comparison, a
/// negation — are fine.
fn isPrivateLocal(tree: *const Ast, scope: Scope, binding: *const local_bindings.Binding, other: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    if (binding.rhs_last != binding.rhs_first + 2 or tags[binding.rhs_first] != .period or
        tags[binding.rhs_first + 1] != .l_brace or tags[binding.rhs_first + 2] != .r_brace) return false;
    var t: Ast.TokenIndex = binding.name_token + 1;
    while (t <= scope.last) : (t += 1) {
        if (tags[t] != .identifier or !std.mem.eql(u8, tree.tokenSlice(t), binding.name)) continue;
        if (tags[t - 1] == .period) continue;
        if (tags[t - 1] == .ampersand) {
            if (!addressIsPlainCallArgument(tree, tags, scope, t - 1, other)) return false;
            continue;
        }
        if (t + 1 > scope.last or tags[t + 1] != .period) return false;
        // The end of the `a.b.c` chain.
        var end = t;
        while (end + 2 <= scope.last and tags[end + 1] == .period and tags[end + 2] == .identifier) end += 2;
        const next = if (end + 1 <= scope.last) tags[end + 1] else .semicolon;
        if (next == .l_paren) continue;
        if (next == .equal) {
            // `<local>.<field> = <path>;` copies the other path's contents.
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
        // A bare field value in a position that stores or passes it on.
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
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    scope: Scope,
    amp: Ast.TokenIndex,
    other: []const u8,
) bool {
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
    return !identAppearsIn(tree, tags, first, rp, other);
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
            std.mem.eql(u8, tree.tokenSlice(t), recv.name) and
            t + 3 <= end and
            tags[t + 1] == .period and
            tags[t + 2] == .identifier and
            tags[t + 3] == .l_paren)
        {
            const callee = tree.tokenSlice(t + 2);
            if (method_names.isArrayListGrowMethodName(callee) and
                !namesOtherObject(tree, scope, recv, recvAt(tree, t)))
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

        // Suppress when the iterated list's root object doesn't appear
        // anywhere in the call's argument list.  If the callee can't reach
        // the iterated collection (it isn't passed as an argument), it
        // cannot reallocate it — the slice pointer remains valid.  The
        // ROOT identifier is what a callee reaches a nested receiver
        // through (`grow(tally, e)` grows `tally.entries`), not the last
        // field name.
        const call_rp = matchParen(tags, t + 1, end) orelse {
            try reportCallee(gpa, problems, tree, t, callee, recv.name);
            continue;
        };
        if (!identAppearsIn(tree, tags, t + 2, call_rp - 1, tree.tokenSlice(recv.first))) {
            t = call_rp;
            continue;
        }

        // The callee's own verdict says WHICH storage it reallocates.  The
        // declaration the call really reaches (the type engine's answer, which
        // also reads an imported module) is preferred; a call it cannot
        // connect is read by name in this document, and failing that keeps
        // the summary's conservative default.
        const named = t == start or tags[t - 1] != .period;
        const verdict = (try grow_mod.calleeGrowVerdict(cache, if (named) t else t - 1)) orelse
            (if (named) try grow_mod.ownFnGrowVerdict(cache, callee) else null) orelse reading.verdict;
        // A `*const` parameter's storage cannot be reallocated through the
        // pointer a callee receives, so a call handed only that pointer
        // cannot move the list the loop walks.
        const const_root = !recv.chained and isConstPointerParam(tree, scope, recv.first);
        if (!verdictReachesIterated(tree, tags, t + 1, call_rp, recv, const_root, verdict)) {
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

/// True when `root` names a parameter declared `*const T`.  Storage reached
/// only through such a pointer cannot be reallocated by whoever receives it.
fn isConstPointerParam(tree: *const Ast, scope: Scope, root: Ast.TokenIndex) bool {
    const binding = scope.bindings.findAt(tree.tokenSlice(root), root) orelse return false;
    if (binding.origin != .param) return false;
    var params = scope.proto.iterate(tree);
    while (params.next()) |param| {
        const name_token = param.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), binding.name)) continue;
        const type_node = param.type_expr orelse return false;
        const pointer = tree.fullPtrType(type_node) orelse return false;
        return pointer.size == .one and pointer.const_token != null;
    }
    return false;
}

/// True when argument `arg` passes the const pointer `root` itself, or the
/// address of a path below it (`root`, `&root.nodes`): a const pointer
/// either way.  A path read by value (`root.nodes`) copies a list header and
/// is not one.
fn handsOverConstPointer(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    arg: TokenSpan,
    root: []const u8,
) bool {
    var s = arg.first;
    const address = tags[s] == .ampersand;
    if (address) s += 1;
    if (s > arg.last or tags[s] != .identifier or !std.mem.eql(u8, tree.tokenSlice(s), root)) return false;
    if (s == arg.last) return true;
    if (!address) return false;
    var buffer: [path_capacity]u8 = undefined;
    return s + 2 <= arg.last and tags[s + 1] == .period and chainText(tree, tags, s + 2, arg.last, &buffer) != null;
}

/// True when `verdict` — which storage the callee reallocates, by parameter —
/// can move the iterated list through the call whose parentheses are `lp` and
/// `rp`.  The iterated list is `recv.first`'s root plus its field path.  A
/// grow charged to a parameter whose argument does not name that root moves
/// another object, and one charged to a field path that neither contains nor
/// lies inside the iterated field path moves another list of the same
/// object.  A `*const` root passed on as the pointer itself moves nothing.  A
/// grow the callee reaches through a name of its own, a handover it could not
/// root, an argument that is more than a plain path of the root, or a call
/// that does not pass the parameter at all stays possibly the iterated list.
fn verdictReachesIterated(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    lp: Ast.TokenIndex,
    rp: Ast.TokenIndex,
    recv: Recv,
    const_root: bool,
    verdict: grow_mod.GrowVerdict,
) bool {
    if (verdict.unknown) return true;
    const root = tree.tokenSlice(recv.first);
    for (verdict.unplaced) |param| {
        const arg = argumentSpan(tags, lp, rp, param) orelse return true;
        if (!identAppearsIn(tree, tags, arg.first, arg.last, root)) continue;
        if (const_root and handsOverConstPointer(tree, tags, arg, root)) continue;
        return true;
    }
    if (verdict.paths.len == 0) return false;
    var iterated_buffer: [path_capacity]u8 = undefined;
    var arg_buffer: [path_capacity]u8 = undefined;
    var full_buffer: [2 * path_capacity + 1]u8 = undefined;
    for (verdict.paths) |gp| {
        const arg = argumentSpan(tags, lp, rp, gp.param) orelse return true;
        if (!identAppearsIn(tree, tags, arg.first, arg.last, root)) continue;
        if (const_root and handsOverConstPointer(tree, tags, arg, root)) continue;
        if (recv.chained) return true;
        const iterated: []const u8 = if (recv.first == recv.last)
            ""
        else
            chainText(tree, tags, recv.first + 2, recv.last, &iterated_buffer) orelse return true;
        // The argument must be exactly `[&]root(.field)*`.
        var s = arg.first;
        if (tags[s] == .ampersand) s += 1;
        if (s > arg.last or tags[s] != .identifier or !std.mem.eql(u8, tree.tokenSlice(s), root)) return true;
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

test "slice-loop-reentrant-grow: grow on different recv doesn't fire" {
    try testing.expectNoFire(check,
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

test "slice-loop-reentrant-grow: may_grow callee not passed recv doesn't fire" {
    try testing.expectNoFire(check,
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
    try testing.expectNoFire(check,
        \\const Output = struct { allocations: std.ArrayListUnmanaged(u32) = .empty };
        \\pub fn forward(gpa: std.mem.Allocator, output: *Output) !void {
        \\    var origin: Output = .{};
        \\    for (origin.allocations.items) |requirement| {
        \\        try output.allocations.append(gpa, requirement);
        \\    }
        \\}
        \\pub fn join(self: *Output, other: *const Output, gpa: std.mem.Allocator) !void {
        \\    for (other.allocations.items) |premise| {
        \\        try self.allocations.append(gpa, premise);
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
    try testing.expectNoFire(check,
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
    try testing.expectNoFire(check,
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

test "slice-loop-reentrant-grow: a callee that grows another list while the walked tree is const does not fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Ast = std.zig.Ast;
        \\const Problem = struct { line: u32 };
        \\fn report(gpa: std.mem.Allocator, problems: *std.ArrayListUnmanaged(Problem), tree: *const Ast, node: u32) !void {
        \\    try problems.append(gpa, .{ .line = tree.firstToken(@enumFromInt(node)) });
        \\}
        \\pub fn check(gpa: std.mem.Allocator, tree: *const Ast, problems: *std.ArrayListUnmanaged(Problem)) !void {
        \\    for (tree.nodes.items(.tag), 0..) |tag, index| {
        \\        _ = tag;
        \\        try report(gpa, problems, tree, @intCast(index));
        \\    }
        \\}
        \\
    );
}

test "slice-loop-reentrant-grow: the same callee fires when the walked tree is mutable" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Ast = std.zig.Ast;
        \\const Problem = struct { line: u32 };
        \\fn report(gpa: std.mem.Allocator, problems: *std.ArrayListUnmanaged(Problem), tree: *Ast, node: u32) !void {
        \\    try problems.append(gpa, .{ .line = tree.firstToken(@enumFromInt(node)) });
        \\}
        \\pub fn check(gpa: std.mem.Allocator, tree: *Ast, problems: *std.ArrayListUnmanaged(Problem)) !void {
        \\    for (tree.nodes.items(.tag), 0..) |tag, index| {
        \\        _ = tag;
        \\        try report(gpa, problems, tree, @intCast(index));
        \\    }
        \\}
        \\
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
