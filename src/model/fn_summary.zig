//! Per-fn behavioral summary, inferred from the body (purely
//! syntactic).  No annotations are read — the author overrides
//! the tool's inferred belief via `// zbc-disable-line:` suppressions,
//! not by asserting alternative semantics.
//!
//! Summary fields are deliberately COARSE.  Each one answers a
//! specific question a downstream consumer asks:
//!
//!   returns                — "does the call leak ownership to the caller?"
//!   takes_ownership_of     — "does the call invalidate one of its args?"
//!   is_noreturn            — "does the call terminate the basic block?"
//!   allocates              — "does the body call into an allocator?"
//!
//! Anything inference can't reach is `.unknown` / null / false.
//! Consumers MUST treat `.unknown` as "assume nothing" — same as
//! today's `lowering_gap` conservative fallback.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../ast/tokens.zig");
const receiver_mod = @import("method_names.zig");

/// Result-shape classification.
pub const Returns = union(enum) {
    /// No lifetime constraint — value-typed return, primitive, etc.
    plain,
    /// Caller receives a tracked heap allocation (the body has an
    /// alloc / create / dupe call whose result feeds the return).
    heap,
    /// Caller owns the value but it isn't a tracked heap id (returned
    /// from a wrapper / opaque source).  Distinct from `.heap` so
    /// consumers know NOT to mint a HeapId.
    owned,
    /// Return value borrows from the named parameter (0-indexed).
    /// Caller's lifetime is bound to the param's.
    borrowed_from: u32,
    /// Couldn't classify — conservative.
    unknown,
};

/// A `<param>.<field>.<method>()` chain that a fn's body destroys.
/// Multiple entries per fn possible — `fn deinit(self) {
/// self.x.free(); self.y.close(); }` emits two.  The `method` slot
/// lets post-inference filters check the SPECIFIC method's existence
/// on the field's type (rather than just "any cleanup method").
pub const FieldFree = struct {
    /// 0-indexed param whose `.<field>` is freed (0 = receiver).
    param: u32,
    /// Field name (slice into source — caller keeps tree alive).
    field: []const u8,
    /// Method name that matched (e.g. "deinit" / "close").  Slice
    /// into source.  Used by FileCache.filterMayFreeFields to verify
    /// the field's TYPE actually has this method before propagating.
    method: []const u8,
};

pub const FnSummary = struct {
    returns: Returns = .unknown,
    /// If non-null, the call site invalidates the value passed at
    /// this parameter index — i.e. the callee takes ownership of
    /// that arg.
    takes_ownership_of: ?u32 = null,
    /// Body returns via `unreachable` / calls `@panic` / signature
    /// says `noreturn`.
    is_noreturn: bool = false,
    /// Body invokes an alloc-class call somewhere.  Coarse — doesn't
    /// distinguish allocator identities.
    allocates: bool = false,
    /// `<param>.<field>.<destroy_method>()` chains in the body — one
    /// entry per chain.  Lets call sites emit a `.field_heap_free`
    /// per chain.  Slice is owned by the FnSummaryCache arena.
    may_free_fields: []const FieldFree = &.{},
    /// Field names that a constructor allocates and stores into the
    /// returned struct literal — i.e. `return .{ .X = alloc(), ... }`.
    /// Lets call sites mint synthetic `field_assign(local, X,
    /// .heap_alloc)` so subsequent `local.X` reads see correct UAF
    /// state.  Slice is owned by the FnSummaryCache arena.
    result_heap_fields: []const []const u8 = &.{},
    /// Body contains `<x>.create(<containing-type>)` or
    /// `<x>.create(Self)` — i.e. allocates a heap instance of its
    /// own type.  Filled when the containing type is known; null
    /// when the fn is top-level (no containing type).
    heap_allocates_self: bool = false,
    /// True iff EVERY return statement's expression is structurally
    /// independent of every parameter — no param name appears in any
    /// return.  Used by borrowed-slice analysis to suppress
    /// "<deferred>.field passed to F(...)" fires when F's result
    /// can't carry a borrow back from any of its args.  Conservative:
    /// false when any return expression touches a param OR when the
    /// fn's body has a non-statement return path we can't see.
    result_independent_of_args: bool = false,
    /// Per-param return-embedding bitmask.  Bit `i` is set when param
    /// index `i` (0-based) appears as an unqualified identifier in at
    /// least one non-recursive return expression.  Bit 31 (`SAW_RETURN_BIT`)
    /// is set when the body has at least one `return` statement at all
    /// — lets callers distinguish "no returns seen" from "saw returns,
    /// no params embedded".  Only bits 0–30 track params; functions
    /// with >30 params fall back to conservative (bit never cleared).
    /// Zero means "no return statements found" (conservative, not
    /// "independent").  Used by borrowed-slice analysis for per-arg
    /// suppression when the overall `result_independent_of_args` is
    /// false because a DIFFERENT param appears in returns.
    result_params_in_return: u32 = 0,
    /// True iff this fn (or any fn it transitively calls in the same
    /// file) directly invokes an ArrayList-grow method — i.e. a call
    /// that may reallocate the backing buffer and invalidate existing
    /// element pointers / slices.  Set by direct body scan in
    /// `inferFromBody`; propagated transitively by
    /// `FileCache.resolveTransitiveTakes` Phase 5.
    /// Consumed by `slice-loop-reentrant-grow`.
    may_grow_collections: bool = false,
    /// True iff this fn (or any callee it reaches transitively within the
    /// same file) calls a JSC method that may trigger garbage collection,
    /// making raw slice/pointer borrows from ArrayBuffers or JSStrings
    /// potentially invalid after the call returns.
    /// Set by direct body scan in `inferFromBody`; propagated transitively
    /// by `FileCache.resolveTransitiveTakes` Phase 6.
    /// Consumed by `arraybuffer-slice-without-pin`.
    may_invoke_gc: bool = false,
    /// True iff this fn is registered (or transitively reachable from a
    /// function registered) as an at-exit callback, signal handler, or
    /// cross-thread task — meaning it may run on a non-main thread.
    /// Set by direct body scan (detects registration-site bare calls);
    /// propagated transitively by Phase 7.
    /// Consumed by `exit-callback-cross-thread`.
    may_run_on_any_thread: bool = false,
    /// Internal flag: true iff FileCache.summaryOfFn has fully
    /// populated this entry (cheap + deep inference).  Distinct
    /// from "no fields detected" — without this flag, fns with
    /// genuinely empty `may_free_fields` would be indistinguishable
    /// from never-resolved and would get re-inferred (wiping any
    /// R10 transitive updates).  Not part of the public contract;
    /// consumers should treat the summary as resolved when they
    /// retrieve it via FileCache.
    _resolved: bool = false,
};

/// Infer a summary for `body`.  Conservative: when unclear, returns
/// `.unknown` / null / false — never guesses.  `proto` carries the
/// param list so `borrowed_from` can resolve to a param index.
///
/// Body-only inference: only fills fields that can be determined
/// from the proto + body alone.  `heap_allocates_self` requires the
/// containing type's NAME (a contextual lookup) and `may_free_fields`
/// / `result_heap_fields` need allocations to land somewhere stable —
/// caller may want `inferFromBodyAlloc` for those.
pub fn inferFromBody(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
) FnSummary {
    var out: FnSummary = .{};
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // ── is_noreturn from the return-type signature ─────────────
    if (proto.ast.return_type.unwrap()) |rt| {
        const rt_first = tree.firstToken(rt);
        if (tags[rt_first] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(rt_first), "noreturn"))
        {
            out.is_noreturn = true;
        }
    }

    // ── Body-wide effects (allocates) ──────────────────────────
    // Scan for `.<method>(` shapes where method is alloc / free / etc.
    // Skips nested fns so a helper-fn-decl inside the body doesn't
    // leak its own classification upward.
    var t = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        const method = tree.tokenSlice(t + 1);
        if (receiver_mod.isAllocMethodName(method)) out.allocates = true;
        if (receiver_mod.isArrayListGrowMethodName(method)) out.may_grow_collections = true;
        if (receiver_mod.isGcTriggerMethodName(method)) out.may_invoke_gc = true;
    }

    // Second pass: detect bare exit-callback-register calls:
    // `add_exit_callback(fn_ptr)` — a top-level (non-method) bare call.
    t = first;
    while (t + 1 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (t > first and tags[t - 1] == .period) continue;
        if (receiver_mod.isExitCallbackRegisterName(tree.tokenSlice(t))) {
            out.may_run_on_any_thread = true;
            break;
        }
    }

    // ── returns: scan the FIRST `return <expr>` shape ──────────
    // Body inference is conservative — we only classify when the
    // shape is unambiguous.  Multi-arm returns (different shapes per
    // arm) collapse to `.unknown` rather than guessing.
    if (firstReturnExpr(tree, first, last)) |re| {
        out.returns = classifyReturnExpr(tree, proto, re.first, re.last, out.allocates);
    }

    // R8a: stronger `.heap` inference covers the two-statement form
    // (`{ var x = alloc(); return x; }`) that firstReturnExpr's
    // token-walk doesn't handle.  Overrides `.owned` because `.heap`
    // mints a HeapId (enables UAF + double-free tracking).  Skipped
    // when `returns` is already a concrete signal (`.borrowed_from`
    // — those carry MORE information than `.heap`).
    switch (out.returns) {
        .unknown, .owned, .heap => {
            if (inferReturnsHeap(tree, body)) out.returns = .heap;
        },
        .borrowed_from, .plain => {},
    }

    // Direct takes_ownership_of inference (R8b-style: .free(<param>)
    // / .destroy(<param>) only).  See inferDirectTakes for the
    // conservative rationale around <param>.deinit() being excluded.
    out.takes_ownership_of = inferDirectTakes(tree, proto, body);

    // result_params_in_return / result_independent_of_args:
    // Scan all `return <expr>` statements; track which param names
    // appear in them.  Used by borrowed-slice analysis.
    const ret_mask = inferResultParamsInReturn(tree, proto, first, last);
    out.result_params_in_return = ret_mask;
    out.result_independent_of_args =
        (ret_mask & SAW_RETURN_BIT) != 0 and
        (ret_mask & ~SAW_RETURN_BIT) == 0;

    return out;
}

/// Sentinel bit in `result_params_in_return`: set when the body has
/// at least one `return` statement (distinguishes "saw returns, no
/// params embedded" from "no returns found at all").
pub const SAW_RETURN_BIT: u32 = 1 << 31;

/// Walk every `return <expr>` statement in the fn body and record
/// which parameter names (by 0-based index) appear in at least one
/// non-recursive return expression.  Returns a bitmask:
///   bit 31 (SAW_RETURN_BIT) — body has at least one return statement
///   bits 0–30              — param i appears in some return expr
/// Zero means no return statements were found (conservative).
/// Self-recursive `return fn_name(...)` expressions are skipped;
/// param appearances there don't mean the result embeds those args.
fn inferResultParamsInReturn(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) u32 {
    const tags = tree.tokens.items(.tag);
    const self_name: ?[]const u8 = if (proto.name_token) |nt| tree.tokenSlice(nt) else null;
    var param_buf: [16][]const u8 = undefined;
    var n_params: u32 = 0;
    var it = proto.iterate(tree);
    while (it.next()) |p| {
        if (p.name_token) |nt| {
            if (n_params < param_buf.len) {
                param_buf[n_params] = tree.tokenSlice(nt);
                n_params += 1;
            }
        }
    }
    if (n_params == 0) return 0;
    var result: u32 = 0;
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_return) continue;
        result |= SAW_RETURN_BIT;
        var u: Ast.TokenIndex = t + 1;
        if (u <= last and tags[u] == .keyword_try) u += 1;
        // Self-recursive tail call: `return [try] fn_name(...)`.
        if (self_name) |sn| {
            var v = u;
            while (v + 1 <= last and (tags[v] == .identifier or tags[v] == .period)) : (v += 1) {}
            if (v > u and tags[v] == .l_paren) {
                var found_self = false;
                var w = u;
                while (w < v) : (w += 1) {
                    if (tags[w] == .identifier and std.mem.eql(u8, tree.tokenSlice(w), sn)) {
                        found_self = true;
                        break;
                    }
                }
                if (found_self) {
                    var pd2: i32 = 0;
                    var x = u;
                    while (x <= last) : (x += 1) {
                        switch (tags[x]) {
                            .l_paren, .l_bracket, .l_brace => pd2 += 1,
                            .r_paren, .r_bracket, .r_brace => {
                                if (pd2 == 0) break;
                                pd2 -= 1;
                            },
                            .semicolon => if (pd2 == 0) break,
                            else => {},
                        }
                    }
                    t = x;
                    continue;
                }
            }
        }
        var pd: i32 = 0;
        while (u <= last) : (u += 1) {
            switch (tags[u]) {
                .l_paren, .l_bracket, .l_brace => pd += 1,
                .r_paren, .r_bracket, .r_brace => {
                    if (pd == 0) break;
                    pd -= 1;
                },
                .semicolon => if (pd == 0) break,
                .identifier => {
                    if (u > 0 and tags[u - 1] == .period) continue;
                    const name = tree.tokenSlice(u);
                    for (param_buf[0..n_params], 0..) |p, i| {
                        if (std.mem.eql(u8, p, name) and i < 31) {
                            result |= @as(u32, 1) << @intCast(i);
                        }
                    }
                },
                else => {},
            }
        }
    }
    return result;
}

/// R8a: body is `{ return EXPR; }` or `{ var x = EXPR; return x; }`
/// where EXPR (after stripping try/catch wrappers) is a call to an
/// allocator-vocabulary method.  The matched pattern is:
/// with the vocabulary-based "is alloc method" check instead of
/// string-pattern matching.
fn inferReturnsHeap(tree: *const Ast, body_node: Ast.Node.Index) bool {
    var expr = singleReturnExpr(tree, body_node) orelse return false;
    while (true) {
        switch (tree.nodeTag(expr)) {
            .@"try" => expr = tree.nodeData(expr).node,
            .@"catch" => expr = tree.nodeData(expr).node_and_node[0],
            else => break,
        }
    }
    const is_call = switch (tree.nodeTag(expr)) {
        .call, .call_one, .call_comma, .call_one_comma => true,
        else => false,
    };
    if (!is_call) return false;
    // Walk the call's token range looking for the LAST `.<ident>(` —
    // that's the method name on the deepest receiver chain.
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(expr);
    const last = tree.lastToken(expr);
    var last_method: ?tokens.TokenIndex = null;
    var t: tokens.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        last_method = t + 1;
    }
    const m = last_method orelse return false;
    return receiver_mod.isAllocMethodName(tree.tokenSlice(m));
}

/// Token range of a `return <expr>;` body, if the body has one at
/// brace-depth 0 (relative to the fn body).  Skips nested fns.
fn firstReturnExpr(
    tree: *const Ast,
    body_first: tokens.TokenIndex,
    body_last: tokens.TokenIndex,
) ?struct { first: tokens.TokenIndex, last: tokens.TokenIndex } {
    const tags = tree.tokens.items(.tag);
    var t = body_first;
    while (t <= body_last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, body_last);
            continue;
        }
        if (tags[t] != .keyword_return) continue;
        if (t + 1 > body_last) return null;
        // `return;` (no value) — not a value return.
        if (tags[t + 1] == .semicolon) return null;
        const sc = tokens.findStmtSemicolon(tags, t + 1, body_last) orelse return null;
        if (sc == t + 1) return null;
        return .{ .first = t + 1, .last = sc - 1 };
    }
    return null;
}

/// Classify a `return <expr>` token range against the param list.
fn classifyReturnExpr(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    first: tokens.TokenIndex,
    last: tokens.TokenIndex,
    body_allocates: bool,
) Returns {
    const tags = tree.tokens.items(.tag);
    if (first > last) return .unknown;

    // `return try <expr>` — strip the `try` and re-classify.
    if (tags[first] == .keyword_try and first + 1 <= last) {
        return classifyReturnExpr(tree, proto, first + 1, last, body_allocates);
    }

    // Bare `return undefined;` — `.unknown` rather than misclassify.
    // `undefined` is tokenized as an identifier with that text.
    if (first == last and tags[first] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(first), "undefined")) return .unknown;

    // `return <chain>.<allocMethod>(...)` — if the chain ends in an
    // alloc-class call, the result is a fresh heap allocation.
    // Checked BEFORE the param-borrow check so `return gpa.alloc(...)`
    // classifies as .heap, not .borrowed_from(gpa).
    if (returnIsAllocCall(tree, first, last)) return .heap;

    if (returnIsDirectParamBorrow(tree, proto, first, last)) |idx| {
        return .{ .borrowed_from = idx };
    }

    if (body_allocates) return .owned;

    return .unknown;
}
/// Return the parameter index when `[first, last]` is a simple
/// parameter-rooted path (`p`, `p.field`, `p[index]`, or `p.*`).
/// Calls are deliberately excluded: a method/function can return a
/// detached value even when its receiver is a parameter.
fn returnIsDirectParamBorrow(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    first: tokens.TokenIndex,
    last: tokens.TokenIndex,
) ?u32 {
    const tags = tree.tokens.items(.tag);
    if (first > last or tags[first] != .identifier) return null;
    const idx = paramIndex(tree, proto, tree.tokenSlice(first)) orelse return null;
    var t = first + 1;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .period => {
                if (t + 1 > last or tags[t + 1] != .identifier) return null;
                t += 1;
            },
            .period_asterisk => {},
            .l_bracket => {
                var depth: u32 = 1;
                t += 1;
                while (t <= last and depth > 0) : (t += 1) {
                    switch (tags[t]) {
                        .l_bracket => depth += 1,
                        .r_bracket => depth -= 1,
                        .l_paren, .r_paren, .l_brace, .r_brace => return null,
                        else => {},
                    }
                }
                if (depth != 0) return null;
                t -= 1;
            },
            else => return null,
        }
    }
    return idx;
}

fn returnIsAllocCall(
    tree: *const Ast,
    first: tokens.TokenIndex,
    last: tokens.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    // Walk the chain `<id>(.<id>)*\(`, identify the LAST method ident
    // before the first `(`, and look it up in the vocabulary.
    var t = first;
    var last_method: ?tokens.TokenIndex = null;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .identifier => last_method = t,
            .period => {},
            .l_paren => break,
            else => return false,
        }
    }
    const m = last_method orelse return false;
    return receiver_mod.isAllocMethodName(tree.tokenSlice(m));
}

const isAllocatorName = receiver_mod.isAllocatorishName;

pub fn paramIndex(tree: *const Ast, proto: Ast.full.FnProto, name: []const u8) ?u32 {
    var it = proto.iterate(tree);
    var index: u32 = 0;
    while (it.next()) |p| : (index += 1) {
        if (p.name_token) |nt| {
            if (std.mem.eql(u8, tree.tokenSlice(nt), name)) return index;
        }
    }
    return null;
}

/// Scan `body` for direct ownership-transfer patterns and return
/// the index of the first param the fn takes (if any).
///
/// Matches `.free(<param>)` / `.destroy(<param>)` — the param is
/// passed as the explicit arg to an allocator-vocabulary free.
/// R8b: `fn(g, p) void { g.free(p); }` infers  ownership(p).
///
/// Deliberately does NOT match `<param>.deinit()` / `.close()` /
/// other receiver-cleanup forms.  Those signals are ambiguous: a
/// fn body can call `self.deinit(); self.entries = ...;` as a
/// reset-and-resurrect pattern where self isn't actually consumed.
/// Without dataflow tracking we can't tell the difference, so we
/// stay conservative.
///
/// Returns the FIRST match.  When multiple params are consumed the
/// summary only records one; consumers that need fuller fidelity
/// should consult `may_free_fields` for the field-typed cases.
pub fn inferDirectTakes(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
) ?u32 {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var t = first;
    while (t + 3 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        // `.free(<param>)` / `.destroy(<param>)`.  The arg is the
        // consumed value (not the receiver).  Reject mid-chain match
        // where the arg has its own field access (`.free(this.field)`
        // doesn't consume this).
        if (tags[t] == .period and tags[t + 1] == .identifier and
            tags[t + 2] == .l_paren and tags[t + 3] == .identifier)
        {
            const method = tree.tokenSlice(t + 1);
            const is_free = std.mem.eql(u8, method, "free") or
                std.mem.eql(u8, method, "destroy");
            if (!is_free) continue;
            // Guard: arg followed by `.` is a field access on the
            // arg — the param itself isn't being freed.
            if (t + 4 <= last and tags[t + 4] == .period) continue;
            const arg = tree.tokenSlice(t + 3);
            // Guard: `obj.destroy(alloc)` receiver-freed pattern.
            // When the token just before `.` is a plain (non-allocator-
            // named) identifier AND the arg IS allocator-named, the arg
            // is the allocator being passed to the destructor — not the
            // value being freed.  Marking it as "taken" here would
            // produce a false takes_ownership_of for any caller that
            // passes its own allocator param through.
            if (t > first and tags[t - 1] == .identifier) {
                const recv = tree.tokenSlice(t - 1);
                if (!isAllocatorName(recv) and isAllocatorName(arg)) continue;
            }
            if (paramIndex(tree, proto, arg)) |pi| return pi;
        }
    }
    return null;
}

// ── Deep inference (allocates) ────────────────────────────

/// Scan `body` for `<param>.<field>.<destroy_method>(...)` chains.
/// Returns one entry per chain.  Caller owns the returned slice;
/// pass an arena allocator so per-fn deinit is cheap.
/// True for cleanup methods whose RECEIVER is the freed value
/// (`<X>.deinit()` / `<X>.close()` etc.).  Excludes .free / .destroy
/// because those take their ARG, not their receiver — e.g.
/// `self.allocator.free(self.slices)` does NOT consume self.allocator.
// ── R7 helpers (delegating-return inference) ──────────────
//
// Pure-syntactic helpers used by FileCache's R7 pass.  Mirror
// R7-style helpers — live here so FileCache can run
// delegator-borrow inference without consulting the legacy db.
// Cache-dependent steps (callee summary lookup, cross-file
// resolution) live in FileCache.

/// Returns the inner expression of the body's "return value" if the
/// body has a R7-recognizable shape:
///
///   { return EXPR; }                       → EXPR
///   { var/const X = EXPR; return X; }      → EXPR  (X must match)
///
/// Anything else returns null.
pub fn singleReturnExpr(tree: *const Ast, body_node: Ast.Node.Index) ?Ast.Node.Index {
    const tag = tree.nodeTag(body_node);
    var stmt0: Ast.Node.Index = undefined;
    var stmt1_opt: ?Ast.Node.Index = null;
    switch (tag) {
        .block_two, .block_two_semicolon => {
            const d = tree.nodeData(body_node).opt_node_and_opt_node;
            stmt0 = d[0].unwrap() orelse return null;
            stmt1_opt = d[1].unwrap();
        },
        .block, .block_semicolon => {
            const d = tree.nodeData(body_node).extra_range;
            const start: u32 = @intFromEnum(d.start);
            const end: u32 = @intFromEnum(d.end);
            if (end - start == 1) {
                stmt0 = @enumFromInt(tree.extra_data[start]);
            } else if (end - start == 2) {
                stmt0 = @enumFromInt(tree.extra_data[start]);
                stmt1_opt = @as(Ast.Node.Index, @enumFromInt(tree.extra_data[start + 1]));
            } else return null;
        },
        else => return null,
    }

    if (stmt1_opt == null) {
        if (tree.nodeTag(stmt0) != .@"return") return null;
        return tree.nodeData(stmt0).opt_node.unwrap();
    }

    const stmt1 = stmt1_opt.?;
    if (tree.nodeTag(stmt1) != .@"return") return null;
    const ret_val = tree.nodeData(stmt1).opt_node.unwrap() orelse return null;
    if (tree.nodeTag(ret_val) != .identifier) return null;
    const ret_name = tree.tokenSlice(tree.nodeMainToken(ret_val));

    const var_decl = tree.fullVarDecl(stmt0) orelse return null;
    const name_tok = var_decl.ast.mut_token + 1;
    if (tree.tokens.items(.tag)[name_tok] != .identifier) return null;
    const decl_name = tree.tokenSlice(name_tok);
    if (!std.mem.eql(u8, decl_name, ret_name)) return null;

    return var_decl.ast.init_node.unwrap();
}

/// True iff `expr` is a return-value shape that doesn't borrow
/// from any local/param — string literal, integer, null, undefined,
/// `&.{}` (empty tuple-to-slice coercion).
pub fn isNonBorrowReturnValue(tree: *const Ast, expr: Ast.Node.Index) bool {
    switch (tree.nodeTag(expr)) {
        .string_literal,
        .multiline_string_literal,
        .number_literal,
        .char_literal,
        => return true,
        .identifier => {
            const name = tree.tokenSlice(tree.nodeMainToken(expr));
            return std.mem.eql(u8, name, "null") or
                std.mem.eql(u8, name, "undefined") or
                std.mem.eql(u8, name, "true") or
                std.mem.eql(u8, name, "false");
        },
        .address_of => {
            const inner = tree.nodeData(expr).node;
            return switch (tree.nodeTag(inner)) {
                .struct_init_dot_two, .struct_init_dot_two_comma => true,
                else => false,
            };
        },
        else => return false,
    }
}

/// When the return is a struct literal and any field initializer is
/// exactly a fn-param identifier, infer `borrowed_from(<that param>)`.
/// Picks the first match.
pub fn inferReturnStructLiteralBorrowsParam(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    return_expr: Ast.Node.Index,
) ?u32 {
    var buf: [2]Ast.Node.Index = undefined;
    const si = tree.fullStructInit(&buf, return_expr) orelse return null;
    for (si.ast.fields) |field_value| {
        if (tree.nodeTag(field_value) != .identifier) continue;
        const name = tree.tokenSlice(tree.nodeMainToken(field_value));
        if (paramIndex(tree, proto, name)) |idx| return idx;
    }
    return null;
}

/// Cleanup methods whose RECEIVER is the destroyed value.
/// A strict subset of receiver_mod.isCleanupMethodName — excludes
/// `.free` and `.destroy` which take their target as an explicit ARG
/// (the allocator is the receiver, not the freed thing).
pub fn isReceiverCleanupMethodName(name: []const u8) bool {
    return receiver_mod.isCleanupMethodName(name) and
        !std.mem.eql(u8, name, "free") and
        !std.mem.eql(u8, name, "destroy");
}

pub fn inferMayFreeFields(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
) ![]const FieldFree {
    var out: std.ArrayListUnmanaged(FieldFree) = .empty;
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var t = first;
    while (t + 5 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        // Match `<id>(.<id>)+(` — receiver, one or more field
        // segments, method name, then `(`.  Reject mid-chain matches
        // (where token before t is `.`, meaning we're in the middle
        // of a larger chain).
        if (tags[t] != .identifier) continue;
        if (t > first and tags[t - 1] == .period) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        // Walk the dotted chain forward as long as we see `.<id>`,
        // tracking the FIRST and LAST field identifiers.  The chain
        // ends at the trailing `(` — the ident right before `(` is
        // the method name; everything between t+2 and that ident
        // forms the field path.
        const recv = tree.tokenSlice(t);
        const param_idx = paramIndex(tree, proto, recv) orelse continue;
        const first_field_tok: tokens.TokenIndex = t + 2;
        var last_field_tok: tokens.TokenIndex = t + 2;
        var k: tokens.TokenIndex = t + 3;
        var method_tok: ?tokens.TokenIndex = null;
        while (k + 1 <= last) {
            if (tags[k] == .period and tags[k + 1] == .identifier) {
                // The trailing ident might be the method (followed by
                // `(`) or another field segment (followed by `.`).
                if (k + 2 <= last and tags[k + 2] == .l_paren) {
                    method_tok = k + 1;
                    break;
                }
                last_field_tok = k + 1;
                k += 2;
                continue;
            }
            break;
        }
        const mtok = method_tok orelse continue;
        const method = tree.tokenSlice(mtok);
        // Only methods that consume their RECEIVER (deinit/close/etc.)
        // count — `.free` / `.destroy` take their ARG instead.
        if (!isReceiverCleanupMethodName(method)) continue;
        // Field path: source-slice from first field's start to last
        // field's end.  Same shape as the R10 Case B inference.
        const start_byte = tree.tokens.items(.start)[first_field_tok];
        const last_start = tree.tokens.items(.start)[last_field_tok];
        const last_len = tree.tokenSlice(last_field_tok).len;
        const field_path = tree.source[start_byte..(last_start + last_len)];
        try out.append(arena, .{
            .param = param_idx,
            .field = field_path,
            .method = method,
        });
        // Advance past the method to avoid re-matching the same chain.
        t = mtok;
    }
    return out.toOwnedSlice(arena);
}

/// True iff the body contains `<x>.create(<type_name>)` or
/// `<x>.create(Self)`.  Returns false when `type_name` is null
/// (top-level fns have no containing type).
pub fn inferHeapAllocatesSelf(
    tree: *const Ast,
    body: Ast.Node.Index,
    type_name: ?[]const u8,
) bool {
    const tn = type_name orelse return false;
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var t = first;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "create")) continue;
        if (tags[t + 2] != .l_paren) continue;
        // Walk the call's arg list (single arg expected, possibly
        // namespaced like `ns.Type`) and check the LAST identifier
        // against `tn` / `Self`.
        var k = t + 3;
        var last_ident: ?Ast.TokenIndex = null;
        while (k <= last) : (k += 1) {
            if (tags[k] == .r_paren or tags[k] == .comma) break;
            if (tags[k] == .identifier) last_ident = k;
        }
        if (last_ident) |li| {
            const text = tree.tokenSlice(li);
            if (std.mem.eql(u8, text, tn)) return true;
            if (std.mem.eql(u8, text, "Self")) return true;
        }
    }
    return false;
}

/// If `body` is `{ return <struct_literal>; }` and any field's
/// initializer text contains an alloc call (`.alloc(`, `.create(`,
/// `.dupe(`, etc.), return the list of those field names.  Empty
/// for non-constructor bodies.  Caller owns the returned slice.
pub fn inferResultHeapFields(
    arena: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
) ![]const []const u8 {
    var out: std.ArrayListUnmanaged([]const u8) = .empty;
    // Text-based approach for
    // pipeline: find a `return ... { .X = ... }` struct-literal
    // shape, then text-match each field's RHS against the alloc-call
    // vocabulary.  Per-token introspection of a struct literal AST
    // node would be more precise but this is good enough for the
    // common constructor shape and matches the existing pipeline's
    // conservatism.
    const source = tree.source;
    const tags = tree.tokens.items(.tag);
    const starts = tree.tokens.items(.start);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Find `return` at depth 0 of the body, then look for `.{` or
    // `<Type>{` following it.
    var t = first;
    var ret_at: ?Ast.TokenIndex = null;
    while (t <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] == .keyword_return) {
            ret_at = t;
            break;
        }
    }
    const ra = ret_at orelse return &.{};
    // Find the `{` after the return that opens a struct literal.
    var k = ra + 1;
    while (k <= last and tags[k] != .l_brace and tags[k] != .semicolon) : (k += 1) {}
    if (k > last or tags[k] != .l_brace) return &.{};
    const lb = k;
    const rb = tokens.matchBrace(tags, lb, last) orelse return &.{};
    // Walk the literal's body looking for `.<name> = <rhs>,` pairs.
    var i: tokens.TokenIndex = lb + 1;
    while (i < rb) : (i += 1) {
        if (tags[i] != .period) continue;
        if (i + 2 > rb) break;
        if (tags[i + 1] != .identifier) continue;
        if (tags[i + 2] != .equal) continue;
        const fname = tree.tokenSlice(i + 1);
        // Find end of this field's RHS: the comma at depth 0
        // (relative to where we are) or `}`.
        var depth: u32 = 0;
        var j: tokens.TokenIndex = i + 3;
        while (j <= rb) : (j += 1) {
            switch (tags[j]) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => {
                    if (depth == 0) break;
                    depth -= 1;
                },
                .comma => if (depth == 0) break,
                else => {},
            }
        }
        const rhs_first = i + 3;
        const rhs_last = if (j > rb) rb - 1 else j - 1;
        if (rhs_first > rhs_last) {
            i = j;
            continue;
        }
        const rhs_text = source[starts[rhs_first] .. starts[rhs_last] + tree.tokenSlice(rhs_last).len];
        if (rhsTextLooksAlloc(rhs_text)) {
            try out.append(arena, fname);
        }
        i = j;
    }
    return out.toOwnedSlice(arena);
}

/// True iff `text` contains a substring matching the alloc-pattern
/// vocabulary.  Conservative text match (same shape the old
/// inference uses).
fn rhsTextLooksAlloc(text: []const u8) bool {
    const patterns = [_][]const u8{
        ".alloc(",      ".allocSentinel(", ".allocAdvanced(",
        ".create(",     ".dupe(",          ".dupeZ(",
        ".allocPrint(", ".allocPrintZ(",   ".toOwnedSlice(",
    };
    for (patterns) |p| {
        if (std.mem.indexOf(u8, text, p) != null) return true;
    }
    return false;
}

// ── Tests ──────────────────────────────────────────────────

const testing = std.testing;

fn parse(src: [:0]const u8) !Ast {
    var tree = try Ast.parse(testing.allocator, src, .zig);
    errdefer tree.deinit(testing.allocator);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    return tree;
}

/// Find the first fn_decl in `tree` and infer its summary.  The
/// `proto_buf` parameter MUST outlive the returned summary because
/// fnProtoOne/Simple store params into it — a stack-local buffer
/// would dangle by the time the caller uses the summary.
fn inferFirstFn(tree: *const Ast, proto_buf: *[1]Ast.Node.Index) FnSummary {
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const proto = tokens.fnProto(tree, proto_buf, node).?;
        const body = tokens.bodyOf(tree, node).?;
        return inferFromBody(tree, proto, body);
    }
    unreachable;
}

test "infer: noreturn return type sets is_noreturn" {
    var tree = try parse("fn die() noreturn { @panic(\"\"); }");
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const s = inferFirstFn(&tree, &buf);
    try testing.expect(s.is_noreturn);
}

test "infer: body with .alloc() sets allocates" {
    var tree = try parse(
        \\fn f(gpa: std.mem.Allocator) ![]u8 {
        \\    return try gpa.alloc(u8, 16);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const s = inferFirstFn(&tree, &buf);
    try testing.expect(s.allocates);
    try testing.expect(s.returns == .heap);
}

test "skript regression: direct parameter field borrow remains classified" {
    var tree = try parse(
        \\fn text(self: *Foo) []const u8 {
        \\    return self.buf;
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const s = inferFirstFn(&tree, &buf);
    try testing.expect(s.returns == .borrowed_from);
    try testing.expectEqual(@as(u32, 0), s.returns.borrowed_from);
}

test "skript regression: receiver method call is not a direct parameter borrow" {
    var tree = try parse(
        \\fn wrap(ctx: *Foo) ![]u8 {
        \\    return try ctx.makeBuf();
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const s = inferFirstFn(&tree, &buf);
    try testing.expect(s.returns == .unknown);
}

test "infer: no return statement leaves returns as unknown" {
    var tree = try parse(
        \\fn nothing() void {}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const s = inferFirstFn(&tree, &buf);
    try testing.expect(s.returns == .unknown);
}

test "infer: bare return undefined stays unknown (per design)" {
    var tree = try parse(
        \\fn placeholder() u32 {
        \\    return undefined;
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const s = inferFirstFn(&tree, &buf);
    try testing.expect(s.returns == .unknown);
}

test "infer: nested fns don't leak effects to outer" {
    var tree = try parse(
        \\fn outer() void {
        \\    const inner = struct {
        \\        fn deep(gpa: std.mem.Allocator) ![]u8 {
        \\            return try gpa.alloc(u8, 1);
        \\        }
        \\    };
        \\    _ = inner;
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const s = inferFirstFn(&tree, &buf);
    try testing.expect(!s.allocates);
    try testing.expect(s.returns == .unknown);
}

fn firstFnProtoAndBody(
    tree: *const Ast,
    proto_buf: *[1]Ast.Node.Index,
) struct { Ast.full.FnProto, Ast.Node.Index } {
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        return .{ tokens.fnProto(tree, proto_buf, node).?, tokens.bodyOf(tree, node).? };
    }
    unreachable;
}

test "inferDirectTakes: gpa.destroy(<param>) returns param index" {
    var tree = try parse(
        \\fn cleanup(gpa: std.mem.Allocator, p: *Foo) void {
        \\    gpa.destroy(p);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    // inferDirectTakes is callable on its own even though it isn't
    // currently wired into inferFromBody (see the note there).
    try testing.expectEqual(@as(?u32, 1), inferDirectTakes(&tree, pb[0], pb[1]));
}

test "inferDirectTakes: gpa.free(<param>) returns param index" {
    var tree = try parse(
        \\fn drop(gpa: std.mem.Allocator, buf: []u8) void {
        \\    gpa.free(buf);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    try testing.expectEqual(@as(?u32, 1), inferDirectTakes(&tree, pb[0], pb[1]));
}

test "inferDirectTakes: obj.destroy(alloc) receiver-freed — does NOT mark alloc as taken" {
    // `loading.destroy(alloc)` is a receiver-freed pattern: `loading` is what
    // gets destroyed, `alloc` is the allocator passed to the destructor.
    // inferDirectTakes must NOT infer takes_ownership_of = alloc_index here.
    var tree = try parse(
        \\fn deinit(self: *ImageStorage, alloc: std.mem.Allocator) void {
        \\    if (self.loading) |loading| loading.destroy(alloc);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    try testing.expectEqual(@as(?u32, null), inferDirectTakes(&tree, pb[0], pb[1]));
}

test "inferDirectTakes: no .free/.destroy returns null" {
    var tree = try parse(
        \\fn touch(self: *Foo) void {
        \\    _ = self;
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    try testing.expect(inferDirectTakes(&tree, pb[0], pb[1]) == null);
}

test "inferDirectTakes: <param>.deinit() does NOT match (reset-and-resurrect risk)" {
    var tree = try parse(
        \\fn cleanup(self: *Foo) void {
        \\    self.deinit();
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    try testing.expect(inferDirectTakes(&tree, pb[0], pb[1]) == null);
}

test "inferMayFreeFields: detects <param>.<field>.<deallocMethod>()" {
    var tree = try parse(
        \\fn cleanup(self: *Foo, other: *Bar) void {
        \\    self.x.deinit();
        \\    other.y.close();
        \\    self.z.deref();
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    const ff = try inferMayFreeFields(arena.allocator(), &tree, pb[0], pb[1]);
    try testing.expectEqual(@as(usize, 3), ff.len);
    try testing.expectEqual(@as(u32, 0), ff[0].param);
    try testing.expectEqualStrings("x", ff[0].field);
    try testing.expectEqual(@as(u32, 1), ff[1].param);
    try testing.expectEqualStrings("y", ff[1].field);
    try testing.expectEqual(@as(u32, 0), ff[2].param);
    try testing.expectEqualStrings("z", ff[2].field);
}

test "inferMayFreeFields: ignores non-deallocating methods" {
    var tree = try parse(
        \\fn touch(self: *Foo) void {
        \\    self.x.append(1);
        \\    self.y.process();
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    const ff = try inferMayFreeFields(arena.allocator(), &tree, pb[0], pb[1]);
    try testing.expectEqual(@as(usize, 0), ff.len);
}

test "inferHeapAllocatesSelf: <x>.create(<TypeName>) hits" {
    var tree = try parse(
        \\fn factory(gpa: std.mem.Allocator) !*Foo {
        \\    return try gpa.create(Foo);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    try testing.expect(inferHeapAllocatesSelf(&tree, pb[1], "Foo"));
    try testing.expect(!inferHeapAllocatesSelf(&tree, pb[1], "Bar"));
    try testing.expect(!inferHeapAllocatesSelf(&tree, pb[1], null));
}

test "inferHeapAllocatesSelf: <x>.create(Self) hits" {
    var tree = try parse(
        \\fn factory(gpa: std.mem.Allocator) !*Foo {
        \\    return try gpa.create(Self);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    try testing.expect(inferHeapAllocatesSelf(&tree, pb[1], "AnyType"));
}

test "inferResultHeapFields: collects alloc-RHS fields from struct-literal return" {
    var tree = try parse(
        \\fn init(gpa: std.mem.Allocator, src: []const u8) !Foo {
        \\    return .{
        \\        .bytes = try gpa.alloc(u8, 16),
        \\        .name = try gpa.dupe(u8, src),
        \\        .count = 0,
        \\    };
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    const rhf = try inferResultHeapFields(arena.allocator(), &tree, pb[1]);
    try testing.expectEqual(@as(usize, 2), rhf.len);
    try testing.expectEqualStrings("bytes", rhf[0]);
    try testing.expectEqualStrings("name", rhf[1]);
}

test "inferResultHeapFields: non-constructor body yields empty" {
    var tree = try parse(
        \\fn make() Foo { return .{}; }
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const pb = firstFnProtoAndBody(&tree, &buf);
    const rhf = try inferResultHeapFields(arena.allocator(), &tree, pb[1]);
    try testing.expectEqual(@as(usize, 0), rhf.len);
}
