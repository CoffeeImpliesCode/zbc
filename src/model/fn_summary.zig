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
//!   grow_paths            — "WHOSE buffer can move?": the
//!                            parameter-rooted storage paths this fn (or
//!                            anything it reaches) can grow, next to
//!                            `may_grow_collections`'s "can anything move?"
//!
//! The two are kept CONSISTENT: after `FileCache.resolveTransitiveTakes`
//! Phase 8, `grows_unknown_path == true` implies `may_grow_collections ==
//! true`.  An effect that could not be attributed to a parameter is
//! still a reallocation, and must not be one of the reasons the coarse
//! flag says this fn grows nothing.
//!
//! Consumers MUST treat `.unknown` as "assume nothing" — same as
//! today's `lowering_gap` conservative fallback.  Storage counts as
//! this fn's own only when the DECLARATIONS behind it prove this fn
//! built it.  This file cannot read a declaration, so it never claims
//! ownership: it hands the question to
//! `FileCache.provesFreshStorage` as a `FreshClaim`, and every claim
//! that resolver cannot prove is charged as unknown storage.  A call
//! result, a file-level `var`, a copied header and a cast are all
//! claims that cannot be proved, because each can hand back an
//! allocation somebody else is walking.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../ast/tokens.zig");
const receiver_mod = @import("method_names.zig");
const local_bindings = @import("local_bindings.zig");

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

/// Storage reached from a parameter through a dotted field path.
/// `path` is `""` when the parameter's OWN storage is meant.
pub const ParamPath = struct {
    /// 0-indexed parameter of the enclosing fn.
    param: u32,
    /// Dotted field path from that parameter (`""` = the whole).
    path: []const u8,
};

/// Where a value came from, as far as this file can prove.  Anything
/// the file cannot read — a call result, an index, a `@constCast` of a
/// view, a loop capture, a local whose initializer it does not
/// understand — stays `.unknown`, and consumers MUST assume it carries
/// any storage at all.
pub const StorageOwner = union(enum) {
    param: ParamPath,
    unknown,
};

/// One parameter-rooted storage path whose backing buffer a fn may
/// grow.  `field` is `""` when the parameter's own storage is grown
/// (`fn g(list: *List) { list.append(1); }`) and a dotted path
/// otherwise (`fn g(o: *Oracle) { o.aliases.append(1); }`).  Slice is
/// owned by the summary arena.
pub const GrowPath = struct {
    param: u32,
    field: []const u8,
};

/// A call in the body whose callee's grow paths fold into the caller's.
/// Produced by `inferGrowEffects`, consumed by
/// `FileCache.resolveGrowPathsOne` — never stored in an `FnSummary`.
pub const GrowCall = struct {
    /// Final callee token, for exact AST and declaration lookup in this snapshot.
    callee_token: Ast.TokenIndex,
    /// Free-fn name (`.bare` / `.qualified`) or method name
    /// (`.method` / `.unresolved`).
    name: []const u8,
    ///   `.bare`      — `growNames(list, n)`, a free call this file
    ///                  may be able to name;
    ///   `.method`    — `recv.grow(n)`, a method on storage this fn
    ///                  holds, whose receiver is `args[0]`;
    ///   `.qualified` — `helpers.grow(list, n)`, a free function in
    ///                  the module `qualifier` names.  The qualifier
    ///                  is not storage the caller was handed, so
    ///                  nothing is prepended to `args`.  Only a
    ///                  receiver that is ONE identifier reaches
    ///                  here: `a.b.c(` names a field of something
    ///                  else, and a module never has one.
    ///   `.unresolved` — an invocation whose callee this fn cannot
    ///                  root on a parameter: a method on a receiver
    ///                  it was NOT handed (a header it built itself,
    ///                  a global, a call result, an index), or an
    ///                  indirect one — `@call`, a grouped or
    ///                  computed callee — which names nothing at
    ///                  all.  Its name is a METHOD name, or `""`,
    ///                  and must never be dispatched to a file-level
    ///                  declaration that happens to share it, so the
    ///                  cache charges only what the call hands over.
    kind: enum { bare, method, qualified, unresolved },
    /// The declaration a `.qualified` call goes through; `""` otherwise.
    qualifier: []const u8 = "",
    /// One entry per callee parameter; `args[0]` of a `.method` call is
    /// the receiver.  Slice is owned by the summary arena.
    args: []const StorageOwner,
};

/// "This initializer may be storage this fn built for itself, and only
/// a reader of declarations can say so."  The resolver
/// (`FileCache.provesFreshStorage`) answers by resolving the
/// constructor's declaration, the struct type's own fields and their
/// defaults, or the callee's returns.  A claim it cannot prove is
/// charged as unattributed storage, never as this fn's own.
pub const FreshClaim = struct {
    /// First and last token of the initializer expression.
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    /// The type the binding declared (`var x: List = .{}`), when it
    /// spelled one.  An anonymous `.{ }` names no type of its own, so
    /// proving its omitted fields needs this; `null` when the type was
    /// left to inference.
    type_first: ?Ast.TokenIndex = null,
    type_last: ?Ast.TokenIndex = null,
};

/// What one pass over a body established about its growth effects.
pub const GrowEffects = struct {
    paths: []const GrowPath = &.{},
    /// A grow site exists that is attributed to no listed path: it
    /// reaches a global, or storage this file cannot trace.  Consumers
    /// MUST assume such a fn may grow storage they cannot prove is
    /// elsewhere.
    unknown: bool = false,
    calls: []const GrowCall = &.{},
    /// Grow sites whose receiver may be storage this fn built for
    /// itself.  Each is recorded here instead of in `paths` / `unknown`
    /// so the resolver can still prove it fresh; whatever it cannot
    /// prove becomes unknown storage.
    claims: []const FreshClaim = &.{},
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
    /// WHICH parameter-rooted storage paths this fn (or anything it
    /// reaches) can grow, folded to a fixed point by
    /// `FileCache.resolveTransitiveTakes` Phase 8.  `may_grow_collections`
    /// says a reallocation is possible; this says where.  A callee
    /// that grows its own list, or a different field of the same
    /// owner, moves nothing the caller is iterating — that is a
    /// DISJOINT set of effects, not a weaker type.
    ///
    /// A grow method used as a free function (`ensureCapacity(gpa,
    /// &list, n)`) is covered here too, and sets
    /// `may_grow_collections` as well: two views of the same body must
    /// never disagree about whether a reallocation is reachable.
    ///
    /// A call this file CANNOT resolve — an unreadable module, a
    /// method the receiver's type does not declare — lands here as
    /// well, one entry per parameter-rooted argument it was handed.
    /// Nothing is known about what such a callee does, and the only
    /// claim its arguments support is that it can reallocate the
    /// storage they were rooted at; that is a PATH, not unattributed
    /// storage, so a caller can still tell a handover to one list
    /// from a loop walking another.  An argument this file cannot
    /// root is the one thing that carries no path, and it is what
    /// `grows_unknown_path` records.
    ///
    /// `grow_paths` is NOT a promise that the listed storage is the
    /// ONLY thing this fn grows.  `grows_unknown_path` carries that,
    /// and it is the flag consumers must read.
    grow_paths: []const GrowPath = &.{},
    /// A reachable grow site is attributed to no path in
    /// `grow_paths` — it reaches a global, or storage this file
    /// cannot trace.  Defaults TRUE so a summary that has not been
    /// through Phase 8 is conservative.  Consumers MUST treat it as
    /// "may grow storage I cannot prove it does not reach".
    grows_unknown_path: bool = true,
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
        // A grow method used as a FREE function
        // (`ensureCapacity(gpa, &list, n)`) reallocates just as the
        // method form does, so the coarse flag covers it as well:
        // leaving it out made the coarse view deny a reallocation
        // the precise view can see.
        const name = tree.tokenSlice(t);
        if (receiver_mod.isArrayListGrowMethodName(name)) out.may_grow_collections = true;
        if (receiver_mod.isExitCallbackRegisterName(name)) {
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

/// Deepest `<param> . <local> . …` chain followed before the answer is
/// declared unknown.  Chains longer than this are vanishingly rare and
/// the alternative (following them) risks not terminating on a
/// self-referential binding.
const max_owner_depth = 6;

/// Concatenate two dotted path segments.  `arena` owns the result; an
/// empty side is returned unchanged (it is not copied).
pub fn joinPath(arena: std.mem.Allocator, outer: []const u8, inner: []const u8) ![]const u8 {
    if (outer.len == 0) return inner;
    if (inner.len == 0) return outer;
    return std.fmt.allocPrint(arena, "{s}.{s}", .{ outer, inner });
}

/// Source text of the token range `[first, last]`, or `""` when empty.
fn tokenText(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) []const u8 {
    if (first > last) return "";
    const starts = tree.tokens.items(.start);
    return tree.source[starts[first] .. starts[last] + tree.tokenSlice(last).len];
}

/// Walk a pure `<id>(.<id>)*` chain rooted at `first`, returning one
/// past its last token.  A `(` or `[` inside the range ends the walk
/// early, which the caller detects by comparing against `last + 1`.
fn pathChainEnd(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (first > last or tags[first] != .identifier) return null;
    var t: Ast.TokenIndex = first + 1;
    while (t + 1 <= last and tags[t] == .period and tags[t + 1] == .identifier) : (t += 2) {}
    return t;
}

/// Storage the value produced by `[first, last]` came from.
///
/// Recognised shapes are `&<path>`, `try <path>`, `<param>(.<field>)*`
/// and `(<param>|<local>)(.<field>)*`, the last two with an optional
/// `.*` deref.  A local is followed through its own initializer, so
/// `const tree = o.tree;` reports the same owner as `o.tree` — that
/// forwarding is what lets a call-site prove which of ITS parameters
/// the loop's storage came from.
///
/// Everything else — a call result, an index, a cast, a loop capture,
/// a local this file cannot read — is `.unknown`.  Unknown means "may
/// carry any storage", never "carries none".
pub fn ownerOfExpr(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    depth: u8,
) !StorageOwner {
    const tags = tree.tokens.items(.tag);
    if (first > last) return .unknown;
    // `&x` and `try x` wrap an expression without changing the storage
    // it names.
    switch (tags[first]) {
        .ampersand, .keyword_try => return ownerOfExpr(
            arena,
            tree,
            proto,
            bindings,
            first + 1,
            last,
            depth,
        ),
        else => {},
    }
    const chain_end = pathChainEnd(tree, first, last) orelse return .unknown;
    var end = chain_end;
    // `.*` is a SINGLE `period_asterisk` token in the Zig tokenizer.
    if (end <= last and tags[end] == .period_asterisk) end += 1;
    if (end != last + 1) return .unknown;

    const fields = tokenText(tree, first + 2, chain_end - 1);
    const root = tree.tokenSlice(first);
    if (paramIndex(tree, proto, root)) |idx| {
        return .{ .param = .{ .param = idx, .path = fields } };
    }
    if (depth >= max_owner_depth) return .unknown;
    const binding = bindings.find(root) orelse return .unknown;
    // A loop capture is one ELEMENT copied out of the buffer, not the
    // list; whether that element aliases the list is its own question.
    if (binding.origin == .loop_capture) return .unknown;
    const inner = try ownerOfExpr(
        arena,
        tree,
        proto,
        bindings,
        binding.rhsFirstAfterTry(tags),
        binding.rhs_last,
        depth + 1,
    );
    return switch (inner) {
        .unknown => .unknown,
        .param => |p| .{ .param = .{
            .param = p.param,
            .path = try joinPath(arena, p.path, fields),
        } },
    };
}

/// The storage a `<grow method>` receiver names.  `.unproven` is
/// storage this fn may have BUILT for itself — a container
/// constructor, a struct literal of them — which only a reader of
/// declarations can confirm.  This file records the initializer as a
/// `FreshClaim` and leaves the verdict to
/// `FileCache.provesFreshStorage`; until that resolver proves one,
/// the grow is unattributed storage, which is the conservative
/// direction.
pub const GrowBase = union(enum) {
    unproven: FreshClaim,
    storage: StorageOwner,
};

/// A token range, as `FreshClaim` and the fresh-storage resolver
/// carry them around `FileCache`.
pub const TokenRange = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

/// Classify the receiver of a grow call for `inferGrowEffects`.  Its
/// base name is followed through whatever chain of locals introduced
/// it, so a header copy (`var copy = tally.*; copy.entries.append(x)`)
/// is charged to the parameter whose buffer the copy shares.
pub fn growBaseOfExpr(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) !GrowBase {
    const tags = tree.tokens.items(.tag);
    var root_tok = first;
    if (root_tok <= last and tags[root_tok] == .keyword_try) root_tok += 1;
    if (root_tok > last or tags[root_tok] != .identifier) {
        return .{ .storage = .unknown };
    }
    const origin = try growOriginOfName(
        arena,
        tree,
        proto,
        bindings,
        tree.tokenSlice(root_tok),
        0,
    );
    return switch (origin) {
        // The claim names an initializer, not a field of it, so the
        // field path the receiver walked is not part of the question:
        // fresh storage stays fresh one level down.
        .unproven => |claim| .{ .unproven = claim },
        .storage => |s| switch (s) {
            .unknown => GrowBase{ .storage = .unknown },
            .param => |p| .{ .storage = .{ .param = .{
                .param = p.param,
                .path = try joinPath(arena, p.path, tokenText(tree, root_tok + 2, last)),
            } } },
        },
    };
}

/// Storage `name` was introduced from.  A local initialised from
/// another binding inherits that binding's answer; anything else is a
/// claim the resolver has to answer from declarations, and unknown
/// until it does.
fn growOriginOfName(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    name: []const u8,
    depth: u8,
) !GrowBase {
    if (depth >= max_owner_depth) return .{ .storage = .unknown };
    if (paramIndex(tree, proto, name)) |idx| {
        return .{ .storage = .{ .param = .{ .param = idx, .path = "" } } };
    }
    const binding = bindings.find(name) orelse return .{ .storage = .unknown };
    if (binding.origin == .loop_capture) return .{ .storage = .unknown };
    const tags = tree.tokens.items(.tag);
    const rhs_first = binding.rhsFirstAfterTry(tags);
    const base_tok = if (rhs_first <= binding.rhs_last and tags[rhs_first] == .ampersand)
        rhs_first + 1
    else
        rhs_first;
    if (base_tok > binding.rhs_last or tags[base_tok] != .identifier) {
        // Not a name this fn introduced: a construction, a call, a
        // cast, `undefined`.  Whoever built it may have handed back
        // somebody else's buffer, so this is a question for the
        // resolver rather than an answer.
        return .{ .unproven = claimFor(tree, binding) };
    }
    const base_name = tree.tokenSlice(base_tok);
    // `var x: T = SomeType.init(…)` also starts with an identifier,
    // but one this fn never introduced: a type, a namespace, a
    // container-level declaration.  There is nothing here to follow,
    // and treating it as borrowed would throw away every constructor
    // the resolver CAN read — so it is a claim like any other.
    if (paramIndex(tree, proto, base_name) == null and bindings.find(base_name) == null) {
        return .{ .unproven = claimFor(tree, binding) };
    }
    return switch (try growOriginOfName(
        arena,
        tree,
        proto,
        bindings,
        base_name,
        depth + 1,
    )) {
        .unproven => |claim| .{ .unproven = claim },
        .storage => |s| switch (s) {
            .unknown => GrowBase{ .storage = .unknown },
            .param => |p| .{
                .storage = .{
                    .param = .{
                        .param = p.param,
                        // A trailing `.*` copies the header at the path, so it
                        // names no further field — `var copy = o.entries.*;`
                        // shares `o.entries`'s buffer, not a field ".*".
                        .path = try joinPath(
                            arena,
                            p.path,
                            tokenText(tree, base_tok + 2, derefLast(tags, base_tok, binding.rhs_last)),
                        ),
                    },
                },
            },
        },
    };
}

/// Last token of a field path, with a trailing `.*` deref removed.
/// `.*` is a SINGLE `period_asterisk` token, and it copies the header
/// it follows rather than naming a field of it.
fn derefLast(
    tags: []const std.zig.Token.Tag,
    base: Ast.TokenIndex,
    last: Ast.TokenIndex,
) Ast.TokenIndex {
    if (last > base and tags[last] == .period_asterisk) return last - 1;
    return last;
}

/// The type expression a local's declaration spelled (`var x: T = …`),
/// or null when it left the type to be inferred.  An anonymous `.{ }`
/// names no type of its own, so the resolver needs this to say which
/// fields it omitted and what defaults they carry.
fn declaredTypeRange(tree: *const Ast, binding: *const local_bindings.Binding) ?TokenRange {
    if (binding.rhs_first == 0) return null;
    const tags = tree.tokens.items(.tag);
    const first = binding.name_token + 1;
    if (first + 1 > binding.rhs_first) return null;
    if (tags[first] != .colon) return null;
    // A local declaration's initializer starts one token after its
    // own `=`, so everything between the `:` and that `=` is the type.
    // Anchoring on that `=` rather than scanning for one keeps a `=`
    // inside a generic argument or a fn type out of the answer.
    if (tags[binding.rhs_first - 1] != .equal) return null;
    const type_first = first + 1;
    const type_last = binding.rhs_first - 2;
    if (type_last < type_first) return null;
    return .{ .first = type_first, .last = type_last };
}

/// The claim a local's initializer leaves behind: the expression
/// itself, plus the type its declaration spelled — an anonymous `.{ }`
/// names no type of its own, and the resolver needs the declaration to
/// say which fields it left out.
fn claimFor(tree: *const Ast, binding: *const local_bindings.Binding) FreshClaim {
    const declared = declaredTypeRange(tree, binding);
    return .{
        .first = binding.rhs_first,
        .last = binding.rhs_last,
        .type_first = if (declared) |range| range.first else null,
        .type_last = if (declared) |range| range.last else null,
    };
}

/// Walk back from the `.` of a method call over `<id>(.<id>)*` to the
/// first token of the receiver.  A receiver that is not a plain path
/// (`foo().bar`, `xs[i].bar`) yields a start token that
/// `growBaseOfExpr` rejects as `.unknown`.
fn receiverStart(
    tags: []const std.zig.Token.Tag,
    dot: Ast.TokenIndex,
    lower: Ast.TokenIndex,
) Ast.TokenIndex {
    var start = dot - 1;
    while (start >= lower + 2 and tags[start - 1] == .period and tags[start - 2] == .identifier) {
        start -= 2;
    }
    return start;
}

/// The parameter-rooted storage one operand of an invocation came
/// from, resolved by the same rooting every other argument uses.
fn operandOwner(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    node: Ast.Node.Index,
) !StorageOwner {
    return ownerOfExpr(
        arena,
        tree,
        proto,
        bindings,
        tree.firstToken(node),
        tree.lastToken(node),
        0,
    );
}

/// Append the storage an invocation's CALLEE was reached through.
/// A plain name is the function being invoked, not storage it holds,
/// so it contributes nothing: charging it would put a function-pointer
/// parameter on the grow list of every fn that calls through it.
/// Anything else reaches storage — `@field(o, "push")` names a field
/// OF what the builtin was handed, `o.make().replace(…)` hands over
/// what the inner call was reached through — and an expression this
/// file cannot follow (`xs[i]`, `(cb)`) stays `.unknown`, which is
/// what it is.
///
/// A callee that is itself a call value chains (`f()(g())(…)`), so
/// the walk is bounded by the same `max_owner_depth` every other
/// chain in this file uses.  Exhausting it records `.unknown` — what
/// an expression this deep hands over — rather than dropping the
/// callee, whose storage would then go uncharged.
fn appendCalleeOperands(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    callee: Ast.Node.Index,
    out: *std.ArrayListUnmanaged(StorageOwner),
    depth: u8,
) !void {
    if (depth >= max_owner_depth) {
        try out.append(arena, .unknown);
        return;
    }
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(callee);
    if (first == tree.lastToken(callee) and tags[first] == .identifier) return;
    var call_buf: [1]Ast.Node.Index = undefined;
    if (tree.fullCall(&call_buf, callee)) |sub| {
        try appendCalleeOperands(arena, tree, proto, bindings, sub.ast.fn_expr, out, depth + 1);
        for (sub.ast.params) |p| try out.append(arena, try operandOwner(arena, tree, proto, bindings, p));
        return;
    }
    var params_buf: [2]Ast.Node.Index = undefined;
    if (tree.builtinCallParams(&params_buf, callee)) |params| {
        for (params) |p| try out.append(arena, try operandOwner(arena, tree, proto, bindings, p));
        return;
    }
    // A grouped or computed callee — `(cb)`, `xs[i].replace` — is
    // rooted as the expression it is, which is what the operand rules
    // make of it: whatever it names, or `.unknown`.
    try out.append(arena, try operandOwner(arena, tree, proto, bindings, callee));
}

/// The argument slots of an `@call` tuple, when the third argument is
/// the literal `@call`'s grammar puts there: `.{ … }`, which the AST
/// holds as an anonymous struct- or array-init, whose fields (or
/// elements) ARE the arguments.
///
/// The literal's IDENTITY is what this reads, not its source text.  A
/// search for a `{` takes the first one it finds, including one that
/// belongs to an expression inside an argument
/// (`@call(.auto, cb, makeArgs(.{ .a = 1 }))`), and splits that
/// expression's own tokens into argument slots.
///
/// `null` means "not a literal this file can take apart": a named or
/// forwarded tuple (`const args = .{ list, value }; @call(.auto, cb,
/// args)`), a computed one, a typed struct init that is not an
/// argument tuple at all.  The invocation still ran, so its caller
/// roots the value whole rather than dropping the call.
fn tupleArgumentSlots(
    tree: *const Ast,
    buf: *[2]Ast.Node.Index,
    node: Ast.Node.Index,
) ?[]const Ast.Node.Index {
    // The two forms share one buffer: only one of them can match a
    // given node's tag.
    if (tree.fullArrayInit(buf, node)) |init| {
        if (init.ast.type_expr != .none) return null;
        return init.ast.elements;
    }
    if (tree.fullStructInit(buf, node)) |init| {
        if (init.ast.type_expr != .none) return null;
        return init.ast.fields;
    }
    return null;
}

/// True iff the token pass in `inferGrowEffects` already recorded the
/// call whose final callee token is `callee` — its adjacency rule,
/// asked about the token the AST named instead of about a scan.
fn adjacencyPassReadIt(
    tags: []const std.zig.Token.Tag,
    callee: Ast.TokenIndex,
) bool {
    if (tags[callee] != .identifier) return false;
    // A bare `name(` needs nothing before it.  A `recv.name(` needs the
    // receiver to be a plain name for the pass to reach the call at
    // all: `xs[i].name(` and `f().name(` are exactly the shapes it
    // skips.
    if (callee == 0 or tags[callee - 1] != .period) return true;
    return callee >= 2 and tags[callee - 2] == .identifier;
}

/// True iff `tok` falls inside one of `ranges` — the token span of a
/// declaration this body only NAMES, whose effects are its own.
fn tokenInRanges(ranges: []const TokenRange, tok: Ast.TokenIndex) bool {
    for (ranges) |r| {
        if (tok >= r.first and tok <= r.last) return true;
    }
    return false;
}

/// True iff `tok` is in the body being analyzed rather than in a
/// declaration that body only names.
fn bodyOwnsToken(
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    nested: []const TokenRange,
    tok: Ast.TokenIndex,
) bool {
    if (tok < body_first or tok > body_last) return false;
    return !tokenInRanges(nested, tok);
}

/// Record the invocations in `body` that no identifier runs into a
/// `(` with: an indirect call through a value
/// (`@call(.auto, cb, .{ … })`), a grouped or computed callee, a
/// method reached through an index or a call result
/// (`xs[i].push(v)`, `o.make().replace(v)`).
///
/// Those leave nothing behind in a token pass, so a summary built from
/// that answer reads the fn as growing nothing at all.  They are found
/// through the AST instead, where an invocation IS a node: an `if` /
/// `while` condition, a grouped condition and a fn pointer merely held
/// in a declaration are not invocations, and are not invented as ones.
/// A nested declaration's body is skipped for the same reason the
/// token pass skips it — that fn has an entry of its own.
///
/// Every one of them is recorded `.unresolved`.  Its name is a method
/// name reached through a receiver this file cannot root, or no name
/// at all for an indirect call, so the cache must never dispatch it to
/// a declaration that happens to share it; what it may reallocate is
/// the storage the invocation was handed, which is what `.unresolved`
/// charges.
///
/// The `@call` argument tuple is read as the AST node it is, never as
/// source text: the entries of a `.{ … }` literal ARE the arguments,
/// and a tuple named, forwarded or computed is charged as the whole
/// value it is.  How its arguments are spelled never removes the
/// invocation from the summary.
///
/// `unknown` is the one thing an `@call` costs on its own.  Nothing in
/// this file resolves the callback behind it, so what it reallocates
/// is not only the storage it was handed — a callback reached through
/// a global, a table, or a field may move storage this fn never held
/// at all, and an EMPTY argument list does not stop it.  Every actual
/// `@call` execution therefore marks the fn as having grown something
/// unattributable, while the call entry keeps carrying the precise
/// paths its own arguments root to.
fn collectIndirectInvocations(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    body_first: Ast.TokenIndex,
    body_last: Ast.TokenIndex,
    nested: []const TokenRange,
    calls: *std.ArrayListUnmanaged(GrowCall),
    unknown: *bool,
) !void {
    const tags = tree.tokens.items(.tag);
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        // The tag decides whether this node can be an invocation at
        // all, and both tokens below are reached without walking the
        // node's own subtree — `firstToken` would, once per node in
        // the file, for every fn in it.
        switch (tree.nodeTag(node)) {
            .call, .call_one, .call_comma, .call_one_comma => {
                // The call's `(` is its main token, and reaching it
                // costs a data read rather than a walk of the node's
                // own subtree — which is what every node in the file
                // would otherwise pay, for every fn in it.
                if (!bodyOwnsToken(body_first, body_last, nested, tree.nodeMainToken(node))) continue;
                var call_buf: [1]Ast.Node.Index = undefined;
                const call = tree.fullCall(&call_buf, node) orelse continue;
                const callee = call.ast.fn_expr;
                // The token the call's `(` follows: what a call index
                // keys on, and what the token pass's adjacency rule
                // reads.
                const callee_tok = tree.lastToken(callee);
                if (adjacencyPassReadIt(tags, callee_tok)) continue;
                // A grow-vocabulary method is attributed by the grow
                // pass, from the receiver ITS adjacency rules reach.
                // Recording it again here would charge the same site
                // from a second, weaker reading.
                if (receiver_mod.isArrayListGrowMethodName(tree.tokenSlice(callee_tok))) continue;
                var args: std.ArrayListUnmanaged(StorageOwner) = .empty;
                try appendCalleeOperands(arena, tree, proto, bindings, callee, &args, 0);
                for (call.ast.params) |p| {
                    try args.append(arena, try operandOwner(arena, tree, proto, bindings, p));
                }
                try calls.append(arena, .{
                    .callee_token = callee_tok,
                    // A computed callee (`xs[i].push`, `(cb)`) names
                    // nothing this file could dispatch on, and must
                    // never be mistaken for a declaration sharing it.
                    .name = if (tags[callee_tok] == .identifier)
                        tree.tokenSlice(callee_tok)
                    else
                        "",
                    .kind = .unresolved,
                    .args = try args.toOwnedSlice(arena),
                });
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                // The `@` of a builtin is the first token of the call.
                const at = tree.nodeMainToken(node);
                if (!bodyOwnsToken(body_first, body_last, nested, at)) continue;
                // `@call` runs a value this body only holds: no
                // declaration to read, and nothing in its spelling
                // says what that value does.  What the body does know
                // is the storage the invocation was handed — through
                // the callee, and through the argument tuple.
                if (!std.mem.eql(u8, tree.tokenSlice(at), "@call")) continue;
                var params_buf: [2]Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&params_buf, node) orelse continue;
                if (params.len < 3) continue;
                // The callback is a value: this file cannot resolve
                // what it does, and what it does may reach storage
                // past the arguments below — a global, a table, a
                // field — which an empty `.{}` does not stop it from
                // moving.
                unknown.* = true;
                var args: std.ArrayListUnmanaged(StorageOwner) = .empty;
                try appendCalleeOperands(arena, tree, proto, bindings, params[1], &args, 0);
                var slots_buf: [2]Ast.Node.Index = undefined;
                if (tupleArgumentSlots(tree, &slots_buf, params[2])) |slots| {
                    // The literal IS `@call`'s argument list, so each
                    // of its entries is one argument.  `.{}` hands
                    // over nothing, and leaves the invocation itself
                    // as the only thing it proves.
                    for (slots) |slot| {
                        try args.append(arena, try operandOwner(arena, tree, proto, bindings, slot));
                    }
                } else {
                    // A tuple named, forwarded or computed elsewhere.
                    // Its entries cannot be read off here, but it was
                    // still handed to something that may reallocate
                    // what it names, so it is charged as the whole
                    // value it is — never as "no arguments".
                    try args.append(arena, try operandOwner(arena, tree, proto, bindings, params[2]));
                }
                try calls.append(arena, .{
                    .callee_token = at,
                    .name = "@call",
                    .kind = .unresolved,
                    .args = try args.toOwnedSlice(arena),
                });
            },
            else => continue,
        }
    }
}

/// One entry per comma-separated argument in `[start, end]`, each
/// resolved to the parameter-rooted storage it came from.  A `receiver`
/// is prepended for a method call, whose first parameter is the
/// receiver rather than an argument.  Shared with the rules that ask
/// "which of my parameters does this callee reach through".
pub fn argOwners(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    receiver: ?StorageOwner,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) ![]const StorageOwner {
    var out: std.ArrayListUnmanaged(StorageOwner) = .empty;
    if (receiver) |r| try out.append(arena, r);
    if (start > end) return out.toOwnedSlice(arena);
    const tags = tree.tokens.items(.tag);
    var arg_start: Ast.TokenIndex = start;
    var depth: i32 = 0;
    var t: Ast.TokenIndex = start;
    while (t <= end) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket, .l_brace => depth += 1,
            .r_paren, .r_bracket, .r_brace => depth -= 1,
            .comma => if (depth == 0) {
                try out.append(arena, try ownerOfExpr(arena, tree, proto, bindings, arg_start, t - 1, 0));
                arg_start = t + 1;
            },
            else => {},
        }
    }
    try out.append(arena, try ownerOfExpr(arena, tree, proto, bindings, arg_start, end, 0));
    return out.toOwnedSlice(arena);
}

/// Which of this fn's parameter-rooted storage paths its body may grow.
///
/// A grow method invoked as a METHOD (`o.aliases.append(…)`) is
/// attributed to the storage its receiver names, through any number of
/// by-value header copies — `var copy = tally.*; copy.entries.append(x)`
/// still moves `tally`'s buffer, because the copy shares it.
///
/// A grow method used as a FREE function (`ensureCapacity(gpa, &list,
/// n)`) is a reallocation too, and so is a call this file cannot
/// resolve at all: what an arbitrary free function does with the
/// storage it is handed is not decided by its name.  Calls are
/// returned here rather than resolved so
/// `FileCache.resolveGrowPathsOne` can fold the ones it CAN name in,
/// charge the rest to what the call handed over, and drive the
/// transitive fixed point.
///
/// A METHOD call whose receiver cannot be rooted on a parameter is
/// returned for its ARGUMENTS alone (`GrowCall.kind == .unresolved`):
/// the receiver is charged where it was built, and a fresh header
/// proves only that the callee moves that one — never that it leaves
/// the storage it was passed.
///
/// An invocation the token pass cannot see at all — a callee that is
/// a value (`@call(.auto, cb, .{ … })`), a grouped or computed one, a
/// method through an index or a call result — is returned the same
/// way, from the AST: see `collectIndirectInvocations`.  What such a
/// call does is not decided by any name in it, so it may reallocate
/// what it was handed and nothing else.
pub fn inferGrowEffects(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    bindings: *const local_bindings.LocalBindings,
) !GrowEffects {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var paths: std.ArrayListUnmanaged(GrowPath) = .empty;
    var calls: std.ArrayListUnmanaged(GrowCall) = .empty;
    var claims: std.ArrayListUnmanaged(FreshClaim) = .empty;
    // Token spans of the declarations this body only names, shared
    // with the AST pass below so it attributes their calls to them.
    var nested: std.ArrayListUnmanaged(TokenRange) = .empty;
    var unknown = false;
    // Set when this body holds an invocation the token pass cannot
    // read, so the AST pass has something to look for.  Reading the
    // whole AST once per fn would cost more than the token pass
    // itself, and a body that CANNOT hold one is the common case.
    var needs_ast_pass = false;

    var t = first;
    while (t + 2 <= last) : (t += 1) {
        // An invocation this pass cannot read is a `(` whose callee is
        // not `<name>` after a plain-name receiver — the exact case
        // the recording rule below skips, plus `@call`, which runs a
        // value this body holds.  Reading the whole AST once per fn
        // costs more than this pass itself, and a body that holds no
        // such call is the common case.
        if (tags[t + 1] == .l_paren) {
            switch (tags[t]) {
                .identifier => if (t > first and tags[t - 1] == .period and
                    (t < first + 2 or tags[t - 2] != .identifier))
                {
                    needs_ast_pass = true;
                },
                .r_paren, .r_bracket, .r_brace => needs_ast_pass = true,
                .builtin => if (std.mem.eql(u8, tree.tokenSlice(t), "@call")) {
                    needs_ast_pass = true;
                },
                else => {},
            }
        }
        if (tags[t] == .keyword_fn) {
            const after = tokens.skipNestedFn(tags, t, last);
            try nested.append(arena, .{ .first = t, .last = after });
            t = after;
            continue;
        }
        if (tags[t] == .period and tags[t + 1] == .identifier and tags[t + 2] == .l_paren and
            receiver_mod.isArrayListGrowMethodName(tree.tokenSlice(t + 1)))
        {
            switch (try growBaseOfExpr(arena, tree, proto, bindings, receiverStart(tags, t, first), t - 1)) {
                // Storage this fn may have built for itself: the
                // resolver decides, and a claim it cannot prove is
                // charged as unattributed storage below.
                .unproven => |claim| try claims.append(arena, claim),
                .storage => |s| switch (s) {
                    .unknown => unknown = true,
                    .param => |p| try paths.append(arena, .{ .param = p.param, .field = p.path }),
                },
            }
            continue;
        }
        if (tags[t] != .identifier or tags[t + 1] != .l_paren) continue;

        const call_end = tokens.matchParen(tags, t + 1, last) orelse continue;
        const name = tree.tokenSlice(t);
        var receiver: ?StorageOwner = null;
        var kind: @FieldType(GrowCall, "kind") = .bare;
        var qualifier: []const u8 = "";
        if (t > first and tags[t - 1] == .period) {
            if (t < first + 2 or tags[t - 2] != .identifier) continue;
            // A grow-vocabulary method is already recorded as a grow
            // site above, from the storage its receiver names.
            if (receiver_mod.isArrayListGrowMethodName(name)) continue;
            const recv_first = receiverStart(tags, t - 1, first);
            const base = try growBaseOfExpr(
                arena,
                tree,
                proto,
                bindings,
                recv_first,
                t - 2,
            );
            switch (base) {
                // A receiver this fn may have built for itself moves
                // only that storage — but that says nothing about the
                // ARGUMENTS, which the callee can reallocate whatever
                // it was handed.  The call is kept for them, as a name
                // that must never reach a file-level declaration
                // sharing it.
                .unproven => kind = .unresolved,
                // A receiver this fn was not handed — a global, a
                // call result, a loop capture.  When it is a single
                // identifier it may name a MODULE, and then this is a
                // free function in another file rather than a method
                // on storage; the cache resolves it, and charges what
                // the call hands over when it cannot.  A longer chain
                // (`a.b.c(`) names a field of something else and is
                // charged the same way.
                .storage => |s| switch (s) {
                    .unknown => {
                        // `recv_first` is the FIRST token of the
                        // receiver path and `t - 1` its `.`, so a
                        // receiver that is exactly one identifier
                        // spells `qualifier . name (` — two segments
                        // from `recv_first` to `t`.  Anything longer
                        // (`a.b.c(`) reaches a field of something
                        // else, and a module never does.
                        if (t == recv_first + 2) {
                            kind = .qualified;
                            qualifier = tree.tokenSlice(recv_first);
                        } else {
                            kind = .unresolved;
                        }
                    },
                    // A NESTED receiver (`o.inner.method()`) is kept:
                    // the cache resolves the field's type and folds
                    // the callee's paths in, or charges them to the
                    // receiver's storage when it cannot.
                    .param => |p| {
                        receiver = .{ .param = p };
                        kind = .method;
                    },
                },
            }
        }
        try calls.append(arena, .{
            .callee_token = t,
            .name = name,
            .kind = kind,
            .qualifier = qualifier,
            .args = try argOwners(arena, tree, proto, bindings, receiver, t + 2, call_end - 1),
        });
    }
    if (needs_ast_pass) {
        try collectIndirectInvocations(arena, tree, proto, bindings, first, last, nested.items, &calls, &unknown);
    }
    return .{
        .paths = try paths.toOwnedSlice(arena),
        .unknown = unknown,
        .calls = try calls.toOwnedSlice(arena),
        .claims = try claims.toOwnedSlice(arena),
    };
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
