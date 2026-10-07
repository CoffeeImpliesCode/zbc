//! Per-fn behavioral summary. Body-only facts are syntactic; independent
//! self-allocation ownership also reads resolved allocator provenance.
//! No annotations assert semantics — the author can suppress a finding
//! via `// zbc-disable-line:`.
//!
//! Summary fields are deliberately COARSE.  Each one answers a
//! specific question a downstream consumer asks:
//!
//!   returns                — "does the call leak ownership to the caller?"
//!   takes_ownership_of     — "does the call invalidate one of its args?"
//!   is_noreturn            — "does the call terminate the basic block?"
//!   allocates              — "does the body call into an allocator?"
//!
//!   freed_paths            — "WHICH parameter-rooted storage does this
//!                            body hand back, and is it the parameter
//!                            itself or one of its fields?"  Read by a
//!                            call site that must tell "the callee took
//!                            my buffer" from "the callee freed one
//!                            field of the object I still hold".  A name
//!                            the body only reaches through a capture is
//!                            followed to the field it was read out of,
//!                            so `if (self.slot) |image| self.gpa.
//!                            destroy(image)` releases the caller's
//!                            `slot` rather than a mystery blob.
//!
//!   written_paths          — "WHICH parameter-rooted storage does this
//!                            body write?"  Read by a consumer deciding
//!                            whether a condition read from the same
//!                            receiver is still true after a call on it.
//!
//!   grow_paths            — "WHOSE buffer can move?": the
//!                            parameter-rooted storage paths this fn (or
//!                            anything it reaches) can grow, next to
//!                            `may_grow_collections`'s "can anything move?"
//!
//! `freed_paths` and `written_paths` answer about THIS body's own
//! spelled sites only.  A callee's effects, in this file or another, are
//! folded in by `FileCache`; see `FieldEffects` for the exact contract.
//!
//! `grow_paths` and `may_grow_collections` are kept CONSISTENT: after
//! `FileCache.resolveTransitiveTakes` Phase 8,
//! `grows_unknown_path == true` implies `may_grow_collections ==
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
const numeric_nodes = @import("numeric_nodes.zig");
const budget_mod = @import("../budget.zig");
const TokenIndex = tokens.TokenIndex;
const TokenTag = tokens.TokenTag;
/// Reject source offsets at the u32 limit before admitting the exclusive token bound.
pub fn checkedTokenCount(source_len: usize, token_len: usize) error{SourceTooWide}!TokenIndex {
    if (source_len >= std.math.maxInt(u32)) return error.SourceTooWide;
    return std.math.cast(TokenIndex, token_len) orelse return error.SourceTooWide;
}

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
    /// into source.  `FileCache.filterMayFreeFields` resolves it on the
    /// field's own type and keeps the entry only when that method's own
    /// summary says it takes its receiver (`.free(self)` /
    /// `.destroy(self)`, or a chain of them).  The name alone proves
    /// nothing: a `deinit` that only forwards leaves the storage its
    /// receiver holds alive.
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

/// Ordered operations on one parameter payload. Alternatives retain branch
/// correlation; two releases are not collapsed into one release.
pub const StorageOperation = struct {
    path: ParamPath,
    /// Entry releases name the payload present on call entry, even after a
    /// replace. Current releases name the latest published payload. Replace
    /// is emitted only for a certified independent, live heap allocation.
    kind: enum { release_entry, replace, release_current },
    /// Formal allocator provenance for replace; null removes exact replay.
    allocator: ?ParamPath = null,
    /// Exact relative payload generation for a release. Zero is entry;
    /// each replacement advances the generation of this path by one.
    /// Null on a current release means the current generation at that step.
    version: ?usize = null,
    /// Positive identity evidence survives an opaque tail even when the
    /// whole trace is incomplete. Ambiguous projections cannot supply it.
    identity_proved: bool = true,
};

pub const StorageOutcome = struct {
    operations: []const StorageOperation = &.{},
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

/// One ALLOCATION, placed in the coordinate space of the fn that
/// holds the loop and makes the call — the answer to "whose buffer
/// can this value reach?".
///
/// `StorageOwner` answers a narrower question ("which of MY
/// parameters does this come from") and answers `.unknown` for
/// everything it cannot root.  That is the right answer for a
/// parameter-indexed effect, and the wrong one for a
/// disjointness question: a loop capture and a container-level
/// constant are not the same storage, and neither is a local object
/// the fn itself constructed.  Collapsing them into `.unknown` makes
/// every one of them look like it could be somebody's list.
pub const Placement = union(enum) {
    /// Reached through parameter `param` of the enclosing fn, at
    /// `path` (`""` is the parameter's own storage).
    param: ParamPath,
    /// An object a LOCAL of this fn declared.  Only a local whose
    /// initializer CONSTRUCTED it reaches here: a local that named
    /// something else is a header copy and is followed to its source.
    /// `token` is the local's name token, which is what makes
    /// `&local` an address inside an object this fn laid out.
    local: struct { token: Ast.TokenIndex },
    /// A container-level declaration — a `const` or `var` this file
    /// declares outside every fn.  Shared state: a callee in this
    /// file can name it without ever being handed it.
    shared,
    /// A by-value value copied out of an iterated buffer.  The copy
    /// is the element's OWN storage, never the buffer it was read
    /// from, so an element argument is not mapped back onto the
    /// list the loop captured.
    element,
    unknown,
};

/// One parameter-rooted storage path whose backing buffer a fn may
/// grow.  `field` is `""` when the parameter's own storage is grown
/// (`fn g(list: *List) { list.append(1); }`) and a dotted path
/// otherwise (`fn g(o: *Oracle) { o.aliases.append(1); }`).  A path
/// stored in an `FnSummary` owns its slice through the cache that built
/// it; a path built while folding a round is that round's to release.
pub const GrowPath = struct {
    param: u32,
    field: []const u8,
};

/// A call in the body whose callee's grow paths fold into the caller's.
/// Produced by `inferGrowEffects`, consumed by
/// `FileCache.resolveGrowPathsOne` — never stored in an `FnSummary`.
pub const GrowCall = struct {
    /// Callee expression's main token, matching FileCache's call index.
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
    /// A grow site exists that this fn reached through a NAME IT
    /// INTRODUCED ITSELF — a container-level `var`, a threadlocal, a
    /// header an opaque constructor may have handed back, or an
    /// indirect invocation that reaches past its arguments.  Only a
    /// caller whose own storage is such a name can be reached this
    /// way, and a consumer MUST NOT discharge it by mapping
    /// arguments.
    unknown: bool = false,
    /// Grow sites charged to a parameter this fn was HANDED and
    /// could not root on one: an index, a call result, a constructor
    /// result.  The storage belongs to the CALLER, and the index says
    /// which handover absorbed it — which is exactly what a caller
    /// comparing its own buffer is able to decide and
    /// `unknown` could never tell it.
    unplaced: []const u32 = &.{},
    calls: []const GrowCall = &.{},
    /// Grow sites whose receiver may be storage this fn built for
    /// itself.  Each is recorded here instead of in `paths` / `unknown`
    /// so the resolver can still prove it fresh; whatever it cannot
    /// prove becomes unknown storage.
    claims: []const FreshClaim = &.{},
};

/// The parameter-rooted storage a body's OWN sites touch: what it
/// hands back to an allocator, and what it writes.
///
/// DIRECT ONLY.  Every entry is a site this body SPELLS OUT.  A callee
/// is not in these lists and never will be: whether the storage behind
/// a call is released or rewritten depends on the DECLARATION of what
/// the body calls — including one in another file — which only
/// `FileCache` can read.  What a body decides here is the part no
/// resolver can add later, so it is exactly the part that must not
/// depend on one.
///
/// WHAT A PATH IS.  `""` is the parameter's OWN storage and a dotted
/// source path is storage below it, so `gpa.free(self)` frees
/// `{0, ""}` while `self.gpa.free(self.items)` frees `{0, "items"}`;
/// `self.slot = null` writes `{0, "slot"}` and `self.* = other` writes
/// `{0, ""}` — the whole object the pointer names.  A path the body
/// spelled is a slice of `tree.source` and keeps the spacing the file
/// used (`self.a . b` reads `"a . b"`), exactly like the paths
/// `ownerOfExpr` hands the grow passes; only a path that had to be
/// JOINED through an alias is allocated.  LIFETIME: both slices are
/// `arena`-owned, and a caller MUST keep `tree` alive for as long as
/// it reads them.
///
/// AN EMPTY LIST IS NOT PURITY.  It means this body spelled no such
/// site — nothing more.  A store through an index or a computed name,
/// a write to a local this pass cannot root, a `??=`, a destructuring
/// assign, a store inside a nested declaration, and EVERYTHING a
/// callee does are all absent from these lists.  A consumer MUST
/// therefore keep reading "may do it" for a path that is not listed,
/// and must fold callees itself; emptiness is an observation, never a
/// proof.
pub const FieldEffects = struct {
    /// Storage this body hands back as an EXPLICIT `.free(…)` /
    /// `.destroy(…)` argument.  The argument is the value being
    /// released and the RECEIVER is the allocator handing the memory
    /// back — reading the receiver instead is what made
    /// `self.gpa.free(self.items)` claim its own receiver, and it is
    /// why this list names `items` while `self.gpa` keeps the storage
    /// it holds.
    freed_paths: []const ParamPath = &.{},
    /// Storage this body WRITES: a direct store (`self.slot = null`),
    /// a compound one (`self.count += 1`), or a whole-object store
    /// through a pointer (`self.* = other`).
    written_paths: []const ParamPath = &.{},
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
    /// Parameter-rooted storage this fn's body releases through an
    /// explicit `.free(…)` / `.destroy(…)` ARGUMENT — `{0, "items"}`
    /// for `self.gpa.free(self.items)`, `{0, ""}` for `gpa.free(self)`.
    /// The allocator receiver is never an entry: it hands memory back,
    /// it does not lose it.  Produced by `inferFieldEffects`; slice is
    /// owned by the cache's summary arena.  Direct sites only — see
    /// `FieldEffects` for the folding and the emptiness contract.
    freed_paths: []const ParamPath = &.{},
    /// Parameter-rooted storage this fn's body writes — `{0, "slot"}`
    /// for `self.slot = null`, `{0, ""}` for `self.* = other`.  A
    /// write through an ALIAS is followed to its source, so
    /// `var copy = self; copy.slot = null` writes the same `{0,
    /// "slot"}` the direct spelling does.  Produced by
    /// `inferFieldEffects`; slice is owned by the cache's summary
    /// arena.  Direct sites only — see `FieldEffects`.
    written_paths: []const ParamPath = &.{},
    /// Field names that a constructor allocates and stores into the
    /// returned struct literal — i.e. `return .{ .X = alloc(), ... }`.
    /// Lets call sites mint synthetic `field_assign(local, X,
    /// .heap_alloc)` so subsequent `local.X` reads see correct UAF
    /// state.  Slice is owned by the FnSummaryCache arena.
    result_heap_fields: []const []const u8 = &.{},
    /// Body creates an instance of its own containing type through the
    /// canonical SDK Allocator.create and may own the heap allocation.
    /// Known arena/buffer backing borrows its owner's lifetime instead.
    /// Pointer-bearing instance fields do not remove this obligation.
    /// Filled by cache-aware inference; false for top-level functions.
    heap_allocates_self: bool = false,
    /// True only when the complete return-dependency scan saw a return
    /// and proved no parameter occurs in any return expression.
    /// Unknown local aliases, calls, and untracked formals prevent proof.
    result_independent_of_args: bool = false,
    /// Positive parameter dependencies found in return expressions.
    /// Bit 31 records a return statement; bits 0–15 cover the bounded
    /// formal-name scan. Absence of a bit is NOT proof unless the return
    /// scan is complete or that input has a separate no-use certificate.
    /// Bits 16–30 are not inferred.
    result_params_in_return: u32 = 0,
    /// Every return expression and formal was understood by the bounded
    /// scan. False for untracked formals or unresolved provenance, even
    /// when some positive dependency bits are known.
    result_params_complete: bool = false,
    /// Formals absent from the entire signature and body apart from their
    /// declaration and direct discard statements. These inputs cannot feed
    /// a result, even when another input has unresolved return provenance.
    /// This is not purity: consumers still need canonical parameter effects.
    result_params_unused: u16 = 0,
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
    /// The half of `grows_unknown_path` this fn reached through a
    /// name it introduced ITSELF — a container-level `var`, a
    /// threadlocal, a header an opaque constructor may have handed
    /// back, an indirect invocation that reaches past its arguments.
    /// Defaults TRUE, the conservative direction: a summary that has
    /// not been through Phase 8 places nothing, and a consumer MUST
    /// NOT read this as "the call handed it something a caller could
    /// have mapped".
    grows_self_named: bool = true,
    /// The other half: grows charged to parameters this fn was handed
    /// and could not root.  Each index is a HANDOVER — the storage is
    /// the caller's, and a caller that mapped its arguments has seen
    /// every one of them.  Kept apart from `grows_self_named`
    /// because a caller can discharge the second and never the
    /// first: a callee's own global is reachable without being
    /// handed anything, so an argument map says nothing about it.
    unplaced_args: []const u32 = &.{},
    /// Internal flag: true iff FileCache.summaryOfFn has fully
    /// populated this entry (cheap + deep inference).  Distinct
    /// from "no fields detected" — without this flag, fns with
    /// genuinely empty `may_free_fields` would be indistinguishable
    /// from never-resolved and would get re-inferred (wiping any
    /// R10 transitive updates).  Not part of the public contract;
    /// consumers should treat the summary as resolved when they
    /// retrieve it via FileCache.
    _resolved: bool = false,

    /// === Normal-success cleanup certificates (positive authenticated effects) ===
    ///
    /// Definite effects hold on every successful return or fallthrough.
    /// MAY effects include conditional cleanup, including catch and else
    /// arms that rejoin a successful path. Errdefer runs only on error exits.
    /// Unmodelled control or callees clear definite claims, not observed MAY.
    ///
    /// `*_definite_*` are intersected across ALL reachable successful
    /// normal exits.  A path that is freed on one exit but not another
    /// is NOT definite — it goes to `*_may_*` instead.  An empty
    /// `*_definite_*` does NOT mean purity; it means no path could be
    /// proven freed on every exit.
    ///
    /// `*_may_*` are the union of effects that MAY occur on some normal
    /// exit.  A path in `*_may_*` but not `*_definite_*` means the
    /// cleanup is conditional.  Consumers MUST NOT treat absence from
    /// `*_may_*` as "never freed" — unmodelled control flow may still
    /// execute it.
    ///
    /// Completeness requires a reachable normal exit and known effects on
    /// every reachable path. Unknown control or callees make it false.
    /// Source, allocation, and budget failures instead propagate as errors.
    ///
    /// `retained_owned_params` is the set of formal parameter indices
    /// (0 = receiver) whose exact FIELD ownership is certified retained
    /// across ALL successful normal exits.  A formal is retained when
    /// the function returns an aggregate that owns the storage, or
    /// assigns/returns it to a location whose lifetime outlives the
    /// call, and FileCache's `retainedStorageAt` confirms the same-owner
    /// cleanup relation.  Distinct from `takes_ownership_of` (immediate
    /// consumption) — retention means the caller's storage is NOT
    /// consumed and remains valid after the call.
    ///
    /// All arrays are owned by the `summary_arena` passed to the
    /// inference function.  Nested path/field/method strings are also
    /// arena-owned.  Inference MUST allocate in the supplied arena.
    ///
    /// SourceTooWide / OOM / AnalysisBudgetExceeded propagate; they are
    /// NOT caught and turned into conservative answers.
    normal_success_definite_freed_paths: []const ParamPath = &.{},
    normal_success_may_freed_paths: []const ParamPath = &.{},
    normal_success_definite_free_fields: []const FieldFree = &.{},
    normal_success_may_free_fields: []const FieldFree = &.{},
    normal_success_effects_complete: bool = false,
    /// Complete ordered alternatives cover every reachable parameter release
    /// and certified replacement. Identity consumers use these instead of
    /// the current-field union above; unknown calls remove this certificate.
    normal_success_storage_outcomes: []const StorageOutcome = &.{},
    normal_success_storage_effects_complete: bool = false,
    retained_owned_params: []const u32 = &.{},
    /// Error exits use a separate intersection and union. They include prior
    /// effects, normal defers, active errdefers, and error-outcome call effects.
    /// With no reachable error exit, completeness is false and no proof exists.
    error_definite_freed_paths: []const ParamPath = &.{},
    error_may_freed_paths: []const ParamPath = &.{},
    error_definite_free_fields: []const FieldFree = &.{},
    error_may_free_fields: []const FieldFree = &.{},
    error_effects_complete: bool = false,
    /// Error alternatives are certified separately; a normal replacement
    /// cannot appear on an allocation failure before publication.
    error_storage_outcomes: []const StorageOutcome = &.{},
    error_storage_effects_complete: bool = false,
    /// Whether this result may carry parameter `param`: known positive
    /// dependency, proved absence, or unknown. No return is not a proof.
    pub fn returnedParamDependency(self: *const FnSummary, param: u32) ?bool {
        if (param >= 31) return null;
        const bit = @as(u32, 1) << @intCast(param);
        if ((self.result_params_in_return & bit) != 0) return true;
        if (param >= 16 or (self.result_params_in_return & SAW_RETURN_BIT) == 0) return null;
        if ((self.result_params_unused & @as(u16, @intCast(bit))) != 0) return false;
        if (!self.result_params_complete) return null;
        return false;
    }
};

/// Infer a summary for `body`.  Conservative: when unclear, returns
/// `.unknown` / null / false — never guesses.  `proto` carries the
/// param list so `borrowed_from` can resolve to a param index.
///
/// Body-only inference: only fills fields that can be determined
/// from the proto + body alone. `heap_allocates_self` requires the
/// containing type and the cache's allocation-provenance proof.
/// `may_free_fields` / `result_heap_fields` need allocations to land
/// somewhere stable; the cache fills those separately.
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

    // Second pass: the grow vocabulary written as a FREE function.
    // `ensureCapacity(gpa, &list, n)` reallocates exactly as
    // `list.ensureCapacity(n)` does, so the coarse flag has to see
    // both: leaving the bare form out made the coarse view deny a
    // reallocation the precise view could see.
    //
    // The whole body is scanned — stopping at the first match loses
    // every grow site written after it.
    t = first;
    while (t + 1 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (t > first and tags[t - 1] == .period) continue;
        if (receiver_mod.isArrayListGrowMethodName(tree.tokenSlice(t))) {
            out.may_grow_collections = true;
        }
    }

    // Third pass: bare exit-callback-register calls —
    // `add_exit_callback(fn_ptr)` is a top-level (non-method) bare
    // call.  Same free-function shape as the grow vocabulary above, but
    // a different claim: this call publishes the body it is handed to a
    // scheduler that may run it on a thread other than the one that
    // registered it.  A method-shaped call is not a registration site
    // here — `self.addExitCallback(cb)` registers a receiver's own
    // callback — so this pass reads only the bare spelling, and it stops
    // at the first one because the flag records that at least one exists.
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

    const ret = inferResultParamsInReturn(tree, proto, first, last);
    out.result_params_in_return = ret.mask;
    out.result_params_complete = ret.complete;
    out.result_params_unused = inferUnusedResultParams(tree, proto, body);
    out.result_independent_of_args =
        ret.complete and (ret.mask & SAW_RETURN_BIT) != 0 and
        (ret.mask & ~SAW_RETURN_BIT) == 0;

    return out;
}

/// Sentinel bit in `result_params_in_return`: set when the body has
/// at least one `return` statement (distinguishes "saw returns, no
/// params embedded" from "no returns found at all").
pub const SAW_RETURN_BIT: u32 = 1 << 31;

/// Bounded positive dependency scan, not a purity or fresh-storage proof.
/// Unsupported provenance preserves known bits but prevents negative proof.
fn inferResultParamsInReturn(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) struct { mask: u32, complete: bool } {
    const tags = tree.tokens.items(.tag);
    var param_buf: [16]?[]const u8 = @splat(null);
    var n_params: usize = 0;
    var complete = true;
    var it = proto.iterate(tree);
    while (it.next()) |p| {
        if (n_params < param_buf.len) {
            if (p.name_token) |nt| {
                param_buf[n_params] = tree.tokenSlice(nt);
            } else {
                complete = false;
            }
        } else {
            complete = false;
        }
        // Unnamed formals still occupy a position in the call.
        n_params += 1;
    }
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
        var pd: i32 = 0;
        while (u <= last) : (u += 1) {
            switch (tags[u]) {
                .l_paren, .l_bracket, .l_brace => pd += 1,
                .r_paren, .r_bracket, .r_brace => {
                    if (pd == 0) break;
                    pd -= 1;
                },
                .semicolon => if (pd == 0) break,
                .builtin => complete = false,
                .identifier => {
                    // A call (including recursion) cannot prove absence:
                    // its result may forward an argument or hidden alias.
                    if (u < last and tags[u + 1] == .l_paren) complete = false;
                    if (u > 0 and tags[u - 1] == .period) continue;
                    const name = tree.tokenSlice(u);
                    var matched = false;
                    for (param_buf, 0..) |maybe_param, i| {
                        const param = maybe_param orelse continue;
                        if (std.mem.eql(u8, param, name)) {
                            result |= @as(u32, 1) << @intCast(i);
                            matched = true;
                        }
                    }
                    // A struct-literal type name is not result storage.
                    // All other unresolved names may be local aliases.
                    if (!matched and !(u < last and tags[u + 1] == .l_brace) and
                        !std.zig.primitives.isPrimitive(name)) complete = false;
                },
                else => {},
            }
        }
    }
    return .{ .mask = result, .complete = complete and (result & SAW_RETURN_BIT) != 0 };
}

/// A bounded negative provenance certificate for inputs never read. The
/// signature and body share this exact source AST. Nested control, types,
/// captures, and method receivers are walked, not excluded by spelling.
fn inferUnusedResultParams(tree: *const Ast, proto: Ast.full.FnProto, body: Ast.Node.Index) u16 {
    if (tree.errors.len != 0) return 0;
    var result: u16 = 0;
    var remaining: u32 = 4096;
    var iterator = proto.iterate(tree);
    var parameter: usize = 0;
    while (iterator.next()) |formal| : (parameter += 1) {
        if (parameter >= 16 or remaining == 0) break;
        const declaration = formal.name_token orelse continue;
        const name = tree.tokenSlice(declaration);
        if (nodeExcludesInput(tree, proto.ast.proto_node, name, &remaining, 0) and
            nodeExcludesInput(tree, body, name, &remaining, 0))
            result |= @as(u16, 1) << @intCast(parameter);
    }
    return result;
}

fn nodeExcludesInput(tree: *const Ast, node: Ast.Node.Index, name: []const u8, remaining: *u32, depth: u8) bool {
    if (remaining.* == 0 or depth >= 64) return false;
    remaining.* -= 1;
    if (tree.nodeTag(node) == .identifier)
        return !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name);
    if (tree.nodeTag(node) == .assign) {
        const operands = tree.nodeData(node).node_and_node;
        // Only an AST-authenticated direct discard ignores an input read.
        if (tree.nodeTag(operands[0]) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(operands[0])), "_") and
            tree.nodeTag(operands[1]) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(operands[1])), name)) return true;
    }
    var children = CleanupIterator.init(tree, node);
    while (children.next(tree)) |child| {
        if (!nodeExcludesInput(tree, child, name, remaining, depth + 1)) return false;
    }
    return true;
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
        // `.free(x)` / `.destroy(x)` name their target in the ARG,
        // not the receiver — but when that argument is a projection
        // of the receiver (`self.gpa.destroy(self.first)`) the call
        // releases storage this receiver OWNS, exactly as a
        // `self.child.deinit()` does.  A target that is not derived
        // from the receiver (`self.gpa.free(other.buf)`) releases
        // something else entirely, and stays out.
        const arg_released = blk: {
            if (isReceiverCleanupMethodName(method)) break :blk false;
            if (!std.mem.eql(u8, method, "free") and !std.mem.eql(u8, method, "destroy")) break :blk false;
            if (mtok + 2 > last) break :blk false;
            if (tags[mtok + 1] != .l_paren) break :blk false;
            const arg0 = mtok + 2;
            if (tags[arg0] != .identifier) break :blk false;
            if (!std.mem.eql(u8, tree.tokenSlice(arg0), recv)) break :blk false;
            // Need at least one field segment after the receiver:
            // `self.gpa.free(self)` releases the receiver itself,
            // which is a param release, not a field release.
            if (arg0 + 2 > last) break :blk false;
            if (tags[arg0 + 1] != .period or tags[arg0 + 2] != .identifier) break :blk false;
            break :blk true;
        };
        // Only methods that consume their RECEIVER (deinit/close/etc.)
        // count — unless the argument is a receiver projection, as
        // above.
        if (!arg_released and !isReceiverCleanupMethodName(method)) continue;
        // For the argument form the released path is spelled in the
        // ARGUMENT's dotted chain, not in the receiver chain.
        var chain_first: tokens.TokenIndex = first_field_tok;
        var chain_last: tokens.TokenIndex = last_field_tok;
        if (arg_released) {
            const arg0 = mtok + 2;
            chain_first = arg0 + 2;
            chain_last = chain_first;
            var j = chain_first - 1;
            while (j + 2 <= last) : (j += 2) {
                if (tags[j] != .period or tags[j + 1] != .identifier) break;
                chain_last = j + 1;
            }
        }
        // Field path: source-slice from first field's start to last
        // field's end.  Same shape as the R10 Case B inference.
        const start_byte = tree.tokens.items(.start)[chain_first];
        const last_start = tree.tokens.items(.start)[chain_last];
        const last_len = tree.tokenSlice(chain_last).len;
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

// An empty first exit must stay an empty intersection after later exits.
test "cleanup exits do not reseed empty definite or retention sets" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var exits = CleanupState{ .present = true };
    try exits.merge(arena.allocator(), .{
        .present = true,
        .definite_paths = &.{.{ .param = 0, .path = "" }},
        .may_paths = &.{.{ .param = 0, .path = "" }},
        .retained = &.{0},
    });
    try testing.expectEqual(@as(usize, 0), exits.definite_paths.len);
    try testing.expectEqual(@as(usize, 1), exits.may_paths.len);
    try testing.expectEqual(@as(usize, 0), exits.retained.len);
}

// Sequential effects accumulate, unlike effects on alternative exits.
test "cleanup sequencing unions definite effects before exit intersection" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var state = CleanupState{ .present = true };
    try state.addEffects(arena.allocator(), &.{.{ .param = 0, .path = "" }}, &.{}, &.{}, &.{}, true);
    try state.addEffects(arena.allocator(), &.{.{ .param = 1, .path = "bytes" }}, &.{}, &.{}, &.{}, true);
    try testing.expectEqual(@as(usize, 2), state.definite_paths.len);
    try testing.expectEqual(@as(usize, 2), state.may_paths.len);
    state.invalidate();
    try testing.expectEqual(@as(usize, 0), state.definite_paths.len);
    try testing.expectEqual(@as(usize, 2), state.may_paths.len);
}

const CleanupError = @import("../cache/file_cache.zig").SummaryError;
const CleanupIterator = @import("type_engine").AstIterator;

/// Arrays and callback text belong to the supplied arena, not to a foreign
/// declaration's source snapshot.
pub const NormalSuccessEffects = struct {
    definite_freed_paths: []const ParamPath = &.{},
    may_freed_paths: []const ParamPath = &.{},
    definite_free_fields: []const FieldFree = &.{},
    may_free_fields: []const FieldFree = &.{},
    complete: bool = false,
    retained_owned_params: []const u32 = &.{},
    error_definite_freed_paths: []const ParamPath = &.{},
    error_may_freed_paths: []const ParamPath = &.{},
    error_definite_free_fields: []const FieldFree = &.{},
    error_may_free_fields: []const FieldFree = &.{},
    error_complete: bool = false,
    storage_outcomes: []const StorageOutcome = &.{},
    error_storage_outcomes: []const StorageOutcome = &.{},
    storage_effects_complete: bool = false,
    error_storage_effects_complete: bool = false,
};

fn cleanupOwnedPath(arena: std.mem.Allocator, work: ?CleanupWork, path: ParamPath) CleanupError!ParamPath {
    try cleanupCharge(work, path.path.len);
    return .{ .param = path.param, .path = if (path.path.len == 0) "" else try arena.dupe(u8, path.path) };
}

fn cleanupEqual(comptime T: type, a: T, b: T) bool {
    if (T == ParamPath) {
        return a.param == b.param and std.mem.eql(u8, a.path, b.path);
    }
    if (T == FieldFree) {
        return a.param == b.param and std.mem.eql(u8, a.field, b.field) and
            std.mem.eql(u8, a.method, b.method);
    }
    return a == b;
}

fn cleanupContains(comptime T: type, items: []const T, value: T) bool {
    for (items) |item| if (cleanupEqual(T, item, value)) return true;
    return false;
}

fn cleanupUnion(
    comptime T: type,
    arena: std.mem.Allocator,
    a: []const T,
    b: []const T,
) error{OutOfMemory}![]const T {
    if (b.len == 0) return a;
    if (a.len == 0) return b;
    var changed = false;
    for (b) |item| {
        if (!cleanupContains(T, a, item)) {
            changed = true;
            break;
        }
    }
    if (!changed) return a;
    var out: std.ArrayListUnmanaged(T) = .empty;
    errdefer out.deinit(arena);
    try out.appendSlice(arena, a);
    for (b) |item| {
        if (!cleanupContains(T, out.items, item)) try out.append(arena, item);
    }
    return out.toOwnedSlice(arena);
}

fn cleanupIntersection(
    comptime T: type,
    arena: std.mem.Allocator,
    a: []const T,
    b: []const T,
) error{OutOfMemory}![]const T {
    if (a.len == 0 or b.len == 0) return &.{};
    var changed = false;
    for (a) |item| {
        if (!cleanupContains(T, b, item)) {
            changed = true;
            break;
        }
    }
    if (!changed) return a;
    var out: std.ArrayListUnmanaged(T) = .empty;
    errdefer out.deinit(arena);
    for (a) |item| {
        if (cleanupContains(T, b, item)) try out.append(arena, item);
    }
    return out.toOwnedSlice(arena);
}

/// True when `released` is `stored` itself or lies below it.
fn pathCoveredByStore(released: []const u8, stored: []const u8) bool {
    // The empty path denotes the whole parameter, not a field prefix
    // that requires a leading dot. Every member lies below that root.
    if (stored.len == 0) return true;
    if (!std.mem.startsWith(u8, released, stored)) return false;
    return released.len == stored.len or released[stored.len] == '.';
}

test "cleanup root coverage includes stored descendants without merging siblings" {
    try testing.expect(pathCoveredByStore("bytes", ""));
    try testing.expect(pathCoveredByStore("inner.bytes", ""));
    try testing.expect(pathCoveredByStore("", ""));
    try testing.expect(!pathCoveredByStore("other.bytes", "inner"));
    try testing.expect(!pathCoveredByStore("inner_bytes", "inner"));

    const stores = [_]ParamPath{.{ .param = 0, .path = "bytes" }};
    const after_store = CleanupAlternative{ .uncertain_stores = &stores };
    try testing.expect(try after_store.uncertain(.{ .param = 0, .path = "" }));
    try testing.expect(!try after_store.uncertain(.{ .param = 0, .path = "other" }));
    try testing.expect(!try after_store.uncertain(.{ .param = 1, .path = "" }));
}

/// `items` without the releases that a store to `param.stored` replaced.
fn withoutStored(
    comptime T: type,
    arena: std.mem.Allocator,
    items: []const T,
    param: u32,
    stored: []const u8,
) error{OutOfMemory}![]const T {
    var drops: usize = 0;
    for (items) |item| {
        const path = if (T == ParamPath) item.path else item.field;
        if (item.param == param and pathCoveredByStore(path, stored)) drops += 1;
    }
    if (drops == 0) return items;
    var kept: std.ArrayListUnmanaged(T) = .empty;
    errdefer kept.deinit(arena);
    for (items) |item| {
        const path = if (T == ParamPath) item.path else item.field;
        if (item.param == param and pathCoveredByStore(path, stored)) continue;
        try kept.append(arena, item);
    }
    return kept.toOwnedSlice(arena);
}

/// Trace work shares the walker/callee allowance. The node pointer follows
/// recursive walks, so array copying failures retain the active source site.
const CleanupWork = struct {
    context: *anyopaque,
    node: *const Ast.Node.Index,
    charge_fn: *const fn (*anyopaque, Ast.Node.Index, usize) CleanupError!void,

    fn init(cache: anytype, node: *const Ast.Node.Index) CleanupWork {
        const Adapter = struct {
            fn charge(context: *anyopaque, at: Ast.Node.Index, units: usize) CleanupError!void {
                const typed: @TypeOf(cache) = @ptrCast(@alignCast(context));
                try typed.normalCleanupStorageWork(at, units);
            }
        };
        return .{ .context = @ptrCast(cache), .node = node, .charge_fn = Adapter.charge };
    }
};

fn cleanupCharge(work: ?CleanupWork, units: usize) CleanupError!void {
    if (units == 0) return;
    if (work) |budget| try budget.charge_fn(budget.context, budget.node.*, units);
}

fn cleanupAddStorageValue(
    comptime T: type,
    arena: std.mem.Allocator,
    work: ?CleanupWork,
    items: []const T,
    value: T,
) CleanupError![]const T {
    try cleanupCharge(work, items.len);
    if (cleanupContains(T, items, value)) return items;
    try cleanupCharge(work, items.len + 1);
    const out = try arena.alloc(T, items.len + 1);
    @memcpy(out[0..items.len], items);
    out[items.len] = value;
    return out;
}

const CleanupSnapshot = struct {
    token: Ast.TokenIndex,
    path: ?ParamPath,
    version: usize = 0,
    fresh_token: ?Ast.TokenIndex = null,
    released: bool = false,
    projection_current: bool = false,
    projection_ambiguous: bool = false,
    projection_operation_count: ?usize = null,
    from_snapshot: bool = false,
    identity_proved: bool = true,
};

const CleanupAlternative = struct {
    operations: []const StorageOperation = &.{},
    snapshots: []const CleanupSnapshot = &.{},
    uncertain_stores: []const ParamPath = &.{},
    work: ?CleanupWork = null,

    fn uncertain(self: CleanupAlternative, path: ParamPath) CleanupError!bool {
        try cleanupCharge(self.work, self.uncertain_stores.len);
        for (self.uncertain_stores) |stored| {
            if (stored.param == path.param and
                (pathCoveredByStore(path.path, stored.path) or pathCoveredByStore(stored.path, path.path))) return true;
        }
        return false;
    }

    fn released(self: CleanupAlternative, path: ParamPath, payload_version: usize) CleanupError!bool {
        try cleanupCharge(self.work, self.operations.len);
        var current: usize = 0;
        for (self.operations) |operation| {
            if (!cleanupEqual(ParamPath, operation.path, path)) continue;
            switch (operation.kind) {
                .replace => current += 1,
                .release_entry => if (payload_version == 0) return true,
                .release_current => if (payload_version == (operation.version orelse current)) return true,
            }
        }
        return false;
    }

    fn version(self: CleanupAlternative, path: ParamPath) CleanupError!usize {
        try cleanupCharge(self.work, self.operations.len);
        var result: usize = 0;
        for (self.operations) |operation| {
            if (operation.kind == .replace and cleanupEqual(ParamPath, operation.path, path)) result += 1;
        }
        return result;
    }

    fn append(self: *CleanupAlternative, arena: std.mem.Allocator, operation: StorageOperation) CleanupError!void {
        try cleanupCharge(self.work, self.operations.len + 1);
        const operations = try arena.alloc(StorageOperation, self.operations.len + 1);
        @memcpy(operations[0..self.operations.len], self.operations);
        operations[self.operations.len] = operation;
        self.operations = operations;
    }

    fn snapshot(self: *CleanupAlternative, arena: std.mem.Allocator, value: CleanupSnapshot) CleanupError!void {
        try cleanupCharge(self.work, self.snapshots.len + 1);
        const snapshots = try arena.alloc(CleanupSnapshot, self.snapshots.len + 1);
        @memcpy(snapshots[0..self.snapshots.len], self.snapshots);
        snapshots[self.snapshots.len] = value;
        self.snapshots = snapshots;
    }
};
/// Presence is independent of an empty effect set: the first empty exit must
/// still participate in every later intersection.
const CleanupState = struct {
    present: bool = false,
    complete: bool = true,
    definite_paths: []const ParamPath = &.{},
    may_paths: []const ParamPath = &.{},
    definite_fields: []const FieldFree = &.{},
    may_fields: []const FieldFree = &.{},
    retained: []const u32 = &.{},
    storage_complete: bool = true,
    alternatives: []const CleanupAlternative = &.{.{}},
    work: ?CleanupWork = null,
    observed_paths: []const ParamPath = &.{},
    observed_fields: []const FieldFree = &.{},

    fn observeReleases(self: *CleanupState, arena: std.mem.Allocator, paths: []const ParamPath, fields: []const FieldFree) CleanupError!void {
        try cleanupCharge(self.work, paths.len + fields.len);
        for (paths) |path| self.observed_paths = try cleanupAddStorageValue(ParamPath, arena, self.work, self.observed_paths, path);
        for (fields) |field| self.observed_fields = try cleanupAddStorageValue(FieldFree, arena, self.work, self.observed_fields, field);
    }

    /// Exact traces distinguish old from current storage. If the trace cannot
    /// be replayed, retain every observed release as conservative MAY evidence.
    fn includeIncompleteReleases(self: *CleanupState, arena: std.mem.Allocator) CleanupError!void {
        if (!self.present or self.storage_complete) return;
        try cleanupCharge(self.work, self.observed_paths.len + self.observed_fields.len);
        for (self.observed_paths) |path| self.may_paths = try cleanupAddStorageValue(ParamPath, arena, self.work, self.may_paths, path);
        for (self.observed_fields) |field| self.may_fields = try cleanupAddStorageValue(FieldFree, arena, self.work, self.may_fields, field);
        try self.filterRetention(arena);
    }

    fn invalidate(self: *CleanupState) void {
        self.storage_complete = false;
        self.invalidateLegacy();
    }

    fn invalidateLegacy(self: *CleanupState) void {
        self.complete = false;
        self.definite_paths = &.{};
        self.definite_fields = &.{};
        self.retained = &.{};
    }

    fn merge(self: *CleanupState, arena: std.mem.Allocator, other: CleanupState) CleanupError!void {
        if (!other.present) return;
        if (!self.present) {
            self.* = other;
            return;
        }
        if (self.alternatives.ptr != other.alternatives.ptr or self.alternatives.len != other.alternatives.len) {
            try cleanupCharge(self.work, self.alternatives.len + other.alternatives.len);
            const alternatives = try arena.alloc(CleanupAlternative, self.alternatives.len + other.alternatives.len);
            @memcpy(alternatives[0..self.alternatives.len], self.alternatives);
            @memcpy(alternatives[self.alternatives.len..], other.alternatives);
            self.alternatives = alternatives;
        }
        self.storage_complete = self.storage_complete and other.storage_complete;
        try self.observeReleases(arena, other.observed_paths, other.observed_fields);
        self.definite_paths = try cleanupIntersection(
            ParamPath,
            arena,
            self.definite_paths,
            other.definite_paths,
        );
        self.definite_fields = try cleanupIntersection(
            FieldFree,
            arena,
            self.definite_fields,
            other.definite_fields,
        );
        self.retained = try cleanupIntersection(u32, arena, self.retained, other.retained);
        self.may_paths = try cleanupUnion(ParamPath, arena, self.may_paths, other.may_paths);
        self.may_fields = try cleanupUnion(FieldFree, arena, self.may_fields, other.may_fields);
        if (!other.complete) self.invalidateLegacy();
    }

    fn isReleased(self: CleanupState, param: u32) bool {
        for (self.may_paths) |path| if (path.param == param) return true;
        for (self.may_fields) |field| if (field.param == param) return true;
        return false;
    }

    /// A store to `param.path` replaces the value a release handed back, so
    /// the storage at that path (or below it) is no longer the released
    /// allocation on this path: `free(self.buf); self.buf = fresh;` leaves
    /// the receiver holding live storage.  A release elsewhere on another
    /// path is untouched, and joins still union the releases of the paths
    /// that did not store.
    fn reassign(
        self: *CleanupState,
        arena: std.mem.Allocator,
        param: u32,
        path: []const u8,
    ) error{OutOfMemory}!void {
        self.definite_paths = try withoutStored(ParamPath, arena, self.definite_paths, param, path);
        self.may_paths = try withoutStored(ParamPath, arena, self.may_paths, param, path);
        self.definite_fields = try withoutStored(FieldFree, arena, self.definite_fields, param, path);
        self.may_fields = try withoutStored(FieldFree, arena, self.may_fields, param, path);
    }

    fn filterRetention(self: *CleanupState, arena: std.mem.Allocator) error{OutOfMemory}!void {
        var changed = false;
        for (self.retained) |param| {
            if (self.isReleased(param)) {
                changed = true;
                break;
            }
        }
        if (!changed) return;
        var kept: std.ArrayListUnmanaged(u32) = .empty;
        defer kept.deinit(arena);
        for (self.retained) |param| {
            if (!self.isReleased(param)) try kept.append(arena, param);
        }
        self.retained = try kept.toOwnedSlice(arena);
    }

    fn addEffects(
        self: *CleanupState,
        arena: std.mem.Allocator,
        definite_paths: []const ParamPath,
        definite_fields: []const FieldFree,
        may_paths: []const ParamPath,
        may_fields: []const FieldFree,
        complete: bool,
    ) CleanupError!void {
        if (!self.present) return;
        try self.observeReleases(arena, definite_paths, definite_fields);
        try self.observeReleases(arena, may_paths, may_fields);
        self.may_paths = try cleanupUnion(ParamPath, arena, self.may_paths, may_paths);
        self.may_paths = try cleanupUnion(ParamPath, arena, self.may_paths, definite_paths);
        self.may_fields = try cleanupUnion(FieldFree, arena, self.may_fields, may_fields);
        self.may_fields = try cleanupUnion(FieldFree, arena, self.may_fields, definite_fields);
        if (self.complete and complete) {
            self.definite_paths = try cleanupUnion(
                ParamPath,
                arena,
                self.definite_paths,
                definite_paths,
            );
            self.definite_fields = try cleanupUnion(
                FieldFree,
                arena,
                self.definite_fields,
                definite_fields,
            );
            try self.filterRetention(arena);
        } else {
            self.invalidateLegacy();
        }
    }

    fn composeStorage(
        self: *CleanupState,
        arena: std.mem.Allocator,
        outcomes: []const StorageOutcome,
        complete: bool,
    ) CleanupError!void {
        if (!self.present) return;
        self.storage_complete = self.storage_complete and complete;
        if (!complete or outcomes.len == 0) return;
        const product = @mulWithOverflow(self.alternatives.len, outcomes.len);
        if (product[1] != 0) {
            try cleanupCharge(self.work, std.math.maxInt(usize));
            return error.AnalysisBudgetExceeded;
        }
        const count = product[0];
        try cleanupCharge(self.work, count);
        const alternatives = try arena.alloc(CleanupAlternative, count);
        var index: usize = 0;
        for (self.alternatives) |prefix| {
            for (outcomes) |outcome| {
                try cleanupCharge(self.work, outcome.operations.len);
                var alternative = prefix;
                for (outcome.operations) |operation| {
                    var mapped = operation;
                    if (try alternative.uncertain(operation.path)) self.storage_complete = false;
                    if (operation.kind != .replace)
                        mapped.identity_proved = mapped.identity_proved and self.storage_complete;
                    const current_version = try alternative.version(operation.path);
                    const entry_version = try prefix.version(operation.path);
                    switch (operation.kind) {
                        .replace => {
                            if (operation.allocator == null) self.storage_complete = false;
                        },
                        .release_entry => {
                            mapped.kind = if (entry_version == 0) .release_entry else .release_current;
                            mapped.version = entry_version;
                        },
                        .release_current => {
                            const version = if (operation.version) |relative|
                                entry_version + relative
                            else
                                current_version;
                            if (version > current_version) self.storage_complete = false;
                            mapped.kind = if (version == 0) .release_entry else .release_current;
                            mapped.version = version;
                        },
                    }
                    try alternative.append(arena, mapped);
                }
                alternatives[index] = alternative;
                index += 1;
            }
        }
        self.alternatives = alternatives;
    }

    fn storageOutcomes(self: CleanupState, arena: std.mem.Allocator) CleanupError![]const StorageOutcome {
        if (!self.present) return &.{};
        try cleanupCharge(self.work, self.alternatives.len);
        const outcomes = try arena.alloc(StorageOutcome, self.alternatives.len);
        for (self.alternatives, outcomes) |alternative, *outcome| {
            outcome.* = .{ .operations = alternative.operations };
        }
        return outcomes;
    }
};

/// An error-valued expression is not an exit until return or try propagates it.
/// Catch handles that value without running the enclosing scope's errdefers.
const CleanupFlow = struct {
    next: CleanupState = .{},
    error_value: CleanupState = .{},
    normal_exit: CleanupState = .{},
    error_exit: CleanupState = .{},
    value_known: bool = true,

    fn merge(self: *CleanupFlow, arena: std.mem.Allocator, other: CleanupFlow) CleanupError!void {
        try self.next.merge(arena, other.next);
        try self.error_value.merge(arena, other.error_value);
        try self.normal_exit.merge(arena, other.normal_exit);
        try self.error_exit.merge(arena, other.error_exit);
        self.value_known = self.value_known and other.value_known;
    }

    fn continuing(self: CleanupFlow, arena: std.mem.Allocator) CleanupError!CleanupState {
        var state = self.next;
        try state.merge(arena, self.error_value);
        return state;
    }
};

const CleanupDefer = struct {
    body: Ast.Node.Index,
    error_only: bool,
};

fn CleanupWalker(comptime Cache: type) type {
    return struct {
        const Self = @This();
        cache: Cache,
        arena: std.mem.Allocator,
        tree: *const Ast,
        proto: Ast.full.FnProto,
        bindings: *const local_bindings.LocalBindings,
        active_node: Ast.Node.Index,

        fn classifyValue(self: *Self, node: Ast.Node.Index, flow: *CleanupFlow) CleanupError!void {
            if (flow.value_known) return;
            const state = try flow.continuing(self.arena);
            if (!state.present) return;
            const kind = try self.cache.normalCleanupReturnKind(node);
            flow.next = .{};
            flow.error_value = .{};
            if (kind) |is_error| {
                if (is_error) {
                    flow.error_value = state;
                } else {
                    flow.next = state;
                }
            } else {
                var unknown = state;
                unknown.invalidate();
                flow.next = unknown;
                flow.error_value = unknown;
            }
            flow.value_known = true;
        }

        fn addRetention(self: *Self, state: *CleanupState, node: Ast.Node.Index) CleanupError!void {
            if (!state.present or !state.complete) return;
            const retained = try self.cache.retainedStorageAt(
                self.arena,
                self.proto,
                self.bindings,
                node,
            );
            state.retained = try cleanupUnion(u32, self.arena, state.retained, retained);
            // Previously observed MAY releases also rule out retention proof.
            try state.filterRetention(self.arena);
        }

        fn storageIdentity(self: *Self, node: Ast.Node.Index, alternative: CleanupAlternative) CleanupError!CleanupSnapshot {
            var expression = node;
            while (true) {
                try self.cache.normalCleanupStorageWork(expression, 1);
                switch (self.tree.nodeTag(expression)) {
                    .grouped_expression => expression = self.tree.nodeData(expression).node_and_token[0],
                    .address_of, .@"try" => expression = self.tree.nodeData(expression).node,
                    else => break,
                }
            }
            const first = self.tree.firstToken(expression);
            const last = self.tree.lastToken(expression);
            const token_count = try checkedTokenCount(self.tree.source.len, self.tree.tokens.len);
            var projection_ambiguous = false;
            var projected_snapshot: ?CleanupSnapshot = null;
            if (self.tree.tokens.items(.tag)[first] == .identifier) {
                if (nameAtUse(self.bindings, self.tree, self.proto, self.tree.tokenSlice(first), first, token_count)) |decl| {
                    switch (decl) {
                        .local => |binding| {
                            try cleanupCharge(alternative.work, alternative.snapshots.len);
                            var index = alternative.snapshots.len;
                            while (index > 0) {
                                index -= 1;
                                var snapshot = alternative.snapshots[index];
                                if (snapshot.token != binding.name_token) continue;
                                if (first == last) {
                                    if (snapshot.path) |path| snapshot.released = try alternative.released(path, snapshot.version);
                                    return snapshot;
                                }
                                // Only an authenticated pointer alias projects
                                // onto a current field. A copied aggregate's
                                // field may still carry an entry payload.
                                projection_ambiguous = !snapshot.projection_current;
                                if (snapshot.path == null) return .{ .token = first, .path = null, .projection_ambiguous = true };
                                if (snapshot.projection_operation_count != null)
                                    projected_snapshot = snapshot;
                                break;
                            }
                        },
                        .clause => {},
                    }
                }
            }
            const owner = try ownerOfExpr(self.arena, self.tree, self.proto, self.bindings, first, last, 0);
            return switch (owner) {
                .param => |path| blk: {
                    var version = try alternative.version(path);
                    var from_snapshot = false;
                    var identity_proved = true;
                    if (projected_snapshot) |snapshot| {
                        const source = snapshot.path.?;
                        const suffix = if (source.path.len == 0)
                            path.path
                        else if (path.path.len > source.path.len and
                            std.mem.startsWith(u8, path.path, source.path) and
                            path.path[source.path.len] == '.')
                            path.path[source.path.len + 1 ..]
                        else
                            "";
                        // A direct member's header was copied with the
                        // aggregate. Deeper projections may dereference a
                        // pointer member, so they still require type proof.
                        if (source.param == path.param and suffix.len != 0 and
                            std.mem.indexOfScalar(u8, suffix, '.') == null)
                        {
                            var at_copy = alternative;
                            at_copy.operations = alternative.operations[0..snapshot.projection_operation_count.?];
                            version = try at_copy.version(path);
                            from_snapshot = true;
                            identity_proved = snapshot.identity_proved;
                            projection_ambiguous = false;
                        }
                    }
                    var projection_current = self.tree.nodeTag(node) == .address_of;
                    if (self.tree.nodeTag(expression) == .identifier and path.path.len == 0) {
                        var parameters = self.proto.iterate(self.tree);
                        while (parameters.next()) |parameter| {
                            try self.cache.normalCleanupStorageWork(expression, 1);
                            const name = parameter.name_token orelse continue;
                            if (!std.mem.eql(u8, self.tree.tokenSlice(name), self.tree.tokenSlice(first))) continue;
                            const type_node = parameter.type_expr orelse break;
                            const pointer = self.tree.fullPtrType(type_node) orelse break;
                            projection_current = pointer.size == .one;
                            break;
                        }
                    }
                    break :blk .{
                        .token = first,
                        .path = try cleanupOwnedPath(self.arena, alternative.work, path),
                        .version = version,
                        .released = try alternative.released(path, version),
                        .projection_current = projection_current,
                        .projection_ambiguous = projection_ambiguous,
                        .from_snapshot = from_snapshot,
                        .identity_proved = identity_proved,
                    };
                },
                .unknown => .{ .token = first, .path = null },
            };
        }

        fn bindSnapshot(self: *Self, state: *CleanupState, token: Ast.TokenIndex, expression: Ast.Node.Index) CleanupError!void {
            if (!state.present) return;
            try cleanupCharge(state.work, state.alternatives.len * 2);
            const alternatives = try self.arena.dupe(CleanupAlternative, state.alternatives);
            for (alternatives) |*alternative| {
                var identity = try self.storageIdentity(expression, alternative.*);
                identity.token = token;
                if (!identity.from_snapshot) {
                    identity.identity_proved = identity.identity_proved and state.storage_complete;
                    if (identity.path) |path|
                        identity.identity_proved = identity.identity_proved and !try alternative.uncertain(path);
                }
                identity.from_snapshot = true;
                if (!identity.projection_current and identity.path != null and
                    identity.projection_operation_count == null)
                    identity.projection_operation_count = alternative.operations.len;
                if (identity.path == null and identity.fresh_token == null and try self.cache.normalCleanupFresh(expression))
                    identity.fresh_token = token;
                try alternative.snapshot(self.arena, identity);
            }
            state.alternatives = alternatives;
        }

        /// Only an exact fresh-storage certificate can revive a receiver path.
        /// Reusing the saved old header must retain its observed release.
        fn reassignOwned(self: *Self, node: Ast.Node.Index, state: *CleanupState) CleanupError!void {
            if (!state.present) return;
            const lhs, const rhs = self.tree.nodeData(node).node_and_node;
            // An element or slice-payload write does not rebind its header.
            // Keep observed release evidence, but do not invent a new owner.
            if (self.tree.nodeTag(lhs) == .array_access) return;
            if (self.tree.nodeTag(lhs) == .deref and
                self.tree.fullSlice(self.tree.nodeData(lhs).node) != null) return;
            if (self.tree.nodeTag(lhs) == .identifier) {
                const first = self.tree.firstToken(lhs);
                const token_count = try checkedTokenCount(self.tree.source.len, self.tree.tokens.len);
                if (nameAtUse(self.bindings, self.tree, self.proto, self.tree.tokenSlice(first), first, token_count)) |decl| {
                    switch (decl) {
                        .local => |binding| {
                            try self.bindSnapshot(state, binding.name_token, rhs);
                            return;
                        },
                        .clause => {},
                    }
                }
            }
            const owner = try ownerOfExpr(self.arena, self.tree, self.proto, self.bindings, self.tree.firstToken(lhs), self.tree.lastToken(lhs), 0);
            switch (owner) {
                .param => |borrowed| {
                    const stored = try cleanupOwnedPath(self.arena, state.work, borrowed);
                    const certified = try self.cache.normalCleanupFresh(rhs);
                    const allocator = if (certified) try self.cache.normalCleanupAllocator(rhs) else null;
                    if (certified and allocator == null) state.storage_complete = false;
                    const owned_allocator = if (allocator) |path| try cleanupOwnedPath(self.arena, state.work, path) else null;
                    try cleanupCharge(state.work, state.alternatives.len * 2);
                    const alternatives = try self.arena.dupe(CleanupAlternative, state.alternatives);
                    var live_replacement = certified;
                    var released_store = false;
                    for (alternatives) |*alternative| {
                        const identity = try self.storageIdentity(rhs, alternative.*);
                        if (identity.released) {
                            released_store = true;
                            live_replacement = false;
                        }
                        if (identity.path != null) live_replacement = false;
                        if (!certified or identity.released or identity.path != null) {
                            alternative.uncertain_stores = try cleanupAddStorageValue(ParamPath, self.arena, state.work, alternative.uncertain_stores, stored);
                            try cleanupCharge(state.work, alternative.operations.len + alternative.snapshots.len);
                            for (alternative.operations) |operation| {
                                if (operation.path.param == stored.param and
                                    (pathCoveredByStore(operation.path.path, stored.path) or pathCoveredByStore(stored.path, operation.path.path)))
                                    state.storage_complete = false;
                            }
                            for (alternative.snapshots) |snapshot| {
                                if (snapshot.path) |path| {
                                    if (path.param == stored.param and
                                        (pathCoveredByStore(path.path, stored.path) or pathCoveredByStore(stored.path, path.path)))
                                        state.storage_complete = false;
                                }
                            }
                            if (identity.released) state.storage_complete = false;
                            continue;
                        }
                        if (try alternative.uncertain(stored)) state.storage_complete = false;
                        try alternative.append(self.arena, .{ .path = stored, .kind = .replace, .allocator = owned_allocator });
                        if (identity.fresh_token) |fresh_token| {
                            const previous = alternative.snapshots;
                            try cleanupCharge(state.work, previous.len);
                            for (previous) |snapshot| {
                                if (snapshot.fresh_token != fresh_token) continue;
                                var published = snapshot;
                                published.path = stored;
                                published.version = try alternative.version(stored);
                                try alternative.snapshot(self.arena, published);
                            }
                        }
                    }
                    state.alternatives = alternatives;
                    if (live_replacement) {
                        try state.reassign(self.arena, stored.param, stored.path);
                    } else if (released_store) {
                        try state.addEffects(self.arena, &.{}, &.{}, &.{stored}, &.{}, true);
                    }
                },
                .unknown => {},
            }
        }

        fn releaseStorage(self: *Self, state: *CleanupState, argument: Ast.Node.Index) CleanupError!void {
            try cleanupCharge(state.work, state.alternatives.len * 2);
            const alternatives = try self.arena.dupe(CleanupAlternative, state.alternatives);
            var current_paths: []const ParamPath = &.{};
            var definite_current: ?ParamPath = null;
            var definite_initialized = false;
            for (alternatives) |*alternative| {
                const identity = try self.storageIdentity(argument, alternative.*);
                var released_current: ?ParamPath = null;
                if (identity.path) |path| {
                    try state.observeReleases(self.arena, &.{path}, &.{});
                    if (identity.projection_ambiguous) state.storage_complete = false;
                    if (try alternative.uncertain(path)) state.storage_complete = false;
                    const current_version = try alternative.version(path);
                    const current = !identity.projection_ambiguous and identity.version == current_version;
                    if (current) {
                        released_current = path;
                        current_paths = try cleanupAddStorageValue(ParamPath, self.arena, state.work, current_paths, path);
                    }
                    try alternative.append(self.arena, .{
                        .path = path,
                        .kind = if (identity.version == 0) .release_entry else .release_current,
                        .version = identity.version,
                        .identity_proved = !identity.projection_ambiguous and
                            if (identity.from_snapshot) identity.identity_proved else
                            state.storage_complete and !try alternative.uncertain(path),
                    });
                } else {
                    released_current = null;
                    if (identity.fresh_token == null and !try self.cache.normalCleanupFresh(argument)) {
                        state.storage_complete = false;
                        state.invalidateLegacy();
                    }
                }
                if (identity.fresh_token) |fresh_token| {
                    const previous = alternative.snapshots;
                    try cleanupCharge(state.work, previous.len);
                    for (previous) |snapshot| {
                        if (snapshot.fresh_token != fresh_token) continue;
                        var released_snapshot = snapshot;
                        released_snapshot.released = true;
                        try alternative.snapshot(self.arena, released_snapshot);
                    }
                }
                try cleanupCharge(state.work, 1);
                if (!definite_initialized) {
                    definite_current = released_current;
                    definite_initialized = true;
                } else if (definite_current) |previous| {
                    if (released_current) |path| {
                        if (!cleanupEqual(ParamPath, previous, path)) definite_current = null;
                    } else {
                        definite_current = null;
                    }
                }
            }
            state.alternatives = alternatives;
            const definite_paths = if (definite_current) |path|
                try cleanupAddStorageValue(ParamPath, self.arena, state.work, &.{}, path)
            else
                &.{};
            try state.addEffects(self.arena, definite_paths, &.{}, current_paths, &.{}, true);
        }

        fn runDefers(
            self: *Self,
            initial: CleanupState,
            registered: []const CleanupDefer,
            error_exit: bool,
        ) CleanupError!CleanupState {
            var state = initial;
            var index = registered.len;
            while (index > 0 and state.present) {
                index -= 1;
                const cleanup = registered[index];
                if (cleanup.error_only and !error_exit) continue;
                const flow = try self.walk(cleanup.body, state);
                state = try flow.continuing(self.arena);
                // Zig disallows escaping a defer. Robustness input must not
                // turn such an escape into a successful certificate.
                if (flow.normal_exit.present or flow.error_exit.present) {
                    try state.merge(self.arena, flow.normal_exit);
                    try state.merge(self.arena, flow.error_exit);
                    state.invalidate();
                }
            }
            return state;
        }

        fn walkBlock(self: *Self, node: Ast.Node.Index, initial: CleanupState) CleanupError!CleanupFlow {
            var buffer: [2]Ast.Node.Index = undefined;
            const statements = self.tree.blockStatements(&buffer, node).?;
            var registered: std.ArrayListUnmanaged(CleanupDefer) = .empty;
            defer registered.deinit(self.arena);
            var state = initial;
            var out = CleanupFlow{};
            for (statements) |statement| {
                if (!state.present) break;
                const tag = self.tree.nodeTag(statement);
                if (tag == .@"defer" or tag == .@"errdefer") {
                    try self.cache.enterNormalCleanup(statement);
                    defer self.cache.leaveNormalCleanup();
                    try self.cache.chargeNormalCleanup(statement);
                    const body = if (tag == .@"defer")
                        self.tree.nodeData(statement).node
                    else
                        self.tree.nodeData(statement).opt_token_and_node[1];
                    try registered.append(self.arena, .{
                        .body = body,
                        .error_only = tag == .@"errdefer",
                    });
                    continue;
                }
                const flow = try self.walk(statement, state);
                try out.normal_exit.merge(self.arena, try self.runDefers(
                    flow.normal_exit,
                    registered.items,
                    false,
                ));
                try out.error_exit.merge(self.arena, try self.runDefers(
                    flow.error_exit,
                    registered.items,
                    true,
                ));
                // Discarding an error union is not returning an error.
                state = try flow.continuing(self.arena);
            }
            out.next = try self.runDefers(state, registered.items, false);
            return out;
        }

        fn walkChildren(self: *Self, node: Ast.Node.Index, initial: CleanupState) CleanupError!CleanupFlow {
            var out = CleanupFlow{ .next = initial };
            var children = CleanupIterator.init(self.tree, node);
            while (children.next(self.tree)) |child| {
                const state = try out.continuing(self.arena);
                if (!state.present) break;
                const flow = try self.walk(child, state);
                try out.normal_exit.merge(self.arena, flow.normal_exit);
                try out.error_exit.merge(self.arena, flow.error_exit);
                out.next = try flow.continuing(self.arena);
                out.error_value = .{};
            }
            return out;
        }

        fn walkCall(self: *Self, node: Ast.Node.Index, initial: CleanupState) CleanupError!CleanupFlow {
            // A failed try in an argument never invokes the outer call.
            var out = try self.walkChildren(node, initial);
            var prefix = out.next;
            out.next = .{};
            if (!prefix.present) return out;
            // The callback has no retained-field preservation contract.
            // A call can overwrite a destination established by an earlier store.
            prefix.retained = &.{};
            const call = try self.cache.normalCleanupCall(
                self.arena,
                self.proto,
                self.bindings,
                node,
            );
            if (call.can_normal and call.returns_error != true) {
                out.next = prefix;
                if (call.release_argument) |argument| {
                    try self.releaseStorage(&out.next, argument);
                    out.next.storage_complete = out.next.storage_complete and call.storage_complete;
                } else {
                    try out.next.addEffects(self.arena, call.definite_paths, call.definite_fields, call.may_paths, call.may_fields, call.complete);
                    try out.next.composeStorage(self.arena, call.storage_outcomes, call.storage_complete);
                }
            }
            if (call.can_error and call.returns_error != false) {
                out.error_value = prefix;
                try out.error_value.addEffects(self.arena, call.error_definite_paths, call.error_definite_fields, call.error_may_paths, call.error_may_fields, call.error_complete);
                try out.error_value.composeStorage(self.arena, call.error_storage_outcomes, call.error_storage_complete);
            }
            return out;
        }

        fn walkIf(self: *Self, node: Ast.Node.Index, initial: CleanupState) CleanupError!CleanupFlow {
            const branch = self.tree.fullIf(node).?;
            var condition = try self.walk(branch.ast.cond_expr, initial);
            const error_condition = branch.error_token != null;
            if (error_condition) try self.classifyValue(branch.ast.cond_expr, &condition);
            var out = CleanupFlow{
                .normal_exit = condition.normal_exit,
                .error_exit = condition.error_exit,
            };
            const state = if (error_condition)
                condition.next
            else
                try condition.continuing(self.arena);
            var known: ?bool = null;
            if (branch.payload_token == null and
                self.tree.nodeTag(branch.ast.cond_expr) == .identifier)
            {
                const text = self.tree.tokenSlice(
                    self.tree.nodeMainToken(branch.ast.cond_expr),
                );
                if (std.mem.eql(u8, text, "true")) known = true;
                if (std.mem.eql(u8, text, "false")) known = false;
            }
            if (known == null and branch.payload_token == null and !error_condition)
                known = try self.cache.normalCleanupCondition(branch.ast.cond_expr);
            if (known != false and state.present) {
                try out.merge(self.arena, try self.walk(branch.ast.then_expr, state));
            }
            const else_state = if (error_condition) condition.error_value else state;
            if (known != true and else_state.present) {
                if (branch.ast.else_expr.unwrap()) |else_node| {
                    try out.merge(self.arena, try self.walk(else_node, else_state));
                } else {
                    try out.next.merge(self.arena, else_state);
                }
            }
            return out;
        }

        fn walkUnknown(self: *Self, node: Ast.Node.Index, initial: CleanupState) CleanupError!CleanupFlow {
            // Independent children retain observed MAY effects without a
            // claim that a loop iteration, switch arm, or jump always runs.
            var state = initial;
            state.invalidate();
            var out = CleanupFlow{ .next = state, .value_known = false };
            var children = CleanupIterator.init(self.tree, node);
            while (children.next(self.tree)) |child| {
                const flow = try self.walk(child, state);
                try out.normal_exit.merge(self.arena, flow.normal_exit);
                try out.error_exit.merge(self.arena, flow.error_exit);
                var observed = try flow.continuing(self.arena);
                try observed.merge(self.arena, flow.normal_exit);
                try out.next.merge(self.arena, observed);
            }
            out.next.invalidate();
            out.normal_exit.invalidate();
            out.error_exit.invalidate();
            return out;
        }

        fn walk(self: *Self, node: Ast.Node.Index, initial: CleanupState) CleanupError!CleanupFlow {
            if (!initial.present) return .{};
            const previous_node = self.active_node;
            self.active_node = node;
            defer self.active_node = previous_node;
            try self.cache.enterNormalCleanup(node);
            defer self.cache.leaveNormalCleanup();
            try self.cache.chargeNormalCleanup(node);
            const tag = self.tree.nodeTag(node);
            var call_buffer: [1]Ast.Node.Index = undefined;
            if (self.tree.fullCall(&call_buffer, node) != null) {
                return self.walkCall(node, initial);
            }
            switch (tag) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => return self.walkBlock(node, initial),
                .@"if", .if_simple => return self.walkIf(node, initial),
                .@"return" => {
                    var flow = if (self.tree.nodeData(node).opt_node.unwrap()) |expression|
                        try self.walk(expression, initial)
                    else
                        CleanupFlow{ .next = initial };
                    if (self.tree.nodeData(node).opt_node.unwrap()) |expression| {
                        try self.classifyValue(expression, &flow);
                    }
                    try self.addRetention(&flow.next, node);
                    try flow.normal_exit.merge(self.arena, flow.next);
                    try flow.error_exit.merge(self.arena, flow.error_value);
                    flow.next = .{};
                    flow.error_value = .{};
                    return flow;
                },
                .@"try" => {
                    const expression = self.tree.nodeData(node).node;
                    var flow = try self.walk(expression, initial);
                    try self.classifyValue(expression, &flow);
                    try flow.error_exit.merge(self.arena, flow.error_value);
                    flow.error_value = .{};
                    return flow;
                },
                .@"catch" => {
                    const lhs, const rhs = self.tree.nodeData(node).node_and_node;
                    var flow = try self.walk(lhs, initial);
                    try self.classifyValue(lhs, &flow);
                    const failure = flow.error_value;
                    flow.error_value = .{};
                    if (failure.present) {
                        try flow.merge(self.arena, try self.walk(rhs, failure));
                    }
                    return flow;
                },
                .grouped_expression => return self.walk(
                    self.tree.nodeData(node).node_and_token[0],
                    initial,
                ),
                .@"comptime", .@"nosuspend" => return self.walk(
                    self.tree.nodeData(node).node,
                    initial,
                ),
                .error_value => return .{ .error_value = initial },
                .unreachable_literal => return .{},
                .fn_decl, .fn_proto, .fn_proto_one, .fn_proto_multi, .fn_proto_simple, .container_decl, .container_decl_trailing, .container_decl_two, .container_decl_two_trailing, .container_decl_arg, .container_decl_arg_trailing, .tagged_union, .tagged_union_trailing, .tagged_union_two, .tagged_union_two_trailing, .tagged_union_enum_tag, .tagged_union_enum_tag_trailing, .error_set_decl => return .{ .next = initial },
                .bool_and, .bool_or => {
                    const lhs, const rhs = self.tree.nodeData(node).node_and_node;
                    var flow = try self.walk(lhs, initial);
                    const state = try flow.continuing(self.arena);
                    var known = try self.cache.normalCleanupCondition(lhs);
                    if (known == null and self.tree.nodeTag(lhs) == .identifier) {
                        const text = self.tree.tokenSlice(self.tree.nodeMainToken(lhs));
                        if (std.mem.eql(u8, text, "true")) known = true;
                        if (std.mem.eql(u8, text, "false")) known = false;
                    }
                    const short_circuit = if (tag == .bool_and) false else true;
                    if (known != short_circuit) {
                        const right = try self.walk(rhs, state);
                        if (known == null) {
                            try flow.merge(self.arena, right);
                        } else {
                            try flow.normal_exit.merge(self.arena, right.normal_exit);
                            try flow.error_exit.merge(self.arena, right.error_exit);
                            flow.next = right.next;
                            flow.error_value = right.error_value;
                        }
                    }
                    flow.value_known = true;
                    return flow;
                },
                .@"while", .while_simple, .while_cont, .@"for", .for_simple, .@"switch", .switch_comma, .@"break", .@"continue", .@"defer", .@"errdefer", .@"suspend", .@"resume", .@"asm", .asm_simple, .@"orelse" => return self.walkUnknown(node, initial),
                .global_var_decl, .local_var_decl, .simple_var_decl, .aligned_var_decl => {
                    const declaration = self.tree.fullVarDecl(node).?;
                    var flow = if (declaration.ast.init_node.unwrap()) |expression|
                        try self.walk(expression, initial)
                    else
                        CleanupFlow{ .next = initial };
                    flow.next = try flow.continuing(self.arena);
                    flow.error_value = .{};
                    if (declaration.ast.init_node.unwrap()) |expression| {
                        try self.bindSnapshot(&flow.next, declaration.ast.mut_token + 1, expression);
                    }
                    flow.value_known = true;
                    return flow;
                },
                .assign, .assign_destructure => {
                    var flow = try self.walkChildren(node, initial);
                    try self.addRetention(&flow.next, node);
                    if (tag == .assign) try self.reassignOwned(node, &flow.next);
                    return flow;
                },
                .char_literal, .number_literal, .enum_literal, .string_literal, .multiline_string_literal => return .{ .next = initial },
                else => {
                    var flow = try self.walkChildren(node, initial);
                    flow.value_known = switch (tag) {
                        .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma, .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma, .array_init, .array_init_comma, .array_init_one, .array_init_one_comma, .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma, .equal_equal, .bang_equal, .less_than, .greater_than, .less_or_equal, .greater_or_equal, .bool_not, .address_of => true,
                        else => false,
                    };
                    // Indirect builtins can execute arbitrary code. Callbacks
                    // authenticate fullCall nodes, never token spellings.
                    switch (tag) {
                        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => flow.next.invalidate(),
                        else => {},
                    }
                    return flow;
                },
            }
        }
    };
}

/// The cache shares one node and nesting allowance across structural and
/// callee recursion. Resource failures propagate; uncertainty removes positive
/// claims but preserves observed MAY effects.
pub fn inferNormalSuccessCleanup(
    cache: anytype,
    arena: std.mem.Allocator,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    body: Ast.Node.Index,
) CleanupError!NormalSuccessEffects {
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    const tree = cache.tree;
    if (tree.errors.len != 0) return error.InvalidSyntax;
    _ = try checkedTokenCount(tree.source.len, tree.tokens.len);
    var walker = CleanupWalker(@TypeOf(cache)){
        .cache = cache,
        .arena = arena,
        .tree = tree,
        .proto = proto,
        .bindings = bindings,
        .active_node = body,
    };
    const work = CleanupWork.init(cache, &walker.active_node);
    const initial_alternatives = [_]CleanupAlternative{.{ .work = work }};
    var flow = try walker.walk(body, .{ .present = true, .work = work, .alternatives = &initial_alternatives });
    // Blocks consume discarded error values themselves. A bare error-valued
    // expression is not evidence of a successful function fallthrough.
    try flow.normal_exit.merge(arena, flow.next);
    var normal = flow.normal_exit;
    var failure = flow.error_exit;
    try normal.includeIncompleteReleases(arena);
    try failure.includeIncompleteReleases(arena);
    return .{
        .definite_freed_paths = normal.definite_paths,
        .may_freed_paths = normal.may_paths,
        .definite_free_fields = normal.definite_fields,
        .may_free_fields = normal.may_fields,
        .complete = normal.present and normal.complete,
        .retained_owned_params = normal.retained,
        .error_definite_freed_paths = failure.definite_paths,
        .error_may_freed_paths = failure.may_paths,
        .error_definite_free_fields = failure.definite_fields,
        .error_may_free_fields = failure.may_fields,
        .error_complete = failure.present and failure.complete,
        .storage_outcomes = try normal.storageOutcomes(arena),
        .error_storage_outcomes = try failure.storageOutcomes(arena),
        .storage_effects_complete = normal.present and normal.storage_complete,
        .error_storage_effects_complete = failure.present and failure.storage_complete,
    };
}

/// Derive the release and write paths this declaration's OWN body
/// spells out.  `arena` owns the two result slices; their `path` texts
/// borrow `tree`, so a consumer reading a FOREIGN declaration's answer
/// must copy the text — that file's summary arena dies with the file.
///
/// `bindings` are this body's own local bindings, so a store through
/// an alias is attributed to the storage the alias names instead of
/// being dropped: `var copy = self; copy.slot = null` writes the same
/// path `self.slot = null` does.
///
/// Every name is resolved against the binding a USE at that token
/// really names, and a pipe capture's storage comes from the
/// scrutinee it unwraps.  `if (self.slot) |image| { self.gpa.free(
/// image.bytes); self.gpa.destroy(image); }` therefore releases
/// `{0, "slot.bytes"}` and `{0, "slot"}` — the body finally says
/// WHICH field of the receiver it releases, which is the fact a
/// call site needs to tell "the callee released my slot" from "the
/// callee released something I still hold".  `ownerOfExpr` documents
/// which clause shapes carry a provenance and which are charged
/// unknown instead; a `switch` prong's `|v|` is among the charged,
/// so `gpa.destroy(payload)` inside one releases nothing this file
/// can name rather than the parameter that happens to share its
/// spelling.
///
/// See `FieldEffects` for what an entry means and, more importantly,
/// what an EMPTY list does not mean.
pub fn inferFieldEffects(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    body: Ast.Node.Index,
) !FieldEffects {
    const token_count = try checkedTokenCount(tree.source.len, tree.tokens.len);
    var freed: std.ArrayListUnmanaged(ParamPath) = .empty;
    errdefer freed.deinit(arena);
    var written: std.ArrayListUnmanaged(ParamPath) = .empty;
    errdefer written.deinit(arena);

    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var t: tokens.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            continue;
        }
        // `<alloc>.free(<storage>)` / `.destroy(<storage>)`: the memory
        // being handed back is the ARGUMENT, so the argument is what
        // this body releases — reading the receiver would charge the
        // allocator for the storage it holds.
        if (tags[t] == .period and t + 2 <= last and tags[t + 1] == .identifier and
            tags[t + 2] == .l_paren)
        {
            const method = tree.tokenSlice(t + 1);
            if (std.mem.eql(u8, method, "free") or std.mem.eql(u8, method, "destroy")) {
                const receiver: ?[]const u8 = if (t > 0 and t > first and tags[t - 1] == .identifier)
                    tree.tokenSlice(t - 1)
                else
                    null;
                if (tokens.matchParen(tags, t + 2, last)) |rp| {
                    var arg = firstArgument(tags, t + 3, rp);
                    while (arg) |range| : (arg = nextArgument(tags, range.end, rp)) {
                        const path = paramPathFromOwner(
                            try ownerOfExprWithTokenCount(
                                arena,
                                tree,
                                proto,
                                bindings,
                                range.start,
                                range.end,
                                0,
                                token_count,
                            ),
                        ) orelse continue;
                        // A whole-value argument on an allocator-shaped
                        // receiver is the allocator being PASSED
                        // (`obj.destroy(alloc)`), not released.
                        if (path.path.len == 0 and receiver != null and
                            !isAllocatorName(receiver.?) and
                            isAllocatorName(tree.tokenSlice(range.start)))
                        {
                            continue;
                        }
                        try freed.append(arena, path);
                    }
                    t = rp;
                    continue;
                }
            }
            continue;
        }
        if (!isStoreOp(tags[t])) continue;
        if (t == 0) continue;
        if (t == first) continue;
        // `self.* = other` names the parameter's whole storage, so the
        // range handed to the resolver stops before the `.*`.
        const whole_object = tags[t - 1] == .period_asterisk;
        const root = storeTargetRoot(tags, t, first, whole_object) orelse continue;
        // `const x = …` / `var x = …` binds a name; the parameter is
        // the store's target only when this body did not declare it.
        if (root > first and (tags[root - 1] == .keyword_const or tags[root - 1] == .keyword_var)) continue;
        // `.{ .items = … }` initialises a FIELD: the token before the
        // name is the dot, and nothing about the field is being stored
        // through.  A parameter that happens to share the field's name
        // must not read as a write to it.
        if (root > first and tags[root - 1] == .period) continue;
        const target_last = if (whole_object) root else t - 1;
        const path = paramPathFromOwner(
            try ownerOfExprWithTokenCount(
                arena,
                tree,
                proto,
                bindings,
                root,
                target_last,
                0,
                token_count,
            ),
        ) orelse continue;
        try written.append(arena, if (whole_object) .{ .param = path.param, .path = "" } else path);
    }
    const freed_paths = try freed.toOwnedSlice(arena);
    errdefer arena.free(freed_paths);
    const written_paths = try written.toOwnedSlice(arena);
    return .{
        .freed_paths = freed_paths,
        .written_paths = written_paths,
    };
}

/// The parameter path an expression's storage owner names, or null
/// when the owner could not be rooted — which is charged, not assumed
/// to be storage-free.
fn paramPathFromOwner(owner: StorageOwner) ?ParamPath {
    return switch (owner) {
        .param => |p| p,
        .unknown => null,
    };
}

/// First token of the value a store at `store_tok` writes through,
/// following the dotted chain back to its root and dropping a `.*`.
fn storeTargetRoot(
    tags: []const std.zig.Token.Tag,
    store_tok: tokens.TokenIndex,
    first: tokens.TokenIndex,
    whole_object: bool,
) ?tokens.TokenIndex {
    var t = store_tok - 1;
    if (whole_object) {
        if (t <= first or tags[t] != .period_asterisk) return null;
        t -= 1;
    }
    if (tags[t] != .identifier) return null;
    while (t > first and tags[t - 1] == .period and t >= 2 and tags[t - 2] == .identifier) t -= 2;
    return t;
}

/// One call argument: `[start, end]` of the tokens between the
/// top-level commas of `( … )`, without the parentheses.
const ArgRange = struct { start: tokens.TokenIndex, end: tokens.TokenIndex };

fn firstArgument(tags: []const std.zig.Token.Tag, from: tokens.TokenIndex, rp: tokens.TokenIndex) ?ArgRange {
    if (from >= rp) return null;
    return argumentEndingAt(tags, from, rp);
}

/// The argument after the one that ended at `prev_end`, found by the
/// comma that closed it.  Nested commas inside `()` / `{}` / `[]` do
/// not separate arguments.
fn nextArgument(tags: []const std.zig.Token.Tag, prev_end: tokens.TokenIndex, rp: tokens.TokenIndex) ?ArgRange {
    const comma = prev_end + 1;
    if (comma >= rp or tags[comma] != .comma) return null;
    const start = comma + 1;
    if (start >= rp) return null;
    return argumentEndingAt(tags, start, rp);
}

fn argumentEndingAt(tags: []const std.zig.Token.Tag, start: tokens.TokenIndex, rp: tokens.TokenIndex) ArgRange {
    var depth: u32 = 0;
    var t = start;
    while (t < rp) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => {
                if (depth == 0) return .{ .start = start, .end = t - 1 };
                depth -= 1;
            },
            .comma => if (depth == 0) return .{ .start = start, .end = t - 1 },
            else => {},
        }
    }
    return .{ .start = start, .end = rp - 1 };
}

/// True iff `tag` stores a value through the expression on its left.
///
/// This is EVERY tag that spells `x op= y` in Zig, plus `=`, because
/// each of them writes its target in place — the bitshift and the
/// saturating shift (`<<=`, `>>=`, `<<|=`) and the wrapping and
/// saturating arithmetic (`+%=`, `+|=`, `-%=`, `-|=`, `*%=`, `*|=`)
/// are stores exactly as much as `+=` is, and a caller that filters
/// them out credits a condition it should have stopped crediting.
///
/// `<=` and `>=` are NOT here: they are COMPARISONS
/// (`.angle_bracket_left_equal` / `.angle_bracket_right_equal`), and
/// the shift-assign tags are the doubled spellings.  `==`, `!=` and
/// `=>` are distinct tokens and never match either.
fn isStoreOp(tag: std.zig.Token.Tag) bool {
    return switch (tag) {
        .equal,
        .pipe_equal,
        .percent_equal,
        .caret_equal,
        .plus_equal,
        .plus_percent_equal,
        .plus_pipe_equal,
        .minus_equal,
        .minus_percent_equal,
        .minus_pipe_equal,
        .asterisk_equal,
        .asterisk_percent_equal,
        .asterisk_pipe_equal,
        .slash_equal,
        .ampersand_equal,
        .angle_bracket_angle_bracket_left_equal,
        .angle_bracket_angle_bracket_left_pipe_equal,
        .angle_bracket_angle_bracket_right_equal,
        => true,
        else => false,
    };
}

/// Deepest `<param> . <local> . …` chain followed before the answer is
/// declared unknown.  Chains longer than this are vanishingly rare and
/// the alternative (following them) risks not terminating on a
/// self-referential binding.
const max_owner_depth = 6;

/// The error set the storage-rooting walks in this file carry. AST-only
/// questions return conservative answers; allocating joined paths can
/// fail, and token-index admission can reject a source that is too wide.
/// The explicit set is required because these walks recurse mutually.
const WalkError = std.mem.Allocator.Error || error{SourceTooWide};

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
/// PAST its last token.  A `(` or `[` inside the range ends the walk
/// early, which the caller detects by comparing against `last + 1`.
///
/// The walk starts ON the root, not after it: a chain that ends on the
/// root's own token (`list` alone) and one that ends on a field
/// (`pair.input`) have to come back the same way, and returning the
/// last segment's token instead made every qualified route read as
/// "one token too many" — so `pair.input` and `self.lines` were
/// reported as unplaceable storage, and a caller could not tell an
/// owner's field from state it was handed.
fn pathChainEnd(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (first > last or tags[first] != .identifier) return null;
    var t: Ast.TokenIndex = first;
    while (t + 2 <= last and tags[t + 1] == .period and tags[t + 2] == .identifier) : (t += 2) {}
    return t + 1;
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
/// `first` is also WHERE the use is written, which is what the name it
/// names is resolved against: an initializer alias is read at its own
/// RHS, and a `const` / `var` / capture that shadows a parameter's
/// name answers for itself inside its own scope instead of silently
/// reading as that parameter.
///
/// A pipe capture is the one binding whose initializer the AST can
/// place.  An optional's SUCCESS payload is stored in the scrutinee
/// itself, so `if (self.slot) |image| …` unwraps to `self.slot` and
/// `image.bytes` reads as `slot.bytes`.  Every other clause binds a
/// value that is not the scrutinee's storage — an `else` payload sits
/// in the error union's field, a `catch` payload is a value the error
/// path built, a `for` capture is one element copied out of an
/// iterable and `|*v|` is a pointer INTO one — and each of those is
/// charged `.unknown` rather than resolved to the expression written
/// beside it.
///
/// A `switch` prong payload is charged for the same reason, and the
/// prong is the case where saying so matters most: the tag picks the
/// union field, so `.List => |list| list.append(…)` names a COPY of
/// one field while the expression beside the prong is the whole
/// union.  Reading `list` as the scrutinee, as a same-spelled
/// parameter, or as an alias declared above the switch would all be
/// answers this file cannot give.
///
/// Everything else — a call result, an index, a cast, a local this
/// file cannot read — is `.unknown` too.  Unknown means "may carry
/// any storage", never "carries none".
pub fn ownerOfExpr(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    depth: u8,
) WalkError!StorageOwner {
    const token_count = try checkedTokenCount(tree.source.len, tree.tokens.len);
    return ownerOfExprWithTokenCount(arena, tree, proto, bindings, first, last, depth, token_count);
}

fn ownerOfExprWithTokenCount(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    depth: u8,
    token_count: TokenIndex,
) WalkError!StorageOwner {
    const tags = tree.tokens.items(.tag);
    if (first > last) return .unknown;
    // `&x` and `try x` wrap an expression without changing the storage
    // it names.
    switch (tags[first]) {
        .ampersand, .keyword_try => return ownerOfExprWithTokenCount(
            arena,
            tree,
            proto,
            bindings,
            first + 1,
            last,
            depth,
            token_count,
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
    // A declaration this position really names outranks the parameter
    // of the same name.  Asking the parameter table first answered
    // `slot` for a `const slot = …` and for an `if (self.slot) |
    // slot|` written inside this body, charging storage to a
    // parameter the value has stopped being.  `nameAtUse` also holds
    // an `else |e|` payload, which `bindings` never recorded and
    // which the parameter table must not answer for either.
    if (nameAtUse(bindings, tree, proto, root, first, token_count)) |decl| {
        return ownerOfBinding(arena, tree, proto, bindings, decl, fields, depth, token_count);
    }
    if (paramIndex(tree, proto, root)) |idx| {
        return .{ .param = .{ .param = idx, .path = fields } };
    }
    return .unknown;
}

/// The declaration a USE of `name` written at `use_token` names.
///
/// `LocalBindings.findAt` answers that question from the binding's own
/// `scope_open` / `scope_close`, and that is right for a `const` /
/// `var`: the declaration is written inside the block it lives in.  A
/// pipe capture is written BEFORE the `{` that opens its branch body,
/// so `assignScopes` leaves it the ENCLOSING block's span — one range
/// covering the `else` branch and every sibling `if` under the same
/// statement.  A capture is therefore asked of the AST for its own
/// body, and a clause `local_bindings` never built as a binding at all
/// — an `else` payload, a `switch` prong's `|v|` — is asked of the AST
/// too, because a name a clause binds is a declaration whether or not
/// the table holds it.
///
/// All three kinds compete on ONE rule: the declaration written last
/// before the use is the one the use names.  A parameter is left out
/// so the caller's fallback answers for it, which keeps a parameter
/// reachable from every position its own scope covers while a local or
/// a capture of the same name wins inside the scope that shadows it.
const NameBinding = union(enum) {
    /// A declaration `LocalBindings` recorded.
    local: *const local_bindings.Binding,
    /// A pipe clause `LocalBindings` never recorded.  Its `body` says
    /// where the name is in scope and whether it is the scrutinee's
    /// own storage at all.
    clause: BranchClause,
};

fn nameAtUse(
    bindings: *const local_bindings.LocalBindings,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    name: []const u8,
    use_token: TokenIndex,
    token_count: TokenIndex,
) ?NameBinding {
    var best: ?NameBinding = null;
    var best_pos: TokenIndex = 0;
    for (bindings.items) |*b| {
        if (!std.mem.eql(u8, b.name, name)) continue;
        if (b.name_token > use_token) continue;
        if (b.origin == .param) continue;
        switch (b.origin) {
            .loop_capture => {
                const body = captureBody(tree, proto, b.name_token, token_count) orelse continue;
                if (!body.contains(use_token)) continue;
            },
            else => if (use_token < b.scope_open or use_token > b.scope_close) continue,
        }
        if (best == null or b.name_token > best_pos) {
            best = .{ .local = b };
            best_pos = b.name_token;
        }
    }
    // A clause the table does not hold is still a declaration, and it
    // wins when it is written after whatever the table does hold: an
    // `else |e|` payload shadows an outer alias or parameter of that
    // name, a prong's `|v|` shadows one the same way, while a
    // `const e` written inside the error branch shadows the payload in
    // turn.  Without this the outer declaration answers, and a
    // `destroy`'s error branch releases the caller's storage.
    if (nearestBranchClause(tree, proto, name, use_token, null)) |c| {
        if (best == null or c.name_token > best_pos) return .{ .clause = c };
    }
    return best;
}

/// Storage the binding a USE named carries, with `fields` — the dotted
/// path that use spelled on top of the name — appended to it.  The
/// name is answered by following what declared it, so an alias of a
/// capture and the capture itself report one owner.
fn ownerOfBinding(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    use: NameBinding,
    fields: []const u8,
    depth: u8,
    token_count: TokenIndex,
) WalkError!StorageOwner {
    // Forwarding is what the alias rule exists for, and a chain this
    // long is charged rather than followed forever.
    if (depth >= max_owner_depth) return .unknown;
    const tags = tree.tokens.items(.tag);
    var rhs_first: TokenIndex = undefined;
    var rhs_last: TokenIndex = undefined;
    switch (use) {
        .local => |b| {
            rhs_first = b.rhsFirstAfterTry(tags);
            rhs_last = b.rhs_last;
            // A `for` capture is one element COPIED out of an
            // iterable, and an `else` / `catch` payload is not the
            // storage written beside the clause at all; only an
            // optional's success value is the scrutinee's own
            // storage.  A clause the AST could not place is charged
            // the same way.
            if (b.origin == .loop_capture) {
                const body = captureBody(tree, proto, b.name_token, token_count) orelse return .unknown;
                if (!body.carries_scrutinee_storage) return .unknown;
            }
        },
        .clause => |c| {
            // The scrutinee of an `if` / `while` optional is spelled
            // BEFORE the clause, so the names in it resolve at their
            // own position and a capture can never name itself.  An
            // `else` payload's source is the error union above it,
            // whose field this file cannot name, so there is nothing
            // to read.
            if (!c.body.carries_scrutinee_storage) return .unknown;
            const span = scrutineeSpan(tree, c) orelse return .unknown;
            rhs_first = span[0];
            rhs_last = span[1];
        },
    }
    if (rhs_first > rhs_last) return .unknown;
    const inner = try ownerOfExprWithTokenCount(
        arena,
        tree,
        proto,
        bindings,
        rhs_first,
        rhs_last,
        depth + 1,
        token_count,
    );
    return switch (inner) {
        .unknown => .unknown,
        .param => |p| .{ .param = .{
            .param = p.param,
            .path = try joinPath(arena, p.path, fields),
        } },
    };
}

/// The block a pipe capture's name is written in.
///
/// `LocalBindings` cannot answer that: a clause is written before the
/// `{` that opens its branch, so the block recorded for it is the
/// ENCLOSING one — a range covering the `else` branch and every
/// sibling `if` under the same statement.  The node the clause is
/// attached to says which expression the payload is in scope in:
/// `then_expr` for a success payload, `else_expr` for an error one,
/// and a prong's `target_expr` for a `switch` payload — the one shape
/// that may be written with no braces at all.
/// A `{}` written inside any of them is inside that span by
/// construction, which is what keeps a use in a block nested inside an
/// error branch reading the error payload rather than an outer
/// declaration.
const BranchBody = struct {
    open: TokenIndex,
    close: TokenIndex,
    /// True only for a payload that IS the storage the scrutinee was
    /// read out of — the success value an `if` / `while` unwraps off
    /// its condition, which is that storage whether the condition is
    /// an optional (`if (self.slot) |image|`) or an error union
    /// (`if (self.res) |v| … else |err|`).  A `for` capture is one
    /// element copied out of an iterable, a `switch` prong binds a
    /// copy of the field its tag selected, and an `else` / `catch`
    /// payload is a value the error path built; none of those is the
    /// expression the clause follows.
    carries_scrutinee_storage: bool,
    /// True for a `for` capture — one value copied out of an iterable.
    /// A caller handed it moves the storage the ELEMENT names, never
    /// the buffer the loop read from, which is why it keeps an answer
    /// of its own rather than being folded into the iterable's.  A
    /// `switch` prong is an element of nothing, so it is false there
    /// too and the prong is charged.
    is_iterable_element: bool,

    /// A use inside the body, ends included.  `open` is the body's
    /// first token, which for a braced body is a `{` no name is ever
    /// written on, so nothing is lost by including it.
    fn contains(self: BranchBody, tok: TokenIndex) bool {
        return tok >= self.open and tok <= self.close;
    }
};

/// A `|name|` clause, as the node it is attached to gives it.
const BranchClause = struct {
    /// The identifier the clause binds.
    name_token: TokenIndex,
    body: BranchBody,
    /// The condition / iterable node a payload was read out of, or
    /// null for a clause with no readable scrutinee.  Stored as a
    /// plain node index because `firstToken` / `lastToken` take one:
    /// a reader unwraps it and charges when there is nothing to read.
    scrutinee: ?Ast.Node.Index,
};

/// The block the capture whose identifier is at `name_token` is in
/// scope in, or null when no node of this file places it.
fn captureBody(tree: *const Ast, proto: Ast.full.FnProto, name_token: TokenIndex, token_count: TokenIndex) ?BranchBody {
    if (nearestBranchClause(tree, proto, tree.tokenSlice(name_token), name_token, name_token)) |c| {
        return c.body;
    }
    return catchClauseBody(tree, name_token, token_count);
}

/// The token range a clause's payload was read out of, or null when
/// the clause has no scrutinee this file can read — an `else` payload,
/// whose source is the error union above it rather than a field of a
/// nameable expression.  A reader charges on null rather than
/// defaulting to a range, because there is no range that means it.
fn scrutineeSpan(tree: *const Ast, c: BranchClause) ?[2]TokenIndex {
    const node = c.scrutinee orelse return null;
    return .{ tree.firstToken(node), tree.lastToken(node) };
}

/// The innermost `if` / `while` / `for` / `switch` clause binding
/// `name`.
///
/// Two questions come out of one walk because both are answered by the
/// same thing — the clause's own `payload_token` / `error_token` and
/// the expression that payload is in scope in.  `exact` pins the
/// answer to the clause a KNOWN identifier belongs to and needs no
/// containment, since that identifier is written in FRONT of the body
/// it is in scope in; without it the answer is the clause binding a
/// SPELLING whose body a use at `anchor` sits in, which is what finds
/// the `else |e|` payload and the `switch` prong's `|v|` that
/// `local_bindings` never recorded.
fn nearestBranchClause(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    name: []const u8,
    anchor: TokenIndex,
    exact: ?TokenIndex,
) ?BranchClause {
    const gate = exact orelse anchor;
    // A branch node's main token IS its `if` / `while` / `for` /
    // `switch` keyword, so a node starting after the gate cannot hold
    // the clause and is skipped without a `full*` call.
    const main_tokens = tree.nodes.items(.main_token);
    // Only this fn's own body can bind a name one of its expressions
    // reads, and the parser emits that body as one contiguous run of
    // nodes, so the walk covers that run instead of the whole array.
    // Without that bound the whole array is walked: that is what this
    // replaces, not a new correctness claim.
    const body = fnBodyNodes(tree, proto);
    var found: ?BranchClause = null;
    var idx: u32 = if (body) |b| b.first else 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const main = main_tokens[idx];
        if (body) |b| {
            // The bound is the subtree's own index, not a token's.
            // Nodes are NOT main-token sorted: a nested `if` is
            // emitted after its own children, and so is the
            // container a struct-declared fn sits in — so leaving the
            // run on a token would truncate the walk on a node this
            // body owns.  The gate below still filters one node at a
            // time for the same reason.
            if (idx > b.end) break;
        }
        if (main > gate) continue;
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.fullIf(node)) |n| {
            considerIf(tree, n, name, anchor, exact, &found);
        } else if (tree.fullWhile(node)) |n| {
            considerWhile(tree, n, name, anchor, exact, &found);
        } else if (tree.fullFor(node)) |n| {
            considerFor(tree, n, name, anchor, exact, &found);
        } else if (tree.fullSwitch(node)) |n| {
            considerSwitch(tree, n, name, anchor, exact, &found);
        }
    }
    return found;
}

/// The nodes one fn's BODY occupies in `tree.nodes`: the first index of
/// the run and the last, both from the parser's own emission order.
///
/// `std.zig.Parse` emits one container member at a time, and each step
/// is provable from the source: `parseFnProto` RESERVES the
/// `fn_proto` slot before it parses the parameters and return type and
/// fills it in afterwards ("we want the fn proto node to be before its
/// children in the array"), `expectTopLevelDecl` reserves the
/// `fn_decl` slot before `parseBlock` runs and fills it in afterwards,
/// and `parseBlock` calls `addNode` for the block only after every
/// statement inside it.  `reserveNode` merely grows the array and
/// `setNode` writes in place, so a member's subtree is exactly the
/// contiguous run `fn_decl_index + 1 .. body_block_index` — no node
/// allocated inside the body falls outside it, and no node outside it
/// falls inside.  `proto_node` names the header's slot (every
/// `fnProto*` variant sets it to the node it was handed), so the
/// declaration owning this proto is the `fn_decl` pointing back at it,
/// and its body is the second node beside it.
///
/// This is deliberately an index range and not a token one.  A node is
/// emitted after its own children, so a node inside a body can carry a
/// main token BEFORE that body's `{` — and a container wrapping a whole
/// struct-declared fn is emitted after the fn's subtree while carrying
/// the `struct` keyword's token.  Truncating on tokens would drop a
/// node the body owns; truncating on indices cannot.
///
/// `null` is the honest answer for a proto no `fn_decl` owns — an
/// `extern fn`, a fn type spelled in a field — and the walk then covers
/// the whole array, which is what was already correct for them.
fn fnBodyNodes(
    tree: *const Ast,
    proto: Ast.full.FnProto,
) ?struct { first: u32, end: u32 } {
    var idx: u32 = @intFromEnum(proto.ast.proto_node) + 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        if (tree.nodeData(node).node_and_node[0] != proto.ast.proto_node) continue;
        const fn_body = tokens.bodyOf(tree, node) orelse return null;
        return .{ .first = idx + 1, .end = @intFromEnum(fn_body) };
    }
    return null;
}

/// Keep the clause written LAST: it is the innermost one, and the one
/// a use inside another clause's body must not read through.
fn nearerClause(found: *?BranchClause, candidate: BranchClause) void {
    if (found.*) |f| {
        if (f.name_token > candidate.name_token) return;
    }
    found.* = candidate;
}

/// Does the clause answer this walk's question?  The caller has
/// already matched the clause's SPELLING against the name asked
/// about, so what is left here is containment — except when the
/// question was pinned to one known identifier, which is written in
/// front of the body it belongs to and so cannot be inside it.
fn clauseAnswers(
    exact: ?TokenIndex,
    clause_name: TokenIndex,
    body: BranchBody,
    anchor: TokenIndex,
) bool {
    if (exact) |e| return clause_name == e;
    return body.contains(anchor);
}

/// Record the clause `n` binds for this walk, when it is the one
/// asked for.
fn considerIf(
    tree: *const Ast,
    n: Ast.full.If,
    name: []const u8,
    anchor: TokenIndex,
    exact: ?TokenIndex,
    found: *?BranchClause,
) void {
    if (payloadNameToken(tree, n.payload_token)) |t| {
        // `if (cond) |x|` UNWRAPS `cond`, so `x` holds the storage
        // that was read out of it — an optional's success value for
        // `if (self.slot) |image|`, and the very same thing for an
        // error union's in `if (self.res) |v| … else |err|`.  The
        // `else` payload is the value the error path built, and that
        // is the clause charged below; an `if` that ALSO has an
        // `else` does not make its success payload unknown.
        const body: BranchBody = .{
            .open = tree.firstToken(n.ast.then_expr),
            .close = tree.lastToken(n.ast.then_expr),
            .carries_scrutinee_storage = true,
            .is_iterable_element = false,
        };
        if (std.mem.eql(u8, tree.tokenSlice(t), name) and clauseAnswers(exact, t, body, anchor)) {
            nearerClause(found, .{
                .name_token = t,
                .body = body,
                .scrutinee = n.ast.cond_expr,
            });
        }
    }
    if (n.error_token) |e| {
        if (!std.mem.eql(u8, tree.tokenSlice(e), name)) return;
        const node = n.ast.else_expr.unwrap() orelse return;
        const body: BranchBody = .{
            .open = tree.firstToken(node),
            .close = tree.lastToken(node),
            .carries_scrutinee_storage = false,
            .is_iterable_element = false,
        };
        if (!clauseAnswers(exact, e, body, anchor)) return;
        nearerClause(found, .{ .name_token = e, .body = body, .scrutinee = null });
    }
}

/// A `while` is an `if` over its body, plus the continue expression
/// written AFTER the body with the payload still in scope.
fn considerWhile(
    tree: *const Ast,
    n: Ast.full.While,
    name: []const u8,
    anchor: TokenIndex,
    exact: ?TokenIndex,
    found: *?BranchClause,
) void {
    if (payloadNameToken(tree, n.payload_token)) |t| {
        // `while (c) |v| : (cont) { body }` writes the continue
        // expression BEFORE the body, and the payload is in scope in
        // both, so the span runs from whichever of the two comes
        // first to the end of the body.
        var open = tree.firstToken(n.ast.then_expr);
        if (n.ast.cont_expr.unwrap()) |cont| open = @min(open, tree.firstToken(cont));
        const body: BranchBody = .{
            .open = open,
            .close = tree.lastToken(n.ast.then_expr),
            .carries_scrutinee_storage = true,
            .is_iterable_element = false,
        };
        if (std.mem.eql(u8, tree.tokenSlice(t), name) and clauseAnswers(exact, t, body, anchor)) {
            nearerClause(found, .{
                .name_token = t,
                .body = body,
                .scrutinee = n.ast.cond_expr,
            });
        }
    }
    if (n.error_token) |e| {
        if (!std.mem.eql(u8, tree.tokenSlice(e), name)) return;
        const node = n.ast.else_expr.unwrap() orelse return;
        const body: BranchBody = .{
            .open = tree.firstToken(node),
            .close = tree.lastToken(node),
            .carries_scrutinee_storage = false,
            .is_iterable_element = false,
        };
        if (!clauseAnswers(exact, e, body, anchor)) return;
        nearerClause(found, .{ .name_token = e, .body = body, .scrutinee = null });
    }
}

/// A `for` capture is an ELEMENT of the iterable — a leaf, never the
/// iterable's own header — so it never carries the scrutinee's
/// storage.  Only the first identifier of `|x, i|` is
/// `payload_token`; an index capture is read from the tokens.
fn considerFor(
    tree: *const Ast,
    n: Ast.full.For,
    name: []const u8,
    anchor: TokenIndex,
    exact: ?TokenIndex,
    found: *?BranchClause,
) void {
    const t = payloadNameToken(tree, n.payload_token) orelse return;
    if (!std.mem.eql(u8, tree.tokenSlice(t), name)) return;
    const body: BranchBody = .{
        .open = tree.firstToken(n.ast.then_expr),
        .close = tree.lastToken(n.ast.then_expr),
        .carries_scrutinee_storage = false,
        .is_iterable_element = true,
    };
    if (!clauseAnswers(exact, t, body, anchor)) return;
    const inputs = n.ast.inputs;
    nearerClause(found, .{
        .name_token = t,
        .body = body,
        .scrutinee = if (inputs.len == 0) null else inputs[0],
    });
}

/// A prong's `|v|` binds a COPY of whichever union field its tag
/// selected, so it is not the scrutinee's storage, is not an element
/// of anything, and is never an element answer.  It is still a
/// DECLARATION — the one thing that keeps a same-spelled parameter or
/// outer alias from answering for a use inside the prong — so it is
/// charged, with no scrutinee to read, which is what a reader does
/// with any clause whose source it cannot name.
///
/// The prong's `target_expr` is the whole scope, braced or not: a
/// braceless target and a nested block inside it are both inside that
/// one node's token range.  The clause itself is written AFTER the
/// `=>` and ends where the target begins, so every identifier between
/// the two is a declaration of THIS prong — `|v|`, `|*v|`,
/// `|payload, tag|` and `|_, tag|` alike — and sibling prongs reusing
/// a spelling keep separate identities.
fn considerSwitch(
    tree: *const Ast,
    n: Ast.full.Switch,
    name: []const u8,
    anchor: TokenIndex,
    exact: ?TokenIndex,
    found: *?BranchClause,
) void {
    const tags = tree.tokens.items(.tag);
    for (n.ast.cases) |case_node| {
        const prong = tree.fullSwitchCase(case_node) orelse continue;
        const target = prong.ast.target_expr;
        const body: BranchBody = .{
            .open = tree.firstToken(target),
            .close = tree.lastToken(target),
            .carries_scrutinee_storage = false,
            .is_iterable_element = false,
        };
        var t = payloadNameToken(tree, prong.payload_token) orelse continue;
        const clause_end = tree.firstToken(target);
        while (t < clause_end) : (t += 1) {
            if (tags[t] != .identifier) continue;
            // `|_|` discards; it binds nothing a later use can name.
            if (std.mem.eql(u8, tree.tokenSlice(t), "_")) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
            if (!clauseAnswers(exact, t, body, anchor)) continue;
            nearerClause(found, .{
                .name_token = t,
                .body = body,
                .scrutinee = null,
            });
        }
    }
}

/// The identifier a capture clause binds.  `payload_token` points at
/// the first token after the bars, which is the identifier itself or
/// the `*` of a pointer capture.
fn payloadNameToken(tree: *const Ast, payload: ?TokenIndex) ?TokenIndex {
    const tok = payload orelse return null;
    if (tree.tokenTag(tok) == .asterisk) return tok + 1;
    return tok;
}

/// The block a `catch` clause's body runs in, read from the tokens.
///
/// `catch |e| { … }` is a clause on an expression suffix rather than
/// on a statement node, so the walk that finds the other clauses
/// cannot see it.  Its body is the block that FOLLOWS the clause, and
/// the scan stops at every token a body can never follow — a `;` or a
/// `}` — so a clause with no block of its own cannot claim the next
/// statement's.  A `catch` payload is a value the error path built,
/// never the storage the expression beside it read from, so it is
/// charged.
fn catchClauseBody(tree: *const Ast, name_token: TokenIndex, token_count: TokenIndex) ?BranchBody {
    const tags = tree.tokens.items(.tag);
    const end = token_count;
    // Close the clause: the `|` in front of the body.
    var t: TokenIndex = name_token + 1;
    while (t < end and tags[t] != .pipe) {
        switch (tags[t]) {
            .identifier, .comma, .asterisk, .ampersand => {},
            else => return null,
        }
        t += 1;
    }
    if (t >= end) return null;
    // The body follows the clause.  Braces inside parentheses are not
    // a body, and a `while (c) |v| : (i += 1)` continue expression
    // sits between the two.
    var depth: u32 = 0;
    t += 1;
    while (t < end) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket => depth += 1,
            .r_paren, .r_bracket => {
                if (depth > 0) depth -= 1;
            },
            .l_brace => {
                if (depth != 0) continue;
                const close = tokens.matchBrace(tags, t, end - 1) orelse return null;
                return .{
                    .open = t,
                    .close = close,
                    .carries_scrutinee_storage = false,
                    .is_iterable_element = false,
                };
            },
            .semicolon, .r_brace => return null,
            else => {},
        }
    }
    return null;
}

/// The allocation `[first, last]` names, for a consumer asking
/// whether two values can reach ONE buffer rather than which
/// parameter index they belong to.
///
/// The walk is `ownerOfExpr`'s, with three answers it collapses into
/// `.unknown` kept apart, because "this file cannot say" and "this
/// is definitely not that" are different claims:
///
///   - a FOR capture is `.element`.  It is one value copied out of an
///     iterated buffer — a leaf, not the buffer's header — so a callee
///     handed it grows the storage the ELEMENT names, never the list
///     the loop captured.  The other pipe captures are not elements:
///     an optional's success payload is held IN the field the
///     scrutinee read from, so it is that field's placement, while an
///     `else` / `catch` payload is a value the error path built and a
///     prong's `|v|` is a copy of the field its tag selected — neither
///     is given an identity here, and both are charged `.unknown`
///     rather than named after the union they were read from.
///   - a name that is neither a parameter nor a local of this fn is
///     a CONTAINER-LEVEL declaration, so `.shared`.  Reading it as
///     `.unknown` would charge every call a file-level constant to
///     whatever the caller happens to be walking.
///   - a LOCAL whose initializer CONSTRUCTED it is `.local`, and a
///     local that NAMED something else is a header copy and is
///     followed to that source.  The split is what makes `&local`
///     an address inside an object this fn laid out, rather than a
///     pointer this fn was handed.
///
/// Identity is resolved exactly as `ownerOfExpr` resolves it — by
/// `nameAtUse`, at the position the use is written — so the declaration
/// a `.local.token` names is the one in scope THERE and not the first
/// of that spelling in the fn, and a prong payload that shares a
/// spelling with a container-level `var` is the prong's declaration
/// rather than that `.shared` one.
pub fn placementOfExpr(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    depth: u8,
) WalkError!Placement {
    const token_count = try checkedTokenCount(tree.source.len, tree.tokens.len);
    return placementOfExprWithTokenCount(
        arena,
        tree,
        proto,
        bindings,
        first,
        last,
        depth,
        token_count,
    );
}

fn placementOfExprWithTokenCount(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    depth: u8,
    token_count: TokenIndex,
) WalkError!Placement {
    const tags = tree.tokens.items(.tag);
    if (first > last) return .unknown;
    switch (tags[first]) {
        .ampersand, .keyword_try => return placementOfExprWithTokenCount(
            arena,
            tree,
            proto,
            bindings,
            first + 1,
            last,
            depth,
            token_count,
        ),
        else => {},
    }
    const chain_end = pathChainEnd(tree, first, last) orelse return .unknown;
    var end = chain_end;
    if (end <= last and tags[end] == .period_asterisk) end += 1;
    if (end != last + 1) return .unknown;

    const fields = tokenText(tree, first + 2, chain_end - 1);
    const root = tree.tokenSlice(first);
    // The declaration this position names outranks the parameter of the
    // same name: `bindings.find` returned the FIRST binding of a
    // spelling, so `&item` after a sibling block had already declared
    // an `item` of its own reported an address inside THAT one.
    const decl = nameAtUse(bindings, tree, proto, root, first, token_count) orelse
        return paramPlacement(tree, proto, root, fields);
    if (depth >= max_owner_depth) return .unknown;
    return switch (decl) {
        .clause => |c| blk: {
            // Only an optional's success payload is the storage the
            // scrutinee read from.  An `else` payload is the error
            // union's own value and a `for` payload an element of the
            // iterable; neither is given an identity here.
            if (!c.body.carries_scrutinee_storage) break :blk .unknown;
            const span = scrutineeSpan(tree, c) orelse break :blk .unknown;
            const inner = try placementOfExprWithTokenCount(
                arena,
                tree,
                proto,
                bindings,
                span[0],
                span[1],
                depth + 1,
                token_count,
            );
            break :blk withFields(arena, inner, fields);
        },
        .local => |b| {
            if (b.origin == .loop_capture) {
                const body = captureBody(tree, proto, b.name_token, token_count) orelse return .unknown;
                if (body.is_iterable_element) return .element;
                return placementOfCapture(
                    arena,
                    tree,
                    proto,
                    bindings,
                    b.name,
                    b.name_token,
                    fields,
                    depth,
                    token_count,
                );
            }
            const rhs = b.rhsFirstAfterTry(tags);
            if (rhs > b.rhs_last) return .unknown;
            if (initializerConstructs(tags[rhs]) or
                (tags[rhs] == .identifier and std.mem.eql(u8, tree.tokenSlice(rhs), "undefined")))
            {
                return .{ .local = .{ .token = b.name_token } };
            }
            // A header copy (`const copy = list;`) shares the buffer it
            // names, so the question it raises is the source's question.
            return placementOfExprWithTokenCount(
                arena,
                tree,
                proto,
                bindings,
                rhs,
                b.rhs_last,
                depth + 1,
                token_count,
            );
        },
    };
}

/// The placement of a name that is not declared by a local or a pipe
/// clause: the parameter it is a parameter of, or `.shared` for a
/// container-level declaration this fn only names.
fn paramPlacement(
    tree: *const Ast,
    proto: Ast.full.FnProto,
    root: []const u8,
    fields: []const u8,
) Placement {
    if (paramIndex(tree, proto, root)) |idx| {
        return .{ .param = .{ .param = idx, .path = fields } };
    }
    return .shared;
}

/// The placement of an optional capture: the value is held IN the
/// field the scrutinee read from, so it is that field's placement with
/// the use's own dotted path appended — a header copy, exactly what
/// `const copy = o.field;` produces.  A capture the AST cannot place,
/// or one whose payload is not the scrutinee's own storage, is charged.
fn placementOfCapture(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    name: []const u8,
    name_token: TokenIndex,
    fields: []const u8,
    depth: u8,
    token_count: TokenIndex,
) WalkError!Placement {
    if (depth >= max_owner_depth) return .unknown;
    const c = nearestBranchClause(tree, proto, name, name_token, name_token) orelse return .unknown;
    if (!c.body.carries_scrutinee_storage) return .unknown;
    const span = scrutineeSpan(tree, c) orelse return .unknown;
    const inner = try placementOfExprWithTokenCount(
        arena,
        tree,
        proto,
        bindings,
        span[0],
        span[1],
        depth + 1,
        token_count,
    );
    return withFields(arena, inner, fields);
}

/// `inner` with `fields` — the dotted path the use spelled on top of
/// the name — appended to a parameter path.  An answer that is not a
/// parameter path has no field to extend and is returned as it is.
fn withFields(arena: std.mem.Allocator, inner: Placement, fields: []const u8) !Placement {
    return switch (inner) {
        .unknown, .shared, .local, .element => inner,
        .param => |p| .{ .param = .{
            .param = p.param,
            .path = try joinPath(arena, p.path, fields),
        } },
    };
}

/// Does this initializer BUILD an object, or NAME one that already
/// exists?  `.empty`, `.{ … }`, `Type.init(…)`, `&.{ … }` and
/// `undefined` build; an identifier, a field read, a deref or a
/// call on a name this fn never declared as a type name something
/// this fn did not lay out.
///
/// The distinction is syntactic on purpose: a constructor's own
/// declaration says what it returns, but WHICH storage a name it
/// never declared as a type refers to is not this walk's question,
/// and reading it as shared storage would make every constructor call
/// look like a borrow.
fn initializerConstructs(tag: std.zig.Token.Tag) bool {
    return switch (tag) {
        .period, .builtin, .l_brace, .l_bracket, .number_literal, .string_literal => true,
        else => false,
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
    const token_count = try checkedTokenCount(tree.source.len, tree.tokens.len);
    return growBaseOfExprWithTokenCount(arena, tree, proto, bindings, first, last, token_count);
}

fn growBaseOfExprWithTokenCount(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    token_count: TokenIndex,
) !GrowBase {
    const tags = tree.tokens.items(.tag);
    var root_tok = first;
    while (root_tok <= last and (tags[root_tok] == .keyword_try or tags[root_tok] == .ampersand)) {
        root_tok += 1;
    }
    if (root_tok > last or tags[root_tok] != .identifier) {
        return .{ .storage = .unknown };
    }
    const origin = try growOriginOfName(
        arena,
        tree,
        proto,
        bindings,
        tree.tokenSlice(root_tok),
        root_tok,
        0,
        token_count,
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
///
/// `use_token` is where the name is READ, and it is what picks the
/// declaration: the same `nameAtUse` every other walk in this file
/// uses, so an `else` / `catch` payload that happens to share a
/// parameter's spelling is not that parameter.  Asking the parameter
/// table first invented a grow path on the caller's parameter for a
/// value the error path built.
fn growOriginOfName(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    name: []const u8,
    use_token: TokenIndex,
    depth: u8,
    token_count: TokenIndex,
) WalkError!GrowBase {
    if (depth >= max_owner_depth) return .{ .storage = .unknown };
    const binding = switch (nameAtUse(bindings, tree, proto, name, use_token, token_count) orelse
        return paramGrowBase(tree, proto, name)) {
        // A pipe capture is charged: a `for` element is a value copied
        // out of a buffer, an optional's payload names storage this
        // walk has not proved it can grow, and a prong's `|v|` is a
        // copy of the union field its tag picked.
        .clause => return .{ .storage = .unknown },
        .local => |b| b,
    };
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
    if (paramIndex(tree, proto, base_name) == null and
        nameAtUse(bindings, tree, proto, base_name, base_tok, token_count) == null)
    {
        return .{ .unproven = claimFor(tree, binding) };
    }
    return switch (try growOriginOfName(
        arena,
        tree,
        proto,
        bindings,
        base_name,
        base_tok,
        depth + 1,
        token_count,
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

/// The grow answer for a name no local and no pipe clause declares at
/// this position: the parameter it is a parameter of, or `.unknown` for
/// a name this fn never declared at all.
fn paramGrowBase(tree: *const Ast, proto: Ast.full.FnProto, name: []const u8) GrowBase {
    if (paramIndex(tree, proto, name)) |idx| {
        return .{ .storage = .{ .param = .{ .param = idx, .path = "" } } };
    }
    return .{ .storage = .unknown };
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
pub fn claimFor(tree: *const Ast, binding: *const local_bindings.Binding) FreshClaim {
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
    token_count: TokenIndex,
) WalkError!StorageOwner {
    return ownerOfExprWithTokenCount(
        arena,
        tree,
        proto,
        bindings,
        tree.firstToken(node),
        tree.lastToken(node),
        0,
        token_count,
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
    token_count: TokenIndex,
) WalkError!void {
    if (depth >= max_owner_depth) {
        try out.append(arena, .unknown);
        return;
    }
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(callee);
    if (first == tree.lastToken(callee) and tags[first] == .identifier) return;
    var call_buf: [1]Ast.Node.Index = undefined;
    if (tree.fullCall(&call_buf, callee)) |sub| {
        try appendCalleeOperands(arena, tree, proto, bindings, sub.ast.fn_expr, out, depth + 1, token_count);
        for (sub.ast.params) |p| try out.append(arena, try operandOwner(arena, tree, proto, bindings, p, token_count));
        return;
    }
    var params_buf: [2]Ast.Node.Index = undefined;
    if (tree.builtinCallParams(&params_buf, callee)) |params| {
        for (params) |p| try out.append(arena, try operandOwner(arena, tree, proto, bindings, p, token_count));
        return;
    }
    // A grouped or computed callee — `(cb)`, `xs[i].replace` — is
    // rooted as the expression it is, which is what the operand rules
    // make of it: whatever it names, or `.unknown`.
    try out.append(arena, try operandOwner(arena, tree, proto, bindings, callee, token_count));
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
    token_count: TokenIndex,
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
                // Adjacency and the display name use the final token; the
                // canonical call query uses the expression's main token.
                const callee_tok = tree.lastToken(callee);
                if (adjacencyPassReadIt(tags, callee_tok)) continue;
                // A grow-vocabulary method is attributed by the grow
                // pass, from the receiver ITS adjacency rules reach.
                // Recording it again here would charge the same site
                // from a second, weaker reading.
                if (receiver_mod.isArrayListGrowMethodName(tree.tokenSlice(callee_tok))) continue;
                var args: std.ArrayListUnmanaged(StorageOwner) = .empty;
                try appendCalleeOperands(arena, tree, proto, bindings, callee, &args, 0, token_count);
                for (call.ast.params) |p| {
                    try args.append(arena, try operandOwner(arena, tree, proto, bindings, p, token_count));
                }
                try calls.append(arena, .{
                    .callee_token = tree.nodeMainToken(callee),
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
                try appendCalleeOperands(arena, tree, proto, bindings, params[1], &args, 0, token_count);
                var slots_buf: [2]Ast.Node.Index = undefined;
                if (tupleArgumentSlots(tree, &slots_buf, params[2])) |slots| {
                    // The literal IS `@call`'s argument list, so each
                    // of its entries is one argument.  `.{}` hands
                    // over nothing, and leaves the invocation itself
                    // as the only thing it proves.
                    for (slots) |slot| {
                        try args.append(arena, try operandOwner(arena, tree, proto, bindings, slot, token_count));
                    }
                } else {
                    // A tuple named, forwarded or computed elsewhere.
                    // Its entries cannot be read off here, but it was
                    // still handed to something that may reallocate
                    // what it names, so it is charged as the whole
                    // value it is — never as "no arguments".
                    try args.append(arena, try operandOwner(arena, tree, proto, bindings, params[2], token_count));
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
    const token_count = try checkedTokenCount(tree.source.len, tree.tokens.len);
    return argOwnersWithTokenCount(arena, tree, proto, bindings, receiver, start, end, token_count);
}

fn argOwnersWithTokenCount(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    bindings: *const local_bindings.LocalBindings,
    receiver: ?StorageOwner,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    token_count: TokenIndex,
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
                try out.append(arena, try ownerOfExprWithTokenCount(
                    arena,
                    tree,
                    proto,
                    bindings,
                    arg_start,
                    t - 1,
                    0,
                    token_count,
                ));
                arg_start = t + 1;
            },
            else => {},
        }
    }
    try out.append(arena, try ownerOfExprWithTokenCount(
        arena,
        tree,
        proto,
        bindings,
        arg_start,
        end,
        0,
        token_count,
    ));
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
    const token_count = try checkedTokenCount(tree.source.len, tree.tokens.len);
    return inferGrowEffectsWithTokenCount(arena, tree, proto, body, bindings, token_count);
}

fn inferGrowEffectsWithTokenCount(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    bindings: *const local_bindings.LocalBindings,
    token_count: TokenIndex,
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
            switch (try growBaseOfExprWithTokenCount(arena, tree, proto, bindings, receiverStart(tags, t, first), t - 1, token_count)) {
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
            const base = try growBaseOfExprWithTokenCount(
                arena,
                tree,
                proto,
                bindings,
                recv_first,
                t - 2,
                token_count,
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
            .callee_token = if (t > first and tags[t - 1] == .period) t - 1 else t,
            .name = name,
            .kind = kind,
            .qualifier = qualifier,
            .args = try argOwnersWithTokenCount(arena, tree, proto, bindings, receiver, t + 2, call_end - 1, token_count),
        });
    }
    if (needs_ast_pass) {
        try collectIndirectInvocations(arena, tree, proto, bindings, first, last, nested.items, &calls, &unknown, token_count);
    }
    const owned_paths = try paths.toOwnedSlice(arena);
    errdefer arena.free(owned_paths);
    const owned_calls = try calls.toOwnedSlice(arena);
    errdefer arena.free(owned_calls);
    const owned_claims = try claims.toOwnedSlice(arena);
    return .{
        .paths = owned_paths,
        .unknown = unknown,
        .calls = owned_calls,
        .claims = owned_claims,
    };
}

/// True iff a canonical SDK Allocator.create of the containing type can
/// impose an allocator.destroy(self) obligation on its destructor.
/// Spelling locates candidates; the shared allocator-provenance query
/// resolves the allocator and follows aliases/accessor returns. Known
/// arena/buffer backing belongs to that backing owner. The instance's own
/// pointer or slice fields do not decide who must free the instance.
pub fn inferHeapAllocatesSelf(
    cache: *@import("../cache/file_cache.zig").FileCache,
    body: Ast.Node.Index,
    type_name: ?[]const u8,
) @import("../cache/file_cache.zig").SummaryError!bool {
    const freshness = @import("../cache/fresh_storage.zig");
    const tn = type_name orelse return false;
    const tree = cache.tree;
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
        const index = try cache.getCallIndex();
        const node = index.by_callee_token.get(t) orelse continue;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, node) orelse continue;
        if (call.ast.params.len != 1) continue;
        const allocated_type = call.ast.params[0];
        const type_token = tree.lastToken(allocated_type);
        if (tree.tokenTag(type_token) != .identifier) continue;
        const text = tree.tokenSlice(type_token);
        if (!std.mem.eql(u8, text, tn) and !std.mem.eql(u8, text, "Self")) continue;
        const canonical = (try cache.actualCallSummaryAt(freshness.calleeQueryToken(tree, call), cache.cleanup_frame)) orelse continue;
        if (try freshness.sdkCreateMayOwnHeap(cache, canonical, freshness.FreshWalk.root(.{
            .first = tree.firstToken(node),
            .last = tree.lastToken(node),
        }))) return true;
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

test "checked token count rejects counts outside TokenIndex" {
    const max_count: usize = @as(usize, @intCast(std.math.maxInt(TokenIndex)));
    try testing.expectEqual(
        std.math.maxInt(TokenIndex),
        try checkedTokenCount(0, max_count),
    );
    try testing.expectError(error.SourceTooWide, checkedTokenCount(0, max_count + 1));
    try testing.expectError(
        error.SourceTooWide,
        checkedTokenCount(std.math.maxInt(u32), 0),
    );
}

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

test "result dependence proves unused inputs without trusting scalar builtin spelling" {
    const Case = struct { source: [:0]const u8, dependency: ?bool };
    const cases = [_]Case{
        .{ .source = "fn f(ignored: Allocator, n: usize) Packet { _ = ignored; return .{ .bytes = &[_]u8{1}, .level = @intCast(n) }; }", .dependency = false },
        .{ .source = "fn f(allocator: Allocator, n: usize) Packet { return .{ .bytes = allocator.alloc(u8, n), .level = @intCast(n) }; }", .dependency = true },
        .{ .source = "fn f(allocator: Allocator, n: usize) Packet { const alias = allocator; return make(alias, @intCast(n)); }", .dependency = null },
        .{ .source = "fn f(callback: anytype, n: usize) Packet { publish(callback); return .{ .bytes = &[_]u8{1}, .level = @intCast(n) }; }", .dependency = null },
        .{ .source = "fn f(input: Allocator, n: usize) Packet { if (n != 0) { input.observe(); } return .{ .bytes = &[_]u8{1}, .level = @intCast(n) }; }", .dependency = null },
        .{ .source = "fn f(input: ?Allocator, n: usize) Packet { if (input) |value| { publish(value); } return .{ .bytes = &[_]u8{1}, .level = @intCast(n) }; }", .dependency = null },
        .{ .source = "fn f(input: anytype, n: usize) Packet { const Local = struct { const Type = @TypeOf(input); }; _ = Local; return .{ .bytes = &[_]u8{1}, .level = @intCast(n) }; }", .dependency = null },
        .{ .source = "fn f(comptime input: anytype, n: usize) @TypeOf(input) { _ = input; return @intCast(n); }", .dependency = null },
        .{ .source = "fn f(input: usize) *u8 { return @ptrFromInt(input); }", .dependency = true },
        .{ .source = "fn f(input: usize) void { _ = input; }", .dependency = null },
    };
    for (cases) |case| {
        var tree = try parse(case.source);
        defer tree.deinit(testing.allocator);
        var buffer: [1]Ast.Node.Index = undefined;
        const summary = inferFirstFn(&tree, &buffer);
        try testing.expectEqual(case.dependency, summary.returnedParamDependency(0));
        try testing.expect(!summary.result_params_complete);
    }
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

/// What `inferFieldEffects` produced for the first fn of a tree, with
/// the bindings it produced it from.
const FirstFnEffects = struct {
    effects: FieldEffects,
    bindings: local_bindings.LocalBindings,
};

/// Run `inferFieldEffects` over the first fn of `tree` the way
/// `FileCache` does: a real `LocalBindings` built from the same proto
/// and body, and the public entry point itself.  `arena` owns both,
/// so nothing here frees; `proto_buf` must outlive the result because
/// `fnProtoOne` / `Simple` store params into it.
fn inferFirstFnEffects(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto_buf: *[1]Ast.Node.Index,
) !FirstFnEffects {
    const pb = firstFnProtoAndBody(tree, proto_buf);
    const bindings = try local_bindings.build(arena, tree, pb[0], pb[1]);
    return .{
        .effects = try inferFieldEffects(arena, tree, pb[0], &bindings, pb[1]),
        .bindings = bindings,
    };
}

/// `true` iff `paths` names `{param, path}` — the entry a consumer
/// compares a released or written field against.
fn namesPath(paths: []const ParamPath, param: u32, path: []const u8) bool {
    for (paths) |p| {
        if (p.param == param and std.mem.eql(u8, p.path, path)) return true;
    }
    return false;
}

/// Assert `paths` names `{param, path}`, printing what it holds when
/// it does not — a bare `expect` on a two-entry list says nothing
/// about WHICH entry is missing.
fn expectNamesPath(
    label: []const u8,
    paths: []const ParamPath,
    param: u32,
    path: []const u8,
) !void {
    if (namesPath(paths, param, path)) return;
    std.debug.print("{s} has no {{{d}, \"{s}\"}}; it holds", .{ label, param, path });
    for (paths) |p| std.debug.print(" {{{d}, \"{s}\"}}", .{ p.param, p.path });
    std.debug.print("\n", .{});
    return error.TestExpectedEqual;
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

test "inferHeapAllocatesSelf: allocation provenance distinguishes heap and backing owners" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Pool = struct {
        \\    memory: std.heap.ArenaAllocator,
        \\    fn init(child: std.mem.Allocator) Pool {
        \\        return .{ .memory = std.heap.ArenaAllocator.init(child) };
        \\    }
        \\    fn allocator(self: *Pool) std.mem.Allocator {
        \\        return self.memory.allocator();
        \\    }
        \\    fn aliasedAllocator(self: *Pool) std.mem.Allocator {
        \\        const allocator = self.memory.allocator();
        \\        return allocator;
        \\    }
        \\    fn selectedAllocator(self: *Pool, use_alias: bool) std.mem.Allocator {
        \\        if (use_alias) return self.aliasedAllocator();
        \\        return self.memory.allocator();
        \\    }
        \\    fn deinit(self: *Pool) void {
        \\        std.debug.assert(self.memory.reset(.free_all));
        \\        self.* = undefined;
        \\    }
        \\};
        \\const BufferPool = struct {
        \\    memory: std.heap.FixedBufferAllocator,
        \\    fn allocator(self: *BufferPool) std.mem.Allocator {
        \\        return self.memory.allocator();
        \\    }
        \\};
        \\const MixedPool = struct {
        \\    memory: std.heap.ArenaAllocator,
        \\    gpa: std.mem.Allocator,
        \\    fn allocator(self: *MixedPool, use_pool: bool) std.mem.Allocator {
        \\        if (use_pool) return self.memory.allocator();
        \\        return self.gpa;
        \\    }
        \\};
        \\const FakeAllocator = struct {
        \\    fn create(_: *FakeAllocator, comptime T: type) !*T { return error.NotAllocator; }
        \\};
        \\const HeapSource = struct { gpa: std.mem.Allocator };
        \\fn forward(gpa: std.mem.Allocator) std.mem.Allocator { return gpa; }
        \\const Object = struct {
        \\    const Self = @This();
        \\    bytes: []u8,
        \\    fn heap(gpa: std.mem.Allocator) !*Object {
        \\        const object = try gpa.create(Object);
        \\        object.bytes = try gpa.alloc(u8, 8);
        \\        return object;
        \\    }
        \\    fn privateHeap(gpa: std.mem.Allocator) !*Self {
        \\        const allocator = gpa;
        \\        return try allocator.create(Self);
        \\    }
        \\    fn privateForward(gpa: std.mem.Allocator) !*Self {
        \\        return try forward(gpa).create(Self);
        \\    }
        \\    fn heapField(source: *HeapSource) !*Self {
        \\        return try source.gpa.create(Self);
        \\    }
        \\    fn processHeap() !*Self {
        \\        return try std.heap.page_allocator.create(Self);
        \\    }
        \\    fn wrapped(dev: *Pool) !*Object {
        \\        const object = try dev.allocator().create(Object);
        \\        object.bytes = try dev.allocator().alloc(u8, 8);
        \\        return object;
        \\    }
        \\    fn direct(dev: *std.heap.ArenaAllocator) !*Self {
        \\        return try dev.allocator().create(Self);
        \\    }
        \\    fn arenaAlias(dev: *Pool) !*Self {
        \\        const allocator = dev.allocator();
        \\        return try allocator.create(Self);
        \\    }
        \\    fn forwardedArena(dev: *Pool) !*Self {
        \\        const allocator = forward(dev.allocator());
        \\        return try allocator.create(Self);
        \\    }
        \\    fn accessorAlias(dev: *Pool) !*Self {
        \\        return try dev.aliasedAllocator().create(Self);
        \\    }
        \\    fn knownReturns(dev: *Pool, use_alias: bool) !*Self {
        \\        return try dev.selectedAllocator(use_alias).create(Self);
        \\    }
        \\    fn buffered(dev: *std.heap.FixedBufferAllocator) !*Self {
        \\        return try dev.allocator().create(Self);
        \\    }
        \\    fn wrappedBuffer(dev: *BufferPool) !*Self {
        \\        return try dev.allocator().create(Self);
        \\    }
        \\    fn bufferAlias(dev: *BufferPool) !*Self {
        \\        const allocator = dev.allocator();
        \\        return try allocator.create(Self);
        \\    }
        \\    fn forwardedBuffer(dev: *BufferPool) !*Self {
        \\        const allocator = forward(dev.allocator());
        \\        return try allocator.create(Self);
        \\    }
        \\    fn custom(source: *FakeAllocator) !*Self {
        \\        return try source.create(Self);
        \\    }
        \\    fn mixed(dev: *Pool, gpa: std.mem.Allocator, use_pool: bool) !*Self {
        \\        if (use_pool) return try dev.allocator().create(Self);
        \\        return try gpa.create(Self);
        \\    }
        \\    fn mixedWrapped(dev: *MixedPool, use_pool: bool) !*Self {
        \\        return try dev.allocator(use_pool).create(Self);
        \\    }
        \\    fn destroy(self: *Object) void { self.bytes = &.{}; }
        \\};
        \\test "pool lifetime owns its objects" {
        \\    var pool = Pool.init(std.testing.allocator);
        \\    const object = try Object.wrapped(&pool);
        \\    object.destroy();
        \\    pool.deinit();
        \\}
    ;
    const engine = @import("type_engine");
    const FileCache = @import("../cache/file_cache.zig").FileCache;
    var context: engine.TypeContext = undefined;
    try context.init(testing.allocator, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", testing.allocator);
    defer testing.allocator.free(cwd);
    const path = try std.fs.path.join(testing.allocator, &.{ cwd, "zbc-self-allocation-test.zig" });
    defer testing.allocator.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, testing.allocator, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(testing.allocator, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.module_id = resolver.handle.module;
    const model = try cache.fileModel();
    const object = model.findType("Object").?;
    const Case = struct { name: []const u8, owns_self: bool };
    for ([_]Case{
        .{ .name = "heap", .owns_self = true },
        .{ .name = "privateHeap", .owns_self = true },
        .{ .name = "privateForward", .owns_self = true },
        .{ .name = "heapField", .owns_self = true },
        .{ .name = "processHeap", .owns_self = true },
        .{ .name = "wrapped", .owns_self = false },
        .{ .name = "direct", .owns_self = false },
        .{ .name = "arenaAlias", .owns_self = false },
        .{ .name = "forwardedArena", .owns_self = false },
        .{ .name = "accessorAlias", .owns_self = false },
        .{ .name = "knownReturns", .owns_self = false },
        .{ .name = "buffered", .owns_self = false },
        .{ .name = "wrappedBuffer", .owns_self = false },
        .{ .name = "bufferAlias", .owns_self = false },
        .{ .name = "forwardedBuffer", .owns_self = false },
        .{ .name = "custom", .owns_self = false },
        .{ .name = "mixed", .owns_self = true },
        .{ .name = "mixedWrapped", .owns_self = true },
    }) |case| {
        const body = tokens.bodyOf(tree, object.findMethod(case.name).?.fn_decl).?;
        const owns_self = try inferHeapAllocatesSelf(&cache, body, "Object");
        try testing.expectEqual(case.owns_self, owns_self);
        try testing.expect(!try inferHeapAllocatesSelf(&cache, body, null));
    }
    const heap_body = tokens.bodyOf(tree, object.findMethod("heap").?.fn_decl).?;
    try testing.expect(!try inferHeapAllocatesSelf(&cache, heap_body, "Other"));
    var untyped_cache = FileCache.init(testing.allocator, tree);
    defer untyped_cache.deinit();
    try testing.expect(!try inferHeapAllocatesSelf(&untyped_cache, heap_body, "Object"));
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

// ── Scoped capture provenance ────────────────────────────
//
// `inferFieldEffects` is what a call site reads to decide "the callee
// released my slot" from "the callee released something I still
// hold".  These are the entries that question is answered from, read
// through the real producer: a parsed tree, the `LocalBindings` the
// cache builds for it, and `inferFieldEffects` itself.

test "inferFieldEffects: optional capture releases the scrutinee's own storage paths" {
    var tree = try parse(
        \\fn destroy(self: *Cache) void {
        \\    if (self.slot) |image| {
        \\        self.gpa.free(image.bytes);
        \\        self.gpa.destroy(image);
        \\        self.slot = null;
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const got = try inferFirstFnEffects(arena.allocator(), &tree, &buf);
    const eff = got.effects;
    // `image` IS the pointer stored in `self.slot`, so the payload's
    // own bytes and the image both belong to that one field.
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "slot.bytes");
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "slot");
    try expectNamesPath("written_paths", eff.written_paths, 0, "slot");
    try testing.expectEqual(@as(usize, 2), eff.freed_paths.len);
    try testing.expectEqual(@as(usize, 1), eff.written_paths.len);
    // The allocator receiver hands memory back; it never loses any.
    try testing.expect(!namesPath(eff.freed_paths, 0, ""));
    try testing.expect(!namesPath(eff.freed_paths, 0, "gpa"));
}

test "inferFieldEffects: capture of a nested optional field keeps the whole dotted path" {
    var tree = try parse(
        \\fn release(self: *Cache) void {
        \\    if (self.opts.inner) |buf| {
        \\        self.gpa.free(buf);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "opts.inner");
    try testing.expectEqual(@as(usize, 1), eff.freed_paths.len);
}

test "inferFieldEffects: alias of a successful capture releases the captured path" {
    var tree = try parse(
        \\fn release(self: *Cache) void {
        \\    if (self.slot) |image| {
        \\        const alias = image;
        \\        self.gpa.destroy(alias);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "slot");
    try testing.expectEqual(@as(usize, 1), eff.freed_paths.len);
}

test "inferFieldEffects: a store through an alias of a capture writes the captured path" {
    var tree = try parse(
        \\fn blank(self: *Cache) void {
        \\    if (self.slot) |image| {
        \\        const alias = image.*;
        \\        alias.bytes = &[_]u8{};
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    try expectNamesPath("written_paths", eff.written_paths, 0, "slot.bytes");
    try testing.expectEqual(@as(usize, 1), eff.written_paths.len);
}

test "inferFieldEffects: a use outside the capture's branch reads the parameter" {
    var tree = try parse(
        \\fn rearm(self: *Cache, image: *Image, gpa: std.mem.Allocator) void {
        \\    if (self.slot) |held| {
        \\        gpa.destroy(held);
        \\    }
        \\    gpa.destroy(image);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    // The branch release is the captured field; the release after the
    // branch is the caller's own parameter, and the capture's recorded
    // scope — the whole body — is what could have claimed it.
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "slot");
    try expectNamesPath("freed_paths", eff.freed_paths, 1, "");
    try testing.expectEqual(@as(usize, 2), eff.freed_paths.len);
}

test "inferFieldEffects: a use in a block nested inside the capture's branch still names the capture" {
    var tree = try parse(
        \\fn nested(self: *Cache) void {
        \\    if (self.outer) |slot| {
        \\        {
        \\            self.gpa.destroy(slot);
        \\        }
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    // The plain `{}` is inside the branch node, so the payload is
    // still what the name means there.
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "outer");
    try testing.expectEqual(@as(usize, 1), eff.freed_paths.len);
}

test "inferFieldEffects: two sibling branches reusing a capture name resolve to their own scrutinee" {
    var tree = try parse(
        \\fn swap(self: *Cache, gpa: std.mem.Allocator) void {
        \\    if (self.slot) |slot| {
        \\        gpa.destroy(slot);
        \\    }
        \\    if (self.next) |slot| {
        \\        gpa.free(slot.bytes);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "slot");
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "next.bytes");
    try testing.expectEqual(@as(usize, 2), eff.freed_paths.len);
}

test "inferFieldEffects: else, for and catch captures are charged unknown, not the scrutinee" {
    var tree = try parse(
        \\fn variants(self: *Cache, gpa: std.mem.Allocator) void {
        \\    if (self.slot) |image| {
        \\        gpa.destroy(image);
        \\    } else |err| {
        \\        gpa.destroy(err);
        \\    }
        \\    for (self.list) |item| {
        \\        gpa.destroy(item);
        \\    }
        \\    try self.step() catch |err| {
        \\        gpa.destroy(err);
        \\    };
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    // Only the success payload is the scrutinee's own storage.  The
    // `else` payload sits in the error union's field, the `catch`
    // payload is a value the error path built, and the loop capture
    // is one element copied out of the list — none of them may be
    // charged to `self.slot` or `self.list`.
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "slot");
    try testing.expectEqual(@as(usize, 1), eff.freed_paths.len);
}

test "inferFieldEffects: fail-closed on an else payload shadowing a parameter's name" {
    // INTENTIALLY INVALID ZIG: `else |err|` shadows the `err`
    // parameter, which Zig rejects.  The source is here only as
    // robustness input — it proves the walk does not answer an error
    // payload from the parameter table, and it makes NO claim about
    // behaviour on source the compiler accepts.
    var tree = try parse(
        \\fn release(self: *Cache, err: *Failure, gpa: std.mem.Allocator) void {
        \\    if (self.slot) |image| {
        \\        gpa.destroy(image);
        \\    } else |err| {
        \\        gpa.destroy(err);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    // The error branch's `err` is the payload, not the caller's
    // `err` parameter the proto declares under the same name.
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "slot");
    try testing.expect(!namesPath(eff.freed_paths, 1, ""));
    try testing.expectEqual(@as(usize, 1), eff.freed_paths.len);
}

test "inferFieldEffects: a loop-element capture keeps the list borrowed, not released" {
    var tree = try parse(
        \\fn each(self: *Cache, gpa: std.mem.Allocator) void {
        \\    for (self.list) |item| {
        \\        gpa.free(item.bytes);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    try testing.expectEqual(@as(usize, 0), eff.freed_paths.len);
    try testing.expectEqual(@as(usize, 0), eff.written_paths.len);
}

test "inferFieldEffects: unrelated fields keep their own paths and the receiver is never charged" {
    var tree = try parse(
        \\fn drain(self: *Cache) void {
        \\    self.gpa.free(self.buffer);
        \\    self.gpa.destroy(self.owned);
        \\    self.count = 0;
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "buffer");
    try expectNamesPath("freed_paths", eff.freed_paths, 0, "owned");
    try expectNamesPath("written_paths", eff.written_paths, 0, "count");
    try testing.expect(!namesPath(eff.freed_paths, 0, "gpa"));
    try testing.expect(!namesPath(eff.freed_paths, 0, ""));
}

test "inferFieldEffects: a call-free body writes every compound target it spells" {
    var tree = try parse(
        \\fn step(self: *Tally) void {
        \\    self.cursor <<= 1;
        \\    self.cursor >>= 1;
        \\    self.cursor <<|= 1;
        \\    self.depth +%= 1;
        \\    self.depth +|= 1;
        \\    self.depth -%= 1;
        \\    self.depth -|= 1;
        \\    self.depth *%= 1;
        \\    self.depth *|= 1;
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    // The CFG guard consumer reads this list to decide whether a
    // condition pinned before a call survives it.  A body that spells
    // no call passes `calleeBodySpellsEveryStore`, so a target missing
    // from here is a write the consumer never invalidates — the exact
    // `self.cursor >>= 1; self.depth = 0;` stale-edge counterexample.
    try expectNamesPath("written_paths", eff.written_paths, 0, "cursor");
    try expectNamesPath("written_paths", eff.written_paths, 0, "depth");
}

test "inferFieldEffects: `<=` and `>=` are comparisons, so they write nothing" {
    var tree = try parse(
        \\fn inRange(self: *Tally) bool {
        \\    if (self.cursor <= self.depth) return true;
        \\    return self.depth >= self.cursor;
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    // Charging a comparison as a store would invent a write the body
    // never performs and hand the consumer an empty written list where
    // it must keep reading "may do it".
    try testing.expectEqual(@as(usize, 0), eff.written_paths.len);
}

test "inferFieldEffects: an allocator-shaped argument on a static receiver is a handover" {
    var tree = try parse(
        \\fn handOver(pool: *Pool, alloc: std.mem.Allocator) void {
        \\    pool.destroy(alloc);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    // `alloc` is being HANDED to `pool`, not released by it.
    try testing.expectEqual(@as(usize, 0), eff.freed_paths.len);
}

// ── Placement identity ────────────────────────────────────
//
// `Placement.local.token` is what a consumer compares against when it
// asks "is this the same object?", so it must be the declaration the
// USE is written in — not the first of that spelling in the fn.  These
// read the real producer, through the same parse + `LocalBindings` seam.

/// `placementOfExpr` for the name written at `[first, last]` of the
/// first fn in `tree`, the way `FileCache` calls it.
fn firstFnPlacementAt(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto_buf: *[1]Ast.Node.Index,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) !Placement {
    const pb = firstFnProtoAndBody(tree, proto_buf);
    const bindings = try local_bindings.build(arena, tree, pb[0], pb[1]);
    return placementOfExpr(arena, tree, pb[0], &bindings, first, last, 0);
}

/// Token of the `n`th identifier spelled `name` in `tree`, 0-based.
fn nthIdentifier(tree: *const Ast, name: []const u8, n: usize) !?Ast.TokenIndex {
    const token_count = try checkedTokenCount(tree.source.len, tree.tokens.len);
    const tags = tree.tokens.items(.tag);
    var seen: usize = 0;
    var t: Ast.TokenIndex = 0;
    while (t < token_count) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        if (seen == n) return t;
        seen += 1;
    }
    return null;
}

/// Assert `got` is `.local` naming exactly `token`.
fn expectLocalToken(got: Placement, token: Ast.TokenIndex) !void {
    switch (got) {
        .local => |l| {
            if (l.token == token) return;
            std.debug.print("placement is .local of token {d}, not {d}\n", .{ l.token, token });
            return error.TestExpectedEqual;
        },
        else => {
            std.debug.print("placement is not .local\n", .{});
            return error.TestExpectedEqual;
        },
    }
}

test "placementOfExpr: &local names the declaration in scope at the use, not the first of that name" {
    var tree = try parse(
        \\fn record() void {
        \\    {
        \\        const item = .{};
        \\        _ = item;
        \\    }
        \\    const item = .{};
        \\    sink(&item);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    // `item` occurrences: 0 the first declaration, 1 its `_ = item`,
    // 2 the second declaration, 3 the `&item` handed to `sink`.
    const declared = (try nthIdentifier(&tree, "item", 2)).?;
    const use = (try nthIdentifier(&tree, "item", 3)).?;
    const got = try firstFnPlacementAt(arena.allocator(), &tree, &buf, use, use);
    try expectLocalToken(got, declared);
}

test "placementOfExpr: an optional capture is the placement of the field it was read from" {
    var tree = try parse(
        \\fn release(self: *Cache) void {
        \\    if (self.slot) |image| {
        \\        sink(&image);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const use = (try nthIdentifier(&tree, "image", 1)).?;
    const got = try firstFnPlacementAt(arena.allocator(), &tree, &buf, use, use);
    // The payload is held IN `self.slot`, so the address is an address
    // inside the caller's own object — never a disjoint element.
    switch (got) {
        .param => |p| {
            try testing.expectEqual(@as(u32, 0), p.param);
            try testing.expectEqualStrings("slot", p.path);
        },
        else => {
            std.debug.print("capture is not placed on param 0\n", .{});
            return error.TestExpectedEqual;
        },
    }
}

test "placementOfExpr: a for capture stays an element, not the iterable" {
    var tree = try parse(
        \\fn each(self: *Cache) void {
        \\    for (self.list) |item| {
        \\        sink(&item);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const use = (try nthIdentifier(&tree, "item", 1)).?;
    const got = try firstFnPlacementAt(arena.allocator(), &tree, &buf, use, use);
    try testing.expect(got == .element);
}

test "placementOfExpr: an else payload is charged, never given an identity" {
    var tree = try parse(
        \\fn release(self: *Cache, gpa: std.mem.Allocator) void {
        \\    if (self.slot) |image| {
        \\        gpa.destroy(image);
        \\    } else |failure| {
        \\        sink(&failure);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const use = (try nthIdentifier(&tree, "failure", 1)).?;
    const got = try firstFnPlacementAt(arena.allocator(), &tree, &buf, use, use);
    try testing.expect(got == .unknown);
}

// ── Grow receiver identity ────────────────────────────────
//
// The grow pass asks the same "which declaration is this name?" and
// must answer it the same way: an opaque payload that merely shares a
// parameter's spelling is not that parameter, and answering as if it
// were would hand the caller a grow path on storage this fn never
// reached.

/// `inferGrowEffects` over the first fn of `tree`, through the same
/// proto + body + `LocalBindings` the cache uses.
fn firstFnGrowEffects(
    arena: std.mem.Allocator,
    tree: *const Ast,
    proto_buf: *[1]Ast.Node.Index,
) !GrowEffects {
    const pb = firstFnProtoAndBody(tree, proto_buf);
    const bindings = try local_bindings.build(arena, tree, pb[0], pb[1]);
    return inferGrowEffects(arena, tree, pb[0], pb[1], &bindings);
}

fn hasGrowPath(paths: []const GrowPath, param: u32, field: []const u8) bool {
    for (paths) |p| {
        if (p.param == param and std.mem.eql(u8, p.field, field)) return true;
    }
    return false;
}

test "inferGrowEffects: a receiver reached through a parameter still names that path" {
    var tree = try parse(
        \\fn push(self: *Cache) void {
        \\    self.list.append(1);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = try firstFnGrowEffects(arena.allocator(), &tree, &buf);
    try testing.expect(hasGrowPath(eff.paths, 0, "list"));
}

test "inferGrowEffects: a for-element capture is charged, never grown through" {
    var tree = try parse(
        \\fn each(self: *Cache) void {
        \\    for (self.list) |item| {
        \\        item.append(1);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = try firstFnGrowEffects(arena.allocator(), &tree, &buf);
    // The capture is one value copied out of the buffer, so the grow
    // cannot be charged to `self.list` — and this fn named no other
    // parameter for it to land on.
    try testing.expectEqual(@as(usize, 0), eff.paths.len);
    try testing.expect(eff.unknown);
}

test "inferGrowEffects: fail-closed on an else payload sharing a parameter's name" {
    // INTENTIALLY INVALID ZIG: `else |tally|` shadows the `tally`
    // parameter, which Zig rejects.  The source is robustness input
    // only — it proves the grow pass does not answer an error payload
    // from the parameter table, and makes no claim about source the
    // compiler accepts.
    var tree = try parse(
        \\fn step(self: *Cache, tally: *Tally) void {
        \\    if (self.ready()) |ok| {
        \\        _ = ok;
        \\    } else |tally| {
        \\        tally.entries.append(1);
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = try firstFnGrowEffects(arena.allocator(), &tree, &buf);
    // Reading `tally` as the parameter would hand the caller a grow
    // path on storage the error branch never reached.
    try testing.expectEqual(@as(usize, 0), eff.paths.len);
    try testing.expect(eff.unknown);
}

// ── Switch prong payloads ─────────────────────────────────
//
// `switch (u) { .List => |list| … }` binds a COPY of whichever union
// field its tag selected, and `local_bindings` records no prong
// payload at all — a capture table that only knows `for` / `while` /
// `if` / `catch`.  So before the walks learned the prong, a name the
// prong shadows fell straight through to a same-spelled parameter or
// an outer alias, and the call site was told the caller had lost
// storage this body never reached.  These read the real producer:
// parse, the proto + body the cache builds, and the public entry
// points themselves.

/// Two sibling prongs binding the SAME spelling, one braced and one
/// braceless, with a nested statement inside the braced one — every
/// shape a prong's scope can take.  Reusing a spelling across SIBLING
/// prongs is legal Zig, so this source is what the legal cases parse.
const sibling_prong_src =
    \\fn release(self: *Cache, gpa: std.mem.Allocator) void {
    \\    switch (self.u.*) {
    \\        .List => |value| {
    \\            gpa.destroy(&value);
    \\            if (self.ok()) gpa.free(value.bytes);
    \\        },
    \\        .Map => |*value| gpa.destroy(value.inner),
    \\        else => {},
    \\    }
    \\}
;

test "inferFieldEffects: sibling prong payloads release nothing they cannot name" {
    var tree = try parse(sibling_prong_src);
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    // Both prongs bind a copy of a union field, so `gpa.destroy(…)`
    // in one releases no field of any receiver: there is no dotted
    // path to hand back, and inventing one from the scrutinee would
    // be exactly the claim this file cannot make.
    try testing.expectEqual(@as(usize, 0), eff.freed_paths.len);
    try testing.expectEqual(@as(usize, 0), eff.written_paths.len);
}

/// The same shape with each prong's capture shadowing a PARAMETER of
/// that name, which Zig rejects.  Robustness input only — see the
/// note on the test that reads it.
const shadowed_prong_src =
    \\fn release(self: *Cache, gpa: std.mem.Allocator, value: *Payload) void {
    \\    self.flag = true;
    \\    switch (self.u.*) {
    \\        .List => |value| gpa.destroy(value),
    \\        .Map => |*value| gpa.destroy(value.inner),
    \\        else => {},
    \\    }
    \\}
;

test "inferFieldEffects: a prong payload sharing a parameter's name releases nothing" {
    // INTENTIALLY INVALID ZIG: `|value|` and `|*value|` shadow the
    // `value` parameter, which Zig rejects.  The source is robustness
    // input only — it proves the release pass does not answer a prong
    // payload from the parameter table or from the union it was read
    // from, and makes no claim about source the compiler accepts.
    var tree = try parse(shadowed_prong_src);
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = (try inferFirstFnEffects(arena.allocator(), &tree, &buf)).effects;
    // Reading the payload as `{2, ""}` would tell the call site the
    // callee released the caller's own `value`.
    try testing.expectEqual(@as(usize, 0), eff.freed_paths.len);
    try testing.expect(!namesPath(eff.freed_paths, 2, ""));
    try testing.expect(!namesPath(eff.freed_paths, 2, "inner"));
    // A store through the receiver is unaffected, so this pass is not
    // simply empty for a body holding a prong.
    try expectNamesPath("written_paths", eff.written_paths, 0, "flag");
}

test "placementOfExpr: a prong payload is charged, never an element or shared storage" {
    var tree = try parse(sibling_prong_src);
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    // `&value` in the braced prong, then the bare name in the
    // braceless one — both spell the payload, neither is a placement.
    const amp = (try nthIdentifier(&tree, "value", 1)).?;
    const bare = (try nthIdentifier(&tree, "value", 4)).?;
    try testing.expectEqual(TokenTag.ampersand, tree.tokenTag(amp - 1));
    try testing.expect(try firstFnPlacementAt(arena.allocator(), &tree, &buf, amp - 1, amp) == .unknown);
    try testing.expect(try firstFnPlacementAt(arena.allocator(), &tree, &buf, bare, bare) == .unknown);
}

test "nearestBranchClause: sibling prongs keep separate identities and scopes" {
    var tree = try parse(sibling_prong_src);
    defer tree.deinit(testing.allocator);
    var buf: [1]Ast.Node.Index = undefined;
    const proto = firstFnProtoAndBody(&tree, &buf)[0];
    const capture_a = (try nthIdentifier(&tree, "value", 0)).?;
    const use_a = (try nthIdentifier(&tree, "value", 1)).?;
    const use_nested = (try nthIdentifier(&tree, "value", 2)).?;
    const capture_b = (try nthIdentifier(&tree, "value", 3)).?;
    const use_b = (try nthIdentifier(&tree, "value", 4)).?;

    // Each use names ITS OWN prong's capture.  The two `|value|` are
    // two declarations with two scopes — a walk that resolved the
    // spelling once would hand both uses one `name_token` and one
    // body, and a use in either prong would read through the other.
    const a = nearestBranchClause(&tree, proto, "value", use_a, null).?;
    const b = nearestBranchClause(&tree, proto, "value", use_b, null).?;
    try testing.expectEqual(capture_a, a.name_token);
    try testing.expectEqual(capture_b, b.name_token);
    try testing.expect(a.body.contains(use_a));
    try testing.expect(a.body.contains(use_nested));
    try testing.expect(!a.body.contains(use_b));
    try testing.expect(b.body.contains(use_b));
    try testing.expect(!b.body.contains(use_a));

    // The `exact` route `captureBody` takes for a capture the
    // binding table never recorded: both prongs answer for the
    // identifier that is theirs.
    try testing.expectEqual(capture_a, nearestBranchClause(&tree, proto, "value", capture_a, capture_a).?.name_token);
    try testing.expectEqual(capture_b, nearestBranchClause(&tree, proto, "value", capture_b, capture_b).?.name_token);

    // A prong never carries the scrutinee's storage and is never an
    // element: the tag picked the field, so there is nothing to read.
    try testing.expect(!a.body.carries_scrutinee_storage);
    try testing.expect(!b.body.carries_scrutinee_storage);
    try testing.expect(!a.body.is_iterable_element);
    try testing.expect(!b.body.is_iterable_element);
    try testing.expect(a.scrutinee == null);
    try testing.expect(b.scrutinee == null);
}

test "inferGrowEffects: a parameter receiver still names its path beside a charged prong" {
    var tree = try parse(
        \\fn push(self: *Cache, list: *List) void {
        \\    switch (self.u.*) {
        \\        .List => |payload| payload.append(1),
        \\        else => {},
        \\    }
        \\    list.append(1);
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = try firstFnGrowEffects(arena.allocator(), &tree, &buf);
    // The prong's payload grows storage this file cannot root, so it
    // is charged unknown …
    try testing.expect(eff.unknown);
    try testing.expect(!hasGrowPath(eff.paths, 0, ""));
    // … while the receiver that IS a parameter keeps naming its own
    // path, so the pass is not blind beside it.
    try testing.expect(hasGrowPath(eff.paths, 1, ""));
}

test "inferGrowEffects: a prong payload sharing a parameter's name is never grown through" {
    // INTENTIALLY INVALID ZIG: `|list|` shadows the `list` parameter,
    // which Zig rejects.  The source is robustness input only — it
    // proves the grow pass does not answer a prong payload from the
    // parameter table, and makes no claim about source the compiler
    // accepts.
    var tree = try parse(
        \\fn push(self: *Cache, list: *List) void {
        \\    switch (self.u.*) {
        \\        .List => |list| list.append(1),
        \\        else => {},
        \\    }
        \\}
    );
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    const eff = try firstFnGrowEffects(arena.allocator(), &tree, &buf);
    // Reading the payload as the parameter would hand the caller a
    // grow path on storage the prong never reached.
    try testing.expectEqual(@as(usize, 0), eff.paths.len);
    try testing.expect(!hasGrowPath(eff.paths, 1, ""));
    try testing.expect(eff.unknown);
}

/// These fixtures exercise control flow over parsed nodes. Call certificates
/// are explicit inputs; authentication of them is FileCache's separate job.
const CleanupTestCache = struct {
    const Call = struct {
        node: Ast.Node.Index,
        effects: @import("../cache/file_cache.zig").FileCache.NormalCleanupCall,
    };

    tree: *const Ast,
    calls: []const Call,
    retained_at: ?Ast.Node.Index = null,
    fresh_nodes: []const Ast.Node.Index = &.{},
    allocator_path: ?ParamPath = .{ .param = 0, .path = "allocator" },
    resource_error: ?CleanupError = null,
    queries: u32 = 0,
    depth: u32 = 0,
    visited: u32 = 0,
    storage_work: usize = 0,

    fn beginNormalCleanup(self: *@This()) void {
        self.queries += 1;
    }

    fn endNormalCleanup(self: *@This()) void {
        std.debug.assert(self.queries > 0);
        self.queries -= 1;
    }

    fn enterNormalCleanup(self: *@This(), node: Ast.Node.Index) CleanupError!void {
        std.debug.assert(@intFromEnum(node) < self.tree.nodes.len);
        if (self.depth == 64) return budget_mod.fail(.{ .limit = .normal_cleanup_depth, .limit_value = 64, .reached = 64 });
        self.depth += 1;
    }

    fn leaveNormalCleanup(self: *@This()) void {
        std.debug.assert(self.depth > 0);
        self.depth -= 1;
    }

    fn chargeNormalCleanup(self: *@This(), node: Ast.Node.Index) CleanupError!void {
        std.debug.assert(@intFromEnum(node) < self.tree.nodes.len);
        if (self.visited == 50_000) return budget_mod.fail(.{ .limit = .normal_cleanup_nodes, .limit_value = 50_000, .reached = 50_000 });
        self.visited += 1;
    }

    fn normalCleanupStorageWork(self: *@This(), node: Ast.Node.Index, units: usize) CleanupError!void {
        std.debug.assert(@intFromEnum(node) < self.tree.nodes.len);
        if (units > 50_000 - self.visited) {
            return budget_mod.fail(.{ .limit = .normal_cleanup_nodes, .limit_value = 50_000, .reached = 50_000 });
        }
        self.visited += @intCast(units);
        self.storage_work += units;
    }

    fn normalCleanupCall(
        self: *@This(),
        _: std.mem.Allocator,
        _: Ast.full.FnProto,
        _: *const local_bindings.LocalBindings,
        node: Ast.Node.Index,
    ) CleanupError!@import("../cache/file_cache.zig").FileCache.NormalCleanupCall {
        if (self.resource_error) |err| return err;
        for (self.calls) |call| if (call.node == node) return call.effects;
        return .{};
    }

    fn normalCleanupReturnKind(_: *@This(), _: Ast.Node.Index) CleanupError!?bool {
        return false;
    }

    fn normalCleanupCondition(_: *@This(), _: Ast.Node.Index) CleanupError!?bool {
        return null;
    }

    fn normalCleanupFresh(self: *@This(), node: Ast.Node.Index) CleanupError!bool {
        for (self.fresh_nodes) |fresh| if (fresh == node) return true;
        return false;
    }

    fn normalCleanupAllocator(self: *@This(), _: Ast.Node.Index) CleanupError!?ParamPath {
        return self.allocator_path;
    }

    fn retainedStorageAt(
        self: *@This(),
        _: std.mem.Allocator,
        _: Ast.full.FnProto,
        _: *const local_bindings.LocalBindings,
        node: Ast.Node.Index,
    ) CleanupError![]const u32 {
        if (self.retained_at == node) return &.{7};
        return &.{};
    }
};

fn cleanupTestCall(tree: *const Ast, name: []const u8) ?Ast.Node.Index {
    for (1..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        const token = tree.nodeMainToken(call.ast.fn_expr);
        if (std.mem.eql(u8, tree.tokenSlice(token), name)) return node;
    }
    return null;
}

test "cleanup structural exits distinguish normal error defer catch and try" {
    const Case = struct {
        source: [:0]const u8,
        normal_definite: usize,
        normal_may: usize,
        error_definite: usize,
        error_may: usize,
        complete: bool = true,
        error_complete: bool = false,
    };
    const cases = [_]Case{
        .{
            .source = "fn f(flag: bool) void { if (flag) release(); }",
            .normal_definite = 0,
            .normal_may = 1,
            .error_definite = 0,
            .error_may = 0,
        },
        .{
            .source = "fn f() void { if (true) release() else onError(); }",
            .normal_definite = 1,
            .normal_may = 1,
            .error_definite = 0,
            .error_may = 0,
        },
        .{
            .source = "fn f() void { if (false) release(); }",
            .normal_definite = 0,
            .normal_may = 0,
            .error_definite = 0,
            .error_may = 0,
        },
        .{
            .source = "fn f(flag: bool) void { if (flag) { release(); return; } }",
            .normal_definite = 0,
            .normal_may = 1,
            .error_definite = 0,
            .error_may = 0,
        },
        .{
            .source = "fn f() !void { release(); return error.Fail; }",
            .normal_definite = 0,
            .normal_may = 0,
            .error_definite = 1,
            .error_may = 1,
            .complete = false,
            .error_complete = true,
        },
        .{
            .source = "fn f(flag: bool) !void { defer release(); " ++
                "errdefer onError(); if (flag) return error.Fail; }",
            .normal_definite = 1,
            .normal_may = 1,
            .error_definite = 2,
            .error_may = 2,
            .error_complete = true,
        },
        .{
            .source = "fn f() !void { try attempt(); defer release(); }",
            .normal_definite = 1,
            .normal_may = 1,
            .error_definite = 1,
            .error_may = 1,
            .error_complete = true,
        },
        .{
            .source = "fn f() void { attempt() catch release(); }",
            .normal_definite = 0,
            .normal_may = 2,
            .error_definite = 0,
            .error_may = 0,
        },
        .{
            .source = "fn f() !void { release(try fail()); }",
            .normal_definite = 0,
            .normal_may = 0,
            .error_definite = 1,
            .error_may = 1,
            .complete = false,
            .error_complete = true,
        },
        .{
            .source = "fn f(flag: bool) void { while (flag) release(); }",
            .normal_definite = 0,
            .normal_may = 1,
            .error_definite = 0,
            .error_may = 0,
            .complete = false,
        },
        .{
            .source = "fn f(flag: bool) !void { " ++
                "while (flag) { release(); return error.Fail; } }",
            .normal_definite = 0,
            .normal_may = 0,
            .error_definite = 0,
            .error_may = 1,
            .complete = false,
        },
        .{
            .source = "fn f() noreturn { unreachable; }",
            .normal_definite = 0,
            .normal_may = 0,
            .error_definite = 0,
            .error_may = 0,
            .complete = false,
        },
    };
    for (cases) |case| {
        var tree = try parse(case.source);
        defer tree.deinit(testing.allocator);
        var arena = std.heap.ArenaAllocator.init(testing.allocator);
        defer arena.deinit();
        const allocator = arena.allocator();
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto, const body = firstFnProtoAndBody(&tree, &proto_buffer);
        const bindings = try local_bindings.build(allocator, &tree, proto, body);
        var calls: std.ArrayListUnmanaged(CleanupTestCache.Call) = .empty;
        defer calls.deinit(allocator);
        const names = [_][]const u8{ "release", "onError", "attempt", "fail" };
        for (names, 0..) |name, index| {
            const node = cleanupTestCall(&tree, name) orelse continue;
            const paths = try allocator.alloc(ParamPath, 1);
            paths[0] = .{ .param = @intCast(index), .path = "" };
            try calls.append(allocator, .{ .node = node, .effects = switch (index) {
                0, 1 => .{
                    .definite_paths = paths,
                    .may_paths = paths,
                    .complete = true,
                    .error_complete = true,
                    .can_normal = true,
                    .can_error = false,
                    .returns_error = false,
                },
                2 => .{
                    .complete = true,
                    .error_complete = true,
                    .error_definite_paths = paths,
                    .error_may_paths = paths,
                    .can_normal = true,
                    .can_error = true,
                    .returns_error = null,
                },
                3 => .{
                    .complete = true,
                    .error_complete = true,
                    .error_definite_paths = paths,
                    .error_may_paths = paths,
                    .can_normal = false,
                    .can_error = true,
                    .returns_error = true,
                },
                else => unreachable,
            } });
        }
        var cache = CleanupTestCache{ .tree = &tree, .calls = calls.items };
        const effects = try inferNormalSuccessCleanup(
            &cache,
            allocator,
            proto,
            &bindings,
            body,
        );
        try testing.expectEqual(case.normal_definite, effects.definite_freed_paths.len);
        try testing.expectEqual(case.normal_may, effects.may_freed_paths.len);
        try testing.expectEqual(case.error_definite, effects.error_definite_freed_paths.len);
        try testing.expectEqual(case.error_may, effects.error_may_freed_paths.len);
        try testing.expectEqual(case.complete, effects.complete);
        try testing.expectEqual(case.error_complete, effects.error_complete);
        try testing.expectEqual(@as(u32, 0), cache.depth);
        try testing.expectEqual(@as(u32, 0), cache.queries);
        try testing.expect(cache.visited > 0);
    }
}

test "cleanup resource errors propagate and unwind shared work hooks" {
    var tree = try parse("fn f() void { release(); }");
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &proto_buffer);
    const bindings = try local_bindings.build(arena.allocator(), &tree, proto, body);
    const failures = [_]CleanupError{
        error.OutOfMemory,   error.SourceTooWide,  error.AnalysisBudgetExceeded,
        error.InvalidSyntax, error.SourceExcluded, error.Canceled,
    };
    for (failures) |failure| {
        var cache = CleanupTestCache{
            .tree = &tree,
            .calls = &.{},
            .resource_error = failure,
        };
        try testing.expectError(failure, inferNormalSuccessCleanup(
            &cache,
            arena.allocator(),
            proto,
            &bindings,
            body,
        ));
        try testing.expectEqual(@as(u32, 0), cache.depth);
        try testing.expectEqual(@as(u32, 0), cache.queries);
    }
}

test "cleanup sibling defers do not consume nesting depth" {
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(testing.allocator);
    try source.appendSlice(testing.allocator, "fn f() void {");
    for (0..96) |_| try source.appendSlice(testing.allocator, "defer release();");
    try source.appendSlice(testing.allocator, "}");
    const text = try testing.allocator.dupeZ(u8, source.items);
    defer testing.allocator.free(text);
    var tree = try parse(text);
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &proto_buffer);
    const bindings = try local_bindings.build(arena.allocator(), &tree, proto, body);
    var cache = CleanupTestCache{ .tree = &tree, .calls = &.{} };
    _ = try inferNormalSuccessCleanup(&cache, arena.allocator(), proto, &bindings, body);
    try testing.expectEqual(@as(u32, 0), cache.depth);
    try testing.expectEqual(@as(u32, 0), cache.queries);
}

test "cleanup genuine nested syntax still exhausts the depth budget" {
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(testing.allocator);
    try source.appendSlice(testing.allocator, "fn f() void {");
    for (0..80) |_| try source.appendSlice(testing.allocator, "{");
    try source.appendSlice(testing.allocator, "release();");
    for (0..80) |_| try source.appendSlice(testing.allocator, "}");
    try source.appendSlice(testing.allocator, "}");
    const text = try testing.allocator.dupeZ(u8, source.items);
    defer testing.allocator.free(text);
    var tree = try parse(text);
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &proto_buffer);
    const bindings = try local_bindings.build(arena.allocator(), &tree, proto, body);
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    var cache = CleanupTestCache{ .tree = &tree, .calls = &.{} };
    try testing.expectError(error.AnalysisBudgetExceeded, inferNormalSuccessCleanup(
        &cache,
        arena.allocator(),
        proto,
        &bindings,
        body,
    ));
    // The mock reports the bound the way the real cache does, so the CLI can
    // name it instead of saying the limit is unknown.
    const stop = budget_mod.take() orelse return error.TestUnexpectedResult;
    try testing.expectEqual(budget_mod.Limit.normal_cleanup_depth, stop.limit);
    try testing.expectEqual(@as(u32, 64), stop.limit_value);
    try testing.expectEqual(@as(u32, 0), cache.depth);
    try testing.expectEqual(@as(u32, 0), cache.queries);
}

test "cleanup retention intersects explicit return and bare fallthrough" {
    var tree = try parse("fn f(flag: bool) void { if (flag) return; }");
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &proto_buffer);
    const bindings = try local_bindings.build(arena.allocator(), &tree, proto, body);
    var retained_at: ?Ast.Node.Index = null;
    for (1..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeTag(node) == .@"return") retained_at = node;
    }
    try testing.expect(retained_at != null);
    var cache = CleanupTestCache{
        .tree = &tree,
        .calls = &.{},
        .retained_at = retained_at,
    };
    const effects = try inferNormalSuccessCleanup(
        &cache,
        arena.allocator(),
        proto,
        &bindings,
        body,
    );
    try testing.expect(effects.complete);
    try testing.expectEqual(@as(usize, 0), effects.retained_owned_params.len);
}

// Path and field certificates have distinct keys, including the field method.
test "cleanup field joins retain MAY without mixing path certificates" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var state = CleanupState{ .present = true };
    const fields = [_]FieldFree{
        .{ .param = 0, .field = "slot", .method = "close" },
        .{ .param = 0, .field = "slot", .method = "deinit" },
    };
    try state.addEffects(arena.allocator(), &.{}, &fields, &.{}, &fields, true);
    try state.merge(arena.allocator(), .{ .present = true });
    try testing.expectEqual(@as(usize, 0), state.definite_fields.len);
    try testing.expectEqual(@as(usize, 2), state.may_fields.len);
    try testing.expectEqual(@as(usize, 0), state.may_paths.len);
}

test "cleanup unknown call cannot certify empty purity" {
    var tree = try parse("fn f() void { unknownCall(); }");
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &buffer);
    const bindings = try local_bindings.build(arena.allocator(), &tree, proto, body);
    var cache = CleanupTestCache{ .tree = &tree, .calls = &.{} };
    const effects = try inferNormalSuccessCleanup(&cache, arena.allocator(), proto, &bindings, body);
    try testing.expect(!effects.complete);
    try testing.expect(!effects.error_complete);
    try testing.expectEqual(@as(usize, 0), effects.definite_freed_paths.len);
    try testing.expectEqual(@as(usize, 0), effects.retained_owned_params.len);
}

test "cleanup rejects invalid syntax instead of publishing unknown purity" {
    var tree = try Ast.parse(testing.allocator, "fn f() void { release(); } fn broken(", .zig);
    defer tree.deinit(testing.allocator);
    try testing.expect(tree.errors.len != 0);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &buffer);
    const bindings = try local_bindings.build(arena.allocator(), &tree, proto, body);
    var cache = CleanupTestCache{ .tree = &tree, .calls = &.{} };
    try testing.expectError(error.InvalidSyntax, inferNormalSuccessCleanup(
        &cache,
        arena.allocator(),
        proto,
        &bindings,
        body,
    ));
    try testing.expectEqual(@as(u32, 0), cache.queries);
    try testing.expectEqual(@as(u32, 0), cache.depth);
}

test "cleanup storage outcomes preserve replacement snapshots and empty exits" {
    const Case = struct {
        source: [:0]const u8,
        kinds: []const @FieldType(StorageOperation, "kind"),
        empty_exit: bool = false,
        error_empty: bool = false,
        complete: bool = true,
        released_store: bool = false,
        legacy_may: ?usize = null,
        allocator_known: bool = true,
    };
    const cases = [_]Case{
        .{
            .source = "fn f(self: *Owner, flag: bool) void { if (flag and self.inner.bytes.len != 0) return; const old = self.inner.bytes; const next = fresh(); self.inner.bytes = next; release(old); }",
            .kinds = &.{ .replace, .release_entry },
            .empty_exit = true,
        },
        .{
            .source = "fn f(self: *Owner) void { const next = fresh(); self.inner.bytes = next; const current = self.inner.bytes; release(current); }",
            .kinds = &.{ .replace, .release_current },
        },
        .{
            .source = "fn f(self: *Owner) !void { const old = self.inner.bytes; const next = try fresh(); self.inner.bytes = next; release(old); }",
            .kinds = &.{ .replace, .release_entry },
            .error_empty = true,
        },
        .{
            .source = "fn f(self: *Owner, other: []u8) void { self.inner.bytes = other; release(self.inner.bytes); }",
            .kinds = &.{},
            .complete = false,
        },
        .{
            .source = "fn f(self: *Owner, size: usize) void { const old = self.inner.bytes; const next = fresh(); self.inner.bytes = next; self.capacity = size; release(old); }",
            .kinds = &.{ .replace, .release_entry },
        },
        .{
            .source = "fn f(self: *Owner) void { const next = fresh(); release(next); self.inner.bytes = next; }",
            .kinds = &.{},
            .complete = false,
            .released_store = true,
        },
        .{
            .source = "fn f(self: *Owner) void { const old = self.inner.bytes; release(old); self.inner.bytes = old; }",
            .kinds = &.{},
            .complete = false,
            .released_store = true,
        },
        .{
            .source = "fn f(self: *Owner) void { const next = fresh(); self.inner.bytes = next; release(next); release(next); }",
            .kinds = &.{ .replace, .release_current, .release_current },
        },
        .{
            .source = "fn f(self: *Owner) void { const old = self.*; const next = fresh(); self.inner.bytes = next; release(old.inner.bytes); }",
            .kinds = &.{},
            .complete = false,
            .legacy_may = 1,
        },
        .{
            .source = "fn f(self: *Owner) void { const old = self.inner.bytes; const next = fresh(); self.inner.bytes = next; release(old); opaqueValue(); }",
            .kinds = &.{},
            .complete = false,
            .legacy_may = 1,
        },
        .{
            .source = "fn f(self: *Owner) void { const old = self.inner.bytes; const next = fresh(); self.inner.bytes = next; release(old); }",
            .kinds = &.{ .replace, .release_entry },
            .legacy_may = 0,
        },
        .{
            .source = "fn f(self: *Owner) void { const old = self.inner.bytes; const next = fresh(); self.inner.bytes = next; release(old); }",
            .kinds = &.{},
            .complete = false,
            .legacy_may = 1,
            .allocator_known = false,
        },
    };
    for (cases) |case| {
        var tree = try parse(case.source);
        defer tree.deinit(testing.allocator);
        var arena = std.heap.ArenaAllocator.init(testing.allocator);
        defer arena.deinit();
        const allocator = arena.allocator();
        var buffer: [1]Ast.Node.Index = undefined;
        const proto, const body = firstFnProtoAndBody(&tree, &buffer);
        const bindings = try local_bindings.build(allocator, &tree, proto, body);
        var calls: std.ArrayListUnmanaged(CleanupTestCache.Call) = .empty;
        for (1..tree.nodes.len) |index| {
            const candidate: Ast.Node.Index = @enumFromInt(index);
            var call_buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buffer, candidate) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(call.ast.fn_expr)), "release")) continue;
            try calls.append(allocator, .{ .node = candidate, .effects = .{
                .complete = true,
                .can_normal = true,
                .can_error = false,
                .returns_error = false,
                .storage_complete = true,
                .release_argument = call.ast.params[0],
            } });
        }
        if (cleanupTestCall(&tree, "fresh")) |fresh| {
            try calls.append(allocator, .{ .node = fresh, .effects = .{
                .complete = true,
                .error_complete = true,
                .can_normal = true,
                .can_error = case.error_empty,
                .returns_error = if (case.error_empty) null else false,
                .storage_complete = true,
                .error_storage_complete = true,
            } });
        }
        var fresh_nodes: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        const fresh_call = cleanupTestCall(&tree, "fresh");
        for (1..tree.nodes.len) |index| {
            const candidate: Ast.Node.Index = @enumFromInt(index);
            const tag = tree.nodeTag(candidate);
            if (tag == .identifier and std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(candidate)), "next"))
                try fresh_nodes.append(allocator, candidate);
            if (tag == .@"try") try fresh_nodes.append(allocator, candidate);
            if (fresh_call) |fresh| {
                if (candidate == fresh) try fresh_nodes.append(allocator, candidate);
            }
        }
        var cache = CleanupTestCache{
            .tree = &tree,
            .calls = calls.items,
            .fresh_nodes = fresh_nodes.items,
            .allocator_path = if (case.allocator_known) .{ .param = 0, .path = "allocator" } else null,
        };
        const effects = try inferNormalSuccessCleanup(&cache, allocator, proto, &bindings, body);
        try testing.expectEqual(case.complete, effects.storage_effects_complete);
        if (case.legacy_may) |count| try testing.expectEqual(count, effects.may_freed_paths.len);
        if (case.released_store) try testing.expect(namesPath(effects.may_freed_paths, 0, "inner.bytes"));
        if (!case.complete) continue;
        try testing.expectEqual(@as(usize, if (case.empty_exit) 2 else 1), effects.storage_outcomes.len);
        var found = false;
        for (effects.storage_outcomes) |outcome| {
            if (outcome.operations.len == 0) continue;
            found = true;
            try testing.expectEqual(case.kinds.len, outcome.operations.len);
            for (outcome.operations, case.kinds) |operation, kind| {
                try testing.expectEqual(kind, operation.kind);
                try testing.expectEqual(@as(u32, 0), operation.path.param);
                try testing.expectEqualStrings("inner.bytes", operation.path.path);
                if (operation.kind == .replace) {
                    try testing.expectEqual(@as(u32, 0), operation.allocator.?.param);
                    try testing.expectEqualStrings("allocator", operation.allocator.?.path);
                }
            }
        }
        try testing.expect(found);
        if (case.error_empty) {
            try testing.expect(effects.error_storage_effects_complete);
            try testing.expectEqual(@as(usize, 1), effects.error_storage_outcomes.len);
            try testing.expectEqual(@as(usize, 0), effects.error_storage_outcomes[0].operations.len);
        }
    }
}

test "cleanup storage child entry release composes with active replacement" {
    var tree = try parse("fn f(self: *Owner) void { self.inner.bytes = fresh(); child(); }");
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &buffer);
    const bindings = try local_bindings.build(allocator, &tree, proto, body);
    const operations = [_]StorageOperation{.{ .path = .{ .param = 0, .path = "inner.bytes" }, .kind = .release_entry }};
    const outcomes = [_]StorageOutcome{.{ .operations = &operations }};
    const calls = [_]CleanupTestCache.Call{
        .{ .node = cleanupTestCall(&tree, "fresh").?, .effects = .{
            .complete = true,
            .can_normal = true,
            .can_error = false,
            .returns_error = false,
            .storage_complete = true,
        } },
        .{ .node = cleanupTestCall(&tree, "child").?, .effects = .{
            .complete = true,
            .can_normal = true,
            .can_error = false,
            .returns_error = false,
            .storage_complete = true,
            .storage_outcomes = &outcomes,
        } },
    };
    const fresh_nodes = [_]Ast.Node.Index{cleanupTestCall(&tree, "fresh").?};
    var cache = CleanupTestCache{ .tree = &tree, .calls = &calls, .fresh_nodes = &fresh_nodes };
    const effects = try inferNormalSuccessCleanup(&cache, allocator, proto, &bindings, body);
    try testing.expect(effects.storage_effects_complete);
    try testing.expectEqual(@as(usize, 1), effects.storage_outcomes.len);
    try testing.expectEqual(@as(usize, 2), effects.storage_outcomes[0].operations.len);
    try testing.expectEqual(.replace, effects.storage_outcomes[0].operations[0].kind);
    try testing.expectEqual(.release_current, effects.storage_outcomes[0].operations[1].kind);
}

test "cleanup errdefer of unpublished fresh local has empty receiver outcome" {
    var tree = try parse("fn f(self: *Owner) !void { const next = fresh(); errdefer release(next); return error.Fail; }");
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &buffer);
    const bindings = try local_bindings.build(allocator, &tree, proto, body);
    const fresh = cleanupTestCall(&tree, "fresh").?;
    const release = cleanupTestCall(&tree, "release").?;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const calls = [_]CleanupTestCache.Call{
        .{ .node = fresh, .effects = .{
            .complete = true,
            .storage_complete = true,
            .can_normal = true,
            .can_error = false,
            .returns_error = false,
        } },
        .{ .node = release, .effects = .{
            .complete = true,
            .storage_complete = true,
            .can_normal = true,
            .can_error = false,
            .returns_error = false,
            .release_argument = tree.fullCall(&call_buffer, release).?.ast.params[0],
        } },
    };
    const fresh_nodes = [_]Ast.Node.Index{fresh};
    var cache = CleanupTestCache{ .tree = &tree, .calls = &calls, .fresh_nodes = &fresh_nodes };
    const effects = try inferNormalSuccessCleanup(&cache, allocator, proto, &bindings, body);
    try testing.expect(!effects.storage_effects_complete);
    try testing.expect(effects.error_storage_effects_complete);
    try testing.expectEqual(@as(usize, 1), effects.error_storage_outcomes.len);
    try testing.expectEqual(@as(usize, 0), effects.error_storage_outcomes[0].operations.len);
    try testing.expectEqual(@as(usize, 0), effects.error_may_freed_paths.len);
}

test "cleanup correlated child products consume the existing node allowance" {
    var tree = try parse("fn f() void { child(); child(); child(); }");
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &buffer);
    const bindings = try local_bindings.build(allocator, &tree, proto, body);
    const outcomes = [_]StorageOutcome{.{}} ** 8;
    var calls: std.ArrayListUnmanaged(CleanupTestCache.Call) = .empty;
    for (1..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var call_buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&call_buffer, node) == null) continue;
        try calls.append(allocator, .{ .node = node, .effects = .{
            .complete = true,
            .storage_complete = true,
            .storage_outcomes = &outcomes,
            .can_normal = true,
            .can_error = false,
            .returns_error = false,
        } });
    }
    _ = budget_mod.take();
    defer _ = budget_mod.take();
    var cache = CleanupTestCache{ .tree = &tree, .calls = calls.items, .visited = 49_950 };
    try testing.expectError(error.AnalysisBudgetExceeded, inferNormalSuccessCleanup(
        &cache,
        allocator,
        proto,
        &bindings,
        body,
    ));
    const stop = budget_mod.take() orelse return error.TestUnexpectedResult;
    try testing.expectEqual(budget_mod.Limit.normal_cleanup_nodes, stop.limit);
    try testing.expectEqual(@as(u32, 50_000), stop.limit_value);
    try testing.expect(cache.storage_work > 0);
    try testing.expect(cache.visited < 50_000);
    try testing.expectEqual(@as(u32, 0), cache.depth);
    try testing.expectEqual(@as(u32, 0), cache.queries);
}

test "cleanup current release guarantees intersect correlated local snapshots" {
    var tree = try parse("fn f(self: *Owner, flag: bool) void { var old: []u8 = undefined; if (flag) old = self.a else old = self.b; release(old); }");
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &buffer);
    const bindings = try local_bindings.build(allocator, &tree, proto, body);
    const release = cleanupTestCall(&tree, "release").?;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const calls = [_]CleanupTestCache.Call{.{ .node = release, .effects = .{
        .complete = true,
        .storage_complete = true,
        .can_normal = true,
        .can_error = false,
        .returns_error = false,
        .release_argument = tree.fullCall(&call_buffer, release).?.ast.params[0],
    } }};
    var cache = CleanupTestCache{ .tree = &tree, .calls = &calls };
    const effects = try inferNormalSuccessCleanup(&cache, allocator, proto, &bindings, body);
    try testing.expect(effects.complete);
    try testing.expect(effects.storage_effects_complete);
    try testing.expectEqual(@as(usize, 0), effects.definite_freed_paths.len);
    try testing.expectEqual(@as(usize, 2), effects.may_freed_paths.len);
    try testing.expect(namesPath(effects.may_freed_paths, 0, "a"));
    try testing.expect(namesPath(effects.may_freed_paths, 0, "b"));
    try testing.expectEqual(@as(usize, 2), effects.storage_outcomes.len);
}

test "cleanup child replacement without allocator provenance removes exact replay" {
    var tree = try parse("fn f(self: *Owner) void { child(); }");
    defer tree.deinit(testing.allocator);
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var buffer: [1]Ast.Node.Index = undefined;
    const proto, const body = firstFnProtoAndBody(&tree, &buffer);
    const bindings = try local_bindings.build(allocator, &tree, proto, body);
    const operations = [_]StorageOperation{.{ .path = .{ .param = 0, .path = "inner.bytes" }, .kind = .replace }};
    const outcomes = [_]StorageOutcome{.{ .operations = &operations }};
    const calls = [_]CleanupTestCache.Call{.{ .node = cleanupTestCall(&tree, "child").?, .effects = .{
        .complete = true,
        .storage_complete = true,
        .storage_outcomes = &outcomes,
        .can_normal = true,
        .can_error = false,
        .returns_error = false,
    } }};
    var cache = CleanupTestCache{ .tree = &tree, .calls = &calls };
    const effects = try inferNormalSuccessCleanup(&cache, allocator, proto, &bindings, body);
    try testing.expect(!effects.storage_effects_complete);
}

test "cleanup child replacement retains the intermediate payload identity" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const path: ParamPath = .{ .param = 0, .path = "bytes" };
    const replacement: StorageOperation = .{
        .path = path,
        .kind = .replace,
        .allocator = .{ .param = 0, .path = "allocator" },
    };
    var state: CleanupState = .{ .present = true };
    const first = [_]StorageOutcome{.{ .operations = &.{replacement} }};
    try state.composeStorage(allocator, &first, true);
    const child = [_]StorageOutcome{.{ .operations = &.{
        replacement,
        .{ .path = path, .kind = .release_entry },
    } }};
    try state.composeStorage(allocator, &child, true);
    try testing.expect(state.storage_complete);
    const trace = state.alternatives[0];
    try testing.expect(try trace.released(path, 1));
    try testing.expect(!try trace.released(path, 2));
}
