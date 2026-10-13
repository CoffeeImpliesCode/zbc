//! Layer 2 CFG types and Zig-AST → CFG lowering.
//!
//! v1 scope: extract a flow graph from a single Zig function over the
//! subset of statement shapes that affect our abstract state.  Most
//! Zig syntax doesn't change lifetime/identity; we collapse it into
//! `.plain_expr` and only emit dedicated statement nodes for the ops
//! the analyzer transfers over.
//!
//! What we DO model:
//!   - `var/const NAME = INIT;` (local binding)
//!   - `LHS = RHS;` (assignment)
//!   - fixed-array selected reads, sparse stores, and bounded counter prefixes
//!     (initialization coverage is independent of memory lifetime)
//!   - call expressions (especially annotated-callee returns)
//!   - `arena.deinit()` (arena death)
//!   - `thread.join()` (thread join)
//!   - `return EXPR;` (function exit)
//!   - `if/else`, `while`, `for`, `switch` branching (real CFG edges)
//!   - `defer` / `errdefer` (replayed at function-exit / return sites)
//!   - `try` / `catch` (error-exit sinks + catch-arm forks; errdefers
//!     replayed on error returns, including `return error.X` and
//!     `return <error-capture>` from `catch |err|` / `else |err|`)
//!
//! What we DON'T model (yet):
//!   - error-UNION returns (`return foo()` yielding `!T`): the success
//!     vs error path isn't forked, so errdefers are not replayed there
//!     (sound: a residual false-negative, never a false-positive)
//!   - generics / comptime
//!   - for-loop iteration variable origin (treated as .plain)
//!   - switch-case pattern bindings (treated as .plain)
//!
//! Errors during lowering are surfaced as `Stmt{.lowering_gap}` nodes
//! rather than aborts — keeps the analyzer running on the rest of the
//! function even when one statement uses an unsupported construct.

const std = @import("std");
const Ast = std.zig.Ast;
const abstract_state = @import("abstract_state.zig");
const config_mod = @import("../config.zig");
const file_cache = @import("../cache/file_cache.zig");
const fn_summary = @import("../model/fn_summary.zig");
const tokens = @import("../ast/tokens.zig");
const receiver_mod = @import("../model/method_names.zig");
const model_mod = @import("../model/file_model.zig");
const zls_resolver_mod = @import("../type_resolver.zig");

pub const Config = config_mod.Config;

pub const BlockId = abstract_state.BlockId;
pub const LocalId = abstract_state.LocalId;
/// Reserved diagnostic path: an optional has no source-level fields.
pub const diagnostic_optional_tag = "$optional-tag";

/// Identity of an `if` condition within one function.  Two `if`s
/// reading the same condition get the same id, so the transfer can
/// remember which paths had it true — see
/// [AbstractState.facts].  Function-scoped like every other id here.
pub const GuardId = abstract_state.GuardId;

pub const IndexTerm = abstract_state.IndexTerm;
pub const Comparison = abstract_state.Comparison;

/// Bounds for an authenticated unsigned local modulo a positive constant.
pub const ModuloIndex = struct {
    input: LocalId,
    modulus: u64,
};

// ── Source position ─────────────────────────────────────────

pub const SrcPos = struct {
    /// Byte offset into source.
    byte: u32,
    /// 1-indexed line.
    line: u32,
    /// 1-indexed column.
    column: u32,
};

pub const ValueInput = union(enum) {
    local: LocalId,
    field: struct { parent: LocalId, name: []const u8 },
    indexed: struct {
        array: LocalId,
        index: IndexTerm,
        modulo: ?ModuloIndex = null,
        /// Raw scaled byte coverage is not a value certificate.
        scaled: ?abstract_state.ScaledElement = null,
    },
};

/// Canonical physical frame-cell loans, independent of those cells' values.
/// `locals` always report, including integers that encode frame addresses.
/// A complete proof is the whole stack decision. An incomplete proof permits
/// a coarse stack origin only when `legacy_locals` independently proves that
/// the returned expression carries that cell's address, not merely a call
/// argument derived from it.
pub const StackLoanProof = struct {
    complete: bool = false,
    locals: []const LocalId = &.{},
    legacy_locals: []const LocalId = &.{},
};
// ── Statements ─────────────────────────────────────────────

pub const StmtKind = union(enum) {
    /// `var/const NAME = INIT;` — local declared, bound to RHS.
    decl: struct {
        local: LocalId,
        init_kind: ExprKind,
        integer_value: ?u64 = null,
        value_defined: bool = false,
        value_inputs: [8]?ValueInput = .{null} ** 8,
        /// Lifetime copies may reinterpret bytes instead of copying array slots.
        array_copy: bool = true,
        value_has_undefined_origin: bool = false,
        entire_source_undefined: bool = true,
        value_entirely_undefined: bool = false,
        result_is_computation: bool = false,
    },

    /// `LHS = RHS;` — overwrite local with new RHS.
    assign: struct {
        target: LocalId,
        rhs_kind: ExprKind,
        integer_value: ?u64 = null,
        value_defined: bool = false,
        value_inputs: [8]?ValueInput = .{null} ** 8,
        array_copy: bool = true,
        value_has_undefined_origin: bool = false,
        entire_source_undefined: bool = true,
        value_entirely_undefined: bool = false,
        result_is_computation: bool = false,
    },

    /// Require a boolean condition on this path.
    assume: BooleanValue,

    /// Read selected initialization coverage, then its independent lifetime.
    indexed_read: struct {
        array: LocalId,
        index: IndexTerm,
        modulo: ?ModuloIndex = null,
        name: ?[]const u8 = null,
        /// Stable fixed-array field identity; dynamic indices are not keys.
        field_array: ?[]const u8 = null,
        scaled: ?abstract_state.ScaledElement = null,
    },
    indexed_write: struct {
        array: LocalId,
        index: IndexTerm,
        /// Evaluated LHS snapshot and arithmetic shape, for byte masks only.
        diagnostic_index: ?IndexTerm = null,
        diagnostic_scaled: ?abstract_state.ScaledElement = null,
        diagnostic_stride: ?struct { period: u64, offset: u64 } = null,
        rhs_kind: ExprKind,
        /// A following precise constructor mask owns these diagnostic bytes.
        diagnostic_children_follow: bool = false,
        /// Literal element lifetime path, borrowed from source.
        name: ?[]const u8 = null,
        /// Stable fixed-array field identity; dynamic indices are not keys.
        field_array: ?[]const u8 = null,
        /// Bounded dependencies of a value expression. Unsupported values
        /// retain their reads but cannot establish initialized coverage.
        inputs: [8]?LocalId = .{null} ** 8,
        selected_inputs: [8]?ValueInput = .{null} ** 8,
        /// An appended old-element obligation certifies coverage, not the RHS.
        /// Inputs before this slot remain actual value dependencies.
        certificate_only_input: ?u4 = null,
        all_elements: bool = false,
        defined: bool = false,
        value_has_undefined_origin: bool = false,
        entire_source_undefined: bool = true,
        value_entirely_undefined: bool = false,
        result_is_computation: bool = false,
    },
    counter_step: struct { local: LocalId, step: i8 },
    compare_assume: Comparison,
    scaled_index: @import("bounded_prefix.zig").ScaledIndex,
    /// Existing exhaustive-fill proofs commit coverage explicitly.
    array_complete: struct {
        array: LocalId,
        /// Whole location coverage is not necessarily a value certificate.
        value_defined: bool = true,
        inputs: [8]?LocalId = .{null} ** 8,
        selected_inputs: [8]?ValueInput = .{null} ** 8,
        value_has_undefined_origin: bool = false,
        value_entirely_undefined: bool = false,
    },
    /// A natural-exit loop unconditionally wrote every slot in [start, end).
    /// Written bytes are separate from the optional strict value certificate.
    array_range_complete: struct {
        array: LocalId,
        start: u64,
        end: u64,
        inputs: [8]?LocalId = .{null} ** 8,
        selected_inputs: [8]?ValueInput = .{null} ** 8,
        value_defined: bool = true,
        value_has_undefined_origin: bool = false,
        /// Exact zero-offset enumeration copy; replay bytes, not certificates.
        diagnostic_source: ?LocalId = null,
    },
    /// A canonical helper's successful return proves this count of stores.
    /// Seeded local append loops use a separate diagnostic-only branch below.
    array_prefix: struct {
        array: LocalId,
        count: LocalId,
        inputs: [8]?LocalId = .{null} ** 8,
        scale: u64 = 1,
        /// A local seed-one append shape. Transfer checks the initial written
        /// slot and retains only diagnostic bytes plus its exact last selector.
        seeded_append: bool = false,
    },
    /// A successful zero-based memset initializes only its defined count.
    /// Count and fill dependencies remain reads, never helper-return proofs.
    array_memset_prefix: struct {
        array: LocalId,
        count: IndexTerm,
        rhs_kind: ExprKind,
        defined: bool = false,
        selected_inputs: [8]?ValueInput = .{null} ** 8,
        value_has_undefined_origin: bool = false,
        entire_source_undefined: bool = true,
    },
    /// A selected pointer-free array value copies actual source coverage.
    /// Unknown sources remain uncertified even when their bytes were written.
    array_value: struct {
        target: LocalId,
        source: ExprKind,
        inputs: [8]?LocalId = .{null} ** 8,
        selected_inputs: [8]?ValueInput = .{null} ** 8,
        /// Vector coercions and bit casts require the entire source payload.
        /// Their elements are not a one-to-one initialization map.
        whole_payload: bool = false,
        /// Layout-changing computations cannot reuse source element repairs.
        layout_change: bool = false,
        /// Byte transport alone: retain holes and repairs without certifying
        /// the copied values or changing lifetime/resource identities.
        diagnostic_only: bool = false,
        /// Capture byte replay changes only negative masks and physical repairs.
        /// It must not change value, array, pointer, or lifetime certificates.
        mask_only: bool = false,
        /// Optional captures omit the enclosing tag's diagnostic bytes.
        optional_payload: bool = false,
        target_field: ?[]const u8 = null,
    },

    /// `<receiver>.deinit()` on an arena.  Marks the arena dead.
    arena_kill: struct { arena_local: LocalId },

    /// `gpa.free(p)` / `gpa.destroy(p)` — marks the heap allocation
    /// bound to `freed_local` dead.  Double-free fires here.
    heap_free: struct {
        freed_local: LocalId,
        /// Fallback HeapId — used by transferHeapFree when the local
        /// has no prior tracked .heap origin (e.g. inter-procedural
        /// free of a `*T` parameter via @takes ownership(0); the
        /// caller might have allocated, or might not have, but we
        /// know the callee took ownership so any subsequent use is
        /// undefined regardless).  Same shape as
        /// .field_heap_free.fallback_hid.
        fallback_hid: abstract_state.HeapId,
        /// The allocator local that's freeing — `gpa` in
        /// `gpa.free(p)`.  Compared against the original alloc
        /// site's allocator to detect mismatch (oven-sh/bun#29840 class).
        /// Null when the free's receiver isn't a known local
        /// (dotted chain, stdlib reference, etc.).
        allocator_local: ?LocalId = null,
    },

    /// `obj.field = RHS;` — write to a struct field.  We track field
    /// origins separately from the parent local so heap allocations
    /// stored in fields can be freed and UAF-checked.
    field_assign: struct {
        parent: LocalId,
        name: []const u8,
        rhs_kind: ExprKind,
        /// Value-definedness is independent of pointer/resource lifetime.
        defined: bool = false,
        inputs: [8]?LocalId = .{null} ** 8,
        /// Selected scalar RHS storage; sibling payloads are not dependencies.
        selected_inputs: [8]?ValueInput = .{null} ** 8,
        /// Compound scalar stores also consume the previous selected value.
        reads_old_value: bool = false,
        /// The slice header's `ptr` of an offset view of another slice. Local
        /// frame storage is addressed by index from its base, so an offset view
        /// of it carries no element coverage; every other origin carries over.
        interior_view: bool = false,
        /// Replayed byte facts must not replace a resource/lifetime origin.
        /// An empty path denotes the whole value, or a pointer's pointee.
        diagnostic_only: bool = false,
        /// A possible source-proved poisoned store, never a write/repair credit.
        /// Unknown inputs have no effect; existing byte masks remain intact.
        may_write_only: bool = false,
        /// A settled whole-byte negative proof, not a value certificate.
        entire_value_undefined: bool = false,
        /// A replayed base witness does not overwrite its separately copied holes.
        preserve_undefined_descendants: bool = false,
        /// Return replay describes the value's bytes, even for a pointer value.
        /// Other empty pointer paths describe pointee storage.
        whole_value_bytes: bool = false,
        value_has_undefined_origin: bool = false,
        entire_source_undefined: bool = true,
        result_is_computation: bool = false,
        aggregate_value: bool = false,
    },

    /// `g.free(obj.field)` / `g.destroy(obj.field)` — kill a field's
    /// heap allocation.
    field_heap_free: struct {
        parent: LocalId,
        name: []const u8,
        /// Synthetic HeapId minted at cfg-build time, used by
        /// transferFieldHeapFree when the field has no prior tracked
        /// origin (e.g. an inter-procedural free of a field on a
        /// `*T` parameter where the allocation happened in the
        /// caller).  Lets subsequent .field_use reads see a .dead
        /// state and fire UAF.  Without this, only fields with an
        /// in-function alloc + free pair were trackable.
        fallback_hid: abstract_state.HeapId,
    },

    /// Read of `obj.field` — fires UAF / use-of-undef checks against
    /// the field's tracked origin (separate from the parent local's).
    field_use: struct {
        parent: LocalId,
        name: []const u8,
        /// An inline aggregate prefix checks lifetime, not sibling payload.
        lifetime_only: bool = false,
        /// Whole aggregate transport reads no selected member. It still
        /// rejects an entirely undefined value and retains all byte holes.
        aggregate_transport: bool = false,
        /// A scalar unwrap consumes payload bytes despite tag-mask children.
        optional_payload: bool = false,
        /// Optional tag selection is independent of the lifetime field path.
        optional_tag_path: ?[]const u8 = null,
    },

    /// Additional value-position borrow in a returned aggregate. The origin
    /// can be a direct address or a runtime alias, not an ampersand token.
    composite_escape: struct {
        value_kind: ExprKind,
        stack_loans: StackLoanProof = .{},
    },

    /// `return <expr>;` — function exit.  `value_kind` describes what's
    /// being returned.  `is_borrowed_return_type` tags whether the
    /// enclosing function's signature returns a borrowed-shape type
    /// (slice/pointer) — only those returns can leak a borrowed
    /// origin.  Value-typed returns MOVE the value (and any arena it
    /// owns) to the caller and are exempt from the escape check.
    ret: struct {
        value_kind: ExprKind,
        is_borrowed_return_type: bool,
        stack_loans: StackLoanProof = .{},
        /// Source-backed return definedness, consumed only by callee summaries.
        /// These operands are the value read before the function exits.
        value_defined: bool = false,
        value_inputs: [8]?ValueInput = .{null} ** 8,
        /// Snapshot of constructor bytes, used only by negative return replay.
        /// It supplies no returned-value or lifetime certificate.
        diagnostic_source: ?LocalId = null,
        /// Negative-only tag selection; null retains settled whole-byte origins.
        /// Payload boxing can exclude tag bytes without certifying the payload.
        tag_may_undefined: ?bool = null,
        tag_source: ?LocalId = null,
        value_has_undefined_origin: bool = false,
        entire_source_undefined: bool = true,
        value_entirely_undefined: bool = false,
        result_is_computation: bool = false,
        /// `return undefined;` written literally — canonical sentinel
        /// for comptime-gated branches (e.g. `if (comptime X) return
        /// undefined;` in bindgen stubs).  The author is explicitly
        /// opting in to returning garbage on a path the caller is
        /// comptime-guaranteed not to use.  The real undef-leak bug
        /// class is `var x: T = undefined; return x;` (via identifier),
        /// which still flows through .undef and gets caught.
        is_literal_undef: bool = false,
    },

    /// Use of a local (to read it).  Generates "is origin still live?"
    /// checks in the analyzer.
    /// Write through a pointer / field of `target` (e.g.
    /// `arena.* = X;`, `obj.field = X;`).  Does NOT rebind the
    /// local — its resource identity (.heap / .arena) is unchanged.
    /// Invalidates numeric/coverage facts for possibly mutated storage.
    /// Non-array scalar storage retains the existing out-write semantics;
    /// an array write never initializes all its elements.
    pointer_write: struct {
        target: LocalId,
        initializes: bool = true,
        /// The write goes through an element of the slice `target`, so its
        /// ptr/len words are unchanged. Element coverage is still revoked.
        payload_only: bool = false,
        /// Selected slice-element placement constrains diagnostics only.
        diagnostic_index: ?IndexTerm = null,
        /// A source-proven element mutation preserves only existing complete
        /// coverage, and only when its actual value dependencies are defined.
        preserves_complete_array: bool = false,
        /// Complete physical recipes replay scoped writes after revocation.
        preserves_diagnostic_base: bool = false,
        preserve_inputs: [8]?ValueInput = .{null} ** 8,
        /// Byte-source dependencies used only by the diagnostic.
        diagnostic_inputs: [2]?ValueInput = .{null} ** 2,
        value_has_undefined_origin: bool = false,
        /// Whole-array helpers can consume fully supplied aggregate values.
        /// Their selected payload inputs remain subject to definedness checks.
        preserve_whole_payload: bool = false,
    },
    /// Write through a `*T` parameter (or pointer-typed local) to
    /// caller-visible storage — `out.* = X;` or `out.field = X;`
    /// where `out` is pointer-typed.  Mirrors the escape-style
    /// checks at `return`: a value whose lifetime ends with this
    /// function (function-local arena, stack reference) being
    /// reachable from caller-owned storage is an escape.  `out`
    /// is the pointer-typed local; `value_kind` is the RHS
    /// classification used to derive the written value's origin.
    out_param_write: struct { out: LocalId, value_kind: ExprKind },
    /// Calling a destructor on an interior pointer — UB under
    /// typical allocators since the pointer wasn't returned by
    /// `allocator.create()`.  The canonical oven-sh/bun#30166 pattern:
    /// `for (entries.items) |*r| r.destroy();`.  `receiver` is
    /// the interior pointer local; `container` is the source
    /// container it borrows from (recorded at for-loop capture).
    interior_pointer_destroy: struct { receiver: LocalId, container: LocalId },
    /// Type T has a heap creator (`<x>.create(T)`) and a
    /// destructor (finalize / deinit / destroy) but the
    /// destructor doesn't free `self` — every instance of T
    /// leaks the heap-allocated descriptor.  oven-sh/bun#29840 class.
    /// `type_name` is the bare ident of T (source slice); used
    /// in the diagnostic.
    leak_warning: struct { type_name: []const u8 },
    /// `<long-lived-lhs> = .{ .tag = <expr> }` where `<expr>`
    /// contains an early-exit (`try` or `catch ... return /
    /// unreachable`).  Zig writes the union tag to the result
    /// location before evaluating the payload, so the early-exit
    /// path leaves the LHS with the new tag and stale payload
    /// bytes.  oven-sh/bun#29422 class.  `tag_name` is the source slice
    /// of the union variant being written (`.zlib`, `.namedPipe`,
    /// `.Locked`, `.err`, …).
    partial_union_write: struct { tag_name: []const u8 },
    /// Re-bind a local to .plain.  Emitted at loop body entry for
    /// `while (it) |n|` / `for (xs) |x|` captures so back-edges
    /// don't carry one iteration's `free(n)` state into the next —
    /// the capture refers to a different element each iteration.
    /// Without this, the @takes-ownership / heap_free fallback path
    /// (which now marks plain locals as .heap.dead) cascades
    /// spurious double-free reports across loop iterations.
    reset_capture: struct {
        local: LocalId,
        /// Iteration selects a value from this live array/slice backing.
        value_source: ?LocalId = null,
        value_defined: bool = true,
        /// By-value captures retain strict source obligations before reset.
        value_inputs: [8]?ValueInput = .{null} ** 8,
    },
    use: struct {
        local: LocalId,
        /// The resolved instance method takes a pointer to its receiver.
        /// Borrowing a value place does not read that place's payload.
        /// The receiver's pointer header and resource lifetime are still
        /// checked. This flag never proves an initialization write.
        from_method_call: bool = false,
        /// Select a proved optional tag origin without changing lifetime checks.
        tag_only: bool = false,
        optional_payload: bool = false,
    },
    /// A bare `if (COND)` whose condition carries a [GuardId].  The
    /// arm that COND holds records that fact; the arm it does not
    /// records the opposite.  Pruning the second kind of path when a
    /// later `if` assumes the same condition is what lets a local
    /// initialised under one guard be read under a later, re-tested
    /// spelling of the same condition.
    guard_fact: struct {
        guard: abstract_state.GuardId,
        /// True in the arm where the condition HOLDS, false in the
        /// other one.
        holds: bool,
    },

    /// Unknown operation. Calls cannot assign unexposed local variables.
    lowering_gap: struct { note: []const u8, may_assign_locals: bool = true },
};

pub const Stmt = struct {
    kind: StmtKind,
    /// Start position — first token of the source construct.
    pos: SrcPos,
    /// End position (exclusive) — one past the last token.  Used to
    /// emit span-based Problem diagnostics (editors highlight the
    /// full construct, not just a single column).  When the
    /// statement isn't derived from a real source node (synthetic
    /// gaps, etc.), the emitter may set end_pos == pos as a sentinel
    /// and the diagnostic falls back to a single-column range.
    end_pos: SrcPos,
};

// ── Expression-result classification ────────────────────────

/// Shape of a value produced by an expression.  We don't model expressions
/// as trees; just classify what the RHS produces lifetime-wise.
pub const ExprKind = union(enum) {
    /// Literal, arithmetic, value-typed call — no lifetime constraint.
    plain,
    boolean: BooleanValue,
    /// Call to a fn annotated `// @returns borrowed_from(<param>)`.
    /// `borrowed_from_local` is the local that the lifetime is tied to.
    borrowed_from: LocalId,
    /// Call to a fn annotated `// @returns owned` — caller owns, no
    /// lifetime constraint despite borrowed-shape signature.
    owned,
    /// `ArenaAllocator.init(...)` — produces a fresh arena.  The
    /// ArenaId is minted at lowering time so worklist re-visits of
    /// the same call site reuse the SAME id; otherwise loops would
    /// blow `state.arenas` up unboundedly.
    /// Fresh arena.  `is_heap_allocated` distinguishes stack-
    /// allocated (`var a = ArenaAllocator.init(...)`) from heap-
    /// allocated (`var a = gpa.create(ArenaAllocator)`) — both
    /// mint an ArenaId for UAK tracking, but out-param escape
    /// gates on this.
    arena_init: struct { id: abstract_state.ArenaId, is_heap_allocated: bool = false },
    /// Heap allocation call (gpa.alloc / gpa.create / dupe / ...).
    /// HeapId is minted at lowering time, same reasoning as arena_init.
    /// `allocator_local` records the receiver of the call (e.g.
    /// `gpa` in `gpa.alloc(...)`) — null when the receiver isn't a
    /// known local.  Used at the matching free site to detect
    /// allocator-mismatch.
    heap_alloc: struct {
        id: abstract_state.HeapId,
        allocator_local: ?LocalId = null,
        /// Exact caller allocator header for interprocedural replacements.
        /// Null preserves ordinary heap-allocation behavior.
        allocator_source: ?ValueInput = null,
    },
    /// `&<local>` — address-of a function-local.  Produces a pointer
    /// whose lifetime is bound to that local's stack frame.
    stack_ref: LocalId,
    /// A composite/aggregate expression (struct literal, array
    /// literal, etc.) whose return-shape borrows from `local`.
    /// Distinct from `.copy_of` so transferRet can fire escape
    /// checks regardless of return type — the surrounding composite
    /// makes this a borrow embedded in a value, not a move of the
    /// resource itself.
    composite_borrow: LocalId,
    /// `undefined` keyword — the value is explicitly uninitialized.
    undef,
    /// Reading a local — pass-through of that local's current origin.
    copy_of: LocalId,
    /// Reading `parent.name` — pass-through of the field's current
    /// origin (looked up in state.fields).
    field_copy_of: struct { parent: LocalId, name: []const u8 },
    /// Couldn't classify — conservative .plain at use site.
    unknown,
};

pub const BooleanValue = union(enum) {
    constant: bool,
    local: LocalId,
    not_local: LocalId,

    pub fn negate(value: BooleanValue) BooleanValue {
        return switch (value) {
            .constant => |v| .{ .constant = !v },
            .local => |v| .{ .not_local = v },
            .not_local => |v| .{ .local = v },
        };
    }
};

// ── Basic block ────────────────────────────────────────────

pub const BasicBlock = struct {
    id: BlockId,
    stmts: []Stmt,
    /// Successor blocks in CFG.  Empty for terminal blocks (after return).
    /// Two successors for branches (if/while); the analyzer joins their
    /// post-states at the merge block.
    successors: []BlockId,
};

// ── CFG ────────────────────────────────────────────────────

pub const Cfg = struct {
    blocks: []BasicBlock,
    entry: BlockId,
    /// Source span of the function whose body this CFG represents.
    fn_span: struct { start: u32, end: u32 },
    /// Local-name table (name & decl position keyed by LocalId).
    locals: []LocalInfo,
    /// Immutable LocalId type bounds. Empty means no static integer facts.
    /// Solver states borrow this storage and must die before this graph.
    integer_domains: []const abstract_state.IntegerDomain = &.{},
    /// Path strings referenced by `field_assign` / `field_use`
    /// statements that aren't contiguous in source — e.g. struct-
    /// literal unpacking builds "parent_prefix.field_name" from two
    /// disjoint tokens.  Most paths ARE source slices (no entry
    /// here); these own the rest.
    owned_paths: [][]u8 = &.{},
    /// Return and composite statements borrow these arrays. Each array is
    /// registered once, even when several statements share its proof.
    owned_stack_loans: [][]LocalId = &.{},
    /// Runtime member names for diagnostic byte completeness. Locals borrow
    /// these arrays; field-name bytes borrow source or owned_paths.
    owned_field_layouts: [][]const []const u8 = &.{},
    owned_index_domains: [][]u64 = &.{},

    pub fn deinit(self: *Cfg, gpa: std.mem.Allocator) void {
        for (self.blocks) |b| {
            gpa.free(b.stmts);
            gpa.free(b.successors);
        }
        gpa.free(self.blocks);
        gpa.free(self.locals);
        gpa.free(self.integer_domains);
        for (self.owned_paths) |p| gpa.free(p);
        gpa.free(self.owned_paths);
        for (self.owned_stack_loans) |loans| gpa.free(loans);
        gpa.free(self.owned_stack_loans);
        for (self.owned_field_layouts) |fields| gpa.free(fields);
        gpa.free(self.owned_field_layouts);
        for (self.owned_index_domains) |domain| gpa.free(domain);
        gpa.free(self.owned_index_domains);
    }
};

pub const LocalInfo = struct {
    name: []const u8, // borrowed from source — caller keeps source alive
    decl_pos: SrcPos,
    /// True iff the local was declared with an array type annotation
    /// like `var x: [N]T = ...`.  Set so slice-of-local classification
    /// only flags real stack arrays — slicing a local that holds a
    /// slice or pointer just produces another view of caller-owned
    /// storage, not an escape.
    is_array: bool = false,
    array_extent: ?u64 = null,
    is_unsigned: bool = false,
    /// CFG-only control state has no source binding or source-visible alias.
    /// An opaque source write cannot change its recorded branch outcome.
    is_control_local: bool = false,
    /// Selected data-valued projections need payload facts, not merely an
    /// initialized pointer or descriptor. Unrelated locals do not pay for it.
    tracks_array_payload: bool = false,
    tracks_optional_tag: bool = false,
    /// A switch selector's diagnostic observes its union tag, not payload bytes.
    /// Its full value_inputs remain unchanged for strict certificates.
    diagnostic_tag_only: bool = false,
    diagnostic_tag_may_undefined: ?bool = null,
    diagnostic_tag_guard: ?LocalId = null,
    /// The binding's actual value type is scalar, not a metatype or an
    /// aggregate/pointer header. Its runtime definedness uses value_inputs.
    tracks_scalar_value: bool = false,
    /// Known runtime struct members. Null means no layout fact. Written
    /// UNKNOWN members can cover bytes, but never supply value certificates.
    runtime_fields: ?[]const []const u8 = null,
    /// Exact by-value capture of authenticated std.meta.fields(Enum).
    /// Only its `value` member has this intrinsic scalar type certificate.
    /// Live field definedness remains a separate transfer-state fact.
    is_enum_field_capture: bool = false,
    /// Authenticated reflected tag domain; never a fill certificate.
    enum_value_indices: ?[]const u64 = null,
    /// True for a declared pointer spelling or an actual resolved non-slice
    /// pointer type (including aliases). Typically a `*Self` parameter.
    /// The pointee lives in the
    /// caller, so `&local.field` for a pointer-typed local is NOT a
    /// stack-frame borrow; it's a borrow from caller-owned storage.
    /// Address-of classification gates on this to avoid spurious
    /// stack-escape on the common `return &self.field` shape.
    is_pointer: bool = false,
    /// Actual slice descriptor type. This says nothing about its header's
    /// initializedness or the bytes behind its pointer.
    is_slice: bool = false,
    /// Aliases can mutate this local; do not retain boolean path facts.
    address_taken: bool = false,
    /// Coarse classification of the init expression — lets the
    /// composite-borrow walker decide at classify time whether a
    /// bare reference to this local in a returned struct should be
    /// treated as a borrow source.  Set at registerLocalFull from
    /// the same classifier that produces the .decl's init_kind.
    init_hint: InitHint = .other,
    /// True iff this local is the error-value capture of a `catch |err|`
    /// or `else |err|` arm.  Such a value is *definitely* an error, so a
    /// `return <this>` fires errdefers (Zig only runs errdefers on error
    /// returns).  Lets lowerReturn replay errdefers at `return err`,
    /// closing the errdefer-double-free-on-error-return false negative.
    is_error_capture: bool = false,
    /// If this local was declared from a bare identifier that names
    /// a fn in our annotation DB, the name of that fn.  Lets call
    /// sites `local(args)` resolve through the binding to the
    /// underlying fn's annotation.
    bound_fn_name: ?[]const u8 = null,
    /// The local's declared base type name (e.g. "Foo" for `*Foo`,
    /// `*const Foo`, `?*Foo`), with pointer/optional/const wrappers
    /// stripped.  `*Self` / `*@This()` is resolved to the enclosing
    /// fn's containing type.  Null when the local has no explicit
    /// type annotation (inferred type — not tracked).
    ///
    /// Used by call-site lookup to disambiguate `<recv>.method()`
    /// across method-name overloads on different types.
    type_name: ?[]const u8 = null,
    /// Set when this local is an interior pointer captured from a
    /// for-loop over `<container>.<field>` with `|*p|` capture
    /// style.  The LocalId names the container the pointer
    /// references.  Used by `interior_pointer_destroy` detection
    /// to flag calls like `for (entries.items) |*result|
    /// result.destroy();` — destroying an interior pointer is UB
    /// under typical allocators (oven-sh/bun#30166).
    from_container: ?LocalId = null,
    /// The frame local addressed by a direct borrow initializer
    /// (`const alias = &local;`) or a fixed-array pointer capture.
    /// Null when no frame storage owner is known.
    ///
    /// `&local` is not the only way a `catch` / `orelse` fallback can
    /// hand out frame storage — naming a binding that holds it produces
    /// exactly the same pointer — and the alias is resolved at
    /// LOWERING time, so the hop has to be recorded here rather than
    /// left to a consumer that never sees the initializer.  A fallback
    /// naming this local binds the local named by this field, so the
    /// stack escape the direct spelling reports is not lost.
    frame_borrow_origin: ?LocalId = null,
    /// Immutable `for (&array) |*entry|` capture of a fixed array element.
    /// Whole-element stores may preserve existing coverage but never fill it.
    /// Other pointer aliases retain only their dynamic storage origin.
    array_element_owner: ?LocalId = null,
};

pub const InitHint = enum {
    other,
    /// Local was initialized from `ArenaAllocator.init(...)` — IS the arena.
    arena_local,
    /// Local was initialized from `<arena_local>.allocator()` (directly
    /// or via copy of another arena_allocator local).  Tracks "this
    /// std.mem.Allocator value's storage dies with arena X" so calls
    /// to `.alloc()` / `.create()` / etc. through this allocator
    /// produce arena-bound memory (.arena origin), not a fresh .heap
    /// allocation.  Without this, arena-UAK on the standard pattern
    /// `const a = arena.allocator(); buf = a.alloc(...); arena.deinit(); use(buf);`
    /// would never fire — buf would carry a heap id unrelated to arena.
    arena_allocator,
    heap_local,
    /// Local is a TYPE ALIAS — `const X = struct {...};` /
    /// `const X = enum {...};` etc.  No runtime storage; `X.<id>`
    /// addresses a STATIC field, not a stack-frame slot.  Without
    /// this, `&X.field` looks like a stack-borrow and fires
    /// stack-escape on `return &X.<static_var>` (singleton pattern).
    type_alias,
};

// ── Tests ──────────────────────────────────────────────────
// Test bodies live in cfg_tests.zig to keep this file navigable.  The
// one carve-out: a test that must assert against a MODULE-PRIVATE
// limit stays with that module rather than moving here against an
// exported copy of the number — asserting the copy tests the copy.
// `cfg_builder.zig` keeps its lowering-budget tests for that reason.

test {
    _ = @import("cfg_tests.zig");
}
