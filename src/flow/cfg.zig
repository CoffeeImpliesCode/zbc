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
/// Identity of an `if` condition within one function.  Two `if`s
/// reading the same condition get the same id, so the transfer can
/// remember which paths had it true — see
/// [AbstractState.facts].  Function-scoped like every other id here.
pub const GuardId = abstract_state.GuardId;

// ── Source position ─────────────────────────────────────────

pub const SrcPos = struct {
    /// Byte offset into source.
    byte: u32,
    /// 1-indexed line.
    line: u32,
    /// 1-indexed column.
    column: u32,
};

// ── Statements ─────────────────────────────────────────────

pub const StmtKind = union(enum) {
    /// `var/const NAME = INIT;` — local declared, bound to RHS.
    decl: struct { local: LocalId, init_kind: ExprKind },

    /// `LHS = RHS;` — overwrite local with new RHS.
    assign: struct { target: LocalId, rhs_kind: ExprKind },

    /// Require a boolean condition on this path.
    assume: BooleanValue,

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
    field_assign: struct { parent: LocalId, name: []const u8, rhs_kind: ExprKind },

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
    field_use: struct { parent: LocalId, name: []const u8 },

    /// Additional value-position borrow in a returned aggregate. The origin
    /// can be a direct address or a runtime alias, not an ampersand token.
    composite_escape: ExprKind,

    /// `return <expr>;` — function exit.  `value_kind` describes what's
    /// being returned.  `is_borrowed_return_type` tags whether the
    /// enclosing function's signature returns a borrowed-shape type
    /// (slice/pointer) — only those returns can leak a borrowed
    /// origin.  Value-typed returns MOVE the value (and any arena it
    /// owns) to the caller and are exempt from the escape check.
    ret: struct {
        value_kind: ExprKind,
        is_borrowed_return_type: bool,
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
    /// Only clears .undef → .plain (the underlying storage was
    /// initialized via this write).
    pointer_write: struct { target: LocalId },
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
    reset_capture: struct { local: LocalId },
    use: struct {
        local: LocalId,
        /// True when this .use was emitted by a method-call walker
        /// pass (`x.method(...)`).  Method-call receivers on a local
        /// whose current origin is .undef are almost certainly init
        /// calls (you don't read garbage); transferUse clears .undef
        /// to .plain instead of firing use_undefined.  For .heap /
        /// .arena origins, the call still counts as a real use.
        from_method_call: bool = false,
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
    heap_alloc: struct { id: abstract_state.HeapId, allocator_local: ?LocalId = null },
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
    /// Path strings referenced by `field_assign` / `field_use`
    /// statements that aren't contiguous in source — e.g. struct-
    /// literal unpacking builds "parent_prefix.field_name" from two
    /// disjoint tokens.  Most paths ARE source slices (no entry
    /// here); these own the rest.
    owned_paths: [][]u8 = &.{},

    pub fn deinit(self: *Cfg, gpa: std.mem.Allocator) void {
        for (self.blocks) |b| {
            gpa.free(b.stmts);
            gpa.free(b.successors);
        }
        gpa.free(self.blocks);
        gpa.free(self.locals);
        for (self.owned_paths) |p| gpa.free(p);
        gpa.free(self.owned_paths);
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
    /// True iff the local's declared type begins with `*` (possibly
    /// preceded by `?` or `const`) — i.e. the local is a pointer
    /// (typically a `*Self` parameter).  The pointee lives in the
    /// caller, so `&local.field` for a pointer-typed local is NOT a
    /// stack-frame borrow; it's a borrow from caller-owned storage.
    /// Address-of classification gates on this to avoid spurious
    /// stack-escape on the common `return &self.field` shape.
    is_pointer: bool = false,
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
    /// The frame local this one holds the ADDRESS of, when its own
    /// initializer produced a borrow of this frame
    /// (`const alias = &local;`).  Null for every other initializer.
    ///
    /// `&local` is not the only way a `catch` / `orelse` fallback can
    /// hand out frame storage — naming a binding that holds it produces
    /// exactly the same pointer — and the alias is resolved at
    /// LOWERING time, so the hop has to be recorded here rather than
    /// left to a consumer that never sees the initializer.  A fallback
    /// naming this local binds the local named by this field, so the
    /// stack escape the direct spelling reports is not lost.
    frame_borrow_origin: ?LocalId = null,
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
    noreturn_alias,
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
