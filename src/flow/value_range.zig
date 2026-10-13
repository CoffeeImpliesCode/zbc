//! Bounded forward range proofs within one function body.
//!
//! Tracks lower bounds, nonzero values, container lengths, aliases, and
//! branch predicates. Joins retain only facts that hold on every reaching
//! path. Writes and calls invalidate facts they can change. Unsupported
//! transfers prove nothing, and a query that spends its step budget or
//! runs past one of the walks' depth bounds fails with
//! `error.AnalysisBudgetExceeded` rather than answering from a body it
//! only half-walked.
//!
//! Two shapes of proof are deliberately narrow: a dominating read bounds its
//! container only when the receiver carries a length (a slice or a fixed-size
//! array — never a C or many-pointer), and what a call reaches is resolved
//! from the pointer bindings in force at that point, so a rebound pointer no
//! longer inherits the target it was declared with.

const std = @import("std");
const Ast = std.zig.Ast;
const tokens = @import("../ast/tokens.zig");
const file_cache_mod = @import("../cache/file_cache.zig");
const fn_summary = @import("../model/fn_summary.zig");
const local_bindings = @import("../model/local_bindings.zig");
const numeric_nodes = @import("../model/numeric_nodes.zig");
const numeric_escape = @import("numeric_escape.zig");
const numeric_loops = @import("numeric_loops.zig");
const numbers = @import("numeric_range.zig");
const numeric_eval = @import("numeric_eval.zig");
const budget_mod = @import("../budget.zig");
const TypeResolver = @import("../type_resolver.zig").TypeResolver;
pub const NumericRange = numbers.Range;

/// Analysis steps one query may spend.  This is a property of the oracle,
/// not of the file: raising it hides work instead of reporting it, and
/// the cap is what the CLI diagnostic reports when a query gives up.
pub const step_budget: u32 = 50_000;

/// The bound a bounded walk inside the oracle hit, kept so the
/// diagnostic names the bound that actually stopped the walk.
const Stop = budget_mod.Stop;

/// Frames a recursive descent may take before it declines to go deeper.
/// Shared by the statement walk, the expression walk, the address-walk,
/// the predicate unwrap and the numeric evaluator: all five give up at the
/// same depth, so the diagnostic names one number for the module.
pub const walk_depth_cap: u8 = numeric_eval.Evaluator.frame_cap;

/// Rounds the numeric-alias fixpoint may run before it is declared not
/// to converge.
const alias_fold_rounds = 32;

/// What a query can fail with.  A query that spends its whole step
/// budget — or that declines to descend past a walk's depth bound —
/// has established nothing about the site it was asked about, and the
/// answer it would otherwise return is indistinguishable from "no proof
/// exists here".  Failing keeps the two apart: an unproven site is
/// still a plain `false` / `.unknown`, a walk that gave up is an
/// incomplete analysis the CLI has to say so.
/// Source loading, cancellation, and census failures retain their exact
/// shared summary error instead of becoming a missing numeric proof.
pub const QueryError = file_cache_mod.SummaryError;

/// A set of string keys (source slices, stable for the tree's lifetime).
const KeySet = struct {
    keys: std.ArrayListUnmanaged([]const u8) = .empty,

    pub fn deinit(self: *KeySet, gpa: std.mem.Allocator) void {
        self.keys.deinit(gpa);
    }
    pub fn contains(self: *const KeySet, k: []const u8) bool {
        for (self.keys.items) |e| if (std.mem.eql(u8, e, k)) return true;
        return false;
    }
    pub fn add(self: *KeySet, gpa: std.mem.Allocator, k: []const u8) !void {
        if (self.contains(k)) return;
        try self.keys.append(gpa, k);
    }
    /// Remove every key a rebinding of `root` invalidates: `root` itself and
    /// the paths rooted at it.  A key is a source spelling, and a spelling
    /// need not start with the name being rebound — `p.*` is a fact about the
    /// object `p` POINTS AT, so rebinding `p` leaves it stale even though
    /// `p.*` has nothing in common with `p` as a string.
    fn removeRooted(self: *KeySet, root: []const u8) void {
        var i: usize = 0;
        while (i < self.keys.items.len) {
            if (pathRootedAt(self.keys.items[i], root)) {
                _ = self.keys.swapRemove(i);
            } else i += 1;
        }
    }
    fn intersectWith(self: *KeySet, other: *const KeySet) void {
        var i: usize = 0;
        while (i < self.keys.items.len) {
            if (other.contains(self.keys.items[i])) i += 1 else _ = self.keys.swapRemove(i);
        }
    }
};

/// A `const n = c.len` binding: scalar `n` snapshots container `c`'s length.
/// Lets a guard on either side establish the other's fact (nonzero(n) ⟺
/// nonempty(c)).  Dropped when `n` is rebound or `c` is mutated.
const Alias = struct { scalar: []const u8, container: []const u8 };

/// A `const DIFF = MINUEND - SUBTRAHEND` binding.
/// Propagation: DIFF nonzero AND SUBTRAHEND provably >= 0 → MINUEND nonzero.
/// Sound because MINUEND - SUBTRAHEND > 0 and SUBTRAHEND >= 0 implies MINUEND >= 1.
/// Dropped when DIFF or MINUEND is rebound.
const DiffAlias = struct {
    diff: []const u8,
    minuend: []const u8,
    sub_node: Ast.Node.Index, // AST node of the subtrahend (for provablyNonneg check)
};

/// A local snapshot of a path, optionally plus a checked constant offset.
/// With another nonnegative path, the relation supplies only an upper bound
/// on this component. Writes to any dependency retire the relation.
const ValueAlias = struct {
    local: []const u8,
    path: []const u8,
    /// A successfully checked sum holds `local == path + offset`.
    offset: u64 = 0,
    /// For a variable sum, `local == path + other_path`; neither component
    /// inherits the total's lower bound or its nonzero fact.
    other_path: ?[]const u8 = null,
};

/// A local scalar is known to be at least `n` on this path.  Bounds of zero
/// retain non-negativity for later expression proofs; the query uses only
/// bounds >= 1.
const ScalarMin = struct {
    name: []const u8,
    n: u64,
};

/// `scalar` is known to equal the comptime constant `val` on the recorded path
/// (e.g. inside `switch (scalar) { K => … }` arm, or after `const scalar = K`).
const ScalarVal = struct {
    name: []const u8,

    val: u64,
};

/// Container `path` is known to have length >= `n` on this path, established
/// by a guard `if (path.len >= n) { … }` / `if (path.len < n) return;` etc.
/// (`containers` tracks the special case n == 1; this carries n >= 2 too).
const MinLen = struct {
    path: []const u8,
    n: u64,
};

/// A copied header's true-branch extent while its bare bool selector is stable.
/// The producer proves the selector's type before publishing this relation.
pub const ConditionalLength = struct {
    header: []const u8,
    selector: []const u8,
    value: NumericRange,
};

/// A factor of a checked or plain integer product.  Container factors are
/// canonical `<path>` keys (the `.len` access is removed); scalar factors keep
/// the local name so aliases can resolve them later.
pub const ProductFactor = struct {
    key: []const u8,
    is_container: bool,
};

/// A local scalar is equal to a product of two factors on the recorded path.
/// `condition` is set when the product is selected by an `if` expression; the
/// fact is usable only after the same predicate is established.
const ProductAlias = struct {
    result: []const u8,
    left: ProductFactor,
    right: ProductFactor,
    condition: ?Ast.Node.Index = null,
    condition_true: bool = true,
};

/// A branch predicate retained for exact conditional-product matching and
/// limited boolean implication (`!(A and B)`, `A` => `!B`).
pub const Predicate = struct {
    node: Ast.Node.Index,
    truth: bool,
};

/// One operand of a retained compound that the fold is still WAITING on.
///
/// `A and B` proved false proves `!B` from `A` alone, and `A or B` proved true
/// proves `B` from `!A` alone — but only once that operand is itself retained,
/// and the two are routinely recorded by different statements.  This entry is
/// that dependency: the compound, which of its two operands settles it
/// (`side`), and the truth value that operand has to carry (`needed`).  When
/// that predicate arrives the fold hands the OTHER operand over with the
/// compound's own truth value, which is the one implication that was waiting.
///
/// `side` is an index rather than the operand's node so that the pair cannot
/// drift apart when the same compound is offered again.
const UnsettledOperand = struct {
    predicate: Predicate,
    side: u1,
    needed: bool,
};

/// Equality between a scalar and a container length (`scalar == path.len`).
const Equality = struct {
    scalar: []const u8,
    container: []const u8,
};

const BitAlias = struct {
    local: []const u8 = "",
    source: []const u8,
    mask: u64,
    float_bits: u8,
    union_view: bool = false,
    absolute: bool = false,
};

/// Abstract state: fact sets plus length/value/product aliases and predicates.
pub const State = struct {
    scalars: KeySet = .{}, // locals known != 0
    containers: KeySet = .{}, // container paths known non-empty
    aliases: std.ArrayListUnmanaged(Alias) = .empty, // n == c.len
    diff_aliases: std.ArrayListUnmanaged(DiffAlias) = .empty, // n = A - B
    value_aliases: std.ArrayListUnmanaged(ValueAlias) = .empty, // local == path
    scalar_mins: std.ArrayListUnmanaged(ScalarMin) = .empty, // scalar >= n
    scalar_vals: std.ArrayListUnmanaged(ScalarVal) = .empty, // scalar == const K
    min_lens: std.ArrayListUnmanaged(MinLen) = .empty, // path.len >= n
    /// `name.len` as a RANGE SNAPSHOT, recorded where the binding that
    /// produced it was established: `const b = alloc.alloc(T, n)` returns
    /// exactly `n` elements, so BOTH ends of the count's own range are known
    /// at that one point and are kept together as one value.
    ///
    /// The snapshot is deliberately not a live read of the count's name.  The
    /// count was a value at one point; anything that happens to it since —
    /// a write to its own local, a refinement the walk learned from a later
    /// guard — describes a different value and must not move a length that
    /// was already proved.  What DOES withdraw it is a write to the binding
    /// itself (`dropFactsForRebind`), a rebind inside a loop
    /// (`dropLoopMutated`), or an effect that can reach the binding's address
    /// (`dropIndirectFacts`): the three ways a slice's length can change at
    /// all.  A slice header lives in the local's own frame slot, so a callee
    /// that receives the slice by value cannot resize it.
    len_bounds: std.ArrayListUnmanaged(numeric_eval.Fact) = .empty,
    conditional_lengths: std.ArrayListUnmanaged(ConditionalLength) = .empty,
    product_aliases: std.ArrayListUnmanaged(ProductAlias) = .empty,
    predicates: std.ArrayListUnmanaged(Predicate) = .empty,
    numeric: std.ArrayListUnmanaged(numeric_eval.Fact) = .empty,
    bit_aliases: std.ArrayListUnmanaged(BitAlias) = .empty,
    /// Retained compounds the fold has not been able to hand over yet,
    /// paired with the operand each is waiting on.  See `Fold`.
    ///
    /// This is the ONLY part of the fold that is not a fixed rule, which is
    /// why it is the only part that has to be kept: everything else is decided
    /// the moment its predicate is recorded, and no later predicate changes
    /// what it gives.  It lives on the STATE because a compound and the operand
    /// that settles it are routinely recorded by different statements, so the
    /// dependency outlives the walk step that created it.
    ///
    /// JOINED WITH `predicates` and never independently.  An entry is a claim
    /// that its compound is retained, so the two lists must agree about which
    /// compounds are retained: `clone`, `intersectWith` and `replaceWith` move
    /// both together and `clearPredicates` clears both.
    unsettled: std.ArrayListUnmanaged(UnsettledOperand) = .empty,

    pub fn deinit(self: *State, gpa: std.mem.Allocator) void {
        self.scalars.deinit(gpa);
        self.containers.deinit(gpa);
        self.aliases.deinit(gpa);
        self.diff_aliases.deinit(gpa);
        self.value_aliases.deinit(gpa);
        self.scalar_mins.deinit(gpa);
        self.scalar_vals.deinit(gpa);
        self.min_lens.deinit(gpa);
        self.len_bounds.deinit(gpa);
        self.conditional_lengths.deinit(gpa);
        self.product_aliases.deinit(gpa);
        self.predicates.deinit(gpa);
        self.numeric.deinit(gpa);
        self.bit_aliases.deinit(gpa);
        self.unsettled.deinit(gpa);
    }
    pub fn clone(self: *const State, gpa: std.mem.Allocator) !State {
        var out: State = .{};
        errdefer out.deinit(gpa);
        try out.scalars.keys.appendSlice(gpa, self.scalars.keys.items);
        try out.containers.keys.appendSlice(gpa, self.containers.keys.items);
        try out.aliases.appendSlice(gpa, self.aliases.items);
        try out.diff_aliases.appendSlice(gpa, self.diff_aliases.items);
        try out.value_aliases.appendSlice(gpa, self.value_aliases.items);
        try out.scalar_mins.appendSlice(gpa, self.scalar_mins.items);
        try out.scalar_vals.appendSlice(gpa, self.scalar_vals.items);
        try out.min_lens.appendSlice(gpa, self.min_lens.items);
        try out.len_bounds.appendSlice(gpa, self.len_bounds.items);
        try out.conditional_lengths.appendSlice(gpa, self.conditional_lengths.items);
        try out.product_aliases.appendSlice(gpa, self.product_aliases.items);
        try out.predicates.appendSlice(gpa, self.predicates.items);
        try out.numeric.appendSlice(gpa, self.numeric.items);
        try out.bit_aliases.appendSlice(gpa, self.bit_aliases.items);
        try out.unsettled.appendSlice(gpa, self.unsettled.items);
        return out;
    }

    fn intersectWith(self: *State, other: *const State) void {
        var numeric: usize = 0;
        while (numeric < self.numeric.items.len) {
            const value = self.numeric.items[numeric];
            const joined = value.value.join(other.numericValue(value.name));
            if (joined == .unknown) {
                const removed = self.numeric.swapRemove(numeric);
                std.debug.assert(std.mem.eql(u8, removed.name, value.name));
            } else {
                self.numeric.items[numeric].value = joined;
                numeric += 1;
            }
        }
        var bit: usize = 0;
        while (bit < self.bit_aliases.items.len) {
            if (other.hasBitAlias(self.bit_aliases.items[bit])) bit += 1 else _ = self.bit_aliases.swapRemove(bit);
        }
        self.scalars.intersectWith(&other.scalars);
        self.containers.intersectWith(&other.containers);
        var i: usize = 0;
        while (i < self.aliases.items.len) {
            if (other.hasAlias(self.aliases.items[i])) i += 1 else _ = self.aliases.swapRemove(i);
        }
        // Conservatively keep diff_aliases present in both states.
        var j: usize = 0;
        while (j < self.diff_aliases.items.len) {
            if (other.hasDiffAlias(self.diff_aliases.items[j])) j += 1 else _ = self.diff_aliases.swapRemove(j);
        }
        var k: usize = 0;
        while (k < self.value_aliases.items.len) {
            if (other.hasValueAlias(self.value_aliases.items[k])) k += 1 else _ = self.value_aliases.swapRemove(k);
        }
        var m: usize = 0;
        while (m < self.scalar_vals.items.len) {
            if (other.hasScalarVal(self.scalar_vals.items[m])) m += 1 else _ = self.scalar_vals.swapRemove(m);
        }
        // Scalar lower bounds also join by the weaker bound, but only when
        // both branches prove a bound for the same local.
        var sm: usize = 0;
        while (sm < self.scalar_mins.items.len) {
            const e = self.scalar_mins.items[sm];
            if (other.scalarMinOf(e.name)) |ov| {
                if (ov < e.n) self.scalar_mins.items[sm].n = ov;
                sm += 1;
            } else {
                _ = self.scalar_mins.swapRemove(sm);
            }
        }

        // A product fact is path-sensitive and remains sound only when it is
        // present in both incoming states with the same selected branch.
        var q: usize = 0;
        while (q < self.product_aliases.items.len) {
            if (other.hasProductAlias(self.product_aliases.items[q])) q += 1 else _ = self.product_aliases.swapRemove(q);
        }
        var r: usize = 0;
        while (r < self.predicates.items.len) {
            if (other.hasPredicate(self.predicates.items[r])) r += 1 else _ = self.predicates.swapRemove(r);
        }
        // A compound the join did not keep cannot settle anything: its
        // consequence was only ever valid while it was retained.  The entries
        // are keyed on the COMPOUND and not on the operand, so this is the same
        // question the line above was just asked, and the two lists cannot
        // come apart.
        var s: usize = 0;
        while (s < self.unsettled.items.len) {
            if (other.hasPredicate(self.unsettled.items[s].predicate)) s += 1 else _ = self.unsettled.swapRemove(s);
        }
        // min_lens: keep paths present in BOTH branches; the proven minimum
        // after a join is the WEAKER (smaller) of the two branch bounds.
        var p: usize = 0;
        while (p < self.min_lens.items.len) {
            const e = self.min_lens.items[p];
            if (other.minLenOf(e.path)) |ov| {
                if (ov < e.n) self.min_lens.items[p].n = ov;
                p += 1;
            } else _ = self.min_lens.swapRemove(p);
        }
        // len_bounds: a snapshot describes ONE binding, so it survives a join
        // only where both branches carry the same name.  The range both may be
        // relied on to hold is the wider of the two, and a branch that never
        // reached the allocation contributes nothing at all — its range is
        // unknown, and joining with unknown is exactly how the entry leaves.
        var b: usize = 0;
        while (b < self.len_bounds.items.len) {
            const e = self.len_bounds.items[b];
            const joined = e.value.join(other.baselineLenBoundOf(e.name) orelse .unknown);
            if (joined == .unknown) {
                _ = self.len_bounds.swapRemove(b);
            } else {
                self.len_bounds.items[b].value = joined;
                b += 1;
            }
        }
        var conditional: usize = 0;
        while (conditional < self.conditional_lengths.items.len) {
            if (other.hasConditionalLength(self.conditional_lengths.items[conditional])) {
                conditional += 1;
            } else {
                _ = self.conditional_lengths.swapRemove(conditional);
            }
        }
    }
    pub fn replaceWith(self: *State, gpa: std.mem.Allocator, src: *const State) !void {
        self.scalars.keys.clearRetainingCapacity();
        self.containers.keys.clearRetainingCapacity();
        self.aliases.clearRetainingCapacity();
        self.diff_aliases.clearRetainingCapacity();
        self.value_aliases.clearRetainingCapacity();
        self.scalar_mins.clearRetainingCapacity();
        self.scalar_vals.clearRetainingCapacity();
        self.min_lens.clearRetainingCapacity();
        self.len_bounds.clearRetainingCapacity();
        self.conditional_lengths.clearRetainingCapacity();
        self.product_aliases.clearRetainingCapacity();
        self.predicates.clearRetainingCapacity();
        self.numeric.clearRetainingCapacity();
        self.bit_aliases.clearRetainingCapacity();
        self.unsettled.clearRetainingCapacity();
        try self.scalars.keys.appendSlice(gpa, src.scalars.keys.items);
        try self.containers.keys.appendSlice(gpa, src.containers.keys.items);
        try self.aliases.appendSlice(gpa, src.aliases.items);
        try self.diff_aliases.appendSlice(gpa, src.diff_aliases.items);
        try self.value_aliases.appendSlice(gpa, src.value_aliases.items);
        try self.scalar_mins.appendSlice(gpa, src.scalar_mins.items);
        try self.scalar_vals.appendSlice(gpa, src.scalar_vals.items);
        try self.min_lens.appendSlice(gpa, src.min_lens.items);
        try self.len_bounds.appendSlice(gpa, src.len_bounds.items);
        try self.conditional_lengths.appendSlice(gpa, src.conditional_lengths.items);
        try self.product_aliases.appendSlice(gpa, src.product_aliases.items);
        try self.predicates.appendSlice(gpa, src.predicates.items);
        try self.numeric.appendSlice(gpa, src.numeric.items);
        try self.bit_aliases.appendSlice(gpa, src.bit_aliases.items);
        try self.unsettled.appendSlice(gpa, src.unsettled.items);
    }
    fn hasProductAlias(self: *const State, pa: ProductAlias) bool {
        for (self.product_aliases.items) |e| {
            if (!std.mem.eql(u8, e.result, pa.result)) continue;
            if (e.left.is_container != pa.left.is_container or
                !std.mem.eql(u8, e.left.key, pa.left.key)) continue;
            if (e.right.is_container != pa.right.is_container or
                !std.mem.eql(u8, e.right.key, pa.right.key)) continue;
            if (e.condition != pa.condition or e.condition_true != pa.condition_true) continue;
            return true;
        }
        return false;
    }
    fn addProductAlias(self: *State, gpa: std.mem.Allocator, pa: ProductAlias) !void {
        if (!self.hasProductAlias(pa)) try self.product_aliases.append(gpa, pa);
    }
    fn hasPredicate(self: *const State, predicate: Predicate) bool {
        for (self.predicates.items) |e| {
            if (e.node == predicate.node and e.truth == predicate.truth) return true;
        }
        return false;
    }
    fn addPredicate(self: *State, gpa: std.mem.Allocator, predicate: Predicate) !bool {
        if (self.hasPredicate(predicate)) return false;
        try self.predicates.append(gpa, predicate);
        return true;
    }
    fn clearPredicates(self: *State) void {
        self.predicates.clearRetainingCapacity();
        self.unsettled.clearRetainingCapacity();
    }
    /// Register `entry` unless the same dependency is already waiting.  The
    /// same compound is offered again every time one of its operands settles,
    /// and the side that is still absent would otherwise be registered twice.
    fn addUnsettled(self: *State, gpa: std.mem.Allocator, entry: UnsettledOperand) !void {
        for (self.unsettled.items) |waiting| {
            if (waiting.predicate.node == entry.predicate.node and
                waiting.predicate.truth == entry.predicate.truth and
                waiting.side == entry.side and waiting.needed == entry.needed) return;
        }
        try self.unsettled.append(gpa, entry);
    }
    fn dropProductAliasesByName(self: *State, name: []const u8) void {
        var i: usize = 0;
        while (i < self.product_aliases.items.len) {
            const pa = self.product_aliases.items[i];
            if (std.mem.eql(u8, pa.result, name) or
                (!pa.left.is_container and std.mem.eql(u8, pa.left.key, name)) or
                (!pa.right.is_container and std.mem.eql(u8, pa.right.key, name)))
            {
                _ = self.product_aliases.swapRemove(i);
            } else {
                i += 1;
            }
        }
    }
    fn dropProductAliasesByRoot(self: *State, root: []const u8) void {
        var i: usize = 0;
        while (i < self.product_aliases.items.len) {
            const pa = self.product_aliases.items[i];
            if (std.mem.eql(u8, pa.result, root) or
                (pa.left.is_container and pathRootedAt(pa.left.key, root)) or
                (pa.right.is_container and pathRootedAt(pa.right.key, root)))
            {
                _ = self.product_aliases.swapRemove(i);
            } else {
                i += 1;
            }
        }
    }

    fn hasAlias(self: *const State, a: Alias) bool {
        for (self.aliases.items) |e|
            if (std.mem.eql(u8, e.scalar, a.scalar) and std.mem.eql(u8, e.container, a.container)) return true;
        return false;
    }
    fn addAlias(self: *State, gpa: std.mem.Allocator, a: Alias) !void {
        if (self.hasAlias(a)) return;
        try self.aliases.append(gpa, a);
    }
    fn dropAliasesByScalar(self: *State, scalar: []const u8) void {
        var i: usize = 0;
        while (i < self.aliases.items.len) {
            if (std.mem.eql(u8, self.aliases.items[i].scalar, scalar)) _ = self.aliases.swapRemove(i) else i += 1;
        }
    }
    fn dropAliasesByContainer(self: *State, container: []const u8) void {
        var i: usize = 0;
        while (i < self.aliases.items.len) {
            if (pathRootedAt(self.aliases.items[i].container, container)) _ = self.aliases.swapRemove(i) else i += 1;
        }
    }
    fn hasDiffAlias(self: *const State, da: DiffAlias) bool {
        for (self.diff_aliases.items) |e|
            if (e.sub_node == da.sub_node and
                std.mem.eql(u8, e.diff, da.diff) and
                std.mem.eql(u8, e.minuend, da.minuend)) return true;
        return false;
    }
    fn addDiffAlias(self: *State, gpa: std.mem.Allocator, da: DiffAlias) !void {
        if (self.hasDiffAlias(da)) return;
        try self.diff_aliases.append(gpa, da);
    }
    /// Drop diff_aliases where the diff variable or minuend equals `name`
    /// (called when `name` is rebound — both bindings become stale).
    fn dropDiffAliasesByName(self: *State, name: []const u8) void {
        var i: usize = 0;
        while (i < self.diff_aliases.items.len) {
            const da = self.diff_aliases.items[i];
            if (std.mem.eql(u8, da.diff, name) or std.mem.eql(u8, da.minuend, name)) {
                _ = self.diff_aliases.swapRemove(i);
            } else i += 1;
        }
    }
    fn hasValueAlias(self: *const State, va: ValueAlias) bool {
        for (self.value_aliases.items) |e| {
            if ((e.other_path == null) != (va.other_path == null)) continue;
            if (e.other_path) |other|
                if (!std.mem.eql(u8, other, va.other_path.?)) continue;
            if (e.offset == va.offset and std.mem.eql(u8, e.local, va.local) and std.mem.eql(u8, e.path, va.path)) return true;
        }
        return false;
    }
    fn addValueAlias(self: *State, gpa: std.mem.Allocator, va: ValueAlias) !void {
        if (self.hasValueAlias(va)) return;
        try self.value_aliases.append(gpa, va);
    }
    /// Retire relations when a write reaches the result or either source.
    fn dropValueAliasesByRoot(self: *State, root: []const u8) void {
        var i: usize = 0;
        while (i < self.value_aliases.items.len) {
            const va = self.value_aliases.items[i];
            const other_root_match = if (va.other_path) |other| pathRootedAt(other, root) else false;
            if (pathRootedAt(va.local, root) or pathRootedAt(va.path, root) or other_root_match) {
                _ = self.value_aliases.swapRemove(i);
            } else i += 1;
        }
    }
    fn hasScalarVal(self: *const State, sv: ScalarVal) bool {
        for (self.scalar_vals.items) |e|
            if (std.mem.eql(u8, e.name, sv.name) and e.val == sv.val) return true;
        return false;
    }
    fn setScalarVal(self: *State, gpa: std.mem.Allocator, name: []const u8, val: u64) !void {
        self.dropScalarValsByName(name);
        try self.scalar_vals.append(gpa, .{ .name = name, .val = val });
    }
    fn scalarVal(self: *const State, name: []const u8) ?u64 {
        for (self.scalar_vals.items) |e|
            if (std.mem.eql(u8, e.name, name)) return e.val;
        return null;
    }
    /// Drop the constant-value facts of `name` alone.  Recording a value for
    /// one path says nothing about the paths under it, so this stays exact;
    /// invalidation uses `dropScalarValsRootedAt`.
    fn dropScalarValsByName(self: *State, name: []const u8) void {
        var i: usize = 0;
        while (i < self.scalar_vals.items.len) {
            if (std.mem.eql(u8, self.scalar_vals.items[i].name, name)) {
                _ = self.scalar_vals.swapRemove(i);
            } else i += 1;
        }
    }
    /// Drop the constant-value facts a rebinding (or an escaping call) of
    /// `root` invalidates — the ones keyed `root` and the ones keyed by a
    /// path rooted at it, `root.field` and `root.*` among them.
    fn dropScalarValsRootedAt(self: *State, root: []const u8) void {
        var i: usize = 0;
        while (i < self.scalar_vals.items.len) {
            if (pathRootedAt(self.scalar_vals.items[i].name, root)) {
                _ = self.scalar_vals.swapRemove(i);
            } else i += 1;
        }
    }
    fn scalarMinOf(self: *const State, name: []const u8) ?u64 {
        var best: ?u64 = null;
        for (self.scalar_mins.items) |e| {
            if (!std.mem.eql(u8, e.name, name)) continue;
            if (best == null or e.n > best.?) best = e.n;
        }
        return best;
    }
    /// Record `name >= n`, retaining the strongest bound on this path.
    fn setScalarMin(self: *State, gpa: std.mem.Allocator, name: []const u8, n: u64) !void {
        for (self.scalar_mins.items) |*e| {
            if (std.mem.eql(u8, e.name, name)) {
                if (n > e.n) e.n = n;
                return;
            }
        }
        try self.scalar_mins.append(gpa, .{ .name = name, .n = n });
    }
    /// Drop the lower bounds a rebinding (or an escaping call) of `root`
    /// invalidates.  Root-matched rather than name-matched for the reason
    /// `dropScalarValsRootedAt` gives: `p.*` is a fact about what `p` points
    /// at, and `p = other` makes it about something else.
    fn dropScalarMinsRootedAt(self: *State, root: []const u8) void {
        var i: usize = 0;
        while (i < self.scalar_mins.items.len) {
            if (pathRootedAt(self.scalar_mins.items[i].name, root)) {
                _ = self.scalar_mins.swapRemove(i);
            } else {
                i += 1;
            }
        }
    }

    fn minLenOf(self: *const State, path: []const u8) ?u64 {
        var best: ?u64 = null;
        for (self.min_lens.items) |e| {
            if (!std.mem.eql(u8, e.path, path)) continue;
            if (best == null or e.n > best.?) best = e.n;
        }
        return best;
    }
    /// Record `path.len >= n`, raising any existing bound (knowledge only
    /// strengthens within a path).
    fn setMinLen(self: *State, gpa: std.mem.Allocator, path: []const u8, n: u64) !void {
        for (self.min_lens.items) |*e| {
            if (std.mem.eql(u8, e.path, path)) {
                if (n > e.n) e.n = n;
                return;
            }
        }
        try self.min_lens.append(gpa, .{ .path = path, .n = n });
    }
    /// Drop min-length facts whose path is rooted at `root` (mutation of the
    /// container may shrink it — conservative, mirrors container kills).
    fn dropMinLensByRoot(self: *State, root: []const u8) void {
        var i: usize = 0;
        while (i < self.min_lens.items.len) {
            const path = self.min_lens.items[i].path;
            const rooted = std.mem.startsWith(u8, path, root) and
                (path.len == root.len or path[root.len] == '.' or path[root.len] == '[');
            if (rooted) _ = self.min_lens.swapRemove(i) else i += 1;
        }
    }

    /// Read the snapshot, narrowed only by a still-stable true bool selector.
    fn lenBoundOf(self: *const State, name: []const u8) ?NumericRange {
        var bound = self.baselineLenBoundOf(name);
        for (self.conditional_lengths.items) |entry| {
            if (!std.mem.eql(u8, entry.header, name)) continue;
            if (!self.scalars.contains(entry.selector)) continue;
            const held: NumericRange = bound orelse .unknown;
            bound = held.intersect(entry.value);
        }
        return bound;
    }

    /// Joins must not promote a selected branch into the unconditional snapshot.
    fn baselineLenBoundOf(self: *const State, name: []const u8) ?NumericRange {
        for (self.len_bounds.items) |fact| {
            if (std.mem.eql(u8, fact.name, name)) return fact.value;
        }
        return null;
    }

    fn hasConditionalLength(self: *const State, entry: ConditionalLength) bool {
        for (self.conditional_lengths.items) |other| {
            if (std.mem.eql(u8, entry.header, other.header) and
                std.mem.eql(u8, entry.selector, other.selector) and
                std.meta.eql(entry.value, other.value)) return true;
        }
        return false;
    }

    /// Publish a type-proved true-branch extent after assigning its baseline.
    pub fn addConditionalLength(
        self: *State,
        gpa: std.mem.Allocator,
        entry: ConditionalLength,
    ) !void {
        if (entry.value == .unknown or self.hasConditionalLength(entry)) return;
        try self.conditional_lengths.append(gpa, entry);
    }

    /// Changing the selector retires the relation, not the copied header's extent.
    fn dropConditionalLengthsRootedAt(self: *State, root: []const u8) void {
        var index: usize = 0;
        while (index < self.conditional_lengths.items.len) {
            const entry = self.conditional_lengths.items[index];
            if (pathRootedAt(entry.header, root) or pathRootedAt(entry.selector, root)) {
                _ = self.conditional_lengths.swapRemove(index);
            } else index += 1;
        }
    }

    /// Record the range a binding's length was proved to hold.  A second
    /// entry for the same name REPLACES the first rather than merging with
    /// it: two allocations are two different objects, and only the branch
    /// join (`intersectWith`) may widen what both of them admit.
    fn setLenBound(self: *State, gpa: std.mem.Allocator, name: []const u8, range: NumericRange) !void {
        for (self.len_bounds.items) |*fact| {
            if (std.mem.eql(u8, fact.name, name)) {
                fact.value = range;
                return;
            }
        }
        try self.len_bounds.append(gpa, .{ .name = name, .value = range });
    }

    /// Drop every length snapshot rooted at `root` — the entry a write to
    /// `root`, or to anything reached through it, has made stale.  An unknown
    /// range is simply not recorded, so there is nothing here to keep.
    fn dropLenBoundsRootedAt(self: *State, root: []const u8) void {
        var i: usize = 0;
        while (i < self.len_bounds.items.len) {
            if (pathRootedAt(self.len_bounds.items[i].name, root)) {
                _ = self.len_bounds.swapRemove(i);
            } else i += 1;
        }
    }

    pub fn numericValue(self: *const State, name: []const u8) NumericRange {
        for (self.numeric.items) |fact| if (std.mem.eql(u8, fact.name, name)) return fact.value;
        return .unknown;
    }

    /// Record `name`'s range, or withdraw it when there is none.
    ///
    /// An UNKNOWN range is a withdrawal, not a value.  Keeping the entry and
    /// writing `.unknown` into it leaves a standing fact that carries no
    /// claim, which every reader has to special-case and which makes the list
    /// longer than the state it describes; `numericValue` answers `.unknown`
    /// for a name that is absent, `Evaluator.evaluate` skips an `.unknown`
    /// fact and falls back to the declared type, and a join drops an entry the
    /// other branch does not carry either way.  So the entry goes, and what
    /// the name is left with is its DECLARED type — never the range a guard
    /// proved about a value this assignment has just replaced.
    pub fn setNumeric(self: *State, gpa: std.mem.Allocator, name: []const u8, value: NumericRange) !void {
        var index: usize = 0;
        while (index < self.numeric.items.len) {
            if (!std.mem.eql(u8, self.numeric.items[index].name, name)) {
                index += 1;
                continue;
            }
            if (value != .unknown) {
                self.numeric.items[index].value = value;
            } else {
                _ = self.numeric.swapRemove(index);
            }
            return;
        }
        if (value != .unknown) try self.numeric.append(gpa, .{ .name = name, .value = value });
    }

    fn bitAlias(self: *const State, name: []const u8) ?BitAlias {
        for (self.bit_aliases.items) |alias| if (std.mem.eql(u8, name, alias.local)) return alias;
        return null;
    }

    fn hasBitAlias(self: *const State, alias: BitAlias) bool {
        const other = self.bitAlias(alias.local) orelse return false;
        return std.mem.eql(u8, alias.source, other.source) and alias.mask == other.mask and
            alias.float_bits == other.float_bits and alias.union_view == other.union_view and
            alias.absolute == other.absolute;
    }

    fn dropNumericRoot(self: *State, root: []const u8) void {
        var index: usize = 0;
        while (index < self.numeric.items.len) {
            if (pathRootedAt(self.numeric.items[index].name, root)) {
                const removed = self.numeric.swapRemove(index);
                std.debug.assert(pathRootedAt(removed.name, root));
            } else index += 1;
        }
        var bit: usize = 0;
        while (bit < self.bit_aliases.items.len) {
            const alias = self.bit_aliases.items[bit];
            if (pathRootedAt(alias.local, root) or pathRootedAt(alias.source, root)) {
                _ = self.bit_aliases.swapRemove(bit);
            } else bit += 1;
        }
    }
};

const Flow = struct {
    answer: ?bool = null,
    diverged: bool = false,
};

const Query = enum { nonzero_scalar, nonempty_container, min_len_container, positive_expression, numeric_range };

/// States reaching `break` while analyzing one loop.  Multiple breaks join by
/// intersection because every exit must satisfy a fact before it can be used
/// after the loop.
const BreakCapture = struct {
    gpa: std.mem.Allocator,
    state: ?State = null,
    has_unresolved_target: bool = false,

    fn deinit(self: *BreakCapture) void {
        if (self.state) |*state| state.deinit(self.gpa);
    }

    fn record(self: *BreakCapture, source: *const State) error{OutOfMemory}!void {
        var candidate = try source.clone(self.gpa);
        if (self.state) |*state| {
            state.intersectWith(&candidate);
            candidate.deinit(self.gpa);
        } else {
            self.state = candidate;
        }
    }
};

const PredicateCapture = struct {
    gpa: std.mem.Allocator,
    truth: bool,
    state: ?State = null,

    fn deinit(self: *PredicateCapture) void {
        if (self.state) |*state| state.deinit(self.gpa);
    }

    fn record(self: *PredicateCapture, o: *Oracle, expression: Ast.Node.Index, source: *const State) QueryError!void {
        const node = unwrapGrouped(o.tree, expression);
        var literal: ?bool = null;
        if (o.tree.nodeTag(node) == .identifier) {
            const name = o.tree.tokenSlice(o.tree.nodeMainToken(node));
            if (std.mem.eql(u8, name, "true")) literal = true;
            if (std.mem.eql(u8, name, "false")) literal = false;
        }
        if (literal) |value| if (value != self.truth) return;
        var candidate = try source.clone(self.gpa);
        errdefer candidate.deinit(self.gpa);
        if (literal == null) try applyRefine(o, &candidate, .{ .node = node, .truth = self.truth });
        if (self.state) |*state| {
            state.intersectWith(&candidate);
            candidate.deinit(self.gpa);
        } else self.state = candidate;
    }
};

/// What one predicate callee proved about one of its parameters, in the
/// CALLEE's own spelling.  The call site is what maps that spelling onto the
/// storage it handed over, so a contract carries no call-site state and two
/// call sites of one callee under the same truth read exactly the same rows.
const PredicateFact = struct {
    /// The callee's own name for the storage — a parameter, or the `@as`
    /// target that decides whether a float crossed a conversion.
    name: []const u8,
    /// Its position in the callee's parameter list, so the call site can ask
    /// the resolver what it passed there.
    index: usize,
    type_expr: ?Ast.Node.Index,
    bound: NumericRange,
    minimum: ?u64,
    non_empty: bool,
};

/// The contracts this query has already proved, folded once per
/// (callee declaration, truth).
///
/// A predicate call spawns a walk of the CALLEE's body, and the answer that
/// walk reaches depends on the callee's body and on the truth the call site
/// assumed — and on neither the call site nor the caller's own state: the
/// child is seeded from declared types alone (`infer_callers` is off), is
/// walked to no token, and exports one row per parameter.  So the fixpoint this
/// step takes is over CONTRACTS, not over call sites, and taking it there is
/// what keeps a body that calls two predicates from costing their product:
/// the first site in walk order pays for the callee, and every later site of
/// that callee — at any depth, including from inside another callee's walk —
/// reads the rows that walk produced.
///
/// Only a COMPLETE walk is recorded.  A walk that ran out of steps has
/// exported nothing, and recording it would let a later call site with more
/// room read the first one's truncated answer instead of establishing the
/// contract itself; an incomplete walk is simply taken again, at its own
/// cost, which the step budget already bounds.
///
/// Every site still pays its own `spend` and its own charge for the child's
/// allowance, so the step accounting is a function of the source order and of
/// which site came first — not of how many times a body was met.
const PredicateMemo = struct {
    gpa: std.mem.Allocator,
    walked: std.ArrayListUnmanaged(Key) = .empty,
    rows: std.ArrayListUnmanaged(PredicateFact) = .empty,
    aggregate_returns: std.ArrayListUnmanaged(AggregateReturn) = .empty,
    // Integer-only return summaries depend on the whole actual argument
    // vector as well as the call's identity and remaining recursion depth.
    // Store only complete walks; a failed walk never publishes a row.
    numeric_returns: std.ArrayListUnmanaged(NumericReturn) = .empty,
    numeric_arguments: std.ArrayListUnmanaged(numbers.Integer) = .empty,

    /// Root-query keys borrow only root-owned spellings and resolver types.
    /// Nested/inherited contexts compute uncached until their complete entry
    /// context and spelling lifetime can be represented by this owner.
    const AggregateReturn = struct {
        reference: TypeResolver.FunctionReference,
        call: Ast.Node.Index,
        depth: u8,
        numeric: []const numeric_eval.Fact,
        lengths: []const numeric_eval.Fact,
        /// Full mapped actual snapshots distinguish selected branch walks
        /// from the joined interval at the same call node.
        inputs: []const numeric_eval.Fact,
        input_lengths: []const numeric_eval.Fact,
        /// An empty projection names a returned slice itself.
        fields: []numeric_eval.Fact = &.{},
        visiting: bool = true,

        fn matches(self: *const AggregateReturn, reference: TypeResolver.FunctionReference, call: Ast.Node.Index, depth: u8, st: *const State, inputs: []const numeric_eval.Fact, input_lengths: []const numeric_eval.Fact) bool {
            return self.call == call and self.depth == depth and
                self.reference.tree == reference.tree and
                self.reference.fn_token == reference.fn_token and
                self.reference.handle.eql(reference.handle) and
                self.reference.actual_type.eql(reference.actual_type) and
                factsEqual(self.numeric, st.numeric.items) and
                factsEqual(self.lengths, st.len_bounds.items) and
                factsEqual(self.inputs, inputs) and
                factsEqual(self.input_lengths, input_lengths);
        }

        fn factsEqual(a: []const numeric_eval.Fact, b: []const numeric_eval.Fact) bool {
            if (a.len != b.len) return false;
            for (a, b) |left, right| {
                if (!std.mem.eql(u8, left.name, right.name) or
                    !std.meta.eql(left.value, right.value)) return false;
            }
            return true;
        }

        fn deinit(self: *AggregateReturn, gpa: std.mem.Allocator) void {
            gpa.free(self.numeric);
            gpa.free(self.lengths);
            gpa.free(self.inputs);
            gpa.free(self.input_lengths);
            gpa.free(self.fields);
        }
    };

    const NumericReturn = struct {
        reference: TypeResolver.FunctionReference,
        caller: TypeResolver.ResolutionFrame,
        call: Ast.Node.Index,
        depth: u8,
        start: usize,
        count: usize,
        value: NumericRange,
    };

    const Key = struct {
        declaration: Ast.Node.Index,
        truth: bool,
        start: usize,
        count: usize,
    };

    fn deinit(self: *PredicateMemo) void {
        self.walked.deinit(self.gpa);
        self.rows.deinit(self.gpa);
        for (self.aggregate_returns.items) |*entry| entry.deinit(self.gpa);
        self.aggregate_returns.deinit(self.gpa);
        self.numeric_returns.deinit(self.gpa);
        self.numeric_arguments.deinit(self.gpa);
    }

    fn find(self: *const PredicateMemo, declaration: Ast.Node.Index, truth: bool) ?[]const PredicateFact {
        for (self.walked.items) |key| {
            if (key.declaration == declaration and key.truth == truth)
                return self.rows.items[key.start..][0..key.count];
        }
        return null;
    }

    /// Publish the rows `rows.items[start..]` holds for this callee.  The
    /// caller has already appended them, so the table is composed once and
    /// read back by every later site; a key that could not be recorded rolls
    /// the rows back so a half-published contract is never read.
    fn record(self: *PredicateMemo, start: usize, declaration: Ast.Node.Index, truth: bool) error{OutOfMemory}!void {
        self.walked.append(self.gpa, .{
            .declaration = declaration,
            .truth = truth,
            .start = start,
            .count = self.rows.items.len - start,
        }) catch |err| {
            self.rows.shrinkRetainingCapacity(start);
            return err;
        };
    }

    fn findNumericReturn(
        self: *const PredicateMemo,
        reference: TypeResolver.FunctionReference,
        caller: TypeResolver.ResolutionFrame,
        call: Ast.Node.Index,
        depth: u8,
        arguments: []const numeric_eval.Fact,
    ) ?NumericRange {
        for (self.numeric_returns.items) |row| {
            if (row.call != call or row.depth != depth or row.count != arguments.len or
                row.reference.tree != reference.tree or row.reference.fn_token != reference.fn_token or
                !row.reference.handle.eql(reference.handle) or !row.reference.actual_type.eql(reference.actual_type) or
                row.caller.resolver != caller.resolver or !row.caller.handle.eql(caller.handle) or
                !optionalActualTypeEqual(row.caller.actual_type, caller.actual_type) or
                !optionalActualTypeEqual(row.caller.container_type, caller.container_type)) continue;
            var matches = true;
            for (self.numeric_arguments.items[row.start..][0..row.count], arguments) |known, actual| {
                if (actual.value != .integer or known.min != actual.value.integer.min or known.max != actual.value.integer.max) {
                    matches = false;
                    break;
                }
            }
            if (matches) return row.value;
        }
        return null;
    }

    fn recordNumericReturn(
        self: *PredicateMemo,
        reference: TypeResolver.FunctionReference,
        caller: TypeResolver.ResolutionFrame,
        call: Ast.Node.Index,
        depth: u8,
        arguments: []const numeric_eval.Fact,
        value: NumericRange,
    ) error{OutOfMemory}!void {
        const start = self.numeric_arguments.items.len;
        errdefer self.numeric_arguments.shrinkRetainingCapacity(start);
        for (arguments) |argument| try self.numeric_arguments.append(self.gpa, argument.value.integer);
        try self.numeric_returns.append(self.gpa, .{
            .reference = reference,
            .caller = caller,
            .call = call,
            .depth = depth,
            .start = start,
            .count = arguments.len,
            .value = value,
        });
    }

    fn optionalActualTypeEqual(a: ?TypeResolver.ActualType, b: ?TypeResolver.ActualType) bool {
        if (a) |left| return if (b) |right| left.eql(right) else false;
        return b == null;
    }
};

/// What every `return` of one body produces, joined into a single range.
///
/// The join is over ALL of the exits, which is what makes it a claim about the
/// call rather than about one path through the callee: a body whose second
/// return the walk could not evaluate returns a value this cannot describe,
/// so the whole summary is dropped instead of being narrowed by the exit that
/// happened to read first.  `complete` records that every return was
/// accounted for; a body that can also run off its end is rejected by the
/// caller, which is a different way of leaving without a value.
///
/// An exit is read where the STATEMENT stands, and that is the state from
/// BEFORE the return's operand ran.  An operand that runs code leaves a
/// different state behind it, so a fact read off the earlier one describes a
/// value the body need no longer be returning — the two arms of
/// `return if (rewrites(&x)) x else x` both read the value `x` held before
/// `rewrites` handed it something else, and joining them yields a domain of a
/// single value that no exit can produce.  Such an exit is unaccounted for in
/// the same way an unreadable one is.
const ReturnSummary = struct {
    value: ?NumericRange = null,
    complete: bool = true,
    /// In aggregate mode, retain only slice projections present on every
    /// successful return. Error exits do not produce a returned header.
    aggregate: ?*State = null,
    bare_slice: bool = false,
    success_only: bool = false,
    saw_success: bool = false,

    fn record(self: *ReturnSummary, o: *Oracle, expression: Ast.Node.Index, st: *const State) QueryError!void {
        if (self.success_only and o.tree.nodeTag(unwrapGrouped(o.tree, expression)) == .error_value) return;
        if (self.aggregate) |aggregate| {
            const node = unwrapGrouped(o.tree, expression);
            if (!pureAggregateExpression(o, node, 0)) {
                self.complete = false;
                return;
            }
            if (self.bare_slice) {
                if (o.tree.fullSwitch(node)) |selection| {
                    // Join every returned header, not the selector's type.
                    // Purity above rules out effects between those snapshots.
                    for (selection.ast.cases) |case_node| {
                        const case = o.tree.fullSwitchCase(case_node) orelse {
                            self.complete = false;
                            return;
                        };
                        const target = unwrapGrouped(o.tree, case.ast.target_expr);
                        if (o.tree.nodeTag(target) == .unreachable_literal) continue;
                        try self.record(o, target, st);
                    }
                    return;
                }
            }
            var returned: State = .{};
            defer returned.deinit(o.gpa);
            if (self.bare_slice) {
                var evaluation = evaluator(o, st);
                const length: NumericRange = blk: {
                    // Zig parses the ambiguous empty `.{}` as a struct
                    // initializer. This summary already proved a slice
                    // return type, so its anonymous address initializer
                    // describes the zero-element array, not a struct.
                    if (o.tree.nodeTag(node) == .address_of) {
                        const child = unwrapGrouped(o.tree, o.tree.nodeData(node).node);
                        var buffer: [2]Ast.Node.Index = undefined;
                        if (o.tree.fullStructInit(&buffer, child)) |initializer| {
                            if (initializer.ast.type_expr == .none and initializer.ast.fields.len == 0)
                                break :blk NumericRange.constant(0);
                        }
                    }
                    break :blk evaluation.containerLength(node);
                };
                if (length != .unknown) try returned.setLenBound(o.gpa, "", length);
            } else {
                try recordAggregateLengths(o, st, &returned, node, "", 0);
            }
            if (self.saw_success) {
                aggregate.intersectWith(&returned);
            } else {
                aggregate.* = returned;
                returned = .{};
                self.saw_success = true;
            }
            return;
        }
        // A compound operand must run no code: later operands could read
        // state an earlier call changed. A whole forwarded scalar call is
        // different: its own complete return summary accounts for its body,
        // and no caller operand is read after it returns.
        const node = unwrapGrouped(o.tree, expression);
        var buffer: [1]Ast.Node.Index = undefined;
        const bound = if (o.tree.fullCall(&buffer, node) != null)
            // A whole forwarded call has no later operand that could read
            // state it changed. Its scalar arguments must be pure, and its
            // own complete body summary is the only value exported.
            try forwardedReturnRange(o, st, node)
        else blk: {
            if (!pureIntegerExpression(o, expression, 0)) {
                self.complete = false;
                return;
            }
            var value = numericValue(o, st, expression);
            // A successful append or guard can prove a length floor without
            // supplying its upper endpoint. Export that same proven floor
            // with the scalar return, including transparent value casts.
            if (value == .integer) {
                if (exprMin(o, st, expression)) |minimum| {
                    value = value.intersect(.{ .integer = .{
                        .min = @intCast(minimum),
                        .max = value.integer.max,
                    } });
                }
            }
            break :blk value;
        };
        if (bound == .unknown) {
            self.complete = false;
            return;
        }
        self.value = if (self.value) |previous| previous.join(bound) else bound;
    }
};

/// Where a walk's numeric facts are copied out so a caller and its callee
/// can be reasoned about as one walk.  `point` records the state at the one
/// place the query asks about, which is what a callee needs to learn what
/// its callers handed it; `exit` intersects the state of every path that
/// leaves the body, which is what makes a contract the callee exports true
/// for the caller on every path the call can take.
///
/// Joining rather than listing is the point: a fact that holds on only one
/// exit says nothing about the call, and intersecting drops it.
const Capture = struct {
    gpa: std.mem.Allocator,
    mode: Mode,
    state: ?State = null,
    /// Explicit error returns do not reach a propagated call's success edge.
    success_only: bool = false,
    complete: bool = true,

    const Mode = enum { point, exit };

    fn deinit(self: *Capture) void {
        if (self.state) |*state| state.deinit(self.gpa);
    }

    fn record(self: *Capture, source: *const State) error{OutOfMemory}!void {
        // A point capture is one snapshot: the innermost node that answers
        // the query is the last place the walk reached before it stopped.
        if (self.mode == .point and self.state != null) return;
        var candidate = try source.clone(self.gpa);
        errdefer candidate.deinit(self.gpa);
        if (self.state) |*state| {
            state.intersectWith(&candidate);
            candidate.deinit(self.gpa);
        } else self.state = candidate;
    }
};

pub const Oracle = struct {
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    query: Query,
    target: []const u8,
    use_token: Ast.TokenIndex,
    expression: ?Ast.Node.Index = null,
    upper_expression: ?Ast.Node.Index = null,
    /// For `min_len_container`: the threshold N — is `target.len >= N`?
    min_n: u64 = 0,
    /// Optional type engine, used only to confirm a comparison operand is an
    /// UNSIGNED integer (so `key > operand` soundly implies `key >= 1`).  Null
    /// in unit tests → the type-gated `>` generalization simply doesn't apply.
    cache: ?*file_cache_mod.FileCache = null,
    budget: u32 = step_budget,
    /// The step budget this query started with.  Child oracles inherit
    /// the parent's REMAINING steps, so the cap is carried separately
    /// for the diagnostic to report the bound that was in force.
    budget_cap: u32 = step_budget,
    /// The non-step bound that stopped the walk, if any.  Null while the
    /// walk is inside every bound, and while the step counter is what
    /// ran out.
    stopped: ?Stop = null,
    /// Set when a per-file index this walk depends on could not be built for
    /// want of memory.  That is not a bound and not an answer: the walk has
    /// not established anything about the site, so the query reports an
    /// incomplete analysis rather than the `false` it would otherwise return.
    /// A missing-safety proof must never come out of a failed allocation.
    out_of_memory: bool = false,
    /// Nonthrowing format callbacks retain the first exact census failure.
    /// Throwing walk boundaries return it before publishing a result.
    summary_error: ?QueryError = null,
    addressed: KeySet = .{},
    walk_depth: u8 = 0,
    expression_depth: u8 = 0,
    numeric_answer: NumericRange = .unknown,
    /// Extent of the exact queried `call(...).len`, captured before that
    /// call's effects. It describes the returned header, not caller storage.
    queried_return_length: NumericRange = .unknown,
    std_valid: ?bool = null,
    /// The `fn_decl` whose body this walk analyzes, resolved ONCE per query.
    /// Every walk of this file's node array to answer it made the cost of a
    /// query grow with the number of questions it asks — one per pointer-
    /// valued local, one per declared type it reads — and each of those is
    /// itself asked once per expression in the body.  The flag separates
    /// "resolved, and there is none" from "not asked yet"; the node index is
    /// borrowed from the tree, which outlives every oracle.
    fn_decl: ?Ast.Node.Index = null,
    fn_decl_resolved: bool = false,
    /// Whether this file has a root-scope `const std = @import("std");` and
    /// whether this body's own declaration takes a parameter named `std`.
    /// Both are properties of the file and the body, asked once per standard-
    /// library call the walk meets; the second was a whole-file node walk each
    /// time.
    std_imported: ?bool = null,
    std_parameter: ?bool = null,
    /// Every block node of this file, collected once per query and then read
    /// back.  `declaredTypeOf` asks which blocks enclose a token, and it is
    /// asked once per receiver the walk reads a dominating index out of, so
    /// scanning the whole node array per question made a body's cost grow
    /// with its number of reads.
    blocks: std.ArrayListUnmanaged(Ast.Node.Index) = .empty,
    blocks_built: bool = false,
    /// The nodes of this file a whole-file question is ABOUT, in node-array
    /// order, built once per query and read back by every whole-file walk
    /// this oracle spawns.  BORROWED from `nodes_owned`, which owns the
    /// backing list; `nodes` itself owns nothing.  Null here means "not asked
    /// yet", never "found none" — a completed empty index is a published
    /// empty slice, and a build that FAILED sets `out_of_memory` instead.
    nodes: ?[]const Ast.Node.Index = null,
    nodes_owned: std.ArrayListUnmanaged(Ast.Node.Index) = .empty,
    /// Maximum float precision this query has already proved for a
    /// type-parameter reference token.  An ACCELERATOR, never the answer:
    /// a width is proved by the walk that files it, and failing to file one
    /// changes how long the next question takes, not what any of them is
    /// told.  Owned here, so `deinit` releases it with the rest.
    max_float_bits: std.AutoHashMapUnmanaged(Ast.TokenIndex, u16) = .empty,
    /// The escape model's reading of THIS body: the roots whose address it
    /// takes, and the writes that can move a pointer-valued name.  The
    /// lexical half of that is a property of the function, so it is
    /// BORROWED from the file cache when the query has one — the cache
    /// builds it once per fn body and owns it for the snapshot's lifetime,
    /// and every walk of that body reads the same table.
    ///
    /// That is the difference this seam exists for.  `analyzeBody` runs
    /// again for every interprocedural child oracle this query spawns, and
    /// each of those used to walk the file's whole node array twice to
    /// rebuild what the previous one had already derived.
    ///
    /// OWNED by `body_index_owned`, and only there, on the cache-less path:
    /// several unit tests and the `.ptr[0..N]` rule pass no cache at all,
    /// and there is then no per-file owner to borrow from.  Null here means
    /// "not asked yet", never "found none" — a completed index with neither
    /// an address taken nor a pointer binding is a published empty pair.
    body_index: ?*const file_cache_mod.FileCache.EscapeRootIndex = null,
    body_index_owned: ?file_cache_mod.FileCache.EscapeRootIndex = null,
    /// The caller-side spelling of `<container>.len`, the KEY a caller-side
    /// walk recorded a length guard under.  Set only on the child walk that
    /// asks one call site what it held about an argument's length, and read
    /// only in `answerAt`: no node in the file spells `.len` on an argument,
    /// so the key is what the question can be phrased in.  Minted by the
    /// asking step and owned by that oracle, so it outlives the child.
    length_query: ?[]const u8 = null,
    /// Evaluate the argument's extent at the same point, including literals
    /// that have no pathname under which a `.len` guard could be recorded.
    length_expression: bool = false,
    caller_parent: ?*const Oracle = null,
    /// Exact actual callable context for nested return-summary resolution.
    resolution_frame: ?TypeResolver.ResolutionFrame = null,
    infer_callers: bool = true,
    /// The exact call whose error edge the current `try` propagates.
    successful_call: ?Ast.Node.Index = null,
    predicate_capture: ?*PredicateCapture = null,
    /// Where a walk records what every `return` of the body it is walking
    /// produces.  Set only by the step that asks a callee what its exits say;
    /// a walk that was not asked records nothing.
    return_summary: ?*ReturnSummary = null,
    /// Where this walk's numeric facts are copied out for an
    /// interprocedural step.  `point` records the state at the one place
    /// the query asks about; `exit` intersects every state that reaches a
    /// caller, which is what makes a transferred contract hold on every
    /// path the caller can take out of the call.
    capture: ?*Capture = null,
    /// What the CALL SITE held about the storage this body is reached
    /// through, in this body's own spelling.  `applyCallContracts` reads it
    /// off the caller and mints the paths it spells under this body's
    /// parameter names, so nothing here is owned by the callee and nothing
    /// is allocated.  Non-empty means this walk models ONE call, and it is
    /// then not asked about this body's other callers at all: the values
    /// below are that call's own, which for every path both of them speak
    /// about is the narrower of the two claims, and asking anyway would cost
    /// the caller a re-derivation per call site before this body was walked
    /// once.  A walk with none of them below still asks, and takes whatever
    /// the receiver contract proves over its declared domain.
    entry_facts: []const numeric_eval.Fact = &.{},
    /// Copied slice headers at the exact call entry, in parameter spelling.
    entry_lengths: []const numeric_eval.Fact = &.{},
    /// Non-zero while the walk is inside an expression whose call has NOT
    /// run yet — the failing side of `catch`/`orelse`, and the body of a
    /// `defer`/`errdefer`.  A callee's exit contract says what is true
    /// AFTER it returns, so applying one there would claim a fact about a
    /// call that has not happened.
    contract_effects_pending: u8 = 0,
    /// How many contract hops this walk already took.  Bounds the cycle
    /// between two functions that call each other, which the caller chain
    /// does not: a callee asks its callers and its callers ask theirs, and
    /// that chain can lead back here.
    contract_depth: u8 = 0,
    /// The predicate contracts this query has already proved.  BORROWED: a
    /// query entry owns the table for the whole walk and every child oracle
    /// this walk spawns — the callee walks, the caller re-derivations and the
    /// callee scanners — carries the pointer, so a contract proved at any
    /// depth is the same contract everywhere.  No oracle OWNS it, which is why
    /// there is no ownership flag and no second owner to disagree with.
    memo: ?*PredicateMemo = null,
    locals: []const local_bindings.Binding = &.{},
    /// Locals and parameters whose own value is a POINTER.  A path rooted at
    /// one (`*Holder` parameter `h` → `h.data`) is reached indirectly by
    /// every callee the pointer is handed to, and a `const p = &x` binding
    /// hands out the address of `x` the same way.
    pointer_roots: KeySet = .{},
    /// The subset of `pointer_roots` whose value is an ADDRESS (`*T`, `?*T`,
    /// a `&expr` binding): reading `root.field` loads through that address, so
    /// a callee the address is handed to may rewrite the storage behind it.
    /// A slice/array/struct local is NOT here — its header lives in the
    /// binding's own frame slot, which no callee can reach without `&local`
    /// (already covered by `addressed`).  Keeping the two sets apart is what
    /// lets a `const stmts = tree.blockStatements(..)` style by-value slice
    /// keep its proven length across an unrelated call.
    indirection_roots: KeySet = .{},
    /// `const P = &path` bindings, so `f(P)` invalidates what `f(&path)` does.
    escape_aliases: std.ArrayListUnmanaged(numeric_escape.EscapeAlias) = .empty,
    /// Container-path keys spelled `<receiver>.items`.  The `.items` half is
    /// implied by a resolved declaration rather than written at the call site,
    /// so the key cannot be a slice of the source and is owned here for the
    /// whole query — state clones outlive the call that recorded them.
    items_paths: std.ArrayListUnmanaged([]const u8) = .empty,
    /// The call sites of this body's own declaration.  OWNED here for the
    /// whole query, because the slices `callSitesOf` hands out are read by
    /// the step that asked for them after it has walked a caller.
    call_sites: std.ArrayListUnmanaged(Ast.Node.Index) = .empty,
    /// Paths this analysis mints by joining two spellings the source keeps
    /// apart — a callee's name for a parameter and the caller's name for the
    /// storage it names, or an audited element and the field the audit
    /// bounds.  No single token range spells them, and a fact carrying one
    /// outlives the step that recorded it, so this oracle owns them for the
    /// whole query.
    minted_paths: std.ArrayListUnmanaged([]const u8) = .empty,
    /// The file's compile-time container audits, read once per query and
    /// only when something actually draws an element out of a container.
    audits: ?std.ArrayListUnmanaged(ElementAudit) = null,
    /// The root-scope `const` declarations of this file and what each is
    /// initialised to, so a compile-time integer written as a name the file
    /// defines can be followed under that name — a vector block length is
    /// written `const VLEN: usize = 64;`, and the type engine resolves the
    /// expression inside such a binding but not the name around it.
    ///
    /// Read from the file cache's ONE lazily built per-file index and
    /// BORROWED from it, so a file pays for its declarations once rather
    /// than once per anchor.  Nothing here is owned: the slice and every
    /// name in it belong to the source snapshot.
    file_consts: ?numeric_eval.ContainerConsts = null,
    /// This body's numeric facts as they stood right after its parameters were
    /// seeded — what every path INTO the body starts from.  Read only to fill
    /// an exit that left before a later write introduced its key: that exit
    /// holds the entry value, not the type's whole range.
    entry_numeric: std.ArrayListUnmanaged(numeric_eval.Fact) = .empty,

    /// Non-null only while collecting exits of an outer `while (true)`.
    /// Nested loops temporarily disable this pointer so their breaks do not
    /// escape into the enclosing loop.
    break_capture: ?*BreakCapture = null,

    /// The `.items` slice of the container spelled `receiver`, materialized once
    /// per distinct receiver so repeated visits to one call site don't grow
    /// the list.
    fn itemsPath(self: *Oracle, receiver: []const u8) error{OutOfMemory}![]const u8 {
        const suffix = ".items";
        for (self.items_paths.items) |path| {
            if (path.len == receiver.len + suffix.len and std.mem.startsWith(u8, path, receiver)) return path;
        }
        const path = try std.fmt.allocPrint(self.gpa, "{s}{s}", .{ receiver, suffix });
        errdefer self.gpa.free(path);
        try self.items_paths.append(self.gpa, path);
        return path;
    }

    pub fn tokenInNode(self: *Oracle, node: Ast.Node.Index) bool {
        return self.use_token >= self.tree.firstToken(node) and
            self.use_token <= self.tree.lastToken(node);
    }
    pub fn spend(self: *Oracle) bool {
        if (self.budget == 0) {
            // Name the bound here too: a walk that has run out of steps
            // keeps unwinding, and without this a later depth guard
            // could be reported as the reason the query failed.
            self.giveUp(.{ .limit = .numeric_oracle_steps, .cap = self.budget_cap });
            return false;
        }
        self.budget -= 1;
        return true;
    }
    /// Stop the walk and name the bound that stopped it.  First stop
    /// wins: a walk that gives up keeps unwinding and may trip further
    /// bounds, but the first one is the one that explains the rest.
    pub fn giveUp(self: *Oracle, stop: Stop) void {
        self.budget = 0;
        if (self.stopped == null) self.stopped = stop;
    }
    /// Did a bound actually stop this walk?
    ///
    /// The step COUNTER cannot answer that: `spend` consumes the last
    /// available step and returns, so a walk that finishes its work on that
    /// step ends with `budget == 0` and nothing wrong.  Only a bound that
    /// was hit sets `stopped`, which is what a query entry has to test
    /// before it answers from a body it did not finish walking.
    fn stoppedShort(self: *const Oracle) bool {
        return self.stopped != null;
    }
    /// Read a projected length from every channel that records that SAME
    /// header: a guard on `.len`, an inherited/allocated length, or an exact
    /// scalar snapshot. Rebinding either half retires the snapshot alias.
    fn lengthValueAt(self: *Oracle, st: *const State, key: []const u8) NumericRange {
        const container = key[0 .. key.len - ".len".len];
        var bound = st.numericValue(key).intersect(st.lenBoundOf(container) orelse .unknown);
        for (st.aliases.items) |alias| {
            if (!self.spend()) return .unknown;
            if (!std.mem.eql(u8, alias.container, container)) continue;
            bound = bound.intersect(st.numericValue(alias.scalar));
        }
        return bound;
    }

    fn answerAt(self: *Oracle, st: *const State) bool {
        // A point capture reads the state as it stands where the query is
        // answered.  Failing to copy it is not a wrong answer: the caller
        // step that wanted it sees no capture and records nothing.
        if (self.capture) |capture| {
            if (capture.mode == .point) capture.record(st) catch {};
        }
        return switch (self.query) {
            .numeric_range => {
                // A length question evaluates the actual container at this point.
                // A named header additionally reads its guards and scalar aliases.
                self.numeric_answer = if (self.length_expression) blk: {
                    var evaluation = evaluator(self, st);
                    var length = evaluation.containerLength(self.expression.?);
                    if (self.length_query) |key|
                        length = length.intersect(self.lengthValueAt(st, key));
                    break :blk length;
                } else blk: {
                    const expression = self.expression.?;
                    const spelled = numericValue(self, st, expression);
                    // A callee summary narrows a known integer domain. It
                    // cannot establish the value kind of an unknown operand.
                    if (spelled != .integer) break :blk spelled;
                    const returned = callReturnRange(self, st, expression) catch |err| {
                        self.summary_error = self.summary_error orelse err;
                        return false;
                    };
                    var result = spelled.intersect(returned).intersect(self.queried_return_length);
                    // Lower-bound and numeric facts describe the same value.
                    // Checked addition can retain a floor even when its full
                    // interval was widened for possible overflow.
                    if (result == .integer) {
                        if (exprMin(self, st, expression)) |floor| {
                            result = result.intersect(.{ .integer = .{
                                .min = @intCast(floor),
                                .max = result.integer.max,
                            } });
                        }
                    }
                    break :blk result;
                };
                if (self.upper_expression) |upper| return strictlyLessAt(self, st, upper);
                return true;
            },
            .positive_expression => expressionPositive(self, st, self.expression.?),
            .nonzero_scalar => st.scalars.contains(self.target) or
                (st.scalarMinOf(self.target) orelse 0) >= 1,
            .nonempty_container => containerProvenNonEmpty(self.tree, st, self.target),
            // Minimum extents read the same initializer/return snapshots as
            // numeric length queries, not a live scalar endpoint after a write.
            .min_len_container => {
                // (a) a `target.len >= N` guard refinement (N >= min_n).
                if (st.minLenOf(self.target)) |v| if (v >= self.min_n) return true;
                if (st.lenBoundOf(self.target)) |bound| {
                    if (bound == .integer and bound.integer.min >= self.min_n) return true;
                }
                // min_n <= 1 is just "non-empty" — honor a plain nonempty fact.
                if (self.min_n <= 1 and st.containers.contains(self.target)) return true;
                // (b) a slice-length alias (`target.len == scalar`) whose
                // scalar has a known constant value >= min_n (switch arm).
                for (st.aliases.items) |a| {
                    if (!std.mem.eql(u8, a.container, self.target)) continue;
                    if (st.scalarVal(a.scalar)) |v| if (v >= self.min_n) return true;
                }
                return false;
            },
        };
    }
    /// An oracle owns the key sets it collects (`addressed`, `pointer_roots`,
    /// `indirection_roots`), the pointer-target map (`escape_aliases`), the
    /// tables it read (`items_paths`, `minted_paths`, `audits`), its block
    /// index (`blocks`), and — on the cache-less path only — the node index it
    /// built for itself (`nodes_owned`).  Every value must release all of them,
    /// so the cleanup belongs to the struct.  `nodes` and `file_consts` are NOT
    /// among them: both are BORROWED from the file cache, which owns them until
    /// the file is torn down.
    pub fn deinit(self: *Oracle) void {
        self.addressed.deinit(self.gpa);
        self.pointer_roots.deinit(self.gpa);
        self.indirection_roots.deinit(self.gpa);
        self.escape_aliases.deinit(self.gpa);
        for (self.items_paths.items) |path| self.gpa.free(path);
        self.items_paths.deinit(self.gpa);
        for (self.minted_paths.items) |path| self.gpa.free(path);
        self.minted_paths.deinit(self.gpa);
        if (self.audits) |*audits| {
            for (audits.items) |audit| {
                self.gpa.free(audit.container);
                self.gpa.free(audit.field);
            }
            audits.deinit(self.gpa);
        }
        self.blocks.deinit(self.gpa);
        // The borrowed slice owns nothing; only the cache-less fallback's
        // backing list does.
        self.nodes_owned.deinit(self.gpa);
        // Same split as `nodes`: the cache's own index owns nothing this
        // value can free, and only the cache-less fallback's copy is ours —
        // both of its backing slices were minted with this gpa.
        if (self.body_index_owned) |*owned| {
            self.gpa.free(owned.addressed);
            self.gpa.free(owned.writes);
        }
        self.entry_numeric.deinit(self.gpa);
        self.call_sites.deinit(self.gpa);
        self.max_float_bits.deinit(self.gpa);
    }
};

/// Is unsigned scalar `target` provably != 0 at `use_token`?  `cache` (optional)
/// supplies the type engine for the unsigned-operand `>` generalization.
pub fn provesNonzero(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body_node: Ast.Node.Index,
    target: []const u8,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
) QueryError!bool {
    return run(gpa, tree, body_node, .nonzero_scalar, target, use_token, 0, cache, null);
}

/// Is container `target` (a source-spelling like "arr" or "self.items")
/// provably non-empty (len >= 1) at `use_token`?
pub fn provesNonempty(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body_node: Ast.Node.Index,
    target: []const u8,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
) QueryError!bool {
    return run(gpa, tree, body_node, .nonempty_container, target, use_token, 0, cache, null);
}

/// Is container `target` provably of length >= `n` at `use_token`?
/// Reads guard minima, fixed/static extents, and initializer/return length
/// intervals. Slice extents are snapshots: later endpoint writes cannot
/// enlarge an old slice, and header writes retire the old extent.
pub fn provesMinLen(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body_node: Ast.Node.Index,
    target: []const u8,
    n: u64,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
) QueryError!bool {
    return run(gpa, tree, body_node, .min_len_container, target, use_token, n, cache, null);
}

/// Is an index operand positive on every path reaching this use?
pub fn provesPositive(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    expression: Ast.Node.Index,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
) QueryError!bool {
    return run(gpa, tree, body, .positive_expression, "", use_token, 0, cache, expression);
}

/// Numeric bounds on every path reaching the expression. Unknown is not safe.
///
/// A direct call with a known integer kind intersects its declared domain
/// with the canonical callee return summary. Unknown value kinds stay unknown.
pub fn boundsAt(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    expression: Ast.Node.Index,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
) QueryError!NumericRange {
    var remaining: u32 = step_budget;
    return boundsAtFrame(gpa, tree, body, expression, use_token, cache, null, &remaining);
}

/// Bounds in one concrete generic instance. All instances of one conversion
/// share the ordinary query allowance; contextual walks do not borrow facts
/// computed in the uninstantiated declaration.
fn boundsAtFrame(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    expression: Ast.Node.Index,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
    frame: ?TypeResolver.ResolutionFrame,
    remaining: *u32,
) QueryError!NumericRange {
    var memo: PredicateMemo = .{ .gpa = gpa };
    defer memo.deinit();
    var oracle: Oracle = .{
        .gpa = gpa,
        .tree = tree,
        .body = body,
        .query = .numeric_range,
        .target = "",
        .use_token = use_token,
        .memo = &memo,
        .expression = expression,
        .cache = cache,
        .resolution_frame = frame,
        .infer_callers = frame == null,
        .budget = remaining.*,
    };
    defer oracle.deinit();
    defer remaining.* = oracle.budget;
    const flow = try analyzeBody(&oracle);
    if (oracle.out_of_memory) return error.OutOfMemory;
    // A bound that stopped the walk outranks whatever the walk had reached:
    // the range below would describe the paths the walk did get to, not the
    // ones reaching the use.  The step counter cannot decide this: `spend`
    // consumes the last available step and returns, so a walk that finishes
    // its work on that step leaves the counter at zero without having failed.
    if (oracle.stoppedShort()) return reportGiveUp(&oracle);
    if (flow.answer == null) return .unknown;
    return oracle.numeric_answer;
}

/// Classify a generic float conversion only when every closed local call
/// supplies a resolved destination. A mixed set still includes an f32 site
/// when any instance uses f32; other formats remain outside this rule's scope.
pub fn closedFloatConversionUsesF32(
    tree: *const Ast,
    declaration: Ast.Node.Index,
    conversion: Ast.Node.Index,
    cache: *file_cache_mod.FileCache,
) QueryError!?bool {
    const resolver = cache.zls orelse return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
    if (proto.visib_token != null or proto.extern_export_inline_token != null) return null;
    const calls = (try cache.closedLocalCalls(declaration)) orelse return null;
    if (calls.len == 0) return null;
    const token = tree.nodeMainToken(conversion);
    if (calls.len > max_contract_calls)
        return file_cache_mod.tokenBudgetFailure(tree, token, .numeric_oracle_callers, max_contract_calls);
    var uses_f32 = false;
    for (calls) |call| {
        const reference = switch (resolver.functionReferenceOfCall(call) catch |err| {
            if (strictQueryError(err)) |failure| return failure;
            return null;
        }) {
            .function => |found| found,
            else => return null,
        };
        if (reference.tree != tree or reference.fn_token != proto.ast.fn_token) return null;
        const bits = (resolver.frameForFunction(reference).floatBits(conversion) catch |err| {
            if (strictQueryError(err)) |failure| return failure;
            return null;
        }) orelse return null;
        uses_f32 = uses_f32 or bits == 32;
    }
    return uses_f32;
}

/// Prove a conversion for every closed local instantiation. Integer
/// destinations need an in-range source; f32 destinations need exact integers.
/// Each range and destination come from the same actual frame.
pub fn instantiatedConversionFits(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    declaration: Ast.Node.Index,
    conversion: Ast.Node.Index,
    expression: Ast.Node.Index,
    cache: *file_cache_mod.FileCache,
) QueryError!bool {
    const resolver = cache.zls orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
    if (proto.visib_token != null or proto.extern_export_inline_token != null) return false;
    const builtin = tree.tokenSlice(tree.nodeMainToken(conversion));
    const to_float = std.mem.eql(u8, builtin, "@floatFromInt");
    if (!to_float and !std.mem.eql(u8, builtin, "@intFromFloat")) return false;
    var parameters = proto.iterate(tree);
    var generic = false;
    while (parameters.next()) |parameter| {
        if (parameter.type_expr == null or
            (parameter.comptime_noalias != null and tree.tokenTag(parameter.comptime_noalias.?) == .keyword_comptime))
            generic = true;
    }
    // A nongeneric method can still capture a generic container's format.
    if (!generic and !to_float) return false;
    const calls = (try cache.closedLocalCalls(declaration)) orelse return false;
    if (calls.len == 0) return false;
    const token = tree.nodeMainToken(conversion);
    if (calls.len > max_contract_calls)
        return file_cache_mod.tokenBudgetFailure(tree, token, .numeric_oracle_callers, max_contract_calls);
    var remaining: u32 = step_budget;
    var instances_remaining: usize = max_contract_calls;
    for (calls) |call| {
        var single: [1]TypeResolver.FunctionReference = undefined;
        const references = (resolver.resolutionFrame().inlineTupleCallReferences(call, &remaining, &instances_remaining) catch |err| {
            if (err == error.InlineTupleStepsExceeded)
                return file_cache_mod.tokenBudgetFailure(tree, token, .numeric_oracle_steps, step_budget);
            if (err == error.InlineTupleCallersExceeded)
                return file_cache_mod.tokenBudgetFailure(tree, token, .numeric_oracle_callers, max_contract_calls);
            if (strictQueryError(err)) |failure| return failure;
            return false;
        }) orelse blk: {
            if (instances_remaining == 0)
                return file_cache_mod.tokenBudgetFailure(tree, token, .numeric_oracle_callers, max_contract_calls);
            instances_remaining -= 1;
            single[0] = switch (resolver.functionReferenceOfCall(call) catch |err| {
                if (strictQueryError(err)) |failure| return failure;
                return false;
            }) {
                .function => |found| found,
                else => return false,
            };
            break :blk &single;
        };
        for (references) |reference| {
            if (remaining == 0)
                return file_cache_mod.tokenBudgetFailure(tree, token, .numeric_oracle_steps, step_budget);
            remaining -= 1;
            if (reference.tree != tree or reference.fn_token != proto.ast.fn_token) return false;
            const frame = resolver.frameForFunction(reference);
            if (to_float) {
                const bits = (frame.floatBits(conversion) catch |err| {
                    if (strictQueryError(err)) |failure| return failure;
                    return false;
                }) orelse return false;
                // Other resolved float widths are outside the f32 rule's scope.
                if (bits != 32) continue;
                const bounds = try boundsAtFrame(gpa, tree, tokens.bodyOf(tree, declaration).?, expression, token, cache, frame, &remaining);
                if (!bounds.exactInF32()) return false;
            } else {
                const destination = (frame.contextIntInfo(conversion) catch |err| {
                    if (strictQueryError(err)) |failure| return failure;
                    return false;
                }) orelse return false;
                const bounds = try boundsAtFrame(gpa, tree, tokens.bodyOf(tree, declaration).?, expression, token, cache, frame, &remaining);
                if (!bounds.fitsInteger(destination.bits, destination.signed)) return false;
            }
        }
    }
    return true;
}

/// Is `lower < upper` true on every path reaching `use_token`?
///
/// The cache is OPTIONAL, exactly as it is on the five sibling queries, and
/// that is the honest shape of what this needs.  A type engine supplies the
/// declared types and the unsigned-domain reading; without one the query
/// declines any operand whose SIGN it cannot establish — which is the
/// conservative direction — but it is not a bare `false` for everything.  Two
/// integer literals need no type at all: `0 < 1` is decided by the evaluator's
/// own constants before any type is consulted, and so is any comparison whose
/// two ranges the walk already proved disjoint.
pub fn provesLessThan(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    lower: Ast.Node.Index,
    upper: Ast.Node.Index,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
) QueryError!bool {
    var memo: PredicateMemo = .{ .gpa = gpa };
    defer memo.deinit();
    var oracle: Oracle = .{
        .gpa = gpa,
        .tree = tree,
        .body = body,
        .query = .numeric_range,
        .target = "",
        .use_token = use_token,
        .expression = lower,
        .upper_expression = upper,
        .cache = cache,
        .memo = &memo,
    };
    defer oracle.deinit();
    // The pre-walk is part of the query: it decides whether either operand is
    // an integer expression at all, before the body is walked once.  A
    // pre-walk that stopped short has not shown the comparison to be
    // unprovable — it has failed to look — so it reports the bound that
    // stopped it instead of a plain `false`.
    if (!pureIntegerExpression(&oracle, lower, 0) or
        !pureIntegerExpression(&oracle, upper, 0))
    {
        if (oracle.out_of_memory) return error.OutOfMemory;
        if (oracle.stoppedShort()) return reportGiveUp(&oracle);
        return false;
    }
    const flow = try analyzeBody(&oracle);
    if (oracle.out_of_memory) return error.OutOfMemory;
    if (oracle.stoppedShort()) return reportGiveUp(&oracle);
    return flow.answer orelse false;
}

/// The walk stopped short of a complete answer.  Report which bound
/// stopped it through the shared channel, so the file is summarized as
/// incomplete instead of a half-answered query being filed next to the
/// findings that WERE checked.
fn reportGiveUp(o: *Oracle) budget_mod.BudgetError {
    var name: budget_mod.NameBuf = .{};
    if (enclosingFnDecl(o)) |declaration| {
        var buffer: [1]Ast.Node.Index = undefined;
        if (tokens.fnProto(o.tree, &buffer, declaration)) |proto| {
            if (proto.name_token) |name_token| name.set(o.tree.tokenSlice(name_token));
        }
    }
    const starts = o.tree.tokens.items(.start);
    const byte: u32 = if (o.use_token < starts.len) @intCast(starts[o.use_token]) else 0;
    const site = budget_mod.lineCol(o.tree.source, byte);
    // Every path that calls this has a bound in hand, so the fallback is
    // unreachable in practice and only keeps the function total.  It names
    // the step budget because that is the bound a spent walk is inside; a
    // wrong name here would send the reader after a limit the analyzer never
    // enforced.
    const stop = o.stopped orelse Stop{ .limit = .numeric_oracle_steps, .cap = o.budget_cap };
    return budget_mod.fail(.{
        .limit = stop.limit,
        .limit_value = stop.cap,
        // Every bound in this module is checked before it is used, so a
        // walk that stopped did so exactly at its cap: the spent step
        // counter reads 0, and a depth or round cap reads its own bound.
        .reached = stop.cap,
        .byte = byte,
        .document = budget_mod.documentForTree(o.tree),
        .line = site.line,
        .column = site.column,
        .function = name,
    });
}

fn strictlyLessAt(o: *Oracle, st: *const State, upper: Ast.Node.Index) bool {
    const lower = o.expression.?;
    const left = o.numeric_answer;
    const right = numericValue(o, st, upper);
    if (left == .integer and right == .integer and left.integer.max < right.integer.min)
        return true;
    const cache = o.cache orelse return false;
    if (left != .integer and cache.intInfoOf(lower) == null) return false;
    if (right != .integer and cache.intInfoOf(upper) == null) return false;
    for (st.predicates.items) |predicate| {
        if (!o.spend()) return false;
        const tag = o.tree.nodeTag(predicate.node);
        const forward = (tag == .less_than and predicate.truth) or
            (tag == .greater_or_equal and !predicate.truth);
        const reverse = (tag == .greater_than and predicate.truth) or
            (tag == .less_or_equal and !predicate.truth);
        if (!forward and !reverse) continue;
        const operands = o.tree.nodeData(predicate.node).node_and_node;
        const a = if (forward) operands[0] else operands[1];
        const b = if (forward) operands[1] else operands[0];
        if (sameExpression(o.tree, unwrapGrouped(o.tree, a), unwrapGrouped(o.tree, lower)) and
            sameExpression(o.tree, unwrapGrouped(o.tree, b), unwrapGrouped(o.tree, upper))) return true;
    }
    return false;
}

/// The evaluator every numeric read of this walk goes through, wired to the
/// walk's own step counter and stop record.  Sharing both is what keeps a
/// depth stop inside an expression from being reported as a cost problem:
/// the evaluator writes the bound it hit into the same record the statement
/// walk does, so whichever ran out is the one the diagnostic names.
fn evaluator(o: *Oracle, st: *const State) numeric_eval.Evaluator {
    if (o.std_valid == null) o.std_valid = stdBindingValidAt(o, o.use_token);
    return .{
        .tree = o.tree,
        .cache = o.cache,
        .resolution_frame = o.resolution_frame,
        .facts = st.numeric.items,
        .budget = &o.budget,
        .budget_cap = o.budget_cap,
        .stopped = &o.stopped,
        .query_error = &o.summary_error,
        .std_valid = o.std_valid.?,
        .container_consts = o.file_consts,
        .len_bounds = st.len_bounds.items,
        .length_bounds = .{ .context = st, .bound = stateLengthBound },
        .float_formats = .{ .context = o, .bounds = genericFloatFormats },
    };
}

fn stateLengthBound(context: *const anyopaque, name: []const u8) ?NumericRange {
    const st: *const State = @ptrCast(@alignCast(context));
    return st.lenBoundOf(name);
}

fn genericFloatFormats(context: *anyopaque, node: Ast.Node.Index) ?numeric_eval.Evaluator.FloatFormats {
    const o: *Oracle = @ptrCast(@alignCast(context));
    const minimum = computedFloatBitsAtDepth(o, node, 0, .minimum) orelse return null;
    const maximum = computedFloatBitsAtDepth(o, node, 0, .maximum) orelse return null;
    return .{ .minimum = minimum, .maximum = maximum };
}

fn numericValue(o: *Oracle, st: *const State, node: Ast.Node.Index) NumericRange {
    var evaluation = evaluator(o, st);
    return evaluation.evaluate(node);
}

fn numericAssignment(o: *Oracle, st: *const State, source: Ast.Node.Index, destination: Ast.Node.Index) QueryError!NumericRange {
    if (o.query != .numeric_range and o.query != .min_len_container) return .unknown;
    var evaluation = evaluator(o, st);
    // The outer @floatCast takes its format from the store. Its own node
    // may have no resolved result location in a generic body, so evaluate
    // its operand here and round once at the actual destination. Inner
    // casts still go through the evaluator and keep their own rounding.
    var operand = unwrapGrouped(o.tree, source);
    var buffer: [2]Ast.Node.Index = undefined;
    if (o.tree.builtinCallParams(&buffer, operand)) |arguments| {
        if (arguments.len == 1 and
            std.mem.eql(u8, o.tree.tokenSlice(o.tree.nodeMainToken(operand)), "@floatCast"))
            operand = arguments[0];
    }
    // A returned range and the spelled range describe the same value.
    const spelled = evaluation.evaluate(operand);
    const returned = try callReturnRange(o, st, source);
    return evaluation.coerce(spelled.intersect(returned), operand, destination);
}

/// The range a binding is left with once a store has landed on it.
///
/// What the walk could READ off the right-hand side is the answer whenever it
/// read one.  When it could not, the store has still replaced the value, so
/// the whole of what a guard proved about the OLD value is gone — and keeping
/// that bound would be the worst of the two answers, because a stale interval
/// is a claim about a value the store has already replaced.
///
/// What is left is the DECLARED domain: `var x: u8 = 200; x = opaque();` puts
/// `x` back inside `0..255` and never inside `200..200`, and
/// `var x: u8 = opaque(); if (x > 250) …` still has a guard worth reading
/// because the TYPE says `x - 1` cannot wrap for any `x` above 250.  A binding
/// with no type the walk can read has no domain to fall back to, and an entry
/// whose value is `.unknown` is not recorded at all — the withdrawal
/// `setNumeric` already performs, which leaves the reader to answer from the
/// declared type itself.  Nothing here turns an UNKNOWN into a specific fact:
/// the fallback is a type, never the interval the guard had recorded.
fn assignedRange(
    o: *Oracle,
    st: *const State,
    name: []const u8,
    computed: NumericRange,
    at: Ast.TokenIndex,
    destination: Ast.Node.Index,
) NumericRange {
    if (computed != .unknown) return computed;
    var evaluation = evaluator(o, st);
    const written = evaluation.typeRange(destination);
    if (written != .unknown) return written;
    // A field or element the type engine cannot reach is still typed by the
    // BINDING the store wrote through, and that binding's own declaration is
    // read here by token position rather than by the type engine.
    const declared = declaredTypeOf(o, name, at) orelse return .unknown;
    const read = evaluation.typeRange(declared);
    if (read != .unknown) return read;
    // No type engine: a type SPELLED as `u8`, `i32` or `usize` is still the
    // whole of what it admits, and reading it from the spelling is a fact
    // about the type rather than about the value.  Anything else — an alias, a
    // named constant, `isize` whose width is not written down — answers
    // nothing and the fact is withdrawn.
    return spelledIntegerDomain(o, declared);
}

/// The whole domain of an integer type written out as a type name.
///
/// This is the one reading that needs no resolver, and it is deliberately a
/// SPELLING reading: `u8` and `i32` say exactly what they admit, `usize` is the
/// 64-bit domain on every platform this analyzer reads, and `isize` says only
/// "pointer-sized", which is not an integer this can name.  A type written any
/// other way answers nothing, because guessing at an alias would be a claim
/// about a value the source never described.
fn spelledIntegerDomain(o: *Oracle, type_node: Ast.Node.Index) NumericRange {
    const tree = o.tree;
    const name = identName(tree, type_node) orelse return .unknown;
    if (std.mem.eql(u8, name, "usize")) {
        // The whole 64-bit domain, and the same interval the `u64` spelling
        // builds below.  `std.math.maxInt(i64)` is only half of what a 64-bit
        // `usize` admits, so a range that quietly stops at 2^63 is a fact the
        // type does not have; it shows up downstream as a narrowing
        // conversion to `u63` — or to any narrower signed type — reading as
        // proved on a value that can be 2^63.  The interval is `i128`, so the
        // upper half is representable and costs nothing to keep.
        return .{ .integer = .{ .min = 0, .max = (@as(i128, 1) << 64) - 1 } };
    }
    if (name.len < 2 or (name[0] != 'u' and name[0] != 'i')) return .unknown;
    const bits = std.fmt.parseUnsigned(u16, name[1..], 10) catch return .unknown;
    if (bits == 0 or bits > 64) return .unknown;
    if (name[0] == 'u') return .{ .integer = .{ .min = 0, .max = (@as(i128, 1) << @intCast(bits)) - 1 } };
    const limit = (@as(i128, 1) << @intCast(bits - 1)) - 1;
    return .{ .integer = .{ .min = -limit - 1, .max = limit } };
}

fn refineNumeric(o: *Oracle, st: *State, node: Ast.Node.Index, truth: bool) error{OutOfMemory}!void {
    var evaluation = evaluator(o, st);
    const constraints = numeric_eval.refine(&evaluation, node, truth);
    for (constraints) |constraint| {
        const value = constraint orelse continue;
        if (numeric_eval.path(o.tree, value.node)) |name| try st.setNumeric(o.gpa, name, st.numericValue(name).intersect(value.value));
        try propagateSubtractionBound(o, st, value.node, value.value);
        const alias = bitAliasOf(o, st, value.node, 0) orelse continue;
        if (alias.union_view) continue;
        const bound = numbers.ieeeFloatRange(alias.float_bits, alias.mask, value.value, alias.absolute);
        if (bound != .unknown) try st.setNumeric(o.gpa, alias.source, st.numericValue(alias.source).intersect(bound));
    }
    try propagateNumericAliases(o, st);
}

/// What a bound on an UNSIGNED subtraction says about the operand being
/// subtracted.
///
/// `minuend - subtrahend` TRAPS when the subtrahend is the larger of the two,
/// so on every path that reaches the expression `subtrahend <= minuend`.  A
/// guard that bounds the difference therefore bounds what is being subtracted
/// by the minuend — which is what turns a "would not grow past the ceiling"
/// check into a ceiling on the container itself, the fact the caller reads
/// after the call.  It is the subtrahend that moves, so the bound is recorded
/// on it and never on the difference.
///
/// The trap is the WHOLE of that argument, so only the operator that has it is
/// read here.  `x -% y` is WRAPPING: it is defined for every pair, so a
/// completed subtraction constrains nothing.  `x -% y` with `x = 0` and
/// `y = 16777217` yields a wrapped value instead of trapping, and deriving
/// `y <= x` from it would bound `y` by a minuend it was never under — which is
/// the opposite of what a rule reads this for.  A later revision that wanted
/// the wrap would have to carry the no-trap precondition itself, not borrow the
/// checked operator's.
///
/// Signed arithmetic is excluded: there the difference may be negative and
/// says nothing about the order of its operands.
fn propagateSubtractionBound(o: *Oracle, st: *State, node: Ast.Node.Index, bound: NumericRange) error{OutOfMemory}!void {
    if (bound != .integer or bound.integer.min < 0) return;
    const tree = o.tree;
    const expression = unwrapGrouped(tree, node);
    switch (tree.nodeTag(expression)) {
        .sub => {},
        else => return,
    }
    const cache = o.cache orelse return;
    const info = cache.intInfoOf(expression) orelse return;
    if (info.signed) return;
    const operands = tree.nodeData(expression).node_and_node;
    const minuend = unwrapGrouped(tree, operands[0]);
    const subtrahend = unwrapGrouped(tree, operands[1]);
    const name = numeric_eval.path(tree, subtrahend) orelse return;
    const upper = numericValue(o, st, minuend);
    if (upper != .integer) return;
    const reached: NumericRange = .{ .integer = .{ .min = 0, .max = upper.integer.max } };
    try st.setNumeric(o.gpa, name, st.numericValue(name).intersect(reached));
}

fn propagateNumericAliases(o: *Oracle, st: *State) error{OutOfMemory}!void {
    for (0..alias_fold_rounds) |_| {
        var changed = false;
        for (st.value_aliases.items) |alias| {
            if (!o.spend()) return;
            const local = st.numericValue(alias.local);
            const source = st.numericValue(alias.path);
            if (alias.other_path != null) {
                if (local != .integer or local.integer.max < 0) continue;
                const underlying = source.intersect(.{ .integer = .{
                    .min = 0,
                    .max = local.integer.max,
                } });
                if (!std.meta.eql(source, underlying)) {
                    try st.setNumeric(o.gpa, alias.path, underlying);
                    changed = true;
                }
                continue;
            }
            const common = local.intersect(offsetRange(source, @intCast(alias.offset)));
            if (common == .unknown) continue;
            if (!std.meta.eql(local, common)) {
                try st.setNumeric(o.gpa, alias.local, common);
                changed = true;
            }
            const underlying = source.intersect(offsetRange(common, -@as(i128, alias.offset)));
            if (!std.meta.eql(source, underlying)) {
                try st.setNumeric(o.gpa, alias.path, underlying);
                changed = true;
            }
        }
        if (!changed) return;
    }
    o.giveUp(.{ .limit = .numeric_oracle_fold, .cap = alias_fold_rounds });
}

fn offsetRange(value: NumericRange, offset: i128) NumericRange {
    if (offset == 0) return value;
    if (value != .integer) return .unknown;
    return .{ .integer = .{
        .min = std.math.add(i128, value.integer.min, offset) catch return .unknown,
        .max = std.math.add(i128, value.integer.max, offset) catch return .unknown,
    } };
}

fn pureCallInputs(o: *Oracle, call: Ast.full.Call) bool {
    if (!pureIntegerExpression(o, call.ast.fn_expr, 0)) return false;
    for (call.ast.params) |argument| if (!pureIntegerExpression(o, argument, 0)) return false;
    return true;
}

fn refinePredicateOutcome(o: *Oracle, st: *State, original: Predicate, depth: u8) QueryError!void {
    if (depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return;
    }
    if (!o.spend()) return;
    const node = unwrapGrouped(o.tree, original.node);
    switch (o.tree.nodeTag(node)) {
        .bool_not => try refinePredicateOutcome(o, st, .{
            .node = o.tree.nodeData(node).node,
            .truth = !original.truth,
        }, depth + 1),
        .bool_and, .bool_or => |tag| {
            if ((tag == .bool_and) != original.truth) return;
            const parts = o.tree.nodeData(node).node_and_node;
            if (pureIntegerExpression(o, parts[1], 0))
                try refinePredicateOutcome(o, st, .{ .node = parts[0], .truth = original.truth }, depth + 1);
            try refinePredicateOutcome(o, st, .{ .node = parts[1], .truth = original.truth }, depth + 1);
        },
        .call, .call_comma, .call_one, .call_one_comma => {
            try refinePredicateCall(o, st, node, original.truth);
            try propagateNumericAliases(o, st);
        },
        // A plain comparison is itself a proved outcome: `!(a or b)` knows BOTH
        // `!a` and `!b`, and before `addStablePredicates` walked both operands
        // only one of them was ever constrained.  `numeric_eval.refine` ignores
        // any node that is not a comparison or a call, so this cannot invent
        // facts elsewhere.
        else => try refineNumeric(o, st, node, original.truth),
    }
}

fn purePredicateBody(o: *Oracle, node: Ast.Node.Index, depth: u8) bool {
    if (depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return false;
    }
    if (!o.spend()) return false;
    switch (o.tree.nodeTag(node)) {
        .block, .block_semicolon, .block_two, .block_two_semicolon, .@"if", .if_simple, .@"return" => {},
        .global_var_decl, .local_var_decl, .simple_var_decl, .aligned_var_decl => {
            const declaration = o.tree.fullVarDecl(node).?;
            if (o.tree.tokenTag(declaration.ast.mut_token) != .keyword_const) return false;
        },
        else => return pureIntegerExpression(o, node, depth),
    }
    var children = @import("type_engine").AstIterator.init(o.tree, node);
    while (children.next(o.tree)) |child| if (!purePredicateBody(o, child, depth + 1)) return false;
    return true;
}

fn refinePredicateCall(o: *Oracle, st: *State, node: Ast.Node.Index, truth: bool) QueryError!void {
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = o.tree.fullCall(&call_buffer, node) orelse return;
    if (!pureCallInputs(o, call)) return;
    const resolver = (o.cache orelse return).zls orelse return;
    const reference = switch (resolver.functionReference(call.ast.fn_expr) catch return) {
        .function => |reference| reference,
        .unknown, .not_callable => return,
    };
    if (reference.tree != o.tree) return;
    const declaration = tokens.enclosingFnDecl(o.tree, reference.fn_token) orelse return;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(o.tree, &proto_buffer, declaration) orelse return;
    if (proto.ast.fn_token != reference.fn_token) return;
    const return_type = proto.ast.return_type.unwrap() orelse return;
    if ((resolver.isBoolType(return_type) catch null) != true) return;
    const body = tokens.bodyOf(o.tree, declaration) orelse return;
    if (!o.spend()) return;
    const allowance = contractAllowance(o) orelse return;

    // The walk this is about to take is a walk of the CALLEE's body, and what
    // it exports depends on that body and on the truth the site assumed — not
    // on the site and not on the caller's own state.  So the contract is taken
    // ONCE per (declaration, truth) for the whole query and read back after
    // that.  A callee whose own body calls two predicates used to cost the
    // product of its call sites: every site walked its body, and every body
    // walked its own callees again.  What is charged per site is unchanged —
    // the `spend` above and the child's allowance below — so the step
    // accounting is still a function of the source order and of which site
    // came first.
    var unshared: PredicateMemo = .{ .gpa = o.gpa };
    defer unshared.deinit();
    const memo = o.memo orelse &unshared;
    if (memo.find(declaration, truth)) |facts|
        return applyPredicateFacts(o, st, node, declaration, facts);

    var capture: PredicateCapture = .{ .gpa = o.gpa, .truth = truth };
    defer capture.deinit();
    var child: Oracle = .{
        .gpa = o.gpa,
        .tree = o.tree,
        .body = body,
        .cache = o.cache,
        .query = .numeric_range,
        .target = "",
        .use_token = std.math.maxInt(Ast.TokenIndex),
        .budget = allowance,
        .budget_cap = o.budget_cap,
        .infer_callers = false,
        .predicate_capture = &capture,
        .memo = o.memo,
    };
    defer child.deinit();
    // A bound the helper hit is the asking query's to report: an unread
    // contract leaves the walk to answer from less than the body proves, and
    // an answer drawn from less is not a finished one.
    defer inheritStop(o, &child);
    // Charge consumed work even when the helper cannot finish.
    // An incomplete helper exports no facts.
    defer {
        const spent = chargeContractSteps(allowance, &child);
        // Settling what the child cost happens AFTER the contract is applied,
        // and applying one runs the caller's own step counter — so the two
        // subtractions are no longer the only claim on `o.budget`.  The counter
        // saturates rather than wrapping; a walk that has genuinely run out
        // says so through `spend`, which names the bound it hit.
        if (o.budget > spent) o.budget -= spent else o.budget = 0;
    }
    if (!purePredicateBody(&child, body, 0)) return;
    const flow = try analyzeBody(&child);
    if (!flow.diverged or child.stoppedShort()) return;
    const returned = if (capture.state) |*state| state else return;
    // Rows are appended straight into the table, so the contract is composed
    // once and every later site reads these.  A row that could not be
    // appended leaves the table without the KEY that names this contract, so
    // the partial rows are never read back; `record` rolls them back itself
    // when it is the key that could not be stored.
    const start = memo.rows.items.len;
    var parameters = proto.iterate(o.tree);
    var parameter_index: usize = 0;
    while (parameters.next()) |parameter| {
        const name = o.tree.tokenSlice(parameter.name_token orelse {
            parameter_index += 1;
            continue;
        });
        const index = parameter_index;
        parameter_index += 1;
        const bound = returned.numericValue(name);
        const minimum = returned.minLenOf(name);
        const non_empty = returned.containers.contains(name);
        if (bound == .unknown and minimum == null and !non_empty) continue;
        try memo.rows.append(o.gpa, .{
            .name = name,
            .index = index,
            .type_expr = parameter.type_expr,
            .bound = bound,
            .minimum = minimum,
            .non_empty = non_empty,
        });
    }
    try memo.record(start, declaration, truth);
    return applyPredicateFacts(o, st, node, declaration, memo.rows.items[start..]);
}

/// Read one proved predicate contract back onto the storage THIS call site
/// handed over.  The contract is in the callee's spelling; the caller owns the
/// mapping, and a contract about a parameter is about the ARGUMENT this site
/// passed for it — two sites that pass the same storage share the fact, and a
/// site that passed something spelling no path cannot be keyed on and gets
/// nothing.
fn applyPredicateFacts(
    o: *Oracle,
    st: *State,
    call_node: Ast.Node.Index,
    declaration: Ast.Node.Index,
    facts: []const PredicateFact,
) error{OutOfMemory}!void {
    const resolver = (o.cache orelse return).zls orelse return;
    for (facts) |fact| {
        const argument = (resolver.callArgument(call_node, fact.index) catch continue) orelse continue;
        const caller_name = numeric_eval.path(o.tree, argument) orelse continue;
        if (fact.bound == .floating) {
            // A float contract is about the VALUE, and the argument may have
            // crossed a conversion on its way in.  The conversion is read in
            // the caller's own namespace, which is where the argument is.
            const type_expr = fact.type_expr orelse continue;
            if (!predicateArgumentUnchanged(o, call_node, declaration, type_expr, argument)) continue;
            try st.setNumeric(o.gpa, caller_name, st.numericValue(caller_name).intersect(fact.bound));
        } else if (fact.bound != .unknown) {
            try st.setNumeric(o.gpa, caller_name, st.numericValue(caller_name).intersect(fact.bound));
        }
        // A helper that validates a container's length states that as a
        // CONTAINER fact, not as a range on the container itself: `items.len
        // != 0` proves nothing numeric about `items`, and reading only the
        // scalar range dropped the whole contract.  Both channels the length
        // is recorded in travel, because a later read may ask for either —
        // `minLenOf` is what a `>= N` proof is read from, and `containers` is
        // what a plain non-emptiness proof is read from.
        if (fact.minimum) |n| {
            try st.setMinLen(o.gpa, caller_name, n);
            if (n >= 1) try st.containers.add(o.gpa, caller_name);
        } else if (fact.non_empty) {
            try st.containers.add(o.gpa, caller_name);
            try st.setMinLen(o.gpa, caller_name, 1);
        }
    }
}

/// Maximum precision across closed generic instantiations, not an arithmetic
/// format.
///
/// A float-typed value's WIDTH is not a property of the expression that
/// produces it when that expression is a generic parameter: the same
/// parameter is one width per call site, so the only width that can be
/// proved for it is the maximum over every call this file makes of the
/// declaration it belongs to.
///
/// Null means "not proved", never "no width": the first is a missing fact and
/// the second would be a claim, and every consumer here takes its
/// conservative branch on a missing fact.
fn maxFloatBitsOf(o: *Oracle, node: Ast.Node.Index) ?u16 {
    return computedFloatBitsAtDepth(o, node, 0, .maximum);
}

/// A bit view needs one arithmetic format, not only a precision ceiling.
/// Both bounds use the same canonical parameter identity and closed census;
/// an open edge or an unknown argument prevents either bound from completing.
fn exactFloatBitsOf(o: *Oracle, node: Ast.Node.Index) ?u16 {
    const minimum = computedFloatBitsAtDepth(o, node, 0, .minimum) orelse return null;
    const maximum = maxFloatBitsOf(o, node) orelse return null;
    return if (minimum == maximum) minimum else null;
}

const FloatWidthBound = enum { minimum, maximum };

/// Frames of generic-parameter indirection one float-width proof may follow
/// before it stops looking.
const float_width_depth_cap: u8 = 8;

fn computedFloatBitsAtDepth(o: *Oracle, node: Ast.Node.Index, depth: u8, bound: FloatWidthBound) ?u16 {
    if (o.summary_error != null) return null;
    if (depth == float_width_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = float_width_depth_cap });
        return null;
    }
    if (!o.spend()) return null;
    const cache = o.cache orelse return null;
    const resolver = cache.zls orelse return null;
    const direct = resolver.floatBits(node) catch |err| blk: {
        if (strictQueryError(err)) |failure|
            o.summary_error = o.summary_error orelse failure;
        break :blk null;
    };
    if (direct) |bits| return if (bits == 0) null else bits;
    const reference = (resolver.typeParameterReference(node) catch |err| {
        if (strictQueryError(err)) |failure|
            o.summary_error = o.summary_error orelse failure;
        return null;
    }) orelse return null;
    if (reference.tree != o.tree) return null;
    if (bound == .maximum) if (o.max_float_bits.get(reference.token)) |bits| return bits;
    const declaration = tokens.enclosingFnDecl(o.tree, reference.token) orelse return null;
    if (externallyReachable(o, declaration)) return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(o.tree, &buffer, declaration) orelse return null;
    var parameters = proto.iterate(o.tree);
    var parameter_index: usize = 0;
    var found = false;
    while (parameters.next()) |parameter| {
        if (parameter.name_token == reference.token) {
            found = true;
            break;
        }
        parameter_index += 1;
    }
    if (!found) return null;
    const calls = (cache.closedLocalCalls(declaration) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return null;
    }) orelse return null;
    if (calls.len == 0) return null;
    if (calls.len > max_contract_calls) {
        o.giveUp(.{ .limit = .numeric_oracle_callers, .cap = max_contract_calls });
        return null;
    }
    var result: u16 = if (bound == .maximum) 0 else std.math.maxInt(u16);
    for (calls) |call| {
        const argument = (resolver.callArgument(call, parameter_index) catch |err| {
            if (strictQueryError(err)) |failure|
                o.summary_error = o.summary_error orelse failure;
            return null;
        }) orelse return null;
        const bits = computedFloatBitsAtDepth(o, argument, depth + 1, bound) orelse return null;
        result = if (bound == .maximum) @max(result, bits) else @min(result, bits);
    }
    if (result == 0) return null;
    // The memo is an ACCELERATOR, never the answer: the maximum is already
    // proved by the time this line runs, and failing to file it changes how
    // long the next question takes, not what any of them is told.  Laundering
    // the allocation failure into a null would answer "no float-bits ceiling
    // is known" about a declaration whose width this walk just established,
    // and every consumer would take its conservative branch on a proved fact.
    if (bound == .maximum) o.max_float_bits.put(o.gpa, reference.token, result) catch {};
    return result;
}

fn predicateArgumentUnchanged(o: *Oracle, call: Ast.Node.Index, declaration: Ast.Node.Index, type_node: ?Ast.Node.Index, argument: Ast.Node.Index) bool {
    const cache = o.cache orelse return false;
    const resolver = cache.zls orelse return false;
    const expected = actualParameterType(o, call, declaration, type_node orelse return false) orelse return false;
    if (resolver.typeParameterReference(argument) catch null) |source| {
        if (resolver.typeParameterReference(expected) catch null) |destination| {
            if (source.tree == destination.tree and source.token == destination.token) return true;
        }
    }
    const source_bits = maxFloatBitsOf(o, argument) orelse return false;
    // A destination ceiling is insufficient: one instantiation can be wider
    // than the source while another narrows it. Compare the source ceiling
    // with the destination floor unless both name the same bound parameter.
    const destination_bits = computedFloatBitsAtDepth(o, expected, 0, .minimum) orelse return false;
    return source_bits <= destination_bits;
}

fn actualParameterType(o: *Oracle, call: Ast.Node.Index, declaration: Ast.Node.Index, type_node: Ast.Node.Index) ?Ast.Node.Index {
    const resolver = (o.cache orelse return null).zls orelse return null;
    const reference = (resolver.typeParameterReference(type_node) catch return null) orelse return type_node;
    if (reference.tree != o.tree) return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(o.tree, &buffer, declaration) orelse return null;
    var parameters = proto.iterate(o.tree);
    var index: usize = 0;
    while (parameters.next()) |parameter| {
        if (parameter.name_token == reference.token) return resolver.callArgument(call, index) catch null;
        index += 1;
    }
    return null;
}

/// Frames of nested expression one bit-alias read may unwrap before it stops
/// looking.
const bit_alias_depth_cap: u8 = 32;

fn bitAliasOf(o: *Oracle, st: *const State, node: Ast.Node.Index, depth: u8) ?BitAlias {
    if (depth == bit_alias_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = bit_alias_depth_cap });
        return null;
    }
    if (!o.spend()) return null;
    const tree = o.tree;
    if (numeric_eval.path(tree, node)) |name| if (st.bitAlias(name)) |alias| return alias;
    switch (tree.nodeTag(node)) {
        .grouped_expression => return bitAliasOf(o, st, tree.nodeData(node).node_and_token[0], depth + 1),
        .bit_and => return maskedBitAlias(o, st, node, depth + 1),
        .field_access => {
            const owner = numeric_eval.path(tree, tree.nodeData(node).node_and_token[0]) orelse return null;
            var alias = st.bitAlias(owner) orelse return null;
            if (!alias.union_view) return null;
            const info = (o.cache orelse return null).intInfoOf(node) orelse return null;
            if (info.signed or info.bits != alias.float_bits) return null;
            alias.union_view = false;
            return alias;
        },
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
            var buffer: [2]Ast.Node.Index = undefined;
            const arguments = tree.builtinCallParams(&buffer, node).?;
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            const cache = o.cache orelse return null;
            const info = cache.intInfoOf(node) orelse return null;
            if (info.signed) return null;
            if (std.mem.eql(u8, name, "@as")) {
                if (arguments.len != 2) return null;
                return bitAliasOf(o, st, arguments[1], depth + 1);
            }
            if (std.mem.eql(u8, name, "@intCast")) {
                if (arguments.len != 1) return null;
                return bitAliasOf(o, st, arguments[0], depth + 1);
            }
            if (!std.mem.eql(u8, name, "@bitCast") or arguments.len != 1) return null;
            const input_bits = exactFloatBitsOf(o, arguments[0]);
            if (input_bits != info.bits) return null;
            return floatBitSource(o, st, arguments[0], info.bits, null);
        },
        else => return unionBitAlias(o, st, node),
    }
}

fn maskedBitAlias(o: *Oracle, st: *const State, node: Ast.Node.Index, depth: u8) ?BitAlias {
    const operands = o.tree.nodeData(node).node_and_node;
    const parts = [2]Ast.Node.Index{ operands[0], operands[1] };
    for (0..2) |side| {
        const mask = numericValue(o, st, parts[1 - side]);
        if (mask != .integer or mask.integer.min != mask.integer.max or
            mask.integer.min < 0 or mask.integer.max > std.math.maxInt(u64)) continue;
        var alias = bitAliasOf(o, st, parts[side], depth) orelse continue;
        if (alias.union_view) continue;
        alias.mask &= @intCast(mask.integer.min);
        return alias;
    }
    return null;
}

fn floatBitSource(o: *Oracle, st: *const State, original: Ast.Node.Index, width: u16, destination: ?Ast.Node.Index) ?BitAlias {
    if (width != 16 and width != 32 and width != 64) return null;
    var evaluation = evaluator(o, st);
    // `width` is the declared width of the value receiving this expression.
    // The outer cast can have no independently resolved result location in a
    // generic body; its destination is nevertheless known at this binding.
    var node = original;
    var absolute = false;
    var destination_width = width;
    var contextual_width: ?u16 = width;
    var contextual_type = destination;
    const generic_destination = if (destination) |target|
        evaluation.sameTypeParameter(target, target)
    else
        false;
    // A matching parameter does not narrow itself. Other intermediate
    // formats still need to retain every possible source value.
    var independent_width: ?u16 = if (generic_destination) null else width;
    for (0..32) |_| {
        if (!o.spend()) return null;
        if (numeric_eval.path(o.tree, node)) |name| {
            const bits = maxFloatBitsOf(o, node) orelse return null;
            const same_parameter = if (destination) |target|
                evaluation.sameTypeParameter(node, target)
            else
                false;
            const required_width: ?u16 = if (same_parameter) independent_width else destination_width;
            if (required_width) |limit| if (bits > limit) return null;
            return .{
                .source = name,
                .float_bits = @intCast(width),
                .absolute = absolute,
                .mask = @as(u64, std.math.maxInt(u64)) >> @as(u6, @intCast(64 - width)),
            };
        }
        if (o.tree.nodeTag(node) == .grouped_expression) {
            node = o.tree.nodeData(node).node_and_token[0];
            continue;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const arguments = o.tree.builtinCallParams(&buffer, node) orelse return null;
        const name = o.tree.tokenSlice(o.tree.nodeMainToken(node));
        if (std.mem.eql(u8, name, "@abs") and arguments.len == 1) {
            absolute = true;
            node = arguments[0];
        } else {
            const float_cast = std.mem.eql(u8, name, "@floatCast") and arguments.len == 1;
            const explicit_cast = std.mem.eql(u8, name, "@as") and arguments.len == 2;
            if (!float_cast and !explicit_cast) return null;
            const input = arguments[if (explicit_cast) @as(usize, 1) else 0];
            const resolved_output_width = if (float_cast) evaluation.floatBits(node) else null;
            const output_width = if (explicit_cast)
                computedFloatBitsAtDepth(o, arguments[0], 0, .minimum) orelse return null
            else
                resolved_output_width orelse contextual_width orelse
                    computedFloatBitsAtDepth(o, node, 0, .minimum) orelse return null;
            // Every intermediate format must retain the original value. A
            // final widening cannot repair an earlier narrowing. Taking the
            // minimum also handles a contextual cast whose generic output
            // varies between lossless widths at different closed call sites.
            destination_width = @min(destination_width, output_width);
            const output_type: ?Ast.Node.Index = if (explicit_cast)
                arguments[0]
            else if (resolved_output_width == null and contextual_width != null)
                contextual_type
            else
                node;
            const same_parameter = if (destination) |target|
                if (output_type) |output| evaluation.sameTypeParameter(output, target) else false
            else
                false;
            if (!same_parameter) {
                independent_width = if (independent_width) |limit|
                    @min(limit, output_width)
                else
                    output_width;
            }
            contextual_width = if (explicit_cast) output_width else null;
            contextual_type = if (explicit_cast) arguments[0] else null;
            node = input;
        }
    }
    return null;
}

fn unionBitAlias(o: *Oracle, st: *const State, node: Ast.Node.Index) ?BitAlias {
    const resolver = (o.cache orelse return null).zls orelse return null;
    var buffer: [2]Ast.Node.Index = undefined;
    const initializer = o.tree.fullStructInit(&buffer, node) orelse return null;
    if (initializer.ast.fields.len != 1) return null;
    const value = initializer.ast.fields[0];
    const first = o.tree.firstToken(value);
    if (first < 2 or o.tree.tokenTag(first - 2) != .identifier) return null;
    const field = o.tree.tokenSlice(first - 2);
    const width = (resolver.externUnionFloatFieldBits(node, field) catch return null) orelse return null;
    var alias = floatBitSource(o, st, value, width, null) orelse return null;
    alias.union_view = true;
    return alias;
}

/// Run one query.  `false` means the answer is genuinely unproven; a
/// walk that ran out of bounds returns `error.AnalysisBudgetExceeded`
/// instead, because "not proven" and "not finished" are different
/// claims about the file.
fn run(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body_node: Ast.Node.Index,
    query: Query,
    target: []const u8,
    use_token: Ast.TokenIndex,
    min_n: u64,
    cache: ?*file_cache_mod.FileCache,
    expression: ?Ast.Node.Index,
) QueryError!bool {
    var memo: PredicateMemo = .{ .gpa = gpa };
    defer memo.deinit();
    var oracle: Oracle = .{
        .gpa = gpa,
        .tree = tree,
        .body = body_node,
        .query = query,
        .target = target,
        .use_token = use_token,
        .min_n = min_n,
        .memo = &memo,
        .cache = cache,
        .expression = expression,
    };
    defer oracle.deinit();
    const flow = try analyzeBody(&oracle);
    if (oracle.out_of_memory) return error.OutOfMemory;
    if (oracle.stoppedShort()) return reportGiveUp(&oracle);
    if (oracle.summary_error) |err| return err;
    return flow.answer orelse false;
}

fn analyzeBody(o: *Oracle) QueryError!Flow {
    if (o.summary_error) |err| return err;
    var owned_bindings: ?local_bindings.LocalBindings = null;
    defer if (owned_bindings) |*bindings| bindings.deinit();
    // Cached bindings outlive this walk and are needed by the later contract
    // effect phase. Only locally owned tables must be retired at this exit.
    defer if (owned_bindings != null) {
        o.locals = &.{};
        o.file_consts = null;
    };
    try numeric_escape.collectEscapeRoots(o);
    var st: State = .{};
    defer st.deinit(o.gpa);
    try seedParameters(o, &st, &owned_bindings);
    if (o.summary_error) |err| return err;
    // What the call site held about this receiver, over whatever the
    // receiver contract proved about it.  It is applied BEFORE the snapshot
    // below so that an exit leaving before the body writes a path is filled
    // with the value the body was handed rather than with the declared
    // domain — a callee that declined to append leaves the caller's length
    // exactly as it was, and that value is the caller's to know.
    for (o.entry_facts) |fact| {
        try st.setNumeric(o.gpa, fact.name, st.numericValue(fact.name).intersect(fact.value));
    }
    for (o.entry_lengths) |fact| try st.setLenBound(o.gpa, fact.name, fact.value);
    // Every path into this body starts from what the seeding established, so
    // that is what an exit which leaves BEFORE a later write still holds.  The
    // snapshot is read only for that, and only by a walk that is collecting
    // exits; a top-level query has no exit to fill.
    if (o.capture) |capture| {
        if (capture.mode == .exit) try o.entry_numeric.appendSlice(o.gpa, st.numeric.items);
    }
    const flow = try analyzeNode(o, o.body, &st);
    // Control that runs off the end of the body comes back to the caller
    // too, and for a function with no trailing `return` that is the only
    // exit there is — a contract read from the `return` statements alone
    // would be empty for exactly the functions that most often establish
    // one.
    if (o.capture) |capture| {
        if (capture.mode == .exit and !flow.diverged) try capture.record(&st);
    }
    return flow;
}

/// The `const` bindings outside this function, and what each is initialised
/// to, so the numeric evaluator can follow the name a compile-time integer
/// is written under.  Read by the numeric evaluator and by `exprMin`.
///
/// These declarations are a property of the FILE, not of this query, so they
/// come from the file cache's one lazily built index instead of from a walk
/// of the whole node array per anchor.  Nothing is copied: the slice and
/// every name in it are the snapshot's own.
///
/// Two things are decided per query rather than once per file, and both are
/// about what THIS walk means rather than about what the file declares:
///
///   - A name the walk binds is answered by the walk.  A local of the same
///     name is a different value entirely, so a file-level declaration must
///     not answer for it.  The root tier alone cannot decide that, which is
///     why the check lives in the consumer and not in the index.
///   - A name the file declares twice answers nothing.  Neither declaration
///     can be shown to be the one a use names, so the name stops resolving
///     rather than resolving to whichever declaration happened to come last.
fn buildContainerConsts(o: *Oracle) void {
    if (o.file_consts != null) return;
    const cache = o.cache orelse return;
    // The table is not materialised: `FileCache.fileConstInitializer` already
    // drops a name declared twice and answers null for a declaration with no
    // initializer, so it IS the index, and it can fail only on allocation —
    // which the lookup itself reports to its own caller.
    o.file_consts = .{
        .tree = o.tree,
        .cache = cache,
        .walk_binds = o.locals,
    };
}

fn walkBindsName(o: *const Oracle, name: []const u8) bool {
    for (o.locals) |binding| {
        if (std.mem.eql(u8, binding.name, name)) return true;
    }
    return false;
}

/// A scalar projection of an immutable file constant. Do not follow pointers:
/// a const pointer can still refer to mutable storage. Local names shadow the
/// file declaration, and field selection requires a concrete struct value.
fn fileScalarInitializer(o: *Oracle, original: Ast.Node.Index, depth: u8) QueryError!?Ast.Node.Index {
    if (depth >= walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return null;
    }
    if (!o.spend()) return null;
    const tree = o.tree;
    const node = unwrapGrouped(tree, original);
    if (tree.nodeTag(node) == .identifier) {
        const name = tree.tokenSlice(tree.nodeMainToken(node));
        for (o.locals) |binding| if (std.mem.eql(u8, binding.name, name)) return null;
        return (o.cache orelse return null).fileConstInitializer(name);
    }
    if (tree.nodeTag(node) != .field_access) return null;
    const owner, const field = tree.nodeData(node).node_and_token;
    const resolver = (o.cache orelse return null).zls orelse return null;
    const frame = o.resolution_frame orelse resolver.resolutionFrame();
    const actual = (frame.typeOfNode(owner) catch |err| {
        if (strictQueryError(err)) |failure| return failure;
        return null;
    }) orelse return null;
    if (resolver.typeTag(actual) != .@"struct") return null;
    const initializer = (try fileScalarInitializer(o, owner, depth + 1)) orelse return null;
    var buffer: [2]Ast.Node.Index = undefined;
    const fields = (tree.fullStructInit(&buffer, unwrapGrouped(tree, initializer)) orelse return null).ast.fields;
    for (fields) |value| {
        if (!o.spend()) return null;
        const token = tree.firstToken(value);
        if (token < 2 or tree.tokenTag(token - 2) != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(token - 2), tree.tokenSlice(field))) return value;
    }
    return null;
}

fn seedFileScalarFacts(o: *Oracle, st: *State, node: Ast.Node.Index, depth: u8) QueryError!void {
    if (depth >= walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return;
    }
    if (!o.spend()) return;
    if (numeric_eval.path(o.tree, node)) |name| {
        if (try fileScalarInitializer(o, node, 0)) |initializer| {
            var evaluation = evaluator(o, st);
            // Coerce at the stored field's actual format, not at f128:
            // 4294967295 stored in f32 rounds to the unsafe 2^32 boundary.
            const raw = evaluation.evaluate(initializer);
            const value = if (evaluation.floatBits(node)) |bits|
                raw.asFloat(bits)
            else
                evaluation.coerce(raw, initializer, node);
            if (value != .unknown) try st.setNumeric(o.gpa, name, value);
        }
    }
    var children = @import("type_engine").AstIterator.init(o.tree, node);
    while (children.next(o.tree)) |child| try seedFileScalarFacts(o, st, child, depth + 1);
}

fn seedParameters(o: *Oracle, st: *State, owned: *?local_bindings.LocalBindings) QueryError!void {
    const tree = o.tree;
    const declaration = enclosingFnDecl(o);
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = if (declaration) |node| tokens.fnProto(tree, &buffer, node) else null;
    // A body with no readable proto is a MISS, not a forced unwrap: the cache
    // cannot key a table it has no proto to build, and the walk answers it
    // from the locally built table instead — the same table `localBindings`
    // would have produced for that null, and the same one the loop below
    // declines to iterate over.
    if (o.cache) |cache| if (proto) |readable| {
        o.locals = (try cache.localBindings(readable, o.body)).items;
    } else {
        owned.* = try local_bindings.build(o.gpa, tree, null, o.body);
        o.locals = owned.*.?.items;
    } else {
        owned.* = try local_bindings.build(o.gpa, tree, proto, o.body);
        o.locals = owned.*.?.items;
    }
    // After `o.locals` is set: the table is exactly the names this walk does
    // NOT bind, so it can only be read once the walk knows its own.
    buildContainerConsts(o);
    if (o.query == .numeric_range) if (o.expression) |expression|
        try seedFileScalarFacts(o, st, expression, 0);
    var parameters = (proto orelse return).iterate(tree);
    var parameter_index: usize = 0;
    while (parameters.next()) |parameter| {
        const current_parameter = parameter_index;
        parameter_index += 1;
        const token = parameter.name_token orelse continue;
        if (o.query == .numeric_range or o.query == .min_len_container) {
            var evaluation = evaluator(o, st);
            const declared = if (parameter.type_expr) |type_node|
                evaluation.typeRange(type_node)
            else
                .unknown;
            var initial = declared;
            if (declared == .unknown) if (parameter.type_expr) |type_node| {
                if (maxFloatBitsOf(o, type_node) != null) initial = .{ .floating = .{} };
            };
            const incoming = if (o.infer_callers and (declared != .unknown or parameter.type_expr == null))
                try callerParameterBounds(o, declaration.?, current_parameter, parameter.type_expr)
            else
                .unknown;
            try st.setNumeric(o.gpa, tree.tokenSlice(token), initial.intersect(incoming));
            // A container parameter's LENGTH is a fact its declared type does
            // not speak for — `[]const u8` bounds no index — so nothing above
            // records it and the callee's own walk cannot see it.  What every
            // caller proved about the argument it passes is exactly that fact,
            // and it travels on the length channel `allocatedLengthBound`
            // reads, which the three ways a length can change already
            // withdraw: a rebind of the binding, a rebind inside a loop, and
            // an effect that reaches the binding's address.
            if (o.infer_callers and parameter.type_expr != null) {
                if (declaredTypeIsBounded(tree, parameter.type_expr.?)) {
                    const length = try callerParameterLengthBounds(o, declaration.?, current_parameter);
                    if (length != .unknown) {
                        try st.setLenBound(o.gpa, tree.tokenSlice(token), length);
                    }
                }
            }
            if (parameter.type_expr) |type_node| {
                const fixed = evaluation.containerLength(type_node);
                if (fixed != .unknown)
                    try st.setLenBound(o.gpa, tree.tokenSlice(token), fixed.intersect(st.lenBoundOf(tree.tokenSlice(token)) orelse .unknown));
            }
        }
        if (parameterNonnegative(o, parameter.type_expr)) {
            try st.setScalarMin(o.gpa, tree.tokenSlice(token), 0);
        }
        // A parameter with no type expression (`anytype`, a bare `comptime`)
        // may be an address; assume it is so nothing reached through it is
        // treated as call-stable.  A spelled or resolved pointer type is the
        // same.  A slice parameter is a by-value header in this frame, so only
        // `pointer_roots` (the escape model) takes it — see `callStableRoot`.
        const name = tree.tokenSlice(token);
        if (parameter.type_expr) |type_node| {
            if (numeric_escape.spellingIsPointer(tree, type_node)) {
                try o.pointer_roots.add(o.gpa, name);
                try o.indirection_roots.add(o.gpa, name);
            } else if (o.cache) |cache| {
                if (cache.typeRefIsPointerLike(type_node) == true) {
                    try o.pointer_roots.add(o.gpa, name);
                    if (numeric_escape.valueIsAddress(o, type_node)) try o.indirection_roots.add(o.gpa, name);
                }
            }
        } else {
            try o.pointer_roots.add(o.gpa, name);
            try o.indirection_roots.add(o.gpa, name);
        }
    }
    // After the loop, so `pointer_roots` names every parameter a contract
    // could travel along.
    try seedReceiverContracts(o, st);
}

/// Tell a recorded exit what a path held on an edge that had no fact about
/// it.  An exit contract is the intersection of the states that LEAVE the
/// body, and an intersection keeps only what every exit carries: a field the
/// body writes is missing from the exit that returned BEFORE the write, so
/// the fact the later exit proves about it is dropped for exactly the exits
/// that need it, and the caller reads an unconstrained field.
///
/// What such an exit holds is the value the path held on ENTRY — it left
/// before the write, so it left whatever it was handed.  Filling it with the
/// declared domain instead is far wider than the truth, and that width is what
/// loses a ceiling the caller established: a `usize` arena starts inside the
/// caller's own bound, so answering for the whole range is exactly how an
/// exported length goes back to unbounded.  The declared domain is still
/// intersected, so a path nothing established an entry value for stays
/// unconstrained.
///
/// Asked of the write that introduces the key, so no pass over the file is
/// spent looking for the paths it will write.
fn recordAbsentExitFact(o: *Oracle, name: []const u8, target: Ast.Node.Index) error{OutOfMemory}!void {
    const capture = o.capture orelse return;
    if (capture.mode != .exit) return;
    var entry: ?NumericRange = null;
    for (o.entry_numeric.items) |fact| {
        if (std.mem.eql(u8, fact.name, name)) {
            entry = fact.value;
            break;
        }
    }
    if (capture.state) |*recorded| {
        var evaluation = evaluator(o, recorded);
        const declared = evaluation.typeRange(target);
        if (declared == .unknown) return;
        const held = entry orelse declared;
        try recorded.setNumeric(
            o.gpa,
            name,
            recorded.numericValue(name).intersect(held).intersect(declared),
        );
    }
}

/// What EVERY call site of `declaration` proves about the VALUE it passes for
/// `parameter`, or unknown.
///
/// The census is over call sites, so it is counted under the same allowance the
/// two sibling contract steps use and is refused the same way: a set larger
/// than `max_contract_calls` cannot be walked to an answer, and answering from
/// part of one would be a claim about a narrowing this oracle never checked.
/// Each entry is a whole walk of one caller body, and each of those walks asks
/// its own callers the same question again, so an unbounded census here is not
/// merely slow — it is a question about the transitive caller graph that runs
/// until the step counter stops it and is then reported as
/// `numeric_oracle_steps`.  The bound the diagnostic owes is the caller
/// allowance, so this names it, and the cap itself stays where it was declared.
fn callerParameterBounds(o: *Oracle, declaration: Ast.Node.Index, parameter: usize, destination: ?Ast.Node.Index) QueryError!NumericRange {
    if (!callersMayBeAsked(o)) return .unknown;
    const cache = o.cache orelse return .unknown;
    // A declaration the file does not own is entered through callers this
    // scan cannot enumerate, so a site that proved nothing is not evidence
    // that every site proved nothing — it is evidence about the sites seen.
    if (externallyReachable(o, declaration)) return .unknown;
    const resolver = cache.zls orelse return .unknown;
    const calls = (try cache.closedLocalCalls(declaration)) orelse return .unknown;
    if (calls.len == 0) return .unknown;
    if (calls.len > max_contract_calls) {
        // The complete census is larger than this query may inspect. Keep the
        // original allowance, but distinguish a capped walk from missing proof.
        o.giveUp(.{ .limit = .numeric_oracle_callers, .cap = max_contract_calls });
        return .unknown;
    }
    var combined: ?NumericRange = null;
    for (calls) |call| {
        if (!o.spend()) return .unknown;
        const argument = (resolver.callArgument(call, parameter) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return .unknown,
        }) orelse return .unknown;
        var value = try callerArgumentBounds(o, call, argument);
        if (destination) |type_node| {
            var evaluation = evaluator(o, &.{});
            value = evaluation.coerce(value, argument, type_node);
        }
        if (value == .unknown) return .unknown;
        combined = if (combined) |previous| previous.join(value) else value;
    }
    return combined orelse .unknown;
}

/// May this walk ask its callers at all?
///
/// A caller chain that comes back to this same body is a cycle and supplies no
/// new evidence. A chain longer than eight hops hits the existing recursion
/// allowance; report that bound rather than quietly dropping the proof.
fn callersMayBeAsked(o: *Oracle) bool {
    var ancestor = o.caller_parent;
    for (0..8) |_| {
        const parent = ancestor orelse break;
        if (parent.body == o.body) return false;
        ancestor = parent.caller_parent;
    }
    if (ancestor != null) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = 8 });
        return false;
    }
    return true;
}

/// Is `declaration` reachable from OUTSIDE this file?
///
/// `FileCache.closedLocalCalls` answers a different question from this one,
/// and both have to hold for a census to be usable.  That one asks whether
/// every call site the file SPELLS has been placed; this asks whether those
/// sites are ALL the sites there are.  A `pub` or `export` declaration
/// belongs to whatever imports this file, so a scan of this file's nodes
/// cannot enumerate its callers however completely it places the ones it
/// finds — there is a caller no scan of this file can see, which is exactly
/// the situation `closedLocalCalls` already refuses for an unplaceable
/// reference.
///
/// Refusing here rather than in `buildClosedLocalCalls` keeps the two
/// questions apart: the cache answers "which sites does this file spell",
/// which stays true for a `pub` declaration and is what the enumeration fix
/// this tree already carries is about.  Whether a completed enumeration is
/// the whole caller set is a property of the CONSUMER's claim — the same
/// census is a sound basis for one question and not another — so the check
/// belongs with the questions that make the "every caller" claim. Numeric
/// parameter bounds, length bounds, and generic float-width ceilings all
/// require that complete caller set. Function-value escapes are rejected by
/// `closedLocalCalls` using resolved declaration identity.
///
/// The conservative direction is the only one available: refusing can only
/// remove a proof, never invent one.
fn externallyReachable(o: *Oracle, declaration: Ast.Node.Index) bool {
    var buffer: [1]Ast.Node.Index = undefined;
    // No readable proto is a MISS, and a miss cannot establish that nothing
    // outside this file calls in, so it answers the reachable side.
    const proto = tokens.fnProto(o.tree, &buffer, declaration) orelse return true;
    return proto.visib_token != null or proto.extern_export_inline_token != null;
}

/// What EVERY call site of `declaration` proves about the LENGTH of the
/// argument it passes for `parameter`, or unknown.
///
/// This is the container-length counterpart of `callerParameterBounds`: a
/// parameter's own value is a slice header, and nothing in its declared type
/// speaks for its length, so a caller that proved `arg.len <= N` before
/// calling has proved something about a value the callee reads and the
/// callee's own walk cannot see.  The question is asked of every declaration-
/// bound caller and combined with `join`, for the reason
/// `callerParameterBounds` gives: a call the callee is entered through and
/// nothing else decides which length it is entered with, so only the widest
/// of them holds for all of them.
///
/// A site that proves nothing bounds the whole claim to nothing, exactly as an
/// absent answer bounds a parameter's own range.  That is also what keeps the
/// claim off an UNBOUNDED sibling caller, a call after a write that withdrew
/// the fact, and a declaration whose callers the cache could not close — the
/// last of which is already refused before this is asked.
fn callerParameterLengthBounds(
    o: *Oracle,
    declaration: Ast.Node.Index,
    parameter: usize,
) QueryError!NumericRange {
    if (!callersMayBeAsked(o)) return .unknown;
    const cache = o.cache orelse return .unknown;
    // The same closure the value twin above requires: a `pub` or `export`
    // parameter has callers this scan cannot enumerate, so one of them may
    // pass a length nothing here bounds.
    if (externallyReachable(o, declaration)) return .unknown;
    const resolver = cache.zls orelse return .unknown;
    const calls = (try cache.closedLocalCalls(declaration)) orelse return .unknown;
    if (calls.len == 0) return .unknown;
    if (calls.len > max_contract_calls) {
        // The complete census is larger than this query may inspect. Keep the
        // original allowance, but distinguish a capped walk from missing proof.
        o.giveUp(.{ .limit = .numeric_oracle_callers, .cap = max_contract_calls });
        return .unknown;
    }
    var combined: ?NumericRange = null;
    for (calls) |call| {
        if (!o.spend()) return .unknown;
        const argument = (resolver.callArgument(call, parameter) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return .unknown,
        }) orelse return .unknown;
        const value = try callerArgumentLength(o, call, argument);
        if (value == .unknown) return .unknown;
        combined = if (combined) |previous| previous.join(value) else value;
    }
    return combined orelse .unknown;
}

/// The range one call site held about `<argument>.len` at the call.
///
/// Named arguments also read the caller's `.len` guards. Literal containers
/// have no such key, but their static extent still holds at the call point.
/// Walking to the argument retires facts invalidated before it is copied.
fn callerArgumentLength(
    o: *Oracle,
    call_node: Ast.Node.Index,
    argument: Ast.Node.Index,
) QueryError!NumericRange {
    const key = if (numeric_eval.path(o.tree, argument)) |spelling|
        try internPath(o, spelling, ".len")
    else
        null;
    const body = callerBody(o, call_node);
    var child: Oracle = .{
        .gpa = o.gpa,
        .tree = o.tree,
        .body = body orelse .root,
        .query = .numeric_range,
        .target = "",
        .expression = argument,
        .use_token = o.tree.firstToken(argument),
        .cache = o.cache,
        .budget = o.budget,
        .budget_cap = o.budget_cap,
        .caller_parent = o,
        .length_query = key,
        .length_expression = true,
        .memo = o.memo,
    };
    defer child.deinit();
    defer o.budget = child.budget;
    defer o.stopped = o.stopped orelse child.stopped;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = o.tree.fullCall(&buffer, call_node) orelse return .unknown;
    // Impure sibling arguments can replace a slice header. Static extents,
    // unlike guarded headers, still hold without any caller-state evidence.
    if (body == null or !pureCallInputs(&child, call)) {
        var evaluation = evaluator(&child, &.{});
        const length = evaluation.containerLength(argument);
        if (child.summary_error) |err| return err;
        return length;
    }
    const flow = try analyzeBody(&child);
    if (flow.answer == null or child.stoppedShort()) return .unknown;
    return child.numeric_answer;
}

fn callerArgumentBounds(o: *Oracle, call_node: Ast.Node.Index, argument: Ast.Node.Index) QueryError!NumericRange {
    const body = callerBody(o, call_node);
    var child: Oracle = .{
        .gpa = o.gpa,
        .tree = o.tree,
        .body = body orelse .root,
        .query = .numeric_range,
        .target = "",
        .expression = argument,
        .use_token = o.tree.firstToken(argument),
        .cache = o.cache,
        .budget = o.budget,
        .budget_cap = o.budget_cap,
        .caller_parent = o,
        .memo = o.memo,
    };
    defer child.deinit();
    defer o.budget = child.budget;
    defer o.stopped = o.stopped orelse child.stopped;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = o.tree.fullCall(&buffer, call_node).?;
    // Impure sibling arguments can change guarded values before they are copied.
    if (body == null or !pureCallInputs(&child, call)) {
        const value = numericValue(&child, &.{}, argument);
        if (child.summary_error) |err| return err;
        return value;
    }
    const flow = try analyzeBody(&child);
    // The spent steps and the bound that spent them go back to the
    // parent (above), so the query that started the walk is the one
    // that reports the give-up.
    if (flow.answer == null or child.stoppedShort()) return .unknown;
    return child.numeric_answer;
}

/// The body a call inside a `test` declaration sits in.  A call in a plain
/// function is inside that function's declaration and the enclosing-FN
/// answer covers it; a `test` block declares no `fn_decl`, so the test bodies
/// are read out of the one per-query node index rather than from a fresh walk
/// of the file's whole node array at every call site.
fn callerBody(o: *Oracle, call: Ast.Node.Index) ?Ast.Node.Index {
    const tree = o.tree;
    const token = tree.firstToken(call);
    if (tokens.enclosingFnDecl(tree, token)) |declaration| return tokens.bodyOf(tree, declaration);
    for (fileNodes(o)) |node| {
        if (tree.nodeTag(node) != .test_decl) continue;
        const body = tree.nodeData(node).opt_token_and_node[1];
        if (token >= tree.firstToken(body) and token <= tree.lastToken(body)) return body;
    }
    return null;
}

// ── Contracts across a call ───────────────────────────────────────────────
//
// A bound a function establishes about storage it was HANDED is not visible
// in the caller that made the call, and a bound it establishes about that
// storage on the way OUT is not visible either.  Both directions are the
// same fact seen from the two ends of one call, so they are modelled as a
// single translation between the callee's parameter spelling and the
// caller's.
//
// What crosses the boundary is only ever a numeric range about a path, and
// only for a path rooted at a PARAMETER: a fact about the callee's own
// locals says nothing about what the caller owns.  For a POINTER parameter
// that is the whole of `self.field` — the same storage under two names — so
// a bound written on one side is a bound on the other.

/// One parameter of a call and what the caller passed for it.  `name` is the
/// callee's spelling, `caller_path` the source spelling of the storage the
/// caller handed over, and `through_pointer` whether that parameter is a
/// pointer — which is what makes `name.field` and `caller_path.field` the
/// same storage rather than merely equal values.
const Binding = struct {
    name: []const u8,
    caller_path: []const u8,
    through_pointer: bool,
};

/// How deep the contract steps go, and how many call sites of one function
/// they will consider.  Each hop re-walks a body, so both are COSTS: a
/// chain deeper than this, or a function called from more places than this,
/// simply records nothing.
const max_contract_depth = 3;
const max_contract_calls = 24;
pub const max_contract_bindings = 8;
/// How many numeric facts one contract step may carry across the call
/// boundary.  It bounds both what the caller reads out of its own state to
/// hand the callee an entry domain and what the callee is given; a longer
/// set is left uncrossed, which costs a proof and takes nothing away.
const max_contract_entry_facts = 16;

/// Steps one contract may spend from the caller's remaining allowance.
/// Successful and incomplete contracts both pay for consumed work.
/// An incomplete contract exports no facts.
pub const max_contract_steps = 1_500;

/// The storage an argument expression names, or null when it names none.
/// `&x` names the storage `x` lives in, a bare pointer names what it points
/// at, and a computed receiver (`getList()`) names nothing a later read
/// could be keyed on.
fn storagePath(tree: *const Ast, original: Ast.Node.Index) ?[]const u8 {
    var node = unwrapGrouped(tree, original);
    if (tree.nodeTag(node) == .address_of) {
        node = unwrapGrouped(tree, tree.nodeData(node).node);
        if (!isPureFieldPath(tree, node)) return null;
    }
    return numeric_eval.path(tree, node);
}

/// Suffix of `path` under `name`; an exact value root has an empty suffix.
/// Only a pointer parameter can export facts about its reachable fields.
/// Null when the path is not rooted at the parameter at all.
fn suffixUnder(path: []const u8, name: []const u8, through_pointer: bool) ?[]const u8 {
    if (std.mem.eql(u8, path, name)) return "";
    if (!through_pointer) return null;
    if (path.len <= name.len + 1) return null;
    if (!std.mem.startsWith(u8, path, name) or path[name.len] != '.') return null;
    return path[name.len..];
}

/// Whether this body spells `name` as a token at all.  A parameter no
/// expression in the body names cannot carry a contract, and not asking
/// about it is most of the cost of this feature.
fn bodyMentions(tree: *const Ast, body: Ast.Node.Index, name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    var token = tree.firstToken(body);
    const last = tree.lastToken(body);
    while (token <= last) : (token += 1) {
        if (tags[token] == .identifier and std.mem.eql(u8, tree.tokenSlice(token), name)) return true;
    }
    return false;
}

/// Whether the body schedules anything to run after the point the walk is
/// at.  A deferred call runs at scope exit, where the walk never sees its
/// effects, so a contract read off the body would claim a state the defer
/// can still invalidate.  A body carrying one exports nothing: the weaker
/// answer is "unproven", which is the only claim left that stays true.
pub fn bodyDefers(tree: *const Ast, body: Ast.Node.Index) bool {
    const tags = tree.tokens.items(.tag);
    var token = tree.firstToken(body);
    const last = tree.lastToken(body);
    while (token <= last) : (token += 1) {
        switch (tags[token]) {
            .keyword_defer, .keyword_errdefer => return true,
            else => {},
        }
    }
    return false;
}

/// A function-level `errdefer` cannot run on a successful call. Nested
/// error-only scopes remain conservative: they can fail and be caught.
fn contractBodyDefers(tree: *const Ast, body: Ast.Node.Index, success_only: bool) bool {
    if (!success_only) return bodyDefers(tree, body);
    const tags = tree.tokens.items(.tag);
    var buffer: [2]Ast.Node.Index = undefined;
    const statements = blockStmts(tree, body, &buffer);
    var token = tree.firstToken(body);
    const last = tree.lastToken(body);
    while (token <= last) : (token += 1) {
        if (tags[token] == .keyword_defer) return true;
        if (tags[token] != .keyword_errdefer) continue;
        var direct = false;
        for (statements) |statement| {
            if (tree.nodeTag(statement) == .@"errdefer" and tree.nodeMainToken(statement) == token) {
                direct = true;
                break;
            }
        }
        if (!direct) return true;
    }
    return false;
}

/// Whether the query can name the storage `path` reaches.  A callee's
/// contract is a statement about its receiver and its arguments, so a
/// query about some other path gains nothing from it.  Skipping is a COST
/// decision only: every contract this could install is one the query would
/// have had to read to make use of.
fn contractRelevant(o: *Oracle, path: []const u8) bool {
    if (path.len == 0) return false;
    const expression = o.expression orelse return false;
    return nodeHasIdentifier(o.tree, expression, numeric_escape.rootText(path));
}

/// What the callers of this body hand it, read in the callee's spelling.
///
/// A guard can only bound what the body itself can name, so the ceiling on
/// `self.options.max_text_bytes` lives in the caller that sets it, and it
/// reaches the callee only by asking.  Asking is transitive through the
/// same step — each caller's own parameters are seeded the same way — so a
/// chain of pointer parameters carries the fact from where it is written
/// down to where it is read.  A body reached through one call site is not
/// asked: it is handed that site's facts directly (see the gate below).
fn seedReceiverContracts(o: *Oracle, st: *State) QueryError!void {
    if (!o.infer_callers or o.contract_depth >= max_contract_depth) return;
    // A walk reached through a call site already holds what that site hands
    // it: `applyCallContracts` mints the call site's own facts under this
    // body's parameter names and applies them before the body runs.  Asking
    // this body's callers again from inside it re-derives the same question
    // one hop later, and it does so through a walk of the CALLER — which
    // re-derives every contract the caller's own body holds, once per call
    // site.  A callee called twice from one body therefore pays for two full
    // re-derivations before it has walked its own body once; a step that runs
    // out of its allowance exports nothing at all, so the first call's length
    // never reaches the second call and the second is entered with an arena as
    // wide as its type.  What the call site held is also the better answer for
    // a walk that models ONE call: where both speak about a path, the
    // all-callers join is the wider of the two.  A walk with no entry facts
    // has nothing of its own to start from, and a chain of pointer parameters
    // is carried by exactly those, so it still asks.
    if (o.entry_facts.len != 0) return;
    const cache = o.cache orelse return;
    const resolver = cache.zls orelse return;
    const declaration = enclosingFnDecl(o) orelse return;
    var pbuf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(o.tree, &pbuf, declaration) orelse return;
    const calls = (try callSitesOf(o, declaration)) orelse return;
    if (calls.len == 0 or calls.len > max_contract_calls) return;
    // Only a parameter whose value is an ADDRESS is a receiver here.  A
    // by-value slice or array header is pointer-LIKE enough to sit in
    // `pointer_roots`, but its header lives in the callee's own frame slot:
    // a caller hands it a COPY, so no fact about the caller's storage travels
    // through it and there is nothing for this step to ask such a site.
    // Demanding a storage path for one of those would be a category error —
    // and because a site that cannot supply one vetoes the whole contract,
    // it would silently switch the entire ceiling off for every function that
    // takes one, which is most of them.  `indirection_roots` is exactly the
    // set that separates "a receiver" from "a header that happens to look like
    // one".
    var wanted: [max_contract_bindings][]const u8 = undefined;
    var wanted_count: usize = 0;
    var parameters = proto.iterate(o.tree);
    while (parameters.next()) |parameter| {
        const name = o.tree.tokenSlice(parameter.name_token orelse continue);
        if (!o.indirection_roots.contains(name)) continue;
        if (wanted_count == wanted.len) break;
        if (!bodyMentions(o.tree, o.body, name)) continue;
        wanted[wanted_count] = name;
        wanted_count += 1;
    }
    if (wanted_count == 0) return;
    // A receiver contract is a claim about EVERY call this function has, not
    // about the calls that happened to leave a fact behind.  One site that
    // cannot be translated, or that proves nothing, bounds the whole claim to
    // nothing — the rule `callerParameterBounds` already applies to a plain
    // parameter, where an absent answer is not a neutral one.
    //
    // The combination is `join` for the same reason.  A field written as C1 at
    // one site and C2 at another reaches the callee as whichever the taken
    // path wrote, so only `max(C1, C2)` is guaranteed; `intersect` would claim
    // the smaller ceiling, which neither site wrote.
    var acc = [_]ContractCeiling{
        .{ .path = "", .combined = .unknown, .complete = true },
    } ** max_contract_bindings;
    var acc_count: usize = 0;
    for (calls, 0..) |call, site_index| {
        if (!o.spend()) return;
        var cbuf: [1]Ast.Node.Index = undefined;
        if (o.tree.fullCall(&cbuf, call) == null) return;
        var bound: [max_contract_bindings]?Binding = .{null} ** max_contract_bindings;
        var bound_count: usize = 0;
        var site_ok = true;
        var entries = proto.iterate(o.tree);
        var index: usize = 0;
        while (entries.next()) |entry| {
            const current = index;
            index += 1;
            if (bound_count >= wanted_count) break;
            const name = o.tree.tokenSlice(entry.name_token orelse continue);
            if (!std.mem.eql(u8, name, wanted[bound_count])) continue;
            const argument = (resolver.callArgument(call, current) catch null) orelse {
                site_ok = false;
                break;
            };
            const path = storagePath(o.tree, argument) orelse {
                site_ok = false;
                break;
            };
            bound[bound_count] = .{ .name = name, .caller_path = path, .through_pointer = true };
            bound_count += 1;
        }
        // A site that does not say what the receiver names tells the callee
        // nothing about it, whatever the other sites wrote.
        if (!site_ok or bound_count < wanted_count) return;
        var captured = (try captureCallerFacts(o, call)) orelse return;
        defer captured.deinit(o.gpa);
        // Which accumulated paths THIS site spoke to.  A path a site never
        // mentioned keeps the value some other site wrote, which is not a
        // fact about every call.
        var touched: [max_contract_bindings]bool = .{false} ** max_contract_bindings;
        for (captured.numeric.items) |fact| {
            for (bound[0..bound_count]) |maybe| {
                const binding = maybe.?;
                // The captured fact is in the CALLER's naming, so it is the
                // caller's half that comes off it; the callee's half is
                // what the body writes.
                const suffix = suffixUnder(fact.name, binding.caller_path, true) orelse continue;
                if (suffix.len == 0) continue;
                const name = try internPath(o, binding.name, suffix);
                var slot: usize = 0;
                while (slot < acc_count and !std.mem.eql(u8, acc[slot].path, name)) : (slot += 1) {}
                if (slot == acc_count) {
                    // More distinct paths than the table holds would mean
                    // dropping one silently, so install nothing instead.
                    if (acc_count == acc.len) return;
                    acc[acc_count] = .{
                        .path = name,
                        .combined = fact.value,
                        // A path no earlier site spoke for cannot be claimed
                        // about every call.
                        .complete = site_index == 0,
                    };
                    acc_count += 1;
                }
                touched[slot] = true;
                acc[slot].combined = acc[slot].combined.join(fact.value);
            }
        }
        for (0..acc_count) |slot| {
            if (!touched[slot]) acc[slot].complete = false;
        }
    }
    for (0..acc_count) |slot| {
        if (!acc[slot].complete) continue;
        const path = acc[slot].path;
        try st.setNumeric(o.gpa, path, st.numericValue(path).intersect(acc[slot].combined));
    }
}

/// Every call site in this file that reaches `declaration`, or null when the
/// census cannot be closed.
///
/// The question is the CALLERS of a body, so the scan is over the whole file
/// and each call is bound to the DECLARATION its callee resolves to — the
/// same binding `applyCallContracts` reads, and the one a method spelled
/// `recv.grow(..)` needs, since nothing about the spelling names the body.
///
/// Three answers, and only the third refuses:
///
///   * a call that resolves into ANOTHER document is not a caller of this
///     declaration and is stepped over.  `std.math.maxInt(..)` is in almost
///     every file, and refusing on it would refuse every body that mentions
///     the standard library;
///   * a call that resolves HERE is a caller exactly when it lands on this
///     declaration's own `fn` token, so an alias reaches the same body and a
///     same-named declaration elsewhere does not;
///   * a call this run cannot place REFUSES.  An unplaced reference may be a
///     caller no scan of this file can see, and a receiver contract is a
///     claim about what EVERY site agreed on — one hidden site has to bound
///     the whole claim to nothing, not to be missing from the average.
fn callSitesOf(o: *Oracle, declaration: Ast.Node.Index) error{OutOfMemory}!?[]Ast.Node.Index {
    const cache = o.cache orelse return null;
    const resolver = cache.zls orelse return null;
    const tree = o.tree;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return null;
    o.call_sites.clearRetainingCapacity();
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        const reference = switch (resolver.functionReference(call.ast.fn_expr) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return null,
        }) {
            .function => |r| r,
            .unknown, .not_callable => return null,
        };
        if (reference.tree != tree) continue;
        if (reference.fn_token != proto.ast.fn_token) continue;
        try o.call_sites.append(o.gpa, node);
        // One past the cap is enough for the caller's own check to refuse;
        // completing the list would only pay for an answer that is discarded.
        if (o.call_sites.items.len > max_contract_calls) break;
    }
    return o.call_sites.items;
}

/// One callee path a receiver contract is being built for: the value every
/// call site agrees on, and whether they ALL did.
///
/// A ceiling written by only some of a function's callers is not a ceiling on
/// the callee: the other calls reach it with the field as the caller's own
/// code left it.  `complete` is what records that, and a path is installed
/// only when it stayed true through every site.
const ContractCeiling = struct {
    path: []const u8,
    combined: NumericRange,
    complete: bool,
};

/// The facts in force at one call site in the caller's own walk.
fn captureCallerFacts(o: *Oracle, call: Ast.Node.Index) QueryError!?State {
    if (o.contract_depth >= max_contract_depth) return null;
    const body = callerBody(o, call) orelse return null;
    const allowance = contractAllowance(o) orelse return null;
    var capture: Capture = .{ .gpa = o.gpa, .mode = .point };
    defer capture.deinit();
    var child: Oracle = .{
        .gpa = o.gpa,
        .tree = o.tree,
        .body = body,
        .query = .numeric_range,
        .target = "",
        .use_token = o.tree.firstToken(call),
        .expression = call,
        .cache = o.cache,
        .budget = allowance,
        .budget_cap = o.budget_cap,
        .caller_parent = o,
        .contract_depth = o.contract_depth + 1,
        .capture = &capture,
        .memo = o.memo,
    };
    defer child.deinit();
    defer inheritStop(o, &child);
    defer o.budget -= chargeContractSteps(allowance, &child);
    // The bound this step hit goes back to the caller: a contract that could
    // not be read leaves the caller's own answer drawn from less than the
    // callee proves, and that answer is not a finished one.
    const flow = try analyzeBody(&child);
    if (flow.answer == null or child.stoppedShort()) return null;
    const captured = capture.state orelse return null;
    // Captured keys can point into paths owned by the child oracle.
    // Transfer those buffers before its deferred teardown frees them.
    try o.minted_paths.ensureUnusedCapacity(o.gpa, child.minted_paths.items.len);
    try o.items_paths.ensureUnusedCapacity(o.gpa, child.items_paths.items.len);
    o.minted_paths.appendSliceAssumeCapacity(child.minted_paths.items);
    o.items_paths.appendSliceAssumeCapacity(child.items_paths.items);
    child.minted_paths.clearRetainingCapacity();
    child.items_paths.clearRetainingCapacity();
    capture.state = null;
    return captured;
}

/// Charge every step the child consumed, including incomplete attempts.
/// Completion and exported facts do not change the work already spent.
pub fn chargeContractSteps(allowance: u32, child: *const Oracle) u32 {
    return if (child.budget < allowance) allowance - child.budget else 0;
}

/// The steps a helper walk may spend: whatever the asking walk has left,
/// capped at one contract's share.  A caller with none left is out of steps,
/// not out of ideas, so the helper is not run and the bound is recorded —
/// skipping it silently would read as a helper that proved nothing.
pub fn contractAllowance(o: *Oracle) ?u32 {
    const allowance = @min(o.budget, max_contract_steps);
    if (allowance != 0) return allowance;
    o.giveUp(.{ .limit = .numeric_oracle_steps, .cap = o.budget_cap });
    return null;
}

/// Hand the bound a helper walk hit back to the walk that asked for it.
/// First stop wins, as in `giveUp`.  The step counter is left alone: the
/// caller settles the helper's cost itself and must not underflow it.
pub fn inheritStop(o: *Oracle, helper: *const Oracle) void {
    const stop = helper.stopped orelse return;
    if (o.stopped == null) o.stopped = stop;
}

/// A path spelled partly in one frame and partly in another.  The spelling
/// is minted here rather than read from a source: no token sequence in the
/// tree says `builder.text_bytes.items.len` while the analysis is inside
/// `appendBytesToCurrent`, and the fact outlives the step that made it.
pub fn internPath(o: *Oracle, prefix: []const u8, suffix: []const u8) error{OutOfMemory}![]const u8 {
    if (suffix.len == 0) return prefix;
    for (o.minted_paths.items) |path| {
        if (path.len == prefix.len + suffix.len and
            std.mem.startsWith(u8, path, prefix) and std.mem.endsWith(u8, path, suffix)) return path;
    }
    const text = try std.fmt.allocPrint(o.gpa, "{s}{s}", .{ prefix, suffix });
    errdefer o.gpa.free(text);
    try o.minted_paths.append(o.gpa, text);
    return text;
}

/// Copy this state's numeric facts out, up to the contract step's own limit.
///
/// The contract about what a callee leaves is applied right after the call's
/// effects have been dropped, and those effects drop exactly the facts the
/// contract is about: the callee may rewrite them, so the walk cannot keep
/// them as a claim about the state after.  What the caller HELD is a
/// different claim — about the value the callee is entered with — and the
/// callee is the only one that can use it.  A body with more facts than the
/// step may carry simply gets none of them, which costs a proof and claims
/// nothing.
fn holdNumericFacts(st: *const State, out: *[max_contract_entry_facts]numeric_eval.Fact) usize {
    var count: usize = 0;
    for (st.numeric.items) |fact| {
        // Only a FIELD is a receiver's fact: the contract step matches a
        // captured name against the storage the caller passed and needs a
        // suffix under it, so a bare local is never one of these — and the
        // callee's own seeding already answers for its parameters.
        if (std.mem.indexOfScalar(u8, fact.name, '.') == null) continue;
        if (count == out.len) break;
        out[count] = fact;
        count += 1;
    }
    return count;
}

/// Install, in the caller's naming, what the callee establishes on the way
/// out.
///
/// A propagated call intersects only successful exits: explicit errors and
/// errors propagated by nested `try` never reach that continuation. Raw calls
/// retain explicit error exits too and refuse a contract when propagated
/// errors were not walked. Unknown return outcomes remain in the join, which
/// can weaken a bound but cannot strengthen it. Handler walks suppress this
/// transfer through `contract_effects_pending`.
fn applyCallContracts(
    o: *Oracle,
    st: *State,
    node: Ast.Node.Index,
    held: []const numeric_eval.Fact,
) QueryError!void {
    if ((o.query != .numeric_range and o.query != .min_len_container and o.query != .positive_expression) or o.contract_effects_pending != 0) return;
    // Receiver contracts still use root-frame lookup and argument mapping.
    // A contextual numeric-return walk cannot borrow those root answers.
    if (o.resolution_frame != null) return;
    if (o.contract_depth >= max_contract_depth) return;
    const cache = o.cache orelse return;
    const resolver = cache.zls orelse return;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = o.tree.fullCall(&buffer, node) orelse return;
    const reference = switch (resolver.functionReference(call.ast.fn_expr) catch |err| {
        if (strictQueryError(err)) |failure| return failure;
        return;
    }) {
        .function => |reference| reference,
        .unknown, .not_callable => return,
    };
    const callee_tree = reference.tree;
    const declaration = tokens.enclosingFnDecl(callee_tree, reference.fn_token) orelse return;
    var pbuf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(callee_tree, &pbuf, declaration) orelse return;
    if (proto.ast.fn_token != reference.fn_token) return;
    const body = tokens.bodyOf(callee_tree, declaration) orelse return;
    if ((callee_tree == o.tree and body == o.body) or
        contractBodyDefers(callee_tree, body, o.successful_call == node)) return;
    var callee_cache = cache;
    var foreign_memo: PredicateMemo = .{ .gpa = o.gpa };
    defer foreign_memo.deinit();
    if (callee_tree != o.tree) {
        // A borrowed source resolver does not carry generic instantiations.
        // Only concrete declarations outside a type-producing function may
        // cross this boundary; every contextual body remains unknown.
        var parameters = proto.iterate(callee_tree);
        while (parameters.next()) |parameter| {
            if (parameter.anytype_ellipsis3 != null) return;
            if (parameter.comptime_noalias) |modifier| {
                if (callee_tree.tokenTag(modifier) == .keyword_comptime) return;
            }
        }
        const first = callee_tree.firstToken(declaration);
        if (first > 0) {
            if (tokens.enclosingFnDecl(callee_tree, first - 1)) |outer| {
                if (callee_tree.lastToken(outer) >= callee_tree.lastToken(declaration)) return;
            }
        }
        const document = try cache.sourceDocument(reference.handle);
        callee_cache = &document.cache;
    }
    var bound: [max_contract_bindings]?Binding = .{null} ** max_contract_bindings;
    var bound_count: usize = 0;
    // What the callee is ENTERED with is read off every parameter this call
    // hands storage for, not only the ones this query reads back: a body
    // reached through a call site is not asked about its other callers (see
    // `seedReceiverContracts`), so these are the only facts it will hold
    // about its receiver.  `bound` stays filtered — it is what the exit
    // contract below is translated through, and there the filter is a cost
    // decision about this query, not about the callee's own reasoning.
    var entered: [max_contract_bindings]Binding = undefined;
    var entered_count: usize = 0;
    var entries = proto.iterate(callee_tree);
    var index: usize = 0;
    while (entries.next()) |entry| {
        const current = index;
        index += 1;
        if (bound_count == bound.len and entered_count == entered.len) break;
        const name = callee_tree.tokenSlice(entry.name_token orelse continue);
        const argument = (resolver.callArgument(node, current) catch |err| {
            if (strictQueryError(err)) |failure| return failure;
            return;
        }) orelse continue;
        const path = storagePath(o.tree, argument) orelse continue;
        if (entered_count < entered.len) {
            entered[entered_count] = .{ .name = name, .caller_path = path, .through_pointer = true };
            entered_count += 1;
        }
        // A scalar guard can constrain a checked local whose source, rather
        // than the local itself, is what this query reads.
        const scalar_argument = cache.intInfoOf(argument) != null;
        if (bound_count == bound.len or (!scalar_argument and !contractRelevant(o, path))) continue;
        bound[bound_count] = .{ .name = name, .caller_path = path, .through_pointer = false };
        bound_count += 1;
    }
    // Nothing this walk could read back: the only reason to walk the callee
    // is what it leaves on the storage this query names.
    if (bound_count == 0) return;
    // What this call SITE held about the storage is what the callee is
    // handed, and it is one half of what the caller may read back: a body
    // that leaves before it writes anything leaves the value it was given.
    // The receiver contract asks every site, which is the right question for a
    // field the callee READS — a ceiling is what the callers agree on — and
    // the wrong one for the field it WRITES: what a later site hands over is
    // whatever the earlier calls established, and asking from inside those
    // calls re-derives the caller's own contracts once per call site before
    // the callee is walked at all.  This site is one hop, and the one the
    // caller's own walk has just proved.  Only fields cross: the bare storage
    // is the parameter itself, which the callee already seeds from the call
    // site.
    var entry: [max_contract_entry_facts]numeric_eval.Fact = undefined;
    var entry_count: usize = 0;
    for (entered[0..entered_count]) |binding| {
        for (held) |fact| {
            const suffix = suffixUnder(fact.name, binding.caller_path, true) orelse continue;
            if (suffix.len == 0) continue;
            if (entry_count == entry.len) break;
            entry[entry_count] = .{ .name = try internPath(o, binding.name, suffix), .value = fact.value };
            entry_count += 1;
        }
    }
    if (!o.spend()) return;
    const allowance = contractAllowance(o) orelse return;
    var capture: Capture = .{ .gpa = o.gpa, .mode = .exit, .success_only = o.successful_call == node };
    defer capture.deinit();
    var child: Oracle = .{
        .gpa = o.gpa,
        .tree = callee_tree,
        .body = body,
        .query = .numeric_range,
        .target = "",
        .use_token = std.math.maxInt(Ast.TokenIndex),
        // Nested helpers refer to this body's parameter names, not the
        // caller's expression. Only captured receiver facts seed this call.
        .expression = body,
        .cache = callee_cache,
        .budget = allowance,
        .budget_cap = o.budget_cap,
        .caller_parent = o,
        .infer_callers = false,
        .contract_depth = o.contract_depth + 1,
        .capture = &capture,
        .entry_facts = entry[0..entry_count],
        .memo = if (callee_tree == o.tree) o.memo else &foreign_memo,
    };
    defer child.deinit();
    defer inheritStop(o, &child);
    var child_charged = false;
    defer if (!child_charged) {
        o.budget -= chargeContractSteps(allowance, &child);
    };
    // Same as the caller-side step: a bound hit while reading the callee goes
    // back to the caller, whose answer would otherwise rest on an unread
    // contract.
    _ = try analyzeBody(&child);
    // Caller-side filters spend the same allowance. Settle this phase before
    // running them; later child effect work is charged separately below.
    o.budget -= chargeContractSteps(allowance, &child);
    child_charged = true;
    if (child.stoppedShort() or !capture.complete) return;
    const exported = capture.state orelse return;
    var scalar_effects: ?numeric_escape.EffectScan = null;
    for (exported.numeric.items) |fact| {
        for (bound[0..bound_count]) |maybe| {
            const binding = maybe.?;
            const through = child.pointer_roots.contains(binding.name);
            const suffix = suffixUnder(fact.name, binding.name, through) orelse continue;
            if (suffix.len == 0 and through) continue;
            if (suffix.len == 0) {
                // Other arguments (and their evaluation) can rewrite the
                // caller's storage after this argument's value was copied.
                if (!numeric_escape.scalarSurvivesCall(o, binding.caller_path, .{ .subtree = node })) continue;
                // A copied scalar's exit value constrains its entry argument
                // only while the parameter remains unchanged. Address-taken,
                // written, or unmodeled storage cannot establish that equality.
                if (child.addressed.contains(binding.name)) continue;
                const unchanged = try contractScalarUnchanged(o, &child, body, binding.name, &scalar_effects);
                if (child.stoppedShort()) return;
                if (!unchanged) continue;
            }
            const name = try internPath(o, binding.caller_path, suffix);
            try st.setNumeric(o.gpa, name, st.numericValue(name).intersect(fact.value));
        }
    }
    for (bound[0..bound_count]) |maybe| {
        const binding = maybe.?;
        const through = child.pointer_roots.contains(binding.name);
        for (exported.scalar_mins.items) |fact| {
            const suffix = suffixUnder(fact.name, binding.name, through) orelse continue;
            if (suffix.len == 0 and through) continue;
            if (suffix.len == 0) {
                if (!numeric_escape.scalarSurvivesCall(o, binding.caller_path, .{ .subtree = node })) continue;
                if (child.addressed.contains(binding.name)) continue;
                const unchanged = try contractScalarUnchanged(o, &child, body, binding.name, &scalar_effects);
                if (child.stoppedShort()) return;
                if (!unchanged) continue;
            }
            const name = try internPath(o, binding.caller_path, suffix);
            try st.setScalarMin(o.gpa, name, fact.n);
            if (fact.n > 0) try st.scalars.add(o.gpa, name);
        }
        for (exported.min_lens.items) |fact| {
            const suffix = suffixUnder(fact.path, binding.name, through) orelse continue;
            if (suffix.len == 0 and through) continue;
            const path = try internPath(o, binding.caller_path, suffix);
            try st.setMinLen(o.gpa, path, fact.n);
            if (fact.n > 0) try st.containers.add(o.gpa, path);
        }
    }
    try propagateNumericAliases(o, st);
}

/// A completed contract child can still spend steps scanning its effects.
/// Its old remainder is not a reservation: caller filters may have spent it.
/// Clip each phase to both remainders and settle it before the caller resumes.
fn contractScalarUnchanged(
    o: *Oracle,
    child: *Oracle,
    body: Ast.Node.Index,
    name: []const u8,
    effects: *?numeric_escape.EffectScan,
) QueryError!bool {
    child.budget = @min(child.budget, o.budget);
    const allowance = child.budget;
    defer o.budget -= chargeContractSteps(allowance, child);
    if (effects.* == null) {
        effects.* = .{};
        numeric_escape.scanEffects(child, body, &effects.*.?, 0);
    }
    if (child.stoppedShort()) return false;
    const unchanged = !effects.*.?.reaches(child, name);
    if (child.summary_error) |err| return err;
    return unchanged and !child.stoppedShort();
}

fn strictQueryError(err: anyerror) ?QueryError {
    inline for (@typeInfo(QueryError).error_set.?) |member| {
        const query_error = @field(QueryError, member.name);
        if (err == query_error) return query_error;
    }
    return null;
}

/// Bind only an entirely scalar call whose arguments run no code. Reading
/// all arguments from one incoming state is then valid, including a
/// comptime integer width. Unsupported signatures retain declared domains.
fn numericCallArguments(
    o: *Oracle,
    st: *const State,
    call: Ast.full.Call,
    proto: Ast.full.FnProto,
    out: *[max_contract_entry_facts]numeric_eval.Fact,
) QueryError!?usize {
    var parameters = proto.iterate(o.tree);
    var count: usize = 0;
    var evaluation = evaluator(o, st);
    while (parameters.next()) |parameter| {
        if (count == out.len or count == call.ast.params.len) return null;
        const name = parameter.name_token orelse return null;
        const destination = parameter.type_expr orelse return null;
        const declared = evaluation.typeRange(destination);
        if (declared != .integer) return null;
        const argument = call.ast.params[count];
        if (!pureIntegerExpression(o, argument, 0)) {
            if (o.summary_error) |err| return err;
            return null;
        }
        const actual = evaluation.evaluate(argument).intersect(declared);
        if (actual != .integer) return null;
        out[count] = .{ .name = o.tree.tokenSlice(name), .value = actual };
        count += 1;
    }
    if (count != call.ast.params.len) return null;
    if (o.summary_error) |err| return err;
    return count;
}

fn forwardedReturnRange(o: *Oracle, st: *const State, node: Ast.Node.Index) QueryError!NumericRange {
    var buffer: [1]Ast.Node.Index = undefined;
    const call = o.tree.fullCall(&buffer, node) orelse return .unknown;
    var evaluation = evaluator(o, st);
    // No argument may carry caller storage or execute a mutation before a
    // later argument is read. The callee may run code; its own walk accounts
    // for that code before recording the value it returns.
    for (call.ast.params) |argument| {
        if (!pureIntegerExpression(o, argument, 0)) {
            if (o.summary_error) |err| return err;
            return .unknown;
        }
        if (evaluation.evaluate(argument) != .integer) return .unknown;
    }
    return callReturnRange(o, st, node);
}

/// The range of values a call in this body can produce, or unknown.
///
/// `numeric_eval` reads a call through the type the callee DECLARED it
/// returns, which is the widest value the declaration admits and nothing the
/// body produces.  Where the body is narrower — a decoder that accepts three
/// formats and can therefore only hand back an exponent from those three
/// formats — the declaration is the worse of the two available answers, so
/// the body is walked and its exits joined instead.
///
/// This asks about the VALUE, not about storage, which is what keeps it
/// narrower than the receiver contract above: there is no name to translate
/// between the two scopes, so nothing here can collide with a caller's own
/// spelling of a local.  The walk runs in the callee's own scope — its
/// parameters seeded from declared types and pure scalar actual arguments,
/// its locals recorded under its own names — and only the joined range
/// comes back out.
///
/// Everything that would make the claim a claim about something other than
/// what the callee returns is declined rather than approximated: a result the
/// declared type does not pin to an integer, a body that schedules a `defer`
/// to run where the walk stops, a body that can run off its end, an exit the
/// walk could not evaluate, and a return whose operand runs code the walk
/// reads before that code ran (see `ReturnSummary`). Resource, semantic-query,
/// cancellation, and walk-budget failures propagate instead of answering unknown.
fn callReturnRange(o: *Oracle, st: *const State, node: Ast.Node.Index) QueryError!NumericRange {
    if (o.query != .numeric_range and o.query != .min_len_container) return .unknown;
    if (o.contract_depth >= max_contract_depth) return .unknown;
    const cache = o.cache orelse return .unknown;
    const resolver = cache.zls orelse return .unknown;
    var call_node = unwrapGrouped(o.tree, node);
    var propagating = o.tree.nodeTag(call_node) == .@"try";
    if (propagating) {
        call_node = unwrapGrouped(o.tree, o.tree.nodeData(call_node).node);
    } else if (o.tree.nodeTag(call_node) == .@"catch") {
        const caught = o.tree.nodeData(call_node).node_and_node;
        if (o.tree.nodeTag(unwrapGrouped(o.tree, caught[1])) != .@"return") return .unknown;
        propagating = true;
        call_node = unwrapGrouped(o.tree, caught[0]);
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const call = o.tree.fullCall(&buffer, call_node) orelse return .unknown;
    // Resolve methods and plain calls through the canonical call record.
    // Computed callees still carry no supported stable declaration.
    switch (o.tree.nodeTag(call.ast.fn_expr)) {
        .identifier, .field_access => {},
        else => return .unknown,
    }
    const caller_frame = o.resolution_frame orelse resolver.resolutionFrame();
    const actual = (cache.actualCallSummaryAt(o.tree.nodeMainToken(call.ast.fn_expr), caller_frame) catch |err| {
        if (strictQueryError(err)) |failure| return failure;
        return .unknown;
    }) orelse return .unknown;
    if (actual.callee.call_node != call_node) return .unknown;
    const reference = actual.callee.reference;
    if (reference.tree != o.tree) return .unknown;
    const declaration = tokens.enclosingFnDecl(o.tree, reference.fn_token) orelse return .unknown;
    var pbuf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(o.tree, &pbuf, declaration) orelse return .unknown;
    if (proto.ast.fn_token != reference.fn_token) return .unknown;
    var returned_type = (resolver.normalizedType(reference.actual_type.data.function.return_value.*) catch |err| {
        if (strictQueryError(err)) |failure| return failure;
        return .unknown;
    }) orelse return .unknown;
    const fallible = resolver.typeTag(returned_type) == .error_union;
    if (fallible) {
        if (!propagating) return .unknown;
        returned_type = resolver.childType(returned_type) orelse return .unknown;
    }
    // Only integer success values are joined. Optional and float results
    // remain outside this contract; caught failures cannot borrow success.
    if (resolver.typeTag(returned_type) != .int) return .unknown;
    const body = tokens.bodyOf(o.tree, declaration) orelse return .unknown;
    if (body == o.body or bodyDefers(o.tree, body)) return .unknown;
    var ancestor = o.caller_parent;
    while (ancestor) |parent| : (ancestor = parent.caller_parent) {
        if (parent.body == body) return .unknown;
    }
    var arguments: [max_contract_entry_facts]numeric_eval.Fact = undefined;
    const argument_count = try numericCallArguments(o, st, call, proto, &arguments);
    if (!o.spend()) return .unknown;
    if (argument_count) |count| if (o.memo) |memo| {
        if (memo.findNumericReturn(reference, caller_frame, node, o.contract_depth, arguments[0..count])) |value| return value;
    };
    const allowance = contractAllowance(o) orelse return .unknown;
    var summary = ReturnSummary{ .success_only = fallible };
    var child: Oracle = .{
        .gpa = o.gpa,
        .tree = o.tree,
        .body = body,
        .query = .numeric_range,
        .target = "",
        .use_token = std.math.maxInt(Ast.TokenIndex),
        .cache = o.cache,
        .budget = allowance,
        .budget_cap = o.budget_cap,
        .infer_callers = false,
        .caller_parent = o,
        .contract_depth = o.contract_depth + 1,
        .return_summary = &summary,
        .memo = o.memo,
        .entry_facts = if (argument_count) |count| arguments[0..count] else &.{},
        .resolution_frame = resolver.frameForFunction(reference),
    };
    defer child.deinit();
    defer o.budget -= chargeContractSteps(allowance, &child);
    // A body that does not diverge ran off its end somewhere, and the value
    // handed to the caller there is not one of its returns.
    const flow = try analyzeBody(&child);
    if (child.out_of_memory) return error.OutOfMemory;
    if (child.stoppedShort()) return reportGiveUp(&child);
    if (child.summary_error) |err| return err;
    if (!flow.diverged) return .unknown;
    if (!summary.complete) return .unknown;
    const value = summary.value orelse return .unknown;
    if (argument_count) |count| if (o.memo) |memo| {
        try memo.recordNumericReturn(reference, caller_frame, node, o.contract_depth, arguments[0..count], value);
    };
    return value;
}

/// Header extents share the returned-field walk and its success/memo gates.
/// A terminating catch, unlike a value-producing fallback, keeps success.
/// Inputs are captured before the call runs. A pure bare bool selector can
/// retain its true-arm header extent, separately from the joined baseline;
/// changing either binding or reaching it through effects drops that link.
fn callReturnLengths(o: *Oracle, source: *const State, expression: Ast.Node.Index, output: *State, prefix: []const u8) QueryError!void {
    // A framed caller requires canonical frame resolution and a frame key.
    if (o.resolution_frame != null) return;
    if ((o.query != .numeric_range and o.query != .min_len_container) or o.contract_depth >= max_contract_depth) return;
    var node = unwrapGrouped(o.tree, expression);
    var propagating = o.tree.nodeTag(node) == .@"try";
    if (propagating) {
        node = unwrapGrouped(o.tree, o.tree.nodeData(node).node);
    } else if (o.tree.nodeTag(node) == .@"catch") {
        const caught = o.tree.nodeData(node).node_and_node;
        if (o.tree.nodeTag(unwrapGrouped(o.tree, caught[1])) != .@"return") return;
        propagating = true;
        node = unwrapGrouped(o.tree, caught[0]);
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const call = o.tree.fullCall(&buffer, node) orelse return;
    const resolver = (o.cache orelse return).zls orelse return;
    const reference = switch (resolver.functionReferenceOfCall(node) catch |err| {
        if (strictQueryError(err)) |failure| return failure;
        return;
    }) {
        .function => |reference| reference,
        else => return,
    };
    if (reference.tree != o.tree) return;
    const declaration = tokens.enclosingFnDecl(o.tree, reference.fn_token) orelse return;
    var pbuf: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(o.tree, &pbuf, declaration) orelse return;
    if (proto.ast.fn_token != reference.fn_token) return;
    var returned_type = (resolver.normalizedType(reference.actual_type.data.function.return_value.*) catch |err| {
        if (strictQueryError(err)) |failure| return failure;
        return;
    }) orelse return;
    const fallible = resolver.typeTag(returned_type) == .error_union;
    if (fallible) {
        if (!propagating) return;
        returned_type = resolver.childType(returned_type) orelse return;
    }
    // A pointer to an aggregate shares mutable fields, unlike a copied
    // aggregate's slice headers. Optional/unknown results also carry no fact.
    const returned_tag = resolver.typeTag(returned_type);
    const bare_slice = returned_tag == .pointer and resolver.pointerSize(returned_type) == .slice;
    if (!bare_slice and returned_tag != .@"struct" and returned_tag != .@"union") return;
    const body = tokens.bodyOf(o.tree, declaration) orelse return;
    if (bodyDefers(o.tree, body)) return;
    var ancestor: ?*const Oracle = o;
    while (ancestor) |parent| : (ancestor = parent.caller_parent) {
        if (body == parent.body) return;
    }
    var inputs: ReturnLengthInputs = .{};
    if (bare_slice) {
        const recorded = try inputs.record(o, source, call, proto);
        if (o.summary_error) |err| return err;
        if (!recorded) return;
    }
    try summarizeReturnedLengths(o, source, reference, node, body, fallible, bare_slice, inputs.numeric[0..inputs.numeric_count], inputs.lengths[0..inputs.length_count], output, prefix);
    const selector = inputs.selector orelse return;
    if (!numeric_escape.scalarSurvivesCall(o, selector, .{ .subtree = expression })) return;
    var selected: State = .{};
    defer selected.deinit(o.gpa);
    try summarizeReturnedLengths(o, source, reference, node, body, fallible, bare_slice, inputs.true_numeric[0..inputs.numeric_count], inputs.lengths[0..inputs.length_count], &selected, prefix);
    if (selected.lenBoundOf(prefix)) |length|
        try output.addConditionalLength(o.gpa, .{ .header = prefix, .selector = selector, .value = length });
}

/// Input snapshots are bounded by the existing call-contract limit, and are
/// part of the same memo key as the returned aggregate fields.
const ReturnLengthInputs = struct {
    numeric: [max_contract_entry_facts]numeric_eval.Fact = undefined,
    true_numeric: [max_contract_entry_facts]numeric_eval.Fact = undefined,
    lengths: [max_contract_entry_facts]numeric_eval.Fact = undefined,
    numeric_count: usize = 0,
    length_count: usize = 0,
    selector: ?[]const u8 = null,

    fn record(self: *ReturnLengthInputs, o: *Oracle, source: *const State, call: Ast.full.Call, proto: Ast.full.FnProto) QueryError!bool {
        // Sibling operands must not change an earlier argument before entry.
        for (call.ast.params) |actual| if (!pureAggregateExpression(o, actual, 0)) return false;
        var parameters = proto.iterate(o.tree);
        var index: usize = 0;
        while (parameters.next()) |parameter| {
            if (!o.spend()) return false;
            if (index >= call.ast.params.len) return false;
            const actual = call.ast.params[index];
            index += 1;
            const token = parameter.name_token orelse return false;
            const type_node = parameter.type_expr orelse return false;
            const name = o.tree.tokenSlice(token);
            var evaluation = evaluator(o, source);
            const declared = evaluation.typeRange(type_node);
            if (declared == .integer) {
                const value = evaluation.evaluate(actual).intersect(declared);
                if (value != .integer or self.numeric_count == self.numeric.len) return false;
                const slot = self.numeric_count;
                self.numeric_count += 1;
                self.numeric[slot] = .{ .name = name, .value = value };
                self.true_numeric[slot] = self.numeric[slot];
                if (o.tree.fullIf(unwrapGrouped(o.tree, actual))) |conditional| {
                    if (conditional.payload_token != null or conditional.ast.else_expr.unwrap() == null) continue;
                    const condition = unwrapGrouped(o.tree, conditional.ast.cond_expr);
                    const flag = identName(o.tree, condition) orelse continue;
                    const resolver = (o.cache orelse continue).zls orelse continue;
                    const boolean = resolver.isBoolType(condition) catch |err| {
                        if (strictQueryError(err)) |failure| return failure;
                        continue;
                    };
                    if (boolean != true) continue;
                    if (self.selector) |previous| {
                        if (!std.mem.eql(u8, previous, flag)) return false;
                    }
                    const selected = evaluation.evaluate(conditional.ast.then_expr).intersect(declared);
                    if (selected != .integer) continue;
                    self.selector = flag;
                    self.true_numeric[slot].value = selected;
                }
            } else {
                const length = evaluation.containerLength(actual);
                if (length == .unknown) continue;
                if (self.length_count == self.lengths.len) return false;
                self.lengths[self.length_count] = .{ .name = name, .value = length };
                self.length_count += 1;
            }
        }
        return index == call.ast.params.len;
    }
};

fn summarizeReturnedLengths(o: *Oracle, source: *const State, reference: TypeResolver.FunctionReference, node: Ast.Node.Index, body: Ast.Node.Index, fallible: bool, bare_slice: bool, inputs: []const numeric_eval.Fact, input_lengths: []const numeric_eval.Fact, output: *State, prefix: []const u8) QueryError!void {
    if (o.resolution_frame != null) return;
    const memo = if (o.resolution_frame == null and o.contract_depth == 0 and o.caller_parent == null and o.entry_facts.len == 0 and o.entry_lengths.len == 0)
        o.memo
    else
        null;
    var cache_index: ?usize = null;
    var published = false;
    defer if (!published) {
        if (cache_index) |index| {
            var removed = memo.?.aggregate_returns.swapRemove(index);
            removed.deinit(o.gpa);
        }
    };
    if (memo) |owner| {
        for (owner.aggregate_returns.items) |*entry| {
            if (!o.spend()) return;
            if (!entry.matches(reference, node, o.contract_depth, source, inputs, input_lengths)) continue;
            if (entry.visiting) return;
            try applyReturnedLengths(o, entry.fields, output, prefix);
            return;
        }
        const numeric = try o.gpa.dupe(numeric_eval.Fact, source.numeric.items);
        errdefer o.gpa.free(numeric);
        const lengths = try o.gpa.dupe(numeric_eval.Fact, source.len_bounds.items);
        errdefer o.gpa.free(lengths);
        const saved_inputs = try o.gpa.dupe(numeric_eval.Fact, inputs);
        errdefer o.gpa.free(saved_inputs);
        const saved_lengths = try o.gpa.dupe(numeric_eval.Fact, input_lengths);
        errdefer o.gpa.free(saved_lengths);
        const index = owner.aggregate_returns.items.len;
        try owner.aggregate_returns.append(o.gpa, .{
            .reference = reference,
            .call = node,
            .depth = o.contract_depth,
            .numeric = numeric,
            .lengths = lengths,
            .inputs = saved_inputs,
            .input_lengths = saved_lengths,
        });
        cache_index = index;
    }
    if (!o.spend()) return;
    const allowance = contractAllowance(o) orelse return;
    var fields: State = .{};
    defer fields.deinit(o.gpa);
    var summary: ReturnSummary = .{ .aggregate = &fields, .bare_slice = bare_slice, .success_only = fallible };
    var child: Oracle = .{
        .gpa = o.gpa,
        .tree = o.tree,
        .body = body,
        .query = .numeric_range,
        .target = "",
        .use_token = std.math.maxInt(Ast.TokenIndex),
        .cache = o.cache,
        .budget = allowance,
        .budget_cap = o.budget_cap,
        .infer_callers = false,
        .caller_parent = o,
        .contract_depth = o.contract_depth + 1,
        .return_summary = &summary,
        .memo = o.memo,
        .entry_facts = inputs,
        .entry_lengths = input_lengths,
    };
    defer child.deinit();
    defer inheritStop(o, &child);
    var child_charged = false;
    defer if (!child_charged) {
        o.budget -= chargeContractSteps(allowance, &child);
    };
    const flow = try analyzeBody(&child);
    // Exporting a returned field spends the parent's budget. Settle this
    // child's completed walk before any parent export can spend those steps.
    o.budget -= chargeContractSteps(allowance, &child);
    child_charged = true;
    if (child.out_of_memory) return error.OutOfMemory;
    if (child.stoppedShort()) return reportGiveUp(&child);
    if (child.summary_error) |err| return err;
    if (!flow.diverged or !summary.complete or !summary.saw_success) return;
    try applyReturnedLengths(o, fields.len_bounds.items, output, prefix);
    if (o.stoppedShort()) return;
    if (cache_index) |index| {
        const saved = try o.gpa.dupe(numeric_eval.Fact, fields.len_bounds.items);
        errdefer o.gpa.free(saved);
        // A child's minted paths die with the child, whereas memo entries
        // live until the root query ends. Intern every result in the root.
        for (saved) |*field| field.name = try internPath(o, "", field.name);
        memo.?.aggregate_returns.items[index].fields = saved;
        memo.?.aggregate_returns.items[index].visiting = false;
        published = true;
    }
}

fn applyReturnedLengths(o: *Oracle, fields: []const numeric_eval.Fact, output: *State, prefix: []const u8) QueryError!void {
    for (fields) |field| {
        if (!o.spend()) return;
        const name = if (field.name.len == 0) prefix else try aggregateFieldPath(o, prefix, field.name);
        try output.setLenBound(o.gpa, name, field.value);
    }
}

fn aggregateFieldPath(o: *Oracle, prefix: []const u8, field: []const u8) error{OutOfMemory}![]const u8 {
    if (prefix.len == 0) return field;
    const owner = try internPath(o, prefix, ".");
    return internPath(o, owner, field);
}

/// Check every evaluated field, not just the bounded one. A sibling
/// initializer must not overwrite the header whose extent is being read.
fn pureAggregateExpression(o: *Oracle, expression: Ast.Node.Index, depth: u8) bool {
    if (depth >= walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return false;
    }
    if (!o.spend()) return false;
    const node = unwrapGrouped(o.tree, expression);
    var buffer: [2]Ast.Node.Index = undefined;
    if (o.tree.fullStructInit(&buffer, node)) |initializer| {
        for (initializer.ast.fields) |field| {
            if (!pureAggregateExpression(o, field, depth + 1)) return false;
        }
        return true;
    }
    if (o.tree.fullArrayInit(&buffer, node)) |initializer| {
        for (initializer.ast.elements) |element| {
            if (!pureAggregateExpression(o, element, depth + 1)) return false;
        }
        return true;
    }
    if (o.tree.nodeTag(node) == .address_of)
        return pureAggregateExpression(o, o.tree.nodeData(node).node, depth + 1);
    if (o.tree.fullSwitch(node)) |selection| {
        if (!pureIntegerExpression(o, selection.ast.condition, depth + 1)) return false;
        for (selection.ast.cases) |case_node| {
            const case = o.tree.fullSwitchCase(case_node) orelse return false;
            if (case.payload_token != null) return false;
            const target = unwrapGrouped(o.tree, case.ast.target_expr);
            if (o.tree.nodeTag(target) == .unreachable_literal) continue;
            if (!pureAggregateExpression(o, target, depth + 1)) return false;
        }
        return true;
    }
    if (o.tree.fullSlice(node)) |slice| {
        if (!pureAggregateExpression(o, slice.ast.sliced, depth + 1) or
            !pureIntegerExpression(o, slice.ast.start, depth + 1)) return false;
        if (slice.ast.end.unwrap()) |end| {
            if (!pureIntegerExpression(o, end, depth + 1)) return false;
        }
        if (slice.ast.sentinel.unwrap()) |sentinel| {
            if (!pureIntegerExpression(o, sentinel, depth + 1)) return false;
        }
        return true;
    }
    if (o.tree.nodeTag(node) == .string_literal or o.tree.nodeTag(node) == .multiline_string_literal) return true;
    return pureIntegerExpression(o, node, depth);
}

/// Snapshot copied header projections. Rebinding the owner or a field
/// invalidates these through the existing length-fact machinery.
fn recordAggregateLengths(o: *Oracle, source: *const State, output: *State, expression: Ast.Node.Index, prefix: []const u8, depth: u8) QueryError!void {
    if (depth >= walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return;
    }
    if (!o.spend()) return;
    const node = unwrapGrouped(o.tree, expression);
    var buffer: [2]Ast.Node.Index = undefined;
    if (o.tree.fullStructInit(&buffer, node)) |initializer| {
        for (initializer.ast.fields) |field| {
            const token = o.tree.firstToken(field);
            if (token < 2 or o.tree.tokenTag(token - 2) != .identifier) continue;
            const name = try aggregateFieldPath(o, prefix, o.tree.tokenSlice(token - 2));
            var evaluation = evaluator(o, source);
            const length = evaluation.containerLength(field);
            if (length != .unknown) try output.setLenBound(o.gpa, name, length);
            try recordAggregateLengths(o, source, output, field, name, depth + 1);
        }
    } else if (numeric_eval.path(o.tree, node)) |owner| {
        var value_type_checked = false;
        for (source.len_bounds.items) |field| {
            if (!o.spend()) return;
            if (field.name.len <= owner.len or !pathRootedAt(field.name, owner)) continue;
            if (!value_type_checked) {
                const resolver = (o.cache orelse return).zls orelse return;
                const actual = (resolver.resolutionFrame().typeOfNode(node) catch |err| {
                    if (strictQueryError(err)) |failure| return failure;
                    return;
                }) orelse return;
                const actual_tag = resolver.typeTag(actual);
                if (actual_tag != .@"struct" and actual_tag != .@"union") return;
                value_type_checked = true;
            }
            const name = try aggregateFieldPath(o, prefix, field.name[owner.len + 1 ..]);
            try output.setLenBound(o.gpa, name, field.value);
        }
    }
}

// ── Compile-time audits of a container ────────────────────────────────────
//
// `comptime { for (TABLE) |e| if (LIMIT < e.field.len) @compileError(..); }`
// is how a generated table is validated: the branch that would reject a
// violating element is one the compiler evaluated and did not take, so
// every element of the table has `e.field.len <= LIMIT`.  Nothing else in
// the file says how wide those elements are — the table is a fixed-size
// array of a slice field, and its length is not a type — so without this
// the only honest answer for a use of one element's length is "unknown".

/// One audited container: `container` is its source spelling, `field` the
/// element field path the audit compares, and `limit` the ceiling it
/// compares against.
const ElementAudit = struct {
    container: []const u8,
    field: []const u8,
    limit: i128,
};

fn comptimeAudits(o: *Oracle) error{OutOfMemory}!?std.ArrayListUnmanaged(ElementAudit) {
    if (o.audits) |audits| return audits;
    var read: std.ArrayListUnmanaged(ElementAudit) = .empty;
    errdefer releaseAudits(o.gpa, &read);
    const tree = o.tree;
    const nodes = try requiredNodes(o);
    for (nodes) |node| {
        if (tree.nodeTag(node) != .@"comptime") continue;
        if (!o.spend()) {
            releaseAudits(o.gpa, &read);
            return null;
        }
        try readElementAudit(o, tree.nodeData(node).node, &read);
    }
    o.audits = read;
    return o.audits;
}

fn releaseAudits(gpa: std.mem.Allocator, audits: *std.ArrayListUnmanaged(ElementAudit)) void {
    for (audits.items) |audit| {
        gpa.free(audit.container);
        gpa.free(audit.field);
    }
    audits.deinit(gpa);
}

/// Read one `comptime` block as an audit, or record nothing for it.
///
/// Every requirement below is a shape, never a name: a loop over one named
/// container, a single rejection guard comparing a bound against one of the
/// element's own fields, and nothing in the block that could step over that
/// guard.  Anything else records nothing rather than a weaker reading.
fn readElementAudit(
    o: *Oracle,
    expression: Ast.Node.Index,
    audits: *std.ArrayListUnmanaged(ElementAudit),
) error{OutOfMemory}!void {
    const tree = o.tree;
    const block = unwrapGrouped(tree, expression);
    if (!isBlockTag(tree.nodeTag(block))) return;
    var statements: [2]Ast.Node.Index = undefined;
    const listed = blockStmts(tree, block, &statements);
    if (listed.len == 0) return;
    var loop: ?Ast.full.For = null;
    for (listed) |statement| {
        switch (tree.nodeTag(statement)) {
            .@"for", .for_simple => {
                if (loop != null) return;
                loop = tree.fullFor(statement) orelse return;
            },
            // A guard that can be stepped over is not an audit.  A second
            // loop, a conditional of its own, an early exit, or a nested
            // declaration could all leave an element unchecked, so the block
            // carrying one is not read at all.
            .@"while",
            .while_simple,
            .while_cont,
            .@"if",
            .if_simple,
            .@"switch",
            .switch_comma,
            .@"orelse",
            .@"catch",
            .@"return",
            .@"break",
            .@"continue",
            .fn_decl,
            .container_decl,
            .container_decl_trailing,
            .container_decl_two,
            .container_decl_two_trailing,
            .container_decl_arg,
            .container_decl_arg_trailing,
            => return,
            else => {},
        }
    }
    const written = loop orelse return;
    if (written.ast.inputs.len != 1) return;
    if (written.ast.else_expr != .none) return;
    const container = storagePath(tree, unwrapGrouped(tree, written.ast.inputs[0])) orelse return;
    const element = tree.tokenSlice(written.payload_token);
    if (element.len == 0) return;
    const body = unwrapGrouped(tree, written.ast.then_expr);
    if (!isBlockTag(tree.nodeTag(body))) return;
    var inner: [2]Ast.Node.Index = undefined;
    const body_statements = blockStmts(tree, body, &inner);
    if (body_statements.len != 1) return;
    const tag = tree.nodeTag(body_statements[0]);
    if (tag != .@"if" and tag != .if_simple) return;
    const guard = tree.fullIf(body_statements[0]) orelse return;
    if (guard.ast.else_expr != .none) return;
    // The branch is what the compiler must have declined to take; what else
    // is inside it cannot change that.
    if (!bodySpans(tree, guard.ast.then_expr, "@compileError")) return;
    if (tree.nodeTag(guard.ast.cond_expr) != .less_than) return;
    const operands = tree.nodeData(guard.ast.cond_expr).node_and_node;
    const measured = storagePath(tree, operands[1]) orelse return;
    if (!std.mem.startsWith(u8, measured, element)) return;
    const field = measured[element.len..];
    if (field.len == 0 or field[0] != '.') return;
    const limit = comptimeValOf(o, operands[0]) orelse return;
    const container_copy = try o.gpa.dupe(u8, container);
    errdefer o.gpa.free(container_copy);
    const field_copy = try o.gpa.dupe(u8, field);
    errdefer o.gpa.free(field_copy);
    try audits.append(o.gpa, .{
        .container = container_copy,
        .field = field_copy,
        .limit = @intCast(limit),
    });
}

fn isBlockTag(tag: Ast.Node.Tag) bool {
    return switch (tag) {
        .block, .block_semicolon, .block_two, .block_two_semicolon => true,
        else => false,
    };
}

/// Whether any token in `node`'s own range spells `text`.  Used for
/// `@compileError`, which is a builtin token rather than an identifier, so
/// the identifier-only scan would miss it.
fn bodySpans(tree: *const Ast, node: Ast.Node.Index, text: []const u8) bool {
    var token = tree.firstToken(node);
    const last = tree.lastToken(node);
    while (token <= last) : (token += 1) {
        if (std.mem.eql(u8, tree.tokenSlice(token), text)) return true;
    }
    return false;
}

/// Record what the file's audits say about the element this binding draws.
///
/// Only an element taken by SUBSCRIPT is audited: that is the reading the
/// audit loop wrote, and an element copied by `for (T) |e|` is the loop's
/// own variable, which already has the bound where it is read.
fn recordAuditedElementFacts(o: *Oracle, st: *State, name: []const u8, init_node: Ast.Node.Index) error{OutOfMemory}!void {
    if (o.query != .numeric_range) return;
    const tree = o.tree;
    const drawn = unwrapGrouped(tree, init_node);
    if (tree.nodeTag(drawn) != .array_access) return;
    const parts = tree.nodeData(drawn).node_and_node;
    const container = storagePath(tree, parts[0]) orelse return;
    if (!o.spend()) return;
    const audits = (try comptimeAudits(o)) orelse return;
    var matched = false;
    for (audits.items) |audit| {
        if (!std.mem.eql(u8, audit.container, container)) continue;
        matched = true;
        break;
    }
    if (!matched) return;
    // A binding that draws no audited element drops what the previous one
    // established under the same name, so an audited bound can never outlive
    // the element it was read from.
    st.dropNumericRoot(name);
    for (audits.items) |audit| {
        if (!std.mem.eql(u8, audit.container, container)) continue;
        const target = try internPath(o, name, audit.field);
        const bound: NumericRange = .{ .integer = .{ .min = 0, .max = audit.limit } };
        try st.setNumeric(o.gpa, target, st.numericValue(target).intersect(bound));
    }
}

pub fn isLocalName(o: *const Oracle, name: []const u8) bool {
    for (o.locals) |binding| if (std.mem.eql(u8, binding.name, name)) return true;
    return false;
}

/// What an expression can do to storage it does not name: nothing enumerable,
/// exactly one call, or every call a whole expression contains.
///
/// `.unknown` is the answer when the effects cannot be enumerated at all, and
/// it is what a `null` effect used to mean — so every path counted as reached
/// and every fact on a field path was dropped.  That is the only sound answer
/// when the effects really are unknown, but it was being given for effects
/// that ARE enumerable: an assignment's whole expression, and a `catch`
/// handler's, were both charged as if an arbitrary callee could run there.
/// `.subtree` names the expression instead of admitting ignorance, and the
/// scan below is what turns it back into a per-path answer.
pub const Reach = union(enum) {
    unknown,
    one: Ast.Node.Index,
    subtree: Ast.Node.Index,

    /// `pub` because the escape model is a separate module and every survivor
    /// question it asks is this one: the statement walk owns the policy, the
    /// module that owns the reach model calls it.  It is the same question for
    /// every caller, so it is answered here once rather than re-implemented
    /// per shape.
    pub fn reaches(self: Reach, o: *Oracle, path: []const u8) bool {
        return switch (self) {
            .unknown => true,
            .one => |node| numeric_escape.pathEscapedBy(o, node, path),
            .subtree => |root| blk: {
                var scan: numeric_escape.EffectScan = .{};
                numeric_escape.scanEffects(o, root, &scan, 0);
                break :blk scan.reaches(o, path);
            },
        };
    }
};

/// Invalidate the facts reachable from `effect`.  `.unknown` is the answer
/// when the effects cannot be enumerated, and it drops every container, alias
/// and product fact; a named effect keeps the ones it cannot reach.
pub fn dropIndirectFacts(o: *Oracle, st: *State, effect: Reach) void {
    // Every root whose ADDRESS this body takes is a root some effect can write
    // through — but WHICH of them THIS effect can write is the reach model
    // above, not the whole-body `addressed` set.  Applying `addressed` on its
    // own here meant one `&x` anywhere dropped every container fact, every
    // recorded constant and every difference fact about `x` at every call in
    // the body, including a call handed the address of a different name and a
    // callee that provably never writes `x`.  Each root is now asked whether
    // this effect reaches it, which still answers `true` for an effect that
    // cannot be read.
    for (o.addressed.keys.items) |root| {
        if (!effect.reaches(o, root)) continue;
        dropContainersRootedAt(st, root);
        st.dropScalarValsRootedAt(root);
        st.dropDiffAliasesByName(root);
    }
    var scalar: usize = 0;
    while (scalar < st.scalars.keys.items.len) {
        if (!numeric_escape.scalarSurvivesCall(o, st.scalars.keys.items[scalar], effect)) {
            const removed = st.scalars.keys.swapRemove(scalar);
            std.debug.assert(!numeric_escape.scalarSurvivesCall(o, removed, effect));
        } else scalar += 1;
    }
    var bound: usize = 0;
    while (bound < st.scalar_mins.items.len) {
        if (!numeric_escape.scalarSurvivesCall(o, st.scalar_mins.items[bound].name, effect)) {
            const removed = st.scalar_mins.swapRemove(bound);
            std.debug.assert(!numeric_escape.scalarSurvivesCall(o, removed.name, effect));
        } else bound += 1;
    }
    var numeric: usize = 0;
    while (numeric < st.numeric.items.len) {
        if (!numeric_escape.scalarSurvivesCall(o, st.numeric.items[numeric].name, effect)) {
            _ = st.numeric.swapRemove(numeric);
        } else numeric += 1;
    }
    // A length snapshot is keyed by the same kind of name a range fact is,
    // and the effect that reaches a scalar reaches the slice header with it:
    // handing `&b` to a callee, or writing through a pointer alias, is what
    // can put a different slice in the slot the snapshot describes.
    var len_bound: usize = 0;
    while (len_bound < st.len_bounds.items.len) {
        if (!numeric_escape.scalarSurvivesCall(o, st.len_bounds.items[len_bound].name, effect)) {
            const removed = st.len_bounds.swapRemove(len_bound);
            std.debug.assert(!numeric_escape.scalarSurvivesCall(o, removed.name, effect));
        } else len_bound += 1;
    }
    var conditional: usize = 0;
    while (conditional < st.conditional_lengths.items.len) {
        const entry = st.conditional_lengths.items[conditional];
        if (!numeric_escape.scalarSurvivesCall(o, entry.header, effect) or
            !numeric_escape.scalarSurvivesCall(o, entry.selector, effect))
        {
            _ = st.conditional_lengths.swapRemove(conditional);
        } else conditional += 1;
    }
    var scalar_value: usize = 0;
    while (scalar_value < st.scalar_vals.items.len) {
        if (!numeric_escape.scalarSurvivesCall(o, st.scalar_vals.items[scalar_value].name, effect)) {
            const removed = st.scalar_vals.swapRemove(scalar_value);
            std.debug.assert(!numeric_escape.scalarSurvivesCall(o, removed.name, effect));
        } else scalar_value += 1;
    }
    var container: usize = 0;
    while (container < st.containers.keys.items.len) {
        if (!numeric_escape.containerSurvivesCall(o, st.containers.keys.items[container], effect)) {
            _ = st.containers.keys.swapRemove(container);
        } else container += 1;
    }
    var min_len: usize = 0;
    while (min_len < st.min_lens.items.len) {
        if (!numeric_escape.containerSurvivesCall(o, st.min_lens.items[min_len].path, effect)) {
            _ = st.min_lens.swapRemove(min_len);
        } else min_len += 1;
    }
    var alias: usize = 0;
    while (alias < st.aliases.items.len) {
        const entry = st.aliases.items[alias];
        if (!numeric_escape.containerSurvivesCall(o, entry.container, effect) or
            !numeric_escape.scalarSurvivesCall(o, entry.scalar, effect))
        {
            _ = st.aliases.swapRemove(alias);
        } else alias += 1;
    }
    var product: usize = 0;
    while (product < st.product_aliases.items.len) {
        const entry = st.product_aliases.items[product];
        if (!numeric_escape.scalarSurvivesCall(o, entry.result, effect) or
            !numeric_escape.productFactorSurvives(o, entry.left, effect) or
            !numeric_escape.productFactorSurvives(o, entry.right, effect))
        {
            _ = st.product_aliases.swapRemove(product);
        } else product += 1;
    }
    // These three are PAIRS, and each half is storage the other is read
    // through: `DIFF = A - B` keeps a claim that only holds while both of its
    // names still hold what it was taken from, `LOCAL = self.field` is a
    // snapshot of one storage under a second name, and a `@bitCast`-derived
    // local is a reinterpretation of one.  Clearing the whole list on any
    // effect threw that away for effects that reach neither half — a call
    // handed an unrelated argument, a write to a different field — and an
    // unrelated store costing a proof is a false positive of exactly the kind
    // these rules exist to avoid.
    //
    // Each entry is therefore asked the same reach question the families above
    // are asked, and survives only when the effect is PROVED not to reach
    // either of its names.  Nothing here preserves an entry on the strength of
    // what a name LOOKS like: an effect the reach model cannot enumerate still
    // answers `true` for every path, which is the direction that drops.
    var diff: usize = 0;
    while (diff < st.diff_aliases.items.len) {
        const entry = st.diff_aliases.items[diff];
        if (numeric_escape.pathSurvivesCall(o, entry.diff, effect) and
            numeric_escape.pathSurvivesCall(o, entry.minuend, effect)) diff += 1 else _ = st.diff_aliases.swapRemove(diff);
    }
    var value: usize = 0;
    while (value < st.value_aliases.items.len) {
        const entry = st.value_aliases.items[value];
        const other_survives = if (entry.other_path) |other|
            numeric_escape.pathSurvivesCall(o, other, effect)
        else
            true;
        if (numeric_escape.scalarSurvivesCall(o, entry.local, effect) and other_survives and
            numeric_escape.pathSurvivesCall(o, entry.path, effect)) value += 1 else _ = st.value_aliases.swapRemove(value);
    }
    var bit: usize = 0;
    while (bit < st.bit_aliases.items.len) {
        const entry = st.bit_aliases.items[bit];
        // `local` is empty for an alias that has not been bound to a name of
        // its own yet, and an empty name is storage nobody has a fact about.
        const local_kept = entry.local.len == 0 or
            numeric_escape.scalarSurvivesCall(o, entry.local, effect);
        if (local_kept and numeric_escape.pathSurvivesCall(o, entry.source, effect)) bit += 1 else _ = st.bit_aliases.swapRemove(bit);
    }
    st.clearPredicates();
}

pub fn analyzeNode(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    if (o.summary_error) |err| return err;
    const flow = try analyzeNodeInner(o, node, st);
    if (o.summary_error) |err| return err;
    return flow;
}

fn analyzeNodeInner(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    if (o.walk_depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return .{};
    }
    o.walk_depth += 1;
    defer o.walk_depth -= 1;
    if (!o.spend()) return .{};
    const tree = o.tree;
    switch (tree.nodeTag(node)) {
        .block, .block_semicolon, .block_two, .block_two_semicolon => {
            var buf: [2]Ast.Node.Index = undefined;
            return analyzeSeq(o, blockStmts(tree, node, &buf), st);
        },
        .@"if", .if_simple => return analyzeIf(o, node, st),
        .@"switch", .switch_comma => return analyzeSwitch(o, node, st),
        .@"while", .while_simple, .while_cont => return analyzeLoop(o, node, st, .while_),
        .@"for", .for_simple => return analyzeLoop(o, node, st, .for_),
        .simple_var_decl, .local_var_decl, .aligned_var_decl => return analyzeVarDecl(o, node, st),
        .assign => return analyzeAssign(o, node, st),
        .assign_destructure => {
            const rhs = tree.nodeData(node).extra_and_node[1];
            const flow = try analyzeNode(o, rhs, st);
            if (o.tokenInNode(rhs) and flow.answer != null) return flow;
            st.deinit(o.gpa);
            st.* = .{};
            return if (o.tokenInNode(node)) .{ .answer = o.answerAt(st) } else .{};
        },
        .assign_add => return analyzeCompoundAdd(o, node, st),
        .assign_mul,
        .assign_div,
        .assign_mod,
        .assign_sub,
        .assign_shl,
        .assign_shl_sat,
        .assign_shr,
        .assign_bit_and,
        .assign_bit_xor,
        .assign_bit_or,
        .assign_mul_wrap,
        .assign_add_wrap,
        .assign_sub_wrap,
        .assign_mul_sat,
        .assign_add_sat,
        .assign_sub_sat,
        => return analyzeCompoundMutation(o, node, st),
        // canonical guarded last-element idioms `c.len > 0 and c[c.len-1]` and
        // `c.len == 0 or c[c.len-1]` (endsWith/startsWith), where the bounds
        // proof lives in the same expression rather than an enclosing `if`.
        .bool_and => return analyzeShortCircuit(o, node, st, true),
        .bool_or => return analyzeShortCircuit(o, node, st, false),
        .call, .call_comma, .call_one, .call_one_comma => return analyzeCall(o, node, st),
        .@"return", .@"break", .@"continue", .unreachable_literal => {
            if (tree.nodeTag(node) == .@"break") {
                if (o.break_capture) |capture| {
                    if (tree.nodeData(node).opt_token_and_opt_node[0].unwrap() != null) {
                        capture.has_unresolved_target = true;
                    } else {
                        try capture.record(st);
                    }
                }
            }
            var flow: Flow = .{ .diverged = true };
            // Descend into a `return <expr>;` operand so short-circuit
            // refinement (bool_and/bool_or) applies before answering.
            const operand: ?Ast.Node.Index = if (tree.nodeTag(node) == .@"return")
                tree.nodeData(node).opt_node.unwrap()
            else
                null;
            if (operand) |expression| {
                if (o.predicate_capture) |capture| try capture.record(o, expression, st);
                if (o.return_summary) |summary| try summary.record(o, expression, st);
            } else if (tree.nodeTag(node) == .@"return") {
                // `return;` leaves nothing to join.  A body that reaches it is
                // not a body whose exits this can summarise, so the claim is
                // withdrawn rather than narrowed by the exits it did read.
                if (o.return_summary) |summary| summary.complete = false;
            }
            // Return operands can mutate the state or propagate a helper's
            // successful edge. Capture after those effects, never before.
            if (operand) |e| {
                const sub = try analyzeNode(o, e, st);
                if (o.tokenInNode(node)) flow.answer = sub.answer orelse o.answerAt(st);
                if (sub.diverged) return flow;
            } else if (o.tokenInNode(node)) flow.answer = o.answerAt(st);
            if (tree.nodeTag(node) == .@"return") {
                if (o.capture) |capture| {
                    const error_return = if (operand) |e| tree.nodeTag(unwrapGrouped(tree, e)) == .error_value else false;
                    if (capture.mode == .exit and (!capture.success_only or !error_return)) try capture.record(st);
                }
            }
            return flow;
        },
        .@"comptime" => {
            // Only a resolved standard assertion exports a predicate. The
            // assertion must succeed for any instantiation that can execute.
            const expression = tree.nodeData(node).node;
            var buffer: [1]Ast.Node.Index = undefined;
            if (tree.fullCall(&buffer, expression)) |call| {
                if (call.ast.params.len == 1 and
                    isStdAssert(o, call.ast.fn_expr, tree.firstToken(expression)))
                    try applyRefine(o, st, .{ .node = call.ast.params[0], .truth = true });
            }
            return .{};
        },
        .fn_decl, .container_decl, .container_decl_trailing, .container_decl_two, .container_decl_two_trailing, .container_decl_arg, .container_decl_arg_trailing => return .{},
        // `try <expr>` is a propagating edge: the statements after it run only
        // when the expression succeeded, which is what makes a fallible std
        // append's stored element a fact on this side of the call.
        .@"try" => return analyzeTry(o, node, st),
        .@"catch", .@"orelse" => {
            // The right operand runs only when the left one failed, so a use
            // inside it is analyzed on its own path: its own guards must be
            // seen, and the left operand's success facts must NOT be assumed.
            const data = tree.nodeData(node).node_and_node;
            if (o.tokenInNode(data[1])) {
                // Evaluate the failing operand first, then enter the fallback
                // with its actual effects. Mutations later in the fallback
                // cannot invalidate a guard before the indexed read.
                // The failing operand's own call has NOT returned, so what it
                // would establish on success is not available to the
                // handler running because it did not succeed.
                const saved = o.contract_effects_pending;
                o.contract_effects_pending = saved + 1;
                const left_flow = analyzeNode(o, data[0], st) catch |err| {
                    o.contract_effects_pending = saved;
                    return err;
                };
                o.contract_effects_pending = saved;
                if (left_flow.diverged) return left_flow;
                return try analyzeNode(o, data[1], st);
            }
            // The left operand is evaluated first and the fallback only runs
            // when it failed, so a use inside it sees the state as it stood
            // before the expression — not the state the fallback path wipes.
            if (o.tokenInNode(data[0])) {
                const left_flow = try analyzeNode(o, data[0], st);
                if (left_flow.answer != null or left_flow.diverged) return left_flow;
            }
            dropLoopMutated(o, node, st);
            // Both edges of the operator are live here, and both are inside
            // this expression: the caught expression runs first and the
            // handler runs only when it failed.  Naming the whole expression
            // is what keeps a handler that merely READS the storage a fact is
            // about from dropping that fact.
            dropIndirectFacts(o, st, .{ .subtree = node });
            return if (o.tokenInNode(node)) .{ .answer = o.answerAt(st) } else .{};
        },
        .@"defer" => {
            dropLoopMutated(o, node, st);
            dropIndirectFacts(o, st, .{ .subtree = tree.nodeData(node).node });
            return if (o.tokenInNode(node)) .{ .answer = o.answerAt(st) } else .{};
        },
        .@"errdefer" => {
            if (o.capture) |capture| {
                if (capture.success_only and !o.tokenInNode(node)) {
                    var buffer: [2]Ast.Node.Index = undefined;
                    for (blockStmts(tree, o.body, &buffer)) |statement| {
                        if (statement == node) return .{};
                    }
                }
            }
            dropLoopMutated(o, node, st);
            dropIndirectFacts(o, st, .{ .subtree = tree.nodeData(node).opt_token_and_node[1] });
            return if (o.tokenInNode(node)) .{ .answer = o.answerAt(st) } else .{};
        },
        else => return analyzeExpression(o, node, st),
    }
}

/// `try <expr>` is a propagating edge, so the fallible std appends modelled in
/// `recordAppendedElement` have stored their item by the time control reaches
/// the next statement.  The rest of the walk is the ordinary expression walk —
/// the operand has to be analysed for its own effects either way.
fn analyzeTry(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    const tree = o.tree;
    const inner = tree.nodeData(node).node;
    if (o.capture) |capture| {
        // A raw fallible call can leave through the error propagated here.
        // That edge is not walked, so it cannot export an all-exit contract.
        if (capture.mode == .exit and !capture.success_only) capture.complete = false;
    }
    const saved_success = o.successful_call;
    o.successful_call = unwrapGrouped(tree, inner);
    defer o.successful_call = saved_success;
    const flow = try analyzeNode(o, inner, st);
    if (o.tokenInNode(inner) and flow.answer != null) return flow;
    if (flow.diverged) return flow;
    if (o.tokenInNode(node)) return .{ .answer = o.answerAt(st) };
    // The operand invalidated its effects before installing its success
    // contracts. Repeating the invalidation would erase those contracts.
    try recordReadBounds(o, node, st);
    try recordAppendedElement(o, st, inner, true);
    try recordAssertedCondition(o, st, inner);
    return .{};
}

/// `try std.testing.expect(cond)` lets the statements after it run only when
/// `cond` held, so on this edge — and only on this edge — `cond` is proved.
///
/// The call itself proves nothing, and that is the whole difference from
/// `std.debug.assert`: an error union has to be handled, so the edge a reader
/// can be standing on after a bare `expect` is the FAILURE one, which is
/// where `cond` was false.  A `catch`/`orelse` that continues reaches exactly
/// that edge, so the fact is recorded here rather than in `analyzeCall` —
/// where recording it would prove the condition on the handler as well.
fn recordAssertedCondition(o: *Oracle, st: *State, expression: Ast.Node.Index) QueryError!void {
    const tree = o.tree;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, unwrapGrouped(tree, expression)) orelse return;
    if (!isStdExpect(o, call, tree.firstToken(expression))) return;
    try applyRefine(o, st, .{ .node = call.ast.params[0], .truth = true });
}

fn analyzeExpression(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    const tree = o.tree;
    if (tree.nodeTag(node) == .builtin_call or tree.nodeTag(node) == .builtin_call_two or
        tree.nodeTag(node) == .builtin_call_comma or tree.nodeTag(node) == .builtin_call_two_comma)
    {
        const name = tree.tokenSlice(tree.nodeMainToken(node));
        if (std.mem.eql(u8, name, "@TypeOf")) return .{};
    }
    var children = @import("type_engine").AstIterator.init(tree, node);
    while (children.next(tree)) |child| {
        const flow = try analyzeNode(o, child, st);
        if (o.tokenInNode(child) and flow.answer != null) return flow;
    }
    if (mayMutateIndirect(o, node)) dropIndirectFacts(o, st, .{ .one = node });
    if (o.tokenInNode(node)) return .{ .answer = o.answerAt(st) };
    killMutatedContainers(o, node, st);
    try recordReadBounds(o, node, st);
    return .{};
}

/// A dominating read `c[i]` bounds `c` from below: for a slice the index is
/// checked against `.len`, so reaching the statement means `i < c.len`.  That
/// only carries a length fact when the receiver is a container whose own type
/// bounds the index — a slice or a fixed-size array.  A C pointer (`[*c]T`),
/// a many-pointer (`[*]T`) or a single pointer (`*T`) has no `.len` at all, so
/// indexing one proves nothing about any length.
fn recordReadBounds(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!void {
    const tree = o.tree;
    var container: Ast.Node.Index = undefined;
    var minimum: u64 = 0;
    if (tree.nodeTag(node) == .array_access) {
        const parts = tree.nodeData(node).node_and_node;
        container = parts[0];
        const index = exprMin(o, st, parts[1]) orelse 0;
        minimum = std.math.add(u64, index, 1) catch return;
    } else if (tree.fullSlice(node)) |slice| {
        container = slice.ast.sliced;
        minimum = exprMin(o, st, slice.ast.start) orelse return;
    } else return;
    if (minimum == 0 or !isPureFieldPath(tree, container)) return;
    if (!isLengthBoundedReceiver(o, container)) return;
    try applyRefineFacts(o, st, .{}, .{ .name = nodeSrc(tree, container), .min = minimum }, null);
}

/// Is `receiver` a value whose own length bounds every index into it?
///
/// The RECEIVER's type decides this, and the root's type is only the
/// receiver's own when the two are the same name.  A field of a struct is a
/// different value with a different type: `struct { items: []u8, next: *u8 }`
/// gives the root a length that `next` does not have, and answering from the
/// root records a non-empty fact about storage a pointer cannot bound.  So a
/// dotted receiver is answered only from a root type that is not written out
/// as an aggregate — one whose fields are the only place a length could hide.
fn isLengthBoundedReceiver(o: *Oracle, receiver: Ast.Node.Index) bool {
    const tree = o.tree;
    const spelling = nodeSrc(tree, receiver);
    const root = numeric_escape.rootText(spelling);
    const declared = declaredTypeOf(o, root, tree.firstToken(receiver)) orelse
        return false;
    if (!declaredTypeIsBounded(tree, declared)) return false;
    if (std.mem.eql(u8, spelling, root)) return true;
    return !typeIsAggregate(tree, declared);
}

/// Is this written type a struct, union or opaque spelled out in full, so
/// that it carries fields whose own types the root's bracket does not speak
/// for?
fn typeIsAggregate(tree: *const Ast, type_node: Ast.Node.Index) bool {
    const tags = tree.tokens.items(.tag);
    var token = tree.firstToken(type_node);
    const last = tree.lastToken(type_node);
    while (token <= last) : (token += 1) {
        if (tags[token] == .l_brace) return true;
    }
    return false;
}

/// The written type `name` has at the use at `at` — a parameter's type
/// annotation or an annotated `const`/`var`.
///
/// The use is written inside the blocks, so those are what answer first: a
/// local is visible from its own declaration to the end of its block, and a
/// same-named binding in a sibling block is a different value with a
/// different type that must not supply one.  A parameter is the enclosing
/// scope of all of them and answers only when no local in scope claims the
/// name — consulting it first would type a use by a binding that is not the
/// one the source names at `at`, and an unannotated local has to leave the
/// domain unresolved rather than fall through to somebody else's.  Lexical on
/// purpose: queries reach this oracle without the type engine (the
/// `.ptr[0..N]` rule passes a null cache), so the proof must not depend on
/// one.
fn declaredTypeOf(o: *Oracle, name: []const u8, at: Ast.TokenIndex) ?Ast.Node.Index {
    const tree = o.tree;
    var scope: [16]Ast.Node.Index = undefined;
    const depth = enclosingBlocks(o, at, &scope);
    var statements: [2]Ast.Node.Index = undefined;
    for (scope[0..depth]) |block| {
        for (blockStmts(tree, block, &statements)) |statement| {
            if (tree.firstToken(statement) > at) break;
            switch (tree.nodeTag(statement)) {
                .simple_var_decl, .local_var_decl, .aligned_var_decl => {},
                else => continue,
            }
            const decl = tree.fullVarDecl(statement) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(decl.ast.mut_token + 1), name)) continue;
            // An unannotated local has no type to answer with.  That is a
            // different thing from a panicking `unwrap`: the question this
            // function answers is what a name is DECLARED to be, and a source
            // that does not say declares nothing.
            return decl.ast.type_node.unwrap();
        }
    }
    const declaration = enclosingFnDecl(o) orelse return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
    var params = proto.iterate(tree);
    while (params.next()) |param| {
        const name_token = param.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), name)) continue;
        return param.type_expr;
    }
    return null;
}

/// This file's indexed nodes, in node-array order.
///
/// OWNED by `nodes_owned` and released by `deinit` with the rest of what the
/// oracle owns.  Null in `nodes` means "not asked yet", never "found none" —
/// a completed empty index is a published empty slice, and a build that
/// FAILED sets `out_of_memory` instead.
///
/// The failure convention is the `out_of_memory` one the block index already
/// used: an index that could not be built is reported as such and every entry
/// point turns that into `error.OutOfMemory`, rather than answering from what
/// is missing.  An index that could not be built and an EMPTY index are
/// different answers, and `requiredNodes` below is what keeps them apart.
fn fileNodes(o: *Oracle) []const Ast.Node.Index {
    if (o.nodes) |borrowed| return borrowed;
    const tree = o.tree;
    // Sparse, so there is nothing to pre-size: the list grows to what the file
    // actually holds of these tags, which is a small fraction of the node
    // table, and a sized list would reserve for nodes it never keeps.
    //
    // Ownership moves to `nodes_owned` only on the last line.  The `catch` arm
    // frees what it built and returns — an `errdefer` would NOT run there,
    // because that arm returns normally, which is exactly the shape that
    // leaks the partial list.
    var index: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
    for (tree.nodes.items(.tag), 0..) |tag, i| {
        if (!numeric_nodes.isIndexedTag(tag)) continue;
        index.append(o.gpa, @enumFromInt(i)) catch {
            index.deinit(o.gpa);
            o.out_of_memory = true;
            return &.{};
        };
    }
    o.nodes_owned = index;
    o.nodes = o.nodes_owned.items;
    return o.nodes_owned.items;
}

/// `fileNodes` for a caller whose EMPTY answer would be a wrong answer rather
/// than a missing proof.
///
/// `comptimeAudits` CACHES what it derives, and would otherwise cache "this
/// file has no compile-time audits" out of an index that only failed to build,
/// so it propagates and that becomes `error.OutOfMemory` at the query entry
/// instead of a fact the walk cannot support.  The remaining callers —
/// `enclosingFnDecl`, `enclosingBlocks`, `callerBody` — can only lose a proof,
/// and each already reports the failure through `out_of_memory` at the entry.
/// Both facts are read here, and both are set only on a build that FAILED,
/// never on a build that completed and found nothing.
///
/// The escape model caches its own reading too, and for the same reason, but
/// it does not come through here: it has a body-keyed index of its own
/// (`numeric_escape.bodyEscapeIndex`) rather than a slice of this one, so it
/// propagates the cache's own error rather than reading `out_of_memory`.
fn requiredNodes(o: *Oracle) error{OutOfMemory}![]const Ast.Node.Index {
    const nodes = fileNodes(o);
    if (o.out_of_memory) return error.OutOfMemory;
    return nodes;
}

/// Blocks whose tokens contain `at`, innermost first, and how many were
/// found.  Nesting deeper than `scope.len` leaves the outer blocks unvisited:
/// a binding found only there stays unresolved, which costs a proof but never
/// takes a wrong one.
///
/// The block nodes are read out of the one per-query node index, so building
/// them costs no second walk of the file's node array.  A list that could not
/// be built is not a shorter list: a missing block hides the local that would
/// have answered, and the parameter's type would answer in its place, which is
/// a wrong reading rather than a lost proof.  That is the failure
/// `out_of_memory` already reports.
fn enclosingBlocks(
    o: *Oracle,
    at: Ast.TokenIndex,
    scope: *[16]Ast.Node.Index,
) usize {
    if (!o.blocks_built) {
        o.blocks_built = true;
        const tree = o.tree;
        for (fileNodes(o)) |node| {
            switch (tree.nodeTag(node)) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => {},
                else => continue,
            }
            o.blocks.append(o.gpa, node) catch {
                o.blocks.clearRetainingCapacity();
                o.out_of_memory = true;
                return 0;
            };
        }
    }
    const tree = o.tree;
    var len: usize = 0;
    for (o.blocks.items) |node| {
        if (tree.firstToken(node) > at or tree.lastToken(node) < at) continue;
        // Keep the order by first token descending: nested blocks open later.
        var position: usize = 0;
        while (position < len and tree.firstToken(scope[position]) > tree.firstToken(node)) : (position += 1) {}
        if (position == len) {
            if (len == scope.len) break;
            len += 1;
        } else {
            var shift = len;
            while (shift > position) : (shift -= 1) scope[shift] = scope[shift - 1];
        }
        scope[position] = node;
    }
    return len;
}

/// The `fn_decl` whose body the oracle analyzes, or null for a synthetic body.
/// Resolved once per query and then read back: every caller of this wants the
/// same node, and the walk that finds it costs the whole file's node array.
/// The answer is a property of the BODY, which an oracle carries for its whole
/// life and never replaces, so a memo cannot go stale under it.
pub fn enclosingFnDecl(o: *Oracle) ?Ast.Node.Index {
    if (o.fn_decl_resolved) return o.fn_decl;
    o.fn_decl_resolved = true;
    const tree = o.tree;
    for (fileNodes(o)) |node| {
        if (tree.nodeTag(node) != .fn_decl) continue;
        if (tree.nodeData(node).node_and_node[1] == o.body) {
            o.fn_decl = node;
            return node;
        }
    }
    return null;
}

/// A written type that bounds its own indices: `[]T` (any slice) or `[N]T`
/// with `N >= 1`.  Everything else — `*T`, `[*c]T`, `[*]T`, the sentinel-
/// terminated `[0:N]T`, an unannotated binding, a name — bounds no index.
///
/// The WHOLE expression is scanned rather than answered at its first bracket.
/// A type written out in full carries brackets of its own, and stopping at the
/// first one read a struct's slice FIELD as a length for every field of that
/// struct.  A pointer anywhere in the type therefore bounds nothing: the
/// question is whether this value carries a length at all, and one field
/// having one says nothing about the field being asked about.
fn declaredTypeIsBounded(tree: *const Ast, type_node: Ast.Node.Index) bool {
    const tags = tree.tokens.items(.tag);
    const last = tree.lastToken(type_node);
    var bounded = false;
    var token = tree.firstToken(type_node);
    while (token <= last) : (token += 1) {
        switch (tags[token]) {
            .asterisk, .asterisk_asterisk => return false,
            .l_bracket => {
                if (token + 1 > last) return false;
                // `[]T` — any slice carries a length.
                if (tags[token + 1] == .r_bracket) {
                    bounded = true;
                } else {
                    // `[*c]T` and `[*]T` carry none.
                    if (tags[token + 1] != .number_literal) return false;
                    if (token + 2 > last or tags[token + 2] != .r_bracket) return false;
                    const count = std.fmt.parseInt(u64, tree.tokenSlice(token + 1), 0) catch return false;
                    // `[N]T` bounds an index only when `N >= 1`; `[0:N]T` is a
                    // sentinel-terminated C array and bounds none.
                    if (count >= 1) bounded = true;
                }
            },
            else => {},
        }
    }
    return bounded;
}

fn analyzeCall(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    const tree = o.tree;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node).?;
    if (o.query == .numeric_range) {
        if (o.expression) |expression| {
            const queried = unwrapGrouped(tree, expression);
            if (tree.nodeTag(queried) == .field_access) {
                const field = tree.nodeData(queried).node_and_token;
                if (unwrapGrouped(tree, field[0]) == node and
                    std.mem.eql(u8, tree.tokenSlice(field[1]), "len"))
                {
                    // Arguments are copied before this call can rewrite
                    // their sources. A post-call re-read would describe a
                    // different header, even at this same AST occurrence.
                    var returned: State = .{};
                    defer returned.deinit(o.gpa);
                    try callReturnLengths(o, st, node, &returned, "");
                    o.queried_return_length = returned.lenBoundOf("") orelse .unknown;
                }
            }
        }
    }
    // The callee expression is evaluated before the arguments and long
    // before the callee body runs, so a use inside it — a subscript of a
    // method receiver, say — is answered against the state as it stood when
    // the call started, not against the state left by the call's own effects.
    if (o.tokenInNode(call.ast.fn_expr)) {
        const receiver_flow = try analyzeNode(o, call.ast.fn_expr, st);
        if (receiver_flow.answer != null or receiver_flow.diverged) return receiver_flow;
    }
    for (call.ast.params) |parameter| {
        const flow = try analyzeNode(o, parameter, st);
        if (o.tokenInNode(parameter) and flow.answer != null) return flow;
        if (flow.diverged) return flow;
    }
    // What the caller HELD is the domain the callee is entered with, so it
    // is read BEFORE the call's own effects are dropped below.  The drop is
    // right about the value after the call and knows nothing about the value
    // before it, and the facts it takes are exactly the ones a callee
    // WRITES: a method call hands its receiver over as `&recv`, so `grow`
    // taking `self.len` takes the caller's `builder.len` with it.  That is
    // right for the state after the call and fatal for the state before it —
    // read afterwards, the entry domain is missing the very path the callee
    // is about, `recordAbsentExitFact` finds no entry value for it and fills
    // the exits that left before the write with the declared `usize`, and the
    // length the callee left comes back as wide as its type.  The arguments
    // and the receiver were read before the callee ran, so none of this can
    // change the answer for this use either.
    var held: [max_contract_entry_facts]numeric_eval.Fact = undefined;
    const held_count = if (o.query == .numeric_range or o.query == .min_len_container) holdNumericFacts(st, &held) else 0;
    // This is the one drop of what the call reached: `dropEscapedScalarFacts`
    // has already run exactly this on this very node on the way here, so the
    // explicit copy that used to follow was a second full pass over every fact
    // in the state — one callee-body scan per fact, charged again.
    killMutatedContainers(o, node, st);
    // A verified std append that cannot fail has already stored its item by
    // the time it returns, so the fact holds on every edge out of the call.
    // The fallible spelling only does so on its success edge, which the
    // `try` case above models.
    try recordAppendedElement(o, st, node, false);
    if (call.ast.params.len == 1 and isStdAssert(o, call.ast.fn_expr, tree.firstToken(node))) {
        try applyRefine(o, st, .{ .node = call.ast.params[0], .truth = true });
    }
    // After the effects above, so a contract about what the callee leaves
    // behind is not then dropped as one of the callee's own writes.
    try applyCallContracts(o, st, node, held[0..held_count]);
    return if (o.tokenInNode(node)) .{ .answer = o.answerAt(st) } else .{};
}

/// A `std/array_list.zig` single-element append stores exactly one item, so
/// the receiver's `.items` slice is non-empty from the edge the item is stored
/// on: every edge out of an infallible `appendAssumeCapacity`, and the success
/// edge of a fallible `append` reached through `try`.  A `catch`/`orelse` that
/// continues runs the failure edge instead, where nothing was stored; a call
/// whose declaration is not std's own never matches, so a custom no-op
/// `append` proves nothing — and neither does `appendSlice`, which may be
/// handed an empty slice.  Whatever invalidates the receiver afterwards (a
/// later mutating call on it, a write through it, a rebinding) already drops
/// this key through the ordinary mutation paths.
fn recordAppendedElement(
    o: *Oracle,
    st: *State,
    expression: Ast.Node.Index,
    propagating: bool,
) error{OutOfMemory}!void {
    const tree = o.tree;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, unwrapGrouped(tree, expression)) orelse return;
    if (tree.nodeTag(call.ast.fn_expr) != .field_access) return;
    const callee = tree.nodeData(call.ast.fn_expr).node_and_token;
    // Cheap pre-filter only — the verdict still comes from the resolved
    // declaration — so the type engine is not asked about every call in every
    // walked body.
    const method = tree.tokenSlice(callee[1]);
    if (!std.mem.eql(u8, method, "append") and !std.mem.eql(u8, method, "appendAssumeCapacity")) return;
    const receiver = callee[0];
    // A computed receiver (`getList().append(x)`) has no stable spelling for a
    // later `.items` read to be keyed on, so only a field path carries it.
    if (!isPureFieldPath(tree, receiver)) return;
    const resolver = (o.cache orelse return).zls orelse return;
    switch (resolver.stdCollectionAppendOf(call.ast.fn_expr, call.ast.params.len) catch return) {
        .no => return,
        .fallible => if (!propagating) return,
        .infallible => {},
    }
    const path = try o.itemsPath(nodeSrc(tree, receiver));
    try st.containers.add(o.gpa, path);
    try st.setMinLen(o.gpa, path, 1);
}

fn isStdAssert(o: *Oracle, callee: Ast.Node.Index, anchor: Ast.TokenIndex) bool {
    return std.mem.eql(u8, nodeSrc(o.tree, callee), "std.debug.assert") and stdBindingValidAt(o, anchor);
}

/// The one-argument `std.testing.expect`, which reports whether a condition
/// held by RETURNING an error rather than by panicking.
///
/// It is a different contract from `std.debug.assert` and the two are
/// therefore not interchangeable: what the call proves depends on which edge
/// out of it the reader is standing on. The exact `std` spelling keeps its
/// token-only binding proof; aliases require the declaring toolchain document,
/// so a project function with the same name proves nothing here.
fn isStdExpect(o: *Oracle, call: Ast.full.Call, anchor: Ast.TokenIndex) bool {
    if (call.ast.params.len != 1) return false;
    if (std.mem.eql(u8, nodeSrc(o.tree, call.ast.fn_expr), "std.testing.expect") and
        stdBindingValidAt(o, anchor)) return true;
    const resolver = (o.cache orelse return false).zls orelse return false;
    return resolver.stdTestingExpectOf(call.ast.fn_expr, call.ast.params.len) catch |err| {
        o.summary_error = o.summary_error orelse err;
        return false;
    };
}

/// A standard assertion, which only ever READS the storage its condition
/// names.  Treating either one as an arbitrary callee would drop facts for
/// writes that cannot happen.
fn isStdAssertion(o: *Oracle, call: Ast.full.Call, anchor: Ast.TokenIndex) bool {
    return isStdAssert(o, call.ast.fn_expr, anchor) or isStdExpect(o, call, anchor);
}

fn isPureStdCall(o: *Oracle, callee: Ast.Node.Index, anchor: Ast.TokenIndex) bool {
    const name = nodeSrc(o.tree, callee);
    const pure = [_][]const u8{
        "std.math.minInt",   "std.math.maxInt", "std.math.inf",   "std.math.nan",
        "std.math.isFinite", "std.math.isNan",  "std.math.isInf", "std.math.clamp",
    };
    for (pure) |candidate| {
        if (std.mem.eql(u8, name, candidate)) return stdBindingValidAt(o, anchor);
    }
    return false;
}

fn analyzeSeq(o: *Oracle, stmts: []const Ast.Node.Index, st: *State) QueryError!Flow {
    for (stmts) |s| {
        const flow = try analyzeNode(o, s, st);
        if (flow.answer != null) return flow;
        if (flow.diverged) return flow;
    }
    return .{};
}

fn analyzeVarDecl(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    const tree = o.tree;
    const decl = tree.fullVarDecl(node) orelse return .{};
    const name = tree.tokenSlice(decl.ast.mut_token + 1);
    const init_node = decl.ast.init_node.unwrap() orelse {
        dropFactsForRebind(o, st, name);
        return .{};
    };
    const call_nonzero = callResultNonzero(o, init_node, st);
    // ONE reading of the allocator contract this initializer relies on: the
    // callee's identity and the purity of its count are settled once, and the
    // lower bound and the length range then read the same count node.
    const alloc_count = stdAllocCountNode(o, init_node);
    const allocated_minimum = allocatedMinimum(o, st, alloc_count);
    // Numeric and minimum-length queries need the same count interval.
    const allocated_length = if (o.query == .numeric_range or o.query == .min_len_container)
        allocatedLengthRange(o, st, alloc_count)
    else
        null;
    var aggregate_lengths: State = .{};
    defer aggregate_lengths.deinit(o.gpa);
    // The value arguments are copied before a call can mutate their sources.
    // A query inside the initializer still stops before that call executes.
    if (!o.tokenInNode(init_node) and (o.query == .numeric_range or o.query == .min_len_container))
        try callReturnLengths(o, st, init_node, &aggregate_lengths, name);
    const init_flow = try analyzeNode(o, init_node, st);
    if (o.tokenInNode(init_node) and init_flow.answer != null) return init_flow;
    const initializer_length: NumericRange = if (o.query == .numeric_range or o.query == .min_len_container) blk: {
        var evaluation = evaluator(o, st);
        // A fixed declared type also supplies an extent when its initializer
        // is undefined. Dynamic slice headers never gain a bound from type.
        break :blk evaluation.containerLength(init_node).intersect(evaluation.containerLength(node));
    } else .unknown;
    const init_min = exprMin(o, st, init_node) orelse
        if (parameterNonnegative(o, decl.ast.type_node.unwrap())) @as(?u64, 0) else null;
    const init_numeric = try numericAssignment(o, st, init_node, node);
    if (o.query == .numeric_range or o.query == .min_len_container) {
        if (pureAggregateExpression(o, init_node, 0))
            try recordAggregateLengths(o, st, &aggregate_lengths, init_node, name, 0);
    }
    const bit_alias = if (o.query == .numeric_range) bitAliasOf(o, st, init_node, 0) else null;
    // Re-binding `name` invalidates prior facts/aliases keyed on it.
    dropFactsForRebind(o, st, name);
    // A declaration the walk could not evaluate has still replaced the
    // binding, and it leaves the DECLARED type behind rather than the interval
    // a guard had recorded for a value that is gone — the same rule the
    // assignment path applies, and for the same reason.
    if (o.query == .numeric_range or o.query == .min_len_container) {
        try st.setNumeric(o.gpa, name, assignedRange(o, st, name, init_numeric, tree.firstToken(node), decl.ast.type_node.unwrap() orelse node));
    }
    if (bit_alias) |recorded| {
        var alias = recorded;
        alias.local = name;
        try st.bit_aliases.append(o.gpa, alias);
    }
    if (init_min) |min| {
        try st.setScalarMin(o.gpa, name, min);
        if (min >= 1) try st.scalars.add(o.gpa, name);
    }
    // Record a `const name = <field-path>` value alias (e.g.
    // `const bit_length = self.bit_length`): name and the path are equal, so a
    // guard on `name` later proves the path non-zero (see argProvablyNonzero).
    if (fieldPathSrc(o, init_node)) |psrc| {
        try st.addValueAlias(o.gpa, .{ .local = name, .path = psrc });
    }
    if (o.query == .numeric_range) {
        try recordCheckedAddAliases(o, st, init_node, name);
    }
    if (o.query == .numeric_range) {
        var evaluation = evaluator(o, st);
        const destination_width = evaluation.floatBits(node) orelse width: {
            const resolver = (o.cache orelse break :width null).zls orelse break :width null;
            if ((resolver.typeParameterReference(node) catch null) == null) break :width null;
            break :width computedFloatBitsAtDepth(o, node, 0, .minimum);
        };
        if (destination_width) |width| {
            if (floatBitSource(o, st, init_node, width, node)) |source| {
                if (!source.absolute) try st.addValueAlias(o.gpa, .{ .local = name, .path = source.source });
            }
        }
    }
    // Cross-fn: `const name = callee(arg)` where `callee` provably returns a
    // non-zero value given a non-zero argument (e.g. ceil-division `numMasks`),
    // and `arg` is proven non-zero here.  Then `name` is non-zero.
    if (call_nonzero) {
        try st.scalars.add(o.gpa, name);
        try st.setScalarMin(o.gpa, name, 1);
    }
    if (allocated_minimum) |minimum| {
        try st.setMinLen(o.gpa, name, minimum);
        if (minimum > 0) try st.containers.add(o.gpa, name);
    }
    // `alloc(T, n)` returns exactly `n` elements, so `name.len` is the count —
    // and the count is a RANGE, recorded whole at this binding.  A count this
    // walk could not bound records nothing here and `name.len` stays as wide
    // as the declared `usize`; a later write to `name` drops the entry
    // through the ordinary rebind path rather than leaving a length behind
    // that describes a slice that is no longer there.
    if (allocated_length) |length| try st.setLenBound(o.gpa, name, length);
    if (initializer_length != .unknown) try st.setLenBound(o.gpa, name, initializer_length);
    for (aggregate_lengths.len_bounds.items) |field|
        try st.setLenBound(o.gpa, field.name, field.value);
    for (aggregate_lengths.conditional_lengths.items) |entry|
        try st.addConditionalLength(o.gpa, entry);
    // Record a `const/var name = <c>.len` length-snapshot alias.
    if (lenContainerPath(o, init_node)) |cpath| {
        try st.addAlias(o.gpa, .{ .scalar = name, .container = cpath });
    }
    // Record a `const/var name = base[0..N]` slice alias: name.len == N (same
    // semantics as a `.len` snapshot, scalar=N container=name).  So a nonzero N
    // ⟹ name non-empty, making `name[name.len - 1]` safe.  Restricted to a `0`
    // start so the length is exactly the single scalar N.
    if (sliceLenScalarName(o, init_node)) |nname| {
        try st.addAlias(o.gpa, .{ .scalar = nname, .container = name });
        // Immediate propagation: if N is already proven nonzero (e.g. a prior
        // `if (N == 0) return` guard), `name` is non-empty right now.
        if (st.scalars.contains(nname)) try st.containers.add(o.gpa, name);
    }
    // `const tail = base[start..]` under a retained `start < base.len` holds at
    // least `base.len - start >= 1` elements.  The order is the guard's own
    // strict predicate, read as written, so it dies wherever a predicate does.
    if (tree.fullSlice(init_node)) |slice| {
        if (slice.ast.end == .none and startBelowLength(o, st, slice.ast.sliced, slice.ast.start)) {
            try st.setMinLen(o.gpa, name, 1);
            try st.containers.add(o.gpa, name);
        }
    }
    // Record a `const/var name = MINUEND - SUBTRAHEND` diff alias.
    // Used to propagate: when `name` is proven nonzero AND the subtrahend
    // is provably >= 0 (non-negative literal, .len, or unsigned by type engine),
    // then MINUEND is also nonzero (MINUEND > SUBTRAHEND >= 0 → MINUEND >= 1).
    if (tree.nodeTag(init_node) == .sub) {
        const sub_data = tree.nodeData(init_node).node_and_node;
        if (identName(tree, sub_data[0])) |lhs_name| {
            try st.addDiffAlias(o.gpa, .{
                .diff = name,
                .minuend = lhs_name,
                .sub_node = sub_data[1],
            });
        }
    }
    try recordProductAliases(o, st, name, init_node);
    try recordAuditedElementFacts(o, st, name, init_node);
    return .{};
}

fn analyzeAssign(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    const tree = o.tree;
    const data = tree.nodeData(node).node_and_node;
    const lhs = data[0];
    const rhs = data[1];
    // The use may be in the LHS index expression of a subscript write
    // (`buf[idx - 1] = …`).  The index is READ before the store, so answer the
    // query against the current state — otherwise a provably-nonzero index on
    // the write side is never resolved and the rule false-positives.
    if (o.tokenInNode(lhs)) {
        const flow = try analyzeNode(o, lhs, st);
        if (flow.answer != null) return flow;
    }
    var aggregate_lengths: State = .{};
    defer aggregate_lengths.deinit(o.gpa);
    if (!o.tokenInNode(rhs) and (o.query == .numeric_range or o.query == .min_len_container)) {
        if (scalarPath(o, lhs)) |name|
            try callReturnLengths(o, st, rhs, &aggregate_lengths, name);
    }
    const rhs_flow = try analyzeNode(o, rhs, st);
    if (o.tokenInNode(rhs) and rhs_flow.answer != null) return rhs_flow;
    const rhs_min = exprMin(o, st, rhs);
    const rhs_numeric = try numericAssignment(o, st, rhs, lhs);
    const rhs_length: NumericRange = if (o.query == .numeric_range or o.query == .min_len_container) blk: {
        var evaluation = evaluator(o, st);
        const length = evaluation.containerLength(rhs);
        if (o.cache) |cache| if (cache.fixedArrayLenOf(lhs)) |fixed|
            break :blk length.intersect(NumericRange.constant(fixed));
        break :blk length;
    } else .unknown;
    if (o.query == .numeric_range or o.query == .min_len_container) if (scalarPath(o, lhs)) |name| {
        if (pureAggregateExpression(o, rhs, 0))
            try recordAggregateLengths(o, st, &aggregate_lengths, rhs, name, 0);
    };
    const stored_source = if (rhs_min != null) sameIntegerElementSource(o, lhs, rhs) else null;
    // The written target is inside this expression, so the scan records it as
    // a write; what a right-hand call reaches is recorded as a call.  Neither
    // needs the "unknown effects" answer this used to give.
    if (tree.nodeTag(lhs) != .identifier) dropIndirectFacts(o, st, .{ .subtree = node });
    if (scalarPath(o, lhs)) |name| {
        dropFactsForRebind(o, st, name);
        // `alias.index = 0` and `state.index = 0` are the same store when the
        // body bound `alias` to `state`, so the facts keyed on the other
        // spelling describe storage that has moved.
        //
        // A store that goes THROUGH the pointer writes the storage behind it;
        // a bare rebind of it does not.  `p = other` writes the slot `p` lives
        // in and nothing else — the storage `p` used to name keeps exactly the
        // value the guard described, and invalidating it here would claim the
        // assignment rewrote an object it never mentions.  That is what lets
        // the bound a guard recorded under the storage's own spelling survive,
        // instead of travelling to whatever `p` names next.
        //
        // The write-through side resolves the WHOLE chain, keeps the field
        // projection the store carries, and drops conservatively when the
        // chain does not end — see `dropAliasedWrite` below.
        if (tree.nodeTag(lhs) != .identifier) {
            try dropAliasedWrite(o, st, name, tree.firstToken(node));
        }
        if (o.query == .numeric_range or o.query == .min_len_container) {
            try st.setNumeric(o.gpa, name, assignedRange(o, st, name, rhs_numeric, tree.firstToken(node), lhs));
            try recordAbsentExitFact(o, name, lhs);
            if (rhs_length != .unknown) try st.setLenBound(o.gpa, name, rhs_length);
            for (aggregate_lengths.len_bounds.items) |field|
                try st.setLenBound(o.gpa, field.name, field.value);
            for (aggregate_lengths.conditional_lengths.items) |entry|
                try st.addConditionalLength(o.gpa, entry);
        }
        if (rhs_min) |min| {
            try st.setScalarMin(o.gpa, name, min);
            if (min >= 1) try st.scalars.add(o.gpa, name);
        }
        // A re-bind to `c.len` re-establishes the alias.
        if (lenContainerPath(o, rhs)) |cpath| try st.addAlias(o.gpa, .{ .scalar = name, .container = cpath });
        try recordProductAliases(o, st, name, rhs);
    } else {
        // Assignment through a field/index (`c.items = ...`) — conservatively
        // drop container facts whose path the LHS could alter.
        killMutatedContainers(o, node, st);
        // A field write (`self.bit_length = …`) invalidates value-aliases whose
        // path is rooted at the written path's head identifier.
        if (lhsRootIdent(o, lhs)) |root| st.dropValueAliasesByRoot(root);
    }
    if (stored_source) |name| {
        // A same-type, naturally aligned element store either misses this
        // scalar or writes back exactly the value just loaded from it.
        try st.setScalarMin(o.gpa, name, rhs_min.?);
        if (rhs_min.? > 0) try st.scalars.add(o.gpa, name);
    }
    return .{};
}

/// Preserve only the scalar read by `slice[i] = pointer.*`, not arbitrary
/// alias facts. Explicit natural alignment and one identical builtin integer
/// type exclude partially overlapping stores and coercions. Computed pointers,
/// address spaces, volatile storage, aliases and effectful indices prove nothing.
fn sameIntegerElementSource(o: *Oracle, lhs: Ast.Node.Index, rhs: Ast.Node.Index) ?[]const u8 {
    const tree = o.tree;
    if (tree.nodeTag(lhs) != .array_access or tree.nodeTag(rhs) != .deref) return null;
    const destination = tree.nodeData(lhs).node_and_node;
    const slice_name = identName(tree, destination[0]) orelse return null;
    const pointer_name = identName(tree, tree.nodeData(rhs).node) orelse return null;
    if (!pureIntegerExpression(o, lhs, 0)) return null;
    const declaration = enclosingFnDecl(o) orelse return null;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
    var parameters = proto.iterate(tree);
    var slice_integer: ?[]const u8 = null;
    var pointer_integer: ?[]const u8 = null;
    while (parameters.next()) |parameter| {
        const name = tree.tokenSlice(parameter.name_token orelse continue);
        const is_slice = std.mem.eql(u8, name, slice_name);
        const is_pointer = std.mem.eql(u8, name, pointer_name);
        if (!is_slice and !is_pointer) continue;
        const pointer = tree.fullPtrType(parameter.type_expr orelse return null) orelse return null;
        if (pointer.ast.align_node != .none or pointer.ast.addrspace_node != .none or
            pointer.ast.bit_range_start != .none or pointer.volatile_token != null) return null;
        if (is_slice and pointer.size != .slice) return null;
        if (is_pointer and pointer.size != .one) return null;
        const child = pointer.ast.child_type;
        if (tree.nodeTag(child) != .identifier) return null;
        const integer = tree.tokenSlice(tree.nodeMainToken(child));
        if (!std.mem.eql(u8, integer, "u8") and !std.mem.eql(u8, integer, "u16") and
            !std.mem.eql(u8, integer, "u32") and !std.mem.eql(u8, integer, "u64")) return null;
        if (is_slice) slice_integer = integer;
        if (is_pointer) pointer_integer = integer;
    }
    if (!std.mem.eql(u8, slice_integer orelse return null, pointer_integer orelse return null)) return null;
    for (o.locals) |binding| {
        if (binding.origin == .param) continue;
        if (std.mem.eql(u8, binding.name, slice_name) or std.mem.eql(u8, binding.name, pointer_name)) return null;
    }
    return nodeSrc(tree, rhs);
}

/// The part of a written path that sits BELOW its root: `.count` in
/// `holder.count`, and empty for a write to the root itself.
fn writeProjection(path: []const u8) []const u8 {
    return path[numeric_escape.rootText(path).len..];
}

/// True when `projection` names plain fields all the way down, so the write
/// carrying it lands on ONE field of the object its root points at.  A deref
/// or a subscript — `p.*`, `p[i]` — names storage that no field path can
/// spell, so a write through it reaches whatever that storage turned out to
/// be and nothing narrows it.
fn isFieldProjection(projection: []const u8) bool {
    if (projection.len < 2 or projection[0] != '.') return false;
    var start: usize = 1;
    var cursor: usize = 1;
    while (cursor < projection.len) : (cursor += 1) {
        const c = projection[cursor];
        if (c == '.') {
            if (cursor == start) return false;
            start = cursor + 1;
            continue;
        }
        const letter = (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or c == '_';
        const digit = c >= '0' and c <= '9';
        if (!letter and !(digit and cursor != start)) return false;
    }
    return cursor > start;
}

/// True when this body recorded a binding for the pointer root `name` that
/// was already in force at `at`.  Its ABSENCE is what a pointer PARAMETER
/// looks like: the pointer was aimed before this frame existed, so no binding
/// in here follows it anywhere, and the storage behind it is a set rather
/// than a name.
fn escapeBindingBefore(o: *const Oracle, name: []const u8, at: Ast.TokenIndex) bool {
    for (o.escape_aliases.items) |entry| {
        if (std.mem.eql(u8, entry.local, name) and entry.token < at) return true;
    }
    return false;
}

/// Invalidate what a write THROUGH a pointer reaches besides the path it is
/// spelled with.
///
/// A store names one location.  `holder.count = v` writes `count` and leaves
/// every sibling field of the same object exactly as it was, so a proven fact
/// about `holder.text.len` survives it — and retiring the whole root would
/// claim a store to one field says something about the others, which is the
/// reading every unrelated-field guard is lost to.
///
/// The storage a pointer names is its ROOT; the field the store lands on is
/// the projection.  So each storage the root can stand for is asked about
/// `root.projection`, exactly as `writeReachesPath` decides the same question
/// for a store on a name this body can spell.  Every path that cannot be
/// projected — a deref, a subscript, a root that is not a pointer at all —
/// is handed to `numeric_escape.dropAliasedStorage` unchanged, so the answer
/// for those is still the escape model's own.
fn dropAliasedWrite(o: *Oracle, st: *State, name: []const u8, at: Ast.TokenIndex) error{OutOfMemory}!void {
    const root = numeric_escape.rootText(name);
    const projection = writeProjection(name);
    if (!o.pointer_roots.contains(root) or !isFieldProjection(projection) or
        numeric_escape.hasFreshStorage(o, root, at))
    {
        try numeric_escape.dropAliasedStorage(o, st, name, at);
        return;
    }
    // The one storage this body can name the chain ends at, or null when it
    // does not end at one: no binding was ever recorded (a parameter), a hop
    // stopped AT a pointer root that is still aimed at something only the
    // caller's frame knows, or a hop could not be followed at all.
    var one: ?[]const u8 = null;
    if (escapeBindingBefore(o, root, at)) {
        const storage = try numeric_escape.resolveEscapePath(o, root, at);
        if (storage.len == 0) {
            // A chain this walk could not follow: the write may land on
            // storage no name here can spell, and that is the escape model's
            // answer rather than a narrower one.
            try numeric_escape.dropAliasedStorage(o, st, name, at);
            return;
        }
        if (!o.pointer_roots.contains(numeric_escape.rootText(storage))) one = storage;
    }
    if (one) |storage| {
        dropFactsForRebind(o, st, try internPath(o, storage, projection));
        return;
    }
    // The set: two parameters may be handed the same object, and a pointer
    // aimed before this frame existed can name any local whose address this
    // body handed out.  It is every pointer root and every addressed name —
    // and the projection is part of every member, because the store lands on
    // one field of whichever object the pointer is aimed at and on no other.
    for (o.pointer_roots.keys.items) |other| {
        dropFactsForRebind(o, st, try internPath(o, other, projection));
    }
    for (o.addressed.keys.items) |other| {
        dropFactsForRebind(o, st, try internPath(o, other, projection));
    }
}

/// The count argument of a `std.mem.Allocator.alloc(T, n)` call, when this
/// walk can prove the callee IS that allocator and the count is a pure
/// integer expression; null for every other initializer.
///
/// `alloc` returns a slice of exactly `n` elements.  That is the toolchain's
/// own contract, and it is what both readings of the call rest on — the
/// lower bound (`allocatedMinimum`) and the length range
/// (`allocatedLengthRange`) — so the proof is settled once here and both read
/// the same count.
///
/// Every refusal is the one the lower bound has always made.  The callee is
/// resolved through the type engine against the toolchain's own
/// `/std/mem/Allocator.zig`, so a method that merely SPELLS `alloc` on some
/// other receiver proves nothing; no resolver, no cache and no pure-field
/// receiver each answer null rather than guess; and a count the pre-walk
/// cannot read as an integer expression is not a count at all.  Only the
/// node index crosses back out: `fullCall`'s parameter slice may point into
/// the caller's own buffer, and an index into the AST outlives both.
fn stdAllocCountNode(o: *Oracle, initializer: Ast.Node.Index) ?Ast.Node.Index {
    const tree = o.tree;
    const node = if (tree.nodeTag(initializer) == .@"try") tree.nodeData(initializer).node else initializer;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return null;
    if (tree.nodeTag(call.ast.fn_expr) != .field_access) return null;
    const callee = tree.nodeData(call.ast.fn_expr).node_and_token;
    if (!isPureFieldPath(tree, callee[0])) return null;
    const method = tree.tokenSlice(callee[1]);
    if (!std.mem.eql(u8, method, "alloc") or call.ast.params.len != 2) return null;
    const cache = o.cache orelse return null;
    const resolver = cache.zls orelse return null;
    if ((resolver.isStdAllocator(callee[0]) catch null) != true) return null;
    if (!pureIntegerExpression(o, call.ast.params[1], 0)) return null;
    return call.ast.params[1];
}

/// The proven lower bound on the count a standard allocator was handed, read
/// through the SAME channel the length range reads its upper end through, so
/// a count this walk cannot bound at the bottom is not silently held to be
/// zero.
fn allocatedMinimum(o: *Oracle, st: *const State, count: ?Ast.Node.Index) ?u64 {
    return exprMin(o, st, count orelse return null);
}

/// The range of the count a standard allocator was handed, as it stood AT
/// THIS BINDING — or null when the oracle cannot name a range for it.
///
/// Both ends come from the numeric evaluator the rest of this walk already
/// reads: the count's own declared type when nothing narrower was proved, and
/// a recorded fact or a `@as`/`@intCast` coercion when one was.  A `u32`
/// capture read as `@as(usize, v)` therefore answers every value up to
/// 2^32-1 — narrower than the `usize` the slice declares, and the whole of
/// what the source proves.
///
/// A count the evaluator cannot range is UNKNOWN, and an unknown count makes
/// the length unknown: falling back to the declared `usize` here would answer
/// every allocation as though it had been asked for the largest one this
/// platform can name, which is the very reading this fact exists to replace,
/// and it would answer it for a count that was never bound at all.
fn allocatedLengthRange(o: *Oracle, st: *const State, count: ?Ast.Node.Index) ?NumericRange {
    const value = numericValue(o, st, count orelse return null);
    return if (value == .integer) value else null;
}

pub fn isPureBuiltin(name: []const u8) bool {
    const pure = std.StaticStringMap(void).initComptime(.{
        .{ "@as", {} },
        .{ "@intCast", {} },
        .{ "@floatCast", {} },
        .{ "@floatFromInt", {} },
        .{ "@intFromFloat", {} },
        .{ "@bitCast", {} },
        .{ "@truncate", {} },
        .{ "@abs", {} },
        .{ "@min", {} },
        .{ "@max", {} },
        .{ "@divTrunc", {} },
        .{ "@divFloor", {} },
        .{ "@divExact", {} },
        .{ "@mod", {} },
        .{ "@rem", {} },
        .{ "@clz", {} },
        .{ "@ctz", {} },
        .{ "@popCount", {} },
        .{ "@sqrt", {} },
        .{ "@floor", {} },
        .{ "@ceil", {} },
        .{ "@trunc", {} },
        .{ "@round", {} },
        .{ "@sin", {} },
        .{ "@cos", {} },
        .{ "@tan", {} },
        .{ "@exp", {} },
        .{ "@exp2", {} },
        .{ "@log", {} },
        .{ "@log2", {} },
        .{ "@log10", {} },
        .{ "@mulAdd", {} },
        .{ "@addWithOverflow", {} },
        .{ "@subWithOverflow", {} },
        .{ "@mulWithOverflow", {} },
        .{ "@shlWithOverflow", {} },
        .{ "@TypeOf", {} },
        .{ "@This", {} },
        .{ "@sizeOf", {} },
        .{ "@alignOf", {} },
        .{ "@bitSizeOf", {} },
        .{ "@typeInfo", {} },
        .{ "@FieldType", {} },
        .{ "@offsetOf", {} },
        .{ "@bitOffsetOf", {} },
        .{ "@hasDecl", {} },
        .{ "@hasField", {} },
        .{ "@Vector", {} },
        .{ "@field", {} },
        .{ "@intFromEnum", {} },
        .{ "@enumFromInt", {} },
        .{ "@intFromBool", {} },
        .{ "@intFromPtr", {} },
        .{ "@ptrFromInt", {} },
        .{ "@ptrCast", {} },
        .{ "@alignCast", {} },
        .{ "@addrSpaceCast", {} },
        .{ "@constCast", {} },
        .{ "@volatileCast", {} },
        .{ "@branchHint", {} },
        .{ "@setFloatMode", {} },
        .{ "@setRuntimeSafety", {} },
        .{ "@import", {} },
    });
    return pure.has(name);
}

fn mayMutateIndirect(o: *Oracle, node: Ast.Node.Index) bool {
    const tree = o.tree;
    switch (tree.nodeTag(node)) {
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => return !isPureBuiltin(tree.tokenSlice(tree.nodeMainToken(node))),
        else => {},
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return false;
    return !isStdAssertion(o, call, tree.firstToken(node)) and
        !isStdMathMul(o, call.ast.fn_expr, node) and
        !isPureStdCall(o, call.ast.fn_expr, tree.firstToken(node));
}
pub fn pureIntegerExpression(o: *Oracle, node: Ast.Node.Index, depth: u8) bool {
    // The pre-walk declines to descend on the SAME bound the rest of the
    // module uses, and it says so: a query that asks whether an operand is a
    // pure integer expression has to be able to tell "this is not one" from
    // "I stopped looking", and only the second one is a bound.
    if (depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return false;
    }
    if (!o.spend()) return false;
    const tree = o.tree;
    switch (tree.nodeTag(node)) {
        .@"switch", .switch_comma => {
            const selector = tree.fullSwitch(node) orelse return false;
            const condition_pure = pureIntegerExpression(o, selector.ast.condition, depth + 1);
            if (!condition_pure) return false;
            // Case labels are compile-time selectors, not runtime operands.
            // Every arm that yields a value must be pure before its numeric
            // range can be read from the state preceding the return.
            for (selector.ast.cases) |case_node| {
                const case = tree.fullSwitchCase(case_node) orelse return false;
                if (case.payload_token != null) return false;
                const target = unwrapGrouped(tree, case.ast.target_expr);
                if (tree.nodeTag(target) == .unreachable_literal) continue;
                if (!pureIntegerExpression(o, target, depth + 1)) return false;
            }
            return true;
        },
        .@"if", .if_simple => {
            const conditional = tree.fullIf(node) orelse return false;
            if (conditional.payload_token != null) return false;
            const fallback = conditional.ast.else_expr.unwrap() orelse return false;
            if (!pureIntegerExpression(o, conditional.ast.cond_expr, depth + 1)) return false;
            for ([_]Ast.Node.Index{ conditional.ast.then_expr, fallback }) |arm| {
                const target = unwrapGrouped(tree, arm);
                if (tree.nodeTag(target) == .unreachable_literal) continue;
                if (!pureIntegerExpression(o, target, depth + 1)) return false;
            }
            return true;
        },
        .call, .call_comma, .call_one, .call_one_comma => {
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node).?;
            if (!isPureStdCall(o, call.ast.fn_expr, tree.firstToken(node))) return false;
        },
        .identifier, .number_literal, .char_literal, .enum_literal, .field_access, .grouped_expression, .array_access, .deref, .negation, .bit_not, .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor, .bool_not, .bool_and, .bool_or, .equal_equal, .bang_equal, .less_than, .less_or_equal, .greater_than, .greater_or_equal => {},
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            if (!isPureBuiltin(name)) return false;
        },
        else => return false,
    }
    var children = @import("type_engine").AstIterator.init(tree, node);
    while (children.next(tree)) |child| {
        if (!pureIntegerExpression(o, child, depth + 1)) return false;
    }
    return true;
}

/// Retain the mathematical relation only on checked addition's success edge.
/// A continuing overflow fallback produces a different value and no relation.
fn recordCheckedAddAliases(o: *Oracle, st: *State, original: Ast.Node.Index, local: []const u8) error{OutOfMemory}!void {
    const tree = o.tree;
    var node = unwrapGrouped(tree, original);
    switch (tree.nodeTag(node)) {
        .@"try" => node = unwrapGrouped(tree, tree.nodeData(node).node),
        .@"catch" => {
            const parts = tree.nodeData(node).node_and_node;
            var fallback = unwrapGrouped(tree, parts[1]);
            if (isBlockTag(tree.nodeTag(fallback))) {
                var statements: [2]Ast.Node.Index = undefined;
                const listed = blockStmts(tree, fallback, &statements);
                if (listed.len != 1) return;
                fallback = unwrapGrouped(tree, listed[0]);
            }
            switch (tree.nodeTag(fallback)) {
                .@"return", .unreachable_literal => {},
                else => return,
            }
            node = unwrapGrouped(tree, parts[0]);
        },
        else => return,
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return;
    if (call.ast.params.len != 3 or
        !std.mem.eql(u8, nodeSrc(tree, call.ast.fn_expr), "std.math.add") or
        !stdBindingValidAt(o, tree.firstToken(node))) return;
    const domain = spelledIntegerDomain(o, call.ast.params[0]);
    if (domain != .integer or domain.integer.min < 0) return;
    const operands = call.ast.params[1..3];
    for (operands) |operand|
        if (!pureIntegerExpression(o, operand, 0)) return;
    const left = numericValue(o, st, operands[0]);
    const right = numericValue(o, st, operands[1]);
    if (left != .integer or left.integer.min < 0 or right != .integer or right.integer.min < 0) return;
    const values = [_]NumericRange{ left, right };
    // Exact offsets retain both ends, as before. A variable sum does not.
    for (0..2) |side| {
        const path = numeric_eval.path(tree, operands[side]) orelse continue;
        const offset = values[1 - side].integer;
        if (offset.min != offset.max or offset.max > std.math.maxInt(u64)) continue;
        try st.addValueAlias(o.gpa, .{ .local = local, .path = path, .offset = @intCast(offset.min) });
        return;
    }
    const left_path = numeric_eval.path(tree, operands[0]) orelse return;
    const right_path = numeric_eval.path(tree, operands[1]) orelse return;
    try st.addValueAlias(o.gpa, .{ .local = local, .path = left_path, .other_path = right_path });
    try st.addValueAlias(o.gpa, .{ .local = local, .path = right_path, .other_path = left_path });
}

fn recordProductAliases(
    o: *Oracle,
    st: *State,
    result: []const u8,
    init_node: Ast.Node.Index,
) error{OutOfMemory}!void {
    if (productFactors(o, st, init_node)) |factors| {
        try st.addProductAlias(o.gpa, .{
            .result = result,
            .left = factors.left,
            .right = factors.right,
        });
        return;
    }
    if (o.tree.nodeTag(init_node) != .@"if" and o.tree.nodeTag(init_node) != .if_simple) return;
    const if_data = o.tree.fullIf(init_node) orelse return;
    if (productFactors(o, st, if_data.ast.then_expr)) |factors| {
        try st.addProductAlias(o.gpa, .{
            .result = result,
            .left = factors.left,
            .right = factors.right,
            .condition = if_data.ast.cond_expr,
            .condition_true = true,
        });
    }
    if (if_data.ast.else_expr.unwrap()) |else_expr| {
        if (productFactors(o, st, else_expr)) |factors| {
            try st.addProductAlias(o.gpa, .{
                .result = result,
                .left = factors.left,
                .right = factors.right,
                .condition = if_data.ast.cond_expr,
                .condition_true = false,
            });
        }
    }
}

const ProductFactors = struct {
    left: ProductFactor,
    right: ProductFactor,
};

fn productFactors(o: *Oracle, st: *const State, node: Ast.Node.Index) ?ProductFactors {
    const tree = o.tree;
    const expr = unwrapProductExpr(tree, node);
    if (tree.nodeTag(expr) == .mul) {
        const data = tree.nodeData(expr).node_and_node;
        return .{
            .left = productFactor(o, st, data[0]) orelse return null,
            .right = productFactor(o, st, data[1]) orelse return null,
        };
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, expr) orelse return null;
    if (!isStdMathMul(o, call.ast.fn_expr, expr)) return null;
    if (call.ast.params.len != 3) return null;
    const type_name = identName(tree, call.ast.params[0]) orelse return null;
    if (!std.mem.eql(u8, type_name, "usize")) return null;
    return .{
        .left = productFactor(o, st, call.ast.params[1]) orelse return null,
        .right = productFactor(o, st, call.ast.params[2]) orelse return null,
    };
}

fn productFactor(o: *Oracle, st: *const State, node: Ast.Node.Index) ?ProductFactor {
    const tree = o.tree;
    const expr = unwrapProductExpr(tree, node);
    if (lenContainerPath(o, expr)) |path| {
        return .{ .key = path, .is_container = true };
    }
    const name = identName(tree, expr) orelse return null;
    for (st.aliases.items) |alias| {
        if (std.mem.eql(u8, alias.scalar, name)) {
            return .{ .key = alias.container, .is_container = true };
        }
    }
    return .{ .key = name, .is_container = false };
}

fn unwrapProductExpr(tree: *const Ast, node: Ast.Node.Index) Ast.Node.Index {
    var expr = node;
    while (true) switch (tree.nodeTag(expr)) {
        .grouped_expression => expr = tree.nodeData(expr).node_and_token[0],
        .@"try" => expr = tree.nodeData(expr).node,
        .@"catch" => expr = tree.nodeData(expr).node_and_node[0],
        else => break,
    };
    return expr;
}

fn isStdMathMul(o: *Oracle, callee: Ast.Node.Index, call_node: Ast.Node.Index) bool {
    const tree = o.tree;
    if (tree.nodeTag(callee) != .field_access) return false;
    if (!std.mem.eql(u8, nodeSrc(tree, callee), "std.math.mul")) return false;
    return stdBindingValidAt(o, tree.firstToken(call_node));
}

fn stdBindingValidAt(o: *Oracle, anchor: Ast.TokenIndex) bool {
    if (!fileImportsStd(o)) return false;
    if (bodyHasStdParameter(o)) return false;
    const tree = o.tree;
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(o.body);
    var t = first;
    while (t < anchor and t + 1 < tags.len) : (t += 1) {
        if ((tags[t] == .keyword_const or tags[t] == .keyword_var) and
            tags[t + 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 1), "std"))
        {
            return false;
        }
        if (tags[t] == .identifier and std.mem.eql(u8, tree.tokenSlice(t), "std") and
            isAssignOp(tags[t + 1]))
        {
            return false;
        }
        if (tags[t] == .pipe and tags[t + 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t + 1), "std"))
        {
            return false;
        }
    }
    return true;
}

/// Whether this file binds the name `std` at root scope to `@import("std")`.
///
/// A property of the SNAPSHOT, settled once per query and read back after: it
/// is asked of every call the walk meets that could name the standard library,
/// and re-reading the file's root declarations for each of them is what made a
/// body with many std calls pay for the file once per call.
fn fileImportsStd(o: *Oracle) bool {
    if (o.std_imported) |answer| return answer;
    const tree = o.tree;
    var imported = false;
    for (tree.rootDecls()) |root| {
        const decl = tree.fullVarDecl(root) orelse continue;
        if (tree.tokens.items(.tag)[decl.ast.mut_token] != .keyword_const) continue;
        const name_token = decl.ast.mut_token + 1;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), "std")) continue;
        const init = decl.ast.init_node.unwrap() orelse break;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(init)), "@import")) break;
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, init) orelse break;
        if (params.len != 1 or tree.nodeTag(params[0]) != .string_literal) break;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(params[0])), "\"std\"")) break;
        imported = true;
        break;
    }
    o.std_imported = imported;
    return imported;
}

/// Whether this body's own declaration takes a parameter named `std`, in
/// which case the name inside it is that parameter and not the file's import.
///
/// Settled once per query, because the walk that answers it covers this file's
/// whole node array.  A body no `fn_decl` claims is a synthetic one and
/// answers true: there is no parameter list to read, and the reading that
/// cannot mistake a parameter for the import is the one that declines.
fn bodyHasStdParameter(o: *Oracle) bool {
    if (o.std_parameter) |answer| return answer;
    const tree = o.tree;
    var shadowed = true;
    if (enclosingFnDecl(o)) |declaration| {
        const data = tree.nodeData(declaration).node_and_node;
        shadowed = blk: {
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tree.fullFnProto(&buffer, data[0]) orelse break :blk true;
            var params = proto.iterate(tree);
            while (params.next()) |param| {
                const name_token = param.name_token orelse continue;
                if (std.mem.eql(u8, tree.tokenSlice(name_token), "std")) break :blk true;
            }
            break :blk false;
        };
    }
    o.std_parameter = shadowed;
    return shadowed;
}

/// Root identifier of an assignment LHS path (`self` from `self.bit_length`,
/// `arr` from `arr[i].x`), or null.
pub fn lhsRootIdent(o: *Oracle, lhs: Ast.Node.Index) ?[]const u8 {
    const root = @import("../ast/tokens.zig").rootIdentifier(o.tree, lhs) orelse return null;
    return o.tree.tokenSlice(o.tree.nodeMainToken(root));
}

/// `x += <expr>` transfers a proven lower bound.  When both the old value and
/// the addend have known non-negative lower bounds, the sum is retained (with
/// checked `u64` arithmetic).  An unknown addend drops the bound instead of
/// guessing that the local is unsigned; this keeps signed `-1 += 1` unknown.
fn analyzeCompoundAdd(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    const tree = o.tree;
    const data = tree.nodeData(node).node_and_node;
    const lhs = data[0];
    const rhs = data[1];
    // Use may be in the LHS subscript (`buf[idx - 1] += …`) — answer first.
    if (o.tokenInNode(lhs)) {
        const flow = try analyzeNode(o, lhs, st);
        if (flow.answer != null) return flow;
    }
    const rhs_flow = try analyzeNode(o, rhs, st);
    if (o.tokenInNode(rhs) and rhs_flow.answer != null) return rhs_flow;
    if (scalarPath(o, lhs)) |name| {
        const old_min = exprMin(o, st, lhs);
        const rhs_min = exprMin(o, st, rhs);
        const new_min: ?u64 = if (old_min) |left_min| blk: {
            const right_min = rhs_min orelse break :blk null;
            if (left_min > std.math.maxInt(u64) - right_min) break :blk null;
            break :blk left_min + right_min;
        } else null;
        // The induction verifier reads the numeric channel, not only the
        // scalar floor. Checked integer addition keeps its mathematical
        // interval on the successful edge, clipped to the destination domain.
        var numeric: NumericRange = .unknown;
        if ((o.query == .numeric_range or o.query == .min_len_container) and
            tree.nodeTag(lhs) == .identifier and pureIntegerExpression(o, rhs, 0))
        {
            const domain = assignedRange(o, st, name, .unknown, tree.firstToken(node), lhs);
            if (domain == .integer) {
                numeric = numericValue(o, st, lhs).binary(numericValue(o, st, rhs), .add).intersect(domain);
                if (new_min) |minimum| {
                    numeric = numeric.intersect(.{ .integer = .{
                        .min = @intCast(minimum),
                        .max = domain.integer.max,
                    } });
                }
            }
        }
        if (tree.nodeTag(lhs) != .identifier) dropIndirectFacts(o, st, .{ .subtree = node });
        // The value changed: a `n = c.len` snapshot no longer holds, and any
        // container path rooted at `name` is stale.
        dropFactsForRebind(o, st, name);
        if (tree.nodeTag(lhs) != .identifier) {
            try numeric_escape.dropAliasedStorage(o, st, name, tree.firstToken(node));
        }
        if (numeric != .unknown) try st.setNumeric(o.gpa, name, numeric);
        if (new_min) |min| {
            try st.setScalarMin(o.gpa, name, min);
            if (min >= 1) try st.scalars.add(o.gpa, name);
        }
    } else {
        killMutatedContainers(o, node, st);
    }
    return .{};
}
/// Any non-`+=` compound assignment can reduce a scalar to zero or destroy a
/// product/equality snapshot.  Drop all facts before continuing after it.
fn analyzeCompoundMutation(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    const tree = o.tree;
    const data = tree.nodeData(node).node_and_node;
    const lhs = data[0];
    const rhs = data[1];
    if (o.tokenInNode(lhs)) {
        const flow = try analyzeNode(o, lhs, st);
        if (flow.answer != null) return flow;
    }
    const rhs_flow = try analyzeNode(o, rhs, st);
    if (o.tokenInNode(rhs) and rhs_flow.answer != null) return rhs_flow;
    if (scalarPath(o, lhs)) |name| {
        const old_min = st.scalarMinOf(name);
        const new_min: ?u64 = if (tree.nodeTag(node) == .assign_sub) blk: {
            const amount = intLiteralVal(tree, rhs) orelse break :blk null;
            const current = old_min orelse break :blk null;
            if (current < amount) break :blk null;
            break :blk current - amount;
        } else null;
        if (tree.nodeTag(lhs) != .identifier) dropIndirectFacts(o, st, .{ .subtree = node });

        dropFactsForRebind(o, st, name);
        if (tree.nodeTag(lhs) != .identifier) {
            try numeric_escape.dropAliasedStorage(o, st, name, tree.firstToken(node));
        }
        if (new_min) |min| {
            try st.setScalarMin(o.gpa, name, min);
            if (min >= 1) try st.scalars.add(o.gpa, name);
        }
    } else {
        killMutatedContainers(o, node, st);
    }
    return .{};
}

/// A payload introduces a new binding even when its spelling matches a selector.
fn dropConditionalCapture(tree: *const Ast, st: *State, payload: ?Ast.TokenIndex) void {
    var token = payload orelse return;
    const tags = tree.tokens.items(.tag);
    while (token < tags.len) {
        if (tags[token] == .asterisk) token += 1;
        if (token >= tags.len or tags[token] != .identifier) return;
        st.dropConditionalLengthsRootedAt(tree.tokenSlice(token));
        token += 1;
        if (token >= tags.len or tags[token] != .comma) return;
        token += 1;
    }
}

fn analyzeIf(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    const tree = o.tree;
    const if_data = tree.fullIf(node) orelse return .{};
    const cond = if_data.ast.cond_expr;
    const condition_flow = try analyzeNode(o, cond, st);
    if (o.tokenInNode(cond) and condition_flow.answer != null) return condition_flow;
    if (condition_flow.diverged) return condition_flow;

    const then_node = if_data.ast.then_expr;
    const else_opt = if_data.ast.else_expr.unwrap();

    var then_st = try st.clone(o.gpa);
    defer then_st.deinit(o.gpa);
    try applyRefine(o, &then_st, .{ .node = cond, .truth = true });
    dropConditionalCapture(tree, &then_st, if_data.payload_token);
    if (o.tokenInNode(then_node)) return try analyzeNode(o, then_node, &then_st);
    const then_flow = try analyzeNode(o, then_node, &then_st);

    var else_st = try st.clone(o.gpa);
    defer else_st.deinit(o.gpa);
    try applyRefine(o, &else_st, .{ .node = cond, .truth = false });
    dropConditionalCapture(tree, &else_st, if_data.error_token);
    var else_flow: Flow = .{};
    if (else_opt) |else_node| {
        if (o.tokenInNode(else_node)) return try analyzeNode(o, else_node, &else_st);
        else_flow = try analyzeNode(o, else_node, &else_st);
    }

    if (then_flow.diverged and else_flow.diverged) {
        return .{ .diverged = true };
    } else if (then_flow.diverged) {
        try st.replaceWith(o.gpa, &else_st);
    } else if (else_flow.diverged) {
        try st.replaceWith(o.gpa, &then_st);
    } else {
        then_st.intersectWith(&else_st);
        try st.replaceWith(o.gpa, &then_st);
    }
    return .{};
}

/// `A and B` / `A or B` as a (sub)expression.  When the use token is inside the
/// RHS, evaluate it under the short-circuit refinement of the LHS: for `and`,
/// the LHS's THEN-facts hold (A is true); for `or`, the LHS's ELSE-facts hold
/// (A is false).  Sound because Zig `and`/`or` only evaluate B when A is
/// true/false respectively.
fn analyzeShortCircuit(o: *Oracle, node: Ast.Node.Index, st: *State, is_and: bool) QueryError!Flow {
    const parts = o.tree.nodeData(node).node_and_node;
    const lhs_flow = try analyzeNode(o, parts[0], st);
    if (o.tokenInNode(parts[0]) and lhs_flow.answer != null) return lhs_flow;
    if (lhs_flow.diverged) return lhs_flow;

    var rhs_state = try st.clone(o.gpa);
    defer rhs_state.deinit(o.gpa);
    try applyRefine(o, &rhs_state, .{ .node = parts[0], .truth = is_and });
    const rhs_flow = try analyzeNode(o, parts[1], &rhs_state);
    if (o.tokenInNode(parts[1]) and rhs_flow.answer != null) return rhs_flow;
    if (!rhs_flow.diverged) st.intersectWith(&rhs_state);
    return if (o.tokenInNode(node)) .{ .answer = o.answerAt(st) } else .{};
}

/// A copied payload reads only its selected variant's projection. The return
/// join has already dropped projections missing from any alternate return.
/// Pointer captures and multi-label arms do not describe one copied header.
fn refineSwitchPayload(o: *Oracle, source: *const State, output: *State, condition: Ast.Node.Index, case_node: Ast.Node.Index) QueryError!void {
    const arm_capture = o.tree.fullSwitchCase(case_node) orelse return;
    dropConditionalCapture(o.tree, output, arm_capture.payload_token);
    if (o.query != .numeric_range) return;
    const tree = o.tree;
    const arm = tree.fullSwitchCase(case_node) orelse return;
    const capture_token = arm.payload_token orelse return;
    if (tree.tokenTag(capture_token) != .identifier) return;
    const capture = tree.tokenSlice(capture_token);
    dropFactsForRebind(o, output, capture);
    if (arm.ast.values.len != 1) return;
    const label = unwrapGrouped(tree, arm.ast.values[0]);
    if (tree.nodeTag(label) != .enum_literal) return;
    const owner_node = unwrapGrouped(tree, condition);
    const owner = numeric_eval.path(tree, owner_node) orelse return;
    const resolver = (o.cache orelse return).zls orelse return;
    const actual = (resolver.resolutionFrame().typeOfNode(owner_node) catch |err| {
        if (strictQueryError(err)) |failure| return failure;
        return;
    }) orelse return;
    if (resolver.typeTag(actual) != .@"union") return;
    const projection = try aggregateFieldPath(o, owner, tree.tokenSlice(tree.nodeMainToken(label)));
    for (source.len_bounds.items) |field| {
        if (!o.spend()) return;
        if (!pathRootedAt(field.name, projection)) continue;
        const name = if (field.name.len == projection.len)
            capture
        else
            try aggregateFieldPath(o, capture, field.name[projection.len + 1 ..]);
        try output.setLenBound(o.gpa, name, field.value);
    }
}

/// `switch (scrutinee) { K => arm, … }`.  When the use is in an arm whose single
/// label is an integer literal `K` and the scrutinee is a simple scalar, record
/// `scrutinee == K` (and nonzero if K != 0) for that arm — so a slice whose
/// length aliases the scrutinee is known to have length K inside the arm.
fn analyzeSwitch(o: *Oracle, node: Ast.Node.Index, st: *State) QueryError!Flow {
    const tree = o.tree;
    const sw = tree.fullSwitch(node) orelse return .{};
    const condition_flow = try analyzeNode(o, sw.ast.condition, st);
    if (o.tokenInNode(sw.ast.condition) and condition_flow.answer != null) return condition_flow;
    if (condition_flow.diverged) return condition_flow;
    const scrut = identName(tree, sw.ast.condition);
    for (sw.ast.cases) |case_node| {
        const sc = tree.fullSwitchCase(case_node) orelse continue;
        const body = sc.ast.target_expr;
        if (!o.tokenInNode(body)) continue;
        var arm_st = try st.clone(o.gpa);
        defer arm_st.deinit(o.gpa);
        try refineSwitchPayload(o, st, &arm_st, sw.ast.condition, case_node);
        if (scrut) |sn| {
            if (sc.ast.values.len == 1) {
                if (intLiteralVal(tree, sc.ast.values[0])) |k| {
                    try arm_st.setScalarVal(o.gpa, sn, k);
                    if (k != 0) try arm_st.scalars.add(o.gpa, sn);
                }
            }
        }
        return try analyzeNode(o, body, &arm_st);
    }
    // The use is in no arm, so every arm can still run before it.  Walking the
    // arms is what keeps their effects precise: a `switch` that only computes
    // a `has_comma`-style flag mutates nothing, and discarding every fact here
    // threw away proofs for containers the switch never mentions — the shape
    // `if (C.len == 0) { … } else { … C[C.len - 1] … }` where a `switch` sits
    // between the guard and the use.  Joining the arms (intersection, like
    // `analyzeIf`) still drops whatever ANY arm invalidates.
    dropLoopMutated(o, node, st);
    var base = try st.clone(o.gpa);
    defer base.deinit(o.gpa);
    var joined = false;
    for (sw.ast.cases) |case_node| {
        const sc = tree.fullSwitchCase(case_node) orelse continue;
        var arm_st = try base.clone(o.gpa);
        defer arm_st.deinit(o.gpa);
        try refineSwitchPayload(o, &base, &arm_st, sw.ast.condition, case_node);
        _ = try analyzeNode(o, sc.ast.target_expr, &arm_st);
        if (!joined) {
            joined = true;
            try st.replaceWith(o.gpa, &arm_st);
        } else st.intersectWith(&arm_st);
    }
    return .{};
}

fn analyzeLoop(o: *Oracle, node: Ast.Node.Index, st: *State, kind: numeric_loops.LoopKind) QueryError!Flow {
    const tree = o.tree;
    if (tree.fullFor(node)) |loop| {
        for (loop.ast.inputs) |input| {
            const flow = try analyzeNode(o, input, st);
            if (o.tokenInNode(input) and flow.answer != null) return flow;
        }
    }
    var invariants = try numeric_loops.numericLoopInvariants(o, node, st);
    defer invariants.deinit(o.gpa);
    if (kind == .for_ and !o.tokenInNode(node) and o.query == .numeric_range) {
        var evaluation = evaluator(o, st);
        try numeric_loops.numericForExitFacts(o, node, st, &evaluation, &invariants);
    }
    dropLoopMutated(o, node, st);
    for (invariants.items) |fact| try st.setNumeric(o.gpa, fact.name, fact.value);

    const body_node: ?Ast.Node.Index = switch (kind) {
        .while_ => if (tree.fullWhile(node)) |w| w.ast.then_expr else null,
        .for_ => if (tree.fullFor(node)) |f| f.ast.then_expr else null,
    };
    const cond_node: ?Ast.Node.Index = switch (kind) {
        .while_ => if (tree.fullWhile(node)) |w| w.ast.cond_expr else null,
        .for_ => null,
    };
    // Use inside the loop condition itself: descend so short-circuit refinement
    // applies (`while (tmp > beg and self.text[tmp-1] == …)` — the `and`'s LHS
    // guards its RHS).  analyzeNode handles bool_and/bool_or; a plain comparison
    // falls through to answerAt.
    if (cond_node) |c| if (o.tokenInNode(c)) return try analyzeNode(o, c, st);
    if (body_node) |b| {
        if (o.tokenInNode(b)) {
            var body_st = try st.clone(o.gpa);
            defer body_st.deinit(o.gpa);
            if (cond_node) |c| {
                const condition_flow = try analyzeNode(o, c, &body_st);
                if (condition_flow.diverged) return condition_flow;
                try applyRefine(o, &body_st, .{ .node = c, .truth = true });
                if (tree.fullWhile(node)) |while_data|
                    dropConditionalCapture(tree, &body_st, while_data.payload_token);
            } else if (tree.fullFor(node)) |for_data| {
                var capture = for_data.payload_token;
                const tags = tree.tokens.items(.tag);
                for (for_data.ast.inputs) |input| {
                    if (capture >= tags.len) break;
                    const pointer_capture = tags[capture] == .asterisk;
                    if (pointer_capture) capture += 1;
                    if (capture >= tags.len or tags[capture] != .identifier) break;
                    body_st.dropConditionalLengthsRootedAt(tree.tokenSlice(capture));
                    if (!pointer_capture) try refineForInput(o, &body_st, input, tree.tokenSlice(capture));
                    if (rangeUpperName(tree, input)) |upper| {
                        // The body only runs once `0 < upper`, which is a
                        // POSITIVE bound, not merely a nonzero one.  The
                        // range endpoints are evaluated into a `usize`
                        // result location and the loop counts in a `usize`,
                        // so `upper` is what that count reached, whatever
                        // the source declared it as.  Recording it as a
                        // minimum is also what keeps `!= 0` from being read
                        // as `> 0` for a name the walk knows nothing else
                        // about.
                        try body_st.setScalarMin(o.gpa, upper, 1);
                        try body_st.scalars.add(o.gpa, upper);
                    } else if (iterablePath(o, input)) |path| {
                        try applyRefineFacts(o, &body_st, .{}, .{ .name = path, .min = 1 }, null);
                    }
                    capture += 1;
                    if (capture < tags.len and tags[capture] == .comma) capture += 1;
                }
            }
            if (o.break_capture) |outer_capture| {
                o.break_capture = null;
                defer o.break_capture = outer_capture;
                return try analyzeNode(o, b, &body_st);
            }
            return try analyzeNode(o, b, &body_st);
        }
    }
    // For `while (true)`, the only terminating paths are breaks.  Analyze one
    // body execution with a dedicated capture and join all captured states.
    // A nested loop gets its own break scope (above), so its breaks cannot
    // escape into this loop.
    if (kind == .while_ and cond_node != null and o.break_capture == null and
        isTrueExpr(tree, cond_node.?))
    {
        var exits = BreakCapture{ .gpa = o.gpa };
        defer exits.deinit();
        o.break_capture = &exits;
        defer o.break_capture = null;
        if (body_node) |b| {
            var body_st = try st.clone(o.gpa);
            defer body_st.deinit(o.gpa);
            _ = try analyzeNode(o, b, &body_st);
        }
        if (exits.has_unresolved_target) return .{};
        if (exits.state) |*exit_st| {
            try st.replaceWith(o.gpa, exit_st);
            return .{};
        }
        return .{ .diverged = true };
    }
    return .{};
}

fn refineForInput(o: *Oracle, st: *State, input: Ast.Node.Index, capture: []const u8) error{OutOfMemory}!void {
    const tree = o.tree;
    const is_range = tree.nodeTag(input) == .for_range;
    const lower = if (is_range)
        exprMin(o, st, tree.nodeData(input).node_and_opt_node[0])
    else blk: {
        var buffer: [2]Ast.Node.Index = undefined;
        const array = tree.fullArrayInit(&buffer, input) orelse break :blk null;
        if (array.ast.elements.len == 0) break :blk null;
        var minimum: u64 = std.math.maxInt(u64);
        for (array.ast.elements) |element| {
            minimum = @min(minimum, exprMin(o, st, element) orelse break :blk null);
        }
        break :blk @as(?u64, minimum);
    };
    st.scalars.removeRooted(capture);
    st.dropScalarMinsRootedAt(capture);
    if (lower) |value| {
        try st.setScalarMin(o.gpa, capture, value);
        if (value > 0) try st.scalars.add(o.gpa, capture);
    }
    // A `for (start..end)` body only runs with `start <= capture < end`, and
    // `end` is evaluated once on entry, so the range end's own numeric bounds
    // are the capture's upper bound.  The loop variable is `usize` whatever
    // the endpoints are declared as, so this is where a narrow endpoint type
    // reaches a value the type engine reports as 64 bits wide.
    if (o.query != .numeric_range or !is_range) return;
    const end_node = tree.nodeData(input).node_and_opt_node[1].unwrap() orelse return;
    const end = blk: {
        var evaluation = evaluator(o, st);
        break :blk evaluation.evaluate(end_node);
    };
    if (end != .integer) return;
    const start = lower orelse return;
    const last = std.math.sub(i128, end.integer.max, 1) catch return;
    if (last < @as(i128, @intCast(start))) return;
    try st.setNumeric(o.gpa, capture, .{ .integer = .{ .min = @intCast(start), .max = last } });
}

pub fn applyRefine(o: *Oracle, st: *State, predicate: Predicate) QueryError!void {
    if (o.summary_error) |err| return err;
    // A helper's contract lands in the same state every query reads, so it is
    // applied for every query and not only for the range one: `provesPositive`
    // and `provesNonempty` ask whether a container is long enough, and the
    // callee that established that is the answer they were looking for.  What
    // it leaves is applied once and is never retained as a stable predicate
    // below — whether the helper holds is the callee's to make, not this
    // walk's.
    try refinePredicateOutcome(o, st, predicate, 0);
    var fold = Fold{ .o = o, .st = st };
    defer fold.deinit();
    _ = try addStablePredicates(&fold, st, predicate, 0);
    // Drained here rather than inside `addStablePredicates`, so every fact a
    // consequence records lands AFTER `laterOperandKeepsEarlierFacts` has
    // answered for every operand of this condition.  Folding mid-descent would
    // decide that question against facts the descent has not established yet,
    // and the answer is a choice about which operand's facts to keep.
    try fold.pump();
    if (o.summary_error) |err| return err;
}

/// Record every fact a proved predicate hands over as a standalone condition.
///
/// `A or B` is false only when BOTH operands are, and `A and B` is true only
/// when both are, so the earlier operand is not dead weight — but its facts
/// describe the state BEFORE the later operand ran, and a call in between can
/// rewrite exactly what they name.  The earlier operand is therefore recorded
/// only when `laterOperandKeepsEarlierFacts` says the later one cannot reach
/// them.  The later operand's own facts describe the state the walk ends in,
/// so that side always descends whatever the earlier one did.
fn addStablePredicates(
    fold: *Fold,
    st: *State,
    predicate: Predicate,
    depth: u8,
) error{OutOfMemory}!bool {
    const o = fold.o;
    if (depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return false;
    }
    if (!o.spend()) return false;
    var current = predicate;
    current.node = unwrapGrouped(o.tree, current.node);
    if (pureIntegerExpression(o, current.node, 0))
        return fold.imply(current.node, current.truth);
    var changed = false;
    switch (o.tree.nodeTag(current.node)) {
        .bool_not => {
            changed = try addStablePredicates(fold, st, .{
                .node = o.tree.nodeData(current.node).node,
                .truth = !current.truth,
            }, depth + 1);
        },
        .bool_and, .bool_or => |tag| {
            // A short-circuit that was proved the other way round settles
            // neither operand: `A or B` proved true proves nothing of `B`, and
            // `A and B` proved false proves nothing of `B` either.
            if ((tag == .bool_and) != current.truth) return false;
            const parts = o.tree.nodeData(current.node).node_and_node;
            if (laterOperandKeepsEarlierFacts(o, st, parts[0], parts[1], current.truth)) {
                const earlier = try addStablePredicates(fold, st, .{
                    .node = parts[0],
                    .truth = current.truth,
                }, depth + 1);
                changed = changed or earlier;
            }
            const later = try addStablePredicates(fold, st, .{
                .node = parts[1],
                .truth = current.truth,
            }, depth + 1);
            changed = changed or later;
        },
        else => {},
    }
    return changed;
}

/// Can the later operand of a short-circuit `and`/`or` change what the earlier
/// operand's truth would record?
///
/// Both operands always run, in source order, so the earlier one's facts
/// describe the state before the later one started.  An effect-free later
/// operand cannot move that state.  Past that, the question is whether the
/// NAMES those facts are about survive the later operand, which is the same
/// reachability model `analyzeCall` uses to drop facts at a call — asked of
/// the later operand as a whole, since a nested call is part of it.  A direct
/// assignment is not a callee that model can enumerate, so a write at all
/// ends it.
fn laterOperandKeepsEarlierFacts(
    o: *Oracle,
    st: *const State,
    earlier: Ast.Node.Index,
    later: Ast.Node.Index,
    truth: bool,
) bool {
    if (pureIntegerExpression(o, later, 0)) return true;
    if (writesDirectly(o, later, 0)) return false;
    return earlierFactsOutliveLaterOperand(o, st, earlier, later, truth, 0);
}

/// The descend that records the earlier operand's facts, run for what it
/// NAMES: does the later operand reach anything any of them is about?
///
/// The names have to come from this walk and not from `collectRefinement`,
/// which answers for one comparison.  A `!A` and a parenthesised `A or B` are
/// both shapes it has no case for, so asking it about the earlier operand
/// found no name at all; and a settled `A or B` it does model reaches both
/// sides, which `mergeFact` collapses to the first.
/// Either way the operand's facts were kept under a later operand that could
/// rewrite them, and the rules read them as proof.
///
/// Enumerating by hand is also what keeps the answer complete: a proved
/// comparison records under more names than `collectRefinement` reports (see
/// `recordedFactSurvivesLater`), so reading the names off the recording
/// would under-check exactly the facts that get kept.
fn earlierFactsOutliveLaterOperand(
    o: *Oracle,
    st: *const State,
    node: Ast.Node.Index,
    later: Ast.Node.Index,
    truth: bool,
    depth: u8,
) bool {
    if (depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return false;
    }
    if (!o.spend()) return false;
    const current = unwrapGrouped(o.tree, node);
    switch (o.tree.nodeTag(current)) {
        // A recorded `!A` is re-derived as `A` with the flipped truth, so the
        // name to check is the operand's, not the negation's.
        .bool_not => return earlierFactsOutliveLaterOperand(
            o,
            st,
            o.tree.nodeData(current).node,
            later,
            !truth,
            depth + 1,
        ),
        .bool_and, .bool_or => |tag| {
            // Only the settled case records, and it records BOTH sides — each
            // one becomes a predicate of its own.  The unsettled case settles
            // neither, so what its sides would contribute is not this walk's
            // to enumerate, and nothing from it is kept.
            if ((tag == .bool_and) != truth) return false;
            const parts = o.tree.nodeData(current).node_and_node;
            if (!earlierFactsOutliveLaterOperand(o, st, parts[0], later, truth, depth + 1)) return false;
            return earlierFactsOutliveLaterOperand(o, st, parts[1], later, truth, depth + 1);
        },
        else => {},
    }
    // A leaf recording writes through more than one channel: the refinement
    // below, and — for a numeric query — one constraint per RECORDING TARGET.
    // The refinement names the left operand of a comparison only, and only in
    // the arm this walk is asking about, so a leaf proved false (`a > lit`,
    // `a < b`) names nothing at all.  Every name the recording writes has to
    // be asked for here, because none of them can be read back off it.
    var refine: Refinement = .{};
    collectRefinement(o, st, current, &refine);
    const scalar = if (truth) refine.then_scalar.name else refine.else_scalar.name;
    const container = if (truth) refine.then_container.name else refine.else_container.name;
    const equality = if (truth) refine.then_equal else refine.else_equal;
    if (!recordedFactSurvivesLater(o, st, scalar, .scalar, later)) return false;
    if (!recordedFactSurvivesLater(o, st, container, .container, later)) return false;
    if (equality) |eq| {
        if (!recordedFactSurvivesLater(o, st, eq.scalar, .scalar, later)) return false;
        if (!recordedFactSurvivesLater(o, st, eq.container, .container, later)) return false;
    }
    if (o.query == .numeric_range) {
        // The recording targets are not only comparison OPERANDS: a std math
        // finiteness predicate records under the argument it was handed
        // (`std.math.isFinite(x)` true, `std.math.isNan(x)` false), and that
        // is exactly the name a later `poison(&x)` rewrites.  Reading them off
        // the producer is what keeps this set the one that is kept.
        var evaluation = evaluator(o, st);
        const targets = numeric_eval.recordedTargets(&evaluation, current, truth);
        for (targets.slice()) |target| {
            const name = numeric_eval.path(o.tree, target) orelse continue;
            // The same rule `dropIndirectFacts` drops a numeric fact by,
            // so what survives here is what survives there.
            if (!recordedFactSurvivesLater(o, st, name, .scalar, later)) return false;
        }
    }
    return true;
}

/// Which survival rule a recorded name is checked by.  A `c.len` fact is a
/// container fact and every other operand key is a scalar one — the same
/// split `dropIndirectFacts` makes when a call invalidates them.
const FactKind = enum { scalar, container };

/// Does a fact recorded under `name` — and every name it is handed on to —
/// still hold after `later` has run?
///
/// `applyRefineFacts` does not stop at the name it is given: a scalar fact
/// marks each alias's container non-empty, a container fact marks each
/// alias's scalar non-zero, and a difference fact marks its minuend
/// non-zero.  Those names are recorded in the same pass from the same
/// comparison, so they describe the same state and have to survive it too.
fn recordedFactSurvivesLater(
    o: *Oracle,
    st: *const State,
    name: ?[]const u8,
    kind: FactKind,
    later: Ast.Node.Index,
) bool {
    const key = name orelse return true;
    if (!o.spend()) return false;
    // `later` is an operand expression, not necessarily a call: `.one` answers
    // "reaches everything" for any node that is not a call, so a call nested
    // inside `!f(x)` was charged as an arbitrary effect.  The subtree scan
    // names the calls and writes the operand really holds.
    const effect: Reach = .{ .subtree = later };
    const survives = switch (kind) {
        .scalar => numeric_escape.scalarSurvivesCall(o, key, effect),
        .container => numeric_escape.containerSurvivesCall(o, key, effect),
    };
    if (!survives) return false;
    for (st.aliases.items) |alias| {
        if (std.mem.eql(u8, alias.scalar, key)) {
            if (!numeric_escape.containerSurvivesCall(o, alias.container, effect)) return false;
        } else if (std.mem.eql(u8, alias.container, key)) {
            if (!numeric_escape.scalarSurvivesCall(o, alias.scalar, effect)) return false;
        }
    }
    if (kind == .scalar) {
        for (st.diff_aliases.items) |da| {
            if (!std.mem.eql(u8, da.diff, key)) continue;
            if (!numeric_escape.scalarSurvivesCall(o, da.minuend, effect)) return false;
        }
    }
    return true;
}

/// Does `node` write anything itself?  A write is not a callee, so the
/// reachability model that answers for calls has nothing to say about it —
/// every assignment therefore disqualifies the earlier operand's facts, and
/// running out of walk depth answers yes for the same reason.
fn writesDirectly(o: *Oracle, node: Ast.Node.Index, depth: u8) bool {
    if (depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return true;
    }
    if (!o.spend()) return true;
    if (numeric_nodes.isScalarAssignTag(o.tree.nodeTag(node))) return true;
    var children = @import("type_engine").AstIterator.init(o.tree, node);
    while (children.next(o.tree)) |child| if (writesDirectly(o, child, depth + 1)) return true;
    return false;
}

fn applyRefineFacts(
    o: *Oracle,
    st: *State,
    scalar: RefinedFact,
    container: RefinedFact,
    equality: ?Equality,
) error{OutOfMemory}!void {
    if (scalar.name) |s| {
        try st.scalars.add(o.gpa, s);
        if (scalar.min >= 1) try st.setScalarMin(o.gpa, s, scalar.min);
        // Propagate via `const s = c.len`: s != 0 ⟹ c non-empty.
        for (st.aliases.items) |a| {
            if (std.mem.eql(u8, a.scalar, s)) try st.containers.add(o.gpa, a.container);
        }
        // Propagate via `const s = MINUEND - SUBTRAHEND`: s != 0 and
        // SUBTRAHEND >= 0 (provably) ⟹ MINUEND > SUBTRAHEND >= 0 ⟹ MINUEND >= 1.
        // Sound when operandProvablyNonneg(sub_node): literal, .len field, or
        // ZLS-confirmed unsigned type.  Identifier subtrahends (e.g. `range.start`)
        // require ZLS; without it, the propagation is silently skipped.
        for (st.diff_aliases.items) |da| {
            if (!std.mem.eql(u8, da.diff, s)) continue;
            if (operandProvablyNonneg(o, da.sub_node)) {
                try st.scalars.add(o.gpa, da.minuend);
            }
        }
    }
    if (container.name) |c| {
        try st.containers.add(o.gpa, c);
        if (container.min > 0) try st.setMinLen(o.gpa, c, container.min);
        // c non-empty ⟹ any snapshot `s = c.len` is != 0.
        for (st.aliases.items) |a| {
            if (std.mem.eql(u8, a.container, c)) try st.scalars.add(o.gpa, a.scalar);
        }
    }
    if (equality) |eq| {
        try st.addAlias(o.gpa, .{ .scalar = eq.scalar, .container = eq.container });
        if (st.scalars.contains(eq.scalar)) try st.containers.add(o.gpa, eq.container);
        if (st.containers.contains(eq.container)) try st.scalars.add(o.gpa, eq.scalar);
    }
}

/// The consequences of a retained predicate, derived exactly once.
///
/// A retained predicate is a FIXED rule: `!(A and B)` settles `!B` the moment
/// `A` is retained, and no later predicate changes what `!A` gives.  The fold
/// therefore decides each of those the moment its predicate is recorded and
/// never reads it again.  That is the whole of the difference from re-folding
/// the predicate list, which re-read every predicate the state had accumulated
/// — once per pass, and once over per condition the body proved, so a body's
/// cost grew with the square of its predicate count.  An atomic comparison has
/// no operand to imply and a settled compound has already implied both of its,
/// so neither is ever read a second time.
///
/// What is NOT a fixed rule is an `and`/`or` in the direction that proves
/// neither operand: `!(A and B)` needs `A` or `B` retained, `A or B` needs `!A`
/// or `!B`.  Those are `State.unsettled`, keyed on the operand whose arrival
/// settles them, and they live on the state because a compound and its operand
/// are routinely recorded by different statements.
///
/// One queue per entry into the fold, and it never holds more than the chain of
/// derivations that entry started: a predicate already in the state was decided
/// when it was recorded, and a consequence already in the state has had its
/// own consequences decided too.  `pump` walks each item once.
///
/// The implications are exactly the ones the refold drew, in the same
/// direction: `!(A and B)` plus `A` proves `!B`, `A or B` plus `!A` proves `B`,
/// `!(A or B)` proves both operands false, and nothing here proves a converse.
/// Every recursion goes through the queue rather than the call stack, so a
/// chain of compounds costs one frame and its steps, and the step counter is
/// charged per item exactly as the refold charged one per predicate visit.
const Fold = struct {
    o: *Oracle,
    st: *State,
    /// Retained predicates whose consequences are still owed.
    queue: std.ArrayListUnmanaged(Predicate) = .empty,
    /// The next one to look at.
    cursor: usize = 0,

    fn deinit(self: *Fold) void {
        self.queue.deinit(self.o.gpa);
    }

    /// Record `original` as a retained predicate and queue what it implies.
    /// False when the state already carried it: that one was decided when it
    /// was recorded, so nothing is owed for it now.
    fn imply(self: *Fold, original: Ast.Node.Index, truth: bool) error{OutOfMemory}!bool {
        const o = self.o;
        const st = self.st;
        const node = unwrapGrouped(o.tree, original);
        const predicate = Predicate{ .node = node, .truth = truth };
        // Only published selectors are type-proved bools; arbitrary nonzero
        // scalars cannot establish a conditional header's selected branch.
        if (truth) {
            if (identName(o.tree, node)) |name| {
                for (st.conditional_lengths.items) |entry| {
                    if (!std.mem.eql(u8, entry.selector, name)) continue;
                    try st.scalars.add(o.gpa, name);
                    break;
                }
            }
        }
        if (st.hasPredicate(predicate)) return false;
        if (o.query == .numeric_range or o.query == .min_len_container) try refineNumeric(o, st, node, truth);
        var refine: Refinement = .{};
        collectRefinement(o, st, node, &refine);
        if (truth) {
            try applyRefineFacts(o, st, refine.then_scalar, refine.then_container, refine.then_equal);
        } else {
            try applyRefineFacts(o, st, refine.else_scalar, refine.else_container, refine.else_equal);
        }
        try mirrorAliasedStorage(self, node, truth, refine);
        _ = try st.addPredicate(o.gpa, predicate);
        try liftDisequalityOrder(self, node, truth);
        try self.queue.append(o.gpa, predicate);
        return true;
    }

    /// Look at every predicate this entry retained, once each.
    fn pump(self: *Fold) error{OutOfMemory}!void {
        while (self.cursor < self.queue.items.len) {
            const arrived = self.queue.items[self.cursor];
            self.cursor += 1;
            if (!self.o.spend()) return;
            try self.settle(arrived);
            try self.handOver(arrived);
        }
    }

    /// Hand `arrived` to every compound that was waiting on this operand.
    ///
    /// The test is the one `offer` refused on, so a compound settles on
    /// exactly the predicate that supplies what it was missing — wherever in
    /// the file the two are spelled, and whether they were recorded by the
    /// same statement or by two statements far apart.
    fn settle(self: *Fold, arrived: Predicate) error{OutOfMemory}!void {
        const o = self.o;
        const st = self.st;
        if (st.unsettled.items.len == 0) return;
        const operand = unwrapGrouped(o.tree, arrived.node);
        var i: usize = 0;
        while (i < st.unsettled.items.len) {
            // The scan is charged per entry, as the refold charged per
            // predicate visit: a walk that spends nothing here would be hiding
            // the cost of looking at every dependency from the bound that is
            // supposed to report it.
            if (!self.o.spend()) return;
            const entry = st.unsettled.items[i];
            const parts: [2]Ast.Node.Index = o.tree.nodeData(entry.predicate.node).node_and_node;
            if (entry.needed != arrived.truth or
                !sameExpression(o.tree, unwrapGrouped(o.tree, parts[entry.side]), operand))
            {
                i += 1;
                continue;
            }
            _ = st.unsettled.swapRemove(i);
            _ = try self.imply(parts[1 - entry.side], entry.predicate.truth);
        }
    }

    /// What `predicate` hands over on its own, with nothing else in hand.
    fn handOver(self: *Fold, predicate: Predicate) error{OutOfMemory}!void {
        const tree = self.o.tree;
        const tag = tree.nodeTag(predicate.node);
        if (tag == .bool_not) {
            _ = try self.imply(tree.nodeData(predicate.node).node, !predicate.truth);
            return;
        }
        if (tag != .bool_and and tag != .bool_or) return;
        const parts = tree.nodeData(predicate.node).node_and_node;
        if ((tag == .bool_and) == predicate.truth) {
            // `A and B` proved, `A or B` disproved: both operands follow, and
            // nothing recorded later can take that back.
            _ = try self.imply(parts[0], predicate.truth);
            _ = try self.imply(parts[1], predicate.truth);
            return;
        }
        // `A and B` disproved, `A or B` proved: either operand settles the
        // other, and only once it is itself retained.
        try self.offer(predicate, parts, 0);
        try self.offer(predicate, parts, 1);
    }

    fn offer(
        self: *Fold,
        predicate: Predicate,
        parts: [2]Ast.Node.Index,
        side: usize,
    ) error{OutOfMemory}!void {
        const needed = !predicate.truth;
        // The operand is UNWRAPPED here for the same reason `imply` unwraps
        // what it records: `hasPredicateNode` compares token spans, and the
        // span of a parenthesised `a and (b)` operand starts at its `(`.  A
        // grouped operand would therefore never match the ungrouped predicate
        // it is the same expression as, and the entry registered below would be
        // one nothing can ever settle.
        if (hasPredicateNode(self.o.tree, self.st, unwrapGrouped(self.o.tree, parts[side]), needed)) {
            _ = try self.imply(parts[1 - side], predicate.truth);
            return;
        }
        try self.st.addUnsettled(self.o.gpa, .{
            .predicate = predicate,
            .side = @intCast(side),
            .needed = needed,
        });
    }
};

/// Record the same lower bound under the STORAGE a `p.*` guard describes.
///
/// A guard about `p.*` is a claim about the storage `p` points at, and that
/// claim outlives the pointer: `p = other` replaces which storage `p` NAMES,
/// it does not rewrite the storage the guard already described.  Spelling the
/// bound again as `first.*` is what survives the rebind.  Resolving the alias
/// at the GUARD's own anchor is what makes that true — resolving it later would
/// move the fact onto whatever `p` names afterwards, which is the one reading
/// the source does not make.
///
/// Only a pointer this body bound to a name of its own resolves, so the extra
/// key names storage the walk could already have written.  A pointer whose
/// target this body never established resolves to nothing and records nothing.
fn mirrorAliasedStorage(
    fold: *Fold,
    node: Ast.Node.Index,
    truth: bool,
    refine: Refinement,
) error{OutOfMemory}!void {
    const o = fold.o;
    const st = fold.st;
    const fact = if (truth) refine.then_scalar else refine.else_scalar;
    const source = fact.name orelse return;
    const bound = fact.min;
    if (bound < 1) return;
    const dot = std.mem.indexOfScalar(u8, source, '.') orelse return;
    const root = source[0..dot];
    if (!o.pointer_roots.contains(root)) return;
    const storage = try numeric_escape.resolveEscapePath(o, root, o.tree.firstToken(node));
    if (storage.len == 0 or std.mem.eql(u8, storage, root)) return;
    if (!o.spend()) return;
    const mirror = try internPath(o, storage, source[dot..]);
    try st.setScalarMin(o.gpa, mirror, bound);
    try st.scalars.add(o.gpa, mirror);
}

/// `x != y` together with a proved `y <= x` proves `x > y`, and `y`'s own
/// proven floor carries that to `x >= floor + 1`.
///
/// The two OVERLAPPING intervals are deliberately not the input.  `x` in
/// `[0, 9]` and `y` in `[5, 14]` say nothing about which is larger, and no
/// endpoint of either is a proof of anything; what this reads is the two
/// RELATIONS the walk retained, and `weakOrderProves` compares the operand
/// expressions themselves rather than the names they are spelled with, so the
/// order is always one the source established on this path.
///
/// A signed `y` has no floor this module will guess at, so the lift declines
/// for it exactly as every other lower bound does.
fn liftDisequalityOrder(fold: *Fold, node: Ast.Node.Index, truth: bool) error{OutOfMemory}!void {
    const o = fold.o;
    const st = fold.st;
    const tree = o.tree;
    const tag = tree.nodeTag(node);
    // `x != y` and `!(x == y)` are the same predicate.
    if (!((tag == .bang_equal and truth) or (tag == .equal_equal and !truth))) return;
    const parts = tree.nodeData(node).node_and_node;
    const greater = unwrapGrouped(tree, parts[0]);
    const lesser = unwrapGrouped(tree, parts[1]);
    const key = scalarPath(o, greater) orelse return;
    _ = scalarPath(o, lesser) orelse return;
    if (!weakOrderProves(o, st, lesser, greater)) return;
    const floor = exprMin(o, st, lesser) orelse return;
    if (floor == std.math.maxInt(u64)) return;
    try st.setScalarMin(o.gpa, key, floor + 1);
    try st.scalars.add(o.gpa, key);
}

/// Does a retained predicate prove `lesser <= greater`?
///
/// The mirror of `differenceOrdered`, which asks the same list for the STRICT
/// form: `y <= x` recorded directly, `x >= y` recorded directly, and each of
/// their negations, all four normalised to the one orientation so the two
/// operands are always compared as the same canonical expressions.
fn weakOrderProves(o: *Oracle, st: *const State, lesser: Ast.Node.Index, greater: Ast.Node.Index) bool {
    const tree = o.tree;
    for (st.predicates.items) |predicate| {
        if (!o.spend()) return false;
        const tag = tree.nodeTag(predicate.node);
        const forward = (tag == .less_or_equal and predicate.truth) or
            (tag == .greater_than and !predicate.truth);
        const reverse = (tag == .greater_or_equal and predicate.truth) or
            (tag == .less_than and !predicate.truth);
        if (!forward and !reverse) continue;
        const operands = tree.nodeData(predicate.node).node_and_node;
        const low = if (forward) operands[0] else operands[1];
        const high = if (forward) operands[1] else operands[0];
        if (sameExpression(tree, unwrapGrouped(tree, low), lesser) and
            sameExpression(tree, unwrapGrouped(tree, high), greater)) return true;
    }
    return false;
}

fn hasPredicateNode(
    tree: *const Ast,
    st: *const State,
    node: Ast.Node.Index,
    truth: bool,
) bool {
    for (st.predicates.items) |predicate| {
        if (predicate.truth == truth and sameExpression(tree, predicate.node, node)) return true;
    }
    return false;
}

/// One fact a guard establishes, and the lower bound it proves for it.
///
/// The name and the bound are ONE value, not two parameters every call has to
/// keep in step: a name with no bound is a fact, and a bound with no name is
/// nothing at all, so a pair threaded separately through four call sites is a
/// place to swap one for the other.
const RefinedFact = struct {
    name: ?[]const u8 = null,
    /// `0` means "recorded, and no lower bound proven": the `x != 0` shape,
    /// which is a fact about `x` and nothing about its size.  A CONTAINER
    /// fact defaults to 1 instead, because `applyRefineFacts` reads every
    /// recorded container as non-empty and a container name with no bound has
    /// still proven exactly that.
    min: u64 = 0,
};

/// Fold `src` into `dst` when it speaks about the same name.
///
/// The FIRST fact recorded for a name wins the slot, and a later fact about
/// that SAME name can only raise the bound.  Two facts about DIFFERENT names
/// are both true and only one of them can be carried, so the second is
/// dropped — which is the direction the consumers need, because a fact about
/// the wrong name proves nothing about the one they ask about.
fn mergeFact(dst: *RefinedFact, src: RefinedFact) void {
    const name = src.name orelse return;
    if (dst.name == null) {
        dst.* = .{ .name = name, .min = src.min };
    } else if (std.mem.eql(u8, dst.name.?, name) and src.min > dst.min) {
        dst.min = src.min;
    }
}

/// Record a name that is nonzero / non-empty, keeping any bound already there.
/// A name the slot already holds is left alone: a second name is dropped
/// rather than replacing the first, and this only supplies the name.
fn setFactNameIfAbsent(dst: *RefinedFact, name: []const u8) void {
    if (dst.name == null) dst.name = name;
}

/// Record a name AND its bound only into an empty slot, never raising or
/// replacing what is already there.  Distinct from `mergeFact` on purpose:
/// this is the rule the expression-bound comparison was read with, and
/// collapsing the two would make a later `x >= N` rewrite an earlier
/// `x != 0` that it never contradicted.
fn setFactIfAbsent(dst: *RefinedFact, src: RefinedFact) void {
    if (src.name == null) return;
    if (dst.name == null) dst.* = src;
}

const Refinement = struct {
    then_scalar: RefinedFact = .{},
    else_scalar: RefinedFact = .{},
    then_container: RefinedFact = .{ .min = 1 },
    else_container: RefinedFact = .{ .min = 1 },
    then_equal: ?Equality = null,
    else_equal: ?Equality = null,
};

fn collectRefinement(o: *Oracle, st: *const State, cond: Ast.Node.Index, out: *Refinement) void {
    if (!o.spend()) return;
    const tree = o.tree;
    const tag = tree.nodeTag(cond);
    if (tag == .bool_and) {
        // `(A) and (B)` true ⟹ both A and B ⟹ union of their THEN-refinements.
        const d = tree.nodeData(cond).node_and_node;
        var a: Refinement = .{};
        var b: Refinement = .{};
        collectRefinement(o, st, d[0], &a);
        collectRefinement(o, st, d[1], &b);
        mergeFact(&out.then_scalar, a.then_scalar);
        mergeFact(&out.then_scalar, b.then_scalar);
        mergeFact(&out.then_container, a.then_container);
        mergeFact(&out.then_container, b.then_container);
        if (out.then_equal == null) out.then_equal = a.then_equal orelse b.then_equal;
        return;
    }
    if (tag == .bool_or) {
        // `(A) or (B)` false ⟹ !A and !B ⟹ union of their ELSE-refinements.
        // This is the canonical early-return-on-empty guard:
        //   if (c.len == 0 or c.empty()) return;   // fall-through ⟹ c non-empty
        const d = tree.nodeData(cond).node_and_node;
        var a: Refinement = .{};
        var b: Refinement = .{};
        collectRefinement(o, st, d[0], &a);
        collectRefinement(o, st, d[1], &b);
        mergeFact(&out.else_scalar, a.else_scalar);
        mergeFact(&out.else_scalar, b.else_scalar);
        mergeFact(&out.else_container, a.else_container);
        mergeFact(&out.else_container, b.else_container);
        if (out.else_equal == null) out.else_equal = a.else_equal orelse b.else_equal;
        return;
    }
    const cmp: Cmp = switch (tag) {
        .greater_than => .gt,
        .less_than => .lt,
        .greater_or_equal => .ge,
        .less_or_equal => .le,
        .bang_equal => .ne,
        .equal_equal => .eq,
        else => return,
    };
    const d = tree.nodeData(cond).node_and_node;
    // Determine (operand, literal) orientation.
    const lhs_key = operandKey(o, d[0]);
    const rhs_key = operandKey(o, d[1]);
    if (lhs_key) |lk| {
        if (rhs_key) |rk| setEquality(out, lk, rk, cmp);
    }
    if (lhs_key) |lk| {
        if (intLiteralVal(tree, d[1])) |v| {
            applyCmp(out, lk, cmp, v, false);
        } else if (exprMin(o, st, d[1])) |min| {
            applyCmpExpr(out, lk, cmp, min, false);
        }
    } else if (rhs_key) |rk| {
        // Literal or proven lower-bounded expression on the left → flip orientation.
        if (intLiteralVal(tree, d[0])) |v| {
            applyCmp(out, rk, cmp, v, true);
        } else if (exprMin(o, st, d[0])) |min| {
            applyCmpExpr(out, rk, cmp, min, true);
        }
    }
    // `x < c.len` true ⟹ `c.len >= x + 1`, and `x <= c.len` true ⟹
    // `c.len >= x`.  `exprMin` returns null for anything whose sign it could
    // not establish, so a recorded minimum here is always a real lower bound
    // and the container is that much longer.
    //
    // The reversed spelling reaches this on its own: there the container is
    // the LEFT operand, so `applyCmpExpr` reads the container's own key.
    // Written the other way round the container is the right operand, every
    // branch above keyed on the SCALAR side, and the length the comparison
    // bounds was recorded nowhere — which is why `while (i < c.len) { … c.len
    // - 1 … }` could not see that `c` is not empty inside the loop.
    if (cmp != .lt and cmp != .le) return;
    const container = rhs_key orelse return;
    if (!container.is_container) return;
    const bound = exprMin(o, st, d[0]) orelse return;
    const minimum = if (cmp == .lt) bound +| 1 else bound;
    // A minimum of zero is not a length fact: `applyRefineFacts` reads any
    // recorded container as non-empty, and `0 <= c.len` says nothing about
    // that — it holds for the empty container too.
    if (minimum == 0) return;
    mergeFact(&out.then_container, .{ .name = container.key, .min = minimum });
}

const Cmp = enum { gt, lt, ge, le, ne, eq };

fn setEquality(out: *Refinement, lhs: OperandKey, rhs: OperandKey, cmp: Cmp) void {
    if (cmp != .eq and cmp != .ne) return;
    const equality: ?Equality = if (lhs.is_container and !rhs.is_container)
        .{ .scalar = rhs.key, .container = lhs.key }
    else if (!lhs.is_container and rhs.is_container)
        .{ .scalar = lhs.key, .container = rhs.key }
    else
        null;
    const eq = equality orelse return;
    if (cmp == .eq) {
        if (out.then_equal == null) out.then_equal = eq;
    } else if (out.else_equal == null) {
        out.else_equal = eq;
    }
}
const OperandKey = struct { key: []const u8, is_container: bool };

fn expressionPositive(o: *Oracle, st: *const State, node: Ast.Node.Index) bool {
    if (lenContainerPath(o, node)) |path| {
        if (containerProvenNonEmpty(o.tree, st, path)) return true;
    }
    const name = scalarPath(o, node);
    if (exprMin(o, st, node)) |lower| {
        if (lower > 0) return true;
        // A non-null `exprMin` is a proven NON-NEGATIVE lower bound: every
        // branch yields a length, a literal, a recorded fact, or a resolved
        // UNSIGNED type, never a signed domain.  On top of that domain a
        // proved `!= 0` does mean `> 0`, because no non-negative value other
        // than zero is nonzero.
        return name != null and st.scalars.contains(name.?);
    }
    // `exprMin` proved no lower bound at all, which is exactly the signed or
    // unresolved case.  A dominating `!= 0` carries no sign information there
    // — `-1 != 0` — so it may only be read as `> 0` after the DECLARED domain
    // has been recovered as unsigned.  Recovering it must not mean assuming
    // it: a name whose type the walk could not resolve is not an unsigned
    // name.
    const path = name orelse return false;
    if (!st.scalars.contains(path)) return false;
    const declared = declaredTypeOf(o, numeric_escape.rootText(path), o.tree.firstToken(node)) orelse return false;
    return parameterNonnegative(o, declared);
}

/// Return a proven non-negative lower bound for an integer expression.  This
/// intentionally returns null for unknown signed values: a name-only guess
/// would make `x > rhs` prove `x != 0` when `rhs` can be negative.
fn exprMin(o: *Oracle, st: *const State, node: Ast.Node.Index) ?u64 {
    if (o.expression_depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return null;
    }
    o.expression_depth += 1;
    defer o.expression_depth -= 1;
    if (!o.spend()) return null;
    const tree = o.tree;
    const n = unwrapGrouped(tree, node);
    if (lenContainerPath(o, n)) |path| {
        // A user-defined field can be named `len` and still be signed.
        // Its declared negative domain must not acquire a collection's zero
        // floor. Only a numeric value proof can supply a nonnegative floor.
        if (o.cache) |cache| if (cache.intInfoOf(n)) |info| {
            if (info.signed) return recordedFloor(st, nodeSrc(tree, n));
        };
        if (st.minLenOf(path)) |minimum| return minimum;
        if (st.containers.contains(path)) return 1;
        if (o.cache) |cache| {
            const container = tree.nodeData(n).node_and_token[0];
            if (cache.fixedArrayLenOf(container)) |length| return length;
        }
        if (recordedFloor(st, nodeSrc(tree, n))) |floor| return floor;
        return 0;
    }
    if (intLiteralVal(tree, n)) |v| return v;
    if (scalarPath(o, n)) |name| {
        if (st.scalarMinOf(name)) |v| return v;
        if (st.scalarVal(name)) |v| return v;
        if (o.cache) |cache| {
            if (cache.comptimeIntValueOf(n)) |value| return value;
        }
        // The NUMERIC channel is read before the declared type is, because the
        // type is the whole domain and a proven interval inside it is the
        // narrower of the two answers.  A refinement that proved `start < end`
        // while the body was walked left `end`'s own interval on this name, and
        // the unsigned-domain answer below would report zero for it — which is
        // the one value the interval had already excluded.
        if (recordedFloor(st, name)) |floor| return floor;
        if (o.cache) |cache| {
            if (cache.intInfoOf(n)) |info| if (!info.signed) return 0;
        }
        // A root-scope `const` the file itself defines is a compile-time
        // integer whether or not a type engine is attached — a vector block
        // length is written `const VLEN: usize = 64;` — and reading it here
        // is what lets that proof be asked by a rule that carries no
        // resolver, which is the whole difference between `@min(VLEN, …)`
        // reading as 64 and reading as nothing at all.
        //
        // The declarations come from the file cache's one per-file index, so
        // this costs a lookup and never a walk of the file's nodes, and the
        // table withholds a name this walk binds as well as a name the file
        // declares twice: a local of the same name is a different value, and
        // neither of two root bindings can be shown to be the one a use
        // means.  Both are answered by the walk or by nothing at all.
        if (o.file_consts) |consts| {
            if (consts.lookup(name)) |initializer| {
                var evaluation = evaluator(o, st);
                const value = evaluation.evaluate(initializer);
                if (value == .integer and value.integer.min >= 0 and
                    value.integer.max <= std.math.maxInt(u64)) return @intCast(value.integer.max);
            }
        }
        if (derefIsUnsignedParameter(o, n)) return 0;
        return null;
    }
    return switch (tree.nodeTag(n)) {
        .@"try" => exprMin(o, st, tree.nodeData(n).node),
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => builtinMin(o, st, n),
        .call, .call_comma, .call_one, .call_one_comma => if (callResultNonzero(o, n, st)) 1 else null,
        .add => blk: {
            const d = tree.nodeData(n).node_and_node;
            const lhs = exprMin(o, st, d[0]) orelse break :blk null;
            const rhs = exprMin(o, st, d[1]) orelse break :blk null;
            if (lhs > std.math.maxInt(u64) - rhs) break :blk null;
            break :blk lhs + rhs;
        },
        .sub => blk: {
            const d = tree.nodeData(n).node_and_node;
            const minuend = unwrapGrouped(tree, d[0]);
            const subtrahend = unwrapGrouped(tree, d[1]);
            const lhs = exprMin(o, st, minuend) orelse break :blk null;
            if (intLiteralVal(tree, subtrahend)) |rhs| {
                if (lhs < rhs) break :blk null;
                break :blk lhs - rhs;
            }
            // A literal subtrahend is the only way the difference is exact.
            // Otherwise the ORDER of the two operands has to come from the
            // walk, and a comparison that proves it is what a bounded loop
            // leaves behind: `while (cursor < input.len)` records itself on
            // the body walk, so a block length read in the body can use the
            // difference the condition ordered.  Unordered operands leave the
            // difference saying nothing at all.
            if (differenceOrdered(o, st, minuend, subtrahend)) break :blk 1;
            break :blk null;
        },
        else => blk: {
            if (o.cache) |cache| {
                if (cache.intInfoOf(n)) |info| if (!info.signed) break :blk 0;
            }
            break :blk null;
        },
    };
}

/// The smallest value a recorded numeric interval for `name` still admits,
/// when that smallest value is itself a `u64` and not negative.
///
/// The interval is read from the same table `refineNumeric` writes, and it is
/// already the value's range and not its type's: the evaluator narrows every
/// fact to the declared type before recording it, so an interval that came
/// back with a positive floor is one the type already agreed with, and a
/// signed name is covered by exactly the same rule as an unsigned one.
///
/// Three things answer nothing, and all three mean "no floor was proved":
/// no entry at all, an entry whose range is not an integer (a float, or the
/// `unknown` an assignment the walk could not evaluate leaves behind), and an
/// interval that starts below zero — the first of a signed domain, which this
/// whole function refuses to guess at.
fn recordedFloor(st: *const State, name: []const u8) ?u64 {
    const value = st.numericValue(name);
    if (value != .integer) return null;
    const floor = value.integer.min;
    if (floor < 0 or floor > @as(i128, std.math.maxInt(u64))) return null;
    return @intCast(floor);
}

/// Does a retained predicate prove `subtrahend < minuend`?
/// A predicate is only ever recorded for a comparison PROVED on the path that
/// reaches the use, and it is dropped again wherever the branches join
/// without both of them holding it, so the order this reads is the order the
/// source established on this path — nothing about it comes from the spelling
/// of the names.
///
/// Only a STRICT order counts.  `a <= b` leaves the difference at zero for the
/// equal case, and a zero block length is exactly what underflows when it is
/// indexed at `- 1`.
fn differenceOrdered(o: *Oracle, st: *const State, minuend: Ast.Node.Index, subtrahend: Ast.Node.Index) bool {
    const tree = o.tree;
    for (st.predicates.items) |predicate| {
        if (!o.spend()) return false;
        const tag = tree.nodeTag(predicate.node);
        const forward = (tag == .less_than and predicate.truth) or
            (tag == .greater_or_equal and !predicate.truth);
        const reverse = (tag == .greater_than and predicate.truth) or
            (tag == .less_or_equal and !predicate.truth);
        if (!forward and !reverse) continue;
        const operands = tree.nodeData(predicate.node).node_and_node;
        const low = if (forward) operands[0] else operands[1];
        const high = if (forward) operands[1] else operands[0];
        if (sameExpression(tree, unwrapGrouped(tree, low), subtrahend) and
            sameExpression(tree, unwrapGrouped(tree, high), minuend)) return true;
    }
    return false;
}

fn builtinMin(o: *Oracle, st: *const State, node: Ast.Node.Index) ?u64 {
    const tree = o.tree;
    var buffer: [2]Ast.Node.Index = undefined;
    const arguments = tree.builtinCallParams(&buffer, node) orelse return null;
    const name = tree.tokenSlice(tree.nodeMainToken(node));
    if (arguments.len == 1 and std.mem.eql(u8, name, "@intCast")) return exprMin(o, st, arguments[0]);
    if (arguments.len != 2) return null;
    if (std.mem.eql(u8, name, "@as")) return exprMin(o, st, arguments[1]);
    const left = exprMin(o, st, arguments[0]);
    const right = exprMin(o, st, arguments[1]);
    if (std.mem.eql(u8, name, "@max")) {
        if (left == null) return right;
        if (right == null) return left;
        return @max(left.?, right.?);
    }
    if (std.mem.eql(u8, name, "@min")) return @min(left orelse return null, right orelse return null);
    return null;
}

fn derefIsUnsignedParameter(o: *Oracle, node: Ast.Node.Index) bool {
    const tree = o.tree;
    if (tree.nodeTag(node) != .deref) return false;
    const name = identName(tree, tree.nodeData(node).node) orelse return false;
    const ast_tokens = @import("../ast/tokens.zig");
    const declaration = ast_tokens.enclosingFnDecl(tree, tree.firstToken(o.body) + 1) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = ast_tokens.fnProto(tree, &buffer, declaration) orelse return false;
    var parameters = proto.iterate(tree);
    while (parameters.next()) |parameter| {
        const name_token = parameter.name_token orelse continue;
        if (!std.mem.eql(u8, name, tree.tokenSlice(name_token))) continue;
        const type_node = parameter.type_expr orelse return false;
        if (tree.tokens.items(.tag)[tree.firstToken(type_node)] != .asterisk) return false;
        const pointer = tree.fullPtrType(type_node) orelse return false;
        return parameterNonnegative(o, pointer.ast.child_type);
    }
    return false;
}

fn isTrueExpr(tree: *const Ast, node: Ast.Node.Index) bool {
    const n = unwrapGrouped(tree, node);
    return tree.nodeTag(n) == .identifier and
        std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(n)), "true");
}

/// True iff `node` (a comparison operand) is provably >= 0, so that
/// `key > node` soundly implies `key >= 1`:
///   - a bare number literal (the AST represents `-5` as a negation node, so a
///     `.number_literal` is always non-negative);
///   - a `.len` field access (slice/array length is always >= 0);
///   - an integer expression the type engine resolves to an UNSIGNED type.
fn operandProvablyNonneg(o: *Oracle, node: Ast.Node.Index) bool {
    const tree = o.tree;
    if (tree.nodeTag(node) == .number_literal) return true;
    if (lenContainerPath(o, node) != null) return true;
    if (o.cache) |c| {
        if (c.intInfoOf(node)) |info| return !info.signed;
    }
    return false;
}

/// Record that `ok` is nonzero / non-empty in the THEN arm.
fn setThenNonzero(out: *Refinement, ok: OperandKey) void {
    if (ok.is_container) {
        setFactNameIfAbsent(&out.then_container, ok.key);
    } else setFactNameIfAbsent(&out.then_scalar, ok.key);
}

fn setElseNonzero(out: *Refinement, ok: OperandKey) void {
    if (ok.is_container) {
        setFactNameIfAbsent(&out.else_container, ok.key);
    } else setFactNameIfAbsent(&out.else_scalar, ok.key);
}

fn scalarPath(o: *Oracle, node: Ast.Node.Index) ?[]const u8 {
    if (identName(o.tree, node)) |name| return name;
    if (fieldPathSrc(o, node)) |path| return path;
    if (o.tree.nodeTag(node) == .deref) {
        if (isPureFieldPath(o.tree, o.tree.nodeData(node).node)) return nodeSrc(o.tree, node);
    }
    return null;
}

/// Classify a comparison operand as either a scalar local `x` or a container
/// length `c.len` (→ container key = source spelling of `c`).
fn operandKey(o: *Oracle, node: Ast.Node.Index) ?OperandKey {
    if (lenContainerPath(o, node)) |c| return .{ .key = c, .is_container = true };
    if (scalarPath(o, node)) |path| return .{ .key = path, .is_container = false };
    return null;
}

/// If `node` is `<c>.len`, return the source spelling of `<c>`; else null.
fn lenContainerPath(o: *Oracle, node: Ast.Node.Index) ?[]const u8 {
    const tree = o.tree;
    if (tree.nodeTag(node) != .field_access) return null;
    const data = tree.nodeData(node).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(data[1]), "len")) return null;
    return nodeSrc(tree, data[0]);
}

/// Apply a comparison `key <cmp> lit` (or flipped) to a refinement.  Encodes
/// the nonzero/non-empty truth of each arm.  `flipped` means literal was on
/// the left (`lit <cmp> key`).
fn applyCmp(out: *Refinement, ok: OperandKey, cmp: Cmp, lit: u64, flipped: bool) void {
    // Normalize to `key OP lit`.
    const op: Cmp = if (!flipped) cmp else switch (cmp) {
        .gt => .lt,
        .lt => .gt,
        .ge => .le,
        .le => .ge,
        .ne => .ne,
        .eq => .eq,
    };
    var then_bound: ?u64 = null;
    var else_bound: ?u64 = null;
    var then_nonzero = false;
    var else_nonzero = false;
    switch (op) {
        .gt => if (lit < std.math.maxInt(u64)) {
            then_bound = lit + 1;
        },
        .ge => if (lit > 0) {
            then_bound = lit;
        },
        .lt => if (lit > 0) {
            else_bound = lit;
        },
        .le => if (lit < std.math.maxInt(u64)) {
            else_bound = lit + 1;
        },
        .eq => if (lit == 0) {
            else_nonzero = true;
        } else {
            then_bound = lit;
        },
        .ne => if (lit == 0) {
            then_nonzero = true;
        },
    }
    if (then_bound != null or then_nonzero) {
        if (ok.is_container) {
            mergeFact(&out.then_container, .{ .name = ok.key, .min = then_bound orelse 1 });
        } else if (then_bound) |bound| {
            mergeFact(&out.then_scalar, .{ .name = ok.key, .min = bound });
        } else {
            setThenNonzero(out, ok);
        }
    }
    if (else_bound != null or else_nonzero) {
        if (ok.is_container) {
            mergeFact(&out.else_container, .{ .name = ok.key, .min = else_bound orelse 1 });
        } else if (else_bound) |bound| {
            mergeFact(&out.else_scalar, .{ .name = ok.key, .min = bound });
        } else {
            setElseNonzero(out, ok);
        }
    }
}

/// Apply a comparison against an expression known to have a lower bound.
/// Unlike `applyCmp`, this does not treat `!=` as a positive lower bound:
/// `x != y` can still hold for a negative `x`.
fn applyCmpExpr(out: *Refinement, ok: OperandKey, cmp: Cmp, rhs_min: u64, flipped: bool) void {
    const op: Cmp = if (!flipped) cmp else switch (cmp) {
        .gt => .lt,
        .lt => .gt,
        .ge => .le,
        .le => .ge,
        .ne => .ne,
        .eq => .eq,
    };
    var then_bound: ?u64 = null;
    var else_bound: ?u64 = null;
    switch (op) {
        .gt => {
            if (rhs_min < std.math.maxInt(u64)) then_bound = rhs_min + 1;
        },
        .ge, .eq => {
            if (rhs_min >= 1) then_bound = rhs_min;
        },
        .lt => {
            if (rhs_min >= 1) else_bound = rhs_min;
        },
        .le => {
            if (rhs_min < std.math.maxInt(u64)) else_bound = rhs_min + 1;
        },
        .ne => {},
    }
    if (ok.is_container) {
        if (then_bound) |bound| {
            setFactIfAbsent(&out.then_container, .{ .name = ok.key, .min = bound });
        }
        if (else_bound) |bound| {
            setFactIfAbsent(&out.else_container, .{ .name = ok.key, .min = bound });
        }
    } else {
        if (then_bound) |bound| mergeFact(&out.then_scalar, .{ .name = ok.key, .min = bound });
        if (else_bound) |bound| mergeFact(&out.else_scalar, .{ .name = ok.key, .min = bound });
    }
}

/// Invalidate the facts an effect can change.  Taking an address is not such
/// an effect: `&x` writes nothing by itself, so a discarded `_ = &x` keeps
/// every bound `x` had.  The write arrives later — with the callee the pointer
/// is handed to, with the deref assignment that writes through it, or with
/// whatever a stored pointer reaches — and every one of those routes reaches
/// `dropIndirectFacts`, which drops each root in `addressed` wholesale.
fn dropEscapedScalarFacts(o: *Oracle, node: Ast.Node.Index, st: *State, depth: u8) void {
    if (depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return;
    }
    if (!o.spend()) return;
    const tree = o.tree;
    if (tree.nodeTag(node) == .fn_decl) return;
    var buffer: [2]Ast.Node.Index = undefined;
    if (tree.builtinCallParams(&buffer, node) != null and
        std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@TypeOf")) return;
    if (mayMutateIndirect(o, node)) dropIndirectFacts(o, st, .{ .one = node });
    var children = @import("type_engine").AstIterator.init(tree, node);
    while (children.next(tree)) |child| {
        dropEscapedScalarFacts(o, child, st, depth + 1);
    }
}

/// Drop container facts whose root path is mutated within `node`'s tokens.
fn killMutatedContainers(o: *Oracle, node: Ast.Node.Index, st: *State) void {
    const tree = o.tree;
    const first = tree.firstToken(node);
    const last = tree.lastToken(node);
    dropEscapedScalarFacts(o, node, st, 0);
    dropContainersMutatedInTokens(tree, first, last, st);
}

fn compoundAddPreservesScalar(o: *Oracle, st: *const State, node: Ast.Node.Index) bool {
    const tree = o.tree;
    const data = tree.nodeData(node).node_and_node;
    const lhs = data[0];
    const name = scalarPath(o, lhs) orelse return false;
    var lhs_nonneg = st.scalarMinOf(name) != null;
    if (!lhs_nonneg) {
        if (o.cache) |cache| {
            if (cache.intInfoOf(lhs)) |info| lhs_nonneg = !info.signed;
        }
    }
    return lhs_nonneg and exprMin(o, st, data[1]) != null;
}

pub fn dropLoopMutated(o: *Oracle, loop_node: Ast.Node.Index, st: *State) void {
    const tree = o.tree;
    const first = tree.firstToken(loop_node);
    const last = tree.lastToken(loop_node);
    dropEscapedScalarFacts(o, loop_node, st, 0);
    // Scalars: drop a nonzero fact only when the loop mutates the name
    // NON-monotonically.  `NAME += …` survives only when both operands have a
    // proven non-negative bound; otherwise an unknown signed addend can reach
    // zero.  Any other assign op (`=`, `-=`, `*=`, …) can reach 0, so drop.
    var ni: u32 = 0;
    while (ni < tree.nodes.len) : (ni += 1) {
        const node: Ast.Node.Index = @enumFromInt(ni);
        const tag = tree.nodeTag(node);
        if (!numeric_nodes.isScalarAssignTag(tag)) continue;
        if (tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
        const lhs = tree.nodeData(node).node_and_node[0];
        const name = scalarPath(o, lhs) orelse {
            // Computed storage has no scalar path; use the existing reach
            // model rather than keep facts on an unresolved write target.
            dropIndirectFacts(o, st, .{ .one = node });
            continue;
        };
        if (tree.nodeTag(lhs) != .identifier) {
            // The loop may be skipped, so no body walk will visit this store.
            // Retire the aliased storage before retaining any loop facts.
            dropAliasedWrite(o, st, name, tree.firstToken(node)) catch |err| {
                o.summary_error = o.summary_error orelse err;
                return;
            };
        }
        st.dropNumericRoot(name);
        st.dropValueAliasesByRoot(name);
        // The loop rebinds the name, so an exact constant recorded for it (a
        // `switch` arm's `scrutinee == K`) and a `name = c.len` snapshot both
        // describe a value this assignment replaces.  `exprMin` reads the
        // constant as a live lower bound and a non-empty container hands its
        // snapshot back a non-zero, so leaving either standing is the same
        // mistake every other rebinding site already undoes.
        st.dropScalarValsRootedAt(name);
        st.dropAliasesByScalar(name);
        st.dropAliasesByContainer(name);
        // A rebind inside the loop replaces the slice whose length this
        // snapshot records, exactly as it replaces the constant and the
        // `name = c.len` alias dropped just above.
        st.dropLenBoundsRootedAt(name);
        st.dropConditionalLengthsRootedAt(name);
        if (tag != .assign_add or !compoundAddPreservesScalar(o, st, node)) {
            st.scalars.removeRooted(name);
            st.dropScalarMinsRootedAt(name);
        }
        // Even monotonic `+=` invalidates `name = left * right`; only the
        // nonzero fact can survive that operation.
        st.dropProductAliasesByName(name);
        dropProductAliasesByConditionName(o, st, name);
        if (stateMentionsName(o, st, name)) st.clearPredicates();
    }
    dropContainersMutatedInTokens(tree, first, last, st);
}

/// Methods that resize, truncate, or otherwise rewrite the receiver's length
/// (`std.ArrayList` / `std.MultiArrayList`, managed and unmanaged spellings).
/// Any of these invalidates a proven `path.len >= N`.  Length-preserving calls
/// (`len`, `clone`, `get`, `slice`, `items`, `sort`, …) are deliberately
/// absent so a pure call keeps the facts it cannot affect.
fn isMutatingMethod(name: []const u8) bool {
    const muts = std.StaticStringMap(void).initComptime(.{
        .{ "addManyAsArray", {} },
        .{ "addManyAsArrayAssumeCapacity", {} },
        .{ "addManyAsArrayBounded", {} },
        .{ "addManyAsSlice", {} },
        .{ "addManyAsSliceAssumeCapacity", {} },
        .{ "addManyAsSliceBounded", {} },
        .{ "addManyAt", {} },
        .{ "addManyAtAssumeCapacity", {} },
        .{ "addManyAtBounded", {} },
        .{ "addOne", {} },
        .{ "addOneAssumeCapacity", {} },
        .{ "addOneBounded", {} },
        .{ "append", {} },
        .{ "appendAssumeCapacity", {} },
        .{ "appendBounded", {} },
        .{ "appendNTimes", {} },
        .{ "appendNTimesAssumeCapacity", {} },
        .{ "appendSlice", {} },
        .{ "appendSliceAssumeCapacity", {} },
        .{ "appendSliceBounded", {} },
        .{ "appendUnalignedSlice", {} },
        .{ "appendUnalignedSliceAssumeCapacity", {} },
        .{ "appendUnalignedSliceBounded", {} },
        .{ "clearAndFree", {} },
        .{ "clearRetainingCapacity", {} },
        .{ "deinit", {} },
        .{ "ensureTotalCapacity", {} },
        .{ "ensureTotalCapacityPrecise", {} },
        .{ "ensureUnusedCapacity", {} },
        .{ "expandToCapacity", {} },
        .{ "insert", {} },
        .{ "insertAssumeCapacity", {} },
        .{ "insertBounded", {} },
        .{ "insertSlice", {} },
        .{ "insertSliceAssumeCapacity", {} },
        .{ "insertSliceBounded", {} },
        .{ "moveToUnmanaged", {} },
        .{ "orderedRemove", {} },
        .{ "orderedRemoveMany", {} },
        .{ "pop", {} },
        .{ "popOrNull", {} },
        .{ "print", {} },
        .{ "printAssumeCapacity", {} },
        .{ "printBounded", {} },
        .{ "replaceRange", {} },
        .{ "replaceRangeAssumeCapacity", {} },
        .{ "replaceRangeBounded", {} },
        .{ "resize", {} },
        .{ "setCapacity", {} },
        .{ "shrinkAndFree", {} },
        .{ "shrinkAndFreePrecise", {} },
        .{ "shrinkRetainingCapacity", {} },
        .{ "shrinkToLen", {} },
        .{ "swapRemove", {} },
        .{ "toManaged", {} },
        .{ "toOwnedSlice", {} },
        .{ "toOwnedSliceAssert", {} },
        .{ "toOwnedSliceSentinel", {} },
        .{ "toOwnedSliceSentinelAssert", {} },
        .{ "writer", {} },
    });
    return muts.has(name);
}

/// For each tracked container path, drop it if the token range mutates it:
/// `<path> . <mutating-method> (` or `<path> <assign-op>` or `<path> . X =`.
fn dropContainersMutatedInTokens(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    st: *State,
) void {
    if (st.containers.keys.items.len == 0 and st.aliases.items.len == 0 and
        st.min_lens.items.len == 0 and st.product_aliases.items.len == 0)
    {
        return;
    }
    const tags = tree.tokens.items(.tag);
    var mutated = false;
    var i: usize = 0;
    while (i < st.containers.keys.items.len) {
        const path = st.containers.keys.items[i];
        if (containerMutatedInTokens(tree, tags, first, last, path)) {
            _ = st.containers.keys.swapRemove(i);
            mutated = true;
        } else i += 1;
    }
    // A mutated container also stales any `n = c.len` length snapshot.
    var ai: usize = 0;
    while (ai < st.aliases.items.len) {
        if (containerMutatedInTokens(tree, tags, first, last, st.aliases.items[ai].container)) {
            _ = st.aliases.swapRemove(ai);
            mutated = true;
        } else ai += 1;
    }
    // ...and any proven `path.len >= N` lower bound (a grow/shrink/clear
    // may invalidate it).
    var mi: usize = 0;
    while (mi < st.min_lens.items.len) {
        if (containerMutatedInTokens(tree, tags, first, last, st.min_lens.items[mi].path)) {
            _ = st.min_lens.swapRemove(mi);
            mutated = true;
        } else mi += 1;
    }
    var pi: usize = 0;
    while (pi < st.product_aliases.items.len) {
        const product = st.product_aliases.items[pi];
        const left_mutated = product.left.is_container and
            containerMutatedInTokens(tree, tags, first, last, product.left.key);
        const right_mutated = product.right.is_container and
            containerMutatedInTokens(tree, tags, first, last, product.right.key);
        if (left_mutated or right_mutated) {
            _ = st.product_aliases.swapRemove(pi);
            mutated = true;
        } else pi += 1;
    }
    if (mutated) st.clearPredicates();
}

/// True iff `path` (a source spelling like "arr" or "self.items") is mutated
/// in [first,last]: a call `path.<mut>(`, `path <assign>`, or `path.<f> =`.
fn containerMutatedInTokens(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    path: []const u8,
) bool {
    var t = first;
    while (t + 1 <= last) : (t += 1) {
        // Match the path as a contiguous source run beginning at token t.
        const after = matchPathTokens(tree, t, last, path) orelse continue;
        // after = token index just past the matched path.
        if (after > last) return false;
        switch (tags[after]) {
            .period => {
                // path.<ident>(  → method call; treat as mutation if the
                // method is mutating, OR `path.<ident> =` (field write).
                if (after + 1 <= last and tags[after + 1] == .identifier) {
                    const m = tree.tokenSlice(after + 1);
                    if (after + 2 <= last and tags[after + 2] == .l_paren and isMutatingMethod(m)) return true;
                    if (after + 2 <= last and isAssignOp(tags[after + 2])) return true;
                }
            },
            else => if (isAssignOp(tags[after])) return true,
        }
    }
    return false;
}

/// If the source spelling `path` matches the contiguous token run starting at
/// `t`, return the token index just past it; else null.  Handles dotted paths
/// like "self.items" (identifier period identifier).
fn matchPathTokens(tree: *const Ast, t: Ast.TokenIndex, last: Ast.TokenIndex, path: []const u8) ?Ast.TokenIndex {
    var cur = t;
    var rest = path;
    while (rest.len > 0) {
        if (cur > last) return null;
        if (tree.tokens.items(.tag)[cur] == .identifier) {
            const slice = tree.tokenSlice(cur);
            if (!std.mem.startsWith(u8, rest, slice)) return null;
            rest = rest[slice.len..];
            cur += 1;
        } else if (rest[0] == '.') {
            if (tree.tokens.items(.tag)[cur] != .period) return null;
            rest = rest[1..];
            cur += 1;
        } else return null;
    }
    return cur;
}

fn dropContainersRootedAt(st: *State, root: []const u8) void {
    st.dropNumericRoot(root);
    var scalar: usize = 0;
    while (scalar < st.scalars.keys.items.len) {
        if (pathRootedAt(st.scalars.keys.items[scalar], root)) {
            _ = st.scalars.keys.swapRemove(scalar);
        } else scalar += 1;
    }
    var bound: usize = 0;
    while (bound < st.scalar_mins.items.len) {
        if (pathRootedAt(st.scalar_mins.items[bound].name, root)) {
            _ = st.scalar_mins.swapRemove(bound);
        } else bound += 1;
    }
    var i: usize = 0;
    while (i < st.containers.keys.items.len) {
        const p = st.containers.keys.items[i];
        // root match: p == root, or p starts with `root.`
        const rooted = std.mem.eql(u8, p, root) or
            (p.len > root.len and std.mem.startsWith(u8, p, root) and p[root.len] == '.');
        if (rooted) _ = st.containers.keys.swapRemove(i) else i += 1;
    }
}

fn pathRootedAt(path: []const u8, root: []const u8) bool {
    return std.mem.eql(u8, path, root) or
        (path.len > root.len and std.mem.startsWith(u8, path, root) and
            (path[root.len] == '.' or path[root.len] == '['));
}

/// Drop every fact, alias and retained predicate keyed on `name` or on a path
/// rooted at it.  This lives in one place on purpose: every write path has to
/// invalidate the same set, each new collection added to `State` would
/// otherwise have to be threaded through one copy per write path by hand, and
/// a line missed in a copy is an unsound answer rather than a lint.
pub fn dropFactsForRebind(o: *Oracle, st: *State, name: []const u8) void {
    st.scalars.removeRooted(name);
    st.dropScalarMinsRootedAt(name);
    dropContainersRootedAt(st, name);
    st.dropMinLensByRoot(name);
    st.dropLenBoundsRootedAt(name);
    st.dropConditionalLengthsRootedAt(name);
    st.dropAliasesByScalar(name);
    // A header rebind breaks the scalar snapshot's equality with its length.
    // Indirect/header-field stores retire aliases through dropIndirectFacts.
    st.dropAliasesByContainer(name);
    st.dropDiffAliasesByName(name);
    st.dropValueAliasesByRoot(name);
    st.dropScalarValsRootedAt(name);
    st.dropProductAliasesByName(name);
    st.dropProductAliasesByRoot(name);
    dropProductAliasesByConditionName(o, st, name);
    if (stateMentionsName(o, st, name)) st.clearPredicates();
}

fn dropProductAliasesByConditionName(o: *Oracle, st: *State, name: []const u8) void {
    var i: usize = 0;
    while (i < st.product_aliases.items.len) {
        const condition = st.product_aliases.items[i].condition orelse {
            i += 1;
            continue;
        };
        if (nodeHasIdentifier(o.tree, condition, name)) {
            _ = st.product_aliases.swapRemove(i);
        } else {
            i += 1;
        }
    }
}

fn stateMentionsName(o: *Oracle, st: *const State, name: []const u8) bool {
    const root = name[0 .. std.mem.indexOfScalar(u8, name, '.') orelse name.len];
    for (st.conditional_lengths.items) |entry| {
        if (pathRootedAt(entry.header, root) or pathRootedAt(entry.selector, root)) return true;
    }
    for (st.predicates.items) |predicate| {
        if (nodeHasIdentifier(o.tree, predicate.node, root)) return true;
    }
    return false;
}

fn nodeHasIdentifier(tree: *const Ast, node: Ast.Node.Index, name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    var token = tree.firstToken(node);
    const last = tree.lastToken(node);
    while (token <= last) : (token += 1) {
        if (tags[token] == .identifier and std.mem.eql(u8, tree.tokenSlice(token), name)) return true;
    }
    return false;
}

fn sameExpression(tree: *const Ast, left: Ast.Node.Index, right: Ast.Node.Index) bool {
    const tags = tree.tokens.items(.tag);
    var lt = tree.firstToken(left);
    var rt = tree.firstToken(right);
    const ll = tree.lastToken(left);
    const rl = tree.lastToken(right);
    while (lt <= ll and rt <= rl) {
        if (tags[lt] != tags[rt] or !std.mem.eql(u8, tree.tokenSlice(lt), tree.tokenSlice(rt))) return false;
        lt += 1;
        rt += 1;
    }
    return lt > ll and rt > rl;
}

fn productFactorMatches(
    st: *const State,
    factor: ProductFactor,
    target: []const u8,
) bool {
    if (factor.is_container) return std.mem.eql(u8, factor.key, target);
    for (st.aliases.items) |alias| {
        if (std.mem.eql(u8, alias.scalar, factor.key) and
            std.mem.eql(u8, alias.container, target))
        {
            return true;
        }
    }
    return false;
}

/// Is container `path` provably non-empty in `st`?
///
/// Free-standing, because the answer depends on nothing the oracle carries
/// beyond the tree: asking it of a copy of the oracle would copy an owner,
/// and an `Oracle` owns the key sets it collected and has exactly one
/// `deinit`.  One implementation also keeps the two callers — the
/// `provesNonempty` query and the "is this index's own container non-empty"
/// question inside `provesPositive` — from drifting apart.
fn containerProvenNonEmpty(tree: *const Ast, st: *const State, path: []const u8) bool {
    if (st.containers.contains(path)) return true;
    for (st.product_aliases.items) |pa| {
        if (!productConditionActive(tree, st, pa)) continue;
        if (!st.scalars.contains(pa.result)) continue;
        if (productFactorMatches(st, pa.left, path) or
            productFactorMatches(st, pa.right, path))
        {
            return true;
        }
    }
    return false;
}

/// Is the predicate a conditional product alias was selected by still
/// established here?  An alias with no condition is unconditional.
fn productConditionActive(tree: *const Ast, st: *const State, pa: ProductAlias) bool {
    const condition = pa.condition orelse return true;
    for (st.predicates.items) |predicate| {
        if (predicate.truth != pa.condition_true) continue;
        if (sameExpression(tree, condition, predicate.node)) return true;
    }
    return false;
}

fn rangeUpperName(tree: *const Ast, input: Ast.Node.Index) ?[]const u8 {
    if (tree.nodeTag(input) != .for_range) return null;
    const data = tree.nodeData(input).node_and_opt_node;
    if (!isIntLiteralValue(tree, data[0], 0)) return null;
    const end = data[1].unwrap() orelse return null;
    return identName(tree, end);
}

fn iterablePath(o: *Oracle, input: Ast.Node.Index) ?[]const u8 {
    const tree = o.tree;
    if (tree.nodeTag(input) == .for_range) return null;
    if (!isPureFieldPath(tree, input)) return null;
    return nodeSrc(tree, input);
}

// ── small AST predicates ────────────────────────────────────

pub fn identName(tree: *const Ast, node: Ast.Node.Index) ?[]const u8 {
    if (tree.nodeTag(node) != .identifier) return null;
    return tree.tokenSlice(tree.nodeMainToken(node));
}

/// For a slice expression `base[0..N]` (start literal 0, end an identifier),
/// return N's name — the slice's length equals N.  Null for non-slices,
/// non-zero starts, open-ended slices, or non-identifier ends.
fn sliceLenScalarName(o: *Oracle, node: Ast.Node.Index) ?[]const u8 {
    const tree = o.tree;
    const sl = tree.fullSlice(node) orelse return null;
    if (!isIntLiteralValue(tree, sl.ast.start, 0)) return null;
    const end = sl.ast.end.unwrap() orelse return null;
    return identName(tree, end);
}

/// Does a retained predicate prove `start < base.len`?  The four spellings
/// of the strict order (`start < base.len`, `base.len > start`, and the
/// negations of `start >= base.len` / `base.len <= start`) are read against
/// the same operands `differenceOrdered` compares, except that the high side
/// is the length of `base` written as a field access.
fn startBelowLength(o: *Oracle, st: *const State, base: Ast.Node.Index, start: Ast.Node.Index) bool {
    const tree = o.tree;
    const sliced = unwrapGrouped(tree, base);
    const offset = unwrapGrouped(tree, start);
    for (st.predicates.items) |predicate| {
        if (!o.spend()) return false;
        const tag = tree.nodeTag(predicate.node);
        const forward = (tag == .less_than and predicate.truth) or
            (tag == .greater_or_equal and !predicate.truth);
        const reverse = (tag == .greater_than and predicate.truth) or
            (tag == .less_or_equal and !predicate.truth);
        if (!forward and !reverse) continue;
        const operands = tree.nodeData(predicate.node).node_and_node;
        const low = unwrapGrouped(tree, if (forward) operands[0] else operands[1]);
        const high = unwrapGrouped(tree, if (forward) operands[1] else operands[0]);
        if (tree.nodeTag(high) != .field_access) continue;
        const access = tree.nodeData(high).node_and_token;
        if (!std.mem.eql(u8, tree.tokenSlice(access[1]), "len")) continue;
        if (sameExpression(tree, unwrapGrouped(tree, access[0]), sliced) and sameExpression(tree, low, offset)) return true;
    }
    return false;
}

fn isAssignOp(tag: std.zig.Token.Tag) bool {
    return switch (tag) {
        .equal,
        .plus_equal,
        .minus_equal,
        .asterisk_equal,
        .slash_equal,
        .percent_equal,
        .plus_percent_equal,
        .minus_percent_equal,
        => true,
        else => false,
    };
}

fn isPositiveIntLiteral(tree: *const Ast, node: Ast.Node.Index) bool {
    if (tree.nodeTag(node) != .number_literal) return false;
    const v = std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(node)), 0) catch return false;
    return v > 0;
}

fn isIntLiteralValue(tree: *const Ast, node: Ast.Node.Index, want: u64) bool {
    if (tree.nodeTag(node) != .number_literal) return false;
    const v = std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(node)), 0) catch return false;
    return v == want;
}

/// Returns the unsigned value of a number-literal node, or null if not a literal.
fn intLiteralVal(tree: *const Ast, node: Ast.Node.Index) ?u64 {
    if (tree.nodeTag(node) != .number_literal) return null;
    return std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(node)), 0) catch null;
}

/// Source substring spanning a node (for canonical container-path keys).
pub fn nodeSrc(tree: *const Ast, node: Ast.Node.Index) []const u8 {
    const starts = tree.tokens.items(.start);
    const ft = tree.firstToken(node);
    const lt = tree.lastToken(node);
    const start: usize = starts[ft];
    const end: usize = starts[lt] + tree.tokenSlice(lt).len;
    return tree.source[start..end];
}

pub fn unwrapGrouped(tree: *const Ast, node: Ast.Node.Index) Ast.Node.Index {
    var n = node;
    while (tree.nodeTag(n) == .grouped_expression) n = tree.nodeData(n).node_and_token[0];
    return n;
}

/// True iff `node` is a pure field-access chain rooted at an identifier
/// (`self.bit_length`, `a.b.c`) — no calls, no subscripts.
pub fn isPureFieldPath(tree: *const Ast, node: Ast.Node.Index) bool {
    return switch (tree.nodeTag(node)) {
        .identifier => true,
        .field_access => isPureFieldPath(tree, tree.nodeData(node).node_and_token[0]),
        else => false,
    };
}

/// Source spelling of a pure field-access path with at least one `.`, else null.
fn fieldPathSrc(o: *Oracle, node: Ast.Node.Index) ?[]const u8 {
    const tree = o.tree;
    if (tree.nodeTag(node) != .field_access) return null;
    if (!isPureFieldPath(tree, node)) return null;
    return nodeSrc(tree, node);
}

/// Is the call argument `arg` provably non-zero in `st`?  A simple identifier is
/// looked up in the nonzero set; a field-path is matched against a value-alias
/// (`const local = path`) whose local is non-zero.
fn argProvablyNonzero(o: *Oracle, st: *const State, arg: Ast.Node.Index) bool {
    const tree = o.tree;
    if (identName(tree, arg)) |nm| return st.scalars.contains(nm);
    if (fieldPathSrc(o, arg)) |psrc| {
        if (st.scalars.contains(psrc)) return true;
        for (st.value_aliases.items) |va|
            if (va.other_path == null and va.offset == 0 and std.mem.eql(u8, va.path, psrc) and st.scalars.contains(va.local)) return true;
    }
    return false;
}

/// Cross-fn: is `init` a call whose result is provably non-zero?
///
/// Two independent things answer it, and they are different claims.  The first
/// is a contract about one ARGUMENT: an in-file single-return function whose
/// return is non-zero given its first parameter non-zero (e.g. ceil-division),
/// AND `arg` proven non-zero at the call.  That one is single-argument, and
/// staying that way is deliberate.
///
/// The second is a sum over the callee's own EXITS and needs no argument at
/// all: a callee whose every return the source already proves is at least one
/// hands back at least one however it was called — with no arguments, with
/// several, and whether it is a root function or a container method.  It is
/// asked FIRST because it is the stronger statement, and it is asked from the
/// resolved declaration rather than from the callee's name.
fn callResultNonzero(o: *Oracle, init: Ast.Node.Index, st: *const State) bool {
    const tree = o.tree;
    var buf: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buf, init) orelse return false;
    if (calleeAlwaysReturnsPositive(o, call.ast.fn_expr)) return true;
    const callee = identName(tree, call.ast.fn_expr) orelse return false;
    if (call.ast.params.len != 1) return false;
    if (!argProvablyNonzero(o, st, call.ast.params[0])) return false;
    return calleeReturnsNonzeroGivenArg(o, callee);
}

/// Does a top-level `fn` in this file named `name` return a provably non-zero
/// value given its first parameter non-zero?
///
/// Only ROOT declarations are visited, and the FIRST declaration that carries
/// the name decides: a container method is a different function reached by a
/// different spelling, and a second top-level declaration of one name is not
/// something this file's source disambiguates.  Conservative — false if no
/// such declaration is found, if it has no single `return EXPR`, or if that
/// expression does not meet the postcondition.
fn calleeReturnsNonzeroGivenArg(o: *Oracle, name: []const u8) bool {
    const tree = o.tree;
    for (tree.rootDecls()) |fnode| {
        if (tree.nodeTag(fnode) != .fn_decl) continue;
        const fdata = tree.nodeData(fnode).node_and_node;
        var pbuf: [1]Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&pbuf, fdata[0]) orelse continue;
        const nt = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(nt), name)) continue;
        const ret = fn_summary.singleReturnExpr(tree, fdata[1]) orelse return false;
        var it = proto.iterate(tree);
        const parameter = it.next() orelse return false;
        const pname = if (parameter.name_token) |t| tree.tokenSlice(t) else return false;
        return exprNonzeroPostcond(o, ret, .{
            .name = pname,
            .nonnegative = parameterNonnegative(o, parameter.type_expr),
        }, 0);
    }
    return false;
}

/// Does every way this call can leave its callee hand back a value of at least
/// one?
///
/// This is a SUM over the callee's own exits, and it is read from the body:
/// every `return` (and every `break` that leaves the function itself) has to
/// name a value the source already proves is at least one, and control has to
/// reach the last statement of the body, which has to be one of those returns.
/// Nothing about the callee's NAME answers it — a function called `count`,
/// `size` or `len` proves nothing here — and nothing about a state it
/// maintains does either: a field it writes on one path is a value the other
/// exit never returns.
///
/// Two shapes this deliberately does not reach.  A callee whose LAST statement
/// is not a `return` may still return on every path, but proving that is a
/// control-flow question, and an unproved one costs this a proof rather than
/// taking a wrong one.  And an exit whose operand runs code is not a value at
/// all: a body that can hand back something a callee computed, or a `try` that
/// can fail, exports nothing here.
///
/// The declaration is resolved rather than spelled, so a container method is
/// reached the way it is written — `object.id.index()`, `Holder.count(kind)` —
/// and two containers declaring one name stay two functions.
fn calleeAlwaysReturnsPositive(o: *Oracle, fn_expr: Ast.Node.Index) bool {
    const cache = o.cache orelse return false;
    const resolver = cache.zls orelse return false;
    const tree = o.tree;
    const reference = switch (resolver.functionReference(fn_expr) catch return false) {
        .function => |reference| reference,
        .unknown, .not_callable => return false,
    };
    if (reference.tree != tree) return false;
    const declaration = tokens.enclosingFnDecl(tree, reference.fn_token) orelse return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
    if (proto.ast.fn_token != reference.fn_token) return false;
    // A plain integer return type and a resolvable declaration are also what
    // make this a claim about a VALUE: an error union can leave the call
    // without one at all, and the type engine declines to call that an
    // integer, so nothing here has to reason about it.
    const return_type = proto.ast.return_type.unwrap() orelse return false;
    if (cache.intInfoOf(return_type) == null) return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    if (body == o.body or bodyDefers(tree, body)) return false;
    var statements: [2]Ast.Node.Index = undefined;
    const body_statements = blockStmts(tree, body, &statements);
    if (body_statements.len == 0) return false;
    if (tree.nodeTag(body_statements[body_statements.len - 1]) != .@"return") return false;
    const function_name = proto.name_token orelse return false;

    const allowance = contractAllowance(o) orelse return false;
    var scanner: Oracle = .{
        .gpa = o.gpa,
        .tree = tree,
        .body = body,
        .query = .numeric_range,
        .target = "",
        .use_token = 0,
        .budget = allowance,
        .budget_cap = o.budget_cap,
        .memo = o.memo,
    };
    defer scanner.deinit();
    defer inheritStop(o, &scanner);
    defer o.budget -= chargeContractSteps(allowance, &scanner);
    var exits: State = .{};
    defer exits.deinit(o.gpa);

    // ONE pass over the body's own subtree.  The callee's nodes are not this
    // walk's, and re-reading the file's whole node array per call site is the
    // cost this module exists not to pay.
    var exits_seen: usize = 0;
    var complete = true;
    var children = @import("type_engine").AstIterator.init(tree, body);
    while (children.next(tree)) |child| {
        const data = tree.nodeData(child);
        const tag = tree.nodeTag(child);
        if (tag != .@"return" and tag != .@"break") continue;
        // A labeled `break` leaves the function only when the label is the
        // function's own name; an unlabeled one leaves the innermost loop, and
        // a label that names anything else leaves a block inside this body.
        if (tag == .@"break") {
            const label = data.opt_token_and_opt_node[0].unwrap() orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(label), tree.tokenSlice(function_name))) continue;
        }
        // `return;` carries no value, so it is not an exit this sum describes.
        // A `.@"return"` node stores its value in `.opt_node`; only a
        // `.@"break"` uses `.opt_token_and_opt_node`. Reading one tag's
        // payload through the other's is a union-field panic.
        const value = switch (tag) {
            .@"return" => data.opt_node.unwrap(),
            else => data.opt_token_and_opt_node[1].unwrap(),
        } orelse continue;
        if (!pureIntegerExpression(&scanner, value, 0)) {
            complete = false;
            break;
        }
        const minimum = exprMin(&scanner, &exits, value) orelse {
            complete = false;
            break;
        };
        if (minimum < 1) {
            complete = false;
            break;
        }
        exits_seen += 1;
    }
    if (!complete or exits_seen == 0) return false;
    // A body that stops short has established the exits it reached and nothing
    // about the rest, and its steps are the walk's own cost to answer again.
    return !scanner.stoppedShort();
}

const NonzeroParameter = struct {
    name: []const u8,
    nonnegative: bool,
};

fn parameterNonnegative(o: *Oracle, type_node: ?Ast.Node.Index) bool {
    const node = type_node orelse return false;
    if (o.cache) |cache| {
        if (cache.intInfoOf(node)) |info| return !info.signed;
    }
    const name = identName(o.tree, node) orelse return false;
    if (std.mem.eql(u8, name, "usize")) return true;
    if (name.len < 2 or name[0] != 'u') return false;
    const bits = std.fmt.parseUnsigned(u16, name[1..], 10) catch return false;
    return bits != 0;
}

fn postconditionNonnegative(o: *Oracle, node: Ast.Node.Index, parameter: NonzeroParameter) bool {
    const n = unwrapGrouped(o.tree, node);
    if (identName(o.tree, n)) |name| {
        if (std.mem.eql(u8, name, parameter.name)) return parameter.nonnegative;
    }
    return operandProvablyNonneg(o, n);
}

/// Nonzero after normal completion of checked arithmetic. This does not prove
/// that the source arithmetic itself cannot overflow.
fn exprNonzeroPostcond(o: *Oracle, expr: Ast.Node.Index, parameter: NonzeroParameter, depth: u8) bool {
    if (depth == walk_depth_cap) {
        o.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
        return false;
    }
    if (!o.spend()) return false;
    const tree = o.tree;
    const e = unwrapGrouped(tree, expr);
    switch (tree.nodeTag(e)) {
        .number_literal => return isPositiveIntLiteral(tree, e),
        .identifier => return std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(e)), parameter.name),
        .add, .add_sat => {
            const d = tree.nodeData(e).node_and_node;
            if (!postconditionNonnegative(o, d[0], parameter) or
                !postconditionNonnegative(o, d[1], parameter)) return false;
            return exprNonzeroPostcond(o, d[0], parameter, depth + 1) or
                exprNonzeroPostcond(o, d[1], parameter, depth + 1);
        },
        .div => {
            const d = tree.nodeData(e).node_and_node;
            const div_node = d[1];
            const num = unwrapGrouped(tree, d[0]);
            if (tree.nodeTag(num) != .add) return false;
            const ad = tree.nodeData(num).node_and_node;
            return ceilDivBase(o, ad[0], ad[1], div_node, parameter, depth + 1) or
                ceilDivBase(o, ad[1], ad[0], div_node, parameter, depth + 1);
        },
        else => return false,
    }
}

/// Positive base and nonnegative offset, with a known positive divisor.
fn ceilDivBase(
    o: *Oracle,
    base: Ast.Node.Index,
    addend: Ast.Node.Index,
    div_node: Ast.Node.Index,
    parameter: NonzeroParameter,
    depth: u8,
) bool {
    if (!postconditionNonnegative(o, base, parameter) or
        !exprNonzeroPostcond(o, base, parameter, depth)) return false;
    const divisor = comptimeValOf(o, div_node) orelse return false;
    if (divisor == 0) return false;
    if (comptimeValOf(o, addend)) |offset| return offset >= divisor - 1;
    return addendIsDivisorMinusOne(o, addend, divisor);
}

fn addendIsDivisorMinusOne(o: *Oracle, addend: Ast.Node.Index, divisor: u64) bool {
    const tree = o.tree;
    const a = unwrapGrouped(tree, addend);
    if (tree.nodeTag(a) != .sub) return false;
    const operands = tree.nodeData(a).node_and_node;
    if (!isIntLiteralValue(tree, operands[1], 1)) return false;
    return (comptimeValOf(o, operands[0]) orelse return false) == divisor;
}

/// Literal or resolved compile-time integer value.
///
/// The type engine resolves a compile-time integer only where the
/// expression itself is one; a plain `const width = 16;` sitting next to the
/// code that uses it is the commoner spelling and is not.  Following it is
/// what lets an audit bound be written as the name the source gives it.
fn comptimeValOf(o: *Oracle, node: Ast.Node.Index) ?u64 {
    return comptimeValAt(o, node, 0);
}

fn comptimeValAt(o: *Oracle, node: Ast.Node.Index, depth: u8) ?u64 {
    const bare = unwrapGrouped(o.tree, node);
    if (intLiteralVal(o.tree, bare)) |value| return value;
    if (o.cache) |cache| {
        if (cache.comptimeIntValueOf(bare)) |value| return value;
    }
    if (depth >= 8 or o.tree.nodeTag(bare) != .identifier) return null;
    return constInitializerInt(o, o.tree.tokenSlice(o.tree.nodeMainToken(bare)), depth + 1);
}

/// The integer a `const` binding is initialised to.
///
/// The declarations are read from the file cache's one per-file index rather
/// than by walking this file's whole node array per question.  Two names are
/// answered by nothing: one this walk binds, which is a different value whose
/// facts the walk already holds, and one the file declares twice, where
/// neither binding can be shown to be the one a use names.  A chained
/// constant — a `const` whose initializer is another bare name — is refused
/// too: which of the two a use means depends on the scope it was read in.
fn constInitializerInt(o: *Oracle, name: []const u8, depth: u8) ?u64 {
    if (walkBindsName(o, name)) return null;
    const cache = o.cache orelse return null;
    const initializer = cache.fileConstInitializer(name) catch {
        // Out of memory is not the absence of a declaration: reading it as one
        // would turn a failed allocation into a claim about the site.
        o.out_of_memory = true;
        return null;
    } orelse return null;
    if (o.tree.nodeTag(unwrapGrouped(o.tree, initializer)) == .identifier) return null;
    return comptimeValAt(o, initializer, depth);
}

fn blockStmts(
    tree: *const Ast,
    block_node: Ast.Node.Index,
    buf: *[2]Ast.Node.Index,
) []const Ast.Node.Index {
    return switch (tree.nodeTag(block_node)) {
        .block, .block_semicolon => tree.extraDataSlice(tree.nodeData(block_node).extra_range, Ast.Node.Index),
        .block_two, .block_two_semicolon => blk: {
            const data = tree.nodeData(block_node);
            buf[0] = data.opt_node_and_opt_node[0].unwrap() orelse break :blk &.{};
            if (data.opt_node_and_opt_node[1].unwrap()) |second| {
                buf[1] = second;
                break :blk buf[0..2];
            }
            break :blk buf[0..1];
        },
        else => &.{},
    };
}

test "latched census failure is returned before numeric results" {
    var tree = try Ast.parse(std.testing.allocator, "", .zig);
    defer tree.deinit(std.testing.allocator);
    var oracle: Oracle = .{
        .gpa = std.testing.allocator,
        .tree = &tree,
        .body = .root,
        .query = .numeric_range,
        .target = "",
        .use_token = 0,
        .summary_error = error.UnsupportedScheme,
    };
    defer oracle.deinit();
    var state: State = .{};
    defer state.deinit(std.testing.allocator);
    try std.testing.expectError(error.UnsupportedScheme, analyzeBody(&oracle));
    try std.testing.expectError(error.UnsupportedScheme, analyzeNode(&oracle, .root, &state));
    try std.testing.expectError(error.UnsupportedScheme, applyRefine(
        &oracle,
        &state,
        .{ .node = .root, .truth = true },
    ));
}

fn emptyOracle(tree: *const Ast) Oracle {
    return .{
        .gpa = std.testing.allocator,
        .tree = tree,
        .body = .root,
        .query = .numeric_range,
        .target = "",
        .use_token = 0,
    };
}

test "contract allowance: a caller out of steps records the bound instead of skipping the helper silently" {
    var tree = try Ast.parse(std.testing.allocator, "", .zig);
    defer tree.deinit(std.testing.allocator);
    var oracle = emptyOracle(&tree);
    defer oracle.deinit();
    oracle.budget = 0;
    try std.testing.expectEqual(@as(?u32, null), contractAllowance(&oracle));
    const stop = oracle.stopped orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_steps, stop.limit);
    try std.testing.expect(oracle.stoppedShort());

    oracle.stopped = null;
    oracle.budget = 10;
    try std.testing.expectEqual(@as(?u32, 10), contractAllowance(&oracle));
    oracle.budget = step_budget;
    try std.testing.expectEqual(@as(?u32, max_contract_steps), contractAllowance(&oracle));
    try std.testing.expect(!oracle.stoppedShort());
}

test "inherit stop: a helper's bound reaches the asking walk and the first stop wins" {
    var tree = try Ast.parse(std.testing.allocator, "", .zig);
    defer tree.deinit(std.testing.allocator);
    var parent = emptyOracle(&tree);
    defer parent.deinit();
    var helper = emptyOracle(&tree);
    defer helper.deinit();

    inheritStop(&parent, &helper);
    try std.testing.expect(!parent.stoppedShort());

    helper.giveUp(.{ .limit = .numeric_oracle_depth, .cap = walk_depth_cap });
    parent.budget = 7;
    inheritStop(&parent, &helper);
    const stop = parent.stopped orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_depth, stop.limit);
    // The caller settles the helper's cost itself; this must not touch it.
    try std.testing.expectEqual(@as(u32, 7), parent.budget);

    var later = emptyOracle(&tree);
    defer later.deinit();
    later.giveUp(.{ .limit = .numeric_oracle_steps, .cap = step_budget });
    inheritStop(&parent, &later);
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_depth, parent.stopped.?.limit);
}

test "depth cutoffs record the bound instead of answering conservatively in silence" {
    var tree = try Ast.parse(std.testing.allocator, "", .zig);
    defer tree.deinit(std.testing.allocator);
    var state: State = .{};
    defer state.deinit(std.testing.allocator);

    var bits = emptyOracle(&tree);
    defer bits.deinit();
    try std.testing.expect(bitAliasOf(&bits, &state, .root, bit_alias_depth_cap) == null);
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_depth, bits.stopped.?.limit);
    try std.testing.expectEqual(@as(u32, bit_alias_depth_cap), bits.stopped.?.cap);

    var width = emptyOracle(&tree);
    defer width.deinit();
    try std.testing.expect(computedFloatBitsAtDepth(&width, .root, float_width_depth_cap, .minimum) == null);
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_depth, width.stopped.?.limit);
    try std.testing.expectEqual(@as(u32, float_width_depth_cap), width.stopped.?.cap);

    var writes = emptyOracle(&tree);
    defer writes.deinit();
    try std.testing.expect(writesDirectly(&writes, .root, walk_depth_cap));
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_depth, writes.stopped.?.limit);

    // Inside every bound nothing is recorded.
    var quiet = emptyOracle(&tree);
    defer quiet.deinit();
    _ = bitAliasOf(&quiet, &state, .root, 0);
    _ = computedFloatBitsAtDepth(&quiet, .root, 0, .minimum);
    try std.testing.expect(!quiet.stoppedShort());
}

test "a predicate helper that runs out of steps fails the query instead of dropping its contract" {
    const gpa = std.testing.allocator;
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/intfromfloat_without_clamp.zig");
    // `valid` is a pure predicate, and the call guard below is what proves the
    // conversion in range.  Its body is longer than one contract may walk, so
    // the contract cannot be read; the query must say so rather than report an
    // unproven conversion from the contract it never finished reading.
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    try source.appendSlice(gpa,
        \\fn valid(comptime T: type, value: T) bool {
        \\    const wide: f64 = @floatCast(value);
        \\
    );
    var line: [64]u8 = undefined;
    for (0..600) |index| {
        try source.appendSlice(gpa, try std.fmt.bufPrint(&line, "    const pad{d} = wide + 1;\n", .{index}));
    }
    try source.appendSlice(gpa,
        \\    if (wide != wide) return false;
        \\    return wide >= -0x1p63 and wide < 0x1p63;
        \\}
        \\fn convert(comptime T: type, value: T) i64 {
        \\    if (!valid(T, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(value: f32) i64 { return convert(f32, value); }
        \\
    );
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, testing.runRuleTyped(gpa, rule.check, source.items));
    const diagnostic = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_steps, diagnostic.limit);
}

test "aggregate return memo compares complete fact names and ranges" {
    const Fact = numeric_eval.Fact;
    const original = [_]Fact{
        .{ .name = "input.len", .value = NumericRange.constant(12) },
        .{ .name = "count", .value = NumericRange.constant(4) },
    };
    const identical = [_]Fact{
        .{ .name = "input.len", .value = NumericRange.constant(12) },
        .{ .name = "count", .value = NumericRange.constant(4) },
    };
    const widened = [_]Fact{
        .{ .name = "input.len", .value = NumericRange.constant(1200) },
        .{ .name = "count", .value = NumericRange.constant(4) },
    };
    const renamed = [_]Fact{
        .{ .name = "other.len", .value = NumericRange.constant(12) },
        .{ .name = "count", .value = NumericRange.constant(4) },
    };
    try std.testing.expect(PredicateMemo.AggregateReturn.factsEqual(&original, &identical));
    try std.testing.expect(!PredicateMemo.AggregateReturn.factsEqual(&original, &widened));
    try std.testing.expect(!PredicateMemo.AggregateReturn.factsEqual(&original, &renamed));
    try std.testing.expect(!PredicateMemo.AggregateReturn.factsEqual(&original, original[0..1]));
}

test "Ocean universal nonempty controls require a current element proof" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/index_minus_one_without_zero_guard.zig");
    try testing.expectNoFireTyped(rule.check,
        \\const Block = struct { instructions: []const u8 };
        \\pub fn validate(blocks: []const Block) !u8 {
        \\    for (blocks) |block| {
        \\        if (block.instructions.len == 0) return error.Empty;
        \\    }
        \\    var result: u8 = 0;
        \\    for (blocks) |block| {
        \\        if (block.instructions.len == 0) return error.Empty;
        \\        result ^= block.instructions[block.instructions.len - 1];
        \\    }
        \\    return result;
        \\}
    );
    try testing.expectFiresTyped(rule.check, "index-minus-one-without-zero-guard",
        \\const Block = struct { instructions: []const u8 };
        \\pub fn validate(blocks: []const Block) !u8 {
        \\    for (blocks) |block| {
        \\        if (block.instructions.len == 0) return error.Empty;
        \\        break;
        \\    }
        \\    var result: u8 = 0;
        \\    for (blocks) |block| {
        \\        result ^= block.instructions[block.instructions.len - 1];
        \\    }
        \\    return result;
        \\}
    );
}

test "Ocean universal nonempty controls reject overwritten instruction headers" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/index_minus_one_without_zero_guard.zig");
    try testing.expectFiresTyped(rule.check, "index-minus-one-without-zero-guard",
        \\const Block = struct { instructions: []const u8 };
        \\pub fn validate(blocks: []Block) !u8 {
        \\    for (blocks) |block| {
        \\        if (block.instructions.len == 0) return error.Empty;
        \\    }
        \\    if (blocks.len == 0) return 0;
        \\    blocks[0].instructions = &.{};
        \\    return blocks[0].instructions[blocks[0].instructions.len - 1];
        \\}
    );
}

test "Ocean optional loop witness controls require a container proof" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/index_minus_one_without_zero_guard.zig");
    try testing.expectNoFireTyped(rule.check,
        \\pub fn moveLast(items: []u8) void {
        \\    var last: ?usize = null;
        \\    for (items, 0..) |item, index| {
        \\        if (item == 1) last = index;
        \\    }
        \\    if (last) |index| {
        \\        if (items.len == 0) return;
        \\        const tmp = items[index];
        \\        items[index] = items[items.len - 1];
        \\        items[items.len - 1] = tmp;
        \\    }
        \\}
    );
    try testing.expectFiresTyped(rule.check, "index-minus-one-without-zero-guard",
        \\pub fn moveLast(items: []u8, seed: ?usize) void {
        \\    var last = seed;
        \\    for (items, 0..) |item, index| {
        \\        if (item == 1) last = index;
        \\    }
        \\    if (last) |index| {
        \\        items[index] = items[items.len - 1];
        \\    }
        \\}
    );
}

test "Ocean optional loop witness controls reject a later slice rebind" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/index_minus_one_without_zero_guard.zig");
    try testing.expectFiresTyped(rule.check, "index-minus-one-without-zero-guard",
        \\pub fn moveLast(input: []u8) void {
        \\    var items = input;
        \\    var last: ?usize = null;
        \\    for (items, 0..) |item, index| {
        \\        if (item == 1) last = index;
        \\    }
        \\    items = items[0..0];
        \\    if (last) |index| {
        \\        items[index] = items[items.len - 1];
        \\    }
        \\}
    );
}

test "Ocean seeded positive counter survives disjoint producer effects" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/index_minus_one_without_zero_guard.zig");
    try testing.expectNoFireTyped(rule.check,
        \\const Producer = struct {
        \\    fn create(_: *Producer, state: *u64, inputs: []const u8) !u8 {
        \\        state.* +%= 1;
        \\        return if (inputs.len == 0) @truncate(state.*) else inputs[0];
        \\    }
        \\};
        \\fn next(state: *u64) u64 { state.* +%= 1; return state.*; }
        \\pub fn last(state: *u64) !u8 {
        \\    var producer: Producer = .{};
        \\    var values: [32]u8 = @splat(0);
        \\    var count: usize = 0;
        \\    values[count] = try producer.create(state, &.{});
        \\    count += 1;
        \\    const operation_count: usize = @intCast(next(state) % 20);
        \\    for (0..operation_count) |_| {
        \\        if (count >= values.len) break;
        \\        const lhs = values[@as(usize, @intCast(next(state) % count))];
        \\        const value = try producer.create(state, &.{lhs});
        \\        values[count] = value;
        \\        count += 1;
        \\    }
        \\    const shape = next(state) % 4;
        \\    _ = shape;
        \\    return values[count - 1];
        \\}
    );
}

test "Ocean seeded positive counter controls reject zero reaching loop updates" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/index_minus_one_without_zero_guard.zig");
    try testing.expectFiresTyped(rule.check, "index-minus-one-without-zero-guard",
        \\pub fn last(values: []const u8, iterations: usize) u8 {
        \\    var count: usize = 1;
        \\    for (0..iterations) |_| {
        \\        count = 0;
        \\    }
        \\    return values[count - 1];
        \\}
    );
    try testing.expectFiresTyped(rule.check, "index-minus-one-without-zero-guard",
        \\pub fn last(values: []const u8, iterations: usize) u8 {
        \\    var count: usize = 1;
        \\    for (0..iterations) |_| {
        \\        count -= 1;
        \\    }
        \\    return values[count - 1];
        \\}
    );
    try testing.expectFiresTyped(rule.check, "index-minus-one-without-zero-guard",
        \\fn reset(count: *usize) void { count.* = 0; }
        \\pub fn last(values: []const u8, iterations: usize) u8 {
        \\    var count: usize = 1;
        \\    for (0..iterations) |_| {
        \\        reset(&count);
        \\    }
        \\    return values[count - 1];
        \\}
    );
}

test {
    _ = numbers;
    _ = @import("value_range_tests.zig");
}

test "numeric return memo: one nested call node keeps distinct actual callable contexts" {
    const gpa = std.testing.allocator;
    const resolver_mod = @import("../type_resolver.zig");
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-numeric-return-context.zig",
        \\fn target(value: anytype) i32 { return @intCast(value); }
        \\fn forward(comptime T: type, value: T) i32 { return target(value); }
        \\pub fn use() i32 { return forward(u8, 0) + forward(u32, 0); }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const Find = struct {
        fn call(tree_: *const Ast, name: []const u8, occurrence: usize) !Ast.Node.Index {
            var seen: usize = 0;
            for (0..tree_.nodes.len) |index| {
                const node: Ast.Node.Index = @enumFromInt(index);
                var buffer: [1]Ast.Node.Index = undefined;
                const full = tree_.fullCall(&buffer, node) orelse continue;
                if (!std.mem.eql(u8, tree_.getNodeSource(full.ast.fn_expr), name)) continue;
                if (seen == occurrence) return node;
                seen += 1;
            }
            return error.MissingCall;
        }
    };
    const narrow_call = try Find.call(tree, "forward", 0);
    const wide_call = try Find.call(tree, "forward", 1);
    const nested_call = try Find.call(tree, "target", 0);
    const narrow = switch (try resolver.functionReferenceOfCall(narrow_call)) {
        .function => |reference| reference,
        else => return error.MissingNarrowContext,
    };
    const wide = switch (try resolver.functionReferenceOfCall(wide_call)) {
        .function => |reference| reference,
        else => return error.MissingWideContext,
    };
    const narrow_frame = resolver.frameForFunction(narrow);
    const wide_frame = resolver.frameForFunction(wide);
    var buffer: [1]Ast.Node.Index = undefined;
    const nested = tree.fullCall(&buffer, nested_call).?;
    const token = tree.nodeMainToken(nested.ast.fn_expr);
    const narrow_actual = (try cache.actualCallSummaryAt(token, narrow_frame)) orelse return error.MissingNarrowCallee;
    const wide_actual = (try cache.actualCallSummaryAt(token, wide_frame)) orelse return error.MissingWideCallee;
    try std.testing.expect(narrow_actual.callee.reference.fn_token == wide_actual.callee.reference.fn_token);
    try std.testing.expect(!narrow_actual.callee.reference.actual_type.eql(wide_actual.callee.reference.actual_type));
    var memo: PredicateMemo = .{ .gpa = gpa };
    defer memo.deinit();
    const arguments = [_]numeric_eval.Fact{.{ .name = "value", .value = NumericRange.constant(0) }};
    try memo.recordNumericReturn(narrow_actual.callee.reference, narrow_frame, nested_call, 1, &arguments, NumericRange.constant(0));
    try std.testing.expect(memo.findNumericReturn(narrow_actual.callee.reference, narrow_frame, nested_call, 1, &arguments) != null);
    try std.testing.expect(memo.findNumericReturn(wide_actual.callee.reference, wide_frame, nested_call, 1, &arguments) == null);
}

test "caller length fallback propagates embed metadata failure and permits retry" {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    const resolver_mod = @import("../type_resolver.zig");
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const source =
        \\fn consume(bytes: []const u8, token: u8) usize { _ = token; return bytes.len; }
        \\extern fn effect() u8;
        \\pub fn caller() usize { return consume(@embedFile("late.bin"), effect()); }
    ;
    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data = source });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const path = try std.fs.path.join(gpa, &.{ root, "main.zig" });
    defer gpa.free(path);
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{root} };
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.file_path = path;
    var oracle = emptyOracle(tree);
    defer oracle.deinit();
    oracle.cache = &cache;
    var call_node: ?Ast.Node.Index = null;
    for (0..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (std.mem.eql(u8, tree.getNodeSource(call.ast.fn_expr), "consume")) {
            call_node = node;
            break;
        }
    }
    const node = call_node orelse return error.MissingCall;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node).?;
    try std.testing.expectError(error.FileNotFound, callerArgumentLength(&oracle, node, call.ast.params[0]));
    try std.testing.expectEqual(@as(usize, 0), cache.embedded_file_lengths.count());
    try tmp.dir.writeFile(io, .{ .sub_path = "late.bin", .data = "abc" });
    const extent = try callerArgumentLength(&oracle, node, call.ast.params[0]);
    try std.testing.expect(extent == .integer);
    try std.testing.expectEqual(@as(i128, 3), extent.integer.min);
    try std.testing.expectEqual(@as(i128, 3), extent.integer.max);
}

test "returned length export settles child cost before spending the final parent step" {
    const gpa = std.testing.allocator;
    const resolver_mod = @import("../type_resolver.zig");
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-returned-length-budget.zig",
        \\fn take() []const u8 { return "abc"; }
        \\pub fn caller() []const u8 { return take(); }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var call_node: ?Ast.Node.Index = null;
    for (0..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (std.mem.eql(u8, tree.getNodeSource(call.ast.fn_expr), "take")) {
            call_node = node;
            break;
        }
    }
    const node = call_node orelse return error.MissingCall;
    const reference = switch (try resolver.functionReferenceOfCall(node)) {
        .function => |function| function,
        else => return error.MissingCallee,
    };
    const declaration = tokens.enclosingFnDecl(tree, reference.fn_token) orelse return error.MissingCallee;
    const body = tokens.bodyOf(tree, declaration) orelse return error.MissingCallee;
    var source: State = .{};
    defer source.deinit(gpa);
    var output: State = .{};
    defer output.deinit(gpa);
    var generous = emptyOracle(tree);
    defer generous.deinit();
    generous.cache = &cache;
    const initial = generous.budget;
    try summarizeReturnedLengths(&generous, &source, reference, node, body, false, true, &.{}, &.{}, &output, "header");
    try std.testing.expect(!generous.stoppedShort());
    try std.testing.expect(output.lenBoundOf("header") != null);
    const spent = initial - generous.budget;
    try std.testing.expect(spent > 1);
    var tight = emptyOracle(tree);
    defer tight.deinit();
    tight.cache = &cache;
    tight.budget = spent - 1;
    tight.budget_cap = tight.budget;
    var refused: State = .{};
    defer refused.deinit(gpa);
    try summarizeReturnedLengths(&tight, &source, reference, node, body, false, true, &.{}, &.{}, &refused, "header");
    try std.testing.expectEqual(@as(u32, 0), tight.budget);
    try std.testing.expect(tight.stoppedShort());
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_steps, tight.stopped.?.limit);
    try std.testing.expect(refused.lenBoundOf("header") == null);
}

test "scalar contract settles analysis and clips later effect work to the caller budget" {
    const gpa = std.testing.allocator;
    const resolver_mod = @import("../type_resolver.zig");
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-scalar-contract-budget.zig",
        \\fn positive(value: usize) !void {
        \\    if (value == 0) return error.Zero;
        \\}
        \\pub fn caller(n: usize) !usize {
        \\    try positive(n);
        \\    return n - 1;
        \\}
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var call_node: ?Ast.Node.Index = null;
    for (0..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (std.mem.eql(u8, tree.getNodeSource(call.ast.fn_expr), "positive")) {
            call_node = node;
            break;
        }
    }
    const node = call_node orelse return error.MissingCall;
    const caller_decl = tokens.enclosingFnDecl(tree, tree.firstToken(node)) orelse return error.MissingCaller;
    const caller_body = tokens.bodyOf(tree, caller_decl) orelse return error.MissingCaller;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const caller_proto = tokens.fnProto(tree, &proto_buffer, caller_decl) orelse return error.MissingCaller;
    var bindings = try local_bindings.build(gpa, tree, caller_proto, caller_body);
    defer bindings.deinit();
    const reference = switch (try resolver.functionReferenceOfCall(node)) {
        .function => |function| function,
        else => return error.MissingCallee,
    };
    const callee_decl = tokens.enclosingFnDecl(tree, reference.fn_token) orelse return error.MissingCallee;
    const callee_body = tokens.bodyOf(tree, callee_decl) orelse return error.MissingCallee;
    var probe = emptyOracle(tree);
    defer probe.deinit();
    probe.cache = &cache;
    probe.body = caller_body;
    probe.locals = bindings.items;
    probe.successful_call = node;
    var capture: Capture = .{ .gpa = gpa, .mode = .exit, .success_only = true };
    defer capture.deinit();
    var child = emptyOracle(tree);
    defer child.deinit();
    child.cache = &cache;
    child.body = callee_body;
    child.expression = callee_body;
    child.use_token = std.math.maxInt(Ast.TokenIndex);
    child.capture = &capture;
    child.caller_parent = &probe;
    child.infer_callers = false;
    child.contract_depth = 1;
    child.budget = contractAllowance(&probe).?;
    const child_initial = child.budget;
    _ = try analyzeBody(&child);
    try std.testing.expect(capture.complete);
    try std.testing.expect(!child.stoppedShort());
    try std.testing.expect(capture.state.?.numericValue("value") == .integer);
    try std.testing.expect(capture.state.?.numericValue("value").integer.min >= 1);
    const analysis_cost = child_initial - child.budget;
    const parent_initial = probe.budget;
    try std.testing.expect(numeric_escape.scalarSurvivesCall(&probe, "n", .{ .subtree = node }));
    const filter_cost = parent_initial - probe.budget;
    try std.testing.expect(filter_cost > 0);

    var generous = emptyOracle(tree);
    defer generous.deinit();
    generous.cache = &cache;
    generous.body = caller_body;
    generous.locals = bindings.items;
    generous.successful_call = node;
    var accepted: State = .{};
    defer accepted.deinit(gpa);
    try applyCallContracts(&generous, &accepted, node, &.{});
    try std.testing.expect(!generous.stoppedShort());
    try std.testing.expect(accepted.numericValue("n") == .integer);
    try std.testing.expect(accepted.numericValue("n").integer.min >= 1);

    var tight = emptyOracle(tree);
    defer tight.deinit();
    tight.cache = &cache;
    tight.body = caller_body;
    tight.locals = bindings.items;
    tight.successful_call = node;
    // Analysis and the caller filter fit; the later child effect scan does not.
    tight.budget = 1 + analysis_cost + filter_cost;
    tight.budget_cap = tight.budget;
    var refused: State = .{};
    defer refused.deinit(gpa);
    try applyCallContracts(&tight, &refused, node, &.{});
    try std.testing.expectEqual(@as(u32, 0), tight.budget);
    try std.testing.expect(tight.stoppedShort());
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_steps, tight.stopped.?.limit);
    try std.testing.expect(refused.scalarMinOf("n") == null);
    try std.testing.expect(!refused.scalars.contains("n"));
    try std.testing.expectEqual(@as(usize, 0), refused.numeric.items.len);
}
