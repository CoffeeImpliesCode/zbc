//! Bounded forward range proofs within one function body.
//!
//! Tracks lower bounds, nonzero values, container lengths, aliases, and
//! branch predicates. Joins retain only facts that hold on every reaching
//! path. Writes and calls invalidate facts they can change. Unsupported
//! transfers and exhausted budgets return unknown, not a safety proof.

const std = @import("std");
const Ast = std.zig.Ast;
const tokens = @import("../ast/tokens.zig");
const file_cache_mod = @import("../cache/file_cache.zig");
const fn_summary = @import("../model/fn_summary.zig");
const local_bindings = @import("../model/local_bindings.zig");
const numbers = @import("numeric_range.zig");
const numeric_eval = @import("numeric_eval.zig");
pub const NumericRange = numbers.Range;

/// A set of string keys (source slices, stable for the tree's lifetime).
const KeySet = struct {
    keys: std.ArrayListUnmanaged([]const u8) = .empty,

    fn deinit(self: *KeySet, gpa: std.mem.Allocator) void {
        self.keys.deinit(gpa);
    }
    fn contains(self: *const KeySet, k: []const u8) bool {
        for (self.keys.items) |e| if (std.mem.eql(u8, e, k)) return true;
        return false;
    }
    fn add(self: *KeySet, gpa: std.mem.Allocator, k: []const u8) !void {
        if (self.contains(k)) return;
        try self.keys.append(gpa, k);
    }
    fn remove(self: *KeySet, k: []const u8) void {
        var i: usize = 0;
        while (i < self.keys.items.len) {
            if (std.mem.eql(u8, self.keys.items[i], k)) {
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

/// A `const LOCAL = <field-path>` binding (e.g. `const bit_length = self.bit_length`):
/// LOCAL and the path hold the same value.  Lets a guard on the simple local
/// (`if (bit_length == 0) return;`) establish that a later use of the path
/// (`numMasks(self.bit_length)`) sees a non-zero argument.  Dropped when LOCAL is
/// rebound or anything touches the path's root.
const ValueAlias = struct {
    local: []const u8,
    path: []const u8,
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

/// A factor of a checked or plain integer product.  Container factors are
/// canonical `<path>` keys (the `.len` access is removed); scalar factors keep
/// the local name so aliases can resolve them later.
const ProductFactor = struct {
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
const Predicate = struct {
    node: Ast.Node.Index,
    truth: bool,
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
const State = struct {
    scalars: KeySet = .{}, // locals known != 0
    containers: KeySet = .{}, // container paths known non-empty
    aliases: std.ArrayListUnmanaged(Alias) = .empty, // n == c.len
    diff_aliases: std.ArrayListUnmanaged(DiffAlias) = .empty, // n = A - B
    value_aliases: std.ArrayListUnmanaged(ValueAlias) = .empty, // local == path
    scalar_mins: std.ArrayListUnmanaged(ScalarMin) = .empty, // scalar >= n
    scalar_vals: std.ArrayListUnmanaged(ScalarVal) = .empty, // scalar == const K
    min_lens: std.ArrayListUnmanaged(MinLen) = .empty, // path.len >= n
    product_aliases: std.ArrayListUnmanaged(ProductAlias) = .empty,
    predicates: std.ArrayListUnmanaged(Predicate) = .empty,
    numeric: std.ArrayListUnmanaged(numeric_eval.Fact) = .empty,
    bit_aliases: std.ArrayListUnmanaged(BitAlias) = .empty,

    fn deinit(self: *State, gpa: std.mem.Allocator) void {
        self.scalars.deinit(gpa);
        self.containers.deinit(gpa);
        self.aliases.deinit(gpa);
        self.diff_aliases.deinit(gpa);
        self.value_aliases.deinit(gpa);
        self.scalar_mins.deinit(gpa);
        self.scalar_vals.deinit(gpa);
        self.min_lens.deinit(gpa);
        self.product_aliases.deinit(gpa);
        self.predicates.deinit(gpa);
        self.numeric.deinit(gpa);
        self.bit_aliases.deinit(gpa);
    }
    fn clone(self: *const State, gpa: std.mem.Allocator) !State {
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
        try out.product_aliases.appendSlice(gpa, self.product_aliases.items);
        try out.predicates.appendSlice(gpa, self.predicates.items);
        try out.numeric.appendSlice(gpa, self.numeric.items);
        try out.bit_aliases.appendSlice(gpa, self.bit_aliases.items);
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
    }
    fn replaceWith(self: *State, gpa: std.mem.Allocator, src: *const State) !void {
        self.scalars.keys.clearRetainingCapacity();
        self.containers.keys.clearRetainingCapacity();
        self.aliases.clearRetainingCapacity();
        self.diff_aliases.clearRetainingCapacity();
        self.value_aliases.clearRetainingCapacity();
        self.scalar_mins.clearRetainingCapacity();
        self.scalar_vals.clearRetainingCapacity();
        self.min_lens.clearRetainingCapacity();
        self.product_aliases.clearRetainingCapacity();
        self.predicates.clearRetainingCapacity();
        self.numeric.clearRetainingCapacity();
        self.bit_aliases.clearRetainingCapacity();
        try self.scalars.keys.appendSlice(gpa, src.scalars.keys.items);
        try self.containers.keys.appendSlice(gpa, src.containers.keys.items);
        try self.aliases.appendSlice(gpa, src.aliases.items);
        try self.diff_aliases.appendSlice(gpa, src.diff_aliases.items);
        try self.value_aliases.appendSlice(gpa, src.value_aliases.items);
        try self.scalar_mins.appendSlice(gpa, src.scalar_mins.items);
        try self.scalar_vals.appendSlice(gpa, src.scalar_vals.items);
        try self.min_lens.appendSlice(gpa, src.min_lens.items);
        try self.product_aliases.appendSlice(gpa, src.product_aliases.items);
        try self.predicates.appendSlice(gpa, src.predicates.items);
        try self.numeric.appendSlice(gpa, src.numeric.items);
        try self.bit_aliases.appendSlice(gpa, src.bit_aliases.items);
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
            if (std.mem.eql(u8, self.aliases.items[i].container, container)) _ = self.aliases.swapRemove(i) else i += 1;
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
        for (self.value_aliases.items) |e|
            if (std.mem.eql(u8, e.local, va.local) and std.mem.eql(u8, e.path, va.path)) return true;
        return false;
    }
    fn addValueAlias(self: *State, gpa: std.mem.Allocator, va: ValueAlias) !void {
        if (self.hasValueAlias(va)) return;
        try self.value_aliases.append(gpa, va);
    }
    /// Drop value_aliases whose local or whose path *starts with* `root` (so a
    /// rebind of the local, or a mutation of the path's root identifier,
    /// invalidates the equality).
    fn dropValueAliasesByRoot(self: *State, root: []const u8) void {
        var i: usize = 0;
        while (i < self.value_aliases.items.len) {
            const va = self.value_aliases.items[i];
            const path_root_match = std.mem.startsWith(u8, va.path, root) and
                (va.path.len == root.len or va.path[root.len] == '.' or va.path[root.len] == '[');
            if (std.mem.eql(u8, va.local, root) or path_root_match) {
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
    fn dropScalarValsByName(self: *State, name: []const u8) void {
        var i: usize = 0;
        while (i < self.scalar_vals.items.len) {
            if (std.mem.eql(u8, self.scalar_vals.items[i].name, name)) {
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
    fn dropScalarMinsByName(self: *State, name: []const u8) void {
        var i: usize = 0;
        while (i < self.scalar_mins.items.len) {
            if (std.mem.eql(u8, self.scalar_mins.items[i].name, name)) {
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

    fn numericValue(self: *const State, name: []const u8) NumericRange {
        for (self.numeric.items) |fact| if (std.mem.eql(u8, fact.name, name)) return fact.value;
        return .unknown;
    }

    fn setNumeric(self: *State, gpa: std.mem.Allocator, name: []const u8, value: NumericRange) !void {
        for (self.numeric.items) |*fact| {
            if (std.mem.eql(u8, fact.name, name)) {
                fact.value = value;
                return;
            }
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

    fn record(self: *PredicateCapture, o: *Oracle, expression: Ast.Node.Index, source: *const State) error{OutOfMemory}!void {
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

const Oracle = struct {
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
    budget: u32 = 50_000,
    addressed: KeySet = .{},
    walk_depth: u8 = 0,
    expression_depth: u8 = 0,
    numeric_answer: NumericRange = .unknown,
    std_valid: ?bool = null,
    caller_parent: ?*const Oracle = null,
    infer_callers: bool = true,
    predicate_capture: ?*PredicateCapture = null,
    locals: []const local_bindings.Binding = &.{},

    /// Non-null only while collecting exits of an outer `while (true)`.
    /// Nested loops temporarily disable this pointer so their breaks do not
    /// escape into the enclosing loop.
    break_capture: ?*BreakCapture = null,

    fn tokenInNode(self: *Oracle, node: Ast.Node.Index) bool {
        return self.use_token >= self.tree.firstToken(node) and
            self.use_token <= self.tree.lastToken(node);
    }
    fn spend(self: *Oracle) bool {
        if (self.budget == 0) return false;
        self.budget -= 1;
        return true;
    }
    fn answerAt(self: *Oracle, st: *const State) bool {
        return switch (self.query) {
            .numeric_range => {
                self.numeric_answer = numericValue(self, st, self.expression.?);
                if (self.upper_expression) |upper| return strictlyLessAt(self, st, upper);
                return true;
            },
            .positive_expression => expressionPositive(self, st, self.expression.?),
            .nonzero_scalar => st.scalars.contains(self.target) or
                (st.scalarMinOf(self.target) orelse 0) >= 1,
            .nonempty_container => {
                if (st.containers.contains(self.target)) return true;
                for (st.product_aliases.items) |pa| {
                    if (!self.productConditionActive(st, pa)) continue;
                    if (!st.scalars.contains(pa.result)) continue;
                    if (productFactorMatches(self.tree, st, pa.left, self.target) or
                        productFactorMatches(self.tree, st, pa.right, self.target))
                    {
                        return true;
                    }
                }
                return false;
            },
            // `target.len >= min_n`: proven via a slice-length alias (`target
            // = base[0..S]` ⟹ `target.len == S`) whose scalar has a known
            // value >= min_n (e.g. from a `switch (scalar)` arm).
            .min_len_container => {
                // (a) a `target.len >= N` guard refinement (N >= min_n).
                if (st.minLenOf(self.target)) |v| if (v >= self.min_n) return true;
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

    fn productConditionActive(self: *const Oracle, st: *const State, pa: ProductAlias) bool {
        const condition = pa.condition orelse return true;
        for (st.predicates.items) |predicate| {
            if (predicate.truth != pa.condition_true) continue;
            if (sameExpression(self.tree, condition, predicate.node)) return true;
        }
        return false;
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
) bool {
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
) bool {
    return run(gpa, tree, body_node, .nonempty_container, target, use_token, 0, cache, null);
}

/// Is container `target` provably of length >= `n` at `use_token`?  Proven via a
/// slice-length alias (`target = base[0..S]` ⟹ `target.len == S`) whose scalar
/// `S` has a known constant value >= n (e.g. from an enclosing `switch (S)` arm).
/// Covers the wyhash-style `switch (rem_len) { K => rem_key[N..] }` family.
pub fn provesMinLen(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body_node: Ast.Node.Index,
    target: []const u8,
    n: u64,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
) bool {
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
) bool {
    return run(gpa, tree, body, .positive_expression, "", use_token, 0, cache, expression);
}

/// Numeric bounds on every path reaching the expression. Unknown is not safe.
pub fn boundsAt(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    expression: Ast.Node.Index,
    use_token: Ast.TokenIndex,
    cache: ?*file_cache_mod.FileCache,
) error{OutOfMemory}!NumericRange {
    var oracle: Oracle = .{
        .gpa = gpa, .tree = tree, .body = body, .query = .numeric_range,
        .target = "", .use_token = use_token, .expression = expression, .cache = cache,
    };
    defer oracle.addressed.deinit(gpa);
    const flow = try analyzeBody(&oracle);
    if (flow.answer == null or oracle.budget == 0) return .unknown;
    return oracle.numeric_answer;
}

/// Is `lower < upper` true on every path reaching `use_token`?
pub fn provesLessThan(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    lower: Ast.Node.Index,
    upper: Ast.Node.Index,
    use_token: Ast.TokenIndex,
    cache: *file_cache_mod.FileCache,
) error{OutOfMemory}!bool {
    var oracle: Oracle = .{
        .gpa = gpa, .tree = tree, .body = body, .query = .numeric_range,
        .target = "", .use_token = use_token, .expression = lower,
        .upper_expression = upper, .cache = cache,
    };
    defer oracle.addressed.deinit(gpa);
    if (!pureIntegerExpression(&oracle, lower, 0) or
        !pureIntegerExpression(&oracle, upper, 0)) return false;
    const flow = try analyzeBody(&oracle);
    return oracle.budget != 0 and (flow.answer orelse false);
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

fn evaluator(o: *Oracle, st: *const State) numeric_eval.Evaluator {
    if (o.std_valid == null) o.std_valid = stdBindingValidAt(o, o.use_token);
    return .{
        .tree = o.tree, .cache = o.cache, .facts = st.numeric.items,
        .budget = &o.budget, .std_valid = o.std_valid.?,
    };
}

fn numericValue(o: *Oracle, st: *const State, node: Ast.Node.Index) NumericRange {
    var evaluation = evaluator(o, st);
    return evaluation.evaluate(node);
}

fn numericAssignment(o: *Oracle, st: *const State, source: Ast.Node.Index, destination: Ast.Node.Index) NumericRange {
    if (o.query != .numeric_range) return .unknown;
    var evaluation = evaluator(o, st);
    return evaluation.coerce(evaluation.evaluate(source), source, destination);
}

fn refineNumeric(o: *Oracle, st: *State, node: Ast.Node.Index, truth: bool) error{OutOfMemory}!void {
    var evaluation = evaluator(o, st);
    const constraints = numeric_eval.refine(&evaluation, node, truth);
    for (constraints) |constraint| {
        const value = constraint orelse continue;
        if (numeric_eval.path(o.tree, value.node)) |name| try st.setNumeric(o.gpa, name, value.value);
        const alias = bitAliasOf(o, st, value.node, 0) orelse continue;
        if (alias.union_view) continue;
        const bound = numbers.ieeeFloatRange(alias.float_bits, alias.mask, value.value, alias.absolute);
        if (bound != .unknown) try st.setNumeric(o.gpa, alias.source, st.numericValue(alias.source).intersect(bound));
    }
    try propagateNumericAliases(o, st);
}

fn propagateNumericAliases(o: *Oracle, st: *State) error{OutOfMemory}!void {
    for (0..32) |_| {
        var changed = false;
        for (st.value_aliases.items) |alias| {
            if (!o.spend()) return;
            const local = st.numericValue(alias.local);
            const source = st.numericValue(alias.path);
            const common = local.intersect(source);
            if (common == .unknown) continue;
            if (!std.meta.eql(local, common)) {
                try st.setNumeric(o.gpa, alias.local, common);
                changed = true;
            }
            if (!std.meta.eql(source, common)) {
                try st.setNumeric(o.gpa, alias.path, common);
                changed = true;
            }
        }
        if (!changed) return;
    }
    o.budget = 0;
}

fn pureCallInputs(o: *Oracle, call: Ast.full.Call) bool {
    if (!pureIntegerExpression(o, call.ast.fn_expr, 0)) return false;
    for (call.ast.params) |argument| if (!pureIntegerExpression(o, argument, 0)) return false;
    return true;
}

fn refinePredicateOutcome(o: *Oracle, st: *State, original: Predicate, depth: u8) error{OutOfMemory}!void {
    if (depth == 64 or !o.spend()) return;
    const node = unwrapGrouped(o.tree, original.node);
    switch (o.tree.nodeTag(node)) {
        .bool_not => try refinePredicateOutcome(o, st, .{
            .node = o.tree.nodeData(node).node, .truth = !original.truth,
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
        else => {},
    }
}

fn purePredicateBody(o: *Oracle, node: Ast.Node.Index, depth: u8) bool {
    if (depth == 64 or !o.spend()) return false;
    switch (o.tree.nodeTag(node)) {
        .block, .block_semicolon, .block_two, .block_two_semicolon,
        .@"if", .if_simple, .@"return" => {},
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

fn refinePredicateCall(o: *Oracle, st: *State, node: Ast.Node.Index, truth: bool) error{OutOfMemory}!void {
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = o.tree.fullCall(&call_buffer, node) orelse return;
    if (!pureCallInputs(o, call)) return;
    const resolver = (o.cache orelse return).zls orelse return;
    const reference = (resolver.functionReference(call.ast.fn_expr) catch return) orelse return;
    if (reference.tree != o.tree) return;
    const declaration = tokens.enclosingFnDecl(o.tree, reference.fn_token) orelse return;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(o.tree, &proto_buffer, declaration) orelse return;
    if (proto.ast.fn_token != reference.fn_token) return;
    const return_type = proto.ast.return_type.unwrap() orelse return;
    if ((resolver.isBoolType(return_type) catch null) != true) return;
    const body = tokens.bodyOf(o.tree, declaration) orelse return;
    var capture = PredicateCapture{ .gpa = o.gpa, .truth = truth };
    defer capture.deinit();
    var child: Oracle = .{
        .gpa = o.gpa, .tree = o.tree, .body = body, .cache = o.cache,
        .query = .numeric_range, .target = "", .use_token = std.math.maxInt(Ast.TokenIndex),
        .budget = o.budget, .infer_callers = false, .predicate_capture = &capture,
    };
    defer child.addressed.deinit(o.gpa);
    defer o.budget = child.budget;
    if (!purePredicateBody(&child, body, 0)) return;
    const flow = try analyzeBody(&child);
    if (!flow.diverged or child.budget == 0) return;
    const returned = if (capture.state) |*state| state else return;
    var parameters = proto.iterate(o.tree);
    var parameter_index: usize = 0;
    while (parameters.next()) |parameter| {
        const current = parameter_index;
        parameter_index += 1;
        const name = o.tree.tokenSlice(parameter.name_token orelse continue);
        const bound = returned.numericValue(name);
        if (bound == .unknown) continue;
        const argument = (resolver.callArgument(node, current) catch continue) orelse continue;
        const caller_name = numeric_eval.path(o.tree, argument) orelse continue;
        if (bound == .floating and !predicateArgumentUnchanged(&child, node, declaration, parameter.type_expr, argument)) continue;
        try st.setNumeric(o.gpa, caller_name, st.numericValue(caller_name).intersect(bound));
    }
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
    const source_bits = cache.maxFloatBitsOf(argument, &o.budget) orelse return false;
    const destination_bits = (resolver.floatBits(expected) catch null) orelse return false;
    return destination_bits != 0 and source_bits <= destination_bits;
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

fn bitAliasOf(o: *Oracle, st: *const State, node: Ast.Node.Index, depth: u8) ?BitAlias {
    if (depth == 32 or !o.spend()) return null;
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
            const info = (o.cache orelse return null).intInfoOf(node) orelse return null;
            if (info.signed) return null;
            if ((std.mem.eql(u8, name, "@as") and arguments.len == 2) or
                (std.mem.eql(u8, name, "@intCast") and arguments.len == 1))
                return bitAliasOf(o, st, arguments[arguments.len - 1], depth + 1);
            if (!std.mem.eql(u8, name, "@bitCast") or arguments.len != 1) return null;
            var evaluation = evaluator(o, st);
            if (evaluation.floatBits(arguments[0]) != info.bits) return null;
            return floatBitSource(o, st, arguments[0], info.bits);
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

fn floatBitSource(o: *Oracle, st: *const State, original: Ast.Node.Index, width: u16) ?BitAlias {
    if (width != 16 and width != 32 and width != 64) return null;
    var evaluation = evaluator(o, st);
    const cache = o.cache orelse return null;
    const source_width = cache.maxFloatBitsOf(original, &o.budget) orelse return null;
    if (source_width == 0 or source_width > width) return null;
    var node = original;
    var absolute = false;
    for (0..32) |_| {
        if (!o.spend()) return null;
        if (numeric_eval.path(o.tree, node)) |name| return .{
            .source = name, .float_bits = @intCast(width), .absolute = absolute,
            .mask = @as(u64, std.math.maxInt(u64)) >> @as(u6, @intCast(64 - width)),
        };
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
        } else if ((std.mem.eql(u8, name, "@floatCast") and arguments.len == 1) or
            (std.mem.eql(u8, name, "@as") and arguments.len == 2))
        {
            const input = arguments[arguments.len - 1];
            const input_width = cache.maxFloatBitsOf(input, &o.budget) orelse return null;
            const output_width = evaluation.floatBits(node) orelse return null;
            if (input_width == 0 or input_width > output_width) return null;
            node = input;
        } else return null;
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
    var alias = floatBitSource(o, st, value, width) orelse return null;
    alias.union_view = true;
    return alias;
}

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
) bool {
    var oracle: Oracle = .{
        .gpa = gpa,
        .tree = tree,
        .body = body_node,
        .query = query,
        .target = target,
        .use_token = use_token,
        .min_n = min_n,
        .cache = cache,
        .expression = expression,
    };
    defer oracle.addressed.deinit(gpa);
    const flow = analyzeBody(&oracle) catch return false;
    if (oracle.budget == 0) return false;
    return flow.answer orelse false;
}

fn analyzeBody(o: *Oracle) error{OutOfMemory}!Flow {
    var owned_bindings: ?local_bindings.LocalBindings = null;
    defer if (owned_bindings) |*bindings| bindings.deinit();
    defer o.locals = &.{};
    try collectAddressedRoots(o);
    var st: State = .{};
    defer st.deinit(o.gpa);
    try seedParameters(o, &st, &owned_bindings);
    return analyzeNode(o, o.body, &st);
}

fn seedParameters(o: *Oracle, st: *State, owned: *?local_bindings.LocalBindings) error{OutOfMemory}!void {
    const tree = o.tree;
    var declaration: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .fn_decl) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeData(node).node_and_node[1] == o.body) {
            declaration = node;
            break;
        }
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = if (declaration) |node| tokens.fnProto(tree, &buffer, node) else null;
    if (o.cache) |cache| {
        o.locals = (try cache.localBindings(proto, o.body)).items;
    } else {
        owned.* = try local_bindings.build(o.gpa, tree, proto, o.body);
        o.locals = owned.*.?.items;
    }
    var parameters = (proto orelse return).iterate(tree);
    var parameter_index: usize = 0;
    while (parameters.next()) |parameter| {
        const current_parameter = parameter_index;
        parameter_index += 1;
        const token = parameter.name_token orelse continue;
        if (o.query == .numeric_range) {
            var evaluation = evaluator(o, st);
            const declared = if (parameter.type_expr) |type_node|
                evaluation.typeRange(type_node) else .unknown;
            var initial = declared;
            if (declared == .unknown) if (parameter.type_expr) |type_node| {
                if (o.cache) |cache| {
                    if (cache.maxFloatBitsOf(type_node, &o.budget) != null) initial = .{ .floating = .{} };
                }
            };
            const incoming = if (o.infer_callers and (declared != .unknown or parameter.type_expr == null))
                try callerParameterBounds(o, declaration.?, current_parameter, parameter.type_expr)
            else
                .unknown;
            try st.setNumeric(o.gpa, tree.tokenSlice(token), initial.intersect(incoming));
        }
        if (parameterNonnegative(o, parameter.type_expr)) {
            try st.setScalarMin(o.gpa, tree.tokenSlice(token), 0);
        }
    }
}

fn callerParameterBounds(o: *Oracle, declaration: Ast.Node.Index, parameter: usize, destination: ?Ast.Node.Index) error{OutOfMemory}!NumericRange {
    var ancestor = o.caller_parent;
    for (0..8) |_| {
        const parent = ancestor orelse break;
        if (parent.body == o.body) return .unknown;
        ancestor = parent.caller_parent;
    }
    if (ancestor != null) return .unknown;
    const cache = o.cache orelse return .unknown;
    const resolver = cache.zls orelse return .unknown;
    const calls = (try cache.closedLocalCalls(declaration)) orelse return .unknown;
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

fn callerArgumentBounds(o: *Oracle, call_node: Ast.Node.Index, argument: Ast.Node.Index) error{OutOfMemory}!NumericRange {
    const body = callerBody(o.tree, call_node);
    var child: Oracle = .{
        .gpa = o.gpa, .tree = o.tree, .body = body orelse .root,
        .query = .numeric_range, .target = "", .expression = argument,
        .use_token = o.tree.firstToken(argument), .cache = o.cache,
        .budget = o.budget, .caller_parent = o,
    };
    defer child.addressed.deinit(o.gpa);
    defer o.budget = child.budget;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = o.tree.fullCall(&buffer, call_node).?;
    // Impure sibling arguments can change guarded values before they are copied.
    if (body == null or !pureCallInputs(&child, call)) return numericValue(&child, &.{}, argument);
    const flow = try analyzeBody(&child);
    if (flow.answer == null or child.budget == 0) return .unknown;
    return child.numeric_answer;
}

fn callerBody(tree: *const Ast, call: Ast.Node.Index) ?Ast.Node.Index {
    const token = tree.firstToken(call);
    if (tokens.enclosingFnDecl(tree, token)) |declaration| return tokens.bodyOf(tree, declaration);
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .test_decl) continue;
        const body = tree.nodeData(@enumFromInt(index)).opt_token_and_node[1];
        if (token >= tree.firstToken(body) and token <= tree.lastToken(body)) return body;
    }
    return null;
}

fn collectAddressedRoots(o: *Oracle) error{OutOfMemory}!void {
    const tree = o.tree;
    const first = tree.firstToken(o.body);
    const last = tree.lastToken(o.body);
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .address_of) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
        if (lhsRootIdent(o, tree.nodeData(node).node)) |root| try o.addressed.add(o.gpa, root);
    }
}

fn localScalarSurvivesCall(o: *const Oracle, name: []const u8) bool {
    if (std.mem.indexOfScalar(u8, name, '.') != null or o.addressed.contains(name)) return false;
    for (o.locals) |binding| if (std.mem.eql(u8, binding.name, name)) return true;
    return false;
}

fn dropIndirectFacts(o: *Oracle, st: *State) void {
    for (o.addressed.keys.items) |root| {
        dropContainersRootedAt(st, root);
        st.dropScalarValsByName(root);
        st.dropDiffAliasesByName(root);
    }
    var scalar: usize = 0;
    while (scalar < st.scalars.keys.items.len) {
        if (!localScalarSurvivesCall(o, st.scalars.keys.items[scalar])) {
            const removed = st.scalars.keys.swapRemove(scalar);
            std.debug.assert(!localScalarSurvivesCall(o, removed));
        } else scalar += 1;
    }
    var bound: usize = 0;
    while (bound < st.scalar_mins.items.len) {
        if (!localScalarSurvivesCall(o, st.scalar_mins.items[bound].name)) {
            const removed = st.scalar_mins.swapRemove(bound);
            std.debug.assert(!localScalarSurvivesCall(o, removed.name));
        } else bound += 1;
    }
    var numeric: usize = 0;
    while (numeric < st.numeric.items.len) {
        if (!localScalarSurvivesCall(o, st.numeric.items[numeric].name)) {
            const removed = st.numeric.swapRemove(numeric);
            std.debug.assert(!localScalarSurvivesCall(o, removed.name));
        } else numeric += 1;
    }
    var scalar_value: usize = 0;
    while (scalar_value < st.scalar_vals.items.len) {
        if (!localScalarSurvivesCall(o, st.scalar_vals.items[scalar_value].name)) {
            const removed = st.scalar_vals.swapRemove(scalar_value);
            std.debug.assert(!localScalarSurvivesCall(o, removed.name));
        } else scalar_value += 1;
    }
    st.containers.keys.clearRetainingCapacity();
    st.min_lens.clearRetainingCapacity();
    st.aliases.clearRetainingCapacity();
    st.diff_aliases.clearRetainingCapacity();
    st.value_aliases.clearRetainingCapacity();
    st.bit_aliases.clearRetainingCapacity();
    st.product_aliases.clearRetainingCapacity();
    st.clearPredicates();
}

fn analyzeNode(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
    if (o.walk_depth == 64) {
        o.budget = 0;
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
            if (operand) |expression| if (o.predicate_capture) |capture| try capture.record(o, expression, st);
            if (o.tokenInNode(node)) {
                if (operand) |e| {
                    const sub = try analyzeNode(o, e, st);
                    flow.answer = sub.answer orelse o.answerAt(st);
                } else flow.answer = o.answerAt(st);
            }
            return flow;
        },
        .fn_decl, .container_decl, .container_decl_trailing, .container_decl_two,
        .container_decl_two_trailing, .container_decl_arg, .container_decl_arg_trailing,
        .@"comptime" => return .{},
        .@"catch", .@"orelse", .@"defer", .@"errdefer" => {
            dropLoopMutated(o, node, st);
            dropIndirectFacts(o, st);
            return if (o.tokenInNode(node)) .{ .answer = o.answerAt(st) } else .{};
        },
        else => return analyzeExpression(o, node, st),
    }
}

fn analyzeExpression(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
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
    if (mayMutateIndirect(o, node)) dropIndirectFacts(o, st);
    if (o.tokenInNode(node)) return .{ .answer = o.answerAt(st) };
    killMutatedContainers(o, node, st);
    try recordReadBounds(o, node, st);
    return .{};
}

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
    try applyRefineFacts(o, st, null, 0, nodeSrc(tree, container), minimum, null);
}

fn analyzeCall(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
    const tree = o.tree;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node).?;
    for (call.ast.params) |parameter| {
        const flow = try analyzeNode(o, parameter, st);
        if (o.tokenInNode(parameter) and flow.answer != null) return flow;
        if (flow.diverged) return flow;
    }
    killMutatedContainers(o, node, st);
    if (mayMutateIndirect(o, node)) dropIndirectFacts(o, st);
    if (call.ast.params.len == 1 and isStdAssert(o, call.ast.fn_expr, tree.firstToken(node))) {
        try applyRefine(o, st, .{ .node = call.ast.params[0], .truth = true });
    }
    return if (o.tokenInNode(node)) .{ .answer = o.answerAt(st) } else .{};
}

fn isStdAssert(o: *Oracle, callee: Ast.Node.Index, anchor: Ast.TokenIndex) bool {
    return std.mem.eql(u8, nodeSrc(o.tree, callee), "std.debug.assert") and stdBindingValidAt(o, anchor);
}

fn isPureStdCall(o: *Oracle, callee: Ast.Node.Index, anchor: Ast.TokenIndex) bool {
    const name = nodeSrc(o.tree, callee);
    const pure = [_][]const u8{
        "std.math.minInt", "std.math.maxInt", "std.math.inf", "std.math.nan",
        "std.math.isFinite", "std.math.isNan", "std.math.isInf", "std.math.clamp",
    };
    for (pure) |candidate| {
        if (std.mem.eql(u8, name, candidate)) return stdBindingValidAt(o, anchor);
    }
    return false;
}

fn analyzeSeq(o: *Oracle, stmts: []const Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
    for (stmts) |s| {
        const flow = try analyzeNode(o, s, st);
        if (flow.answer != null) return flow;
        if (flow.diverged) return flow;
    }
    return .{};
}

fn analyzeVarDecl(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
    const tree = o.tree;
    const decl = tree.fullVarDecl(node) orelse return .{};
    const name = tree.tokenSlice(decl.ast.mut_token + 1);
    const init_node = decl.ast.init_node.unwrap() orelse {
        st.scalars.remove(name);
        st.dropScalarMinsByName(name);
        dropContainersRootedAt(st, name);
        st.dropMinLensByRoot(name);
        st.dropAliasesByScalar(name);
        st.dropDiffAliasesByName(name);
        st.dropValueAliasesByRoot(name);
        st.dropScalarValsByName(name);
        st.dropProductAliasesByName(name);
        st.dropProductAliasesByRoot(name);
        dropProductAliasesByConditionName(o, st, name);
        if (stateMentionsName(o, st, name)) st.clearPredicates();
        return .{};
    };
    const call_nonzero = callResultNonzero(o, init_node, st);
    const allocated_minimum = allocatedMinimum(o, st, init_node);
    const init_flow = try analyzeNode(o, init_node, st);
    if (o.tokenInNode(init_node) and init_flow.answer != null) return init_flow;
    const init_min = exprMin(o, st, init_node) orelse
        if (parameterNonnegative(o, decl.ast.type_node.unwrap())) @as(?u64, 0) else null;
    const init_numeric = numericAssignment(o, st, init_node, node);
    const bit_alias = if (o.query == .numeric_range) bitAliasOf(o, st, init_node, 0) else null;
    // Re-binding `name` invalidates prior facts/aliases keyed on it.
    st.scalars.remove(name);
    st.dropScalarMinsByName(name);
    dropContainersRootedAt(st, name);
    st.dropMinLensByRoot(name);
    st.dropAliasesByScalar(name);
    st.dropDiffAliasesByName(name);
    st.dropValueAliasesByRoot(name);
    st.dropScalarValsByName(name);
    st.dropProductAliasesByName(name);
    st.dropProductAliasesByRoot(name);
    dropProductAliasesByConditionName(o, st, name);
    if (stateMentionsName(o, st, name)) st.clearPredicates();
    if (o.query == .numeric_range) try st.setNumeric(o.gpa, name, init_numeric);
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
        var evaluation = evaluator(o, st);
        if (evaluation.floatBits(node)) |width| {
            if (floatBitSource(o, st, init_node, width)) |source| {
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
    return .{};
}

fn analyzeAssign(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
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
    const rhs_flow = try analyzeNode(o, rhs, st);
    if (o.tokenInNode(rhs) and rhs_flow.answer != null) return rhs_flow;
    const rhs_min = exprMin(o, st, rhs);
    const rhs_numeric = numericAssignment(o, st, rhs, lhs);
    if (tree.nodeTag(lhs) != .identifier) dropIndirectFacts(o, st);
    if (scalarPath(o, lhs)) |name| {
        st.scalars.remove(name);
        st.dropScalarMinsByName(name);
        dropContainersRootedAt(st, name);
        st.dropMinLensByRoot(name);
        st.dropAliasesByScalar(name);
        st.dropDiffAliasesByName(name);
        st.dropValueAliasesByRoot(name);
        st.dropScalarValsByName(name);
        st.dropProductAliasesByName(name);
        st.dropProductAliasesByRoot(name);
        dropProductAliasesByConditionName(o, st, name);
        if (stateMentionsName(o, st, name)) st.clearPredicates();
        if (o.query == .numeric_range) try st.setNumeric(o.gpa, name, rhs_numeric);
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
    return .{};
}

fn allocatedMinimum(o: *Oracle, st: *const State, initializer: Ast.Node.Index) ?u64 {
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
    return exprMin(o, st, call.ast.params[1]);
}


fn isPureBuiltin(name: []const u8) bool {
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
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma =>
            return !isPureBuiltin(tree.tokenSlice(tree.nodeMainToken(node))),
        else => {},
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return false;
    return !isStdAssert(o, call.ast.fn_expr, tree.firstToken(node)) and
        !isStdMathMul(o, call.ast.fn_expr, node) and
        !isPureStdCall(o, call.ast.fn_expr, tree.firstToken(node));
}
fn pureIntegerExpression(o: *Oracle, node: Ast.Node.Index, depth: u8) bool {
    if (depth == 64 or !o.spend()) return false;
    const tree = o.tree;
    switch (tree.nodeTag(node)) {
        .call, .call_comma, .call_one, .call_one_comma => {
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node).?;
            if (!isPureStdCall(o, call.ast.fn_expr, tree.firstToken(node))) return false;
        },
        .identifier, .number_literal, .char_literal, .enum_literal, .field_access, .grouped_expression,
        .array_access, .deref, .negation, .bit_not,
        .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor,
        .bool_not, .bool_and, .bool_or,
        .equal_equal, .bang_equal, .less_than, .less_or_equal, .greater_than, .greater_or_equal => {},
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
    const tree = o.tree;
    var imported = false;
    for (tree.rootDecls()) |root| {
        const decl = tree.fullVarDecl(root) orelse continue;
        if (tree.tokens.items(.tag)[decl.ast.mut_token] != .keyword_const) continue;
        const name_token = decl.ast.mut_token + 1;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), "std")) continue;
        const init = decl.ast.init_node.unwrap() orelse return false;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(init)), "@import")) return false;
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, init) orelse return false;
        if (params.len != 1 or tree.nodeTag(params[0]) != .string_literal) return false;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(params[0])), "\"std\"")) return false;
        imported = true;
        break;
    }
    if (!imported) return false;
    if (bodyHasStdParameter(tree, o.body)) return false;
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

fn bodyHasStdParameter(tree: *const Ast, body: Ast.Node.Index) bool {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .fn_decl) continue;
        const fn_node: Ast.Node.Index = @enumFromInt(index);
        const data = tree.nodeData(fn_node).node_and_node;
        if (data[1] != body) continue;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buffer, data[0]) orelse return true;
        var params = proto.iterate(tree);
        while (params.next()) |param| {
            if (param.name_token) |name_token| {
                if (std.mem.eql(u8, tree.tokenSlice(name_token), "std")) return true;
            }
        }
        return false;
    }
    return true;
}

/// Root identifier of an assignment LHS path (`self` from `self.bit_length`,
/// `arr` from `arr[i].x`), or null.
fn lhsRootIdent(o: *Oracle, lhs: Ast.Node.Index) ?[]const u8 {
    const root = @import("../ast/tokens.zig").rootIdentifier(o.tree, lhs) orelse return null;
    return o.tree.tokenSlice(o.tree.nodeMainToken(root));
}

/// `x += <expr>` transfers a proven lower bound.  When both the old value and
/// the addend have known non-negative lower bounds, the sum is retained (with
/// checked `u64` arithmetic).  An unknown addend drops the bound instead of
/// guessing that the local is unsigned; this keeps signed `-1 += 1` unknown.
fn analyzeCompoundAdd(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
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
        if (tree.nodeTag(lhs) != .identifier) dropIndirectFacts(o, st);
        // The value changed: a `n = c.len` snapshot no longer holds, and any
        // container path rooted at `name` is stale.
        st.scalars.remove(name);
        st.dropScalarMinsByName(name);
        dropContainersRootedAt(st, name);
        st.dropMinLensByRoot(name);
        st.dropAliasesByScalar(name);
        st.dropDiffAliasesByName(name);
        st.dropValueAliasesByRoot(name);
        st.dropScalarValsByName(name);
        st.dropProductAliasesByName(name);
        st.dropProductAliasesByRoot(name);
        dropProductAliasesByConditionName(o, st, name);
        if (stateMentionsName(o, st, name)) st.clearPredicates();
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
fn analyzeCompoundMutation(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
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
        if (tree.nodeTag(lhs) != .identifier) dropIndirectFacts(o, st);

        st.scalars.remove(name);
        st.dropScalarMinsByName(name);
        dropContainersRootedAt(st, name);
        st.dropMinLensByRoot(name);
        st.dropAliasesByScalar(name);
        st.dropDiffAliasesByName(name);
        st.dropValueAliasesByRoot(name);
        st.dropScalarValsByName(name);
        st.dropProductAliasesByName(name);
        st.dropProductAliasesByRoot(name);
        dropProductAliasesByConditionName(o, st, name);
        if (stateMentionsName(o, st, name)) st.clearPredicates();
        if (new_min) |min| {
            try st.setScalarMin(o.gpa, name, min);
            if (min >= 1) try st.scalars.add(o.gpa, name);
        }
    } else {
        killMutatedContainers(o, node, st);
    }
    return .{};
}

fn analyzeIf(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
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
    if (o.tokenInNode(then_node)) return try analyzeNode(o, then_node, &then_st);
    const then_flow = try analyzeNode(o, then_node, &then_st);

    var else_st = try st.clone(o.gpa);
    defer else_st.deinit(o.gpa);
    try applyRefine(o, &else_st, .{ .node = cond, .truth = false });
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
fn analyzeShortCircuit(o: *Oracle, node: Ast.Node.Index, st: *State, is_and: bool) error{OutOfMemory}!Flow {
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

/// `switch (scrutinee) { K => arm, … }`.  When the use is in an arm whose single
/// label is an integer literal `K` and the scrutinee is a simple scalar, record
/// `scrutinee == K` (and nonzero if K != 0) for that arm — so a slice whose
/// length aliases the scrutinee is known to have length K inside the arm.
fn analyzeSwitch(o: *Oracle, node: Ast.Node.Index, st: *State) error{OutOfMemory}!Flow {
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
    dropLoopMutated(o, node, st);
    dropIndirectFacts(o, st);
    return .{};
}

const LoopKind = enum { while_, for_ };

fn numericLoopInvariants(o: *Oracle, loop_node: Ast.Node.Index, st: *const State) error{OutOfMemory}!std.ArrayList(numeric_eval.Fact) {
    var facts: std.ArrayList(numeric_eval.Fact) = .empty;
    errdefer facts.deinit(o.gpa);
    if (o.query != .numeric_range or !o.tokenInNode(loop_node)) return facts;
    const loop = o.tree.fullWhile(loop_node) orelse return facts;
    if (!o.tokenInNode(loop.ast.then_expr)) return facts;
    if (!pureIntegerExpression(o, loop.ast.cond_expr, 0)) return facts;
    if (!try collectLoopCandidates(o, loop_node, st, &facts) or facts.items.len == 0) {
        facts.clearRetainingCapacity();
        return facts;
    }
    var envelope = facts.items[0].value;
    for (facts.items[1..]) |fact| envelope = envelope.join(fact.value);
    for (facts.items) |*fact| fact.value = envelope;
    if (!try verifyLoopInvariant(o, loop_node, loop, st, facts.items)) facts.clearRetainingCapacity();
    return facts;
}

fn collectLoopCandidates(o: *Oracle, loop_node: Ast.Node.Index, st: *const State, facts: *std.ArrayList(numeric_eval.Fact)) error{OutOfMemory}!bool {
    const tree = o.tree;
    const first = tree.firstToken(loop_node);
    const last = tree.lastToken(loop_node);
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (node == loop_node or tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
        if (!o.spend()) return false;
        switch (tag) {
            .@"break" => if (tree.nodeData(node).opt_token_and_opt_node[0].unwrap() != null) return false,
            .@"continue", .@"defer", .@"errdefer", .@"catch", .@"orelse",
            .assign_destructure, .fn_decl, .@"asm", .asm_simple => return false,
            else => {},
        }
        if (!isScalarAssignTag(tag)) continue;
        const lhs = tree.nodeData(node).node_and_node[0];
        if (tree.nodeTag(lhs) != .identifier) continue;
        const name = tree.tokenSlice(tree.nodeMainToken(lhs));
        const value = st.numericValue(name);
        if (value != .integer) continue;
        var present = false;
        for (facts.items) |fact| {
            if (std.mem.eql(u8, fact.name, name)) present = true;
        }
        if (present) continue;
        if (facts.items.len == 32) return false;
        try facts.append(o.gpa, .{ .name = name, .value = value });
    }
    return true;
}

fn loopFactsContain(state: *const State, facts: []const numeric_eval.Fact) bool {
    for (facts) |fact| {
        const result = state.numericValue(fact.name);
        if (result != .integer or result.integer.min < fact.value.integer.min or
            result.integer.max > fact.value.integer.max) return false;
    }
    return true;
}

fn verifyLoopInvariant(o: *Oracle, loop_node: Ast.Node.Index, loop: Ast.full.While, initial: *const State, facts: []const numeric_eval.Fact) error{OutOfMemory}!bool {
    var state = try initial.clone(o.gpa);
    defer state.deinit(o.gpa);
    const saved_token = o.use_token;
    o.use_token = std.math.maxInt(Ast.TokenIndex);
    defer o.use_token = saved_token;
    const saved_capture = o.break_capture;
    o.break_capture = null;
    defer o.break_capture = saved_capture;
    if ((try analyzeNode(o, loop.ast.cond_expr, &state)).diverged) return false;
    try applyRefine(o, &state, .{ .node = loop.ast.cond_expr, .truth = true });
    if (!loopFactsContain(&state, facts)) return false;
    dropLoopMutated(o, loop_node, &state);
    for (facts) |fact| try state.setNumeric(o.gpa, fact.name, fact.value);
    try applyRefine(o, &state, .{ .node = loop.ast.cond_expr, .truth = true });
    if ((try analyzeNode(o, loop.ast.then_expr, &state)).diverged) return false;
    if (loop.ast.cont_expr.unwrap()) |continuation| {
        if ((try analyzeNode(o, continuation, &state)).diverged) return false;
    }
    // Only a backedge that re-enters the body must preserve its invariant.
    // The condition and continuation are not covered by these body facts.
    if ((try analyzeNode(o, loop.ast.cond_expr, &state)).diverged) return false;
    try applyRefine(o, &state, .{ .node = loop.ast.cond_expr, .truth = true });
    return o.budget > 0 and loopFactsContain(&state, facts);
}

fn analyzeLoop(o: *Oracle, node: Ast.Node.Index, st: *State, kind: LoopKind) error{OutOfMemory}!Flow {
    const tree = o.tree;
    if (tree.fullFor(node)) |loop| {
        for (loop.ast.inputs) |input| {
            const flow = try analyzeNode(o, input, st);
            if (o.tokenInNode(input) and flow.answer != null) return flow;
        }
    }
    var invariants = try numericLoopInvariants(o, node, st);
    defer invariants.deinit(o.gpa);
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
            } else if (tree.fullFor(node)) |for_data| {
                var capture = for_data.payload_token;
                const tags = tree.tokens.items(.tag);
                for (for_data.ast.inputs) |input| {
                    if (capture >= tags.len) break;
                    const pointer_capture = tags[capture] == .asterisk;
                    if (pointer_capture) capture += 1;
                    if (capture >= tags.len or tags[capture] != .identifier) break;
                    if (!pointer_capture) try refineForInput(o, &body_st, input, tree.tokenSlice(capture));
                    if (rangeUpperName(tree, input)) |upper| {
                        try body_st.scalars.add(o.gpa, upper);
                    } else if (iterablePath(o, input)) |path| {
                        try applyRefineFacts(o, &body_st, null, 0, path, 1, null);
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
    const lower = if (tree.nodeTag(input) == .for_range)
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
    st.scalars.remove(capture);
    st.dropScalarMinsByName(capture);
    if (lower) |value| {
        try st.setScalarMin(o.gpa, capture, value);
        if (value > 0) try st.scalars.add(o.gpa, capture);
    }
}

fn applyRefine(o: *Oracle, st: *State, predicate: Predicate) error{OutOfMemory}!void {
    // Apply proved return facts once; do not retain a helper call as a stable predicate.
    if (o.query == .numeric_range) try refinePredicateOutcome(o, st, predicate, 0);
    const stable = stablePredicate(o, predicate) orelse return;
    if (!try addImpliedPredicate(o, st, stable.node, stable.truth)) return;
    try derivePredicateConsequences(o, st);
}

fn stablePredicate(o: *Oracle, original: Predicate) ?Predicate {
    var predicate = original;
    for (0..64) |_| {
        predicate.node = unwrapGrouped(o.tree, predicate.node);
        if (pureIntegerExpression(o, predicate.node, 0)) return predicate;
        switch (o.tree.nodeTag(predicate.node)) {
            .bool_not => {
                predicate.node = o.tree.nodeData(predicate.node).node;
                predicate.truth = !predicate.truth;
            },
            .bool_and, .bool_or => |tag| {
                if ((tag == .bool_and) != predicate.truth) return null;
                // Both operands ran; only the last operand's facts can
                // survive effects in the preceding operand.
                predicate.node = o.tree.nodeData(predicate.node).node_and_node[1];
            },
            else => return null,
        }
    }
    o.budget = 0;
    return null;
}

fn applyRefineFacts(
    o: *Oracle,
    st: *State,
    scalar: ?[]const u8,
    scalar_min: u64,
    container: ?[]const u8,
    container_min: u64,
    equality: ?Equality,
) error{OutOfMemory}!void {
    if (scalar) |s| {
        try st.scalars.add(o.gpa, s);
        if (scalar_min >= 1) try st.setScalarMin(o.gpa, s, scalar_min);
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
    if (container) |c| {
        try st.containers.add(o.gpa, c);
        if (container_min > 0) try st.setMinLen(o.gpa, c, container_min);
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

/// Use only logical implications that are valid on every path. In
/// particular, `!(A and B)` plus `A` proves `!B`; `!(A or B)` proves both
/// operands false.
fn derivePredicateConsequences(o: *Oracle, st: *State) error{OutOfMemory}!void {
    var changed = true;
    while (changed) {
        changed = false;
        var i: usize = 0;
        while (i < st.predicates.items.len) : (i += 1) {
            const predicate = st.predicates.items[i];
            if (!o.spend()) return;
            const tag = o.tree.nodeTag(predicate.node);
            if (tag == .bool_not) {
                if (try addImpliedPredicate(o, st, o.tree.nodeData(predicate.node).node, !predicate.truth)) changed = true;
                continue;
            }
            if (tag != .bool_and and tag != .bool_or) continue;
            const parts = o.tree.nodeData(predicate.node).node_and_node;
            if ((tag == .bool_and) == predicate.truth) {
                if (try addImpliedPredicate(o, st, parts[0], predicate.truth)) changed = true;
                if (try addImpliedPredicate(o, st, parts[1], predicate.truth)) changed = true;
            } else {
                if (hasPredicateNode(o.tree, st, parts[0], !predicate.truth)) {
                    if (try addImpliedPredicate(o, st, parts[1], predicate.truth)) changed = true;
                }
                if (hasPredicateNode(o.tree, st, parts[1], !predicate.truth)) {
                    if (try addImpliedPredicate(o, st, parts[0], predicate.truth)) changed = true;
                }
            }
        }
    }
}

fn addImpliedPredicate(
    o: *Oracle,
    st: *State,
    original: Ast.Node.Index,
    truth: bool,
) error{OutOfMemory}!bool {
    const node = unwrapGrouped(o.tree, original);
    const predicate = Predicate{ .node = node, .truth = truth };
    if (st.hasPredicate(predicate)) return false;
    if (o.query == .numeric_range) try refineNumeric(o, st, node, truth);
    var refine: Refinement = .{};
    collectRefinement(o, st, node, &refine);
    if (truth) {
        try applyRefineFacts(
            o,
            st,
            refine.then_scalar,
            refine.then_scalar_min,
            refine.then_container,
            refine.then_container_min,
            refine.then_equal,
        );
    } else {
        try applyRefineFacts(
            o,
            st,
            refine.else_scalar,
            refine.else_scalar_min,
            refine.else_container,
            refine.else_container_min,
            refine.else_equal,
        );
    }
    _ = try st.addPredicate(o.gpa, predicate);
    return true;
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

const Refinement = struct {
    then_scalar: ?[]const u8 = null,
    then_scalar_min: u64 = 0,
    else_scalar: ?[]const u8 = null,
    else_scalar_min: u64 = 0,
    then_container: ?[]const u8 = null,
    else_container: ?[]const u8 = null,
    then_equal: ?Equality = null,
    else_equal: ?Equality = null,
    // Proven minimum length of the container in each arm (>= 1 means
    // non-empty; > 1 carries the `c.len >= N` bound).
    then_container_min: u64 = 1,
    else_container_min: u64 = 1,
};

fn mergeScalarFact(
    dst_key: *?[]const u8,
    dst_min: *u64,
    src_key: ?[]const u8,
    src_min: u64,
) void {
    const src = src_key orelse return;
    if (dst_key.* == null) {
        dst_key.* = src;
        dst_min.* = src_min;
    } else if (std.mem.eql(u8, dst_key.*.?, src) and src_min > dst_min.*) {
        dst_min.* = src_min;
    }
}

fn mergeContainerFact(
    dst_key: *?[]const u8,
    dst_min: *u64,
    src_key: ?[]const u8,
    src_min: u64,
) void {
    const src = src_key orelse return;
    if (dst_key.* == null) {
        dst_key.* = src;
        dst_min.* = src_min;
    } else if (std.mem.eql(u8, dst_key.*.?, src) and src_min > dst_min.*) {
        dst_min.* = src_min;
    }
}

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
        mergeScalarFact(&out.then_scalar, &out.then_scalar_min, a.then_scalar, a.then_scalar_min);
        mergeScalarFact(&out.then_scalar, &out.then_scalar_min, b.then_scalar, b.then_scalar_min);
        mergeContainerFact(&out.then_container, &out.then_container_min, a.then_container, a.then_container_min);
        mergeContainerFact(&out.then_container, &out.then_container_min, b.then_container, b.then_container_min);
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
        mergeScalarFact(&out.else_scalar, &out.else_scalar_min, a.else_scalar, a.else_scalar_min);
        mergeScalarFact(&out.else_scalar, &out.else_scalar_min, b.else_scalar, b.else_scalar_min);
        mergeContainerFact(&out.else_container, &out.else_container_min, a.else_container, a.else_container_min);
        mergeContainerFact(&out.else_container, &out.else_container_min, b.else_container, b.else_container_min);
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
        var query = o.*;
        query.query = .nonempty_container;
        query.target = path;
        if (query.answerAt(st)) return true;
    }
    const lower = exprMin(o, st, node) orelse return false;
    if (lower > 0) return true;
    if (scalarPath(o, node)) |path| return st.scalars.contains(path);
    return false;
}

/// Return a proven non-negative lower bound for an integer expression.  This
/// intentionally returns null for unknown signed values: a name-only guess
/// would make `x > rhs` prove `x != 0` when `rhs` can be negative.
fn exprMin(o: *Oracle, st: *const State, node: Ast.Node.Index) ?u64 {
    if (o.expression_depth == 64) {
        o.budget = 0;
        return null;
    }
    o.expression_depth += 1;
    defer o.expression_depth -= 1;
    if (!o.spend()) return null;
    const tree = o.tree;
    const n = unwrapGrouped(tree, node);
    if (lenContainerPath(o, n)) |path| {
        if (st.minLenOf(path)) |minimum| return minimum;
        if (st.containers.contains(path)) return 1;
        if (o.cache) |cache| {
            const container = tree.nodeData(n).node_and_token[0];
            if (cache.fixedArrayLenOf(container)) |length| return length;
        }
        return 0;
    }
    if (intLiteralVal(tree, n)) |v| return v;
    if (scalarPath(o, n)) |name| {
        if (st.scalarMinOf(name)) |v| return v;
        if (st.scalarVal(name)) |v| return v;
        if (o.cache) |cache| {
            if (cache.comptimeIntValueOf(n)) |value| return value;
            if (cache.intInfoOf(n)) |info| if (!info.signed) return 0;
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
            const lhs = exprMin(o, st, d[0]) orelse break :blk null;
            const rhs = intLiteralVal(tree, d[1]) orelse break :blk null;
            if (lhs < rhs) break :blk null;
            break :blk lhs - rhs;
        },
        else => blk: {
            if (o.cache) |cache| {
                if (cache.intInfoOf(n)) |info| if (!info.signed) break :blk 0;
            }
            break :blk null;
        },
    };
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
        if (out.then_container == null) out.then_container = ok.key;
    } else if (out.then_scalar == null) out.then_scalar = ok.key;
}

fn setElseNonzero(out: *Refinement, ok: OperandKey) void {
    if (ok.is_container) {
        if (out.else_container == null) out.else_container = ok.key;
    } else if (out.else_scalar == null) out.else_scalar = ok.key;
}

fn setThenScalarMin(out: *Refinement, key: []const u8, min: u64) void {
    if (out.then_scalar == null) {
        out.then_scalar = key;
        out.then_scalar_min = min;
    } else if (std.mem.eql(u8, out.then_scalar.?, key) and min > out.then_scalar_min) {
        out.then_scalar_min = min;
    }
}

fn setElseScalarMin(out: *Refinement, key: []const u8, min: u64) void {
    if (out.else_scalar == null) {
        out.else_scalar = key;
        out.else_scalar_min = min;
    } else if (std.mem.eql(u8, out.else_scalar.?, key) and min > out.else_scalar_min) {
        out.else_scalar_min = min;
    }
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
            mergeContainerFact(&out.then_container, &out.then_container_min, ok.key, then_bound orelse 1);
        } else if (then_bound) |bound| {
            setThenScalarMin(out, ok.key, bound);
        } else {
            setThenNonzero(out, ok);
        }
    }
    if (else_bound != null or else_nonzero) {
        if (ok.is_container) {
            mergeContainerFact(&out.else_container, &out.else_container_min, ok.key, else_bound orelse 1);
        } else if (else_bound) |bound| {
            setElseScalarMin(out, ok.key, bound);
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
            if (out.then_container == null) {
                out.then_container = ok.key;
                out.then_container_min = bound;
            }
        }
        if (else_bound) |bound| {
            if (out.else_container == null) {
                out.else_container = ok.key;
                out.else_container_min = bound;
            }
        }
    } else {
        if (then_bound) |bound| setThenScalarMin(out, ok.key, bound);
        if (else_bound) |bound| setElseScalarMin(out, ok.key, bound);
    }
}

/// A pointer escape can mutate a tracked scalar or container binding through a
/// callee.  Invalidate facts for explicit `&name`; by-value uses remain reads.
fn dropEscapedScalarFacts(o: *Oracle, node: Ast.Node.Index, st: *State, depth: u8) void {
    if (depth == 64) {
        o.budget = 0;
        return;
    }
    if (!o.spend()) return;
    const tree = o.tree;
    if (tree.nodeTag(node) == .fn_decl) return;
    var buffer: [2]Ast.Node.Index = undefined;
    if (tree.builtinCallParams(&buffer, node) != null and
        std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@TypeOf")) return;
    if (mayMutateIndirect(o, node)) dropIndirectFacts(o, st);
    if (tree.nodeTag(node) == .address_of) {
        if (lhsRootIdent(o, unwrapGrouped(tree, tree.nodeData(node).node))) |name| {
            st.scalars.remove(name);
            st.dropScalarMinsByName(name);
            dropContainersRootedAt(st, name);
            st.dropMinLensByRoot(name);
            st.dropAliasesByScalar(name);
            st.dropDiffAliasesByName(name);
            st.dropValueAliasesByRoot(name);
            st.dropScalarValsByName(name);
            st.dropProductAliasesByName(name);
            st.dropProductAliasesByRoot(name);
            dropProductAliasesByConditionName(o, st, name);
            if (stateMentionsName(o, st, name)) st.clearPredicates();
        }
    }
    var children = @import("type_engine").AstIterator.init(tree, node);
    while (children.next(tree)) |child| {
        dropEscapedScalarFacts(o, child, st, depth + 1);
        if (o.budget == 0) return;
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

fn isScalarAssignTag(tag: Ast.Node.Tag) bool {
    return switch (tag) {
        .assign,
        .assign_add,
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
        => true,
        else => false,
    };
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

fn dropLoopMutated(o: *Oracle, loop_node: Ast.Node.Index, st: *State) void {
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
        if (!isScalarAssignTag(tag)) continue;
        if (tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
        const name = scalarPath(o, tree.nodeData(node).node_and_node[0]) orelse continue;
        st.dropNumericRoot(name);
        st.dropValueAliasesByRoot(name);
        if (tag != .assign_add or !compoundAddPreservesScalar(o, st, node)) {
            st.scalars.remove(name);
            st.dropScalarMinsByName(name);
        }
        // Even monotonic `+=` invalidates `name = left * right`; only the
        // nonzero fact can survive that operation.
        st.dropProductAliasesByName(name);
        dropProductAliasesByConditionName(o, st, name);
        if (stateMentionsName(o, st, name)) st.clearPredicates();
    }
    dropContainersMutatedInTokens(tree, first, last, st);
}

/// Mutating container methods (grow/shrink/clear).
fn isMutatingMethod(name: []const u8) bool {
    const muts = [_][]const u8{
        "append",                  "appendSlice",            "appendAssumeCapacity", "appendNTimes",
        "insert",                  "insertSlice",            "resize",               "shrinkAndFree",
        "shrinkRetainingCapacity", "clearRetainingCapacity", "clearAndFree",         "pop",
        "popOrNull",               "orderedRemove",          "swapRemove",           "addOne",
        "addOneAssumeCapacity",    "addManyAsArray",         "addManyAsSlice",       "ensureTotalCapacity",
        "ensureUnusedCapacity",    "writer",                 "deinit",               "toOwnedSlice",
    };
    for (muts) |m| if (std.mem.eql(u8, name, m)) return true;
    return false;
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
    tree: *const Ast,
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
    _ = tree;
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

fn identName(tree: *const Ast, node: Ast.Node.Index) ?[]const u8 {
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
fn nodeSrc(tree: *const Ast, node: Ast.Node.Index) []const u8 {
    const starts = tree.tokens.items(.start);
    const ft = tree.firstToken(node);
    const lt = tree.lastToken(node);
    const start: usize = starts[ft];
    const end: usize = starts[lt] + tree.tokenSlice(lt).len;
    return tree.source[start..end];
}

fn unwrapGrouped(tree: *const Ast, node: Ast.Node.Index) Ast.Node.Index {
    var n = node;
    while (tree.nodeTag(n) == .grouped_expression) n = tree.nodeData(n).node_and_token[0];
    return n;
}

/// True iff `node` is a pure field-access chain rooted at an identifier
/// (`self.bit_length`, `a.b.c`) — no calls, no subscripts.
fn isPureFieldPath(tree: *const Ast, node: Ast.Node.Index) bool {
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
            if (std.mem.eql(u8, va.path, psrc) and st.scalars.contains(va.local)) return true;
    }
    return false;
}

/// Cross-fn: is `init` a call `callee(arg)` whose result is provably non-zero?
/// True when `callee` is an in-file single-return function whose return is
/// non-zero given its first parameter non-zero (e.g. ceil-division), AND `arg`
/// is proven non-zero at the call.  Single-argument callees only (v1).
fn callResultNonzero(o: *Oracle, init: Ast.Node.Index, st: *const State) bool {
    const tree = o.tree;
    var buf: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buf, init) orelse return false;
    const callee = identName(tree, call.ast.fn_expr) orelse return false;
    if (call.ast.params.len != 1) return false;
    if (!argProvablyNonzero(o, st, call.ast.params[0])) return false;
    return calleeReturnsNonzeroGivenArg(o, callee);
}

/// Every in-file function (top-level or method) named `name` has a single
/// `return EXPR` whose value is provably non-zero given its first parameter
/// non-zero.  Conservative: false if no such function is found, or ANY same-named
/// function fails (so it holds whichever overload is actually called).
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
    if (depth == 64 or !o.spend()) return false;
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
fn comptimeValOf(o: *Oracle, node: Ast.Node.Index) ?u64 {
    if (intLiteralVal(o.tree, unwrapGrouped(o.tree, node))) |value| return value;
    const cache = o.cache orelse return null;
    return cache.comptimeIntValueOf(unwrapGrouped(o.tree, node));
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

test {
    _ = @import("value_range_tests.zig");
}

test "range joins cannot equate different subtraction operands" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "const a = 0; const b = -1;", .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    const declarations = tree.rootDecls();
    const nonnegative = tree.fullVarDecl(declarations[0]).?.ast.init_node.unwrap().?;
    const negative = tree.fullVarDecl(declarations[1]).?.ast.init_node.unwrap().?;
    var left: State = .{};
    defer left.deinit(gpa);
    var right: State = .{};
    defer right.deinit(gpa);
    try left.addDiffAlias(gpa, .{ .diff = "difference", .minuend = "value", .sub_node = nonnegative });
    try right.addDiffAlias(gpa, .{ .diff = "difference", .minuend = "value", .sub_node = negative });
    left.intersectWith(&right);
    var oracle: Oracle = .{
        .gpa = gpa,
        .tree = &tree,
        .body = .root,
        .query = .nonzero_scalar,
        .target = "value",
        .use_token = 0,
    };
    try applyRefineFacts(&oracle, &left, "difference", 0, null, 0, null);
    try std.testing.expect(!oracle.answerAt(&left));
}
