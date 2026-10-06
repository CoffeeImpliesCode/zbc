//! Bounded numeric expression evaluation over resolved types and path facts.
const std = @import("std");
const Ast = std.zig.Ast;
const numbers = @import("numeric_range.zig");
const FileCache = @import("../cache/file_cache.zig").FileCache;
const Range = numbers.Range;
const budget_mod = @import("../budget.zig");
const local_bindings = @import("../model/local_bindings.zig");

/// A named value together with the range it was proved to hold: the shape
/// every range fact in this module takes.  It carries no claim of its own
/// about WHAT the range describes — `facts` reads it as the value of the
/// path, `len_bounds` reads it as the length of the binding — so the two
/// tables stay separate and a length is never mistaken for the slice.
pub const Fact = struct { name: []const u8, value: Range };

/// The root-scope `const` declarations a use may name, and what each is
/// initialised to.
///
/// A compile-time integer is routinely written as a name the file defines —
/// `const max_u32 = std.math.maxInt(u32);`, `const VLEN: usize = 64;` — and
/// the type engine resolves the expression inside such a binding but not the
/// name around it.  The declarations are BORROWED from the file cache's one
/// per-file index (`FileCache.fileConstInitializer`), which is built once per
/// file and answers a name directly; nothing here is allocated, and no
/// consumer builds a second table.
///
/// Two answers are deliberately withheld, and both are about a NAME rather
/// than about a value:
///
///   - A name the asking walk binds itself is asked of the walk, not of the
///     file.  A local of the same name is a different value whose facts the
///     walk already holds, so the file-level declaration must not answer for
///     it.  The root tier alone cannot decide that, which is why the walk's
///     own bindings travel with the cache handle.
///   - A name the file declares twice answers nothing.  That rule belongs to
///     the table itself, which drops such a name (and stays dropped, so a
///     third declaration cannot revive it) rather than resolving to whichever
///     declaration happened to come last.  A `const X: T;` with no
///     initializer is recorded the same way: it binds a name without
///     declaring a value this file can read.
pub const ContainerConsts = struct {
    tree: *const Ast,
    /// The cache holding the per-file constant index.  Borrowed, not owned:
    /// the table lives as long as the analysis of this file does.
    cache: *FileCache,
    /// The names this walk binds, borrowed from the walk's own bindings.
    walk_binds: []const local_bindings.Binding,

    pub fn lookup(self: ContainerConsts, name: []const u8) ?Ast.Node.Index {
        for (self.walk_binds) |binding| {
            if (std.mem.eql(u8, binding.name, name)) return null;
        }
        // A table that could not be allocated is not a file with no constants
        // in it: it is a file whose constants cannot be proven.  The name
        // answers nothing, which leaves it to its declared type — the weaker
        // reading, and never a claim the failed allocation invented.
        return (self.cache.fileConstInitializer(name) catch null) orelse null;
    }
};

pub const Evaluator = struct {
    /// The frame cap every descent in the numeric analysis shares: the
    /// evaluator's own recursion, and the statement walk's.
    pub const frame_cap: u8 = 64;

    tree: *const Ast,
    cache: ?*FileCache,
    facts: []const Fact,
    budget: *u32,
    std_valid: bool,
    depth: u8 = 0,
    /// File-scope `const` bindings, when the caller could resolve which of
    /// them this walk may name.  Null leaves an identifier to its declared
    /// type, which is the weaker but never wrong reading.
    container_consts: ?ContainerConsts = null,
    /// Range snapshots of a local's LENGTH, keyed by the local's own name.
    ///
    /// A standard allocator's `alloc(T, n)` returns exactly `n` elements, so
    /// the length of the binding it produced IS the count — and the count is
    /// a RANGE, not a constant: `@as(usize, v)` over a `u32` capture is
    /// every value up to 2^32-1, which is a narrower answer than the slice's
    /// own `usize` and a wider one than the allocator was ever asked about.
    ///
    /// The snapshot is taken where the binding was established and is owned
    /// by the walk's state, not re-read from the count's name: a write to
    /// the binding, or to the count it was given, drops the entry rather than
    /// leaving a length behind that describes a value no longer there.  It
    /// is deliberately NOT part of `facts`: a fact there is the value of the
    /// path itself, and the length of a slice is not the slice.
    len_bounds: []const Fact = &.{},

    /// Frames a recursive descent may take before it declines to go deeper.
    /// The owning walk spends the same bound on its own descents, so the two
    /// stop at the same depth and the diagnostic names one number.
    depth_limit: u8 = frame_cap,
    /// The step budget the owning query started with, reported when this
    /// evaluator runs the counter to zero.  The remaining count alone cannot
    /// say what the bound in force was.
    budget_cap: u32 = 0,
    /// Where the owning walk records the bound that stopped it.  Depth and
    /// steps are different bounds and the record has to say which one ran
    /// out: writing the step counter on the depth path would report a cost
    /// limit for a walk that spent a few dozen steps and stopped on nesting.
    stopped: ?*?budget_mod.Stop = null,

    /// Record the bound that stopped this evaluator.  First stop wins: a walk
    /// that gives up keeps unwinding and may trip a second bound, but the
    /// first one is the one that explains the rest.  The step counter is
    /// emptied as well, because a bound that stopped this expression has
    /// stopped everything computed from it.
    fn noteStop(self: *Evaluator, limit: budget_mod.Limit, cap: u32) void {
        self.budget.* = 0;
        if (self.stopped) |record| {
            if (record.* == null) record.* = .{ .limit = limit, .cap = cap };
        }
    }

    pub fn evaluate(self: *Evaluator, original: Ast.Node.Index) Range {
        if (self.depth >= self.depth_limit) {
            self.noteStop(.numeric_oracle_depth, self.depth_limit);
            return .unknown;
        }
        if (self.budget.* == 0) {
            self.noteStop(.numeric_oracle_steps, self.budget_cap);
            return .unknown;
        }
        self.budget.* -= 1;
        self.depth += 1;
        defer self.depth -= 1;
        const node = ungroup(self.tree, original);
        if (path(self.tree, node)) |name| {
            for (self.facts) |fact| {
                if (!std.mem.eql(u8, fact.name, name)) continue;
                // An assignment the walk could not evaluate records "this name
                // says nothing here", which is not the same claim as "this
                // name's type says nothing".  Falling through lets the
                // declared type bound it again, so `x = <unresolved call>`
                // keeps the parameter's or field's own range instead of
                // losing it to the absence of knowledge.
                if (fact.value == .unknown) continue;
                return self.narrow(fact.value, node);
            }
        }
        return switch (self.tree.nodeTag(node)) {
            .number_literal => self.literal(node),
            .negation => self.evaluate(self.tree.nodeData(node).node).negate(),
            .identifier, .field_access, .deref => self.declaredRange(node),
            .@"try" => self.evaluate(self.tree.nodeData(node).node),
            .add, .sub, .mul, .div => self.arithmetic(node),
            .bit_and, .bit_or, .bit_xor => self.bitwise(node),
            .shl, .shr => self.shift(node),
            .@"switch", .switch_comma => self.switchExpression(node),
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => self.builtinCall(node),
            .call, .call_comma, .call_one, .call_one_comma => self.standardCall(node),
            else => self.typeRange(node),
        };
    }

    pub fn typeRange(self: *Evaluator, node: Ast.Node.Index) Range {
        const cache = self.cache orelse return .unknown;
        if (cache.intInfoOf(node)) |info| return Range.integerType(info.bits, info.signed);
        if (cache.isFloatType(node) == true) return .{ .floating = .{} };
        return .unknown;
    }

    pub fn floatBits(self: *Evaluator, node: Ast.Node.Index) ?u16 {
        const cache = self.cache orelse return null;
        const resolver = cache.zls orelse return null;
        return resolver.floatBits(node) catch null;
    }

    pub fn coerce(self: *Evaluator, value: Range, source: Ast.Node.Index, destination: Ast.Node.Index) Range {
        if (self.floatBits(destination)) |bits| {
            if (self.floatBits(source)) |source_bits| {
                if (source_bits <= bits and value == .floating) return value;
            }
            return value.asFloat(bits);
        }
        const target = self.typeRange(destination);
        if (target == .integer) return value.intersect(target);
        return value;
    }

    fn literal(self: *Evaluator, node: Ast.Node.Index) Range {
        const text = self.tree.tokenSlice(self.tree.nodeMainToken(node));
        return switch (std.zig.parseNumberLiteral(text)) {
            .int, .big_int => Range.constant(std.fmt.parseInt(i128, text, 0) catch return .unknown),
            .float => Range.floatConstant(std.fmt.parseFloat(f128, text) catch return .unknown)
                .asFloat(self.floatBits(node) orelse 128),
            .failure => .unknown,
        };
    }

    /// What the binding itself says about the node, without consulting any
    /// path fact: a fixed array's own length, a compile-time integer, a
    /// container-level `const` alias, or otherwise the declared type.  This
    /// is the outer bound every fact for the same node is measured against.
    fn declaredRange(self: *Evaluator, node: Ast.Node.Index) Range {
        if (self.tree.nodeTag(node) == .field_access) {
            const parts = self.tree.nodeData(node).node_and_token;
            if (std.mem.eql(u8, self.tree.tokenSlice(parts[1]), "len")) {
                if (self.cache) |cache| {
                    if (cache.fixedArrayLenOf(parts[0])) |length| return Range.constant(length);
                }
                if (self.sliceSourceBound(parts[0])) |bound| return bound;
                if (self.allocatedLengthBound(parts[0])) |bound| {
                    // The snapshot says what the COUNT was when the binding
                    // was made; the slice's own `len` still has to hold it,
                    // and `len` is a `usize` whether the count was spelled as
                    // one or arrived through a coercion from something
                    // narrower.  Reading the snapshot through that type is
                    // what keeps a `u32` capture's 2^32-1 across the `@as`
                    // that widened it to `usize`.
                    const declared = self.typeRange(node);
                    return if (declared == .integer) bound.intersect(declared) else bound;
                }
            }
        }
        if (self.cache) |cache| {
            if (cache.comptimeIntValueOf(node)) |value| return Range.constant(value);
        }
        const declared = self.typeRange(node);
        // A file-scope `const` the file itself defines is the other ordinary
        // spelling of a compile-time integer, and only an identifier can name
        // one.  The table holds no name this walk binds, so what comes back
        // is the value the file gave that name, not a local of the same name.
        if (self.tree.nodeTag(node) == .identifier) {
            if (self.container_consts) |consts| {
                const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
                if (consts.lookup(name)) |initializer| {
                    const value = self.evaluate(initializer);
                    if (value == .integer) return value.intersect(declared);
                }
            }
        }
        return declared;
    }

    /// `s[a..b].len` never exceeds `s.len`: a slice's end is checked against
    /// the source's length before the slice exists, and a slice counts
    /// elements from `a` up to at most `b`.  That is the whole of what a
    /// sub-slice says about the source, and it is what lets a bounded input
    /// bound every span cut from it.
    fn sliceSourceBound(self: *Evaluator, node: Ast.Node.Index) ?Range {
        const slice = self.tree.fullSlice(node) orelse return null;
        const source = self.evaluate(slice.ast.sliced);
        if (source != .integer) return null;
        return .{ .integer = .{ .min = 0, .max = source.integer.max } };
    }

    /// `local.len` for a local bound to the result of a standard allocator's
    /// `alloc(T, n)`: the range `n` held AT THAT BINDING.
    ///
    /// The allocator's contract is that it returns a slice of exactly `n`
    /// elements, so the count bounds the length from both sides at once —
    /// which is why one snapshot answers what a lower bound alone could not.
    /// The snapshot is a value, not a query: nothing here re-reads the count's
    /// own name, so a count the walk has since learned something new about
    /// cannot widen a length that was proved at the allocation.
    ///
    /// A local the state carries no entry for, or one whose count the walk
    /// could not bound, proves nothing and answers nothing: the length stays
    /// what the declared `usize` says, which is the whole domain and never a
    /// claim that this allocation was small.
    fn allocatedLengthBound(self: *Evaluator, node: Ast.Node.Index) ?Range {
        const name = path(self.tree, node) orelse return null;
        for (self.len_bounds) |fact| {
            if (!std.mem.eql(u8, fact.name, name)) continue;
            if (fact.value == .unknown) continue;
            return fact.value;
        }
        return null;
    }

    /// A recorded fact narrows the value; the declared type bounds it from
    /// outside.  Intersecting keeps a fact that was established where the
    /// type could not be resolved from widening past the type it was later
    /// resolved to, and keeps a fact from outliving the exact length of the
    /// fixed array it was derived from.  Only two integer ranges are merged:
    /// anything else keeps the fact verbatim rather than losing it to a
    /// variant mismatch.
    fn narrow(self: *Evaluator, fact: Range, node: Ast.Node.Index) Range {
        if (fact != .integer) return fact;
        const declared = self.declaredRange(node);
        if (declared != .integer) return fact;
        return fact.intersect(declared);
    }

    fn arithmetic(self: *Evaluator, node: Ast.Node.Index) Range {
        const parts = self.tree.nodeData(node).node_and_node;
        var left = self.evaluate(parts[0]);
        var right = self.evaluate(parts[1]);
        const precision = self.floatBits(node);
        if (left == .floating or right == .floating) {
            const bits = precision orelse return .{ .floating = .{} };
            left = left.asFloat(bits);
            right = right.asFloat(bits);
        }
        const op: numbers.Operation = switch (self.tree.nodeTag(node)) {
            .add => .add,
            .sub => .sub,
            .mul => .mul,
            .div => .div,
            else => unreachable,
        };
        const value = left.binary(right, op);
        if (value == .floating) return value.asFloat(precision orelse 0);
        // Integer arithmetic does not leave the type it is written in: it
        // traps on overflow in the checked modes and is undefined in the
        // unchecked ones, and there is no value this analysis may name for
        // the result of an operation that can do either.  The mathematical
        // interval is therefore read back through the type only where the
        // operation provably stays inside it; where it may not, the answer is
        // the whole type — never a narrower claim, and never one that reports
        // a value the operation cannot be relied on to produce.  That is what
        // keeps a length bounded by its own guard, `arena.len`, apart from a
        // difference against a snapshot that has no bound of its own.
        const declared = self.typeRange(node);
        if (declared == .integer and value == .integer) {
            return overflowInterval(value.integer, declared.integer);
        }
        return value;
    }

    /// The values `a op b` can be relied on to take, computed inside
    /// `declared`.
    ///
    /// An operation whose mathematical result stays inside the type is
    /// answered exactly.  One that can leave it has no answer narrower than
    /// the type: the overflow traps in the checked modes and is undefined in
    /// the unchecked ones, so no value of it is a fact a reader may use.  The
    /// whole type is the one claim that stays true either way — and it is a
    /// claim about the RESULT's domain, not about wrapping: nothing here says
    /// the operation produces a wrapped value, only that it cannot be shown to
    /// produce anything narrower.  A builtin that wraps by definition
    /// (`+%`, `-%`, `*%`) is the opposite case and is not routed here.
    fn overflowInterval(value: numbers.Integer, declared: numbers.Integer) Range {
        if (value.min >= declared.min and value.max <= declared.max) return .{ .integer = value };
        return .{ .integer = declared };
    }

    /// What a switch expression yields: the union of the ranges of the
    /// arms, never the one arm a particular discriminant would pick.
    ///
    /// Nothing here knows which arm runs — the discriminant is a value
    /// this evaluator has not read — so every arm may be the one taken,
    /// and the answer has to hold for all of them.  That is also the
    /// safe direction when an arm cannot be read: `Range.join` answers
    /// `unknown` when either side is, and an unreadable arm keeps the
    /// declared type the arms share instead of being dropped, so a
    /// switch never claims a range narrower than its least readable arm
    /// allows.
    ///
    /// Each arm spends one step of the budget every other descent here
    /// shares, and the arms are siblings rather than nested, so a wide
    /// switch costs steps instead of the depth the walk reports.
    fn switchExpression(self: *Evaluator, node: Ast.Node.Index) Range {
        const switch_node = self.tree.fullSwitch(node) orelse return self.typeRange(node);
        var joined: ?Range = null;
        for (switch_node.ast.cases) |case_node| {
            const case = self.tree.fullSwitchCase(case_node) orelse return self.typeRange(node);
            const arm = self.evaluate(case.ast.target_expr);
            joined = if (joined) |left| left.join(arm) else arm;
        }
        // A switch that yields nothing, or one whose arms do not all
        // read, says exactly what reading none of them said: the type
        // they share.  That is the same bound the arms carried before
        // this arm existed, so a switch the evaluator cannot reduce
        // costs no precision.
        const value = joined orelse return self.typeRange(node);
        if (value == .unknown) return self.typeRange(node);
        // The arms are peer-typed with the switch itself, so the
        // declared type bounds the union from outside the same way it
        // bounds an integer arithmetic result.
        const declared = self.typeRange(node);
        if (declared == .integer and value == .integer) return value.intersect(declared);
        return value;
    }

    fn bitwise(self: *Evaluator, node: Ast.Node.Index) Range {
        const parts = self.tree.nodeData(node).node_and_node;
        const left = self.evaluate(parts[0]);
        const right = self.evaluate(parts[1]);
        const tag = self.tree.nodeTag(node);
        if (tag == .bit_and) {
            if (right == .integer and right.integer.min >= 0) return .{ .integer = .{
                .min = 0,
                .max = if (left == .integer and left.integer.min >= 0)
                    @min(left.integer.max, right.integer.max)
                else
                    right.integer.max,
            } };
            if (left == .integer and left.integer.min >= 0)
                return .{ .integer = .{ .min = 0, .max = left.integer.max } };
        }
        if (left != .integer or right != .integer or left.integer.min < 0 or right.integer.min < 0)
            return self.typeRange(node);
        const largest: u128 = @intCast(@max(left.integer.max, right.integer.max));
        const upper: i128 = if (largest == 0) 0 else @intCast(@as(u128, std.math.maxInt(u128)) >> @intCast(@clz(largest)));
        return .{ .integer = .{
            .min = if (tag == .bit_or) @max(left.integer.min, right.integer.min) else 0,
            .max = upper,
        } };
    }

    fn shift(self: *Evaluator, node: Ast.Node.Index) Range {
        const parts = self.tree.nodeData(node).node_and_node;
        const left = self.evaluate(parts[0]);
        const right = self.evaluate(parts[1]);
        if (left != .integer or right != .integer or right.integer.min < 0 or right.integer.max > 126)
            return self.typeRange(node);
        var low: i128 = std.math.maxInt(i128);
        var high: i128 = std.math.minInt(i128);
        for ([_]i128{ left.integer.min, left.integer.max }) |value| {
            for ([_]i128{ right.integer.min, right.integer.max }) |count| {
                const amount: u7 = @intCast(count);
                const shifted = if (self.tree.nodeTag(node) == .shr) value >> amount else std.math.mul(i128, value, @as(i128, 1) << amount) catch return self.typeRange(node);
                low = @min(low, shifted);
                high = @max(high, shifted);
            }
        }
        if (self.tree.nodeTag(node) == .shl) {
            const destination = self.typeRange(node);
            if (destination == .integer) {
                if (low < destination.integer.min or high > destination.integer.max) return destination;
            } else if (self.tree.nodeTag(parts[0]) != .number_literal or self.tree.nodeTag(parts[1]) != .number_literal)
                return .unknown;
        }
        return .{ .integer = .{ .min = low, .max = high } };
    }

    fn builtinCall(self: *Evaluator, node: Ast.Node.Index) Range {
        var buffer: [2]Ast.Node.Index = undefined;
        const params = self.tree.builtinCallParams(&buffer, node) orelse return .unknown;
        const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
        if (std.mem.eql(u8, name, "@as") and params.len == 2)
            return self.coerce(self.evaluate(params[1]), params[1], params[0]);
        if (params.len == 1 and (std.mem.eql(u8, name, "@intCast") or std.mem.eql(u8, name, "@floatCast")))
            return self.coerce(self.evaluate(params[0]), params[0], node);
        if (params.len == 1 and std.mem.eql(u8, name, "@floatFromInt"))
            return self.evaluate(params[0]).asFloat(self.floatBits(node) orelse 0);
        if (params.len == 2 and (std.mem.eql(u8, name, "@min") or std.mem.eql(u8, name, "@max")))
            return self.minimumMaximum(node, params[0], params[1], std.mem.eql(u8, name, "@min"));
        if (params.len == 2 and std.mem.eql(u8, name, "@divTrunc"))
            return self.evaluate(params[0]).binary(self.evaluate(params[1]), .div);
        if (params.len == 1 and (std.mem.eql(u8, name, "@clz") or std.mem.eql(u8, name, "@ctz") or
            std.mem.eql(u8, name, "@popCount")))
        {
            if (self.cache) |cache| {
                if (cache.intInfoOf(params[0])) |info| return .{ .integer = .{ .min = 0, .max = info.bits } };
            }
        }
        if (params.len == 1) return self.floatBuiltin(node, name, params[0]);
        return self.typeRange(node);
    }

    fn minimumMaximum(self: *Evaluator, node: Ast.Node.Index, left: Ast.Node.Index, right: Ast.Node.Index, minimum: bool) Range {
        var a = self.evaluate(left);
        var b = self.evaluate(right);
        if (a == .unknown or b == .unknown or a == .floating or b == .floating) {
            const bits = self.floatBits(node) orelse return .unknown;
            a = a.asFloat(bits);
            b = b.asFloat(bits);
        }
        return a.binary(b, if (minimum) .minimum else .maximum);
    }

    fn floatBuiltin(self: *Evaluator, node: Ast.Node.Index, name: []const u8, operand: Ast.Node.Index) Range {
        const value = self.evaluate(operand);
        if (value != .floating) return self.typeRange(node);
        var result = value.floating;
        result.min_open = false;
        result.max_open = false;
        if (std.mem.eql(u8, name, "@abs")) {
            const lower = @abs(result.min);
            const upper = @abs(result.max);
            result.min = if (result.min <= 0 and result.max >= 0) 0 else @min(lower, upper);
            result.max = @max(lower, upper);
        } else if (std.mem.eql(u8, name, "@sqrt")) {
            result.no_nan = result.no_nan and result.min >= 0;
            result.min = std.math.nextAfter(f128, @sqrt(@max(result.min, 0)), -std.math.inf(f128));
            result.max = std.math.nextAfter(f128, @sqrt(@max(result.max, 0)), std.math.inf(f128));
        } else if (std.mem.eql(u8, name, "@floor")) {
            result.min = @floor(result.min);
            result.max = @floor(result.max);
        } else if (std.mem.eql(u8, name, "@ceil")) {
            result.min = @ceil(result.min);
            result.max = @ceil(result.max);
        } else if (std.mem.eql(u8, name, "@trunc")) {
            result.min = @trunc(result.min);
            result.max = @trunc(result.max);
        } else if (std.mem.eql(u8, name, "@round")) {
            result.min = @round(result.min);
            result.max = @round(result.max);
        } else return self.typeRange(node);
        return (Range{ .floating = result }).asFloat(self.floatBits(node) orelse 128);
    }

    fn standardCall(self: *Evaluator, node: Ast.Node.Index) Range {
        if (!self.std_valid) return self.typeRange(node);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = self.tree.fullCall(&buffer, node).?;
        const name = path(self.tree, call.ast.fn_expr) orelse return self.typeRange(node);
        const params = call.ast.params;
        if (params.len == 1 and std.mem.eql(u8, name, "std.math.inf"))
            return Range.floatConstant(std.math.inf(f128));
        if (params.len == 1 and std.mem.eql(u8, name, "std.math.nan")) return .{ .floating = .{} };
        if (params.len == 1 and (std.mem.eql(u8, name, "std.math.minInt") or std.mem.eql(u8, name, "std.math.maxInt"))) {
            const target = self.typeRange(params[0]);
            if (target != .integer) return .unknown;
            return Range.constant(if (std.mem.eql(u8, name, "std.math.minInt")) target.integer.min else target.integer.max);
        }
        if (params.len == 3 and std.mem.eql(u8, name, "std.math.clamp")) {
            const bits = self.floatBits(node) orelse return .unknown;
            const value = self.evaluate(params[0]).asFloat(bits);
            const lower = self.evaluate(params[1]).asFloat(bits);
            const upper = self.evaluate(params[2]).asFloat(bits);
            return value.binary(upper, .minimum).binary(lower, .maximum);
        }
        return self.typeRange(node);
    }
};

/// Wrappers one path peel may undo before it declines.
///
/// A peel is SYNTACTIC, not a descent: it only unwraps `(…)`, `.field` and
/// `.*`, and each of those steps strictly shortens the token span, so it cannot
/// loop and it consumes no step.  The cap is therefore not a walk-depth bound
/// and must not be reported as one — it is the same NUMBER the module spends on
/// a real descent (`Evaluator.frame_cap`) so this file has one depth in it
/// rather than two spellings of it, and a peel that reaches the cap gives the
/// same answer a peel that found no identifier gives: null, which proves
/// nothing.  Nothing that was provable before stops being provable.
const max_path_peel: usize = Evaluator.frame_cap;

pub fn path(tree: *const Ast, original: Ast.Node.Index) ?[]const u8 {
    const node = ungroup(tree, original);
    var part = node;
    for (0..max_path_peel) |_| {
        switch (tree.nodeTag(part)) {
            .identifier => {
                const first = tree.firstToken(node);
                const last = tree.lastToken(node);
                return tree.source[tree.tokenStart(first) .. tree.tokenStart(last) + tree.tokenSlice(last).len];
            },
            .field_access => part = tree.nodeData(part).node_and_token[0],
            .deref => part = tree.nodeData(part).node,
            .grouped_expression => part = tree.nodeData(part).node_and_token[0],
            else => return null,
        }
    }
    return null;
}

fn ungroup(tree: *const Ast, original: Ast.Node.Index) Ast.Node.Index {
    var node = original;
    for (0..max_path_peel) |_| {
        if (tree.nodeTag(node) != .grouped_expression) return node;
        node = tree.nodeData(node).node_and_token[0];
    }
    return node;
}

pub const Constraint = struct { node: Ast.Node.Index, value: Range };

/// What a std math finiteness predicate adds to the value it is handed: a
/// proven `std.math.isFinite(x)` also rules out an infinite bound, a proven
/// `std.math.isNan(x)` being false rules out NaN alone.
pub const Finiteness = enum { finite, not_nan };

/// The nodes `refine` records a fact under, in recording order; `count == 0`
/// means it records nothing for that condition.
///
/// A caller that has to NAME what a proved condition left behind has to be
/// reading the set the recording writes under, so `refine` reads this rather
/// than the other way round — one switch is the only place that can say so.
/// Both shapes are here: a comparison records under each of its OPERANDS, and
/// a call-shaped finiteness predicate under the argument it was handed.
pub const Targets = struct {
    nodes: [2]Ast.Node.Index = undefined,
    count: u2 = 0,
    /// Read only when `count == 1`, the call shape.
    finiteness: Finiteness = .not_nan,

    pub const none: Targets = .{ .count = 0 };

    pub fn slice(self: *const Targets) []const Ast.Node.Index {
        return self.nodes[0..self.count];
    }
};

/// The std math predicates `refine` records a finiteness fact for, and what
/// each records.  The polarity matters: `isFinite` says something only when it
/// holds, `isNan` only when it does not.
fn finitenessOf(name: []const u8, truth: bool) ?Finiteness {
    if (std.mem.eql(u8, name, "std.math.isFinite")) return if (truth) .finite else null;
    if (std.mem.eql(u8, name, "std.math.isNan")) return if (truth) null else .not_nan;
    return null;
}

pub fn recordedTargets(
    evaluation: *Evaluator,
    original: Ast.Node.Index,
    truth: bool,
) Targets {
    const tree = evaluation.tree;
    return targetsAt(tree, ungroup(tree, original), evaluation.std_valid, truth);
}

fn targetsAt(tree: *const Ast, node: Ast.Node.Index, std_valid: bool, truth: bool) Targets {
    var call_buffer: [1]Ast.Node.Index = undefined;
    if (tree.fullCall(&call_buffer, node)) |call| {
        if (!std_valid or call.ast.params.len != 1) return .none;
        const finiteness = finitenessOf(path(tree, call.ast.fn_expr) orelse return .none, truth) orelse
            return .none;
        return .{ .nodes = .{ call.ast.params[0], undefined }, .count = 1, .finiteness = finiteness };
    }
    if (comparison(tree.nodeTag(node), truth) == null) return .none;
    return .{ .nodes = tree.nodeData(node).node_and_node, .count = 2 };
}

pub fn refine(evaluation: *Evaluator, original: Ast.Node.Index, truth: bool) [2]?Constraint {
    const tree = evaluation.tree;
    const node = ungroup(tree, original);
    const tag = tree.nodeTag(node);
    const targets = targetsAt(tree, node, evaluation.std_valid, truth);
    if (targets.count == 0) return .{ null, null };
    // A finiteness predicate records under the one value it was handed.
    if (targets.count == 1) {
        var value = evaluation.evaluate(targets.nodes[0]);
        if (value != .floating) value = .{ .floating = .{} };
        value.floating.no_nan = true;
        if (targets.finiteness == .finite) {
            if (std.math.isInf(value.floating.min)) value.floating.min_open = true;
            if (std.math.isInf(value.floating.max)) value.floating.max_open = true;
        }
        return .{ .{ .node = targets.nodes[0], .value = value }, null };
    }
    const op = comparison(tag, truth) orelse return .{ null, null };
    const parts = tree.nodeData(node).node_and_node;
    const left = evaluation.evaluate(parts[0]);
    const right = evaluation.evaluate(parts[1]);
    if (path(tree, parts[0])) |key| {
        if (path(tree, parts[1])) |other| {
            if (std.mem.eql(u8, key, other) and
                ((tag == .equal_equal and truth) or (tag == .bang_equal and !truth)))
            {
                var value = left;
                if (value == .unknown) value = .{ .floating = .{} };
                if (value == .floating) value.floating.no_nan = true;
                return .{ .{ .node = parts[0], .value = value }, null };
            }
        }
    }
    return .{
        .{ .node = parts[0], .value = constrained(evaluation, parts[0], left, right, op, tag, truth) },
        .{ .node = parts[1], .value = constrained(evaluation, parts[1], right, left, reverse(op), tag, truth) },
    };
}

const Comparison = enum { lt, le, gt, ge, eq, ne };

fn comparison(tag: Ast.Node.Tag, truth: bool) ?Comparison {
    return switch (tag) {
        .less_than => if (truth) .lt else .ge,
        .less_or_equal => if (truth) .le else .gt,
        .greater_than => if (truth) .gt else .le,
        .greater_or_equal => if (truth) .ge else .lt,
        .equal_equal => if (truth) .eq else .ne,
        .bang_equal => if (truth) .ne else .eq,
        else => null,
    };
}

fn reverse(op: Comparison) Comparison {
    return switch (op) {
        .lt => .gt,
        .le => .ge,
        .gt => .lt,
        .ge => .le,
        .eq => .eq,
        .ne => .ne,
    };
}

fn constrained(
    evaluation: *Evaluator,
    node: Ast.Node.Index,
    value: Range,
    limit: Range,
    op: Comparison,
    tag: Ast.Node.Tag,
    truth: bool,
) Range {
    if (value == .integer and limit == .integer) return constrainInteger(value.integer, limit.integer, op);
    const bits = evaluation.floatBits(node) orelse 0;
    const current = if (value == .floating) value.floating else value.asFloat(bits).floating;
    const boundary = limit.asFloat(bits).floating;
    const ordered = (truth and tag != .bang_equal) or (!truth and tag == .bang_equal);
    return constrainFloat(current, boundary, op, ordered);
}

fn constrainInteger(original: numbers.Integer, limit: numbers.Integer, op: Comparison) Range {
    var value = original;
    switch (op) {
        .lt => value.max = @min(value.max, std.math.sub(i128, limit.max, 1) catch return .unknown),
        .le => value.max = @min(value.max, limit.max),
        .gt => value.min = @max(value.min, std.math.add(i128, limit.min, 1) catch return .unknown),
        .ge => value.min = @max(value.min, limit.min),
        .eq => {
            value.min = @max(value.min, limit.min);
            value.max = @min(value.max, limit.max);
        },
        .ne => if (limit.min == limit.max) {
            if (value.min == limit.min) value.min = std.math.add(i128, value.min, 1) catch return .unknown;
            if (value.max == limit.max) value.max = std.math.sub(i128, value.max, 1) catch return .unknown;
        },
    }
    if (value.min > value.max) return .unknown;
    return .{ .integer = value };
}

fn constrainFloat(original: numbers.Floating, limit: numbers.Floating, op: Comparison, ordered: bool) Range {
    if (!ordered and !limit.no_nan) return .{ .floating = original };
    var value = original;
    if (ordered) value.no_nan = true;
    switch (op) {
        .lt, .le => {
            if (limit.max <= value.max) {
                const open = (op == .lt) or limit.max_open;
                value.max_open = open or (limit.max == value.max and value.max_open);
                value.max = limit.max;
            }
        },
        .gt, .ge => {
            if (limit.min >= value.min) {
                const open = (op == .gt) or limit.min_open;
                value.min_open = open or (limit.min == value.min and value.min_open);
                value.min = limit.min;
            }
        },
        .eq => return (Range{ .floating = value }).intersect(.{ .floating = limit }),
        .ne => if (limit.min == limit.max and limit.no_nan) {
            if (value.min == limit.min) value.min_open = true;
            if (value.max == limit.max) value.max_open = true;
        },
    }
    if (value.min > value.max) return .unknown;
    return .{ .floating = value };
}

// ── Tests ────────────────────────────────────────────────────────
// These drive the evaluator with no type cache, so what they pin is the
// switch dispatch itself: the union of the arms, the prong that catches
// the rest, and an arm that cannot be read taking the answer with it.

/// The range of the first switch expression in `source`, evaluated with
/// no type cache: every arm the fixtures write is either a literal or a
/// name only a cache could resolve, so nothing here but the arms
/// decides the answer.
fn switchRange(gpa: std.mem.Allocator, source: [:0]const u8) !Range {
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const node = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .@"switch" or tag == .switch_comma) break @as(Ast.Node.Index, @enumFromInt(index));
    } else return error.NoSwitch;
    var budget: u32 = Evaluator.frame_cap;
    var evaluation: Evaluator = .{
        .tree = &tree,
        .cache = null,
        .facts = &.{},
        .budget = &budget,
        .std_valid = true,
    };
    return evaluation.evaluate(node);
}

fn integerOf(value: Range) error{NotAnInteger}!numbers.Integer {
    return switch (value) {
        .integer => |bounds| bounds,
        else => error.NotAnInteger,
    };
}

test "a switch expression reads as the union of every arm" {
    const gpa = std.testing.allocator;
    const source = try gpa.dupeZ(u8,
        \\const Format = enum { half, single, double };
        \\fn biasOf(format: Format) i32 {
        \\    return switch (format) {
        \\        .half => 15,
        \\        .single => 127,
        \\        .double => 1023,
        \\    };
        \\}
    );
    defer gpa.free(source);
    // Every arm may be the one that runs: no discriminant has been read,
    // so the range spans all three and neither end of the type does.
    try std.testing.expectEqual(
        numbers.Integer{ .min = 15, .max = 1023 },
        try integerOf(try switchRange(gpa, source)),
    );
}

test "a switch expression keeps the prong that catches the rest" {
    const gpa = std.testing.allocator;
    const source = try gpa.dupeZ(u8,
        \\fn scale(large: bool) i32 {
        \\    return switch (large) {
        \\        true => 1,
        \\        else => 1000,
        \\    };
        \\}
    );
    defer gpa.free(source);
    // The catch-all runs whenever no tagged prong does, so answering with
    // the tagged arm alone would be narrower than the switch really is.
    try std.testing.expectEqual(
        numbers.Integer{ .min = 1, .max = 1000 },
        try integerOf(try switchRange(gpa, source)),
    );
}

test "a switch expression does not drop an arm it cannot read" {
    const gpa = std.testing.allocator;
    const source = try gpa.dupeZ(u8,
        \\const Format = enum { half, single, double };
        \\const Spec = struct { bias: i32 };
        \\fn biasOf(format: Format, spec: *const Spec) i32 {
        \\    return switch (format) {
        \\        .half => 15,
        \\        .single => spec.bias,
        \\        .double => 1023,
        \\    };
        \\}
    );
    defer gpa.free(source);
    // `spec.bias` is a field only the cache could resolve.  Joining the
    // two readable arms and skipping it would answer `[15, 1023]` for a
    // switch that can also yield whatever the caller put in the struct.
    try std.testing.expect((try switchRange(gpa, source)) == .unknown);
}
