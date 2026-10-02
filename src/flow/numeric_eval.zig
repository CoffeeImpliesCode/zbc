//! Bounded numeric expression evaluation over resolved types and path facts.
const std = @import("std");
const Ast = std.zig.Ast;
const numbers = @import("numeric_range.zig");
const FileCache = @import("../cache/file_cache.zig").FileCache;
const Range = numbers.Range;

pub const Fact = struct { name: []const u8, value: Range };

pub const Evaluator = struct {
    tree: *const Ast,
    cache: ?*FileCache,
    facts: []const Fact,
    budget: *u32,
    std_valid: bool,
    depth: u8 = 0,

    pub fn evaluate(self: *Evaluator, original: Ast.Node.Index) Range {
        if (self.depth == 64 or self.budget.* == 0) {
            self.budget.* = 0;
            return .unknown;
        }
        self.budget.* -= 1;
        self.depth += 1;
        defer self.depth -= 1;
        const node = ungroup(self.tree, original);
        if (path(self.tree, node)) |name| {
            for (self.facts) |fact| {
                if (!std.mem.eql(u8, fact.name, name)) continue;
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
    /// path fact: a fixed array's own length, a compile-time integer, or
    /// otherwise the declared type.  This is the outer bound every fact for
    /// the same node is measured against.
    fn declaredRange(self: *Evaluator, node: Ast.Node.Index) Range {
        if (self.tree.nodeTag(node) == .field_access) {
            const parts = self.tree.nodeData(node).node_and_token;
            if (std.mem.eql(u8, self.tree.tokenSlice(parts[1]), "len")) {
                if (self.cache) |cache| {
                    if (cache.fixedArrayLenOf(parts[0])) |length| return Range.constant(length);
                }
            }
        }
        if (self.cache) |cache| {
            if (cache.comptimeIntValueOf(node)) |value| return Range.constant(value);
        }
        return self.typeRange(node);
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

pub fn path(tree: *const Ast, original: Ast.Node.Index) ?[]const u8 {
    const node = ungroup(tree, original);
    var part = node;
    for (0..64) |_| {
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
    for (0..64) |_| {
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

    pub fn slice(self: Targets) []const Ast.Node.Index {
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
