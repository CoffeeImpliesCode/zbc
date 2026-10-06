//! Numeric intervals used by the forward range analysis.
//! Integer operations are checked. Floating arithmetic rounds bounds outward.
const std = @import("std");
const inf = std.math.inf(f128);

pub const Integer = struct {
    min: i128,
    max: i128,
};

pub const Floating = struct {
    min: f128 = -inf,
    max: f128 = inf,
    min_open: bool = false,
    max_open: bool = false,
    no_nan: bool = false,

    pub fn fitsInteger(self: Floating, bits: u16, signed: bool) bool {
        if (!self.no_nan or bits > 128) return false;
        const high = powerOfTwo(if (signed and bits > 0) bits - 1 else bits);
        const low = if (signed and bits > 0) -high else 0;
        // Truncation toward zero also admits the open unit interval below
        // the minimum integer. Keep a conservative bound for wide integers.
        const lower = if (bits <= 64) low - 1 else low;
        const lower_ok = self.min > lower or (self.min == lower and
            (self.min_open or bits > 64));
        const upper_ok = self.max < high or (self.max == high and self.max_open);
        return lower_ok and upper_ok;
    }
};

/// Decode an upper bound on masked IEEE bits without assuming omitted bits are zero.
pub fn ieeeFloatRange(width: u8, mask: u64, value: Range, absolute: bool) Range {
    const infinity_bits: u64 = switch (width) {
        16 => 0x7c00,
        32 => 0x7f800000,
        64 => 0x7ff0000000000000,
        else => return .unknown,
    };
    if (value != .integer or value.integer.min < 0) return .unknown;
    const sign = @as(u64, 1) << @as(u6, @intCast(width - 1));
    const magnitude_mask = sign - 1;
    const full_mask = sign | magnitude_mask;
    if (mask & ~full_mask != 0 or value.integer.min > full_mask) return .unknown;
    var maximum: u64 = @intCast(@min(value.integer.max, full_mask));
    const minimum: u64 = @intCast(value.integer.min);
    const positive = mask & sign != 0 and maximum < sign;
    const negative = mask & sign != 0 and minimum >= sign;
    if (mask & sign != 0 and !positive and !negative) return .unknown;
    const forbidden = maximum & ~mask;
    if (forbidden != 0) {
        const bit = @as(u64, 1) << @as(u6, @intCast(63 - @clz(forbidden)));
        const lower = bit - 1;
        maximum = (maximum & ~(lower | bit)) | (mask & lower);
    }
    const magnitude = (maximum & magnitude_mask) | (~mask & magnitude_mask);
    if (magnitude >= infinity_bits) return .unknown;
    const upper: f128 = switch (width) {
        16 => @floatCast(@as(f16, @bitCast(@as(u16, @intCast(magnitude))))),
        32 => @floatCast(@as(f32, @bitCast(@as(u32, @intCast(magnitude))))),
        64 => @floatCast(@as(f64, @bitCast(magnitude))),
        else => unreachable,
    };
    return .{ .floating = .{
        .min = if (positive and !absolute) 0 else -upper,
        .max = if (negative and !absolute) 0 else upper,
        .no_nan = true,
    } };
}

pub const Operation = enum { add, sub, mul, div, minimum, maximum };

pub const Range = union(enum) {
    unknown,
    integer: Integer,
    floating: Floating,

    pub fn constant(value: i128) Range {
        return .{ .integer = .{ .min = value, .max = value } };
    }

    pub fn floatConstant(value: f128) Range {
        if (std.math.isNan(value)) return .{ .floating = .{} };
        return .{ .floating = .{ .min = value, .max = value, .no_nan = true } };
    }

    pub fn integerType(bits: u16, signed: bool) Range {
        if (bits == 0) return constant(0);
        if (bits > 128 or (!signed and bits == 128)) return .unknown;
        if (bits == 128) return .{ .integer = .{
            .min = std.math.minInt(i128), .max = std.math.maxInt(i128),
        } };
        if (bits == 127 and !signed) return .{ .integer = .{
            .min = 0, .max = std.math.maxInt(i128),
        } };
        const shift: u7 = @intCast(if (signed) bits - 1 else bits);
        const high = @as(i128, 1) << shift;
        return .{ .integer = .{ .min = if (signed) -high else 0, .max = high - 1 } };
    }

    pub fn fitsInteger(self: Range, bits: u16, signed: bool) bool {
        return switch (self) {
            .unknown => false,
            .floating => |value| value.fitsInteger(bits, signed),
            .integer => |value| blk: {
                if (signed and bits >= 128) break :blk true;
                if (!signed and bits >= 127) break :blk value.min >= 0;
                const target = integerType(bits, signed);
                if (target != .integer) break :blk false;
                break :blk value.min >= target.integer.min and value.max <= target.integer.max;
            },
        };
    }

    pub fn exactInF32(self: Range) bool {
        if (self != .integer) return false;
        const value = self.integer;
        if (value.min >= -16777216 and value.max <= 16777216) return true;
        if (value.min != value.max) return false;
        const magnitude = @abs(value.min);
        std.debug.assert(magnitude != 0);
        return 128 - @clz(magnitude) - @ctz(magnitude) <= 24;
    }

    pub fn join(a: Range, b: Range) Range {
        if (a == .integer and b == .integer) return .{ .integer = .{
            .min = @min(a.integer.min, b.integer.min), .max = @max(a.integer.max, b.integer.max),
        } };
        if (a != .floating or b != .floating) return .unknown;
        const x = a.floating;
        const y = b.floating;
        return .{ .floating = .{
            .min = @min(x.min, y.min), .max = @max(x.max, y.max),
            .min_open = if (x.min < y.min) x.min_open else if (y.min < x.min) y.min_open else x.min_open and y.min_open,
            .max_open = if (x.max > y.max) x.max_open else if (y.max > x.max) y.max_open else x.max_open and y.max_open,
            .no_nan = x.no_nan and y.no_nan,
        } };
    }

    pub fn intersect(a: Range, b: Range) Range {
        if (a == .unknown) return b;
        if (b == .unknown) return a;
        if (a == .integer and b == .integer) {
            const low = @max(a.integer.min, b.integer.min);
            const high = @min(a.integer.max, b.integer.max);
            if (low > high) return .unknown;
            return .{ .integer = .{ .min = low, .max = high } };
        }
        if (a != .floating or b != .floating) return .unknown;
        const x = a.floating;
        const y = b.floating;
        const low = @max(x.min, y.min);
        const high = @min(x.max, y.max);
        if (low > high) return .unknown;
        return .{ .floating = .{
            .min = low, .max = high,
            .min_open = if (x.min > y.min) x.min_open else if (y.min > x.min) y.min_open else x.min_open or y.min_open,
            .max_open = if (x.max < y.max) x.max_open else if (y.max < x.max) y.max_open else x.max_open or y.max_open,
            .no_nan = x.no_nan or y.no_nan,
        } };
    }

    pub fn negate(self: Range) Range {
        return switch (self) {
            .unknown => .unknown,
            .integer => |value| .{ .integer = .{
                .min = std.math.negate(value.max) catch return .unknown,
                .max = std.math.negate(value.min) catch return .unknown,
            } },
            .floating => |value| .{ .floating = .{
                .min = -value.max, .max = -value.min,
                .min_open = value.max_open, .max_open = value.min_open, .no_nan = value.no_nan,
            } },
        };
    }

    pub fn asFloat(self: Range, bits: u16) Range {
        var value: Floating = switch (self) {
            .unknown => return .{ .floating = .{} },
            .floating => |floating| floating,
            .integer => |integer| blk: {
                const exact: i128 = @as(i128, 1) << 113;
                const low: f128 = @floatFromInt(integer.min);
                const high: f128 = @floatFromInt(integer.max);
                break :blk .{
                    .min = if (integer.min >= -exact and integer.min <= exact) low else outward(low, false),
                    .max = if (integer.max >= -exact and integer.max <= exact) high else outward(high, true),
                    .no_nan = true,
                };
            },
        };
        if (bits != 16 and bits != 32 and bits != 64 and bits != 80 and bits != 128)
            return .{ .floating = .{ .no_nan = value.no_nan } };
        value.min = roundToFormat(value.min, bits);
        value.max = roundToFormat(value.max, bits);
        // A cast can round an excluded endpoint into an included value.
        value.min_open = false;
        value.max_open = false;
        return .{ .floating = value };
    }

    pub fn binary(a: Range, b: Range, op: Operation) Range {
        if (a == .integer and b == .integer) return integerBinary(a.integer, b.integer, op);
        if (a == .unknown or b == .unknown) return .unknown;
        const x = if (a == .floating) a.floating else a.asFloat(128).floating;
        const y = if (b == .floating) b.floating else b.asFloat(128).floating;
        return floatBinary(x, y, op);
    }
};

fn integerBinary(a: Integer, b: Integer, op: Operation) Range {
    const value: Integer = switch (op) {
        .add => .{
            .min = std.math.add(i128, a.min, b.min) catch return .unknown,
            .max = std.math.add(i128, a.max, b.max) catch return .unknown,
        },
        .sub => .{
            .min = std.math.sub(i128, a.min, b.max) catch return .unknown,
            .max = std.math.sub(i128, a.max, b.min) catch return .unknown,
        },
        .minimum => .{ .min = @min(a.min, b.min), .max = @min(a.max, b.max) },
        .maximum => .{ .min = @max(a.min, b.min), .max = @max(a.max, b.max) },
        .mul, .div => return integerCorners(a, b, op),
    };
    return .{ .integer = value };
}

fn integerCorners(a: Integer, b: Integer, op: Operation) Range {
    if (op == .div and b.min <= 0 and b.max >= 0) return .unknown;
    var low: i128 = std.math.maxInt(i128);
    var high: i128 = std.math.minInt(i128);
    for ([_]i128{ a.min, a.max }) |left| {
        for ([_]i128{ b.min, b.max }) |right| {
            const value = switch (op) {
                .mul => std.math.mul(i128, left, right) catch return .unknown,
                .div => blk: {
                    if (left == std.math.minInt(i128) and right == -1) return .unknown;
                    break :blk @divTrunc(left, right);
                },
                else => unreachable,
            };
            low = @min(low, value);
            high = @max(high, value);
        }
    }
    return .{ .integer = .{ .min = low, .max = high } };
}

fn floatBinary(a: Floating, b: Floating, op: Operation) Range {
    if (op == .minimum or op == .maximum) return floatMinMax(a, b, op);
    if (!std.math.isFinite(a.min) or !std.math.isFinite(a.max) or
        !std.math.isFinite(b.min) or !std.math.isFinite(b.max)) return .{ .floating = .{} };
    if (op == .div and b.min <= 0 and b.max >= 0) return .{ .floating = .{} };
    var low: f128 = inf;
    var high: f128 = -inf;
    for ([_]f128{ a.min, a.max }) |left| {
        for ([_]f128{ b.min, b.max }) |right| {
            const value = switch (op) {
                .add => left + right,
                .sub => left - right,
                .mul => left * right,
                .div => left / right,
                else => unreachable,
            };
            if (std.math.isNan(value)) return .{ .floating = .{} };
            low = @min(low, value);
            high = @max(high, value);
        }
    }
    return .{ .floating = .{
        .min = outward(low, false), .max = outward(high, true),
        .no_nan = a.no_nan and b.no_nan,
    } };
}

fn floatMinMax(a: Floating, b: Floating, op: Operation) Range {
    const minimum = op == .minimum;
    var low = if (minimum) @min(a.min, b.min) else @max(a.min, b.min);
    var high = if (minimum) @min(a.max, b.max) else @max(a.max, b.max);
    // If either operand can be NaN, Zig selects the other operand.
    if (!a.no_nan) { low = @min(low, b.min); high = @max(high, b.max); }
    if (!b.no_nan) { low = @min(low, a.min); high = @max(high, a.max); }
    return .{ .floating = .{ .min = low, .max = high, .no_nan = a.no_nan or b.no_nan } };
}

fn outward(value: f128, up: bool) f128 {
    return std.math.nextAfter(f128, value, if (up) inf else -inf);
}

fn roundToFormat(value: f128, bits: u16) f128 {
    return switch (bits) {
        16 => @as(f16, @floatCast(value)),
        32 => @as(f32, @floatCast(value)),
        64 => @as(f64, @floatCast(value)),
        80 => @as(f80, @floatCast(value)),
        128 => value,
        else => unreachable,
    };
}

pub fn powerOfTwo(exponent: u16) f128 {
    std.debug.assert(exponent <= 128);
    return std.math.scalbn(@as(f128, 1), @as(i32, exponent));
}

test "numeric intervals preserve inclusive and exclusive integer conversion bounds" {
    const high = powerOfTwo(64);
    const inclusive: Floating = .{ .min = 0, .max = high, .no_nan = true };
    try std.testing.expect(!inclusive.fitsInteger(64, false));
    var exclusive = inclusive;
    exclusive.max_open = true;
    try std.testing.expect(exclusive.fitsInteger(64, false));
    exclusive.no_nan = false;
    try std.testing.expect(!exclusive.fitsInteger(64, false));
    try std.testing.expect(Range.floatConstant(-0.5).fitsInteger(8, false));
    try std.testing.expect(!Range.floatConstant(-1).fitsInteger(8, false));
}

test "numeric intervals do not overflow their analysis representation" {
    const largest = Range.constant(std.math.maxInt(i128));
    try std.testing.expect(largest.binary(Range.constant(1), .add) == .unknown);
    try std.testing.expect(Range.constant(std.math.minInt(i128)).negate() == .unknown);
    try std.testing.expect(Range.integerType(25, true).exactInF32());
    try std.testing.expect(!Range.constant(16777217).exactInF32());
    const unsigned127 = Range.integerType(127, false);
    try std.testing.expectEqual(@as(i128, 0), unsigned127.integer.min);
    try std.testing.expectEqual(std.math.maxInt(i128), unsigned127.integer.max);
}

test "numeric clipping models NaN selection without accepting one sided bounds" {
    const unknown: Range = .{ .floating = .{} };
    const low = unknown.binary(Range.floatConstant(0), .maximum);
    const high = unknown.binary(Range.floatConstant(255), .minimum);
    try std.testing.expect(!low.fitsInteger(8, false));
    try std.testing.expect(!high.fitsInteger(8, false));
    try std.testing.expect(low.binary(Range.floatConstant(255), .minimum).fitsInteger(8, false));
}

test "f32 exactness includes representable isolated integers beyond consecutive coverage" {
    const power: i128 = @as(i128, 1) << 30;
    try std.testing.expect(Range.constant(power).exactInF32());
    try std.testing.expect(Range.constant(-power).exactInF32());
    try std.testing.expect(!Range.constant(power + 1).exactInF32());
    try std.testing.expect(!Range.constant(-power - 1).exactInF32());
    try std.testing.expect(Range.constant(std.math.minInt(i128)).exactInF32());
    try std.testing.expect(!Range.constant(std.math.minInt(i128) + 1).exactInF32());
    const interval: Range = .{ .integer = .{ .min = power, .max = power + 128 } };
    try std.testing.expect(!interval.exactInF32());
}

test "wide integer destinations admit known bounds without admitting negative unsigned inputs" {
    const positive = Range.constant(std.math.maxInt(i128));
    try std.testing.expect(positive.fitsInteger(128, false));
    try std.testing.expect(positive.fitsInteger(256, true));
    try std.testing.expect(!Range.constant(-1).fitsInteger(128, false));
    try std.testing.expect(!positive.fitsInteger(64, false));
}

test "IEEE mask bounds contain every admitted binary16 value" {
    const Case = struct { mask: u16, min: u16 = 0, max: u16 };
    const cases = [_]Case{
        .{ .mask = 0x7fff, .max = 0x3c00 },
        .{ .mask = 0x7c00, .max = 0x3c01 },
        .{ .mask = 0x7c00, .max = 0x3bff },
        .{ .mask = 0x7d55, .max = 0x3caa },
        .{ .mask = 0xffff, .max = 0x3c00 },
        .{ .mask = 0xffff, .min = 0x8000, .max = 0xbc00 },
    };
    for (cases) |case| {
        const range = ieeeFloatRange(16, case.mask, .{ .integer = .{
            .min = case.min, .max = case.max,
        } }, false);
        try std.testing.expect(range == .floating);
        try std.testing.expect(range.floating.no_nan);
        for (0..65536) |raw| {
            const bits: u16 = @intCast(raw);
            const masked = bits & case.mask;
            if (masked < case.min or masked > case.max) continue;
            const value: f128 = @floatCast(@as(f16, @bitCast(bits)));
            try std.testing.expect(value >= range.floating.min);
            try std.testing.expect(value <= range.floating.max);
        }
    }
}
