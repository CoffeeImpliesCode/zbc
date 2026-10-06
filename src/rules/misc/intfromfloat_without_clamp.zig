//! Report float-to-integer conversions without a proved finite conversion range.
//! Rounding, a helper name, or a nearby comparison is not a range proof.
const std = @import("std");
const Ast = std.zig.Ast;
const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");
const testing = @import("../../testing.zig");
const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "intfromfloat-without-clamp";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .intfromfloat_without_clamp)) return;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const token = tree.nodeMainToken(node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "@intFromFloat")) continue;
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        if (!tokens.isRuntimeUse(tree, declaration, token)) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, node).?;
        if (params.len != 1) continue;
        if (cache.intInfoOf(node)) |destination| {
            const bounds = try value_range.boundsAt(gpa, tree, tokens.bodyOf(tree, declaration).?, params[0], token, cache);
            if (bounds.fitsInteger(destination.bits, destination.signed)) continue;
        }
        const message = try gpa.dupe(u8,
            "a finite value within the destination conversion range was not proved for `@intFromFloat`; NaN, infinity, or an out-of-range value traps in Debug/ReleaseSafe and causes undefined behavior in unchecked builds");
        errdefer gpa.free(message);
        try problems.append(gpa, .{
            .rule_id = R,
            .severity = .warning,
            .start = Pos.fromTokenStart(tree, token),
            .end = Pos.fromTokenEnd(tree, tree.lastToken(node)),
            .message = message,
        });
    }
}

test "intfromfloat-without-clamp: bare conversion remains uncertain" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: f64) i64 { return @intFromFloat(value); }
    );
}

test "intfromfloat-without-clamp: and-range excludes NaN and out-of-range values" {
    try testing.expectNoFireTyped(check,
        \\fn convert(value: f64) ?i32 {
        \\    if (!(value >= -2147483648.0 and value < 2147483648.0)) return null;
        \\    const result: i32 = @intFromFloat(value);
        \\    return result;
        \\}
    );
}

test "intfromfloat-without-clamp: OR exit guard still admits NaN" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: f64) u8 {
        \\    if (value < 0.0 or value >= 256.0) return 0;
        \\    return @intFromFloat(value);
        \\}
    );
}

test "intfromfloat-without-clamp: one-sided clipping leaves invalid inputs" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: f64) u8 { return @intFromFloat(@min(value, 255.0)); }
    );
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: f64) u8 { return @intFromFloat(@max(value, 0.0)); }
    );
}

test "intfromfloat-without-clamp: rounding does not prove a finite range" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: f64) u8 { return @intFromFloat(@floor(value)); }
    );
}

test "intfromfloat-without-clamp: a guard must match the destination range" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: f64) u8 {
        \\    if (value >= 0.0 and value < 512.0) return @intFromFloat(value);
        \\    return 0;
        \\}
    );
}

test "intfromfloat-without-clamp: dominating finite bounds prove conversion" {
    try testing.expectNoFireTyped(check,
        \\fn convert(value: f64) u8 {
        \\    if (value != value) return 0;
        \\    if (value < 0.0) return 0;
        \\    if (value >= 256.0) return 0;
        \\    return @intFromFloat(value);
        \\}
    );
}

test "intfromfloat-without-clamp: standard clipping proves both bounds including NaN" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn convert(value: f64) u8 { return @intFromFloat(std.math.clamp(value, 0.0, 255.0)); }
    );
}

test "intfromfloat-without-clamp: clamp spelling does not supply a contract" {
    try testing.expectFiresTyped(check, R,
        \\fn clamp(value: f64) f64 { return value; }
        \\fn convert(value: f64) u8 { return @intFromFloat(clamp(value)); }
    );
}

test "intfromfloat-without-clamp: standard clamp selects its upper bound for NaN" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn convert(value: f64) u8 {
        \\    if (value < 0.0 or value > 2.0) return 0;
        \\    return @intFromFloat(std.math.clamp(value, 0.0, 1000.0));
        \\}
    );
}

test "intfromfloat-without-clamp: rounded integer maximum is not an inclusive float bound" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn convert(value: f64) u64 {
        \\    if (value >= 0.0 and value <= @as(f64, @floatFromInt(std.math.maxInt(u64))))
        \\        return @intFromFloat(value);
        \\    return 0;
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn convert(value: f64) u64 {
        \\    if (value >= 0.0 and value < 0x1p64) return @intFromFloat(value);
        \\    return 0;
        \\}
    );
}

test "intfromfloat-without-clamp: range effects discard facts changed inside the operand" {
    try testing.expectFiresTyped(check, R,
        \\fn change(value: *f64) u0 { value.* = 300.0; return 0; }
        \\fn convert() u8 {
        \\    var value: f64 = 10.0;
        \\    return @intFromFloat(@as(f64, @floatFromInt(change(&value))) + value);
        \\}
    );
}

test "intfromfloat-without-clamp: range effects include later loop iterations through aliases" {
    try testing.expectFiresTyped(check, R,
        \\fn change(value: *f64) void { value.* = 300.0; }
        \\fn convert(again: bool) void {
        \\    var value: f64 = 10.0;
        \\    const alias = &value;
        \\    value = 10.0;
        \\    while (again) {
        \\        const number: u8 = @intFromFloat(value);
        \\        _ = number;
        \\        change(alias);
        \\    }
        \\}
    );
}

test "intfromfloat-without-clamp: range effects retain unordered comparison alternatives" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: f64, lower: f64) u8 {
        \\    if (value != value) return 0;
        \\    if (lower < 0.0) return 0;
        \\    if (value < lower) return 0;
        \\    if (value >= 256.0) return 0;
        \\    return @intFromFloat(value);
        \\}
    );
}

test "intfromfloat-without-clamp: caller bounds include parameter rounding" {
    try testing.expectNoFireTyped(check,
        \\fn convert(value: f32) i32 { return @intFromFloat(value); }
        \\pub fn exact() i32 { return convert(42.0); }
    );
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: f32) i32 { return @intFromFloat(value); }
        \\pub fn rounded() i32 { return convert(2147483647.0); }
    );
    try testing.expectFiresTyped(check, R,
        \\fn convert(comptime T: type, value: T) i32 { return @intFromFloat(value); }
        \\pub fn rounded() i32 { return convert(f32, 2147483647.0); }
    );
}

test "intfromfloat-without-clamp: IEEE magnitude guards constrain the original float" {
    try testing.expectNoFireTyped(check,
        \\pub fn convert(value: f32) u32 {
        \\    const bits: u32 = @bitCast(value);
        \\    const magnitude = bits & 0x7fffffff;
        \\    if (magnitude > 0x407ad444) return 0;
        \\    return @intFromFloat(@abs(value) * 16.0);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f32) u32 {
        \\    const bits: u32 = @bitCast(value);
        \\    if ((bits & 0x7fffffff) > 0x7f800000) return 0;
        \\    return @intFromFloat(@abs(value));
        \\}
    );
}

test "intfromfloat-without-clamp: exponent masks retain omitted mantissa bits" {
    try testing.expectNoFireTyped(check,
        \\pub fn convert(value: f32) i64 {
        \\    const bits: u32 = @bitCast(value);
        \\    const exponent = bits & 0x7f800000;
        \\    if (exponent > (150 << 23)) return 0;
        \\    return @intFromFloat(value * 4.0);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f32) u8 {
        \\    const bits: u32 = @bitCast(value);
        \\    if ((bits & 0x7f800000) > (134 << 23)) return 0;
        \\    return @intFromFloat(@abs(value) + 1.0);
        \\}
    );
}

test "intfromfloat-without-clamp: raw bit intervals crossing the sign bit admit NaN" {
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f32) i32 {
        \\    const bits: u32 = @bitCast(value);
        \\    if (bits > 0xbf800000) return 0;
        \\    return @intFromFloat(value);
        \\}
    );
}

test "intfromfloat-without-clamp: extern union views require matching field widths" {
    try testing.expectNoFireTyped(check,
        \\const View = extern union { float: f32, bits: u32 };
        \\pub fn convert(value: f32) u32 {
        \\    const view = View{ .float = @abs(value) };
        \\    if (view.bits > 0x407ad444) return 0;
        \\    return @intFromFloat(@abs(value) * 16.0);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const View = extern union { float: f64, bits: u32 };
        \\pub fn convert(value: f32) u32 {
        \\    const view = View{ .float = value };
        \\    if (view.bits > 0x407ad444) return 0;
        \\    return @intFromFloat(@abs(value));
        \\}
    );
}

test "intfromfloat-without-clamp: rewritten bit views lose their source relation" {
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f32, other: f32) u32 {
        \\    var current = value;
        \\    const bits: u32 = @bitCast(current);
        \\    current = other;
        \\    if ((bits & 0x7fffffff) > 0x407ad444) return 0;
        \\    return @intFromFloat(@abs(current));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f32) u32 {
        \\    var bits: u32 = @bitCast(value);
        \\    bits = 0;
        \\    if (bits > 0x407ad444) return 0;
        \\    return @intFromFloat(@abs(value));
        \\}
    );
}

test "intfromfloat-without-clamp: conditional bit rewrites cannot constrain every path" {
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f32, other: f32, replace: bool) u32 {
        \\    var bits: u32 = @bitCast(value);
        \\    if (replace) bits = @bitCast(other);
        \\    if (bits > 0x407ad444) return 0;
        \\    return @intFromFloat(@abs(value));
        \\}
    );
}

test "intfromfloat-without-clamp: absolute bit views do not prove a positive source" {
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f32) u32 {
        \\    const bits: u32 = @bitCast(@abs(value));
        \\    if (bits > 0x407ad444) return 0;
        \\    return @intFromFloat(value);
        \\}
    );
}

test "intfromfloat-without-clamp: resolved predicate returns provide range facts" {
    try testing.expectNoFireTyped(check,
        \\fn valid(value: f64) bool { return value >= 0.0 and value < 256.0; }
        \\pub fn convert(value: f64) u8 {
        \\    if (!valid(value)) return 0;
        \\    return @intFromFloat(value);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn valid(value: f64) bool {
        \\    if (value > 10.0) return true;
        \\    return value >= 0.0 and value < 256.0;
        \\}
        \\pub fn convert(value: f64) u8 {
        \\    if (!valid(value)) return 0;
        \\    return @intFromFloat(value);
        \\}
    );
}

test "intfromfloat-without-clamp: generic predicates require lossless widening" {
    try testing.expectNoFireTyped(check,
        \\fn valid(comptime T: type, value: T) bool {
        \\    const wide: f64 = @floatCast(value);
        \\    if (wide != wide) return false;
        \\    if (wide < -0x1p63 or wide >= 0x1p63) return false;
        \\    return true;
        \\}
        \\fn convert(comptime T: type, value: T) i64 {
        \\    if (!valid(T, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(value: f32) i64 { return convert(f32, value); }
        \\pub fn double(value: f64) i64 { return convert(f64, value); }
    );
    try testing.expectFiresTyped(check, R,
        \\fn valid(comptime T: type, value: T) bool {
        \\    const wide: f64 = @floatCast(value);
        \\    if (wide != wide) return false;
        \\    if (wide < -0x1p63 or wide >= 0x1p63) return false;
        \\    return true;
        \\}
        \\fn convert(comptime T: type, value: T) i64 {
        \\    if (!valid(T, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn extended(value: f128) i64 { return convert(f128, value); }
    );
}

test "intfromfloat-without-clamp: predicate effects invalidate global facts" {
    try testing.expectFiresTyped(check, R,
        \\var value: f64 = 1;
        \\fn valid(input: f64) bool {
        \\    value = 1e300;
        \\    return input >= 0.0 and input < 256.0;
        \\}
        \\pub fn convert() u8 {
        \\    value = 1;
        \\    if (!valid(value)) return 0;
        \\    return @intFromFloat(value);
        \\}
    );
}

test "intfromfloat-without-clamp: chained exponent guards survive scalar calls" {
    try testing.expectNoFireTyped(check,
        \\const magnitude_mask: u32 = 0x7fff_ffff;
        \\const infinity_bits: u32 = 0x7f80_0000;
        \\fn rounded(value: f64) f64 { return (value + 0x1.8p52) - 0x1.8p52; }
        \\pub fn convert(value: f32) f32 {
        \\    const bits: u32 = @bitCast(value);
        \\    const magnitude = bits & magnitude_mask;
        \\    const exponent = magnitude & infinity_bits;
        \\    if (magnitude > infinity_bits) return 0;
        \\    if (magnitude == infinity_bits) return 0;
        \\    if (exponent > (150 << 23)) return 0;
        \\    const scaled: f32 = 4.0 * value;
        \\    const delta: f32 = scaled - @as(f32, @floatCast(rounded(@floatCast(scaled))));
        \\    if (delta == 0) {
        \\        var quadrant: i64 = @intFromFloat(scaled);
        \\        quadrant &= 6;
        \\        return @floatFromInt(quadrant);
        \\    }
        \\    return 0;
        \\}
    );
}

test "intfromfloat-without-clamp: discarded addresses do not mutate bounded scalars" {
    try testing.expectNoFireTyped(check,
        \\pub fn convert(value: f32) u32 {
        \\    const bits: u32 = @bitCast(value);
        \\    const magnitude = bits & 0x7fff_ffff;
        \\    if (magnitude > 0x407a_d444) return 0;
        \\    var copy = value;
        \\    _ = &copy;
        \\    var absolute = @abs(copy);
        \\    _ = &absolute;
        \\    return @intFromFloat(16.0 * absolute);
        \\}
    );
}
