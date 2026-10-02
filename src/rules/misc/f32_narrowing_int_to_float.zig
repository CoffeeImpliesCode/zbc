//! Report integer-to-f32 conversions without an exact input range.
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

const R = "f32-narrowing-int-to-float";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .f32_narrowing_int_to_float)) return;
    const resolver = cache.zls orelse return;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const token = tree.nodeMainToken(node);
        if (!std.mem.eql(u8, tree.tokenSlice(token), "@floatFromInt")) continue;
        if ((resolver.floatBits(node) catch null) != 32) continue;
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        if (!tokens.isRuntimeUse(tree, declaration, token)) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, node).?;
        if (params.len != 1) continue;
        if (cache.intInfoOf(params[0])) |source| {
            if (value_range.NumericRange.integerType(source.bits, source.signed).exactInF32()) continue;
        }
        const bounds = try value_range.boundsAt(gpa, tree, tokens.bodyOf(tree, declaration).?, params[0], token, cache);
        if (bounds.exactInF32()) continue;
        const message = try gpa.dupe(u8, "the integer input was not proved exactly representable in f32; conversion can round before subsequent arithmetic or bounds checks; prove an exact input range or use sufficient precision");
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

test "f32-narrowing-int-to-float: range proof ignores color spelling" {
    try testing.expectFiresTyped(check, R,
        \\const Color = struct { r: u32 };
        \\fn convert(color: Color) f32 { return @as(f32, @floatFromInt(color.r)); }
    );
}

test "f32-narrowing-int-to-float: range proof precedes division" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: u32) f32 { return @as(f32, @floatFromInt(value)) / 255.0; }
    );
}

test "f32-narrowing-int-to-float: range proof covers the whole expression" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: u32) f32 { return @as(f32, @floatFromInt((value & 0xff) + 0x1000001)); }
    );
}

test "f32-narrowing-int-to-float: range proof includes signed 25 bit inputs" {
    try testing.expectNoFireTyped(check,
        \\fn convert(value: i25) f32 { return @as(f32, @floatFromInt(value)); }
    );
}

test "f32-narrowing-int-to-float: inferred destination uses the same proof" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: u32) f32 { return @floatFromInt(value); }
    );
    try testing.expectNoFireTyped(check,
        \\fn convert(value: u32) f64 { return @floatFromInt(value); }
    );
}

test "f32-narrowing-int-to-float: typed fields and masks provide bounds" {
    try testing.expectNoFireTyped(check,
        \\const Color = struct { r: u8 };
        \\fn convert(color: Color) f32 { return @floatFromInt(color.r); }
    );
    try testing.expectNoFireTyped(check,
        \\fn convert(value: u32) f32 { return @floatFromInt(value & 0x1ffff); }
    );
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: u32) f32 { return @floatFromInt(value & 0x1ffffff); }
    );
}

test "f32-narrowing-int-to-float: dominating bounds admit the exact endpoint" {
    try testing.expectNoFireTyped(check,
        \\fn convert(value: u32) f32 {
        \\    if (value > 16777216) return 0;
        \\    return @floatFromInt(value);
        \\}
    );
}

test "f32-narrowing-int-to-float: isolated large exact values retain precision" {
    try testing.expectNoFireTyped(check,
        \\fn convert() f32 {
        \\    const value: u64 = 1073741824;
        \\    return @floatFromInt(value);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn convert() f32 {
        \\    const value: u64 = 1073741825;
        \\    return @floatFromInt(value);
        \\}
    );
}

test "f32-narrowing-int-to-float: closed helper inherits guarded caller bounds" {
    try testing.expectNoFireTyped(check,
        \\fn convert(value: u32) f32 { return @floatFromInt(value); }
        \\pub fn bounded(value: u32) f32 {
        \\    if (value > 16777216) return 0;
        \\    return convert(value);
        \\}
    );
}

test "f32-narrowing-int-to-float: every caller contributes to a helper bound" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: u32) f32 { return @floatFromInt(value); }
        \\pub fn small() f32 { return convert(42); }
        \\pub fn large() f32 { return convert(16777217); }
    );
}

test "f32-narrowing-int-to-float: public and escaped helpers have unknown callers" {
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: u32) f32 { return @floatFromInt(value); }
        \\pub fn small() f32 { return convert(42); }
    );
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: u32) f32 { return @floatFromInt(value); }
        \\pub const exported = convert;
        \\pub fn small() f32 { return convert(42); }
    );
}

test "f32-narrowing-int-to-float: caller bounds use declaration identity" {
    try testing.expectNoFireTyped(check,
        \\fn convert(value: u32) f32 { return @floatFromInt(value); }
        \\const Other = struct { fn convert(value: u32) f64 { return @floatFromInt(value); } };
        \\pub fn small() f32 { return convert(42); }
        \\pub fn unrelated(value: u32) f64 { return Other.convert(value); }
    );
}

test "f32-narrowing-int-to-float: recursive caller cycles stay uncertain" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: u32) f32 {
        \\    const converted: f32 = @floatFromInt(value);
        \\    if (value > 0) return convert(value - 1);
        \\    return converted;
        \\}
        \\pub fn small() f32 { return convert(42); }
    );
}

test "f32-narrowing-int-to-float: reflection prevents a closed caller proof" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: u32) f32 { return @floatFromInt(value); }
        \\pub fn small() f32 { return convert(42); }
        \\pub fn reflected() f32 { return @field(@This(), "convert")(16777217); }
    );
}

test "f32-narrowing-int-to-float: caller bounds map explicit and implicit receivers" {
    try testing.expectNoFireTyped(check,
        \\const Converter = struct {
        \\    fn convert(_: *const @This(), value: u32) f32 { return @floatFromInt(value); }
        \\};
        \\pub fn small(converter: *const Converter) f32 {
        \\    return converter.convert(42) + Converter.convert(converter, 43);
        \\}
    );
}

test "f32-narrowing-int-to-float: quoted caller aliases cannot be skipped" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(value: u32) f32 { return @floatFromInt(value); }
        \\pub fn small() f32 { return convert(42); }
        \\pub fn large() f32 { return @"\x63onvert"(16777217); }
    );
}

test "f32-narrowing-int-to-float: impure caller arguments invalidate guarded globals" {
    try testing.expectFiresTyped(check, R,
        \\var value: u32 = 0;
        \\fn convert(_: void, input: u32) f32 { return @floatFromInt(input); }
        \\fn mutate() void { value = 16777217; }
        \\pub fn call() f32 {
        \\    value = 0;
        \\    return convert(mutate(), value);
        \\}
    );
}
