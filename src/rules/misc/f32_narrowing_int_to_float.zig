//! Report integer-to-f32 conversions without an exact input range.
//! Known non-f32 destinations are outside scope. An unresolved destination
//! precision gets an advisory unless the input is exact in every supported
//! float format; it is not assumed to be f32.
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
        const destination_bits = resolver.floatBits(node) catch null;
        if (destination_bits) |bits| {
            if (bits != 32) continue;
        } else if (cache.isFloatType(node) == false) {
            continue;
        }
        const operand = runtimeOperand(tree, node) orelse continue;
        // The type engine's answer about the SOURCE, consulted before the
        // oracle because the oracle cannot always give it: an expression's
        // range is computed from its operands in unbounded arithmetic, so
        // `u16 * u16` reaches past the result's own type and a narrow
        // source can be handed back a wider range than any value it can
        // take. Where the declared domain is exact for the destination there
        // is nothing for the oracle to add. An unresolved width needs a
        // domain exact in every supported float format, not an f32 default.
        // This is a different question from the oracle's range answer.
        if (cache.intInfoOf(operand.source)) |source| {
            if (inputIsExact(value_range.NumericRange.integerType(source.bits, source.signed), destination_bits)) continue;
        }
        const bounds = try value_range.boundsAt(gpa, tree, tokens.bodyOf(tree, operand.declaration).?, operand.source, token, cache);
        if (inputIsExact(bounds, destination_bits)) continue;
        const message = try gpa.dupe(u8, if (destination_bits == null)
            "the destination float precision could not be resolved for `@floatFromInt`, and the integer input was not proved exact in every supported float format; conversion exactness remains unknown; resolve the destination precision or prove an exact input range"
        else
            "the integer input was not proved exactly representable in f32; conversion can round before subsequent arithmetic or bounds checks; prove an exact input range or use sufficient precision");
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

/// The operand one runtime builtin call reads, paired with the
/// declaration that call sits in.  `source` is a node index copied out
/// of the call's argument list, so it outlives that list.
const Operand = struct {
    declaration: Ast.Node.Index,
    source: Ast.Node.Index,
};

/// The single operand `node`'s builtin call converts, or null when the
/// call is not one this rule reads: it lies outside any function
/// declaration, it can only run under `comptime`, or it does not take
/// exactly one operand.  The scan applies these gates in this order and
/// keeps one copy of them here.
fn runtimeOperand(tree: *const Ast, node: Ast.Node.Index) ?Operand {
    const token = tree.nodeMainToken(node);
    const declaration = tokens.enclosingFnDecl(tree, token) orelse return null;
    if (!isRuntimeUse(tree, declaration, token)) return null;
    var buffer: [2]Ast.Node.Index = undefined;
    const params = tree.builtinCallParams(&buffer, node).?;
    if (params.len != 1) return null;
    return .{ .declaration = declaration, .source = params[0] };
}

/// True when the use at `token` runs at runtime: it sits inside
/// `declaration`'s body but outside any `comptime { … }` block (or
/// `comptime label: { … }` block) and outside the expression a bare
/// `comptime` keyword governs.  The compiler checks what it evaluates
/// itself, so a conversion that can only ever run there is not a
/// runtime hazard this rule reports.  A use this cannot place is a
/// runtime use: an unreadable seam declines into the check, never out
/// of it.
fn isRuntimeUse(tree: *const Ast, declaration: Ast.Node.Index, token: Ast.TokenIndex) bool {
    const body = tokens.bodyOf(tree, declaration) orelse return true;
    const first = tree.firstToken(body);
    if (token < first) return true;
    const tags = tree.tokens.items(.tag);
    var stack: [64]Ast.TokenIndex = undefined;
    var depth: usize = 0;
    var t = first;
    while (t <= token) : (t += 1) {
        switch (tags[t]) {
            .l_brace => {
                if (depth < stack.len) stack[depth] = t;
                depth += 1;
            },
            .r_brace => {
                if (depth > 0) depth -= 1;
            },
            else => {},
        }
    }
    var i = depth;
    while (i > 0) {
        i -= 1;
        if (i >= stack.len) continue;
        const brace = stack[i];
        if (brace == 0) continue;
        if (tags[brace - 1] == .keyword_comptime) return false;
        if (brace >= 3 and tags[brace - 3] == .keyword_comptime and
            tags[brace - 2] == .identifier and tags[brace - 1] == .colon) return false;
    }
    return !statementStartsWithComptime(tags, first, token);
}

/// True when the statement owning `token` is written under a bare
/// `comptime` keyword (`comptime assert(x[i] == 0);`), or `token` sits
/// inside the parenthesised call such a keyword governs.  Only the
/// expression the keyword opens counts: once a group it did not open
/// closes, the rest of the statement runs at runtime.
fn statementStartsWithComptime(tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, token: Ast.TokenIndex) bool {
    var start = first;
    var t = token;
    while (t > first) : (t -= 1) {
        switch (tags[t]) {
            .semicolon, .l_brace, .r_brace => {
                start = t + 1;
                break;
            },
            else => {},
        }
    }
    var c: ?Ast.TokenIndex = null;
    t = start;
    while (t < token) : (t += 1) {
        if (tags[t] == .keyword_comptime) {
            c = t;
            break;
        }
    }
    const comptime_tok = c orelse return false;
    var depth: i32 = 0;
    t = comptime_tok + 1;
    while (t < token) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket, .l_brace => depth += 1,
            .r_paren, .r_bracket, .r_brace => {
                depth -= 1;
                if (depth < 0) return false;
            },
            else => {},
        }
    }
    return true;
}

fn inputIsExact(bounds: value_range.NumericRange, destination_bits: ?u16) bool {
    if (destination_bits != null) return bounds.exactInF32();
    if (bounds != .integer) return false;
    // f16 has the least precision and smallest finite integer domain of
    // Zig's supported float formats. This proves a universal input domain,
    // not the unresolved destination's width.
    const dense_limit: i128 = @as(i128, 1) << (std.math.floatFractionalBits(f16) + 1);
    const value = bounds.integer;
    if (value.min >= -dense_limit and value.max <= dense_limit) return true;
    if (value.min != value.max) return false;
    const finite_limit: i128 = @intFromFloat(std.math.floatMax(f16));
    if (value.min < -finite_limit or value.min > finite_limit) return false;
    const converted = bounds.asFloat(16).floating.min;
    return std.math.isFinite(converted) and converted == @as(f128, @floatFromInt(value.min));
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

test "f32-narrowing-int-to-float: generic destination reports unresolved precision" {
    const source =
        \\pub fn convert(comptime T: type, value: u32) T { return @floatFromInt(value); }
        \\pub fn use(value: u32) f32 { return convert(f32, value); }
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, source);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "destination float precision could not be resolved") != null);
}

test "f32-narrowing-int-to-float: unresolved precision preserves universal exact values" {
    try testing.expectNoFireTyped(check,
        \\pub fn convert(comptime T: type, value: u1) T { return @floatFromInt(value); }
        \\pub fn use(value: u1) f32 { return convert(f32, value); }
    );
    try testing.expectNoFireTyped(check,
        \\pub fn convert(comptime T: type) T {
        \\    const value: u64 = 8192;
        \\    return @floatFromInt(value);
        \\}
        \\pub fn use() f32 { return convert(f32); }
    );
    try testing.expectNoFireTyped(check,
        \\pub fn convert(comptime T: type, value: u11) T { return @floatFromInt(value); }
        \\pub fn use(value: u11) f32 { return convert(f32, value); }
    );
}

test "f32-narrowing-int-to-float: known narrowing distinguishes quiet and rounded inputs" {
    try testing.expectNoFireTyped(check,
        \\pub fn convert(value: u1) f32 { return @floatFromInt(value); }
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: u32) f32 { return @floatFromInt(value); }
    );
}

test "f32-narrowing-int-to-float: known non-f32 destinations remain outside scope" {
    inline for (.{
        "pub fn convert(value: u32) f16 { return @floatFromInt(value); }",
        "pub fn convert(value: u64) f64 { return @floatFromInt(value); }",
        "pub fn convert(value: u128) f80 { return @floatFromInt(value); }",
        "pub fn convert(value: u128) f128 { return @floatFromInt(value); }",
    }) |source| {
        try testing.expectNoFireTyped(check, source);
    }
}

test "f32-narrowing-int-to-float: f32 exactness cannot certify unresolved precision" {
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(comptime T: type) T {
        \\    const value: u32 = 16777216;
        \\    return @floatFromInt(value);
        \\}
        \\pub fn use() f32 { return convert(f32); }
    );
    try testing.expectNoFireTyped(check,
        \\pub fn convert() f32 {
        \\    const value: u32 = 16777216;
        \\    return @floatFromInt(value);
        \\}
    );
}
