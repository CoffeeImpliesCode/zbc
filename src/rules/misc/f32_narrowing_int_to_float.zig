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
        var destination_bits = destinationBits(resolver, node);
        if (destination_bits) |bits| {
            if (bits != 32) continue;
        } else if (cache.isFloatType(node) == false) {
            continue;
        }
        const operand = runtimeOperand(tree, node) orelse continue;
        if (destination_bits == null) {
            if (try value_range.closedFloatConversionUsesF32(tree, operand.declaration, node, cache)) |uses_f32| {
                if (!uses_f32) continue;
                destination_bits = 32;
            }
        }
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
        if (try value_range.instantiatedConversionFits(gpa, tree, operand.declaration, node, operand.source, cache)) continue;
        const message = try gpa.dupe(u8, if (destination_bits == null)
            "the destination float precision could not be resolved for `@floatFromInt`, and the integer input was not proved exact in every supported float format; conversion exactness remains unknown; resolve the destination precision or prove an exact input range"
        else
            "the integer input was not proved exactly representable in f32; conversion can round before subsequent arithmetic or bounds checks; prove an exact input range or use sufficient precision");
        errdefer gpa.free(message);
        try problems.append(gpa, .{
            .rule_id = R,
            .severity = .warning,
            .start = try Pos.fromTokenStart(tree, token),
            .end = try Pos.fromTokenEnd(tree, tree.lastToken(node)),
            .message = message,
        });
    }
}

/// A conversion's result location can carry a field or return payload type
/// even when the builtin's own type query has no answer.
fn destinationBits(resolver: *@import("../../type_resolver.zig").TypeResolver, node: Ast.Node.Index) ?u16 {
    if (resolver.floatBits(node) catch null) |bits| return bits;
    var expected = (resolver.resolutionFrame().expectedTypeOfNode(node) catch null) orelse return null;
    for (0..128) |_| {
        switch (resolver.typeTag(expected) orelse return null) {
            .optional, .error_union => expected = resolver.childType(expected) orelse return null,
            .float, .comptime_float => return resolver.ctx.ip.floatBits(expected.ipIndex() orelse return null, @import("builtin").target),
            else => return null,
        }
    }
    return null;
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

test "f32-narrowing-int-to-float: bounded for counts retain exit ranges" {
    try testing.expectNoFireTyped(check,
        \\fn convert(done: []const bool) f32 {
        \\    var count: u32 = 0;
        \\    for (done[0..@min(done.len, 4)]) |value| {
        \\        if (value) count += 1;
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn convert(done: [4]bool, visible_count: u8) f32 {
        \\    var count: u32 = 0;
        \\    for (done[0..visible_count]) |value| {
        \\        if (value) count += 1;
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn convert(done: [4]bool) f32 {
        \\    var count: u32 = 0;
        \\    for (done) |value| {
        \\        if (value) count += 1;
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
}

test "f32-narrowing-int-to-float: bounded count rejects extra writes" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(done: [4]bool, extra: u32) f32 {
        \\    var count: u32 = 0;
        \\    for (done) |value| {
        \\        if (value) count += 1;
        \\        count += extra;
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
}

test "f32-narrowing-int-to-float: nested and unbounded iterations remain uncertain" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(done: [4]bool, repetitions: usize) f32 {
        \\    var count: u32 = 0;
        \\    for (done) |value| {
        \\        for (0..repetitions) |_| {
        \\            if (value) count += 1;
        \\        }
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn convert(done: []const bool) f32 {
        \\    var count: u32 = 0;
        \\    for (done) |value| {
        \\        if (value) count += 1;
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
}

test "f32-narrowing-int-to-float: escaped count and unknown calls remain uncertain" {
    try testing.expectFiresTyped(check, R,
        \\extern fn overwrite(*u32) void;
        \\fn convert(done: [4]bool) f32 {
        \\    var count: u32 = 0;
        \\    const alias = &count;
        \\    for (done) |value| {
        \\        if (value) count += 1;
        \\        overwrite(alias);
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\extern fn next() bool;
        \\fn convert(done: [4]bool) f32 {
        \\    var count: u32 = 0;
        \\    for (done) |_| {
        \\        if (next()) count += 1;
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
}

test "f32-narrowing-int-to-float: bounded count survives unrelated calls" {
    try testing.expectNoFireTyped(check,
        \\extern fn observe(u32) void;
        \\fn convert(done: [4]bool) f32 {
        \\    var count: u32 = 0;
        \\    for (done) |value| {
        \\        if (value) count += 1;
        \\    }
        \\    observe(count);
        \\    return @floatFromInt(count);
        \\}
    );
}

test "f32-narrowing-int-to-float: iteration bounds include initial count" {
    try testing.expectNoFireTyped(check,
        \\fn convert() f32 {
        \\    var count: u32 = 10;
        \\    for (2..6) |_| {
        \\        count += 1;
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn convert(done: [4]bool) f32 {
        \\    var count: u32 = 16777216;
        \\    for (done) |value| {
        \\        if (value) count += 1;
        \\    }
        \\    return @floatFromInt(count);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn convert() f32 {
        \\    var count: u32 = 0;
        \\    for (0..16777217) |_| {
        \\        count += 1;
        \\    }
        \\    return @floatFromInt(count);
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

test "f32-narrowing-int-to-float: unrelated exported alias does not open helper callers" {
    try testing.expectNoFireTyped(check,
        \\fn convert(value: u32) f32 { return @floatFromInt(value); }
        \\const Other = struct { fn convert(value: u32) f64 { return @floatFromInt(value); } };
        \\pub const exported = Other.convert;
        \\pub fn small() f32 { return convert(42); }
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

test "intfromfloat-without-clamp: finite SDK f16 maximum fits i128" {
    const consumer = @import("./intfromfloat_without_clamp.zig");
    try testing.expectNoFireTyped(consumer.check,
        \\const std = @import("std");
        \\fn positive() i128 { return @intFromFloat(std.math.floatMax(f16)); }
        \\fn negative() i128 { return @intFromFloat(-std.math.floatMax(f16)); }
        \\fn local_value_alias() i128 {
        \\    const maximum = std.math.floatMax(f16);
        \\    return @intFromFloat(maximum);
        \\}
        \\fn sdk_function_alias() i128 {
        \\    const maximum = std.math.floatMax;
        \\    return @intFromFloat(maximum(f16));
        \\}
        \\fn expression() i128 { return @intFromFloat(std.math.floatMax(f16) / 2); }
    );
}

test "intfromfloat-without-clamp: SDK nonfinite constants remain unsafe" {
    const consumer = @import("./intfromfloat_without_clamp.zig");
    try testing.expectFiresTyped(consumer.check, "intfromfloat-without-clamp",
        \\const std = @import("std");
        \\fn convert() i128 { return @intFromFloat(std.math.nan(f16)); }
    );
    try testing.expectFiresTyped(consumer.check, "intfromfloat-without-clamp",
        \\const std = @import("std");
        \\fn convert() i128 { return @intFromFloat(std.math.inf(f16)); }
    );
}

test "intfromfloat-without-clamp: larger SDK float maxima exceed i128" {
    const consumer = @import("./intfromfloat_without_clamp.zig");
    try testing.expectFiresTyped(consumer.check, "intfromfloat-without-clamp",
        \\const std = @import("std");
        \\fn convert() i128 { return @intFromFloat(std.math.floatMax(f64)); }
    );
}

test "intfromfloat-without-clamp: finite f16 maximum still exceeds u8" {
    const consumer = @import("./intfromfloat_without_clamp.zig");
    try testing.expectFiresTyped(consumer.check, "intfromfloat-without-clamp",
        \\const std = @import("std");
        \\fn convert() u8 { return @intFromFloat(std.math.floatMax(f16)); }
    );
}

test "intfromfloat-without-clamp: runtime f16 input is not universally safe" {
    const consumer = @import("./intfromfloat_without_clamp.zig");
    try testing.expectFiresTyped(consumer.check, "intfromfloat-without-clamp",
        \\fn convert(value: f16) i128 { return @intFromFloat(value); }
    );
}

test "intfromfloat-without-clamp: unrelated floatMax leaf remains unsafe" {
    const consumer = @import("./intfromfloat_without_clamp.zig");
    try testing.expectFiresTyped(consumer.check, "intfromfloat-without-clamp",
        \\const Other = struct {
        \\    fn floatMax(comptime _: type) f64 { return 1e300; }
        \\};
        \\fn convert() i128 { return @intFromFloat(Other.floatMax(f16)); }
    );
}

test "f32-narrowing-int-to-float: resolved image aliases preserve byte channels" {
    try testing.expectNoFireTyped(check,
        \\const Host = struct { const Image = struct { pixels: []const u8 }; };
        \\const Svg = struct { const DecodedImage = Host.Image; };
        \\const DecodedImage = Svg.DecodedImage;
        \\pub fn upload(image: *const DecodedImage, index: usize) [4]f32 {
        \\    return .{
        \\        @as(f32, @floatFromInt(image.pixels[index])),
        \\        @as(f32, @floatFromInt(image.pixels[index + 1])),
        \\        @as(f32, @floatFromInt(image.pixels[index + 2])),
        \\        @as(f32, @floatFromInt(image.pixels[index + 3])),
        \\    };
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Host = struct { const Image = struct { pixels: []const u32 }; };
        \\const DecodedImage = Host.Image;
        \\pub fn channel(image: *const DecodedImage, index: usize) f32 {
        \\    return @floatFromInt(image.pixels[index]);
        \\}
    );
}

test "f32-narrowing-int-to-float: saturated frame delta includes the exact endpoint" {
    try testing.expectNoFireTyped(check,
        \\pub fn delta(now: u64, before: u64) f32 {
        \\    return @floatFromInt(@min(now -| before, 1 << 24));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn delta(now: u64, before: u64) f32 {
        \\    return @floatFromInt(@min(now -| before, (1 << 24) + 1));
        \\}
    );
}

test "f32-narrowing-int-to-float: accessor return type does not certify byte storage" {
    try testing.expectNoFireTyped(check,
        \\const Object = struct {
        \\    raw: u8,
        \\    fn toInt(self: @This()) u8 { return self.raw; }
        \\};
        \\pub fn convert(comptime T: type, object: Object) T {
        \\    return @floatFromInt(object.toInt());
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Object = struct {
        \\    raw: u64,
        \\    fn toInt(self: @This()) u32 { return @truncate(self.raw); }
        \\};
        \\pub fn convert(comptime T: type, object: Object) T {
        \\    return @floatFromInt(object.toInt());
        \\}
    );
}

test "f32-narrowing-int-to-float: contextual float constructors use declared parameters" {
    try testing.expectNoFireTyped(check,
        \\const Value = struct {
        \\    number: f64,
        \\    pub fn @"f64"(value: f64) @This() { return .{ .number = value }; }
        \\};
        \\pub fn fill(element: *Value, index: u64) void {
        \\    element.* = .f64(@floatFromInt(index));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const Value = struct {
        \\    number: f32,
        \\    pub fn @"f64"(value: f32) @This() { return .{ .number = value }; }
        \\};
        \\pub fn fill(element: *Value, index: u64) void {
        \\    element.* = .f64(@floatFromInt(index));
        \\}
    );
}

test "f32-narrowing-int-to-float: unrelated format inputs cannot borrow caller precision" {
    try testing.expectFiresTyped(check, R,
        \\fn payload(comptime Float: type, comptime Bits: type, comptime mask: Bits, bits: Bits) Float {
        \\    return @floatFromInt(bits & mask);
        \\}
        \\pub fn inexact(bits: u32) f32 { return payload(f32, u32, 0x1ffffff, bits); }
        \\pub fn exact(bits: u64) f64 { return payload(f64, u64, 0x7ffffffffffff, bits); }
    );
    try testing.expectNoFireTyped(check,
        \\pub fn payload(bits: u32) f32 { return @floatFromInt(bits & 0x3fffff); }
    );
}

test "f32-narrowing-int-to-float: bounded exponents need actual integer bounds" {
    try testing.expectNoFireTyped(check,
        \\pub fn exponent(value: i32) f32 {
        \\    if (value < -1074 or value > 1023) return 0;
        \\    return @floatFromInt(value);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn exponent(value: i32) f32 { return @floatFromInt(value); }
    );
}

test "f32-narrowing-int-to-float: integer round trip cannot borrow a wider source format" {
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f64) f32 {
        \\    if (!(value >= 0 and value < 33554432)) return 0;
        \\    const truncated: i64 = @intFromFloat(value);
        \\    return @floatFromInt(truncated);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\pub fn convert(value: f32) f32 {
        \\    if (!(value >= 0 and value <= 16777216)) return 0;
        \\    const truncated: i64 = @intFromFloat(value);
        \\    if (truncated < 0 or truncated > 16777216) return 0;
        \\    return @floatFromInt(truncated);
        \\}
    );
}

test "f32-narrowing-int-to-float: aggregate destinations use the resolved field type" {
    try testing.expectNoFireTyped(check,
        \\const V = union(enum) { f64: f64 };
        \\pub fn store(value: u32) V { return .{ .f64 = @floatFromInt(value) }; }
    );
    try testing.expectFiresTyped(check, R,
        \\const V = union(enum) { f64: f32 };
        \\pub fn store(value: u32) V { return .{ .f64 = @floatFromInt(value) }; }
    );
}

test "f32-narrowing-int-to-float: slice element types bound direct channel reads" {
    try testing.expectNoFireTyped(check,
        \\pub fn channel(bytes: []const u8, index: usize) f32 { return @floatFromInt(bytes[index]); }
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn channel(bytes: []const u32, index: usize) f32 { return @floatFromInt(bytes[index]); }
    );
}

test "f32-narrowing-int-to-float: local modulo and early return preserve small bounds" {
    try testing.expectNoFireTyped(check,
        \\pub fn caret(end: usize) ?f32 {
        \\    const column = end % 8;
        \\    const line = end / 8;
        \\    if (line >= 3) return null;
        \\    return @as(f32, @floatFromInt(column)) + @floatFromInt(line);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn caret(end: usize) ?f32 {
        \\    const column = end % 8;
        \\    const line = end / 8;
        \\    return @as(f32, @floatFromInt(column)) + @floatFromInt(line);
        \\}
    );
}

test "f32-narrowing-int-to-float: closed generic masks keep destination correlation" {
    try testing.expectNoFireTyped(check,
        \\fn payload(comptime Float: type, comptime Bits: type, comptime mask: Bits, bits: Bits) Float {
        \\    return @floatFromInt(bits & mask);
        \\}
        \\pub fn small(bits: u32) f32 { return payload(f32, u32, 0x3fffff, bits); }
        \\pub fn wide(bits: u64) f64 { return payload(f64, u64, 0x7ffffffffffff, bits); }
    );
    try testing.expectFiresTyped(check, R,
        \\fn payload(comptime Float: type, comptime Bits: type, comptime mask: Bits, bits: Bits) Float {
        \\    return @floatFromInt(bits & mask);
        \\}
        \\pub fn small(bits: u32) f32 { return payload(f32, u32, 0x1ffffff, bits); }
        \\pub fn wide(bits: u64) f64 { return payload(f64, u64, 0x7ffffffffffff, bits); }
    );
}

test "f32-narrowing-int-to-float: private test helpers require every caller bound" {
    try testing.expectNoFireTyped(check,
        \\fn coordinate(value: usize) f32 { return @floatFromInt(value); }
        \\test "small fixture" { _ = coordinate(3); _ = coordinate(8); }
    );
    try testing.expectFiresTyped(check, R,
        \\fn coordinate(value: usize) f32 { return @floatFromInt(value); }
        \\test "small fixture" { _ = coordinate(3); }
        \\test "large fixture" { _ = coordinate(16777217); }
    );
}

test "f32-narrowing-int-to-float: escaped test callbacks retain unknown callers" {
    try testing.expectFiresTyped(check, R,
        \\const Callback = *const fn (usize) f32;
        \\extern fn invoke(Callback) void;
        \\fn coordinate(value: usize) f32 { return @floatFromInt(value); }
        \\test "callback fixture" { invoke(coordinate); }
    );
}

test "f32-narrowing-int-to-float: named imported image reexports preserve element widths" {
    const resolver_mod = @import("../../type_resolver.zig");
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "build.zig", .data =
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const host = b.createModule(.{ .root_source_file = b.path("host.zig") });
        \\    const demo = b.addModule("demo", .{ .root_source_file = b.path("main.zig") });
        \\    demo.addImport("nogui_host", host);
        \\}
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data =
        \\pub const svg = @import("svg.zig");
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "host.zig", .data =
        \\pub const svg = @import("host_svg.zig");
    });
    try tmp.dir.writeFile(io, .{ .sub_path = "host_svg.zig", .data =
        \\pub const DecodedImage = @import("image.zig").DecodedImage;
    });
    const source: [:0]const u8 =
        \\const host = @import("nogui_host");
        \\const host_svg = host.svg;
        \\pub const DecodedImage = host_svg.DecodedImage;
        \\pub fn channel(image: *const DecodedImage, index: usize) f32 {
        \\    return @as(f32, @floatFromInt(image.pixels[index]));
        \\}
    ;
    try tmp.dir.writeFile(io, .{ .sub_path = "svg.zig", .data = source });
    const root = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(root);
    const source_path = try std.fs.path.join(gpa, &.{ root, "svg.zig" });
    defer gpa.free(source_path);
    const cases = [_]struct { image: []const u8, bits: u16, count: usize }{
        .{ .image = "pub const DecodedImage = struct { pixels: []u8 };", .bits = 8, .count = 0 },
        .{ .image = "pub const DecodedImage = struct { pixels: []u32 };", .bits = 32, .count = 1 },
    };
    for (cases) |case| {
        try tmp.dir.writeFile(io, .{ .sub_path = "image.zig", .data = case.image });
        var context: resolver_mod.TypeContext = undefined;
        try context.init(gpa, io);
        defer context.deinit();
        context.store.source_policy = .{ .roots = &.{root} };
        var resolver: resolver_mod.TypeResolver = undefined;
        try resolver.init(&context, gpa, source_path, source);
        defer resolver.deinit();
        try std.testing.expect(resolver.handle.module != .unscoped);
        const tree = &resolver.handle.document.tree;
        try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
        var cache = file_cache_mod.FileCache.init(gpa, tree);
        defer cache.deinit();
        cache.setZls(&resolver);
        cache.file_path = source_path;
        cache.module_id = resolver.handle.module;
        var accesses: usize = 0;
        for (tree.nodes.items(.tag), 0..) |tag, index| {
            if (tag != .array_access) continue;
            const info = cache.intInfoOf(@enumFromInt(index)) orelse return error.MissingElementType;
            try std.testing.expectEqual(case.bits, info.bits);
            accesses += 1;
        }
        try std.testing.expectEqual(@as(usize, 1), accesses);
        var problems: std.ArrayListUnmanaged(Problem) = .empty;
        defer testing.freeProblems(gpa, &problems);
        try check(gpa, tree, &cache, &config_mod.Default, &problems);
        try std.testing.expectEqual(case.count, problems.items.len);
        for (problems.items) |problem| try std.testing.expectEqualStrings(R, problem.rule_id);
    }
}

test "f32-narrowing-int-to-float: private measurement helpers inherit closed slice lengths" {
    try testing.expectNoFireTyped(check,
        \\fn measure(content: []const u8) f32 { return @floatFromInt(content.len * 10); }
        \\test "small text" { _ = measure("three"); }
    );
    try testing.expectFiresTyped(check, R,
        \\extern fn content() []const u8;
        \\fn measure(text: []const u8) f32 { return @floatFromInt(text.len * 10); }
        \\test "unknown text" { _ = measure(content()); }
    );
}

test "f32-narrowing-int-to-float: separate tags cannot certify wide stored payloads" {
    const source =
        \\const Value = struct { tag: enum { byte, word }, payload: u32 };
        \\fn convert(comptime Float: type, value: Value) Float {
        \\    return switch (value.tag) {
        \\        .byte => @floatFromInt(value.payload),
        \\        .word => @floatFromInt(value.payload),
        \\    };
        \\}
        \\pub fn use(value: Value) f32 { return convert(f32, value); }
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, source);
    defer testing.freeProblems(std.testing.allocator, &problems);
    // Both branches contain a distinct unsafe conversion of the wide payload.
    try std.testing.expectEqual(@as(usize, 2), problems.items.len);
    for (problems.items) |problem| {
        try std.testing.expectEqualStrings(R, problem.rule_id);
        try std.testing.expect(std.mem.indexOf(u8, problem.message, "exactly representable in f32") != null);
        try std.testing.expect(std.mem.indexOf(u8, problem.message, "could not be resolved") == null);
    }
    try std.testing.expect(!std.meta.eql(problems.items[0].start, problems.items[1].start));
    try testing.expectNoFireTyped(check,
        \\const Value = struct { tag: enum { byte, word }, payload: u8 };
        \\fn convert(comptime Float: type, value: Value) Float {
        \\    return switch (value.tag) {
        \\        .byte => @floatFromInt(value.payload),
        \\        .word => @floatFromInt(value.payload),
        \\    };
        \\}
        \\pub fn use(value: Value) f32 { return convert(f32, value); }
    );
}

test "f32-narrowing-int-to-float: closed destination classification does not certify escaped callers" {
    try testing.expectNoFireTyped(check,
        \\fn convert(comptime Float: type, value: u64) Float { return @floatFromInt(value); }
        \\pub fn wide(value: u64) f64 { return convert(f64, value); }
    );
    const source =
        \\fn convert(comptime Float: type, value: u32) Float { return @floatFromInt(value); }
        \\pub const exported = convert;
        \\pub fn use(value: u32) f32 { return convert(f32, value); }
    ;
    var problems = try testing.runRuleTyped(std.testing.allocator, check, source);
    defer testing.freeProblems(std.testing.allocator, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings(R, problems.items[0].rule_id);
    try std.testing.expect(std.mem.indexOf(u8, problems.items[0].message, "destination float precision could not be resolved") != null);
}
