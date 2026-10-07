//! Report float-to-integer conversions without a proved finite conversion range.
//! Rounding, a helper name, or a nearby comparison is not a range proof.
//! Immutable scalar projections retain their stored floating format. Generic
//! conversions require separate proofs for every closed actual call frame.
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

test "intfromfloat-without-clamp: finite repeat count excludes invalid inputs" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn count(extra: f32) ?usize {
        \\    if (!std.math.isFinite(extra) or extra < 0) return null;
        \\    if (extra > 16_777_216.0) return null;
        \\    return @intFromFloat(extra);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn count(extra: f32) ?usize {
        \\    if (extra < 0 or extra > 16_777_216.0) return null;
        \\    return @intFromFloat(extra);
        \\}
    );
}

test "intfromfloat-without-clamp: reduced wide integer maxima are safe float clamps" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn sleep(sleep_ms: f32) ?u64 {
        \\    const ns = @as(f64, sleep_ms) * 1_000_000.0;
        \\    const maximum = std.math.maxInt(u64) - 2048;
        \\    const high: f64 = @floatFromInt(maximum);
        \\    if (!std.math.isFinite(ns)) return null;
        \\    if (ns < 0 or ns > high) return null;
        \\    return @intFromFloat(@min(@max(ns, 0.0), high));
        \\}
        \\pub fn seek(seconds: f32) ?i64 {
        \\    if (!std.math.isFinite(seconds)) return null;
        \\    const us = @as(f64, @floatCast(seconds)) * 1_000_000.0;
        \\    const high = std.math.maxInt(i64) - 1024;
        \\    return @intFromFloat(@min(@max(us, 0.0), @as(f64, @floatFromInt(high))));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn seek(seconds: f32) i64 {
        \\    const us = @as(f64, seconds) * 1_000_000.0;
        \\    const high: f64 = @floatFromInt(std.math.maxInt(i64));
        \\    return @intFromFloat(@min(@max(us, 0.0), high));
        \\}
    );
}

test "intfromfloat-without-clamp: rounded finite nanoseconds retain a checked maximum" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn convert(ticks: u64, period: f64) ?u64 {
        \\    if (!std.math.isFinite(period) or period <= 0) return null;
        \\    const ns = @as(f64, @floatFromInt(ticks)) * period;
        \\    if (!std.math.isFinite(ns) or ns < 0) return null;
        \\    const rounded = @round(ns);
        \\    if (rounded > 18_446_744_073_709_549_568.0) return null;
        \\    return @intFromFloat(rounded);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(ns: f64) ?u64 {
        \\    const rounded = @round(ns);
        \\    if (rounded < 0 or rounded > 18_446_744_073_709_549_568.0) return null;
        \\    return @intFromFloat(rounded);
        \\}
    );
}

test "intfromfloat-without-clamp: bounded player minutes divide below the integer limit" {
    try testing.expectNoFireTyped(check,
        \\pub fn convert(progress: f32, duration: u32) u32 {
        \\    const seconds: f32 = @floatFromInt(duration);
        \\    const elapsed = @max(@as(f32, 0), @min(progress, seconds));
        \\    return @intFromFloat(elapsed / 60.0);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(progress: f32) u32 {
        \\    return @intFromFloat(progress / 60.0);
        \\}
    );
}

test "intfromfloat-without-clamp: bounded player seconds use a positive remainder divisor" {
    try testing.expectNoFireTyped(check,
        \\pub fn convert(progress: f32, duration: u32) u32 {
        \\    const seconds: f32 = @floatFromInt(duration);
        \\    const elapsed = @max(@as(f32, 0), @min(progress, seconds));
        \\    return @intFromFloat(@mod(elapsed, 60.0));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(progress: f32) u32 {
        \\    return @intFromFloat(@mod(progress, 60.0));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(progress: f32, divisor: f32) u32 {
        \\    const elapsed = @min(@max(progress, 0.0), 1000.0);
        \\    return @intFromFloat(@mod(elapsed, divisor));
        \\}
    );
}

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
        if (!isRuntimeUse(tree, declaration, token)) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, node).?;
        if (params.len != 1) continue;
        if (cache.coercedIntInfoOf(node) orelse cache.intInfoOf(node)) |destination| {
            const bounds = try value_range.boundsAt(gpa, tree, tokens.bodyOf(tree, declaration).?, params[0], token, cache);
            if (bounds.fitsInteger(destination.bits, destination.signed)) continue;
        }
        if (try value_range.instantiatedConversionFits(gpa, tree, declaration, node, params[0], cache)) continue;
        const message = try gpa.dupe(u8, "a finite value within the destination conversion range was not proved for `@intFromFloat`; NaN, infinity, or an out-of-range value traps in Debug/ReleaseSafe and causes undefined behavior in unchecked builds");
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

test "intfromfloat-without-clamp: a finite mask is not a destination bound" {
    // The magnitude mask separates finite from infinite and says nothing
    // about size: every f32 under 0x7f80_0000 takes the conversion, including
    // the magnitudes no i64 can hold.
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f32) i64 {
        \\    const bits: u32 = @bitCast(value);
        \\    if ((bits & 0x7fff_ffff) < 0x7f80_0000) return @intFromFloat(value);
        \\    return 0;
        \\}
    );
    // The same original-form shape cut at the destination's own exclusive
    // bound.  0x5f000000 IS 2^63, so every accepted value is an exact i64.
    try testing.expectNoFireTyped(check,
        \\pub fn convert(value: f32) i64 {
        \\    const bits: u32 = @bitCast(value);
        \\    if ((bits & 0x7fff_ffff) < 0x5f00_0000) return @intFromFloat(value);
        \\    return 0;
        \\}
    );
    // Spelling that same cutoff inclusively admits exactly 2^63, and 2^63 is
    // not an i64.
    try testing.expectFiresTyped(check, R,
        \\pub fn convert(value: f32) i64 {
        \\    const bits: u32 = @bitCast(value);
        \\    if ((bits & 0x7fff_ffff) <= 0x5f00_0000) return @intFromFloat(value);
        \\    return 0;
        \\}
    );
}

test "intfromfloat-without-clamp: nested strict masks retain destination bounds beside unrelated exports" {
    try testing.expectNoFireTyped(check,
        \\test "native" {
        \\    const Native = struct {
        \\        fn convert(value: f32) i64 {
        \\            const bits: u32 = @bitCast(value);
        \\            if ((bits & 0x7fff_ffff) < 0x5f00_0000) return @intFromFloat(value);
        \\            return 0;
        \\        }
        \\        fn unrelated(value: f32) callconv(.c) f32 { return value; }
        \\    };
        \\    comptime { @export(&Native.unrelated, .{ .name = "unrelated" }); }
        \\    _ = Native.convert(42.0);
        \\    _ = Native.convert(0x1p63);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\test "native" {
        \\    const Native = struct {
        \\        fn convert(value: f32) callconv(.c) i64 {
        \\            const bits: u32 = @bitCast(value);
        \\            if ((bits & 0x7fff_ffff) <= 0x5f00_0000) return @intFromFloat(value);
        \\            return 0;
        \\        }
        \\        fn unrelated(value: f32) callconv(.c) f32 { return value; }
        \\    };
        \\    comptime {
        \\        @export(&Native.unrelated, .{ .name = "unrelated" });
        \\        @export(&Native.convert, .{ .name = "conversion" });
        \\    }
        \\    _ = Native.convert(42.0);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\test "native" {
        \\    const Native = struct {
        \\        fn convert(value: f32) callconv(.c) i64 {
        \\            const bits: u32 = @bitCast(value);
        \\            if ((bits & 0x7fff_ffff) < 0x7f80_0000) return @intFromFloat(value);
        \\            return 0;
        \\        }
        \\        fn unrelated(value: f32) callconv(.c) f32 { return value; }
        \\    };
        \\    comptime {
        \\        @export(&Native.unrelated, .{ .name = "unrelated" });
        \\        @export(&Native.convert, .{ .name = "conversion" });
        \\    }
        \\    _ = Native.convert(42.0);
        \\}
    );
}

test "intfromfloat-without-clamp: nested private generic masks use the actual float format" {
    try testing.expectNoFireTyped(check,
        \\fn factory(comptime Float: type) type {
        \\    return struct {
        \\        fn convert(value: Float) i64 {
        \\            const bits: u32 = @bitCast(value);
        \\            if ((bits & 0x7fff_ffff) < 0x5f00_0000) return @intFromFloat(value);
        \\            return 0;
        \\        }
        \\    };
        \\}
        \\pub fn convert(value: f32) i64 { return factory(f32).convert(value); }
    );
    try testing.expectFiresTyped(check, R,
        \\fn factory(comptime Float: type) type {
        \\    return struct {
        \\        fn convert(value: Float) i64 {
        \\            const bits: u32 = @bitCast(value);
        \\            if ((bits & 0x7fff_ffff) <= 0x5f00_0000) return @intFromFloat(value);
        \\            return 0;
        \\        }
        \\    };
        \\}
        \\pub fn convert(value: f32) i64 { return factory(f32).convert(value); }
    );
}

test "intfromfloat-without-clamp: mixed factory widths cannot establish an exact bit format" {
    try testing.expectFiresTyped(check, R,
        \\fn factory(comptime Float: type) type {
        \\    return struct {
        \\        fn convert(value: Float) i64 {
        \\            const bits: u32 = @bitCast(value);
        \\            if ((bits & 0x7fff_ffff) < 0x5f00_0000) return @intFromFloat(value);
        \\            return 0;
        \\        }
        \\    };
        \\}
        \\pub fn convert(value: f32) i64 { return factory(f32).convert(value); }
        \\pub fn halfType() type { return factory(f16); }
    );
}

test "intfromfloat-without-clamp: an open factory cannot establish an exact bit format" {
    try testing.expectFiresTyped(check, R,
        \\pub fn factory(comptime Float: type) type {
        \\    return struct {
        \\        fn convert(value: Float) i64 {
        \\            const bits: u32 = @bitCast(value);
        \\            if ((bits & 0x7fff_ffff) < 0x5f00_0000) return @intFromFloat(value);
        \\            return 0;
        \\        }
        \\    };
        \\}
        \\pub fn convert(value: f32) i64 { return factory(f32).convert(value); }
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

test "intfromfloat-without-clamp: widening cannot hide an inner narrowing cast" {
    try testing.expectFiresTyped(check, R,
        \\fn valid(comptime T: type, value: T) bool {
        \\    const wide: f64 = @as(f32, @floatCast(value));
        \\    return wide >= 0 and wide < 256;
        \\}
        \\fn convert(comptime T: type, value: T) u8 {
        \\    if (!valid(T, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn convertDouble(value: f64) u8 { return convert(f64, value); }
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

test "intfromfloat-without-clamp: a predicate that writes its argument loses the finiteness it was handed" {
    // `isFinite(x)` is proved for the state BEFORE `rewrite` runs.  The call
    // that then decides the branch leaves `x` a NaN, so the conversion reads
    // a value no guard described.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn rewrite(v: *f64) bool {
        \\    v.* = std.math.nan(f64);
        \\    return true;
        \\}
        \\pub fn convert(raw: f64) u64 {
        \\    var x = raw;
        \\    if (x < 0 or x > 1e18) return 0;
        \\    if (std.math.isFinite(x) and rewrite(&x)) return @intFromFloat(x);
        \\    return 0;
        \\}
    );
    // One token apart: the same predicate handed a COPY cannot move `x`, so
    // the recorded finiteness still describes what the conversion reads.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn probe(v: f64) bool {
        \\    return std.math.isFinite(v);
        \\}
        \\pub fn convert(raw: f64) u64 {
        \\    const x = raw;
        \\    if (x < 0 or x > 1e18) return 0;
        \\    if (std.math.isFinite(x) and probe(x)) return @intFromFloat(x);
        \\    return 0;
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

test "intfromfloat-without-clamp: a call after a discarded address keeps the guarded bound" {
    // `note` is handed a COPY, and an address taken only to be thrown away
    // writes nothing, so the guard still describes the value the conversion
    // reads.
    try testing.expectNoFireTyped(check,
        \\fn note(x: f32) void { _ = x; }
        \\pub fn convert(value: f32) u32 {
        \\    const bits: u32 = @bitCast(value);
        \\    const magnitude = bits & 0x7fff_ffff;
        \\    if (magnitude > 0x407a_d444) return 0;
        \\    var copy = value;
        \\    _ = &copy;
        \\    var absolute = @abs(copy);
        \\    _ = &absolute;
        \\    note(absolute);
        \\    return @intFromFloat(16.0 * absolute);
        \\}
    );
}

test "intfromfloat-without-clamp: a callee handed the address invalidates the bound" {
    // The same body with the address actually handed out: `blowUp` writes
    // through it, so the discarded `_ =` does not make the bound survive.
    try testing.expectFiresTyped(check, R,
        \\fn blowUp(x: *f32) void { x.* = 1e30; }
        \\pub fn convert(value: f32) u32 {
        \\    const bits: u32 = @bitCast(value);
        \\    const magnitude = bits & 0x7fff_ffff;
        \\    if (magnitude > 0x407a_d444) return 0;
        \\    var copy = value;
        \\    _ = &copy;
        \\    var absolute = @abs(copy);
        \\    _ = &absolute;
        \\    blowUp(&absolute);
        \\    return @intFromFloat(16.0 * absolute);
        \\}
    );
}

test "intfromfloat-without-clamp: a generic mutable cast rounds a certified finite constant" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn convert(comptime T: type) u128 {
        \\    var value: T = @floatCast(std.math.floatMax(f32));
        \\    _ = &value;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn use() u128 { return convert(f16); }
    );
}

test "intfromfloat-without-clamp: a generic reassignment rounds at the stored format" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn convert(comptime T: type) u128 {
        \\    var value: T = 0;
        \\    value = @floatCast(std.math.floatMax(f32));
        \\    return @intFromFloat(value);
        \\}
        \\pub fn use() u128 { return convert(f16); }
    );
}

test "intfromfloat-without-clamp: every closed generic destination format must fit" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn convert(comptime T: type) u128 {
        \\    var value: T = @floatCast(std.math.floatMax(f32));
        \\    _ = &value;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn half() u128 { return convert(f16); }
        \\pub fn double() u128 { return convert(f64); }
    );
}

test "intfromfloat-without-clamp: an open generic store cannot retain a finite source bound" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn convert(comptime T: type) u128 {
        \\    var value: T = @floatCast(std.math.floatMax(f32));
        \\    _ = &value;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn use() u128 { return convert(f32); }
    );
}

test "intfromfloat-without-clamp: closed same and wider generic stores retain finite bounds" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn convert(comptime T: type) u128 {
        \\    var value: T = @floatCast(std.math.floatMax(f32));
        \\    _ = &value;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single() u128 { return convert(f32); }
        \\pub fn double() u128 { return convert(f64); }
    );
}

test "intfromfloat-without-clamp: a bounded constant remains finite in a closed half format" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn convert(comptime T: type) u16 {
        \\    var value: T = @floatCast(std.math.floatMax(f16));
        \\    _ = &value;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn use() u16 { return convert(f16); }
    );
}

test "intfromfloat-without-clamp: a closed generic same-format store keeps strict endpoints" {
    try testing.expectNoFireTyped(check,
        \\fn convert(comptime T: type, raw: T) u8 {
        \\    if (!(raw >= 0.0 and raw < 256.0)) return 0;
        \\    var value: T = raw;
        \\    _ = &value;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn use(raw: f32) u8 { return convert(f32, raw); }
    );
}

test "intfromfloat-without-clamp: mixed closed same-parameter stores keep strict endpoints" {
    try testing.expectNoFireTyped(check,
        \\fn convert(comptime T: type, raw: T) u8 {
        \\    if (!(raw >= 0.0 and raw < 256.0)) return 0;
        \\    var value: T = raw;
        \\    _ = &value;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(raw: f32) u8 { return convert(f32, raw); }
        \\pub fn double(raw: f64) u8 { return convert(f64, raw); }
    );
}

test "intfromfloat-without-clamp: mixed same-parameter cast aliases keep later guards" {
    try testing.expectNoFireTyped(check,
        \\fn convert(comptime T: type, raw: T) u8 {
        \\    var value: T = @as(T, @floatCast(raw));
        \\    _ = &value;
        \\    if (!(raw >= 0.0 and raw < 256.0)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(raw: f32) u8 { return convert(f32, raw); }
        \\pub fn double(raw: f64) u8 { return convert(f64, raw); }
    );
}

test "intfromfloat-without-clamp: distinct generic parameters can round to an excluded limit" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(comptime Source: type, comptime Destination: type, raw: Source) u8 {
        \\    if (!(raw >= 0.0 and raw < 256.0)) return 0;
        \\    var value: Destination = @as(Destination, @floatCast(raw));
        \\    _ = &value;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn narrow(raw: f64) u8 { return convert(f64, f32, raw); }
        \\pub fn widen(raw: f32) u8 { return convert(f32, f64, raw); }
    );
}

test "intfromfloat-without-clamp: same-parameter stores cannot undo inner half narrowing" {
    try testing.expectFiresTyped(check, R,
        \\fn convert(comptime T: type, raw: T) u8 {
        \\    var value: T = @floatCast(@as(f16, @floatCast(raw)));
        \\    _ = &value;
        \\    if (!(raw >= 0.0 and raw < 256.0)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(raw: f32) u8 { return convert(f32, raw); }
        \\pub fn double(raw: f64) u8 { return convert(f64, raw); }
    );
}

// ── the same conversions, compiled ─────────────────────────
//
// The fixtures above are read as source text.  These are the conversions
// themselves, so the expected results below are what `@intFromFloat` really
// returns rather than a re-derivation of it.  Every helper is local to the
// test that owns it, so none of this is library surface.  A reported shape is
// reached only through `comptime @export`, which is what makes the compiler
// analyze and emit a body nothing calls — no unsafe input is handed to one.

test "intfromfloat-without-clamp: the compiled strict-mask conversion converts what it accepts" {
    const Native = struct {
        /// The paired safe shape: the cutoff IS the destination's exclusive
        /// bound, so every input below is one it may be handed.
        fn strict_mask(value: f32) i64 {
            const bits: u32 = @bitCast(value);
            if ((bits & 0x7fff_ffff) < 0x5f00_0000) return @intFromFloat(value);
            return 0;
        }

        /// Reported shape: the finiteness mask admits every finite f32,
        /// magnitudes an i64 cannot take included.  Reached only by `export`.
        fn finite_mask(value: f32) callconv(.c) i64 {
            const bits: u32 = @bitCast(value);
            if ((bits & 0x7fff_ffff) < 0x7f80_0000) return @intFromFloat(value); // zbc-disable-line: intfromfloat-without-clamp — intentional unsafe control; the analyzer regression above judges it
            return 0;
        }

        /// Reported shape: that cutoff spelled inclusively, which admits
        /// 2^63.  Reached only by `export`.
        fn inclusive_mask(value: f32) callconv(.c) i64 {
            const bits: u32 = @bitCast(value);
            if ((bits & 0x7fff_ffff) <= 0x5f00_0000) return @intFromFloat(value); // zbc-disable-line: intfromfloat-without-clamp — intentional unsafe control; the analyzer regression above judges it
            return 0;
        }
    };

    comptime {
        @export(&Native.finite_mask, .{ .name = "zbc_intfromfloat_finite_mask" });
        @export(&Native.inclusive_mask, .{ .name = "zbc_intfromfloat_inclusive_mask" });
    }

    // 2^63 - 2^39 is the largest f32 below 2^63 and is itself an i64, so the
    // conversion there is exact; 2^63 is the first magnitude the cutoff turns
    // away, and no i64 holds it either way.
    try std.testing.expectEqual(@as(i64, 0), Native.strict_mask(0.0));
    try std.testing.expectEqual(@as(i64, 0), Native.strict_mask(-0.0));
    try std.testing.expectEqual(@as(i64, 42), Native.strict_mask(42.0));
    try std.testing.expectEqual(@as(i64, -42), Native.strict_mask(-42.0));
    try std.testing.expectEqual(@as(i64, 3), Native.strict_mask(3.5));
    try std.testing.expectEqual(@as(i64, -3), Native.strict_mask(-3.5));
    try std.testing.expectEqual(@as(i64, 9223371487098961920), Native.strict_mask(0x1.fffffep62));
    try std.testing.expectEqual(@as(i64, -9223371487098961920), Native.strict_mask(-0x1.fffffep62));
    try std.testing.expectEqual(@as(i64, 0), Native.strict_mask(0x1p63));
    try std.testing.expectEqual(@as(i64, 0), Native.strict_mask(-0x1p63));
    try std.testing.expectEqual(@as(i64, 0), Native.strict_mask(std.math.nan(f32)));
    try std.testing.expectEqual(@as(i64, 0), Native.strict_mask(std.math.inf(f32)));
    try std.testing.expectEqual(@as(i64, 0), Native.strict_mask(-std.math.inf(f32)));
}

test "intfromfloat-without-clamp: the compiled copy-only consumer keeps its bound" {
    const Native = struct {
        /// Handed a copy, so it cannot move what the conversion reads.
        fn probe(value: f64) bool {
            return std.math.isFinite(value);
        }

        fn copy_only(raw: f64) u64 {
            const x = raw;
            if (x < 0 or x > 1e18) return 0;
            if (std.math.isFinite(x) and probe(x)) return @intFromFloat(x);
            return 0;
        }

        /// Reported shape: `isFinite(x)` is true for the value `rewrite` is
        /// handed, and `rewrite` leaves `x` a NaN.  Reached only by `export`.
        fn rewrite(value: *f64) bool {
            value.* = std.math.nan(f64);
            return true;
        }

        fn rewrite_convert(raw: f64) callconv(.c) u64 {
            var x = raw;
            if (x < 0 or x > 1e18) return 0;
            if (std.math.isFinite(x) and rewrite(&x)) return @intFromFloat(x); // zbc-disable-line: intfromfloat-without-clamp — intentional unsafe control; the analyzer regression above judges it
            return 0;
        }
    };

    comptime {
        @export(&Native.rewrite_convert, .{ .name = "zbc_intfromfloat_rewrite_convert" });
    }

    try std.testing.expectEqual(@as(u64, 42), Native.copy_only(42.0));
    try std.testing.expectEqual(@as(u64, 0), Native.copy_only(-1.0));
    try std.testing.expectEqual(@as(u64, 1000000000000000000), Native.copy_only(1e18));
    try std.testing.expectEqual(@as(u64, 0), Native.copy_only(std.math.nan(f64)));
    try std.testing.expectEqual(@as(u64, 0), Native.copy_only(std.math.inf(f64)));
    try std.testing.expectEqual(@as(u64, 0), Native.copy_only(-std.math.inf(f64)));
}

test "intfromfloat-without-clamp: concrete finite truncation controls cover the generic callers' domains" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn byte(value: f64) error{TypeMismatch}!u8 {
        \\    if (!std.math.isFinite(value)) return error.TypeMismatch;
        \\    const truncated = @trunc(value);
        \\    if (truncated < 0.0 or truncated >= 256.0) return error.TypeMismatch;
        \\    return @intFromFloat(truncated);
        \\}
        \\pub fn signed(value: f64) error{TypeMismatch}!c_int {
        \\    if (!std.math.isFinite(value)) return error.TypeMismatch;
        \\    const truncated = @trunc(value);
        \\    if (truncated < -2147483648.0 or truncated >= 2147483648.0) return error.TypeMismatch;
        \\    return @intFromFloat(truncated);
        \\}
        \\pub fn unsigned(value: f64) error{TypeMismatch}!c_uint {
        \\    if (!std.math.isFinite(value)) return error.TypeMismatch;
        \\    const truncated = @trunc(value);
        \\    if (truncated < 0.0 or truncated >= 4294967296.0) return error.TypeMismatch;
        \\    return @intFromFloat(truncated);
        \\}
    );
}

test "intfromfloat-without-clamp: generic wide bounds cannot prove a narrow instantiation" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checked(comptime T: type, value: f64) error{TypeMismatch}!T {
        \\    if (!std.math.isFinite(value)) return error.TypeMismatch;
        \\    const truncated = @trunc(value);
        \\    const lower: f64 = @floatFromInt(std.math.minInt(c_int));
        \\    const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(c_uint))) + 1.0;
        \\    if (truncated < lower or truncated >= upper) return error.TypeMismatch;
        \\    return @intFromFloat(truncated);
        \\}
        \\pub fn byte(value: f64) error{TypeMismatch}!u8 { return checked(u8, value); }
        \\pub fn signed(value: f64) error{TypeMismatch}!c_int { return checked(c_int, value); }
        \\pub fn unsigned(value: f64) error{TypeMismatch}!c_uint { return checked(c_uint, value); }
    );
}

test "intfromfloat-without-clamp: generic truncation without finite rejection still admits NaN" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checked(comptime T: type, value: f64) error{TypeMismatch}!T {
        \\    const truncated = @trunc(value);
        \\    const lower: f64 = @floatFromInt(std.math.minInt(T));
        \\    const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
        \\    if (truncated < lower or truncated >= upper) return error.TypeMismatch;
        \\    return @intFromFloat(truncated);
        \\}
        \\pub fn byte(value: f64) error{TypeMismatch}!u8 { return checked(u8, value); }
        \\pub fn signed(value: f64) error{TypeMismatch}!c_int { return checked(c_int, value); }
    );
}

test "intfromfloat-without-clamp: generic inclusive exclusive-bound guard remains unsafe" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checked(comptime T: type, value: f64) error{TypeMismatch}!T {
        \\    if (!std.math.isFinite(value)) return error.TypeMismatch;
        \\    const truncated = @trunc(value);
        \\    const lower: f64 = @floatFromInt(std.math.minInt(T));
        \\    const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
        \\    if (truncated < lower or truncated > upper) return error.TypeMismatch;
        \\    return @intFromFloat(truncated);
        \\}
        \\pub fn byte(value: f64) error{TypeMismatch}!u8 { return checked(u8, value); }
        \\pub fn signed(value: f64) error{TypeMismatch}!c_int { return checked(c_int, value); }
    );
}

test "intfromfloat-without-clamp: test-local generic finite truncation covers every boundary and inline tuple call" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\test "native" {
        \\    const Native = struct {
        \\        fn checked(comptime T: type, source: anytype) error{TypeMismatch}!T {
        \\            const value: f64 = @floatCast(source);
        \\            if (!std.math.isFinite(value)) return error.TypeMismatch;
        \\            const truncated = @trunc(value);
        \\            const lower: f64 = @floatFromInt(std.math.minInt(T));
        \\            const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
        \\            if (truncated < lower or truncated >= upper) return error.TypeMismatch;
        \\            return @intFromFloat(truncated);
        \\        }
        \\    };
        \\    try std.testing.expectEqual(@as(u8, 0), try Native.checked(u8, @as(f64, -0.5)));
        \\    try std.testing.expectEqual(@as(u8, 255), try Native.checked(u8, @as(f64, 255.75)));
        \\    try std.testing.expectError(error.TypeMismatch, Native.checked(u8, @as(f64, -1.0)));
        \\    try std.testing.expectError(error.TypeMismatch, Native.checked(u8, @as(f64, 256.0)));
        \\    try std.testing.expectEqual(@as(c_int, -42), try Native.checked(c_int, @as(f32, -42.75)));
        \\    try std.testing.expectEqual(std.math.minInt(c_int), try Native.checked(c_int, @as(f64, -2147483648.0)));
        \\    try std.testing.expectEqual(std.math.maxInt(c_int), try Native.checked(c_int, @as(f64, 2147483647.75)));
        \\    try std.testing.expectError(error.TypeMismatch, Native.checked(c_int, @as(f64, -2147483649.0)));
        \\    try std.testing.expectError(error.TypeMismatch, Native.checked(c_int, @as(f32, 2147483648.0)));
        \\    try std.testing.expectEqual(@as(c_uint, 42), try Native.checked(c_uint, @as(f16, 42.75)));
        \\    try std.testing.expectEqual(std.math.maxInt(c_uint), try Native.checked(c_uint, @as(f64, 4294967295.75)));
        \\    try std.testing.expectError(error.TypeMismatch, Native.checked(c_uint, @as(f16, -1.0)));
        \\    try std.testing.expectError(error.TypeMismatch, Native.checked(c_uint, @as(f64, 4294967296.0)));
        \\    inline for (.{ u8, c_int, c_uint }) |T| {
        \\        try std.testing.expectError(error.TypeMismatch, Native.checked(T, std.math.nan(f64)));
        \\        try std.testing.expectError(error.TypeMismatch, Native.checked(T, std.math.inf(f64)));
        \\        try std.testing.expectError(error.TypeMismatch, Native.checked(T, -std.math.inf(f64)));
        \\    }
        \\}
    );
}

test "intfromfloat-without-clamp: test-local generic inline tuple calls retain unsafe controls" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\test "native" {
        \\    const Native = struct {
        \\        fn checked(comptime T: type, source: anytype) error{TypeMismatch}!T {
        \\            const value: f64 = @floatCast(source);
        \\            if (!std.math.isFinite(value)) return error.TypeMismatch;
        \\            const truncated = @trunc(value);
        \\            const lower: f64 = @floatFromInt(std.math.minInt(T));
        \\            const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
        \\            if (truncated < lower or truncated > upper) return error.TypeMismatch;
        \\            return @intFromFloat(truncated);
        \\        }
        \\    };
        \\    inline for (.{ u8, c_int, c_uint }) |T| {
        \\        _ = Native.checked(T, @as(f64, 256.0)) catch 0;
        \\    }
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\test "native" {
        \\    const Native = struct {
        \\        fn checked(comptime T: type, source: anytype) error{TypeMismatch}!T {
        \\            const value: f64 = @floatCast(source);
        \\            const truncated = @trunc(value);
        \\            const lower: f64 = @floatFromInt(std.math.minInt(T));
        \\            const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
        \\            if (truncated < lower or truncated >= upper) return error.TypeMismatch;
        \\            return @intFromFloat(truncated);
        \\        }
        \\    };
        \\    inline for (.{ u8, c_int, c_uint }) |T| {
        \\        _ = Native.checked(T, std.math.nan(f64)) catch 0;
        \\    }
        \\}
    );
}

test "intfromfloat-without-clamp: unrelated unresolved methods require a complete nonescaping census" {
    const safe =
        \\const std = @import("std");
        \\fn unrelated(bounds: anytype) bool { return bounds.fitsInteger(8, false); }
        \\test "native" {
        \\    const Native = struct {
        \\        fn checked(comptime T: type, source: anytype) error{Bad}!T {
        \\            const value: f64 = @floatCast(source);
        \\            if (!std.math.isFinite(value)) return error.Bad;
        \\            const truncated = @trunc(value);
        \\            const lower: f64 = @floatFromInt(std.math.minInt(T));
        \\            const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
        \\            if (truncated < lower or truncated >= upper) return error.Bad;
        \\            return @intFromFloat(truncated);
        \\        }
        \\    };
        \\    _ = Native.checked(u8, @as(f64, 42)) catch 0;
        \\}
    ;
    try testing.expectNoFireTyped(check, safe);
    const gpa = std.testing.allocator;
    const inclusive = try std.mem.replaceOwned(u8, gpa, safe, "truncated >= upper", "truncated > upper");
    defer gpa.free(inclusive);
    try testing.expectFiresTyped(check, R, inclusive);
    const no_finite = try std.mem.replaceOwned(u8, gpa, safe, "if (!std.math.isFinite(value)) return error.Bad;", "");
    defer gpa.free(no_finite);
    try testing.expectFiresTyped(check, R, no_finite);
    const alias = try std.mem.replaceOwned(u8, gpa, safe, "_ = Native.checked", "const callback = Native.checked; _ = callback");
    defer gpa.free(alias);
    try testing.expectFiresTyped(check, R, alias);
    const unknown_same_name = try std.mem.replaceOwned(u8, gpa, safe, "bounds.fitsInteger", "bounds.checked");
    defer gpa.free(unknown_same_name);
    try testing.expectFiresTyped(check, R, unknown_same_name);
    const reflective = try std.mem.replaceOwned(u8, gpa, safe, "bounds.fitsInteger", "@field(bounds, \"fitsInteger\")");
    defer gpa.free(reflective);
    try testing.expectFiresTyped(check, R, reflective);
    const namespace = try std.mem.replaceOwned(u8, gpa, safe, "_ = Native.checked", "unknown_owner.invoke(Native); _ = Native.checked");
    defer gpa.free(namespace);
    try testing.expectFiresTyped(check, R, namespace);
    const instance_type = try std.mem.replaceOwned(u8, gpa, safe, "_ = Native.checked", "unknown_owner.invoke(@TypeOf(Native{})); _ = Native.checked");
    defer gpa.free(instance_type);
    try testing.expectFiresTyped(check, R, instance_type);
    const nested_owner = try std.mem.replaceOwned(u8, gpa, safe, "const Native = struct", "const Outer = struct { const Native = struct");
    defer gpa.free(nested_owner);
    const nested_transport = try std.mem.replaceOwned(u8, gpa, nested_owner, "_ = Native.checked(u8, @as(f64, 42)) catch 0;", "fn run() void { _ = Native.checked(u8, @as(f64, 42)) catch 0; } }; unknown_owner.invoke(Outer);");
    defer gpa.free(nested_transport);
    try testing.expectFiresTyped(check, R, nested_transport);
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn unrelated(bounds: anytype) bool { return bounds.fitsInteger(8, false); }
        \\test "native" {
        \\    unknown_owner.invoke(struct {
        \\        fn checked(comptime T: type, source: anytype) error{Bad}!T {
        \\            const value: f64 = @floatCast(source);
        \\            if (!std.math.isFinite(value)) return error.Bad;
        \\            const truncated = @trunc(value);
        \\            const lower: f64 = @floatFromInt(std.math.minInt(T));
        \\            const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
        \\            if (truncated < lower or truncated >= upper) return error.Bad;
        \\            return @intFromFloat(truncated);
        \\        }
        \\        fn run() void { _ = @This().checked(u8, @as(f64, 42)) catch 0; }
        \\    });
        \\}
    );
}

test "intfromfloat-without-clamp: compiled generic finite truncation checks each instantiated boundary" {
    const Native = struct {
        fn checked(comptime T: type, source: anytype) error{TypeMismatch}!T {
            const value: f64 = @floatCast(source);
            if (!std.math.isFinite(value)) return error.TypeMismatch;
            const truncated = @trunc(value);
            const lower: f64 = @floatFromInt(std.math.minInt(T));
            const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
            if (truncated < lower or truncated >= upper) return error.TypeMismatch;
            return @intFromFloat(truncated);
        }
    };

    try std.testing.expectEqual(@as(u8, 0), try Native.checked(u8, @as(f64, -0.5)));
    try std.testing.expectEqual(@as(u8, 255), try Native.checked(u8, @as(f64, 255.75)));
    try std.testing.expectError(error.TypeMismatch, Native.checked(u8, @as(f64, -1.0)));
    try std.testing.expectError(error.TypeMismatch, Native.checked(u8, @as(f64, 256.0)));
    try std.testing.expectEqual(@as(c_int, -42), try Native.checked(c_int, @as(f32, -42.75)));
    try std.testing.expectEqual(std.math.minInt(c_int), try Native.checked(c_int, @as(f64, -2147483648.0)));
    try std.testing.expectEqual(std.math.maxInt(c_int), try Native.checked(c_int, @as(f64, 2147483647.75)));
    try std.testing.expectError(error.TypeMismatch, Native.checked(c_int, @as(f64, -2147483649.0)));
    try std.testing.expectError(error.TypeMismatch, Native.checked(c_int, @as(f32, 2147483648.0)));
    try std.testing.expectEqual(@as(c_uint, 42), try Native.checked(c_uint, @as(f16, 42.75)));
    try std.testing.expectEqual(std.math.maxInt(c_uint), try Native.checked(c_uint, @as(f64, 4294967295.75)));
    try std.testing.expectError(error.TypeMismatch, Native.checked(c_uint, @as(f16, -1.0)));
    try std.testing.expectError(error.TypeMismatch, Native.checked(c_uint, @as(f64, 4294967296.0)));
    inline for (.{ u8, c_int, c_uint }) |T| {
        try std.testing.expectError(error.TypeMismatch, Native.checked(T, std.math.nan(f64)));
        try std.testing.expectError(error.TypeMismatch, Native.checked(T, std.math.inf(f64)));
        try std.testing.expectError(error.TypeMismatch, Native.checked(T, -std.math.inf(f64)));
    }
}

test "intfromfloat-without-clamp: generic anytype truncation checks each concrete result location" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn convert(byte: f64, signed: f32, unsigned: f16) !void {
        \\    const Native = struct {
        \\        fn checked(comptime T: type, source: anytype) !T {
        \\            const value: f64 = @floatCast(source);
        \\            if (!std.math.isFinite(value)) return error.Bad;
        \\            const truncated = @trunc(value);
        \\            const lower: f64 = @floatFromInt(std.math.minInt(T));
        \\            const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
        \\            if (truncated < lower or truncated >= upper) return error.Bad;
        \\            return @intFromFloat(truncated);
        \\        }
        \\    };
        \\    _ = try Native.checked(u8, byte);
        \\    _ = try Native.checked(c_int, signed);
        \\    _ = try Native.checked(c_uint, unsigned);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn checked(comptime T: type, source: anytype) !T {
        \\    const value: f64 = @floatCast(source);
        \\    if (!std.math.isFinite(value)) return error.Bad;
        \\    const truncated = @trunc(value);
        \\    const lower: f64 = @floatFromInt(std.math.minInt(T));
        \\    const upper: f64 = @as(f64, @floatFromInt(std.math.maxInt(T))) + 1.0;
        \\    if (truncated < lower or truncated > upper) return error.Bad;
        \\    return @intFromFloat(truncated);
        \\}
        \\pub fn convert(value: f64) !u8 { return checked(u8, value); }
    );
}

test "intfromfloat-without-clamp: floating integer width clamps retain rounded boundary hazards" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn pixel(point: f32, extent: u32) usize {
        \\    const highest: f32 = @floatFromInt(extent);
        \\    return @intFromFloat(std.math.clamp(point, 0, highest));
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn pixel(point: f32, extent: u32) u32 {
        \\    const highest: f32 = @floatFromInt(extent);
        \\    return @intFromFloat(std.math.clamp(point, 0, highest));
        \\}
    );
}

test "intfromfloat-without-clamp: immutable floating constants supply conversion bounds" {
    try testing.expectNoFireTyped(check,
        \\const Extent = struct { width: f32, height: f32 };
        \\const surface: Extent = .{ .width = 520, .height = 480 };
        \\const limit: f64 = 4503599627370496.0;
        \\pub fn width() u32 { return @intFromFloat(surface.width); }
        \\pub fn count() usize { return @intFromFloat(limit); }
    );
    try testing.expectFiresTyped(check, R,
        \\const Extent = struct { width: f32 };
        \\const surface: Extent = .{ .width = 4294967295.0 };
        \\pub fn width() u32 { return @intFromFloat(surface.width); }
    );
    try testing.expectFiresTyped(check, R,
        \\const Extent = struct { width: f32 };
        \\const surface: Extent = .{ .width = 520 };
        \\pub fn width(surface: Extent) u32 { return @intFromFloat(surface.width); }
    );
    try testing.expectFiresTyped(check, R,
        \\const Extent = struct { width: f32 };
        \\var storage: Extent = .{ .width = 520 };
        \\const surface = &storage;
        \\pub fn width() u32 { return @intFromFloat(surface.width); }
    );
}
