//! Report midpoint sums without a proved non-overflowing integer range.
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

const R = "midpoint-addition-overflow";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .midpoint_addition_overflow)) return;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [2]Ast.Node.Index = undefined;
        const operands: [2]Ast.Node.Index = switch (tag) {
            .div => tree.nodeData(node).node_and_node,
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => blk: {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (!std.mem.eql(u8, name, "@divTrunc") and
                    !std.mem.eql(u8, name, "@divFloor") and
                    !std.mem.eql(u8, name, "@divExact")) continue;
                const params = tree.builtinCallParams(&buffer, node).?;
                if (params.len != 2) continue;
                break :blk .{ params[0], params[1] };
            },
            else => continue,
        };
        if (tree.nodeTag(operands[1]) != .number_literal) continue;
        const divisor = std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(operands[1])), 0) catch continue;
        if (divisor != 2) continue;
        const sum = addition(tree, operands[0]) orelse continue;
        if (cache.isFloatType(sum) == true) continue;
        const token = tree.firstToken(sum);
        const declaration = tokens.enclosingFnDecl(tree, token) orelse continue;
        if (!isRuntimeUse(tree, declaration, token)) continue;
        // two operands are bounded where they are read and combined here.
        // Asking for the sum's own range instead would answer a different
        // question: the evaluator reads every integer result back through
        // the type it is written in, because a value outside that type is
        // either a trap or a wrap and never observable.  That clamp is
        // right for "can this expression produce something out of range"
        // and useless here — every sum fits its own type by construction,
        // which is exactly what this rule reports.
        if (cache.intInfoOf(sum)) |integer| {
            const body = tokens.bodyOf(tree, declaration).?;
            const addends = tree.nodeData(sum).node_and_node;
            const left = try value_range.boundsAt(gpa, tree, body, addends[0], token, cache);
            const right = try value_range.boundsAt(gpa, tree, body, addends[1], token, cache);
            if (value_range.NumericRange.binary(left, right, .add).fitsInteger(integer.bits, integer.signed)) continue;
        }
        const message = try gpa.dupe(u8, "the midpoint sum was not proved to fit its integer type before division; prove bounds for the addition or widen the operands before adding");
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
/// itself, so an addition that can only ever run there is not a
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

fn addition(tree: *const Ast, original: Ast.Node.Index) ?Ast.Node.Index {
    var node = original;
    for (0..64) |_| {
        if (tree.nodeTag(node) == .add) return node;
        if (tree.nodeTag(node) != .grouped_expression) return null;
        node = tree.nodeData(node).node_and_token[0];
    }
    return null;
}

test "midpoint-addition-overflow: range proof accepts bounded operands" {
    try testing.expectNoFireTyped(check,
        \\fn middle(left: u32, right: u32) u32 {
        \\    if (left > 100 or right > 100) return 0;
        \\    return (left + right) / 2;
        \\}
    );
}

test "midpoint-addition-overflow: range proof ignores unrelated float declarations" {
    try testing.expectFiresTyped(check, R,
        \\fn middle(x: u32, y: u32) u32 {
        \\    const left = x;
        \\    const scale: f32 = 0.0;
        \\    _ = scale;
        \\    const right = y;
        \\    return (left + right) / 2;
        \\}
    );
}

test "midpoint-addition-overflow: unbounded sum remains uncertain" {
    try testing.expectFiresTyped(check, R,
        \\fn midpoint(left: usize, right: usize) usize { return (left + right) / 2; }
    );
}

test "midpoint-addition-overflow: floating arithmetic is not integer overflow" {
    try testing.expectNoFireTyped(check,
        \\fn midpoint(left: f64, right: f64) f64 { return (left + right) / 2; }
    );
}

test "midpoint-addition-overflow: subtraction formulation is outside this rule" {
    try testing.expectNoFireTyped(check,
        \\fn midpoint(left: usize, right: usize) usize { return left + (right - left) / 2; }
    );
}

test "midpoint-addition-overflow: loop induction proves a fixed table envelope" {
    try testing.expectNoFireTyped(check,
        \\fn search(value: f64, table: *const [29]f64) usize {
        \\    var lower: usize = 0;
        \\    var upper: usize = table.len;
        \\    while (lower + 1 < upper) {
        \\        const middle = (lower + upper) / 2;
        \\        if (table[middle] < value) lower = middle else upper = middle;
        \\    }
        \\    return lower;
        \\}
    );
}

test "midpoint-addition-overflow: loop induction rejects a growing upper bound" {
    try testing.expectFiresTyped(check, R,
        \\fn search(table: *const [256]bool) u8 {
        \\    var lower: u8 = 0;
        \\    var upper: u8 = 100;
        \\    while (lower + 1 < upper) {
        \\        const middle = (lower + upper) / 2;
        \\        if (table[middle]) lower = middle else upper += 100;
        \\    }
        \\    return lower;
        \\}
    );
}

test "midpoint-addition-overflow: signed division builtins retain addition risk" {
    try testing.expectFiresTyped(check, R,
        \\fn midpoint(left: i32, right: i32) i32 {
        \\    return @divTrunc(left + right, 2);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\fn midpoint(left: i32, right: i32) i32 {
        \\    if (left < -100 or left > 100 or right < -100 or right > 100) return 0;
        \\    return @divFloor(left + right, 2);
        \\}
    );
}

test "midpoint-addition-overflow: body invariants exclude terminating search states" {
    try testing.expectNoFireTyped(check,
        \\fn search(value: i64, table: *const [97]i64) i32 {
        \\    var lower: i32 = 0;
        \\    var upper: i32 = @intCast(table.len - 1);
        \\    while (lower <= upper) {
        \\        const middle = @divTrunc(lower + upper, 2);
        \\        const element = table[@intCast(middle)];
        \\        if (element < value) lower = middle + 1
        \\        else if (element > value) upper = middle - 1
        \\        else return middle;
        \\    }
        \\    return -1;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn search(value: i64, table: *const [97]i64) i8 {
        \\    var lower: i8 = 0;
        \\    var upper: i8 = @intCast(table.len - 1);
        \\    while (lower <= upper) {
        \\        const middle = @divTrunc(lower + upper, 2);
        \\        const element = table[@intCast(middle)];
        \\        if (element < value) lower = middle + 1
        \\        else if (element > value) upper = middle - 1
        \\        else return middle;
        \\    }
        \\    return -1;
        \\}
    );
}

test "midpoint-addition-overflow: nested searches preserve only unchanged outer bounds" {
    try testing.expectNoFireTyped(check,
        \\fn search(value: i64, table: *const [97]i64) i32 {
        \\    var lower: i32 = 0;
        \\    var upper: i32 = @intCast(table.len - 1);
        \\    while (lower <= upper) {
        \\        const middle = @divTrunc(lower + upper, 2);
        \\        const element = table[@intCast(middle)];
        \\        if (element < value) lower = middle + 1
        \\        else if (element > value) upper = middle - 1
        \\        else {
        \\            var offset: i8 = -1;
        \\            while (offset <= 1) : (offset += 1) {
        \\                if (offset == 0) return middle;
        \\            }
        \\            break;
        \\        }
        \\    }
        \\    return -1;
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\fn growing(limit: u8) u8 {
        \\    const lower: u8 = 16;
        \\    var upper: u8 = 96;
        \\    while (lower <= upper) {
        \\        const middle = (lower + upper) / 2;
        \\        if (middle == limit) return middle;
        \\        var index: u8 = 0;
        \\        while (index < 2) : (index += 1) upper += 1;
        \\    }
        \\    return 0;
        \\}
    );
}

// ── #75c3: the row count is the whole proof ─────────────────────────────
//
// zmath's `scalar_asin.zig:426` searches a 29-row database with `i8`
// bounds, so both bounds stay below 29 and their sum never passes 56 —
// inside `i8`.  The same search over 97 rows reaches 96 + 96 = 192, which
// `i8` cannot hold.  The row count is the whole difference between the
// two, and the boundary it crosses is 64: an `i8` envelope carries
// `2 * (rows - 1)` up to there and no further.

test "midpoint-addition-overflow: #75c3 a 29-row i8 envelope fits its sum, 97 rows do not" {
    // `undefined` is all this source says about the table and all it has
    // to say: only the TYPE is read, and a source that is analyzed is
    // never run, so the element reads another rule would ask about are
    // text here.  The compiled mirror below is the one that executes, and
    // it differs from this in nothing but an initialized table.
    try testing.expectNoFireTyped(check,
        \\const table: [29]i64 = undefined;
        \\
        \\// The table fits, but the i8 DESTINATION of the midpoint sum does not.
        \\pub fn search(value: i64) i8 {
        \\    var lower: i8 = 0;
        \\    var upper: i8 = @intCast(table.len - 1);
        \\    while (lower <= upper) {
        \\        const middle: i8 = @divTrunc(lower + upper, 2);
        \\        if (table[@intCast(middle)] < value) lower = middle + 1 else upper = middle - 1;
        \\    }
        \\    return lower;
        \\}
    );
    // One row count wider and nothing else changed: the envelope reaches
    // 96 on both bounds, and 96 + 96 leaves `i8`.
    try testing.expectFiresTyped(check, R,
        \\const table: [97]i64 = undefined;
        \\
        \\// The table fits, but the i8 DESTINATION of the midpoint sum does not.
        \\pub fn search(value: i64) i8 {
        \\    var lower: i8 = 0;
        \\    var upper: i8 = @intCast(table.len - 1);
        \\    while (lower <= upper) {
        \\        const middle: i8 = @divTrunc(lower + upper, 2);
        \\        if (table[@intCast(middle)] < value) lower = middle + 1 else upper = middle - 1;
        \\    }
        \\    return lower;
        \\}
    );
}

// ── #75c1: a private helper's bound is its callers' ─────────────────────
//
// zmath's `exceptionLookup` takes the row count it searches as a
// `comptime` argument, and every call site passes a fixed table length.
// The single caller below is the whole proof: it is the only call this
// file spells, and a caller set the cache cannot close is no answer at
// all rather than a partial one.

test "midpoint-addition-overflow: #75c1 one caller fixes the count the exception lookup searches" {
    try testing.expectNoFireTyped(check,
        \\fn exceptionLookup(comptime n: usize, key: usize) usize {
        \\    var a: usize = 0;
        \\    const b: usize = n - 1;
        \\    while (a + 1 < b) {
        \\        const m = (a + b) / 2;
        \\        if (key == m) return m;
        \\        a = m;
        \\    }
        \\    return a;
        \\}
        \\pub fn lookupSmall(key: usize) usize {
        \\    return exceptionLookup(5, key);
        \\}
    );
    // The same helper and the same single caller with the count widened to
    // `maxInt(usize)`: `b` is then `maxInt(usize) - 1` and `a` walks for
    // it, so the sum has nothing left to prove itself by.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn exceptionLookup(comptime n: usize, key: usize) usize {
        \\    var a: usize = 0;
        \\    const b: usize = n - 1;
        \\    while (a + 1 < b) {
        \\        const m = (a + b) / 2;
        \\        if (key == m) return m;
        \\        a = m;
        \\    }
        \\    return a;
        \\}
        \\pub fn lookupSmall(key: usize) usize {
        \\    return exceptionLookup(std.math.maxInt(usize), key);
        \\}
    );
}

test "midpoint-addition-overflow: unrelated nested exports retain only closed caller bounds" {
    try testing.expectNoFireTyped(check,
        \\test "native" {
        \\    const Native = struct {
        \\        fn exceptionLookup(comptime n: usize, key: usize) usize {
        \\            var a: usize = 0;
        \\            const b: usize = n - 1;
        \\            while (a + 1 < b) {
        \\                const m = (a + b) / 2;
        \\                if (key == m) return m;
        \\                a = m;
        \\            }
        \\            return a;
        \\        }
        \\        fn unrelated(key: usize) callconv(.c) usize { return key; }
        \\    };
        \\    comptime { @export(&Native.unrelated, .{ .name = "unrelated" }); }
        \\    _ = Native.exceptionLookup(5, 0);
        \\    _ = Native.exceptionLookup(5, 3);
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\test "native" {
        \\    const Native = struct {
        \\        fn exceptionLookup(comptime n: usize, key: usize) usize {
        \\            var a: usize = 0;
        \\            const b: usize = n - 1;
        \\            while (a + 1 < b) {
        \\                const m = (a + b) / 2;
        \\                if (key == m) return m;
        \\                a = m;
        \\            }
        \\            return a;
        \\        }
        \\        fn lookup(key: usize) callconv(.c) usize {
        \\            return exceptionLookup(std.math.maxInt(usize), key);
        \\        }
        \\        fn unrelated(key: usize) callconv(.c) usize { return key; }
        \\    };
        \\    comptime {
        \\        @export(&Native.unrelated, .{ .name = "unrelated" });
        \\        @export(&Native.lookup, .{ .name = "lookup" });
        \\    }
        \\}
    );
}

// ── #02c0: a real overflow, and the width that removes it ──────────────

test "midpoint-addition-overflow: #02c0 the ceiling helper overflows u64 on every non-zero input" {
    // `f` calls `ceil` only with `x != 0`, and one is the smallest value
    // that reaches the sum: `x + 2^64 - 1` leaves `u64` from there up, so
    // the caller's guard narrows nothing that would make it safe.
    try testing.expectFiresTyped(check, R,
        \\fn ceil(x: u64) u64 {
        \\    return (x + 18446744073709551615) / 2;
        \\}
        \\pub fn f(x: u64, bytes: []const u8) u8 {
        \\    if (x != 0) {
        \\        const n = ceil(x);
        \\        return bytes[n - 1];
        \\    }
        \\    return 0;
        \\}
    );
}

// ── the same code, compiled ─────────────────────────────────────────────
//
// The fixtures above are read as source text.  These are the search, the
// lookup and the sums themselves, so the results asserted below are what
// the arithmetic really returns rather than a re-derivation of it.  Every
// helper is local to the test that owns it, so none of this is library
// surface.  A body the analyzer is meant to report is reached only
// through `comptime @export` of a plain `callconv(.c)` wrapper — a
// `comptime`-parameter helper cannot carry an export itself — and no
// unsafe input is ever handed to one.

test "midpoint-addition-overflow: the compiled 29-row search returns the row it stops on" {
    const Native = struct {
        /// The original table with the values the analyzer fixture leaves
        /// `undefined`: there only the LENGTH is at issue, and this copy
        /// is read to answer anything.
        const table: [29]i64 = .{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28 };

        fn search(value: i64) i8 {
            var lower: i8 = 0;
            var upper: i8 = @intCast(table.len - 1);
            while (lower <= upper) {
                const middle: i8 = @divTrunc(lower + upper, 2);
                if (table[@intCast(middle)] < value) lower = middle + 1 else upper = middle - 1;
            }
            return lower;
        }
    };
    // table[i] == i, so the search answers the first row at or above the
    // value it is handed, and a value past the last row answers past it.
    try std.testing.expectEqual(@as(i8, 0), Native.search(0));
    try std.testing.expectEqual(@as(i8, 5), Native.search(5));
    try std.testing.expectEqual(@as(i8, 29), Native.search(29));
}

test "midpoint-addition-overflow: the compiled exception lookup answers 3 for a five-row table" {
    // The safe class, and the only helper here with no suppression: every
    // call in this file hands it 5, so `b` is 4 and `a` stays under it,
    // and the analyzer has to say that from the callers alone.
    const Native = struct {
        fn exceptionLookup(comptime n: usize, key: usize) usize {
            var a: usize = 0;
            const b: usize = n - 1;
            while (a + 1 < b) {
                const m = (a + b) / 2;
                if (key == m) return m;
                a = m;
            }
            return a;
        }
    };
    // n == 5 puts b at 4 and a walks 2, 3: key 0 walks the whole way and
    // leaves a at 3, and key 3 stops on the row it names.
    try std.testing.expectEqual(@as(usize, 3), Native.exceptionLookup(5, 0));
    try std.testing.expectEqual(@as(usize, 3), Native.exceptionLookup(5, 3));

    // The unsafe class is a separate helper for that reason: the same body
    // with a count nothing bounds.  The wrapper carries the export, since
    // the helper cannot, and nothing calls it.
    const Unsafe = struct {
        fn exceptionLookup(comptime n: usize, key: usize) usize {
            var a: usize = 0;
            const b: usize = n - 1;
            while (a + 1 < b) {
                const m = (a + b) / 2; // zbc-disable-line: midpoint-addition-overflow — intentional unsafe control; the wrapper below hands this helper std.math.maxInt(usize) rows
                if (key == m) return m;
                a = m;
            }
            return a;
        }

        fn lookupAll(key: usize) callconv(.c) usize {
            return exceptionLookup(std.math.maxInt(usize), key);
        }
    };
    comptime {
        @export(&Unsafe.lookupAll, .{ .name = "zbc_midpoint_75c1_lookup_all" });
    }
}

test "midpoint-addition-overflow: the compiled ceiling sum leaves u64 where the widened one does not" {
    const Native = struct {
        /// Reported shape: every non-zero `x` sends `x + 2^64 - 1` past
        /// `u64`'s maximum.  Reached only by `export`.
        fn ceil(x: u64) callconv(.c) u64 {
            return (x + 18446744073709551615) / 2; // zbc-disable-line: midpoint-addition-overflow — intentional unsafe control; the analyzer regression above judges it
        }

        /// The repair: the sum is formed in `u128`, where `2 * (2^64 - 1)`
        /// still fits, and the halved result — `[2^63 - 1, 2^64 - 1]`, the
        /// range the cast back needs — is what comes home to `u64`.
        fn wide_ceil(x: u64) u64 {
            const sum = @as(u128, x) + @as(u128, 18446744073709551615);
            return @intCast(sum / 2);
        }
    };
    comptime {
        @export(&Native.ceil, .{ .name = "zbc_midpoint_02c0_ceil" });
    }
    // (1 + 2^64 - 1) / 2 is 2^63, and the largest sum halved is itself.
    try std.testing.expectEqual(@as(u64, 9223372036854775808), Native.wide_ceil(1));
    try std.testing.expectEqual(@as(u64, 18446744073709551615), Native.wide_ceil(18446744073709551615));
}
