//! Detects `x < A and x > B` — a range validation that uses `and` instead
//! of `or`, making the guard permanently dead.
//!
//! No value can be simultaneously less than A and greater than B (when A ≤ B),
//! so the `if` body is unreachable.  The correct out-of-range check is
//! `x < A or x > B`.  Note: `x > A and x < B` is the valid *in-range* check
//! and is NOT flagged by this rule.
//!
//! Real-world shape: oven-sh/bun#25905 (S3 credentials validation)
//!   Three adjacent copy-paste occurrences in `s3/credentials.zig`:
//!     pageSize < MIN and pageSize > MAX
//!     partSize < MIN and partSize > MAX
//!     retry   < 0   and retry   > 255
//!   All silently never threw the intended RangeError.
//!
//! Detection (Tier 1, AST structure):
//!   Match ordered comparisons of the same identifier within one conjunction.
//!   Parentheses are transparent. Disjunctions, branches, calls, and statements
//!   separate conjunctions. Inspect only the two parsed bound expressions.
//!
//!   Suppression:
//!   - The reversed form `x > A and x < B` (valid in-range check) is NOT flagged.
//!   - When B is the literal `0`: `x < N and x > 0` is the standard in-range
//!     guard and is suppressed.
//!   - When both A and B are integer literals: fire only when A ≤ B (making the
//!     AND truly impossible).  When A > B (e.g. `x < 76 and x > 65`), the range
//!     (65, 76) is valid and the pattern is suppressed.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const tokens = @import("../../ast/tokens.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "impossible-range-and";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .impossible_range_and)) return;
    _ = cache;

    // Only conjunctions and parentheses have transparent parent links.
    // An OR or any other expression therefore ends the upward walk.
    var has_conjunction = false;
    var has_lower = false;
    for (tree.nodes.items(.tag)) |tag| {
        has_conjunction = has_conjunction or tag == .bool_and;
        has_lower = has_lower or tag == .less_than;
    }
    if (!has_conjunction or !has_lower) return;
    const parents = try gpa.alloc(Ast.Node.Index, tree.nodes.len);
    defer gpa.free(parents);
    @memset(parents, .root);
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        switch (tag) {
            .bool_and => {
                const pair = tree.nodeData(node).node_and_node;
                parents[@intFromEnum(pair[0])] = node;
                parents[@intFromEnum(pair[1])] = node;
            },
            .grouped_expression => parents[@intFromEnum(tree.nodeData(node).node_and_token[0])] = node,
            else => {},
        }
    }

    var remaining: usize = 50_000;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .less_than) continue;
        const lower: Ast.Node.Index = @enumFromInt(index);
        const variable = try ungroup(tree, tree.nodeData(lower).node_and_node[0], &remaining);
        if (tree.nodeTag(variable) != .identifier) continue;
        const anchor = tree.nodeMainToken(variable);
        const name = tree.tokenSlice(anchor);
        var child = lower;
        var depth: usize = 0;
        while (parents[@intFromEnum(child)] != .root) {
            try charge(&remaining);
            if (depth == 64) return error.AnalysisBudgetExceeded;
            depth += 1;
            const parent = parents[@intFromEnum(child)];
            if (tree.nodeTag(parent) == .bool_and) {
                const pair = tree.nodeData(parent).node_and_node;
                // Preserve the ordered lower-then-upper pattern. The reversed
                // greater-then-less pattern remains an in-range candidate.
                if (pair[0] == child and try findUpper(tree, pair[1], lower, name, &remaining, depth)) {
                    try report(gpa, problems, tree, anchor, name);
                    break;
                }
            }
            child = parent;
        }
    }
}

fn charge(remaining: *usize) error{AnalysisBudgetExceeded}!void {
    if (remaining.* == 0) return error.AnalysisBudgetExceeded;
    remaining.* -= 1;
}

fn ungroup(
    tree: *const Ast,
    expression: Ast.Node.Index,
    remaining: *usize,
) error{AnalysisBudgetExceeded}!Ast.Node.Index {
    var node = expression;
    for (0..64) |_| {
        try charge(remaining);
        if (tree.nodeTag(node) != .grouped_expression) return node;
        node = tree.nodeData(node).node_and_token[0];
    }
    return error.AnalysisBudgetExceeded;
}

fn findUpper(
    tree: *const Ast,
    node: Ast.Node.Index,
    lower: Ast.Node.Index,
    name: []const u8,
    remaining: *usize,
    depth: usize,
) error{AnalysisBudgetExceeded}!bool {
    try charge(remaining);
    if (depth >= 64) return error.AnalysisBudgetExceeded;
    switch (tree.nodeTag(node)) {
        .grouped_expression => return findUpper(tree, tree.nodeData(node).node_and_token[0], lower, name, remaining, depth + 1),
        .bool_and => {
            const pair = tree.nodeData(node).node_and_node;
            return try findUpper(tree, pair[0], lower, name, remaining, depth + 1) or
                try findUpper(tree, pair[1], lower, name, remaining, depth + 1);
        },
        .greater_than => {
            const pair = tree.nodeData(node).node_and_node;
            const variable = try ungroup(tree, pair[0], remaining);
            if (tree.nodeTag(variable) != .identifier or
                !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(variable)), name)) return false;
            const left = try ungroup(tree, tree.nodeData(lower).node_and_node[1], remaining);
            const right = try ungroup(tree, pair[1], remaining);
            return !validRange(tree, left, right);
        },
        // In particular, do not extract comparisons from boolean alternatives.
        else => return false,
    }
}

fn validRange(tree: *const Ast, left: Ast.Node.Index, right: Ast.Node.Index) bool {
    if (tree.nodeTag(right) == .number_literal) {
        const right_str = tree.tokenSlice(tree.nodeMainToken(right));
        if (std.mem.eql(u8, right_str, "0")) return true;
        if (tree.nodeTag(left) == .number_literal) {
            const lv = std.fmt.parseUnsigned(u64, tree.tokenSlice(tree.nodeMainToken(left)), 0) catch null;
            const rv = std.fmt.parseUnsigned(u64, right_str, 0) catch null;
            if (lv != null and rv != null and lv.? > rv.?) return true;
        }
    }
    const first = tree.firstToken(left);
    const last = tree.lastToken(left);
    if (tokens.hasIdentInRange(tree, first, last, "maxInt") and
        tokens.hasIdentInRange(tree, tree.firstToken(right), tree.lastToken(right), "minInt")) return true;
    return leftBoundIsDotLen(tree.tokens.items(.tag), tree, first, last + 1);
}

/// True iff the left-bound token range [start, end) contains a `. len` field
/// access — i.e. the upper bound is a slice/array length.
fn leftBoundIsDotLen(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    var i = start;
    while (i + 1 < end) : (i += 1) {
        if (tags[i] == .period and
            tags[i + 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(i + 1), "len")) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    anchor_tok: Ast.TokenIndex,
    x_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s} < … and {s} > …` is an impossible range: no value can be simultaneously less than the lower bound and greater than the upper bound — the guard is permanently dead; use `or` instead of `and` for an out-of-range check",
        .{ x_name, x_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, anchor_tok),
        .end = try Pos.fromTokenEnd(tree, anchor_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "impossible-range-and: simple literal fires" {
    try testing.expectFires(check, R,
        \\fn validate(retry: i64) bool {
        \\    return retry < 0 and retry > 255;
        \\}
        \\
    );
}

test "impossible-range-and: qualified constant fires" {
    try testing.expectFires(check, R,
        \\fn validate(pageSize: i64) bool {
        \\    return pageSize < Options.MIN and pageSize > Options.MAX;
        \\}
        \\
    );
}

test "impossible-range-and: or form does not fire" {
    try testing.expectNoFire(check,
        \\fn validate(retry: i64) bool {
        \\    return retry < 0 or retry > 255;
        \\}
        \\
    );
}

test "impossible-range-and: valid in-range check does not fire" {
    try testing.expectNoFire(check,
        \\fn inRange(x: i64) bool {
        \\    return x > 0 and x < 100;
        \\}
        \\
    );
}

test "impossible-range-and: different variables do not fire" {
    try testing.expectNoFire(check,
        \\fn check(a: i64, b: i64) bool {
        \\    return a < 0 and b > 255;
        \\}
        \\
    );
}

test "impossible-range-and: literal valid range does not fire (left > right)" {
    try testing.expectNoFire(check,
        \\fn isAsciiUpper(code: u8) bool {
        \\    return code < 76 and code > 65;
        \\}
        \\
    );
}

test "impossible-range-and: right-bound 0 does not fire" {
    try testing.expectNoFire(check,
        \\fn trim(buf: []u8, max: usize) []u8 {
        \\    return if (max < buf.len and max > 0) buf[0..max] else buf;
        \\}
        \\
    );
}

test "impossible-range-and: maxInt/minInt full-range check does not fire" {
    try testing.expectNoFire(check,
        \\fn fits(value: f64) bool {
        \\    return value < std.math.maxInt(i32) and value > std.math.minInt(i32);
        \\}
        \\
    );
}

test "impossible-range-and: dot-len upper bound does not fire" {
    try testing.expectNoFire(check,
        \\fn scan(content: []const u8, end: usize, beg: usize) bool {
        \\    return end < content.len and end > beg;
        \\}
        \\
    );
}

test "impossible-range-and: literal-left + named-max still fires" {
    try testing.expectFires(check, R,
        \\fn validate(id: i64) bool {
        \\    return id < 0 and id > MAX_STREAM_ID;
        \\}
        \\
    );
}

test "impossible-range-and: optional maximum alternatives stay separate" {
    try testing.expectNoFire(check,
        \\fn validate(next_ordinal: u64, stream: anytype, source_contract: anytype) bool {
        \\    return next_ordinal < stream.min_count or
        \\        (stream.max_count != 0 and next_ordinal > stream.max_count) or
        \\        next_ordinal < source_contract.min_count or
        \\        (source_contract.max_count != 0 and next_ordinal > source_contract.max_count);
        \\}
    );
}

test "impossible-range-and: kind specific alternatives stay separate" {
    try testing.expectNoFire(check,
        \\fn validate(point_count: u32, needed: u32, kind: anytype) bool {
        \\    return point_count < needed or (kind == .box and point_count > 5) or
        \\        (kind != .box and kind != .polygon and kind != .wire and point_count > needed);
        \\}
    );
}

test "impossible-range-and: grouped OR inside conjunction does not fire" {
    try testing.expectNoFire(check,
        \\fn validate(x: i64, ready: bool) bool {
        \\    return (x < 0 or ready) and x > 255;
        \\}
    );
}

test "impossible-range-and: ungrouped OR precedence does not fire" {
    try testing.expectNoFire(check,
        \\fn validate(x: i64, ready: bool) bool {
        \\    return x < 0 or ready and x > 255;
        \\}
    );
}

test "impossible-range-and: comparisons in separate statements do not fire" {
    try testing.expectNoFire(check,
        \\fn validate(x: i64, ready: bool) bool {
        \\    const below = x < 0;
        \\    const above = ready and x > 255;
        \\    return below or above;
        \\}
    );
}

test "impossible-range-and: comparisons in separate functions do not fire" {
    try testing.expectNoFire(check,
        \\fn below(x: i64) bool { return x < 0; }
        \\fn above(x: i64, ready: bool) bool { return ready and x > 255; }
    );
}

test "impossible-range-and: comparisons in separate conditional branches do not fire" {
    try testing.expectNoFire(check,
        \\fn validate(x: i64, ready: bool) bool {
        \\    return if (ready) x < 0 else ready and x > 255;
        \\}
    );
}

test "impossible-range-and: grouped contradictory comparisons fire" {
    try testing.expectFires(check, R,
        \\fn validate(x: i64) bool {
        \\    return ((x < (0))) and ((x > (255)));
        \\}
    );
}

test "impossible-range-and: contradictory comparisons across conjuncts fire" {
    try testing.expectFires(check, R,
        \\fn validate(x: i64, ready: bool, active: bool) bool {
        \\    return (x < 0 and ready) and (active and x > 255);
        \\}
    );
}

test "impossible-range-and: contradictory alternative still fires" {
    try testing.expectFires(check, R,
        \\fn validate(x: i64, ready: bool) bool {
        \\    return ready or ((x < 0) and (x > 255));
        \\}
    );
}

test "impossible-range-and: grouped valid literal range does not fire" {
    try testing.expectNoFire(check,
        \\fn validate(x: i64, ready: bool) bool {
        \\    return (x < (76) and ready) and (x > (65));
        \\}
    );
}

test "impossible-range-and: unrelated bound names cannot exclude contradiction" {
    try testing.expectFires(check, R,
        \\fn validate(x: i64, minInt: bool) bool {
        \\    return x < std.math.maxInt(i32) and x > UPPER and minInt;
        \\}
    );
}
