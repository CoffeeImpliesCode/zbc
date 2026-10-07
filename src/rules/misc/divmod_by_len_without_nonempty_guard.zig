//! Detect integer division by a container length — `x / c.len` — where
//! the container is not proved non-empty. Division by zero can panic in
//! Debug and ReleaseSafe; unchecked builds have undefined behavior.
//!
//! Classic shape: averaging over a possibly-empty collection —
//!   const avg = total / items.len;
//!
//! This is a semantics-first rule: a token walk firing on every `/ c.len`
//! would flag fixed arrays, guarded slices, and product-bounded loops.
//! Precision comes from two semantic queries:
//!   - the value-range oracle (`value_range.provesNonempty`): a dominating
//!     guard `if (c.len > 0)` / `if (c.len == 0) return` / `c.len != 0`,
//!     a `const n = c.len` length-snapshot, a non-empty iterable loop, or
//!     an AST-backed product count whose range/equality relation proves the
//!     divisor factor nonzero;
//!   - the type engine (`FileCache.fixedArrayLenOf`): `c` is a fixed array
//!     `[N]T` with N >= 1 — its length is a non-zero compile-time constant.
//! Only divisions the analyzer cannot prove safe fire.
//!
//! The divisor must be exactly `<path>.len` immediately after binary `/`.
//! Modulo, assignment operators, grouped divisors, and arithmetic divisors
//! are outside this detector's scope, not proved safe by their exclusion.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const value_range = @import("../../flow/value_range.zig");
const testing = @import("../../testing.zig");

const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "divmod-by-len-without-nonempty-guard";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .divmod_by_len_without_nonempty_guard)) return;

    // Map each `<c>.len` field-access's `len` token → the container node `<c>`,
    // so the firing site can ask the type engine for `c`'s fixed-array length.
    // Empty/unused when the resolver is absent.
    var len_container: std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index) = .empty;
    defer len_container.deinit(gpa);
    {
        var ni: u32 = 0;
        while (ni < tree.nodes.len) : (ni += 1) {
            const node: Ast.Node.Index = @enumFromInt(ni);
            if (tree.nodeTag(node) != .field_access) continue;
            const data = tree.nodeData(node).node_and_token;
            if (std.mem.eql(u8, tree.tokenSlice(data[1]), "len")) {
                try len_container.put(gpa, data[1], data[0]);
            }
        }
    }

    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |e| {
        try checkBody(gpa, tree, cache, &len_container, e.body, problems);
    }
}

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    len_container: *const std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index),
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    if (first + 2 > last) return;

    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Only binary `/` is in scope. Modulo and `/=` are not checked.
        if (tags[t] != .slash) continue;

        const div = parseLenDivisor(tree, tags, t + 1, last) orelse continue;

        // Suppress: container is a fixed array `[N]T`, N >= 1 (non-zero len).
        if (len_container.get(div.len_tok)) |cnode| {
            if (cache.fixedArrayLenOf(cnode)) |n| {
                if (n >= 1) continue;
            }
        }

        // Suppress: container proven non-empty by a dominating guard.
        const path = tree.source[tree.tokens.items(.start)[div.container_first] .. tree.tokens.items(.start)[div.container_last] + tree.tokenSlice(div.container_last).len];
        if (try value_range.provesNonempty(gpa, tree, body, path, div.len_tok, cache)) continue;

        try report(gpa, problems, tree, t, div.container_first, div.len_tok, path);
    }
}

const LenDivisor = struct {
    /// Token of the final `len` identifier.
    len_tok: Ast.TokenIndex,
    /// First and last tokens of the container path (`<c>` in `<c>.len`).
    container_first: Ast.TokenIndex,
    container_last: Ast.TokenIndex,
};

/// If the tokens starting at `s` form `<path>.len` (a dotted identifier path
/// whose final segment is `len`, with at least one container segment before
/// it) and `len` is not a method call, return the pieces; else null.
fn parseLenDivisor(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    s: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?LenDivisor {
    if (s > last or tags[s] != .identifier) return null;
    // Consume `ident (. ident)*`.
    var cur = s;
    while (cur + 2 <= last and tags[cur + 1] == .period and tags[cur + 2] == .identifier) {
        cur += 2;
    }
    // Final segment must be `len`, with a container segment before it.
    if (cur == s) return null; // bare `len` with no container
    if (!std.mem.eql(u8, tree.tokenSlice(cur), "len")) return null;
    // Reject a `.len(...)` method call.
    if (cur + 1 <= last and tags[cur + 1] == .l_paren) return null;
    // Reject indexing `c.len[...]` (not a plain length value).
    if (cur + 1 <= last and tags[cur + 1] == .l_bracket) return null;
    return .{ .len_tok = cur, .container_first = s, .container_last = cur - 2 };
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    op_tok: Ast.TokenIndex,
    span_first: Ast.TokenIndex,
    span_last: Ast.TokenIndex,
    path: []const u8,
) !void {
    const op = tree.tokenSlice(op_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s} {s}.len` divides by a container length that is 0 when `{s}` is empty — integer `/` and `%` by zero is safety-checked illegal behaviour (panics in Debug/ReleaseSafe, UB in ReleaseFast); guard with `if ({s}.len == 0)` / `if ({s}.len != 0)` or prove `{s}` non-empty before dividing",
        .{ op, path, path, path, path, path },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, span_first),
        .end = try Pos.fromTokenEnd(tree, span_last),
        .message = msg,
    });
}

// ── Tests ───────────────────────────────────────────────────
// (provesNonempty is pure-AST, so guard suppression is exercised here;
//  fixedArrayLenOf needs the type engine and no-ops in unit tests.)

test "divmod-by-len: bare division by slice len fires" {
    try testing.expectFires(check, R,
        \\fn avg(items: []const u32, total: u32) u32 {
        \\    return total / items.len;
        \\}
        \\
    );
}

test "divmod-by-len: modulo not covered in v1 (no fire)" {
    try testing.expectNoFire(check,
        \\fn slot(buckets: []const u32, hash: u32) u32 {
        \\    return hash % buckets.len;
        \\}
        \\
    );
}

test "divmod-by-len: nonempty guard suppresses" {
    try testing.expectNoFire(check,
        \\fn avg(items: []const u32, total: u32) u32 {
        \\    if (items.len == 0) return 0;
        \\    return total / items.len;
        \\}
        \\
    );
}

test "divmod-by-len: len>0 guard suppresses" {
    try testing.expectNoFire(check,
        \\fn avg(items: []const u32, total: u32) u32 {
        \\    if (items.len > 0) return total / items.len;
        \\    return 0;
        \\}
        \\
    );
}

test "divmod-by-len: early-return OR guard suppresses" {
    try testing.expectNoFire(check,
        \\fn avg(items: []const u32, total: u32) u32 {
        \\    if (items.len == 0 or total == 0) return 0;
        \\    return total / items.len;
        \\}
        \\
    );
}

test "divmod-by-len: dotted container path guard suppresses" {
    try testing.expectNoFire(check,
        \\fn avg(self: *Foo, total: u32) u32 {
        \\    if (self.items.len == 0) return 0;
        \\    return total / self.items.len;
        \\}
        \\
    );
}

test "divmod-by-len: parenthesized non-zero divisor does not fire" {
    try testing.expectNoFire(check,
        \\fn f(items: []const u32, total: u32) u32 {
        \\    return total / (items.len + 1);
        \\}
        \\
    );
}

test "divmod-by-len: division by plain integer does not fire" {
    try testing.expectNoFire(check,
        \\fn f(total: u32, n: u32) u32 {
        \\    return total / n;
        \\}
        \\
    );
}

test "divmod-by-len: len() method call does not fire" {
    try testing.expectNoFire(check,
        \\fn f(list: List, total: u32) u32 {
        \\    return total / list.len();
        \\}
        \\
    );
}

test "divmod-by-len: multiply by len does not fire" {
    try testing.expectNoFire(check,
        \\fn f(items: []const u32, x: u32) u32 {
        \\    return x * items.len;
        \\}
        \\
    );
}

test "skript residual: product-bounded outer loop suppresses len division" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn apply(operation: Operation, left: Holder, right: Holder) !void {
        \\    const count = if (operation == .outer)
        \\        std.math.mul(usize, left.data.len, right.data.len) catch return error.Unsupported
        \\    else
        \\        left.data.len;
        \\    for (0..count) |index| {
        \\        const indexes: [2]usize = if (operation == .outer)
        \\            .{ index / right.data.len, index % right.data.len }
        \\        else
        \\            .{ index, index };
        \\        _ = indexes;
        \\    }
        \\}
        \\
    );
}

test "skript residual: equal product-bounded iterable suppresses len division" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn apply(operation: Operation, left: Holder, right: Holder, cot: Holder) !void {
        \\    const count =
        \\        std.math.mul(usize, left.data.len, right.data.len) catch return error.Unsupported;
        \\    if (operation == .outer and cot.data.len != count) return error.TypeMismatch;
        \\    for (cot.data, 0..) |value, index| {
        \\        const indexes: [2]usize = if (operation == .outer)
        \\            .{ index / right.data.len, index % right.data.len }
        \\        else
        \\            .{ index, index };
        \\        _ = value;
        \\        _ = indexes;
        \\    }
        \\}
        \\
    );
}

test "skript residual: unrelated product loop still reports empty divisor" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn apply(left: Holder, source: Holder, divisor: Holder) !void {
        \\    const count =
        \\        std.math.mul(usize, left.data.len, source.data.len) catch return error.Unsupported;
        \\    for (0..count) |index| {
        \\        consume(index / divisor.data.len);
        \\    }
        \\}
        \\
    );
}

test "product loop: AST multiplication proves divisor nonempty" {
    try testing.expectNoFire(check,
        \\fn apply(left: Holder, right: Holder) void {
        \\    const count = left.data.len * right.data.len;
        \\    for (0..count) |index| {
        \\        _ = index / right.data.len;
        \\    }
        \\}
        \\
    );
}

test "product loop: length alias operand proves divisor nonempty" {
    try testing.expectNoFire(check,
        \\fn apply(left: Holder, right: Holder) void {
        \\    const right_count = right.data.len;
        \\    const count = left.data.len * right_count;
        \\    for (0..count) |index| {
        \\        _ = index / right.data.len;
        \\    }
        \\}
        \\
    );
}

test "product loop: additive occurrence of divisor does not prove nonempty" {
    try testing.expectFires(check, R,
        \\fn apply(left: Holder, right: Holder) void {
        \\    const count = left.data.len * 2 + right.data.len;
        \\    for (0..count) |index| {
        \\        consume(index / right.data.len);
        \\    }
        \\}
        \\
    );
}
test "product loop: conditional product does not cross branch mismatch" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn apply(operation: Operation, left: Holder, right: Holder) !void {
        \\    const count = if (operation == .outer)
        \\        std.math.mul(usize, left.data.len, right.data.len) catch return error.Unsupported
        \\    else
        \\        left.data.len;
        \\    for (0..count) |index| {
        \\        if (operation != .outer) consume(index / right.data.len);
        \\    }
        \\}
        \\
    );
}

test "product loop: reassigned count invalidates product proof" {
    try testing.expectFires(check, R,
        \\fn apply(left: Holder, right: Holder) void {
        \\    var count = left.data.len * right.data.len;
        \\    count = left.data.len;
        \\    for (0..count) |index| {
        \\        consume(index / right.data.len);
        \\    }
        \\}
        \\
    );
}

test "product loop: compound count mutation invalidates product proof" {
    try testing.expectFires(check, R,
        \\fn apply(left: Holder, right: Holder) void {
        \\    var count = left.data.len * right.data.len;
        \\    count -= 1;
        \\    for (0..count) |index| {
        \\        consume(index / right.data.len);
        \\    }
        \\}
        \\
    );
}

test "product loop: divisor mutation invalidates product proof" {
    try testing.expectFires(check, R,
        \\fn apply(left: Holder, right: Holder) void {
        \\    const count = left.data.len * right.data.len;
        \\    right.data.clearRetainingCapacity();
        \\    for (0..count) |index| {
        \\        consume(index / right.data.len);
        \\    }
        \\}
        \\
    );
}

test "product loop: iterable equality does not survive mutation" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn apply(left: Holder, right: Holder, cot: Holder) !void {
        \\    const count =
        \\        std.math.mul(usize, left.data.len, right.data.len) catch return error.Unsupported;
        \\    if (cot.data.len != count) return error.TypeMismatch;
        \\    cot.data.appendAssumeCapacity(0);
        \\    for (cot.data, 0..) |value, index| {
        \\        consume(value, index / right.data.len);
        \\    }
        \\}
        \\
    );
}

test "product loop: shadowed std math mul does not prove nonempty" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn apply(left: Holder, right: Holder) !void {
        \\    const std = FakeStd;
        \\    const count =
        \\        std.math.mul(usize, left.data.len, right.data.len) catch return error.Unsupported;
        \\    for (0..count) |index| {
        \\        consume(index / right.data.len);
        \\    }
        \\}
        \\
    );
}

test "product loop: nonzero range fact does not escape loop body" {
    try testing.expectFires(check, R,
        \\fn apply(left: Holder, right: Holder, total: usize) void {
        \\    const count = left.data.len * right.data.len;
        \\    for (0..count) |_| {}
        \\    consume(total / right.data.len);
        \\}
        \\
    );
}

test "product-sized iterable carries an existing length equality" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\fn apply(operation: Operation, left: Holder, right: Holder, cot: Holder) !void {
        \\    const count = if (operation == .outer)
        \\        std.math.mul(usize, left.data.len, right.data.len) catch return error.Unsupported
        \\    else
        \\        left.data.len;
        \\    if (cot.data.len != count) return error.TypeMismatch;
        \\    for (cot.data, 0..) |value, index| {
        \\        const indexes: [2]usize = if (operation == .outer)
        \\            .{ index / right.data.len, index % right.data.len }
        \\        else
        \\            .{ index, index };
        \\        _ = value;
        \\        _ = indexes;
        \\    }
        \\}
        \\
    );
}

test "product loop: a later call can empty a borrowed divisor before the next iteration" {
    try testing.expectFiresTyped(check, R,
        \\const Holder = struct { data: []const usize };
        \\fn clear(holder: *Holder) void { holder.data = &.{}; }
        \\fn apply(left: *Holder, right: *Holder) void {
        \\    const count = left.data.len * right.data.len;
        \\    for (0..count) |index| {
        \\        _ = index / right.data.len;
        \\        clear(right);
        \\    }
        \\}
    );
}

test "pointer field projection can replace a guarded slice" {
    try testing.expectFiresTyped(check, R,
        \\const Box = struct { bytes: []const u8, slot: *[]const u8 };
        \\fn clear(p: *[]const u8) void { p.* = ""; }
        \\pub fn divide(box: *Box) usize {
        \\    if (box.bytes.len == 0) return 0;
        \\    clear(box.slot);
        \\    return 10 / box.bytes.len;
        \\}
    );
}

test "dereferenced pointer projection can replace a guarded slice" {
    try testing.expectFiresTyped(check, R,
        \\fn clear(p: *[]const u8) void { p.* = ""; }
        \\pub fn divide(bytes: *[]const u8, slot: **[]const u8) usize {
        \\    if (bytes.len == 0) return 0;
        \\    clear(slot.*);
        \\    return 10 / bytes.len;
        \\}
    );
}

test "indexed pointer projection can replace a guarded slice" {
    try testing.expectFiresTyped(check, R,
        \\fn clear(p: *[]const u8) void { p.* = ""; }
        \\pub fn divide(bytes: *[]const u8, slots: []const *[]const u8) usize {
        \\    if (bytes.len == 0) return 0;
        \\    clear(slots[0]);
        \\    return 10 / bytes.len;
        \\}
    );
}

test "opaque projection does not preserve a guarded indirect slice" {
    try testing.expectFires(check, R,
        \\pub fn divide(box: *Box) usize {
        \\    if (box.bytes.len == 0) return 0;
        \\    clear(box.slot);
        \\    return 10 / box.bytes.len;
        \\}
    );
}

test "scalar field projection preserves a guarded indirect slice" {
    try testing.expectNoFireTyped(check,
        \\const Box = struct { bytes: []const u8, count: usize };
        \\fn consume(count: usize) void { _ = count; }
        \\pub fn divide(box: *Box) usize {
        \\    if (box.bytes.len == 0) return 0;
        \\    consume(box.count);
        \\    return 10 / box.bytes.len;
        \\}
    );
}

test "read only pointer projection preserves a guarded indirect slice" {
    try testing.expectNoFireTyped(check,
        \\const Box = struct { bytes: []const u8, slot: *[]const u8 };
        \\fn readOnly(p: *[]const u8) void { _ = p.*.len; }
        \\pub fn divide(box: *Box) usize {
        \\    if (box.bytes.len == 0) return 0;
        \\    readOnly(box.slot);
        \\    return 10 / box.bytes.len;
        \\}
    );
}

test "pointer projection cannot replace an unaddressed local slice header" {
    try testing.expectNoFireTyped(check,
        \\const Box = struct { slot: *[]const u8 };
        \\fn clear(p: *[]const u8) void { p.* = ""; }
        \\pub fn divide(bytes: []const u8, box: *Box) usize {
        \\    if (bytes.len == 0) return 0;
        \\    clear(box.slot);
        \\    return 10 / bytes.len;
        \\}
    );
}

test "scalar dereference projection preserves a guarded indirect slice" {
    try testing.expectNoFireTyped(check,
        \\fn consume(count: usize) void { _ = count; }
        \\pub fn divide(bytes: *[]const u8, count: *const usize) usize {
        \\    if (bytes.len == 0) return 0;
        \\    consume(count.*);
        \\    return 10 / bytes.len;
        \\}
    );
}

test "scalar index projection preserves a guarded indirect slice" {
    try testing.expectNoFireTyped(check,
        \\fn consume(count: usize) void { _ = count; }
        \\pub fn divide(bytes: *[]const u8, counts: []const usize) usize {
        \\    if (bytes.len == 0) return 0;
        \\    consume(counts[0]);
        \\    return 10 / bytes.len;
        \\}
    );
}

test "slice field projection can carry pointers to a guarded slice header" {
    try testing.expectFiresTyped(check, R,
        \\const Box = struct { bytes: []const u8, slots: []const *[]const u8 };
        \\fn clear(slots: []const *[]const u8) void { slots[0].* = ""; }
        \\pub fn divide(box: *Box) usize {
        \\    if (box.bytes.len == 0) return 0;
        \\    clear(box.slots);
        \\    return 10 / box.bytes.len;
        \\}
    );
}
