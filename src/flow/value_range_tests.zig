//! Tests for the standalone nonzero value-range oracle.

const std = @import("std");
const Ast = std.zig.Ast;
const value_range = @import("value_range.zig");

/// Parse `src`, locate the first fn body, find the `[` token of the
/// subscript on array `arr`, and ask whether `target` is provably nonzero
/// there.  Returns the oracle's answer.
fn proveAt(src: [:0]const u8, target: []const u8, arr: []const u8) !bool {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;

    const body = firstFnBody(&tree) orelse return error.NoFnBody;
    const lbracket = subscriptLBracket(&tree, arr) orelse return error.NoSubscript;
    return value_range.provesNonzero(gpa, &tree, body, target, lbracket, null);
}

fn firstFnBody(tree: *const Ast) ?Ast.Node.Index {
    var ni: u32 = 0;
    while (ni < tree.nodes.len) : (ni += 1) {
        const node: Ast.Node.Index = @enumFromInt(ni);
        if (tree.nodeTag(node) != .fn_decl) continue;
        // fn_decl data: { proto, body }.
        const data = tree.nodeData(node).node_and_node;
        return data[1];
    }
    return null;
}

/// First `[` token preceded by identifier `arr`.
fn subscriptLBracket(tree: *const Ast, arr: []const u8) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = 1;
    while (t < tags.len) : (t += 1) {
        if (tags[t] != .l_bracket) continue;
        if (tags[t - 1] != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t - 1), arr)) return t;
    }
    return null;
}

test "nonzero: bare param is unknown (fires)" {
    try std.testing.expect(!try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    return buf[i - 1];
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: i > 0 guard in then-arm" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    if (i > 0) {
        \\        return buf[i - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: i > <non-negative literal> guard (generalized lower bound)" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    if (i > 5) {
        \\        return buf[i - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: i > other.len guard (.len operand is provably >= 0)" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []const u8, other: []const u8) u8 {
        \\    if (i > other.len) {
        \\        return buf[i - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: `x += 1` makes an unsigned x nonzero (post-increment look-back)" {
    try std.testing.expect(try proveAt(
        \\fn f(buf: []const u8) u8 {
        \\    var i: usize = 0;
        \\    i += 1;
        \\    return buf[i - 1];
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: i != 0 guard" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    if (i != 0) return buf[i - 1];
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: i >= 1 guard" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    if (i >= 1) return buf[i - 1];
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: 0 < i guard" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    if (0 < i) return buf[i - 1];
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: early return on zero (divergence)" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    if (i == 0) return 0;
        \\    return buf[i - 1];
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: use in else-arm of i==0 is nonzero" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    if (i == 0) {
        \\        return 0;
        \\    } else {
        \\        return buf[i - 1];
        \\    }
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: positive-literal assignment" {
    try std.testing.expect(try proveAt(
        \\fn f(buf: []const u8) u8 {
        \\    var i: usize = 3;
        \\    return buf[i - 1];
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: zero-literal assignment is unsafe" {
    try std.testing.expect(!try proveAt(
        \\fn f(buf: []const u8) u8 {
        \\    var i: usize = 0;
        \\    return buf[i - 1];
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: merge of nonzero/zero arms is unsafe" {
    try std.testing.expect(!try proveAt(
        \\fn f(c: bool, buf: []const u8) u8 {
        \\    var i: usize = 1;
        \\    if (c) {
        \\        i = 5;
        \\    } else {
        \\        i = 0;
        \\    }
        \\    return buf[i - 1];
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: guard in while condition refines body" {
    try std.testing.expect(try proveAt(
        \\fn f(i_in: usize, buf: []const u8) u8 {
        \\    var i = i_in;
        \\    while (i > 0) {
        \\        const x = buf[i - 1];
        \\        if (x == 0) return 0;
        \\        i -= 1;
        \\    }
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: use on LHS of a subscript write (buf[i-1] = …)" {
    // Regression: analyzeAssign only inspected the RHS for the use token, so a
    // provably-nonzero index on the WRITE side (`buf[i-1] = 0`) was never
    // resolved and the rule false-positived. `.len` guard needs no type engine.
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []u8, other: []const u8) void {
        \\    if (i > other.len) {
        \\        buf[i - 1] = 0;
        \\    }
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: LHS subscript write under a bare (no-block) if" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []u8, other: []const u8) void {
        \\    if (i > other.len) buf[i - 1] = 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: no false-negative — unguarded LHS write still unproven" {
    try std.testing.expect(!try proveAt(
        \\fn f(i: usize, buf: []u8) void {
        \\    buf[i - 1] = 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: cross-fn ceil-div postcondition (numMasks) with guarded arg" {
    // `m = numMasks(k)` where numMasks is `(x + (D-1)) / D` (ceil-div, structural
    // D-1 == D-1), and k is guarded non-zero ⟹ m non-zero. Caller listed first so
    // `proveAt` analyzes it; the callee scan finds `numMasks` regardless of order.
    try std.testing.expect(try proveAt(
        \\fn f(a: []u8, k: usize) u8 {
        \\    if (k == 0) return 0;
        \\    const m = numMasks(k);
        \\    return a[m - 1];
        \\}
        \\fn numMasks(x: usize) usize {
        \\    return (x + (64 - 1)) / 64;
        \\}
    , "m", "a"));
}

test "nonzero: cross-fn — unguarded arg leaves result UNPROVEN (no false-negative)" {
    try std.testing.expect(!try proveAt(
        \\fn f(a: []u8, k: usize) u8 {
        \\    const m = numMasks(k);
        \\    return a[m - 1];
        \\}
        \\fn numMasks(x: usize) usize {
        \\    return (x + (64 - 1)) / 64;
        \\}
    , "m", "a"));
}

test "nonzero: cross-fn via field-path value-alias (const L = s.len guards s.len arg)" {
    try std.testing.expect(try proveAt(
        \\fn f(s: S, a: []u8) u8 {
        \\    const L = s.len;
        \\    if (L == 0) return 0;
        \\    const m = numMasks(s.len);
        \\    return a[m - 1];
        \\}
        \\fn numMasks(x: usize) usize {
        \\    return (x + (64 - 1)) / 64;
        \\}
    , "m", "a"));
}

test "nonempty: `s = base[0..n]` with n guarded nonzero ⟹ s non-empty" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn f(buf: []u8, n: usize) u8 {
        \\    if (n == 0) return 0;
        \\    const s = buf[0..n];
        \\    return s[s.len - 1];
        \\}
    , "s", "s"));
}

test "nonempty: `s = base[0..n]` with n unguarded is UNPROVEN (no false-negative)" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(buf: []u8, n: usize) u8 {
        \\    const s = buf[0..n];
        \\    return s[s.len - 1];
        \\}
    , "s", "s"));
}

test "nonempty: short-circuit `c.len > 0 and c[c.len-1]` (endsWith idiom)" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn endsWith(self: []const u8, ch: u8) bool {
        \\    return self.len > 0 and self[self.len - 1] == ch;
        \\}
        \\
    , "self", "self"));
}

test "nonempty: short-circuit `c.len == 0 or c[c.len-1]` (or-form)" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn endsWithOrEmpty(self: []const u8, ch: u8) bool {
        \\    return self.len == 0 or self[self.len - 1] == ch;
        \\}
        \\
    , "self", "self"));
}

test "nonempty: no false-negative — unguarded access in same fn still unproven" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn last(self: []const u8) u8 {
        \\    return self[self.len - 1];
        \\}
        \\
    , "self", "self"));
}

test "nonzero: and-chain guard (i > 0 and c)" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, c: bool, buf: []const u8) u8 {
        \\    if (i > 0 and c) return buf[i - 1];
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: unrelated guard does not prove" {
    try std.testing.expect(!try proveAt(
        \\fn f(i: usize, j: usize, buf: []const u8) u8 {
        \\    if (j > 0) return buf[i - 1];
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

test "nonzero: reassignment after guard clears fact" {
    try std.testing.expect(!try proveAt(
        \\fn f(i_in: usize, other: usize, buf: []const u8) u8 {
        \\    var i = i_in;
        \\    if (i > 0) {
        \\        i = other;
        \\        return buf[i - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "i", "buf"));
}

// ── container non-empty ──────────────────────────────────────

/// Query `provesNonempty(container)` at the `[` token after identifier `arr`.
fn proveNonemptyAt(src: [:0]const u8, container: []const u8, arr: []const u8) !bool {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const body = firstFnBody(&tree) orelse return error.NoFnBody;
    const lbracket = subscriptLBracket(&tree, arr) orelse return error.NoSubscript;
    return value_range.provesNonempty(gpa, &tree, body, container, lbracket, null);
}

/// Query `provesMinLen(container, n)` at the `[` token after identifier `arr`.
fn proveMinLenAt(src: [:0]const u8, container: []const u8, n: u64, arr: []const u8) !bool {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const body = firstFnBody(&tree) orelse return error.NoFnBody;
    const lbracket = subscriptLBracket(&tree, arr) orelse return error.NoSubscript;
    return value_range.provesMinLen(gpa, &tree, body, container, n, lbracket, null);
}

test "minlen: switch-arm bounds a slice-from-range length (k.len >= 16 in arm 20)" {
    try std.testing.expect(try proveMinLenAt(
        \\fn f(b: []const u8) u8 {
        \\    const n = b.len;
        \\    const k = b[0..n];
        \\    return switch (n) {
        \\        20 => k[16],
        \\        else => 0,
        \\    };
        \\}
    , "k", 16, "k"));
}

test "minlen: switch arm BELOW threshold is UNPROVEN (no false-negative)" {
    try std.testing.expect(!try proveMinLenAt(
        \\fn f(b: []const u8) u8 {
        \\    const n = b.len;
        \\    const k = b[0..n];
        \\    return switch (n) {
        \\        10 => k[16],
        \\        else => 0,
        \\    };
        \\}
    , "k", 16, "k"));
}

test "minlen: no switch ⟹ unproven (no false-negative)" {
    try std.testing.expect(!try proveMinLenAt(
        \\fn f(b: []const u8) u8 {
        \\    const n = b.len;
        \\    const k = b[0..n];
        \\    return k[16];
        \\}
    , "k", 16, "k"));
}

test "minlen: `if (b.len >= 4)` guard proves len >= 4 in then-arm (#23)" {
    try std.testing.expect(try proveMinLenAt(
        \\fn f(b: []const u8) u8 {
        \\    if (b.len >= 4) {
        \\        return b[3];
        \\    }
        \\    return 0;
        \\}
    , "b", 4, "b"));
}

test "minlen: `if (b.len > 3)` guard proves len >= 4 (#23)" {
    try std.testing.expect(try proveMinLenAt(
        \\fn f(b: []const u8) u8 {
        \\    if (b.len > 3) return b[3];
        \\    return 0;
        \\}
    , "b", 4, "b"));
}

test "minlen: early-return `if (b.len < 4) return` proves len >= 4 after (#23)" {
    try std.testing.expect(try proveMinLenAt(
        \\fn f(b: []const u8) u8 {
        \\    if (b.len < 4) return 0;
        \\    return b[3];
        \\}
    , "b", 4, "b"));
}

test "minlen: guard for N=4 does NOT prove len >= 5 (no over-claim)" {
    try std.testing.expect(!try proveMinLenAt(
        \\fn f(b: []const u8) u8 {
        \\    if (b.len >= 4) return b[3];
        \\    return 0;
        \\}
    , "b", 5, "b"));
}

test "minlen: reassigning the slice drops the bound (sound kill)" {
    // Same-path mutation (here a reassignment of `b`) invalidates the
    // proven bound — mirrors how the existing nonempty-container tracking
    // is killed.  (Root-level mutation of a sub-path, e.g. `x.clear()`
    // dropping an `x.items.len` bound, is the same pre-existing limitation
    // the whole container model shares; guard+access are normally adjacent.)
    try std.testing.expect(!try proveMinLenAt(
        \\fn f(input: []const u8) u8 {
        \\    var b = input;
        \\    if (b.len >= 4) {
        \\        b = input[0..2];
        \\        return b[3];
        \\    }
        \\    return 0;
        \\}
    , "b", 4, "b"));
}

test "nonempty: bare arr.len-1 is unknown (fires)" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(arr: []const u8) u8 {
        \\    return arr[arr.len - 1];
        \\}
        \\
    , "arr", "arr"));
}

test "nonempty: arr.len > 0 guard" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn f(arr: []const u8) u8 {
        \\    if (arr.len > 0) return arr[arr.len - 1];
        \\    return 0;
        \\}
        \\
    , "arr", "arr"));
}

test "nonempty: early return on empty (divergence)" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn f(arr: []const u8) u8 {
        \\    if (arr.len == 0) return 0;
        \\    return arr[arr.len - 1];
        \\}
        \\
    , "arr", "arr"));
}

test "nonempty: arr.len != 0 guard" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn f(arr: []const u8) u8 {
        \\    if (arr.len != 0) return arr[arr.len - 1];
        \\    return 0;
        \\}
        \\
    , "arr", "arr"));
}

test "nonempty: dotted path self.items" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn f(self: *Foo) u8 {
        \\    if (self.items.len > 0) return self.items[self.items.len - 1];
        \\    return 0;
        \\}
        \\
    , "self.items", "items"));
}

test "nonempty: clear after guard is unsafe" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(arr: *std.ArrayList(u8)) u8 {
        \\    if (arr.len > 0) {
        \\        arr.clearRetainingCapacity();
        \\        return arr[arr.len - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "arr", "arr"));
}

test "nonempty: reassignment after guard is unsafe" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(arr: []const u8, other: []const u8) u8 {
        \\    if (arr.len > 0) {
        \\        arr = other;
        \\        return arr[arr.len - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "arr", "arr"));
}

test "nonempty: early-return with OR guard and immutable predicate" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn tail(self: *Foo) u8 {
        \\    if (self.buffer.len == 0 or self.empty) return 0;
        \\    return self.buffer[(self.index) % self.buffer.len];
        \\}
        \\
    , "self.buffer", "buffer"));
}

test "nonempty: a mutating OR predicate invalidates the earlier length comparison" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn tail(self: *Foo) u8 {
        \\    if (self.buffer.len == 0 or self.empty()) return 0;
        \\    return self.buffer[self.index % self.buffer.len];
        \\}
        \\const Foo = struct {
        \\    buffer: []u8,
        \\    index: usize,
        \\    fn empty(self: *Foo) bool { self.buffer.len = 0; return false; }
        \\};
    , "self.buffer", "buffer"));
}

test "nonzero: early-return with OR guard (i==0 or other)" {
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, c: bool, buf: []const u8) u8 {
        \\    if (i == 0 or c) return 0;
        \\    return buf[i - 1];
        \\}
        \\
    , "i", "buf"));
}

test "nonempty: unrelated container guard does not prove" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(arr: []const u8, other: []const u8) u8 {
        \\    if (other.len > 0) return arr[arr.len - 1];
        \\    return 0;
        \\}
        \\
    , "arr", "arr"));
}

// ── len-bound local aliases (n == c.len) ─────────────────────

test "alias: scalar guard proves container nonempty (n=c.len, if n>0, c[c.len-1])" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn f(arr: []const u8) u8 {
        \\    const n = arr.len;
        \\    if (n > 0) return arr[arr.len - 1];
        \\    return 0;
        \\}
        \\
    , "arr", "arr"));
}

test "alias: scalar early-return proves container nonempty" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn f(arr: []const u8) u8 {
        \\    const n = arr.len;
        \\    if (n == 0) return 0;
        \\    return arr[arr.len - 1];
        \\}
        \\
    , "arr", "arr"));
}

test "alias: container guard proves scalar nonzero (n=c.len, if c.len>0, buf[n-1])" {
    try std.testing.expect(try proveAt(
        \\fn f(arr: []const u8, buf: []const u8) u8 {
        \\    const n = arr.len;
        \\    if (arr.len > 0) return buf[n - 1];
        \\    return 0;
        \\}
        \\
    , "n", "buf"));
}

test "alias: container mutated after snapshot is unsafe" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(arr: *std.ArrayList(u8)) u8 {
        \\    const n = arr.len;
        \\    arr.clearRetainingCapacity();
        \\    if (n > 0) return arr[arr.len - 1];
        \\    return 0;
        \\}
        \\
    , "arr", "arr"));
}

test "alias: unrelated container not proven by scalar guard" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(arr: []const u8, other: []const u8) u8 {
        \\    const n = other.len;
        \\    if (n > 0) return arr[arr.len - 1];
        \\    return 0;
        \\}
        \\
    , "arr", "arr"));
}

// ── applyCmp: lit >= 2 (N-bounded guards) ────────────────────

test "nonzero: if (n < 2) return diverges, fall-through n >= 2 >= 1" {
    try std.testing.expect(try proveAt(
        \\fn f(n: usize, buf: []const u8) u8 {
        \\    if (n < 2) return 0;
        \\    return buf[n - 1];
        \\}
        \\
    , "n", "buf"));
}

test "nonzero: if (n >= 3) then n nonzero" {
    try std.testing.expect(try proveAt(
        \\fn f(n: usize, buf: []const u8) u8 {
        \\    if (n >= 3) return buf[n - 1];
        \\    return 0;
        \\}
        \\
    , "n", "buf"));
}

test "nonzero: if (2 > n) return diverges, fall-through n >= 2 >= 1 (flipped)" {
    try std.testing.expect(try proveAt(
        \\fn f(n: usize, buf: []const u8) u8 {
        \\    if (2 > n) return 0;
        \\    return buf[n - 1];
        \\}
        \\
    , "n", "buf"));
}

test "nonzero: if (n == 0) and if (n < 2) both still nonzero in fall-through" {
    try std.testing.expect(try proveAt(
        \\fn f(n: usize, buf: []const u8) u8 {
        \\    if (n < 5) return 0;
        \\    return buf[n - 1];
        \\}
        \\
    , "n", "buf"));
}

// ── DiffAlias: n = A - B, n nonzero → A nonzero ──────────────
// These tests use subtrahends that are provably non-negative WITHOUT the type
// engine (literal 0 or .len field), so they work in the cache-null test harness.
// The real-world case (identifier subtrahend, e.g. `range.end - range.start`)
// requires ZLS confirmation that the subtrahend is unsigned.

test "diff-alias: n = end - 0, if (n == 0) return, buf[end - 1] suppressed" {
    // Subtrahend is literal 0: operandProvablyNonneg = true, no type engine needed.
    try std.testing.expect(try proveAt(
        \\fn f(end: usize, buf: []const u8) u8 {
        \\    const n = end - 0;
        \\    if (n == 0) return 0;
        \\    return buf[end - 1];
        \\}
        \\
    , "end", "buf"));
}

test "diff-alias: n = end - other.len, if (n == 0) return, buf[end - 1] suppressed" {
    // Subtrahend is .len (provably >= 0), no type engine needed.
    try std.testing.expect(try proveAt(
        \\fn f(end: usize, other: []const u8, buf: []const u8) u8 {
        \\    const n = end - other.len;
        \\    if (n == 0) return 0;
        \\    return buf[end - 1];
        \\}
        \\
    , "end", "buf"));
}

test "diff-alias: n = end - 0, if (n < 2) return, buf[end - 1] suppressed (combined)" {
    // Both the lit>=2 applyCmp extension AND the DiffAlias are exercised.
    try std.testing.expect(try proveAt(
        \\fn f(end: usize, buf: []const u8) u8 {
        \\    const n = end - 0;
        \\    if (n < 2) return 0;
        \\    return buf[end - 1];
        \\}
        \\
    , "end", "buf"));
}

test "diff-alias: unrelated var not proven" {
    try std.testing.expect(!try proveAt(
        \\fn f(end: usize, start: usize, other: usize, buf: []const u8) u8 {
        \\    const n = end - 0;
        \\    if (n == 0) return 0;
        \\    return buf[other - 1];
        \\}
        \\
    , "other", "buf"));
}

test "diff-alias: rebinding end clears diff fact" {
    try std.testing.expect(!try proveAt(
        \\fn f(end: usize, buf: []const u8) u8 {
        \\    const n = end - 0;
        \\    if (n == 0) return 0;
        \\    const end2 = end;
        \\    _ = end2;
        \\    var end_mut: usize = 0;
        \\    end_mut = end;
        \\    return buf[end_mut - 1];
        \\}
        \\
    , "end_mut", "buf"));
}

test "nonzero: loop var only `+=`'d keeps its positive init (monotonic)" {
    try std.testing.expect(try proveAt(
        \\fn f(buf: []u8) void {
        \\    var p: usize = 1;
        \\    while (p < buf.len) {
        \\        buf[p - 1] = 0;
        \\        p += 1;
        \\    }
        \\}
    , "p", "buf"));
}

test "nonzero: loop var reset to 0 then accessed is UNPROVEN (no false-negative)" {
    try std.testing.expect(!try proveAt(
        \\fn f(buf: []u8) void {
        \\    var p: usize = 1;
        \\    while (p < buf.len) {
        \\        p = 0;
        \\        buf[p - 1] = 0;
        \\        p += 1;
        \\    }
        \\}
    , "p", "buf"));
}

test "nonzero: if-condition OR descent refines a later operand" {
    try std.testing.expect(try proveAt(
        \\fn f(tags: []const u8, other: []const u8, t: usize) bool {
        \\    if (t < 3 or other[t - 3] != 0 or tags[t - 1] != 0) return false;
        \\    return true;
        \\}
    , "t", "tags"));
}

test "nonzero: guarded decrement preserves the remaining lower bound" {
    try std.testing.expect(try proveAt(
        \\fn f(tags: []const u8, anchor: usize) u8 {
        \\    const start: usize = 0;
        \\    var k = anchor;
        \\    while (k > start + 1) {
        \\        k -= 1;
        \\        return tags[k - 1];
        \\    }
        \\    return 0;
        \\}
    , "k", "tags"));
}

test "nonzero: unsigned relational guard refines its then branch" {
    try std.testing.expect(try proveAt(
        \\fn f(tags: []const u8, lhs_start: usize) u8 {
        \\    const first: usize = 0;
        \\    if (lhs_start > first) return tags[lhs_start - 1];
        \\    return 0;
        \\}
    , "lhs_start", "tags"));
}

test "nonzero: early-return offset guard flows through subtraction aliases" {
    try std.testing.expect(try proveAt(
        \\fn f(tags: []const u8, other: []const u8, alias_tok: usize) u8 {
        \\    const first: usize = 0;
        \\    if (alias_tok < first + 3 or other[alias_tok - 1] != 0) return 0;
        \\    const name_tok = alias_tok - 2;
        \\    return tags[name_tok - 1];
        \\}
    , "name_tok", "tags"));
}

test "nonzero: increment before every infinite-loop break refines loop exit" {
    try std.testing.expect(try proveAt(
        \\fn f(names: []const u8, stop: bool) u8 {
        \\    var len: usize = 0;
        \\    while (true) {
        \\        len += 1;
        \\        if (stop) break;
        \\    }
        \\    return names[len - 1];
        \\}
    , "len", "names"));
}

test "nonzero: an infinite-loop break before increment keeps zero possible" {
    try std.testing.expect(!try proveAt(
        \\fn f(names: []const u8, stop_early: bool, stop_late: bool) u8 {
        \\    var len: usize = 0;
        \\    while (true) {
        \\        if (stop_early) break;
        \\        len += 1;
        \\        if (stop_late) break;
        \\    }
        \\    return names[len - 1];
        \\}
    , "len", "names"));
}

test "nonzero: signed addition can reach zero and remains unproven" {
    try std.testing.expect(!try proveAt(
        \\fn f(tags: []const u8) u8 {
        \\    var k: isize = -1;
        \\    k += 1;
        \\    return tags[k - 1];
        \\}
    , "k", "tags"));
}

test "nonzero: a while-body guard does not escape the loop" {
    try std.testing.expect(!try proveAt(
        \\fn f(names: []const u8, initial: usize) u8 {
        \\    var len = initial;
        \\    while (len > 0) {
        \\        len -= 1;
        \\    }
        \\    return names[len - 1];
        \\}
    , "len", "names"));
}

test "nonzero: a labeled block break does not prove the enclosing loop exit" {
    try std.testing.expect(!try proveAt(
        \\fn f(names: []const u8) u8 {
        \\    var len: usize = 0;
        \\    while (true) {
        \\        inner: {
        \\            len = 1;
        \\            break :inner;
        \\        }
        \\        len = 0;
        \\        break;
        \\    }
        \\    return names[len - 1];
        \\}
    , "len", "names"));
}

test "nonzero: an address argument invalidates a scalar-only guard" {
    try std.testing.expect(!try proveAt(
        \\fn f(bytes: []const u8, initial: usize) u8 {
        \\    var i = initial;
        \\    if (i == 0) return 0;
        \\    mutate(&i);
        \\    return bytes[i - 1];
        \\}
        \\fn mutate(i: *usize) void { i.* = 0; }
    , "i", "bytes"));
}

test "nonzero: a bitwise value argument preserves the scalar guard" {
    try std.testing.expect(try proveAt(
        \\fn f(bytes: []const u8, i: usize, mask: usize) u8 {
        \\    if (i == 0) return 0;
        \\    consume(mask & i);
        \\    return bytes[i - 1];
        \\}
        \\fn consume(value: usize) void { _ = value; }
    , "i", "bytes"));
}

test "nonzero: wrapping callee arithmetic can return zero" {
    try std.testing.expect(!try proveAt(
        \\fn f(bytes: []const u8, x: u8) u8 {
        \\    if (x == 0) return 0;
        \\    const n = cancel(x);
        \\    return bytes[@intCast(n - 1)];
        \\}
        \\fn cancel(x: u8) u8 { return x +% (0 -% x); }
    , "n", "bytes"));
}

test "nonzero: signed callee addition can cancel a nonzero argument" {
    try std.testing.expect(!try proveAt(
        \\fn f(bytes: []const u8, x: isize) u8 {
        \\    if (x == 0) return 0;
        \\    const n = increment(x);
        \\    return bytes[@intCast(n - 1)];
        \\}
        \\fn increment(x: isize) isize { return x + 1; }
    , "n", "bytes"));
}

test "nonzero: signed saturating callee addition can return zero" {
    try std.testing.expect(!try proveAt(
        \\fn f(bytes: []const u8, x: isize) u8 {
        \\    if (x == 0) return 0;
        \\    const n = increment(x);
        \\    return bytes[@intCast(n - 1)];
        \\}
        \\fn increment(x: isize) isize { return x +| 1; }
    , "n", "bytes"));
}

test "nonzero: ceiling offset at the u64 boundary remains comparable" {
    try std.testing.expect(try proveAt(
        \\fn f(bytes: []const u8, x: u128) u8 {
        \\    if (x == 0) return 0;
        \\    const n = rounded(x);
        \\    return bytes[@intCast(n - 1)];
        \\}
        \\fn rounded(x: u128) u128 {
        \\    return (x + 18446744073709551615) / 2;
        \\}
    , "n", "bytes"));
}

test "nonzero: an indirect callee cannot borrow a namespace postcondition" {
    try std.testing.expect(!try proveAt(
        \\fn f(bytes: []const u8, x: u8, helper: *const fn (u8) u8) u8 {
        \\    if (x == 0) return 0;
        \\    const n = helper(x);
        \\    return bytes[@intCast(n - 1)];
        \\}
        \\const Other = struct {
        \\    fn helper(x: u8) u8 { return x; }
        \\};
    , "n", "bytes"));
}

test "nonzero: a direct callee ignores unrelated namespace functions" {
    try std.testing.expect(try proveAt(
        \\fn f(bytes: []const u8, x: u8) u8 {
        \\    if (x == 0) return 0;
        \\    const n = helper(x);
        \\    return bytes[@intCast(n - 1)];
        \\}
        \\const Other = struct {
        \\    fn helper(x: u8) u8 { _ = x; return 0; }
        \\};
        \\fn helper(x: u8) u8 { return x; }
    , "n", "bytes"));
}
