//! Tests for the standalone nonzero value-range oracle.

const std = @import("std");
const Ast = std.zig.Ast;
const value_range = @import("value_range.zig");
const budget_mod = @import("../budget.zig");
const file_cache_mod = @import("../cache/file_cache.zig");
const resolver_mod = @import("../type_resolver.zig");

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

test "minlen: conditional entry-size interval proves every table offset" {
    const src =
        \\fn f(table: []const u8, index: usize, is64: bool) u8 {
        \\    const entry_size: usize = if (is64) 64 else 40;
        \\    const entry = table[index * entry_size..][0..entry_size];
        \\    return entry[32];
        \\}
    ;
    for ([_]u64{ 16, 20, 24, 32, 40 }) |minimum|
        try std.testing.expect(try proveMinLenAt(src, "entry", minimum, "entry"));
    try std.testing.expect(!try proveMinLenAt(src, "entry", 41, "entry"));
}

test "minlen: initializer interval is a snapshot not a live endpoint alias" {
    try std.testing.expect(try proveMinLenAt(
        \\fn f(table: []const u8) u8 {
        \\    var entry_size: usize = 64;
        \\    const entry = table[0..entry_size];
        \\    entry_size = 0;
        \\    return entry[32];
        \\}
    , "entry", 40, "entry"));
    try std.testing.expect(!try proveMinLenAt(
        \\fn f(table: []const u8) u8 {
        \\    var entry_size: usize = 16;
        \\    const entry = table[0..entry_size];
        \\    entry_size = 64;
        \\    return entry[32];
        \\}
    , "entry", 40, "entry"));
}

test "minlen: scalar assignment is evaluated before a subslice snapshot" {
    try std.testing.expect(try proveMinLenAt(
        \\fn f(table: []const u8, is64: bool) u8 {
        \\    var entry_size: usize = 0;
        \\    entry_size = if (is64) 64 else 40;
        \\    const entry = table[0..entry_size];
        \\    return entry[32];
        \\}
    , "entry", 40, "entry"));
    try std.testing.expect(!try proveMinLenAt(
        \\fn f(table: []const u8, is64: bool) u8 {
        \\    var entry_size: usize = 64;
        \\    entry_size = if (is64) 16 else 40;
        \\    const entry = table[0..entry_size];
        \\    return entry[32];
        \\}
    , "entry", 32, "entry"));
}

test "minlen: slice rebind replaces the interval snapshot" {
    try std.testing.expect(try proveMinLenAt(
        \\fn f(table: []const u8, is64: bool) u8 {
        \\    var entry = table[0..16];
        \\    const entry_size: usize = if (is64) 64 else 40;
        \\    entry = table[0..entry_size];
        \\    return entry[32];
        \\}
    , "entry", 40, "entry"));
    try std.testing.expect(!try proveMinLenAt(
        \\fn f(table: []const u8, is64: bool) u8 {
        \\    const entry_size: usize = if (is64) 64 else 40;
        \\    var entry = table[0..entry_size];
        \\    entry = table[0..16];
        \\    return entry[32];
        \\}
    , "entry", 32, "entry"));
}

test "minlen: indirect header and scalar writes withdraw interval facts" {
    try std.testing.expect(!try proveMinLenAt(
        \\fn f(table: []const u8, is64: bool) u8 {
        \\    const entry_size: usize = if (is64) 64 else 40;
        \\    var entry = table[0..entry_size];
        \\    shrink(&entry);
        \\    return entry[32];
        \\}
        \\fn shrink(entry: *[]const u8) void { entry.* = entry.*[0..16]; }
    , "entry", 32, "entry"));
    try std.testing.expect(!try proveMinLenAt(
        \\fn f(table: []const u8, is64: bool) u8 {
        \\    var entry_size: usize = if (is64) 64 else 40;
        \\    shrink(&entry_size);
        \\    const entry = table[0..entry_size];
        \\    return entry[32];
        \\}
        \\fn shrink(size: *usize) void { size.* = 16; }
    , "entry", 32, "entry"));
}

test "minlen: static container extents prove only their own lower bound" {
    const src =
        \\fn f() u8 {
        \\    const base = "0123456789abcdef";
        \\    const entry = base[0..];
        \\    return entry[8];
        \\}
    ;
    try std.testing.expect(try proveMinLenAt(src, "entry", 16, "entry"));
    try std.testing.expect(!try proveMinLenAt(src, "entry", 17, "entry"));
}

fn proveMinLenWithEngine(src: [:0]const u8, container: []const u8, n: u64, arr: []const u8) !bool {
    const gpa = std.testing.allocator;
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-value-range-minimum-extent.zig", src);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const body = firstFnBody(tree) orelse return error.NoFnBody;
    const lbracket = subscriptLBracket(tree, arr) orelse return error.NoSubscript;
    return value_range.provesMinLen(gpa, tree, body, container, n, lbracket, &cache);
}

test "minlen: fixed array and whole-array slice preserve exact extents" {
    const src =
        \\fn f() u8 {
        \\    var base: [48]u8 = undefined;
        \\    const entry = base[0..];
        \\    return entry[32];
        \\}
    ;
    try std.testing.expect(try proveMinLenWithEngine(src, "entry", 48, "entry"));
    try std.testing.expect(!try proveMinLenWithEngine(src, "entry", 49, "entry"));
}

test "minlen: fixed array parameters differ from unbounded slice headers" {
    try std.testing.expect(try proveMinLenWithEngine(
        \\fn f(entry: *const [48]u8) u8 { return entry[32]; }
    , "entry", 48, "entry"));
    try std.testing.expect(!try proveMinLenWithEngine(
        \\fn f(entry: []const u8) u8 { return entry[32]; }
    , "entry", 48, "entry"));
}

test "minlen: scalar guard interval is captured only before a scalar rebind" {
    try std.testing.expect(try proveMinLenWithEngine(
        \\fn f(table: []const u8, entry_size: usize) u8 {
        \\    if (entry_size < 40) return 0;
        \\    const entry = table[0..entry_size];
        \\    return entry[32];
        \\}
    , "entry", 40, "entry"));
    try std.testing.expect(!try proveMinLenWithEngine(
        \\fn f(table: []const u8, size: usize) u8 {
        \\    var entry_size = size;
        \\    if (entry_size < 40) return 0;
        \\    entry_size = 16;
        \\    const entry = table[0..entry_size];
        \\    return entry[32];
        \\}
    , "entry", 40, "entry"));
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

test "nonempty: early-return with a pure OR operand preserves length" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn tail(self: *Foo, empty: bool) u8 {
        \\    if (self.buffer.len == 0 or empty) return 0;
        \\    return self.buffer[(self.index) % self.buffer.len];
        \\}
        \\
    , "self.buffer", "buffer"));
}

test "nonempty: unresolved pointer call in OR guard cannot preserve length" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn tail(self: *Foo) u8 {
        \\    if (self.buffer.len == 0 or self.empty()) return 0;
        \\    return self.buffer[(self.index) % self.buffer.len];
        \\}
        \\
    , "self.buffer", "buffer"));
}

test "nonempty: a negated call that is handed copies in an OR guard preserves length" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn last(arr: []const u32, extra: u32) u32 {
        \\    if (arr.len == 0 or !isReturn(extra)) return 0;
        \\    return arr[arr.len - 1];
        \\}
        \\fn isReturn(x: u32) bool { return x == 7; }
        \\
    , "arr", "arr"));
}

test "nonempty: a negated call handed the container's address in an OR guard cannot preserve length" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn last(arr: []const u32) u32 {
        \\    var view = arr;
        \\    if (view.len == 0 or !shrink(&view)) return 0;
        \\    return view[view.len - 1];
        \\}
        \\fn shrink(list: *[]const u32) bool { list.* = list.*[0..0]; return true; }
        \\
    , "view", "view"));
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

test "slice tail: a strict length guard on the offset proves the tail non-empty" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn f(name: []const u8, prefix: []const u8) u8 {
        \\    if (name.len <= prefix.len) return 0;
        \\    const tail = name[prefix.len..];
        \\    return tail[tail.len - 1];
        \\}
        \\
    , "tail", "tail"));
}

test "slice tail: a strict length guard on a literal offset proves the tail non-empty" {
    try std.testing.expect(try proveNonemptyAt(
        \\fn f(name: []const u8) u8 {
        \\    if (name.len > 3) {
        \\        const tail = name[3..];
        \\        return tail[tail.len - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "tail", "tail"));
}

test "slice tail: a weak length guard leaves the tail possibly empty" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(name: []const u8, prefix: []const u8) u8 {
        \\    if (name.len < prefix.len) return 0;
        \\    const tail = name[prefix.len..];
        \\    return tail[tail.len - 1];
        \\}
        \\
    , "tail", "tail"));
}

test "slice tail: a guard on another offset leaves the tail possibly empty" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(name: []const u8, prefix: []const u8, other: []const u8) u8 {
        \\    if (name.len <= other.len) return 0;
        \\    const tail = name[prefix.len..];
        \\    return tail[tail.len - 1];
        \\}
        \\
    , "tail", "tail"));
}

test "slice tail: an offset rewritten after the guard leaves the tail possibly empty" {
    try std.testing.expect(!try proveNonemptyAt(
        \\fn f(name: []const u8, prefix: []const u8) u8 {
        \\    var cut = prefix.len;
        \\    if (name.len <= cut) return 0;
        \\    cut = name.len;
        \\    const tail = name[cut..];
        \\    return tail[tail.len - 1];
        \\}
        \\
    , "tail", "tail"));
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

test "float width: generic widening needs a closed caller set" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/intfromfloat_without_clamp.zig");
    try testing.expectNoFireTyped(rule.check,
        \\fn valid(comptime T: type, value: T) bool {
        \\    const wide: f64 = @floatCast(value);
        \\    if (wide != wide) return false;
        \\    return wide >= -0x1p63 and wide < 0x1p63;
        \\}
        \\fn convert(comptime T: type, value: T) i64 {
        \\    if (!valid(T, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(value: f32) i64 { return convert(f32, value); }
    );
    try testing.expectFiresTyped(rule.check, "intfromfloat-without-clamp",
        \\fn valid(comptime T: type, value: T) bool {
        \\    const wide: f64 = @floatCast(value);
        \\    if (wide != wide) return false;
        \\    return wide >= -0x1p63 and wide < 0x1p63;
        \\}
        \\pub fn convert(comptime T: type, value: T) i64 {
        \\    if (!valid(T, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(value: f32) i64 { return convert(f32, value); }
    );
    try testing.expectFiresTyped(rule.check, "intfromfloat-without-clamp",
        \\fn valid(comptime T: type, value: T) bool {
        \\    const wide: f64 = @floatCast(value);
        \\    if (wide != wide) return false;
        \\    return wide >= -0x1p63 and wide < 0x1p63;
        \\}
        \\fn convert(comptime T: type, value: T) i64 {
        \\    if (!valid(T, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub const exported = convert;
        \\pub fn single(value: f32) i64 { return convert(f32, value); }
    );
}

test "float width: private generic widening retains every caller width" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/intfromfloat_without_clamp.zig");
    try testing.expectNoFireTyped(rule.check,
        \\fn valid(comptime T: type, value: T) bool {
        \\    const wide: f64 = @floatCast(value);
        \\    return wide >= 0 and wide < 256;
        \\}
        \\fn convert(comptime T: type, value: T) u8 {
        \\    if (!valid(T, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(value: f32) u8 { return convert(f32, value); }
        \\pub fn double(value: f64) u8 { return convert(f64, value); }
    );
    try testing.expectFiresTyped(rule.check, "intfromfloat-without-clamp",
        \\fn valid(comptime T: type, value: T) bool {
        \\    const wide: f32 = @floatCast(value);
        \\    return wide >= 0 and wide < 256;
        \\}
        \\fn convert(comptime T: type, value: T) u8 {
        \\    if (!valid(T, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(value: f32) u8 { return convert(f32, value); }
        \\pub fn double(value: f64) u8 { return convert(f64, value); }
    );
}

test "float width: a generic destination needs a lossless width floor" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/intfromfloat_without_clamp.zig");
    try testing.expectNoFireTyped(rule.check,
        \\fn valid(comptime Source: type, comptime Wide: type, value: Source) bool {
        \\    const wide: Wide = @floatCast(value);
        \\    return wide >= 0 and wide < 256;
        \\}
        \\fn convert(comptime Source: type, comptime Wide: type, value: Source) u8 {
        \\    if (!valid(Source, Wide, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(value: f32) u8 { return convert(f32, f32, value); }
        \\pub fn widened(value: f32) u8 { return convert(f32, f64, value); }
    );
    try testing.expectFiresTyped(rule.check, "intfromfloat-without-clamp",
        \\fn valid(comptime Source: type, comptime Wide: type, value: Source) bool {
        \\    const wide: Wide = @floatCast(value);
        \\    return wide >= 0 and wide < 256;
        \\}
        \\fn convert(comptime Source: type, comptime Wide: type, value: Source) u8 {
        \\    if (!valid(Source, Wide, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn narrowed(value: f64) u8 { return convert(f64, f32, value); }
        \\pub fn double(value: f64) u8 { return convert(f64, f64, value); }
    );
}

test "float width: contextual generic casts prove only lossless source bounds" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/intfromfloat_without_clamp.zig");
    try testing.expectNoFireTyped(rule.check,
        \\fn valid(comptime Source: type, comptime Wide: type, value: Source) bool {
        \\    const wide = @as(Wide, @floatCast(value));
        \\    return wide >= 0 and wide < 256;
        \\}
        \\fn convert(comptime Source: type, comptime Wide: type, value: Source) u8 {
        \\    if (!valid(Source, Wide, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn single(value: f32) u8 { return convert(f32, f32, value); }
        \\pub fn widened(value: f32) u8 { return convert(f32, f64, value); }
    );
    try testing.expectFiresTyped(rule.check, "intfromfloat-without-clamp",
        \\fn valid(comptime Source: type, comptime Wide: type, value: Source) bool {
        \\    const wide: Wide = @floatCast(@as(f32, @floatCast(value)));
        \\    return wide >= 0 and wide < 256;
        \\}
        \\fn convert(comptime Source: type, comptime Wide: type, value: Source) u8 {
        \\    if (!valid(Source, Wide, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn widened(value: f64) u8 { return convert(f64, f64, value); }
    );
}

test "float width: unclosed generic destinations cannot prove the consumer range" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/intfromfloat_without_clamp.zig");
    try testing.expectFiresTyped(rule.check, "intfromfloat-without-clamp",
        \\fn valid(comptime Source: type, comptime Wide: type, value: Source) bool {
        \\    const wide: Wide = @floatCast(value);
        \\    return wide >= 0 and wide < 256;
        \\}
        \\pub fn convert(comptime Source: type, comptime Wide: type, value: Source) u8 {
        \\    if (!valid(Source, Wide, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn widened(value: f32) u8 { return convert(f32, f64, value); }
    );
    try testing.expectFiresTyped(rule.check, "intfromfloat-without-clamp",
        \\fn valid(comptime Source: type, comptime Wide: type, value: Source) bool {
        \\    const wide: Wide = @floatCast(value);
        \\    return wide >= 0 and wide < 256;
        \\}
        \\fn convert(comptime Source: type, comptime Wide: type, value: Source) u8 {
        \\    if (!valid(Source, Wide, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub const exported = convert;
        \\pub fn widened(value: f32) u8 { return convert(f32, f64, value); }
    );
    try testing.expectFiresTyped(rule.check, "intfromfloat-without-clamp",
        \\fn valid(comptime Source: type, comptime Wide: type, value: Source) bool {
        \\    const wide: Wide = @floatCast(value);
        \\    return wide >= 0 and wide < 256;
        \\}
        \\fn convert(comptime Source: type, comptime Wide: type, value: Source) u8 {
        \\    if (!valid(Source, Wide, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
    );
}

test "float width: every generic destination rounding contributes to the bound" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/intfromfloat_without_clamp.zig");
    try testing.expectFiresTyped(rule.check, "intfromfloat-without-clamp",
        \\fn valid(comptime Wide: type, value: f64) bool {
        \\    const wide: Wide = @floatCast(value);
        \\    return wide >= 0 and wide <= 255.99999999999999999;
        \\}
        \\fn convert(comptime Wide: type, value: f64) u8 {
        \\    if (!valid(Wide, value)) return 0;
        \\    return @intFromFloat(value);
        \\}
        \\pub fn double(value: f64) u8 { return convert(f64, value); }
        \\pub fn quad(value: f64) u8 { return convert(f128, value); }
    );
}

/// The `occurrence`-th `[` token preceded by identifier `arr` (0-based).  A
/// dominating read and the queried access often share a name, so the position
/// of the access under test has to be selectable.
fn nthSubscriptLBracket(tree: *const Ast, arr: []const u8, occurrence: usize) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    var seen: usize = 0;
    var t: Ast.TokenIndex = 1;
    while (t < tags.len) : (t += 1) {
        if (tags[t] != .l_bracket) continue;
        if (tags[t - 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t - 1), arr)) continue;
        if (seen == occurrence) return t;
        seen += 1;
    }
    return null;
}

fn proveAtNth(
    src: [:0]const u8,
    target: []const u8,
    arr: []const u8,
    occurrence: usize,
) !bool {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const body = firstFnBody(&tree) orelse return error.NoFnBody;
    const lbracket = nthSubscriptLBracket(&tree, arr, occurrence) orelse return error.NoSubscript;
    return try value_range.provesNonzero(gpa, &tree, body, target, lbracket, null);
}

fn proveNonemptyAtNth(
    src: [:0]const u8,
    container: []const u8,
    arr: []const u8,
    occurrence: usize,
) !bool {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const body = firstFnBody(&tree) orelse return error.NoFnBody;
    const lbracket = nthSubscriptLBracket(&tree, arr, occurrence) orelse return error.NoSubscript;
    return try value_range.provesNonempty(gpa, &tree, body, container, lbracket, null);
}

fn proveMinLenAtNth(
    src: [:0]const u8,
    container: []const u8,
    n: u64,
    arr: []const u8,
    occurrence: usize,
) !bool {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const body = firstFnBody(&tree) orelse return error.NoFnBody;
    const lbracket = nthSubscriptLBracket(&tree, arr, occurrence) orelse return error.NoSubscript;
    return try value_range.provesMinLen(gpa, &tree, body, container, n, lbracket, null);
}

/// The `array_access` node whose subscript `[` is `token`.  Nodes are in
/// pre-order, so the first enclosing match is the one that owns the bracket.
fn arrayAccessAt(tree: *const Ast, token: Ast.TokenIndex) ?Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .array_access) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.firstToken(node) <= token and token <= tree.lastToken(node)) return node;
    }
    return null;
}

/// The `X` of an `arr[X - 1]` subscript, with an explicit index conversion
/// peeled off.  A signed operand only reaches a subscript through `@intCast`,
/// and the conversion is not what the positivity rule asks about — the operand
/// is.  `@intCast` is the only transparent one: every other builtin computes a
/// value of its own (`@min`, `@max`, `@abs`), so an `arr[@max(a, b) - 1]`
/// subscripts with the builtin's result, not with `b`, and asking about `b`
/// would answer a question the source never asks.
fn subscriptMinuend(tree: *const Ast, subscript: Ast.Node.Index) ?Ast.Node.Index {
    var node = subscript;
    var builtin_buffer: [2]Ast.Node.Index = undefined;
    if (tree.builtinCallParams(&builtin_buffer, node)) |arguments| {
        if (arguments.len != 1) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@intCast")) return null;
        node = arguments[0];
    }
    while (tree.nodeTag(node) == .grouped_expression) node = tree.nodeData(node).node_and_token[0];
    if (tree.nodeTag(node) != .sub) return null;
    return tree.nodeData(node).node_and_node[0];
}

/// Query `value_range.provesPositive` on the `X` of an `arr[X - 1]` access —
/// the shape the index-minus-one rule asks about, where the proof that matters
/// is a dominating `arr.len == 0` guard rather than anything in the index.
fn provePositiveForLastIndex(
    src: [:0]const u8,
    arr: []const u8,
    occurrence: usize,
) !bool {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const body = firstFnBody(&tree) orelse return error.NoFnBody;
    const lbracket = nthSubscriptLBracket(&tree, arr, occurrence) orelse return error.NoSubscript;
    const access = arrayAccessAt(&tree, lbracket) orelse return error.NoSubscript;
    const minuend = subscriptMinuend(&tree, tree.nodeData(access).node_and_node[1]) orelse
        return error.NoSubscript;
    return try value_range.provesPositive(gpa, &tree, body, minuend, lbracket, null);
}

test "nonzero: a join of arms bounding DIFFERENT names proves neither of them" {
    // Each arm constrains only its OWN operand, so nothing is known about `i`
    // on the else path and nothing about `j` on the then path.  A per-name
    // fact that outlived the join would be describing a guard this state never
    // passed.
    const joined: [:0]const u8 =
        \\fn f(flag: bool, i: usize, j: usize, buf: []const u8, other: []const u8) u8 {
        \\    if (flag) {
        \\        if (i == 0) return 0;
        \\    } else {
        \\        if (j == 0) return 0;
        \\    }
        \\    return buf[i - 1] + other[j - 1];
        \\}
        \\
    ;
    try std.testing.expect(!try proveAt(joined, "i", "buf"));
    try std.testing.expect(!try proveAt(joined, "j", "other"));
    // The same join with a dominating guard per name AFTER it: each bound is
    // then proved by its own check, which is what makes the pair above a
    // statement about the join rather than about a walk that gave up.
    const guarded: [:0]const u8 =
        \\fn f(flag: bool, i: usize, j: usize, buf: []const u8, other: []const u8) u8 {
        \\    if (flag) {
        \\        if (i == 0) return 0;
        \\    } else {
        \\        if (j == 0) return 0;
        \\    }
        \\    if (i == 0) return 0;
        \\    if (j == 0) return 0;
        \\    return buf[i - 1] + other[j - 1];
        \\}
        \\
    ;
    try std.testing.expect(try proveAt(guarded, "i", "buf"));
    try std.testing.expect(try proveAt(guarded, "j", "other"));
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

test "nonzero: if-condition OR descent refines a later operand" {
    try std.testing.expect(try proveAt(
        \\fn f(tags: []const u8, other: []const u8, t: usize) bool {
        \\    if (t < 3 or other[t - 3] != 0 or tags[t - 1] != 0) return false;
        \\    return true;
        \\}
    , "t", "tags"));
}

test "nonzero: an unsplit `or` chain keeps its leading bound past a read-only call" {
    // One `if` holds all three tests, so the walk has to descend past two
    // calls before it reaches `t < 3`.  Neither call can write the by-value
    // `t` parameter — a callee gets a copy of a slice argument, and this
    // parameter's own address never leaves the frame — so the bound still
    // holds once they have run.
    try std.testing.expect(try proveAt(
        \\const std = @import("std");
        \\fn f(tags: []const u8, other: []const u8, t: usize, flag: bool) u8 {
        \\    if (t < 3 or !std.mem.eql(u8, tags, other) or probe(flag)) return 0;
        \\    return tags[t - 1];
        \\}
        \\fn probe(b: bool) bool {
        \\    return b;
        \\}
    , "t", "tags"));
}

test "nonzero: a later call that can write the leading scalar keeps its bound out" {
    // `zero(&k)` hands the callee `&k`, so `k >= 3` describes the state
    // BEFORE it ran and after it ran `k` is 0.  Falling through really does
    // reach `tags[k - 1]` with `k == 0`.
    try std.testing.expect(!try proveAt(
        \\fn f(seed: usize, tags: []const u8) u8 {
        \\    var k = seed;
        \\    if (k < 3 or zero(&k)) return 0;
        \\    return tags[k - 1];
        \\}
        \\fn zero(slot: *usize) bool {
        \\    slot.* = 0;
        \\    return false;
        \\}
    , "k", "tags"));
}

test "nonzero: a later operand that writes the leading scalar itself keeps its bound out" {
    // No callee at all here: the second operand's own body is the write, so
    // the earlier comparison is already stale by the time the walk moves on.
    // The block evaluates to false, so the guard really does fall through —
    // with `k == 0`, one below the bound it recorded.
    try std.testing.expect(!try proveAt(
        \\fn f(seed: usize, tags: []const u8) u8 {
        \\    var k = seed;
        \\    if (k < 3 or blk: {
        \\        k = 0;
        \\        break :blk false;
        \\    }) return 0;
        \\    return tags[k - 1];
        \\}
    , "k", "tags"));
}

test "nonzero: a later method call that can reach the leading field keeps its bound out" {
    // `self.count` is a field path, so its stability is the receiver's, and
    // `bump()` is handed `&self` however the source spells the call.
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn f(self: *Bag, items: []const u8) u8 {
        \\    if (self.count < 3 or self.bump()) return 0;
        \\    return items[self.count - 1];
        \\}
        \\const Bag = struct {
        \\    count: usize,
        \\    fn bump(self: *Bag) bool {
        \\        self.count = 0;
        \\        return false;
        \\    }
        \\};
    , "items", 0));
}

test "nonempty: a negated earlier operand's length fact is dropped past a later clear" {
    // The guard is false here, so `!(items.len > 0)` is false too and the
    // length comparison it hides is proved the other way round: `items` is
    // non-empty.  `wipe(&items)` is handed the address afterwards and can
    // empty the slice, so that fact describes a state the read below no
    // longer has.
    try std.testing.expect(!try proveNonemptyAt(
        \\fn tail(items: []u8) u8 {
        \\    if (!(items.len > 0) or wipe(&items)) return 0;
        \\    return items[items.len - 1];
        \\}
        \\fn wipe(slot: *[]u8) bool {
        \\    slot.len = 0;
        \\    return false;
        \\}
    , "items", "items"));
}

test "nonzero: a nested `or` drops every name its later operand can reach" {
    // Proved false, the outer `or` settles both operands, so the inner one
    // settles too: `i >= 3` AND `j >= 3` are both proved, and both describe
    // the state before `wipe(&j)` ran.  The inner operand is parenthesised, so
    // nothing about its two names comes from a single comparison.
    try std.testing.expect(!try proveAt(
        \\fn f(seed: usize, tags: []const u8) u8 {
        \\    var i = seed;
        \\    var j = seed;
        \\    if ((i < 3 or j < 3) or wipe(&j)) return 0;
        \\    return tags[j - 1];
        \\}
        \\fn wipe(slot: *usize) bool {
        \\    slot.* = 0;
        \\    return false;
        \\}
    , "j", "tags"));
}

test "nonzero: a nested `or` keeps its names past a later operand that reaches none" {
    // Same shape as the case above, with a later operand that gets a copy of
    // `seed` and no address at all: neither name moves, so both bounds still
    // hold when the read below runs.
    try std.testing.expect(try proveAt(
        \\fn f(seed: usize, tags: []const u8) u8 {
        \\    var i = seed;
        \\    var j = seed;
        \\    if ((i < 3 or j < 3) or probe(seed)) return 0;
        \\    return tags[j - 1];
        \\}
        \\fn probe(x: usize) bool {
        \\    return x == 0;
        \\}
    , "j", "tags"));
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
        \\    return tags[@intCast(k - 1)];
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

// ── dominated reads need a receiver that bounds its own length ─────
// `c[i]` reaching a later statement proves `c.len > i` only for a slice or a
// fixed-size array.  A C pointer has no length at all, so its index proves
// nothing about one — indexing a `[*c]u8` is never a bounds check.

test "read-bounds: a dominating slice read proves the lower bound" {
    try std.testing.expect(try proveMinLenAtNth(
        \\fn decode(bytes: []const u8) u8 {
        \\    const head = bytes[3];
        \\    _ = head;
        \\    return bytes[7 - 1];
        \\}
        \\
    , "bytes", 4, "bytes", 1));
}

test "read-bounds: a dominating fixed-array read proves the lower bound" {
    try std.testing.expect(try proveMinLenAtNth(
        \\fn decode(bytes: [8]u8) u8 {
        \\    const head = bytes[3];
        \\    _ = head;
        \\    return bytes[7 - 1];
        \\}
        \\
    , "bytes", 4, "bytes", 1));
}

test "read-bounds: a dominating C-pointer read proves NO length (no false-negative)" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn decode(p: [*c]u8) u8 {
        \\    const head = p[3];
        \\    _ = head;
        \\    return p[7 - 1];
        \\}
        \\
    , "p", 4, "p", 1));
}

test "read-bounds: a dominating many-pointer read proves NO length (no false-negative)" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn decode(p: [*]const u8) u8 {
        \\    const head = p[3];
        \\    _ = head;
        \\    return p[7 - 1];
        \\}
        \\
    , "p", 4, "p", 1));
}

test "read-bounds: a dominating C-pointer read proves not even non-emptiness" {
    // The index is unknown, so the only claim available is `len >= 1` — still
    // a claim about a length a C pointer does not have.
    try std.testing.expect(!try proveNonemptyAtNth(
        \\fn first(p: [*c]const u8, i: usize) u8 {
        \\    const head = p[i];
        \\    _ = head;
        \\    return p[7 - 1];
        \\}
        \\
    , "p", "p", 1));
}

test "read-bounds: a dominating read on an unannotated local proves NO length" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn decode(src: []const u8) u8 {
        \\    var alias = src;
        \\    const head = alias[3];
        \\    _ = head;
        \\    return alias[7 - 1];
        \\}
        \\
    , "alias", 4, "alias", 1));
}

test "read-bounds: a sibling block's slice type does not type this receiver" {
    // Both arms declare `bytes`, so only the one in scope where the read
    // happens may type it.  `[*c]const u8` has no length for `bytes[3]` to
    // bound, whatever the other arm declared.
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn decode(flag: bool, src: []const u8) u8 {
        \\    if (flag) {
        \\        const bytes: []const u8 = src;
        \\        _ = bytes[0];
        \\    } else {
        \\        const bytes: [*c]const u8 = src.ptr;
        \\        const head = bytes[3];
        \\        _ = head;
        \\        return bytes[7 - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "bytes", 4, "bytes", 2));
}

test "read-bounds: the receiver's own block type bounds its index" {
    // Mirror of the case above: the arm that reads is the slice one, so its
    // dominating read proves the bound even though a sibling arm names the
    // same local with a C-pointer type.
    try std.testing.expect(try proveMinLenAtNth(
        \\fn decode(flag: bool, src: []const u8) u8 {
        \\    if (flag) {
        \\        const bytes: [*c]const u8 = src.ptr;
        \\        _ = bytes[0];
        \\    } else {
        \\        const bytes: []const u8 = src;
        \\        const head = bytes[3];
        \\        _ = head;
        \\        return bytes[7 - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "bytes", 4, "bytes", 2));
}

test "read-bounds: a local C-pointer receiver proves NO length" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn decode(src: []const u8) u8 {
        \\    const p: [*c]const u8 = src.ptr;
        \\    const head = p[3];
        \\    _ = head;
        \\    return p[7 - 1];
        \\}
        \\
    , "p", 4, "p", 1));
}

// ── what a call can reach ───────────────────────────────────────

test "escape: a pointer local with no established target reaches everything" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(buf: []u8) u8 {
        \\    var p: *[]u8 = makePtr();
        \\    if (buf.len >= 4) {
        \\        mutate(p);
        \\        return buf[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "buf", 4, "buf", 0));
}

test "escape: a pointer-to-pointer local with no target reaches everything" {
    // `**[]u8` is one `**` token, not two `*` ones, so a spelling test that
    // only looks for `*` misses it and reads `p` as a by-value header.  A
    // callee holding `p` can write through `p.*`, so nothing is call-stable.
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(src: []u8) u8 {
        \\    const buf: []u8 = src;
        \\    const p: **[]u8 = makeDouble();
        \\    if (buf.len >= 4) {
        \\        mutate(p);
        \\        return buf[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "buf", 4, "buf", 0));
}

test "escape: a pointer PARAMETER cannot name a local of this body" {
    // `holder` was pointed at storage that existed before this frame, so it
    // cannot rewrite `buf` — the bound survives a call that takes it.
    try std.testing.expect(try proveMinLenAtNth(
        \\fn f(holder: *Holder, buf: []u8) u8 {
        \\    if (buf.len >= 4) {
        \\        touch(holder);
        \\        return buf[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "buf", 4, "buf", 0));
}

test "escape: a method call on the tracked field may rewrite it" {
    // Zig passes `bag` to a pointer-receiver method as `&bag`, so `reset()`
    // can truncate `bag.items` without any address appearing in the source.
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(bag: Bag) u8 {
        \\    if (bag.items.len >= 4) {
        \\        bag.reset();
        \\        return bag.items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "bag.items", 4, "items", 0));
}

test "escape: a by-value argument is a copy and keeps the bound" {
    try std.testing.expect(try proveMinLenAtNth(
        \\fn f(buf: []u8) u8 {
        \\    if (buf.len >= 4) {
        \\        consume(buf);
        \\        return buf[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "buf", 4, "buf", 0));
}

test "escape: a pointer bound to another container does not reach this one" {
    try std.testing.expect(try proveMinLenAtNth(
        \\fn f(a: []u8, buf: []u8) u8 {
        \\    const p: *[]u8 = &a;
        \\    if (buf.len >= 4) {
        \\        mutate(p);
        \\        return buf[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "buf", 4, "buf", 0));
}

// A binding only describes the pointer on paths that reach it.  One nested in
// a branch or a loop may never run, so after it the pointer may name anything
// the earlier bindings could name — the analysis cannot pick a winner.

test "escape: a conditional rebinding invalidates every target conservatively" {
    // `p` may still be `&a` when the flag is false, so `mutate(p)` may still
    // reach `a`'s header; nothing about `buf` follows from it either way.
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(a: []u8, other: []u8, buf: []u8, flag: bool) u8 {
        \\    var p: *[]u8 = &a;
        \\    if (flag) p = &other;
        \\    if (buf.len >= 4) {
        \\        mutate(p);
        \\        return buf[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "buf", 4, "buf", 0));
}

test "escape: a loop rebinding invalidates every target conservatively" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(a: []u8, other: []u8, buf: []u8) u8 {
        \\    var p: *[]u8 = &a;
        \\    var i: usize = 0;
        \\    while (i < 2) : (i += 1) {
        \\        p = &other;
        \\    }
        \\    if (buf.len >= 4) {
        \\        mutate(p);
        \\        return buf[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "buf", 4, "buf", 0));
}

test "escape: an unconditional rebinding still resolves to its own target" {
    // Both bindings run on every path, so `p` names `a` alone and cannot
    // reach `buf` — the position must be used, not just "was it rebound?".
    try std.testing.expect(try proveMinLenAtNth(
        \\fn f(a: []u8, buf: []u8) u8 {
        \\    var p: *[]u8 = &a;
        \\    p = &a;
        \\    if (buf.len >= 4) {
        \\        mutate(p);
        \\        return buf[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "buf", 4, "buf", 0));
}

// ── length-changing methods ────────────────────────────────────

test "mutator: appendSliceAssumeCapacity drops the proven bound" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(list: std.ArrayList(u8), other: []const u8) u8 {
        \\    if (list.items.len >= 4) {
        \\        list.appendSliceAssumeCapacity(other);
        \\        return list.items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "list.items", 4, "items", 0));
}

test "mutator: replaceRange drops the proven bound" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(list: std.ArrayList(u8)) u8 {
        \\    if (list.items.len >= 4) {
        \\        list.replaceRange(0, 1, other);
        \\        return list.items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "list.items", 4, "items", 0));
}

test "mutator: addManyAsArrayAssumeCapacity drops the proven bound" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(list: std.ArrayList(u8)) u8 {
        \\    if (list.items.len >= 4) {
        \\        const room = list.addManyAsArrayAssumeCapacity(2);
        \\        _ = room;
        \\        return list.items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "list.items", 4, "items", 0));
}

test "mutator: a length-preserving free call keeps the proven bound" {
    try std.testing.expect(try proveMinLenAtNth(
        \\fn f(list: std.ArrayList(u8), other: []const u8) u8 {
        \\    if (list.items.len >= 4) {
        \\        const same = std.mem.eql(u8, list.items, other);
        \\        _ = same;
        \\        return list.items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "list.items", 4, "items", 0));
}

// ── a switch between the guard and the use ────────────────────────
//
// A switch whose arms do not contain the queried use still runs every arm
// before it, so the arms have to be walked for their EFFECTS.  Discarding
// every fact instead threw away proofs for containers the switch never
// mentions — the common `if (C.len == 0) return;` /
// `const trailing = switch (tag) { … };` / `C[C.len - 1]` shape.

test "switch between guard and use: a non-mutating arm keeps the bound" {
    try std.testing.expect(try proveMinLenAtNth(
        \\fn f(list: std.ArrayList(u8), mode: u8) u8 {
        \\    if (list.items.len < 4) return 0;
        \\    const trailing = switch (mode) {
        \\        0 => false,
        \\        else => true,
        \\    };
        \\    if (trailing) {
        \\        return list.items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "list.items", 4, "items", 0));
}

test "switch between guard and use: an arm that writes the receiver drops the bound" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(list: std.ArrayList(u8), mode: u8) u8 {
        \\    if (list.items.len < 4) return 0;
        \\    const trailing = switch (mode) {
        \\        0 => list.discard(),
        \\        else => true,
        \\    };
        \\    if (trailing) {
        \\        return list.items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "list.items", 4, "items", 0));
}

test "switch between guard and use: a standard shrinking arm drops the bound" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(list: std.ArrayList(u8), mode: u8) u8 {
        \\    if (list.items.len < 4) return 0;
        \\    const trailing = switch (mode) {
        \\        0 => list.clearRetainingCapacity(),
        \\        else => true,
        \\    };
        \\    if (trailing) {
        \\        return list.items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "list.items", 4, "items", 0));
}

test "switch between guard and use: a slice local keeps its own length" {
    try std.testing.expect(try proveMinLenAtNth(
        \\fn f(src: []const u8, mode: u8) u8 {
        \\    const items: []const u8 = src;
        \\    if (items.len < 4) return 0;
        \\    const trailing = switch (mode) {
        \\        0 => false,
        \\        else => true,
        \\    };
        \\    if (trailing) {
        \\        return items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "items", 4, "items", 0));
}

test "switch between guard and use: a slice local whose address escapes drops the bound" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(src: []const u8, mode: u8) u8 {
        \\    const items: []const u8 = src;
        \\    if (items.len < 4) return 0;
        \\    const trailing = switch (mode) {
        \\        0 => fill(&items),
        \\        else => true,
        \\    };
        \\    if (trailing) {
        \\        return items[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "items", 4, "items", 0));
}

// ── call stability: an address is not a by-value header ──────────

test "call stability: a pointer parameter is not call-stable" {
    try std.testing.expect(!try proveMinLenAtNth(
        \\const Holder = struct { data: []const u8 };
        \\fn f(h: *const Holder) u8 {
        \\    if (h.data.len >= 4) {
        \\        touch(h.data.len);
        \\        return h.data[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "h.data", 4, "data", 0));
}

test "call stability: a by-value holder parameter is call-stable" {
    try std.testing.expect(try proveMinLenAtNth(
        \\const Holder = struct { data: []const u8 };
        \\fn f(h: Holder) u8 {
        \\    if (h.data.len >= 4) {
        \\        touch(h.data.len);
        \\        return h.data[3];
        \\    }
        \\    return 0;
        \\}
        \\
    , "h.data", 4, "data", 0));
}

test "call stability: a discarded address leaves a container call-stable" {
    // `_ = &items` hands the address to nobody, so the length still describes
    // the by-value header `probe` is given a copy of.
    try std.testing.expect(try proveMinLenAtNth(
        \\fn f(src: []const u8, other: []const u8) u8 {
        \\    var items: []const u8 = src;
        \\    if (items.len < 4) return 0;
        \\    _ = &items;
        \\    probe(other);
        \\    return items[3];
        \\}
        \\fn probe(items: []const u8) void {
        \\    _ = items.len;
        \\}
        \\
    , "items", 4, "items", 0));
}

test "call stability: an address handed to a writer is still an escape" {
    // Same body with the address really handed out: `truncate` rewrites the
    // local's own header, so the bound describes a value that is gone.
    try std.testing.expect(!try proveMinLenAtNth(
        \\fn f(src: []const u8) u8 {
        \\    var items: []const u8 = src;
        \\    if (items.len < 4) return 0;
        \\    _ = &items;
        \\    truncate(&items);
        \\    return items[3];
        \\}
        \\fn truncate(items: *[]const u8) void {
        \\    items.* = items.*[0..1];
        \\}
        \\
    , "items", 4, "items", 0));
}

test "call stability: a discarded address keeps a guarded scalar past a call" {
    try std.testing.expect(try proveAt(
        \\fn f(seed: usize, bytes: []const u8) u8 {
        \\    var i = seed;
        \\    if (i == 0) return 0;
        \\    _ = &i;
        \\    probe(bytes);
        \\    return bytes[i - 1];
        \\}
        \\fn probe(items: []const u8) void {
        \\    _ = items.len;
        \\}
        \\
    , "i", "bytes"));
}

test "call stability: a writer handed the scalar drops the bound" {
    // The discard is still there, but `zero` writes through the address, so
    // the read really can happen with `i == 0`.
    try std.testing.expect(!try proveAt(
        \\fn f(seed: usize, bytes: []const u8) u8 {
        \\    var i = seed;
        \\    if (i == 0) return 0;
        \\    _ = &i;
        \\    zero(&i);
        \\    return bytes[i - 1];
        \\}
        \\fn zero(slot: *usize) void {
        \\    slot.* = 0;
        \\}
        \\
    , "i", "bytes"));
}

// ── guarded-else last-element reads ──────────────────────────────

test "guarded-else: a switch between the len guard and the last-element read proves" {
    try std.testing.expect(try provePositiveForLastIndex(
        \\fn f(buf: []const u8, mode: u8) u8 {
        \\    if (buf.len == 0) return 0;
        \\    const trailing = switch (mode) {
        \\        0 => false,
        \\        else => true,
        \\    };
        \\    if (trailing) {
        \\        return buf[buf.len - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "buf", 0));
}

test "guarded-else: a shrinking switch arm leaves the last-element read unproven" {
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn f(list: std.ArrayList(u8), mode: u8) u8 {
        \\    if (list.items.len == 0) return 0;
        \\    const trailing = switch (mode) {
        \\        0 => list.discard(),
        \\        else => true,
        \\    };
        \\    if (trailing) {
        \\        return list.items[list.items.len - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "items", 0));
}

test "guarded-else: an arm that hands out the container's address is unproven" {
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn f(list: std.ArrayList(u8), owner: *std.ArrayList(u8), mode: u8) u8 {
        \\    if (list.items.len == 0) return 0;
        \\    const trailing = switch (mode) {
        \\        0 => owner.adopt(&list.items),
        \\        else => true,
        \\    };
        \\    if (trailing) {
        \\        return list.items[list.items.len - 1];
        \\    }
        \\    return 0;
        \\}
        \\
    , "items", 0));
}

// ── Budget exhaustion ────────────────────────────────────────

/// A body with more statements than a query has steps.  Every statement
/// costs the statement walk at least one step, so the budget cannot
/// survive this many of them no matter what else the body does — the
/// query has to fail rather than answer from the statements it did
/// reach.
fn stepHeavySource(gpa: std.mem.Allocator, statements: usize) ![]u8 {
    var source: std.ArrayListUnmanaged(u8) = .empty;
    errdefer source.deinit(gpa);
    try source.appendSlice(gpa, "fn f(arr: []const u8) u8 {\n    var x: u8 = 0;\n");
    for (0..statements) |_| try source.appendSlice(gpa, "    x=0;\n");
    try source.appendSlice(gpa, "    return arr[x];\n}\n");
    return try source.toOwnedSlice(gpa);
}

/// A body nested deeper than the walk's frame bound.  Each `if` costs
/// two frames — the condition, then the block holding the next level —
/// so this many levels cannot be walked all the way down.
fn deepSource(gpa: std.mem.Allocator, levels: usize) ![]u8 {
    var source: std.ArrayListUnmanaged(u8) = .empty;
    errdefer source.deinit(gpa);
    try source.appendSlice(gpa, "fn f(arr: []const u8) u8 {\n");
    for (0..levels) |_| try source.appendSlice(gpa, "if (arr.len > 0) {\n");
    try source.appendSlice(gpa, "return 0;\n");
    for (0..levels) |_| try source.appendSlice(gpa, "}\n");
    try source.appendSlice(gpa, "return arr[arr.len - 1];\n}\n");
    return try source.toOwnedSlice(gpa);
}

/// Parse `source`, find the fn body and the `[` of the subscript on
/// `arr`, then ask whether `arr` is provably non-empty there.  Exhaustive:
/// the budget error has to come back out, not be turned into `false`.
fn provesNonemptyIn(gpa: std.mem.Allocator, source: []const u8) !bool {
    const src = try gpa.dupeSentinel(u8, source, 0);
    defer gpa.free(src);
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const body = firstFnBody(&tree) orelse return error.NoFnBody;
    const lbracket = subscriptLBracket(&tree, "arr") orelse return error.NoSubscript;
    return value_range.provesNonempty(gpa, &tree, body, "arr", lbracket, null);
}

test "a query that spends its step budget fails instead of answering" {
    const gpa = std.testing.allocator;
    budget_mod.clear();
    const source = try stepHeavySource(gpa, value_range.step_budget + 1_000);
    defer gpa.free(source);
    try std.testing.expectError(error.AnalysisBudgetExceeded, provesNonemptyIn(gpa, source));
    // The walk really did run out of steps, rather than giving up on
    // some other bound.
    const taken = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_steps, taken.limit);
    try std.testing.expectEqual(value_range.step_budget, taken.limit_value);
    try std.testing.expectEqual(value_range.step_budget, taken.reached);
}

test "a depth give-up names the depth bound, not the step budget" {
    const gpa = std.testing.allocator;
    budget_mod.clear();
    const source = try deepSource(gpa, 50);
    defer gpa.free(source);
    try std.testing.expectError(error.AnalysisBudgetExceeded, provesNonemptyIn(gpa, source));
    const taken = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.numeric_oracle_depth, taken.limit);
    try std.testing.expectEqual(@as(u32, 64), taken.limit_value);
    try std.testing.expectEqual(@as(u32, 64), taken.reached);
}

test "a give-up reports the enclosing function and the queried site" {
    const gpa = std.testing.allocator;
    budget_mod.clear();
    const source = try deepSource(gpa, 50);
    defer gpa.free(source);
    try std.testing.expectError(error.AnalysisBudgetExceeded, provesNonemptyIn(gpa, source));
    const taken = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqualStrings("f", taken.function.slice());
    // The `arr[arr.len - 1]` read is on the last line of the source, so
    // a site that points anywhere else is not pointing at the query.
    try std.testing.expect(taken.line > 1);
    try std.testing.expect(taken.column > 1);
    try std.testing.expect(taken.byte > 0);
}

test "an unproven site is still a plain false, with no budget record" {
    // Nothing was proven here and nothing was walked off the end of:
    // the two must not be confused, or every rule that consults the
    // oracle would report an incomplete file.
    budget_mod.clear();
    try std.testing.expect(!try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    return buf[i - 1];
        \\}
        \\
    , "i", "buf"));
    try std.testing.expect(budget_mod.peek() == null);
}

test "a completed query leaves no budget record behind" {
    budget_mod.clear();
    try std.testing.expect(try proveAt(
        \\fn f(i: usize, buf: []const u8) u8 {
        \\    if (i == 0) return 0;
        \\    return buf[i - 1];
        \\}
        \\
    , "i", "buf"));
    try std.testing.expect(budget_mod.peek() == null);
}

// ── verified std single-element append ───────────────────────────
//
// The proof that `C.items` gained one element comes from the declaration the
// compiler resolves, not from the spelling at the call site, so these run
// against the real toolchain sources.  A `try` is a propagating edge; a
// `catch` that continues is the failure edge, where nothing was stored.

/// `provesPositive` on the `X` of an `arr[X - 1]` access, with the type engine
/// attached so declaration-resolved facts apply.
fn provePositiveWithEngine(src: [:0]const u8, arr: []const u8) !bool {
    const gpa = std.testing.allocator;
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-value-range-std-append.zig", src);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    // A fixture that does not parse cannot resolve any declaration, so every
    // query would answer "no" and a negative case would pass for the wrong
    // reason.  Report the syntax error instead of a silent absence.
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const body = firstFnBody(tree) orelse return error.NoFnBody;
    const lbracket = subscriptLBracket(tree, arr) orelse return error.NoSubscript;
    const access = arrayAccessAt(tree, lbracket) orelse return error.NoSubscript;
    const subscript = tree.nodeData(access).node_and_node[1];
    if (tree.nodeTag(subscript) != .sub) return error.NoSubscript;
    return try value_range.provesPositive(
        gpa,
        tree,
        body,
        tree.nodeData(subscript).node_and_node[0],
        lbracket,
        &cache,
    );
}

test "std append: an infallible appendAssumeCapacity proves the last-element read" {
    try std.testing.expect(try provePositiveWithEngine(
        \\const std = @import("std");
        \\fn peek(list: *std.ArrayList(u8)) u8 {
        \\    if (list.items.len == 0) {
        \\        list.appendAssumeCapacity(0);
        \\    }
        \\    return list.items[list.items.len - 1];
        \\}
        \\
    , "items"));
}

test "std append: a fallible append on a try edge proves the last-element read" {
    try std.testing.expect(try provePositiveWithEngine(
        \\const std = @import("std");
        \\fn peek(list: *std.ArrayList(u8), gpa: std.mem.Allocator) !u8 {
        \\    if (list.items.len == 0) {
        \\        try list.append(gpa, 0);
        \\    }
        \\    return list.items[list.items.len - 1];
        \\}
        \\
    , "items"));
}

test "std append: a catch that continues is the failure edge and proves nothing" {
    try std.testing.expect(!try provePositiveWithEngine(
        \\const std = @import("std");
        \\fn peek(list: *std.ArrayList(u8), gpa: std.mem.Allocator) u8 {
        \\    if (list.items.len == 0) {
        \\        list.append(gpa, 0) catch {};
        \\    }
        \\    return list.items[list.items.len - 1];
        \\}
        \\
    , "items"));
}

test "std append: appendSlice may insert nothing, so it proves nothing" {
    try std.testing.expect(!try provePositiveWithEngine(
        \\const std = @import("std");
        \\fn peek(list: *std.ArrayList(u8), other: []const u8) u8 {
        \\    if (list.items.len == 0) {
        \\        list.appendSliceAssumeCapacity(other);
        \\    }
        \\    return list.items[list.items.len - 1];
        \\}
        \\
    , "items"));
}

test "std append: a local method named append proves nothing" {
    try std.testing.expect(!try provePositiveWithEngine(
        \\fn peek(list: *Bag, value: u8) u8 {
        \\    if (list.items.len == 0) {
        \\        list.append(value);
        \\    }
        \\    return list.items[list.items.len - 1];
        \\}
        \\const Bag = struct {
        \\    items: []u8,
        \\    fn append(self: *Bag, value: u8) void {
        \\        _ = self;
        \\        _ = value;
        \\    }
        \\};
        \\
    , "items"));
}

test "std append: shrinking the receiver afterwards drops the proof" {
    try std.testing.expect(!try provePositiveWithEngine(
        \\const std = @import("std");
        \\fn peek(list: *std.ArrayList(u8), mode: u8) u8 {
        \\    if (list.items.len == 0) {
        \\        list.appendAssumeCapacity(0);
        \\    }
        \\    if (mode == 0) {
        \\        list.clearRetainingCapacity();
        \\    }
        \\    return list.items[list.items.len - 1];
        \\}
        \\
    , "items"));
}

test "std append: the receiver field spelling the oracle sees is the one proved" {
    // The `self.states` shape the value-range queries actually meet: the fact
    // is keyed by the receiver's own spelling plus `.items`.
    try std.testing.expect(try provePositiveWithEngine(
        \\const std = @import("std");
        \\const Stack = struct {
        \\    states: std.ArrayList(u8),
        \\    fn peek(self: *Stack) u8 {
        \\        if (self.states.items.len == 0) {
        \\            self.states.appendAssumeCapacity(0);
        \\        }
        \\        return self.states.items[self.states.items.len - 1];
        \\    }
        \\};
        \\
    , "items"));
}

// ── evaluation order of a use inside a larger expression ─────

/// The `occurrence`-th `[` token in the file (0-based).
fn nthLBracket(tree: *const Ast, occurrence: usize) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    var seen: usize = 0;
    var t: Ast.TokenIndex = 1;
    while (t < tags.len) : (t += 1) {
        if (tags[t] != .l_bracket) continue;
        if (seen == occurrence) return t;
        seen += 1;
    }
    return null;
}

/// `provesPositive` on the `X` of an `X - 1` subscript, selected by the
/// position of its `[` rather than by a preceding identifier: an index
/// inside a method receiver (`recv.items[X - 1].method(…)`) has no bare name
/// in front of the bracket.
fn provePositiveForNthSubscript(
    src: [:0]const u8,
    occurrence: usize,
) !bool {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, src, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    const body = firstFnBody(&tree) orelse return error.NoFnBody;
    const lbracket = nthLBracket(&tree, occurrence) orelse return error.NoSubscript;
    const access = arrayAccessAt(&tree, lbracket) orelse return error.NoSubscript;
    const minuend = subscriptMinuend(&tree, tree.nodeData(access).node_and_node[1]) orelse
        return error.NoSubscript;
    return try value_range.provesPositive(gpa, &tree, body, minuend, lbracket, null);
}

test "guard: an early return on zero proves the fall-through index" {
    // `!= 0` establishes only nonzeroness, which is not a positive lower bound
    // on its own; it is one here because `n` is declared `usize`, so no
    // non-negative value but zero is nonzero.
    try std.testing.expect(try provePositiveForLastIndex(
        \\fn f(items: []const u8, n: usize) u8 {
        \\    if (n == 0) return 0;
        \\    return items[n - 1];
        \\}
        \\
    , "items", 0));
}

test "guard: an or-guard on the same scalar proves the later index" {
    // The early-return-on-zero idiom: falling through means the left operand
    // of the `or` was false, so the scalar is nonzero there too.
    try std.testing.expect(try provePositiveForLastIndex(
        \\fn f(tags: []const u8, pt: usize) u8 {
        \\    if (pt == 0 or tags[pt - 1] != 0) return 0;
        \\    return tags[pt - 1];
        \\}
        \\
    , "tags", 1));
}

test "guard: without the guard the index stays unproven" {
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn f(items: []const u8, n: usize) u8 {
        \\    return items[n - 1];
        \\}
        \\
    , "items", 0));
}

test "orelse: a dominating guard still holds inside the left operand" {
    // The payload only runs when the left operand failed, so the subscript
    // there is evaluated before the fallback wipes the state.
    try std.testing.expect(try provePositiveForLastIndex(
        \\fn f(stack: *Stack, items: []const u8) u8 {
        \\    if (stack.depth < 2) return 0;
        \\    const last = items[stack.depth - 1] orelse return 0;
        \\    return last;
        \\}
        \\const Stack = struct { depth: usize };
        \\
    , "items", 0));
}

test "orelse: without the guard the left operand stays unproven" {
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn f(stack: *Stack, items: []const u8) u8 {
        \\    const last = items[stack.depth - 1] orelse return 0;
        \\    return last;
        \\}
        \\const Stack = struct { depth: usize };
        \\
    , "items", 0));
}

test "call receiver: a dominating guard holds inside a method receiver subscript" {
    // `sink` is a pointer local, so the call really can rewrite the frame —
    // but the receiver is read before the callee runs, so its own subscript
    // is evaluated while the guard still holds.
    try std.testing.expect(try provePositiveForNthSubscript(
        \\fn f(stack: *Stack, value: u8) void {
        \\    var sink: *u8 = undefined;
        \\    if (stack.depth < 2) return;
        \\    stack.frames.items[stack.depth - 1].set(sink, value);
        \\}
        \\const Stack = struct { depth: usize, frames: Frames };
        \\const Frames = struct {
        \\    items: []u8,
        \\    fn set(self: *Frames, index: usize, out: *u8, value: u8) void {
        \\        self.items[index] = value;
        \\        out.* = value;
        \\    }
        \\};
        \\
    , 0));
}

test "call receiver: without the guard the receiver subscript stays unproven" {
    try std.testing.expect(!try provePositiveForNthSubscript(
        \\fn f(stack: *Stack, value: u8) void {
        \\    var sink: *u8 = undefined;
        \\    stack.frames.items[stack.depth - 1].set(sink, value);
        \\}
        \\const Stack = struct { depth: usize, frames: Frames };
        \\const Frames = struct {
        \\    items: []u8,
        \\    fn set(self: *Frames, index: usize, out: *u8, value: u8) void {
        \\        self.items[index] = value;
        \\        out.* = value;
        \\    }
        \\};
        \\
    , 0));
}

// ── loop range bounds reach the capture's value ──────────────

fn nthIdentToken(tree: *const Ast, name: []const u8, occurrence: usize) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    var seen: usize = 0;
    var t: Ast.TokenIndex = 1;
    while (t < tags.len) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        if (seen == occurrence) return t;
        seen += 1;
    }
    return null;
}

fn identAt(tree: *const Ast, token: Ast.TokenIndex) ?Ast.Node.Index {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeMainToken(node) == token) return node;
    }
    return null;
}

/// `value_range.boundsAt` on the `occurrence`-th identifier spelled `name`,
/// asked at that identifier's own token: the bounds of the value a
/// conversion is about, at the site of the conversion.
fn boundsOfIdentWithEngine(
    src: [:0]const u8,
    name: []const u8,
    occurrence: usize,
) !value_range.NumericRange {
    const gpa = std.testing.allocator;
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-value-range-for-range.zig", src);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    const body = firstFnBody(tree) orelse return error.NoFnBody;
    const token = nthIdentToken(tree, name, occurrence) orelse return error.NoSubscript;
    const node = identAt(tree, token) orelse return error.NoSubscript;
    return try value_range.boundsAt(gpa, tree, body, node, token, &cache);
}

test "for-range: a narrow range end bounds the loop capture" {
    // The capture is a `usize` whatever the endpoints are declared as, so
    // the endpoint's own type is the only thing that bounds it.  Every value
    // below 65536 is exactly representable in f32.
    const bounds = try boundsOfIdentWithEngine(
        \\fn scale(count: u16) f32 {
        \\    var total: f32 = 0;
        \\    for (0..count) |i| {
        \\        total += @floatFromInt(i);
        \\    }
        \\    return total;
        \\}
        \\
    , "i", 1);
    try std.testing.expect(bounds.exactInF32());
}

test "for-range: a wide range end leaves the capture unbounded" {
    const bounds = try boundsOfIdentWithEngine(
        \\fn scale(count: usize) f32 {
        \\    var total: f32 = 0;
        \\    for (0..count) |i| {
        \\        total += @floatFromInt(i);
        \\    }
        \\    return total;
        \\}
        \\
    , "i", 1);
    try std.testing.expect(!bounds.exactInF32());
}

// ── `!= 0` is not `> 0` without a non-negative domain ─────────
// `-1 != 0`, so a dominating nonzero guard proves a positive lower bound only
// where the value's domain rules out the negative side.  That domain has to be
// recovered from the declaration: a name the walk could not type is not an
// unsigned name, and neither is one whose declaration it never saw.

test "positive: a signed nonzero guard does not prove a positive lower bound" {
    // `offset` reaches this line as -1 on a real path, where `offset - 1` is
    // -2.  The guard says the value is not zero; it says nothing about which
    // side of zero it is on.  A signed index only reaches a subscript through
    // the explicit conversion real code writes, so that is what the fixture
    // spells — the query peels it and asks about `offset - 1` itself.
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn pick(items: []const u8, offset: i32) u8 {
        \\    if (offset == 0) return 0;
        \\    return items[@intCast(offset - 1)];
        \\}
        \\
    , "items", 0));
}

test "positive: an untyped local does not turn a nonzero guard positive" {
    // `n` is `anytype`: the walk has no declaration to type it with, so
    // `!= 0` has to stay `!= 0` whatever integer the caller instantiates
    // with.  The index is spelled as the explicit conversion that shape
    // needs — a signed instantiation does not coerce into a subscript on its
    // own — so the query peels it and asks about `n` itself.
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn pick(items: []const u8, offset: anytype) u8 {
        \\    const n = offset;
        \\    if (n == 0) return 0;
        \\    return items[@intCast(n - 1)];
        \\}
        \\
    , "items", 0));
}

test "positive: a reassigned local keeps its declared unsigned domain" {
    // The assignment drops the recorded minimum — `if (allow) raw else 0` has
    // no lower bound of its own — but the binding is still declared `u32`, so
    // the zero guard is enough again.
    try std.testing.expect(try provePositiveForLastIndex(
        \\fn pick(items: []const u8, raw: u32, allow: bool) u8 {
        \\    var n: u32 = raw;
        \\    n = if (allow) raw else 0;
        \\    if (n == 0) return 0;
        \\    return items[n - 1];
        \\}
        \\
    , "items", 0));
}

test "positive: a sibling block's scalar type does not type this one" {
    // Both arms declare `n`, and only the one in scope at the read may type
    // it.  The read is in the arm whose `n` is signed, so its `!= 0` guard
    // stays `!= 0` whatever the other arm declared.
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn pick(items: []const u8, mode: u8, raw: i32) u8 {
        \\    if (mode == 0) {
        \\        const n: i32 = raw;
        \\        if (n == 0) return 0;
        \\        return items[@intCast(n - 1)];
        \\    } else {
        \\        const n: u32 = @intCast(raw);
        \\        if (n == 0) return 0;
        \\        return items[n - 1];
        \\    }
        \\}
        \\
    , "items", 0));
}

test "positive: a local declared after the read does not type it" {
    // The outer `n` is declared below the read, so it is not the binding the
    // read is written against.  The inner one is signed, so its `!= 0` guard
    // stays `!= 0` even though a same-named unsigned local exists in an
    // enclosing block.
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn pick(items: []const u8, flag: bool, raw: i32) u8 {
        \\    if (flag) {
        \\        const n: i32 = raw;
        \\        if (n == 0) return 0;
        \\        return items[@intCast(n - 1)];
        \\    }
        \\    const n: u32 = @intCast(raw);
        \\    return items[n - 1];
        \\}
        \\
    , "items", 0));
}

test "positive: a counted range end is positive inside its own body" {
    // Reaching the body means the loop ran, and `for (0..n)` only runs its
    // body when `0 < n`.  Nothing else in this function says so: there is no
    // `n != 0` guard, and the only fact about `n` is the minimum the loop
    // leaves behind.  The loop counts in a `usize` whatever the end is
    // declared as — the endpoints are evaluated into a `usize` — so `i`
    // subscripts as it stands, and `n - 1` widens into the subscript.
    try std.testing.expect(try provePositiveForLastIndex(
        \\fn mix_last(items: []const u8, n: u16) u8 {
        \\    var total: u8 = 0;
        \\    for (0..n) |i| {
        \\        total +%= items[i];
        \\        total +%= items[n - 1];
        \\    }
        \\    return total;
        \\}
        \\
    , "items", 1));
}

test "positive: outside any loop the same guard on a signed name is not positive" {
    // Same `!= 0` guard and the same name, but no loop that could have run:
    // `n` is `i32`, so a nonzeroness is all that is left, and it does not say
    // which side of zero the value is on.
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn mix_last(items: []const u8, n: i32) u8 {
        \\    if (n == 0) return 0;
        \\    return items[@intCast(n - 1)];
        \\}
        \\
    , "items", 0));
}

test "positive: a capture starting above zero is positive" {
    // `for (1..n)` starts the capture at 1, so `i - 1` never underflows.
    try std.testing.expect(try provePositiveForLastIndex(
        \\fn shifted(items: []const u8, n: u16) u8 {
        \\    var total: u8 = 0;
        \\    for (1..n) |i| {
        \\        total +%= items[i - 1];
        \\    }
        \\    return total;
        \\}
        \\
    , "items", 0));
}

test "positive: a capture starting at zero is not" {
    // One loop bound lower: `for (0..n)` starts the capture at 0, and `i - 1`
    // is then a real underflow on the first iteration.
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn shifted(items: []const u8, n: u16) u8 {
        \\    var total: u8 = 0;
        \\    for (0..n) |i| {
        \\        total +%= items[i - 1];
        \\    }
        \\    return total;
        \\}
        \\
    , "items", 0));
}

// ── a rebinding pointer invalidates the pointee's facts ───────

test "positive: rebinding the pointer drops the pointee's guard fact" {
    // The key the oracle records for `p.*` is that spelling, but the fact it
    // holds is about the OBJECT `p` points at.  `p = other` makes the same
    // expression read a different object, which may hold 0 — so `p.* - 1`
    // wraps on a real path and the guard's bound is stale by the read.
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn f(first: *usize, other: *usize, items: []const u8) u8 {
        \\    var p = first;
        \\    if (p.* < 10) return 0;
        \\    p = other;
        \\    return items[p.* - 1];
        \\}
        \\
    , "items", 0));
}

test "positive: a pointee guard survives while the pointer is left alone" {
    // The same guard with nothing rebinding `p`: the bound still describes
    // the object the read goes through, so it has to keep standing.
    try std.testing.expect(try provePositiveForLastIndex(
        \\fn f(first: *usize, items: []const u8) u8 {
        \\    const p = first;
        \\    if (p.* < 10) return 0;
        \\    return items[p.* - 1];
        \\}
        \\
    , "items", 0));
}

// ── what a short-circuit's earlier operand records ─────────────
// A proved comparison is recorded twice over: the refinement channel names
// its left operand, and the numeric channel stores one constraint per
// OPERAND.  For the false arm of `j > 5` the first names nothing at all, so
// the second is the only record of what the guard established — and it is
// the one a later `raise(&j)` invalidates.

/// The largest value an integer bound still allows, or null when the answer
/// is not an integer bound.
fn integerMax(range: value_range.NumericRange) ?i128 {
    return switch (range) {
        .integer => |value| value.max,
        else => null,
    };
}

test "numeric: a later operand that can write the guarded scalar keeps its bound out" {
    // Falling through proves `j <= 5`, and that bound describes the state
    // BEFORE `raise(&j)` set `j` to 1000.  The conversion below reads the
    // value the call left, so the bound must not reach it.
    const bounds = try boundsOfIdentWithEngine(
        \\fn f(j: i32, bytes: []const u8) u8 {
        \\    if (j > 5 or raise(&j)) return 0;
        \\    return bytes[@intCast(j) - 1];
        \\}
        \\fn raise(x: *i32) bool {
        \\    x.* = 1000;
        \\    return false;
        \\}
        \\
    , "j", 3);
    // The declared `i32` domain answers here, so this is a real bound rather
    // than a walk that gave up on the way to the site.
    try std.testing.expect(bounds == .integer);
    try std.testing.expect(integerMax(bounds).? > 5);
}

test "numeric: the same guard keeps its bound past an operand that cannot write it" {
    // `probe(j)` takes a copy, so nothing moves and `j <= 5` still describes
    // the state the conversion reads.
    const bounds = try boundsOfIdentWithEngine(
        \\fn f(j: i32, bytes: []const u8) u8 {
        \\    if (j > 5 or probe(j)) return 0;
        \\    return bytes[@intCast(j) - 1];
        \\}
        \\fn probe(x: i32) bool {
        \\    return x < 0;
        \\}
        \\
    , "j", 3);
    try std.testing.expect(bounds == .integer);
    try std.testing.expect(integerMax(bounds).? == 5);
}

// ── a loop rebinds what it assigns ───────────────────────────
// A `switch` arm records its scrutinee's exact value, and `exprMin` reads that
// constant as a live lower bound.  An assignment in the loop replaces the
// value, so the constant and the `n = c.len` snapshot beside it describe a
// state the walk has already left.

test "switch arm: a loop that rebinds the scrutinee drops its constant" {
    // The arm proves `n == 3`; the loop then rebinds `n` to 0 on the very path
    // the read is on, where `n - 1` wraps to `maxInt(usize)`.
    try std.testing.expect(!try provePositiveForLastIndex(
        \\fn f(buf: []const u8) u8 {
        \\    var n = buf.len;
        \\    switch (n) {
        \\        3 => {
        \\            var flag = true;
        \\            while (flag) {
        \\                flag = false;
        \\                n = 0;
        \\            }
        \\            return buf[n - 1];
        \\        },
        \\        else => return 0,
        \\    }
        \\}
        \\
    , "buf", 0));
}

test "switch arm: a loop that rebinds another name keeps the constant" {
    // Same arm, same loop, one line different: the loop assigns `flag` and
    // leaves the scrutinee alone, so `n == 3` still describes the read.
    try std.testing.expect(try provePositiveForLastIndex(
        \\fn f(buf: []const u8) u8 {
        \\    var n = buf.len;
        \\    switch (n) {
        \\        3 => {
        \\            var flag = true;
        \\            while (flag) {
        \\                flag = false;
        \\            }
        \\            return buf[n - 1];
        \\        },
        \\        else => return 0,
        \\    }
        \\}
        \\
    , "buf", 0));
}

test "loop: a rebound length snapshot is not handed back a non-zero" {
    // `n = list.len` is the snapshot, and the loop's `n = 0` destroys it: the
    // guard below proves `list` non-empty, which says nothing about `n` — and
    // `n` really is 0 there, so `n - 1` is the underflow.
    try std.testing.expect(!try proveAt(
        \\fn f(mode: u8, list: []const u8, buf: []const u8) u8 {
        \\    var n = list.len;
        \\    switch (mode) {
        \\        3 => {
        \\            var flag = true;
        \\            while (flag) {
        \\                flag = false;
        \\                n = 0;
        \\            }
        \\            if (list.len > 0) return buf[n - 1];
        \\            return 0;
        \\        },
        \\        else => return 0,
        \\    }
        \\}
        \\
    , "n", "buf"));
}

test "loop: an untouched length snapshot still hands back a non-zero" {
    // The same guard and the same loop with no assignment to `n`: the snapshot
    // still holds, so a non-empty `list` does make `n` non-zero.
    try std.testing.expect(try proveAt(
        \\fn f(mode: u8, list: []const u8, buf: []const u8) u8 {
        \\    var n = list.len;
        \\    switch (mode) {
        \\        3 => {
        \\            var flag = true;
        \\            while (flag) {
        \\                flag = false;
        \\            }
        \\            if (list.len > 0) return buf[n - 1];
        \\            return 0;
        \\        },
        \\        else => return 0,
        \\    }
        \\}
        \\
    , "n", "buf"));
}

// ── what a call-shaped predicate records ─────────────────────
// `std.math.isFinite(x)` true and `std.math.isNan(x)` false each record their
// finiteness under the ARGUMENT they were handed, not under a comparison
// operand.  `intfromfloat_without_clamp` asks exactly that of `boundsAt`, so
// the question below is the rule's own: does the value the conversion sees fit
// the destination integer?  A NaN or an infinity does not.

fn convertsToU64(bounds: value_range.NumericRange) bool {
    return bounds.fitsInteger(64, false);
}

test "finiteness: a later operand that can write the guarded float drops it" {
    // The dominating range guard bounds `x` to [0, 1e18]; `isFinite(x)` supplies
    // the other half of what a `u64` conversion needs — "not NaN" — for the
    // state BEFORE `poison(&x)` runs.  In the then-arm `x` really is NaN, so
    // the conversion is not proved.
    const bounds = try boundsOfIdentWithEngine(
        \\const std = @import("std");
        \\fn f(raw: f64) u64 {
        \\    var x = raw;
        \\    if (x < 0 or x > 1e18) return 0;
        \\    if (std.math.isFinite(x) and poison(&x)) {
        \\        return @intFromFloat(x);
        \\    }
        \\    return 0;
        \\}
        \\fn poison(v: *f64) bool {
        \\    v.* = std.math.nan(f64);
        \\    return true;
        \\}
        \\
    , "x", 5);
    try std.testing.expect(!convertsToU64(bounds));
}

test "finiteness: a plain isFinite guard still proves the conversion" {
    // The same bound and the same predicate with no later operand to rewrite
    // `x`: nothing moves, so the conversion is proved.
    const bounds = try boundsOfIdentWithEngine(
        \\const std = @import("std");
        \\fn f(x: f64) u64 {
        \\    if (x < 0 or x > 1e18) return 0;
        \\    if (std.math.isFinite(x)) {
        \\        return @intFromFloat(x);
        \\    }
        \\    return 0;
        \\}
        \\
    , "x", 4);
    try std.testing.expect(convertsToU64(bounds));
}

test "finiteness: an isNan early return drops its fact past a writing operand" {
    // Proved false, the `or` settles the earlier operand, so `isNan(x)` being
    // false records a "not NaN" fact for the state BEFORE `poison(&x)` runs.
    // The fall-through read sees the NaN that call left.
    const bounds = try boundsOfIdentWithEngine(
        \\const std = @import("std");
        \\fn f(raw: f64) u64 {
        \\    var x = raw;
        \\    if (x < 0 or x > 1e18) return 0;
        \\    if (std.math.isNan(x) or poison(&x)) return 0;
        \\    return @intFromFloat(x);
        \\}
        \\fn poison(v: *f64) bool {
        \\    v.* = std.math.nan(f64);
        \\    return false;
        \\}
        \\
    , "x", 5);
    try std.testing.expect(!convertsToU64(bounds));
}

test "finiteness: an isNan guard keeps its fact past an operand given a copy" {
    // Same early-return shape, but `probe(x)` cannot move `x`, so the recorded
    // "not NaN" still describes the value the conversion reads.
    const bounds = try boundsOfIdentWithEngine(
        \\const std = @import("std");
        \\fn f(x: f64) u64 {
        \\    if (x < 0 or x > 1e18) return 0;
        \\    if (std.math.isNan(x) or probe(x)) return 0;
        \\    return @intFromFloat(x);
        \\}
        \\fn probe(v: f64) bool {
        \\    return v < 0;
        \\}
        \\
    , "x", 5);
    try std.testing.expect(convertsToU64(bounds));
}

const ReturnedSliceMinLenExpectation = struct {
    minimum: u64,
    proven: bool,
};

fn expectReturnedSliceMinLenWithEngine(
    src: [:0]const u8,
    caller: []const u8,
    container: []const u8,
    expectations: []const ReturnedSliceMinLenExpectation,
) !void {
    const gpa = std.testing.allocator;
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-value-range-returned-slice.zig", src);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);

    var body: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .fn_decl) continue;
        const declaration: Ast.Node.Index = @enumFromInt(index);
        const data = tree.nodeData(declaration).node_and_node;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buffer, data[0]) orelse continue;
        const name = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name), caller)) continue;
        if (body != null) return error.AmbiguousCaller;
        body = data[1];
    }
    const caller_body = body orelse return error.NoFnBody;
    const first = tree.firstToken(caller_body);
    const last = tree.lastToken(caller_body);
    var use_token: ?Ast.TokenIndex = null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .array_access) continue;
        const access: Ast.Node.Index = @enumFromInt(index);
        const token = tree.nodeMainToken(access);
        if (token < first or token > last) continue;
        const base = tree.nodeData(access).node_and_node[0];
        if (tree.nodeTag(base) != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(base)), container)) continue;
        if (use_token != null) return error.AmbiguousSubscript;
        use_token = token;
    }
    const token = use_token orelse return error.NoSubscript;
    for (expectations) |expectation| {
        try std.testing.expectEqual(expectation.proven, try value_range.provesMinLen(
            gpa,
            tree,
            caller_body,
            container,
            expectation.minimum,
            token,
            &cache,
        ));
    }
}

const checkedReturnedSliceProducer =
    \\const std = @import("std");
    \\fn bounded(bytes: []const u8, offset: usize, len: usize) error{Invalid}![]const u8 {
    \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
    \\    if (end > bytes.len) return error.Invalid;
    \\    return bytes[offset..][0..len];
    \\}
    \\
;

test "returned slice: checked object slice joins selector lengths at 52" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8, is64: bool) !u8 {
        \\    const header = try bounded(bytes, 0, if (is64) @as(usize, 64) else @as(usize, 52));
        \\    return header[51];
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 52, .proven = true },
        .{ .minimum = 64, .proven = false },
    });
}

test "returned slice: fixed 64 actual proves a 64 byte header" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8) !u8 {
        \\    const header = try bounded(bytes, 0, 64);
        \\    return header[63];
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 64, .proven = true },
        .{ .minimum = 65, .proven = false },
    });
}

test "returned slice: fixed 51 actual does not prove a 62 byte header" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8) !u8 {
        \\    const header = try bounded(bytes, 0, 51);
        \\    return header[61];
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 51, .proven = true },
        .{ .minimum = 62, .proven = false },
    });
}

test "returned slice: early explicit error does not join successful 64" {
    try expectReturnedSliceMinLenWithEngine(
        \\const std = @import("std");
        \\fn bounded(bytes: []const u8, reject: bool) error{Invalid}![]const u8 {
        \\    if (reject) return error.Invalid;
        \\    const end = std.math.add(usize, 0, 64) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[0..][0..64];
        \\}
        \\fn caller(bytes: []const u8, reject: bool) !u8 {
        \\    const header = try bounded(bytes, reject);
        \\    return header[63];
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 64, .proven = true },
        .{ .minimum = 65, .proven = false },
    });
}

test "returned slice: short successful return joins successful 64" {
    try expectReturnedSliceMinLenWithEngine(
        \\const std = @import("std");
        \\fn bounded(bytes: []const u8, short: bool) error{Invalid}![]const u8 {
        \\    if (short) return "";
        \\    const end = std.math.add(usize, 0, 64) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[0..][0..64];
        \\}
        \\fn caller(bytes: []const u8, short: bool) !u8 {
        \\    const header = try bounded(bytes, short);
        \\    return header[63];
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 0, .proven = true },
        .{ .minimum = 64, .proven = false },
    });
}

test "returned slice: catch returning an error keeps successful 64" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8) error{Invalid}!u8 {
        \\    const header = bounded(bytes, 0, 64) catch return error.Invalid;
        \\    return header[63];
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 64, .proven = true },
        .{ .minimum = 65, .proven = false },
    });
}

test "returned slice: catch empty fallback loses successful 64" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8) u8 {
        \\    const header = bounded(bytes, 0, 64) catch "";
        \\    return header[63];
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 64, .proven = false },
    });
}

test "returned slice: mutating the length after a snapshot keeps original 52" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8, is64: bool) !u8 {
        \\    var len = if (is64) @as(usize, 64) else @as(usize, 52);
        \\    const header = try bounded(bytes, 0, len);
        \\    len = 1;
        \\    return header[51] + @as(u8, @intCast(len));
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 52, .proven = true },
        .{ .minimum = 64, .proven = false },
    });
}

test "returned slice: setting the snapshotted selector true cannot claim 64" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8, selected: bool) !u8 {
        \\    var is64 = selected;
        \\    const header = try bounded(bytes, 0, if (is64) @as(usize, 64) else @as(usize, 52));
        \\    is64 = true;
        \\    if (is64) return header[63];
        \\    return 0;
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 52, .proven = true },
        .{ .minimum = 64, .proven = false },
    });
}

test "returned slice: rebinding the header shorter loses original 64" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8) !u8 {
        \\    var header = try bounded(bytes, 0, 64);
        \\    header = header[0..51];
        \\    return header[63];
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 51, .proven = true },
        .{ .minimum = 64, .proven = false },
    });
}

test "returned slice: addressed shrinking helper loses original 64" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8) !u8 {
        \\    var header = try bounded(bytes, 0, 64);
        \\    shrink(&header);
        \\    return header[63];
        \\}
        \\fn shrink(header: *[]const u8) void {
        \\    header.* = header.*[0..51];
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 64, .proven = false },
    });
}

test "returned slice: two calls keep separate 64 and 51 actual contexts" {
    const src = checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8) !u8 {
        \\    const header64 = try bounded(bytes, 0, 64);
        \\    const header51 = try bounded(bytes, 0, 51);
        \\    return header64[63] + header51[50];
        \\}
        \\
    ;
    try expectReturnedSliceMinLenWithEngine(src, "caller", "header64", &.{
        .{ .minimum = 64, .proven = true },
        .{ .minimum = 65, .proven = false },
    });
    try expectReturnedSliceMinLenWithEngine(src, "caller", "header51", &.{
        .{ .minimum = 51, .proven = true },
        .{ .minimum = 62, .proven = false },
    });
}

test "returned slice: stable selector guard recovers its 64 byte snapshot" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8, is64: bool) !u8 {
        \\    const header = try bounded(bytes, 0, if (is64) @as(usize, 64) else @as(usize, 52));
        \\    if (is64) return header[63];
        \\    return 0;
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 64, .proven = true },
        .{ .minimum = 65, .proven = false },
    });
}

test "returned slice: swapped snapshot arms do not prove 64 under the true guard" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8, is64: bool) !u8 {
        \\    const header = try bounded(bytes, 0, if (is64) @as(usize, 52) else @as(usize, 64));
        \\    if (is64) return header[63];
        \\    return 0;
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 52, .proven = true },
        .{ .minimum = 64, .proven = false },
    });
}

test "returned slice: addressed selector mutation loses correlation but keeps 52" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8, selected: bool) !u8 {
        \\    var is64 = selected;
        \\    const header = try bounded(bytes, 0, if (is64) @as(usize, 64) else @as(usize, 52));
        \\    select64(&is64);
        \\    if (is64) return header[63];
        \\    return 0;
        \\}
        \\fn select64(selector: *bool) void {
        \\    selector.* = true;
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 52, .proven = true },
        .{ .minimum = 64, .proven = false },
    });
}

test "returned slice: unrelated addressed effect preserves selector correlation" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8, is64: bool) !u8 {
        \\    const header = try bounded(bytes, 0, if (is64) @as(usize, 64) else @as(usize, 52));
        \\    var counter: usize = 0;
        \\    increment(&counter);
        \\    if (is64) return header[63];
        \\    return @intCast(counter);
        \\}
        \\fn increment(counter: *usize) void {
        \\    counter.* += 1;
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 64, .proven = true },
        .{ .minimum = 65, .proven = false },
    });
}

test "returned slice: read only selector helper preserves snapshot correlation" {
    try expectReturnedSliceMinLenWithEngine(checkedReturnedSliceProducer ++
        \\fn caller(bytes: []const u8, is64: bool) !u8 {
        \\    const header = try bounded(bytes, 0, if (is64) @as(usize, 64) else @as(usize, 52));
        \\    observe(&is64);
        \\    if (is64) return header[63];
        \\    return 0;
        \\}
        \\fn observe(selector: *const bool) void {
        \\    _ = selector.*;
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 64, .proven = true },
        .{ .minimum = 65, .proven = false },
    });
}

test "returned slice: callee selector mutation cannot refine an earlier argument snapshot" {
    try expectReturnedSliceMinLenWithEngine(
        \\const std = @import("std");
        \\var is64: bool = false;
        \\fn bounded(bytes: []const u8, offset: usize, len: usize) error{Invalid}![]const u8 {
        \\    is64 = true;
        \\    const end = std.math.add(usize, offset, len) catch return error.Invalid;
        \\    if (end > bytes.len) return error.Invalid;
        \\    return bytes[offset..][0..len];
        \\}
        \\fn caller(bytes: []const u8) !u8 {
        \\    const header = try bounded(bytes, 0, if (is64) @as(usize, 64) else @as(usize, 52));
        \\    if (is64) return header[63];
        \\    return 0;
        \\}
        \\
    , "caller", "header", &.{
        .{ .minimum = 52, .proven = true },
        .{ .minimum = 64, .proven = false },
    });
}

test "numeric return: a private arithmetic sign extension retains the exact immediate domain" {
    const bounds = try boundsOfIdentWithEngine(
        \\pub fn decode(word: u32) i32 {
        \\    const immediate = immediateI(word);
        \\    return immediate;
        \\}
        \\fn signExtend(comptime bits: u6, value: u32) i32 {
        \\    const shift: u5 = @intCast(32 - bits);
        \\    return @as(i32, @bitCast(value << shift)) >> shift;
        \\}
        \\fn immediateI(word: u32) i32 { return signExtend(12, word >> 20); }
    , "immediate", 1);
    try std.testing.expect(bounds == .integer);
    try std.testing.expectEqual(@as(i128, -2048), bounds.integer.min);
    try std.testing.expectEqual(@as(i128, 2047), bounds.integer.max);
}

test "numeric return: different scalar widths cannot reuse a narrower summary" {
    const bounds = try boundsOfIdentWithEngine(
        \\pub fn decode(word: u32) i32 {
        \\    const narrow = immediate(12, word);
        \\    _ = narrow;
        \\    const wide = immediate(32, word);
        \\    return wide;
        \\}
        \\fn signExtend(comptime bits: u6, value: u32) i32 {
        \\    const shift: u5 = @intCast(32 - bits);
        \\    return @as(i32, @bitCast(value << shift)) >> shift;
        \\}
        \\fn immediate(comptime bits: u6, word: u32) i32 {
        \\    return signExtend(bits, word);
        \\}
    , "wide", 1);
    try std.testing.expect(bounds == .integer);
    try std.testing.expectEqual(@as(i128, std.math.minInt(i32)), bounds.integer.min);
    try std.testing.expectEqual(@as(i128, std.math.maxInt(i32)), bounds.integer.max);
}

test "minlen: skipped loop alias write invalidates initializer length" {
    try std.testing.expect(!try proveMinLenWithEngine(
        \\pub fn f(run:bool) []const u8 { var bytes:[]const u8="abc"; const p=&bytes; while(run){p.*="";break;} return bytes[2..]; }
    , "bytes", 2, "bytes"));
}

test "minlen: skipped loop read preserves initializer length" {
    try std.testing.expect(try proveMinLenWithEngine(
        \\pub fn f(run: bool) []const u8 {
        \\    var bytes: []const u8 = "abc";
        \\    const p = &bytes;
        \\    while (run) { _ = p.*; break; }
        \\    return bytes[2..];
        \\}
    , "bytes", 2, "bytes"));
}

test "minlen: skipped loop disjoint alias write preserves initializer length" {
    try std.testing.expect(try proveMinLenWithEngine(
        \\pub fn f(run: bool) []const u8 {
        \\    var bytes: []const u8 = "abc";
        \\    _ = &bytes;
        \\    var other: []const u8 = "def";
        \\    const p = &other;
        \\    while (run) { p.* = ""; break; }
        \\    return bytes[2..];
        \\}
    , "bytes", 2, "bytes"));
}

test "minlen: skipped loop unknown alias write invalidates initializer length" {
    try std.testing.expect(!try proveMinLenWithEngine(
        \\pub fn f(run: bool, choose: bool) []const u8 {
        \\    var bytes: []const u8 = "abc";
        \\    var other: []const u8 = "def";
        \\    const p = if (choose) &bytes else &other;
        \\    while (run) { p.* = ""; break; }
        \\    return bytes[2..];
        \\}
    , "bytes", 2, "bytes"));
}

test "minlen: skipped loop alias write retires dependent length equality" {
    try std.testing.expect(!try proveMinLenWithEngine(
        \\pub fn f(run: bool) []const u8 {
        \\    var bytes: []const u8 = "abc";
        \\    const n = bytes.len;
        \\    const p = &bytes;
        \\    const q = p;
        \\    while (run) { q.* = ""; break; }
        \\    if (n >= 2) return bytes[2..];
        \\    return "";
        \\}
    , "bytes", 2, "bytes"));
}

test "minlen: skipped loop computed pointer write invalidates initializer length" {
    try std.testing.expect(!try proveMinLenWithEngine(
        \\pub fn f(run: bool, choose: bool) []const u8 {
        \\    var bytes: []const u8 = "abc";
        \\    var other: []const u8 = "def";
        \\    while (run) { (if (choose) &bytes else &other).* = ""; break; }
        \\    return bytes[2..];
        \\}
    , "bytes", 2, "bytes"));
}

test "minlen: skipped loop disjoint pointer field store preserves initializer length" {
    try std.testing.expect(try proveMinLenWithEngine(
        \\pub fn f(run: bool) []const u8 {
        \\    var holder: struct { bytes: []const u8, count: usize } = .{ .bytes = "abc", .count = 1 };
        \\    holder.bytes = "abc";
        \\    const p = &holder;
        \\    while (run) { p.count = 0; break; }
        \\    return holder.bytes[2..];
        \\}
    , "holder.bytes", 2, "bytes"));
}

test "returned slice selector rejects an escaped flag changed through a global pointer" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/slice_from_fixed_offset_without_len_check.zig");
    try testing.expectFiresTyped(rule.check, "slice-from-fixed-offset-without-len-check",
        \\var saved: *bool = undefined;
        \\var backing: [64]u8 = @splat(0);
        \\fn cut(n: usize) []const u8 { saved.* = true; return backing[0..n]; }
        \\pub fn caller(initial: bool) []const u8 {
        \\    var flag = initial;
        \\    saved = &flag;
        \\    const header = cut(if (flag) @as(usize, 64) else @as(usize, 52));
        \\    if (flag) return header[63..];
        \\    return header;
        \\}
    );
    try testing.expectNoFireTyped(rule.check,
        \\var saved: *bool = undefined;
        \\var backing: [64]u8 = @splat(0);
        \\fn observe() void { _ = saved.*; }
        \\fn cut(n: usize) []const u8 { observe(); return backing[0..n]; }
        \\pub fn caller(initial: bool) []const u8 {
        \\    var flag = initial;
        \\    saved = &flag;
        \\    const header = cut(if (flag) @as(usize, 64) else @as(usize, 52));
        \\    if (flag) return header[63..];
        \\    return header;
        \\}
    );
}

test "successful scalar contract rejects a caller value reset through an escaped global pointer" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/index_minus_one_without_zero_guard.zig");
    try testing.expectFiresTyped(rule.check, "index-minus-one-without-zero-guard",
        \\var saved: *usize = undefined;
        \\fn reset() void { saved.* = 0; }
        \\fn positive(value: usize) !void { if (value == 0) return error.Zero; reset(); }
        \\pub fn caller(bytes: []const u8, initial: usize) !u8 {
        \\    var n = initial;
        \\    saved = &n;
        \\    try positive(n);
        \\    return bytes[n - 1];
        \\}
    );
    try testing.expectNoFireTyped(rule.check,
        \\var saved: *usize = undefined;
        \\fn observe() void { _ = saved.*; }
        \\fn positive(value: usize) !void { if (value == 0) return error.Zero; observe(); }
        \\pub fn caller(bytes: []const u8, initial: usize) !u8 {
        \\    var n = initial;
        \\    saved = &n;
        \\    try positive(n);
        \\    return bytes[n - 1];
        \\}
    );
}

test "returned slice child drops a length local reset through an escaped global pointer" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/slice_from_fixed_offset_without_len_check.zig");
    try testing.expectFiresTyped(rule.check, "slice-from-fixed-offset-without-len-check",
        \\var saved: *usize = undefined;
        \\var backing: [64]u8 = @splat(0);
        \\fn reset() void { saved.* = 0; }
        \\fn cut(n: usize) []const u8 {
        \\    var len = n;
        \\    saved = &len;
        \\    reset();
        \\    return backing[0..len];
        \\}
        \\pub fn caller() []const u8 { const header = cut(64); return header[63..]; }
    );
    try testing.expectNoFireTyped(rule.check,
        \\var saved: *usize = undefined;
        \\var backing: [64]u8 = @splat(0);
        \\fn observe() void { _ = saved.*; }
        \\fn cut(n: usize) []const u8 {
        \\    var len = n;
        \\    saved = &len;
        \\    observe();
        \\    return backing[0..len];
        \\}
        \\pub fn caller() []const u8 { const header = cut(64); return header[63..]; }
    );
}

test "float exactness: captured format masks use each closed instance" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/f32_narrowing_int_to_float.zig");
    try testing.expectNoFireTyped(rule.check,
        \\fn Format(comptime Float: type, comptime mask: u32) type {
        \\    return struct {
        \\        const payload_mask: u32 = mask;
        \\        fn convert(bits: u32) Float { return @floatFromInt(bits & payload_mask); }
        \\    };
        \\}
        \\pub fn small(bits: u32) f32 { return Format(f32, 0x3fffff).convert(bits); }
        \\pub fn wide(bits: u32) f64 { return Format(f64, 0x1ffffff).convert(bits); }
    );
    try testing.expectFiresTyped(rule.check, "f32-narrowing-int-to-float",
        \\fn Format(comptime Float: type, comptime mask: u32) type {
        \\    return struct {
        \\        const payload_mask: u32 = mask;
        \\        fn convert(bits: u32) Float { return @floatFromInt(bits & payload_mask); }
        \\    };
        \\}
        \\pub fn small(bits: u32) f32 { return Format(f32, 0x1ffffff).convert(bits); }
        \\pub fn wide(bits: u32) f64 { return Format(f64, 0x3fffff).convert(bits); }
    );
}

test "float exactness: instantiated signed constants retain their own values" {
    const testing = @import("../testing.zig");
    const rule = @import("../rules/misc/f32_narrowing_int_to_float.zig");
    try testing.expectNoFireTyped(rule.check,
        \\fn convert(comptime value: i32) f32 { return @floatFromInt(value); }
        \\pub fn small() f32 { return convert(-16777216); }
    );
    try testing.expectFiresTyped(rule.check, "f32-narrowing-int-to-float",
        \\fn convert(comptime value: i32) f32 { return @floatFromInt(value); }
        \\pub fn small() f32 { return convert(-16777216); }
        \\pub fn rounded() f32 { return convert(-16777217); }
    );
}

test "Ocean index facts: short-circuit rejection proves unsigned positivity" {
    try std.testing.expect(try provePositiveWithEngine(
        \\pub fn previous(items: []const u8, raw: usize) ?u8 {
        \\    if (raw == 0 or raw > items.len) return null;
        \\    return items[raw - 1];
        \\}
    , "items"));
}

test "Ocean index facts: upper-only rejection does not prove positivity" {
    try std.testing.expect(!try provePositiveWithEngine(
        \\pub fn previous(items: []const u8, raw: usize) ?u8 {
        \\    if (raw > items.len) return null;
        \\    return items[raw - 1];
        \\}
    , "items"));
}

test "Ocean index facts: one-based induction retains its own floor" {
    const bound = try boundsOfIdentWithEngine(
        \\pub fn sumThree(items: [3]u8) u8 {
        \\    var id: usize = 1;
        \\    var sum: u8 = 0;
        \\    while (id <= 3) : (id += 1) sum +%= items[id - 1];
        \\    return sum;
        \\}
    , "id", 3);
    try std.testing.expect(bound == .integer);
    try std.testing.expectEqual(@as(i128, 1), bound.integer.min);
    try std.testing.expectEqual(@as(i128, 3), bound.integer.max);
}

test "Ocean index facts: zero-based induction retains zero" {
    const bound = try boundsOfIdentWithEngine(
        \\pub fn sumThree(items: [3]u8) u8 {
        \\    var id: usize = 0;
        \\    var sum: u8 = 0;
        \\    while (id <= 3) : (id += 1) sum +%= items[id - 1];
        \\    return sum;
        \\}
    , "id", 3);
    try std.testing.expect(bound == .integer);
    try std.testing.expectEqual(@as(i128, 0), bound.integer.min);
}

test "Ocean index facts: checked addition publishes a numeric floor" {
    const bound = try boundsOfIdentWithEngine(
        \\pub fn next(input: usize) usize {
        \\    var id = input;
        \\    id += 1;
        \\    return id;
        \\}
    , "id", 2);
    try std.testing.expect(bound == .integer);
    try std.testing.expectEqual(@as(i128, 1), bound.integer.min);
}

test "Ocean index facts: wrapping addition cannot publish a positive floor" {
    const bound = try boundsOfIdentWithEngine(
        \\pub fn next(input: usize) usize {
        \\    var id = input;
        \\    id +%= 1;
        \\    return id;
        \\}
    , "id", 2);
    try std.testing.expect(bound == .integer);
    try std.testing.expectEqual(@as(i128, 0), bound.integer.min);
}

test "Ocean index facts: returned nonempty array header supplies its length floor" {
    const bound = try boundsOfIdentWithEngine(
        \\pub fn lastLength() usize {
        \\    const entries = nonEmpty();
        \\    const length = entries.len;
        \\    return length;
        \\}
        \\fn nonEmpty() []const u8 { return &.{ 7, 9 }; }
    , "length", 1);
    try std.testing.expectEqual(value_range.NumericRange.constant(2), bound);
}

test "Ocean index facts: returned empty array header retains a zero floor" {
    const bound = try boundsOfIdentWithEngine(
        \\pub fn lastLength() usize {
        \\    const entries = empty();
        \\    const length = entries.len;
        \\    return length;
        \\}
        \\fn empty() []const u8 { return &.{}; }
    , "length", 1);
    try std.testing.expectEqual(value_range.NumericRange.constant(0), bound);
}

test "Ocean index facts: successful method emitter exports the append floor" {
    const bound = try boundsOfIdentWithEngine(
        \\const std = @import("std");
        \\pub fn set(trace: *Trace, allocator: std.mem.Allocator) !usize {
        \\    const node = try trace.emit(allocator);
        \\    return node;
        \\}
        \\const Trace = struct {
        \\    nodes: std.ArrayList(u8),
        \\    fn emit(self: *Trace, allocator: std.mem.Allocator) !usize {
        \\        try self.nodes.append(allocator, 7);
        \\        return @intCast(self.nodes.items.len);
        \\    }
        \\};
    , "node", 1);
    try std.testing.expect(bound == .integer);
    try std.testing.expectEqual(@as(i128, 1), bound.integer.min);
}

test "Ocean index facts: method emitter without append exports no positive floor" {
    const bound = try boundsOfIdentWithEngine(
        \\const std = @import("std");
        \\pub fn set(trace: *Trace) !usize {
        \\    const node = try trace.emit();
        \\    return node;
        \\}
        \\const Trace = struct {
        \\    nodes: std.ArrayList(u8),
        \\    fn emit(self: *Trace) !usize { return @intCast(self.nodes.items.len); }
        \\};
    , "node", 1);
    try std.testing.expect(bound == .integer);
    try std.testing.expectEqual(@as(i128, 0), bound.integer.min);
}

test "Ocean index facts: zero-admitting ceiling does not erase a one-based floor" {
    const bound = try boundsOfIdentWithEngine(
        \\pub fn sumValues(items: []const u8, count: usize) u8 {
        \\    var id: usize = 1;
        \\    var sum: u8 = 0;
        \\    while (id <= count) : (id += 1) sum +%= items[id - 1];
        \\    return sum;
        \\}
    , "id", 3);
    try std.testing.expect(bound == .integer);
    try std.testing.expectEqual(@as(i128, 1), bound.integer.min);
}

test "Ocean index facts: zero-admitting ceiling does not exclude a zero initializer" {
    const bound = try boundsOfIdentWithEngine(
        \\pub fn sumValues(items: []const u8, count: usize) u8 {
        \\    var id: usize = 0;
        \\    var sum: u8 = 0;
        \\    while (id <= count) : (id += 1) sum +%= items[id - 1];
        \\    return sum;
        \\}
    , "id", 3);
    try std.testing.expect(bound == .integer);
    try std.testing.expectEqual(@as(i128, 0), bound.integer.min);
}
