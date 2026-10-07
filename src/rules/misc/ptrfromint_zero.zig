//! Detects `@ptrFromInt(0)` — creating a non-nullable pointer from the
//! null address.
//!
//! In Zig, non-nullable pointer types (`*T`, `[*]T`, `*const T`, etc.)
//! must never hold the value 0.  `@ptrFromInt(0)` manufactures a pointer
//! to address 0, which is undefined behaviour on every major platform —
//! dereferencing it traps in Debug/ReleaseSafe and produces silent memory
//! corruption in ReleaseFast.
//!
//! If you need a sentinel "no pointer" value, use an optional: `?*T` with
//! `null`.  If you need an untyped zero-address for pointer arithmetic
//! (e.g., to compute an offset), use `@as(usize, 0)` and stay in integer
//! space until you have a valid base address.
//!
//! Real-world shape: common when porting C code that passes NULL as a
//! sentinel or placeholder; also seen in unsafe FFI bridges that try to
//! represent an "empty" struct pointer.
//!
//! Detection (Tier 1, token walk):
//!   4-token pattern: `builtin("@ptrFromInt") l_paren number_literal("0") r_paren`
//!   Fire at the `@ptrFromInt` builtin token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "ptrfromint-zero";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .ptrfromint_zero)) return;
    _ = cache;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var t: Ast.TokenIndex = 0;
    while (t + 3 <= last_tok) : (t += 1) {
        if (tags[t] != .builtin) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "@ptrFromInt")) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (tags[t + 2] != .number_literal) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 2), "0")) continue;
        if (tags[t + 3] != .r_paren) continue;

        // Suppress when the target pointer type is `allowzero` (e.g.
        // `@as(*allowzero u0, @ptrFromInt(0))`, a C-varargs null sentinel).
        // `allowzero` pointers may legally hold address 0, so the rule's
        // premise (a non-nullable pointer must never be 0) does not apply.
        if (targetIsAllowzero(tags, t)) continue;

        try report(gpa, problems, tree, t);
    }
}

/// True iff an `allowzero` qualifier appears in the pointer-type context
/// enclosing this `@ptrFromInt(0)` — scanning backward to the nearest
/// statement boundary (`;` / `{` / `}`).  Covers the `@as(*allowzero T, …)`
/// cast form and the `var p: *allowzero T = …` declaration form.
fn targetIsAllowzero(tags: []const std.zig.Token.Tag, t: std.zig.Ast.TokenIndex) bool {
    var k = t;
    var steps: u32 = 0;
    while (k > 0 and steps < 24) : (steps += 1) {
        k -= 1;
        switch (tags[k]) {
            .keyword_allowzero => return true,
            .semicolon, .l_brace, .r_brace => return false,
            else => {},
        }
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    builtin_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`@ptrFromInt(0)` creates a null pointer to a non-nullable type — dereferencing it is undefined behaviour on every platform (trap in Debug/Safe, silent corruption in ReleaseFast); use `?*T` with `null` for a sentinel, or stay in `usize` for offset arithmetic",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, builtin_tok),
        .end = try Pos.fromTokenEnd(tree, builtin_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "ptrfromint-zero: bare zero fires" {
    try testing.expectFires(check, R,
        \\fn nullPtr() *u8 {
        \\    return @ptrFromInt(0);
        \\}
        \\
    );
}

test "ptrfromint-zero: non-zero does not fire" {
    try testing.expectNoFire(check,
        \\fn mmioPtr(addr: usize) *volatile u32 {
        \\    return @ptrFromInt(addr);
        \\}
        \\
    );
}

test "ptrfromint-zero: non-zero literal does not fire" {
    try testing.expectNoFire(check,
        \\fn fixedAddr() *u32 {
        \\    return @ptrFromInt(0x1000_0000);
        \\}
        \\
    );
}

test "ptrfromint-zero: allowzero cast target does not fire" {
    try testing.expectNoFire(check,
        \\fn nullSentinel() *allowzero u0 {
        \\    return @as(*allowzero u0, @ptrFromInt(0));
        \\}
        \\
    );
}

test "ptrfromint-zero: allowzero var-decl target does not fire" {
    try testing.expectNoFire(check,
        \\fn nullSentinel() void {
        \\    const p: *allowzero u8 = @ptrFromInt(0);
        \\    _ = p;
        \\}
        \\
    );
}

test "ptrfromint-zero: non-allowzero @as still fires" {
    try testing.expectFires(check, R,
        \\fn bad() *u8 {
        \\    return @as(*u8, @ptrFromInt(0));
        \\}
        \\
    );
}
