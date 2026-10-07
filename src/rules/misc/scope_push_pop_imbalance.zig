//! Detects parser functions that push a scope (pushScope, enterScope, etc.)
//! without a matching `defer pop` — early returns leave the scope stack
//! unbalanced.  Real-world shape: oven-sh/bun#31239 / #31340 / #31231.
//!
//! Detection (Tier 1 token walk, per-fn body):
//!   1. Find the FIRST `.method(` where method matches isScopePushMethodName.
//!   2. Check for a `defer` at brace-depth 0 whose body contains a call
//!      matching isScopePopMethodName.  If present → skip (defer handles it).
//!   3. Check for at least one `return` anywhere in the body (multiple
//!      exit paths).  If none → single exit path, skip.
//!   4. Suppress if the fn name contains "pop", "exit", "cleanup", "deinit".
//!   5. Otherwise fire at the push call token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const method_names = @import("../../model/method_names.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const skipFnDecl = tokens.skipFnDecl;
const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "scope-push-pop-imbalance";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .scope_push_pop_imbalance)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    _: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    // Suppress if the fn itself is a cleanup/pop fn.
    if (proto.name_token) |nt| {
        const fn_name = tree.tokenSlice(nt);
        if (isSuppressedFnName(fn_name)) return;
    }

    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Step 1: find the first push call in this fn body (depth-0, skip nested fns).
    const push_tok = findFirstPushCall(tree, first, last) orelse return;

    // Step 2: check for a defer that contains a pop call.
    if (hasDeferPop(tags, tree, first, last)) return;

    // Step 3: check for at least one `return` in the body (multiple exit paths).
    if (!hasReturn(tags, first, last)) return;

    try report(gpa, problems, tree, push_tok);
}

/// Find the first `.method(` sequence where method matches isScopePushMethodName,
/// skipping over nested fn bodies.
fn findFirstPushCall(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?Ast.TokenIndex {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Pattern: period + identifier(pushMethod) + l_paren
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        const method = tree.tokenSlice(t + 1);
        if (method_names.isScopePushMethodName(method)) return t + 1;
    }
    return null;
}

/// Returns true if there is a `defer` statement at brace-depth 0 whose
/// body contains a `.method(` call matching isScopePopMethodName.
fn hasDeferPop(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    var brace_depth: u32 = 0;
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_brace => brace_depth += 1,
            .r_brace => if (brace_depth > 0) {
                brace_depth -= 1;
            },
            .keyword_defer => {
                if (brace_depth != 1) continue; // only depth-0 (inside fn body braces)
                // Find the end of the defer statement.
                const defer_end = tokens.skipDeferStmt(tags, t, last) orelse continue;
                // Check if any token in [t+1, defer_end] is a pop method call.
                if (hasPopsCall(tags, tree, t + 1, defer_end)) return true;
                t = defer_end;
            },
            .keyword_fn => {
                t = skipNestedFn(tags, t, last);
            },
            else => {},
        }
    }
    return false;
}

/// Returns true if `[start, end]` contains `.method(` where method is a pop name.
fn hasPopsCall(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    if (start > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        const method = tree.tokenSlice(t + 1);
        if (method_names.isScopePopMethodName(method)) return true;
    }
    return false;
}

/// Returns true if there is any `return` keyword in `[first, last]`,
/// skipping over nested fn bodies.
fn hasReturn(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] == .keyword_return) return true;
    }
    return false;
}

/// True if the fn is itself a pop/cleanup fn (suppressed).
fn isSuppressedFnName(name: []const u8) bool {
    return std.mem.indexOf(u8, name, "pop") != null or
        std.mem.indexOf(u8, name, "exit") != null or
        std.mem.indexOf(u8, name, "cleanup") != null or
        std.mem.indexOf(u8, name, "deinit") != null;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    push_tok: Ast.TokenIndex,
) !void {
    const msg = try gpa.dupe(u8, "scope push without matching `defer pop` — early returns will leave the scope stack unbalanced; wrap the pop in `defer`");
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, push_tok),
        .end = try Pos.fromTokenEnd(tree, push_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "scope-push-pop-imbalance: push then return then pop fires" {
    try testing.expectFires(check, R,
        \\const Parser = struct {
        \\    pub fn parseBlock(p: *Parser) !void {
        \\        try p.pushScope(.block);
        \\        const ok = true;
        \\        if (!ok) return error.Fail;
        \\        p.popScope();
        \\    }
        \\};
        \\
    );
}

test "scope-push-pop-imbalance: push then defer pop then return doesn't fire" {
    try testing.expectNoFire(check,
        \\const Parser = struct {
        \\    pub fn parseBlock(p: *Parser) !void {
        \\        try p.pushScope(.block);
        \\        defer p.popScope();
        \\        const ok = true;
        \\        if (!ok) return error.Fail;
        \\    }
        \\};
        \\
    );
}

test "scope-push-pop-imbalance: push at end of fn with no returns doesn't fire" {
    try testing.expectNoFire(check,
        \\const Parser = struct {
        \\    pub fn enter(p: *Parser) void {
        \\        p.pushScope(.block);
        \\    }
        \\};
        \\
    );
}

test "scope-push-pop-imbalance: function named cleanupScope is suppressed" {
    try testing.expectNoFire(check,
        \\const Parser = struct {
        \\    pub fn cleanupScope(p: *Parser) void {
        \\        if (p.depth > 0) return;
        \\        p.pushScope(.sentinel);
        \\    }
        \\};
        \\
    );
}
