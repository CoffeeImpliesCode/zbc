//! Detects `?*?T` — a pointer-to-optional type.  In FFI/NAPI code the
//! intended type for a nullable out-parameter is `?*T` (nullable pointer to
//! T) or `*?T` (non-null pointer that writes back an optional); the
//! doubly-optional form `?*?T` means "nullable pointer to optional T" and is
//! almost always a copy-paste error where one `?` was duplicated.
//!
//! Real-world instance:
//!   - oven-sh/bun#13955 (napi_open_escapable_handle_scope): the out-parameter
//!     was typed `?*?napi_escapable_handle_scope` instead of
//!     `?*napi_escapable_handle_scope`; writing through the pointer wrote the
//!     inner optional's discriminant byte, leaving the value uninitialised
//!     and corrupting the caller's stack.
//!     Fix: removed the inner `?`, making it `?*napi_escapable_handle_scope`.
//!
//! Detection (Tier 1, flat token walk):
//!   Pattern: `question_mark asterisk question_mark identifier` — 4 tokens.
//!   Fire at the first `?` of the `?*?T` sequence.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "double-optional-ptr";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .double_optional_ptr)) return;

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    // Map identifier nodes by main token so the inner `T` of `?*?T` can be
    // resolved to its denoted type.  Empty/unused without the type engine.
    var ident_nodes: std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index) = .empty;
    defer ident_nodes.deinit(gpa);
    {
        var ni: u32 = 0;
        while (ni < tree.nodes.len) : (ni += 1) {
            const node: Ast.Node.Index = @enumFromInt(ni);
            if (tree.nodeTag(node) == .identifier) {
                try ident_nodes.put(gpa, tree.nodeMainToken(node), node);
            }
        }
    }

    var t: Ast.TokenIndex = 0;
    while (t + 3 <= last_tok) : (t += 1) {
        // Pattern: ? * ? identifier
        if (tags[t] != .question_mark) continue;
        if (tags[t + 1] != .asterisk) continue;
        if (tags[t + 2] != .question_mark) continue;
        if (tags[t + 3] != .identifier) continue;

        // Suppress `field: ?*?T = null` — a struct field with an explicit
        // default is always intentional: the outer `?` is the "no-storage"
        // sentinel and the inner `?T` is the "not-yet-populated" sentinel.
        // Scan forward past any qualified-name tokens (`.identifier`) to
        // find `=` (struct default) before `,` / `;` / `)` (end of param).
        {
            var s = t + 3;
            const has_default = while (s <= @min(t + 12, last_tok)) : (s += 1) {
                switch (tags[s]) {
                    .equal => break true,
                    .comma, .semicolon, .r_paren, .r_brace => break false,
                    else => {},
                }
            } else false;
            if (has_default) continue;
        }

        // SEMANTIC: suppress when the inner `T` denotes a pointer/optional type.
        // `?*?T` with pointer-like `T` is a valid "nullable pointer to optional
        // pointer" out-parameter (e.g. Win32 `?*?BSTR`, `BSTR = *u16`), not the
        // duplicated-`?`-on-a-value-type bug.  No-op without the type engine.
        if (ident_nodes.get(t + 3)) |t_node| {
            if (cache.typeRefIsPointerLike(t_node)) |ptrlike| {
                if (ptrlike) continue;
            }
        }

        try report(gpa, problems, tree, t);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    question_tok: Ast.TokenIndex,
) !void {
    const type_name = tree.tokenSlice(question_tok + 3);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`?*?{s}` — doubly-optional pointer type; for a nullable out-parameter use `?*{s}`, for a non-null pointer that writes an optional use `*?{s}`; `?*?T` is almost always a copy-paste error",
        .{ type_name, type_name, type_name },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, question_tok),
        .end = Pos.fromTokenEnd(tree, question_tok + 3),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "double-optional-ptr: fires on ?*?T parameter" {
    try testing.expectFires(check, R,
        \\extern fn napi_open_escapable_handle_scope(
        \\    env: napi_env,
        \\    result: ?*?napi_escapable_handle_scope,
        \\) napi_status;
        \\
    );
}

test "double-optional-ptr: ?*T does not fire" {
    try testing.expectNoFire(check,
        \\extern fn napi_open_handle_scope(
        \\    env: napi_env,
        \\    result: ?*napi_handle_scope,
        \\) napi_status;
        \\
    );
}

test "double-optional-ptr: *?T does not fire" {
    try testing.expectNoFire(check,
        \\fn writeOptional(out: *?u32, value: u32) void {
        \\    out.* = value;
        \\}
        \\
    );
}

test "double-optional-ptr: plain *T does not fire" {
    try testing.expectNoFire(check,
        \\fn readValue(ptr: *u32) u32 {
        \\    return ptr.*;
        \\}
        \\
    );
}

test "double-optional-ptr: struct field with null default suppressed" {
    try testing.expectNoFire(check,
        \\const LintContext = struct {
        \\    checker_storage: ?*?Checker = null,
        \\};
        \\
    );
}

test "double-optional-ptr: struct field with qualified type + null default suppressed" {
    try testing.expectNoFire(check,
        \\const Ctx = struct {
        \\    tag_csr_out: ?*?js_buffer.TagNodeCsrResult = null,
        \\};
        \\
    );
}

test "double-optional-ptr: function param without default still fires" {
    try testing.expectFires(check, R,
        \\extern fn napi_fn(env: napi_env, result: ?*?SomeType) napi_status;
        \\
    );
}
