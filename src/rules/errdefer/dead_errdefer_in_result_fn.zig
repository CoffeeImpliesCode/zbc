//! oven-sh/bun#27706 detector — `errdefer` inside a fn whose return type
//! is a parameterized tagged union (`Result(T)`, `Maybe(T)`, …),
//! NOT an error union (`!T`).  Zig's `errdefer` only fires on a
//! Zig error return, but `return .{ .err = e }` is a normal
//! return — so the errdefer is dead code and any cleanup it was
//! meant to perform leaks.
//!
//! Detection (pure token scan per fn):
//!   1. Classify the return type: it must be `<?>* <ident> ( … )`
//!      with NO `!` token anywhere in the return type's range
//!      (which would make it an error union).
//!   2. Walk the fn body for any `keyword_errdefer` token at any
//!      nesting depth — fire one diagnostic per token.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");
const fnProto = tokens.fnProto;
const bodyOf = tokens.bodyOf;
const skipFnDecl = tokens.skipFnDecl;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

/// Returns `SourceTooWide` if the source, token count, or node count exceeds the AST position domain.
pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .dead_errdefer_in_result_fn)) return;
    _ = cache;

    if (tree.source.len >= std.math.maxInt(u32)) return error.SourceTooWide;
    const tok_count = std.math.cast(u32, tree.tokens.len) orelse return error.SourceTooWide;
    const node_count = std.math.cast(u32, tree.nodes.len) orelse return error.SourceTooWide;
    const last_tok: Ast.TokenIndex = tok_count -| 1;

    var node_idx: u32 = 1;
    while (node_idx < node_count) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const fp = fnProto(tree, &buf, node) orelse continue;
        const rt = fp.ast.return_type.unwrap() orelse continue;
        // Reject error-union returns by checking for `!` between
        // the params' close `)` and the return type's first token.
        // The FnProto.return_type field points PAST the `!` (it's
        // the payload type), so walking the type node's own tokens
        // misses the marker.
        if (fnReturnIsErrorUnion(tree, fp, rt, last_tok)) continue;
        if (!returnTypeIsParameterizedTaggedUnion(tree, rt)) continue;
        const body = bodyOf(tree, node) orelse continue;
        try walkBodyForErrdefer(gpa, tree, body, problems);
    }
}

/// True iff a `!` token appears at top level between the params'
/// close paren and the return type's first token.  Walks forward
/// from the matching `)` of `fp.ast.lparen` to `firstToken(rt) - 1`,
/// tracking paren depth so a `!` inside a callconv arg (e.g.
/// `callconv(.{ .foo = X!Y })`) doesn't falsely match.
fn fnReturnIsErrorUnion(
    tree: *const Ast,
    fp: Ast.full.FnProto,
    type_node: Ast.Node.Index,
    max_t: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    // Find the params' close paren by walking forward from lparen.
    var depth: u32 = 1;
    var t: Ast.TokenIndex = fp.lparen + 1;
    while (t <= max_t and depth > 0) : (t += 1) {
        switch (tags[t]) {
            .l_paren => depth += 1,
            .r_paren => depth -= 1,
            else => {},
        }
    }
    if (depth != 0) return false;
    // `t` is now one past the params' `)`.  Walk forward until we
    // reach the return type's firstToken, looking for a top-level
    // `!`.
    const rt_first = tree.firstToken(type_node);
    var d: u32 = 0;
    while (t < rt_first) : (t += 1) {
        switch (tags[t]) {
            .l_paren => d += 1,
            .r_paren => if (d > 0) {
                d -= 1;
            },
            .bang => if (d == 0) return true,
            else => {},
        }
    }
    return false;
}

/// True iff the return type is shaped `<?>* <ident> ( … )` with no
/// `!` (error-union marker) anywhere in the type's tokens.
fn returnTypeIsParameterizedTaggedUnion(tree: *const Ast, type_node: Ast.Node.Index) bool {
    // Defensive: also reject error-union nodes directly via their
    // AST tag (some parser shapes may surface them at this point).
    if (tree.nodeTag(type_node) == .error_union) return false;

    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(type_node);
    const last = tree.lastToken(type_node);

    // Defensive: also reject any explicit `bang` in the type's
    // token range (covers parser corner cases where the
    // error_union may be nested differently).
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] == .bang) return false;
    }

    // Strip leading `?` / `const` / pointer prefixes.  We accept
    // `Result(T)` and `?Result(T)` shapes — the latter still has
    // a tagged-union pointee whose `.err` variant is a normal
    // return, so errdefer is still dead.
    t = first;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .keyword_const => continue,
            .l_bracket, .asterisk => return false,
            .identifier => break,
            else => return false,
        }
    }
    if (t > last) return false;
    if (tags[t] != .identifier) return false;
    // Skip past `<ident>.<ident>...` chains (`bun.css.Result`).
    while (t < last and tags[t + 1] == .period) {
        t += 2;
        if (t > last or tags[t] != .identifier) return false;
    }
    // Final token must be followed by `(` for the parameterized
    // tagged-union shape we're looking for.
    if (t >= last) return false;
    return tags[t + 1] == .l_paren;
}

fn walkBodyForErrdefer(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        // Skip past nested `fn …(…) … { … }` declarations — the
        // outer loop visits each fn_decl independently so we'd
        // otherwise fire on the same errdefer once per containing
        // fn.
        if (tags[t] == .keyword_fn) {
            t = skipFnDecl(tags, t, last);
            continue;
        }
        if (tags[t] != .keyword_errdefer) continue;
        try report(gpa, problems, tree, t);
    }
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    errdefer_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`errdefer` in a fn returning a parameterized tagged-union type (not `!T`) is dead code — Zig's errdefer only fires on `return error.X` / `try` propagation, NOT on `return .{{ .err = e }}` normal returns; any cleanup here silently leaks.  Inline the cleanup at each `.err` return site, or convert the fn to `!T`",
        .{},
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "dead-errdefer-in-result-fn",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, errdefer_tok),
        .end = try Pos.fromTokenEnd(tree, errdefer_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "dead-errdefer-in-result-fn: errdefer in `Result(T)` fn fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\fn Result(comptime T: type) type {
        \\    return union(enum) { result: T, err: anyerror };
        \\}
        \\const V = struct { pub fn deinit(_: *V) void {} };
        \\pub fn parse(_: usize) Result(V) {
        \\    var v: V = .{};
        \\    errdefer v.deinit();
        \\    return .{ .err = error.X };
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("dead-errdefer-in-result-fn", problems.items[0].rule_id);
}

test "dead-errdefer-in-result-fn: errdefer in `!T` fn is OK (live)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const V = struct { pub fn deinit(_: *V) void {} };
        \\pub fn parse(_: usize) !V {
        \\    var v: V = .{};
        \\    errdefer v.deinit();
        \\    return error.X;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "dead-errdefer-in-result-fn: errdefer in `E!T` fn is OK" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const E = error{X};
        \\const V = struct { pub fn deinit(_: *V) void {} };
        \\pub fn parse(_: usize) E!V {
        \\    var v: V = .{};
        \\    errdefer v.deinit();
        \\    return error.X;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "dead-errdefer-in-result-fn: `?Result(T)` optional wrapper also fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\fn Result(comptime T: type) type {
        \\    return union(enum) { result: T, err: anyerror };
        \\}
        \\const V = struct { pub fn deinit(_: *V) void {} };
        \\pub fn parse(_: usize) ?Result(V) {
        \\    var v: V = .{};
        \\    errdefer v.deinit();
        \\    return null;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "dead-errdefer-in-result-fn: bare named return (no parens) doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const V = struct { pub fn deinit(_: *V) void {} };
        \\pub fn parse(_: usize) V {
        \\    var v: V = .{};
        \\    errdefer v.deinit();
        \\    return v;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "dead-errdefer-in-result-fn: nested fn errdefer attributed to inner fn only" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\fn Result(comptime T: type) type {
        \\    return union(enum) { result: T, err: anyerror };
        \\}
        \\const V = struct { pub fn deinit(_: *V) void {} };
        \\pub fn outer() void {
        \\    const Inner = struct {
        \\        pub fn parse(_: usize) Result(V) {
        \\            var v: V = .{};
        \\            errdefer v.deinit();
        \\            return .{ .err = error.X };
        \\        }
        \\    };
        \\    _ = Inner;
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    // Inner fn fires once; outer fn returns `void` so its scan skips
    // past the inner fn via skipFnDecl.
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}
