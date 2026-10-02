//! Token-level primitives used by every pattern-detector rule.
//!
//! These exist because the rules turned out to be much more than
//! "find this token sequence" — they need brace/paren matching,
//! statement-terminator finding, nested-fn skipping, and so on.
//! Before this module, every rule reimplemented these helpers
//! ad-hoc, and subtle bugs (`.?` is `period` + `question_mark`,
//! NOT `period_question_mark`; `.*` IS `period_asterisk` single
//! token) only surfaced when tests failed.
//!
//! Conventions:
//!   - All helpers take `tags: []const std.zig.Token.Tag` (the
//!     pre-extracted tag slice) rather than `*const Ast` to keep
//!     them allocation-free and easy to test.
//!   - `last` is the INCLUSIVE upper bound of the scan window.
//!   - Returns `?TokenIndex` for "found / not-found" results so
//!     callers can `orelse continue` on miss.

const std = @import("std");
const Ast = std.zig.Ast;

pub const TokenIndex = Ast.TokenIndex;
pub const TokenTag = std.zig.Token.Tag;

/// Root binding of an lvalue path. Arithmetic expressions have no such root.
pub fn rootIdentifier(tree: *const Ast, expression: Ast.Node.Index) ?Ast.Node.Index {
    var node = expression;
    for (0..tree.nodes.len) |_| {
        switch (tree.nodeTag(node)) {
            .identifier => return node,
            .field_access, .grouped_expression => node = tree.nodeData(node).node_and_token[0],
            .array_access, .slice_open => node = tree.nodeData(node).node_and_node[0],
            .slice, .slice_sentinel => node = tree.nodeData(node).node_and_extra[0],
            .deref => node = tree.nodeData(node).node,
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@field")) return null;
                var children = @import("type_engine").AstIterator.init(tree, node);
                node = children.next(tree) orelse return null;
            },
            else => return null,
        }
    }
    unreachable; // Parsed AST edges cannot form a cycle.
}

/// Complete named type after pointer/optional qualifiers. Compound types
/// and incomplete paths have no named-type identity.
pub fn typeNameFromTokens(tree: *const Ast, first: TokenIndex, last: TokenIndex) ?[]const u8 {
    if (first > last) return null;
    const tags = tree.tokens.items(.tag);
    var token = first;
    while (token <= last) : (token += 1) {
        switch (tags[token]) {
            .question_mark, .asterisk, .asterisk_asterisk, .keyword_const, .keyword_volatile, .keyword_allowzero => {},
            .keyword_align, .keyword_addrspace => {
                if (token + 1 > last or tags[token + 1] != .l_paren) return null;
                token = matchParen(tags, token + 1, last) orelse return null;
            },
            .identifier => break,
            else => return null,
        }
    }
    if (token > last) return null;
    const start = token;
    var identifier = true;
    while (token <= last) : (token += 1) {
        if (tags[token] != (if (identifier) TokenTag.identifier else TokenTag.period)) return null;
        identifier = !identifier;
    }
    if (identifier) return null;
    const starts = tree.tokens.items(.start);
    return tree.source[starts[start] .. starts[last] + tree.tokenSlice(last).len];
}

/// Given the `{` at `lb`, find its matching `}` within `[lb+1, last]`.
pub fn matchBrace(tags: []const TokenTag, lb: TokenIndex, last: TokenIndex) ?TokenIndex {
    var depth: u32 = 1;
    var t: TokenIndex = lb + 1;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => {
                depth -= 1;
                if (depth == 0) return t;
            },
            else => {},
        }
    }
    return null;
}

/// Given the `(` at `lp`, find its matching `)` within `[lp+1, last]`.
pub fn matchParen(tags: []const TokenTag, lp: TokenIndex, last: TokenIndex) ?TokenIndex {
    var depth: u32 = 1;
    var t: TokenIndex = lp + 1;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_paren => depth += 1,
            .r_paren => {
                depth -= 1;
                if (depth == 0) return t;
            },
            else => {},
        }
    }
    return null;
}

/// Given the `[` at `lb`, find its matching `]` within `[lb+1, last]`.
pub fn matchBracket(tags: []const TokenTag, lb: TokenIndex, last: TokenIndex) ?TokenIndex {
    var depth: u32 = 1;
    var t: TokenIndex = lb + 1;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_bracket => depth += 1,
            .r_bracket => {
                depth -= 1;
                if (depth == 0) return t;
            },
            else => {},
        }
    }
    return null;
}

/// Find the next statement-terminating `;` from `start` — one whose
/// paren/brace/bracket depth at the point of occurrence is zero
/// relative to `start`.  Returns null if no such `;` is found in
/// `[start, last]`.
pub fn findStmtSemicolon(tags: []const TokenTag, start: TokenIndex, last: TokenIndex) ?TokenIndex {
    var paren: u32 = 0;
    var brace: u32 = 0;
    var bracket: u32 = 0;
    var t: TokenIndex = start;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_paren => paren += 1,
            .r_paren => if (paren > 0) {
                paren -= 1;
            },
            .l_brace => brace += 1,
            .r_brace => if (brace > 0) {
                brace -= 1;
            },
            .l_bracket => bracket += 1,
            .r_bracket => if (bracket > 0) {
                bracket -= 1;
            },
            .semicolon => if (paren == 0 and brace == 0 and bracket == 0) return t,
            else => {},
        }
    }
    return null;
}

/// Given a `defer` / `errdefer` keyword at `kw`, find the index of
/// the statement's end — either the matching `}` of a block body
/// or the terminating `;` of an inline statement.  Handles the
/// optional `errdefer |err|` capture.
pub fn skipDeferStmt(tags: []const TokenTag, kw: TokenIndex, last: TokenIndex) ?TokenIndex {
    var t: TokenIndex = kw + 1;
    // Optional `|err|` capture on errdefer.
    if (t <= last and tags[t] == .pipe) {
        t += 1;
        while (t <= last and tags[t] != .pipe) : (t += 1) {}
        if (t > last) return null;
        t += 1;
    }
    if (t > last) return null;
    if (tags[t] == .l_brace) return matchBrace(tags, t, last);
    return findStmtSemicolon(tags, t, last);
}

/// Given a `fn` keyword at `start`, skip past the entire function
/// — proto + body.  Used by per-fn-walk rules to avoid re-scanning
/// nested fn bodies through their enclosing fn.
pub fn skipNestedFn(tags: []const TokenTag, start: TokenIndex, last: TokenIndex) TokenIndex {
    var t: TokenIndex = start;
    while (t <= last and tags[t] != .l_brace) : (t += 1) {}
    if (t > last) return last;
    return matchBrace(tags, t, last) orelse last;
}

/// Given a `fn` keyword at `start`, skip past the proto's `(...)`
/// AND the body's `{...}`.  Handles extern / proto-only fn decls
/// (no body) by bailing on `;`, `,`, or nested `fn` between `)` and `{`.
pub fn skipFnDecl(tags: []const TokenTag, start: TokenIndex, last: TokenIndex) TokenIndex {
    var t: TokenIndex = start + 1;
    while (t <= last and tags[t] != .l_paren) : (t += 1) {}
    if (t > last) return last;
    var depth: u32 = 1;
    t += 1;
    while (t <= last and depth > 0) : (t += 1) {
        switch (tags[t]) {
            .l_paren => depth += 1,
            .r_paren => depth -= 1,
            else => {},
        }
    }
    while (t <= last and tags[t] != .l_brace) : (t += 1) {
        if (tags[t] == .semicolon or tags[t] == .comma or tags[t] == .keyword_fn) return t;
    }
    if (t > last or tags[t] != .l_brace) return @min(t, last);
    depth = 1;
    t += 1;
    while (t <= last and depth > 0) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => depth -= 1,
            else => {},
        }
    }
    return @min(t -| 1, last);
}

/// True iff `c` can appear in a Zig identifier (`a-z A-Z 0-9 _`).
pub fn isIdentByte(c: u8) bool {
    return (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or
        (c >= '0' and c <= '9') or c == '_';
}

/// True iff any token in `[start, end]` has tag `needle`.
pub fn hasTokenInRange(tags: []const TokenTag, start: TokenIndex, end: TokenIndex, needle: TokenTag) bool {
    if (start > end) return false;
    var t: TokenIndex = start;
    while (t <= end) : (t += 1) {
        if (tags[t] == needle) return true;
    }
    return false;
}

/// True iff any `.identifier` token in `[start, end]` has source text
/// equal to `name`.  Cheap pre-scan helper for rules that want to
/// skip expensive per-fn analysis when a sentinel type/method name
/// isn't even mentioned.
pub fn hasIdentInRange(
    tree: *const Ast,
    start: TokenIndex,
    end: TokenIndex,
    name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start > end) return false;
    var t: TokenIndex = start;
    while (t <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t), name)) return true;
    }
    return false;
}

/// Scan `[start, last]` for the first occurrence of identifier `name`
/// at brace depth 0 relative to start.  Returns null when the name
/// isn't found or when a `}` closes the current scope before any match.
/// Useful for "does this stmt block use <ident>?" checks that must not
/// look inside nested blocks.
pub fn findIdentInScope(
    tree: *const Ast,
    start: TokenIndex,
    last: TokenIndex,
    name: []const u8,
) ?TokenIndex {
    const tags = tree.tokens.items(.tag);
    if (start > last) return null;
    var depth: u32 = 0;
    var t: TokenIndex = start;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => if (depth == 0) return null else {
                depth -= 1;
            },
            .identifier => if (std.mem.eql(u8, tree.tokenSlice(t), name)) return t,
            else => {},
        }
    }
    return null;
}

/// One argument's token span — inclusive on both ends.
pub const ArgRange = struct { start: TokenIndex, end: TokenIndex };

/// Split a call's arg list at top-level commas, APPENDING into `out`.
/// `lp` is the call's `(` and `rp` is its matching `)` (caller supplies
/// both — use `matchParen` first).  Caller is responsible for clearing
/// `out` between calls if reuse is desired (clearRetainingCapacity
/// avoids per-call allocation on the hot path).
///
/// On allocation error `out` is left partially populated — caller
/// must clear before reuse or treat the result as invalid.
pub fn splitCallArgs(
    gpa: std.mem.Allocator,
    tags: []const TokenTag,
    lp: TokenIndex,
    rp: TokenIndex,
    out: *std.ArrayListUnmanaged(ArgRange),
) !void {
    if (rp <= lp + 1) return;
    var paren: u32 = 0;
    var brace: u32 = 0;
    var bracket: u32 = 0;
    var arg_start: TokenIndex = lp + 1;
    var t: TokenIndex = lp + 1;
    while (t < rp) : (t += 1) {
        switch (tags[t]) {
            .l_paren => paren += 1,
            .r_paren => if (paren > 0) {
                paren -= 1;
            },
            .l_brace => brace += 1,
            .r_brace => if (brace > 0) {
                brace -= 1;
            },
            .l_bracket => bracket += 1,
            .r_bracket => if (bracket > 0) {
                bracket -= 1;
            },
            .comma => if (paren == 0 and brace == 0 and bracket == 0) {
                try out.append(gpa, .{ .start = arg_start, .end = t - 1 });
                arg_start = t + 1;
            },
            else => {},
        }
    }
    if (arg_start < rp) try out.append(gpa, .{ .start = arg_start, .end = rp - 1 });
}

/// True iff fn `fn_decl` returns the literal `type` — used to skip
/// comptime type-builder fns (`fn Wrap(T: type) type { return
/// struct { ... }; }`) so their inner-fn contents don't get
/// double-scanned through the outer fn.
pub fn returnsType(tree: *const Ast, fn_decl: Ast.Node.Index) bool {
    var buf: [1]Ast.Node.Index = undefined;
    const fp = fnProto(tree, &buf, fn_decl) orelse return false;
    const rt = fp.ast.return_type.unwrap() orelse return false;
    const first = tree.firstToken(rt);
    const last = tree.lastToken(rt);
    if (first != last) return false;
    return tree.tokens.items(.tag)[first] == .identifier and
        std.mem.eql(u8, tree.tokenSlice(first), "type");
}

/// Exclude compile-time bodies and operands that Zig does not evaluate.
pub fn isRuntimeUse(tree: *const Ast, fn_decl: Ast.Node.Index, anchor: Ast.TokenIndex) bool {
    if (returnsType(tree, fn_decl)) return false;
    const body = bodyOf(tree, fn_decl) orelse return false;
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    if (anchor < first or anchor > last) return false;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .@"comptime", .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(index);
        const begin = tree.firstToken(node);
        const end = tree.lastToken(node);
        if (begin < first or end > last or anchor < begin or anchor > end) continue;
        if (tag == .@"comptime") return false;
        if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@TypeOf")) return false;
    }
    return true;
}

/// Extract the `FnProto` view of an `fn_decl` node, handling all
/// four AST proto variants.  Caller owns `buf` (used by the
/// `*_one` / `*_simple` variants for inline storage).
pub fn fnProto(tree: *const Ast, buf: *[1]Ast.Node.Index, node: Ast.Node.Index) ?Ast.full.FnProto {
    return switch (tree.nodeTag(node)) {
        .fn_decl => switch (tree.nodeTag(tree.nodeData(node).node_and_node[0])) {
            .fn_proto => tree.fnProto(tree.nodeData(node).node_and_node[0]),
            .fn_proto_multi => tree.fnProtoMulti(tree.nodeData(node).node_and_node[0]),
            .fn_proto_one => tree.fnProtoOne(buf, tree.nodeData(node).node_and_node[0]),
            .fn_proto_simple => tree.fnProtoSimple(buf, tree.nodeData(node).node_and_node[0]),
            else => null,
        },
        else => null,
    };
}

/// Extract the body node of an `fn_decl`.  Returns null for the
/// non-fn-decl node tags or extern fns (no body).
pub fn bodyOf(tree: *const Ast, node: Ast.Node.Index) ?Ast.Node.Index {
    if (tree.nodeTag(node) != .fn_decl) return null;
    return tree.nodeData(node).node_and_node[1];
}

/// Return the text of a fn's first parameter name, if any.
/// Useful for rules that need to identify the method-receiver
/// param (commonly `self` / `this`) without building full bindings.
pub fn firstParamName(tree: *const Ast, fp: Ast.full.FnProto) ?[]const u8 {
    var it = fp.iterate(tree);
    const first = it.next() orelse return null;
    const tok = first.name_token orelse return null;
    return tree.tokenSlice(tok);
}

/// Iterator over every fn_decl in a tree.  The common outer loop
/// every rule has — extracted so rules don't reimplement the
/// `1..tree.nodes.len`, `nodeTag != .fn_decl`, `returnsType`,
/// `bodyOf` boilerplate.
pub const FnDeclIter = struct {
    tree: *const Ast,
    skip_type_builders: bool,
    idx: u32 = 1,

    pub const Entry = struct {
        node: Ast.Node.Index,
        name_token: TokenIndex,
        body: Ast.Node.Index,
        proto: Ast.full.FnProto,
    };

    pub fn next(self: *FnDeclIter, proto_buf: *[1]Ast.Node.Index) ?Entry {
        while (self.idx < self.tree.nodes.len) : (self.idx += 1) {
            const node: Ast.Node.Index = @enumFromInt(self.idx);
            if (self.tree.nodeTag(node) != .fn_decl) continue;
            if (self.skip_type_builders and returnsType(self.tree, node)) continue;
            const fp = fnProto(self.tree, proto_buf, node) orelse continue;
            const name_token = fp.name_token orelse continue;
            const body = bodyOf(self.tree, node) orelse continue;
            self.idx += 1;
            return .{
                .node = node,
                .name_token = name_token,
                .body = body,
                .proto = fp,
            };
        }
        return null;
    }
};

/// Construct a FnDeclIter that skips comptime type-builder fns
/// (the common case).
pub fn iterFnDecls(tree: *const Ast) FnDeclIter {
    return .{ .tree = tree, .skip_type_builders = true };
}

/// For each non-type-builder fn in `tree`, invoke `callback(gpa, tree,
/// fn_body, problems)`.  Eliminates the `proto_buf` / `iterFnDecls` /
/// `while next` boilerplate that every body-only rule reproduces.
/// `problems` is `anytype` so the helper doesn't need to import the
/// `Problem` type; `callback` is also `anytype` for the same reason
/// (Zig duck-types both at the call site).
pub fn forEachFnBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    problems: anytype,
    comptime callback: anytype,
) !void {
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = iterFnDecls(tree);
    while (fns.next(&proto_buf)) |fn_entry| {
        try callback(gpa, tree, fn_entry.body, problems);
    }
}

/// Like `forEachFnBody` but also passes the fn's `FnProto` AND a
/// per-file `cache` to the callback — for rules that inspect
/// parameter lists / return type and want amortized LocalBindings
/// via `cache.localBindings(proto, body)`.
pub fn forEachFnCached(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: anytype,
    problems: anytype,
    comptime callback: anytype,
) !void {
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = iterFnDecls(tree);
    while (fns.next(&proto_buf)) |fn_entry| {
        try callback(gpa, tree, cache, fn_entry.proto, fn_entry.body, problems);
    }
}

/// Find the innermost `fn_decl` node that contains `tok`.
/// Returns null when no fn_decl covers the token (e.g. top-level code).
/// When nested fns are present, returns the one with the largest
/// firstToken (the deepest match).
pub fn enclosingFnDecl(tree: *const Ast, tok: TokenIndex) ?Ast.Node.Index {
    var idx: u32 = 1;
    var best: ?Ast.Node.Index = null;
    var best_first: TokenIndex = 0;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const f = tree.firstToken(node);
        const l = tree.lastToken(node);
        if (tok < f or tok > l) continue;
        if (best == null or f > best_first) {
            best = node;
            best_first = f;
        }
    }
    return best;
}

/// True iff the body `[body_first..body_last]` (inclusive `{` ... `}`)
/// is empty or contains only `_ = <expr>;` discard statements.
pub fn isTrivialBody(tree: *const Ast, body_first: TokenIndex, body_last: TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    if (body_first >= body_last) return true;
    if (body_first + 1 == body_last) return true;
    var t: TokenIndex = body_first + 1;
    while (t < body_last) {
        if (tags[t] != .identifier) return false;
        if (!std.mem.eql(u8, tree.tokenSlice(t), "_")) return false;
        if (t + 1 >= body_last or tags[t + 1] != .equal) return false;
        var depth: u32 = 0;
        var k = t + 2;
        while (k < body_last) : (k += 1) {
            switch (tags[k]) {
                .l_paren, .l_brace, .l_bracket => depth += 1,
                .r_paren, .r_brace, .r_bracket => {
                    if (depth == 0) return false;
                    depth -= 1;
                },
                .semicolon => if (depth == 0) break,
                else => {},
            }
        }
        if (k >= body_last or tags[k] != .semicolon) return false;
        t = k + 1;
    }
    return true;
}

// ── Tests ──────────────────────────────────────────────────

test "matchBrace pairs simple braces" {
    const src: [:0]const u8 = "fn f() void { { } }";
    var tree = try Ast.parse(std.testing.allocator, src, .zig);
    defer tree.deinit(std.testing.allocator);
    const tags = tree.tokens.items(.tag);
    // Find first `{` (after `void`).
    var t: TokenIndex = 0;
    while (tags[t] != .l_brace) : (t += 1) {}
    const rb = matchBrace(tags, t, @intCast(tree.tokens.len - 1)).?;
    try std.testing.expectEqual(TokenTag.r_brace, tags[rb]);
}

test "findStmtSemicolon skips inner parens" {
    const src: [:0]const u8 = "fn f() void { x(a; b); }";
    var tree = try Ast.parse(std.testing.allocator, src, .zig);
    defer tree.deinit(std.testing.allocator);
    const tags = tree.tokens.items(.tag);
    // Start scanning from the `x` token.
    var t: TokenIndex = 0;
    while (tags[t] != .identifier or t == 0) : (t += 1) {
        if (tags[t] == .identifier and t > 0) break;
    }
    // Walk past `f`, `(`, `)`, `void`, `{` to find `x`.
    t = 0;
    while (t < tree.tokens.len) : (t += 1) {
        if (tags[t] == .identifier and std.mem.eql(u8, tree.tokenSlice(t), "x")) break;
    }
    const sc = findStmtSemicolon(tags, t, @intCast(tree.tokens.len - 1)).?;
    // The `;` inside the parens shouldn't count; the outer `;` should.
    try std.testing.expectEqual(TokenTag.semicolon, tags[sc]);
    // Verify it's the one OUTSIDE the parens by checking the next
    // token after is `}`.
    try std.testing.expectEqual(TokenTag.r_brace, tags[sc + 1]);
}

test "hasTokenInRange finds keyword_try" {
    const src: [:0]const u8 = "fn f() !void { _ = try g(); }";
    var tree = try Ast.parse(std.testing.allocator, src, .zig);
    defer tree.deinit(std.testing.allocator);
    const tags = tree.tokens.items(.tag);
    const last: TokenIndex = @intCast(tree.tokens.len - 1);
    try std.testing.expect(hasTokenInRange(tags, 0, last, .keyword_try));
}

test "returnsType detects fn Wrap(T) type" {
    const src: [:0]const u8 =
        \\fn Wrap(comptime _: type) type {
        \\    return struct { x: u32 };
        \\}
    ;
    var tree = try Ast.parse(std.testing.allocator, src, .zig);
    defer tree.deinit(std.testing.allocator);
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        try std.testing.expect(returnsType(&tree, node));
        return;
    }
    try std.testing.expect(false); // no fn_decl found
}

test "isTrivialBody: empty and discard-only bodies are trivial" {
    const gpa = std.testing.allocator;
    const cases = [_]struct { src: [:0]const u8, want: bool }{
        .{ .src = "fn f() void {}", .want = true },
        .{ .src = "fn f() void { _ = 1; }", .want = true },
        .{ .src = "fn f() void { _ = foo(); _ = bar; }", .want = true },
        .{ .src = "fn f() void { x = 1; }", .want = false },
        .{ .src = "fn f() void { foo(); }", .want = false },
    };
    for (cases) |c| {
        var tree = try Ast.parse(gpa, c.src, .zig);
        defer tree.deinit(gpa);
        var idx: u32 = 1;
        while (idx < tree.nodes.len) : (idx += 1) {
            const node: Ast.Node.Index = @enumFromInt(idx);
            if (tree.nodeTag(node) != .fn_decl) continue;
            const body = bodyOf(&tree, node).?;
            const bf = tree.firstToken(body);
            const bl = tree.lastToken(body);
            try std.testing.expectEqual(c.want, isTrivialBody(&tree, bf, bl));
            break;
        }
    }
}

test "skipFnDecl: skips proto+body and handles extern protos" {
    const gpa = std.testing.allocator;
    {
        const src: [:0]const u8 = "const S = struct { fn f(x: u32) void { _ = x; } };";
        var tree = try Ast.parse(gpa, src, .zig);
        defer tree.deinit(gpa);
        const tags = tree.tokens.items(.tag);
        const last: TokenIndex = @intCast(tree.tokens.len - 1);
        var t: TokenIndex = 0;
        while (tags[t] != .keyword_fn) : (t += 1) {}
        const end = skipFnDecl(tags, t, last);
        try std.testing.expectEqual(TokenTag.r_brace, tags[end]);
    }
    {
        // extern fn: no body — should stop at `;`
        const src: [:0]const u8 = "extern fn malloc(n: usize) ?*anyopaque;";
        var tree = try Ast.parse(gpa, src, .zig);
        defer tree.deinit(gpa);
        const tags = tree.tokens.items(.tag);
        const last: TokenIndex = @intCast(tree.tokens.len - 1);
        var t: TokenIndex = 0;
        while (tags[t] != .keyword_fn) : (t += 1) {}
        const end = skipFnDecl(tags, t, last);
        try std.testing.expectEqual(TokenTag.semicolon, tags[end]);
    }
}
