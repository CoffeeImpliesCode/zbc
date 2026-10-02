//! Per-fn-body local-binding origin tracker.
//!
//! Built ONCE per fn body.  Answers questions like:
//!
//!   - "What was `X` assigned from?"
//!     → `bindings.find(\"X\").?.origin` — `.call` / `.literal` /
//!       `.alias` / `.field_access` / etc.
//!   - "Is `X` a fn parameter, or a local?"
//!     → `binding.origin == .param`
//!   - "Did `X` come from `try foo()`?"
//!     → `binding.origin == .try_call`
//!   - "Did `X` come from `self.field`?"
//!     → `binding.origin == .field_access`
//!
//! Rules currently hand-roll one-hop aliasing chains for the few
//! questions they need.  With LocalBindings they share one cache
//! and one set of well-tested classification rules.
//!
//! What's tracked (v1):
//!   - All `const NAME = ...` / `var NAME = ...` declarations
//!     inside the body (at any nesting depth — we record them all
//!     and the rule scopes its lookups itself).
//!   - All fn parameters (added as `.param` origin).
//!
//! What's NOT tracked (v1):
//!   - Reassignments via `NAME = ...;` (after the initial binding).
//!     If a rule needs this, it can scan the body separately.
//!   - Destructuring (`const .{ a, b } = ...`) — entire pattern
//!     treated as one unknown binding.

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../ast/tokens.zig");

const TokenIndex = tokens.TokenIndex;
const TokenTag = tokens.TokenTag;

pub const OriginKind = enum {
    /// Fn parameter binding (declared in the proto).
    param,
    /// Loop / control-flow capture: `for (xs) |x|`, `for (xs) |x, i|`,
    /// `if (opt) |x|`, `while (it.next()) |x|`, `catch |err|`.
    /// `rhs_first` / `rhs_last` span the iterable / scrutinee expr.
    loop_capture,
    /// Literal value: `42`, `\"x\"`, `null`, `undefined`, `true`,
    /// `.{...}`, `.tag`, `[N]u8{...}`, etc.
    literal,
    /// Free fn call: `foo(...)`.
    call,
    /// Method call: `recv.method(...)`.
    method_call,
    /// `try <expr>` where `<expr>` is itself a call/method_call.
    try_call,
    /// `try <expr>` where `<expr>` is method-form.
    try_method_call,
    /// `const X = other_local;` — strict identifier alias.
    alias,
    /// `const X = recv.field;` (no parens — not a call).
    field_access,
    /// `const X = &other;`.
    addr_of,
    /// `const X = arr[...]` or `arr[a..b]` slice.
    index_op,
    /// Anything else.
    unknown,
};

/// The receiver + method tokens for a call/method_call origin.
/// For free `foo()`, `receiver` is the fn name (token slice "foo"),
/// `method` is null.  For `obj.foo()`, `receiver = "obj"`,
/// `method = "foo"`.
///
/// For multi-segment receiver paths (`std.heap.page_allocator.alloc(...)`),
/// `receiver` is the FIRST identifier (`std`) and `method` is the
/// LAST identifier before the call's `(` (`alloc`).  The
/// intermediate segments aren't stored separately — rules that
/// care can scan `[receiver_token, method_token]`.
///
/// For chained method calls (`arena.allocator().alloc(...)`),
/// `method` describes the FIRST call (`allocator`) and the
/// `outermost_*` fields describe the LAST call in the chain
/// (`alloc`).  When the RHS is a single (non-chained) call, the
/// outermost fields stay null.
pub const CallInfo = struct {
    receiver: []const u8,
    receiver_token: TokenIndex,
    method: ?[]const u8,
    method_token: ?TokenIndex,
    /// Token index of the FIRST call's opening `(`.
    paren_token: TokenIndex,
    /// LAST method in a `.foo().bar()` chain, when the RHS chains
    /// past the first call.  Null when the binding is a single call.
    outermost_method: ?[]const u8 = null,
    outermost_method_token: ?TokenIndex = null,
    outermost_paren_token: ?TokenIndex = null,

    /// Convenience: the outermost method name if the call is chained,
    /// else the first method.  Returns null only when the call is a
    /// free-fn call AND not chained.
    pub fn lastMethod(self: CallInfo) ?[]const u8 {
        return self.outermost_method orelse self.method;
    }

    /// True iff the RHS chains past the first call.
    pub fn isChained(self: CallInfo) bool {
        return self.outermost_method != null;
    }
};

pub const FieldAccess = struct {
    receiver: []const u8,
    receiver_token: TokenIndex,
    field: []const u8,
    field_token: TokenIndex,
};

pub const Origin = union(OriginKind) {
    param,
    loop_capture,
    literal,
    call: CallInfo,
    method_call: CallInfo,
    try_call: CallInfo,
    try_method_call: CallInfo,
    alias: []const u8,
    field_access: FieldAccess,
    addr_of: []const u8,
    index_op,
    unknown,
};

pub const Binding = struct {
    /// Bound name (borrowed from tree).
    name: []const u8,
    /// Token of the name identifier (the X in `const X = ...`).
    name_token: TokenIndex,
    /// True for `const`, false for `var`.  Always true for params.
    is_const: bool,
    /// First token of the RHS expression.  For params, the type's
    /// first token.
    rhs_first: TokenIndex,
    /// Last token of the RHS expression (inclusive, before `;`).
    /// For params, the type's last token.
    rhs_last: TokenIndex,
    origin: Origin,

    /// If the binding originated from a call (any form), return the
    /// call info; otherwise null.  Strips the `try` distinction.
    pub fn asCall(self: Binding) ?CallInfo {
        return switch (self.origin) {
            .call, .try_call => |c| c,
            .method_call, .try_method_call => |c| c,
            else => null,
        };
    }

    /// First RHS token after peeling a leading `try`, if present.
    /// Useful when matching token patterns against the RHS without
    /// having to special-case the `try` wrapper at every call site.
    pub fn rhsFirstAfterTry(self: Binding, tags: []const TokenTag) TokenIndex {
        if (self.rhs_first <= self.rhs_last and tags[self.rhs_first] == .keyword_try) {
            return self.rhs_first + 1;
        }
        return self.rhs_first;
    }

    /// True iff the binding's RHS was prefixed with `try` (and so the
    /// classified origin is `.try_call` / `.try_method_call`, OR the
    /// RHS started with a literal `try` keyword for non-call shapes
    /// like `const X = try expr`).  Use when a rule's logic differs
    /// between a fallible `try`-wrapped init and a bare init —
    /// `asCall()` deliberately erases this distinction.
    pub fn wasTryWrapped(self: Binding, tags: []const TokenTag) bool {
        return switch (self.origin) {
            .try_call, .try_method_call => true,
            else => self.rhs_first <= self.rhs_last and
                tags[self.rhs_first] == .keyword_try,
        };
    }
};

pub const LocalBindings = struct {
    arena: std.heap.ArenaAllocator,
    tree: *const Ast,
    items: []const Binding,

    pub fn deinit(self: *LocalBindings) void {
        self.arena.deinit();
    }

    /// First binding with matching name.  Linear scan — local
    /// counts are small per fn.  Returns the FIRST declared
    /// binding; for shadowed names callers should iterate `items`.
    pub fn find(self: *const LocalBindings, name: []const u8) ?*const Binding {
        for (self.items) |*b| {
            if (std.mem.eql(u8, b.name, name)) return b;
        }
        return null;
    }
};

/// Build local bindings. A function prototype adds parameter bindings;
/// null selects a parameterless body, such as a test block.
/// `body` is the AST body node — typically the result of
/// `tokens.bodyOf(tree, fn_decl)`.
pub fn build(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    proto: ?Ast.full.FnProto,
    body: Ast.Node.Index,
) !LocalBindings {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const a = arena.allocator();

    var items: std.ArrayListUnmanaged(Binding) = .empty;

    // ── Pass 1: params ─────────────────────────────────────
    if (proto) |function| {
        var it = function.iterate(tree);
        while (it.next()) |param| {
            const name_tok = param.name_token orelse continue;
            const type_node = param.type_expr;
            var rhs_first: TokenIndex = name_tok;
            var rhs_last: TokenIndex = name_tok;
            if (type_node) |tn| {
                rhs_first = tree.firstToken(tn);
                rhs_last = tree.lastToken(tn);
            }
            try items.append(a, .{
                .name = tree.tokenSlice(name_tok),
                .name_token = name_tok,
                .is_const = true,
                .rhs_first = rhs_first,
                .rhs_last = rhs_last,
                .origin = .param,
            });
        }
    }

    // ── Pass 2: local decls + capture clauses in body ──────
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);
    var t: TokenIndex = first;
    while (t < last) : (t += 1) {
        // Capture clauses on for/while/if/catch.  Pattern:
        //   - for (it) |x|       — pipe pair after the iterable
        //   - for (it) |x, i|    — multi-capture
        //   - if (opt) |x|       — pipe pair after the condition
        //   - while (it.next()) |x| ...
        //   - <expr> catch |err| { ... }
        // We detect by walking to the closing `)`/keyword_catch and
        // checking for a `|name(, name)?|` clause right after.
        if (tags[t] == .keyword_for or tags[t] == .keyword_while or tags[t] == .keyword_if) {
            // Skip past the (cond/iter) and walk to optional `|...|`.
            if (t + 1 > last or tags[t + 1] != .l_paren) continue;
            const close = tokens.matchParen(tags, t + 1, last) orelse continue;
            if (close + 1 > last or tags[close + 1] != .pipe) {
                continue;
            }
            try captureItemsBetween(a, &items, tree, t + 2, close - 1, close + 1, last);
            // Don't advance t past the capture — body still needs walking.
        } else if (tags[t] == .keyword_catch) {
            if (t + 1 > last or tags[t + 1] != .pipe) continue;
            // `catch` has no enclosing parens for the scrutinee — the
            // expression before `catch` is the scrutinee but we don't
            // track its range as the capture's rhs (rare to need).
            try captureItemsBetween(a, &items, tree, t, t, t + 1, last);
        }
        if (tags[t] != .keyword_const and tags[t] != .keyword_var) continue;
        if (t + 1 > last or tags[t + 1] != .identifier) continue;
        const name_tok = t + 1;
        // Skip optional type annotation `: T`.
        var eq: TokenIndex = name_tok + 1;
        if (eq <= last and tags[eq] == .colon) {
            // Walk past type to `=` at depth 0.
            var d: u32 = 0;
            while (eq <= last) : (eq += 1) {
                switch (tags[eq]) {
                    .l_paren, .l_brace, .l_bracket => d += 1,
                    .r_paren, .r_brace, .r_bracket => if (d > 0) {
                        d -= 1;
                    },
                    .equal => if (d == 0) break,
                    .semicolon => if (d == 0) break,
                    else => {},
                }
            }
        }
        if (eq > last or tags[eq] != .equal) {
            // No initializer (extern, etc.) — skip.
            t = name_tok;
            continue;
        }
        const rhs_first = eq + 1;
        const sc = tokens.findStmtSemicolon(tags, rhs_first, last) orelse {
            t = name_tok;
            continue;
        };
        if (sc == rhs_first) {
            t = sc;
            continue;
        }
        const rhs_last = sc - 1;
        const origin = classifyOrigin(tree, rhs_first, rhs_last);
        try items.append(a, .{
            .name = tree.tokenSlice(name_tok),
            .name_token = name_tok,
            .is_const = tags[t] == .keyword_const,
            .rhs_first = rhs_first,
            .rhs_last = rhs_last,
            .origin = origin,
        });
        t = sc;
    }

    return .{
        .arena = arena,
        .tree = tree,
        .items = try items.toOwnedSlice(a),
    };
}

/// Parse a `|name|` / `|name, name|` capture clause starting at
/// the first `|` (at `pipe_open`).  Append each captured identifier
/// as a Binding with origin `.loop_capture` and rhs spanning the
/// iterable / scrutinee range `[iter_first, iter_last]`.  Tolerates
/// `*` pointer-capture prefix (`for (xs) |*x|`) and underscores
/// (`for (xs) |_, i|` — skipped, not bound).
fn captureItemsBetween(
    a: std.mem.Allocator,
    items: *std.ArrayListUnmanaged(Binding),
    tree: *const Ast,
    iter_first: TokenIndex,
    iter_last: TokenIndex,
    pipe_open: TokenIndex,
    last: TokenIndex,
) !void {
    const tags = tree.tokens.items(.tag);
    if (pipe_open > last or tags[pipe_open] != .pipe) return;
    var t: TokenIndex = pipe_open + 1;
    while (t <= last and tags[t] != .pipe) : (t += 1) {
        if (tags[t] == .asterisk) continue; // `|*x|` pointer capture
        if (tags[t] == .comma) continue;
        if (tags[t] != .identifier) continue;
        const name = tree.tokenSlice(t);
        if (std.mem.eql(u8, name, "_")) continue;
        try items.append(a, .{
            .name = name,
            .name_token = t,
            .is_const = true,
            .rhs_first = iter_first,
            .rhs_last = iter_last,
            .origin = .loop_capture,
        });
    }
}

fn isBuiltinValueIdent(name: []const u8) bool {
    return std.mem.eql(u8, name, "null") or
        std.mem.eql(u8, name, "true") or
        std.mem.eql(u8, name, "false") or
        std.mem.eql(u8, name, "undefined");
}

fn classifyOrigin(tree: *const Ast, first: TokenIndex, last: TokenIndex) Origin {
    const tags = tree.tokens.items(.tag);
    if (first > last) return .unknown;

    // Peel a leading `try`.
    var t: TokenIndex = first;
    var wrapped_in_try = false;
    if (tags[t] == .keyword_try) {
        wrapped_in_try = true;
        t += 1;
        if (t > last) return .unknown;
    }

    return switch (tags[t]) {
        .number_literal,
        .string_literal,
        .multiline_string_literal_line,
        .char_literal,
        .keyword_unreachable,
        => .literal,
        .period => blk: {
            // `.{...}`  → struct literal
            // `.tag`    → enum literal
            // `.foo()` is an anonymous-enum-then-call — rare, treat as literal.
            if (t + 1 <= last and (tags[t + 1] == .l_brace or tags[t + 1] == .identifier)) {
                break :blk .literal;
            }
            break :blk .unknown;
        },
        .ampersand => blk: {
            // `&X` where X is an identifier.
            if (t + 1 <= last and tags[t + 1] == .identifier) {
                break :blk .{ .addr_of = tree.tokenSlice(t + 1) };
            }
            break :blk .unknown;
        },
        .l_bracket => .literal, // `[N]u8{...}`, slice literal
        .identifier => blk: {
            const id = tree.tokenSlice(t);
            const id_tok = t;
            // Built-in value identifiers: `null`, `true`, `false`,
            // `undefined` — tokenized as `.identifier` but semantically
            // literal values.
            if (t == last and isBuiltinValueIdent(id)) {
                break :blk .literal;
            }
            // Alias: identifier alone (rhs spans only this token).
            if (t == last) {
                break :blk .{ .alias = id };
            }
            // identifier `[` ... — index/slice op.  Check first since
            // chain-walking below assumes no leading bracket.
            if (tags[t + 1] == .l_bracket) {
                break :blk .index_op;
            }
            // Walk a chain `<id>(.<id>)*` collecting identifier positions.
            // Stops at `(` (call), end-of-range, or non-(period+identifier).
            var chain_buf: [16]TokenIndex = undefined;
            var chain_len: usize = 1;
            chain_buf[0] = id_tok;
            var u: TokenIndex = t + 1;
            while (u <= last) {
                if (tags[u] != .period) break;
                if (u + 1 > last or tags[u + 1] != .identifier) break;
                if (chain_len >= chain_buf.len) break;
                chain_buf[chain_len] = u + 1;
                chain_len += 1;
                u += 2;
            }
            // After the chain walk, u is past the last chain segment.
            // Three possibilities:
            //   (1) u > last  → pure field-chain (no call).  field_access if
            //                  chain_len == 2 and chain_buf[1] == last,
            //                  else .unknown.
            //   (2) tags[u] == .l_paren → call at chain_buf[chain_len - 1].
            //   (3) anything else → unknown.
            if (u > last) {
                if (chain_len == 2 and chain_buf[1] == last) {
                    break :blk .{ .field_access = .{
                        .receiver = id,
                        .receiver_token = id_tok,
                        .field = tree.tokenSlice(chain_buf[1]),
                        .field_token = chain_buf[1],
                    } };
                }
                break :blk .unknown;
            }
            if (tags[u] != .l_paren) break :blk .unknown;

            // Build the first-call CallInfo.  For chain_len == 1, this is a
            // free-fn call (no method).  For chain_len >= 2, the LAST chain
            // segment is the method, with the rest forming the receiver path.
            const first_paren = u;
            const first_is_free = chain_len == 1;
            var info: CallInfo = .{
                .receiver = id,
                .receiver_token = id_tok,
                .method = if (first_is_free) null else tree.tokenSlice(chain_buf[chain_len - 1]), // zbc-disable-line: index-minus-one-without-zero-guard — first_is_free = chain_len==1; else branch only reached when chain_len>=2
                .method_token = if (first_is_free) null else chain_buf[chain_len - 1], // zbc-disable-line: index-minus-one-without-zero-guard — same guard
                .paren_token = first_paren,
            };

            // Walk chained calls past the first `()`: `(...).<id>(`.
            var cp = tokens.matchParen(tags, first_paren, last);
            while (cp) |close| {
                const v = close + 1;
                if (v + 2 > last) break;
                if (tags[v] != .period) break;
                if (tags[v + 1] != .identifier) break;
                if (tags[v + 2] != .l_paren) break;
                info.outermost_method = tree.tokenSlice(v + 1);
                info.outermost_method_token = v + 1;
                info.outermost_paren_token = v + 2;
                cp = tokens.matchParen(tags, v + 2, last);
            }

            if (first_is_free) {
                break :blk if (wrapped_in_try) .{ .try_call = info } else .{ .call = info };
            }
            break :blk if (wrapped_in_try) .{ .try_method_call = info } else .{ .method_call = info };
        },
        else => .unknown,
    };
}

// ── Tests ──────────────────────────────────────────────────

const testing = std.testing;

/// Parse `src` (which must declare exactly one fn `f(...) ...`) and
/// build a LocalBindings for `f`'s body.  Returns the bindings plus
/// the owned tree — caller deinits both (bindings first).
fn parseFn(src: [:0]const u8) !struct { tree: Ast, bindings: LocalBindings } {
    var tree = try Ast.parse(testing.allocator, src, .zig);
    errdefer tree.deinit(testing.allocator);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var idx: u32 = 1;
    while (idx < tree.nodes.len) : (idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(&tree, &buf, node).?;
        const body = tokens.bodyOf(&tree, node).?;
        const bindings = try build(testing.allocator, &tree, proto, body);
        return .{ .tree = tree, .bindings = bindings };
    }
    unreachable;
}

test "build: parameter classified as .param" {
    var r = try parseFn("fn f(a: u32, b: []const u8) void { _ = a; _ = b; }");
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const a_bind = bindings.find("a").?;
    try testing.expectEqual(OriginKind.param, std.meta.activeTag(a_bind.origin));
    const b_bind = bindings.find("b").?;
    try testing.expectEqual(OriginKind.param, std.meta.activeTag(b_bind.origin));
}

test "build: literal initializers" {
    var r = try parseFn(
        \\fn f() void {
        \\    const a = 42;
        \\    const b = "hello";
        \\    const c = .{};
        \\    const d = null;
        \\    const e = undefined;
        \\    const g = true;
        \\    const h = .my_tag;
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    for ([_][]const u8{ "a", "b", "c", "d", "e", "g", "h" }) |name| {
        const bind = bindings.find(name).?;
        try testing.expectEqual(OriginKind.literal, std.meta.activeTag(bind.origin));
    }
}

test "build: free fn call vs method call" {
    var r = try parseFn(
        \\fn f() void {
        \\    const a = foo();
        \\    const b = obj.method();
        \\    const c = try foo();
        \\    const d = try obj.method();
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const a = bindings.find("a").?;
    try testing.expectEqual(OriginKind.call, std.meta.activeTag(a.origin));
    try testing.expectEqualStrings("foo", a.origin.call.receiver);
    try testing.expectEqual(@as(?[]const u8, null), a.origin.call.method);

    const b = bindings.find("b").?;
    try testing.expectEqual(OriginKind.method_call, std.meta.activeTag(b.origin));
    try testing.expectEqualStrings("obj", b.origin.method_call.receiver);
    try testing.expectEqualStrings("method", b.origin.method_call.method.?);

    const c = bindings.find("c").?;
    try testing.expectEqual(OriginKind.try_call, std.meta.activeTag(c.origin));

    const d = bindings.find("d").?;
    try testing.expectEqual(OriginKind.try_method_call, std.meta.activeTag(d.origin));
}

test "build: field access vs alias" {
    var r = try parseFn(
        \\fn f(self: anytype) void {
        \\    const a = self;
        \\    const b = self.field;
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const a = bindings.find("a").?;
    try testing.expectEqual(OriginKind.alias, std.meta.activeTag(a.origin));
    try testing.expectEqualStrings("self", a.origin.alias);

    const b = bindings.find("b").?;
    try testing.expectEqual(OriginKind.field_access, std.meta.activeTag(b.origin));
    try testing.expectEqualStrings("self", b.origin.field_access.receiver);
    try testing.expectEqualStrings("field", b.origin.field_access.field);
}

test "build: addr_of and index_op" {
    var r = try parseFn(
        \\fn f() void {
        \\    var thing: u32 = 0;
        \\    const p = &thing;
        \\    const arr = [_]u8{ 1, 2, 3 };
        \\    const x = arr[0];
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const p = bindings.find("p").?;
    try testing.expectEqual(OriginKind.addr_of, std.meta.activeTag(p.origin));
    try testing.expectEqualStrings("thing", p.origin.addr_of);

    const x = bindings.find("x").?;
    try testing.expectEqual(OriginKind.index_op, std.meta.activeTag(x.origin));
}

test "build: chained method call captures outermost" {
    var r = try parseFn(
        \\fn f() void {
        \\    const a = arena.allocator().alloc(u8, 16);
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const a = bindings.find("a").?;
    const c = a.asCall().?;
    try testing.expectEqualStrings("arena", c.receiver);
    try testing.expectEqualStrings("allocator", c.method.?);
    try testing.expect(c.isChained());
    try testing.expectEqualStrings("alloc", c.outermost_method.?);
    try testing.expectEqualStrings("alloc", c.lastMethod().?);
}

test "build: try-wrapped chained call" {
    var r = try parseFn(
        \\fn f() !void {
        \\    const b = try arena.allocator().dupe(u8, "x");
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const b = bindings.find("b").?;
    try testing.expectEqual(OriginKind.try_method_call, std.meta.activeTag(b.origin));
    const c = b.asCall().?;
    try testing.expectEqualStrings("arena", c.receiver);
    try testing.expectEqualStrings("allocator", c.method.?);
    try testing.expectEqualStrings("dupe", c.outermost_method.?);
}

test "build: multi-segment receiver path (std.heap.page_allocator.alloc)" {
    var r = try parseFn(
        \\fn f() ![]u8 {
        \\    const c = try std.heap.page_allocator.alloc(u8, 16);
        \\    return c;
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const c = bindings.find("c").?;
    const ci = c.asCall().?;
    try testing.expectEqualStrings("std", ci.receiver);
    // `page_allocator` is the LAST identifier before the call's `(`
    // — so it's our "method" name (receiver path was std.heap.page_allocator).
    try testing.expectEqualStrings("alloc", ci.method.?);
    try testing.expect(!ci.isChained()); // single call, just deep receiver
}

test "build: non-chained single call doesn't set outermost" {
    var r = try parseFn(
        \\fn f() void {
        \\    const a = obj.method();
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const a = bindings.find("a").?;
    const c = a.asCall().?;
    try testing.expect(!c.isChained());
    try testing.expectEqual(@as(?[]const u8, null), c.outermost_method);
    try testing.expectEqualStrings("method", c.lastMethod().?);
}

test "build: triple-chained call captures last" {
    var r = try parseFn(
        \\fn f() void {
        \\    const a = obj.first().second().third();
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const a = bindings.find("a").?;
    const c = a.asCall().?;
    try testing.expectEqualStrings("first", c.method.?);
    try testing.expectEqualStrings("third", c.outermost_method.?);
}

test "Binding.asCall unifies try / non-try" {
    var r = try parseFn(
        \\fn f() void {
        \\    const a = obj.method();
        \\    const b = try obj.method();
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const a = bindings.find("a").?.asCall().?;
    const b = bindings.find("b").?.asCall().?;
    try testing.expectEqualStrings("obj", a.receiver);
    try testing.expectEqualStrings("method", a.method.?);
    try testing.expectEqualStrings("obj", b.receiver);
    try testing.expectEqualStrings("method", b.method.?);
}

test "build: var binding" {
    var r = try parseFn(
        \\fn f() void {
        \\    var x: u32 = 0;
        \\    _ = x;
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const x = bindings.find("x").?;
    try testing.expect(!x.is_const);
}

test "build: for-loop capture" {
    var r = try parseFn(
        \\fn f(items: []u8) void {
        \\    for (items) |item| {
        \\        _ = item;
        \\    }
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const item = bindings.find("item").?;
    try testing.expectEqual(OriginKind.loop_capture, std.meta.activeTag(item.origin));
}

test "build: for-loop multi-capture" {
    var r = try parseFn(
        \\fn f(items: []u8) void {
        \\    for (items, 0..) |item, i| {
        \\        _ = item;
        \\        _ = i;
        \\    }
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();

    const item = bindings.find("item").?;
    try testing.expectEqual(OriginKind.loop_capture, std.meta.activeTag(item.origin));
    const i = bindings.find("i").?;
    try testing.expectEqual(OriginKind.loop_capture, std.meta.activeTag(i.origin));
}

test "build: pointer-capture |*x|" {
    var r = try parseFn(
        \\fn f(items: []u8) void {
        \\    for (items) |*item| {
        \\        item.* = 0;
        \\    }
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();
    try testing.expect(bindings.find("item") != null);
}

test "build: if-optional capture" {
    var r = try parseFn(
        \\fn f(maybe: ?u8) void {
        \\    if (maybe) |v| {
        \\        _ = v;
        \\    }
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();
    try testing.expect(bindings.find("v") != null);
}

test "build: while capture" {
    var r = try parseFn(
        \\fn f(it: anytype) void {
        \\    while (it.next()) |v| {
        \\        _ = v;
        \\    }
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();
    try testing.expect(bindings.find("v") != null);
}

test "build: underscore capture is skipped" {
    var r = try parseFn(
        \\fn f(items: []u8) void {
        \\    for (items, 0..) |_, i| {
        \\        _ = i;
        \\    }
        \\}
    );
    defer r.tree.deinit(testing.allocator);
    var bindings = r.bindings;
    defer bindings.deinit();
    try testing.expect(bindings.find("_") == null);
    try testing.expect(bindings.find("i") != null);
}
