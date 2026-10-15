//! Detects `.next().?` — a forced unwrap of an iterator's optional result.
//!
//! Standard Zig iterators return `?T`: `null` signals exhaustion.  Calling
//! `.next().?` asserts at runtime that the iterator has a remaining element.
//! When the iterator is already exhausted (e.g. the caller passed fewer items
//! than the code expects), this panics in debug/safe builds and invokes UB in
//! ReleaseFast.
//!
//! The safe idiom is `iter.next() orelse <handle-end>` or the `while`-loop
//! form `while (iter.next()) |val| { … }`.
//!
//! Real-world shapes:
//!   oven-sh/bun#27415 — `seq` builtin called `.next().?` after consuming all
//!     flags; when only flags were provided (no numeric args) the iterator was
//!     already empty → panic.
//!   oven-sh/bun#27316 — `cmds_array.next().?` on a JS-supplied argument list;
//!     empty array caused unconditional panic.
//!
//! Detection (Tier 1, token walk):
//!   6-token pattern:
//!     t+0: period   t+1: identifier("next")   t+2: l_paren
//!     t+3: r_paren  t+4: period               t+5: question_mark
//!   Fire at the `identifier("next")` token (t+1).
//!
//!   Suppression: findings inside a `test { … }` declaration body are
//!   suppressed.  Test code force-unwraps iterators over hard-coded, known
//!   inputs as a deliberate assertion; a panic there is a test failure, not a
//!   production crash.  This rule targets production input-handling code where
//!   the iterator may be empty at runtime.  (Token-level `keyword_test`
//!   brace-matching — see `collectTestRanges`.)
//!
//! Source-backed suppression resolves an earlier observation and this call to
//! exact bodies on the same receiver. The observation must dominate this path.
//! Unknown calls, writes, deferred cleanup, and unexpanded control flow refuse
//! the proof. First-result proofs read the initialized receiver field and all
//! null exits of the exact consuming body, with the same path stability checks.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const call_effects = @import("../../cache/call_effects.zig");
const tokens = @import("../../ast/tokens.zig");
const TypeResolver = @import("../../type_resolver.zig").TypeResolver;
const Iterator = @import("type_engine").AstIterator;

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "forced-unwrap-iterator-next";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .forced_unwrap_iterator_next)) return;
    const call_index = try cache.getCallIndex();

    const tags = tree.tokens.items(.tag);
    const last_tok = tree.lastToken(.root);

    var test_ranges: std.ArrayListUnmanaged(Range) = .empty;
    defer test_ranges.deinit(gpa);
    try collectTestRanges(gpa, tree, tags, &test_ranges);

    var t: Ast.TokenIndex = 0;
    while (t + 5 <= last_tok) : (t += 1) {
        // Pattern: . next ( ) . ?
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "next")) continue;
        if (tags[t + 2] != .l_paren) continue;
        if (tags[t + 3] != .r_paren) continue;
        if (tags[t + 4] != .period) continue;
        if (tags[t + 5] != .question_mark) continue;

        if (isInTestRange(test_ranges.items, t + 1)) continue;

        // Suppress `assert(RECV.next().?)` — the forced-unwrap is an
        // invariant assertion (programmer-verified that the element exists);
        // it behaves like a test assertion and a panic is a code bug, not
        // user input reaching an unchecked path.
        // Pattern (from t): t-2 = l_paren, t-3 = identifier("assert").
        if (t >= 3 and
            tags[t - 2] == .l_paren and
            tags[t - 3] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t - 3), "assert")) continue;

        if (call_index.by_callee_token.get(t)) |call| {
            if (try hasStableLookahead(cache, call)) continue;
        }

        try report(gpa, problems, tree, t + 1);
    }
}

/// Token span of a `test { … }` declaration, from the `keyword_test` token
/// through its body's closing `r_brace` (inclusive).
const Range = struct { start: Ast.TokenIndex, end: Ast.TokenIndex };

/// Collects the token range of every `test` declaration and every `fn testXxx`
/// test-utility function in the file.  Covers:
///   `KEYWORD_test (STRINGLITERAL / IDENTIFIER)? Block`  — test declarations
///   `KEYWORD_fn IDENTIFIER(testXxx...) PARAMS RETTYPE Block` — test helpers
/// where `testXxx` means the name starts with lowercase "test" followed by an
/// uppercase letter (camelCase convention for Zig test utilities).
/// Ranges are pairwise disjoint (tests cannot nest), so a linear containment
/// check suffices.
fn collectTestRanges(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    out: *std.ArrayListUnmanaged(Range),
) !void {
    // `lastToken` returns a `TokenIndex` — a `u32` — so the scan bound
    // is the width every index below already uses, with no conversion
    // of the token count to re-narrow.
    const last_tok = tree.lastToken(.root);
    var i: Ast.TokenIndex = 0;
    while (i <= last_tok) : (i += 1) {
        const is_test_decl = tags[i] == .keyword_test;
        const is_test_fn = blk: {
            if (tags[i] != .keyword_fn) break :blk false;
            if (i + 1 > last_tok or tags[i + 1] != .identifier) break :blk false;
            const name = tree.tokenSlice(i + 1);
            // Match fn names that start with "test" (lowercase) followed by
            // an uppercase letter — the Zig convention for test helper fns.
            if (name.len < 5) break :blk false;
            if (!std.mem.startsWith(u8, name, "test")) break :blk false;
            break :blk std.ascii.isUpper(name[4]);
        };
        if (!is_test_decl and !is_test_fn) continue;

        // Find the body's opening `l_brace` (skipping header tokens).
        var j = i + 1;
        while (j <= last_tok and tags[j] != .l_brace) : (j += 1) {
            // Defensive: a well-formed header has no `;`/`}` before `{`.
            if (tags[j] == .semicolon or tags[j] == .r_brace) break;
        }
        if (j > last_tok or tags[j] != .l_brace) continue;

        // Brace-match forward from the opening brace.
        var depth: u32 = 0;
        var k = j;
        while (k <= last_tok) : (k += 1) {
            if (tags[k] == .l_brace) {
                depth += 1;
            } else if (tags[k] == .r_brace) {
                depth -= 1;
                if (depth == 0) break;
            }
        }
        if (k > last_tok) break; // unbalanced — only possible on a malformed tree

        try out.append(gpa, .{ .start = i, .end = k });
        i = k; // resume past this body
    }
}

/// True when `tok` falls within any collected `test { … }` range.
fn isInTestRange(ranges: []const Range, tok: Ast.TokenIndex) bool {
    for (ranges) |r| {
        if (tok >= r.start and tok <= r.end) return true;
    }
    return false;
}

/// A first result needs two source facts: the actual initialized receiver field
/// excludes the consuming body's first null exit, and every other return has a
/// nonoptional value. Neither the constructor nor the method spelling is proof.
fn knownInitialResult(proof: *Lookahead, first: Ast.TokenIndex, last: Ast.TokenIndex) file_cache_mod.SummaryError!?Ast.Node.Index {
    const cache = proof.cache;
    const tree = cache.tree;
    const initializer = cache.nodeForExactSpan(first, last) orelse return null;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const target_call = tree.fullCall(&call_buffer, proof.target) orelse return null;
    const consumed = (try cache.actualCallSummaryAt(tree.nodeMainToken(target_call.ast.fn_expr), null)) orelse return null;
    if (consumed.argument_offset != 1) return null;
    var argument_buffer: [2]Ast.Node.Index = undefined;
    const actual_receiver = (try consumed.callArgumentFor(cache, &argument_buffer, 0)) orelse return null;
    if (actual_receiver != tree.nodeData(target_call.ast.fn_expr).node_and_token[0]) return null;
    const source = consumed.callee.tree;
    const body = tokens.bodyOf(source, consumed.callee.declaration) orelse return null;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(source, &proto_buffer, consumed.callee.declaration) orelse return null;
    const receiver = tokens.firstParamName(source, proto) orelse return null;
    const resolver = cache.zls orelse return null;
    const frame = resolver.frameForFunction(consumed.callee.reference);
    var statements = Iterator.init(source, body);
    const guard = statements.next(source) orelse return null;
    var excluded: Ast.Node.Index = undefined;
    var field: []const u8 = undefined;
    var needs_nonempty = false;
    if (source.fullVarDecl(guard)) |local| {
        const value = local.ast.init_node.unwrap() orelse return null;
        if (source.nodeTag(value) != .@"orelse") return null;
        const observed, const missing = source.nodeData(value).node_and_node;
        field = receiverField(source, observed, receiver) orelse return null;
        const observed_type = (try frame.typeOfNode(observed)) orelse return null;
        if (resolver.typeTag(observed_type) != .optional) return null;
        if (!returnsNull(source, missing)) return null;
        excluded = missing;
    } else if (source.fullIf(guard)) |branch| {
        if (branch.ast.else_expr.unwrap() != null or source.nodeTag(branch.ast.cond_expr) != .equal_equal) return null;
        const length, const zero = source.nodeData(branch.ast.cond_expr).node_and_node;
        if (source.nodeTag(zero) != .number_literal or !std.mem.eql(u8, source.getNodeSource(zero), "0")) return null;
        if (source.nodeTag(length) != .field_access) return null;
        const collection, const member = source.nodeData(length).node_and_token;
        if (!std.mem.eql(u8, source.tokenSlice(member), "len")) return null;
        field = receiverField(source, collection, receiver) orelse return null;
        const collection_type = (try frame.typeOfNode(collection)) orelse return null;
        if (resolver.pointerSize(collection_type) != .slice) return null;
        if (!returnsNull(source, branch.ast.then_expr)) return null;
        excluded = branch.ast.then_expr;
        needs_nonempty = true;
    } else return null;

    var literal_tree = tree;
    var literal_node = initializer;
    if (tree.fullCall(&call_buffer, initializer)) |constructor| {
        const actual = (try cache.actualCallSummaryAt(tree.nodeMainToken(constructor.ast.fn_expr), null)) orelse return null;
        literal_tree = actual.callee.tree;
        const constructor_body = tokens.bodyOf(literal_tree, actual.callee.declaration) orelse return null;
        var constructor_statements = Iterator.init(literal_tree, constructor_body);
        const result = constructor_statements.next(literal_tree) orelse return null;
        if (constructor_statements.next(literal_tree) != null or literal_tree.nodeTag(result) != .@"return") return null;
        literal_node = literal_tree.nodeData(result).opt_node.unwrap() orelse return null;
    }
    var literal_buffer: [2]Ast.Node.Index = undefined;
    const literal = literal_tree.fullStructInit(&literal_buffer, literal_node) orelse return null;
    var found = false;
    for (literal.ast.fields) |value| {
        try proof.charge();
        const token = literal_tree.firstToken(value);
        if (token < 2 or literal_tree.tokenTag(token - 1) != .equal or
            !std.mem.eql(u8, literal_tree.tokenSlice(token - 2), field)) continue;
        if (found) return null;
        found = true;
        if (needs_nonempty) {
            if (literal_tree.nodeTag(value) != .address_of) return null;
            const array = literal_tree.nodeData(value).node;
            var array_buffer: [2]Ast.Node.Index = undefined;
            const elements = literal_tree.fullArrayInit(&array_buffer, array) orelse return null;
            if (elements.ast.elements.len == 0) return null;
        } else if (literal_tree.nodeTag(value) != .number_literal) return null;
    }
    if (!found) return null;
    if (!try allReturnsPresent(proof, source, body, excluded, frame, 0)) return null;
    return initializer;
}

fn receiverField(tree: *const Ast, node: Ast.Node.Index, receiver: []const u8) ?[]const u8 {
    if (tree.nodeTag(node) != .field_access) return null;
    const base, const member = tree.nodeData(node).node_and_token;
    if (tree.nodeTag(base) != .identifier or
        !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(base)), receiver)) return null;
    return tree.tokenSlice(member);
}

fn returnsNull(tree: *const Ast, node: Ast.Node.Index) bool {
    if (tree.nodeTag(node) != .@"return") return false;
    const value = tree.nodeData(node).opt_node.unwrap() orelse return false;
    return tree.nodeTag(value) == .identifier and std.mem.eql(u8, tree.getNodeSource(value), "null");
}

fn allReturnsPresent(proof: *Lookahead, tree: *const Ast, node: Ast.Node.Index, excluded: Ast.Node.Index, frame: TypeResolver.ResolutionFrame, depth: u32) file_cache_mod.SummaryError!bool {
    try proof.charge();
    if (depth >= 64) return false;
    if (node == excluded) return true;
    switch (tree.nodeTag(node)) {
        .fn_decl, .fn_proto, .fn_proto_one, .fn_proto_multi, .fn_proto_simple => return true,
        .@"return" => {
            const value = tree.nodeData(node).opt_node.unwrap() orelse return false;
            const actual = (try frame.typeOfNode(value)) orelse return false;
            const normalized = (try frame.resolver.normalizedType(actual)) orelse return false;
            return switch (frame.resolver.typeTag(normalized) orelse return false) {
                .int, .comptime_int, .bool, .float, .comptime_float, .pointer, .array, .@"enum" => true,
                else => false,
            };
        },
        else => {},
    }
    var container_buffer: [2]Ast.Node.Index = undefined;
    if (tree.fullContainerDecl(&container_buffer, node) != null) return true;
    var children = Iterator.init(tree, node);
    while (children.next(tree)) |child| {
        if (!try allReturnsPresent(proof, tree, child, excluded, frame, depth + 1)) return false;
    }
    return true;
}

const Flow = struct {
    available: bool = false,
    reaches: bool = true,
    found: bool = false,
};

/// A local path proof. Unknown calls invalidate the entire observation, not
/// merely the receiver argument: they can also change its backing storage.
const Lookahead = struct {
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    target: Ast.Node.Index,
    receiver_binding: Ast.TokenIndex,
    opaque_nodes: []const Ast.Node.Index = &.{},
    first_result: ?Ast.Node.Index = null,
    remaining: u32 = 50_000,

    fn charge(self: *Lookahead) file_cache_mod.SummaryError!void {
        if (self.remaining == 0) return error.AnalysisBudgetExceeded;
        self.remaining -= 1;
    }

    fn contains(self: *const Lookahead, node: Ast.Node.Index) bool {
        const tree = self.cache.tree;
        const target_token = tree.firstToken(self.target);
        return tree.firstToken(node) <= target_token and tree.lastToken(node) >= tree.lastToken(self.target);
    }

    fn cleanupMayRunBeforeTarget(self: *Lookahead, cleanup: Ast.Node.Index) file_cache_mod.SummaryError!bool {
        const tree = self.cache.tree;
        const first = tree.firstToken(cleanup);
        if (first >= tree.firstToken(self.target)) return false;
        var scope = self.body;
        var node = self.body;
        for (0..64) |_| {
            try self.charge();
            switch (tree.nodeTag(node)) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => scope = node,
                else => {},
            }
            if (node == cleanup) return !self.contains(scope);
            var children = Iterator.init(tree, node);
            var containing: ?Ast.Node.Index = null;
            while (children.next(tree)) |child| {
                try self.charge();
                if (tree.firstToken(child) <= first and tree.lastToken(child) >= tree.lastToken(cleanup)) {
                    containing = child;
                    break;
                }
            }
            node = containing orelse return true;
        }
        return true;
    }

    fn sameReceiver(self: *Lookahead, call_node: Ast.Node.Index) file_cache_mod.SummaryError!bool {
        const tree = self.cache.tree;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, call_node) orelse return false;
        if (call.ast.params.len != 0 or tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
        const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
        if (tree.nodeTag(receiver) != .identifier) return false;
        const token = tree.nodeMainToken(receiver);
        const bindings = try self.cache.localBindings(self.proto, self.body);
        const binding = bindings.findAt(tree.tokenSlice(token), token) orelse return false;
        return binding.name_token == self.receiver_binding;
    }

    fn lexicalOwner(self: *Lookahead, tree: *const Ast, declaration: Ast.Node.Index) file_cache_mod.SummaryError!?Ast.Node.Index {
        const first = tree.firstToken(declaration);
        var node: Ast.Node.Index = .root;
        var owner: ?Ast.Node.Index = null;
        for (0..64) |_| {
            try self.charge();
            if (node == declaration) return owner;
            var buffer: [2]Ast.Node.Index = undefined;
            if (tree.fullContainerDecl(&buffer, node) != null) owner = node;
            var children = Iterator.init(tree, node);
            var containing: ?Ast.Node.Index = null;
            while (children.next(tree)) |child| {
                try self.charge();
                if (tree.firstToken(child) <= first and tree.lastToken(child) >= tree.lastToken(declaration)) {
                    containing = child;
                    break;
                }
            }
            node = containing orelse return null;
        }
        return null;
    }

    fn observes(self: *Lookahead, node: Ast.Node.Index) file_cache_mod.SummaryError!bool {
        try self.charge();
        if (!try self.sameReceiver(node)) return false;
        const tree = self.cache.tree;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node).?;
        const target_call = tree.fullCall(&buffer, self.target).?;
        const observed = (try self.cache.actualCallSummaryAt(tree.nodeMainToken(call.ast.fn_expr), null)) orelse return false;
        const consumed = (try self.cache.actualCallSummaryAt(tree.nodeMainToken(target_call.ast.fn_expr), null)) orelse return false;
        if (observed.argument_offset != 1 or consumed.argument_offset != 1) return false;
        if (observed.callee.tree != consumed.callee.tree) return false;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const observed_actual = (try observed.callArgumentFor(self.cache, &argument_buffer, 0)) orelse return false;
        if (observed_actual != tree.nodeData(call.ast.fn_expr).node_and_token[0]) return false;
        const consumed_actual = (try consumed.callArgumentFor(self.cache, &argument_buffer, 0)) orelse return false;
        if (consumed_actual != tree.nodeData(target_call.ast.fn_expr).node_and_token[0]) return false;
        const owner = (try self.lexicalOwner(observed.callee.tree, observed.callee.declaration)) orelse return false;
        if (owner != (try self.lexicalOwner(consumed.callee.tree, consumed.callee.declaration))) return false;
        if ((try self.cache.callEffectAt(tree.nodeMainToken(call.ast.fn_expr), .{ .whole = observed.callee }, .{ .remaining = &self.remaining })) != .read_only) return false;
        return try equivalentObservation(self, observed.callee.tree, observed.callee.declaration, consumed.callee.declaration);
    }

    fn walk(self: *Lookahead, node: Ast.Node.Index, incoming: Flow, depth: u32) file_cache_mod.SummaryError!Flow {
        try self.charge();
        if (depth >= 64) return .{};
        if (node == self.target) return .{ .available = incoming.available, .found = true };
        if (!incoming.reaches) return incoming;
        if (self.first_result == node) return .{ .available = true };
        const tree = self.cache.tree;
        const tag = tree.nodeTag(node);
        // Registration is not execution. The enclosing syntax pass refuses
        // cleanup scopes that may finish before the selected call.
        if (tag == .@"defer" or tag == .@"errdefer") return incoming;
        for (self.opaque_nodes) |unsupported| if (unsupported == node) return .{};
        // Declaring a function or a type does not execute its body.
        if (tag == .fn_decl or tag == .fn_proto or tag == .fn_proto_one or
            tag == .fn_proto_multi or tag == .fn_proto_simple) return incoming;
        var container_buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullContainerDecl(&container_buffer, node) != null) return incoming;
        if (tree.fullIf(node)) |branch| {
            const condition = try self.walk(branch.ast.cond_expr, incoming, depth + 1);
            if (condition.found) return condition;
            if (self.contains(node)) {
                if (self.contains(branch.ast.then_expr)) return self.walk(branch.ast.then_expr, condition, depth + 1);
                if (branch.ast.else_expr.unwrap()) |other| return self.walk(other, condition, depth + 1);
                return .{};
            }
            const yes = try self.walk(branch.ast.then_expr, condition, depth + 1);
            const no = if (branch.ast.else_expr.unwrap()) |other| try self.walk(other, condition, depth + 1) else condition;
            if (!yes.reaches) return no;
            if (!no.reaches) return yes;
            return .{ .available = yes.available and no.available };
        }
        if (tree.fullWhile(node)) |loop| {
            // A preceding observation is not renewable on a backedge.
            if (!self.contains(loop.ast.then_expr)) return .{};
            const condition = try self.walk(loop.ast.cond_expr, .{}, depth + 1);
            return self.walk(loop.ast.then_expr, condition, depth + 1);
        }
        if (tree.fullFor(node)) |loop| {
            if (!self.contains(loop.ast.then_expr)) return .{};
            return self.walk(loop.ast.then_expr, .{}, depth + 1);
        }
        if (tag == .bool_and or tag == .bool_or) {
            const left, const right = tree.nodeData(node).node_and_node;
            const lhs = try self.walk(left, incoming, depth + 1);
            if (lhs.found) return lhs;
            const rhs = try self.walk(right, lhs, depth + 1);
            if (rhs.found) return rhs;
            return .{ .available = lhs.available and rhs.available };
        }
        if (tag == .@"orelse") {
            const left, const right = tree.nodeData(node).node_and_node;
            if (abrupt(tree, right) and try self.observes(left))
                return .{ .available = true };
        }
        if (tag == .@"orelse" or tag == .@"catch") {
            const left, const right = tree.nodeData(node).node_and_node;
            const lhs = try self.walk(left, incoming, depth + 1);
            if (lhs.found) return lhs;
            const rhs = try self.walk(right, lhs, depth + 1);
            if (rhs.found) return rhs;
            return .{ .available = lhs.available and rhs.available };
        }
        if (tree.fullSwitch(node) != null) return .{};
        // Blocks and expressions execute children in order. A declaration
        // creates a new binding; assignments can change an alias or backing.
        var result = incoming;
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            result = try self.walk(child, result, depth + 1);
            if (result.found or !result.reaches) return result;
        }
        if (abrupt(tree, node)) return .{ .reaches = false };
        if (tag == .@"break" or tag == .@"continue") return .{};
        switch (tag) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div,
            .assign_mod, .assign_shl, .assign_shr, .assign_bit_and,
            .assign_bit_or, .assign_bit_xor, .assign_add_wrap,
            .assign_sub_wrap, .assign_mul_wrap, .assign_add_sat,
            .assign_sub_sat, .assign_mul_sat, .assign_shl_sat,
            => {
                // `_ = expression` discards a value without modifying storage.
                const lhs = tree.nodeData(node).node_and_node[0];
                if (tree.nodeTag(lhs) != .identifier or !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(lhs)), "_"))
                    result.available = false;
            },
            .@"defer", .@"errdefer", .@"switch", .switch_comma => result.available = false,
            else => {},
        }
        var call_buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&call_buffer, node)) |call| {
            if (result.available) {
                const effect = try self.cache.callEffectAt(tree.nodeMainToken(call.ast.fn_expr), .{ .whole = null }, .{ .remaining = &self.remaining });
                if (effect != .read_only) result.available = false;
            }
        }
        var builtin_buffer: [2]Ast.Node.Index = undefined;
        if (tree.builtinCallParams(&builtin_buffer, node) != null) result.available = false;
        return result;
    }
};

fn abrupt(tree: *const Ast, node: Ast.Node.Index) bool {
    return switch (tree.nodeTag(node)) {
        .@"return" => true,
        .@"break", .@"continue" => tree.tokens.items(.tag)[tree.nodeMainToken(node) + 1] != .colon,
        else => false,
    };
}

fn hasStableLookahead(cache: *file_cache_mod.FileCache, call_node: Ast.Node.Index) file_cache_mod.SummaryError!bool {
    const tree = cache.tree;
    const declaration = tokens.enclosingFnDecl(tree, tree.firstToken(call_node)) orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, call_node) orelse return false;
    if (tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
    const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
    if (tree.nodeTag(receiver) != .identifier) return false;
    const receiver_token = tree.nodeMainToken(receiver);
    const bindings = try cache.localBindings(proto, body);
    const binding = (bindings.findAt(tree.tokenSlice(receiver_token), receiver_token) orelse return false).*;
    var proof: Lookahead = .{
        .cache = cache,
        .proto = proto,
        .body = body,
        .target = call_node,
        .receiver_binding = binding.name_token,
        .first_result = null,
    };
    proof.first_result = try knownInitialResult(&proof, binding.rhs_first, binding.rhs_last);
    var opaque_nodes: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
    defer opaque_nodes.deinit(cache.gpa);
    const scan_bindings = (try cache.localBindings(proto, body)).*;
    var syntax = call_effects.Scan.init(tree, declaration, &scan_bindings);
    while (try syntax.next()) |event| {
        try proof.charge();
        switch (event) {
            .write_or_unknown => |unsupported| try opaque_nodes.append(cache.gpa, unsupported),
            .node => |visited| {
                const tag = tree.nodeTag(visited);
                if ((tag == .@"defer" or tag == .@"errdefer") and try proof.cleanupMayRunBeforeTarget(visited))
                    return false;
            },
            else => {},
        }
    }
    proof.opaque_nodes = opaque_nodes.items;
    const result = try proof.walk(body, .{}, 0);
    return result.found and result.available;
}

/// Read both exact declarations, not their method names. The consuming body
/// must be identical except for one scalar increment deferred until return.
fn equivalentObservation(proof: *Lookahead, tree: *const Ast, observed: Ast.Node.Index, consumed: Ast.Node.Index) file_cache_mod.SummaryError!bool {
    const read_body = tokens.bodyOf(tree, observed) orelse return false;
    const next_body = tokens.bodyOf(tree, consumed) orelse return false;
    var read_buffer: [1]Ast.Node.Index = undefined;
    var next_buffer: [1]Ast.Node.Index = undefined;
    const read_proto = tokens.fnProto(tree, &read_buffer, observed) orelse return false;
    const next_proto = tokens.fnProto(tree, &next_buffer, consumed) orelse return false;
    const read_name = tokens.firstParamName(tree, read_proto) orelse return false;
    const next_name = tokens.firstParamName(tree, next_proto) orelse return false;
    var reads = Iterator.init(tree, read_body);
    var nexts = Iterator.init(tree, next_body);
    var deferred = false;
    while (reads.next(tree)) |read_node| {
        try proof.charge();
        var next_node = nexts.next(tree) orelse return false;
        if (tree.nodeTag(next_node) == .@"defer") {
            if (deferred or !scalarDeferredAdvance(tree, next_node, next_name)) return false;
            deferred = true;
            next_node = nexts.next(tree) orelse return false;
            // Deferred mutation is accepted only immediately before the final
            // return. Earlier statements must have evaluated the same reads.
            if (tree.nodeTag(next_node) != .@"return") return false;
        }
        var left = tree.firstToken(read_node);
        var right = tree.firstToken(next_node);
        const left_end = tree.lastToken(read_node);
        const right_end = tree.lastToken(next_node);
        while (left <= left_end and right <= right_end) : ({
            left += 1;
            right += 1;
        }) {
            try proof.charge();
            const lhs = tree.tokenSlice(left);
            const rhs = tree.tokenSlice(right);
            const tags = tree.tokens.items(.tag);
            if (tags[left] == .identifier and tags[right] == .identifier and
                (left == 0 or tags[left - 1] != .period) and
                (right == 0 or tags[right - 1] != .period) and
                std.mem.eql(u8, lhs, read_name) and std.mem.eql(u8, rhs, next_name)) continue;
            if (tree.tokens.items(.tag)[left] != tree.tokens.items(.tag)[right] or !std.mem.eql(u8, lhs, rhs)) return false;
        }
        if (left <= left_end or right <= right_end) return false;
    }
    return deferred and nexts.next(tree) == null;
}

fn scalarDeferredAdvance(tree: *const Ast, node: Ast.Node.Index, receiver: []const u8) bool {
    const first = tree.firstToken(node);
    const last = tree.lastToken(node);
    const tags = tree.tokens.items(.tag);
    // `defer receiver.field += 1` has no call, address escape, or destructor.
    return (last == first + 5 or (last == first + 6 and tags[last] == .semicolon)) and tags[first] == .keyword_defer and
        tags[first + 1] == .identifier and std.mem.eql(u8, tree.tokenSlice(first + 1), receiver) and
        tags[first + 2] == .period and tags[first + 3] == .identifier and
        tags[first + 4] == .plus_equal and tags[first + 5] == .number_literal and
        std.mem.eql(u8, tree.tokenSlice(first + 5), "1");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    next_tok: Ast.TokenIndex,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`.next().?` force-unwraps the iterator result — if the iterator is exhausted, this panics (debug/safe) or invokes undefined behaviour (ReleaseFast); use `.next() orelse <handler>` or the `while (iter.next()) |val|` loop form instead",
        .{},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, next_tok),
        .end = try Pos.fromTokenEnd(tree, next_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "forced-unwrap-iterator-next: basic fires" {
    try testing.expectFires(check, R,
        \\fn readFirst(iter: anytype) u32 {
        \\    return iter.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: orelse does not fire" {
    try testing.expectNoFire(check,
        \\fn readFirst(iter: anytype) ?u32 {
        \\    return iter.next() orelse null;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: while loop does not fire" {
    try testing.expectNoFire(check,
        \\fn processAll(iter: anytype) void {
        \\    while (iter.next()) |val| {
        \\        _ = val;
        \\    }
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: next with arg does not fire" {
    try testing.expectNoFire(check,
        \\fn readFirst(iter: anytype) u32 {
        \\    return iter.next(1);
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: first next on splitScalar does not fire" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn firstField(text: []const u8) []const u8 {
        \\    var parts = std.mem.splitScalar(u8, text, ',');
        \\    return parts.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: second next on splitScalar still fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn secondField(text: []const u8) []const u8 {
        \\    var parts = std.mem.splitScalar(u8, text, ',');
        \\    const a = parts.next().?;
        \\    _ = a;
        \\    return parts.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: first next on tokenize still fires" {
    try testing.expectFires(check, R,
        \\fn firstTok(text: []const u8) []const u8 {
        \\    var it = std.mem.tokenizeScalar(u8, text, ',');
        \\    return it.next().?;
        \\}
        \\
    );
}

// ── Test-block suppression ──────────────────────────────────

test "forced-unwrap-iterator-next: suppressed inside named test block" {
    try testing.expectNoFire(check,
        \\test "iterates" {
        \\    var it = makeIter();
        \\    const first = it.next().?;
        \\    _ = first;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: suppressed inside anonymous test block" {
    try testing.expectNoFire(check,
        \\test {
        \\    var it = makeIter();
        \\    _ = it.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: suppressed inside nested braces of a test" {
    try testing.expectNoFire(check,
        \\test "nested" {
        \\    {
        \\        var it = makeIter();
        \\        _ = it.next().?;
        \\    }
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: still fires in fn after a test block" {
    try testing.expectFires(check, R,
        \\test "setup" {
        \\    var it = makeIter();
        \\    _ = it.next().?;
        \\}
        \\fn parse(iter: anytype) u32 {
        \\    return iter.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: still fires in fn before a test block" {
    try testing.expectFires(check, R,
        \\fn parse(iter: anytype) u32 {
        \\    return iter.next().?;
        \\}
        \\test "after" {
        \\    var it = makeIter();
        \\    _ = it.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: assert context suppressed" {
    try testing.expectNoFire(check,
        \\fn checkInvariant(it: *SomeIterator) void {
        \\    assert(it.next().? == expected_first);
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: non-assert call still fires" {
    try testing.expectFires(check, R,
        \\fn process(it: *SomeIterator) void {
        \\    log(it.next().?);
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: fn testXxx body suppressed" {
    try testing.expectNoFire(check,
        \\fn testParse(params: []const u16) Attribute {
        \\    var p: Parser = .{ .params = params };
        \\    return p.next().?;
        \\}
        \\
    );
}

test "forced-unwrap-iterator-next: fn not starting with test still fires" {
    try testing.expectFires(check, R,
        \\fn parse(p: *Parser) Attribute {
        \\    return p.next().?;
        \\}
        \\
    );
}

/// Give SDK fixtures the test compiler's complete target, not a guessed host.
/// The context owns the in-memory document; its configured path borrows this
/// frame's buffer through context teardown.
fn expectSdkArgumentProblems(count: usize, src: []const u8) !void {
    const type_engine = @import("type_engine");
    const gpa = std.testing.allocator;
    var context: type_engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();

    var path_buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const directory_len = try std.Io.Dir.cwd().realPathFile(std.testing.io, ".", &path_buffer);
    const separator = if (std.mem.endsWith(u8, path_buffer[0..directory_len], std.fs.path.sep_str)) "" else std.fs.path.sep_str;
    const document_name = try std.fmt.bufPrint(path_buffer[directory_len..], "{s}zbc-test-compiler-builtin.zig", .{separator});
    const document_path = path_buffer[0 .. directory_len + document_name.len];
    const uri: type_engine.Uri = try .fromPath(gpa, document_path);
    defer uri.deinit(gpa);
    try context.store.openLspSyncedDocument(uri, @embedFile("builtin"));
    context.store.config.builtin_path = document_path;

    var problems = try testing.runRuleTypedWithContext(gpa, check, src, &context);
    defer testing.freeProblems(gpa, &problems);
    try std.testing.expectEqual(count, problems.items.len);
    for (problems.items) |problem| try std.testing.expectEqualStrings(R, problem.rule_id);
}

test "forced-unwrap-iterator-next: second next on SDK argument vector still fires" {
    try expectSdkArgumentProblems(1,
        \\const std = @import("std");
        \\fn run() [:0]const u8 {
        \\    var args: std.process.Args.Iterator.Posix = .{ .remaining = &.{"exe"} };
        \\    _ = args.next();
        \\    return args.next().?;
        \\}
    );
}

const lookahead_fixture =
    \\const Cursor = struct {
    \\    data: []const u8,
    \\    index: usize = 0,
    \\    fn inspect(self: Cursor) ?u8 {
    \\        const data = self.data;
    \\        if (self.index >= data.len) return null;
    \\        return data[self.index];
    \\    }
    \\    fn next(self: *Cursor) ?u8 {
    \\        const data = self.data;
    \\        if (self.index >= data.len) return null;
    \\        defer self.index += 1;
    \\        return data[self.index];
    \\    }
    \\};
    \\
;

test "forced-unwrap-iterator-next: source equivalent lookahead proves one result" {
    try testing.expectNoFireTyped(check, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    const item = cursor.inspect() orelse return null;
        \\    if (item == 0) return null;
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: lookahead excludes a mutating continue branch" {
    try testing.expectNoFireTyped(check, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) void {
        \\    while (true) {
        \\        const item = cursor.inspect() orelse break;
        \\        if (item == 0) {
        \\            _ = cursor.next();
        \\            continue;
        \\        }
        \\        _ = cursor.next().?;
        \\    }
        \\}
    );
}

test "forced-unwrap-iterator-next: exhausted lookahead does not prove two results" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    _ = cursor.inspect() orelse return null;
        \\    _ = cursor.next();
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: reset invalidates lookahead" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    _ = cursor.inspect() orelse return null;
        \\    cursor.* = .{ .data = "" };
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: mutation invalidates lookahead" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    _ = cursor.inspect() orelse return null;
        \\    cursor.index += 1;
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: other receiver cannot transport lookahead" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(left: *Cursor, right: *Cursor) ?u8 {
        \\    _ = left.inspect() orelse return null;
        \\    return right.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: unknown call invalidates lookahead" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\extern fn unknown() void;
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    _ = cursor.inspect() orelse return null;
        \\    unknown();
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: extra argument mutation invalidates lookahead" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn mutate(value: u8, cursor: *Cursor) void {
        \\    _ = value;
        \\    cursor.index = cursor.data.len;
        \\}
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    const value = cursor.inspect() orelse return null;
        \\    mutate(value, cursor);
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: read only helper preserves lookahead" {
    try testing.expectNoFireTyped(check, lookahead_fixture ++
        \\fn identity(value: u8) u8 { return value; }
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    const value = cursor.inspect() orelse return null;
        \\    _ = identity(value);
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: count spelling alone proves nothing" {
    try testing.expectFiresTyped(check, R,
        \\const Cursor = struct {
        \\    fn count(_: Cursor) usize { return 1; }
        \\    fn next(_: *Cursor) ?u8 { return null; }
        \\};
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    if (cursor.count() != 0) return cursor.next().?;
        \\    return null;
        \\}
    );
}

test "forced-unwrap-iterator-next: ahead spelling alone proves nothing" {
    try testing.expectFiresTyped(check, R,
        \\const Cursor = struct {
        \\    fn ahead(_: Cursor) ?u8 { return 1; }
        \\    fn next(_: *Cursor) ?u8 { return null; }
        \\};
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    _ = cursor.ahead() orelse return null;
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: backing storage mutation invalidates lookahead" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn overwrite(data: []u8) void { data[0] = 0; }
        \\fn consume(cursor: *Cursor, alias: []u8) ?u8 {
        \\    _ = cursor.inspect() orelse return null;
        \\    overwrite(alias);
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: skipped boolean observation is not a guard" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(cursor: *Cursor, skip: bool) ?u8 {
        \\    _ = skip or ((cursor.inspect() orelse return null) == 0);
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: malformed producer and truncated field boundaries remain unknown" {
    const sources = .{
        // An empty producer record has no first token.
        \\const std = @import("std");
        \\fn readIndex(record: []const u8) []const u8 {
        \\    var fields = std.mem.tokenizeScalar(u8, record, ' ');
        \\    return fields.next().?;
        \\}
        ,
        // A successful leading column does not validate the required next one.
        \\const std = @import("std");
        \\fn readKind(record: []const u8) ?[]const u8 {
        \\    var fields = std.mem.tokenizeScalar(u8, record, ' ');
        \\    _ = fields.next() orelse return null;
        \\    return fields.next().?;
        \\}
        ,
        // A nonempty line can still be a truncated two-column producer record.
        \\const std = @import("std");
        \\fn readVersion(record: []const u8) void {
        \\    var fields = std.mem.tokenizeScalar(u8, record, ' ');
        \\    while (fields.next()) |name| {
        \\        _ = name;
        \\        _ = fields.next().?;
        \\    }
        \\}
        ,
    };
    inline for (sources) |source| {
        var problems = try testing.runRuleTyped(std.testing.allocator, check, source);
        defer testing.freeProblems(std.testing.allocator, &problems);
        try std.testing.expect(problems.items.len != 0);
        for (problems.items) |problem| {
            try std.testing.expectEqualStrings(R, problem.rule_id);
            try std.testing.expectEqual(problem_mod.Verdict.unknown, problem.verdict);
            try std.testing.expect(problem.witness == null);
        }
    }
}

test "forced-unwrap-iterator-next: labeled block exit does not prove observation" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    const item = value: {
        \\        break :value cursor.inspect() orelse break :value 0;
        \\    };
        \\    _ = item;
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: fresh observation after reset proves one result" {
    try testing.expectNoFireTyped(check, lookahead_fixture ++
        \\fn consume(cursor: *Cursor, text: []const u8) ?u8 {
        \\    cursor.* = .{ .data = text };
        \\    _ = cursor.inspect() orelse return null;
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: lookahead survives the unexecuted consuming branch" {
    try testing.expectNoFireTyped(check, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    const item = cursor.inspect() orelse return null;
        \\    if (item == 0) {
        \\        _ = cursor.next();
        \\    } else if (item == 1) {
        \\        return cursor.next().?;
        \\    }
        \\    return null;
        \\}
    );
}

test "forced-unwrap-iterator-next: reset to a different source does not replay a count" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(cursor: *Cursor, output: []u8) void {
        \\    var count: usize = 0;
        \\    while (cursor.next() != null) { count += 1; }
        \\    cursor.* = .{ .data = "" };
        \\    for (output[0..count]) |*value| value.* = cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: count mismatch does not certify a replay" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(cursor: *Cursor, output: []u8) void {
        \\    const initial = cursor.*;
        \\    var count: usize = 0;
        \\    while (cursor.next() != null) { count += 1; }
        \\    cursor.* = initial;
        \\    for (output[0 .. count + 1]) |*value| value.* = cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: destructuring invalidates lookahead" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    _ = cursor.inspect() orelse return null;
        \\    cursor.index, cursor.data = .{ 0, "" };
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: scope exit cleanup invalidates observed storage" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    {
        \\        defer cursor.index = cursor.data.len;
        \\        _ = cursor.inspect() orelse return null;
        \\    }
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: catch alternative does not establish a common guard" {
    try testing.expectFiresTyped(check, R, lookahead_fixture ++
        \\fn possible(fail: bool) error{Failed}!void {
        \\    if (fail) return error.Failed;
        \\}
        \\fn consume(cursor: *Cursor, fail: bool) ?u8 {
        \\    possible(fail) catch { _ = cursor.inspect() orelse return null; };
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: split lookalike does not certify a result" {
    try testing.expectFiresTyped(check, R,
        \\const Fake = struct {
        \\    fn splitScalar(_: type, _: []const u8, _: u8) Fake { return .{}; }
        \\    fn next(_: *Fake) ?u8 { return null; }
        \\};
        \\fn consume(text: []const u8) u8 {
        \\    var parts = Fake.splitScalar(u8, text, ',');
        \\    return parts.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: unknown call invalidates split constructor observation" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\extern fn unknown() void;
        \\fn consume(text: []const u8) []const u8 {
        \\    var parts = std.mem.splitScalar(u8, text, ',');
        \\    unknown();
        \\    return parts.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: split state mutation invalidates first result" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn consume(text: []const u8) []const u8 {
        \\    var parts = std.mem.splitScalar(u8, text, ',');
        \\    parts.index = null;
        \\    return parts.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: enclosing cleanup runs after the selected return value" {
    try testing.expectNoFireTyped(check, lookahead_fixture ++
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    defer cursor.index = cursor.data.len;
        \\    _ = cursor.inspect() orelse return null;
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: matching bodies from different declaration scopes do not prove equivalence" {
    try testing.expectFiresTyped(check, R,
        \\const Observation = struct {
        \\    const ready = true;
        \\    fn inspect(self: Cursor) ?u8 {
        \\        if (!ready) return null;
        \\        return self.data[0];
        \\    }
        \\};
        \\const Cursor = struct {
        \\    data: []const u8,
        \\    index: usize = 0,
        \\    const ready = false;
        \\    const inspect = Observation.inspect;
        \\    fn next(self: *Cursor) ?u8 {
        \\        if (!ready) return null;
        \\        defer self.index += 1;
        \\        return self.data[0];
        \\    }
        \\};
        \\fn consume(cursor: *Cursor) ?u8 {
        \\    _ = cursor.inspect() orelse return null;
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: renamed constructor source proves initial optional field" {
    try testing.expectNoFireTyped(check,
        \\const Cursor = struct {
        \\    position: ?usize,
        \\    fn build() Cursor { return .{ .position = 0 }; }
        \\    fn next(self: *Cursor) ?u8 {
        \\        const position = self.position orelse return null;
        \\        _ = position;
        \\        self.position = null;
        \\        return 7;
        \\    }
        \\};
        \\fn consume() u8 {
        \\    var cursor = Cursor.build();
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: initialized optional field does not exclude a later null return" {
    try testing.expectFiresTyped(check, R,
        \\const Cursor = struct {
        \\    position: ?usize,
        \\    fn build() Cursor { return .{ .position = 0 }; }
        \\    fn next(self: *Cursor) ?u8 {
        \\        const position = self.position orelse return null;
        \\        if (position == 0) return null;
        \\        self.position = null;
        \\        return 7;
        \\    }
        \\};
        \\fn consume() u8 {
        \\    var cursor = Cursor.build();
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: another initialized field cannot exclude the null exit" {
    try testing.expectFiresTyped(check, R,
        \\const Cursor = struct {
        \\    position: ?usize,
        \\    other: usize,
        \\    fn build() Cursor { return .{ .position = null, .other = 0 }; }
        \\    fn next(self: *Cursor) ?u8 {
        \\        const position = self.position orelse return null;
        \\        _ = position;
        \\        return 7;
        \\    }
        \\};
        \\fn consume() u8 {
        \\    var cursor = Cursor.build();
        \\    return cursor.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: empty SDK argument vector remains unproved" {
    try expectSdkArgumentProblems(1,
        \\const std = @import("std");
        \\fn run() [:0]const u8 {
        \\    var args: std.process.Args.Iterator.Posix = .{ .remaining = &.{} };
        \\    return args.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: runtime SDK argument vector has no argc guarantee" {
    try expectSdkArgumentProblems(1,
        \\const std = @import("std");
        \\fn run(input: std.process.Args.Vector) [:0]const u8 {
        \\    var args: std.process.Args.Iterator.Posix = .{ .remaining = input };
        \\    return args.next().?;
        \\}
    );
}

test "forced-unwrap-iterator-next: SDK argument vector without target context remains unproved" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\fn run() [:0]const u8 {
        \\    var args: std.process.Args.Iterator.Posix = .{ .remaining = &.{"exe"} };
        \\    return args.next().?;
        \\}
    );
}

const enum_selected_cursor_fixture =
    \\const Cursor = struct {
    \\    remaining: Input,
    \\    fn next(self: *Cursor) ?u8 {
    \\        if (self.remaining.len == 0) return null;
    \\        const result = self.remaining[0];
    \\        self.remaining = self.remaining[1..];
    \\        return result;
    \\    }
    \\};
    \\fn run() u8 {
    \\    var cursor: Cursor = .{ .remaining = &.{'x'} };
    \\    return cursor.next().?;
    \\}
;

test "forced-unwrap-iterator-next: canonical enum selector chooses explicit slice type" {
    try testing.expectNoFireTyped(check,
        \\const Mode = enum { bytes, disabled };
        \\const choice: Mode = .bytes;
        \\const Input = switch (choice) { .bytes => []const u8, else => void };
        \\
    ++ enum_selected_cursor_fixture);
}

test "forced-unwrap-iterator-next: immutable aggregate enum selector chooses fallback slice type" {
    try testing.expectNoFireTyped(check,
        \\const Mode = enum { bytes, disabled };
        \\const Config = struct { mode: Mode };
        \\const namespace = struct { const config: Config = .{ .mode = .bytes }; };
        \\const choice = namespace.config.mode;
        \\const Input = switch (choice) { .disabled => void, else => []const u8 };
        \\
    ++ enum_selected_cursor_fixture);
}
