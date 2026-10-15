//! Detects parser/visitor/scanner functions that call themselves recursively
//! without a stack-depth guard (`is_safe_to_recurse()` / `isSafeToRecurse()`
//! / `isStackOverflow()`).  Deeply nested input overflows the call stack.
//!
//! Real-world shape: oven-sh/bun#31361 (skip_typescript_type / skip_binding
//! without stack check), oven-sh/bun#31333 (visit_stmt / print_stmt /
//! print_if without stack check).
//!
//! Detection (Tier 1, per-fn body token walk):
//!   1. For each fn whose name contains "parse", "skip", "visit", or "scan"
//!      (case-insensitive prefix or word-boundary match), inspect its body.
//!   2. In the body, look for a self-recursive call:
//!      a. Method form: `period identifier(fn_name) l_paren`
//!      b. Bare form: `identifier(fn_name) l_paren` where the preceding token
//!         is NOT a `period` (not a method call on another receiver).
//!   3. Recognize entry increment/deferred decrement/refusal for one exact
//!      counter. A fallible helper is read through its canonical source.
//!   4. Retain explicit stack-check and older compatibility heuristics, but
//!      do not treat a recursion meter label or observation as a depth cap.
//!   5. Report a recursive call whose entry has no recognized guard.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const testing = @import("../../testing.zig");

const skipNestedFn = tokens.skipNestedFn;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "recursive-parse-fn-without-stack-check";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .recursive_parse_without_stack_check)) return;
    try tokens.forEachFnCached(gpa, tree, cache, problems, checkFn);
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    // Step 1: get fn name.
    const name_tok = proto.name_token orelse return;
    const fn_name = tree.tokenSlice(name_tok);

    // Step 2: fn name must match the recursive-parser heuristic.
    if (!isRecursiveParserName(fn_name)) return;

    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Step 3 (suppression): if any parameter is named "depth" or "max_depth",
    // the fn is almost certainly bounded by a depth counter.
    if (hasDepthParam(tree, proto)) return;

    // Step 4: find a self-recursive call in the body.
    // Extract the first non-comptime parameter name so the method-form detector
    // can distinguish `self.parse()` (recursive self-call) from calls on
    // other objects.  Comptime type parameters (e.g. `comptime T: type`) are
    // excluded — they are type-dispatch args, not self-receivers.
    //
    // Also: if the FIRST parameter is comptime, the function is a
    // compile-time generic dispatch (e.g. `fn parse(comptime T: type, …)`
    // or `fn parseKey(comptime check_export: bool, …)`).  Each instantiation
    // is a distinct function at runtime, so a call with a different comptime
    // argument is NOT a runtime recursive call — suppress.
    var first_param_name: ?[]const u8 = null;
    {
        const tok_tags = tree.tokens.items(.tag);
        var pit = proto.iterate(tree);
        if (pit.next()) |p| {
            const is_comptime = if (p.comptime_noalias) |cn|
                tok_tags[cn] == .keyword_comptime
            else
                false;
            if (is_comptime) return; // comptime-dispatch generic, not runtime recursion
            if (p.name_token) |nt| first_param_name = tree.tokenSlice(nt);
        }
    }
    const rec_tok = findRecursiveCall(tree, tags, first, last, fn_name, first_param_name) orelse return;

    // Account for the exact counter before this recursive edge. A helper is
    // read only through the canonical declaration and actual receiver.
    if (try hasCheckedCounter(cache, tree, first, rec_tok)) return;
    if (hasStackGuard(tags, tree, first, last)) return;
    if (hasVisitedSetGuard(tags, tree, first, last)) return;
    if (hasRecursionGuardToken(tags, tree, first, rec_tok)) return;


    try report(gpa, problems, tree, rec_tok, fn_name);
}

/// Recognize straight-line entry accounting, not a depth-like spelling.
fn hasCheckedCounter(cache: *file_cache_mod.FileCache, tree: *const Ast, first: Ast.TokenIndex, recursive_call: Ast.TokenIndex) !bool {
    const tags = tree.tokens.items(.tag);
    const start = first + 1;
    const entry_end = tokens.findStmtSemicolon(tags, start, recursive_call) orelse return false;
    const deferred = entry_end + 1;
    if (deferred >= recursive_call or tags[deferred] != .keyword_defer) return false;
    const end = tokens.findStmtSemicolon(tags, deferred + 1, recursive_call) orelse return false;
    if (end < deferred + 4 or tags[end - 2] != .minus_equal or
        tags[end - 1] != .number_literal or
        !std.mem.eql(u8, tree.tokenSlice(end - 1), "1")) return false;
    const counter_first = deferred + 1;
    const counter_last = end - 3;
    if (!isFieldPath(tree, counter_first, counter_last)) return false;
    if (counterRebound(tree, end + 1, recursive_call, counter_first, counter_last)) return false;
    if (sameTokens(tree, start, entry_end - 3, tree, counter_first, counter_last) and
        tags[entry_end - 2] == .plus_equal and
        std.mem.eql(u8, tree.tokenSlice(entry_end - 1), "1"))
        return rejectsCounter(tree, end + 1, recursive_call, counter_first, counter_last);

    // A fallible helper must precede the decrement on the same receiver.
    if (tags[start] != .keyword_try or start + 6 != entry_end or
        tags[start + 1] != .identifier or tags[start + 2] != .period or
        tags[start + 4] != .l_paren or tags[start + 5] != .r_paren) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(start + 1), tree.tokenSlice(counter_first))) return false;
    // Canonical calls are indexed by the dot, not the method-name token.
    const call = (try cache.actualCallSummaryAt(start + 2, null)) orelse return false;
    var actual_buffer: [2]Ast.Node.Index = undefined;
    const actual = (try call.callArgumentFor(cache, &actual_buffer, 0)) orelse return false;
    if (tree.nodeTag(actual) != .identifier or tree.nodeMainToken(actual) != start + 1) return false;
    const callee = call.callee;
    const body = tokens.bodyOf(callee.tree, callee.declaration) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(callee.tree, &buffer, callee.declaration) orelse return false;
    var parameters = proto.iterate(callee.tree);
    const receiver = (parameters.next() orelse return false).name_token orelse return false;
    if (parameters.next() != null) return false;
    const ct = callee.tree;
    const begin = ct.firstToken(body) + 1;
    const finish = ct.lastToken(body);
    const increment_end = tokens.findStmtSemicolon(ct.tokens.items(.tag), begin, finish) orelse return false;
    const width = counter_last - counter_first;
    if (increment_end != begin + width + 3 or
        ct.tokenTag(increment_end - 2) != .plus_equal or
        !std.mem.eql(u8, ct.tokenSlice(increment_end - 1), "1") or
        !std.mem.eql(u8, ct.tokenSlice(begin), ct.tokenSlice(receiver)) or
        !sameTokens(ct, begin + 1, increment_end - 3, tree, counter_first + 1, counter_last)) return false;
    if (!rejectsCounter(ct, increment_end + 1, finish, begin, increment_end - 3)) return false;
    // A successful helper must leave the checked increment in place. Work
    // after the refusal could reset it or replace the receiver.
    const guard_first = increment_end + 1;
    const guard_close = tokens.matchParen(ct.tokens.items(.tag), guard_first + 1, finish) orelse return false;
    const refusal = guard_close + 1;
    const guard_end = if (ct.tokenTag(refusal) == .l_brace)
        (tokens.matchBrace(ct.tokens.items(.tag), refusal, finish) orelse return false) + 1
    else
        refusal + 5;
    return guard_end == finish;
}

fn counterRebound(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex, cf: Ast.TokenIndex, cl: Ast.TokenIndex) bool {
    const width = cl - cf;
    var token = first;
    while (token + width + 1 < last) : (token += 1) {
        if (!sameTokens(tree, token, token + width, tree, cf, cl)) continue;
        switch (tree.tokenTag(token + width + 1)) {
            .equal, .minus_equal, .slash_equal, .asterisk_equal => return true,
            else => {},
        }
    }
    return false;
}

fn isFieldPath(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    if (first > last) return false;
    var token = first;
    while (token <= last) : (token += 1) {
        if (tree.tokenTag(token) != (if ((token - first) % 2 == 0)
            std.zig.Token.Tag.identifier else std.zig.Token.Tag.period)) return false;
    }
    return (last - first) % 2 == 0;
}

fn sameTokens(a: *const Ast, af: Ast.TokenIndex, al: Ast.TokenIndex, b: *const Ast, bf: Ast.TokenIndex, bl: Ast.TokenIndex) bool {
    if (af > al or bf > bl or al - af != bl - bf) return false;
    var offset: Ast.TokenIndex = 0;
    while (offset <= al - af) : (offset += 1) {
        if (a.tokenTag(af + offset) != b.tokenTag(bf + offset) or
            !std.mem.eql(u8, a.tokenSlice(af + offset), b.tokenSlice(bf + offset))) return false;
    }
    return true;
}

fn rejectsCounter(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex, cf: Ast.TokenIndex, cl: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    if (first + 2 >= last or tags[first] != .keyword_if or tags[first + 1] != .l_paren) return false;
    const close = tokens.matchParen(tags, first + 1, last) orelse return false;
    const comparison = first + 2 + (cl - cf + 1);
    if (comparison >= close or !sameTokens(tree, first + 2, comparison - 1, tree, cf, cl) or
        (tags[comparison] != .angle_bracket_right and tags[comparison] != .angle_bracket_right_equal)) return false;
    if (comparison + 2 != close and !isFieldPath(tree, comparison + 1, close - 1)) return false;
    if (comparison + 2 == close and tags[comparison + 1] != .number_literal and
        tags[comparison + 1] != .identifier) return false;
    var refusal = close + 1;
    if (refusal >= last) return false;
    if (tags[refusal] == .l_brace) {
        const block_end = tokens.matchBrace(tags, refusal, last) orelse return false;
        if (block_end < refusal + 6) return false;
        refusal = block_end - 5;
        if (tags[refusal - 1] != .semicolon and tags[refusal - 1] != .l_brace) return false;
    }
    return refusal + 4 < tags.len and tags[refusal] == .keyword_return and
        tags[refusal + 1] == .keyword_error and tags[refusal + 2] == .period and
        tags[refusal + 3] == .identifier and tags[refusal + 4] == .semicolon;
}

/// True iff `name` looks like a recursive parser/visitor/scanner fn name.
/// Matches names that start with (or contain a word-boundary before) one of
/// the keywords, case-insensitive:
///   "parse", "skip", "visit", "scan"
fn isRecursiveParserName(name: []const u8) bool {
    const keywords = [_][]const u8{ "parse", "skip", "visit", "scan" };
    for (keywords) |kw| {
        // Starts with the keyword (camelCase: parseFoo / snake_case: parse_foo).
        if (std.ascii.startsWithIgnoreCase(name, kw)) return true;
        // Word-boundary after underscore: "foo_parseFoo" or "foo_parse_bar".
        var i: usize = 0;
        while (i + kw.len <= name.len) : (i += 1) {
            if (i > 0 and name[i - 1] == '_' and
                std.ascii.eqlIgnoreCase(name[i .. i + kw.len], kw))
                return true;
        }
    }
    return false;
}

/// True iff the fn proto has a parameter named "depth" or "max_depth".
fn hasDepthParam(tree: *const Ast, proto: Ast.full.FnProto) bool {
    var iter = proto.iterate(tree);
    while (iter.next()) |param| {
        const name_tok = param.name_token orelse continue;
        const name = tree.tokenSlice(name_tok);
        if (std.mem.eql(u8, name, "depth") or
            std.mem.eql(u8, name, "max_depth") or
            std.mem.eql(u8, name, "nesting_depth") or
            std.mem.eql(u8, name, "level"))
            return true;
    }
    return false;
}

/// Scan `[first, last]` for a self-recursive call to `fn_name`.
/// Returns the token index of the recursive call identifier, or null.
///
/// Detects:
///   Method form: `period identifier(fn_name) l_paren`
///   Bare form:   `identifier(fn_name) l_paren` where t-1 != period
///
/// Suppression for method form:
///   - Multi-level qualified paths (`mod.sub.fn_name`) are skipped — they
///     refer to a different module's function, not a recursive self-call.
///   - The receiver (token before `.`) must be `self`, `this`, `ctx`, or
///     match `first_param_name` (the fn's own self parameter).  Any other
///     receiver (e.g. a local `parser` variable) is a different object.
fn findRecursiveCall(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    fn_name: []const u8,
    first_param_name: ?[]const u8,
) ?Ast.TokenIndex {
    if (first + 1 > last) return null;
    var t: Ast.TokenIndex = first;
    while (t + 1 <= last) : (t += 1) {
        // Skip nested fn definitions (they can have their own recursive calls
        // but that's a separate fn context).
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_paren) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), fn_name)) continue;

        // Method form: preceded by `.`
        if (t > first and tags[t - 1] == .period) {
            // Skip multi-level qualified paths: `mod.sub.NAME(…)`.
            // If t-3 is also `.`, this is `a.b.NAME` — a different module.
            if (t >= 3 and tags[t - 3] == .period) continue;
            // Skip generic/constructed receivers: `Type(T).NAME(…)`.
            // If t-2 is `)`, the receiver is a computed expression, not self.
            if (t >= 2 and tags[t - 2] == .r_paren) continue;
            // Require the receiver to match the fn's own self-parameter or a
            // conventional receiver name.  Other receivers are different objects.
            if (t >= 2 and tags[t - 2] == .identifier) {
                const recv = tree.tokenSlice(t - 2);
                const is_self =
                    std.mem.eql(u8, recv, "self") or
                    std.mem.eql(u8, recv, "this") or
                    std.mem.eql(u8, recv, "ctx") or
                    (first_param_name != null and std.mem.eql(u8, recv, first_param_name.?));
                if (!is_self) continue;
            }
            return t;
        }

        // Bare form: NOT preceded by `.`
        if (t == first or tags[t - 1] != .period) return t; // zbc-disable-line: index-minus-one-without-zero-guard — short-circuit or; t-1 only evaluated when t!=first, and t>first>=1
    }
    return null;
}

/// True iff the range `[first, last]` contains a call to any of the
/// recognised stack-depth guard functions.
fn hasStackGuard(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (first + 1 > last) return false;
    var t: Ast.TokenIndex = first;
    while (t + 1 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .l_paren) continue;
        const name = tree.tokenSlice(t);
        if (isStackGuardName(name)) return true;
    }
    return false;
}

/// True iff `[first, last]` contains a visited-set membership guard — an
/// access of the form `<visited-ish>.<membership-method>(`, e.g.
/// `self.visited.isSet(i)`, `seen.contains(x)`, `visiting.getOrPut(n)`.
/// Such a guard means the recursion walks a finite graph (visiting each node
/// at most once) rather than descending attacker-controlled input nesting.
fn hasVisitedSetGuard(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (first + 2 > last) return false;
    var t: Ast.TokenIndex = first;
    while (t + 2 <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (tags[t + 1] != .period) continue;
        if (tags[t + 2] != .identifier) continue;
        const set_name = tree.tokenSlice(t);
        const is_visited_set =
            std.ascii.findIgnoreCase(set_name, "visited") != null or
            std.ascii.findIgnoreCase(set_name, "visiting") != null or
            std.ascii.findIgnoreCase(set_name, "visits") != null or
            std.ascii.findIgnoreCase(set_name, "seen") != null;
        if (!is_visited_set) continue;
        const method = tree.tokenSlice(t + 2);
        if (std.mem.eql(u8, method, "isSet") or
            std.mem.eql(u8, method, "contains") or
            std.mem.eql(u8, method, "get") or
            std.mem.eql(u8, method, "getOrPut") or
            std.mem.eql(u8, method, "has") or
            std.mem.eql(u8, method, "exists") or
            std.mem.eql(u8, method, "lookup")) return true;
    }
    return false;
}

/// Retain existing explicit recursion entry/exit compatibility, but a meter
/// label or observation is not a recursion limit.
fn hasRecursionGuardToken(
    tags: []const std.zig.Token.Tag,
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        if (tags[t] != .identifier) continue;
        const name = tree.tokenSlice(t);
        if (std.mem.eql(u8, name, "enterRecursion") and t + 1 <= last and tags[t + 1] == .l_paren) return true;
        if (std.ascii.findIgnoreCase(name, "recursion") == null or t + 1 > last) continue;
        if (tags[t + 1] != .angle_bracket_right and tags[t + 1] != .angle_bracket_right_equal) continue;
        var end = t + 2;
        while (end < last and tags[end] != .r_paren) : (end += 1) {}
        if (end + 1 < last and tags[end + 1] == .keyword_return) return true;
    }
    return false;
}

fn isStackGuardName(name: []const u8) bool {
    return std.mem.eql(u8, name, "is_safe_to_recurse") or
        std.mem.eql(u8, name, "isSafeToRecurse") or
        std.mem.eql(u8, name, "isStackOverflow") or
        std.mem.eql(u8, name, "safeRecurse") or
        std.mem.eql(u8, name, "checkStack") or
        std.mem.eql(u8, name, "checkRecursion") or
        std.mem.eql(u8, name, "stackOverflow");
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    call_tok: Ast.TokenIndex,
    fn_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`{s}` calls itself recursively without a stack-depth guard — deeply nested input will overflow the call stack; add `if (!stack_check.is_safe_to_recurse()) return error.StackOverflow;` at the top of the function",
        .{fn_name},
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, call_tok),
        .end = try Pos.fromTokenEnd(tree, call_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "recursive-parse-fn-without-stack-check: bare recursive parse call fires" {
    try testing.expectFires(check, R,
        \\const Parser = struct {
        \\    pub fn parseExpr(p: *Parser) !void {
        \\        _ = try parseExpr(p);
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: method recursive call fires" {
    try testing.expectFires(check, R,
        \\const Parser = struct {
        \\    pub fn parseExpr(p: *Parser) !void {
        \\        _ = try p.parseExpr();
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: skip fn without guard fires" {
    try testing.expectFires(check, R,
        \\const Parser = struct {
        \\    pub fn skipType(p: *Parser) void {
        \\        p.skipType();
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: visit fn without guard fires" {
    try testing.expectFires(check, R,
        \\const V = struct {
        \\    pub fn visitNode(self: *V) void {
        \\        self.visitNode();
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: recursive fn with is_safe_to_recurse guard does not fire" {
    try testing.expectNoFire(check,
        \\const Parser = struct {
        \\    pub fn parseExpr(p: *Parser) !void {
        \\        if (!p.stack_check.is_safe_to_recurse()) return error.StackOverflow;
        \\        _ = try p.parseExpr();
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: recursive fn with depth param does not fire" {
    try testing.expectNoFire(check,
        \\const Parser = struct {
        \\    pub fn parseExpr(p: *Parser, depth: u32) !void {
        \\        _ = try p.parseExpr(depth + 1);
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: non-recursive parse fn does not fire" {
    try testing.expectNoFire(check,
        \\const Parser = struct {
        \\    pub fn parseExpr(p: *Parser) !void {
        \\        _ = try p.parseToken();
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: non-parser fn does not fire" {
    try testing.expectNoFire(check,
        \\const Allocator = struct {
        \\    pub fn allocate(a: *Allocator) !void {
        \\        _ = try a.allocate();
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: graph visitor with visited-set guard does not fire" {
    try testing.expectNoFire(check,
        \\const Graph = struct {
        \\    pub fn visit(self: *Graph, index: usize) void {
        \\        if (self.visited.isSet(index)) return;
        \\        self.visited.set(index);
        \\        for (self.edges[index]) |e| self.visit(e);
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: visitor with seen.contains guard does not fire" {
    try testing.expectNoFire(check,
        \\const Walker = struct {
        \\    pub fn visitNode(self: *Walker, n: *Node) void {
        \\        if (self.seen.contains(n)) return;
        \\        self.visitNode(n.child);
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: enterRecursion() guard does not fire" {
    try testing.expectNoFire(check,
        \\const Parser = struct {
        \\    pub fn parseStatement(self: *Parser) !void {
        \\        try self.enterRecursion();
        \\        defer self.leaveRecursion();
        \\        return self.parseStatement();
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: inline recursion_depth field cap does not fire" {
    try testing.expectNoFire(check,
        \\const Parser = struct {
        \\    pub fn parseType(p: *Parser) !void {
        \\        if (p.recursion_depth >= 400) return error.NestingTooDeep;
        \\        p.recursion_depth += 1;
        \\        defer p.recursion_depth -= 1;
        \\        return p.parseType();
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: scan fn without guard fires" {
    try testing.expectFires(check, R,
        \\const Lexer = struct {
        \\    pub fn scanToken(l: *Lexer) void {
        \\        l.scanToken();
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: comptime type dispatch does not fire" {
    // `fn parse(comptime T: type, …)` — each call instantiates a DIFFERENT
    // function at compile time; there is no runtime recursion.
    try testing.expectNoFire(check,
        \\pub inline fn parse(comptime T: type, input: *Parser) Result(T) {
        \\    if (comptime @typeInfo(T) == .pointer) {
        \\        const TT = std.meta.Child(T);
        \\        return switch (parse(TT, input)) {
        \\            .result => |v| .{ .result = v },
        \\            .err => |e| .{ .err = e },
        \\        };
        \\    }
        \\    return .{ .result = undefined };
        \\}
        \\
    );
}

test "recursive-parse-fn-without-stack-check: comptime bool as first param does not fire" {
    // `fn parseKey(comptime check_export: bool, …)` with comptime FIRST —
    // each instantiation is a distinct function; calling with false != true.
    try testing.expectNoFire(check,
        \\pub fn parseKey(comptime check_export: bool, input: *Parser) ?[]const u8 {
        \\    if (comptime check_export) {
        \\        return parseKey(false, input);
        \\    }
        \\    return null;
        \\}
        \\
    );
}

test "recursive-parse-fn-without-stack-check: visits.isSet guard does not fire" {
    // Variable named 'visits' (plural) should suppress like 'visited'.
    try testing.expectNoFire(check,
        \\const Walker = struct {
        \\    pub fn visit(self: *Walker, index: u32, visits: *BitSet) void {
        \\        if (visits.isSet(index)) return;
        \\        visits.set(index);
        \\        self.visit(index + 1, visits);
        \\    }
        \\};
        \\
    );
}

test "recursive-parse-fn-without-stack-check: checked field counter bounds declarator descent" {
    try testing.expectNoFire(check,
        \\const P = struct {
        \\    fn parseDeclarator(self: *P) !void {
        \\        self.depth += 1;
        \\        defer self.depth -= 1;
        \\        if (self.depth > self.limits.maximum) {
        \\            try self.report();
        \\            return error.TooDeep;
        \\        }
        \\        try self.parseDeclarator();
        \\    }
        \\};
    );
}

test "recursive-parse-fn-without-stack-check: counter without refusal remains visible" {
    try testing.expectFires(check, R,
        \\const P = struct {
        \\    fn scanStatement(self: *P) !void {
        \\        self.depth += 1;
        \\        defer self.depth -= 1;
        \\        try self.observe(.recursion_depth, self.depth);
        \\        try self.scanStatement();
        \\    }
        \\};
    );
}

test "recursive-parse-fn-without-stack-check: exact helper checks same counter" {
    try testing.expectNoFireTyped(check,
        \\const P = struct {
        \\    depth: u32 = 0,
        \\    maximum: u32 = 64,
        \\    fn enter(self: *P) !void {
        \\        self.depth += 1;
        \\        if (self.depth > self.maximum) return error.TooDeep;
        \\    }
        \\    fn parseUnary(self: *P) !void {
        \\        try self.enter();
        \\        defer self.depth -= 1;
        \\        try self.parseUnary();
        \\    }
        \\};
    );
}

test "recursive-parse-fn-without-stack-check: byte bound does not bound variant depth" {
    try testing.expectFires(check, R,
        \\fn skipTypedValue(reader: *Reader, signature: []const u8) !void {
        \\    if (reader.bytes.len > 4 * 1024 * 1024) return error.TooLarge;
        \\    const nested = try reader.signature();
        \\    try skipTypedValue(reader, nested);
        \\    _ = signature;
        \\}
    );
}

test "recursive-parse-fn-without-stack-check: unguarded entry helper is not a limit" {
    try testing.expectFiresTyped(check, R,
        \\const P = struct {
        \\    depth: u32 = 0,
        \\    fn enter(self: *P) !void { self.depth += 1; }
        \\    fn parseUnary(self: *P) !void {
        \\        try self.enter();
        \\        defer self.depth -= 1;
        \\        try self.parseUnary();
        \\    }
        \\};
    );
}

test "recursive-parse-fn-without-stack-check: fresh body counter and cycle check do not cap caller chain" {
    try testing.expectFires(check, R,
        \\const State = struct {
        \\    fn scanStatement(self: *State, declaration: u32) !void {
        \\        if (self.walking.contains(declaration)) return;
        \\        var nested = State{ .depth = 0 };
        \\        try self.meter.observe(.recursion_depth, nested.depth + 1);
        \\        try self.scanStatement(declaration + 1);
        \\    }
        \\};
    );
}

test "recursive-parse-fn-without-stack-check: larger frame does not cap nested portal variants" {
    try testing.expectFires(check, R,
        \\fn skipTypedValue(reader: *Reader, signature: []const u8) !void {
        \\    if (reader.frameSize() > 8 * 1024 * 1024) return error.FrameTooLarge;
        \\    switch (signature[0]) {
        \\        'v' => {
        \\            const nested = try reader.signature();
        \\            return skipTypedValue(reader, nested);
        \\        },
        \\        else => return,
        \\    }
        \\}
    );
}

test "recursive-parse-fn-without-stack-check: reset counter invalidates entry limit" {
    try testing.expectFires(check, R,
        \\const P = struct {
        \\    fn parseUnary(self: *P) !void {
        \\        self.depth += 1;
        \\        defer self.depth -= 1;
        \\        if (self.depth > self.maximum) return error.TooDeep;
        \\        self.depth = 0;
        \\        try self.parseUnary();
        \\    }
        \\};
    );
}

test "recursive-parse-fn-without-stack-check: helper formal maps to caller receiver" {
    try testing.expectNoFireTyped(check,
        \\const P = struct {
        \\    count: u32 = 0,
        \\    maximum: u32 = 64,
        \\    fn acquire(entry: *P) !void {
        \\        entry.count += 1;
        \\        if (entry.count > entry.maximum) return error.TooDeep;
        \\    }
        \\    fn parseUnary(parser: *P) !void {
        \\        try parser.acquire();
        \\        defer parser.count -= 1;
        \\        try parser.parseUnary();
        \\    }
        \\};
    );
}

test "recursive-parse-fn-without-stack-check: helper checks another field" {
    try testing.expectFiresTyped(check, R,
        \\const P = struct {
        \\    count: u32 = 0,
        \\    other: u32 = 0,
        \\    maximum: u32 = 64,
        \\    fn acquire(entry: *P) !void {
        \\        entry.other += 1;
        \\        if (entry.other > entry.maximum) return error.TooDeep;
        \\    }
        \\    fn parseUnary(parser: *P) !void {
        \\        try parser.acquire();
        \\        defer parser.count -= 1;
        \\        try parser.parseUnary();
        \\    }
        \\};
    );
}

test "recursive-parse-fn-without-stack-check: helper resets counter after checking" {
    try testing.expectFiresTyped(check, R,
        \\const P = struct {
        \\    count: u32 = 0,
        \\    maximum: u32 = 64,
        \\    fn acquire(entry: *P) !void {
        \\        entry.count += 1;
        \\        if (entry.count > entry.maximum) return error.TooDeep;
        \\        entry.count = 0;
        \\    }
        \\    fn parseUnary(parser: *P) !void {
        \\        try parser.acquire();
        \\        defer parser.count -= 1;
        \\        try parser.parseUnary();
        \\    }
        \\};
    );
}

test "recursive-parse-fn-without-stack-check: checked helper on another receiver is not a guard" {
    try testing.expectFiresTyped(check, R,
        \\const P = struct {
        \\    count: u32 = 0,
        \\    maximum: u32 = 64,
        \\    fn acquire(entry: *P) !void {
        \\        entry.count += 1;
        \\        if (entry.count > entry.maximum) return error.TooDeep;
        \\    }
        \\    fn parseUnary(parser: *P, other: *P) !void {
        \\        try other.acquire();
        \\        defer parser.count -= 1;
        \\        try parser.parseUnary(other);
        \\    }
        \\};
    );
}
