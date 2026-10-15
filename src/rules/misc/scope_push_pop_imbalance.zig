//! Detects parser functions that push a scope (pushScope, enterScope, etc.)
//! without a matching `defer pop` — early returns leave the scope stack
//! unbalanced.  Real-world shape: oven-sh/bun#31239 / #31340 / #31231.
//!
//! Push/pop names select candidates. Directly returned acquisitions belong
//! to the caller. Immediate error rollback additionally requires matching
//! receiver/key arguments and inverse counter mutations in the resolved
//! source bodies. Other lifetime transfers require separate source proof.
//! The older lexical-defer and function-name heuristics remain conservative
//! compatibility behavior; neither is a general ownership certificate.

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
    cache: *file_cache_mod.FileCache,
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
    // The acquisition itself is the returned value, not a scope kept by this
    // activation. Do not mistake a discarded acquisition for this transfer.
    if (try returnsAcquisition(cache, tree, push_tok, first, last)) return;
    if (try hasMatchingRollback(cache, tree, push_tok, first, last)) return;

    // Step 2: check for a defer that contains a pop call.
    if (hasDeferPop(tags, tree, first, last)) return;

    // Step 3: check for at least one `return` in the body (multiple exit paths).
    if (!hasReturn(tags, first, last)) return;

    try report(gpa, problems, tree, push_tok);
}

fn returnsAcquisition(cache: *file_cache_mod.FileCache, tree: *const Ast, push: Ast.TokenIndex, first: Ast.TokenIndex, last: Ast.TokenIndex) !bool {
    // The lexical finder returns the method name. The call index uses the dot.
    const query = push - 1;
    const call = (try cache.getCallIndex()).by_callee_token.get(query) orelse return false;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .@"return") continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        const token = tree.nodeMainToken(node);
        if (token <= first or token >= last) continue;
        const returned = tree.nodeData(node).opt_node.unwrap() orelse continue;
        if (returned != call) continue;
        const canonical = (try cache.actualCallSummaryAt(query, null)) orelse return false;
        return canonical.callee.call_node == call and
            tokens.bodyOf(canonical.callee.tree, canonical.callee.declaration) != null;
    }
    return false;
}

/// Error rollback must name the same receiver and the same key arguments.
/// A pop on another process or another stack cannot settle this acquisition.
fn hasMatchingRollback(cache: *file_cache_mod.FileCache, tree: *const Ast, push: Ast.TokenIndex, first: Ast.TokenIndex, last: Ast.TokenIndex) !bool {
    const tags = tree.tokens.items(.tag);
    if (push < first + 2) return false;
    const prefix_end = push - 2;
    var prefix_first = prefix_end;
    while (prefix_first > first + 1 and
        (tags[prefix_first - 1] == .period or tags[prefix_first - 1] == .identifier))
        prefix_first -= 1;
    const push_end = tokens.matchParen(tags, push + 1, last) orelse return false;
    const statement_end = tokens.findStmtSemicolon(tags, push_end + 1, last) orelse return false;
    var token = statement_end + 1;
    // Comments are not tokens; the rollback must be the next statement.
    if (token >= last or tags[token] != .keyword_errdefer) return false;
    const rollback_end = tokens.skipDeferStmt(tags, token, last) orelse return false;
    while (token + 2 < rollback_end) : (token += 1) {
        if (tags[token] != .period or tags[token + 1] != .identifier or tags[token + 2] != .l_paren or
            !method_names.isScopePopMethodName(tree.tokenSlice(token + 1))) continue;
        const width = prefix_end - prefix_first + 1;
        if (token < width) continue;
        var offset: Ast.TokenIndex = 0;
        while (offset < width and std.mem.eql(u8,
            tree.tokenSlice(prefix_first + offset), tree.tokenSlice(token - width + offset))) : (offset += 1) {}
        if (offset != width) continue;
        const pop_end = tokens.matchParen(tags, token + 2, rollback_end) orelse continue;
        const args_first = token + 3;
        const args_len = pop_end - args_first;
        if (push + 2 + args_len > push_end) continue;
        offset = 0;
        while (offset < args_len and std.mem.eql(u8,
            tree.tokenSlice(args_first + offset), tree.tokenSlice(push + 2 + offset))) : (offset += 1) {}
        if (offset == args_len and (push + 2 + args_len == push_end or tags[push + 2 + args_len] == .comma))
            return try inverseCounterMutation(cache, push, token + 1);
    }
    return false;
}

/// A rollback name only selects a candidate. The resolved declarations must
/// apply opposite unit mutations to the same parameter-rooted counter.
fn inverseCounterMutation(cache: *file_cache_mod.FileCache, push: Ast.TokenIndex, pop: Ast.TokenIndex) !bool {
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    const acquisition = (try cache.actualCallSummaryAt(push - 1, null)) orelse return false;
    const rollback = (try cache.actualCallSummaryAt(pop - 1, null)) orelse return false;
    if (acquisition.callee.tree != rollback.callee.tree or
        acquisition.callee.handle.module != rollback.callee.handle.module) return false;
    const tree = acquisition.callee.tree;
    const a_body = tokens.bodyOf(tree, acquisition.callee.declaration) orelse return false;
    const b_body = tokens.bodyOf(tree, rollback.callee.declaration) orelse return false;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .assign_add) continue;
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.firstToken(node) <= tree.firstToken(a_body) or tree.lastToken(node) >= tree.lastToken(a_body)) continue;
        try cache.chargeNormalCleanupAt(tree, node);
        if (!normalPathsReachMutation(tree, a_body, node) or !singleMutationBody(tree, a_body, node)) continue;
        const a = tree.nodeData(node).node_and_node;
        if (tree.nodeTag(a[1]) != .number_literal or
            !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(a[1])), "1")) continue;
        for (tree.nodes.items(.tag), 0..) |other_tag, other_index| {
            if (other_tag != .assign_sub) continue;
            const other: Ast.Node.Index = @enumFromInt(other_index);
            if (tree.firstToken(other) <= tree.firstToken(b_body) or tree.lastToken(other) >= tree.lastToken(b_body)) continue;
            try cache.chargeNormalCleanupAt(tree, other);
            if (!normalPathsReachMutation(tree, b_body, other) or !singleMutationBody(tree, b_body, other)) continue;
            const b = tree.nodeData(other).node_and_node;
            if (tree.nodeTag(b[1]) != .number_literal or
                !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(b[1])), "1")) continue;
            if (try sameCounterCalls(cache, acquisition, rollback, a[0], b[0], 0)) return true;
        }
    }
    return false;
}

/// The mutation must be in the function's outer block. Earlier explicit
/// returns may refuse the operation, but may not publish a successful result.
fn normalPathsReachMutation(tree: *const Ast, body: Ast.Node.Index, mutation: Ast.Node.Index) bool {
    var buffer: [2]Ast.Node.Index = undefined;
    const statements = switch (tree.nodeTag(body)) {
        .block, .block_semicolon => tree.extraDataSlice(tree.nodeData(body).extra_range, Ast.Node.Index),
        .block_two, .block_two_semicolon => blk: {
            const pair = tree.nodeData(body).opt_node_and_opt_node;
            var count: usize = 0;
            inline for (pair) |optional| {
                if (optional.unwrap()) |statement| {
                    buffer[count] = statement;
                    count += 1;
                }
            }
            break :blk buffer[0..count];
        },
        else => return false,
    };
    var outer_statement = false;
    for (statements) |statement| {
        if (statement == mutation) outer_statement = true;
    }
    if (!outer_statement) return false;
    const tags = tree.tokens.items(.tag);
    const limit = tree.firstToken(mutation);
    var depth: u32 = 0;
    var token = tree.firstToken(body);
    while (token < limit) : (token += 1) {
        switch (tags[token]) {
            .l_brace => depth += 1,
            .r_brace => {
                if (depth == 0) return false;
                depth -= 1;
            },
            .keyword_fn => token = skipNestedFn(tags, token, limit),
            .keyword_return => if (token + 2 >= limit or tags[token + 1] != .keyword_error or tags[token + 2] != .period) return false,
            else => {},
        }
    }
    return depth == 1;
}

/// Compare field projections, then map each formal root into the original
/// caller. Equal parameter spellings are not an actual-object identity.
fn sameCounterCalls(cache: *file_cache_mod.FileCache, acquisition: file_cache_mod.FileCache.ActualCallSummary, rollback: file_cache_mod.FileCache.ActualCallSummary, a: Ast.Node.Index, b: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
    if (depth >= 64) return false;
    const tree = acquisition.callee.tree;
    try cache.chargeNormalCleanupAt(tree, a);
    const tag = tree.nodeTag(a);
    if (tag != tree.nodeTag(b)) return false;
    switch (tag) {
        .field_access => {
            const a_base, const a_field = tree.nodeData(a).node_and_token;
            const b_base, const b_field = tree.nodeData(b).node_and_token;
            if (!std.mem.eql(u8, tree.tokenSlice(a_field), tree.tokenSlice(b_field))) return false;
            return sameCounterCalls(cache, acquisition, rollback, a_base, b_base, depth + 1);
        },
        .deref => return sameCounterCalls(cache, acquisition, rollback, tree.nodeData(a).node, tree.nodeData(b).node, depth + 1),
        .identifier => {
            const a_parameter = formalRoot(tree, acquisition.callee.declaration, tree.nodeMainToken(a)) orelse return false;
            const b_parameter = formalRoot(tree, rollback.callee.declaration, tree.nodeMainToken(b)) orelse return false;
            var a_buffer: [2]Ast.Node.Index = undefined;
            var b_buffer: [2]Ast.Node.Index = undefined;
            const a_actual = (try acquisition.callArgumentFor(cache, &a_buffer, a_parameter)) orelse return false;
            const b_actual = (try rollback.callArgumentFor(cache, &b_buffer, b_parameter)) orelse return false;
            return stableActual(cache.tree, a_actual, 0) and stableActual(cache.tree, b_actual, 0) and
                std.mem.eql(u8, cache.tree.getNodeSource(a_actual), cache.tree.getNodeSource(b_actual));
        },
        // A helper returning a counter address needs separate return-provenance
        // proof. Its canonical declaration alone cannot prove a stable object.
        else => return false,
    }
}

fn formalRoot(tree: *const Ast, declaration: Ast.Node.Index, name: Ast.TokenIndex) ?u32 {
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
    var parameters = proto.iterate(tree);
    var ordinal: u32 = 0;
    while (parameters.next()) |parameter| : (ordinal += 1) {
        if (std.mem.eql(u8, tree.tokenSlice(parameter.name_token orelse continue), tree.tokenSlice(name))) return ordinal;
    }
    return null;
}

fn stableActual(tree: *const Ast, node: Ast.Node.Index, depth: u32) bool {
    if (depth >= 64) return false;
    return switch (tree.nodeTag(node)) {
        .identifier => true,
        .field_access => stableActual(tree, tree.nodeData(node).node_and_token[0], depth + 1),
        .address_of, .deref => stableActual(tree, tree.nodeData(node).node, depth + 1),
        .grouped_expression => stableActual(tree, tree.nodeData(node).node_and_token[0], depth + 1),
        else => false,
    };
}

/// No second write or unknown call may change the claimed unit effect.
fn singleMutationBody(tree: *const Ast, body: Ast.Node.Index, mutation: Ast.Node.Index) bool {
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (node == mutation or tree.firstToken(node) <= tree.firstToken(body) or
            tree.lastToken(node) >= tree.lastToken(body)) continue;
        if (std.mem.startsWith(u8, @tagName(tag), "assign")) {
            if (tag == .assign) {
                const lhs = tree.nodeData(node).node_and_node[0];
                if (tree.nodeTag(lhs) == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(lhs)), "_")) continue;
            }
            return false;
        }
        var buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&buffer, node) != null or std.mem.startsWith(u8, @tagName(tag), "builtin_call")) return false;
    }
    return true;
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

test "scope-push-pop-imbalance: returning acquisition transfers handle" {
    try testing.expectNoFireTyped(check,
        \\const ScopeId = enum { none, block };
        \\const Scopes = struct {
        \\    fn openScope(_: *Scopes, _: struct { parent: ?ScopeId }) ScopeId { return .block; }
        \\};
        \\const Run = struct {
        \\    stack: Scopes,
        \\    fn tick(_: *Run) !void {}
        \\    fn scopes(self: *Run) *Scopes { return &self.stack; }
        \\};
        \\fn openRegion(run: *Run) !ScopeId {
        \\    try run.tick();
        \\    return run.scopes().openScope(.{ .parent = null });
        \\}
    );
}

test "scope-push-pop-imbalance: discarded acquisition is not returned ownership" {
    try testing.expectFires(check, R,
        \\fn openRegion(run: *Run) !ScopeId {
        \\    _ = try run.scopes().openScope(.{ .parent = null });
        \\    try run.tick();
        \\    return .none;
        \\}
    );
}

test "scope-push-pop-imbalance: rollback on acquired frame protects errors" {
    try testing.expectNoFireTyped(check,
        \\const Runtime = struct { state: State, entry: u32, fn publish(_: *Runtime, _: u32) !void {} };
        \\const State = struct { depth: u32 = 0 };
        \\const ProcessId = u32;
        \\const Node = u32;
        \\const Interpreter = struct {
        \\    fn pushFrame(state: *State, process: ProcessId) !u32 { state.depth += 1; return process; }
        \\    fn popFrame(state: *State, process: ProcessId) !void { state.depth -= 1; _ = process; }
        \\};
        \\fn enter(runtime: *Runtime, process: ProcessId) !Node {
        \\    const frame = try Interpreter.pushFrame(&runtime.state, process);
        \\    errdefer _ = Interpreter.popFrame(&runtime.state, process) catch {};
        \\    try runtime.publish(frame);
        \\    return runtime.entry;
        \\}
    );
}

test "scope-push-pop-imbalance: rollback for another process does not balance frame" {
    try testing.expectFires(check, R,
        \\fn enter(runtime: *Runtime, process: ProcessId, other: ProcessId) !Node {
        \\    const frame = try Interpreter.pushFrame(&runtime.state, process);
        \\    errdefer _ = Interpreter.popFrame(&runtime.state, other) catch {};
        \\    try runtime.publish(frame);
        \\    return runtime.entry;
        \\}
    );
}

test "scope-push-pop-imbalance: fallible work before borrowed frame release stays visible" {
    try testing.expectFires(check, R,
        \\fn upload(source: *Source, descriptor: Frame, report: *Report) !void {
        \\    try source.pushFrame(descriptor);
        \\    var acquired = source.acquireLatest() orelse return error.Empty;
        \\    try report.emit();
        \\    try uploadProbe(acquired);
        \\    source.releaseFrame(&acquired);
        \\}
    );
}

test "scope-push-pop-imbalance: conditional counter rollback is not a complete cleanup" {
    try testing.expectFiresTyped(check, R,
        \\const S = struct {
        \\    depth: u32 = 0,
        \\    enabled: bool = false,
        \\    fn pushFrame(self: *S) !u32 { self.depth += 1; return self.depth; }
        \\    fn popFrame(self: *S) void { if (self.enabled) { self.depth -= 1; } }
        \\    fn parse(self: *S) !u32 {
        \\        const frame = try self.pushFrame();
        \\        errdefer self.popFrame();
        \\        try opaqueWork();
        \\        return frame;
        \\    }
        \\};
    );
}

test "scope-push-pop-imbalance: renamed rollback formal maps to same actual counter" {
    try testing.expectNoFireTyped(check,
        \\const S = struct {
        \\    depth: u32 = 0,
        \\    fn pushFrame(acquired: *S) !u32 { acquired.depth += 1; return acquired.depth; }
        \\    fn popFrame(released: *S) void { released.depth -= 1; }
        \\    fn parse(self: *S) !u32 {
        \\        const frame = try self.pushFrame();
        \\        errdefer self.popFrame();
        \\        return frame;
        \\    }
        \\};
    );
}

test "scope-push-pop-imbalance: same spelling on a different counter stays visible" {
    try testing.expectFiresTyped(check, R,
        \\const S = struct {
        \\    depth: u32 = 0,
        \\    other: u32 = 0,
        \\    fn pushFrame(self: *S) !u32 { self.depth += 1; return self.depth; }
        \\    fn popFrame(self: *S) void { self.other -= 1; }
        \\    fn parse(self: *S) !u32 {
        \\        const frame = try self.pushFrame();
        \\        errdefer self.popFrame();
        \\        return frame;
        \\    }
        \\};
    );
}

test "scope-push-pop-imbalance: additional mutation is not inverse rollback" {
    try testing.expectFiresTyped(check, R,
        \\const S = struct {
        \\    depth: u32 = 0,
        \\    fn pushFrame(self: *S) !u32 { self.depth += 1; self.depth += 1; return self.depth; }
        \\    fn popFrame(self: *S) void { self.depth -= 1; }
        \\    fn parse(self: *S) !u32 {
        \\        const frame = try self.pushFrame();
        \\        errdefer self.popFrame();
        \\        return frame;
        \\    }
        \\};
    );
}

test "scope-push-pop-imbalance: conditional unbraced rollback is not complete" {
    try testing.expectFiresTyped(check, R,
        \\const S = struct {
        \\    depth: u32 = 0,
        \\    enabled: bool = false,
        \\    fn pushFrame(self: *S) !u32 { self.depth += 1; return self.depth; }
        \\    fn popFrame(self: *S) void { if (self.enabled) self.depth -= 1; }
        \\    fn parse(self: *S) !u32 {
        \\        const frame = try self.pushFrame();
        \\        errdefer self.popFrame();
        \\        return frame;
        \\    }
        \\};
    );
}

test "scope-push-pop-imbalance: typed discarded acquisition does not transfer" {
    try testing.expectFiresTyped(check, R,
        \\const ScopeId = enum { none, block };
        \\const Scopes = struct {
        \\    fn openScope(_: *Scopes, _: struct { parent: ?ScopeId }) ScopeId { return .block; }
        \\};
        \\const Run = struct {
        \\    stack: Scopes,
        \\    fn tick(_: *Run) !void {}
        \\    fn scopes(self: *Run) *Scopes { return &self.stack; }
        \\};
        \\fn openRegion(run: *Run) !ScopeId {
        \\    _ = run.scopes().openScope(.{ .parent = null });
        \\    try run.tick();
        \\    return .none;
        \\}
    );
}

test "scope-push-pop-imbalance: different actual receiver does not balance" {
    try testing.expectFiresTyped(check, R,
        \\const S = struct {
        \\    depth: u32 = 0,
        \\    fn pushFrame(self: *S) !u32 { self.depth += 1; return self.depth; }
        \\    fn popFrame(self: *S) void { self.depth -= 1; }
        \\    fn parse(self: *S, other: *S) !u32 {
        \\        const frame = try self.pushFrame();
        \\        errdefer other.popFrame();
        \\        return frame;
        \\    }
        \\};
    );
}

test "scope-push-pop-imbalance: equal formal spelling does not equate different actual roots" {
    try testing.expectFiresTyped(check, R,
        \\const State = struct { depth: u32 = 0 };
        \\const Ops = struct {
        \\    fn pushFrame(first: *State, second: *State) !u32 {
        \\        first.depth += 1;
        \\        _ = second;
        \\        return first.depth;
        \\    }
        \\    fn popFrame(second: *State, first: *State) void {
        \\        first.depth -= 1;
        \\        _ = second;
        \\    }
        \\};
        \\fn parse(a: *State, b: *State) !u32 {
        \\    const frame = try Ops.pushFrame(a, b);
        \\    errdefer Ops.popFrame(a, b);
        \\    return frame;
        \\}
    );
}
