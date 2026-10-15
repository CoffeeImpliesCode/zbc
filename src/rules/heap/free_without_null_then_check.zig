//! A release must reset a persistent owner slot on every reachable exit.
//! A copied slice length is header metadata, not freed-backing access.
//! Consumed lifetimes and ownership retirement require positive proof.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");

const tokens = @import("../../ast/tokens.zig");
const method_names = @import("../../model/method_names.zig");
const testing = @import("../../testing.zig");
const engine = @import("type_engine");
const fresh_storage = @import("../../cache/fresh_storage.zig");
const file_model = @import("../../model/file_model.zig");
const local_bindings = @import("../../model/local_bindings.zig");
const skipDeferStmt = tokens.skipDeferStmt;
const matchParen = tokens.matchParen;
const findStmtSemicolon = tokens.findStmtSemicolon;
const skipNestedFn = tokens.skipNestedFn;
const returnsType = tokens.returnsType;
const fnProto = tokens.fnProto;
const bodyOf = tokens.bodyOf;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .free_without_null_then_check)) return;
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();

    var node_idx: u32 = 1;
    while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        if (returnsType(tree, node)) continue;
        var buf: [1]Ast.Node.Index = undefined;
        const fp = fnProto(tree, &buf, node) orelse continue;
        const body = bodyOf(tree, node) orelse continue;
        try checkBody(gpa, tree, cache, node, fp, body, problems);
    }
}

/// Conservative allowlist of identifiers that look like an
/// allocator handle.  Used to filter out custom-receiver methods
/// like `link.free(self.page.?)` (where `link` is the destroyed
/// object and `self.page` is the allocator arg) from being treated
/// as `<alloc>.free(<recv>.<field>)`.  Matches by suffix /
/// substring patterns rather than an exact list to handle
/// project-specific allocator names like `string_alloc`,
/// `grapheme_alloc`, `default_allocator`, etc.
const isAllocatorishName = method_names.isAllocatorishName;
/// Legacy entry policy, not a lifetime certificate. In-body backing access,
/// repeated release and failed replacement are checked before this exclusion.
fn isDestructorName(name: []const u8) bool {
    if (std.mem.startsWith(u8, name, "deinit") or
        std.mem.startsWith(u8, name, "destroy") or
        std.mem.startsWith(u8, name, "finalize") or
        std.mem.startsWith(u8, name, "dispose") or
        std.mem.startsWith(u8, name, "take") or
        std.mem.startsWith(u8, name, "consume") or
        std.mem.startsWith(u8, name, "into") or
        std.mem.startsWith(u8, name, "free") or
        std.mem.eql(u8, name, "close")) return true;
    return std.mem.indexOf(u8, name, "Deinit") != null or
        std.mem.indexOf(u8, name, "Destroy") != null or
        std.mem.indexOf(u8, name, "Cleanup") != null or
        std.mem.indexOf(u8, name, "Finalize") != null or
        std.mem.indexOf(u8, name, "Dispose") != null;
}


const Free = struct {
    recv_name: []const u8,
    field_name: []const u8,
    method_tok: Ast.TokenIndex,
    end_token: Ast.TokenIndex,
};

fn checkBody(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    declaration: Ast.Node.Index,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    var frees: std.ArrayListUnmanaged(Free) = .empty;
    defer frees.deinit(gpa);

    var t: Ast.TokenIndex = first;
    while (t + 4 <= last) : (t += 1) {
        if (tags[t] == .keyword_fn) {
            t = skipNestedFn(tags, t, last);
            continue;
        }
        // Skip `defer` / `errdefer` statements entirely — they're
        // deferred actions, not inline frees.  A `errdefer
        // allocator.destroy(self.scans);` registers cleanup for the
        // error path; not flagging the slot for reset is correct.
        if (tags[t] == .keyword_defer or tags[t] == .keyword_errdefer) {
            t = skipDeferStmt(tags, t, last) orelse last;
            continue;
        }
        // Pattern: `.<method>(<recv>.<field>...)` where method ∈
        // {destroy, free}.  `<method>` is preceded by `.` (so it's
        // a method call on something — could be a single allocator
        // var OR a chained `self.gpa.destroy(...)`).  The receiver
        // chain before `.<method>` must look like a real allocator
        // — we filter out custom-receiver methods (`link.free(x)`
        // where `link` is the freed object and `x` is the allocator
        // arg) by requiring the LHS of `.method` to be either a
        // single bare identifier (e.g., `gpa.destroy(...)`) OR a
        // `.<known-alloc-field>` chain (e.g., `self.gpa.destroy(...)`,
        // `bun.default_allocator.free(...)`).
        if (tags[t] != .identifier) continue;
        if (t == 0 or tags[t - 1] != .period) continue;
        const method = tree.tokenSlice(t);
        if (!std.mem.eql(u8, method, "destroy") and !std.mem.eql(u8, method, "free")) continue;
        // A resolved allocator declaration authenticates the receiver.
        // Without that authority, retain the exact legacy spelling filter;
        // an unknown receiver is neither a no-op nor a new allocator name.
        if (t < 2) continue;
        if (tags[t - 2] != .identifier) continue;
        const alloc_name = tree.tokenSlice(t - 2);
        if (!isAllocatorishName(alloc_name) and !try allocatorRelease(cache, t - 1)) continue;
        if (tags[t + 1] != .l_paren) continue;
        const close = matchParen(tags, t + 1, last) orelse continue;
        // First 3 tokens after `(` must be `<recv> . <field>`.
        if (close <= t + 4) continue;
        if (tags[t + 2] != .identifier) continue;
        if (tags[t + 3] != .period) continue;
        if (tags[t + 4] != .identifier) continue;
        // After `<field>`, only these continuations name the slot
        // itself as the freed thing:
        //   - `)` — bare `<recv>.<field>`
        //   - `.?` (period + question_mark) — unwrap then free
        //   - `.*` (period + asterisk) — deref then free
        // Everything else (`(` method call, `[` slice/index,
        // `,` multi-arg) means the freed expression is a different
        // sub-expression and we'd be falsely flagging it.
        if (t + 5 > last) continue;
        const after = tags[t + 5];
        if (after == .r_paren) {
            // bare field — good
        } else if (after == .period and t + 6 <= last and
            (tags[t + 6] == .question_mark or tags[t + 6] == .asterisk))
        {
            // .? or .* — good
        } else continue;
        const recv = tree.tokenSlice(t + 2);
        const field = tree.tokenSlice(t + 4);
        // Restrict to canonical Zig method-receiver names.  This is
        // the rule's main precision lever — without it, hashmap
        // `entry.value_ptr`, result-struct `result.path`,
        // function-local container fields, and similar transient
        // borrows flood the report.  The Bun PR shapes all use
        // `self.X` / `this.X` — narrowing here drops the FP rate by
        // ~95% while preserving the canonical bug.
        if (!std.mem.eql(u8, recv, "self") and !std.mem.eql(u8, recv, "this")) continue;
        const sc = findStmtSemicolon(tags, close + 1, last) orelse continue;
        try frees.append(gpa, .{
            .recv_name = recv,
            .field_name = field,
            .method_tok = t,
            .end_token = sc,
        });
        t = sc;
    }

    if (frees.items.len == 0) return;
    const parents = try buildParents(gpa, tree);
    defer gpa.free(parents);
    for (frees.items) |f| {
        const call_index = try cache.getCallIndex();
        // Member calls are indexed by the field-access main token (`.`),
        // not the method-name token used for the diagnostic.
        const call = call_index.by_callee_token.get(f.method_tok - 1) orelse continue;
        if (try harmlessRelease(cache, f.method_tok - 1)) continue;
        var proof = ReleaseProof{
            .cache = cache, .tree = tree, .parents = parents,
            .free = f, .call = call, .gate = try findGate(cache, body, f),
            .bindings = (try cache.localBindings(proto, body)).*,
            .plain_slice = try plainSliceRelease(cache, declaration, f),
        };
        const flow = try proof.walk(body, clean);
        const exits = flow.next | flow.normal | flow.errors;
        if (!proof.bad) {
            if (isDestructorName(tree.tokenSlice(proto.name_token.?)) and flow.errors & dangling == 0) continue;
            if (exits & (dangling | retired) == 0) continue;
            if (exits & dangling == 0 and proof.gate != null) {
                if (try guardedConsumers(cache, declaration, f, proof.gate.?, parents)) continue;
                if (try consumedAtCallers(cache, declaration, proto, f, parents, true)) continue;
            }
            if (flow.errors & dangling == 0 and
                try consumedAtCallers(cache, declaration, proto, f, parents, false)) continue;
        }
        try report(gpa, problems, tree, f);
    }
}

const clean: u8 = 1;
const dangling: u8 = 2;
const retired: u8 = 4;
const retirement_armed: u8 = 8;
const empty_header: u8 = 16;
// Independent of the current owner header: resetting that header does not
// revive a slice copied before release.
const backing_dead: u8 = 32;

const Flow = struct {
    next: u8 = 0,
    normal: u8 = 0,
    errors: u8 = 0,

    fn merge(self: *Flow, other: Flow) void {
        self.next |= other.next;
        self.normal |= other.normal;
        self.errors |= other.errors;
    }
};

const Gate = struct { field: []const u8, inactive: bool, exchange: ?Ast.Node.Index = null };

fn buildParents(gpa: std.mem.Allocator, tree: *const Ast) ![]Ast.Node.Index {
    const parents = try gpa.alloc(Ast.Node.Index, tree.nodes.len);
    @memset(parents, @enumFromInt(0));
    for (1..tree.nodes.len) |raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        switch (tree.nodeTag(node)) {
            .asm_input, .asm_output => continue,
            else => {},
        }
        var children = engine.AstIterator.init(tree, node);
        while (children.next(tree)) |child| parents[@intFromEnum(child)] = node;
    }
    return parents;
}

fn fieldNamed(tree: *const Ast, node: Ast.Node.Index, receiver: []const u8, field: []const u8) bool {
    if (tree.nodeTag(node) != .field_access) return false;
    const root, const token = tree.nodeData(node).node_and_token;
    return receiverNamed(tree, root, receiver) and std.mem.eql(u8, tree.tokenSlice(token), field);
}

fn receiverNamed(tree: *const Ast, node: Ast.Node.Index, receiver: []const u8) bool {
    return tree.nodeTag(node) == .identifier and
        std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), receiver);
}

fn boolLiteral(tree: *const Ast, node: Ast.Node.Index) ?bool {
    if (tree.nodeTag(node) != .identifier) return null;
    const value = tree.tokenSlice(tree.nodeMainToken(node));
    if (std.mem.eql(u8, value, "true")) return true;
    if (std.mem.eql(u8, value, "false")) return false;
    return null;
}

fn conditionGate(tree: *const Ast, node: Ast.Node.Index, receiver: []const u8) ?struct {
    field: []const u8,
    value: bool,
} {
    if (tree.nodeTag(node) == .bool_not) {
        var gate = conditionGate(tree, tree.nodeData(node).node, receiver) orelse return null;
        gate.value = !gate.value;
        return gate;
    }
    if (tree.nodeTag(node) == .bool_and)
        return conditionGate(tree, tree.nodeData(node).node_and_node[0], receiver);
    if (tree.nodeTag(node) != .field_access) return null;
    const root, const token = tree.nodeData(node).node_and_token;
    if (!receiverNamed(tree, root, receiver)) return null;
    return .{ .field = tree.tokenSlice(token), .value = true };
}

fn containsToken(tree: *const Ast, node: Ast.Node.Index, token: Ast.TokenIndex) bool {
    return tree.firstToken(node) <= token and token <= tree.lastToken(node);
}

fn findGate(cache: *file_cache_mod.FileCache, body: Ast.Node.Index, f: Free) !?Gate {
    const tree = cache.tree;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        const branch = tree.fullIf(node) orelse continue;
        if (tree.firstToken(node) < tree.firstToken(body) or tree.lastToken(node) > tree.lastToken(body)) continue;
        if (conditionGate(tree, branch.ast.cond_expr, f.recv_name)) |condition| {
            if (containsToken(tree, branch.ast.then_expr, f.method_tok))
                return .{ .field = condition.field, .inactive = !condition.value };
            if (tree.nodeTag(branch.ast.then_expr) == .@"return" and
                tree.lastToken(branch.ast.then_expr) < f.method_tok and
                branch.ast.else_expr == .none)
                return .{ .field = condition.field, .inactive = condition.value };
        }
        if (tree.nodeTag(branch.ast.cond_expr) != .bool_not or
            tree.nodeTag(branch.ast.then_expr) != .@"return" or
            tree.lastToken(branch.ast.then_expr) >= f.method_tok or branch.ast.else_expr != .none) continue;
        const exchange = tree.nodeData(branch.ast.cond_expr).node;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = engine.TypeResolver.CallOperands.full(tree, &buffer, exchange) orelse continue;
        const actual = (try cache.actualCallSummaryAt(call.queryToken(tree, exchange), null)) orelse continue;
        const resolver = cache.zls orelse continue;
        if (!try resolver.declaredInToolchainFile(actual.callee.handle, "/std/atomic.zig")) continue;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = fnProto(actual.callee.tree, &proto_buffer, actual.callee.declaration) orelse continue;
        if (!std.mem.eql(u8, actual.callee.tree.tokenSlice(proto.name_token orelse continue), "swap")) continue;
        const receiver = (try actual.callArgumentFor(cache, &buffer, 0)) orelse continue;
        const value = (try actual.callArgumentFor(cache, &buffer, 1)) orelse continue;
        if (boolLiteral(tree, value) != false or tree.nodeTag(receiver) != .field_access) continue;
        const root, const token = tree.nodeData(receiver).node_and_token;
        if (!receiverNamed(tree, root, f.recv_name)) continue;
        return .{ .field = tree.tokenSlice(token), .inactive = false, .exchange = exchange };
    }
    return null;
}

fn harmlessRelease(cache: *file_cache_mod.FileCache, token: Ast.TokenIndex) !bool {
    const actual = (try cache.actualCallSummaryAt(token, null)) orelse return false;
    if (try fresh_storage.allocatorPrimitive(cache, actual, .{
        .claim = .{ .first = token, .last = token }, .depth = 0,
    }) != null) return false;
    // A project method needs a complete whole-call proof; an argument-only
    // read-only result does not exclude a release through another root.
    return try cache.callEffectAt(token, .{ .whole = actual.callee }, .{}) == .read_only;
}

fn allocatorRelease(cache: *file_cache_mod.FileCache, token: Ast.TokenIndex) !bool {
    const actual = (try cache.actualCallSummaryAt(token, null)) orelse return false;
    const primitive = (try fresh_storage.allocatorPrimitive(cache, actual, .{
        .claim = .{ .first = token, .last = token }, .depth = 0,
    })) orelse return false;
    return primitive.operation == .release;
}

const ReleaseProof = struct {
    cache: *file_cache_mod.FileCache,
    tree: *const Ast,
    parents: []const Ast.Node.Index,
    free: Free,
    call: Ast.Node.Index,
    gate: ?Gate,
    bindings: local_bindings.LocalBindings,
    plain_slice: bool,
    bad: bool = false,

    fn slot(self: *const ReleaseProof, node: Ast.Node.Index) bool {
        if (fieldNamed(self.tree, node, self.free.recv_name, self.free.field_name)) return true;
        if (self.tree.nodeTag(node) != .identifier) return false;
        var token = self.tree.nodeMainToken(node);
        for (0..16) |_| {
            const binding = self.bindings.findAt(self.tree.tokenSlice(token), token) orelse return false;
            switch (binding.origin) {
                .field_access => |field| return std.mem.eql(u8, field.receiver, self.free.recv_name) and
                    std.mem.eql(u8, field.field, self.free.field_name),
                .alias => token = binding.rhs_first,
                else => return false,
            }
        }
        return false;
    }

    fn resetTarget(self: *const ReleaseProof, node: Ast.Node.Index) bool {
        return fieldNamed(self.tree, node, self.free.recv_name, self.free.field_name) or
            (self.tree.nodeTag(node) == .deref and
            receiverNamed(self.tree, self.tree.nodeData(node).node, self.free.recv_name));
    }

    fn metadata(self: *const ReleaseProof, node: Ast.Node.Index) !bool {
        const parent = self.parents[@intFromEnum(node)];
        if (self.tree.nodeTag(parent) != .field_access) return false;
        const root, const token = self.tree.nodeData(parent).node_and_token;
        if (root != node or !std.mem.eql(u8, self.tree.tokenSlice(token), "len")) return false;
        if (self.plain_slice) return true;
        const resolver = self.cache.zls orelse return false;
        const ty = (try resolver.resolutionFrame().typeOfNode(node)) orelse return false;
        return resolver.pointerSize(ty) == .slice;
    }

    fn replacement(self: *ReleaseProof, node: Ast.Node.Index) anyerror!bool {
        try self.cache.enterNormalCleanup(node);
        defer self.cache.leaveNormalCleanup();
        try self.cache.chargeNormalCleanup(node);
        const tree = self.tree;
        if (tree.nodeTag(node) == .grouped_expression)
            return self.replacement(tree.nodeData(node).node_and_token[0]);
        if (tree.fullIf(node)) |branch| {
            const known = boolLiteral(tree, branch.ast.cond_expr);
            if (known != false and !try self.replacement(branch.ast.then_expr)) return false;
            if (known != true) {
                const other = branch.ast.else_expr.unwrap() orelse return false;
                if (!try self.replacement(other)) return false;
            }
            return true;
        }
        if (tree.fullSwitch(node)) |selection| {
            if (selection.label_token != null or selection.ast.cases.len == 0) return false;
            for (selection.ast.cases) |case| {
                const prong = tree.fullSwitchCase(case).?;
                if (!try self.replacement(prong.ast.target_expr)) return false;
            }
            return true;
        }
        if (tree.nodeTag(node) == .@"catch" or tree.nodeTag(node) == .@"orelse") {
            const left, const right = tree.nodeData(node).node_and_node;
            return try self.replacement(left) and try self.replacement(right);
        }
        if (tree.nodeTag(node) == .identifier) {
            const value = tree.tokenSlice(tree.nodeMainToken(node));
            return std.mem.eql(u8, value, "null") or std.mem.eql(u8, value, "undefined");
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullStructInit(&buffer, node)) |literal| {
            if (literal.ast.fields.len == 0) return true;
        }
        if (tree.nodeTag(node) == .address_of) {
            const value = tree.nodeData(node).node;
            if (tree.fullArrayInit(&buffer, value)) |literal| return literal.ast.elements.len == 0;
            if (tree.fullStructInit(&buffer, value)) |literal| return literal.ast.fields.len == 0;
        }
        return self.cache.normalCleanupFresh(node);
    }

    fn walkDefers(self: *ReleaseProof, registered: []const Ast.Node.Index, initial: u8, error_exit: bool) !u8 {
        var state = initial;
        var index = registered.len;
        while (index != 0 and state != 0) {
            index -= 1;
            const statement = registered[index];
            const is_error = self.tree.nodeTag(statement) == .@"errdefer";
            if (is_error and !error_exit) continue;
            const body = if (is_error) self.tree.nodeData(statement).opt_token_and_node[1]
                else self.tree.nodeData(statement).node;
            const result = try self.walk(body, state);
            state = result.next;
            if (result.normal != 0 or result.errors != 0) self.bad = true;
        }
        return state;
    }

    fn walkBlock(self: *ReleaseProof, node: Ast.Node.Index, initial: u8) !Flow {
        var buffer: [2]Ast.Node.Index = undefined;
        const statements = self.tree.blockStatements(&buffer, node).?;
        var registered: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        defer registered.deinit(self.cache.gpa);
        var out = Flow{ .next = initial };
        for (statements) |statement| {
            if (out.next == 0) break;
            const tag = self.tree.nodeTag(statement);
            if (tag == .@"defer" or tag == .@"errdefer") {
                try registered.append(self.cache.gpa, statement);
                continue;
            }
            const result = try self.walk(statement, out.next);
            out.normal |= try self.walkDefers(registered.items, result.normal, false);
            out.errors |= try self.walkDefers(registered.items, result.errors, true);
            out.next = result.next;
        }
        out.next = try self.walkDefers(registered.items, out.next, false);
        return out;
    }

    fn walk(self: *ReleaseProof, node: Ast.Node.Index, initial: u8) anyerror!Flow {
        if (initial == 0) return .{};
        try self.cache.enterNormalCleanup(node);
        defer self.cache.leaveNormalCleanup();
        try self.cache.chargeNormalCleanup(node);
        const tree = self.tree;
        if (node == self.call) {
            if (initial & (dangling | retired) != 0) self.bad = true;
            return .{ .next = (if (initial & clean != 0) dangling else @as(u8, 0)) |
                (if (initial & retirement_armed != 0) retired else @as(u8, 0)) |
                (initial & empty_header) | backing_dead };
        }
        switch (tree.nodeTag(node)) {
            .fn_decl, .container_decl, .container_decl_two, .container_decl_trailing,
            .container_decl_two_trailing, .@"defer", .@"errdefer" => return .{ .next = initial },
            .block, .block_semicolon, .block_two, .block_two_semicolon => return self.walkBlock(node, initial),
            .@"if", .if_simple => {
                const branch = tree.fullIf(node).?;
                var out = try self.walk(branch.ast.cond_expr, initial);
                const state = out.next;
                out.next = 0;
                const known = boolLiteral(tree, branch.ast.cond_expr);
                if (known != false) out.merge(try self.walk(branch.ast.then_expr, state));
                if (known != true) {
                    if (branch.ast.else_expr.unwrap()) |other| out.merge(try self.walk(other, state))
                    else out.next |= state;
                }
                return out;
            },
            .@"switch", .switch_comma => {
                const selection = tree.fullSwitch(node).?;
                var out = try self.walk(selection.ast.condition, initial);
                const state = out.next;
                out.next = 0;
                for (selection.ast.cases) |case| {
                    const prong = tree.fullSwitchCase(case).?;
                    out.merge(try self.walk(prong.ast.target_expr, state));
                }
                // Labelled switches can re-enter another prong. Do not
                // certify their exit state with a single traversal.
                if (selection.label_token != null or selection.ast.cases.len == 0) {
                    out.next |= state;
                    if (state & (dangling | retired) != 0) out.errors |= dangling;
                }
                return out;
            },
            .@"catch", .@"orelse", .bool_and, .bool_or => {
                const left, const right = tree.nodeData(node).node_and_node;
                var out = try self.walk(left, initial);
                // The right operand is conditional. In particular, a catch
                // reset cannot repair the successful, unchanged owner path.
                out.merge(try self.walk(right, out.next));
                return out;
            },
            .@"return" => {
                const value = tree.nodeData(node).opt_node.unwrap();
                var out = if (value) |expression| try self.walk(expression, initial)
                    else Flow{ .next = initial };
                if (value != null and tree.nodeTag(value.?) == .error_value) out.errors |= out.next
                else out.normal |= out.next;
                out.next = 0;
                return out;
            },
            .@"try" => {
                var out = try self.walk(tree.nodeData(node).node, initial);
                out.errors |= out.next;
                return out;
            },
            .assign => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                var out = try self.walk(rhs, initial);
                if (tree.nodeTag(lhs) == .field_access and self.plain_slice) {
                    const root, const token = tree.nodeData(lhs).node_and_token;
                    if (fieldNamed(tree, root, self.free.recv_name, self.free.field_name) and
                        std.mem.eql(u8, tree.tokenSlice(token), "len") and
                        tree.nodeTag(rhs) == .number_literal and
                        std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(rhs)), "0"))
                    {
                        if (out.next != 0) out.next = empty_header | (out.next & backing_dead);
                        return out;
                    }
                }
                if (self.resetTarget(lhs) and try self.replacement(rhs)) {
                    if (out.next != 0) out.next = clean | (out.next & backing_dead);
                    return out;
                }
                if (self.gate) |gate| {
                    if (fieldNamed(tree, lhs, self.free.recv_name, gate.field)) {
                        if (boolLiteral(tree, rhs)) |value| {
                            if (value == gate.inactive) {
                                out.next = (if (out.next & (clean | retirement_armed) != 0) retirement_armed else @as(u8, 0)) |
                                    (if (out.next & (dangling | retired) != 0) retired else @as(u8, 0)) |
                                    (out.next & backing_dead);
                            } else if (out.next & retired != 0) out.next = (out.next & ~retired) | dangling;
                        }
                    }
                }
                return out;
            },
            .field_access, .identifier => {
                const copied = if (tree.nodeTag(node) == .identifier)
                    if (self.bindings.findAt(tree.tokenSlice(tree.nodeMainToken(node)), tree.firstToken(node))) |binding|
                        binding.name_token < self.free.method_tok
                    else false
                else false;
                if (self.slot(node) and
                    (initial & (dangling | retired | empty_header) != 0 or
                    (copied and initial & backing_dead != 0)) and !try self.metadata(node))
                    self.bad = true;
            },
            else => {},
        }
        var call_buffer: [2]Ast.Node.Index = undefined;
        if (engine.TypeResolver.CallOperands.full(tree, &call_buffer, node)) |call| {
            if (self.gate) |gate| {
                if (gate.exchange == node) {
                    return .{ .next = (initial & (dangling | retired)) |
                        (if (initial & (clean | retirement_armed) != 0) retirement_armed else @as(u8, 0)) |
                        (initial & backing_dead) };
                }
            }
            if (initial & (dangling | retired) != 0 and
                try consumesReceiver(self.cache, call.queryToken(tree, node), self.free.recv_name))
                return .{ .next = clean | (initial & backing_dead) };
        }
        var out = Flow{ .next = initial };
        var children = engine.AstIterator.init(tree, node);
        while (children.next(tree)) |child| {
            const flow = try self.walk(child, out.next);
            out.normal |= flow.normal;
            out.errors |= flow.errors;
            out.next = flow.next;
        }
        switch (tree.nodeTag(node)) {
            .@"while", .while_simple, .while_cont, .@"for", .for_simple,
            .@"break", .@"continue" => {
                out.next |= initial;
                if (out.next & (dangling | retired) != 0) out.errors |= dangling;
            },
            else => {},
        }
        return out;
    }
};

fn consumesReceiver(cache: *file_cache_mod.FileCache, token: Ast.TokenIndex, receiver: []const u8) !bool {
    const actual = (try cache.actualCallSummaryAt(token, null)) orelse return false;
    const primitive = (try fresh_storage.allocatorPrimitive(cache, actual, .{
        .claim = .{ .first = token, .last = token }, .depth = 0,
    })) orelse return false;
    if (primitive.operation != .release) return false;
    var buffer: [2]Ast.Node.Index = undefined;
    const argument = (try actual.callArgumentFor(cache, &buffer, primitive.previous_parameter.?)) orelse return false;
    return receiverNamed(cache.tree, argument, receiver);
}

fn guardedConsumers(cache: *file_cache_mod.FileCache, declaration: Ast.Node.Index, f: Free, gate: Gate, parents: []const Ast.Node.Index) !bool {
    const model = try cache.fileModel();
    var owner: ?*const file_model.TypeInfo = null;
    for (model.types) |*candidate| {
        for (candidate.methods) |method| {
            if (method.fn_decl == declaration) owner = candidate;
        }
    }
    const ti = owner orelse return false;
    for (ti.methods) |method| {
        if (method.fn_decl == declaration) continue;
        const receiver = method.receiver orelse continue;
        for (cache.tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .field_access) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (!containsToken(cache.tree, method.body, cache.tree.firstToken(node))) continue;
            if (!fieldNamed(cache.tree, node, receiver.name, f.field_name)) continue;
            if (!guardDominates(cache.tree, method.body, node, receiver.name, gate, parents)) return false;
        }
    }
    return true;
}

fn guardDominates(tree: *const Ast, body: Ast.Node.Index, use: Ast.Node.Index, receiver: []const u8, gate: Gate, parents: []const Ast.Node.Index) bool {
    var child = use;
    while (child != body and @intFromEnum(child) != 0) {
        const parent = parents[@intFromEnum(child)];
        if (tree.fullIf(parent)) |branch| {
            if (conditionGate(tree, branch.ast.cond_expr, receiver)) |condition| {
                if (std.mem.eql(u8, condition.field, gate.field) and
                    containsToken(tree, branch.ast.then_expr, tree.firstToken(use)) and
                    condition.value != gate.inactive) return true;
            }
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.blockStatements(&buffer, parent)) |statements| {
            for (statements) |statement| {
                if (statement == child) break;
                const branch = tree.fullIf(statement) orelse continue;
                if (tree.nodeTag(branch.ast.then_expr) != .@"return" or branch.ast.else_expr != .none) continue;
                const condition = conditionGate(tree, branch.ast.cond_expr, receiver) orelse continue;
                if (condition.value == gate.inactive and std.mem.eql(u8, condition.field, gate.field)) return true;
            }
        }
        child = parent;
    }
    return false;
}

fn samePath(tree: *const Ast, left: Ast.Node.Index, right: Ast.Node.Index) bool {
    const lf = tree.firstToken(left);
    const ll = tree.lastToken(left);
    const rf = tree.firstToken(right);
    const rl = tree.lastToken(right);
    if (ll - lf != rl - rf) return false;
    for (0..ll - lf + 1) |offset| {
        const i: Ast.TokenIndex = @intCast(offset);
        if (tree.tokenTag(lf + i) != tree.tokenTag(rf + i) or
            !std.mem.eql(u8, tree.tokenSlice(lf + i), tree.tokenSlice(rf + i))) return false;
    }
    return true;
}

fn pathPrefix(tree: *const Ast, prefix: Ast.Node.Index, value: Ast.Node.Index) bool {
    var current = value;
    while (true) {
        if (samePath(tree, prefix, current)) return true;
        if (tree.nodeTag(current) != .field_access) return false;
        current = tree.nodeData(current).node_and_token[0];
    }
}

fn rangeMentions(tree: *const Ast, range: Ast.Node.Index, value: Ast.Node.Index) bool {
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .identifier and tag != .field_access) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (containsToken(tree, range, tree.firstToken(node)) and samePath(tree, node, value)) return true;
    }
    return false;
}

fn consumedAtCallers(cache: *file_cache_mod.FileCache, declaration: Ast.Node.Index, proto: Ast.full.FnProto, f: Free, parents: []const Ast.Node.Index, guarded: bool) !bool {
    const callers = (try cache.closedLocalCalls(declaration)) orelse return false;
    if (callers.len == 0) return false;
    var parameters = proto.iterate(cache.tree);
    var parameter_index: u32 = 0;
    var selected: ?u32 = null;
    while (parameters.next()) |parameter| : (parameter_index += 1) {
        const token = parameter.name_token orelse continue;
        if (std.mem.eql(u8, cache.tree.tokenSlice(token), f.recv_name)) selected = parameter_index;
    }
    const parameter = selected orelse return false;
    for (callers) |call_node| {
        try cache.chargeNormalCleanup(call_node);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = engine.TypeResolver.CallOperands.full(cache.tree, &buffer, call_node) orelse return false;
        const actual = (try cache.actualCallSummaryAt(call.queryToken(cache.tree, call_node), null)) orelse return false;
        const argument = (try actual.callArgumentFor(cache, &buffer, parameter)) orelse return false;
        const caller_decl = tokens.enclosingFnDecl(cache.tree, cache.tree.firstToken(call_node)) orelse return false;
        const body = bodyOf(cache.tree, caller_decl) orelse return false;
        if (!try callerConsumes(cache, call_node, argument, caller_decl, body, parents, guarded, f)) return false;
    }
    return true;
}

fn plainSliceRelease(cache: *file_cache_mod.FileCache, declaration: Ast.Node.Index, f: Free) !bool {
    const actual = (try cache.actualCallSummaryAt(f.method_tok - 1, null)) orelse return false;
    const primitive = (try fresh_storage.allocatorPrimitive(cache, actual, .{
        .claim = .{ .first = f.method_tok, .last = f.method_tok }, .depth = 0,
    })) orelse return false;
    if (primitive.operation != .release or !std.mem.eql(u8, cache.tree.tokenSlice(f.method_tok), "free")) return false;
    const model = try cache.fileModel();
    for (model.types) |ti| {
        var owns_method = false;
        for (ti.methods) |method| {
            if (method.fn_decl == declaration) owns_method = true;
        }
        if (!owns_method) continue;
        for (ti.fields) |field| {
            if (!std.mem.eql(u8, field.name, f.field_name)) continue;
            const node = cache.nodeForExactSpan(field.type_first, field.type_last) orelse return false;
            const pointer = cache.tree.fullPtrType(node) orelse return false;
            return pointer.size == .slice and pointer.ast.sentinel == .none;
        }
    }
    return false;
}


/// The release and its consumer must share a lexical execution domain.
/// A later conditional consumer or an intervening error exit is not ALL-path.
fn consumptionFollows(tree: *const Ast, release: Ast.Node.Index, consumer: Ast.Node.Index, body: Ast.Node.Index, parents: []const Ast.Node.Index) bool {
    var scope = parents[@intFromEnum(release)];
    while (scope != body and @intFromEnum(scope) != 0) {
        switch (tree.nodeTag(scope)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => break,
            else => scope = parents[@intFromEnum(scope)],
        }
    }
    if (@intFromEnum(scope) == 0 or !containsToken(tree, scope, tree.firstToken(consumer)) or
        hasConditionalParent(tree, consumer, scope, parents)) return false;
    var token = tree.lastToken(release) + 1;
    while (token < tree.firstToken(consumer)) : (token += 1) {
        switch (tree.tokenTag(token)) {
            .keyword_try, .keyword_return, .keyword_break, .keyword_continue => return false,
            else => {},
        }
    }
    return true;
}

fn callerConsumes(cache: *file_cache_mod.FileCache, call_node: Ast.Node.Index, argument: Ast.Node.Index, declaration: Ast.Node.Index, body: Ast.Node.Index, parents: []const Ast.Node.Index, guarded: bool, f: Free) !bool {
    const tree = cache.tree;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = fnProto(tree, &proto_buffer, declaration) orelse return false;
    const bindings = (try cache.localBindings(proto, body)).*;
    const local_header = try localHeader(cache, &bindings, argument);
    var ancestor = call_node;
    while (ancestor != body and @intFromEnum(ancestor) != 0) {
        ancestor = parents[@intFromEnum(ancestor)];
        const tag = tree.nodeTag(ancestor);
        if (tag == .@"defer" or tag == .@"errdefer") {
            if (!local_header) return false;
            const scope = parents[@intFromEnum(ancestor)];
            var buffer: [2]Ast.Node.Index = undefined;
            const statements = tree.blockStatements(&buffer, scope) orelse return false;
            for (statements) |statement| {
                if (statement == ancestor) break;
                if (tree.nodeTag(statement) != .@"defer" and tree.nodeTag(statement) != .@"errdefer") continue;
                if (rangeMentions(tree, statement, argument)) return false;
            }
            return true;
        }
    }
    // A constructed local value header has no persistent slot at scope exit.
    var consumed = guarded or local_header;
    for (bindings.items) |binding| {
        if (binding.origin == .param or binding.origin == .loop_capture) continue;
        if (binding.name_token >= tree.firstToken(call_node)) continue;
        const initializer = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse continue;
        if (rangeMentions(tree, initializer, argument)) return false;
    }
    if (tree.nodeTag(argument) == .identifier) {
        const binding = bindings.findAt(tree.tokenSlice(tree.nodeMainToken(argument)), tree.firstToken(argument)) orelse return false;
        if (binding.origin == .loop_capture and
            try capturedHeaderConsumed(cache, call_node, argument, body, parents)) return true;
    }
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(node) <= tree.lastToken(call_node) or !containsToken(tree, body, tree.firstToken(node))) continue;
        if (tag == .assign) {
            const lhs, const rhs = tree.nodeData(node).node_and_node;
            if (pathPrefix(tree, lhs, argument) and !rangeMentions(tree, rhs, argument) and
                consumptionFollows(tree, call_node, node, body, parents)) consumed = true;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (engine.TypeResolver.CallOperands.full(tree, &buffer, node)) |call| {
            const actual = (try cache.actualCallSummaryAt(call.queryToken(tree, node), null)) orelse continue;
            const primitive = (try fresh_storage.allocatorPrimitive(cache, actual, .{
                .claim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) }, .depth = 0,
            })) orelse continue;
            if (primitive.operation != .release) continue;
            const memory = (try actual.callArgumentFor(cache, &buffer, primitive.previous_parameter.?)) orelse continue;
            if (pathPrefix(tree, memory, argument) and
                consumptionFollows(tree, call_node, node, body, parents)) consumed = true;
        }
        if ((tag == .identifier or tag == .field_access) and samePath(tree, node, argument)) {
            const parent = parents[@intFromEnum(node)];
            if (tree.nodeTag(parent) == .assign and tree.nodeData(parent).node_and_node[0] == node) continue;
            if (tree.nodeTag(parent) == .field_access) {
                const token = tree.nodeData(parent).node_and_token[1];
                if (!std.mem.eql(u8, tree.tokenSlice(token), f.field_name)) {
                    // Another inline field is not the released slot. Method
                    // receivers remain opaque.
                    const grandparent = parents[@intFromEnum(parent)];
                    var call_buffer: [2]Ast.Node.Index = undefined;
                    if (engine.TypeResolver.CallOperands.full(tree, &call_buffer, grandparent) == null) continue;
                }
                return false;
            }
            if (tree.nodeTag(parent) == .call or tree.nodeTag(parent) == .call_one or
                tree.nodeTag(parent) == .call_comma or tree.nodeTag(parent) == .call_one_comma)
            {
                var call_buffer: [2]Ast.Node.Index = undefined;
                const call = engine.TypeResolver.CallOperands.full(tree, &call_buffer, parent).?;
                const actual = (try cache.actualCallSummaryAt(call.queryToken(tree, parent), null)) orelse return false;
                const primitive = (try fresh_storage.allocatorPrimitive(cache, actual, .{
                    .claim = .{ .first = tree.firstToken(parent), .last = tree.lastToken(parent) }, .depth = 0,
                })) orelse return false;
                if (primitive.operation == .release) continue;
            }
            return false;
        }
    }
    return consumed;
}

fn localHeader(cache: *file_cache_mod.FileCache, bindings: *const local_bindings.LocalBindings, argument: Ast.Node.Index) !bool {
    const tree = cache.tree;
    if (tree.nodeTag(argument) != .identifier) return false;
    const binding = bindings.findAt(tree.tokenSlice(tree.nodeMainToken(argument)), tree.firstToken(argument)) orelse return false;
    if (binding.origin == .param or binding.origin == .alias or binding.origin == .field_access or
        binding.origin == .loop_capture or binding.origin == .addr_of) return false;
    const resolver = cache.zls orelse return false;
    const ty = (try resolver.resolutionFrame().typeOfNode(argument)) orelse return false;
    if (resolver.pointerSize(ty) != null) return false;
    return binding.origin == .literal or binding.origin == .call or binding.origin == .try_call or
        binding.origin == .method_call or binding.origin == .try_method_call;
}

fn capturedHeaderConsumed(cache: *file_cache_mod.FileCache, call_node: Ast.Node.Index, argument: Ast.Node.Index, body: Ast.Node.Index, parents: []const Ast.Node.Index) !bool {
    const tree = cache.tree;
    var loop = parents[@intFromEnum(call_node)];
    while (loop != body and @intFromEnum(loop) != 0 and tree.fullFor(loop) == null)
        loop = parents[@intFromEnum(loop)];
    const iteration = tree.fullFor(loop) orelse return false;
    if (hasConditionalParent(tree, call_node, loop, parents)) return false;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .identifier) continue;
        const use: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(use) <= tree.lastToken(call_node) or
            !containsToken(tree, loop, tree.firstToken(use))) continue;
        if (samePath(tree, use, argument)) return false;
    }
    if (iteration.ast.inputs.len != 1) return false;
    const input = iteration.ast.inputs[0];
    if (tree.nodeTag(input) != .field_access) return false;
    const collection, const token = tree.nodeData(input).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(token), "items")) return false;
    // Pointer captures denote cells in this exact backing allocation. The
    // canonical SDK list cleanup consumes that allocation after the loop.
    const argument_token = tree.nodeMainToken(argument);
    if (tree.tokenTag(iteration.payload_token) != .asterisk or
        !std.mem.eql(u8, tree.tokenSlice(iteration.payload_token + 1), tree.tokenSlice(argument_token))) return false;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.firstToken(node) <= tree.lastToken(loop) or !containsToken(tree, body, tree.firstToken(node))) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = engine.TypeResolver.CallOperands.full(tree, &buffer, node) orelse continue;
        const actual = (try cache.actualCallSummaryAt(call.queryToken(tree, node), null)) orelse continue;
        const resolver = cache.zls orelse return false;
        if (!try resolver.declaredInToolchainFile(actual.callee.handle, "/std/array_list.zig")) continue;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = fnProto(actual.callee.tree, &proto_buffer, actual.callee.declaration) orelse continue;
        if (!std.mem.eql(u8, actual.callee.tree.tokenSlice(proto.name_token orelse continue), "deinit")) continue;
        const receiver = (try actual.callArgumentFor(cache, &buffer, 0)) orelse continue;
        if (!samePath(tree, collection, receiver) or
            !consumptionFollows(tree, loop, node, body, parents)) continue;
        var prior_use = false;
        for (tree.nodes.items(.tag), 0..) |tag, use_raw| {
            if (tag != .field_access) continue;
            const use: Ast.Node.Index = @enumFromInt(use_raw);
            if (!containsToken(tree, body, tree.firstToken(use)) or
                containsToken(tree, loop, tree.firstToken(use))) continue;
            if (samePath(tree, use, input)) prior_use = true;
        }
        if (!prior_use) return true;
    }
    return false;
}

fn hasConditionalParent(tree: *const Ast, node: Ast.Node.Index, body: Ast.Node.Index, parents: []const Ast.Node.Index) bool {
    var current = parents[@intFromEnum(node)];
    while (current != body and @intFromEnum(current) != 0) {
        switch (tree.nodeTag(current)) {
            .@"if", .if_simple, .@"while", .while_simple, .while_cont, .@"for", .for_simple,
            .@"switch", .switch_comma, .@"try", .@"catch" => return true,
            else => {},
        }
        current = parents[@intFromEnum(current)];
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    f: Free,
) !void {
    const method = tree.tokenSlice(f.method_tok);
    const msg = try std.fmt.allocPrint(
        gpa,
        "freed `{s}.{s}` via `.{s}()` but never reset the slot — `{s}.{s}` now holds a dangling pointer; a later `if ({s}.{s}) |h| use(h)` will pass the null-check (non-null) and UAF, or the struct's own `deinit` will double-free.  Add `{s}.{s} = null;` (or `= &.{{}};` / `= .empty;`) immediately after",
        .{ f.recv_name, f.field_name, method, f.recv_name, f.field_name, f.recv_name, f.field_name, f.recv_name, f.field_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = "free-without-null-then-check",
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, f.method_tok),
        .end = try Pos.fromTokenEnd(tree, f.method_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

const freeProblems = testing.freeProblems;

test "free-without-null-then-check: destroy then no reset fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    handlers: ?*Handlers,
        \\    const Handlers = struct {};
        \\    pub fn markInactive(self: *Self) void {
        \\        self.gpa.destroy(self.handlers.?);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
    try std.testing.expectEqualStrings("free-without-null-then-check", problems.items[0].rule_id);
}

test "free-without-null-then-check: destroy followed by null reset doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    handlers: ?*Handlers,
        \\    const Handlers = struct {};
        \\    pub fn markInactive(self: *Self) void {
        \\        self.gpa.destroy(self.handlers.?);
        \\        self.handlers = null;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: free([]u8) then = &.{} doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    specifier: []const u8,
        \\    pub fn reset(self: *Self) void {
        \\        self.gpa.free(self.specifier);
        \\        self.specifier = &.{};
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}


test "free-without-null-then-check: free(local) doesn't fire (only <recv>.<field>)" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\pub fn foo(gpa: std.mem.Allocator) void {
        \\    const local = gpa.alloc(u8, 4) catch return;
        \\    gpa.free(local);
        \\}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: sub-field reset (this.X.len = 0) doesn't fire" {
    // A plain slice's empty header prevents another allocator release and
    // in-bounds access. Raw pointer uses still need their own lifetime proof.
    const gpa = std.testing.allocator;
    var problems = try testing.runRuleTyped(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    buf: []u8,
        \\    pub fn clearInput(self: *Self) void {
        \\        self.gpa.free(self.buf);
        \\        self.buf.len = 0;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}


test "free-without-null-then-check: non-allocator receiver doesn't fire" {
    // `link.free(self.page.?)` — `link` is the freed object (a
    // PageEntry); `self.page` is just the allocator arg.  The
    // receiver name `link` isn't allocator-ish, so skip.
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Link = struct { pub fn free(_: *Link, _: usize) void {} };
        \\const Self = struct {
        \\    page: ?usize,
        \\    pub fn onDeleted(self: *const Self, link: *Link) void {
        \\        link.free(self.page.?);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: free inside errdefer is skipped" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Self = struct {
        \\    gpa: std.mem.Allocator,
        \\    scans: *u8,
        \\    pub fn init(self: *Self) !void {
        \\        self.scans = try self.gpa.create(u8);
        \\        errdefer self.gpa.destroy(self.scans);
        \\        _ = try doSomething();
        \\    }
        \\};
        \\fn doSomething() !void {}
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}




test "free-without-null-then-check: camelCase-prefixed destructor fires in non-cleanup fn" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Builder = struct {
        \\    gpa: std.mem.Allocator,
        \\    line_offsets: []u8,
        \\    pub fn process(self: *Builder) void {
        \\        self.gpa.free(self.line_offsets);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}


test "free-without-null-then-check: whole-receiver empty reset doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        self.* = .{};
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: whole-receiver undefined reset doesn't fire" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        self.* = undefined;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "free-without-null-then-check: free without field or receiver reset fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "free-without-null-then-check: resetting another receiver still fires" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, other: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        other.* = .{};
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "free-without-null-then-check: whole-receiver read is not a reset" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8 = &.{},
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        _ = self.*;
        \\    }
        \\};
        \\
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "free-without-null-then-check: lifetime consumed copied header metadata" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: Owner, gpa: std.mem.Allocator) usize {
        \\        gpa.free(self.bytes);
        \\        return self.bytes.len;
        \\    }
        \\};
        \\fn consume(gpa: std.mem.Allocator) !usize {
        \\    const owner: Owner = .{ .bytes = try gpa.alloc(u8, 4) };
        \\    return owner.release(gpa);
        \\}
    );
}

test "free-without-null-then-check: lifetime guarded retired owner" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    live: bool = true,
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void {
        \\        if (self.live) {
        \\            gpa.free(self.bytes);
        \\            self.live = false;
        \\        }
        \\    }
        \\    fn read(self: *Owner) ?u8 {
        \\        if (!self.live) return null;
        \\        return self.bytes[0];
        \\    }
        \\};
    );
}

test "free-without-null-then-check: lifetime no-op project free" {
    try testing.expectNoFireTyped(check,
        \\const Allocator = struct { fn free(_: Allocator, _: []u8) void {} };
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: *Owner, allocator: Allocator) void {
        \\        allocator.free(self.bytes);
        \\    }
        \\};
    );
}

test "free-without-null-then-check: lifetime conditional reset retains stale slot" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator, clear: bool) void {
        \\        gpa.free(self.bytes);
        \\        if (clear) self.bytes = &.{};
        \\    }
        \\};
    );
}

test "free-without-null-then-check: lifetime stale backing and repeated free" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: Owner, gpa: std.mem.Allocator) u8 {
        \\        gpa.free(self.bytes);
        \\        return self.bytes[0];
        \\    }
        \\};
    );
}

test "free-without-null-then-check: lifetime fallible retirement alternate" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    live: bool = true,
        \\    fn release(self: *Owner, gpa: std.mem.Allocator, fail: bool) !void {
        \\        if (self.live) {
        \\            gpa.free(self.bytes);
        \\            if (fail) return error.Refused;
        \\            self.live = false;
        \\        }
        \\    }
        \\};
    );
}

test "free-without-null-then-check: lifetime branch reallocation preserves error defect" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn rebuild(self: *Owner, gpa: std.mem.Allocator) !void {
        \\        gpa.free(self.bytes);
        \\        self.bytes = try gpa.alloc(u8, 4);
        \\    }
        \\};
    );
}

test "free-without-null-then-check: precision captured header consumed by list cleanup" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\fn releaseRows(rows: *std.ArrayList(Owner), gpa: std.mem.Allocator) void {
        \\    for (rows.items) |*row| row.release(gpa);
        \\    rows.deinit(gpa);
        \\}
    );
}

test "free-without-null-then-check: precision canonical atomic retirement" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    active: std.atomic.Value(bool) = .init(true),
        \\    pub fn retire(self: *Owner, gpa: std.mem.Allocator) void {
        \\        if (!self.active.swap(false, .acq_rel)) return;
        \\        gpa.free(self.bytes);
        \\    }
        \\};
    );
}

test "free-without-null-then-check: precision retained copied header still dangles" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: Owner, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\fn invalid(gpa: std.mem.Allocator) !u8 {
        \\    const owner: Owner = .{ .bytes = try gpa.alloc(u8, 4) };
        \\    owner.release(gpa);
        \\    return owner.bytes[0];
        \\}
    );
}

test "free-without-null-then-check: precision resetting header does not repair borrowed backing" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn invalid(self: *Owner, gpa: std.mem.Allocator) u8 {
        \\        const old = self.bytes;
        \\        gpa.free(self.bytes);
        \\        self.bytes = &.{};
        \\        return old[0];
        \\    }
        \\};
    );
}

test "free-without-null-then-check: precision destructor scope cannot hide payload UAF" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    pub fn deinit(self: *Owner, gpa: std.mem.Allocator) u8 {
        \\        gpa.free(self.bytes);
        \\        return self.bytes[0];
        \\    }
        \\};
    );
}

test "free-without-null-then-check: precision destructor scope cannot hide repeated free" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRuleTyped(gpa, check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    pub fn deinit(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        gpa.free(self.bytes);
        \\    }
        \\};
    );
    defer freeProblems(gpa, &problems);
    const first_release = for (problems.items) |problem| {
        if (std.mem.eql(u8, problem.rule_id, "free-without-null-then-check") and
            problem.start.line == 5 and problem.start.column == 13) break problem;
    } else return error.ExpectedRepeatedReleaseDiagnostic;
    try std.testing.expectEqualStrings("free-without-null-then-check", first_release.rule_id);
    try std.testing.expectEqual(@as(u32, 5), first_release.end.line);
    try std.testing.expectEqual(@as(u32, 17), first_release.end.column);
}

test "free-without-null-then-check: precision destructor scope cannot hide failed replacement" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    pub fn deinit(self: *Owner, gpa: std.mem.Allocator) !void {
        \\        gpa.free(self.bytes);
        \\        self.bytes = try gpa.alloc(u8, 4);
        \\    }
        \\};
    );
}

test "free-without-null-then-check: precision length reset does not repair raw pointer" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn invalid(self: *Owner, gpa: std.mem.Allocator) u8 {
        \\        gpa.free(self.bytes);
        \\        self.bytes.len = 0;
        \\        return self.bytes.ptr[0];
        \\    }
        \\};
    );
}

test "free-without-null-then-check: public release cannot close over one local caller" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    pub fn release(self: Owner, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\fn consume(gpa: std.mem.Allocator) !void {
        \\    const owner: Owner = .{ .bytes = try gpa.alloc(u8, 4) };
        \\    owner.release(gpa);
        \\}
    );
}

test "free-without-null-then-check: conditional caller consumption is not ALL-path" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\fn consume(owner: *Owner, gpa: std.mem.Allocator, discard: bool) void {
        \\    owner.release(gpa);
        \\    if (discard) gpa.destroy(owner);
        \\}
    );
}

test "free-without-null-then-check: caller error before consumption retains the stale owner" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: *Owner, gpa: std.mem.Allocator) void { gpa.free(self.bytes); }
        \\};
        \\fn consume(owner: *Owner, gpa: std.mem.Allocator, fail: bool) !void {
        \\    owner.release(gpa);
        \\    if (fail) return error.Retained;
        \\    gpa.destroy(owner);
        \\}
    );
}

test "free-without-null-then-check: switch reset must cover every arm" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator, choose: bool) void {
        \\        gpa.free(self.bytes);
        \\        switch (choose) {
        \\            true => self.bytes = &.{},
        \\            false => self.bytes = &.{},
        \\        }
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator, choose: bool) void {
        \\        gpa.free(self.bytes);
        \\        switch (choose) {
        \\            true => self.bytes = &.{},
        \\            false => {},
        \\        }
        \\    }
        \\};
    );
}

test "free-without-null-then-check: catch reset covers only the error arm" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\fn maybe(fail: bool) !void { if (fail) return error.Failed; }
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator, fail: bool) void {
        \\        gpa.free(self.bytes);
        \\        maybe(fail) catch { self.bytes = &.{}; };
        \\    }
        \\};
    );
}

test "free-without-null-then-check: registered reset applies on each applicable exit" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator) void {
        \\        defer self.bytes = &.{};
        \\        gpa.free(self.bytes);
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator) !void {
        \\        errdefer self.bytes = &.{};
        \\        gpa.free(self.bytes);
        \\    }
        \\};
    );
}

test "free-without-null-then-check: complete branch resets retain stale aliases" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator, choose: bool) u8 {
        \\        const old = self.bytes;
        \\        gpa.free(self.bytes);
        \\        if (choose) self.bytes = &.{} else self.bytes = &.{};
        \\        return old[0];
        \\    }
        \\};
    );
}

test "free-without-null-then-check: allocator declaration outranks receiver spelling" {
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: *Owner, storage: std.mem.Allocator) void {
        \\        storage.free(self.bytes);
        \\    }
        \\};
    );
}

test "free-without-null-then-check: unresolved receiver retains legacy conservative fallback" {
    const gpa = std.testing.allocator;
    var problems = try testing.runRule(gpa, check,
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn release(self: *Owner, gpa: anytype) void {
        \\        gpa.free(self.bytes);
        \\    }
        \\};
    );
    defer freeProblems(gpa, &problems);
    try std.testing.expectEqual(@as(usize, 1), problems.items.len);
}

test "free-without-null-then-check: replacement expression must reset every result" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator, choose: bool) void {
        \\        gpa.free(self.bytes);
        \\        self.bytes = if (choose) &.{} else &.{};
        \\    }
        \\};
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator, choose: bool) void {
        \\        gpa.free(self.bytes);
        \\        self.bytes = switch (choose) { true => &.{}, false => &.{} };
        \\    }
        \\};
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        self.bytes = gpa.alloc(u8, 8) catch &.{};
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, "free-without-null-then-check",
        \\const std = @import("std");
        \\const Owner = struct {
        \\    bytes: []u8,
        \\    fn reset(self: *Owner, gpa: std.mem.Allocator) void {
        \\        gpa.free(self.bytes);
        \\        self.bytes = gpa.alloc(u8, 8) catch self.bytes;
        \\    }
        \\};
    );
}
