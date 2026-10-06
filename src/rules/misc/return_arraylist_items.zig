//! Detects `return identifier.items;` inside a function — returning the
//! `.items` slice of a local `ArrayList` directly leaks the backing
//! allocation: the caller receives a `[]T` slice but has no `ArrayList`
//! handle to call `.deinit()` on, so the capacity bytes are permanently
//! lost.  The correct form is `return list.toOwnedSlice()`, which transfers
//! ownership of exactly the used bytes to the caller.
//!
//! Real-world instance:
//!   - oven-sh/bun#23885 (toUTF8AllocWithType): the function built a local
//!     `var list = try std.ArrayList(u8).initCapacity(allocator, n)` and
//!     returned `list.items`.  The caller freed the returned slice via
//!     `allocator.free()`, which freed only `items.len` bytes; the extra
//!     capacity allocated by `initCapacity` leaked on every call.
//!     Fix: `return list.toOwnedSlice()`.
//!
//! Detection (Tier 1, flat token walk):
//!   Pattern: `keyword_return identifier period identifier("items") semicolon`
//!   — 5 tokens.  Fire at the `return` token.
//!   Suppresses `self`/`this` receivers (those access a struct field, not a
//!   local ArrayList).  `return list.toOwnedSlice()` does NOT match (ends
//!   with `l_paren` not `semicolon`).

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_model = @import("../../model/file_model.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const resolver_mod = @import("../../type_resolver.zig");
const tokens = @import("../../ast/tokens.zig");

const testing = @import("../../testing.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "return-arraylist-items";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .return_arraylist_items)) return;

    const tags = tree.tokens.items(.tag);
    const last_tok: Ast.TokenIndex = @intCast(tree.tokens.len -| 1);

    var t: Ast.TokenIndex = 0;
    while (t + 4 <= last_tok) : (t += 1) {
        // Pattern: return identifier . items ;
        if (tags[t] != .keyword_return) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .period) continue;
        if (tags[t + 3] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t + 3), "items")) continue;
        if (tags[t + 4] != .semicolon) continue;

        // Suppress self/this — those access a struct field, not a local ArrayList.
        const recv = tree.tokenSlice(t + 1);
        if (std.mem.eql(u8, recv, "self") or std.mem.eql(u8, recv, "this")) continue;

        // Suppress `assert(recv.items.len == recv.capacity)` + `return recv.items` —
        // when all capacity is used the caller can `allocator.free(slice)` and it
        // frees the exact allocation (items.len == capacity means no extra capacity
        // was allocated beyond what's returned).  Look for `recv . capacity` within
        // 30 tokens before the return statement.
        {
            const back: Ast.TokenIndex = 30;
            const scan_start: Ast.TokenIndex = if (t >= back) t - back else 0;
            var k = scan_start;
            var found_capacity = false;
            while (k + 2 < t) : (k += 1) {
                if (tags[k] != .identifier) continue;
                if (!std.mem.eql(u8, tree.tokenSlice(k), recv)) continue;
                if (tags[k + 1] != .period) continue;
                if (tags[k + 2] != .identifier) continue;
                if (std.mem.eql(u8, tree.tokenSlice(k + 2), "capacity")) {
                    found_capacity = true;
                    break;
                }
            }
            if (found_capacity) continue;
        }

        // Suppress only when every allocator that can grow this local list is
        // proven to come from an actual ArenaAllocator stored by a long-lived
        // receiver (or reached through a private, exhaustively-called helper).
        // A std.mem.Allocator parameter, an arbitrary pointer, or an
        // allocator-like method on another type is not evidence.
        if (listUsesArenaBackedAllocator(tree, cache, t, recv)) continue;

        if (recvIsPointerParam(tree, t, recv)) continue;

        try report(gpa, problems, tree, t);
    }
}

const ProofPath = struct {
    root: []const u8,
    root_token: Ast.TokenIndex,
    segments: [8][]const u8 = undefined,
    len: usize = 0,
};

const AggregateRange = struct {
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
};

const ArenaProof = struct {
    tree: *const Ast,
    model: *const file_model.FileModel,
    cache: *file_cache_mod.FileCache,

    fn listUsesArena(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        return_tok: Ast.TokenIndex,
        list_name: []const u8,
    ) bool {
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return false;
        const body_first = self.tree.firstToken(body);
        var saw_grow = false;
        var safe = true;

        var ni: u32 = 0;
        while (ni < self.tree.nodes.len) : (ni += 1) {
            const node: Ast.Node.Index = @enumFromInt(ni);
            const first = self.tree.firstToken(node);
            if (first < body_first or first >= return_tok) continue;
            if (tokens.enclosingFnDecl(self.tree, first) != fn_decl) continue;
            if (!isCallNode(self.tree.nodeTag(node))) continue;
            var call_buf: [1]Ast.Node.Index = undefined;
            const call = self.tree.fullCall(&call_buf, node) orelse continue;
            if (self.tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
            const access = self.tree.nodeData(call.ast.fn_expr).node_and_token;
            if (self.tree.nodeTag(access[0]) != .identifier) continue;
            if (!std.mem.eql(
                u8,
                self.tree.tokenSlice(self.tree.nodeMainToken(access[0])),
                list_name,
            )) continue;
            if (!isListMutator(self.tree.tokenSlice(access[1]))) continue;
            saw_grow = true;
            if (call.ast.params.len == 0) {
                safe = false;
                continue;
            }
            const arg = call.ast.params[0];
            if (!self.allocatorExprIsSafe(
                fn_decl,
                self.tree.firstToken(arg),
                self.tree.lastToken(arg),
                0,
            )) safe = false;
        }

        // `initCapacity` is a list allocation too, but its receiver is the
        // `ArrayList` type rather than the local list identifier.
        ni = 0;
        while (ni < self.tree.nodes.len) : (ni += 1) {
            const node: Ast.Node.Index = @enumFromInt(ni);
            switch (self.tree.nodeTag(node)) {
                .local_var_decl, .simple_var_decl, .aligned_var_decl => {},
                else => continue,
            }
            const decl = self.tree.fullVarDecl(node) orelse continue;
            const name_token = decl.ast.mut_token + 1;
            if (name_token >= return_tok or
                !std.mem.eql(u8, self.tree.tokenSlice(name_token), list_name))
                continue;
            if (tokens.enclosingFnDecl(self.tree, name_token) != fn_decl) continue;
            const init_node = decl.ast.init_node.unwrap() orelse continue;
            const call_node = unwrapTry(self.tree, init_node);
            var call_buf: [1]Ast.Node.Index = undefined;
            const call = self.tree.fullCall(&call_buf, call_node) orelse continue;
            if (self.tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
            const method = self.tree.nodeData(call.ast.fn_expr).node_and_token[1];
            const method_name = self.tree.tokenSlice(method);
            if (!std.mem.eql(u8, method_name, "initCapacity") and
                !std.mem.eql(u8, method_name, "init"))
                continue;
            saw_grow = true;
            if (call.ast.params.len == 0 or
                !self.allocatorExprIsSafe(
                    fn_decl,
                    self.tree.firstToken(call.ast.params[0]),
                    self.tree.lastToken(call.ast.params[0]),
                    0,
                )) safe = false;
        }
        return saw_grow and safe;
    }

    fn allocatorExprIsSafe(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
        depth: u8,
    ) bool {
        if (first > last or depth >= 16) return false;
        const tags = self.tree.tokens.items(.tag);
        var start = first;
        var end = last;
        while (start < end and tags[start] == .l_paren and tags[end] == .r_paren) {
            const close = tokens.matchParen(tags, start, end) orelse break;
            if (close != end) break;
            start += 1;
            end -= 1;
        }
        if (self.isArenaAllocatorCall(fn_decl, start, end)) return true;
        if (start == end and tags[start] == .identifier) {
            return self.identifierAllocatorIsSafe(fn_decl, start, depth + 1);
        }
        if (start + 2 == end and tags[start] == .identifier and
            tags[start + 1] == .period and tags[start + 2] == .identifier)
        {
            return self.contextFieldAllocatorIsSafe(fn_decl, start, end);
        }
        return false;
    }

    fn isArenaAllocatorCall(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) bool {
        const tags = self.tree.tokens.items(.tag);
        if (first > last or tags[first] != .identifier) return false;
        var path: ProofPath = .{
            .root = self.tree.tokenSlice(first),
            .root_token = first,
        };
        var t = first;
        while (true) {
            if (t + 2 > last or tags[t + 1] != .period or
                tags[t + 2] != .identifier)
                return false;
            const segment = self.tree.tokenSlice(t + 2);
            if (t + 3 <= last and tags[t + 3] == .l_paren) {
                if (!std.mem.eql(u8, segment, "allocator")) return false;
                return t + 4 <= last and tags[t + 4] == .r_paren and
                    t + 4 == last and self.pathIsArenaObject(fn_decl, &path);
            }
            if (path.len == path.segments.len) return false;
            path.segments[path.len] = segment;
            path.len += 1;
            t += 2;
        }
    }

    fn identifierAllocatorIsSafe(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        name_token: Ast.TokenIndex,
        depth: u8,
    ) bool {
        const name = self.tree.tokenSlice(name_token);
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        var params = proto.iterate(self.tree);
        var index: usize = 0;
        while (params.next()) |param| : (index += 1) {
            const token = param.name_token orelse continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(token), name)) continue;
            return self.allCallsUseArena(fn_decl, index, depth + 1);
        }
        if (self.findLocalDecl(fn_decl, name, name_token)) |decl| {
            const init_node = decl.ast.init_node.unwrap() orelse return false;
            return self.allocatorExprIsSafe(
                fn_decl,
                self.tree.firstToken(init_node),
                self.tree.lastToken(init_node),
                depth + 1,
            );
        }
        if (self.findGlobalDecl(name)) |decl| {
            const init_node = decl.ast.init_node.unwrap() orelse return false;
            return self.allocatorExprIsSafe(
                fn_decl,
                self.tree.firstToken(init_node),
                self.tree.lastToken(init_node),
                depth + 1,
            );
        }
        return false;
    }

    fn allCallsUseArena(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        parameter: usize,
        depth: u8,
    ) bool {
        if (depth >= 16 or !self.functionIsPrivate(fn_decl)) return false;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        const name_token = proto.name_token orelse return false;
        const name = self.tree.tokenSlice(name_token);
        var references: usize = 0;
        var t: Ast.TokenIndex = 0;
        while (t < self.tree.tokens.len) : (t += 1) {
            if (self.tree.tokenTag(t) != .identifier or
                !std.mem.eql(u8, self.tree.tokenSlice(t), name) or
                t == name_token)
                continue;
            if (self.model.containingTypeOf(fn_decl)) |owner| {
                if (!self.tokenMayReferenceMethod(owner, t)) continue;
            }
            references += 1;
        }

        var calls: usize = 0;
        var ni: u32 = 0;
        while (ni < self.tree.nodes.len) : (ni += 1) {
            const node: Ast.Node.Index = @enumFromInt(ni);
            if (!isCallNode(self.tree.nodeTag(node))) continue;
            var call_buf: [1]Ast.Node.Index = undefined;
            const call = self.tree.fullCall(&call_buf, node) orelse continue;
            if (!self.callTargetsFunction(fn_decl, call.ast.fn_expr)) continue;
            const caller = tokens.enclosingFnDecl(
                self.tree,
                self.tree.firstToken(node),
            ) orelse return false;
            const explicit_index = self.explicitArgumentIndex(fn_decl, parameter) orelse return false;
            if (explicit_index >= call.ast.params.len) return false;
            const arg = call.ast.params[explicit_index];
            if (!self.allocatorExprIsSafe(
                caller,
                self.tree.firstToken(arg),
                self.tree.lastToken(arg),
                depth + 1,
            )) return false;
            calls += 1;
        }
        return calls != 0 and calls == references;
    }

    fn tokenMayReferenceMethod(
        self: *const ArenaProof,
        owner: *const file_model.TypeInfo,
        token: Ast.TokenIndex,
    ) bool {
        const tags = self.tree.tokens.items(.tag);
        if (token + 1 < tags.len and tags[token + 1] == .colon) return false;
        if (token > 0 and tags[token - 1] == .period) {
            if (token + 1 < tags.len and tags[token + 1] == .equal) return false;
            for (self.tree.nodes.items(.tag), 0..) |tag, index| {
                if (tag != .field_access) continue;
                const node: Ast.Node.Index = @enumFromInt(index);
                if (self.tree.nodeData(node).node_and_token[1] != token) continue;
                return self.cache.intInfoOf(node) == null;
            }
            return true;
        }
        const caller = tokens.enclosingFnDecl(self.tree, token) orelse return false;
        return self.model.containingTypeOf(caller) == owner;
    }

    fn functionIsPrivate(self: *const ArenaProof, fn_decl: Ast.Node.Index) bool {
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        const name_token = proto.name_token orelse return false;
        var back = name_token;
        var scanned: usize = 0;
        while (back > 0 and scanned < 4) : (scanned += 1) {
            back -= 1;
            if (self.tree.tokenTag(back) == .keyword_export) return false;
        }
        const name = self.tree.tokenSlice(name_token);
        if (self.model.containingTypeOf(fn_decl)) |owner| {
            const method = owner.findMethod(name) orelse return false;
            return !method.is_pub;
        }
        for (self.model.fns) |function| {
            if (function.fn_decl == fn_decl) return !function.is_pub;
        }
        return false;
    }

    fn explicitArgumentIndex(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        parameter: usize,
    ) ?usize {
        const owner = self.model.containingTypeOf(fn_decl) orelse return parameter;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return null;
        const name = self.tree.tokenSlice(proto.name_token orelse return null);
        const method = owner.findMethod(name) orelse return null;
        if (method.receiver) |_| {
            if (parameter == 0) return null;
            return parameter - 1;
        }
        return parameter;
    }

    fn callTargetsFunction(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        fn_expr: Ast.Node.Index,
    ) bool {
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        const name = self.tree.tokenSlice(proto.name_token orelse return false);
        switch (self.tree.nodeTag(fn_expr)) {
            .identifier => {
                if (self.model.containingTypeOf(fn_decl) != null) return false;
                return std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(fn_expr)), name);
            },
            .enum_literal => {
                const owner = self.model.containingTypeOf(fn_decl) orelse return false;
                const method = owner.findMethod(name) orelse return false;
                if (method.receiver != null or
                    !std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(fn_expr)), name))
                    return false;
                const caller = tokens.enclosingFnDecl(self.tree, self.tree.firstToken(fn_expr)) orelse return false;
                return self.shorthandResultMatches(caller, fn_expr, owner);
            },
            .field_access => {
                const access = self.tree.nodeData(fn_expr).node_and_token;
                if (!std.mem.eql(u8, self.tree.tokenSlice(access[1]), name)) return false;
                const owner = self.model.containingTypeOf(fn_decl) orelse return false;
                const method = owner.findMethod(name) orelse return false;
                if (method.receiver == null) {
                    const receiver = terminalIdentifier(self.tree, access[0]) orelse return false;
                    return std.mem.eql(u8, receiver, owner.name);
                }
                return self.callReceiverHasType(access[0], owner.name);
            },
            else => return false,
        }
    }

    fn shorthandResultMatches(
        self: *const ArenaProof,
        caller_fn: Ast.Node.Index,
        fn_expr: Ast.Node.Index,
        result_type: *const file_model.TypeInfo,
    ) bool {
        const tags = self.tree.tokens.items(.tag);
        var first = self.tree.firstToken(fn_expr);
        if (first >= tags.len) return false;
        if (tags[first] != .period) {
            if (first == 0 or tags[first - 1] != .period) return false;
            first -= 1;
        }
        if (first == 0 or tags[first - 1] != .l_paren) return false;
        const open = first - 1;
        if (open == 0 or tags[open - 1] != .identifier) return false;
        const method_name = self.tree.tokenSlice(open - 1);
        var skip_receiver = false;
        const target_fn = target: {
            if (open >= 3 and tags[open - 2] == .period) {
                const receiver_path = pathEndingAt(self.tree, open - 3) orelse return false;
                const owner = self.pathFinalType(caller_fn, &receiver_path) orelse return false;
                const method = owner.findMethod(method_name) orelse return false;
                skip_receiver = method.receiver != null;
                break :target method.fn_decl;
            }
            for (self.model.fns) |function| {
                if (std.mem.eql(u8, function.name, method_name)) break :target function.fn_decl;
            }
            return false;
        };
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, target_fn) orelse return false;
        var params = proto.iterate(self.tree);
        if (skip_receiver and params.next() == null) return false;
        const result_param = params.next() orelse return false;
        const type_node = result_param.type_expr orelse return false;
        return self.tree.nodeTag(type_node) == .identifier and
            std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(type_node)), result_type.name);
    }

    fn callReceiverHasType(
        self: *const ArenaProof,
        receiver: Ast.Node.Index,
        type_name: []const u8,
    ) bool {
        if (self.tree.nodeTag(receiver) != .identifier) return false;
        const caller = tokens.enclosingFnDecl(self.tree, self.tree.firstToken(receiver)) orelse return false;
        const resolved = self.identifierTypeName(caller, self.tree.nodeMainToken(receiver)) orelse return false;
        return std.mem.eql(u8, resolved, type_name);
    }

    fn identifierTypeName(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        name_token: Ast.TokenIndex,
    ) ?[]const u8 {
        const name = self.tree.tokenSlice(name_token);
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return null;
        var params = proto.iterate(self.tree);
        while (params.next()) |param| {
            const token = param.name_token orelse continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(token), name)) continue;
            const type_node = param.type_expr orelse return null;
            return baseTypeName(self.tree, self.tree.firstToken(type_node), self.tree.lastToken(type_node));
        }
        const decl = self.findLocalDecl(fn_decl, name, name_token) orelse return null;
        const type_node = decl.ast.type_node.unwrap() orelse return null;
        return baseTypeName(self.tree, self.tree.firstToken(type_node), self.tree.lastToken(type_node));
    }

    fn pathIsArenaObject(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        path: *const ProofPath,
    ) bool {
        if (path.len == 0) {
            const decl = self.findGlobalDecl(path.root) orelse return false;
            const type_node = decl.ast.type_node.unwrap() orelse return false;
            return isArenaType(
                self.tree,
                self.tree.firstToken(type_node),
                self.tree.lastToken(type_node),
                0,
            );
        }
        var type_info = self.pathRootType(fn_decl, path) orelse return false;
        var i: usize = 0;
        while (i < path.len) : (i += 1) {
            const field = type_info.findField(path.segments[i]) orelse return false;
            if (i + 1 == path.len) {
                return isArenaType(self.tree, field.type_first, field.type_last, 0);
            }
            const field_type = baseTypeName(
                self.tree,
                field.type_first,
                field.type_last,
            ) orelse return false;
            type_info = self.model.findType(field_type) orelse return false;
        }
        return false;
    }

    fn pathRootType(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        path: *const ProofPath,
    ) ?*const file_model.TypeInfo {
        if (self.model.containingTypeOf(fn_decl)) |owner| {
            var proto_buf: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return null;
            const name = self.tree.tokenSlice(proto.name_token orelse return null);
            const method = owner.findMethod(name) orelse return null;
            if (method.receiver) |receiver| {
                if (receiver.is_ptr and std.mem.eql(u8, receiver.name, path.root) and
                    self.receiverTypeMatches(fn_decl, owner))
                    return owner;
            }
        }
        return null;
    }

    fn pathFinalType(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        path: *const ProofPath,
    ) ?*const file_model.TypeInfo {
        var type_info = self.pathRootType(fn_decl, path) orelse return null;
        var i: usize = 0;
        while (i < path.len) : (i += 1) {
            const field = type_info.findField(path.segments[i]) orelse return null;
            const field_type = baseTypeName(
                self.tree,
                field.type_first,
                field.type_last,
            ) orelse return null;
            type_info = self.model.findType(field_type) orelse return null;
        }
        return type_info;
    }

    fn receiverTypeMatches(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        owner: *const file_model.TypeInfo,
    ) bool {
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, fn_decl) orelse return false;
        var params = proto.iterate(self.tree);
        const receiver = params.next() orelse return false;
        const type_node = receiver.type_expr orelse return false;
        const pointer = self.tree.fullPtrType(type_node) orelse return false;
        if (pointer.size != .one) return false;
        const child = pointer.ast.child_type;
        if (std.mem.eql(u8, self.tree.getNodeSource(child), "@This()")) return true;
        return self.tree.nodeTag(child) == .identifier and
            std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(child)), owner.name);
    }

    fn contextFieldAllocatorIsSafe(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) bool {
        const field_name = self.tree.tokenSlice(last);
        const context_name = self.identifierTypeName(fn_decl, first) orelse return false;
        const context_info = self.model.findType(context_name) orelse return false;
        const field = context_info.findField(field_name) orelse return false;
        if (!isAllocatorType(self.tree, field.type_first, field.type_last, 0)) return false;
        if (!self.callbackRegistrationHasContext(fn_decl, context_info)) return false;

        const tags = self.tree.tokens.items(.tag);
        var writes: usize = 0;
        var safe_writes: usize = 0;
        var t: Ast.TokenIndex = 0;
        while (t < self.tree.tokens.len) : (t += 1) {
            if (t < 3 or tags[t] != .equal or tags[t - 1] != .identifier or
                tags[t - 2] != .period or
                !std.mem.eql(u8, self.tree.tokenSlice(t - 1), field_name))
                continue;
            const owner_fn = tokens.enclosingFnDecl(self.tree, t) orelse continue;
            const path = pathEndingAt(self.tree, t - 3) orelse continue;
            const owner = self.pathFinalType(owner_fn, &path) orelse continue;
            if (owner != context_info) continue;
            writes += 1;
            const value_start = t + 1;
            const semicolon = tokens.findStmtSemicolon(
                tags,
                value_start,
                @intCast(tags.len - 1),
            ) orelse continue;
            if (semicolon > value_start and self.allocatorExprIsSafe(
                owner_fn,
                value_start,
                semicolon - 1,
                0,
            )) safe_writes += 1;
        }

        // Also inspect `self.context = .{ .alloc = value }`.
        t = 0;
        while (t < self.tree.tokens.len) : (t += 1) {
            if (tags[t] != .equal or t == 0) continue;
            const lhs = pathEndingAt(self.tree, t - 1) orelse continue;
            const owner_fn = tokens.enclosingFnDecl(self.tree, t) orelse continue;
            const owner = self.pathFinalType(owner_fn, &lhs) orelse continue;
            if (owner != context_info) continue;
            var open = t + 1;
            if (open < tags.len and tags[open] == .period) open += 1;
            if (open >= tags.len or tags[open] != .l_brace) {
                writes += 1;
                continue;
            }
            const close = tokens.matchBrace(tags, open, @intCast(tags.len - 1)) orelse continue;
            var u = open + 1;
            var aggregate_depth: u32 = 0;
            while (u < close) : (u += 1) {
                switch (tags[u]) {
                    .l_brace, .l_paren, .l_bracket => aggregate_depth += 1,
                    .r_brace, .r_paren, .r_bracket => aggregate_depth -|= 1,
                    else => {},
                }
                if (aggregate_depth != 0 or tags[u] != .identifier or
                    !std.mem.eql(u8, self.tree.tokenSlice(u), field_name))
                    continue;
                if (u == 0 or tags[u - 1] != .period or u + 1 >= close or
                    tags[u + 1] != .equal)
                    continue;
                const value_start = u + 2;
                const value_end = aggregateFieldEnd(tags, value_start, close);
                writes += 1;
                if (value_end > value_start and self.allocatorExprIsSafe(
                    owner_fn,
                    value_start,
                    value_end - 1,
                    0,
                )) safe_writes += 1;
            }
            t = close;
        }
        return writes != 0 and writes == safe_writes;
    }

    fn callbackRegistrationHasContext(
        self: *const ArenaProof,
        callback_fn: Ast.Node.Index,
        context_info: *const file_model.TypeInfo,
    ) bool {
        if (!self.functionIsPrivate(callback_fn)) return false;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(self.tree, &proto_buf, callback_fn) orelse return false;
        const callback_token = proto.name_token orelse return false;
        const callback_name = self.tree.tokenSlice(callback_token);
        const tags = self.tree.tokens.items(.tag);
        var references: usize = 0;
        var t: Ast.TokenIndex = 0;
        while (t < self.tree.tokens.len) : (t += 1) {
            if (tags[t] != .identifier or
                !std.mem.eql(u8, self.tree.tokenSlice(t), callback_name) or
                t == callback_token)
                continue;
            if (t + 1 < tags.len and (tags[t + 1] == .colon or
                (t > 0 and tags[t - 1] == .period and tags[t + 1] == .equal)))
                continue;
            references += 1;
            if (t < 3 or tags[t - 3] != .period or
                !std.mem.eql(u8, self.tree.tokenSlice(t - 2), "candidates") or
                tags[t - 1] != .equal)
                return false;
            const aggregate = aggregateAround(tags, t) orelse return false;
            if (!self.aggregateHasContext(
                callback_fn,
                context_info,
                aggregate.first,
                aggregate.last,
            )) return false;
        }
        return references != 0;
    }

    fn aggregateHasContext(
        self: *const ArenaProof,
        callback_fn: Ast.Node.Index,
        context_info: *const file_model.TypeInfo,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) bool {
        const tags = self.tree.tokens.items(.tag);
        var t = first + 1;
        while (t + 3 < last) : (t += 1) {
            if (tags[t] != .period or tags[t + 1] != .identifier or
                !std.mem.eql(u8, self.tree.tokenSlice(t + 1), "ctx") or
                tags[t + 2] != .equal)
                continue;
            var value = t + 3;
            if (value + 2 >= last) continue;
            if (tags[value] == .builtin and
                std.mem.eql(u8, self.tree.tokenSlice(value), "@ptrCast") and
                tags[value + 1] == .l_paren)
                value += 2;
            if (tags[value] != .ampersand) continue;
            const path = pathForward(self.tree, value + 1, last) orelse continue;
            const owner_fn = tokens.enclosingFnDecl(self.tree, t) orelse callback_fn;
            const owner = self.pathFinalType(owner_fn, &path) orelse continue;
            if (owner == context_info) return true;
        }
        return false;
    }

    fn findLocalDecl(
        self: *const ArenaProof,
        fn_decl: Ast.Node.Index,
        name: []const u8,
        before: Ast.TokenIndex,
    ) ?Ast.full.VarDecl {
        const body = tokens.bodyOf(self.tree, fn_decl) orelse return null;
        const tags = self.tree.tokens.items(.tag);
        var best: ?Ast.full.VarDecl = null;
        var best_token: Ast.TokenIndex = 0;
        var ni: u32 = 0;
        while (ni < self.tree.nodes.len) : (ni += 1) {
            const node: Ast.Node.Index = @enumFromInt(ni);
            switch (self.tree.nodeTag(node)) {
                .local_var_decl, .simple_var_decl, .aligned_var_decl => {},
                else => continue,
            }
            const decl = self.tree.fullVarDecl(node) orelse continue;
            const name_token = decl.ast.mut_token + 1;
            if (name_token < self.tree.firstToken(body) or name_token >= before or
                name_token >= tags.len or tags[name_token] != .identifier or
                !std.mem.eql(u8, self.tree.tokenSlice(name_token), name))
                continue;
            if (best == null or name_token > best_token) {
                best = decl;
                best_token = name_token;
            }
        }
        return best;
    }

    fn findGlobalDecl(self: *const ArenaProof, name: []const u8) ?Ast.full.VarDecl {
        const tags = self.tree.tokens.items(.tag);
        for (self.tree.rootDecls()) |node| {
            const decl = self.tree.fullVarDecl(node) orelse continue;
            const name_token = decl.ast.mut_token + 1;
            if (name_token < tags.len and tags[name_token] == .identifier and
                std.mem.eql(u8, self.tree.tokenSlice(name_token), name))
                return decl;
        }
        return null;
    }
};

fn listUsesArenaBackedAllocator(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    return_tok: Ast.TokenIndex,
    list_name: []const u8,
) bool {
    const fn_decl = tokens.enclosingFnDecl(tree, return_tok) orelse return false;
    const model = cache.fileModel() catch return false;
    const proof = ArenaProof{ .tree = tree, .model = model, .cache = cache };
    return proof.listUsesArena(fn_decl, return_tok, list_name);
}

fn isCallNode(tag: Ast.Node.Tag) bool {
    return switch (tag) {
        .call, .call_comma, .call_one, .call_one_comma => true,
        else => false,
    };
}

fn isListMutator(name: []const u8) bool {
    return std.mem.eql(u8, name, "append") or
        std.mem.eql(u8, name, "appendSlice") or
        std.mem.eql(u8, name, "appendNTimes") or
        std.mem.eql(u8, name, "insert") or
        std.mem.eql(u8, name, "insertSlice") or
        std.mem.eql(u8, name, "replaceRange");
}

fn unwrapTry(tree: *const Ast, node: Ast.Node.Index) Ast.Node.Index {
    return if (tree.nodeTag(node) == .@"try") tree.nodeData(node).node else node;
}

fn terminalIdentifier(tree: *const Ast, node: Ast.Node.Index) ?[]const u8 {
    return switch (tree.nodeTag(node)) {
        .identifier => tree.tokenSlice(tree.nodeMainToken(node)),
        .field_access => tree.tokenSlice(tree.nodeData(node).node_and_token[1]),
        else => null,
    };
}

fn pathForward(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) ?ProofPath {
    const tags = tree.tokens.items(.tag);
    if (first > last or first >= tags.len or tags[first] != .identifier) return null;
    var path: ProofPath = .{
        .root = tree.tokenSlice(first),
        .root_token = first,
    };
    var t = first;
    while (t + 2 <= last and tags[t + 1] == .period and
        tags[t + 2] == .identifier)
    {
        if (path.len == path.segments.len) return null;
        path.segments[path.len] = tree.tokenSlice(t + 2);
        path.len += 1;
        t += 2;
    }
    if (t + 1 > last) return null;
    return switch (tags[t + 1]) {
        .r_paren, .comma, .r_brace => path,
        else => null,
    };
}
fn pathEndingAt(tree: *const Ast, last: Ast.TokenIndex) ?ProofPath {
    const tags = tree.tokens.items(.tag);
    if (last >= tags.len or tags[last] != .identifier) return null;
    var names: [8][]const u8 = undefined;
    var len: usize = 0;
    var t = last;
    while (true) {
        if (len == names.len) return null;
        names[len] = tree.tokenSlice(t);
        len += 1;
        if (t < 2 or tags[t - 1] != .period or tags[t - 2] != .identifier) break;
        t -= 2;
    }
    var path: ProofPath = .{
        .root = names[len - 1],
        .root_token = t,
        .len = len - 1,
    };
    var i: usize = 0;
    while (i < path.len) : (i += 1) {
        path.segments[i] = names[path.len - 1 - i];
    }
    return path;
}

fn baseTypeName(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    var t = first;
    while (t < last and (tags[t] == .asterisk or tags[t] == .keyword_const or
        tags[t] == .question_mark)) : (t += 1)
    {}
    return if (t == last and tags[t] == .identifier) tree.tokenSlice(t) else null;
}

fn isStdImport(tree: *const Ast, name: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    for (tree.rootDecls()) |node| {
        const decl = tree.fullVarDecl(node) orelse continue;
        const name_token = decl.ast.mut_token + 1;
        if (name_token >= tags.len or tags[name_token] != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(name_token), name))
            continue;
        const init_node = decl.ast.init_node.unwrap() orelse return false;
        return std.mem.eql(
            u8,
            std.mem.trim(u8, tree.getNodeSource(init_node), " \t\r\n"),
            "@import(\"std\")",
        );
    }
    return false;
}

fn isActualType(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    module: []const u8,
    type_name: []const u8,
    depth: u8,
) bool {
    if (depth >= 8 or first > last) return false;
    const tags = tree.tokens.items(.tag);
    var names: [3][]const u8 = undefined;
    var count: usize = 0;
    var t = first;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .asterisk, .keyword_const => {},
            .identifier => {
                if (count == names.len) return false;
                names[count] = tree.tokenSlice(t);
                count += 1;
            },
            .period => {},
            else => return false,
        }
    }
    if (count == 1) {
        for (tree.rootDecls()) |node| {
            const decl = tree.fullVarDecl(node) orelse continue;
            const name_token = decl.ast.mut_token + 1;
            if (name_token >= tags.len or
                !std.mem.eql(u8, tree.tokenSlice(name_token), names[0]))
                continue;
            const init_node = decl.ast.init_node.unwrap() orelse return false;
            return isActualType(
                tree,
                tree.firstToken(init_node),
                tree.lastToken(init_node),
                module,
                type_name,
                depth + 1,
            );
        }
        return false;
    }
    return count == 3 and std.mem.eql(u8, names[0], "std") and
        std.mem.eql(u8, names[1], module) and
        std.mem.eql(u8, names[2], type_name) and isStdImport(tree, "std");
}

fn isArenaType(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex, depth: u8) bool {
    return isActualType(tree, first, last, "heap", "ArenaAllocator", depth);
}

fn isAllocatorType(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex, depth: u8) bool {
    return isActualType(tree, first, last, "mem", "Allocator", depth);
}

fn aggregateFieldEnd(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    close: Ast.TokenIndex,
) Ast.TokenIndex {
    var depth: u32 = 0;
    var t = first;
    while (t < close) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => depth -|= 1,
            .comma => if (depth == 0) return t,
            else => {},
        }
    }
    return close;
}

fn aggregateAround(
    tags: []const std.zig.Token.Tag,
    token: Ast.TokenIndex,
) ?AggregateRange {
    if (tags.len == 0) return null;
    var best: ?AggregateRange = null;
    var open: Ast.TokenIndex = 0;
    while (open < token) : (open += 1) {
        if (tags[open] != .l_brace) continue;
        const close = tokens.matchBrace(tags, open, @intCast(tags.len - 1)) orelse continue;
        if (close < token) continue;
        if (best == null or open > best.?.first)
            best = .{ .first = open, .last = close };
    }
    return best;
}

/// True iff `recv` is a pointer-typed parameter of the function enclosing `tok`.
fn recvIsPointerParam(tree: *const Ast, tok: Ast.TokenIndex, recv: []const u8) bool {
    // Innermost fn_decl containing `tok` (largest firstToken).  Keep only the
    // proto NODE — `fullFnProto` stores params in a local buf that must outlive
    // the iteration, so resolve the proto here, not in a helper that returns it.
    var best_proto: ?Ast.Node.Index = null;
    var best_first: Ast.TokenIndex = 0;
    var ni: u32 = 0;
    while (ni < tree.nodes.len) : (ni += 1) {
        const node: Ast.Node.Index = @enumFromInt(ni);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const ft = tree.firstToken(node);
        if (tok < ft or tok > tree.lastToken(node)) continue;
        if (best_proto == null or ft > best_first) {
            best_proto = tree.nodeData(node).node_and_node[0];
            best_first = ft;
        }
    }
    const proto_node = best_proto orelse return false;
    var buf: [1]Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&buf, proto_node) orelse return false;
    var it = proto.iterate(tree);
    while (it.next()) |p| {
        const nt = p.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(nt), recv)) continue;
        const te = p.type_expr orelse return false;
        return switch (tree.nodeTag(te)) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => true,
            else => false,
        };
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    return_tok: Ast.TokenIndex,
) !void {
    const recv = tree.tokenSlice(return_tok + 1);
    const msg = try std.fmt.allocPrint(
        gpa,
        "`return {s}.items` — the caller receives a slice but cannot free the ArrayList's backing allocation; use `return {s}.toOwnedSlice()` to transfer ownership of exactly the used bytes, or document that this is an intentional borrow",
        .{ recv, recv },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = Pos.fromTokenStart(tree, return_tok),
        .end = Pos.fromTokenEnd(tree, return_tok + 4),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "return-arraylist-items: fires" {
    try testing.expectFires(check, R,
        \\fn convert(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, input.len);
        \\    try list.appendSlice(input);
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: toOwnedSlice does not fire" {
    try testing.expectNoFire(check,
        \\fn convert(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, input.len);
        \\    try list.appendSlice(input);
        \\    return list.toOwnedSlice();
        \\}
        \\
    );
}

test "return-arraylist-items: self.items does not fire" {
    try testing.expectNoFire(check,
        \\const Buf = struct { items: []u8 };
        \\fn getItems(self: *Buf) []u8 {
        \\    return self.items;
        \\}
        \\
    );
}

test "return-arraylist-items: this.items does not fire" {
    try testing.expectNoFire(check,
        \\const Buf = struct { items: []u8 };
        \\fn getItems(this: *Buf) []u8 {
        \\    return this.items;
        \\}
        \\
    );
}

test "return-arraylist-items: full-capacity assert suppresses" {
    try testing.expectNoFire(check,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var array = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    try fill(&array);
        \\    assert(array.items.len == array.capacity);
        \\    return array.items;
        \\}
        \\
    );
}

test "return-arraylist-items: no capacity check still fires" {
    try testing.expectFires(check, R,
        \\fn build(allocator: Allocator) ![]u8 {
        \\    var list = try std.ArrayList(u8).initCapacity(allocator, 64);
        \\    try list.appendSlice(data);
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: pointer param (caller-owned) suppresses" {
    try testing.expectNoFire(check,
        \\fn collect(out: *std.ArrayList(u8)) []u8 {
        \\    out.append(1) catch {};
        \\    return out.items;
        \\}
        \\
    );
}

test "return-arraylist-items: by-value param still fires (post-append realloc leaks)" {
    try testing.expectFires(check, R,
        \\fn collect(list: std.ArrayList(u8)) []u8 {
        \\    return list.items;
        \\}
        \\
    );
}

test "return-arraylist-items: declared receiver arena owns returned backing storage" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    pub fn render(self: *Context) []const u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "skript regression: caller allocator output still needs ownership transfer" {
    try testing.expectFires(check, R,
        \\fn render(allocator: std.mem.Allocator) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(allocator, 'x') catch {};
        \\    return out.items;
        \\}
        \\
    );
}

test "return-arraylist-items: private call chain preserves declared arena origin" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Allocator = std.mem.Allocator;
        \\fn own(memory: Allocator, raw: []const u8) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.appendSlice(memory, raw) catch {};
        \\    return out.items;
        \\}
        \\fn hang(memory: Allocator, raw: []const u8) []const u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.appendSlice(memory, raw) catch {};
        \\    return out.items;
        \\}
        \\const Capture = struct {
        \\    fn end(self: *Capture, memory: Allocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(memory, 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const Query = struct {
        \\    text: []const u8,
        \\    fn submit(memory: Allocator) Query {
        \\        var capture: Capture = .{};
        \\        return .{ .text = hang(memory, own(memory, capture.end(memory))) };
        \\    }
        \\};
        \\fn add(_: Query) void {}
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn evaluate(self: *Model) void {
        \\        add(.submit(self.arena.allocator()));
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: integer fields do not escape a same-named arena method" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Capture = struct {
        \\    fn end(self: *Capture, allocator: std.mem.Allocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(allocator, 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Model) []const u8 {
        \\        var capture: Capture = .{};
        \\        return capture.end(self.arena.allocator());
        \\    }
        \\};
        \\const Range = struct { end: usize };
        \\pub fn length(range: Range) usize {
        \\    const end = range.end;
        \\    return end;
        \\}
    ;
    const gpa = std.testing.allocator;
    var context: resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-arena-method-identity.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer testing.freeProblems(gpa, &problems);
    try check(gpa, tree, &cache, &config_mod.Default, &problems);
    try std.testing.expectEqual(@as(usize, 0), problems.items.len);
}

test "return-arraylist-items: unknown receivers do not select a same-named arena method" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    fn end(self: *Capture, allocator: std.mem.Allocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(allocator, 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Model, receiver: anytype) []const u8 {
        \\        return receiver.end(self.arena.allocator());
        \\    }
        \\};
    );
}

test "return-arraylist-items: escaped method references still require ownership transfer" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    fn end(self: *Capture, allocator: std.mem.Allocator) []const u8 {
        \\        _ = self;
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(allocator, 'x') catch {};
        \\        return out.items;
        \\    }
        \\};
        \\const escaped = Capture.end;
        \\pub fn render(allocator: std.mem.Allocator) []const u8 {
        \\    var capture: Capture = .{};
        \\    return escaped(&capture, allocator);
        \\}
    );
}

test "return-arraylist-items: mixed private callers remain diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn collect(memory: std.mem.Allocator) []u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 1) catch {};
        \\    return out.items;
        \\}
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn safe(self: *Model) []u8 {
        \\        return collect(self.arena.allocator());
        \\    }
        \\};
        \\pub fn external(memory: std.mem.Allocator) []u8 {
        \\    return collect(memory);
        \\}
        \\
    );
}

test "return-arraylist-items: public allocator helper remains diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\pub fn collect(memory: std.mem.Allocator) []u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 1) catch {};
        \\    return out.items;
        \\}
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn safe(self: *Model) []u8 {
        \\        return collect(self.arena.allocator());
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: mixed arena and heap mutations remain diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Context = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    fn render(self: *Context, memory: std.mem.Allocator) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 1) catch {};
        \\        out.append(memory, 2) catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: allocator-like method on non-arena field remains diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const FauxArena = struct {
        \\    fn allocator(_: *FauxArena) std.mem.Allocator {
        \\        return std.heap.page_allocator;
        \\    }
        \\};
        \\const Context = struct {
        \\    arena: FauxArena,
        \\    fn render(self: *Context) []u8 {
        \\        var out: std.ArrayList(u8) = .empty;
        \\        out.append(self.arena.allocator(), 1) catch {};
        \\        return out.items;
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: unrelated pointer does not prove allocator lifetime" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const State = struct {};
        \\fn render(_: *State, memory: std.mem.Allocator) []u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(memory, 1) catch {};
        \\    return out.items;
        \\}
        \\
    );
}

test "return-arraylist-items: arbitrary model pointer does not prove arena lifetime" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Model = struct { arena: std.heap.ArenaAllocator };
        \\fn render(model: *Model) []u8 {
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(model.arena.allocator(), 1) catch {};
        \\    return out.items;
        \\}
        \\
    );
}

test "return-arraylist-items: callback context field initialized from declared arena" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const CompletionCtx = struct { alloc: std.mem.Allocator };
        \\fn candidates(ctx: *const anyopaque) []u8 {
        \\    const cctx: *const CompletionCtx = @ptrCast(@alignCast(ctx));
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(cctx.alloc, 1) catch {};
        \\    return out.items;
        \\}
        \\const Provider = struct {
        \\    ctx: *const anyopaque,
        \\    candidates: *const fn (*const anyopaque) []u8,
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    completion_ctx: CompletionCtx,
        \\    provider: Provider,
        \\    fn init(self: *Model) void {
        \\        self.* = .{
        \\            .arena = .init(std.heap.page_allocator),
        \\            .completion_ctx = undefined,
        \\            .provider = undefined,
        \\        };
        \\        self.completion_ctx = .{ .alloc = self.arena.allocator() };
        \\        self.provider = .{
        \\            .ctx = @ptrCast(&self.completion_ctx),
        \\            .candidates = candidates,
        \\        };
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: mixed callback context writes remain diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const CompletionCtx = struct { alloc: std.mem.Allocator };
        \\fn candidates(ctx: *const anyopaque) []u8 {
        \\    const cctx: *const CompletionCtx = @ptrCast(@alignCast(ctx));
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(cctx.alloc, 1) catch {};
        \\    return out.items;
        \\}
        \\const Provider = struct {
        \\    ctx: *const anyopaque,
        \\    candidates: *const fn (*const anyopaque) []u8,
        \\};
        \\const Model = struct {
        \\    arena: std.heap.ArenaAllocator,
        \\    completion_ctx: CompletionCtx,
        \\    provider: Provider,
        \\    fn init(self: *Model) void {
        \\        self.completion_ctx = .{ .alloc = self.arena.allocator() };
        \\        self.provider = .{
        \\            .ctx = @ptrCast(&self.completion_ctx),
        \\            .candidates = candidates,
        \\        };
        \\    }
        \\    pub fn replaceContext(self: *Model, memory: std.mem.Allocator) void {
        \\        self.completion_ctx = .{ .alloc = memory };
        \\    }
        \\};
        \\
    );
}

test "return-arraylist-items: externally supplied callback context remains diagnosed" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const CompletionCtx = struct { alloc: std.mem.Allocator };
        \\fn candidates(ctx: *const anyopaque) []u8 {
        \\    const cctx: *const CompletionCtx = @ptrCast(@alignCast(ctx));
        \\    var out: std.ArrayList(u8) = .empty;
        \\    out.append(cctx.alloc, 1) catch {};
        \\    return out.items;
        \\}
        \\const Provider = struct {
        \\    ctx: *const anyopaque,
        \\    candidates: *const fn (*const anyopaque) []u8,
        \\};
        \\pub fn install(ctx: *const anyopaque) Provider {
        \\    return .{ .ctx = ctx, .candidates = candidates };
        \\}
        \\
    );
}
