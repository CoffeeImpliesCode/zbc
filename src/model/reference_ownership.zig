//! Declaration-bound reference effects. Unknown evidence is never a safety certificate.
const std = @import("std");
const Ast = std.zig.Ast;
const file_cache_mod = @import("../cache/file_cache.zig");
const call_summary = @import("../cache/call_summary.zig");
const fresh_storage = @import("../cache/fresh_storage.zig");
const bindings_mod = @import("local_bindings.zig");
const resolver_mod = @import("../type_resolver.zig");
const budget_mod = @import("../budget.zig");
const Pos = @import("../problem.zig").Pos;
const Iterator = @import("type_engine").AstIterator;
const tokens = @import("../ast/tokens.zig");
const hasTokenInRange = tokens.hasTokenInRange;

pub const CounterField = struct {
    tree: *const Ast,
    declaration: Ast.Node.Index,
    payload_key: ?[]const u8 = null,
    instance: Ast.Node.Index = .root,
    returns_resource: bool = false,
};

pub const ReferenceFrame = struct {
    cache: *file_cache_mod.FileCache,
    resolution: resolver_mod.TypeResolver.ResolutionFrame,
    declaration: Ast.Node.Index,
    body: Ast.Node.Index,
    bindings: bindings_mod.LocalBindings,
    selected: Ast.TokenIndex,
    selected_path: ?[]const u8 = null,
    actual: ?file_cache_mod.FileCache.ActualCallSummary = null,
    caller_cache: ?*file_cache_mod.FileCache = null,
    // Recursive cleanup frames borrow stack parents. Returned acquisition
    // frames have no parent; their actual call authenticates the root caller.
    caller: ?*const ReferenceFrame = null,
};

/// Source trees, binding tables and frames borrow their canonical caches.
pub const Increment = struct {
    counter: CounterField,
    frame: ReferenceFrame,
    formal: u32,
    argument: Ast.Node.Index,
};

pub const Acquisition = union(enum) {
    /// Source, type, or exact instance identity could not be established.
    unknown,
    /// Source is visible but supplies no positive increment certificate.
    refused,
    increment: Increment,
};

pub const ReleaseProtocol = struct {
    tree: *const Ast,
    declaration: Ast.Node.Index,
    field: []const u8,
};

/// One shared work allowance covers acquisition and related error handoff.
/// Only `increment` is positive evidence; neither other result proves safety.
pub const Query = struct {
    remaining: u32 = call_summary.actual_query_work_limit,

    fn charge(self: *Query, tree: *const Ast, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!void {
        if (depth >= 64 or self.remaining == 0) {
            const pos = try Pos.fromTokenStart(tree, tree.firstToken(node));
            return budget_mod.fail(.{
                .limit = if (depth >= 64) .normal_cleanup_depth else .normal_cleanup_nodes,
                .limit_value = if (depth >= 64) 64 else call_summary.actual_query_work_limit,
                .reached = if (depth >= 64) depth else call_summary.actual_query_work_limit,
                .byte = pos.byte,
                .document = budget_mod.documentForTree(tree),
                .line = pos.line,
                .column = pos.column,
            });
        }
        self.remaining -= 1;
    }

    pub fn acquisitionAt(self: *Query, cache: *file_cache_mod.FileCache, token: Ast.TokenIndex) file_cache_mod.SummaryError!Acquisition {
        const actual = (try cache.actualCallSummaryAt(token, cache.cleanup_frame)) orelse return .unknown;
        return self.acquisitionFromActual(cache, actual, null, null);
    }

    /// Source-slot identity only: never an ownership or release certificate.
    pub fn namesResource(self: *Query, cache: *file_cache_mod.FileCache, bindings: *const bindings_mod.LocalBindings, node: Ast.Node.Index, selected: Ast.TokenIndex, path: []const u8) file_cache_mod.SummaryError!bool {
        return self.exactResource(cache, bindings, node, selected, path, 0);
    }

    const ActualResource = struct {
        bindings: *const bindings_mod.LocalBindings,
        selected: Ast.TokenIndex,
        path: []const u8,
    };

    fn acquisitionFromActual(
        self: *Query,
        cache: *file_cache_mod.FileCache,
        actual: file_cache_mod.FileCache.ActualCallSummary,
        resource: ?ActualResource,
        release: ?ReferenceFrame,
    ) file_cache_mod.SummaryError!Acquisition {
        var parameter: u32 = 0;
        while (true) : (parameter += 1) {
            var buffer: [2]Ast.Node.Index = undefined;
            const argument = (try actual.callArgumentFor(cache, &buffer, parameter)) orelse break;
            if (resource) |selected| {
                if (!try self.exactResource(cache, selected.bindings, argument, selected.selected, selected.path, 0)) continue;
            }
            const context = (try self.calleeFrame(cache, actual, parameter)) orelse return .unknown;
            if (try self.incrementCounter(context, context.body, release, 0)) |counter| {
                return .{ .increment = .{ .counter = counter, .frame = context, .formal = parameter, .argument = argument } };
            }
        }
        return .refused;
    }

    /// Authenticate the actual argument against the existing owned source.
    /// A copied aggregate, an arbitrary call, or an unknown field is not an alias.
    pub fn acquisitionForResourceAt(
        self: *Query,
        cache: *file_cache_mod.FileCache,
        token: Ast.TokenIndex,
        proto: Ast.full.FnProto,
        body: Ast.Node.Index,
        source_token: Ast.TokenIndex,
        path: []const u8,
        copy: Ast.TokenIndex,
        protocol: ReleaseProtocol,
    ) file_cache_mod.SummaryError!Acquisition {
        const actual = (try cache.actualCallSummaryAt(token, cache.cleanup_frame)) orelse return .unknown;
        // Snapshot the borrowed table view before another localBindings query
        // can rehash its memo entry. The item allocation remains cache-owned.
        const bindings = (try cache.localBindings(proto, body)).*;
        // source_token is a declaration identity, not a token in its live
        // scope. Authenticate that identity at the actual copy use.
        const source = (bindings.findAt(cache.tree.tokenSlice(source_token), copy) orelse return .unknown).*;
        if (source.name_token != source_token) return .unknown;
        if (!try self.resourceUnchanged(cache, &bindings, source.name_token, path, cache.tree.lastToken(actual.callee.call_node), copy, 0)) return .refused;
        const owner_frame = (try self.releaseOwnerFrame(cache, copy, protocol)) orelse return .unknown;
        const declaring = if (protocol.tree == cache.tree and owner_frame.handle.module == cache.module_id) cache else
            &(try @import("../cache/grow_analysis.zig").sourceDocument(cache, owner_frame.handle, owner_frame.resolver.ctx)).cache;
        var buffer: [1]Ast.Node.Index = undefined;
        const release_proto = tokens.fnProto(protocol.tree, &buffer, protocol.declaration) orelse return .unknown;
        const release_body = tokens.bodyOf(protocol.tree, protocol.declaration) orelse return .unknown;
        var parameters = release_proto.iterate(protocol.tree);
        const receiver = parameters.next() orelse return .unknown;
        const release: ReferenceFrame = .{
            .cache = declaring, .resolution = owner_frame,
            .declaration = protocol.declaration, .body = release_body,
            .bindings = (try declaring.localBindings(release_proto, release_body)).*,
            .selected = receiver.name_token orelse return .unknown, .selected_path = protocol.field,
        };
        return self.acquisitionFromActual(cache, actual, .{ .bindings = &bindings, .selected = source.name_token, .path = path }, release);
    }

    fn releaseOwnerFrame(
        self: *Query,
        cache: *file_cache_mod.FileCache,
        copy: Ast.TokenIndex,
        protocol: ReleaseProtocol,
    ) file_cache_mod.SummaryError!?resolver_mod.TypeResolver.ResolutionFrame {
        const resolver = cache.zls orelse return null;
        const frame = cache.cleanup_frame orelse resolver.resolutionFrame();
        if (cache.nodeForExactSpan(copy, copy)) |node| {
            if (try frame.containerOfNode(node)) |container| {
                if (try self.protocolContainer(frame, container, protocol)) |owner| return owner;
            }
        }
        var selected: ?resolver_mod.TypeResolver.ResolutionFrame = null;
        var width: Ast.TokenIndex = std.math.maxInt(Ast.TokenIndex);
        for (cache.tree.nodes.items(.tag), 0..) |_, index| {
            const node: Ast.Node.Index = @enumFromInt(index);
            const first = cache.tree.firstToken(node);
            const last = cache.tree.lastToken(node);
            if (copy < first or copy > last or last - first >= width) continue;
            var buffer: [2]Ast.Node.Index = undefined;
            const literal = cache.tree.fullStructInit(&buffer, node) orelse continue;
            try self.charge(cache.tree, node, 0);
            var ty = if (literal.ast.type_expr == .none)
                (try frame.expectedTypeOfNode(node)) orelse continue
            else
                (try frame.typeOfNode(node)) orelse continue;
            ty = (try resolver.normalizedType(ty)) orelse continue;
            while (resolver.typeTag(ty) == .optional) {
                try self.charge(cache.tree, node, 0);
                ty = resolver.childType(ty) orelse break;
            }
            if (ty.data != .container) continue;
            if (try self.protocolContainer(frame, ty.data.container, protocol)) |owner| {
                selected = owner;
                width = last - first;
            }
        }
        return selected;
    }

    fn protocolContainer(
        self: *Query,
        frame: resolver_mod.TypeResolver.ResolutionFrame,
        container: resolver_mod.TypeResolver.ActualType.Data.Container,
        protocol: ReleaseProtocol,
    ) file_cache_mod.SummaryError!?resolver_mod.TypeResolver.ResolutionFrame {
        const tree = &container.scope_handle.handle.document.tree;
        if (tree != protocol.tree) return null;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return null;
        for (declaration.ast.members) |member| {
            try self.charge(tree, member, 0);
            if (member == protocol.declaration) return frame.resolver.frameForContainer(container);
        }
        return null;
    }

    const ResourceHorizon = enum { runtime, lexical };

    fn exactResource(
        self: *Query,
        cache: *file_cache_mod.FileCache,
        bindings: *const bindings_mod.LocalBindings,
        node: Ast.Node.Index,
        selected: Ast.TokenIndex,
        path: []const u8,
        depth: u32,
    ) file_cache_mod.SummaryError!bool {
        return self.exactResourceIn(cache, bindings, node, selected, path, depth, .runtime);
    }

    fn exactResourceIn(self: *Query, cache: *file_cache_mod.FileCache, bindings: *const bindings_mod.LocalBindings, node: Ast.Node.Index, selected: Ast.TokenIndex, path: []const u8, depth: u32, horizon: ResourceHorizon) file_cache_mod.SummaryError!bool {
        const tree = cache.tree;
        try self.charge(tree, node, depth);
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                const binding = bindings.findAt(tree.tokenSlice(token), token) orelse return false;
                if (binding.name_token == selected) return path.len == 0;
                if (binding.origin == .param) return false;
                const value = if (binding.origin == .loop_capture)
                    (try self.successCaptureSource(cache, binding.*, depth + 1)) orelse return false
                else
                    cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
                if (value == node) return false;
                if (!try self.resourceUnchangedIn(cache, bindings, binding.name_token, "", binding.rhs_last, token, depth + 1, horizon)) return false;
                if (!try self.resourceUnchangedIn(cache, bindings, selected, path, binding.rhs_last, token, depth + 1, horizon)) return false;
                return self.exactResourceIn(cache, bindings, value, selected, path, depth + 1, horizon);
            },
            .field_access => {
                const base, const field = tree.nodeData(node).node_and_token;
                const split = std.mem.lastIndexOfScalar(u8, path, '.');
                const name = if (split) |at| path[at + 1 ..] else path;
                if (!std.mem.eql(u8, name, tree.tokenSlice(field))) return false;
                return self.exactResourceIn(cache, bindings, base, selected, if (split) |at| path[0..at] else "", depth + 1, horizon);
            },
            .deref, .address_of => return self.exactResourceIn(cache, bindings, tree.nodeData(node).node, selected, path, depth + 1, horizon),
            .grouped_expression, .unwrap_optional => return self.exactResourceIn(cache, bindings, tree.nodeData(node).node_and_token[0], selected, path, depth + 1, horizon),
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                var buffer: [2]Ast.Node.Index = undefined;
                const arguments = tree.builtinCallParams(&buffer, node) orelse return false;
                if (arguments.len != 1 or !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@constCast")) return false;
                return self.exactResourceIn(cache, bindings, arguments[0], selected, path, depth + 1, horizon);
            },
            else => return false,
        }
    }

    /// Only an if/while success payload preserves its exact scrutinee value.
    /// A for element, error payload, or switch capture is not that value.
    fn successCaptureSource(self: *Query, cache: *file_cache_mod.FileCache, binding: bindings_mod.Binding, depth: u32) file_cache_mod.SummaryError!?Ast.Node.Index {
        const declaration = tokens.enclosingFnDecl(cache.tree, binding.name_token) orelse return null;
        const body = tokens.bodyOf(cache.tree, declaration) orelse return null;
        return self.successCaptureIn(cache, body, binding, depth);
    }

    fn successCaptureIn(self: *Query, cache: *file_cache_mod.FileCache, node: Ast.Node.Index, binding: bindings_mod.Binding, depth: u32) file_cache_mod.SummaryError!?Ast.Node.Index {
        const tree = cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl or binding.name_token < tree.firstToken(node) or binding.name_token > tree.lastToken(node)) return null;
        const Payload = struct { token: Ast.TokenIndex, value: Ast.Node.Index };
        const payload: ?Payload = if (tree.fullIf(node)) |branch|
            if (branch.payload_token) |token| .{ .token = token, .value = branch.ast.cond_expr } else null
        else if (tree.fullWhile(node)) |loop|
            if (loop.payload_token) |token| .{ .token = token, .value = loop.ast.cond_expr } else null
        else null;
        if (payload) |success| {
            const name = success.token + @intFromBool(tree.tokenTag(success.token) == .asterisk);
            if (name == binding.name_token and tree.firstToken(success.value) == binding.rhs_first and tree.lastToken(success.value) == binding.rhs_last)
                return success.value;
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            if (try self.successCaptureIn(cache, child, binding, depth + 1)) |value| return value;
        return null;
    }

    /// Initializer provenance stops at a write to that exact slot or an
    /// enclosing slot. Taking its address also prevents a stale alias proof.
    fn resourceUnchanged(
        self: *Query,
        cache: *file_cache_mod.FileCache,
        bindings: *const bindings_mod.LocalBindings,
        selected: Ast.TokenIndex,
        path: []const u8,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
        depth: u32,
    ) file_cache_mod.SummaryError!bool {
        return self.resourceUnchangedIn(cache, bindings, selected, path, first, last, depth, .runtime);
    }

    const MutationWindow = struct {
        first: Ast.TokenIndex,
        use: Ast.TokenIndex,
        end: Ast.TokenIndex,
        registration: ?Ast.Node.Index,
    };

    fn resourceUnchangedIn(self: *Query, cache: *file_cache_mod.FileCache, bindings: *const bindings_mod.LocalBindings, selected: Ast.TokenIndex, path: []const u8, first: Ast.TokenIndex, last: Ast.TokenIndex, depth: u32, horizon: ResourceHorizon) file_cache_mod.SummaryError!bool {
        const declaration = tokens.enclosingFnDecl(cache.tree, last) orelse return false;
        const body = tokens.bodyOf(cache.tree, declaration) orelse return false;
        const registration = if (horizon == .runtime) try self.deferredRegistration(cache, body, last, depth + 1) else null;
        return self.resourceUnchangedNode(cache, bindings, body, selected, path, .{
            .first = first,
            .use = last,
            .end = if (registration != null) cache.tree.lastToken(body) else last,
            .registration = registration,
        }, false, depth);
    }

    /// Locate the actual deferred body, not a registration-value snapshot.
    fn deferredRegistration(self: *Query, cache: *file_cache_mod.FileCache, node: Ast.Node.Index, use: Ast.TokenIndex, depth: u32) file_cache_mod.SummaryError!?Ast.Node.Index {
        const tree = cache.tree;
        try self.charge(tree, node, depth);
        if (use < tree.firstToken(node) or use > tree.lastToken(node)) return null;
        switch (tree.nodeTag(node)) {
            .fn_decl => return null,
            .@"defer", .@"errdefer" => return node,
            else => {},
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            if (try self.deferredRegistration(cache, child, use, depth + 1)) |registration| return registration;
        return null;
    }

    /// Identify a possible writer before its own effect. This lexical
    /// projection cannot recursively assume the later cleanup horizon.
    fn mutationNamesResource(self: *Query, cache: *file_cache_mod.FileCache, bindings: *const bindings_mod.LocalBindings, node: Ast.Node.Index, selected: Ast.TokenIndex, path: []const u8, include_selected: bool, depth: u32) file_cache_mod.SummaryError!bool {
        var end = if (include_selected or path.len == 0) path.len else std.mem.lastIndexOfScalar(u8, path, '.') orelse 0;
        while (true) {
            if (try self.exactResourceIn(cache, bindings, node, selected, path[0..end], depth + 1, .lexical)) return true;
            if (end == 0) break;
            end = std.mem.lastIndexOfScalar(u8, path[0..end], '.') orelse 0;
        }
        return false;
    }

    /// A source-readable by-value aggregate formal copies its outer header.
    /// Writes through fields can affect pointees, not the caller's header cell.
    /// This says nothing about reference balance or pointee lifetime.
    fn copiesOwnerHeader(self: *Query, cache: *file_cache_mod.FileCache, actual: file_cache_mod.FileCache.ActualCallSummary, parameter: usize, token: Ast.TokenIndex, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        try self.charge(cache.tree, node, depth);
        if (tokens.bodyOf(actual.callee.tree, actual.callee.declaration) == null) return false;
        const function = switch (actual.callee.reference.actual_type.data) {
            .function => |function| function,
            else => return false,
        };
        if (parameter >= function.parameters.len) return false;
        const resolver = if (actual.callee.caller_frame) |frame| frame.resolver else cache.zls orelse return false;
        const ty = (try resolver.normalizedType(function.parameters[parameter].type)) orelse return false;
        if (ty.data != .container) return false;
        // A copied formal does not excuse globals or an unread callback.
        return (try cache.callEffectAt(token, .unrooted, .{ .frame = actual.callee.caller_frame, .remaining = &self.remaining })) == .read_only;
    }

    fn resourceUnchangedNode(self: *Query, cache: *file_cache_mod.FileCache, bindings: *const bindings_mod.LocalBindings, node: Ast.Node.Index, selected: Ast.TokenIndex, path: []const u8, window: MutationWindow, selected_cleanup: bool, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = cache.tree;
        try self.charge(tree, node, depth);
        const at = tree.firstToken(node);
        var in_cleanup = selected_cleanup;
        var limit = if (in_cleanup) window.use else window.end;
        if (tree.lastToken(node) <= window.first or at >= limit) return true;
        const lhs: ?Ast.Node.Index = switch (tree.nodeTag(node)) {
            .fn_decl => return true,
            .@"defer", .@"errdefer" => block: {
                if (at <= window.use and window.use <= tree.lastToken(node)) {
                    // Only this cleanup's prefix precedes the selected read.
                    // Its later header clear cannot revoke a saved scalar.
                    in_cleanup = true;
                    limit = window.use;
                } else if (window.registration) |registration| {
                    if (at <= tree.firstToken(registration)) return true;
                    // Later registrations can execute before this cleanup.
                } else return true;
                break :block null;
            },
            .assign, .assign_add, .assign_add_wrap, .assign_add_sat,
            .assign_sub, .assign_sub_wrap, .assign_sub_sat, .assign_mul,
            .assign_mul_wrap, .assign_mul_sat, .assign_div, .assign_mod,
            .assign_shl, .assign_shl_sat, .assign_shr, .assign_bit_and,
            .assign_bit_or, .assign_bit_xor => tree.nodeData(node).node_and_node[0],
            .address_of => tree.nodeData(node).node,
            .assign_destructure => return false,
            else => null,
        };
        if (at > window.first and tree.lastToken(node) < limit) {
            if (lhs) |written| {
                if (try self.mutationNamesResource(cache, bindings, written, selected, path, true, depth + 1)) return false;
            }
            if (!(at <= window.use and window.use <= tree.lastToken(node))) {
                var buffer: [2]Ast.Node.Index = undefined;
                if (resolver_mod.TypeResolver.CallOperands.full(tree, &buffer, node)) |call| {
                    var actual: ?file_cache_mod.FileCache.ActualCallSummary = null;
                    var queried = false;
                    if (tree.nodeTag(call.ast.fn_expr) == .field_access) {
                        const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
                        if (try self.mutationNamesResource(cache, bindings, receiver, selected, path, true, depth + 1)) {
                            if (path.len == 0) return false;
                            actual = try cache.actualCallSummaryAt(tree.nodeMainToken(call.ast.fn_expr), cache.cleanup_frame);
                            queried = true;
                            const known = actual orelse return false;
                            if (known.argument_offset != 1 or !try self.copiesOwnerHeader(cache, known, 0, tree.nodeMainToken(call.ast.fn_expr), node, depth + 1)) return false;
                        }
                    }
                    // An enclosing owner can expose the selected slot.
                    // Explicit slot addresses are also checked as escapes.
                    for (call.ast.params, 0..) |argument, index| {
                        if (!try self.mutationNamesResource(cache, bindings, argument, selected, path, false, depth + 1)) continue;
                        if (path.len == 0) return false;
                        if (!queried) {
                            actual = try cache.actualCallSummaryAt(tree.nodeMainToken(call.ast.fn_expr), cache.cleanup_frame);
                            queried = true;
                        }
                        const known = actual orelse return false;
                        const offset = known.argument_offset orelse return false;
                        if (!try self.copiesOwnerHeader(cache, known, index + offset, tree.nodeMainToken(call.ast.fn_expr), node, depth + 1)) return false;
                    }
                }
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            if (!try self.resourceUnchangedNode(cache, bindings, child, selected, path, window, in_cleanup, depth + 1)) return false;
        return true;
    }

    fn calleeFrame(
        _: *Query,
        cache: *file_cache_mod.FileCache,
        actual: file_cache_mod.FileCache.ActualCallSummary,
        parameter: u32,
    ) file_cache_mod.SummaryError!?ReferenceFrame {
        const declaring = (try actual.declaringCache(cache)) orelse return null;
        const resolver = if (actual.callee.caller_frame) |frame| frame.resolver else cache.zls orelse return null;
        const tree = declaring.tree;
        const body = tokens.bodyOf(tree, actual.callee.declaration) orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, actual.callee.declaration) orelse return null;
        var params = proto.iterate(tree);
        var index: u32 = 0;
        while (params.next()) |param| : (index += 1) {
            if (index != parameter) continue;
            return .{
                .cache = declaring,
                .resolution = resolver.frameForFunction(actual.callee.reference),
                .declaration = actual.callee.declaration,
                .body = body,
                .bindings = (try declaring.localBindings(proto, body)).*,
                .selected = param.name_token orelse return null,
                .actual = actual,
                .caller_cache = cache,
            };
        }
        return null;
    }

    pub fn errorCleanupMayConsume(
        self: *Query,
        cache: *file_cache_mod.FileCache,
        proto: Ast.full.FnProto,
        body: Ast.Node.Index,
        acquisition: Ast.TokenIndex,
        after: Ast.TokenIndex,
    ) file_cache_mod.SummaryError!bool {
        const resolver = cache.zls orelse return false;
        const tree = cache.tree;
        const bindings = (try cache.localBindings(proto, body)).*;
        var retained: ?Ast.TokenIndex = null;
        for (bindings.items) |binding| {
            if (binding.origin == .param or binding.origin == .loop_capture) continue;
            if (binding.rhs_first <= acquisition and acquisition <= binding.rhs_last) {
                retained = binding.name_token;
                break;
            }
        }
        const selected = retained orelse return false;
        const declaration = tokens.enclosingFnDecl(tree, acquisition) orelse return false;
        var caller: ReferenceFrame = .{
            .cache = cache,
            .resolution = resolver.resolutionFrame(),
            .declaration = declaration,
            .body = body,
            .bindings = bindings,
            .selected = selected,
        };
        // A field-access AST is indexed by its period, not its name token.
        // The token walk reports the name; use the same call coordinate as
        // every later canonical callee query.
        if (acquisition == 0 or tree.tokenTag(acquisition - 1) != .period) return false;
        const acquired = switch (try self.acquisitionAt(cache, acquisition - 1)) {
            .increment => |increment| increment,
            .unknown, .refused => return false,
        };
        caller.selected_path = acquired.counter.payload_key;
        const later = try self.scanLaterTries(caller, body, after, &acquired, 0);
        return later.seen and later.protected;
    }

    const LaterTries = struct { seen: bool = false, protected: bool = true };

    fn scanLaterTries(self: *Query, caller: ReferenceFrame, node: Ast.Node.Index, after: Ast.TokenIndex, counter: *const Increment, depth: u32) file_cache_mod.SummaryError!LaterTries {
        const tree = caller.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl) return .{};
        if (tree.nodeTag(node) == .@"try" and tree.firstToken(node) > after) {
            const value = tree.nodeData(node).node;
            var buffer: [1]Ast.Node.Index = undefined;
            if (tree.fullCall(&buffer, value)) |call| {
                const token = fresh_storage.calleeQueryToken(tree, call);
                if (try caller.cache.actualCallSummaryAt(token, caller.resolution)) |actual| {
                    var parameter: u32 = 0;
                    while (true) : (parameter += 1) {
                        var argument_buffer: [2]Ast.Node.Index = undefined;
                        const argument = (try actual.callArgumentFor(caller.cache, &argument_buffer, parameter)) orelse break;
                        if (!try self.depends(caller, argument, depth + 1)) continue;
                        var payload_path = caller.selected_path;
                        if (!try self.directOrMovedArgument(caller, argument, &payload_path, depth + 1)) continue;
                        var callee = (try self.calleeFrame(caller.cache, actual, parameter)) orelse continue;
                        callee.caller = &caller;
                        callee.selected_path = payload_path;
                        if (try self.registeredCleanup(callee, counter, depth + 1)) return .{ .seen = true };
                    }
                }
            }
            return .{ .seen = true, .protected = false };
        }
        var result: LaterTries = .{};
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            const child_result = try self.scanLaterTries(caller, child, after, counter, depth + 1);
            result.seen = result.seen or child_result.seen;
            result.protected = result.protected and child_result.protected;
        }
        return result;
    }

    fn directOrMovedArgument(self: *Query, caller: ReferenceFrame, node: Ast.Node.Index, payload_path: *?[]const u8, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = caller.cache.tree;
        try self.charge(tree, node, depth);
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                const binding = caller.bindings.findAt(tree.tokenSlice(token), token) orelse return false;
                if (binding.name_token == caller.selected) return true;
                if (binding.origin == .param) return false;
                const value = caller.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
                if (value == node) return false;
                return self.directOrMovedArgument(caller, value, payload_path, depth + 1);
            },
            .grouped_expression => return self.directOrMovedArgument(caller, tree.nodeData(node).node_and_token[0], payload_path, depth + 1),
            .address_of, .deref => return self.directOrMovedArgument(caller, tree.nodeData(node).node, payload_path, depth + 1),
            else => {},
        }
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse return false;
        const actual = (try caller.cache.actualCallSummaryAt(fresh_storage.calleeQueryToken(tree, call), caller.resolution)) orelse return false;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const receiver = (try actual.callArgumentFor(caller.cache, &argument_buffer, 0)) orelse return false;
        if (!try self.depends(caller, receiver, depth + 1)) return false;
        var callee = (try self.calleeFrame(caller.cache, actual, 0)) orelse return false;
        callee.selected_path = caller.selected_path;
        var block_buffer: [2]Ast.Node.Index = undefined;
        const statements = callee.cache.tree.blockStatements(&block_buffer, callee.body) orelse return false;
        var cleared: ?Ast.TokenIndex = null;
        for (statements) |statement| {
            if (callee.cache.tree.nodeTag(statement) == .assign) {
                const pair = callee.cache.tree.nodeData(statement).node_and_node;
                if (callee.cache.tree.nodeTag(pair[0]) == .deref and
                    callee.cache.tree.nodeTag(pair[1]) == .struct_init_dot_two and
                    try self.depends(callee, callee.cache.tree.nodeData(pair[0]).node, depth + 1))
                {
                    var literal_buffer: [2]Ast.Node.Index = undefined;
                    const literal = callee.cache.tree.fullStructInit(&literal_buffer, pair[1]).?;
                    if (literal.ast.fields.len == 0) cleared = callee.cache.tree.firstToken(statement);
                }
            }
            if (callee.cache.tree.nodeTag(statement) == .@"return") {
                const returned = callee.cache.tree.nodeData(statement).opt_node.unwrap() orelse return false;
                return if (cleared) |clear|
                    try self.savedPayload(callee, returned, clear, payload_path, depth + 1)
                else false;
            }
            if (hasTokenInRange(callee.cache.tree.tokens.items(.tag), callee.cache.tree.firstToken(statement), callee.cache.tree.lastToken(statement), .keyword_try)) return false;
        }
        return false;
    }

    fn registeredCleanup(self: *Query, callee: ReferenceFrame, counter: *const Increment, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = callee.cache.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const statements = tree.blockStatements(&buffer, callee.body) orelse return false;
        for (statements) |statement| {
            try self.charge(tree, statement, depth);
            if (tree.nodeTag(statement) == .@"errdefer") {
                if (try self.cleanupCalls(callee, statement, counter, depth + 1)) return true;
                continue;
            }
            if (tree.fullVarDecl(statement)) |binding| {
                const value = binding.ast.init_node.unwrap() orelse continue;
                if (tree.nodeTag(value) == .identifier) continue;
            }
            // A registration following a branch, return, or fallible call
            // cannot explain an earlier propagated error.
            break;
        }
        return false;
    }

    fn cleanupCalls(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, counter: *const Increment, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl) return false;
        if (tree.fullIf(node)) |conditional| {
            if (tree.nodeTag(conditional.ast.cond_expr) == .identifier) {
                const value = tree.tokenSlice(tree.nodeMainToken(conditional.ast.cond_expr));
                if (std.mem.eql(u8, value, "true"))
                    return self.cleanupCalls(context, conditional.ast.then_expr, counter, depth + 1);
                if (std.mem.eql(u8, value, "false")) {
                    const other = conditional.ast.else_expr.unwrap() orelse return false;
                    return self.cleanupCalls(context, other, counter, depth + 1);
                }
            }
            if (conditional.payload_token == null or !try self.depends(context, conditional.ast.cond_expr, depth + 1)) return false;
            return self.cleanupCalls(context, conditional.ast.then_expr, counter, depth + 1);
        }
        var buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&buffer, node)) |call| {
            const token = fresh_storage.calleeQueryToken(tree, call);
            const actual = (try context.cache.actualCallSummaryAt(token, context.resolution)) orelse return false;
            var parameter: u32 = 0;
            while (true) : (parameter += 1) {
                var argument_buffer: [2]Ast.Node.Index = undefined;
                const argument = (try actual.callArgumentFor(context.cache, &argument_buffer, parameter)) orelse break;
                if (!try self.handoffArgument(context, argument, counter, depth + 1)) continue;
                var callee = (try self.calleeFrame(context.cache, actual, parameter)) orelse return false;
                callee.caller = &context;
                if (try self.forwardedPath(context, argument, depth + 1)) |forwarded| callee.selected_path = forwarded.path;
                if (try self.mayConsume(callee, callee.body, counter, depth + 1)) return true;
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            if (try self.cleanupCalls(context, child, counter, depth + 1)) return true;
        }
        return false;
    }

    fn mayConsume(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, counter: *const Increment, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl) return false;
        var block_buffer: [2]Ast.Node.Index = undefined;
        if (tree.blockStatements(&block_buffer, node)) |statements| {
            for (statements) |statement| {
                if (try self.mayConsume(context, statement, counter, depth + 1)) return true;
                if (try self.mayExitBeforeCleanup(context, statement, depth + 1)) return false;
            }
            return false;
        }
        if (tree.fullIf(node)) |conditional| {
            if (tree.nodeTag(conditional.ast.cond_expr) == .identifier) {
                const value = tree.tokenSlice(tree.nodeMainToken(conditional.ast.cond_expr));
                if (std.mem.eql(u8, value, "true"))
                    return self.mayConsume(context, conditional.ast.then_expr, counter, depth + 1);
                if (std.mem.eql(u8, value, "false")) {
                    const other = conditional.ast.else_expr.unwrap() orelse return false;
                    return self.mayConsume(context, other, counter, depth + 1);
                }
            }
            if (conditional.payload_token == null or !try self.depends(context, conditional.ast.cond_expr, depth + 1)) return false;
            return self.mayConsume(context, conditional.ast.then_expr, counter, depth + 1);
        }
        switch (tree.nodeTag(node)) {
            .assign_sub, .assign_sub_wrap, .assign_sub_sat => {
                const pair = tree.nodeData(node).node_and_node;
                if (!std.mem.eql(u8, tree.getNodeSource(pair[1]), "0") and
                    try self.depends(context, pair[0], depth + 1))
                {
                    const field = try self.counterField(context, pair[0], depth + 1);
                    if (field) |released| {
                        const selected = counter.counter;
                        var acquired_frame = counter.frame;
                        acquired_frame.selected_path = selected.payload_key;
                        if (selected.tree == released.tree and selected.declaration == released.declaration and
                            selected.returns_resource and
                            try self.sameInstance(context, pair[0], acquired_frame, selected.instance, depth + 1)) return true;
                    }
                }
            },
            else => {},
        }
        var buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&buffer, node)) |call| {
            if (tree.tokenTag(tree.nodeMainToken(node)) != .builtin) {
                const token = fresh_storage.calleeQueryToken(tree, call);
                const actual = (try context.cache.actualCallSummaryAt(token, context.resolution)) orelse return false;
                var parameter: u32 = 0;
                while (true) : (parameter += 1) {
                    var argument_buffer: [2]Ast.Node.Index = undefined;
                    const argument = (try actual.callArgumentFor(context.cache, &argument_buffer, parameter)) orelse break;
                    if (!try self.handoffArgument(context, argument, counter, depth + 1)) continue;
                    var callee = (try self.calleeFrame(context.cache, actual, parameter)) orelse return false;
                    callee.caller = &context;
                    if (try self.forwardedPath(context, argument, depth + 1)) |forwarded| callee.selected_path = forwarded.path;
                    if (try self.mayConsume(callee, callee.body, counter, depth + 1)) return true;
                }
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            if (try self.mayConsume(context, child, counter, depth + 1)) return true;
        }
        return false;
    }

    fn mayExitBeforeCleanup(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        switch (tree.nodeTag(node)) {
            .fn_decl => return false,
            .@"return", .@"break", .@"continue", .unreachable_literal => return true,
            else => {},
        }
        if (tree.fullIf(node)) |branch| {
            if (try context.resolution.boolValueOfNode(branch.ast.cond_expr)) |known| {
                if (known) return self.mayExitBeforeCleanup(context, branch.ast.then_expr, depth + 1);
                const other = branch.ast.else_expr.unwrap() orelse return false;
                return self.mayExitBeforeCleanup(context, other, depth + 1);
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            if (try self.mayExitBeforeCleanup(context, child, depth + 1)) return true;
        return false;
    }

    const ForwardedResource = struct { path: ?[]const u8 };

    fn resourceForward(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        return (try self.forwardedPath(context, node, depth)) != null;
    }

    fn forwardedPath(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!?ForwardedResource {
        var result: ?ForwardedResource = if (try self.exactResource(context.cache, &context.bindings, node, context.selected, "", depth))
            .{ .path = context.selected_path }
        else null;
        if (result == null) {
            const path = context.selected_path orelse return null;
            var end = path.len;
            while (end != 0) {
                if (try self.exactResource(context.cache, &context.bindings, node, context.selected, path[0..end], depth)) {
                    result = .{ .path = if (end == path.len) null else path[end + 1 ..] };
                    break;
                }
                end = std.mem.lastIndexOfScalar(u8, path[0..end], '.') orelse break;
            }
        }
        if (result != null) {
            if (context.selected_path) |path| {
                // Whole-header identity alone does not preserve a key field.
                // A by-reference success payload reads it at cleanup time.
                if (!try self.resourceUnchanged(context.cache, &context.bindings, context.selected, path, context.cache.tree.firstToken(context.body), context.cache.tree.firstToken(node), depth + 1)) return null;
            }
        }
        return result;
    }

    fn handoffArgument(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, acquired: *const Increment, depth: u32) file_cache_mod.SummaryError!bool {
        if (acquired.counter.payload_key != null) return self.depends(context, node, depth);
        return self.resourceForward(context, node, depth);
    }


    fn incrementCounter(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, release: ?ReferenceFrame, depth: u32) file_cache_mod.SummaryError!?CounterField {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl) return null;
        var unkeyed: ?CounterField = null;
        switch (tree.nodeTag(node)) {
            .assign_add => {
                const pair = tree.nodeData(node).node_and_node;
                if (tree.nodeTag(pair[1]) == .number_literal and
                    std.mem.eql(u8, tree.getNodeSource(pair[1]), "1") and
                    try self.depends(context, pair[0], depth + 1))
                {
                    if (try self.counterField(context, pair[0], depth + 1)) |field| {
                        var counter = field;
                        counter.instance = pair[0];
                        counter.payload_key = try self.counterKey(context, context.body, pair[0], counter, depth + 1);
                        counter.returns_resource = counter.payload_key != null or try self.returnsWholeResource(context, context.body, depth + 1);
                        if (counter.payload_key == null and release == null and !try self.hasCounterProtocol(context, counter, depth + 1)) return null;
                        const flow = try self.incrementFlow(context, context.body, counter, 0, depth + 1);
                        if (!flow.complete or (mergeProof(flow.next, flow.returned) orelse 0) <= 0) return null;
                        if (release) |selected| {
                            if (!try self.decrementsInstance(selected, selected.body, context, counter, depth + 1)) return null;
                        }
                        if (counter.payload_key != null) return counter;
                        unkeyed = counter;
                    }
                }
            },
            else => {},
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            if (try self.incrementCounter(context, child, release, depth + 1)) |counter| {
                if (counter.payload_key != null) return counter;
                if (unkeyed == null) unkeyed = counter;
            }
        }
        return unkeyed;
    }

    const IncrementFlow = struct {
        // Signed net unit change. The shared 50,000-work allowance bounds it.
        next: ?i32,
        returned: ?i32 = null,
        complete: bool = true,
    };

    fn mergeProof(left: ?i32, right: ?i32) ?i32 {
        if (left) |a| return if (right) |b| @min(a, b) else a;
        return right;
    }

    fn incrementFlow(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, counter: CounterField, incoming: i32, depth: u32) file_cache_mod.SummaryError!IncrementFlow {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        var block_buffer: [2]Ast.Node.Index = undefined;
        if (tree.blockStatements(&block_buffer, node)) |statements| {
            var result = IncrementFlow{ .next = incoming };
            for (statements) |statement| {
                const state = result.next orelse break;
                const next = try self.incrementFlow(context, statement, counter, state, depth + 1);
                result.returned = mergeProof(result.returned, next.returned);
                result.next = next.next;
                result.complete = result.complete and next.complete;
            }
            return result;
        }
        if (tree.fullIf(node)) |branch| {
            const condition = try self.incrementFlow(context, branch.ast.cond_expr, counter, incoming, depth + 1);
            const state = condition.next orelse return condition;
            const known = try context.resolution.boolValueOfNode(branch.ast.cond_expr);
            const yes = if (known != false)
                try self.incrementFlow(context, branch.ast.then_expr, counter, state, depth + 1)
            else IncrementFlow{ .next = null };
            const no = if (known != true) blk: {
                break :blk if (branch.ast.else_expr.unwrap()) |other|
                    try self.incrementFlow(context, other, counter, state, depth + 1)
                else IncrementFlow{ .next = state };
            } else IncrementFlow{ .next = null };
            return .{ .next = mergeProof(yes.next, no.next), .returned = mergeProof(condition.returned, mergeProof(yes.returned, no.returned)), .complete = condition.complete and yes.complete and no.complete };
        }
        switch (tree.nodeTag(node)) {
            .fn_decl => return .{ .next = incoming },
            .@"return" => {
                var delta = incoming;
                if (tree.nodeData(node).opt_node.unwrap()) |value| {
                    if (tree.nodeTag(value) == .error_value) return .{ .next = null };
                    const evaluated = try self.incrementFlow(context, value, counter, incoming, depth + 1);
                    if (!evaluated.complete) return .{ .next = null, .returned = 0, .complete = false };
                    delta = evaluated.next orelse 0;
                    if (counter.payload_key == null and counter.returns_resource and !try self.wholeForward(context, value, depth + 1))
                        return .{ .next = null, .returned = 0 };
                    if (counter.payload_key) |key| {
                        const returned = (try self.returnedCounterKey(context, value, counter.instance, counter, depth + 1)) orelse return .{ .next = null, .returned = 0 };
                        if (!std.mem.eql(u8, key, returned)) return .{ .next = null, .returned = 0 };
                    }
                }
                return .{ .next = null, .returned = delta };
            },
            .assign_add, .assign_sub,
            => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                const evaluated = try self.incrementChildren(context, node, counter, incoming, depth);
                if (!evaluated.complete or evaluated.next == null) return evaluated;
                if (!try self.sameInstance(context, lhs, context, counter.instance, depth + 1)) return evaluated;
                if (tree.nodeTag(rhs) != .number_literal or !std.mem.eql(u8, tree.getNodeSource(rhs), "1"))
                    return .{ .next = incoming, .complete = false };
                return .{ .next = evaluated.next.? + @as(i32, if (tree.nodeTag(node) == .assign_add) 1 else -1) };
            },
            .assign_add_wrap, .assign_add_sat, .assign_sub_wrap, .assign_sub_sat => {
                const lhs = tree.nodeData(node).node_and_node[0];
                return .{ .next = incoming, .complete = !try self.sameInstance(context, lhs, context, counter.instance, depth + 1) };
            },
            .assign, .assign_mul, .assign_mul_wrap, .assign_mul_sat, .assign_div, .assign_mod,
            .assign_shl, .assign_shl_sat, .assign_shr, .assign_bit_and, .assign_bit_or, .assign_bit_xor,
            => {
                const lhs = tree.nodeData(node).node_and_node[0];
                const evaluated = try self.incrementChildren(context, node, counter, incoming, depth);
                return .{
                    .next = evaluated.next,
                    .returned = evaluated.returned,
                    .complete = evaluated.complete and !try self.depends(context, lhs, depth + 1),
                };
            },
            .assign_destructure => return .{ .next = incoming, .complete = false },
            .unreachable_literal => return .{ .next = null },
            .@"while", .while_simple, .while_cont, .@"for", .for_simple, .@"switch", .switch_comma,
            .@"defer", .@"errdefer", .@"break", .@"continue", .@"orelse", .@"catch", .bool_and, .bool_or,
            => return .{ .next = incoming, .complete = false },
            else => {},
        }
        var call_buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&call_buffer, node)) |call| {
            var evaluated = try self.incrementChildren(context, node, counter, incoming, depth);
            if (evaluated.next == null) return evaluated;
            const token = fresh_storage.calleeQueryToken(tree, call);
            const actual = (try context.cache.actualCallSummaryAt(token, context.resolution)) orelse {
                evaluated.complete = false;
                return evaluated;
            };
            // Other formals and unrooted callbacks are not disjointness proof.
            evaluated.complete = evaluated.complete and
                (try context.cache.callEffectAt(token, .{ .whole = actual.callee }, .{ .frame = context.resolution, .remaining = &self.remaining })) == .read_only;
            return evaluated;
        }
        var builtin_buffer: [2]Ast.Node.Index = undefined;
        if (tree.builtinCallParams(&builtin_buffer, node)) |_| {
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            if (!std.mem.eql(u8, name, "@as") and !std.mem.eql(u8, name, "@ptrCast") and
                !std.mem.eql(u8, name, "@alignCast") and !std.mem.eql(u8, name, "@constCast"))
                return .{ .next = incoming, .complete = false };
        }
        return self.incrementChildren(context, node, counter, incoming, depth);
    }

    fn incrementChildren(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, counter: CounterField, incoming: i32, depth: u32) file_cache_mod.SummaryError!IncrementFlow {
        const tree = context.cache.tree;
        var result = IncrementFlow{ .next = incoming };
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            const state = result.next orelse break;
            const next = try self.incrementFlow(context, child, counter, state, depth + 1);
            result.returned = mergeProof(result.returned, next.returned);
            result.next = next.next;
            result.complete = result.complete and next.complete;
        }
        return result;
    }

    fn sameInstance(self: *Query, left: ReferenceFrame, lhs: Ast.Node.Index, right: ReferenceFrame, rhs: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        const a = left.cache.tree;
        const b = right.cache.tree;
        try self.charge(a, lhs, depth);
        if (left.selected_path != null or right.selected_path != null) {
            const left_resource = try self.exactResource(left.cache, &left.bindings, lhs, left.selected, left.selected_path orelse "", depth + 1);
            const right_resource = try self.exactResource(right.cache, &right.bindings, rhs, right.selected, right.selected_path orelse "", depth + 1);
            if (left_resource and right_resource) return true;
            if (left_resource != right_resource) return false;
        }
        switch (a.nodeTag(lhs)) {
            .grouped_expression => return self.sameInstance(left, a.nodeData(lhs).node_and_token[0], right, rhs, depth + 1),
            .deref, .address_of => return self.sameInstance(left, a.nodeData(lhs).node, right, rhs, depth + 1),
            else => {},
        }
        switch (b.nodeTag(rhs)) {
            .grouped_expression => return self.sameInstance(left, lhs, right, b.nodeData(rhs).node_and_token[0], depth + 1),
            .deref, .address_of => return self.sameInstance(left, lhs, right, b.nodeData(rhs).node, depth + 1),
            else => {},
        }
        if (a.nodeTag(lhs) == .identifier) {
            const token = a.nodeMainToken(lhs);
            const binding = left.bindings.findAt(a.tokenSlice(token), token) orelse return false;
            if (binding.name_token != left.selected and binding.is_const and binding.origin != .param) {
                if (!try self.resourceUnchanged(left.cache, &left.bindings, binding.name_token, "", binding.rhs_last, token, depth + 1)) return false;
                const value = left.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
                if (value == lhs) return false;
                return self.sameInstance(left, value, right, rhs, depth + 1);
            }
            if (binding.origin == .param and binding.name_token != left.selected) {
                if (try self.formalSource(left, binding.name_token)) |source|
                    return self.sameInstance(source.frame, source.node, right, rhs, depth + 1);
            }
        }
        if (b.nodeTag(rhs) == .identifier) {
            const token = b.nodeMainToken(rhs);
            const binding = right.bindings.findAt(b.tokenSlice(token), token) orelse return false;
            if (binding.name_token != right.selected and binding.is_const and binding.origin != .param) {
                if (!try self.resourceUnchanged(right.cache, &right.bindings, binding.name_token, "", binding.rhs_last, token, depth + 1)) return false;
                const value = right.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
                if (value == rhs) return false;
                return self.sameInstance(left, lhs, right, value, depth + 1);
            }
            if (binding.origin == .param and binding.name_token != right.selected) {
                if (try self.formalSource(right, binding.name_token)) |source|
                    return self.sameInstance(left, lhs, source.frame, source.node, depth + 1);
            }
        }
        if (a.nodeTag(lhs) != b.nodeTag(rhs)) return false;
        switch (a.nodeTag(lhs)) {
            .identifier => {
                const at = a.nodeMainToken(lhs);
                const bt = b.nodeMainToken(rhs);
                const ab = left.bindings.findAt(a.tokenSlice(at), at) orelse return false;
                const bb = right.bindings.findAt(b.tokenSlice(bt), bt) orelse return false;
                if (left.cache.tree == right.cache.tree and left.declaration == right.declaration and ab.name_token == bb.name_token) return true;
                return ab.name_token == left.selected and bb.name_token == right.selected;
            },
            .field_access => {
                const abase, const afield = a.nodeData(lhs).node_and_token;
                const bbase, const bfield = b.nodeData(rhs).node_and_token;
                return std.mem.eql(u8, a.tokenSlice(afield), b.tokenSlice(bfield)) and
                    try self.sameInstance(left, abase, right, bbase, depth + 1);
            },
            .array_access => {
                const abase, const ai = a.nodeData(lhs).node_and_node;
                const bbase, const bi = b.nodeData(rhs).node_and_node;
                return try self.sameInstance(left, abase, right, bbase, depth + 1) and
                    try self.sameIndexValue(left, ai, right, bi, depth + 1);
            },
            .number_literal => return std.mem.eql(u8, a.getNodeSource(lhs), b.getNodeSource(rhs)),
            else => return false,
        }
    }

    /// Counter indices are values, not cells. An immutable address-free copy
    /// keeps its initializer value after the source header is cleared.
    /// This projection is never used for counter owners or pointer identity.
    fn sameIndexValue(self: *Query, left: ReferenceFrame, lhs: Ast.Node.Index, right: ReferenceFrame, rhs: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        const a = left.cache.tree;
        const b = right.cache.tree;
        try self.charge(a, lhs, depth);
        const left_type = (try left.resolution.typeOfNode(lhs)) orelse return false;
        const right_type = (try right.resolution.typeOfNode(rhs)) orelse return false;
        if (!try fresh_storage.actualTypeAddressFree(left.resolution, left_type, 0, &self.remaining) or
            !try fresh_storage.actualTypeAddressFree(right.resolution, right_type, 0, &self.remaining)) return false;
        if (try self.immutableIndexInitializer(left, lhs, depth + 1)) |value|
            return self.sameIndexValue(left, value, right, rhs, depth + 1);
        if (try self.immutableIndexInitializer(right, rhs, depth + 1)) |value|
            return self.sameIndexValue(left, lhs, right, value, depth + 1);
        switch (a.nodeTag(lhs)) {
            .grouped_expression, .unwrap_optional => return self.sameIndexValue(left, a.nodeData(lhs).node_and_token[0], right, rhs, depth + 1),
            .deref, .address_of => return false,
            else => {},
        }
        switch (b.nodeTag(rhs)) {
            .grouped_expression, .unwrap_optional => return self.sameIndexValue(left, lhs, right, b.nodeData(rhs).node_and_token[0], depth + 1),
            .deref, .address_of => return false,
            else => {},
        }
        const left_resource = try self.exactResource(left.cache, &left.bindings, lhs, left.selected, left.selected_path orelse "", depth + 1);
        const right_resource = try self.exactResource(right.cache, &right.bindings, rhs, right.selected, right.selected_path orelse "", depth + 1);
        if (left_resource or right_resource) {
            if (!left_resource or !right_resource) return false;
            // Authenticate the value when THIS expression was evaluated.
            // Later writes cannot change a previously copied scalar value.
            return try self.resourceUnchanged(left.cache, &left.bindings, left.selected, left.selected_path orelse "", a.firstToken(left.body), a.firstToken(lhs), depth + 1) and
                try self.resourceUnchanged(right.cache, &right.bindings, right.selected, right.selected_path orelse "", b.firstToken(right.body), b.firstToken(rhs), depth + 1);
        }
        if (a.nodeTag(lhs) != b.nodeTag(rhs)) return false;
        switch (a.nodeTag(lhs)) {
            .identifier => return self.sameInstance(left, lhs, right, rhs, depth + 1),
            .field_access => {
                const abase, const afield = a.nodeData(lhs).node_and_token;
                const bbase, const bfield = b.nodeData(rhs).node_and_token;
                return std.mem.eql(u8, a.tokenSlice(afield), b.tokenSlice(bfield)) and
                    try self.sameIndexValue(left, abase, right, bbase, depth + 1);
            },
            .number_literal => return std.mem.eql(u8, a.getNodeSource(lhs), b.getNodeSource(rhs)),
            else => return false,
        }
    }

    /// The caller has proved this expression address-free. Only an immutable,
    /// unescaped local value can use its initializer as a saved snapshot.
    fn immutableIndexInitializer(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!?Ast.Node.Index {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) != .identifier) return null;
        const token = tree.nodeMainToken(node);
        const binding = context.bindings.findAt(tree.tokenSlice(token), token) orelse return null;
        if (binding.name_token == context.selected or !binding.is_const or binding.origin == .param or binding.origin == .loop_capture) return null;
        const value = context.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return null;
        if (value == node or !try self.resourceUnchanged(context.cache, &context.bindings, binding.name_token, "", binding.rhs_last, token, depth + 1)) return null;
        return value;
    }

    const FormalSource = struct { frame: ReferenceFrame, node: Ast.Node.Index };

    fn formalSource(_: *Query, context: ReferenceFrame, selected: Ast.TokenIndex) file_cache_mod.SummaryError!?FormalSource {
        const actual = context.actual orelse return null;
        const cache = context.caller_cache orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(context.cache.tree, &buffer, context.declaration) orelse return null;
        var parameters = proto.iterate(context.cache.tree);
        var index: u32 = 0;
        while (parameters.next()) |parameter| : (index += 1) {
            if (parameter.name_token != selected) continue;
            var arguments: [2]Ast.Node.Index = undefined;
            const argument = (try actual.callArgumentFor(cache, &arguments, index)) orelse return null;
            if (context.caller) |caller| return .{ .frame = caller.*, .node = argument };
            const declaration = tokens.enclosingFnDecl(cache.tree, cache.tree.firstToken(actual.callee.call_node)) orelse return null;
            const body = tokens.bodyOf(cache.tree, declaration) orelse return null;
            const caller_proto = tokens.fnProto(cache.tree, &buffer, declaration) orelse return null;
            return .{
                .frame = .{
                    .cache = cache,
                    .resolution = actual.callee.caller_frame orelse (cache.zls orelse return null).resolutionFrame(),
                    .declaration = declaration,
                    .body = body,
                    .bindings = (try cache.localBindings(caller_proto, body)).*,
                    .selected = std.math.maxInt(Ast.TokenIndex),
                },
                .node = argument,
            };
        }
        return null;
    }

    fn hasCounterProtocol(self: *Query, context: ReferenceFrame, counter: CounterField, depth: u32) file_cache_mod.SummaryError!bool {
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const tree = context.cache.tree;
        const proto = tokens.fnProto(tree, &proto_buffer, context.declaration) orelse return false;
        var parameters = proto.iterate(tree);
        while (parameters.next()) |parameter| {
            if (parameter.name_token != context.selected) continue;
            const type_node = parameter.type_expr orelse return false;
            const owner = (try context.resolution.containerOfNode(type_node)) orelse return false;
            const frame = context.resolution.resolver.frameForContainer(owner);
            const owner_tree = &owner.scope_handle.handle.document.tree;
            const declaring = if (owner_tree == context.cache.tree and frame.handle.module == context.cache.module_id) context.cache else
                &(try @import("../cache/grow_analysis.zig").sourceDocument(context.cache, frame.handle, frame.resolver.ctx)).cache;
            var container_buffer: [2]Ast.Node.Index = undefined;
            const container = owner_tree.fullContainerDecl(&container_buffer, owner.scope_handle.toNode()) orelse return false;
            for (container.ast.members) |member| {
                try self.charge(owner_tree, member, depth);
                const body = tokens.bodyOf(owner_tree, member) orelse continue;
                const member_proto = tokens.fnProto(owner_tree, &proto_buffer, member) orelse continue;
                var member_parameters = member_proto.iterate(owner_tree);
                const receiver = member_parameters.next() orelse continue;
                const release: ReferenceFrame = .{
                    .cache = declaring, .resolution = frame,
                    .declaration = member, .body = body,
                    .bindings = (try declaring.localBindings(member_proto, body)).*,
                    .selected = receiver.name_token orelse continue,
                };
                if (try self.decrementsInstance(release, body, context, counter, depth + 1)) return true;
            }
        }
        return false;
    }

    fn decrementsInstance(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, acquired: ReferenceFrame, counter: CounterField, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl) return false;
        var block_buffer: [2]Ast.Node.Index = undefined;
        if (tree.blockStatements(&block_buffer, node)) |statements| {
            for (statements) |statement| {
                if (try self.decrementsInstance(context, statement, acquired, counter, depth + 1)) return true;
                if (tree.nodeTag(statement) == .@"return" or tree.nodeTag(statement) == .unreachable_literal) break;
            }
            return false;
        }
        if (tree.fullIf(node)) |branch| {
            if (try context.resolution.boolValueOfNode(branch.ast.cond_expr)) |known| {
                if (known) return self.decrementsInstance(context, branch.ast.then_expr, acquired, counter, depth + 1);
                const other = branch.ast.else_expr.unwrap() orelse return false;
                return self.decrementsInstance(context, other, acquired, counter, depth + 1);
            }
        }
        switch (tree.nodeTag(node)) {
            .assign_sub, .assign_sub_wrap, .assign_sub_sat => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                if (tree.nodeTag(rhs) != .number_literal or !std.mem.eql(u8, tree.getNodeSource(rhs), "1")) return false;
                const field = (try self.counterField(context, lhs, depth + 1)) orelse return false;
                if (field.tree == counter.tree and field.declaration == counter.declaration and
                    try self.sameInstance(context, lhs, acquired, counter.instance, depth + 1)) return true;
            },
            else => {},
        }
        var call_buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&call_buffer, node)) |call| {
            const actual = (try context.cache.actualCallSummaryAt(fresh_storage.calleeQueryToken(tree, call), context.resolution)) orelse return false;
            var parameter: u32 = 0;
            while (true) : (parameter += 1) {
                var buffer: [2]Ast.Node.Index = undefined;
                const argument = (try actual.callArgumentFor(context.cache, &buffer, parameter)) orelse break;
                const forwarded = (try self.forwardedPath(context, argument, depth + 1)) orelse continue;
                var callee = (try self.calleeFrame(context.cache, actual, parameter)) orelse continue;
                callee.selected_path = forwarded.path;
                if (try self.decrementsInstance(callee, callee.body, acquired, counter, depth + 1)) return true;
            }
            return false;
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            if (try self.decrementsInstance(context, child, acquired, counter, depth + 1)) return true;
        return false;
    }

    fn counterField(self: *Query, context: ReferenceFrame, expression: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!?CounterField {
        const tree = context.cache.tree;
        try self.charge(tree, expression, depth);
        var node = expression;
        while (true) {
            node = switch (tree.nodeTag(node)) {
                .deref => tree.nodeData(node).node,
                .array_access => tree.nodeData(node).node_and_node[0],
                .grouped_expression => tree.nodeData(node).node_and_token[0],
                else => break,
            };
        }
        if (tree.nodeTag(node) != .field_access) return null;
        const base, const name_token = tree.nodeData(node).node_and_token;
        const container = (try context.resolution.containerOfNode(base)) orelse return null;
        const declaring_tree = &container.scope_handle.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = declaring_tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return null;
        for (declaration.ast.members) |member| {
            if (declaring_tree.fullContainerField(member) == null) continue;
            if (std.mem.eql(u8, declaring_tree.tokenSlice(declaring_tree.nodeMainToken(member)), tree.tokenSlice(name_token)))
                return .{ .tree = declaring_tree, .declaration = member };
        }
        return null;
    }

    fn depends(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl) return false;
        // Arithmetic on a key can select a different instance. Dependence
        // alone is not evidence that cleanup receives the acquired key.
        switch (tree.nodeTag(node)) {
            .add, .add_wrap, .add_sat, .sub, .sub_wrap, .sub_sat,
            .mul, .mul_wrap, .mul_sat, .div, .mod, .shl, .shr,
            .bit_and, .bit_or, .bit_xor,
            => return false,
            .field_access => {
                const base, const field = tree.nodeData(node).node_and_token;
                if (context.selected_path) |path| {
                    if (try self.wholeForward(context, base, depth + 1))
                        return std.mem.eql(u8, tree.tokenSlice(field), path);
                }
                return self.depends(context, base, depth + 1);
            },
            else => {},
        }
        if (tree.nodeTag(node) == .identifier) {
            const token = tree.nodeMainToken(node);
            const binding = context.bindings.findAt(tree.tokenSlice(token), token) orelse return false;
            if (binding.name_token == context.selected) return true;
            if (binding.origin == .param) return false;
            if (!try self.resourceUnchanged(context.cache, &context.bindings, binding.name_token, "", binding.rhs_last, token, depth + 1)) return false;
            const initializer = context.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
            if (initializer == node) return false;
            return self.depends(context, initializer, depth + 1);
        }
        var buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&buffer, node)) |call| {
            if (tree.tokenTag(tree.nodeMainToken(node)) != .builtin) {
                const actual = (try context.cache.actualCallSummaryAt(fresh_storage.calleeQueryToken(tree, call), context.resolution)) orelse {
                    var arguments = Iterator.init(tree, node);
                    while (arguments.next(tree)) |argument| if (try self.depends(context, argument, depth + 1)) return true;
                    return false;
                };
                var parameter: u32 = 0;
                while (true) : (parameter += 1) {
                    var argument_buffer: [2]Ast.Node.Index = undefined;
                    const argument = (try actual.callArgumentFor(context.cache, &argument_buffer, parameter)) orelse break;
                    if (!try self.depends(context, argument, depth + 1)) continue;
                    var callee = (try self.calleeFrame(context.cache, actual, parameter)) orelse return true;
                    if (try self.wholeForward(context, argument, depth + 1))
                        callee.selected_path = context.selected_path;
                    if (try self.returnDepends(callee, callee.body, depth + 1)) return true;
                }
                return false;
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| if (try self.depends(context, child, depth + 1)) return true;
        return false;
    }

    fn returnDepends(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl) return false;
        if (tree.nodeTag(node) == .@"return") {
            const value = tree.nodeData(node).opt_node.unwrap() orelse return false;
            return self.depends(context, value, depth + 1);
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| if (try self.returnDepends(context, child, depth + 1)) return true;
        return false;
    }

    fn wholeForward(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                const binding = context.bindings.findAt(tree.tokenSlice(token), token) orelse return false;
                if (binding.name_token == context.selected) return true;
                if (binding.origin == .param) return false;
                if (!try self.resourceUnchanged(context.cache, &context.bindings, binding.name_token, "", binding.rhs_last, token, depth + 1)) return false;
                const value = context.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
                if (value == node) return false;
                return self.wholeForward(context, value, depth + 1);
            },
            .deref, .address_of => return self.wholeForward(context, tree.nodeData(node).node, depth + 1),
            .grouped_expression, .unwrap_optional => return self.wholeForward(context, tree.nodeData(node).node_and_token[0], depth + 1),
            else => return false,
        }
    }

    fn returnsWholeResource(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl) return false;
        if (tree.nodeTag(node) == .@"return") {
            const value = tree.nodeData(node).opt_node.unwrap() orelse return false;
            return self.wholeForward(context, value, depth + 1);
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            if (try self.returnsWholeResource(context, child, depth + 1)) return true;
        return false;
    }

    fn counterSelectionDepends(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!bool {
        return (try self.indexSelection(context, node, depth)) orelse try self.depends(context, node, depth);
    }

    fn indexSelection(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, depth: u32) file_cache_mod.SummaryError!?bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        return switch (tree.nodeTag(node)) {
            .field_access => self.indexSelection(context, tree.nodeData(node).node_and_token[0], depth + 1),
            .deref, .address_of => self.indexSelection(context, tree.nodeData(node).node, depth + 1),
            .grouped_expression => self.indexSelection(context, tree.nodeData(node).node_and_token[0], depth + 1),
            .array_access => blk: {
                const base, const index = tree.nodeData(node).node_and_node;
                const parent = try self.indexSelection(context, base, depth + 1);
                break :blk (parent orelse true) and try self.depends(context, index, depth + 1);
            },
            else => null,
        };
    }

    fn counterKey(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, lhs: Ast.Node.Index, counter: CounterField, depth: u32) file_cache_mod.SummaryError!?[]const u8 {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .fn_decl) return null;
        if (tree.nodeTag(node) == .@"return") {
            const value = tree.nodeData(node).opt_node.unwrap() orelse return null;
            return self.returnedCounterKey(context, value, lhs, counter, depth + 1);
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            if (try self.counterKey(context, child, lhs, counter, depth + 1)) |key| return key;
        }
        return null;
    }

    fn returnedCounterKey(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, lhs: Ast.Node.Index, counter: CounterField, depth: u32) file_cache_mod.SummaryError!?[]const u8 {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        switch (tree.nodeTag(node)) {
            .deref => return self.returnedCounterKey(context, tree.nodeData(node).node, lhs, counter, depth + 1),
            .grouped_expression => return self.returnedCounterKey(context, tree.nodeData(node).node_and_token[0], lhs, counter, depth + 1),
            else => {},
        }
        if (tree.nodeTag(node) == .identifier) {
            const token = tree.nodeMainToken(node);
            const binding = context.bindings.findAt(tree.tokenSlice(token), token) orelse return null;
            if (binding.origin == .param) {
                if (binding.name_token != context.selected) return null;
                var selected = context;
                selected.selected = binding.name_token;
                // A returned handle's key need not have the counter's name.
                // Select only a source-declared payload field whose exact
                // value reaches the incremented counter instance.
                const container = (try context.resolution.containerOfNode(node)) orelse return null;
                const declaring_tree = &container.scope_handle.handle.document.tree;
                var buffer: [2]Ast.Node.Index = undefined;
                const declaration = declaring_tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return null;
                for (declaration.ast.members) |member| {
                    const field = declaring_tree.fullContainerField(member) orelse continue;
                    if (counter.tree == declaring_tree and counter.declaration == member) {
                        const field_frame = context.resolution.resolver.frameForContainer(container);
                        const type_node = field.ast.type_expr.unwrap() orelse continue;
                        const field_type = (try field_frame.typeOfNode(type_node)) orelse continue;
                        if (context.resolution.resolver.pointerSize(field_type) == null) continue;
                    }
                    try self.charge(declaring_tree, member, depth + 1);
                    const key = declaring_tree.tokenSlice(declaring_tree.nodeMainToken(member));
                    selected.selected_path = key;
                    if (try self.counterSelectionDepends(selected, lhs, depth + 1)) return key;
                }
                return null;
            }
            const initializer = context.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return null;
            if (initializer == node) return null;
            return self.returnedCounterKey(context, initializer, lhs, counter, depth + 1);
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = tree.fullStructInit(&buffer, node) orelse return null;
        for (literal.ast.fields) |value| {
            if (tree.nodeTag(value) != .field_access) continue;
            const base, const field = tree.nodeData(value).node_and_token;
            if (tree.nodeTag(base) != .identifier) continue;
            const token = tree.nodeMainToken(base);
            const binding = context.bindings.findAt(tree.tokenSlice(token), token) orelse continue;
            if (binding.origin != .param or binding.name_token != context.selected) continue;
            var selected = context;
            selected.selected = binding.name_token;
            selected.selected_path = tree.tokenSlice(field);
            if (!try self.counterSelectionDepends(selected, lhs, depth + 1)) continue;
            if (try self.counterField(context, value, depth + 1)) |returned_field| {
                if (returned_field.tree == counter.tree and returned_field.declaration == counter.declaration) {
                    const ty = (try context.resolution.typeOfNode(value)) orelse continue;
                    if (context.resolution.resolver.pointerSize(ty) == null) continue;
                }
            }
            const first = tree.firstToken(value);
            if (first < 2 or tree.tokenTag(first - 1) != .equal) continue;
            return tree.tokenSlice(first - 2);
        }
        return null;
    }

    fn savedPayload(self: *Query, context: ReferenceFrame, node: Ast.Node.Index, clear: Ast.TokenIndex, payload_path: *?[]const u8, depth: u32) file_cache_mod.SummaryError!bool {
        const tree = context.cache.tree;
        try self.charge(tree, node, depth);
        if (tree.nodeTag(node) == .identifier) {
            const token = tree.nodeMainToken(node);
            const binding = context.bindings.findAt(tree.tokenSlice(token), token) orelse return false;
            if (binding.origin == .param or binding.rhs_last >= clear) return false;
            const value = context.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
            if (value == node) return false;
            return self.savedPayload(context, value, clear, payload_path, depth + 1);
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullStructInit(&buffer, node)) |literal| {
            for (literal.ast.fields) |value| {
                var field_path: ?[]const u8 = null;
                if (!try self.savedPayload(context, value, clear, &field_path, depth + 1)) continue;
                // Each returned field is a distinct value. Do not equate the
                // incoming and outgoing spellings when an erasure renames it.
                if (field_path != null) continue;
                const first = tree.firstToken(value);
                if (first < 2 or tree.tokenTag(first - 1) != .equal) continue;
                payload_path.* = tree.tokenSlice(first - 2);
                return true;
            }
            return false;
        }
        if (tree.lastToken(node) >= clear or !try self.depends(context, node, depth + 1)) return false;
        payload_path.* = if (try self.wholeForward(context, node, depth + 1)) context.selected_path else null;
        return true;
    }
};

test "reference ownership query keeps exact formal counter identity and rejects partial returns" {
    const source: [:0]const u8 =
        \\const Snapshot = struct {
        \\    counter: *usize,
        \\    fn take(self: Snapshot) Snapshot { self.counter.* += 1; return self; }
        \\    fn drop(self: Snapshot) void { self.counter.* -= 1; }
        \\    fn borrow(self: Snapshot) Snapshot { return self; }
        \\    fn partial(self: Snapshot, flag: bool) Snapshot {
        \\        if (flag) self.counter.* += 1;
        \\        return self;
        \\    }
        \\    fn alternate(self: Snapshot, other: Snapshot, flag: bool) Snapshot {
        \\        if (flag) { self.counter.* += 1; return self; }
        \\        return other;
        \\    }
        \\};
        \\const Pointer = struct {
        \\    count: usize, metrics: usize,
        \\    fn acquire(self: *Pointer) *Pointer { self.count += 1; return self; }
        \\    fn retain(self: *Pointer) void { self.count += 1; }
        \\    fn release(self: *Pointer) void { self.count -= 1; }
        \\    fn netZero(self: *Pointer) *Pointer { self.count += 1; _ = self.release(); return self; }
        \\    fn bypass(self: *Pointer, input: ?u32) *Pointer {
        \\        const value = input orelse { self.count += 1; return self; };
        \\        _ = value;
        \\        return self;
        \\    }
        \\    fn metric(self: *Pointer) *Pointer { self.metrics += 1; return self; }
        \\};
        \\const Key = struct { key: usize };
        \\const Pool = struct {
        \\    slots: [4]struct { strong: usize },
        \\    fn changed(self: *Pool, handle: Key) Key {
        \\        var key = handle.key;
        \\        key += 1;
        \\        self.slots[key].strong += 1;
        \\        return handle;
        \\    }
        \\};
        \\pub fn pointerWork(value: *Pointer, input: ?u32, pool: *Pool, key: Key) void {
        \\    _ = value.acquire();
        \\    value.retain();
        \\    _ = value.netZero();
        \\    _ = value.bypass(input);
        \\    _ = value.metric();
        \\    _ = pool.changed(key);
        \\}
        \\pub fn work(value: Snapshot, other: Snapshot, flag: bool) void {
        \\    _ = value.take();
        \\    _ = value.borrow();
        \\    _ = value.partial(flag);
        \\    _ = value.alternate(other, flag);
        \\}
        \\pub fn unknownCall(value: Snapshot, invoke: *const fn (Snapshot) Snapshot) void {
        \\    _ = invoke(value);
        \\}
    ;
    const allocator = std.testing.allocator;
    const engine = @import("type_engine");
    var context: engine.TypeContext = undefined;
    try context.init(allocator, std.testing.io);
    defer context.deinit();
    const cwd = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", allocator);
    defer allocator.free(cwd);
    const path = try std.fs.path.join(allocator, &.{ cwd, "zbc-reference-query-test.zig" });
    defer allocator.free(path);
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, allocator, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(allocator, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var query: Query = .{};
    var observed: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) == .identifier) {
            try std.testing.expect(try query.acquisitionAt(&cache, fresh_storage.calleeQueryToken(tree, call)) == .unknown);
            observed += 1;
            continue;
        }
        if (tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
        const method = tree.tokenSlice(tree.nodeData(call.ast.fn_expr).node_and_token[1]);
        const answer = try query.acquisitionAt(&cache, fresh_storage.calleeQueryToken(tree, call));
        if (std.mem.eql(u8, method, "acquire") or std.mem.eql(u8, method, "retain")) {
            try std.testing.expect(answer == .increment);
            try std.testing.expectEqual(@as(u32, 0), answer.increment.formal);
        } else if (std.mem.eql(u8, method, "release")) {
            try std.testing.expect(answer == .refused);
        } else if (std.mem.eql(u8, method, "take")) {
            try std.testing.expect(answer == .increment);
            try std.testing.expectEqual(@as(u32, 0), answer.increment.formal);
            try std.testing.expect(answer.increment.frame.cache.tree == tree);
            try std.testing.expect(answer.increment.counter.tree == tree);
            try std.testing.expectEqualStrings("counter", answer.increment.counter.payload_key.?);
            try std.testing.expectEqualStrings("self", tree.tokenSlice(answer.increment.frame.selected));
            try std.testing.expectEqualStrings("value", tree.getNodeSource(answer.increment.argument));
            _ = budget_mod.take();
            defer _ = budget_mod.take();
            var exhausted: Query = .{ .remaining = 0 };
            try std.testing.expectError(error.AnalysisBudgetExceeded, exhausted.acquisitionAt(&cache, fresh_storage.calleeQueryToken(tree, call)));
        } else {
            try std.testing.expect(answer == .refused);
        }
        observed += 1;
    }
    try std.testing.expectEqual(@as(usize, 12), observed);
}
