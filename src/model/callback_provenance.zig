const std = @import("std");
const Ast = std.zig.Ast;
const engine = @import("type_engine");
const FileCache = @import("../cache/file_cache.zig").FileCache;
const tokens = @import("../ast/tokens.zig");

const Binding = @import("local_bindings.zig").Binding;
const TypeResolver = engine.TypeResolver;

/// A certificate needs a closed function-value census and unchanged context
/// pairing through each source dispatcher. Mutable tables also need a closed
/// mutation census. Unsupported aliases and escapes keep the finding; source
/// and allocation failures propagate rather than masquerading as a verdict.
pub fn callbackParameterProven(
    cache: *FileCache,
    proto: Ast.full.FnProto,
    cast_token: Ast.TokenIndex,
) !bool {
    return prove(cache, proto, cast_token);
}

/// Borrowed source identity. Its resolver and admitted document must outlive
/// the census; the frame retains the original callable's generic bindings.
pub const SourcePoint = struct {
    frame: TypeResolver.ResolutionFrame,
    node: Ast.Node.Index,
};

pub const FormalActual = struct {
    formal: Ast.TokenIndex,
    actual: SourcePoint,
    /// Method syntax borrows the receiver cell without an address-of node.
    implicit_address: bool = false,
};

pub const TransportEdge = struct {
    caller: SourcePoint,
    callee: TypeResolver.FunctionReference,
    actuals: []const FormalActual,
};

pub const CallbackDispatch = struct {
    callback: TypeResolver.FunctionReference,
    registration: SourcePoint,
    context: SourcePoint,
    invocation: SourcePoint,
    arguments: []const SourcePoint,
    edges: []const TransportEdge,
};

/// Complete source pairing, not a non-null, alignment, lifetime, or storage
/// certificate. An incomplete census exposes no subset of its observations.
/// Allocations belong to `scratch`; source identities borrow the FileCache.
pub const DispatchCensus = union(enum) {
    incomplete,
    complete: []const CallbackDispatch,

    pub fn deinit(self: *DispatchCensus, scratch: std.mem.Allocator) void {
        if (self.* == .complete) {
            for (self.complete) |dispatch| {
                scratch.free(dispatch.arguments);
                for (dispatch.edges) |edge| scratch.free(edge.actuals);
                scratch.free(dispatch.edges);
            }
            scratch.free(self.complete);
        }
        self.* = .incomplete;
    }
};

pub fn closedDispatchCensus(
    cache: *FileCache,
    callback_decl: Ast.Node.Index,
    context_parameter: usize,
    scratch: std.mem.Allocator,
) !DispatchCensus {
    const resolver = cache.zls orelse return .incomplete;
    cache.beginNormalCleanup();
    defer cache.endNormalCleanup();
    const frame = resolver.resolutionFrame();
    const tree = cache.tree;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, callback_decl) orelse return .incomplete;
    if (proto.visib_token != null) return .incomplete;
    if (proto.extern_export_inline_token) |modifier| {
        if (tree.tokenTag(modifier) == .keyword_export or
            tree.tokenTag(modifier) == .keyword_extern) return .incomplete;
    }
    // The entry point is a declaration node, not a function-value expression.
    // Authenticate each reached registration value in CensusBuilder.record.
    const callable = (try frame.resolveValueOfNode(callback_decl)) orelse return .incomplete;
    if (callable.data != .function) return .incomplete;
    var parameters = proto.iterate(tree);
    var count: usize = 0;
    while (parameters.next() != null) count += 1;
    if (context_parameter >= count) return .incomplete;
    const parents = try parentMap(cache);
    defer cache.gpa.free(parents);
    const owner_node = parents[@intFromEnum(callback_decl)];
    const owner = if (@intFromEnum(owner_node) != 0) blk: {
        const value = (try frame.resolveValueOfNode(owner_node)) orelse break :blk null;
        break :blk try resolver.normalizedType(value);
    } else null;
    var builder: CensusBuilder = .{ .allocator = scratch };
    defer builder.deinit();
    var proof: Proof = .{
        .cache = cache,
        .parents = parents,
        .callback = proto.ast.fn_token,
        .callback_handle = frame.handle,
        // Neutral mode does not compare the context's pointed-to type.
        .target_child = owner orelse callable,
        .parameter_index = context_parameter,
        .callback_owner = owner,
        .census = &builder,
    };
    defer proof.deinit();
    if (!try closedUses(&proof)) return .incomplete;
    const result = try builder.dispatches.toOwnedSlice(scratch);
    return .{ .complete = result };
}

const CensusBuilder = struct {
    allocator: std.mem.Allocator,
    dispatches: std.ArrayList(CallbackDispatch) = .empty,
    edges: std.ArrayList(TransportEdge) = .empty,

    fn deinit(self: *CensusBuilder) void {
        for (self.dispatches.items) |dispatch| {
            self.allocator.free(dispatch.arguments);
            for (dispatch.edges) |edge| self.allocator.free(edge.actuals);
            self.allocator.free(dispatch.edges);
        }
        self.dispatches.deinit(self.allocator);
        for (self.edges.items) |edge| self.allocator.free(edge.actuals);
        self.edges.deinit(self.allocator);
    }

    fn push(self: *CensusBuilder, proof: *Proof, call_node: Ast.Node.Index, canonical: FileCache.ActualCallSummary) !bool {
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(canonical.callee.tree, &buffer, canonical.callee.declaration) orelse return false;
        var actuals: std.ArrayList(FormalActual) = .empty;
        defer actuals.deinit(self.allocator);
        var parameters = proto.iterate(canonical.callee.tree);
        var index: u32 = 0;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        while (parameters.next()) |parameter| : (index += 1) {
            const argument = (try canonical.callArgumentFor(proof.cache, &argument_buffer, index)) orelse return false;
            try actuals.append(self.allocator, .{
                .formal = parameter.name_token orelse return false,
                .actual = .{ .frame = proof.resolutionFrame(), .node = argument },
                .implicit_address = index == 0 and canonical.argument_offset == 1,
            });
        }
        const owned = try actuals.toOwnedSlice(self.allocator);
        errdefer self.allocator.free(owned);
        try self.edges.append(self.allocator, .{
            .caller = .{ .frame = proof.resolutionFrame(), .node = call_node },
            .callee = canonical.callee.reference,
            .actuals = owned,
        });
        return true;
    }

    fn pop(self: *CensusBuilder) void {
        self.allocator.free(self.edges.pop().?.actuals);
    }

    fn record(self: *CensusBuilder, proof: *Proof, invocation: Ast.Node.Index, call: Ast.full.Call, pair: Pair, context: Ast.Node.Index) !bool {
        const callback_node = pair.origin.aggregateField(pair.initializer, pair.callback_field) orelse pair.initializer;
        const callback = switch (try pair.origin.resolutionFrame().functionReference(callback_node)) {
            .function => |reference| reference,
            else => return false,
        };
        if (!pair.origin.callbackReference(callback)) return false;
        const arguments = try self.allocator.alloc(SourcePoint, call.ast.params.len);
        errdefer self.allocator.free(arguments);
        for (call.ast.params, arguments) |argument, *point| {
            point.* = .{ .frame = proof.resolutionFrame(), .node = argument };
        }
        const edges = try self.allocator.alloc(TransportEdge, self.edges.items.len);
        var initialized: usize = 0;
        errdefer {
            for (edges[0..initialized]) |edge| self.allocator.free(edge.actuals);
            self.allocator.free(edges);
        }
        for (self.edges.items, edges) |edge, *copy| {
            copy.* = edge;
            copy.actuals = try self.allocator.dupe(FormalActual, edge.actuals);
            initialized += 1;
        }
        try self.dispatches.append(self.allocator, .{
            .callback = callback,
            .registration = .{ .frame = pair.origin.resolutionFrame(), .node = pair.initializer },
            .context = .{ .frame = pair.origin.resolutionFrame(), .node = context },
            .invocation = .{ .frame = proof.resolutionFrame(), .node = invocation },
            .arguments = arguments,
            .edges = edges,
        });
        return true;
    }

    fn rewind(self: *CensusBuilder, count: usize) void {
        while (self.dispatches.items.len > count) {
            const dispatch = self.dispatches.pop().?;
            self.allocator.free(dispatch.arguments);
            for (dispatch.edges) |edge| self.allocator.free(edge.actuals);
            self.allocator.free(dispatch.edges);
        }
    }
};

fn prove(cache: *FileCache, proto: Ast.full.FnProto, cast_token: Ast.TokenIndex) !bool {
    const resolver = cache.zls orelse return false;
    const tree = cache.tree;
    const declaration = tokens.enclosingFnDecl(tree, proto.ast.fn_token) orelse return false;
    if (proto.visib_token != null) return false;
    if (proto.extern_export_inline_token) |modifier| {
        if (tree.tokenTag(modifier) == .keyword_export or
            tree.tokenTag(modifier) == .keyword_extern) return false;
    }
    var parameter_index: usize = 0;
    var parameter_name: ?Ast.TokenIndex = null;
    const frame = resolver.resolutionFrame();
    var cast: ?Ast.Node.Index = null;
    for (tree.nodes.items(.main_token), 0..) |token, raw| {
        if (token == cast_token) {
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (builtinArgument(tree, node, "@alignCast") != null) cast = node;
        }
    }
    const align_cast = cast orelse return false;
    const operand = builtinArgument(tree, align_cast, "@alignCast").?;
    if (tree.nodeTag(operand) != .unwrap_optional) return false;
    const unwrapped = tree.nodeData(operand).node_and_token[0];
    if (tree.nodeTag(unwrapped) != .identifier) return false;
    var parameters = proto.iterate(tree);
    while (parameters.next()) |parameter| : (parameter_index += 1) {
        const name = parameter.name_token orelse continue;
        if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(unwrapped)), tree.tokenSlice(name))) {
            parameter_name = name;
            break;
        }
    }
    if (parameter_name == null) return false;

    const parents = try parentMap(cache);
    defer cache.gpa.free(parents);
    const ptr_cast = parents[@intFromEnum(align_cast)];
    if (builtinArgument(tree, ptr_cast, "@ptrCast") != align_cast) return false;
    const local = tree.fullVarDecl(parents[@intFromEnum(ptr_cast)]) orelse return false;
    const type_node = local.ast.type_node.unwrap() orelse return false;
    const target = (try frame.typeOfNode(type_node)) orelse return false;
    const target_size = resolver.pointerSize(target) orelse return false;
    if (target_size != .one and target_size != .many) return false;
    const child = resolver.childType(target) orelse return false;
    const target_child = (try resolver.normalizedType(child)) orelse return false;
    // Exact typed address provenance is stronger than a guessed ABI alignment.
    // Explicitly over-aligned destinations need a separate alignment proof.
    const pointer_source = (try pointerTypeSource(frame, type_node, 0)) orelse return false;
    const pointer = pointer_source.frame.handle.document.tree.fullPtrType(pointer_source.node).?;
    if (pointer.ast.align_node.unwrap() != null or pointer.allowzero_token != null) return false;
    var callback_owner: ?TypeResolver.ActualType = null;
    const owner_node = parents[@intFromEnum(declaration)];
    if (@intFromEnum(owner_node) != 0) {
        switch (tree.nodeTag(owner_node)) {
            .container_decl,
            .container_decl_trailing,
            .container_decl_two,
            .container_decl_two_trailing,
            .container_decl_arg,
            .container_decl_arg_trailing,
            => {
                const value = (try frame.resolveValueOfNode(owner_node)) orelse return false;
                callback_owner = (try resolver.normalizedType(value)) orelse return false;
            },
            else => return false,
        }
    }
    var proof: Proof = .{
        .cache = cache,
        .parents = parents,
        .callback = proto.ast.fn_token,
        .callback_handle = frame.handle,
        .target_child = target_child,
        .parameter_index = parameter_index,
        .callback_owner = callback_owner,
    };
    defer proof.deinit();
    return try closedUses(&proof);
}

fn closedUses(proof: *Proof) !bool {
    const tree = proof.cache.tree;
    const frame = proof.resolutionFrame();
    if (!try proof.ownerUsesClosed()) return false;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .identifier, .field_access, .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (proof.census != null) try proof.cache.chargeNormalCleanupAt(tree, node);
        const reference = switch (try frame.functionReference(node)) {
            .function => |reference| reference,
            else => continue,
        };
        if (!proof.callbackReference(reference)) continue;
        const parent = proof.parent(node);
        var literal_buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullStructInit(&literal_buffer, parent) != null) {
            const field = proof.fieldName(node) orelse return false;
            if (!try proof.registrationProven(parent, field)) return false;
            proof.registrations += 1;
            continue;
        }
        var call_buffer: [2]Ast.Node.Index = undefined;
        if (TypeResolver.CallOperands.full(tree, &call_buffer, parent)) |call| {
            if (call.ast.fn_expr != node) {
                if (!try proof.directCallRegistration(node)) return false;
                proof.registrations += 1;
                continue;
            }
        }
        // Close alias uses explicitly as well as the resolved function census:
        // a failed reference resolution must not silently omit a registration.
        if (tree.fullVarDecl(parent)) |alias| {
            if (alias.ast.init_node.unwrap() != node or
                tree.tokenTag(alias.ast.mut_token) != .keyword_const) return false;
            const selected = (try proof.bindingAtDeclaration(alias.ast.mut_token + 1)) orelse
                return false;
            var uses: usize = 0;
            for (tree.nodes.items(.tag), 0..) |alias_tag, alias_raw| {
                if (alias_tag != .identifier) continue;
                const use: Ast.Node.Index = @enumFromInt(alias_raw);
                if (!try proof.isBinding(use, selected)) continue;
                var use_buffer: [2]Ast.Node.Index = undefined;
                if (tree.fullStructInit(&use_buffer, proof.parent(use)) == null) return false;
                const field = proof.fieldName(use) orelse return false;
                if (!try proof.registrationProven(proof.parent(use), field)) return false;
                proof.registrations += 1;
                uses += 1;
            }
            if (uses == 0) return false;
            continue;
        }
        if (tree.nodeTag(parent) != .assign) return false;
        const lhs, const rhs = tree.nodeData(parent).node_and_node;
        if (rhs != node or tree.nodeTag(lhs) != .field_access) return false;
        const root, const field = tree.nodeData(lhs).node_and_token;
        if (tree.nodeTag(root) != .identifier) return false;
        const binding = (try proof.binding(root)) orelse return false;
        if (!try proof.tableClosed(binding, tree.tokenSlice(field), parent)) return false;
        proof.registrations += 1;
    }
    return proof.registrations != 0 and proof.invocations != 0;
}

fn parentMap(cache: *FileCache) ![]Ast.Node.Index {
    const tree = cache.tree;
    const parents = try cache.gpa.alloc(Ast.Node.Index, tree.nodes.len);
    @memset(parents, @enumFromInt(0));
    for (1..tree.nodes.len) |raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        // The asm iterator yields operand expressions directly. Its input
        // and output descriptor nodes cannot be iterated independently.
        switch (tree.nodeTag(node)) {
            .asm_input, .asm_output => continue,
            else => {},
        }
        var children = engine.AstIterator.init(tree, node);
        while (children.next(tree)) |child| parents[@intFromEnum(child)] = node;
    }
    return parents;
}

fn builtinArgument(tree: *const Ast, node: Ast.Node.Index, name: []const u8) ?Ast.Node.Index {
    if (@intFromEnum(node) == 0) return null;
    switch (tree.nodeTag(node)) {
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
        else => return null,
    }
    if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), name)) return null;
    var children = engine.AstIterator.init(tree, node);
    const argument = children.next(tree) orelse return null;
    if (children.next(tree) != null) return null;
    return argument;
}

/// Borrow the exact pointer declaration through immutable type aliases and
/// optional wrappers. This is syntax identity, not a null/alignment proof.
/// The returned frame/document borrow the original resolver and FileCache.
/// Unresolved aliases return null; resolution and allocation errors propagate.
pub fn pointerTypeSource(
    frame: TypeResolver.ResolutionFrame,
    node: Ast.Node.Index,
    depth: u32,
) anyerror!?SourcePoint {
    if (depth == 32) return null;
    const tree = &frame.handle.document.tree;
    if (tree.fullPtrType(node) != null) return .{ .frame = frame, .node = node };
    if (tree.nodeTag(node) == .optional_type)
        return try pointerTypeSource(frame, tree.nodeData(node).node, depth + 1);
    const value = (try frame.resolveValueOfNode(node)) orelse return null;
    if (!value.is_type_val) return null;
    const declaration = switch (tree.nodeTag(node)) {
        .identifier => try frame.resolver.analyser.lookupSymbolGlobal(
            frame.handle,
            tree.tokenSlice(tree.nodeMainToken(node)),
            tree.tokenStart(tree.nodeMainToken(node)),
        ),
        .field_access => blk: {
            const owner_node, const field = tree.nodeData(node).node_and_token;
            const owner = (try frame.resolveValueOfNode(owner_node)) orelse return null;
            break :blk try owner.lookupSymbol(&frame.resolver.analyser, tree.tokenSlice(field));
        },
        else => return null,
    } orelse return null;
    if (!declaration.isConst()) return null;
    const alias_node = switch (declaration.decl) {
        .ast_node => |alias| alias,
        else => return null,
    };
    const alias_tree = &declaration.handle.document.tree;
    const alias = alias_tree.fullVarDecl(alias_node) orelse return null;
    const initializer = alias.ast.init_node.unwrap() orelse return null;
    const alias_frame: TypeResolver.ResolutionFrame = .{
        .resolver = frame.resolver,
        .handle = declaration.handle,
        .container_type = declaration.container_type orelse
            if (declaration.handle.eql(frame.handle)) frame.container_type else null,
        .actual_type = if (declaration.handle.eql(frame.handle)) frame.actual_type else null,
    };
    return try pointerTypeSource(alias_frame, initializer, depth + 1);
}

const Pair = struct {
    origin: *Proof,
    initializer: Ast.Node.Index,
    table_field: ?[]const u8,
    callback_field: []const u8,
};

/// A direct dispatcher must preserve one exact callback/context pair.
const DirectDispatch = struct {
    context_index: usize,
    invocations: usize,
};

const Origin = struct {
    proof: *Proof,
    node: Ast.Node.Index,
};

const RuntimeActual = struct {
    parameter: Ast.TokenIndex,
    origin: Origin,
    /// A proved indexed cell's current value; never its physical address.
    value_origin: ?Origin = null,
    borrowed: bool = false,
};

/// A field/index path carries the pair without conflating its enclosing
/// aggregate with another callback or another context field.
const Carrier = struct {
    ty: TypeResolver.ActualType,
    pointer: bool = false,
    nullable: bool = false,
    path: []const Segment = &.{},
    store: ?Origin = null,
    birth: ?Origin = null,
    initializer: ?Origin = null,
    /// The local cell created by a source-proved by-value header snapshot.
    copied_cell: ?Origin = null,

    const Segment = struct {
        selector: union(enum) { field: []const u8, index: Origin },
        child: TypeResolver.ActualType,
        pointer: bool,
        nullable: bool,
    };

    fn prepend(self: Carrier, segment: Segment, outer: TypeResolver.ActualType, buffer: *[16]Segment) ?Carrier {
        if (self.path.len == buffer.len) return null;
        std.mem.copyBackwards(Segment, buffer[1 .. self.path.len + 1], self.path);
        buffer[0] = segment;
        var result = self;
        result.path = buffer[0 .. self.path.len + 1];
        result.ty = outer;
        result.pointer = false;
        result.nullable = false;
        return result;
    }

    fn project(self: Carrier) Carrier {
        std.debug.assert(self.path.len != 0);
        var result = self;
        result.ty = self.path[0].child;
        result.pointer = self.path[0].pointer;
        result.nullable = self.path[0].nullable;
        result.path = self.path[1..];
        return result;
    }
};

const Proof = struct {
    cache: *FileCache,
    parents: []const Ast.Node.Index,
    callback: Ast.TokenIndex,
    /// Keep the target declaration tied to its source module.
    callback_handle: engine.DocumentStore.Handle,
    target_child: TypeResolver.ActualType,
    parameter_index: usize,
    callback_owner: ?TypeResolver.ActualType,
    frame: ?TypeResolver.ResolutionFrame = null,
    runtime_actuals: []const RuntimeActual = &.{},
    active_cell: ?Ast.TokenIndex = null,
    registrations: usize = 0,
    invocations: usize = 0,
    test_bindings: std.AutoHashMapUnmanaged(Ast.Node.Index, *@import("local_bindings.zig").LocalBindings) = .empty,
    census: ?*CensusBuilder = null,
    factory_call: ?Ast.Node.Index = null,

    fn leafEnumerable(self: *Proof, node: Ast.Node.Index) bool {
        var ancestor = node;
        for (0..self.cache.tree.nodes.len) |_| {
            if (@intFromEnum(ancestor) == 0) return true;
            if (self.cache.tree.fullFor(ancestor) != null or
                self.cache.tree.fullWhile(ancestor) != null) return false;
            ancestor = self.parent(ancestor);
        }
        return false;
    }

    fn recordDirectInvocations(self: *Proof, selected: *const Binding, declaration: Ast.Node.Index, origin: *Proof, callback_node: Ast.Node.Index, context: Ast.Node.Index) !bool {
        const tree = self.cache.tree;
        const pair: Pair = .{ .origin = origin, .initializer = callback_node, .table_field = null, .callback_field = "" };
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (tree.firstToken(node) < tree.firstToken(declaration) or tree.lastToken(node) > tree.lastToken(declaration)) continue;
            try self.cache.chargeNormalCleanupAt(tree, node);
            if (!try self.isBinding(node, selected)) continue;
            const invocation = self.parent(node);
            var buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, invocation) orelse return false;
            if (call.ast.fn_expr != node or !self.leafEnumerable(invocation)) return false;
            if (!try self.census.?.record(self, invocation, call, pair, context)) return false;
        }
        return true;
    }

    fn enterEdge(self: *Proof, call_node: Ast.Node.Index, canonical: FileCache.ActualCallSummary) !bool {
        if (self.census) |census| return try census.push(self, call_node, canonical);
        return true;
    }

    fn leaveEdge(self: *Proof) void {
        if (self.census) |census| census.pop();
    }

    fn deinit(self: *Proof) void {
        var values = self.test_bindings.valueIterator();
        while (values.next()) |bindings| {
            bindings.*.deinit();
            self.cache.gpa.destroy(bindings.*);
        }
        self.test_bindings.deinit(self.cache.gpa);
    }

    fn resolutionFrame(self: *const Proof) TypeResolver.ResolutionFrame {
        const frame = self.frame orelse self.cache.zls.?.resolutionFrame();
        std.debug.assert(&frame.handle.document.tree == self.cache.tree);
        return frame;
    }

    fn inCache(self: *const Proof, cache: *FileCache, parents: []const Ast.Node.Index) Proof {
        return .{
            .cache = cache,
            .parents = parents,
            .callback = self.callback,
            .callback_handle = self.callback_handle,
            .target_child = self.target_child,
            .parameter_index = self.parameter_index,
            .callback_owner = self.callback_owner,
            .census = self.census,
        };
    }
    fn callbackReference(self: *const Proof, reference: TypeResolver.FunctionReference) bool {
        return reference.handle.eql(self.callback_handle) and
            reference.tree == &self.callback_handle.document.tree and
            reference.fn_token == self.callback;
    }

    fn parent(self: *const Proof, node: Ast.Node.Index) Ast.Node.Index {
        return self.parents[@intFromEnum(node)];
    }

    fn binding(self: *Proof, node: Ast.Node.Index) !?*const Binding {
        const tree = self.cache.tree;
        const token = tree.nodeMainToken(node);
        const bindings = (try self.bindingsAt(token)) orelse return null;
        return bindings.findAt(tree.tokenSlice(token), token);
    }

    fn bindingsAt(self: *Proof, token: Ast.TokenIndex) !?*const @import("local_bindings.zig").LocalBindings {
        const tree = self.cache.tree;
        if (tokens.enclosingFnDecl(tree, token)) |declaration| {
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &buffer, declaration).?;
            return try self.cache.localBindings(proto, tree.nodeData(declaration).node_and_node[1]);
        }
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .test_decl) continue;
            const declaration: Ast.Node.Index = @enumFromInt(raw);
            const body = tree.nodeData(declaration).opt_token_and_node[1];
            if (token < tree.firstToken(body) or token > tree.lastToken(body)) continue;
            if (self.test_bindings.get(body)) |bindings| return bindings;
            const bindings = try self.cache.gpa.create(@import("local_bindings.zig").LocalBindings);
            errdefer self.cache.gpa.destroy(bindings);
            bindings.* = try @import("local_bindings.zig").build(self.cache.gpa, tree, null, body);
            errdefer bindings.deinit();
            try self.test_bindings.put(self.cache.gpa, body, bindings);
            return bindings;
        }
        return null;
    }

    fn isBinding(self: *Proof, node: Ast.Node.Index, selected: *const Binding) !bool {
        if (self.cache.tree.nodeTag(node) != .identifier) return false;
        if (!std.mem.eql(u8, self.cache.tree.tokenSlice(self.cache.tree.nodeMainToken(node)), selected.name)) return false;
        const actual = (try self.binding(node)) orelse return false;
        return actual.name_token == selected.name_token;
    }

    fn fieldName(self: *const Proof, value: Ast.Node.Index) ?[]const u8 {
        const tree = self.cache.tree;
        const first = tree.firstToken(value);
        if (first < 3 or tree.tokenTag(first - 1) != .equal or
            tree.tokenTag(first - 3) != .period) return null;
        return tree.tokenSlice(first - 2);
    }

    fn sameBlock(self: *const Proof, node: Ast.Node.Index, selected: *const Binding) bool {
        const tree = self.cache.tree;
        var current = node;
        for (0..tree.nodes.len) |_| {
            if (@intFromEnum(current) == 0) return false;
            switch (tree.nodeTag(current)) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => return tree.firstToken(current) == selected.scope_open,
                else => current = self.parent(current),
            }
        }
        return false;
    }

    fn directRegistration(
        self: *Proof,
        initializer: Ast.Node.Index,
        callback_field: []const u8,
    ) !bool {
        const tree = self.cache.tree;
        const parent_node = self.parent(initializer);
        const pair: Pair = .{
            .origin = self,
            .initializer = initializer,
            .table_field = null,
            .callback_field = callback_field,
        };
        if (tree.fullVarDecl(parent_node)) |local| {
            if (local.ast.init_node.unwrap() != initializer or
                tree.tokenTag(local.ast.mut_token) != .keyword_const) return false;
            const type_node = local.ast.type_node.unwrap() orelse initializer;
            const ty = (try self.cache.zls.?.resolutionFrame().typeOfNode(type_node)) orelse
                return false;
            if (self.cache.zls.?.typeTag(ty) != .@"struct") return false;
            const selected = (try self.bindingAtDeclaration(local.ast.mut_token + 1)) orelse
                return false;
            return try self.contextClosed(selected, pair, 0);
        }
        if (tree.nodeTag(parent_node) == .@"return") {
            return try self.returnedRegistration(initializer, pair, 0);
        }
        return try self.forwardArgument(initializer, parent_node, pair, 0);
    }
    /// Prove a direct callback argument through its source dispatcher body.
    fn directCallRegistration(self: *Proof, callback_node: Ast.Node.Index) anyerror!bool {
        const tree = self.cache.tree;
        const reference = switch (try self.resolutionFrame().functionReference(callback_node)) {
            .function => |reference| reference,
            else => return false,
        };
        if (!self.callbackReference(reference)) return false;

        const call_node = self.parent(callback_node);
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &call_buffer, call_node) orelse
            return false;
        if (call.ast.fn_expr == callback_node) return false;
        const canonical = (try self.cache.actualCallSummaryAt(
            call.queryToken(tree, call_node),
            self.frame,
        )) orelse return false;
        const declaring = (try canonical.declaringCache(self.cache)) orelse return false;
        const callee_tree = canonical.callee.tree;
        std.debug.assert(declaring.tree == callee_tree);
        const declaration = canonical.callee.declaration;
        if (tokens.bodyOf(callee_tree, declaration) == null) return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(callee_tree, &proto_buffer, declaration) orelse
            return false;
        if (proto.extern_export_inline_token) |modifier| {
            if (callee_tree.tokenTag(modifier) == .keyword_export or
                callee_tree.tokenTag(modifier) == .keyword_extern) return false;
        }

        const owned_parents = if (declaring.tree != tree) try parentMap(declaring) else null;
        defer if (owned_parents) |parents| declaring.gpa.free(parents);
        var dispatcher = self.inCache(declaring, owned_parents orelse self.parents);
        defer dispatcher.deinit();
        dispatcher.frame = declaring.zls.?.frameForFunction(canonical.callee.reference);

        var parameters = proto.iterate(callee_tree);
        var parameter_index: usize = 0;
        var matched = false;
        var invocations: usize = 0;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            const argument = (try canonical.callArgumentFor(
                self.cache,
                &argument_buffer,
                @intCast(parameter_index),
            )) orelse return false;
            if (argument != callback_node) continue;
            if (matched) return false;
            const name = parameter.name_token orelse return false;
            const selected = (try dispatcher.bindingAtDeclaration(name)) orelse return false;
            const paired = (try dispatcher.directDispatcherPair(
                selected,
                declaration,
            )) orelse return false;
            const context = (try canonical.callArgumentFor(
                self.cache,
                &argument_buffer,
                @intCast(paired.context_index),
            )) orelse return false;
            if (self.census) |census| {
                if (!try census.push(self, call_node, canonical)) return false;
                defer census.pop();
                if (!try dispatcher.recordDirectInvocations(selected, declaration, self, callback_node, context)) return false;
            } else if (!try self.directTypedAddress(context, 0)) return false;
            matched = true;
            invocations = paired.invocations;
        }
        if (!matched) return false;
        self.invocations += invocations;
        return true;
    }
    fn directTypedAddress(self: *Proof, expression: Ast.Node.Index, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        if (tree.nodeTag(expression) == .identifier) {
            const selected = (try self.binding(expression)) orelse return false;
            if (selected.origin == .param) return try self.typedAddress(expression);
            for (1..tree.nodes.len) |raw| {
                const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
                if (local.ast.mut_token + 1 != selected.name_token) continue;
                if (tree.tokenTag(local.ast.mut_token) != .keyword_const) return false;
                const initializer = local.ast.init_node.unwrap() orelse return false;
                switch (tree.nodeTag(initializer)) {
                    .@"try", .@"catch", .call, .call_comma, .call_one, .call_one_comma => {
                        // Fresh storage authenticates the allocation origin only.
                        // Ordinary pointer and exact target checks stay separate.
                        if (try self.bindingOwnsPhysicalStorage(selected))
                            return try self.typedAddress(expression);
                    },
                    else => {},
                }
                return try self.directTypedAddress(initializer, depth + 1);
            }
            return false;
        }
        switch (tree.nodeTag(expression)) {
            .address_of, .field_access => return try self.typedAddress(expression),
            else => {},
        }
        if (builtinArgument(tree, expression, "@ptrCast") orelse
            builtinArgument(tree, expression, "@constCast")) |argument|
        {
            return try self.directTypedAddress(argument, depth + 1);
        }
        return false;
    }

    fn directDispatcherPair(
        self: *Proof,
        callback: *const Binding,
        declaration: Ast.Node.Index,
    ) anyerror!?DirectDispatch {
        const tree = self.cache.tree;
        const body = tokens.bodyOf(tree, declaration) orelse return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return null;

        var selected_context: ?*const Binding = null;
        var invocations: usize = 0;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (tree.firstToken(node) < tree.firstToken(body) or
                tree.lastToken(node) > tree.lastToken(body)) continue;
            if (!try self.isBinding(node, callback)) continue;
            const use_declaration = tokens.enclosingFnDecl(tree, tree.firstToken(node)) orelse
                return null;
            if (use_declaration != declaration) return null;
            const call_node = self.parent(node);
            var call_buffer: [2]Ast.Node.Index = undefined;
            const call = TypeResolver.CallOperands.full(tree, &call_buffer, call_node) orelse
                return null;
            if (call.ast.fn_expr != node or call.ast.params.len <= self.parameter_index)
                return null;
            const context_node = call.ast.params[self.parameter_index];
            if (tree.nodeTag(context_node) != .identifier) return null;
            const context = (try self.binding(context_node)) orelse return null;
            if (context.origin != .param or context.name_token == callback.name_token)
                return null;
            if (selected_context) |selected| {
                if (selected.name_token != context.name_token) return null;
            } else {
                selected_context = context;
            }
            invocations += 1;
        }
        const context = selected_context orelse return null;
        if (invocations == 0) return null;

        var context_uses: usize = 0;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (!try self.isBinding(node, context)) continue;
            const use_declaration = tokens.enclosingFnDecl(tree, tree.firstToken(node)) orelse
                return null;
            if (use_declaration != declaration) return null;
            const call_node = self.parent(node);
            var call_buffer: [2]Ast.Node.Index = undefined;
            const call = TypeResolver.CallOperands.full(tree, &call_buffer, call_node) orelse
                return null;
            if (call.ast.fn_expr == node) return null;
            if (!try self.isBinding(call.ast.fn_expr, callback)) return null;
            if (call.ast.params.len <= self.parameter_index or
                call.ast.params[self.parameter_index] != node) return null;
            context_uses += 1;
        }
        if (context_uses != invocations) return null;

        var parameters = proto.iterate(tree);
        var context_index: ?usize = null;
        var index: usize = 0;
        while (parameters.next()) |parameter| : (index += 1) {
            if (parameter.name_token != context.name_token) continue;
            if (context_index != null) return null;
            const resolver = self.cache.zls.?;
            const ty = (try self.resolutionFrame().typeOfNode(
                parameter.type_expr orelse return null,
            )) orelse return null;
            if (resolver.pointerSize(ty) != .one) {
                if (resolver.typeTag(ty) != .optional) return null;
                const payload = resolver.childType(ty) orelse return null;
                if (resolver.pointerSize(payload) != .one) return null;
            }
            context_index = index;
        }
        return .{
            .context_index = context_index orelse return null,
            .invocations = invocations,
        };
    }

    fn forwardArgument(
        self: *Proof,
        argument_node: Ast.Node.Index,
        call_node: Ast.Node.Index,
        pair: Pair,
        depth: u32,
    ) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &call_buffer, call_node) orelse
            return false;
        if (call.ast.fn_expr == argument_node) return false;
        const canonical = (try self.cache.actualCallSummaryAt(
            call.queryToken(tree, call_node),
            self.frame,
        )) orelse return false;
        const declaring = (try canonical.declaringCache(self.cache)) orelse return false;
        const callee_tree = canonical.callee.tree;
        std.debug.assert(declaring.tree == callee_tree);
        const declaration = canonical.callee.declaration;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(callee_tree, &proto_buffer, declaration) orelse return false;
        if (tokens.bodyOf(callee_tree, declaration) == null) return false;
        if (proto.extern_export_inline_token) |modifier| {
            if (callee_tree.tokenTag(modifier) == .keyword_export or
                callee_tree.tokenTag(modifier) == .keyword_extern) return false;
        }
        if (!try self.enterEdge(call_node, canonical)) return false;
        defer self.leaveEdge();
        const owned_parents = if (declaring.tree != tree) try parentMap(declaring) else null;
        defer if (owned_parents) |parents| declaring.gpa.free(parents);
        var next_proof = self.inCache(declaring, owned_parents orelse self.parents);
        defer next_proof.deinit();
        next_proof.frame = declaring.zls.?.frameForFunction(canonical.callee.reference);
        var parameters = proto.iterate(callee_tree);
        var index: u32 = 0;
        var mapped = false;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        while (parameters.next()) |parameter| : (index += 1) {
            const argument = (try canonical.callArgumentFor(
                self.cache, &argument_buffer, index,
            )) orelse return false;
            if (argument != argument_node) continue;
            const name = parameter.name_token orelse return false;
            const next = (try next_proof.bindingAtDeclaration(name)) orelse return false;
            const type_node = parameter.type_expr orelse return false;
            const ty = (try next_proof.resolutionFrame().typeOfNode(type_node)) orelse return false;
            // A readonly receiver can transport the same pair. Its complete
            // source-use census below still rejects writes and alias escapes.
            if (declaring.zls.?.typeTag(ty) != .@"struct") {
                if (declaring.zls.?.pointerSize(ty) != .one) return false;
                const pointer = callee_tree.fullPtrType(type_node) orelse return false;
                if (pointer.const_token == null or pointer.allowzero_token != null) return false;
                const child = declaring.zls.?.childType(ty) orelse return false;
                const actual = (try declaring.zls.?.normalizedType(child)) orelse return false;
                if (declaring.zls.?.typeTag(actual) != .@"struct") return false;
            }
            if (!try next_proof.contextClosed(next, pair, depth + 1)) return false;
            mapped = true;
        }
        self.invocations += next_proof.invocations;
        return mapped;
    }

    fn returnedRegistration(
        self: *Proof,
        initializer: Ast.Node.Index,
        pair: Pair,
        depth: u32,
    ) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        const declaration = tokens.enclosingFnDecl(tree, tree.firstToken(initializer)) orelse
            return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
        // A public factory can export this private callback to unseen callers.
        if (proto.visib_token != null) return false;
        if (proto.extern_export_inline_token) |modifier| {
            if (tree.tokenTag(modifier) == .keyword_export or
                tree.tokenTag(modifier) == .keyword_extern) return false;
        }
        const result_type = proto.ast.return_type.unwrap() orelse return false;
        const ty = (try self.resolutionFrame().typeOfNode(result_type)) orelse return false;
        if (self.cache.zls.?.typeTag(ty) != .@"struct") return false;
        var calls: usize = 0;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            switch (tag) {
                .identifier, .field_access, .builtin_call, .builtin_call_comma,
                .builtin_call_two, .builtin_call_two_comma => {},
                else => continue,
            }
            const node: Ast.Node.Index = @enumFromInt(raw);
            const reference = switch (try self.resolutionFrame().functionReference(node)) {
                .function => |reference| reference,
                else => continue,
            };
            // Close the returned aggregate's factory, not the callback stored
            // inside it. Token identity alone is insufficient across modules.
            if (!reference.handle.eql(self.resolutionFrame().handle) or
                reference.tree != tree or reference.fn_token != proto.ast.fn_token)
                continue;
            const call_node = self.parent(node);
            var call_buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buffer, call_node) orelse return false;
            if (call.ast.fn_expr != node) return false;
            if (!try self.resultClosed(call_node, pair, depth + 1)) return false;
            calls += 1;
        }
        return calls != 0;
    }

    fn resultClosed(self: *Proof, result: Ast.Node.Index, pair: Pair, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        const parent_node = self.parent(result);
        if (tree.fullVarDecl(parent_node)) |local| {
            if (local.ast.init_node.unwrap() != result or
                tree.tokenTag(local.ast.mut_token) != .keyword_const) return false;
            const selected = (try self.bindingAtDeclaration(local.ast.mut_token + 1)) orelse
                return false;
            return try self.contextClosed(selected, pair, depth + 1);
        }
        if (tree.nodeTag(parent_node) == .@"return") {
            return try self.returnedRegistration(result, pair, depth + 1);
        }
        return try self.forwardArgument(result, parent_node, pair, depth + 1);
    }

    fn tableClosed(
        self: *Proof,
        selected: *const Binding,
        callback_field: []const u8,
        registration: Ast.Node.Index,
    ) !bool {
        const tree = self.cache.tree;
        if (selected.origin == .param or !self.sameBlock(registration, selected)) return false;
        const registration_lhs = tree.nodeData(registration).node_and_node[0];
        const table_root = tree.nodeData(registration_lhs).node_and_token[0];
        const resolver = self.cache.zls.?;
        const table_type = (try resolver.resolutionFrame().typeOfNode(table_root)) orelse return false;
        // Different union fields can overwrite the same function-pointer slot.
        if (resolver.typeTag(table_type) != .@"struct") return false;
        var pairs: usize = 0;
        var last_write = tree.lastToken(registration);
        // First close every table mutation. An address alias is never trusted,
        // even when its declared pointer type is const.
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (!try self.isBinding(node, selected)) continue;
            const parent_node = self.parent(node);
            if (tree.nodeTag(parent_node) == .field_access) {
                const field = tree.nodeData(parent_node).node_and_token[1];
                const store = self.parent(parent_node);
                if (tree.nodeTag(store) != .assign or
                    tree.nodeData(store).node_and_node[0] != parent_node or
                    !self.sameBlock(store, selected)) return false;
                if (std.mem.eql(u8, tree.tokenSlice(field), callback_field)) {
                    const rhs = tree.nodeData(store).node_and_node[1];
                    const reference = switch (try self.cache.zls.?.functionReference(rhs)) {
                        .function => |reference| reference,
                        else => return false,
                    };
                    if (!self.callbackReference(reference)) return false;
                    last_write = @max(last_write, tree.lastToken(store));
                }
                continue;
            }
            if (tree.nodeTag(parent_node) != .address_of) return false;
            const initializer = self.parent(parent_node);
            var buffer: [2]Ast.Node.Index = undefined;
            if (tree.fullStructInit(&buffer, initializer) == null) return false;
            if (self.fieldName(parent_node) == null) return false;
        }
        // Every address of the mutable table must remain paired in one local
        // immutable aggregate whose subsequent uses are closed source calls.
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (!try self.isBinding(node, selected)) continue;
            const address = self.parent(node);
            if (tree.nodeTag(address) != .address_of) continue;
            const initializer = self.parent(address);
            const local_node = self.parent(initializer);
            const local = tree.fullVarDecl(local_node) orelse return false;
            if (tree.tokenTag(local.ast.mut_token) != .keyword_const or
                tree.firstToken(initializer) <= last_write or
                !self.sameBlock(local_node, selected)) return false;
            // A dot initializer has no context-free type. Its declaration
            // supplies the expected aggregate type; a named literal carries
            // that type directly when the declaration omits an annotation.
            const context_type_node = local.ast.type_node.unwrap() orelse initializer;
            const context_type = (try resolver.resolutionFrame().typeOfNode(context_type_node)) orelse return false;
            if (resolver.typeTag(context_type) != .@"struct") return false;
            const pair: Pair = .{
                .origin = self,
                .initializer = initializer,
                .table_field = self.fieldName(address).?,
                .callback_field = callback_field,
            };
            const name_token = local.ast.mut_token + 1;
            const context_binding = try self.bindingAtDeclaration(name_token);
            if (!try self.contextClosed(context_binding orelse return false, pair, 0)) return false;
            pairs += 1;
        }
        return pairs != 0;
    }

    fn bindingAtDeclaration(self: *Proof, name_token: Ast.TokenIndex) !?*const Binding {
        const bindings = (try self.bindingsAt(name_token)) orelse return null;
        for (bindings.items) |*binding_item| {
            if (binding_item.name_token == name_token) return binding_item;
        }
        return null;
    }

    fn ownerUsesClosed(self: *Proof) !bool {
        return try self.ownerUsesClosedIn(null, 0);
    }

    fn ownerUsesClosedIn(self: *Proof, scope: ?Ast.Node.Index, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        const frame = self.resolutionFrame();
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            switch (tag) {
                .identifier, .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
                else => continue,
            }
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (scope) |declaration| {
                if (tree.firstToken(node) < tree.firstToken(declaration) or
                    tree.lastToken(node) > tree.lastToken(declaration)) continue;
            }
            const value = (try frame.resolveValueOfNode(node)) orelse continue;
            if (!value.is_type_val) continue;
            const ty = (try self.cache.zls.?.normalizedType(value)) orelse continue;
            // Scalar element types have no declarations that can hide the
            // callback. Their ordinary return/value uses need no owner census.
            if (self.target_child.data != .container or
                !TypeResolver.ActualType.eql(ty, self.target_child))
            {
                const owner = self.callback_owner orelse continue;
                if (!TypeResolver.ActualType.eql(ty, owner)) continue;
            }
            const parent_node = self.parent(node);
            if (tree.nodeTag(parent_node) == .field_access) {
                // Dynamic or reflected access to this owner must not hide an
                // additional callback value from the declaration census.
                switch (try frame.functionReference(parent_node)) {
                    .function => |reference| {
                        if (scope != null) {
                            if (!self.callbackReference(reference)) return false;
                            if (!try self.directCallRegistration(parent_node)) return false;
                            self.registrations += 1;
                        }
                    },
                    else => {
                        const member = (try frame.resolveValueOfNode(parent_node)) orelse
                            return false;
                        if (!member.is_type_val) return false;
                        const member_type = (try self.cache.zls.?.normalizedType(member)) orelse
                            return false;
                        if (!TypeResolver.ActualType.eql(member_type, self.target_child)) {
                            // A pointer typedef exposes no callback value. Its
                            // queried and source-declared pointees must both be
                            // the exact recovery target in their own frames.
                            // Address alignment is still proved at each use.
                            const resolver = self.cache.zls.?;
                            const size = resolver.pointerSize(member_type) orelse return false;
                            if (size != .one and size != .many) return false;
                            const member_child = (try resolver.normalizedType(
                                resolver.childType(member_type) orelse return false,
                            )) orelse return false;
                            if (!TypeResolver.ActualType.eql(member_child, self.target_child))
                                return false;
                            const source = (try pointerTypeSource(frame, parent_node, 0)) orelse
                                return false;
                            const pointer = source.frame.handle.document.tree.fullPtrType(source.node).?;
                            const source_child = (try source.frame.typeOfNode(
                                pointer.ast.child_type,
                            )) orelse return false;
                            if (!TypeResolver.ActualType.eql(source_child, member_child)) return false;
                        }
                    },
                }
                continue;
            }
            if (tree.fullPtrType(parent_node) != null) continue;
            if (tree.fullVarDecl(parent_node)) |local| {
                if (local.ast.type_node.unwrap() == node) continue;
                return false;
            }
            var buffer: [2]Ast.Node.Index = undefined;
            if (tree.fullStructInit(&buffer, parent_node)) |literal| {
                if (literal.ast.type_expr.unwrap() == node) continue;
            }
            if (builtinArgument(tree, parent_node, "@sizeOf") == node or
                builtinArgument(tree, parent_node, "@alignOf") == node) continue;
            // Discarding this resolved type value publishes no callback.
            // Runtime function-value uses remain in the registration census.
            if (tree.nodeTag(parent_node) == .assign) {
                const lhs, const rhs = tree.nodeData(parent_node).node_and_node;
                if (rhs == node and tree.nodeTag(lhs) == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(lhs)), "_"))
                    continue;
            }
            if (try self.ownerArgumentClosed(node, parent_node, depth + 1)) continue;
            return false;
        }
        return true;
    }

    fn ownerArgumentClosed(
        self: *Proof,
        argument_node: Ast.Node.Index,
        call_node: Ast.Node.Index,
        depth: u32,
    ) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, call_node) orelse return false;
        if (call.ast.fn_expr == argument_node) return false;
        const canonical = (try self.cache.actualCallSummaryAt(
            call.queryToken(tree, call_node), self.frame,
        )) orelse return false;
        const declaring = (try canonical.declaringCache(self.cache)) orelse return false;
        const callee_tree = canonical.callee.tree;
        std.debug.assert(declaring.tree == callee_tree);
        const declaration = canonical.callee.declaration;
        if (tokens.bodyOf(callee_tree, declaration) == null) return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(callee_tree, &proto_buffer, declaration) orelse return false;
        var parameters = proto.iterate(callee_tree);
        var index: u32 = 0;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        var matched = false;
        while (parameters.next()) |parameter| : (index += 1) {
            const argument = (try canonical.callArgumentFor(
                self.cache, &argument_buffer, index,
            )) orelse return false;
            if (argument != argument_node) continue;
            const ty = parameter.type_expr orelse return false;
            if (callee_tree.nodeTag(ty) != .identifier or
                !std.mem.eql(u8, callee_tree.tokenSlice(callee_tree.nodeMainToken(ty)), "type"))
                return false;
            matched = true;
        }
        if (!matched) return false;
        const owned_parents = if (callee_tree != tree) try parentMap(declaring) else null;
        defer if (owned_parents) |parents| declaring.gpa.free(parents);
        var next_proof = self.inCache(declaring, owned_parents orelse self.parents);
        defer next_proof.deinit();
        next_proof.frame = declaring.zls.?.frameForFunction(canonical.callee.reference);
        if (!try self.enterEdge(call_node, canonical)) return false;
        defer self.leaveEdge();
        const closed = try next_proof.ownerUsesClosedIn(declaration, depth + 1);
        if (!closed) return false;
        self.registrations += next_proof.registrations;
        self.invocations += next_proof.invocations;
        return true;
    }

    fn contextClosed(self: *Proof, selected: *const Binding, pair: Pair, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (!try self.isBinding(node, selected)) continue;
            const parent_node = self.parent(node);
            if (tree.nodeTag(parent_node) == .field_access) {
                const field = tree.nodeData(parent_node).node_and_token[1];
                if (self.isWritten(parent_node)) return false;
                if (pair.table_field == null) {
                    if (!std.mem.eql(u8, tree.tokenSlice(field), pair.callback_field)) {
                        const use = self.parent(parent_node);
                        var call_buffer: [1]Ast.Node.Index = undefined;
                        if (tree.fullCall(&call_buffer, use)) |call| {
                            if (call.ast.fn_expr == parent_node) {
                                if (!try self.forwardArgument(node, use, pair, depth)) return false;
                                continue;
                            }
                        }
                        if (!self.valueReadOnly(parent_node)) return false;
                        continue;
                    }
                    if (!try self.dispatchClosed(parent_node, selected, pair)) return false;
                    continue;
                }
                if (!std.mem.eql(u8, tree.tokenSlice(field), pair.table_field.?)) {
                    if (!self.valueReadOnly(parent_node)) return false;
                    continue;
                }
                const callback = self.parent(parent_node);
                if (tree.nodeTag(callback) != .field_access or
                    tree.nodeData(callback).node_and_token[0] != parent_node) return false;
                const callback_token = tree.nodeData(callback).node_and_token[1];
                if (!std.mem.eql(u8, tree.tokenSlice(callback_token), pair.callback_field)) {
                    // Other table entries do not carry the selected function.
                    // Their use must still be a read, not a pointer escape.
                    if (!self.valueReadOnly(callback)) return false;
                    continue;
                }
                if (!try self.dispatchClosed(callback, selected, pair)) return false;
                continue;
            }
            if (!try self.forwardArgument(node, parent_node, pair, depth)) return false;
        }
        return true;
    }

    fn isWritten(self: *const Proof, node: Ast.Node.Index) bool {
        const tree = self.cache.tree;
        const parent_node = self.parent(node);
        switch (tree.nodeTag(parent_node)) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod, .assign_shl, .assign_shr, .assign_bit_and, .assign_bit_or, .assign_bit_xor => return tree.nodeData(parent_node).node_and_node[0] == node,
            .address_of => return true,
            else => return false,
        }
    }

    fn valueReadOnly(self: *const Proof, node: Ast.Node.Index) bool {
        // Following parents catches taking the address of a nested field, not
        // just an assignment to the immediate read.
        var current = node;
        for (0..self.cache.tree.nodes.len) |_| {
            if (self.isWritten(current)) return false;
            const parent_node = self.parent(current);
            switch (self.cache.tree.nodeTag(parent_node)) {
                .field_access, .array_access, .deref => current = parent_node,
                else => return true,
            }
        }
        return false;
    }

    fn dispatchClosed(self: *Proof, callback: Ast.Node.Index, context: *const Binding, pair: Pair) !bool {
        const tree = self.cache.tree;
        var source = callback;
        const parent_node = self.parent(source);
        if (tree.nodeTag(parent_node) == .@"orelse" and tree.nodeData(parent_node).node_and_node[0] == source) {
            const rejected = tree.nodeData(parent_node).node_and_node[1];
            if (!self.terminates(rejected)) return false;
            source = parent_node;
        }
        var direct_buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&direct_buffer, self.parent(source))) |call| {
            if (call.ast.fn_expr != source) return false;
            return try self.invocationClosed(self.parent(source), call, context, pair);
        }
        const alias_token = if (tree.fullIf(self.parent(source))) |branch| blk: {
            if (branch.ast.cond_expr != source) return false;
            const payload = branch.payload_token orelse return false;
            // A pointer capture exposes the callback slot to mutation.
            if (tree.tokenTag(payload) != .identifier) return false;
            break :blk payload;
        } else blk: {
            const local = tree.fullVarDecl(self.parent(source)) orelse return false;
            if (tree.tokenTag(local.ast.mut_token) != .keyword_const) return false;
            break :blk local.ast.mut_token + 1;
        };
        const alias = (try self.bindingAtDeclaration(alias_token)) orelse return false;
        var uses: usize = 0;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (!try self.isBinding(node, alias)) continue;
            const invocation = self.parent(node);
            var call_buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buffer, invocation) orelse return false;
            if (call.ast.fn_expr != node) return false;
            if (!try self.invocationClosed(invocation, call, context, pair)) return false;
            uses += 1;
        }
        return uses != 0;
    }

    fn invocationClosed(
        self: *Proof,
        invocation: Ast.Node.Index,
        call: Ast.full.Call,
        context: *const Binding,
        pair: Pair,
    ) !bool {
        const tree = self.cache.tree;
        if (call.ast.params.len <= self.parameter_index) return false;
        const handle = call.ast.params[self.parameter_index];
        if (tree.nodeTag(handle) != .field_access) return false;
        const root, const field_token = tree.nodeData(handle).node_and_token;
        if (!try self.isBinding(root, context)) return false;
        const field = tree.tokenSlice(field_token);
        const origin = pair.origin;
        const actual = origin.aggregateField(pair.initializer, field) orelse return false;
        if (self.census) |census| {
            if (!self.leafEnumerable(invocation)) return false;
            if (!try census.record(self, invocation, call, pair, actual)) return false;
            self.invocations += 1;
            return true;
        }
        const origin_tree = origin.cache.tree;
        const null_actual = origin_tree.nodeTag(actual) == .identifier and
            std.mem.eql(u8, origin_tree.tokenSlice(origin_tree.nodeMainToken(actual)), "null");
        if (null_actual) {
            if (!try self.nullRejected(invocation, context, field)) return false;
        } else if (!try origin.typedAddress(actual)) return false;
        self.invocations += 1;
        return true;
    }

    fn aggregateField(self: *const Proof, initializer: Ast.Node.Index, name: []const u8) ?Ast.Node.Index {
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = self.cache.tree.fullStructInit(&buffer, initializer) orelse return null;
        for (literal.ast.fields) |field| {
            if (std.mem.eql(u8, self.fieldName(field) orelse continue, name)) return field;
        }
        return null;
    }

    fn typedAddress(self: *Proof, expression: Ast.Node.Index) !bool {
        const tree = self.cache.tree;
        const resolver = self.cache.zls.?;
        var source = expression;
        for (0..32) |_| {
            if (builtinArgument(tree, source, "@ptrCast") orelse
                builtinArgument(tree, source, "@constCast")) |argument|
            {
                source = argument;
                continue;
            }
            if (tree.nodeTag(source) == .field_access) {
                const slice, const field = tree.nodeData(source).node_and_token;
                if (!std.mem.eql(u8, tree.tokenSlice(field), "ptr")) return false;
                const slice_type = (try self.resolutionFrame().typeOfNode(slice)) orelse
                    return false;
                if (resolver.pointerSize(slice_type) != .slice) return false;
                const child = resolver.childType(slice_type) orelse return false;
                const actual = (try resolver.normalizedType(child)) orelse return false;
                // Byte destinations need no ABI guess. Other destinations
                // require identical elements and an ordinary slice alignment.
                if (!self.byteTarget() and
                    !TypeResolver.ActualType.eql(actual, self.target_child)) return false;
                return try self.ordinaryPointer(slice, 0);
            }
            const address_type = (try self.resolutionFrame().typeOfNode(source)) orelse
                return false;
            if (resolver.pointerSize(address_type) != .one) return false;
            const child = resolver.childType(address_type) orelse return false;
            const actual = (try resolver.normalizedType(child)) orelse return false;
            if (!TypeResolver.ActualType.eql(actual, self.target_child)) return false;
            if (tree.nodeTag(source) != .address_of) {
                return try self.ordinaryPointer(source, 0);
            }
            const pointee = tree.nodeData(source).node;
            // Packed fields and pointer-derived lvalues may be underaligned.
            if (tree.nodeTag(pointee) != .identifier) return false;
            const object = (try self.binding(pointee)) orelse return false;
            if (object.origin == .param) return false;
            for (1..tree.nodes.len) |raw| {
                const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
                if (local.ast.mut_token + 1 != object.name_token) continue;
                return local.ast.align_node.unwrap() == null;
            }
            return false;
        }
        return false;
    }

    fn byteTarget(self: *const Proof) bool {
        const index = self.target_child.ipIndex() orelse return false;
        return index == .u8_type or index == .i8_type;
    }

    fn ordinaryPointerType(
        self: *const Proof,
        frame: TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
    ) !bool {
        const source = (try pointerTypeSource(frame, node, 0)) orelse return false;
        const pointer = source.frame.handle.document.tree.fullPtrType(source.node).?;
        if (pointer.allowzero_token != null) return false;
        return self.byteTarget() or pointer.ast.align_node.unwrap() == null;
    }

    /// The engine's structural pointer value does not retain explicit
    /// underalignment. Inspect its declaration instead of guessing from it.
    fn ordinaryPointer(self: *Proof, expression: Ast.Node.Index, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        if (tree.nodeTag(expression) == .@"try") {
            return try self.ordinaryPointer(tree.nodeData(expression).node, depth + 1);
        }
        if (tree.nodeTag(expression) == .identifier) {
            const selected = (try self.binding(expression)) orelse return false;
            if (selected.origin == .param) {
                const declaration = tokens.enclosingFnDecl(tree, selected.name_token) orelse
                    return false;
                var buffer: [1]Ast.Node.Index = undefined;
                const proto = tokens.fnProto(tree, &buffer, declaration) orelse return false;
                var parameters = proto.iterate(tree);
                while (parameters.next()) |parameter| {
                    if (parameter.name_token != selected.name_token) continue;
                    return try self.ordinaryPointerType(
                        self.resolutionFrame(), parameter.type_expr orelse return false,
                    );
                }
                return false;
            }
            for (1..tree.nodes.len) |raw| {
                const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
                if (local.ast.mut_token + 1 != selected.name_token) continue;
                if (local.ast.type_node.unwrap()) |ty|
                    return try self.ordinaryPointerType(self.resolutionFrame(), ty);
                return try self.ordinaryPointer(
                    local.ast.init_node.unwrap() orelse return false, depth + 1,
                );
            }
            return false;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, expression) orelse return false;
        const canonical = (try self.cache.actualCallSummaryAt(
            call.queryToken(tree, expression), self.frame,
        )) orelse return false;
        const callee_tree = canonical.callee.tree;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(
            callee_tree, &proto_buffer, canonical.callee.declaration,
        ) orelse return false;
        var result = proto.ast.return_type.unwrap() orelse return false;
        if (callee_tree.nodeTag(result) == .error_union) {
            result = callee_tree.nodeData(result).node_and_node[1];
        }
        return try self.ordinaryPointerType(
            self.cache.zls.?.frameForFunction(canonical.callee.reference), result,
        );
    }

    fn terminates(self: *const Proof, expression: Ast.Node.Index) bool {
        const tree = self.cache.tree;
        var current = expression;
        for (0..tree.nodes.len) |_| {
            switch (tree.nodeTag(current)) {
                .@"return", .unreachable_literal => return true,
                .block, .block_semicolon, .block_two, .block_two_semicolon => {
                    var statements = engine.AstIterator.init(tree, current);
                    const statement = statements.next(tree) orelse return false;
                    if (statements.next(tree) != null) return false;
                    current = statement;
                },
                else => return false,
            }
        }
        return false;
    }

    /// Only straight-line calls may precede the return. Branches or labeled
    /// breaks can produce a borrowed fallback instead and are not certificates.
    fn allocationFallbackTerminates(self: *const Proof, expression: Ast.Node.Index) bool {
        if (self.terminates(expression)) return true;
        const tree = self.cache.tree;
        switch (tree.nodeTag(expression)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {},
            else => return false,
        }
        var statements = engine.AstIterator.init(tree, expression);
        var current = statements.next(tree) orelse return false;
        while (statements.next(tree)) |next| {
            var buffer: [1]Ast.Node.Index = undefined;
            if (tree.fullCall(&buffer, current) == null) return false;
            current = next;
        }
        return self.terminates(current);
    }

    fn nullRejected(
        self: *Proof,
        invocation: Ast.Node.Index,
        context: *const Binding,
        field: []const u8,
    ) !bool {
        const tree = self.cache.tree;
        var ancestor = invocation;
        for (0..tree.nodes.len) |_| {
            const block = self.parent(ancestor);
            if (@intFromEnum(block) == 0) return false;
            switch (tree.nodeTag(block)) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => {
                    var statements = engine.AstIterator.init(tree, block);
                    while (statements.next(tree)) |statement| {
                        if (statement == ancestor) break;
                        const branch = tree.fullIf(statement) orelse continue;
                        if (branch.ast.else_expr.unwrap() != null or
                            !self.terminates(branch.ast.then_expr)) continue;
                        const condition = branch.ast.cond_expr;
                        if (tree.nodeTag(condition) != .equal_equal) continue;
                        const left, const right = tree.nodeData(condition).node_and_node;
                        if (tree.nodeTag(right) != .identifier or
                            !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(right)), "null") or
                            tree.nodeTag(left) != .field_access) continue;
                        const base, const field_token = tree.nodeData(left).node_and_token;
                        if (!std.mem.eql(u8, tree.tokenSlice(field_token), field)) continue;
                        if (try self.isBinding(base, context)) return true;
                    }
                },
                else => {},
            }
            ancestor = block;
        }
        return false;
    }

    fn registrationProven(self: *Proof, initializer: Ast.Node.Index, field: []const u8) !bool {
        const before = self.invocations;
        const recorded = if (self.census) |census| census.dispatches.items.len else 0;
        if (try self.directRegistration(initializer, field)) return true;
        self.invocations = before;
        if (self.census) |census| census.rewind(recorded);
        const ty = (try self.carrierType(initializer)) orelse return false;
        if (self.cache.zls.?.typeTag(ty) != .@"struct") return false;
        const pair: Pair = .{
            .origin = self,
            .initializer = initializer,
            .table_field = null,
            .callback_field = field,
        };
        return try self.traceValue(initializer, .{
            .ty = ty, .initializer = .{ .proof = self, .node = initializer },
        }, pair, 0);
    }

    fn carrierType(self: *Proof, node: Ast.Node.Index) !?TypeResolver.ActualType {
        const resolver = self.cache.zls.?;
        const frame = self.resolutionFrame();
        var ty = (try frame.typeOfNode(node)) orelse
            (try frame.expectedTypeOfNode(node)) orelse return null;
        for (0..32) |_| {
            ty = (try resolver.normalizedType(ty)) orelse return null;
            if (resolver.typeTag(ty) == .optional) {
                ty = resolver.childType(ty) orelse return null;
                continue;
            }
            if (resolver.pointerSize(ty) == .one) {
                ty = resolver.childType(ty) orelse return null;
                continue;
            }
            return ty;
        }
        return null;
    }

    fn isNull(self: *const Proof, node: Ast.Node.Index) bool {
        return self.cache.tree.nodeTag(node) == .identifier and
            std.mem.eql(u8, self.cache.tree.tokenSlice(self.cache.tree.nodeMainToken(node)), "null");
    }

    /// Resolve runtime formal values only through the exact source call that
    /// carried this registration. This is not a declaration-wide assumption.
    fn runtimeOrigin(self: *Proof, node: Ast.Node.Index, depth: u32) anyerror!?Origin {
        if (depth == 32) return null;
        const tree = self.cache.tree;
        switch (tree.nodeTag(node)) {
            .grouped_expression => return try self.runtimeOrigin(tree.nodeData(node).node_and_token[0], depth + 1),
            .identifier => {
                const selected = (try self.binding(node)) orelse return .{ .proof = self, .node = node };
                if (selected.origin == .param) {
                    for (self.runtime_actuals) |actual| {
                        if (actual.parameter != selected.name_token) continue;
                        const value = actual.value_origin orelse actual.origin;
                        return try value.proof.runtimeOrigin(value.node, depth + 1);
                    }
                    return .{ .proof = self, .node = node };
                }
                if (selected.origin == .loop_capture) {
                    for (1..tree.nodes.len) |raw| {
                        const branch = tree.fullIf(@enumFromInt(raw)) orelse continue;
                        const capture = branch.payload_token orelse continue;
                        if (capture != selected.name_token) continue;
                        // A value capture preserves the selected function.
                        // A pointer capture can rebind the aggregate's header.
                        if (tree.tokenTag(capture) != .identifier or !selected.is_const or
                            !try self.runtimeBindingStable(selected)) return null;
                        return try self.runtimeOrigin(branch.ast.cond_expr, depth + 1);
                    }
                    return null;
                }
                for (1..tree.nodes.len) |raw| {
                    const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
                    if (local.ast.mut_token + 1 != selected.name_token) continue;
                    if (!try self.runtimeBindingStable(selected)) return null;
                    return try self.runtimeOrigin(local.ast.init_node.unwrap() orelse return null, depth + 1);
                }
                return .{ .proof = self, .node = node };
            },
            .field_access => {
                const root, const field = tree.nodeData(node).node_and_token;
                const origin = (try self.runtimeOrigin(root, depth + 1)) orelse return null;
                if (origin.proof.aggregateField(origin.node, tree.tokenSlice(field))) |value|
                    return try origin.proof.runtimeOrigin(value, depth + 1);
            },
            .address_of, .deref, .@"try" => return try self.runtimeOrigin(tree.nodeData(node).node, depth + 1),
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                if (builtinArgument(tree, node, "@ptrCast") orelse
                    builtinArgument(tree, node, "@alignCast") orelse
                    builtinArgument(tree, node, "@constCast")) |argument|
                    return try self.runtimeOrigin(argument, depth + 1);
            },
            else => {},
        }
        return .{ .proof = self, .node = node };
    }

    fn sameExpression(self: *Proof, left: Ast.Node.Index, right: Ast.Node.Index, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        if (left == right) return true;
        if (tree.nodeTag(left) == .grouped_expression)
            return try self.sameExpression(tree.nodeData(left).node_and_token[0], right, depth + 1);
        if (tree.nodeTag(right) == .grouped_expression)
            return try self.sameExpression(left, tree.nodeData(right).node_and_token[0], depth + 1);
        if (tree.nodeTag(left) != tree.nodeTag(right)) return false;
        switch (tree.nodeTag(left)) {
            .identifier => {
                const a = (try self.binding(left)) orelse return false;
                const b = (try self.binding(right)) orelse return false;
                return a.name_token == b.name_token;
            },
            .field_access => {
                const a, const af = tree.nodeData(left).node_and_token;
                const b, const bf = tree.nodeData(right).node_and_token;
                return std.mem.eql(u8, tree.tokenSlice(af), tree.tokenSlice(bf)) and
                    try self.sameExpression(a, b, depth + 1);
            },
            .array_access => {
                const a, const ai = tree.nodeData(left).node_and_node;
                const b, const bi = tree.nodeData(right).node_and_node;
                return try self.sameExpression(a, b, depth + 1) and
                    try self.sameExpression(ai, bi, depth + 1);
            },
            .number_literal => return std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(left)), tree.tokenSlice(tree.nodeMainToken(right))),
            else => return false,
        }
    }

    fn storeDominates(self: *const Proof, node: Ast.Node.Index, store: Origin) bool {
        const tree = self.cache.tree;
        if (store.proof.cache.tree != tree) return false;
        if (tree.firstToken(node) <= tree.lastToken(store.node)) return false;
        const block = self.parent(store.node);
        switch (tree.nodeTag(block)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {},
            else => return false,
        }
        var ancestor = node;
        for (0..tree.nodes.len) |_| {
            if (ancestor == block) return true;
            if (@intFromEnum(ancestor) == 0) return false;
            ancestor = self.parent(ancestor);
        }
        return false;
    }

    /// Bind a value only to the exact dominating indexed-cell initializer.
    /// The surrounding traceBinding census must still accept every header use
    /// before the callback certificate can succeed. Physical origin is kept.
    fn indexedRuntimeValue(self: *Proof, value: Ast.Node.Index, carrier: Carrier) !?Origin {
        const store = carrier.store orelse return null;
        const initializer = carrier.initializer orelse return null;
        if (store.proof != self or initializer.proof != self or
            !self.storeDominates(value, store)) return null;
        const tree = self.cache.tree;
        if (tree.nodeTag(store.node) != .assign) return null;
        const left, const right = tree.nodeData(store.node).node_and_node;
        if (tree.nodeTag(left) != .array_access or initializer.node != right) return null;
        var cell = value;
        for (0..32) |_| {
            switch (tree.nodeTag(cell)) {
                .address_of => cell = tree.nodeData(cell).node,
                .grouped_expression => cell = tree.nodeData(cell).node_and_token[0],
                else => return if (try self.sameExpression(cell, left, 0)) initializer else null,
            }
        }
        return null;
    }

    fn carrierRuntimeValue(self: *Proof, value: Ast.Node.Index, carrier: Carrier) !?Origin {
        if (try self.indexedRuntimeValue(value, carrier)) |origin| return origin;
        const copied = carrier.copied_cell orelse return null;
        if (copied.proof != self) return null;
        const initializer = carrier.initializer orelse return null;
        const tree = self.cache.tree;
        const declaration = tree.fullVarDecl(copied.node) orelse return null;
        const selected = (try self.bindingAtDeclaration(declaration.ast.mut_token + 1)) orelse return null;
        var cell = value;
        for (0..32) |_| {
            switch (tree.nodeTag(cell)) {
                .address_of => cell = tree.nodeData(cell).node,
                .grouped_expression => cell = tree.nodeData(cell).node_and_token[0],
                .identifier => return if (try self.isBinding(cell, selected)) initializer else null,
                else => return null,
            }
        }
        return null;
    }

    fn traceBinding(self: *Proof, selected: *const Binding, carrier: Carrier, pair: Pair, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        const old_cell = self.active_cell;
        self.active_cell = selected.name_token;
        defer self.active_cell = old_cell;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (self.census != null) try self.cache.chargeNormalCleanupAt(tree, node);
            if (!try self.isBinding(node, selected)) continue;
            if (!try self.traceUse(node, carrier, pair, depth)) return false;
        }
        return true;
    }

    /// Expand a private receiver-store constructor at every closed source call.
    /// Each result keeps its own receiver actual and transport horizon.
    fn traceFactoryStore(self: *Proof, selected: *const Binding, carrier: Carrier, pair: Pair, store: Ast.Node.Index, depth: u32) anyerror!bool {
        if (depth == 32 or carrier.path.len != 1 or carrier.path[0].selector != .field) return false;
        const tree = self.cache.tree;
        const declaration = tokens.enclosingFnDecl(tree, selected.name_token) orelse return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
        if (proto.visib_token != null) return false;
        const body = tokens.bodyOf(tree, declaration) orelse return false;
        var statements = engine.AstIterator.init(tree, body);
        if (statements.next(tree) != store) return false;
        const returned = statements.next(tree) orelse return false;
        if (statements.next(tree) != null or tree.nodeTag(returned) != .@"return") return false;
        const result = tree.nodeData(returned).opt_node.unwrap() orelse return false;
        if (tree.nodeTag(result) != .address_of) return false;
        const field_node = tree.nodeData(result).node;
        if (tree.nodeTag(field_node) != .field_access) return false;
        const root, const field = tree.nodeData(field_node).node_and_token;
        if (!std.mem.eql(u8, tree.tokenSlice(field), carrier.path[0].selector.field) or
            !try self.isBinding(root, selected)) return false;

        // The unbound registration is a recipe, not one presumed live caller.
        if (self.runtime_actuals.len == 0) {
            const calls = (try self.cache.closedLocalCalls(declaration)) orelse return false;
            if (calls.len == 0) return false;
            for (calls) |call_node| {
                try self.cache.chargeNormalCleanupAt(tree, call_node);
                if (!self.leafEnumerable(call_node)) return false;
                var call_buffer: [2]Ast.Node.Index = undefined;
                const call = TypeResolver.CallOperands.full(tree, &call_buffer, call_node) orelse return false;
                const canonical = (try self.cache.actualCallSummaryAt(call.queryToken(tree, call_node), null)) orelse return false;
                if (!canonical.callee.reference.handle.eql(self.resolutionFrame().handle) or
                    canonical.callee.declaration != declaration) return false;
                var caller = self.inCache(self.cache, self.parents);
                defer caller.deinit();
                caller.frame = canonical.callee.caller_frame;
                caller.factory_call = call_node;
                if (!try caller.enterEdge(call_node, canonical)) return false;
                defer caller.leaveEdge();
                var bound = self.inCache(self.cache, self.parents);
                defer bound.deinit();
                bound.frame = self.cache.zls.?.frameForFunction(canonical.callee.reference);
                var actuals: [64]RuntimeActual = undefined;
                var parameters = proto.iterate(tree);
                var index: usize = 0;
                var argument_buffer: [2]Ast.Node.Index = undefined;
                while (parameters.next()) |parameter| : (index += 1) {
                    if (index == actuals.len) return false;
                    const argument = (try canonical.callArgumentFor(self.cache, &argument_buffer, @intCast(index))) orelse return false;
                    actuals[index] = .{
                        .parameter = parameter.name_token orelse return false,
                        .origin = .{ .proof = &caller, .node = argument },
                        .borrowed = index == 0 and canonical.argument_offset == 1,
                    };
                }
                bound.runtime_actuals = actuals[0..index];
                if (!try bound.registrationProven(pair.initializer, pair.callback_field)) return false;
                self.invocations += bound.invocations;
            }
            return true;
        }
        for (self.runtime_actuals) |actual| {
            if (actual.parameter != selected.name_token) continue;
            const caller = actual.origin.proof;
            const call_node = caller.factory_call orelse return false;
            var cell = actual.origin.node;
            if (!actual.borrowed) {
                if (caller.cache.tree.nodeTag(cell) != .address_of) return false;
                cell = caller.cache.tree.nodeData(cell).node;
            }
            if (caller.cache.tree.nodeTag(cell) != .identifier) return false;
            const binding_item = (try caller.binding(cell)) orelse return false;
            if (binding_item.origin == .param) return false;
            var owner = carrier;
            owner.store = .{ .proof = caller, .node = call_node };
            owner.pointer = false;
            for (1..caller.cache.tree.nodes.len) |raw| {
                const local = caller.cache.tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
                if (local.ast.mut_token + 1 != binding_item.name_token) continue;
                const initializer = local.ast.init_node.unwrap() orelse return false;
                owner.birth = .{ .proof = caller, .node = initializer };
                owner.initializer = .{ .proof = caller, .node = initializer };
            }
            if (owner.birth == null) return false;
            if (!try caller.traceBinding(binding_item, owner, pair, depth + 1)) return false;
            var sink = carrier.project();
            sink.pointer = true;
            sink.store = null;
            sink.initializer = .{ .proof = pair.origin, .node = pair.initializer };
            const before = caller.invocations;
            if (!try caller.traceValue(call_node, sink, pair, depth + 1)) return false;
            self.invocations += caller.invocations - before;
            return true;
        }
        return false;
    }

    fn traceStored(self: *Proof, lhs: Ast.Node.Index, store: Ast.Node.Index, value: Carrier, pair: Pair, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        var node = lhs;
        var carrier = value;
        var path_buffer: [16]Carrier.Segment = undefined;
        carrier.store = .{ .proof = self, .node = store };
        const target_type = (try self.resolutionFrame().typeOfNode(lhs)) orelse return false;
        carrier.nullable = self.cache.zls.?.typeTag(target_type) == .optional;
        for (0..32) |_| {
            switch (tree.nodeTag(node)) {
                .field_access => {
                    const root, const field = tree.nodeData(node).node_and_token;
                    const outer = (try self.carrierType(root)) orelse return false;
                    if (self.cache.zls.?.typeTag(outer) != .@"struct") return false;
                    carrier = carrier.prepend(.{
                        .selector = .{ .field = tree.tokenSlice(field) },
                        .child = carrier.ty,
                        .pointer = carrier.pointer,
                        .nullable = carrier.nullable,
                    }, outer, &path_buffer) orelse return false;
                    node = root;
                },
                .array_access => {
                    const root, const index = tree.nodeData(node).node_and_node;
                    if (!try self.indexStable(index)) return false;
                    const outer = (try self.carrierType(root)) orelse return false;
                    carrier = carrier.prepend(.{
                        .selector = .{ .index = .{ .proof = self, .node = index } },
                        .child = carrier.ty,
                        .pointer = carrier.pointer,
                        .nullable = carrier.nullable,
                    }, outer, &path_buffer) orelse return false;
                    node = root;
                },
                .deref => {
                    carrier.pointer = true;
                    node = tree.nodeData(node).node;
                },
                .identifier => {
                    const selected = (try self.binding(node)) orelse return false;
                    if (selected.origin == .param) {
                        if (self.census == null) return false;
                        return try self.traceFactoryStore(selected, carrier, pair, store, depth + 1);
                    }
                    const root_type = (try self.resolutionFrame().typeOfNode(node)) orelse return false;
                    if (self.cache.zls.?.pointerSize(root_type) != null) {
                        if (!try self.bindingOwnsPhysicalStorage(selected)) return false;
                    }
                    // Physical birth precedes later field registration. Keep
                    // the element initializer when the owner is an array/slice.
                    for (1..tree.nodes.len) |raw| {
                        const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
                        if (local.ast.mut_token + 1 != selected.name_token) continue;
                        const initialized = local.ast.init_node.unwrap() orelse return false;
                        carrier.birth = .{ .proof = self, .node = initialized };
                        if (self.cache.zls.?.typeTag(root_type) == .@"struct")
                            carrier.initializer = .{ .proof = self, .node = initialized };
                        break;
                    }
                    return try self.traceBinding(selected, carrier, pair, depth + 1);
                },
                else => return false,
            }
        }
        return false;
    }

    fn traceValue(self: *Proof, node: Ast.Node.Index, carrier: Carrier, pair: Pair, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        const parent_node = self.parent(node);
        if (tree.fullVarDecl(parent_node)) |local| {
            if (local.ast.init_node.unwrap() != node) return false;
            const selected = (try self.bindingAtDeclaration(local.ast.mut_token + 1)) orelse return false;
            var copied = carrier;
            if (!carrier.pointer) {
                copied.birth = .{ .proof = self, .node = node };
                if (tree.nodeTag(node) == .identifier and carrier.initializer != null) {
                    // The caller's complete header census still applies to
                    // both cells. Copy their proved bytes, not a later value
                    // lookup through the distinct source cell's publications.
                    copied.copied_cell = .{ .proof = self, .node = parent_node };
                } else {
                    copied.initializer = .{ .proof = self, .node = node };
                    copied.copied_cell = null;
                }
            }
            return try self.traceBinding(selected, copied, pair, depth + 1);
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullStructInit(&buffer, parent_node)) |literal| {
            if (literal.ast.type_expr.unwrap() == node) return false;
            if (self.fieldName(node)) |field| {
                const outer = (try self.carrierType(parent_node)) orelse return false;
                if (self.cache.zls.?.typeTag(outer) != .@"struct") return false;
                var path_buffer: [16]Carrier.Segment = undefined;
                var nested = carrier.prepend(.{
                    .selector = .{ .field = field },
                    .child = carrier.ty,
                    .pointer = carrier.pointer,
                    .nullable = carrier.nullable,
                }, outer, &path_buffer) orelse return false;
                nested.initializer = .{ .proof = self, .node = parent_node };
                return try self.traceValue(parent_node, nested, pair, depth);
            }
            return try self.traceSpawn(parent_node, node, carrier, pair, depth);
        }
        if (tree.fullArrayInit(&buffer, parent_node)) |tuple| {
            if (tuple.ast.type_expr.unwrap() != null) return false;
            return try self.traceSpawn(parent_node, node, carrier, pair, depth);
        }
        if (tree.nodeTag(parent_node) == .assign) {
            const lhs, const rhs = tree.nodeData(parent_node).node_and_node;
            if (rhs != node) return false;
            return try self.traceStored(lhs, parent_node, carrier, pair, depth);
        }
        return try self.traceCall(node, parent_node, carrier, pair, depth);
    }

    fn traceUse(self: *Proof, node: Ast.Node.Index, carrier: Carrier, pair: Pair, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        const parent_node = self.parent(node);
        if (tree.nodeTag(parent_node) == .field_access) {
            const root, const field_token = tree.nodeData(parent_node).node_and_token;
            if (root != node) return false;
            const field = tree.tokenSlice(field_token);
            if (carrier.path.len != 0) {
                const selector = carrier.path[0].selector;
                if (selector == .field and std.mem.eql(u8, selector.field, field)) {
                    var projected = carrier.project();
                    if (projected.path.len == 0) {
                        projected.initializer = .{ .proof = pair.origin, .node = pair.initializer };
                    } else if (carrier.initializer) |origin| {
                        const resolved = (try origin.proof.runtimeOrigin(origin.node, 0)) orelse return false;
                        if (resolved.proof.aggregateField(resolved.node, field)) |value|
                            projected.initializer = .{ .proof = resolved.proof, .node = value };
                    }
                    return try self.traceUse(parent_node, projected, pair, depth);
                }
                var call_buffer: [1]Ast.Node.Index = undefined;
                if (tree.fullCall(&call_buffer, self.parent(parent_node))) |call| {
                    if (call.ast.fn_expr == parent_node)
                        return try self.traceCall(node, self.parent(parent_node), carrier, pair, depth);
                }
                if (self.cache.zls.?.typeTag(carrier.ty) != .@"struct") {
                    if ((self.cache.zls.?.pointerSize(carrier.ty) == .slice or
                        self.cache.zls.?.typeTag(carrier.ty) == .array) and
                        std.mem.eql(u8, field, "len")) return self.valueReadOnly(parent_node);
                    return false;
                }
                if (self.census != null and try self.neutralSiblingArgument(parent_node, pair))
                    return true;
                return try self.unrelatedAccess(parent_node, field, carrier, 0);
            }
            if (std.mem.eql(u8, field, pair.callback_field))
                return try self.traceDispatch(parent_node, node, carrier, pair, depth);
            if (self.isWritten(parent_node)) return false;
            var call_buffer: [1]Ast.Node.Index = undefined;
            if (tree.fullCall(&call_buffer, self.parent(parent_node))) |call| {
                if (call.ast.fn_expr == parent_node)
                    return try self.traceCall(node, self.parent(parent_node), carrier, pair, depth);
            }
            return self.valueReadOnly(parent_node);
        }
        if (tree.nodeTag(parent_node) == .array_access) {
            if (carrier.path.len == 0 or carrier.path[0].selector != .index) return false;
            const root, const index = tree.nodeData(parent_node).node_and_node;
            if (root != node) return false;
            const selected = carrier.path[0].selector.index;
            if (selected.proof.cache.tree != tree or !try self.sameExpression(index, selected.node, 0)) return false;
            return try self.traceUse(parent_node, carrier.project(), pair, depth);
        }
        if (tree.nodeTag(parent_node) == .assign) {
            const lhs, const rhs = tree.nodeData(parent_node).node_and_node;
            if (lhs == node) {
                if (carrier.store) |store| {
                    if (store.proof == self and store.node == parent_node) return true;
                }
                // Only the complete optional pair may be cleared. A write
                // to its callback or context field still invalidates it.
                if (carrier.path.len == 0 and carrier.nullable and self.isNull(rhs)) return true;
                return false;
            }
        }
        if (tree.fullIf(parent_node)) |branch| {
            if (branch.ast.cond_expr != node) return false;
            const capture = branch.payload_token orelse return false;
            if (tree.tokenTag(capture) != .identifier) return false;
            if (carrier.store) |store| if (!self.storeDominates(node, store)) return false;
            const selected = (try self.bindingAtDeclaration(capture)) orelse return false;
            var copied = carrier;
            copied.store = null;
            copied.pointer = false;
            copied.nullable = false;
            return try self.traceBinding(selected, copied, pair, depth + 1);
        }
        switch (tree.nodeTag(parent_node)) {
            .equal_equal, .bang_equal => {
                const left, const right = tree.nodeData(parent_node).node_and_node;
                return (left == node and self.isNull(right)) or (right == node and self.isNull(left));
            },
            .address_of => {
                var addressed = carrier;
                addressed.pointer = true;
                return try self.traceUse(parent_node, addressed, pair, depth);
            },
            .grouped_expression, .deref => return try self.traceUse(parent_node, carrier, pair, depth),
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                if (builtinArgument(tree, parent_node, "@alignCast") == node)
                    return try self.traceUse(parent_node, carrier, pair, depth);
                if (builtinArgument(tree, parent_node, "@ptrCast") == node or
                    builtinArgument(tree, parent_node, "@constCast") == node)
                {
                    const target = (try self.carrierType(parent_node)) orelse return false;
                    if (target.ipIndex() != .anyopaque_type and
                        !TypeResolver.ActualType.eql(target, carrier.ty)) return false;
                    return try self.traceUse(parent_node, carrier, pair, depth);
                }
            },
            else => {},
        }
        if (carrier.store) |store| {
            // Source-approved release calls are considered below. Every
            // dispatch/copy must follow the exact initializing store.
            if (!self.storeDominates(node, store) and !try self.standardRelease(parent_node, node)) return false;
        }
        return try self.traceValue(node, carrier, pair, depth);
    }

    fn traceDispatch(self: *Proof, callback: Ast.Node.Index, context: Ast.Node.Index, carrier: Carrier, pair: Pair, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        var source = callback;
        const parent_node = self.parent(source);
        if (tree.nodeTag(parent_node) == .@"orelse") {
            const value, const fallback = tree.nodeData(parent_node).node_and_node;
            if (value != source or !self.terminates(fallback)) return false;
            source = parent_node;
        }
        var buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullCall(&buffer, self.parent(source))) |call| {
            if (call.ast.fn_expr != source) return false;
            return try self.traceInvocation(call, context, pair);
        }
        const alias_token = if (tree.fullIf(self.parent(source))) |branch| blk: {
            if (branch.ast.cond_expr != source) return false;
            const capture = branch.payload_token orelse return false;
            if (tree.tokenTag(capture) != .identifier) return false;
            break :blk capture;
        } else blk: {
            const local = tree.fullVarDecl(self.parent(source)) orelse return false;
            if (tree.tokenTag(local.ast.mut_token) != .keyword_const) return false;
            break :blk local.ast.mut_token + 1;
        };
        if (carrier.store) |store| if (!self.storeDominates(source, store)) return false;
        const alias = (try self.bindingAtDeclaration(alias_token)) orelse return false;
        var uses: usize = 0;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (!try self.isBinding(node, alias)) continue;
            var call_buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buffer, self.parent(node)) orelse return false;
            if (call.ast.fn_expr != node or !try self.traceInvocation(call, context, pair)) return false;
            uses += 1;
        }
        return uses != 0;
    }

    fn traceInvocation(self: *Proof, call: Ast.full.Call, context: Ast.Node.Index, pair: Pair) !bool {
        if (call.ast.params.len <= self.parameter_index) return false;
        const tree = self.cache.tree;
        const handle = call.ast.params[self.parameter_index];
        if (tree.nodeTag(handle) != .field_access) return false;
        const root, const field = tree.nodeData(handle).node_and_token;
        if (!try self.sameExpression(root, context, 0)) return false;
        const actual = pair.origin.aggregateField(pair.initializer, tree.tokenSlice(field)) orelse return false;
        if (self.census) |census| {
            const invocation = self.parent(call.ast.fn_expr);
            if (!self.leafEnumerable(invocation)) return false;
            if (!try census.record(self, invocation, call, pair, actual)) return false;
        } else if (!try pair.origin.typedAddress(actual)) return false;
        self.invocations += 1;
        return true;
    }

    fn reachedRuntime(self: *Proof, call_node: Ast.Node.Index, callee: Ast.Node.Index) !?FileCache.ActualCallSummary {
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.cache.tree, &call_buffer, call_node) orelse return null;
        if (try self.cache.actualCallSummaryAt(call.queryToken(self.cache.tree, call_node), self.frame)) |canonical|
            return canonical;
        const origin = (try self.runtimeOrigin(callee, 0)) orelse return null;
        const reference = switch (try origin.proof.resolutionFrame().functionReference(origin.node)) {
            .function => |reference| reference,
            else => return null,
        };
        for (reference.tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .fn_decl) continue;
            const declaration: Ast.Node.Index = @enumFromInt(raw);
            var buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(reference.tree, &buffer, declaration) orelse continue;
            if (proto.ast.fn_token != reference.fn_token) continue;
            return .{
                .callee = .{
                    .call_node = call_node,
                    .tree = reference.tree,
                    .fn_token = reference.fn_token,
                    .handle = reference.handle,
                    .declaration = declaration,
                    .reference = reference,
                    .caller_frame = self.resolutionFrame(),
                },
                .summary = null,
                .argument_offset = 0,
                .read_only = null,
            };
        }
        return null;
    }

    fn standardRelease(self: *Proof, call_node: Ast.Node.Index, value: Ast.Node.Index) !bool {
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.cache.tree, &buffer, call_node) orelse return false;
        const canonical = (try self.reachedRuntime(call_node, call.ast.fn_expr)) orelse return false;
        const reference = canonical.callee.reference;
        const name = reference.actual_type.data.function.name orelse return false;
        if (!std.mem.eql(u8, name, "free") and !std.mem.eql(u8, name, "destroy")) return false;
        if (!try self.cache.zls.?.declaredInToolchainFile(reference.handle, "/std/mem/Allocator.zig")) return false;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const memory = (try canonical.callArgumentFor(self.cache, &argument_buffer, 1)) orelse return false;
        if (memory != value) return false;
        // A normal free can run before a later carrier read. Only a deferred
        // release stays outside the source dispatcher transport itself.
        var ancestor = call_node;
        for (0..32) |_| {
            ancestor = self.parent(ancestor);
            if (@intFromEnum(ancestor) == 0) return false;
            switch (self.cache.tree.nodeTag(ancestor)) {
                .@"defer", .@"errdefer" => return true,
                .block, .block_semicolon, .block_two, .block_two_semicolon => return false,
                else => {},
            }
        }
        return false;
    }

    fn traceCall(self: *Proof, value: Ast.Node.Index, call_node: Ast.Node.Index, carrier: Carrier, pair: Pair, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        if (self.census != null and self.factory_call == call_node) return true;
        if (try self.standardRelease(call_node, value)) return true;
        const tree = self.cache.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, call_node) orelse return false;
        if (call.ast.fn_expr == value) return false;
        const canonical = (try self.reachedRuntime(call_node, call.ast.fn_expr)) orelse return false;
        if (canonical.argument_offset == 0 and tree.nodeTag(call.ast.fn_expr) == .field_access) {
            const receiver, _ = tree.nodeData(call.ast.fn_expr).node_and_token;
            if (receiver == value) {
                // Reading a function-valued sibling is not a method receiver.
                // Certify its exact same-cell carrier argument instead. The
                // argument trace still checks the complete resolved source body.
                if (carrier.path.len == 0 or carrier.path[0].selector != .field) return false;
                for (call.ast.params) |argument| {
                    if (tree.nodeTag(argument) != .field_access) continue;
                    const root, const field = tree.nodeData(argument).node_and_token;
                    if (!std.mem.eql(u8, tree.tokenSlice(field), carrier.path[0].selector.field)) continue;
                    if (!try self.sameExpression(root, receiver, 0)) continue;
                    return try self.traceUse(root, carrier, pair, depth);
                }
                return false;
            }
        }
        const declaring = (try canonical.declaringCache(self.cache)) orelse return false;
        const callee_tree = canonical.callee.tree;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(callee_tree, &proto_buffer, canonical.callee.declaration) orelse return false;
        if (tokens.bodyOf(callee_tree, canonical.callee.declaration) == null) return false;
        if (proto.extern_export_inline_token) |modifier| {
            if (callee_tree.tokenTag(modifier) == .keyword_extern or callee_tree.tokenTag(modifier) == .keyword_export)
                return false;
        }
        if (!try self.enterEdge(call_node, canonical)) return false;
        defer self.leaveEdge();
        const owned_parents = if (tree != callee_tree) try parentMap(declaring) else null;
        defer if (owned_parents) |parents| declaring.gpa.free(parents);
        var next = self.inCache(declaring, owned_parents orelse self.parents);
        defer next.deinit();
        next.frame = declaring.zls.?.frameForFunction(canonical.callee.reference);
        var actuals: [64]RuntimeActual = undefined;
        var count: usize = 0;
        var selected_token: ?Ast.TokenIndex = null;
        var selected_pointer = false;
        var parameters = proto.iterate(callee_tree);
        var argument_buffer: [2]Ast.Node.Index = undefined;
        while (parameters.next()) |parameter| {
            if (count == actuals.len) return false;
            const argument = (try canonical.callArgumentFor(self.cache, &argument_buffer, @intCast(count))) orelse blk: {
                // A source-resolved runtime callback is not an implicit method.
                if (canonical.argument_offset != 0 or call.ast.params.len != canonical.callee.reference.actual_type.data.function.parameters.len)
                    return false;
                break :blk call.ast.params[count];
            };
            const name = parameter.name_token orelse return false;
            const parameter_type = (try next.resolutionFrame().typeOfNode(parameter.type_expr orelse return false)) orelse return false;
            actuals[count] = .{
                .parameter = name,
                .origin = .{ .proof = self, .node = argument },
                .borrowed = count == 0 and canonical.argument_offset == 1 and
                    declaring.zls.?.pointerSize(parameter_type) == .one,
            };
            count += 1;
            if (argument != value) continue;
            if (selected_token != null) return false;
            selected_token = name;
            actuals[count - 1].value_origin = try self.carrierRuntimeValue(value, carrier);
            const formal = (try next.resolutionFrame().typeOfNode(parameter.type_expr orelse return false)) orelse return false;
            var actual_type = (try declaring.zls.?.normalizedType(formal)) orelse return false;
            if (declaring.zls.?.pointerSize(actual_type) == .one) {
                selected_pointer = true;
                if (!carrier.pointer and !(count == 1 and canonical.argument_offset == 1)) return false;
                actual_type = (try declaring.zls.?.normalizedType(declaring.zls.?.childType(actual_type) orelse return false)) orelse return false;
                if (actual_type.ipIndex() == .anyopaque_type) continue;
            }
            if (!TypeResolver.ActualType.eql(actual_type, carrier.ty)) return false;
        }
        next.runtime_actuals = actuals[0..count];
        const binding_item = (try next.bindingAtDeclaration(selected_token orelse return false)) orelse return false;
        var copied = carrier;
        copied.store = null;
        copied.pointer = selected_pointer;
        if (!copied.pointer) {
            copied.birth = .{ .proof = &next, .node = canonical.callee.declaration };
            copied.initializer = .{ .proof = self, .node = value };
        }
        if (!try next.traceBinding(binding_item, copied, pair, depth + 1)) return false;
        self.invocations += next.invocations;
        return true;
    }

    /// The standard declaration, not a spelling, supplies the tuple-copy and
    /// callback dispatch contract. Project functions named spawn use their body.
    fn traceSpawn(self: *Proof, tuple: Ast.Node.Index, value: Ast.Node.Index, carrier: Carrier, pair: Pair, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call_node = self.parent(tuple);
        const call = tree.fullCall(&call_buffer, call_node) orelse return false;
        if (call.ast.params.len != 3 or call.ast.params[2] != tuple) return false;
        const spawn = switch (try self.resolutionFrame().functionReference(call.ast.fn_expr)) {
            .function => |reference| reference,
            else => return false,
        };
        if (!std.mem.eql(u8, spawn.actual_type.data.function.name orelse return false, "spawn") or
            !try self.cache.zls.?.declaredInToolchainFile(spawn.handle, "/std/Thread.zig")) return false;
        const origin = (try self.runtimeOrigin(call.ast.params[1], 0)) orelse return false;
        const reference = switch (try origin.proof.resolutionFrame().functionReference(origin.node)) {
            .function => |reference| reference,
            else => return false,
        };
        var literal_buffer: [2]Ast.Node.Index = undefined;
        const args = tree.fullArrayInit(&literal_buffer, tuple) orelse return false;
        if (args.ast.type_expr.unwrap() != null or
            args.ast.elements.len != reference.actual_type.data.function.parameters.len) return false;
        var selected_index: ?usize = null;
        for (args.ast.elements, 0..) |argument, index| {
            if (self.fieldName(argument) != null) return false;
            if (argument == value) selected_index = index;
        }
        const index = selected_index orelse return false;
        for (reference.tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .fn_decl) continue;
            const declaration: Ast.Node.Index = @enumFromInt(raw);
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(reference.tree, &proto_buffer, declaration) orelse continue;
            if (proto.ast.fn_token != reference.fn_token) continue;
            const canonical: FileCache.ActualCallSummary = .{
                .callee = .{
                    .call_node = call_node, .tree = reference.tree,
                    .fn_token = reference.fn_token, .handle = reference.handle,
                    .declaration = declaration, .reference = reference,
                    .caller_frame = self.resolutionFrame(),
                },
                .summary = null, .argument_offset = 0, .read_only = null,
            };
            const declaring = (try canonical.declaringCache(self.cache)) orelse return false;
            if (tokens.bodyOf(reference.tree, declaration) == null) return false;
            const owned_parents = if (tree != reference.tree) try parentMap(declaring) else null;
            defer if (owned_parents) |parents| declaring.gpa.free(parents);
            var next = self.inCache(declaring, owned_parents orelse self.parents);
            defer next.deinit();
            next.frame = declaring.zls.?.frameForFunction(reference);
            var actuals: [64]RuntimeActual = undefined;
            if (args.ast.elements.len > actuals.len) return false;
            var parameters = proto.iterate(reference.tree);
            var parameter_index: usize = 0;
            var selected: ?Ast.TokenIndex = null;
            while (parameters.next()) |parameter| : (parameter_index += 1) {
                const name = parameter.name_token orelse return false;
                actuals[parameter_index] = .{
                    .parameter = name,
                    .origin = .{ .proof = self, .node = args.ast.elements[parameter_index] },
                };
                if (parameter_index != index) continue;
                selected = name;
                actuals[parameter_index].value_origin = try self.carrierRuntimeValue(value, carrier);
                const formal = (try next.carrierType(parameter.type_expr orelse return false)) orelse return false;
                if (!TypeResolver.ActualType.eql(formal, carrier.ty)) return false;
            }
            next.runtime_actuals = actuals[0..parameter_index];
            const binding_item = (try next.bindingAtDeclaration(selected orelse return false)) orelse return false;
            var copied = carrier;
            copied.store = null;
            if (!try next.traceBinding(binding_item, copied, pair, depth + 1)) return false;
            self.invocations += next.invocations;
            return true;
        }
        return false;
    }

    fn scalarType(self: *Proof, node: Ast.Node.Index) !bool {
        const ty = (try self.resolutionFrame().typeOfNode(node)) orelse return false;
        return try @import("../cache/fresh_storage.zig").actualTypeAddressFree(self.resolutionFrame(), ty, 0, null);
    }

    /// The initializer is a value origin only while the cell's pointer-bearing
    /// fields remain unchanged. Active carrier aliases have their own complete
    /// source census; other mutable aliases cannot borrow that certificate.
    fn runtimeBindingStable(self: *Proof, selected: *const Binding) !bool {
        const tree = self.cache.tree;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (!try self.isBinding(node, selected)) continue;
            const parent_node = self.parent(node);
            if (self.isWritten(node)) {
                if (tree.nodeTag(parent_node) == .address_of and self.active_cell == selected.name_token) continue;
                return false;
            }
            if (tree.nodeTag(parent_node) != .field_access) continue;
            if (self.isWritten(parent_node) and !try self.scalarType(parent_node)) return false;
            if (self.active_cell == selected.name_token) continue;
            var call_buffer: [2]Ast.Node.Index = undefined;
            const call_node = self.parent(parent_node);
            if (TypeResolver.CallOperands.full(tree, &call_buffer, call_node)) |call| {
                if (call.ast.fn_expr != parent_node) continue;
                const effect = (try self.cache.callEffectAt(call.queryToken(tree, call_node), .{
                    .parameter = .{ .param = 0, .read_only_only = true },
                }, .{ .frame = self.frame })) orelse return false;
                if (effect != .read_only) return false;
            }
        }
        return true;
    }

    fn bindingFresh(self: *Proof, selected: *const Binding) !bool {
        const claim = @import("fn_summary.zig").claimFor(self.cache.tree, selected);
        return try @import("../cache/fresh_storage.zig").freshStorageAt(self.cache, .{
            .claim = claim, .depth = 0, .frame = self.frame,
        });
    }

    /// Fresh backing cells and a fresh reachable value graph are different
    /// claims. SDK allocation creates new physical cells even when their future
    /// elements carry pointers into existing graphs. Every use of this header
    /// still passes the carrier census before a certificate can be issued.
    fn bindingOwnsPhysicalStorage(self: *Proof, selected: *const Binding) !bool {
        if (try self.bindingFresh(selected)) return true;
        if (selected.origin == .param or selected.origin == .loop_capture) return false;
        const tree = self.cache.tree;
        for (1..tree.nodes.len) |raw| {
            const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
            if (local.ast.mut_token + 1 != selected.name_token) continue;
            var node = local.ast.init_node.unwrap() orelse return false;
            for (0..32) |_| {
                switch (tree.nodeTag(node)) {
                    .@"try", .grouped_expression => node = tree.nodeData(node).node,
                    .@"catch" => {
                        const operation, const fallback = tree.nodeData(node).node_and_node;
                        if (!self.allocationFallbackTerminates(fallback)) return false;
                        node = operation;
                    },
                    else => break,
                }
            }
            var buffer: [2]Ast.Node.Index = undefined;
            const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse return false;
            const canonical = (try self.reachedRuntime(node, call.ast.fn_expr)) orelse return false;
            const claim = @import("fn_summary.zig").claimFor(tree, selected);
            const primitive = (try @import("../cache/fresh_storage.zig").allocatorPrimitive(self.cache, canonical, .{
                .claim = claim, .depth = 0, .frame = self.frame,
            })) orelse return false;
            return primitive.operation == .allocate and !primitive.copies_elements;
        }
        return false;
    }

    fn indexStable(self: *Proof, node: Ast.Node.Index) !bool {
        const tree = self.cache.tree;
        if (tree.nodeTag(node) == .number_literal) return true;
        if (tree.nodeTag(node) != .identifier) return false;
        const selected = (try self.binding(node)) orelse return false;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const use: Ast.Node.Index = @enumFromInt(raw);
            if (try self.isBinding(use, selected) and self.isWritten(use)) return false;
        }
        return true;
    }

    fn localAddressBefore(self: *Proof, node: Ast.Node.Index, birth: Origin) !bool {
        const tree = self.cache.tree;
        if (tree.nodeTag(node) != .identifier) return false;
        const selected = (try self.binding(node)) orelse return false;
        if (selected.origin == .param or selected.origin == .loop_capture) return false;
        const ty = (try self.resolutionFrame().typeOfNode(node)) orelse return false;
        if (self.cache.zls.?.pointerSize(ty) != null) return false;
        if (self == birth.proof and selected.name_token >= tree.firstToken(birth.node)) return false;
        for (1..tree.nodes.len) |raw| {
            const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
            if (local.ast.mut_token + 1 != selected.name_token) continue;
            const initializer = local.ast.init_node.unwrap() orelse return false;
            return !(tree.nodeTag(initializer) == .identifier and
                std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(initializer)), "undefined"));
        }
        return false;
    }

    /// A pointer-free initialized lexical cell cannot reach the later carrier.
    /// This is stronger than an older pointer graph and preserves physical
    /// formal origins. Casts and computed pointer origins are not certificates.
    fn localPointeeBefore(self: *Proof, node: Ast.Node.Index, birth: Origin, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        switch (tree.nodeTag(node)) {
            .grouped_expression => return try self.localPointeeBefore(tree.nodeData(node).node_and_token[0], birth, depth + 1),
            .address_of => {
                const cell = tree.nodeData(node).node;
                if (self != birth.proof or !try self.localAddressBefore(cell, birth)) return false;
                if (tree.nodeTag(cell) != .identifier or !try self.scalarType(cell)) return false;
                const selected = (try self.binding(cell)) orelse return false;
                const owner = tokens.enclosingFnDecl(tree, selected.name_token) orelse return false;
                const carrier_owner = tokens.enclosingFnDecl(tree, tree.firstToken(birth.node)) orelse return false;
                return owner == carrier_owner;
            },
            .identifier => {
                const selected = (try self.binding(node)) orelse return false;
                if (selected.origin == .param) {
                    for (self.runtime_actuals) |actual| {
                        if (actual.parameter == selected.name_token)
                            return try actual.origin.proof.localPointeeBefore(actual.origin.node, birth, depth + 1);
                    }
                    return false;
                }
                if (!selected.is_const or !try self.runtimeBindingStable(selected)) return false;
                for (1..tree.nodes.len) |raw| {
                    const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
                    if (local.ast.mut_token + 1 != selected.name_token) continue;
                    return try self.localPointeeBefore(local.ast.init_node.unwrap() orelse return false, birth, depth + 1);
                }
                return false;
            },
            else => return false,
        }
    }

    fn pointerPredates(self: *Proof, node: Ast.Node.Index, birth: Origin, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        switch (tree.nodeTag(node)) {
            .grouped_expression => return try self.pointerPredates(tree.nodeData(node).node_and_token[0], birth, depth + 1),
            .address_of => return try self.localAddressBefore(tree.nodeData(node).node, birth),
            .identifier => {
                const selected = (try self.binding(node)) orelse return false;
                if (selected.origin == .param) {
                    for (self.runtime_actuals) |actual| {
                        if (actual.parameter != selected.name_token) continue;
                        if (actual.borrowed and try actual.origin.proof.localAddressBefore(actual.origin.node, birth)) return true;
                        return try actual.origin.proof.pointerPredates(actual.origin.node, birth, depth + 1);
                    }
                    return false;
                }
                if (self == birth.proof and selected.name_token >= tree.firstToken(birth.node)) return false;
                if (!try self.runtimeBindingStable(selected)) return false;
                for (1..tree.nodes.len) |raw| {
                    const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
                    if (local.ast.mut_token + 1 != selected.name_token) continue;
                    return try self.pointerPredates(local.ast.init_node.unwrap() orelse return false, birth, depth + 1);
                }
            },
            .@"try" => return try self.pointerPredates(tree.nodeData(node).node, birth, depth + 1),
            else => {},
        }
        // Only a complete SDK/source freshness proof admits a computed pointer.
        // Opaque casts and pointer arithmetic are not freshness witnesses.
        switch (tree.nodeTag(node)) {
            .call, .call_comma, .call_one, .call_one_comma => {
                return try @import("../cache/fresh_storage.zig").freshStorageAt(self.cache, .{
                    .claim = .{ .first = tree.firstToken(node), .last = tree.lastToken(node) },
                    .depth = 0, .frame = self.frame,
                });
            },
            else => return false,
        }
    }

    fn initiallyNull(self: *Proof, field: []const u8, carrier: Carrier) !bool {
        _ = self;
        const origin = carrier.initializer orelse return false;
        const resolved = (try origin.proof.runtimeOrigin(origin.node, 0)) orelse return false;
        var buffer: [2]Ast.Node.Index = undefined;
        if (resolved.proof.cache.tree.fullStructInit(&buffer, resolved.node) == null) return false;
        if (resolved.proof.aggregateField(resolved.node, field)) |value| return resolved.proof.isNull(value);
        if (carrier.ty.data != .container) return false;
        const scope = carrier.ty.data.container.scope_handle;
        const tree = &scope.handle.document.tree;
        const declaration = tree.fullContainerDecl(&buffer, scope.toNode()) orelse return false;
        for (declaration.ast.members) |member| {
            const declared = tree.fullContainerField(member) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(declared.ast.main_token), field)) continue;
            const value = declared.ast.value_expr.unwrap() orelse return false;
            return tree.nodeTag(value) == .identifier and
                std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(value)), "null");
        }
        return false;
    }

    /// A sibling address can be data for the same source-paired invocation.
    /// This does not make that data separate from the context's storage.
    fn neutralSiblingArgument(self: *Proof, node: Ast.Node.Index, pair: Pair) !bool {
        const factory_call = self.factory_call orelse return false;
        const tree = self.cache.tree;
        const address = self.parent(node);
        if (tree.nodeTag(address) != .address_of) return false;
        const invocation = self.parent(address);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, invocation) orelse return false;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access or
            call.ast.params.len <= self.parameter_index or
            tree.firstToken(invocation) <= tree.lastToken(factory_call)) return false;
        var found = false;
        for (call.ast.params, 0..) |argument, index| {
            if (argument == address and index != self.parameter_index) found = true;
        }
        if (!found) return false;
        const sink, const callback_field = tree.nodeData(call.ast.fn_expr).node_and_token;
        if (!std.mem.eql(u8, tree.tokenSlice(callback_field), pair.callback_field)) return false;
        if (!try self.factoryResultAlias(sink, factory_call, 0)) return false;
        const context = call.ast.params[self.parameter_index];
        if (tree.nodeTag(context) != .field_access) return false;
        const context_sink, const context_field = tree.nodeData(context).node_and_token;
        if (!try self.sameExpression(sink, context_sink, 0)) return false;
        return pair.origin.aggregateField(pair.initializer, tree.tokenSlice(context_field)) != null;
    }

    fn factoryResultAlias(self: *Proof, node: Ast.Node.Index, factory_call: Ast.Node.Index, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        if (node == factory_call) return true;
        const tree = self.cache.tree;
        if (tree.nodeTag(node) != .identifier) return false;
        const selected = (try self.binding(node)) orelse return false;
        if (selected.origin == .param or !selected.is_const or
            !try self.factoryAliasHeaderStable(selected)) return false;
        for (1..tree.nodes.len) |raw| {
            const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
            if (local.ast.mut_token + 1 != selected.name_token) continue;
            return try self.factoryResultAlias(local.ast.init_node.unwrap() orelse return false, factory_call, depth + 1);
        }
        return false;
    }

    /// This const pointer header cannot be rebound or exposed by address.
    /// The factory result's later full pair census, not this alias check,
    /// closes pointee effects and every callback/context-slot use.
    fn factoryAliasHeaderStable(self: *Proof, selected: *const Binding) !bool {
        const tree = self.cache.tree;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            try self.cache.chargeNormalCleanupAt(tree, node);
            if (!try self.isBinding(node, selected)) continue;
            if (self.isWritten(node)) return false;
            const parent_node = self.parent(node);
            if (tree.nodeTag(parent_node) == .field_access and
                !self.valueReadOnly(parent_node)) return false;
        }
        return true;
    }

    /// An inline component is not the address of its enclosing carrier.
    /// Replacing its value cannot replace the sibling callback/context slots.
    /// Borrowing its address needs a canonical SDK body with no parent recovery;
    /// a project method, opaque call, pointer field, or raw address is not proof.
    /// This closes pairing only: copied collection headers still alias storage.
    fn inlineComponentAccess(self: *Proof, node: Ast.Node.Index) !bool {
        const tree = self.cache.tree;
        if (tree.nodeTag(node) != .field_access) return false;
        const frame = self.resolutionFrame();
        const ty = (try frame.typeOfNode(node)) orelse return false;
        if (frame.resolver.pointerSize(ty) != null or frame.resolver.typeTag(ty) != .@"struct") return false;
        const parent_node = self.parent(node);
        if (tree.nodeTag(parent_node) == .assign)
            return tree.nodeData(parent_node).node_and_node[0] == node;
        if (tree.nodeTag(parent_node) != .field_access) return false;
        const receiver, _ = tree.nodeData(parent_node).node_and_token;
        if (receiver != node) return false;
        const call_node = self.parent(parent_node);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, call_node) orelse return false;
        if (call.ast.fn_expr != parent_node) return false;
        const canonical = (try self.cache.actualCallSummaryAt(call.queryToken(tree, call_node), self.frame)) orelse return false;
        if (canonical.argument_offset != 1) return false;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        if ((try canonical.callArgumentFor(self.cache, &argument_buffer, 0)) != node) return false;
        const fresh = @import("../cache/fresh_storage.zig");
        const standard = (try fresh.toolchainArrayListTree(self.cache, self.frame)) orelse return false;
        if (canonical.callee.tree != standard) return false;
        const name = standard.tokenSlice(canonical.callee.fn_token + 1);
        return std.mem.eql(u8, name, "deinit") or
            @import("method_names.zig").isArrayListGrowMethodName(name);
    }

    /// Before a fresh physical carrier is born, incoming pointer graphs cannot
    /// contain its address. The complete carrier-use census forbids publishing
    /// that address into those graphs and forbids rebinding their pointer headers.
    fn unrelatedAccess(self: *Proof, node: Ast.Node.Index, field: []const u8, carrier: Carrier, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        if (self.census != null and try self.inlineComponentAccess(node)) return true;
        if (self.isWritten(node)) {
            const parent_node = self.parent(node);
            if (tree.nodeTag(parent_node) == .address_of) return false;
            if (tree.nodeTag(parent_node) == .assign and self.isNull(tree.nodeData(parent_node).node_and_node[1])) return true;
            return try self.scalarType(node);
        }
        if (self.valueReadOnly(node)) {
            // A nested method call is not merely a read of its receiver.
            var current = node;
            for (0..tree.nodes.len) |_| {
                const parent_node = self.parent(current);
                var call_buffer: [1]Ast.Node.Index = undefined;
                if (tree.fullCall(&call_buffer, parent_node)) |call| {
                    if (call.ast.fn_expr != current) return true;
                    break;
                }
                switch (tree.nodeTag(parent_node)) {
                    .field_access, .array_access, .deref => current = parent_node,
                    .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => return false,
                    else => return true,
                }
            }
        }
        if (try self.initiallyNull(field, carrier)) return true;
        if (try self.emptyInlineReceiver(node, field, carrier)) return true;
        const birth = carrier.birth orelse return false;
        const initializer = carrier.initializer orelse return false;
        const resolved = (try initializer.proof.runtimeOrigin(initializer.node, 0)) orelse return false;
        const value = resolved.proof.aggregateField(resolved.node, field) orelse return false;
        if (!try resolved.proof.pointerPredates(value, birth, depth + 1)) return false;
        var current = node;
        for (0..tree.nodes.len) |_| {
            const parent_node = self.parent(current);
            if (self.isWritten(current)) {
                if (tree.nodeTag(parent_node) == .address_of) {
                    // An indexed scalar slot may be borrowed, but not a header.
                    const ty = (try self.resolutionFrame().typeOfNode(current)) orelse return false;
                    if (self.cache.zls.?.pointerSize(ty) != null) return false;
                    return true;
                }
                if (tree.nodeTag(current) == .field_access and !try self.scalarType(current)) return false;
                return true;
            }
            var call_buffer: [1]Ast.Node.Index = undefined;
            if (tree.fullCall(&call_buffer, parent_node)) |call| {
                if (call.ast.fn_expr != current) return true;
                const canonical = (try self.reachedRuntime(parent_node, call.ast.fn_expr)) orelse return false;
                if (tokens.bodyOf(canonical.callee.tree, canonical.callee.declaration) == null) return false;
                var operands_buffer: [2]Ast.Node.Index = undefined;
                const operands = TypeResolver.CallOperands.full(tree, &operands_buffer, parent_node) orelse return false;
                const token = operands.queryToken(tree, parent_node);
                const unrooted = (try self.cache.callEffectAt(token, .unrooted, .{
                    .frame = self.frame,
                })) orelse return false;
                if (unrooted != .read_only)
                    return try self.separatedMutexCall(canonical);
                const target = (try self.cache.callEffectAt(token, .{
                    .parameter = .{ .param = 0 },
                }, .{ .frame = self.frame })) orelse return false;
                if (target == .read_only or target == .writes_without_invalidation) return true;
                if (target != .may_invalidate) return false;
                // The unrooted effect and complete carrier-header census still
                // apply. Only this exact older pointer-free cell is separate.
                return try resolved.proof.localPointeeBefore(value, birth, depth + 1);
            }
            switch (tree.nodeTag(parent_node)) {
                .field_access, .array_access, .deref => current = parent_node,
                else => return false,
            }
        }
        return false;
    }

    /// A private physical-carrier proof, not an unrooted purity certificate.
    /// The caller has proved that the receiver graph predates the carrier and
    /// that its headers cannot acquire the carrier's address.
    fn separatedMutexCall(self: *Proof, canonical: FileCache.ActualCallSummary) !bool {
        const declaring = (try canonical.declaringCache(self.cache)) orelse return false;
        const tree = declaring.tree;
        const body = tokens.bodyOf(tree, canonical.callee.declaration) orelse return false;
        const owned_parents = if (tree != self.cache.tree) try parentMap(declaring) else null;
        defer if (owned_parents) |parents| declaring.gpa.free(parents);
        var next = self.inCache(declaring, owned_parents orelse self.parents);
        defer next.deinit();
        next.frame = declaring.zls.?.frameForFunction(canonical.callee.reference);
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, canonical.callee.declaration) orelse return false;
        if (proto.extern_export_inline_token) |modifier|
            if (tree.tokenTag(modifier) == .keyword_extern or tree.tokenTag(modifier) == .keyword_export)
                return false;
        var actuals: [64]RuntimeActual = undefined;
        var count: usize = 0;
        var parameters = proto.iterate(tree);
        while (parameters.next()) |parameter| : (count += 1) {
            if (count == actuals.len) return false;
            var buffer: [2]Ast.Node.Index = undefined;
            const argument = (try canonical.callArgumentFor(self.cache, &buffer, @intCast(count))) orelse return false;
            actuals[count] = .{
                .parameter = parameter.name_token orelse return false,
                .origin = .{ .proof = self, .node = argument },
                .borrowed = count == 0 and canonical.argument_offset == 1,
            };
        }
        if (count == 0 or canonical.argument_offset != 1) return false;
        next.runtime_actuals = actuals[0..count];
        const receiver = (try next.bindingAtDeclaration(actuals[0].parameter)) orelse return false;
        var mutex_calls: usize = 0;
        const first = tree.firstToken(body);
        const last = tree.lastToken(body);
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            const node: Ast.Node.Index = @enumFromInt(raw);
            if (raw == 0 or tree.firstToken(node) < first or tree.lastToken(node) > last) continue;
            switch (tag) {
                .fn_decl, .asm_simple, .@"asm", .address_of, .assign_destructure => return false,
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@intFromEnum")) return false;
                },
                .call, .call_comma, .call_one, .call_one_comma => {
                    if (!try next.selectedMutexCall(node, receiver)) return false;
                    mutex_calls += 1;
                },
                .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
                .assign_shl, .assign_shr, .assign_bit_and, .assign_bit_or, .assign_bit_xor,
                .assign_shl_sat, .assign_mul_wrap, .assign_add_wrap, .assign_sub_wrap,
                .assign_mul_sat, .assign_add_sat, .assign_sub_sat => {
                    const left = tree.nodeData(node).node_and_node[0];
                    if (!try next.scalarType(left) or !try next.rootedInlineField(left, receiver)) return false;
                },
                .identifier => {
                    // Non-scalar receiver/IO values can only select a field or
                    // be arguments of independently proved mutex calls.
                    if (try next.censusScalarValue(node, 0)) continue;
                    const parent_node = next.parent(node);
                    if (tree.nodeTag(parent_node) == .field_access) continue;
                    var buffer: [1]Ast.Node.Index = undefined;
                    if (tree.fullCall(&buffer, parent_node) == null) return false;
                },
                else => {},
            }
        }
        return mutex_calls != 0;
    }

    /// This private value proof does not admit an effect. Every call, builtin,
    /// write and address escape in the method still passes the full census.
    fn censusScalarValue(self: *Proof, node: Ast.Node.Index, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        if (try self.scalarType(node)) return true;
        const tree = self.cache.tree;
        if (builtinArgument(tree, node, "@intFromEnum") != null) return true;
        if (tree.nodeTag(node) == .grouped_expression)
            return try self.censusScalarValue(tree.nodeData(node).node_and_token[0], depth + 1);
        if (tree.nodeTag(node) != .identifier) return false;
        const selected = (try self.binding(node)) orelse return false;
        if (!selected.is_const or selected.origin == .param or selected.origin == .loop_capture or
            !try self.runtimeBindingStable(selected)) return false;
        for (1..tree.nodes.len) |raw| {
            const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
            if (local.ast.mut_token + 1 != selected.name_token) continue;
            return try self.censusScalarValue(local.ast.init_node.unwrap() orelse return false, depth + 1);
        }
        return false;
    }

    fn rootedInlineField(self: *Proof, node: Ast.Node.Index, receiver: *const Binding) !bool {
        var current = node;
        for (0..32) |_| {
            if (self.cache.tree.nodeTag(current) == .identifier)
                return try self.isBinding(current, receiver);
            if (self.cache.tree.nodeTag(current) != .field_access) return false;
            current = self.cache.tree.nodeData(current).node_and_token[0];
        }
        return false;
    }

    fn selectedMutexCall(self: *Proof, node: Ast.Node.Index, receiver: *const Binding) !bool {
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(self.cache.tree, &call_buffer, node) orelse return false;
        const canonical = (try self.reachedRuntime(node, call.ast.fn_expr)) orelse return false;
        const reference = canonical.callee.reference;
        const name = reference.actual_type.data.function.name orelse return false;
        if ((!std.mem.eql(u8, name, "lockUncancelable") and !std.mem.eql(u8, name, "unlock")) or
            !try self.cache.zls.?.declaredInToolchainFile(reference.handle, "/std/Io.zig"))
            return false;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const target = (try canonical.callArgumentFor(self.cache, &argument_buffer, 0)) orelse return false;
        if (!try self.rootedInlineField(target, receiver)) return false;
        const io = (try canonical.callArgumentFor(self.cache, &argument_buffer, 1)) orelse return false;
        return try self.selectedIoProvider(io, 0);
    }

    /// Resolve the selected value, never the mutable provider instance's
    /// initializer. Threaded.io's immutable vtable is independent of userdata.
    fn selectedIoProvider(self: *Proof, node: Ast.Node.Index, depth: u32) anyerror!bool {
        if (depth == 32) return false;
        const tree = self.cache.tree;
        if (tree.nodeTag(node) == .identifier) {
            if (try self.binding(node)) |binding_item|
                if (!try self.runtimeBindingStable(binding_item)) return false;
        }
        const origin = (try self.runtimeOrigin(node, 0)) orelse return false;
        if (origin.proof != self or origin.node != node)
            return try origin.proof.selectedIoProvider(origin.node, depth + 1);
        if (tree.fullIf(node)) |branch| {
            const alternative = branch.ast.else_expr.unwrap() orelse return false;
            if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(alternative)), "@compileError")) return false;
            return try self.selectedIoProvider(branch.ast.then_expr, depth + 1);
        }
        if (tree.nodeTag(node) == .field_access) {
            const root, const field = tree.nodeData(node).node_and_token;
            const value = (try self.resolutionFrame().resolveValueOfNode(root)) orelse return false;
            const namespace = (try self.cache.zls.?.normalizedType(value)) orelse return false;
            if (!namespace.is_type_val or namespace.data != .container) return false;
            const scope = namespace.data.container.scope_handle;
            const source = &scope.handle.document.tree;
            var buffer: [2]Ast.Node.Index = undefined;
            const members = if (@intFromEnum(scope.toNode()) == 0)
                source.rootDecls()
            else
                (source.fullContainerDecl(&buffer, scope.toNode()) orelse return false).ast.members;
            for (members) |member| {
                const declaration = source.fullVarDecl(member) orelse continue;
                if (!std.mem.eql(u8, source.tokenSlice(declaration.ast.mut_token + 1), tree.tokenSlice(field))) continue;
                if (source.tokenTag(declaration.ast.mut_token) != .keyword_const) return false;
                const document = try @import("../cache/grow_analysis.zig").sourceDocument(
                    self.cache, scope.handle, self.cache.zls.?.ctx,
                );
                const parents = try parentMap(&document.cache);
                defer self.cache.gpa.free(parents);
                var next = self.inCache(&document.cache, parents);
                defer next.deinit();
                next.frame = document.cache.zls.?.frameForContainer(namespace.data.container);
                return try next.selectedIoProvider(declaration.ast.init_node.unwrap() orelse return false, depth + 1);
            }
            return false;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const call = TypeResolver.CallOperands.full(tree, &buffer, node) orelse return false;
        const canonical = (try self.reachedRuntime(node, call.ast.fn_expr)) orelse return false;
        if (!std.mem.eql(u8, canonical.callee.reference.actual_type.data.function.name orelse return false, "io") or
            !try self.cache.zls.?.declaredInToolchainFile(canonical.callee.handle, "/std/Io/Threaded.zig"))
            return false;
        const declaring = (try canonical.declaringCache(self.cache)) orelse return false;
        const source = declaring.tree;
        const body = tokens.bodyOf(source, canonical.callee.declaration) orelse return false;
        var statements = engine.AstIterator.init(source, body);
        const result = statements.next(source) orelse return false;
        if (statements.next(source) != null or source.nodeTag(result) != .@"return") return false;
        const literal = source.nodeData(result).opt_node.unwrap() orelse return false;
        // Literal fields and authenticated futex providers do not use parents.
        var next = self.inCache(declaring, &.{});
        defer next.deinit();
        next.frame = declaring.zls.?.frameForFunction(canonical.callee.reference);
        const address = next.aggregateField(literal, "vtable") orelse return false;
        if (source.nodeTag(address) != .address_of) return false;
        const vtable = source.nodeData(address).node;
        for ([_][]const u8{ "futexWaitUncancelable", "futexWake" }) |entry| {
            const provider = next.aggregateField(vtable, entry) orelse return false;
            if (!try next.threadedFutexProvider(provider, entry)) return false;
        }
        return true;
    }

    /// This authenticated SDK primitive touches the futex word and SDK/kernel
    /// synchronization state, not project storage. Its source must discard
    /// userdata and forward the original const word pointer without callbacks.
    fn threadedFutexProvider(self: *Proof, node: Ast.Node.Index, entry: []const u8) !bool {
        const reference = switch (try self.resolutionFrame().functionReference(node)) {
            .function => |reference| reference,
            else => return false,
        };
        if (!std.mem.eql(u8, reference.actual_type.data.function.name orelse return false, entry) or
            !try self.cache.zls.?.declaredInToolchainFile(reference.handle, "/std/Io/Threaded.zig"))
            return false;
        const tree = reference.tree;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            if (tag != .fn_decl) continue;
            const declaration: Ast.Node.Index = @enumFromInt(raw);
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse continue;
            if (proto.ast.fn_token != reference.fn_token) continue;
            var parameters = proto.iterate(tree);
            const userdata = (parameters.next() orelse return false).name_token orelse return false;
            const word = (parameters.next() orelse return false).name_token orelse return false;
            const count = (parameters.next() orelse return false).name_token orelse return false;
            if (parameters.next() != null) return false;
            if (tree != self.cache.tree) return false;
            const userdata_binding = (try self.bindingAtDeclaration(userdata)) orelse return false;
            const word_binding = (try self.bindingAtDeclaration(word)) orelse return false;
            const count_binding = (try self.bindingAtDeclaration(count)) orelse return false;
            var statements = engine.AstIterator.init(tree, tokens.bodyOf(tree, declaration) orelse return false);
            const branch = tree.fullIf(statements.next(tree) orelse return false) orelse return false;
            if (branch.ast.else_expr.unwrap() != null) return false;
            const condition = branch.ast.cond_expr;
            if (tree.nodeTag(condition) != .field_access or
                !std.mem.eql(u8, tree.tokenSlice(tree.nodeData(condition).node_and_token[1]), "single_threaded"))
                return false;
            const terminal = branch.ast.then_expr;
            if (tree.nodeTag(terminal) != .unreachable_literal and
                !(tree.nodeTag(terminal) == .@"return" and tree.nodeData(terminal).opt_node.unwrap() == null))
                return false;
            const local = tree.fullVarDecl(statements.next(tree) orelse return false) orelse return false;
            const cast = builtinArgument(tree, local.ast.init_node.unwrap() orelse return false, "@ptrCast") orelse return false;
            const input = builtinArgument(tree, cast, "@alignCast") orelse return false;
            if (!try self.isBinding(input, userdata_binding)) return false;
            const discard = statements.next(tree) orelse return false;
            if (tree.nodeTag(discard) != .assign) return false;
            const discarded, const temporary = tree.nodeData(discard).node_and_node;
            const temporary_binding = (try self.bindingAtDeclaration(local.ast.mut_token + 1)) orelse return false;
            if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(discarded)), "_") or
                !try self.isBinding(temporary, temporary_binding)) return false;
            const dispatch = statements.next(tree) orelse return false;
            if (statements.next(tree) != null) return false;
            var call_buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buffer, dispatch) orelse return false;
            const arity: usize = if (std.mem.eql(u8, entry, "futexWake")) 2 else 3;
            if (call.ast.params.len != arity or
                !try self.isBinding(call.ast.params[0], word_binding) or
                !try self.isBinding(call.ast.params[1], count_binding)) return false;
            if (arity == 3 and
                !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(call.ast.params[2])), "null")) return false;
            const frame = self.cache.zls.?.frameForFunction(reference);
            const kernel = switch (try frame.functionReference(call.ast.fn_expr)) {
                .function => |function| function,
                else => return false,
            };
            return kernel.tree == reference.tree and kernel.fn_token != reference.fn_token and
                std.mem.eql(u8, kernel.actual_type.data.function.name orelse return false, entry);
        }
        return false;
    }

    fn fieldValueOrigin(self: *Proof, field: []const u8, carrier: Carrier) !?Origin {
        _ = self;
        const initializer = carrier.initializer orelse return null;
        const resolved = (try initializer.proof.runtimeOrigin(initializer.node, 0)) orelse return null;
        var buffer: [2]Ast.Node.Index = undefined;
        if (resolved.proof.cache.tree.fullStructInit(&buffer, resolved.node) == null) return null;
        if (resolved.proof.aggregateField(resolved.node, field)) |value|
            return .{ .proof = resolved.proof, .node = value };
        if (carrier.ty.data != .container) return null;
        const scope = carrier.ty.data.container.scope_handle;
        const tree = &scope.handle.document.tree;
        if (tree != resolved.proof.cache.tree) return null;
        const declaration = tree.fullContainerDecl(&buffer, scope.toNode()) orelse return null;
        for (declaration.ast.members) |member| {
            const declared = tree.fullContainerField(member) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(declared.ast.main_token), field)) continue;
            return .{ .proof = resolved.proof, .node = declared.ast.value_expr.unwrap() orelse return null };
        }
        return null;
    }

    /// A source-proved null field can stop an inline receiver before any effect.
    /// Require a first-statement field load with an empty return, not a method name.
    fn emptyInlineReceiver(self: *Proof, node: Ast.Node.Index, field: []const u8, carrier: Carrier) !bool {
        const tree = self.cache.tree;
        const method = self.parent(node);
        if (tree.nodeTag(method) != .field_access) return false;
        const call_node = self.parent(method);
        const canonical = (try self.reachedRuntime(call_node, method)) orelse
            return try self.sourceEmptyInlineReceiver(node, field, carrier);
        if (canonical.argument_offset != 1) return false;
        var call_buffer: [2]Ast.Node.Index = undefined;
        if ((try canonical.callArgumentFor(self.cache, &call_buffer, 0)) != node) return false;
        const body = tokens.bodyOf(canonical.callee.tree, canonical.callee.declaration) orelse return false;
        const callee_tree = canonical.callee.tree;
        var statements = engine.AstIterator.init(callee_tree, body);
        const first = statements.next(callee_tree) orelse return false;
        const local = callee_tree.fullVarDecl(first) orelse return false;
        const initializer = local.ast.init_node.unwrap() orelse return false;
        if (callee_tree.nodeTag(initializer) != .@"orelse") return false;
        const value, const fallback = callee_tree.nodeData(initializer).node_and_node;
        if (callee_tree.nodeTag(fallback) != .@"return" or
            callee_tree.nodeData(fallback).opt_node.unwrap() != null or
            callee_tree.nodeTag(value) != .field_access) return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(callee_tree, &proto_buffer, canonical.callee.declaration) orelse return false;
        var parameters = proto.iterate(callee_tree);
        const parameter = parameters.next() orelse return false;
        const root, const selected_field = callee_tree.nodeData(value).node_and_token;
        if (callee_tree.nodeTag(root) != .identifier or
            !std.mem.eql(u8, callee_tree.tokenSlice(callee_tree.nodeMainToken(root)),
                callee_tree.tokenSlice(parameter.name_token orelse return false))) return false;
        const supplied = (try self.fieldValueOrigin(field, carrier)) orelse return false;
        const ty = (try self.carrierType(node)) orelse return false;
        return try supplied.proof.initiallyNull(callee_tree.tokenSlice(selected_field), .{
            .ty = ty, .initializer = supplied,
        });
    }

    /// The physical carrier already has an authenticated struct identity.
    /// Resolve its authored field type in that declaration's container frame,
    /// not an unresolved runtime receiver expression from another invocation.
    fn declaredCarrierFieldType(self: *Proof, field: []const u8, carrier: Carrier) !?TypeResolver.ActualType {
        if (carrier.ty.data != .container) return null;
        const scope = carrier.ty.data.container.scope_handle;
        const tree = &scope.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const container = tree.fullContainerDecl(&buffer, scope.toNode()) orelse return null;
        const frame = self.cache.zls.?.frameForContainer(carrier.ty.data.container);
        for (container.ast.members) |member| {
            const declared = tree.fullContainerField(member) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(declared.ast.main_token), field)) continue;
            const type_node = declared.ast.type_expr.unwrap() orelse return null;
            const ty = (try frame.resolveValueOfNode(type_node)) orelse return null;
            return try self.cache.zls.?.normalizedType(ty);
        }
        return null;
    }

    /// A complete function value can be unavailable because its return type
    /// is opaque to resolution. This proof instead authenticates the selected
    /// receiver declaration and its first, effect-free null-return guard.
    fn sourceEmptyInlineReceiver(self: *Proof, node: Ast.Node.Index, field: []const u8, carrier: Carrier) !bool {
        const tree = self.cache.tree;
        const method = self.parent(node);
        if (tree.nodeTag(method) != .field_access) return false;
        const receiver, const member_token = tree.nodeData(method).node_and_token;
        if (receiver != node) return false;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, self.parent(method)) orelse return false;
        if (call.ast.fn_expr != method or call.ast.params.len != 0) return false;
        const ty = (try self.carrierType(node)) orelse
            (try self.declaredCarrierFieldType(field, carrier)) orelse return false;
        if (ty.data != .container or self.cache.zls.?.typeTag(ty) != .@"struct") return false;
        const scope = ty.data.container.scope_handle;
        const source = &scope.handle.document.tree;
        var container_buffer: [2]Ast.Node.Index = undefined;
        const container = source.fullContainerDecl(&container_buffer, scope.toNode()) orelse return false;
        const frame = self.cache.zls.?.frameForContainer(ty.data.container);
        for (container.ast.members) |member| {
            if (source.nodeTag(member) != .fn_decl) continue;
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(source, &proto_buffer, member) orelse continue;
            const name = proto.name_token orelse continue;
            if (!std.mem.eql(u8, source.tokenSlice(name), tree.tokenSlice(member_token))) continue;
            if (proto.extern_export_inline_token) |modifier| {
                if (source.tokenTag(modifier) == .keyword_extern or source.tokenTag(modifier) == .keyword_export) return false;
            }
            var parameters = proto.iterate(source);
            const parameter = parameters.next() orelse return false;
            if (parameters.next() != null) return false;
            const formal = (try frame.typeOfNode(parameter.type_expr orelse return false)) orelse return false;
            const normalized = (try self.cache.zls.?.normalizedType(formal)) orelse return false;
            if (self.cache.zls.?.pointerSize(normalized) != .one) return false;
            const child = (try self.cache.zls.?.normalizedType(self.cache.zls.?.childType(normalized) orelse return false)) orelse return false;
            if (!TypeResolver.ActualType.eql(child, ty)) return false;
            const body = tokens.bodyOf(source, member) orelse return false;
            var statements = engine.AstIterator.init(source, body);
            const first = statements.next(source) orelse return false;
            const local = source.fullVarDecl(first) orelse return false;
            const initializer = local.ast.init_node.unwrap() orelse return false;
            if (source.nodeTag(initializer) != .@"orelse") return false;
            const value, const fallback = source.nodeData(initializer).node_and_node;
            if (source.nodeTag(fallback) != .@"return" or source.nodeData(fallback).opt_node.unwrap() != null or
                source.nodeTag(value) != .field_access) return false;
            const root, const selected = source.nodeData(value).node_and_token;
            if (source.nodeTag(root) != .identifier or
                !std.mem.eql(u8, source.tokenSlice(source.nodeMainToken(root)), source.tokenSlice(parameter.name_token orelse return false))) return false;
            const supplied = (try self.fieldValueOrigin(field, carrier)) orelse return false;
            return try supplied.proof.initiallyNull(source.tokenSlice(selected), .{
                .ty = ty, .initializer = supplied,
            });
        }
        return false;
    }
};

test "closed callback refuses reflected function selection" {
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\fn select(comptime name: []const u8) *const fn (?*anyopaque) void {
        \\    return @field(Recorder, name);
        \\}
        \\test "binding" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    apply(context);
        \\    const escaped = select("callback");
        \\    escaped(null);
        \\}
    , false);
}

test "closed callback requires every actual paired context" {
    try expectProof(fixture_prefix ++
        \\fn apply(context: Context) void {
        \\    const invoke = context.procs.invoke orelse return;
        \\    invoke(context.handle);
        \\}
        \\test "bindings" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const safe: Context = .{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    const unsafe: Context = .{ .procs = &procs, .handle = null };
        \\    apply(safe);
        \\    apply(unsafe);
        \\}
    , false);
}

test "closed callback permits typed nonnull calls and guarded null unreachable calls" {
    try expectProof(fixture_prefix ++
        \\fn apply(context: Context) void {
        \\    const invoke = context.procs.invoke orelse return;
        \\    invoke(context.handle);
        \\}
        \\test "binding" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    apply(context);
        \\}
    , true);
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\test "binding" {
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = null };
        \\    forward(context);
        \\}
    , true);
}

const fixture_prefix =
    \\const Recorder = struct {
    \\    count: u32 = 0,
    \\    fn callback(handle: ?*anyopaque) void {
    \\        const self: *Recorder = @ptrCast(@alignCast(handle.?));
    \\        self.count += 1;
    \\    }
    \\};
    \\const Procs = struct { invoke: ?*const fn (?*anyopaque) void = null };
    \\const Context = struct { procs: *const Procs, handle: ?*anyopaque };
;
const fixture_guarded =
    \\fn apply(context: Context) void {
    \\    if (context.handle == null) return;
    \\    const invoke = context.procs.invoke orelse return;
    \\    invoke(context.handle);
    \\}
    \\fn forward(context: Context) void { apply(context); }
;

fn expectProof(source: [:0]const u8, expected: bool) !void {
    const gpa = std.testing.allocator;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/zbc-callback-provenance-test.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const cache = try gpa.create(FileCache);
    defer gpa.destroy(cache);
    cache.* = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .fn_decl) continue;
        const declaration: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration).?;
        const name = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name), "callback")) continue;
        const body = tree.nodeData(declaration).node_and_node[1];
        var token = tree.firstToken(body);
        while (token <= tree.lastToken(body)) : (token += 1) {
            if (std.mem.eql(u8, tree.tokenSlice(token), "@alignCast")) {
                try std.testing.expectEqual(expected, try callbackParameterProven(cache, proto, token));
                return;
            }
        }
    }
    return error.MissingCallbackCast;
}

test "closed mutable proc binding transports typed context through source calls" {
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\test "binding" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    forward(context);
        \\}
    , true);
}

test "closed callback accepts unconditional null rejection without treating calls as termination" {
    try expectProof(fixture_prefix ++
        \\fn apply(context: Context) void {
        \\    if (context.handle == null) { return; }
        \\    const invoke = context.procs.invoke orelse unreachable;
        \\    invoke(context.handle);
        \\}
        \\test "binding" {
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = null };
        \\    apply(context);
        \\}
    , true);
    try expectProof(fixture_prefix ++
        \\extern fn unknown() void;
        \\fn apply(context: Context) void {
        \\    if (context.handle == null) unknown();
        \\    const invoke = context.procs.invoke orelse return;
        \\    invoke(context.handle);
        \\}
        \\test "binding" {
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = null };
        \\    apply(context);
        \\}
    , false);
}

test "closed callback null guards require the exact primitive identifier" {
    try expectProof(fixture_prefix ++
        \\fn apply(context: Context) void {
        \\    const @"null": ?*anyopaque = @ptrFromInt(1);
        \\    if (context.handle == @"null") return;
        \\    const invoke = context.procs.invoke orelse return;
        \\    invoke(context.handle);
        \\}
        \\test "binding" {
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = null };
        \\    apply(context);
        \\}
    , false);
}

test "closed callback resolves an explicitly named aggregate initializer" {
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\test "binding" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context = Context{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    forward(context);
        \\}
    , true);
}

test "closed callback refuses unguarded null and underaligned handles" {
    try expectProof(fixture_prefix ++
        \\fn apply(context: Context) void {
        \\    const invoke = context.procs.invoke orelse return;
        \\    invoke(context.handle);
        \\}
        \\test "binding" {
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = null };
        \\    apply(context);
        \\}
    , false);
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\test "binding" {
        \\    var bytes: [64]u8 = undefined;
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrCast(&bytes) };
        \\    apply(context);
        \\}
    , false);
}

test "closed callback refuses escaped mutable alias and unrelated pairing" {
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\extern fn unknown(procs: *Procs) void;
        \\test "binding" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const alias = &procs;
        \\    unknown(alias);
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    apply(context);
        \\}
    , false);
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\test "binding" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrFromInt(1) };
        \\    apply(context);
        \\    _ = &recorder;
        \\}
    , false);
}

test "closed callback refuses field mutation after pairing" {
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\test "binding" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    procs.invoke = null;
        \\    apply(context);
        \\}
    , false);
}

test "closed callback refuses explicit underalignment and branch-only null guards" {
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\test "binding" {
        \\    var recorder: Recorder align(1) = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    apply(context);
        \\}
    , false);
    try expectProof(fixture_prefix ++
        \\fn apply(context: Context) void {
        \\    if (context.procs.invoke != null) {
        \\        if (context.handle == null) return;
        \\    }
        \\    const invoke = context.procs.invoke orelse return;
        \\    invoke(context.handle);
        \\}
        \\test "binding" {
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = null };
        \\    apply(context);
        \\}
    , false);
}

test "closed callback refuses escaping the paired aggregate" {
    try expectProof(fixture_prefix ++ "\n" ++ fixture_guarded ++
        \\extern fn unknown(context: Context) void;
        \\test "binding" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = .{};
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    unknown(context);
        \\    apply(context);
        \\}
    , false);
}

test "closed callback refuses overlapping union table fields" {
    try expectProof(
        \\const Recorder = struct {
        \\    count: u32 = 0,
        \\    fn callback(handle: ?*anyopaque) void {
        \\        const self: *Recorder = @ptrCast(@alignCast(handle.?));
        \\        self.count += 1;
        \\    }
        \\};
        \\const Procs = extern union {
        \\    invoke: ?*const fn (?*anyopaque) void,
        \\    other: ?*const fn (?*anyopaque) void,
        \\};
        \\const Context = struct { procs: *const Procs, handle: ?*anyopaque };
        \\fn apply(context: Context) void {
        \\    const invoke = context.procs.invoke orelse return;
        \\    invoke(context.handle);
        \\}
        \\test "binding" {
        \\    var recorder: Recorder = .{};
        \\    var procs: Procs = undefined;
        \\    procs.invoke = Recorder.callback;
        \\    const context: Context = .{ .procs = &procs, .handle = @ptrCast(&recorder) };
        \\    procs.other = null;
        \\    apply(context);
        \\}
    , false);
}

const direct_fixture =
    \\const State = struct { calls: usize = 0 };
    \\const Callback = struct {
    \\    context: ?*anyopaque,
    \\    run_fn: *const fn (usize, ?*anyopaque) void,
    \\};
    \\fn callback(_: usize, context: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(context.?));
    \\    state.calls += 1;
    \\}
    \\fn dispatch(pair: Callback) void { pair.run_fn(0, pair.context); }
;

test "direct callback pair preserves second parameter context in inline registrations" {
    try expectProof(direct_fixture ++
        \\test "registration" {
        \\    var state: State = .{};
        \\    dispatch(.{ .context = &state, .run_fn = callback });
        \\}
    , true);
}

test "direct callback pair survives immutable local and source forwarding" {
    try expectProof(direct_fixture ++
        \\fn forward(pair: Callback) void { dispatch(pair); }
        \\test "registration" {
        \\    var state: State = .{};
        \\    const pair: Callback = .{ .context = @ptrCast(&state), .run_fn = callback };
        \\    forward(pair);
        \\}
    , true);
}

test "direct callback pair refuses mixed null and wrongly typed registrations" {
    try expectProof(direct_fixture ++
        \\test "registration" {
        \\    var state: State = .{};
        \\    dispatch(.{ .context = &state, .run_fn = callback });
        \\    dispatch(.{ .context = null, .run_fn = callback });
        \\}
    , false);
    try expectProof(direct_fixture ++
        \\test "registration" {
        \\    var bytes: [64]u8 = undefined;
        \\    dispatch(.{ .context = @ptrCast(&bytes), .run_fn = callback });
        \\}
    , false);
}

test "direct callback pair refuses explicitly unaligned context and open calls" {
    try expectProof(direct_fixture ++
        \\test "registration" {
        \\    var state: State align(1) = .{};
        \\    dispatch(.{ .context = &state, .run_fn = callback });
        \\}
    , false);
    try expectProof(direct_fixture ++
        \\extern fn escape(pair: Callback) void;
        \\test "registration" {
        \\    var state: State = .{};
        \\    const pair: Callback = .{ .context = &state, .run_fn = callback };
        \\    escape(pair);
        \\    dispatch(pair);
        \\}
    , false);
}

test "direct callback pair refuses context replacement and mismatched invocation field" {
    try expectProof(direct_fixture ++
        \\fn replace(pair: Callback) void {
        \\    var mutable = pair;
        \\    mutable.context = null;
        \\    dispatch(mutable);
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    replace(.{ .context = &state, .run_fn = callback });
        \\}
    , false);
    try expectProof(
        \\const State = struct { calls: usize = 0 };
        \\const Callback = struct {
        \\    context: ?*anyopaque, other: ?*anyopaque,
        \\    run_fn: *const fn (?*anyopaque) void,
        \\};
        \\fn callback(context: ?*anyopaque) void {
        \\    const state: *State = @ptrCast(@alignCast(context.?));
        \\    state.calls += 1;
        \\}
        \\fn dispatch(pair: Callback) void { pair.run_fn(pair.other); }
        \\test "registration" {
        \\    var state: State = .{};
        \\    dispatch(.{ .context = &state, .other = null, .run_fn = callback });
        \\}
    , false);
}

test "direct callback pair refuses an independently escaping callback value" {
    try expectProof(direct_fixture ++
        \\test "registration" {
        \\    var state: State = .{};
        \\    dispatch(.{ .context = &state, .run_fn = callback });
        \\    callback(0, null);
        \\}
    , false);
}

test "direct callback pair refuses reflection on a different callback owner" {
    try expectProof(
        \\const Harness = struct {
        \\    const State = struct { calls: usize = 0 };
        \\    fn callback(context: ?*anyopaque) void {
        \\        const state: *State = @ptrCast(@alignCast(context.?));
        \\        state.calls += 1;
        \\    }
        \\};
        \\const Pair = struct { context: ?*anyopaque, run_fn: *const fn (?*anyopaque) void };
        \\fn dispatch(pair: Pair) void { pair.run_fn(pair.context); }
        \\fn select(comptime name: []const u8) *const fn (?*anyopaque) void {
        \\    return @field(Harness, name);
        \\}
        \\test "registration" {
        \\    var state: Harness.State = .{};
        \\    dispatch(.{ .context = &state, .run_fn = Harness.callback });
        \\    select("callback")(null);
        \\}
    , false);
}

test "direct callback pair supports a test-local spawner method receiver" {
    try expectProof(
        \\test "registration" {
        \\    const SpawnState = struct { spawned: usize = 0 };
        \\    const FailingSpawner = struct {
        \\        fn callback(context: ?*anyopaque, _: *anyopaque) void {
        \\            const state: *SpawnState = @ptrCast(@alignCast(context.?));
        \\            state.spawned += 1;
        \\        }
        \\    };
        \\    var state: SpawnState = .{};
        \\    dispatch(.{ .context = &state, .run_fn = FailingSpawner.callback });
        \\}
        \\const Spawner = struct {
        \\    context: ?*anyopaque, run_fn: *const fn (?*anyopaque, *anyopaque) void,
        \\    fn spawn(self: Spawner) void {
        \\        var thread: u8 = 0;
        \\        self.run_fn(self.context, &thread);
        \\    }
        \\};
        \\fn dispatch(spawner: Spawner) void { spawner.spawn(); }
    , true);
}

test "direct callback pair supports a trace alias without confusing user context" {
    try expectProof(
        \\const TraceState = struct { events: usize = 0 };
        \\const JobContext = struct {
        \\    user_context: ?*anyopaque, trace_context: ?*anyopaque,
        \\    trace_hook: ?*const fn (?*anyopaque) void,
        \\};
        \\fn emit(context: JobContext) void {
        \\    const hook = context.trace_hook orelse return;
        \\    hook(context.trace_context);
        \\}
        \\test "registration" {
        \\    const trace = struct {
        \\        fn callback(context: ?*anyopaque) void {
        \\            const state: *TraceState = @ptrCast(@alignCast(context.?));
        \\            state.events += 1;
        \\        }
        \\    }.callback;
        \\    var state: TraceState = .{};
        \\    emit(.{ .user_context = null, .trace_context = @ptrCast(&state), .trace_hook = trace });
        \\}
    , true);
}

test "direct callback pair proves stored cleanup registrations with closed source uses" {
    try expectProof(
        \\const Scene = struct {
        \\    calls: usize = 0,
        \\    fn callback(context: ?*anyopaque) void {
        \\        const self: *@This() = @ptrCast(@alignCast(context.?));
        \\        self.calls += 1;
        \\    }
        \\};
        \\const Pair = struct { context: ?*anyopaque, release: *const fn (?*anyopaque) void };
        \\const Cleanup = struct {
        \\    scene: ?Pair = null,
        \\    fn deinit(self: *Cleanup) void {
        \\        if (self.scene) |scene| { scene.release(scene.context); self.scene = null; }
        \\    }
        \\};
        \\test "registration" {
        \\    var scene: Scene = .{};
        \\    var cleanup: Cleanup = .{};
        \\    cleanup.scene = .{ .context = &scene, .release = Scene.callback };
        \\    cleanup.deinit();
        \\}
    , true);
}

test "direct callback pair proves trace optional captures through a readonly receiver" {
    try expectProof(
        \\const TraceState = struct { events: usize = 0 };
        \\const JobContext = struct {
        \\    user_context: ?*anyopaque, trace_context: ?*anyopaque,
        \\    trace_hook: ?*const fn (?*anyopaque) void,
        \\    fn emit(self: *const JobContext) void {
        \\        if (self.trace_hook) |hook| hook(self.trace_context);
        \\    }
        \\};
        \\fn dispatch(context: JobContext) void { context.emit(); }
        \\test "registration" {
        \\    const trace = struct {
        \\        fn callback(context: ?*anyopaque) void {
        \\            const state: *TraceState = @ptrCast(@alignCast(context.?));
        \\            state.events += 1;
        \\        }
        \\    }.callback;
        \\    var state: TraceState = .{};
        \\    dispatch(.{
        \\        .user_context = @ptrCast(&state),
        \\        .trace_context = @ptrCast(&state), .trace_hook = trace,
        \\    });
        \\}
    , true);
}

test "direct callback pair refuses a public callback despite one typed registration" {
    try expectProof(
        \\const State = struct { calls: usize = 0 };
        \\const Pair = struct { context: ?*anyopaque, run_fn: *const fn (?*anyopaque) void };
        \\pub fn callback(context: ?*anyopaque) void {
        \\    const state: *State = @ptrCast(@alignCast(context.?));
        \\    state.calls += 1;
        \\}
        \\fn dispatch(pair: Pair) void { pair.run_fn(pair.context); }
        \\test "registration" {
        \\    var state: State = .{};
        \\    dispatch(.{ .context = &state, .run_fn = callback });
        \\}
    , false);
}

test "direct callback pair accepts a nonnull ordinary typed pointer parameter" {
    try expectProof(direct_fixture ++
        \\fn register(state: *State) void {
        \\    dispatch(.{ .context = state, .run_fn = callback });
        \\}
    , true);
}

test "direct callback pair closes instantiated type arguments without callback reflection" {
    try expectProof(direct_fixture ++
        \\fn select(comptime T: type, state: *T) *T {
        \\    _ = @sizeOf(T);
        \\    return state;
        \\}
        \\fn register(state: *State) void {
        \\    const selected = select(State, state);
        \\    dispatch(.{ .context = selected, .run_fn = callback });
        \\}
    , true);
}

test "direct callback pair refuses callback exposure through an instantiated type argument" {
    try expectProof(
        \\const State = struct {
        \\    calls: usize = 0,
        \\    fn callback(context: ?*anyopaque) void {
        \\        const self: *State = @ptrCast(@alignCast(context.?));
        \\        self.calls += 1;
        \\    }
        \\};
        \\const Callback = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) void };
        \\fn select(comptime T: type, state: *T) *T {
        \\    T.callback(null);
        \\    return state;
        \\}
        \\fn dispatch(pair: Callback) void { pair.invoke(pair.context); }
        \\fn register(state: *State) void {
        \\    const selected = select(State, state);
        \\    dispatch(.{ .context = selected, .invoke = State.callback });
        \\}
    , false);
}

test "callback parent map visits assembly operands through the containing asm" {
    try expectProof(direct_fixture ++
        \\fn unrelated(value: usize) usize {
        \\    return asm volatile (""
        \\        : [result] "=r" (-> usize),
        \\        : [input] "r" (value),
        \\        : .{}
        \\    );
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    dispatch(.{ .context = &state, .run_fn = callback });
        \\}
    , true);
}

test "trace optional capture refuses a mismatched context field" {
    try expectProof(
        \\const State = struct { calls: usize = 0 };
        \\const Pair = struct {
        \\    context: ?*anyopaque,
        \\    other: ?*anyopaque,
        \\    invoke: ?*const fn (?*anyopaque) void,
        \\    fn dispatch(self: *const Pair) void {
        \\        if (self.invoke) |callback| callback(self.other);
        \\    }
        \\};
        \\fn callback(context: ?*anyopaque) void {
        \\    const state: *State = @ptrCast(@alignCast(context.?));
        \\    state.calls += 1;
        \\}
        \\fn run(pair: Pair) void { pair.dispatch(); }
        \\test "registration" {
        \\    var state: State = .{};
        \\    run(.{ .context = &state, .other = null, .invoke = callback });
        \\}
    , false);
}

test "trace optional capture refuses callback escape through a readonly receiver" {
    try expectProof(
        \\const State = struct { calls: usize = 0 };
        \\extern fn escape(*const Pair) void;
        \\const Pair = struct {
        \\    context: ?*anyopaque,
        \\    invoke: ?*const fn (?*anyopaque) void,
        \\    fn dispatch(self: *const Pair) void {
        \\        escape(self);
        \\        if (self.invoke) |callback| callback(self.context);
        \\    }
        \\};
        \\fn callback(context: ?*anyopaque) void {
        \\    const state: *State = @ptrCast(@alignCast(context.?));
        \\    state.calls += 1;
        \\}
        \\fn run(pair: Pair) void { pair.dispatch(); }
        \\test "registration" {
        \\    var state: State = .{};
        \\    run(.{ .context = &state, .invoke = callback });
        \\}
    , false);
}

const nested_worker_fixture =
    \\const State = struct { calls: usize = 0 };
    \\const Worker = struct {
    \\    context: ?*anyopaque,
    \\    run_fn: *const fn (?*anyopaque) void,
    \\    fn run(self: Worker) void { self.run_fn(self.context); }
    \\};
    \\const Execution = struct {
    \\    worker: Worker,
    \\    count: usize = 0,
    \\    fn run(raw: *anyopaque) void {
    \\        const execution: *Execution = @ptrCast(@alignCast(raw));
    \\        execution.count += 1;
    \\        execution.worker.run();
    \\    }
    \\};
    \\const Executor = struct {
    \\    run_fn: *const fn (*anyopaque, *const fn (*anyopaque) void) void,
    \\    fn run(self: Executor, context: *anyopaque, callback: *const fn (*anyopaque) void) void {
    \\        self.run_fn(context, callback);
    \\    }
    \\};
    \\fn execute(worker: Worker, executor: Executor) void {
    \\    var execution: Execution = .{ .worker = worker };
    \\    executor.run(&execution, Execution.run);
    \\}
    \\fn callback(context: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(context.?));
    \\    state.calls += 1;
    \\}
;

test "nested callback pair transports an exact source executor and context together" {
    try expectProof(nested_worker_fixture ++
        \\fn dispatch(context: *anyopaque, run: *const fn (*anyopaque) void) void { run(context); }
        \\test "registration" {
        \\    var state: State = .{};
        \\    execute(.{ .context = &state, .run_fn = callback }, .{ .run_fn = dispatch });
        \\}
    , true);
}

test "nested callback pair rejects executor mutation before dispatch" {
    try expectProof(nested_worker_fixture ++
        \\fn dispatch(context: *anyopaque, run: *const fn (*anyopaque) void) void {
        \\    const execution: *Execution = @ptrCast(@alignCast(context));
        \\    execution.worker.context = null;
        \\    run(context);
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    execute(.{ .context = &state, .run_fn = callback }, .{ .run_fn = dispatch });
        \\}
    , false);
}

test "nested callback pair rejects an opaque executor context escape" {
    try expectProof(nested_worker_fixture ++
        \\extern fn mutateUnknown(*anyopaque) void;
        \\fn dispatch(context: *anyopaque, run: *const fn (*anyopaque) void) void {
        \\    mutateUnknown(context);
        \\    run(context);
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    execute(.{ .context = &state, .run_fn = callback }, .{ .run_fn = dispatch });
        \\}
    , false);
}

const nested_thread_fixture =
    \\const std = @import("std");
    \\const State = struct { calls: usize = 0 };
    \\const JobContext = struct {
    \\    trace_context: ?*anyopaque,
    \\    user_context: ?*anyopaque = null,
    \\    trace_hook: ?*const fn (?*anyopaque) void,
    \\    fn emit(self: *const JobContext) void {
    \\        if (self.trace_hook) |hook| hook(self.trace_context);
    \\    }
    \\};
    \\const WorkerSpec = struct { context: JobContext };
    \\const ThreadContext = struct {
    \\    context: JobContext,
    \\    fn run(self: *ThreadContext) void { self.context.emit(); }
    \\};
    \\fn callback(raw: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(raw.?));
    \\    state.calls += 1;
    \\}
    \\fn dispatch(context: JobContext) !void {
    \\    const spec: WorkerSpec = .{ .context = context };
    \\    var contexts: [2]ThreadContext = undefined;
    \\    for (0..contexts.len) |index| {
    \\        contexts[index] = .{ .context = spec.context };
    \\        const thread = try std.Thread.spawn(.{}, ThreadContext.run, .{&contexts[index]});
    \\        thread.join();
    \\    }
    \\}
;

test "nested callback pair transports copied indexed contexts through authenticated thread spawn" {
    try expectProof(nested_thread_fixture ++
        \\test "registration" {
        \\    var state: State = .{};
        \\    try dispatch(.{ .trace_context = &state, .trace_hook = callback });
        \\}
    , true);
}

test "nested callback pair rejects an unaligned original thread context payload" {
    try expectProof(nested_thread_fixture ++
        \\test "registration" {
        \\    var state: State align(1) = .{};
        \\    try dispatch(.{ .trace_context = &state, .trace_hook = callback });
        \\}
    , false);
}

test "nested callback pair rejects a mismatched original thread context payload" {
    try expectProof(nested_thread_fixture ++
        \\test "registration" {
        \\    var bytes: [64]u8 = undefined;
        \\    try dispatch(.{ .trace_context = @ptrCast(&bytes), .trace_hook = callback });
        \\}
    , false);
}

const pointer_graph_prefix =
    \\const State = struct { calls: usize = 0 };
    \\const Older = struct { bytes: [1]u8 = .{0} };
    \\const Worker = struct {
    \\    context: ?*anyopaque,
    \\    invoke: *const fn (?*anyopaque) void,
    \\    fn run(self: Worker) void { self.invoke(self.context); }
    \\};
    \\const Execution = struct {
    \\    owner: *Older,
    \\    worker: Worker,
    \\    fn run(raw: *anyopaque) void {
    \\        const execution: *Execution = @ptrCast(@alignCast(raw));
;

const pointer_graph_suffix =
    \\        execution.worker.run();
    \\    }
    \\};
    \\fn execute(worker: Worker, owner: *Older) void {
    \\    var execution: Execution = .{ .owner = owner, .worker = worker };
    \\    Execution.run(&execution);
    \\}
    \\fn callback(context: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(context.?));
    \\    state.calls += 1;
    \\}
    \\test "registration" {
    \\    var state: State = .{};
    \\    var older: Older = .{};
    \\    execute(.{ .context = &state, .invoke = callback }, &older);
    \\}
;

test "physical callback carrier separates older pointer-backed writes from inline pair slots" {
    try expectProof(pointer_graph_prefix ++
        \\        execution.owner.bytes[0] = 1;
    ++ pointer_graph_suffix, true);
}

test "physical callback carrier refuses pointer-header rebinding to its own address" {
    try expectProof(pointer_graph_prefix ++
        \\        execution.owner = @ptrCast(execution);
        \\        execution.owner.bytes[0] = 1;
    ++ pointer_graph_suffix, false);
}

test "physical callback carrier refuses a mutable executor initializer as its current function value" {
    try expectProof(nested_worker_fixture ++
        \\extern fn mutateUnknown(*anyopaque, *const fn (*anyopaque) void) void;
        \\fn dispatch(context: *anyopaque, run: *const fn (*anyopaque) void) void { run(context); }
        \\test "registration" {
        \\    var state: State = .{};
        \\    var executor: Executor = .{ .run_fn = dispatch };
        \\    executor.run_fn = mutateUnknown;
        \\    execute(.{ .context = &state, .run_fn = callback }, executor);
        \\}
    , false);
}

test "physical callback carrier refuses an index rebound between initialization and dispatch" {
    try expectProof(
        \\const State = struct { calls: usize = 0 };
        \\const Pair = struct {
        \\    context: ?*anyopaque,
        \\    invoke: *const fn (?*anyopaque) void,
        \\    fn run(self: *Pair) void { self.invoke(self.context); }
        \\};
        \\fn callback(context: ?*anyopaque) void {
        \\    const state: *State = @ptrCast(@alignCast(context.?));
        \\    state.calls += 1;
        \\}
        \\fn dispatch(pair: Pair) void {
        \\    var pairs: [2]Pair = undefined;
        \\    var index: usize = 0;
        \\    pairs[index] = pair;
        \\    index = 1;
        \\    pairs[index].run();
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    dispatch(.{ .context = &state, .invoke = callback });
        \\}
    , false);
}

const sibling_method_prefix =
    \\extern fn mutateAll() void;
    \\const State = struct { calls: usize = 0 };
    \\const Older = struct {
    \\    bytes: [1]u8 = .{0},
    \\    fn mutate(self: *Older) void {
;

const sibling_method_suffix =
    \\    }
    \\};
    \\const Worker = struct {
    \\    context: ?*anyopaque,
    \\    invoke: *const fn (?*anyopaque) void,
    \\    fn run(self: Worker) void { self.invoke(self.context); }
    \\};
    \\const Execution = struct {
    \\    owner: *Older,
    \\    worker: Worker,
    \\    fn run(raw: *anyopaque) void {
    \\        const execution: *Execution = @ptrCast(@alignCast(raw));
    \\        execution.owner.mutate();
    \\        execution.worker.run();
    \\    }
    \\};
    \\fn execute(worker: Worker, owner: *Older) void {
    \\    var execution: Execution = .{ .owner = owner, .worker = worker };
    \\    Execution.run(&execution);
    \\}
    \\fn callback(context: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(context.?));
    \\    state.calls += 1;
    \\}
    \\test "registration" {
    \\    var state: State = .{};
    \\    var older: Older = .{};
    \\    execute(.{ .context = &state, .invoke = callback }, &older);
    \\}
;

test "physical callback carrier accepts a sibling method with a complete rooted footprint" {
    try expectProof(sibling_method_prefix ++
        \\        self.bytes[0] = 1;
    ++ sibling_method_suffix, true);
}

test "physical callback carrier refuses a sourced sibling method with opaque global effects" {
    try expectProof(sibling_method_prefix ++
        \\        _ = self;
        \\        mutateAll();
    ++ sibling_method_suffix, false);
}

test "physical callback carrier refuses a sourced sibling method with unbounded memory asm" {
    try expectProof(sibling_method_prefix ++
        \\        asm volatile ("" : : [ptr] "r" (self) : .{ .memory = true });
    ++ sibling_method_suffix, false);
}

test "nested callback pair transports heap indexed contexts and separate function metadata" {
    try expectProof(
        \\const std = @import("std");
        \\const State = struct { calls: usize = 0 };
        \\const JobContext = struct {
        \\    trace_context: ?*anyopaque,
        \\    trace_hook: ?*const fn (?*anyopaque) void,
        \\    fn emit(self: *const JobContext) void {
        \\        if (self.trace_hook) |hook| hook(self.trace_context);
        \\    }
        \\};
        \\const WorkerSpec = struct {
        \\    worker: ?*const fn () void = null,
        \\    context_worker: ?*const fn () void = null,
        \\    job_context: JobContext,
        \\};
        \\const ThreadContext = struct {
        \\    worker: ?*const fn () void,
        \\    context_worker: ?*const fn () void,
        \\    job_context: JobContext,
        \\    fn run(self: *ThreadContext) void { self.job_context.emit(); }
        \\};
        \\fn callback(raw: ?*anyopaque) void {
        \\    const state: *State = @ptrCast(@alignCast(raw.?));
        \\    state.calls += 1;
        \\}
        \\fn dispatch(job_context: JobContext) !void {
        \\    const worker_spec: WorkerSpec = .{ .job_context = job_context };
        \\    const contexts = std.testing.allocator.alloc(ThreadContext, 2) catch |err| {
        \\        std.debug.print("{s}", .{@errorName(err)});
        \\        return err;
        \\    };
        \\    defer std.testing.allocator.free(contexts);
        \\    for (0..contexts.len) |thread_index| {
        \\        contexts[thread_index] = .{
        \\            .worker = worker_spec.worker,
        \\            .context_worker = worker_spec.context_worker,
        \\            .job_context = worker_spec.job_context,
        \\        };
        \\        if (thread_index == contexts.len - 1) {
        \\            ThreadContext.run(&contexts[thread_index]);
        \\        } else {
        \\            const thread = try std.Thread.spawn(.{}, ThreadContext.run, .{&contexts[thread_index]});
        \\            thread.join();
        \\        }
        \\    }
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    try dispatch(.{ .trace_context = &state, .trace_hook = callback });
        \\}
    , true);
}

test "nested callback pair rejects a project allocator spelling over borrowed contexts" {
    try expectProof(
        \\const State = struct { calls: usize = 0 };
        \\const Context = struct {
        \\    payload: ?*anyopaque,
        \\    invoke: *const fn (?*anyopaque) void,
        \\    fn run(self: *Context) void { self.invoke(self.payload); }
        \\};
        \\const Allocator = struct {
        \\    borrowed: *[1]Context,
        \\    fn alloc(self: *Allocator, comptime T: type, count: usize) ![]T {
        \\        _ = count;
        \\        return self.borrowed;
        \\    }
        \\};
        \\fn callback(raw: ?*anyopaque) void {
        \\    const state: *State = @ptrCast(@alignCast(raw.?));
        \\    state.calls += 1;
        \\}
        \\fn dispatch(pair: Context, borrowed: *[1]Context) void {
        \\    var allocator: Allocator = .{ .borrowed = borrowed };
        \\    const contexts = allocator.alloc(Context, 1) catch return;
        \\    contexts[0] = pair;
        \\    Context.run(&contexts[0]);
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    var borrowed: [1]Context = undefined;
        \\    dispatch(.{ .payload = &state, .invoke = callback }, &borrowed);
        \\}
    , false);
}

const default_inline_cleanup_prefix =
    \\const State = struct { calls: usize = 0 };
    \\const Admission = struct {
    \\    session: ?*State = null,
    \\    fn deinit(self: *Admission) anyerror!void {
;
const default_inline_cleanup_suffix =
    \\        const session = self.session orelse return;
    \\        session.calls += 1;
    \\    }
    \\};
    \\const Pair = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque) void };
    \\const Cleanup = struct {
    \\    admission: Admission = .{},
    \\    scene: ?Pair = null,
    \\    operation_error: ?anyerror = null,
    \\    fn fail(self: *Cleanup, cause: anyerror) void {
    \\        self.operation_error = cause;
    \\        self.deinit() catch {};
    \\    }
    \\    fn deinit(self: *Cleanup) anyerror!void {
    \\        try self.admission.deinit();
    \\        if (self.scene) |scene| scene.invoke(scene.context);
    \\    }
    \\};
    \\fn callback(raw: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(raw.?));
    \\    state.calls += 1;
    \\}
    \\test "registration" {
    \\    var state: State = .{};
    \\    var cleanup: Cleanup = .{};
    \\    cleanup.scene = .{ .context = &state, .invoke = callback };
    \\    cleanup.fail(error.Cancelled);
    \\}
;

test "stored cleanup pair proves a source default null inline receiver before callback" {
    try expectProof(default_inline_cleanup_prefix ++ default_inline_cleanup_suffix, true);
}

test "stored cleanup pair refuses an opaque effect before the null receiver guard" {
    try expectProof("extern fn mutateUnknown() void;\n" ++ default_inline_cleanup_prefix ++
        \\        mutateUnknown();
    ++ default_inline_cleanup_suffix, false);
}

const io_sibling_fixture =
    \\const std = @import("std");
    \\const State = struct { calls: usize = 0 };
    \\const Older = struct {
    \\    mutex: std.Io.Mutex = .init,
    \\    failure: ?anyerror = null,
    \\    fn record(self: *Older, io: std.Io) void {
    \\        self.mutex.lockUncancelable(io);
    \\        defer self.mutex.unlock(io);
    \\        self.failure = error.Cancelled;
    \\    }
    \\};
    \\const Worker = struct {
    \\    context: ?*anyopaque,
    \\    invoke: *const fn (?*anyopaque) void,
    \\    fn run(self: Worker) void { self.invoke(self.context); }
    \\};
    \\const Execution = struct {
    \\    older: *Older,
    \\    io: std.Io,
    \\    worker: Worker,
    \\    fn run(raw: *anyopaque) void {
    \\        const execution: *Execution = @ptrCast(@alignCast(raw));
    \\        execution.older.record(execution.io);
    \\        execution.worker.run();
    \\    }
    \\};
    \\fn execute(worker: Worker, older: *Older, io: std.Io) void {
    \\    var execution: Execution = .{ .worker = worker, .older = older, .io = io };
    \\    Execution.run(&execution);
    \\}
    \\fn callback(raw: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(raw.?));
    \\    state.calls += 1;
    \\}
;

test "physical callback carrier proves a source selected IO mutex footprint" {
    try expectProof(io_sibling_fixture ++
        \\test "registration" {
        \\    var state: State = .{};
        \\    var older: Older = .{};
        \\    execute(.{ .context = &state, .invoke = callback }, &older, std.testing.io);
        \\}
    , true);
}

test "physical callback carrier refuses a dynamically rebound IO provider" {
    try expectProof(io_sibling_fixture ++
        \\fn mutateCarrier(userdata: ?*anyopaque, ptr: *const u32, count: u32) void {
        \\    _ = ptr;
        \\    _ = count;
        \\    const execution: *Execution = @ptrCast(@alignCast(userdata.?));
        \\    execution.worker.context = null;
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    var older: Older = .{};
        \\    var io = std.testing.io;
        \\    var vtable = io.vtable.*;
        \\    vtable.futexWake = mutateCarrier;
        \\    io.vtable = &vtable;
        \\    execute(.{ .context = &state, .invoke = callback }, &older, io);
        \\}
    , false);
}

const captured_dispatch_fixture =
    \\const State = struct { calls: usize = 0 };
    \\const JobContext = struct {
    \\    payload: ?*anyopaque,
    \\    invoke: *const fn (?*anyopaque) void,
    \\    fn emit(self: *const JobContext) void { self.invoke(self.payload); }
    \\};
    \\fn worker(context: *const JobContext) void { context.emit(); }
    \\const ThreadContext = struct {
    \\    job_context: JobContext,
    \\    worker: ?*const fn (*const JobContext) void,
    \\    fn run(context: *ThreadContext) void {
    \\        if (context.worker) |selected| selected(&context.job_context);
    \\    }
    \\};
    \\fn callback(raw: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(raw.?));
    \\    state.calls += 1;
    \\}
    \\fn dispatch(context: JobContext) void {
    \\    var execution: ThreadContext = .{ .job_context = context, .worker = worker };
    \\    ThreadContext.run(&execution);
    \\}
;

test "nested callback pair follows a source selected optional dispatcher capture" {
    try expectProof(captured_dispatch_fixture ++
        \\test "registration" {
        \\    var state: State = .{};
        \\    dispatch(.{ .payload = &state, .invoke = callback });
        \\}
    , true);
}

const captured_dispatch_statement = "        if (context.worker) |selected| selected(&context.job_context);";
const captured_dispatch_offset = std.mem.indexOf(u8, captured_dispatch_fixture, captured_dispatch_statement).?;
const captured_dispatch_before = captured_dispatch_fixture[0..captured_dispatch_offset];
const captured_dispatch_after = captured_dispatch_fixture[captured_dispatch_offset + captured_dispatch_statement.len ..];
const captured_dispatch_registration =
    \\test "registration" {
    \\    var state: State = .{};
    \\    dispatch(.{ .payload = &state, .invoke = callback });
    \\}
;

test "nested callback pair refuses a mutated optional dispatcher capture" {
    try expectProof("extern fn mutate(context: *const JobContext) void;\n" ++
        captured_dispatch_before ++
        \\        if (context.worker) |selected| {
        \\            var current = selected;
        \\            current = mutate;
        \\            current(&context.job_context);
        \\        }
    ++ captured_dispatch_after ++ captured_dispatch_registration, false);
}

test "nested callback pair refuses a pointer optional dispatcher capture" {
    try expectProof("extern fn mutate(context: *const JobContext) void;\n" ++
        captured_dispatch_before ++
        \\        if (context.worker) |*selected| {
        \\            selected.* = mutate;
        \\            selected.*(&context.job_context);
        \\        }
    ++ captured_dispatch_after ++ captured_dispatch_registration, false);
}

test "nested callback pair refuses an unrelated optional dispatcher capture" {
    try expectProof("extern fn mutate(context: *const JobContext) void;\n" ++
        captured_dispatch_before ++
        \\        const unrelated: ?*const fn (*const JobContext) void = mutate;
        \\        if (unrelated) |selected| selected(&context.job_context);
    ++ captured_dispatch_after ++ captured_dispatch_registration, false);
}

test "physical callback carrier refuses an opaque effect beside the selected IO mutex" {
    const marker = "        self.mutex.lockUncancelable(io);";
    const offset = comptime std.mem.indexOf(u8, io_sibling_fixture, marker).?;
    try expectProof("extern fn mutateUnknown() void;\n" ++ io_sibling_fixture[0..offset] ++
        \\        mutateUnknown();
    ++ io_sibling_fixture[offset..] ++
        \\test "registration" {
        \\    var state: State = .{};
        \\    var older: Older = .{};
        \\    execute(.{ .context = &state, .invoke = callback }, &older, std.testing.io);
        \\}
    , false);
}

test "nested callback pair selects optional dispatchers from initialized indexed cells" {
    try expectProof(
        \\const std = @import("std");
        \\const State = struct { calls: usize = 0 };
        \\const JobContext = struct {
        \\    payload: ?*anyopaque,
        \\    invoke: *const fn (?*anyopaque) void,
        \\    fn emit(self: *const JobContext) void { self.invoke(self.payload); }
        \\};
        \\fn worker(context: *const JobContext) void { context.emit(); }
        \\const WorkerSpec = struct {
        \\    job_context: JobContext,
        \\    context_worker: ?*const fn (*const JobContext) void,
        \\};
        \\const ThreadContext = struct {
        \\    job_context: JobContext,
        \\    context_worker: ?*const fn (*const JobContext) void,
        \\    fn run(context: *ThreadContext) void {
        \\        if (context.context_worker) |selected| selected(&context.job_context);
        \\    }
        \\};
        \\fn callback(raw: ?*anyopaque) void {
        \\    const state: *State = @ptrCast(@alignCast(raw.?));
        \\    state.calls += 1;
        \\}
        \\fn dispatch(job_context: JobContext) !void {
        \\    const worker_spec: WorkerSpec = .{ .job_context = job_context, .context_worker = worker };
        \\    const contexts = try std.testing.allocator.alloc(ThreadContext, 2);
        \\    defer std.testing.allocator.free(contexts);
        \\    for (0..contexts.len) |index| {
        \\        contexts[index] = .{
        \\            .job_context = worker_spec.job_context,
        \\            .context_worker = worker_spec.context_worker,
        \\        };
        \\        if (index == contexts.len - 1) {
        \\            ThreadContext.run(&contexts[index]);
        \\        } else {
        \\            const thread = try std.Thread.spawn(.{}, ThreadContext.run, .{&contexts[index]});
        \\            thread.join();
        \\        }
        \\    }
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    try dispatch(.{ .payload = &state, .invoke = callback });
        \\}
    , true);
}

test "physical callback carrier refuses an IO provider reaching a published carrier global" {
    const marker = "        execution.older.record(execution.io);";
    const offset = comptime std.mem.indexOf(u8, io_sibling_fixture, marker).?;
    try expectProof(io_sibling_fixture[0..offset] ++
        \\        published = execution;
    ++ io_sibling_fixture[offset..] ++
        \\var published: ?*Execution = null;
        \\fn mutateCarrier(userdata: ?*anyopaque, ptr: *const u32, count: u32) void {
        \\    _ = userdata;
        \\    _ = count;
        \\    if (published) |execution| execution.worker.context = null;
        \\    @constCast(ptr).* = 0;
        \\}
        \\test "registration" {
        \\    var state: State = .{};
        \\    var older: Older = .{ .mutex = .{ .state = .init(.contended) } };
        \\    var io = std.testing.io;
        \\    var vtable = io.vtable.*;
        \\    vtable.futexWaitUncancelable = mutateCarrier;
        \\    vtable.futexWake = mutateCarrier;
        \\    io.vtable = &vtable;
        \\    execute(.{ .context = &state, .invoke = callback }, &older, io);
        \\}
    , false);
}

const io_priority_before = io_sibling_fixture[0..std.mem.indexOf(u8, io_sibling_fixture, "    mutex: std.Io.Mutex = .init,").?];
const io_priority_after = io_sibling_fixture[std.mem.indexOf(u8, io_sibling_fixture, "const Worker = struct").?..];
const io_priority_fields =
    \\    const Kind = enum(u8) { duplicate, worker };
    \\    const Failure = struct { index: usize, kind: Kind, failure_error: anyerror };
    \\    mutex: std.Io.Mutex = .init,
    \\    first_failure: ?Failure = null,
;
const io_priority_method_before =
    \\    fn record(self: *Older, io: std.Io) void {
    \\        self.mutex.lockUncancelable(io);
    \\        defer self.mutex.unlock(io);
;
const io_priority_method_after =
    \\        self.first_failure = .{ .index = 0, .kind = .worker, .failure_error = error.Cancelled };
    \\    }
    \\};
;
const io_priority_registration =
    \\test "registration" {
    \\    var state: State = .{};
    \\    var older: Older = .{};
    \\    execute(.{ .context = &state, .invoke = callback }, &older, std.testing.io);
    \\}
;

test "physical callback carrier proves an immutable enum integer alias beside IO mutex" {
    try expectProof(io_priority_before ++ io_priority_fields ++ io_priority_method_before ++
        \\        if (self.first_failure) |failure| {
        \\            const old_priority = @intFromEnum(failure.kind);
        \\            const new_priority = @intFromEnum(Kind.worker);
        \\            if (old_priority <= new_priority) return;
        \\        }
    ++ io_priority_method_after ++ io_priority_after ++ io_priority_registration, true);
}

test "physical callback carrier refuses a scalar named pointer alias beside IO mutex" {
    try expectProof(io_priority_before ++ io_priority_fields ++ io_priority_method_before ++
        \\        const old_priority = io.userdata;
        \\        if (old_priority != null) return;
    ++ io_priority_method_after ++ io_priority_after ++ io_priority_registration, false);
}

test "physical callback carrier refuses an unknown integer alias effect beside IO mutex" {
    try expectProof("extern fn unknownPriority() u8;\n" ++ io_priority_before ++ io_priority_fields ++ io_priority_method_before ++
        \\        const old_priority = unknownPriority();
        \\        if (old_priority == 0) return;
    ++ io_priority_method_after ++ io_priority_after ++ io_priority_registration, false);
}

const copied_executor_before =
    \\const State = struct { calls: usize = 0 };
    \\const Worker = struct {
    \\    context: ?*anyopaque,
    \\    invoke: *const fn (?*anyopaque) void,
    \\    fn run(self: Worker) void { self.invoke(self.context); }
    \\};
    \\const Execution = struct {
    \\    worker: Worker,
    \\    fn run(raw: *anyopaque) void {
    \\        const execution: *Execution = @ptrCast(@alignCast(raw));
    \\        execution.worker.run();
    \\    }
    \\};
    \\const Duplicate = struct {
    \\    run_context: *anyopaque,
    \\    run_job: *const fn (*anyopaque) void,
    \\    ready: *u32,
    \\    fn run(self: *Duplicate) void {
    \\        self.ready.* += 1;
    \\        self.run_job(self.run_context);
    \\    }
    \\};
    \\fn callback(raw: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(raw.?));
    \\    state.calls += 1;
    \\}
    \\fn duplicate(run_context: *anyopaque, run_job: *const fn (*anyopaque) void) void {
    \\    var ready: u32 = 0;
    \\    var first: Duplicate = .{ .run_context = run_context, .run_job = run_job, .ready = &ready };
    \\    var second = first;
;
const copied_executor_after =
    \\    Duplicate.run(&first);
    \\    Duplicate.run(&second);
    \\}
    \\fn execute(worker: Worker) void {
    \\    var execution: Execution = .{ .worker = worker };
    \\    duplicate(&execution, Execution.run);
    \\}
    \\test "registration" {
    \\    var state: State = .{};
    \\    execute(.{ .context = &state, .invoke = callback });
    \\}
;

test "physical callback carrier preserves an immutable executor copy before closed publication" {
    try expectProof(copied_executor_before ++ copied_executor_after, true);
}

test "physical callback carrier refuses a copied executor header rebind" {
    try expectProof(copied_executor_before ++
        \\    second.run_context = &ready;
    ++ copied_executor_after, false);
}

test "physical callback carrier refuses an unknown mutation of an executor copy" {
    try expectProof("extern fn mutateUnknown(*Duplicate) void;\n" ++ copied_executor_before ++
        \\    mutateUnknown(&second);
    ++ copied_executor_after, false);
}

const atomic_executor_prefix =
    \\const std = @import("std");
    \\const State = struct { calls: usize = 0 };
    \\const Worker = struct {
    \\    context: ?*anyopaque,
    \\    invoke: *const fn (?*anyopaque) void,
    \\    fn run(self: Worker) void { self.invoke(self.context); }
    \\};
    \\const Execution = struct {
    \\    worker: Worker,
    \\    fn run(raw: *anyopaque) void {
    \\        const execution: *Execution = @ptrCast(@alignCast(raw));
    \\        execution.worker.run();
    \\    }
    \\};
    \\fn callback(raw: ?*anyopaque) void {
    \\    const state: *State = @ptrCast(@alignCast(raw.?));
    \\    state.calls += 1;
    \\}
;

const atomic_executor_before =
    \\const Duplicate = struct {
    \\    run_context: *anyopaque,
    \\    run_job: *const fn (*anyopaque) void,
    \\    ready: *Ready,
    \\    fn run(self: *Duplicate) void {
    \\        _ = self.ready.fetchAdd(1, .release);
    \\        self.run_job(self.run_context);
    \\    }
    \\};
    \\fn duplicate(run_context: *anyopaque, run_job: *const fn (*anyopaque) void) !void {
    \\    var ready: Ready = .init(0);
    \\    var first: Duplicate = .{ .run_context = run_context, .run_job = run_job, .ready = &ready };
    \\    var second = first;
;

const atomic_executor_after =
    \\    const first_thread = try std.Thread.spawn(.{}, Duplicate.run, .{&first});
    \\    const second_thread = std.Thread.spawn(.{}, Duplicate.run, .{&second}) catch |err| {
    \\        first_thread.join();
    \\        return err;
    \\    };
    \\    first_thread.join();
    \\    second_thread.join();
    \\}
    \\fn execute(worker: Worker) !void {
    \\    var execution: Execution = .{ .worker = worker };
    \\    try duplicate(&execution, Execution.run);
    \\}
    \\test "registration" {
    \\    var state: State = .{};
    \\    try execute(.{ .context = &state, .invoke = callback });
    \\}
;

test "physical callback carrier separates an authenticated atomic receiver in copied thread executors" {
    try expectProof(atomic_executor_prefix ++ "\nconst Ready = std.atomic.Value(u32);\n" ++
        atomic_executor_before ++ atomic_executor_after, true);
}

test "physical callback carrier refuses an atomic receiver header rebind in copied thread executors" {
    try expectProof(atomic_executor_prefix ++ "\nconst Ready = std.atomic.Value(u32);\n" ++
        atomic_executor_before ++
        \\    second.ready = @ptrCast(@alignCast(run_context));
    ++ atomic_executor_after, false);
}

test "physical callback carrier refuses an opaque effect behind an atomic named receiver" {
    try expectProof(atomic_executor_prefix ++
        \\extern fn mutateUnknown() void;
        \\const Ready = struct {
        \\    raw: u32,
        \\    fn init(value: u32) Ready { return .{ .raw = value }; }
        \\    fn fetchAdd(self: *Ready, operand: u32, comptime order: std.builtin.AtomicOrder) u32 {
        \\        _ = order;
        \\        mutateUnknown();
        \\        self.raw += operand;
        \\        return self.raw;
        \\    }
        \\};
    ++ atomic_executor_before ++ atomic_executor_after, false);
}

const census_factory_source =
    \\const Sink = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque, *u32) void };
    \\const Captured = struct {
    \\    value: u32 = 0,
    \\    sink: Sink = undefined,
    \\    fn bind(self: *Captured) *const Sink {
    \\        self.sink = .{ .context = self, .invoke = callback };
    \\        return &self.sink;
    \\    }
    \\    fn callback(context: ?*anyopaque, value: *u32) void { _ = context; _ = value; }
    \\};
    \\const Verifier = struct {
    \\    sink: ?*const Sink = null,
    \\    fn verify(self: *Verifier) void {
    \\        var value: u32 = 0;
    \\        if (self.sink) |sink| sink.invoke(sink.context, &value);
    \\    }
    \\};
;

test "callback dispatch census retains each closed receiver and actual frame" {
    try expectCensus(census_factory_source ++
        \\fn first() void {
        \\    var captured: Captured = .{};
        \\    var verifier: Verifier = .{ .sink = captured.bind() };
        \\    verifier.verify();
        \\}
        \\fn second() void {
        \\    var captured: Captured = .{};
        \\    var verifier: Verifier = .{ .sink = captured.bind() };
        \\    verifier.verify();
        \\}
    , 2);
}

test "callback dispatch census exposes same-object pairing without storage clearance" {
    try expectCensus(census_factory_source ++
        \\fn same() void {
        \\    var captured: Captured = .{};
        \\    const sink = captured.bind();
        \\    sink.invoke(sink.context, &captured.value);
        \\}
    , 1);
}

test "callback dispatch census does not expose a partial escaped registration set" {
    try expectCensus(census_factory_source ++
        \\fn first() void {
        \\    var captured: Captured = .{};
        \\    var verifier: Verifier = .{ .sink = captured.bind() };
        \\    verifier.verify();
        \\}
        \\pub fn escape(captured: *Captured) *const Sink { return captured.bind(); }
    , null);
}

test "callback dispatch census abstains on loop-generated actuals" {
    try expectCensus(census_factory_source ++
        \\fn selected() void {
        \\    var captured: Captured = .{};
        \\    var value: u32 = 0;
        \\    const sink = captured.bind();
        \\    inline for (.{ false, true }) |shared| {
        \\        sink.invoke(sink.context, if (shared) &captured.value else &value);
        \\    }
        \\}
    , null);
}

test "callback dispatch census is not a null or alignment certificate" {
    try expectCensus(
        \\const Sink = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque, *u32) void };
        \\fn callback(context: ?*anyopaque, value: *u32) void { _ = context; _ = value; }
        \\fn dispatch(sink: Sink) void { var value: u32 = 0; sink.invoke(sink.context, &value); }
        \\fn selected() void { dispatch(.{ .context = null, .invoke = callback }); }
    , 1);
}

fn expectCensus(source: [:0]const u8, expected_count: ?usize) !void {
    const allocator = std.testing.allocator;
    var context: engine.TypeContext = undefined;
    try context.init(allocator, std.testing.io);
    defer context.deinit();
    var resolver: TypeResolver = undefined;
    try resolver.init(&context, allocator, "/zbc-callback-census-test.zig", source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    const cache = try allocator.create(FileCache);
    defer allocator.destroy(cache);
    cache.* = FileCache.init(allocator, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .fn_decl) continue;
        const declaration: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration).?;
        const name = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name), "callback")) continue;
        var result = try closedDispatchCensus(cache, declaration, 0, allocator);
        defer result.deinit(allocator);
        const count = expected_count orelse {
            try std.testing.expect(result == .incomplete);
            return;
        };
        try std.testing.expect(result == .complete);
        try std.testing.expectEqual(count, result.complete.len);
        for (result.complete) |dispatch| {
            try std.testing.expect(dispatch.callback.handle.eql(resolver.handle));
            try std.testing.expectEqual(proto.ast.fn_token, dispatch.callback.fn_token);
            try std.testing.expectEqual(@as(usize, 2), dispatch.arguments.len);
            try std.testing.expect(dispatch.invocation.frame.handle.eql(resolver.handle));
            try std.testing.expect(dispatch.context.frame.handle.eql(resolver.handle));
            try std.testing.expect(dispatch.edges.len != 0);
            for (dispatch.edges) |edge| {
                try std.testing.expect(edge.callee.handle.eql(resolver.handle));
                try std.testing.expect(edge.actuals.len != 0);
            }
        }
        return;
    }
    return error.MissingCallbackDeclaration;
}

test "callback dispatch census refuses sibling addresses sent to unknown callees" {
    try expectCensus(census_factory_source ++
        \\extern fn publish(value: *u32) void;
        \\fn selected() void {
        \\    var captured: Captured = .{};
        \\    const sink = captured.bind();
        \\    publish(&captured.value);
        \\    var value: u32 = 0;
        \\    sink.invoke(sink.context, &value);
        \\}
    , null);
}

test "callback dispatch census refuses a rebound stored context" {
    try expectCensus(census_factory_source ++
        \\fn selected() void {
        \\    var captured: Captured = .{};
        \\    const sink = captured.bind();
        \\    captured.sink.context = null;
        \\    sink.invoke(sink.context, &captured.value);
        \\}
    , null);
}

test "callback dispatch census refuses raw factory-result header publication" {
    try expectCensus(census_factory_source ++
        \\extern fn publish(slot: *const *const Sink) void;
        \\fn selected() void {
        \\    var captured: Captured = .{};
        \\    const sink = captured.bind();
        \\    publish(&sink);
        \\    sink.invoke(sink.context, &captured.value);
        \\}
    , null);
}

test "callback dispatch census refuses a rebound factory-result header" {
    try expectCensus(census_factory_source ++
        \\fn selected() void {
        \\    var captured: Captured = .{};
        \\    var sink = captured.bind();
        \\    sink = captured.bind();
        \\    sink.invoke(sink.context, &captured.value);
        \\}
    , null);
}

test "callback dispatch census separates an authenticated inline list receiver from its owner" {
    try expectCensus(
        \\const std = @import("std");
        \\const Sink = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque, *u32) void };
        \\const Captured = struct {
        \\    list: std.ArrayList(u32) = .empty,
        \\    sink: Sink = undefined,
        \\    fn bind(self: *Captured) *const Sink {
        \\        self.sink = .{ .context = self, .invoke = callback };
        \\        return &self.sink;
        \\    }
        \\    fn callback(context: ?*anyopaque, value: *u32) void { _ = context; _ = value; }
        \\};
        \\fn selected(allocator: std.mem.Allocator) !void {
        \\    var captured: Captured = .{};
        \\    defer captured.list.deinit(allocator);
        \\    const sink = captured.bind();
        \\    try captured.list.append(allocator, 1);
        \\    var value: u32 = 0;
        \\    sink.invoke(sink.context, &value);
        \\}
    , 1);
}

test "callback dispatch census exposes inline header copies after registration without storage clearance" {
    try expectCensus(
        \\const std = @import("std");
        \\const Sink = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque, *u32) void };
        \\const Captured = struct {
        \\    list: std.ArrayList(u32) = .empty,
        \\    sink: Sink = undefined,
        \\    fn bind(self: *Captured) *const Sink {
        \\        self.sink = .{ .context = self, .invoke = callback };
        \\        return &self.sink;
        \\    }
        \\    fn callback(context: ?*anyopaque, value: *u32) void { _ = context; _ = value; }
        \\};
        \\fn selected(input: std.ArrayList(u32)) void {
        \\    var captured: Captured = .{};
        \\    const sink = captured.bind();
        \\    captured.list = input;
        \\    var value: u32 = 0;
        \\    sink.invoke(sink.context, &value);
        \\}
    , 1);
}

const census_projected_child_prefix =
    \\const Sink = struct { context: ?*anyopaque, invoke: *const fn (?*anyopaque, *u32) void };
    \\const Child = struct {
    \\    value: u32 = 0,
    \\    fn mutate(self: *Child) void {
;

const census_projected_child_suffix =
    \\    }
    \\};
    \\const Captured = struct {
    \\    child: Child = .{},
    \\    sink: Sink = undefined,
    \\    fn bind(self: *Captured) *const Sink {
    \\        self.sink = .{ .context = self, .invoke = callback };
    \\        return &self.sink;
    \\    }
    \\    fn callback(context: ?*anyopaque, value: *u32) void { _ = context; _ = value; }
    \\};
    \\fn selected() void {
    \\    var captured: Captured = .{};
    \\    const sink = captured.bind();
    \\    captured.child.mutate();
    \\    var value: u32 = 0;
    \\    sink.invoke(sink.context, &value);
    \\}
;

test "callback dispatch census refuses opaque inline child effects" {
    try expectCensus("extern fn mutateUnknown() void;\n" ++ census_projected_child_prefix ++
        \\        _ = self;
        \\        mutateUnknown();
    ++ census_projected_child_suffix, null);
}

test "callback dispatch census refuses inline child parent recovery" {
    try expectCensus(census_projected_child_prefix ++
        \\        const owner: *Captured = @fieldParentPtr("child", self);
        \\        owner.sink.context = null;
    ++ census_projected_child_suffix, null);
}
