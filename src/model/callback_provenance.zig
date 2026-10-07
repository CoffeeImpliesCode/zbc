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
    const pointer = tree.fullPtrType(type_node) orelse return false;
    if (pointer.ast.align_node.unwrap() != null) return false;
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
        .target_child = target_child,
        .parameter_index = parameter_index,
        .callback_owner = callback_owner,
    };
    defer proof.deinit();
    if (!try proof.ownerUsesClosed()) return false;
    var registrations: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .identifier, .field_access, .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        const reference = switch (try frame.functionReference(node)) {
            .function => |reference| reference,
            else => continue,
        };
        if (reference.tree != tree or reference.fn_token != proto.ast.fn_token) continue;
        const parent = proof.parent(node);
        var literal_buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullStructInit(&literal_buffer, parent) != null) {
            const field = proof.fieldName(node) orelse return false;
            if (!try proof.directRegistration(parent, field)) return false;
            registrations += 1;
            continue;
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
                if (!try proof.directRegistration(proof.parent(use), field)) return false;
                registrations += 1;
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
        registrations += 1;
    }
    return registrations != 0 and proof.invocations != 0;
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

const Pair = struct {
    origin: *Proof,
    initializer: Ast.Node.Index,
    table_field: ?[]const u8,
    callback_field: []const u8,
};

const Proof = struct {
    cache: *FileCache,
    parents: []const Ast.Node.Index,
    callback: Ast.TokenIndex,
    target_child: TypeResolver.ActualType,
    parameter_index: usize,
    callback_owner: ?TypeResolver.ActualType,
    frame: ?TypeResolver.ResolutionFrame = null,
    invocations: usize = 0,
    test_bindings: std.AutoHashMapUnmanaged(Ast.Node.Index, *@import("local_bindings.zig").LocalBindings) = .empty,

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
            .target_child = self.target_child,
            .parameter_index = self.parameter_index,
            .callback_owner = self.callback_owner,
        };
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
            // Only by-value transport preserves a pair without an alias proof.
            if (declaring.zls.?.typeTag(ty) != .@"struct") return false;
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
            if (reference.tree != tree or reference.fn_token != proto.ast.fn_token) continue;
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
                    if (reference.tree != tree or reference.fn_token != self.callback) return false;
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
                    .function => {
                        if (scope != null) return false;
                    },
                    else => {
                        const member = (try frame.resolveValueOfNode(parent_node)) orelse
                            return false;
                        if (!member.is_type_val) return false;
                        const member_type = (try self.cache.zls.?.normalizedType(member)) orelse
                            return false;
                        if (!TypeResolver.ActualType.eql(member_type, self.target_child)) return false;
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
        return try next_proof.ownerUsesClosedIn(declaration, depth + 1);
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
        const local = tree.fullVarDecl(self.parent(source)) orelse return false;
        if (tree.tokenTag(local.ast.mut_token) != .keyword_const) return false;
        const alias = (try self.bindingAtDeclaration(local.ast.mut_token + 1)) orelse return false;
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

    fn ordinaryPointerType(self: *const Proof, tree: *const Ast, node: Ast.Node.Index) bool {
        const pointer = tree.fullPtrType(node) orelse return false;
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
                    return self.ordinaryPointerType(
                        tree, parameter.type_expr orelse return false,
                    );
                }
                return false;
            }
            for (1..tree.nodes.len) |raw| {
                const local = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
                if (local.ast.mut_token + 1 != selected.name_token) continue;
                if (local.ast.type_node.unwrap()) |ty| return self.ordinaryPointerType(tree, ty);
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
        return self.ordinaryPointerType(callee_tree, result);
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
    cache.module_id = resolver.handle.module;
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

test "direct callback pair keeps stored cleanup registrations conservative" {
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
    , false);
}

test "direct callback pair keeps trace optional captures conservative" {
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
    , false);
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
