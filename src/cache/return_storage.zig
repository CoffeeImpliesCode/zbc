//! Parameter-relative returned STORAGE, not scalar value dependencies.
//! Query results and path bytes belong to the root cache until its deinit.

const std = @import("std");
const Ast = std.zig.Ast;
const FileCache = @import("file_cache.zig").FileCache;
const TypeResolver = @import("../type_resolver.zig").TypeResolver;
const fn_summary = @import("../model/fn_summary.zig");
const storage_alias = @import("storage_alias.zig");

const tokens = @import("../ast/tokens.zig");
const bindings_mod = @import("../model/local_bindings.zig");
const grow = @import("grow_analysis.zig");
const budget = @import("../budget.zig");
const Iterator = @import("type_engine").AstIterator;

pub const Error = error{ OutOfMemory, AnalysisBudgetExceeded };
pub const Projection = enum { cell_address, pointer_value, payload_value };
pub const Storage = enum { backing_storage, inline_storage, payload_storage };

/// A positive borrow, in the declaring function's formal coordinates.
/// Payload storage is the pointee carried IN a copied value, never its cell.
pub const Alternative = struct {
    owner: fn_summary.ParamPath,
    projection: Projection,
    storage: Storage,
    /// Field of an aggregate result carrying this borrow; "" is the result.
    result_path: []const u8 = "",
};

pub const ReturnedStorage = struct {
    /// False forbids any negative/safety conclusion, including an empty set.
    complete: bool = false,
    alternatives: []const Alternative = &.{},
};

const Key = struct {
    declaration: @import("file_cache.zig").DeclKey,
    context: TypeResolver.ActualTypeID,
};
const KeyContext = struct {
    pub fn hash(_: KeyContext, key: Key) u64 {
        var h = std.hash.Wyhash.init(0);
        const tree = @intFromPtr(key.declaration.tree);
        h.update(std.mem.asBytes(&tree));
        h.update(std.mem.asBytes(&key.declaration.module));
        h.update(std.mem.asBytes(&key.declaration.declaration));
        const context_hash = key.context.hash64();
        h.update(std.mem.asBytes(&context_hash));
        return h.final();
    }
    pub fn eql(_: KeyContext, a: Key, b: Key) bool {
        return a.declaration.tree == b.declaration.tree and
            a.declaration.module == b.declaration.module and
            a.declaration.declaration == b.declaration.declaration and
            a.context.eql(b.context);
    }
};

/// Only grow_state.owner's instance is used. Keys borrow the canonical
/// resolver arena, which outlives this state; ALL path bytes are owned here.
pub const State = struct {
    memo: ?std.heap.ArenaAllocator = null,
    sets: std.HashMapUnmanaged(Key, ReturnedStorage, KeyContext, 80) = .empty,
    active: std.HashMapUnmanaged(Key, void, KeyContext, 80) = .empty,
    tables: std.HashMapUnmanaged(Key, bool, KeyContext, 80) = .empty,

    pub fn deinit(self: *State, gpa: std.mem.Allocator) void {
        self.sets.deinit(gpa);
        self.active.deinit(gpa);
        self.tables.deinit(gpa);
        if (self.memo) |*arena| arena.deinit();
        self.memo = null;
    }

    fn allocator(self: *State, gpa: std.mem.Allocator) std.mem.Allocator {
        if (self.memo == null) self.memo = std.heap.ArenaAllocator.init(gpa);
        return self.memo.?.allocator();
    }
};

/// Canonical identity/declaration/type queries each cost one semantic edge:
/// those existing queries enforce their own internal bounds. All AST nodes,
/// edges, lexical-binding candidates and helper edges use the SAME caller
/// meter. Only a root entry with no meter seeds one allowance; helpers never do.
pub fn returnedStorageAt(
    cache: *FileCache,
    token: Ast.TokenIndex,
    context: storage_alias.QueryContext,
) Error!ReturnedStorage {
    var root_remaining: u32 = FileCache.actual_query_work_limit;
    const remaining = context.remaining orelse &root_remaining;
    const state = try grow.growStateAlloc(cache);
    const root = state.owner;
    const resolver = if (context.frame) |f| f.resolver else root.zls orelse return .{};
    var scratch = std.heap.ArenaAllocator.init(root.gpa);
    defer scratch.deinit();
    var query: Query = .{
        .root = root, .state = &root.return_storage_state,
        .resolver = resolver, .remaining = remaining,
        .scratch = scratch.allocator(), .entry_tree = cache.tree, .entry_token = token,
    };
    try query.charge();
    const actual = (try cache.actualCallSummaryAt(token, context.frame)) orelse return .{};
    return query.body(cache, actual, 0);
}

/// The mapped node belongs to the call's caller tree, NOT the callee tree.
/// Selection is storage, not value dependency; payload-mode consumers must
/// still ask reachable-storage aliasing rather than certifying a TABLE cell.
pub fn mappedStorageAt(
    cache: *FileCache,
    actual: FileCache.ActualCallSummary,
    alternative: Alternative,
    buffer: *[1]Ast.Node.Index,
) Error!?storage_alias.StorageSelection {
    const argument = (try actual.callArgumentFor(cache, buffer, alternative.owner.param)) orelse return null;
    return .{ .node = argument, .path = alternative.owner.path };
}

const Mode = enum { value, location, coordinate, address_bits };
const Output = struct {
    complete: bool = true,
    items: std.ArrayListUnmanaged(Alternative) = .empty,
};
const Frame = struct {
    cache: *FileCache,
    declaration: Ast.Node.Index,
    body: Ast.Node.Index,
    // Borrow immutable item/arena storage, not a relocatable cache-map slot.
    bindings: bindings_mod.LocalBindings,
    resolution: TypeResolver.ResolutionFrame,
    mutations: []const Ast.Node.Index = &.{},
    return_token: Ast.TokenIndex = 0,
};

const Query = struct {
    root: *FileCache,
    state: *State,
    resolver: *TypeResolver,
    remaining: *u32,
    scratch: std.mem.Allocator,
    entry_tree: *const Ast,
    entry_token: Ast.TokenIndex,

    fn charge(self: *Query) Error!void {
        if (self.remaining.* == 0) {
            const pos = budget.lineCol(self.entry_tree.source, self.entry_tree.tokenStart(self.entry_token));
            var name: budget.NameBuf = .{};
            if (tokens.enclosingFnDecl(self.entry_tree, self.entry_token)) |decl| {
                var buffer: [1]Ast.Node.Index = undefined;
                if (tokens.fnProto(self.entry_tree, &buffer, decl)) |proto| {
                    if (proto.name_token) |t| name.set(self.entry_tree.tokenSlice(t));
                }
            }
            return budget.fail(.{
                .limit = .return_storage_work, .limit_value = FileCache.actual_query_work_limit, .reached = FileCache.actual_query_work_limit,
                .byte = self.entry_tree.tokenStart(self.entry_token),
                .line = pos.line, .column = pos.column, .function = name,
            });
        }
        self.remaining.* -= 1;
    }

    fn body(self: *Query, caller: *FileCache, actual: FileCache.ActualCallSummary, depth: u32) Error!ReturnedStorage {
        try self.charge();
        if (depth >= 64) return .{};
        const callee = actual.callee;
        const key: Key = .{
            .declaration = .{ .tree = callee.tree, .module = callee.handle.module, .declaration = callee.declaration },
            .context = callee.reference.actual_type,
        };
        if (self.state.sets.get(key)) |answer| return answer;
        if (self.state.active.contains(key)) return .{};
        try self.state.active.put(self.root.gpa, key, {});
        defer _ = self.state.active.remove(key);
        try self.charge();
        const cache = (try actual.declaringCache(caller)) orelse return .{};
        const body_node = tokens.bodyOf(cache.tree, callee.declaration) orelse return .{};
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(cache.tree, &buffer, callee.declaration) orelse return .{};
        const resolution = self.resolver.frameForFunction(callee.reference);
        var frame: Frame = .{
            .cache = cache, .declaration = callee.declaration, .body = body_node,
            .bindings = (try cache.localBindings(proto, body_node)).*,
            .resolution = resolution,
        };
        try self.charge();
        const declared = self.resolver.normalizedType(callee.reference.actual_type.data.function.return_value.*) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
        };
        if (declared) |result_type| {
            // The instantiated callable, not its unresolved generic syntax,
            // supplies this shape. Explicit address-bit conversions still
            // require origin tracing rather than a scalar safety conclusion.
            if (try self.addressFree(result_type, 0) and !try self.hasAddressBits(frame, body_node, 0)) {
                const copied: ReturnedStorage = .{ .complete = true };
                try self.state.sets.put(self.root.gpa, key, copied);
                return copied;
            }
        }
        try self.charge();
        var mutations: std.ArrayListUnmanaged(Ast.Node.Index) = .empty;
        const mutations_complete = try self.collectMutations(cache.tree, body_node, &mutations, 0);
        frame.mutations = mutations.items;
        var output: Output = .{ .complete = mutations_complete };
        var returns: usize = 0;
        try self.scan(frame, body_node, &output, &returns, depth);
        if (returns == 0) output.complete = false;
        // SDK table coordinates are the canonical receiver, not the private
        // header layout reached through ptrCast(metadata). This is declaration
        // and instantiated-container identity, never a getter-name opcode.
        if (try self.tableContainer(frame.resolution)) {
            for (output.items.items) |*item| {
                try self.charge();
                if (item.owner.param == 0 and item.storage == .backing_storage and item.projection != .payload_value)
                    item.owner.path = "";
            }
        }
        const arena = self.state.allocator(self.root.gpa);
        const owned = try arena.alloc(Alternative, output.items.items.len);
        for (owned, output.items.items) |*dest, src| {
            dest.* = src;
            dest.owner.path = try arena.dupe(u8, src.owner.path);
            dest.result_path = try arena.dupe(u8, src.result_path);
        }
        const answer: ReturnedStorage = .{ .complete = output.complete, .alternatives = owned };
        try self.state.sets.put(self.root.gpa, key, answer);
        return answer;
    }

    fn scan(self: *Query, frame: Frame, node: Ast.Node.Index, output: *Output, returns: *usize, depth: u32) Error!void {
        try self.charge();
        if (depth >= 64) { output.complete = false; return; }
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) == .fn_decl) return;
        if (tree.nodeTag(node) == .@"return") {
            returns.* += 1;
            const value = tree.nodeData(node).opt_node.unwrap() orelse return;
            var at_return = frame;
            at_return.return_token = tree.lastToken(node);
            try self.expression(at_return, value, .value, "", output, depth + 1);
            return;
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            try self.charge();
            try self.scan(frame, child, output, returns, depth + 1);
        }
    }

    fn collectMutations(self: *Query, tree: *const Ast, node: Ast.Node.Index, result: *std.ArrayListUnmanaged(Ast.Node.Index), depth: u32) Error!bool {
        try self.charge();
        if (depth >= 64) return false;
        if (tree.nodeTag(node) == .fn_decl) return true;
        switch (tree.nodeTag(node)) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
            .assign_bit_and, .assign_bit_or, .assign_bit_xor, .assign_shl, .assign_shr,
            .assign_shl_sat, .assign_mul_wrap, .assign_add_wrap, .assign_sub_wrap,
            .assign_mul_sat, .assign_add_sat, .assign_sub_sat,
            => try result.append(self.scratch, node),
            .assign_destructure => return false,
            else => {},
        }
        var children = Iterator.init(tree, node);
        var complete = true;
        while (children.next(tree)) |child| {
            try self.charge();
            if (!try self.collectMutations(tree, child, result, depth + 1)) complete = false;
        }
        return complete;
    }

    fn tableContainer(self: *Query, resolution: TypeResolver.ResolutionFrame) Error!bool {
        const actual = resolution.container_type orelse return false;
        if (actual.data != .container) return false;
        const container = actual.data.container;
        if (container.scope_handle.scope == .root) return false;
        const tree = &container.scope_handle.handle.document.tree;
        const node = container.scope_handle.toNode();
        const key: Key = .{
            .declaration = .{ .tree = tree, .module = container.scope_handle.handle.module, .declaration = node },
            .context = actual,
        };
        try self.charge();
        if (self.state.tables.get(key)) |known| return known;
        try self.charge();
        const hash_map = self.resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/hash_map.zig") catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => false,
        };
        try self.charge();
        const array_map = self.resolver.declaredInToolchainFile(container.scope_handle.handle, "/std/array_hash_map.zig") catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => false,
        };
        if (!hash_map and !array_map) {
            try self.state.tables.put(self.root.gpa, key, false);
            return false;
        }
        const constructor = tokens.enclosingFnDecl(tree, tree.firstToken(node)) orelse return false;
        var top_level = false;
        for (tree.rootDecls()) |decl| {
            try self.charge();
            if (decl == constructor) { top_level = true; break; }
        }
        if (!top_level) {
            try self.state.tables.put(self.root.gpa, key, false);
            return false;
        }
        const body_node = tokens.bodyOf(tree, constructor) orelse return false;
        const is_table = try self.directReturnedContainer(tree, body_node, node, 0);
        try self.state.tables.put(self.root.gpa, key, is_table);
        return is_table;
    }

    /// A map's literal is returned by its type constructor. Nested iterator,
    /// entry and header literals in that returned struct are NOT table roots.
    fn directReturnedContainer(self: *Query, tree: *const Ast, node: Ast.Node.Index, selected: Ast.Node.Index, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 64 or tree.nodeTag(node) == .fn_decl) return false;
        if (tree.nodeTag(node) == .@"return") {
            const result = tree.nodeData(node).opt_node.unwrap() orelse return false;
            return result == selected;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullContainerDecl(&buffer, node) != null) return false;
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            try self.charge();
            if (try self.directReturnedContainer(tree, child, selected, depth + 1)) return true;
        }
        return false;
    }

    fn pointerSize(self: *Query, initial: TypeResolver.ActualType) Error!?std.builtin.Type.Pointer.Size {
        var ty = initial;
        for (0..32) |_| {
            try self.charge();
            ty = (try self.canonicalType(ty)) orelse return null;
            if (self.resolver.pointerSize(ty)) |size| return size;
            if (self.resolver.typeTag(ty) != .optional) return null;
            ty = self.resolver.childType(ty) orelse return null;
        }
        return null;
    }

    fn hasAddressBits(self: *Query, frame: Frame, node: Ast.Node.Index, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 64) return true;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "@intFromPtr") or std.mem.eql(u8, name, "@ptrFromInt")) return true;
            },
            .identifier => {
                const token = tree.nodeMainToken(node);
                for (frame.bindings.items) |_| try self.charge();
                if (frame.bindings.findAt(tree.tokenSlice(token), token)) |binding| {
                    if (binding.origin == .param) return false;
                    const rhs = frame.cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse return true;
                    if (rhs == node) return true;
                    return self.hasAddressBits(frame, rhs, depth + 1);
                }
            },
            else => {},
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            try self.charge();
            if (try self.hasAddressBits(frame, child, depth + 1)) return true;
        }
        return false;
    }
    const SyntaxPath = struct { binding: *const bindings_mod.Binding, path: []const u8 };

    fn syntaxPath(self: *Query, frame: Frame, node: Ast.Node.Index, depth: u32) Error!?SyntaxPath {
        try self.charge();
        if (depth >= 64) return null;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                for (frame.bindings.items) |_| try self.charge();
                const binding = frame.bindings.findAt(tree.tokenSlice(token), token) orelse return null;
                return .{ .binding = binding, .path = "" };
            },
            .field_access => {
                const data = tree.nodeData(node).node_and_token;
                var root = (try self.syntaxPath(frame, data[0], depth + 1)) orelse return null;
                root.path = try self.join(root.path, tree.tokenSlice(data[1]));
                return root;
            },
            .@"try", .address_of => return self.syntaxPath(frame, tree.nodeData(node).node, depth + 1),
            .grouped_expression, .unwrap_optional => return self.syntaxPath(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            else => return null,
        }
    }

    fn invalidated(self: *Query, frame: Frame, node: Ast.Node.Index) Error!bool {
        const selected = (try self.syntaxPath(frame, node, 0)) orelse return false;
        const tree = frame.cache.tree;
        for (frame.mutations) |write| {
            try self.charge();
            const token = tree.firstToken(write);
            if (token <= selected.binding.name_token or token >= frame.return_token) continue;
            const target = tree.nodeData(write).node_and_node[0];
            const changed = (try self.syntaxPath(frame, target, 0)) orelse continue;
            if (selected.binding.name_token != changed.binding.name_token) continue;
            if (tree.nodeTag(write) == .assign_add or tree.nodeTag(write) == .assign_sub) {
                const target_type = try self.nodeType(frame, target);
                const offset_type = try self.nodeType(frame, tree.nodeData(write).node_and_node[1]);
                if (target_type != null and offset_type != null and try self.pointerSize(target_type.?) != null and
                    try self.addressFree(offset_type.?, 0)) continue;
            }
            if (changed.path.len == 0 or std.mem.eql(u8, selected.path, changed.path) or
                (std.mem.startsWith(u8, selected.path, changed.path) and selected.path.len > changed.path.len and selected.path[changed.path.len] == '.')) return true;
        }
        return false;
    }

    fn nodeType(self: *Query, frame: Frame, node: Ast.Node.Index) Error!?TypeResolver.ActualType {
        try self.charge();
        return frame.resolution.typeOfNode(node) catch |err| switch (err) {
            error.OutOfMemory => error.OutOfMemory,
            else => null,
        };
    }

    fn canonicalType(self: *Query, value: TypeResolver.ActualType) Error!?TypeResolver.ActualType {
        if (value.is_type_val) return value;
        try self.charge();
        return self.resolver.normalizedType(value) catch |err| switch (err) {
            error.OutOfMemory => error.OutOfMemory,
        };
    }

    /// Every declared field must be checked. One borrowed sibling prevents
    /// an aggregate's copied-value proof, even when its first field is scalar.
    fn addressFree(self: *Query, value: TypeResolver.ActualType, depth: u32) Error!bool {
        try self.charge();
        if (depth >= 32) return false;
        const ty = (try self.canonicalType(value)) orelse return false;
        const tag = self.resolver.typeTag(ty) orelse return false;
        switch (tag) {
            .int, .float, .comptime_int, .comptime_float, .bool, .@"enum", .void, .noreturn, .null, .error_set => return true,
            .optional, .array, .vector => {
                const child = self.resolver.childType(ty) orelse return false;
                return self.addressFree(child, depth + 1);
            },
            .@"struct" => {
                if (ty.data != .container) return false;
                const container = ty.data.container;
                const field_frame = self.resolver.frameForContainer(container);
                const tree = &container.scope_handle.handle.document.tree;
                var buffer: [2]Ast.Node.Index = undefined;
                const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse return false;
                for (declaration.ast.members) |member| {
                    try self.charge();
                    const container_field = tree.fullContainerField(member) orelse continue;
                    const node = container_field.ast.type_expr.unwrap() orelse return false;
                    try self.charge();
                    const field_type = field_frame.typeOfNode(node) catch |err| switch (err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        else => return false,
                    } orelse return false;
                    if (!try self.addressFree(field_type, depth + 1)) return false;
                }
                return true;
            },
            else => return false,
        }
    }

    fn payload(self: *Query, value: TypeResolver.ActualType, source: Alternative, output: *Output, depth: u32) Error!void {
        try self.charge();
        if (depth >= 32) { output.complete = false; return; }
        const ty = (try self.canonicalType(value)) orelse { output.complete = false; return; };
        if (try self.addressFree(ty, 0)) return;
        const tag = self.resolver.typeTag(ty) orelse { output.complete = false; return; };
        if (tag == .pointer) {
            var item = source;
            item.projection = .payload_value;
            item.storage = .payload_storage;
            // The carrier is rooted, but the stored pointer's pointee is not
            // proved to be the carrier's cell or its allocation.
            output.complete = false;
            try self.add(output, item);
            return;
        }
        if (tag == .optional or tag == .array) {
            const child = self.resolver.childType(ty) orelse { output.complete = false; return; };
            return self.payload(child, source, output, depth + 1);
        }
        if (tag != .@"struct" or ty.data != .container) { output.complete = false; return; }
        const container = ty.data.container;
        const field_frame = self.resolver.frameForContainer(container);
        const tree = &container.scope_handle.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = tree.fullContainerDecl(&buffer, container.scope_handle.toNode()) orelse { output.complete = false; return; };
        for (declaration.ast.members) |member| {
            try self.charge();
            const container_field = tree.fullContainerField(member) orelse continue;
            const node = container_field.ast.type_expr.unwrap() orelse { output.complete = false; continue; };
            try self.charge();
            const ty_field = field_frame.typeOfNode(node) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => { output.complete = false; continue; },
            } orelse { output.complete = false; continue; };
            var projected = source;
            const name = tree.tokenSlice(container_field.ast.main_token);
            projected.owner.path = try self.join(source.owner.path, name);
            projected.result_path = try self.join(source.result_path, name);
            try self.payload(ty_field, projected, output, depth + 1);
        }
    }

    fn join(self: *Query, left: []const u8, right: []const u8) Error![]const u8 {
        if (left.len == 0) return right;
        if (right.len == 0) return left;
        return std.fmt.allocPrint(self.scratch, "{s}.{s}", .{ left, right });
    }

    fn add(self: *Query, output: *Output, alternative: Alternative) Error!void {
        for (output.items.items) |existing| {
            try self.charge();
            if (existing.owner.param == alternative.owner.param and existing.projection == alternative.projection and
                existing.storage == alternative.storage and std.mem.eql(u8, existing.owner.path, alternative.owner.path) and
                std.mem.eql(u8, existing.result_path, alternative.result_path)) return;
        }
        try output.items.append(self.scratch, alternative);
    }

    fn rebound(self: *Query, frame: Frame, binding: *const bindings_mod.Binding, use_token: Ast.TokenIndex) Error!bool {
        try self.charge();
        const roots = try frame.cache.escapeRoots(frame.body);
        for (roots.writes) |write| {
            try self.charge();
            if (write.declares or write.token <= binding.name_token or write.token >= @max(use_token, frame.return_token)) continue;
            if (!std.mem.eql(u8, write.name, binding.name)) continue;
            const target = frame.bindings.findAt(write.name, write.token) orelse return true;
            if (target.name_token == binding.name_token) return true;
        }
        return false;
    }

    /// A local aggregate may contain positively rooted pointer writes even
    /// when its initializer or loop coverage remains unknown. Retain those
    /// borrows, but do not mistake collecting writes for proving every cell.
    fn assignedOrigins(self: *Query, frame: Frame, binding: *const bindings_mod.Binding, result_path: []const u8, output: *Output, depth: u32) Error!void {
        const tree = frame.cache.tree;
        for (frame.mutations) |write| {
            try self.charge();
            if (tree.nodeTag(write) != .assign) continue;
            const token = tree.firstToken(write);
            if (token <= binding.name_token or token >= frame.return_token) continue;
            const data = tree.nodeData(write).node_and_node;
            var target = data[0];
            for (0..64) |_| {
                try self.charge();
                if (tree.nodeTag(target) != .array_access) break;
                target = tree.nodeData(target).node_and_node[0];
            }
            const destination = (try self.syntaxPath(frame, target, 0)) orelse continue;
            if (destination.binding.name_token != binding.name_token) continue;
            var at_write = frame;
            at_write.return_token = token;
            var source: Output = .{};
            const field_path = try self.join(result_path, destination.path);
            try self.expression(at_write, data[1], .value, field_path, &source, depth + 1);
            if (source.items.items.len != 0 or !source.complete) output.complete = false;
            for (source.items.items) |item| try self.add(output, item);
        }
    }

    fn expression(self: *Query, frame: Frame, node: Ast.Node.Index, mode: Mode, result_path: []const u8, output: *Output, depth: u32) Error!void {
        try self.charge();
        if (depth >= 64) { output.complete = false; return; }
        const tree = frame.cache.tree;
        const tag = tree.nodeTag(node);
        if (mode == .value) {
            if (try self.nodeType(frame, node)) |ty| {
                if (try self.addressFree(ty, 0) and !try self.hasAddressBits(frame, node, 0)) return;
            }
        }
        if (try self.invalidated(frame, node)) { output.complete = false; return; }
        switch (tag) {
            .@"try" => return self.expression(frame, tree.nodeData(node).node, mode, result_path, output, depth + 1),
            .deref => {
                if (mode != .value) return self.expression(frame, tree.nodeData(node).node, if (mode == .location) .value else mode, result_path, output, depth + 1);
                var source: Output = .{};
                try self.expression(frame, tree.nodeData(node).node, .value, result_path, &source, depth + 1);
                if (!source.complete) output.complete = false;
                const ty = (try self.nodeType(frame, node)) orelse { output.complete = false; return; };
                for (source.items.items) |item| try self.payload(ty, item, output, 0);
            },
            .grouped_expression, .unwrap_optional =>
                return self.expression(frame, tree.nodeData(node).node_and_token[0], mode, result_path, output, depth + 1),
            .address_of => {
                var value = tree.nodeData(node).node;
                var peeled: u32 = 0;
                while (peeled < 64) : (peeled += 1) {
                    try self.charge();
                    switch (tree.nodeTag(value)) {
                        .grouped_expression, .unwrap_optional => value = tree.nodeData(value).node_and_token[0],
                        .@"try" => value = tree.nodeData(value).node,
                        else => break,
                    }
                }
                if (peeled == 64) { output.complete = false; return; }
                switch (tree.nodeTag(value)) {
                    .identifier, .call, .call_one, .call_comma, .call_one_comma => {
                        // An address of a parameter/local header or a temporary
                        // result is not the address held IN that value.
                        output.complete = false; return;
                    },
                    else => {},
                }
                var operand: Output = .{};
                try self.expression(frame, tree.nodeData(node).node, .location, result_path, &operand, depth + 1);
                if (!operand.complete) output.complete = false;
                for (operand.items.items) |item| {
                    var address = item;
                    address.projection = .cell_address;
                    try self.add(output, address);
                }
            },
            .identifier => {
                const token = tree.nodeMainToken(node);
                const name = tree.tokenSlice(token);
                if (std.mem.eql(u8, name, "null")) return;
                for (frame.bindings.items) |_| try self.charge();
                const binding = frame.bindings.findAt(name, token) orelse { output.complete = false; return; };
                if (try self.rebound(frame, binding, token)) { output.complete = false; return; }
                if (binding.origin == .param) {
                    var parameter: u32 = 0;
                    for (frame.bindings.items) |*candidate| {
                        try self.charge();
                        if (candidate.origin != .param) continue;
                        if (candidate.name_token == binding.name_token) break;
                        parameter += 1;
                    }
                    const ty = (try self.nodeType(frame, node)) orelse { output.complete = false; return; };
                    const size = try self.pointerSize(ty);
                    if (mode == .address_bits and size == null) { output.complete = false; return; }
                    if (mode == .location and size == null) { output.complete = false; return; }
                    if (mode == .value and size == null) {
                        return self.payload(ty, .{
                            .owner = .{ .param = parameter, .path = "" }, .result_path = result_path,
                            .projection = .payload_value, .storage = .payload_storage,
                        }, output, 0);
                    }
                    try self.add(output, .{
                        .owner = .{ .param = parameter, .path = "" }, .result_path = result_path,
                        .projection = if (mode == .location) .cell_address else .pointer_value,
                        .storage = if (size == .slice or size == .many or size == .c) .backing_storage else .inline_storage,
                    });
                    return;
                }
                if (!binding.is_const and mode != .location)
                    try self.assignedOrigins(frame, binding, result_path, output, depth + 1);
                if (mode == .location) {
                    const ty = (try self.nodeType(frame, node)) orelse { output.complete = false; return; };
                    if (try self.pointerSize(ty) == null) { output.complete = false; return; }
                }
                const rhs = frame.cache.nodeForExactSpan(binding.rhsFirstAfterTry(tree.tokens.items(.tag)), binding.rhs_last) orelse {
                    output.complete = false; return;
                };
                if (rhs == node) { output.complete = false; return; }
                if (binding.origin == .loop_capture) {
                    const rhs_type = try self.nodeType(frame, rhs);
                    if (rhs_type == null or self.resolver.typeTag(rhs_type.?) != .optional) {
                        // A by-value loop element copies its pointer payload;
                        // the iterable's allocation is not the element pointee.
                        var iterable: Output = .{};
                        try self.expression(frame, rhs, .value, result_path, &iterable, depth + 1);
                        output.complete = false;
                        for (iterable.items.items) |original| {
                            var item = original;
                            item.projection = .payload_value;
                            item.storage = .payload_storage;
                            try self.add(output, item);
                        }
                        return;
                    }
                }
                return self.expression(frame, rhs, mode, result_path, output, depth + 1);
            },
            .field_access => {
                const access = tree.nodeData(node).node_and_token;
                try self.field(frame, node, access[0], tree.tokenSlice(access[1]), mode, result_path, output, depth + 1);
            },
            .array_access => {
                const base = tree.nodeData(node).node_and_node[0];
                const ty = (try self.nodeType(frame, base)) orelse { output.complete = false; return; };
                const size = self.resolver.pointerSize(ty);
                var parent: Output = .{};
                const base_mode: Mode = if (mode == .location) (if (size != null) .coordinate else .location) else .value;
                try self.expression(frame, base, base_mode, result_path, &parent, depth + 1);
                if (!parent.complete) output.complete = false;
                if (mode == .location and parent.items.items.len == 0) output.complete = false;
                for (parent.items.items) |original| {
                    var item = original;
                    if (mode == .location) {
                        const known_address = item.projection == .cell_address;
                        item.projection = .cell_address;
                        if (item.storage != .payload_storage) {
                            item.storage = if (size == .slice or size == .many or size == .c)
                                .backing_storage
                            else if (self.resolver.typeTag(ty) == .array)
                                .inline_storage
                            else if (size == .one and item.owner.path.len != 0 and !known_address)
                                .backing_storage
                            else item.storage;
                        }
                    } else {
                        const result_type = (try self.nodeType(frame, node)) orelse { output.complete = false; continue; };
                        try self.payload(result_type, item, output, 0);
                        continue;
                    }
                    try self.add(output, item);
                }
            },
            .slice_open, .slice, .slice_sentinel => {
                const slice = tree.fullSlice(node).?;
                var parent: Output = .{};
                try self.expression(frame, slice.ast.sliced, .value, result_path, &parent, depth + 1);
                if (parent.items.items.len == 0 and parent.complete)
                    try self.expression(frame, slice.ast.sliced, .location, result_path, &parent, depth + 1);
                if (!parent.complete) output.complete = false;
                const ty = (try self.nodeType(frame, slice.ast.sliced)) orelse { output.complete = false; return; };
                for (parent.items.items) |original| {
                    var item = original;
                    if (item.storage != .payload_storage) {
                        item.projection = .pointer_value;
                        item.storage = if (self.resolver.typeTag(ty) == .array) .inline_storage else .backing_storage;
                    }
                    try self.add(output, item);
                }
            },
            .call, .call_one, .call_comma, .call_one_comma => try self.call(frame, node, mode, result_path, output, depth + 1),
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "@field")) {
                    var arguments = Iterator.init(tree, node);
                    const base = arguments.next(tree) orelse { output.complete = false; return; };
                    try self.charge();
                    const name_node = arguments.next(tree) orelse { output.complete = false; return; };
                    try self.charge();
                    if (arguments.next(tree) != null) { output.complete = false; return; }
                    try self.charge();
                    const field_name = frame.resolution.stringValueOfNode(name_node) catch |err| switch (err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        else => { output.complete = false; return; },
                    } orelse { output.complete = false; return; };
                    return self.field(frame, node, base, field_name, mode, result_path, output, depth + 1);
                }
                const cast = std.mem.eql(u8, name, "@ptrCast") or std.mem.eql(u8, name, "@alignCast") or
                    std.mem.eql(u8, name, "@constCast") or std.mem.eql(u8, name, "@volatileCast") or
                    std.mem.eql(u8, name, "@as");
                const bits = std.mem.eql(u8, name, "@intFromPtr") or std.mem.eql(u8, name, "@ptrFromInt");
                if (!cast and !bits) { output.complete = false; return; }
                var children = Iterator.init(tree, node);
                var last: ?Ast.Node.Index = null;
                while (children.next(tree)) |child| { try self.charge(); last = child; }
                const operand = last orelse { output.complete = false; return; };
                var operand_result: Output = .{};
                try self.expression(frame, operand, if (bits) .address_bits else mode, result_path, &operand_result, depth + 1);
                if (!operand_result.complete or (bits and operand_result.items.items.len == 0)) output.complete = false;
                for (operand_result.items.items) |item| try self.add(output, item);
            },
            .add, .sub => {
                if (mode != .address_bits) {
                    const result_type = (try self.nodeType(frame, node)) orelse { output.complete = false; return; };
                    if (try self.pointerSize(result_type) == null) { output.complete = false; return; }
                }
                var children = Iterator.init(tree, node);
                while (children.next(tree)) |child| {
                    try self.charge();
                    // Numeric offsets contribute no storage; pointer-to-int
                    // operands retain their canonical source path.
                    if (tree.nodeTag(child) == .number_literal) continue;
                    if (try self.nodeType(frame, child)) |ty| {
                        if (try self.addressFree(ty, 0) and !try self.hasAddressBits(frame, child, 0)) continue;
                    }
                    try self.expression(frame, child, if (mode == .address_bits) .address_bits else .value, result_path, output, depth + 1);
                }
            },
            .@"if", .if_simple => {
                const conditional = tree.fullIf(node).?;
                try self.charge();
                const known = frame.resolution.boolValueOfNode(conditional.ast.cond_expr) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => null,
                };
                if (known) |condition| {
                    if (condition) return self.expression(frame, conditional.ast.then_expr, mode, result_path, output, depth + 1);
                    if (conditional.ast.else_expr.unwrap()) |other|
                        return self.expression(frame, other, mode, result_path, output, depth + 1);
                    output.complete = false;
                    return;
                }
                try self.expression(frame, conditional.ast.then_expr, mode, result_path, output, depth + 1);
                if (conditional.ast.else_expr.unwrap()) |other| {
                    try self.expression(frame, other, mode, result_path, output, depth + 1);
                } else output.complete = false;
            },
            .number_literal, .char_literal, .enum_literal, .error_value => {},
            else => {
                var buffer: [2]Ast.Node.Index = undefined;
                if (tree.fullStructInit(&buffer, node)) |literal| {
                    for (literal.ast.fields) |member_node| {
                        try self.charge();
                        const first = tree.firstToken(member_node);
                        const tags = tree.tokens.items(.tag);
                        if (first < 3 or tags[first - 1] != .equal or tags[first - 2] != .identifier or tags[first - 3] != .period) {
                            output.complete = false; continue;
                        }
                        const path = try self.join(result_path, tree.tokenSlice(first - 2));
                        try self.expression(frame, member_node, .value, path, output, depth + 1);
                    }
                } else output.complete = false;
            },
        }
    }

    fn field(self: *Query, frame: Frame, node: Ast.Node.Index, base: Ast.Node.Index, name: []const u8, mode: Mode, result_path: []const u8, output: *Output, depth: u32) Error!void {
        var parent: Output = .{};
        try self.expression(frame, base, if (mode == .location) .location else .coordinate, result_path, &parent, depth + 1);
        if (!parent.complete) output.complete = false;
        const ty = try self.nodeType(frame, node);
        if (ty == null and mode != .coordinate and mode != .location) output.complete = false;
        const base_type = try self.nodeType(frame, base);
        const slice_pointer = if (base_type) |value| self.resolver.pointerSize(value) == .slice and std.mem.eql(u8, name, "ptr") else false;
        for (parent.items.items) |original| {
            var item = original;
            if (item.result_path.len != result_path.len) {
                if (mode == .location) { output.complete = false; continue; }
                const selected = try self.join(result_path, name);
                if (!std.mem.eql(u8, item.result_path, selected) and
                    !(std.mem.startsWith(u8, item.result_path, selected) and item.result_path.len > selected.len and item.result_path[selected.len] == '.')) continue;
                item.result_path = if (item.result_path.len == selected.len) result_path else
                    try self.join(result_path, item.result_path[selected.len + 1 ..]);
            } else {
                if (!slice_pointer) item.owner.path = try self.join(item.owner.path, name);
                if (mode == .value or mode == .address_bits) {
                    const field_type = ty orelse { output.complete = false; continue; };
                    const field_size = try self.pointerSize(field_type);
                    if (mode == .address_bits and field_size == null) { output.complete = false; continue; }
                    if ((mode == .value and field_size == null) or field_size == .one) {
                        try self.payload(field_type, item, output, 0);
                        continue;
                    }
                    item.projection = .pointer_value;
                    item.storage = .backing_storage;
                }
            }
            try self.add(output, item);
        }
    }

    fn call(self: *Query, frame: Frame, node: Ast.Node.Index, _: Mode, result_path: []const u8, output: *Output, depth: u32) Error!void {
        var buffer: [1]Ast.Node.Index = undefined;
        const ast_call = frame.cache.tree.fullCall(&buffer, node).?;
        try self.charge();
        const actual = (try frame.cache.actualCallSummaryAt(frame.cache.tree.lastToken(ast_call.ast.fn_expr), frame.resolution)) orelse {
            output.complete = false; return;
        };
        const returned = try self.body(frame.cache, actual, depth);
        if (!returned.complete) output.complete = false;
        for (returned.alternatives) |alternative| {
            try self.charge();
            var argument_buffer: [1]Ast.Node.Index = undefined;
            const mapped = (try mappedStorageAt(frame.cache, actual, alternative, &argument_buffer)) orelse {
                output.complete = false; continue;
            };
            var arguments: Output = .{};
            try self.expression(frame, mapped.node, .coordinate, result_path, &arguments, depth + 1);
            if (!arguments.complete) output.complete = false;
            for (arguments.items.items) |item| {
                var translated = item;
                var suffix = mapped.path;
                const argument_selector = if (item.result_path.len == result_path.len) "" else
                    item.result_path[result_path.len + @intFromBool(result_path.len != 0) ..];
                if (argument_selector.len != 0) {
                    if (!std.mem.eql(u8, suffix, argument_selector) and
                        !(std.mem.startsWith(u8, suffix, argument_selector) and suffix.len > argument_selector.len and suffix[argument_selector.len] == '.')) continue;
                    suffix = if (suffix.len == argument_selector.len) "" else suffix[argument_selector.len + 1 ..];
                }
                translated.owner.path = try self.join(item.owner.path, suffix);
                translated.result_path = try self.join(result_path, alternative.result_path);
                const rooted_payload = argument_selector.len != 0 and
                    alternative.storage == .payload_storage and item.storage != .payload_storage;
                translated.projection = if (rooted_payload) item.projection else alternative.projection;
                // A constructed aggregate's field selector selects its source;
                // it is not another field to append to the source's owner path.
                // Incomplete construction coverage still remains incomplete.
                translated.storage = if (alternative.storage == .inline_storage or rooted_payload)
                    item.storage
                else if (item.storage == .payload_storage)
                    .payload_storage
                else alternative.storage;
                try self.add(output, translated);
            }
        }
    }
};

test "returned storage distinguishes a backing cell from an inline sibling cell" {
    const source: [:0]const u8 =
        \\const Box = struct {
        \\    slots: []u32, scratch: [4]u32,
        \\    fn backing(self: *Box) *u32 { return &self.slots[0]; }
        \\    fn inlineCell(self: *Box) *u32 { return &self.scratch[0]; }
        \\};
        \\fn use(box: *Box) void { _ = box.backing(); _ = box.inlineCell(); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    var remaining: u32 = 50_000;
    const backing = try returnedStorageAt(typed.cache, callNamed(typed.tree(), "backing").?, .{ .remaining = &remaining });
    const inline_cell = try returnedStorageAt(typed.cache, callNamed(typed.tree(), "inlineCell").?, .{ .remaining = &remaining });
    try std.testing.expect(backing.complete and inline_cell.complete);
    try std.testing.expectEqual(@as(usize, 1), backing.alternatives.len);
    try std.testing.expectEqual(@as(usize, 1), inline_cell.alternatives.len);
    try std.testing.expectEqual(Projection.cell_address, backing.alternatives[0].projection);
    try std.testing.expectEqual(Storage.backing_storage, backing.alternatives[0].storage);
    try std.testing.expectEqualStrings("slots", backing.alternatives[0].owner.path);
    try std.testing.expectEqual(Storage.inline_storage, inline_cell.alternatives[0].storage);
    try std.testing.expectEqualStrings("scratch", inline_cell.alternatives[0].owner.path);
}

// In-module typed consumer regressions, appended after the module's own test.
// The `Typed` harness and `callNamed` are the ones src/cache/call_summary.zig
// carries, copied verbatim: top-level declarations resolve in any order, so
// the test above finds both of them here.
//
// Every query runs on its own meter, taken from the canonical consumer-query
// bound rather than from a number this file owns, and that meter is read back
// afterwards, so no assertion below can be satisfied by a query that charged
// nothing.

/// A document the type engine can resolve in, so a call edge inside one body
/// really names the declaration another body spells.
const Typed = struct {
    const engine = @import("type_engine");

    context: engine.TypeContext,
    resolver: engine.TypeResolver,
    cache: *FileCache,

    fn init(gpa: std.mem.Allocator, source: [:0]const u8) !*Typed {
        const self = try gpa.create(Typed);
        errdefer gpa.destroy(self);
        try self.context.init(gpa, std.testing.io);
        errdefer self.context.deinit();
        try self.resolver.init(&self.context, gpa, "/zbc-call-summary-test.zig", source);
        errdefer self.resolver.deinit();
        self.cache = try gpa.create(FileCache);
        errdefer gpa.destroy(self.cache);
        self.cache.* = try FileCache.init(gpa, self.tree());
        self.cache.setZls(&self.resolver);
        return self;
    }

    fn deinit(self: *Typed, gpa: std.mem.Allocator) void {
        self.cache.deinit();
        gpa.destroy(self.cache);
        self.resolver.deinit();
        self.context.deinit();
        gpa.destroy(self);
    }

    fn tree(self: *Typed) *const Ast {
        return &self.resolver.handle.document.tree;
    }
};

fn callNamed(tree: *const Ast, name: []const u8) ?Ast.TokenIndex {
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), name)) continue;
        return tree.lastToken(call.ast.fn_expr);
    }
    return null;
}

/// The call whose OWN FIRST ARGUMENT is written exactly as `argument`.  The
/// callee's name is deliberately not part of this lookup: an SDK accessor is
/// read by what it is handed, never by the getter vocabulary a consumer writes.
fn callTaking(tree: *const Ast, argument: []const u8) ?Ast.TokenIndex {
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (call.ast.params.len == 0) continue;
        if (!std.mem.eql(u8, tree.getNodeSource(call.ast.params[0]), argument)) continue;
        return tree.lastToken(call.ast.fn_expr);
    }
    return null;
}

/// The meter's whole allowance, spelled once and read from the same constant
/// the root cache meters every consumer query with.
const work_limit: u32 = FileCache.actual_query_work_limit;

/// One consumer query on its own meter: an answer is paid for out of the
/// caller's allowance, and the meter is read back so a query that spent
/// nothing is never mistaken for one that proved something.  The result and
/// its path bytes belong to the root cache, so it outlives this call.
fn returnedStorageOf(cache: *FileCache, token: Ast.TokenIndex) !ReturnedStorage {
    var remaining: u32 = work_limit;
    const returned = try returnedStorageAt(cache, token, .{ .remaining = &remaining });
    try std.testing.expect(remaining < work_limit);
    return returned;
}

fn actualOf(cache: *FileCache, token: Ast.TokenIndex) !FileCache.ActualCallSummary {
    return (try cache.actualCallSummaryAt(token, null)) orelse error.TestExpectedCallee;
}

/// One alternative named the way a consumer reads it: by owner, projection,
/// storage and the field of the RESULT that carries it.  The set is searched
/// by owner, so no answer depends on the order its alternatives came out in.
fn expectAlternative(
    returned: ReturnedStorage,
    owner: fn_summary.ParamPath,
    projection: Projection,
    storage: Storage,
    result_path: []const u8,
) !Alternative {
    for (returned.alternatives) |alternative| {
        if (alternative.owner.param != owner.param) continue;
        if (!std.mem.eql(u8, alternative.owner.path, owner.path)) continue;
        try std.testing.expectEqual(projection, alternative.projection);
        try std.testing.expectEqual(storage, alternative.storage);
        try std.testing.expectEqualStrings(result_path, alternative.result_path);
        return alternative;
    }
    return error.TestExpectedAlternative;
}

fn expectOnlyAlternative(
    returned: ReturnedStorage,
    owner: fn_summary.ParamPath,
    projection: Projection,
    storage: Storage,
    result_path: []const u8,
) !Alternative {
    try std.testing.expect(returned.complete);
    try std.testing.expectEqual(@as(usize, 1), returned.alternatives.len);
    return expectAlternative(returned, owner, projection, storage, result_path);
}

fn expectNoAlternative(returned: ReturnedStorage, param: u32, path: []const u8) !void {
    for (returned.alternatives) |alternative| {
        if (alternative.owner.param != param) continue;
        if (!std.mem.eql(u8, alternative.owner.path, path)) continue;
        return error.TestUnexpectedAlternative;
    }
}

fn expectNoStorage(returned: ReturnedStorage, storage: Storage) !void {
    for (returned.alternatives) |alternative| {
        if (alternative.storage == storage) return error.TestUnexpectedStorage;
    }
}

/// UNKNOWN: incomplete and empty.  No conclusion may be drawn from it, and
/// none may be drawn from the absence of alternatives either.
fn expectUnknown(returned: ReturnedStorage) !void {
    try std.testing.expect(!returned.complete);
    try std.testing.expectEqual(@as(usize, 0), returned.alternatives.len);
}

/// Complete and empty: the returned value carries no storage at all, so a
/// consumer may conclude that nothing was lent to it.
fn expectNoBorrow(returned: ReturnedStorage) !void {
    try std.testing.expect(returned.complete);
    try std.testing.expectEqual(@as(usize, 0), returned.alternatives.len);
}

/// The caller-side coordinate of one alternative: the argument the callee's
/// formal was handed, carrying the owner's own path.  The node belongs to the
/// caller's tree.
fn expectMapping(
    cache: *FileCache,
    actual: FileCache.ActualCallSummary,
    alternative: Alternative,
    expression: []const u8,
    path: []const u8,
) !void {
    var buffer: [1]Ast.Node.Index = undefined;
    const mapped = (try mappedStorageAt(cache, actual, alternative, &buffer)) orelse
        return error.TestExpectedMapping;
    const tree = cache.tree;
    try std.testing.expectEqualStrings(
        expression,
        tree.tokenSlice(tree.firstToken(mapped.node), tree.lastToken(mapped.node)),
    );
    try std.testing.expectEqualStrings(path, mapped.path);
}

test "an address into an inline field maps onto the receiver this call site handed it" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    scratch: [4]u32,
        \\    fn inlineCell(self: *Slots) *u32 { return &self.scratch[0]; }
        \\};
        \\const Holder = struct { grid: Slots };
        \\fn run(holder: *Holder) void { _ = holder.grid.inlineCell(); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    const token = callNamed(typed.tree(), "inlineCell") orelse return error.TestExpectedCall;
    const alternative = try expectOnlyAlternative(
        try returnedStorageOf(cache, token),
        .{ .param = 0, .path = "scratch" },
        .cell_address,
        .inline_storage,
        "",
    );
    // The consumer can carry that answer onto its own storage: the receiver
    // EXPRESSION this call site wrote, and the inline field inside it.
    try expectMapping(cache, try actualOf(cache, token), alternative, "holder.grid", "scratch");
}

test "a slice header copied out of a field carries that field's own storage" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    scratch: [4]u32,
        \\    fn view(self: *Slots, index: usize) []u32 { return self.slots[index .. index + 1]; }
        \\    fn inlineView(self: *Slots) []u32 { return self.scratch[0 .. 1]; }
        \\};
        \\fn run(grid: *Slots) void {
        \\    _ = grid.view(1);
        \\    _ = grid.inlineView();
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    // A returned slice is a copied header, not an address: it names the
    // allocation its field names, whether that field is a slice or an inline
    // array.
    _ = try expectOnlyAlternative(
        try returnedStorageOf(cache, callNamed(typed.tree(), "view") orelse return error.TestExpectedCall),
        .{ .param = 0, .path = "slots" },
        .pointer_value,
        .backing_storage,
        "",
    );
    _ = try expectOnlyAlternative(
        try returnedStorageOf(cache, callNamed(typed.tree(), "inlineView") orelse return error.TestExpectedCall),
        .{ .param = 0, .path = "scratch" },
        .pointer_value,
        .inline_storage,
        "",
    );
}

/// The owner and storage kind one answer reports, without pinning how the
/// callee's own return type spells the projection.
fn expectOwnerStorage(
    returned: ReturnedStorage,
    owner: fn_summary.ParamPath,
    storage: Storage,
) !Alternative {
    for (returned.alternatives) |alternative| {
        if (alternative.owner.param != owner.param) continue;
        if (!std.mem.eql(u8, alternative.owner.path, owner.path)) continue;
        try std.testing.expectEqual(storage, alternative.storage);
        return alternative;
    }
    return error.TestExpectedAlternative;
}

test "a helper that returns its pointer formal inherits the storage of the argument it was handed" {
    const source: [:0]const u8 =
        \\const Box = struct {
        \\    slots: []u32,
        \\    scratch: [4]u32,
        \\    fn identity(x: *u32) *u32 { return x; }
        \\    fn borrowed(self: *Box) *u32 { return identity(&self.slots[0]); }
        \\    fn inlined(self: *Box) *u32 { return identity(&self.scratch[0]); }
        \\};
        \\fn run(box: *Box) void {
        \\    _ = box.borrowed();
        \\    _ = box.inlined();
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    // `identity`'s own formal is a pointer, which says nothing about what it
    // was handed: the answer follows the ARGUMENT, so a cell in a field's
    // allocation keeps that allocation.
    const borrowed = try returnedStorageOf(cache, callNamed(typed.tree(), "borrowed") orelse return error.TestExpectedCall);
    try std.testing.expect(borrowed.complete);
    try std.testing.expectEqual(@as(usize, 1), borrowed.alternatives.len);
    _ = try expectOwnerStorage(borrowed, .{ .param = 0, .path = "slots" }, .backing_storage);
    try expectNoStorage(borrowed, .inline_storage);
    // The same helper handed an inline cell leaves it inline.
    const inlined = try returnedStorageOf(cache, callNamed(typed.tree(), "inlined") orelse return error.TestExpectedCall);
    try std.testing.expect(inlined.complete);
    try std.testing.expectEqual(@as(usize, 1), inlined.alternatives.len);
    _ = try expectOwnerStorage(inlined, .{ .param = 0, .path = "scratch" }, .inline_storage);
    try expectNoStorage(inlined, .backing_storage);
}

test "a copied aggregate keeps every pointer it carries and withholds the conclusion" {
    const source: [:0]const u8 =
        \\const Inner = struct { data: *u32 };
        \\const Payload = struct { direct: *u32, value: Inner };
        \\const Pair = struct { first: *u32, second: *u32 };
        \\fn borrow(payload: Payload) Payload { return payload; }
        \\fn copyPair(pair: Pair) Pair { return pair; }
        \\fn run(borrowed: Payload, pair: Pair) void {
        \\    _ = borrow(borrowed);
        \\    _ = copyPair(pair);
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    // The pointers a copied value carries ARE named — payload storage, under
    // the field of the copy that holds them and as deeply as the copy nests
    // them — but a copied payload is not an origin this query vouches for, so
    // the answer stays incomplete.
    const payload = try returnedStorageOf(cache, callNamed(typed.tree(), "borrow") orelse return error.TestExpectedCall);
    try std.testing.expect(!payload.complete);
    try std.testing.expectEqual(@as(usize, 2), payload.alternatives.len);
    _ = try expectAlternative(
        payload,
        .{ .param = 0, .path = "direct" },
        .payload_value,
        .payload_storage,
        "direct",
    );
    _ = try expectAlternative(
        payload,
        .{ .param = 0, .path = "value.data" },
        .payload_value,
        .payload_storage,
        "value.data",
    );
    try expectNoStorage(payload, .backing_storage);
    try expectNoStorage(payload, .inline_storage);
    // Every sibling pointer is represented even while the answer is withheld.
    const pair = try returnedStorageOf(cache, callNamed(typed.tree(), "copyPair") orelse return error.TestExpectedCall);
    try std.testing.expect(!pair.complete);
    try std.testing.expectEqual(@as(usize, 2), pair.alternatives.len);
    _ = try expectAlternative(pair, .{ .param = 0, .path = "first" }, .payload_value, .payload_storage, "first");
    _ = try expectAlternative(pair, .{ .param = 0, .path = "second" }, .payload_value, .payload_storage, "second");
    try expectNoStorage(pair, .backing_storage);
}

test "an aggregate literal of two direct borrows is complete and names both" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []u32, scratch: [4]u32 };
        \\const Pair = struct { backed: *u32, inlined: *u32 };
        \\fn pair(box: *Box) Pair {
        \\    return .{ .backed = &box.slots[0], .inlined = &box.scratch[0] };
        \\}
        \\fn run(box: *Box) void { _ = pair(box); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const returned = try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "pair") orelse return error.TestExpectedCall,
    );
    // Each field of the literal is a direct borrow, named by the field of the
    // RESULT that carries it, and there is nothing left to conclude.
    try std.testing.expect(returned.complete);
    try std.testing.expectEqual(@as(usize, 2), returned.alternatives.len);
    _ = try expectAlternative(
        returned,
        .{ .param = 0, .path = "slots" },
        .cell_address,
        .backing_storage,
        "backed",
    );
    _ = try expectAlternative(
        returned,
        .{ .param = 0, .path = "scratch" },
        .cell_address,
        .inline_storage,
        "inlined",
    );
}

test "a scalar copied out of a formal is complete and borrows nothing" {
    const source: [:0]const u8 =
        \\const Count = struct { value: u32 };
        \\fn scale(count: u32) u32 { return count; }
        \\fn pack(count: u32) Count { return .{ .value = count }; }
        \\fn run(count: u32) void {
        \\    _ = scale(count);
        \\    _ = pack(count);
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    // A by-value copy of an address-free formal reaches nothing at all, and
    // the answer says so outright instead of staying quiet about it.
    try expectNoBorrow(try returnedStorageOf(
        cache,
        callNamed(typed.tree(), "scale") orelse return error.TestExpectedCall,
    ));
    try expectNoBorrow(try returnedStorageOf(
        cache,
        callNamed(typed.tree(), "pack") orelse return error.TestExpectedCall,
    ));
}

test "a helper's nested field and a borrowed sibling are both named and a rebinding makes the answer incomplete" {
    const source: [:0]const u8 =
        \\const Inner = struct { items: []u32 };
        \\const Outer = struct { inner: Inner, spare: []u32 };
        \\fn itemsOf(inner: *Inner) []u32 { return inner.items; }
        \\fn gather(outer: *Outer) []u32 {
        \\    if (outer.inner.items.len == 0) {
        \\        return outer.spare;
        \\    } else if (outer.spare.len == 0) {
        \\        return itemsOf(&outer.inner);
        \\    } else {
        \\        var moved = itemsOf(&outer.inner);
        \\        moved = outer.spare;
        \\        return moved;
        \\    }
        \\}
        \\fn run(state: *Outer) void { _ = state.gather(); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const returned = try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "gather") orelse return error.TestExpectedCall,
    );
    // Every alias the body can hand back is represented, in the callee's own
    // formal coordinates: the field a helper reaches, and the sibling this
    // aggregate already holds.
    try std.testing.expect(!returned.complete);
    try std.testing.expectEqual(@as(usize, 2), returned.alternatives.len);
    _ = try expectAlternative(
        returned,
        .{ .param = 0, .path = "inner.items" },
        .pointer_value,
        .backing_storage,
        "",
    );
    _ = try expectAlternative(
        returned,
        .{ .param = 0, .path = "spare" },
        .pointer_value,
        .backing_storage,
        "",
    );
    // The aggregate itself is never named: only the field that carries it.
    try expectNoAlternative(returned, 0, "inner");
}

test "an aggregate result names the borrow under the field of the result that carries it" {
    const source: [:0]const u8 =
        \\const Inner = struct { items: []u32 };
        \\const Pair = struct { first: []u32, second: []u32 };
        \\fn itemsOf(inner: *Inner) []u32 { return inner.items; }
        \\fn gather(inner: *Inner, spare: []u32) Pair {
        \\    return .{ .first = itemsOf(inner), .second = spare };
        \\}
        \\fn firstOf(inner: *Inner, spare: []u32) []u32 { return gather(inner, spare).first; }
        \\fn run(inner: *Inner, spare: []u32) void { _ = firstOf(inner, spare); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    const gathered = try returnedStorageOf(
        cache,
        callNamed(typed.tree(), "gather") orelse return error.TestExpectedCall,
    );
    // The aggregate hands back both borrows, each under the RESULT field that
    // carries it rather than under a field of a formal.
    try std.testing.expect(gathered.complete);
    try std.testing.expectEqual(@as(usize, 2), gathered.alternatives.len);
    _ = try expectAlternative(
        gathered,
        .{ .param = 0, .path = "items" },
        .pointer_value,
        .backing_storage,
        "first",
    );
    _ = try expectAlternative(
        gathered,
        .{ .param = 1, .path = "" },
        .pointer_value,
        .backing_storage,
        "second",
    );
    // A caller that selects ONE of those fields reads that field's owner
    // alone, and the result path it travelled is already consumed.
    _ = try expectOnlyAlternative(
        try returnedStorageOf(cache, callNamed(typed.tree(), "firstOf") orelse return error.TestExpectedCall),
        .{ .param = 0, .path = "items" },
        .pointer_value,
        .backing_storage,
        "",
    );
}

test "storage a callee copied into its own frame cannot be named relative to a formal" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    scratch: [4]u32,
        \\    fn copied(self: *Slots) *u32 {
        \\        const copy = self.scratch;
        \\        return &copy[0];
        \\    }
        \\};
        \\fn run(grid: *Slots) void { _ = grid.copied(); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    // `copy` is the callee's own frame storage: the answer is not the formal's
    // cell, and no private origin may be invented for it either.
    try expectUnknown(try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "copied") orelse return error.TestExpectedCall,
    ));
}

test "unknown integer bits do not prove a reconstructed pointer independent" {
    const source: [:0]const u8 =
        \\const Cell = struct { address: usize };
        \\fn load(cell: *Cell) *u32 { return @ptrFromInt(cell.address); }
        \\fn run(cell: *Cell) void { _ = load(cell); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    // The integer source does not identify the returned pointer's allocation.
    try expectUnknown(try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "load") orelse return error.TestExpectedCall,
    ));
}

test "a snapshot taken before a formal's own path was rewritten has no provable origin" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    fn swap(self: *Slots, other: []u32) []u32 {
        \\        const snapshot = self.slots;
        \\        self.slots = other;
        \\        return snapshot;
        \\    }
        \\};
        \\fn run(grid: *Slots, other: []u32) void { _ = grid.swap(other); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    // The path `slots` names a different header after the body ran, so the
    // snapshot cannot be read as a borrow of it.
    try expectUnknown(try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "swap") orelse return error.TestExpectedCall,
    ));
}

test "a bodyless declaration returns no storage at all" {
    const source: [:0]const u8 =
        \\extern "c" fn fill(bytes: []u8) void;
        \\fn run(bytes: []u8) void { fill(bytes); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    // A record of a declaration is still an identity; the absence of a body
    // is never a promise that nothing was lent.
    try expectUnknown(try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "fill") orelse return error.TestExpectedCall,
    ));
}

test "a cycle in the return path is unknown rather than an error" {
    const source: [:0]const u8 =
        \\const Node = struct { items: []u32 };
        \\fn ping(node: *Node) []u32 { return pong(node); }
        \\fn pong(node: *Node) []u32 { return ping(node); }
        \\fn run(entry: *Node) void { _ = entry.ping(); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    // The recursion is cut, not reported as a resource failure: a caller
    // still has no answer, and no part of one either.
    try expectUnknown(try returnedStorageOf(
        typed.cache,
        callNamed(typed.tree(), "ping") orelse return error.TestExpectedCall,
    ));
}

test "an owner lands on the caller's own argument expression" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    fn view(self: *Slots, index: usize) []u32 { return self.slots[index .. index + 1]; }
        \\};
        \\fn run(grid: *Slots) void { _ = grid.view(1); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    const token = callNamed(typed.tree(), "view") orelse return error.TestExpectedCall;
    const alternative = try expectOnlyAlternative(
        try returnedStorageOf(cache, token),
        .{ .param = 0, .path = "slots" },
        .pointer_value,
        .backing_storage,
        "",
    );
    // The consumer's own question is answerable: formal zero of the getter is
    // the receiver this call site handed it, and the owner's path rides along.
    try expectMapping(cache, try actualOf(cache, token), alternative, "grid", "slots");
}

test "an owner reached through the caller's receiver keeps that receiver's own coordinate" {
    const source: [:0]const u8 =
        \\const Slots = struct {
        \\    slots: []u32,
        \\    fn view(self: *Slots, index: usize) []u32 { return self.slots[index .. index + 1]; }
        \\};
        \\const Holder = struct { grid: Slots };
        \\fn run(holder: *Holder) void { _ = holder.grid.view(2); }
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    const cache = typed.cache;
    const token = callNamed(typed.tree(), "view") orelse return error.TestExpectedCall;
    const alternative = try expectOnlyAlternative(
        try returnedStorageOf(cache, token),
        .{ .param = 0, .path = "slots" },
        .pointer_value,
        .backing_storage,
        "",
    );
    // The mapped node is the receiver EXPRESSION the call site wrote, so the
    // caller's own storage is `holder.grid.slots`, not some formal of the
    // getter.
    try expectMapping(cache, try actualOf(cache, token), alternative, "holder.grid", "slots");
}

test "a real SDK map hands back a pointer into the table this call site handed it" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Map = std.AutoHashMap(u32, u32);
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    var entries = Map.init(gpa);
        \\    defer entries.deinit();
        \\    try entries.put(1, 2);
        \\    _ = entries.getPtr(3);
        \\    _ = entries.getPtrAdapted(@as(u32, 4), std.hash_map.AutoContext(u32){});
        \\    _ = entries.get(5);
        \\}
    ;
    const gpa = std.testing.allocator;
    const typed = try Typed.init(gpa, source);
    defer typed.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), typed.tree().errors.len);
    typed.cache.module_id = typed.resolver.handle.module;
    const cache = typed.cache;
    // Each accessor is found by the argument it is handed, never by a getter
    // name this query might have learned.  Both name a declaration written in
    // the toolchain's own hash map, not a spelling this file owns.
    const pointer_token = callTaking(typed.tree(), "3") orelse return error.TestExpectedCall;
    const pointer = try actualOf(cache, pointer_token);
    try std.testing.expect(pointer.callee.tree != typed.tree());
    try std.testing.expect(try typed.resolver.declaredInToolchainFile(pointer.callee.handle, "/std/hash_map.zig"));
    // The pointer it returns addresses a cell of the map itself, so the owner
    // is that receiver and the whole of its storage: nothing of the private
    // header layout the compiler walks to reach it leaks into the answer.
    const pointer_storage = try expectOnlyAlternative(
        try returnedStorageOf(cache, pointer_token),
        .{ .param = 0, .path = "" },
        .cell_address,
        .backing_storage,
        "",
    );
    try expectMapping(cache, pointer, pointer_storage, "entries", "");
    // The adapted accessor answers with the same cell of the same map.
    const adapted_token = callTaking(typed.tree(), "@as(u32, 4)") orelse return error.TestExpectedCall;
    const adapted = try actualOf(cache, adapted_token);
    try std.testing.expect(adapted.callee.tree != typed.tree());
    try std.testing.expect(try typed.resolver.declaredInToolchainFile(adapted.callee.handle, "/std/hash_map.zig"));
    _ = try expectOnlyAlternative(
        try returnedStorageOf(cache, adapted_token),
        .{ .param = 0, .path = "" },
        .cell_address,
        .backing_storage,
        "",
    );
    // A copied value, by contrast, is answered outright: the `u32` this map
    // copies is address-free, so nothing was lent to the caller.
    const copied_token = callTaking(typed.tree(), "5") orelse return error.TestExpectedCall;
    const copied = try actualOf(cache, copied_token);
    try std.testing.expect(copied.callee.tree != typed.tree());
    try std.testing.expect(try typed.resolver.declaredInToolchainFile(copied.callee.handle, "/std/hash_map.zig"));
    try expectNoBorrow(try returnedStorageOf(cache, copied_token));
}

test "a copied pointer element carries an unknown pointee rather than its table cell" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []*u32 };
        \\fn copied(box: *Box) *u32 { return box.slots[0]; }
        \\fn use(box: *Box) void { _ = copied(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const result = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copied").?);
    try std.testing.expect(!result.complete);
    _ = try expectAlternative(result, .{ .param = 0, .path = "slots" }, .payload_value, .payload_storage, "");
    try expectNoStorage(result, .backing_storage);
    try expectNoStorage(result, .inline_storage);
}

test "assigned aggregate pointers remain visible without claiming full array coverage" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []u32 };
        \\const View = struct { pointers: [2][*]u32 };
        \\fn view(box: *Box) View {
        \\    var result: View = .{ .pointers = undefined };
        \\    var pointer: [*]u32 = box.slots.ptr;
        \\    for ([_]usize{ 0, 1 }) |index| {
        \\        result.pointers[index] = pointer;
        \\        pointer += 1;
        \\    }
        \\    return result;
        \\}
        \\fn use(box: *Box) void { _ = view(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const result = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "view").?);
    try std.testing.expect(!result.complete);
    _ = try expectAlternative(result, .{ .param = 0, .path = "slots" }, .pointer_value, .backing_storage, "pointers");
}

test "returned storage exhaustion keeps its named origin and shared allowance" {
    const source: [:0]const u8 =
        \\fn borrowed(bytes: []u32) *u32 { return &bytes[0]; }
        \\fn use(bytes: []u32) void { _ = borrowed(bytes); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    budget.clear();
    defer budget.clear();
    var remaining: u32 = 0;
    const token = callNamed(typed.tree(), "borrowed").?;
    try std.testing.expectError(error.AnalysisBudgetExceeded, returnedStorageAt(typed.cache, token, .{ .remaining = &remaining }));
    try std.testing.expectEqual(@as(u32, 0), remaining);
    const diagnostic = budget.take() orelse return error.TestExpectedBudget;
    try std.testing.expectEqual(budget.Limit.return_storage_work, diagnostic.limit);
    try std.testing.expectEqual(FileCache.actual_query_work_limit, diagnostic.limit_value);
}

test "an undefined pointer is unknown rather than a completed copied value" {
    const source: [:0]const u8 =
        \\fn unknown(bytes: []u32) *u32 { _ = bytes; return undefined; }
        \\fn use(bytes: []u32) void { _ = unknown(bytes); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectUnknown(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "unknown").?));
}

test "a canonical constant condition excludes only its unreachable pointer return" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []u32, address: usize };
        \\fn selected(box: *Box) *u32 {
        \\    return if (true) &box.slots[0] else @ptrFromInt(box.address);
        \\}
        \\fn use(box: *Box) void { _ = selected(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    _ = try expectOnlyAlternative(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "selected").?),
        .{ .param = 0, .path = "slots" }, .cell_address, .backing_storage, "");
}

test "a pointer field copy is a pointee and indexing its array addresses a backing cell" {
    const source: [:0]const u8 =
        \\const Box = struct { pointer: *u32, slots: *[4]u32, scratch: [4]u32 };
        \\fn copied(box: *Box) *u32 { return box.pointer; }
        \\fn cell(box: *Box) *u32 { return &box.slots[0]; }
        \\fn inlineAlias(box: *Box) *u32 {
        \\    const view = &box.scratch;
        \\    return &view[0];
        \\}
        \\fn use(box: *Box) void { _ = copied(box); _ = cell(box); _ = inlineAlias(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const copied = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copied").?);
    try std.testing.expect(!copied.complete);
    _ = try expectAlternative(copied, .{ .param = 0, .path = "pointer" }, .payload_value, .payload_storage, "");
    _ = try expectOnlyAlternative(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "cell").?),
        .{ .param = 0, .path = "slots" }, .cell_address, .backing_storage, "");
    _ = try expectOnlyAlternative(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "inlineAlias").?),
        .{ .param = 0, .path = "scratch" }, .cell_address, .inline_storage, "");
}

test "mapping a returned aggregate pointer consumes its formal field selector" {
    const source: [:0]const u8 =
        \\const Box = struct { slots: []u32 };
        \\const View = struct { pointers: [2][*]u32 };
        \\fn assembled(box: *Box) View {
        \\    var result: View = .{ .pointers = undefined };
        \\    var pointer: [*]u32 = box.slots.ptr;
        \\    for ([_]usize{ 0, 1 }) |index| {
        \\        result.pointers[index] = pointer;
        \\        pointer += 1;
        \\    }
        \\    return result;
        \\}
        \\fn projected(view: View) []u32 { return view.pointers[0][0..1]; }
        \\fn borrowed(box: *Box) []u32 { return projected(assembled(box)); }
        \\fn use(box: *Box) void { _ = borrowed(box); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "borrowed").?);
    try std.testing.expect(!returned.complete);
    _ = try expectAlternative(returned, .{ .param = 0, .path = "slots" },
        .pointer_value, .backing_storage, "");
    for (returned.alternatives) |alternative|
        try std.testing.expect(!std.mem.endsWith(u8, alternative.owner.path, ".pointers"));
}

test "a declared scalar result remains a copied value across an undefined zero-size branch" {
    const source: [:0]const u8 =
        \\fn copied(comptime V: type, value: V) V {
        \\    return if (@sizeOf(V) == 0) undefined else value;
        \\}
        \\fn use() void { _ = copied(u32, @as(u32, 5)); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "copied").?);
    try std.testing.expect(returned.complete);
    try std.testing.expectEqual(@as(usize, 0), returned.alternatives.len);
}

test "a real SDK array map pointer return is never classified as a copied scalar" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const Map = std.array_hash_map.Auto(u32, u32);
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    var entries: Map = .empty;
        \\    defer entries.deinit(gpa);
        \\    try entries.put(gpa, 1, 2);
        \\    _ = entries.getPtr(3);
        \\    _ = entries.get(4);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    typed.cache.module_id = typed.resolver.handle.module;
    const pointer_token = callTaking(typed.tree(), "3") orelse return error.TestExpectedCall;
    const actual = try actualOf(typed.cache, pointer_token);
    try std.testing.expect(actual.callee.tree != typed.tree());
    try std.testing.expect(try typed.resolver.declaredInToolchainFile(actual.callee.handle, "/std/array_hash_map.zig"));
    const pointer = try returnedStorageOf(typed.cache, pointer_token);
    // Unknown coverage still requires a borrow. It must not become the
    // completed-empty answer that lets copied address-free values stay quiet.
    try std.testing.expect(!pointer.complete or pointer.alternatives.len != 0);
    for (pointer.alternatives) |alternative| {
        try std.testing.expectEqual(Projection.cell_address, alternative.projection);
        try std.testing.expectEqual(Storage.backing_storage, alternative.storage);
    }
    const copied = try returnedStorageOf(typed.cache,
        callTaking(typed.tree(), "4") orelse return error.TestExpectedCall);
    try std.testing.expect(copied.complete);
    try std.testing.expectEqual(@as(usize, 0), copied.alternatives.len);
}

test "explicitly encoded address bits are not discharged by their scalar return type" {
    const source: [:0]const u8 =
        \\fn encoded(pointer: *u32) usize { return @intFromPtr(pointer); }
        \\fn use(pointer: *u32) void { _ = encoded(pointer); }
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    const returned = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "encoded").?);
    try std.testing.expect(!returned.complete or returned.alternatives.len != 0);
}

test "array child values are classified through their canonical types" {
    const source: [:0]const u8 =
        \\fn scalar(values: [2]u32) [2]u32 { return values; }
        \\fn pointers(values: [2]*u32) [2]*u32 { return values; }
        \\fn use(scalars: [2]u32, addresses: [2]*u32) void {
        \\    _ = scalar(scalars);
        \\    _ = pointers(addresses);
        \\}
    ;
    const typed = try Typed.init(std.testing.allocator, source);
    defer typed.deinit(std.testing.allocator);
    try expectNoBorrow(try returnedStorageOf(typed.cache, callNamed(typed.tree(), "scalar").?));
    const pointer_array = try returnedStorageOf(typed.cache, callNamed(typed.tree(), "pointers").?);
    try std.testing.expect(!pointer_array.complete);
    _ = try expectAlternative(pointer_array, .{ .param = 0, .path = "" },
        .payload_value, .payload_storage, "");
}
