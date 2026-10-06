//! Positive storage-disjointness queries over the current source snapshot.
//! Import this module directly; the cache owns reused declaration and binding facts.

const std = @import("std");
const Ast = std.zig.Ast;
const FileCache = @import("file_cache.zig").FileCache;
const tokens = @import("../ast/tokens.zig");
const fresh = @import("fresh_storage.zig");
const bindings_mod = @import("../model/local_bindings.zig");
const type_query = @import("../model/type_query.zig");
const budget_mod = @import("../budget.zig");
const call_summary_mod = @import("call_summary.zig");
const engine = @import("type_engine");
const Iterator = engine.AstIterator;

/// A call-site expression, optionally projected through an actual formal effect path.
/// `node` belongs to `cache.tree`; `path` borrows dot-separated field names.
pub const StorageSelection = struct {
    node: Ast.Node.Index,
    path: []const u8 = "",
};

/// Backing storage is the collection allocation, not headers stored in its cells.
/// Reachable storage also includes stored keys' and values' transitive allocations.
pub const Domain = enum { backing_storage, reachable_storage };

/// Optional context of an enclosing semantic query. `frame` borrows the original
/// resolver; all input nodes still belong to `cache.tree`. A non-null `remaining`
/// borrows that query's counter: own AST nodes/edges and fresh work decrement it,
/// and a bounded canonical type/declaration query costs one proof edge. Null
/// starts one 50,000-step root allowance; recursive callers pass the same pointer.
pub const QueryContext = struct {
    frame: ?engine.TypeResolver.ResolutionFrame = null,
    remaining: ?*u32 = null,
};

/// Resource failures are not negative alias verdicts.  The set is the
/// cache's own summary set: this query reads call summaries, and reading one
/// models the callee's document first, so a source `std.zig.Ast` cannot
/// address fails this query the same way an exhausted allowance does.
pub const BudgetError = @import("file_cache.zig").SummaryError;

const work_limit: u32 = call_summary_mod.actual_query_work_limit;
const max_path = 16;
const max_origins = 32;
const no_parent = std.math.maxInt(u32);

/// False means a positively proved private construction cannot share the selected
/// storage at this call. Same origins, incoming fields, copies, publication,
/// unsupported writes and cycles answer true. No spelling establishes disjointness.
/// One counter covers this query's AST work and its fresh-producer work; existing
/// canonical type/declaration queries retain their own bounds. Errors propagate
/// without caching a negative verdict. The caller owns no result allocation.
pub fn mayShareStorageAt(
    cache: *FileCache,
    at_node: Ast.Node.Index,
    left: StorageSelection,
    right: StorageSelection,
    domain: Domain,
    context: QueryContext,
) BudgetError!bool {
    var remaining: u32 = work_limit;
    var query: Query = .{
        .root_cache = cache, .at_node = at_node,
        .remaining = context.remaining orelse &remaining, .resolution = context.frame,
    };
    return query.run(left, right, domain) catch |err| {
        if (err == error.AnalysisBudgetExceeded and query.remaining.?.* == 0) {
            return query.failure();
        }
        return err;
    };
}

/// Internal lifetime guard after a producer has proved construction. This does
/// not grant freshness, privacy, or disjointness. Local header aliases retain
/// their actual shared allocation identity through the successful handoff.
/// A null counter adds no allowance or cap to the caller's existing fresh walk.
pub fn allocationSurvivesHandoff(
    cache: *FileCache,
    value_node: Ast.Node.Index,
    boundary: Ast.TokenIndex,
    context: QueryContext,
) BudgetError!bool {
    var query: Query = .{
        .root_cache = cache, .at_node = value_node,
        .remaining = context.remaining, .resolution = context.frame,
        .lifetime_only = true,
    };
    return query.survivesHandoff(value_node, boundary);
}

const Path = struct {
    fields: [max_path][]const u8 = undefined,
    len: usize = 0,

    fn append(self: *Path, name: []const u8) bool {
        if (self.len == max_path or name.len == 0) return false;
        self.fields[self.len] = name;
        self.len += 1;
        return true;
    }

    fn eql(a: Path, b: Path) bool {
        if (a.len != b.len) return false;
        for (a.fields[0..a.len], b.fields[0..b.len]) |x, y| {
            if (!std.mem.eql(u8, x, y)) return false;
        }
        return true;
    }

    fn overlaps(a: Path, b: Path) bool {
        const common = @min(a.len, b.len);
        for (a.fields[0..common], b.fields[0..common]) |x, y| {
            if (!std.mem.eql(u8, x, y)) return false;
        }
        return true;
    }
};

const Root = struct {
    binding: *const bindings_mod.Binding,
    path: Path,
    addressed: bool = false,
};
const Active = struct { cache: *FileCache, token: Ast.TokenIndex, path: Path };

const Frame = struct {
    cache: *FileCache,
    parents: []u32,
    owns_parents: bool = false,
    declaration: Ast.Node.Index,
    body: Ast.Node.Index,
    bindings: *const bindings_mod.LocalBindings,
    resolution: ?engine.TypeResolver.ResolutionFrame = null,
    return_boundary: ?Ast.TokenIndex = null,

    fn init(query: *Query, cache: *FileCache, position: Ast.Node.Index) BudgetError!?Frame {
        const tree = cache.tree;
        const parents = try cache.gpa.alloc(u32, tree.nodes.len);
        errdefer cache.gpa.free(parents);
        @memset(parents, no_parent);
        for (tree.nodes.items(.tag), 0..) |_, raw| {
            try query.charge();
            const node: Ast.Node.Index = @enumFromInt(raw);
            var children = Iterator.init(tree, node);
            while (children.next(tree)) |child| {
                try query.charge();
                parents[@intFromEnum(child)] = @intCast(raw);
            }
        }
        var frame = (try Frame.at(query, cache, parents, position)) orelse {
            cache.gpa.free(parents);
            return null;
        };
        frame.owns_parents = true;
        return frame;
    }

    fn at(
        query: *Query, cache: *FileCache, parents: []u32, position: Ast.Node.Index,
    ) BudgetError!?Frame {
        const tree = cache.tree;
        var node = position;
        const declaration = while (true) {
            try query.charge();
            if (tree.nodeTag(node) == .fn_decl) break node;
            const parent = parents[@intFromEnum(node)];
            if (parent == no_parent) return null;
            node = @enumFromInt(parent);
        };
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
        const body = tokens.bodyOf(tree, declaration) orelse return null;
        try query.charge();
        const bindings = try cache.localBindings(proto, body);
        return .{
            .cache = cache, .parents = parents, .declaration = declaration,
            .body = body, .bindings = bindings,
        };
    }

    fn deinit(self: Frame) void {
        if (self.owns_parents) self.cache.gpa.free(self.parents);
    }

    fn freshWalk(self: Frame, query: *Query, claim: FileCache.TokenRange) fresh.FreshWalk {
        return .{
            .claim = .{ .first = claim.first, .last = claim.last }, .depth = 0,
            .remaining = query.remaining, .frame = self.resolution,
        };
    }

    fn parentOf(self: Frame, node: Ast.Node.Index) ?Ast.Node.Index {
        const raw = self.parents[@intFromEnum(node)];
        return if (raw == no_parent) null else @enumFromInt(raw);
    }

    fn bindingAt(self: Frame, query: *Query, node: Ast.Node.Index) BudgetError!?*const bindings_mod.Binding {
        const token = self.cache.tree.nodeMainToken(node);
        for (self.bindings.items) |_| try query.charge();
        return self.bindings.findAt(self.cache.tree.tokenSlice(token), token);
    }

    fn root(self: Frame, query: *Query, selection: StorageSelection) BudgetError!?Root {
        const tree = self.cache.tree;
        var reverse: Path = .{};
        var node = selection.node;
        var addressed = false;
        while (true) {
            try query.charge();
            switch (tree.nodeTag(node)) {
                .identifier => break,
                .field_access => {
                    const access = tree.nodeData(node).node_and_token;
                    if (!reverse.append(tree.tokenSlice(access[1]))) return null;
                    node = access[0];
                },
                .address_of => {
                    addressed = true;
                    node = tree.nodeData(node).node;
                },
                .deref, .@"try" => node = tree.nodeData(node).node,
                .grouped_expression, .unwrap_optional =>
                    node = tree.nodeData(node).node_and_token[0],
                else => return null,
            }
        }
        var path: Path = .{};
        var index = reverse.len;
        while (index > 0) {
            try query.charge();
            index -= 1;
            if (!path.append(reverse.fields[index])) return null;
        }
        if (selection.path.len != 0) {
            var parts = std.mem.splitScalar(u8, selection.path, '.');
            while (parts.next()) |part| {
                try query.charge();
                if (!path.append(part)) return null;
            }
        }
        const binding = (try self.bindingAt(query, node)) orelse return null;
        return .{ .binding = binding, .path = path, .addressed = addressed };
    }

    fn owns(self: Frame, query: *Query, node: Ast.Node.Index) BudgetError!bool {
        var current = node;
        while (self.parentOf(current)) |parent| {
            try query.charge();
            if (self.cache.tree.nodeTag(parent) == .fn_decl) return parent == self.declaration;
            current = parent;
        }
        return false;
    }

    fn deferred(
        self: Frame, query: *Query, node: Ast.Node.Index, boundary: Ast.TokenIndex,
    ) BudgetError!bool {
        var current = node;
        var found_defer = false;
        var always_runs = false;
        while (self.parentOf(current)) |parent| {
            try query.charge();
            switch (self.cache.tree.nodeTag(parent)) {
                .@"defer" => {
                    found_defer = true;
                    always_runs = true;
                },
                .@"errdefer" => found_defer = true,
                .block, .block_semicolon, .block_two, .block_two_semicolon => {
                    if (found_defer) {
                        // A factory's successful returned value is not private
                        // until its ordinary pending defers have run.
                        if (always_runs and self.cache.tree.tokenTag(boundary) == .keyword_return)
                            return false;
                        return self.cache.tree.lastToken(parent) >= boundary;
                    }
                },
                .fn_decl => return false,
                else => {},
            }
            current = parent;
        }
        return false;
    }
};

const Query = struct {
    root_cache: *FileCache,
    at_node: Ast.Node.Index,
    remaining: ?*u32,
    resolution: ?engine.TypeResolver.ResolutionFrame = null,
    active: [max_origins]Active = undefined,
    active_len: usize = 0,
    calls: [max_origins]struct { tree: *const Ast, declaration: Ast.Node.Index } = undefined,
    call_len: usize = 0,
    value_depth: u8 = 0,
    readonly_address: bool = false,
    lifetime_only: bool = false,
    lifetime_aliases: [max_origins]Root = undefined,
    lifetime_alias_count: usize = 0,
    lifetime_copy_sources: [max_origins]u32 = @splat(0),

    fn failure(self: *Query) BudgetError {
        const tree = self.root_cache.tree;
        const token = tree.firstToken(self.at_node);
        return budget_mod.fail(.{
            .limit = .storage_alias_work, .limit_value = work_limit,
            .reached = work_limit, .byte = tree.tokens.items(.start)[token],
        });
    }

    fn charge(self: *Query) BudgetError!void {
        const remaining = self.remaining orelse return;
        if (remaining.* == 0) return self.failure();
        remaining.* -= 1;
    }

    fn run(self: *Query, left: StorageSelection, right: StorageSelection, domain: Domain) BudgetError!bool {
        var frame = (try Frame.init(self, self.root_cache, self.at_node)) orelse return true;
        defer frame.deinit();
        frame.resolution = self.resolution;
        if (try frame.deferred(self, self.at_node, frame.cache.tree.firstToken(self.at_node)))
            return true;
        const a = try frame.root(self, left);
        const b = try frame.root(self, right);
        const boundary = frame.cache.tree.firstToken(self.at_node);
        if (a != null and b != null and a.?.binding.name_token == b.?.binding.name_token) {
            if (Path.overlaps(a.?.path, b.?.path)) return true;
            // Distinct field spellings do not prove distinct storage within
            // one owner. Each selected origin must independently be private.
            return !(try self.private(&frame, a.?, boundary, domain, null) and
                try self.private(&frame, b.?, boundary, domain, null));
        }
        if (b) |root| {
            if (try self.private(&frame, root, boundary, domain, null)) return false;
        }

        if (a) |root| {
            if (try self.private(&frame, root, boundary, domain, null)) return false;
        }
        return true;
    }
    fn addLifetimeAlias(self: *Query, root: Root) BudgetError!bool {
        for (self.lifetime_aliases[0..self.lifetime_alias_count]) |known| {
            try self.charge();
            if (known.binding.name_token == root.binding.name_token and
                Path.eql(known.path, root.path)) return true;
        }
        if (self.lifetime_alias_count == max_origins) return false;
        self.lifetime_aliases[self.lifetime_alias_count] = root;
        self.lifetime_alias_count += 1;
        return true;
    }

    fn lifetimeSeed(self: *Query, frame: *Frame, node: Ast.Node.Index, depth: u8) BudgetError!bool {
        try self.charge();
        if (depth == max_origins) return false;
        if (try frame.root(self, .{ .node = node })) |root|
            return self.addLifetimeAlias(root);
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .@"try", .address_of, .deref =>
                return self.lifetimeSeed(frame, tree.nodeData(node).node, depth + 1),
            .grouped_expression, .unwrap_optional =>
                return self.lifetimeSeed(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            .slice, .slice_open, .slice_sentinel =>
                return self.lifetimeSeed(frame, tree.fullSlice(node).?.ast.sliced, depth + 1),
            .call, .call_one, .call_comma, .call_one_comma,
            .enum_literal, .field_access, .number_literal, .char_literal,
            .string_literal, .multiline_string_literal => return true,
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullStructInit(&buffer, node)) |literal| {
            for (literal.ast.fields) |field| {
                if (!try self.lifetimeSeed(frame, field, depth + 1)) return false;
            }
            return true;
        }
        if (tree.fullArrayInit(&buffer, node)) |literal| {
            for (literal.ast.elements) |element| {
                if (!try self.lifetimeSeed(frame, element, depth + 1)) return false;
            }
            return true;
        }
        return false;
    }

    fn pathTail(self: *Query, base: Path, whole: Path, destination: Path) BudgetError!?Path {
        if (base.len > whole.len or !Path.overlaps(base, whole)) return null;
        var result = destination;
        for (whole.fields[base.len..whole.len]) |field| {
            try self.charge();
            if (!result.append(field)) return null;
        }
        return result;
    }

    fn lifetimeLink(self: *Query, target: Root, source: Root) BudgetError!bool {
        // Actual lexical initialization must descend to an existing binding;
        // forward/self dependencies cannot manufacture an alive allocation.
        const count = self.lifetime_alias_count;
        var related = false;
        for (self.lifetime_aliases[0..count]) |known| {
            try self.charge();
            if (known.binding.name_token == target.binding.name_token and
                Path.overlaps(known.path, target.path)) {
                if (source.binding.name_token >= target.binding.name_token) return false;
                related = true;
                const path = (try self.pathTail(target.path, known.path, source.path)) orelse source.path;
                if (!try self.addLifetimeAlias(.{ .binding = source.binding, .path = path })) return false;
            }
            if (known.binding.name_token == source.binding.name_token and
                Path.overlaps(known.path, source.path)) {
                if (source.binding.name_token >= target.binding.name_token) return false;
                related = true;
                const path = (try self.pathTail(source.path, known.path, target.path)) orelse target.path;
                if (!try self.addLifetimeAlias(.{ .binding = target.binding, .path = path })) return false;
            }
        }
        if (related and !source.addressed) {
            if (!try self.addLifetimeAlias(source) or !try self.addLifetimeAlias(target)) return false;
            var from: ?u5 = null;
            var to: ?u5 = null;
            for (self.lifetime_aliases[0..self.lifetime_alias_count], 0..) |alias, index| {
                try self.charge();
                if (alias.binding.name_token == source.binding.name_token and Path.eql(alias.path, source.path))
                    from = @intCast(index);
                if (alias.binding.name_token == target.binding.name_token and Path.eql(alias.path, target.path))
                    to = @intCast(index);
            }
            self.lifetime_copy_sources[to.?] |= @as(u32, 1) << from.?;
        }
        return true;
    }

    fn lifetimeLinks(
        self: *Query, frame: *Frame, node: Ast.Node.Index, target: Root, depth: u8,
    ) BudgetError!bool {
        try self.charge();
        if (depth == max_origins) return false;
        if (try frame.root(self, .{ .node = node })) |source|
            return self.lifetimeLink(target, source);
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .@"try", .address_of, .deref =>
                return self.lifetimeLinks(frame, tree.nodeData(node).node, target, depth + 1),
            .grouped_expression, .unwrap_optional =>
                return self.lifetimeLinks(frame, tree.nodeData(node).node_and_token[0], target, depth + 1),
            .slice, .slice_open, .slice_sentinel =>
                return self.lifetimeLinks(frame, tree.fullSlice(node).?.ast.sliced, target, depth + 1),
            .call, .call_one, .call_comma, .call_one_comma =>
                return self.lifetimeCallLinks(frame, node, target),
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullStructInit(&buffer, node)) |literal| {
            for (literal.ast.fields) |field| {
                const first = tree.firstToken(field);
                if (first < 2) return false;
                var child = target;
                if (!child.path.append(tree.tokenSlice(first - 2))) return false;
                if (!try self.lifetimeLinks(frame, field, child, depth + 1)) return false;
            }
            return true;
        }
        if (tree.fullArrayInit(&buffer, node)) |literal| {
            for (literal.ast.elements) |element| {
                if (!try self.lifetimeLinks(frame, element, target, depth + 1)) return false;
            }
        }
        return true;
    }

    fn survivesHandoff(self: *Query, value_node: Ast.Node.Index, boundary: Ast.TokenIndex) BudgetError!bool {
        var frame = (try Frame.init(self, self.root_cache, value_node)) orelse return false;
        defer frame.deinit();
        frame.resolution = self.resolution;
        if (try self.expressionAddressFree(&frame, value_node)) return true;
        frame.return_boundary = boundary;
        if (!try self.lifetimeSeed(&frame, value_node, 0)) return false;
        const tree = frame.cache.tree;
        var rounds: usize = 0;
        while (true) {
            const before = self.lifetime_alias_count;
            for (tree.nodes.items(.tag), 0..) |_, raw| {
                try self.charge();
                const node: Ast.Node.Index = @enumFromInt(raw);
                const declaration = tree.fullVarDecl(node) orelse continue;
                const name = declaration.ast.mut_token + 1;
                if (name >= boundary or !try frame.owns(self, node)) continue;
                const initializer_node = declaration.ast.init_node.unwrap() orelse continue;
                var binding: ?*const bindings_mod.Binding = null;
                for (frame.bindings.items) |*candidate| {
                    try self.charge();
                    if (candidate.name_token == name) {
                        binding = candidate;
                        break;
                    }
                }
                const target: Root = .{ .binding = binding orelse continue, .path = .{} };
                if (!try self.lifetimeLinks(&frame, initializer_node, target, 0)) return false;
            }
            if (self.lifetime_alias_count == before) break;
            rounds += 1;
            if (rounds == max_origins) return false;
        }
        for (self.lifetime_aliases[0..self.lifetime_alias_count]) |root| {
            if (!try self.unpublished(&frame, root, boundary, .backing_storage, null)) return false;
        }
        return true;
    }

    fn lifetimeAliasInitialization(self: *Query, frame: *Frame, use: Ast.Node.Index) BudgetError!bool {
        var node = use;
        while (frame.parentOf(node)) |parent| {
            try self.charge();
            if (frame.cache.tree.fullVarDecl(parent)) |declaration| {
                const initializer_node = declaration.ast.init_node.unwrap() orelse return false;
                if (node != initializer_node) return false;
                for (self.lifetime_aliases[0..self.lifetime_alias_count]) |alias| {
                    try self.charge();
                    if (alias.binding.name_token == declaration.ast.mut_token + 1) return true;
                }
                return false;
            }
            switch (frame.cache.tree.nodeTag(parent)) {
                .call, .call_one, .call_comma, .call_one_comma,
                .block, .block_semicolon, .block_two, .block_two_semicolon, .fn_decl => return false,
                else => node = parent,
            }
        }
        return false;
    }

    fn lifetimeCallLinks(self: *Query, frame: *Frame, node: Ast.Node.Index, target: Root) BudgetError!bool {
        var buffer: [1]Ast.Node.Index = undefined;
        const call = frame.cache.tree.fullCall(&buffer, node) orelse return false;
        var relevant = false;
        for (call.ast.params) |argument| {
            try self.charge();
            const root = (try frame.root(self, .{ .node = argument })) orelse continue;
            for (self.lifetime_aliases[0..self.lifetime_alias_count]) |alias| {
                try self.charge();
                if (root.binding.name_token == alias.binding.name_token and
                    Path.overlaps(root.path, alias.path)) relevant = true;
            }
        }
        if (frame.cache.tree.nodeTag(call.ast.fn_expr) == .field_access) {
            const receiver = frame.cache.tree.nodeData(call.ast.fn_expr).node_and_token[0];
            if (try frame.root(self, .{ .node = receiver })) |root| {
                for (self.lifetime_aliases[0..self.lifetime_alias_count]) |alias| {
                    try self.charge();
                    if (root.binding.name_token == alias.binding.name_token and
                        Path.overlaps(root.path, alias.path)) relevant = true;
                }
            }
        }
        if (!relevant) return true;
        try self.charge();
        const canonical = (try frame.cache.actualCallSummaryAt(
            fresh.calleeQueryToken(frame.cache.tree, call), frame.resolution,
        )) orelse return false;
        const summary = canonical.summary orelse return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration)
            orelse return false;
        var parameters = proto.iterate(canonical.callee.tree);
        var index: u32 = 0;
        while (parameters.next() != null) : (index += 1) {
            try self.charge();
            const dependency = summary.returnedParamDependency(index) orelse return false;
            if (!dependency) continue;
            var argument_buffer: [1]Ast.Node.Index = undefined;
            const argument = (try canonical.callArgumentFor(frame.cache, &argument_buffer, index))
                orelse return false;
            const source = (try frame.root(self, .{ .node = argument })) orelse return false;
            if (!try self.lifetimeLink(target, source)) return false;
        }
        return true;
    }

    fn expressionAddressFree(self: *Query, frame: *Frame, node: Ast.Node.Index) BudgetError!bool {
        try self.charge();
        const resolution = frame.resolution orelse
            (frame.cache.zls orelse return false).resolutionFrame();
        const ty = (resolution.typeOfNode(node) catch |err|
            return resourceFailure(err)) orelse return false;
        return fresh.actualTypeAddressFree(resolution, ty, 0, self.remaining);
    }

    fn lifetimeCallSafe(
        self: *Query, frame: *Frame, canonical: FileCache.ActualCallSummary, selected: Root,
    ) BudgetError!bool {
        const tree = frame.cache.tree;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, canonical.callee.call_node) orelse return false;
        const token = fresh.calleeQueryToken(tree, call);
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration)
            orelse return false;
        var parameters = proto.iterate(canonical.callee.tree);
        var index: u32 = 0;
        var found = false;
        while (parameters.next() != null) : (index += 1) {
            try self.charge();
            var argument_buffer: [1]Ast.Node.Index = undefined;
            const argument = (try canonical.callArgumentFor(frame.cache, &argument_buffer, index))
                orelse continue;
            const root = (try frame.root(self, .{ .node = argument })) orelse continue;
            if (root.binding.name_token != selected.binding.name_token or
                !Path.overlaps(root.path, selected.path)) continue;
            found = true;
            const begin = @min(root.path.len, selected.path.len);
            var bytes: usize = 0;
            for (selected.path.fields[begin..selected.path.len]) |field|
                bytes += field.len + @intFromBool(bytes != 0);
            const effect = query_effect: {
                var stack: [256]u8 = undefined;
                const path = if (bytes <= stack.len) stack[0..bytes] else try frame.cache.gpa.alloc(u8, bytes);
                defer if (bytes > stack.len) frame.cache.gpa.free(path);
                var used: usize = 0;
                for (selected.path.fields[begin..selected.path.len]) |field| {
                    try self.charge();
                    if (used != 0) {
                        path[used] = '.';
                        used += 1;
                    }
                    @memcpy(path[used..][0..field.len], field);
                    used += field.len;
                }
                break :query_effect (try frame.cache.callEffectAt(token, .{ .parameter = .{
                    .param = index, .path = path,
                } }, .{ .frame = frame.resolution, .remaining = self.remaining })) orelse return false;
            };
            switch (effect) {
                .read_only, .writes_without_invalidation => {},
                .may_invalidate, .unknown => return false,
            }
        }
        if (!found) return false;
        const global = (try frame.cache.callEffectAt(token, .unrooted, .{
            .frame = frame.resolution, .remaining = self.remaining,
        })) orelse return false;
        return global == .read_only or global == .writes_without_invalidation;
    }

    fn lifetimeCopyPredates(self: *Query, selected: Root, at: Ast.TokenIndex) BudgetError!bool {
        for (self.lifetime_aliases[0..self.lifetime_alias_count], 0..) |alias, target| {
            try self.charge();
            if (alias.binding.name_token == selected.binding.name_token or alias.binding.rhs_last >= at)
                continue;
            for (self.lifetime_aliases[0..self.lifetime_alias_count], 0..) |source, index| {
                try self.charge();
                if (source.binding.name_token == selected.binding.name_token and
                    Path.overlaps(source.path, selected.path) and
                    self.lifetime_copy_sources[target] & (@as(u32, 1) << @as(u5, @intCast(index))) != 0)
                    return true;
            }
        }
        return false;
    }

    fn initializer(self: *Query, frame: *Frame, root: Root) BudgetError!?Ast.Node.Index {
        const tree = frame.cache.tree;
        var expression: ?Ast.Node.Index = null;
        for (tree.nodes.items(.tag), 0..) |_, raw| {
            try self.charge();
            const node: Ast.Node.Index = @enumFromInt(raw);
            const decl = tree.fullVarDecl(node) orelse continue;
            if (decl.ast.mut_token + 1 != root.binding.name_token) continue;
            expression = decl.ast.init_node.unwrap();
            break;
        }
        return expression;
    }

    fn private(
        self: *Query, frame: *Frame, root: Root, boundary: Ast.TokenIndex,
        domain: Domain, allowed_store: ?Ast.Node.Index,
    ) BudgetError!bool {
        try self.charge();
        const previous_readonly = self.readonly_address;
        self.readonly_address = previous_readonly or (root.addressed and root.binding.is_const);
        defer self.readonly_address = previous_readonly;
        const effective_boundary = frame.return_boundary orelse boundary;
        if (root.binding.origin == .param or root.binding.origin == .loop_capture) {
            if (domain != .reachable_storage or root.path.len != 0 or
                root.binding.origin != .param or self.readonly_address) return false;
            return self.typeAddressFree(frame, root.binding.rhs_first, root.binding.rhs_last);
        }
        for (self.active[0..self.active_len]) |active| {
            try self.charge();
            if (active.cache == frame.cache and active.token == root.binding.name_token and
                Path.eql(active.path, root.path)) return false;
        }
        if (self.active_len == max_origins) return false;
        self.active[self.active_len] = .{
            .cache = frame.cache, .token = root.binding.name_token, .path = root.path,
        };
        self.active_len += 1;
        defer self.active_len -= 1;
        const init = (try self.initializer(frame, root)) orelse return false;
        // A copied header is not a construction origin even when following its
        // initializer eventually reaches an allocation.
        if ((try frame.root(self, .{ .node = init })) != null) return false;
        if (!try self.projectedValue(frame, init, root.path, domain)) return false;
        return self.unpublished(frame, root, effective_boundary, domain, allowed_store);
    }

    fn projectedValue(
        self: *Query, frame: *Frame, node: Ast.Node.Index, path: Path, domain: Domain,
    ) BudgetError!bool {
        if (path.len == 0) return self.value(frame, node, domain);
        try self.charge();
        if (self.value_depth == 64) return false;
        self.value_depth += 1;
        defer self.value_depth -= 1;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .address_of => return false,
            .@"try", .deref =>
                return self.projectedValue(frame, tree.nodeData(node).node, path, domain),
            .grouped_expression, .unwrap_optional =>
                return self.projectedValue(frame, tree.nodeData(node).node_and_token[0], path, domain),
            .call, .call_one, .call_comma, .call_one_comma =>
                return self.callValue(frame, node, domain, path),
            .identifier, .field_access => {
                var root = (try frame.root(self, .{ .node = node })) orelse return false;
                for (path.fields[0..path.len]) |field| {
                    try self.charge();
                    if (!root.path.append(field)) return false;
                }
                return self.private(frame, root, tree.firstToken(node), domain, null);
            },
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = tree.fullStructInit(&buffer, node) orelse return false;
        for (literal.ast.fields) |field| {
            try self.charge();
            const first = tree.firstToken(field);
            if (first < 2 or !std.mem.eql(u8, tree.tokenSlice(first - 2), path.fields[0])) continue;
            var rest: Path = .{};
            for (path.fields[1..path.len]) |name| {
                try self.charge();
                if (!rest.append(name)) return false;
            }
            // A literal field that just copies a local header is not independent.
            if ((try frame.root(self, .{ .node = field })) != null) return false;
            return self.projectedValue(frame, field, rest, domain);
        }
        return false;
    }

    fn value(self: *Query, frame: *Frame, expression: Ast.Node.Index, domain: Domain) BudgetError!bool {
        try self.charge();
        if (self.value_depth == 64) return false;
        self.value_depth += 1;
        defer self.value_depth -= 1;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(expression)) {
            .@"try" => return self.value(frame, tree.nodeData(expression).node, domain),
            // Literal-address freshness is a lifetime fact, not an allocation
            // identity: readonly constants can share their physical storage.
            .address_of => return false,
            .@"catch" => {
                const pair = tree.nodeData(expression).node_and_node;
                const fallback = pair[1];
                if (tree.firstToken(fallback) != tree.lastToken(fallback) or
                    tree.tokenTag(tree.firstToken(fallback)) != .keyword_unreachable) return false;
                return self.value(frame, pair[0], domain);
            },
            .grouped_expression, .unwrap_optional =>
                return self.value(frame, tree.nodeData(expression).node_and_token[0], domain),
            .identifier, .field_access => {
                if (try frame.root(self, .{ .node = expression })) |root| {
                    return self.private(frame, root, tree.firstToken(expression), domain, null);
                }
                if (tree.nodeTag(expression) == .identifier) {
                    const spelling = tree.tokenSlice(tree.nodeMainToken(expression));
                    // These are the language's address-free literal values, not
                    // declarations whose names establish storage independence.
                    return !self.readonly_address and (std.mem.eql(u8, spelling, "true") or
                        std.mem.eql(u8, spelling, "false") or std.mem.eql(u8, spelling, "null"));
                }
            },
            .number_literal, .char_literal => return !self.readonly_address,
            .string_literal, .multiline_string_literal => return false,
            .array_init, .array_init_comma, .array_init_dot, .array_init_dot_comma,
            .array_init_one, .array_init_one_comma, .array_init_dot_two,
            .array_init_dot_two_comma => {
                if (self.readonly_address) return false;
                var buffer: [2]Ast.Node.Index = undefined;
                const array = tree.fullArrayInit(&buffer, expression) orelse return false;
                for (array.ast.elements) |element| {
                    try self.charge();
                    if (!try self.value(frame, element, domain)) return false;
                }
                return true;
            },
            .slice_open, .slice, .slice_sentinel => {
                const slice = tree.fullSlice(expression) orelse return false;
                // Slicing an existing header is a copy, not a new origin.
                if ((try frame.root(self, .{ .node = slice.ast.sliced })) != null) return false;
                if (!try self.value(frame, slice.ast.sliced, .backing_storage)) return false;
                if (domain == .backing_storage) return true;
                const end = slice.ast.end.unwrap() orelse return false;
                // The actual constructor's empty view has no element payload.
                // This is read from its return initializer, not from a field's
                // name or an assumption about every collection header.
                try self.charge();
                return tree.nodeTag(slice.ast.start) == .number_literal and
                    tree.nodeTag(end) == .number_literal and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(slice.ast.start)), "0") and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(end)), "0");
            },
            .call, .call_one, .call_comma, .call_one_comma =>
                return self.callValue(frame, expression, domain, .{}),
            else => {},
        }
        var declared_type: ?Ast.Node.Index = null;
        if (frame.parentOf(expression)) |parent| {
            if (tree.fullVarDecl(parent)) |decl| declared_type = decl.ast.type_node.unwrap();
        }
        try self.charge();
        var walk = frame.freshWalk(self, .{
            .first = tree.firstToken(expression), .last = tree.lastToken(expression),
        });
        walk.claim.type_first = if (declared_type) |node| tree.firstToken(node) else null;
        walk.claim.type_last = if (declared_type) |node| tree.lastToken(node) else null;
        const proved = try fresh.freshStorageAt(frame.cache, walk);
        if (!proved) return false;
        try self.charge();
        if (try fresh.sdkCollectionIsEmpty(frame.cache, walk)) return true;
        const requires_empty = tree.nodeTag(expression) == .enum_literal or
            tree.nodeTag(expression) == .field_access;
        if (requires_empty) {
            try self.charge();
            if (frame.resolution) |resolution| {
                return resolution.stdCollectionEmptyOf(expression, declared_type) catch |err|
                    resourceFailure(err);
            }
            const resolver = frame.cache.zls orelse return false;
            return resolver.stdCollectionEmptyOf(expression, declared_type) catch |err|
                resourceFailure(err);
        }
        if (domain == .backing_storage) return !self.readonly_address;
        return false;
    }

    fn callValue(
        self: *Query, frame: *Frame, node: Ast.Node.Index, domain: Domain, path: Path,
    ) BudgetError!bool {
        const tree = frame.cache.tree;
        const range: FileCache.TokenRange = .{
            .first = tree.firstToken(node), .last = tree.lastToken(node),
        };
        try self.charge();
        // This existing producer owns the SDK constructor identities.
        const list_constructor = try fresh.standardListConstructor(
            frame.cache, range, frame.freshWalk(self, range),
        );
        if (path.len == 0 and list_constructor) {
            if (domain == .backing_storage) return true;
            // The buffer constructor does not prove that allocator/context
            // fields embedded in a managed header are themselves private.
            try self.charge();
            return fresh.freshStorageAt(frame.cache, frame.freshWalk(self, .{
                .first = tree.firstToken(node), .last = tree.lastToken(node),
            })) catch |err| return resourceFailure(err);
        }
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse return false;
        try self.charge();
        const canonical = (try frame.cache.actualCallSummaryAt(
            fresh.calleeQueryToken(tree, call), frame.resolution,
        )) orelse return false;
        if (list_constructor)
            return self.listConstructorProjection(frame, canonical, path);
        if (path.len == 0 and domain == .backing_storage) {
            const resolver = if (frame.resolution) |resolution|
                resolution.resolver
            else
                frame.cache.zls orelse return false;
            try self.charge();
            const allocator = resolver.declaredInToolchainFile(
                canonical.callee.handle, "/std/mem/Allocator.zig",
            ) catch |err| return resourceFailure(err);
            if (allocator) {
                // Only the existing producer chooses which actual allocator
                // declarations grant ownership; document identity alone does not.
                return fresh.freshStorageAt(frame.cache, frame.freshWalk(self, range));
            }
        }
        for (self.calls[0..self.call_len]) |active| {
            try self.charge();
            if (active.tree == canonical.callee.tree and
                active.declaration == canonical.callee.declaration) return false;
        }
        if (self.call_len == max_origins) return false;
        self.calls[self.call_len] = .{
            .tree = canonical.callee.tree, .declaration = canonical.callee.declaration,
        };
        self.call_len += 1;
        defer self.call_len -= 1;
        const declaring = (try canonical.declaringCache(frame.cache)) orelse return false;
        const body = tokens.bodyOf(canonical.callee.tree, canonical.callee.declaration) orelse return false;
        // The exact declared body, not a name census, establishes returned
        // ownership. Parameters stay unknown; no argument-forwarding fiction.
        var callee_frame = (if (declaring == frame.cache)
            try Frame.at(self, declaring, frame.parents, body)
        else
            try Frame.init(self, declaring, body)) orelse return false;
        defer callee_frame.deinit();
        const resolver = if (canonical.callee.caller_frame) |caller|
            caller.resolver
        else
            frame.cache.zls orelse return false;
        callee_frame.resolution = resolver.frameForFunction(canonical.callee.reference);
        var saw_return = false;
        for (declaring.tree.nodes.items(.tag), 0..) |tag, raw| {
            try self.charge();
            if (tag != .@"return") continue;
            const ret: Ast.Node.Index = @enumFromInt(raw);
            const token = declaring.tree.firstToken(ret);
            if (token < declaring.tree.firstToken(body) or token > declaring.tree.lastToken(body)) continue;
            if (!try callee_frame.owns(self, ret)) continue;
            const returned = declaring.tree.nodeData(ret).opt_node.unwrap() orelse return false;
            callee_frame.return_boundary = token;
            if (!try self.projectedValue(&callee_frame, returned, path, domain)) return false;
            saw_return = true;
        }
        return saw_return;
    }

    fn listConstructorProjection(
        self: *Query, frame: *Frame, canonical: FileCache.ActualCallSummary, path: Path,
    ) BudgetError!bool {
        if (path.len != 1) return false;
        const resolver = if (canonical.callee.caller_frame) |caller|
            caller.resolver
        else
            frame.cache.zls orelse return false;
        const resolution = resolver.frameForFunction(canonical.callee.reference);
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(
            canonical.callee.tree, &proto_buffer, canonical.callee.declaration,
        ) orelse return false;
        var returned_type = proto.ast.return_type.unwrap() orelse return false;
        while (canonical.callee.tree.nodeTag(returned_type) == .error_union) {
            try self.charge();
            returned_type = canonical.callee.tree.nodeData(returned_type).node_and_node[1];
        }
        try self.charge();
        const container = (resolution.containerOfNode(returned_type) catch |err|
            return resourceFailure(err)) orelse return false;
        const owner = resolver.frameForContainer(container);
        const tree = &owner.handle.document.tree;
        var container_buffer: [2]Ast.Node.Index = undefined;
        const declaration = tree.fullContainerDecl(
            &container_buffer, container.scope_handle.toNode(),
        ) orelse return false;
        var slices: usize = 0;
        var selected_slice = false;
        for (declaration.ast.members) |member| {
            try self.charge();
            const field = tree.fullContainerField(member) orelse continue;
            if (field.ast.tuple_like) return false;
            const field_type = field.ast.type_expr.unwrap() orelse return false;
            try self.charge();
            const actual_type = (owner.typeOfNode(field_type) catch |err|
                return resourceFailure(err)) orelse return false;
            if (resolver.pointerSize(actual_type) != .slice) continue;
            slices += 1;
            if (std.mem.eql(u8, tree.tokenSlice(field.ast.main_token), path.fields[0]))
                selected_slice = true;
        }
        // The existing SDK constructor owns its buffer. Its actual return
        // declaration identifies that buffer as the unique slice field; no
        // allocator/context field receives ownership from its spelling.
        return slices == 1 and selected_slice;
    }

    fn unpublished(
        self: *Query, frame: *Frame, selected: Root, boundary: Ast.TokenIndex,
        domain: Domain, allowed_store: ?Ast.Node.Index,
    ) BudgetError!bool {
        const tree = frame.cache.tree;
        for (tree.nodes.items(.tag), 0..) |tag, raw| {
            try self.charge();
            if (tag != .identifier) continue;
            const node: Ast.Node.Index = @enumFromInt(raw);
            const token = tree.nodeMainToken(node);
            if (token <= selected.binding.rhs_last or token >= boundary) continue;
            const binding = (try frame.bindingAt(self, node)) orelse continue;
            if (binding.name_token != selected.binding.name_token) continue;
            // A nested declaration may capture and publish an outer header.
            // Its body is not evidence of nonpublication merely because it is
            // written in a different lexical function.
            if (!try frame.owns(self, node)) return false;
            if (try frame.deferred(self, node, boundary)) continue;
            var use = node;
            var use_path: Path = .{};
            while (frame.parentOf(use)) |parent| {
                try self.charge();
                switch (tree.nodeTag(parent)) {
                    .field_access => {
                        const access = tree.nodeData(parent).node_and_token;
                        if (access[0] != use) break;
                        if (frame.parentOf(parent)) |caller| {
                            var call_buffer: [1]Ast.Node.Index = undefined;
                            if (tree.fullCall(&call_buffer, caller)) |call| {
                                if (call.ast.fn_expr == parent) break;
                            }
                        }
                        if (!use_path.append(tree.tokenSlice(access[1]))) return false;
                        use = parent;
                    },
                    .address_of, .deref, .grouped_expression => use = parent,
                    else => break,
                }
            }
            if (!Path.overlaps(selected.path, use_path)) continue;
            if (self.lifetime_only and try self.lifetimeAliasInitialization(frame, use)) continue;
            if (self.lifetime_only and cellDefinition(frame, use)) continue;
            if (self.lifetime_only and try self.expressionAddressFree(frame, use)) continue;
            var parent = frame.parentOf(use) orelse return false;
            if (tree.nodeTag(parent) == .field_access) parent = frame.parentOf(parent) orelse return false;
            if (allowed_store != null and parent == allowed_store.?) continue;
            var call_buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buffer, parent) orelse return false;
            try self.charge();
            const canonical = (try frame.cache.actualCallSummaryAt(
                fresh.calleeQueryToken(tree, call), frame.resolution,
            )) orelse return false;
            if (self.lifetime_only and canonical.read_only == true) continue;
            var argument_buffer: [1]Ast.Node.Index = undefined;
            const receiver = (try canonical.callArgumentFor(frame.cache, &argument_buffer, 0)) orelse {
                if (self.lifetime_only and try self.lifetimeCallSafe(frame, canonical, selected)) continue;
                return false;
            };
            const receiver_root = (try frame.root(self, .{ .node = receiver })) orelse {
                if (self.lifetime_only and try self.lifetimeCallSafe(frame, canonical, selected)) continue;
                return false;
            };
            if (receiver != use or receiver_root.binding.name_token != binding.name_token or
                receiver_root.path.len > selected.path.len or !Path.overlaps(receiver_root.path, selected.path)) {
                if (self.lifetime_only and try self.lifetimeCallSafe(frame, canonical, selected)) continue;
                return false;
            }
            const resolver = if (frame.resolution) |resolution|
                resolution.resolver
            else
                frame.cache.zls orelse return false;
            try self.charge();
            const append = if (frame.resolution) |resolution|
                resolution.stdCollectionAppendOf(call.ast.fn_expr, call.ast.params.len)
                    catch |err| return resourceFailure(err)
            else
                resolver.stdCollectionAppendOf(call.ast.fn_expr, call.ast.params.len)
                    catch |err| return resourceFailure(err);
            if (append != .no) {
                if (self.lifetime_only and try self.lifetimeCopyPredates(selected, tree.firstToken(parent)))
                    return false;
                if (domain == .reachable_storage and !try self.storedValue(
                    frame, call.ast.params[call.ast.params.len - 1], parent, boundary,
                )) return false;
                continue;
            }
            try self.charge();
            const hash_map = resolver.declaredInToolchainFile(
                canonical.callee.handle, "/std/hash_map.zig",
            ) catch |err| return resourceFailure(err);
            const array_hash_map = resolver.declaredInToolchainFile(
                canonical.callee.handle, "/std/array_hash_map.zig",
            ) catch |err| return resourceFailure(err);
            if (!hash_map and !array_hash_map) {
                if (self.lifetime_only and try self.lifetimeCallSafe(frame, canonical, selected)) continue;
                return false;
            }
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration)
                orelse return false;
            const name = proto.name_token orelse return false;
            // The exact toolchain declaration and signature establish a store;
            // a project function merely named put cannot receive this credit.
            if (!std.mem.eql(u8, canonical.callee.tree.tokenSlice(name), "put")) {
                if (self.lifetime_only and try self.lifetimeCallSafe(frame, canonical, selected)) continue;
                return false;
            }
            if (self.lifetime_only and try self.lifetimeCopyPredates(selected, tree.firstToken(parent)))
                return false;
            var params = proto.iterate(canonical.callee.tree);
            var formal: u32 = 0;
            var value_formal: ?u32 = null;
            var key_formal: ?u32 = null;
            while (params.next()) |parameter| : (formal += 1) {
                try self.charge();
                if (parameter.name_token) |parameter_name| {
                    if (std.mem.eql(u8, canonical.callee.tree.tokenSlice(parameter_name), "value")) {
                        value_formal = formal;
                    }
                    if (std.mem.eql(u8, canonical.callee.tree.tokenSlice(parameter_name), "key")) {
                        key_formal = formal;
                    }
                }
            }
            const payload = (try canonical.callArgumentFor(
                frame.cache, &argument_buffer, value_formal orelse return false,
            )) orelse return false;
            const key = (try canonical.callArgumentFor(
                frame.cache, &argument_buffer, key_formal orelse return false,
            )) orelse return false;
            if (domain == .reachable_storage and
                !try self.addressFreeValue(frame, key, 0)) return false;
            if (domain == .reachable_storage and
                !try self.storedValue(frame, payload, parent, boundary)) return false;
        }
        return true;
    }

    fn addressFreeValue(
        self: *Query, frame: *Frame, node: Ast.Node.Index, depth: u8,
    ) BudgetError!bool {
        try self.charge();
        if (depth == max_origins) return false;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .number_literal, .char_literal => return true,
            .grouped_expression =>
                return self.addressFreeValue(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            .identifier => {
                const spelling = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, spelling, "true") or std.mem.eql(u8, spelling, "false") or
                    std.mem.eql(u8, spelling, "null")) return true;
            },
            else => return false,
        }
        const root = (try frame.root(self, .{ .node = node })) orelse return false;
        if (root.path.len != 0) return false;
        if (root.binding.origin == .param) {
            return self.typeAddressFree(frame, root.binding.rhs_first, root.binding.rhs_last);
        }
        if (root.binding.origin == .loop_capture) return false;
        for (tree.nodes.items(.tag), 0..) |_, raw| {
            try self.charge();
            const candidate: Ast.Node.Index = @enumFromInt(raw);
            const decl = tree.fullVarDecl(candidate) orelse continue;
            if (decl.ast.mut_token + 1 != root.binding.name_token) continue;
            if (decl.ast.type_node.unwrap()) |declared_type| {
                return self.typeAddressFree(
                    frame, tree.firstToken(declared_type), tree.lastToken(declared_type),
                );
            }
            return self.addressFreeValue(
                frame, decl.ast.init_node.unwrap() orelse return false, depth + 1,
            );
        }
        return false;
    }

    fn typeAddressFree(
        self: *Query, frame: *Frame, first: Ast.TokenIndex, last: Ast.TokenIndex,
    ) BudgetError!bool {
        try self.charge();
        const tree = frame.cache.tree;
        if (first == last and tree.tokenTag(first) == .identifier and
            type_query.isReservedScalarTypeName(tree.tokenSlice(first))) return true;
        const resolution = frame.resolution orelse
            (frame.cache.zls orelse return false).resolutionFrame();
        const node = frame.cache.nodeForExactSpan(first, last) orelse return false;
        try self.charge();
        const ty = (resolution.typeOfNode(node) catch |err|
            return resourceFailure(err)) orelse return false;
        return fresh.actualTypeAddressFree(resolution, ty, 0, self.remaining);
    }

    fn storedValue(
        self: *Query, frame: *Frame, value_node: Ast.Node.Index,
        store: Ast.Node.Index, boundary: Ast.TokenIndex,
    ) BudgetError!bool {
        var stored = value_node;
        var depth: u32 = 0;
        while (true) {
            try self.charge();
            if (depth == 64) return false;
            depth += 1;
            switch (frame.cache.tree.nodeTag(stored)) {
                .address_of => return false,
                .@"try" => stored = frame.cache.tree.nodeData(stored).node,
                .grouped_expression, .unwrap_optional =>
                    stored = frame.cache.tree.nodeData(stored).node_and_token[0],
                else => break,
            }
        }
        // These values are copied into proven SDK-owned cells. A pointer
        // address was rejected above; scalar/array payload copies do not
        // inherit uncertainty about a readonly source object's address.
        const previous_readonly = self.readonly_address;
        self.readonly_address = false;
        defer self.readonly_address = previous_readonly;
        if (try frame.root(self, .{ .node = stored })) |root| {
            return self.private(frame, root, boundary, .reachable_storage, store);
        }
        return self.value(frame, stored, .reachable_storage);
    }
};

/// A plain assignment THROUGH the selected storage is that storage's own
/// construction, not a publication of it: `out.bytes = fresh` fills a
/// cell the value already owns and hands nothing to anybody else. The
/// fresh-storage proof reads the assigned value separately, so refusing
/// this use here also refuses a local that initialized every one of its
/// own fields. Only a DIRECT write through the selected binding
/// qualifies — a write reached through a call argument, an address-of,
/// or a method receiver still publishes and stays refused.
fn cellDefinition(frame: *Frame, use: Ast.Node.Index) bool {
    const tree = frame.cache.tree;
    const parent = frame.parentOf(use) orelse return false;
    if (tree.nodeTag(parent) != .assign) return false;
    return tree.nodeData(parent).node_and_node[0] == use;
}

fn resourceFailure(err: anyerror) BudgetError!bool {
    return switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        error.AnalysisBudgetExceeded => error.AnalysisBudgetExceeded,
        else => false,
    };
}

// These parse real expressions and exercise the public query, not token echoes.
fn expectProbe(source: [:0]const u8, domain: Domain, expected: bool) !void {
    return expectProbePaths(source, domain, expected, "", "");
}

fn expectProbePaths(
    source: [:0]const u8, domain: Domain, expected: bool,
    left_path: []const u8, right_path: []const u8,
) !void {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var found = false;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "probe")) continue;
        try std.testing.expectEqual(@as(usize, 2), call.ast.params.len);
        try std.testing.expectEqual(expected, try mayShareStorageAt(
            &cache, node,
            .{ .node = call.ast.params[0], .path = left_path },
            .{ .node = call.ast.params[1], .path = right_path }, domain, .{},
        ));
        found = true;
    }
    try std.testing.expect(found);
}

test "different incoming fields and nested arguments are unknown" {
    try expectProbe(
        \\const Pair = struct { members: []u8, other: []u8 };
        \\fn use(self: *Pair) void { probe(self.members, &(self.other)); }
    , .backing_storage, true);
    try expectProbe(
        \\const Inner = struct { bytes: []u8 };
        \\const Pair = struct { first: Inner, second: Inner };
        \\fn use(self: *Pair) void { probe(self.first.bytes, &self.second); }
    , .reachable_storage, true);
}

test "header copies and reassigned fresh locals may alias" {
    try expectProbe(
        \\fn use() void {
        \\    const a = &[_]u8{1};
        \\    const b = a;
        \\    probe(a, b);
        \\}
    , .backing_storage, true);
    try expectProbe(
        \\fn use() void {
        \\    const a = &[_]u8{1};
        \\    var b = &[_]u8{2};
        \\    b = a;
        \\    probe(a, b);
        \\}
    , .backing_storage, true);
}

test "fresh storage published before the call loses disjointness" {
    try expectProbe(
        \\fn use(incoming: []const u8) void {
        \\    var b = [_]u8{2};
        \\    publish(&b);
        \\    probe(incoming, b);
        \\}
    , .backing_storage, true);
    try expectProbe(
        \\var saved: []const u8 = undefined;
        \\fn use(incoming: []const u8) void {
        \\    var b = [_]u8{2};
        \\    saved = &b;
        \\    probe(incoming, b);
        \\}
    , .reachable_storage, true);
}

test "distinct private actual fresh constructions are disjoint" {
    try expectProbe(
        \\fn use() void {
        \\    var a = [_]u8{1};
        \\    var b = [_]u8{2};
        \\    probe(a, &(b));
        \\}
    , .backing_storage, false);
    try expectProbe(
        \\fn use(incoming: []const u8) void {
        \\    var other = [_]u8{2};
        \\    probe(incoming, other);
        \\}
    , .reachable_storage, false);
}

test "same fresh declaration and explicit field header copy are aliases" {
    try expectProbe(
        \\fn use() void {
        \\    const a = &[_]u8{1};
        \\    probe(a, &a);
        \\}
    , .backing_storage, true);
    try expectProbe(
        \\const Pair = struct { members: []u8, other: []u8 };
        \\fn use(self: *Pair) void {
        \\    self.other = self.members;
        \\    probe(self.members, self.other);
        \\}
    , .reachable_storage, true);
}

test "composed field selections need construction proofs not field spelling" {
    try expectProbePaths(
        \\fn use() void {
        \\    var state = .{ .map = [_]u8{1}, .other = [_]u8{2} };
        \\    probe(&state, &state);
        \\}
    , .reachable_storage, false, "map", "other");
    try expectProbePaths(
        \\fn use() void {
        \\    const shared = &[_]u8{1};
        \\    const state = .{ .map = shared, .other = shared };
        \\    probe(&state, &state);
        \\}
    , .reachable_storage, true, "map", "other");
    try expectProbePaths(
        \\const State = struct { map: []const u8, other: []const u8 };
        \\fn use() void {
        \\    var state = State{ .map = &[_]u8{1}, .other = &[_]u8{2} };
        \\    state.map = state.other;
        \\    probe(&state, &state);
        \\}
    , .backing_storage, true, "map", "other");
    try expectProbePaths(
        \\const State = struct { map: []const u8, other: []const u8 };
        \\fn use(state: *State) void { probe(state, state); }
    , .reachable_storage, true, "map", "other");
}

test "query work exhaustion is attributed and is not a disjoint verdict" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "fn use() void { probe(a, b); }", .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var remaining: u32 = 0;
    var query: Query = .{ .root_cache = &cache, .at_node = .root, .remaining = &remaining };
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, query.charge());
    const failure = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.storage_alias_work, failure.limit);
    try std.testing.expectEqual(work_limit, failure.limit_value);
}

fn expectTypedProbe(source: [:0]const u8, domain: Domain, expected: bool) !void {
    return expectTypedProbePaths(source, domain, expected, "", "");
}

fn expectTypedProbePaths(
    source: [:0]const u8, domain: Domain, expected: bool,
    left_path: []const u8, right_path: []const u8,
) !void {
    const gpa = std.testing.allocator;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var fixture_path: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const length = try std.Io.Dir.cwd().realPathFile(std.testing.io, ".", &fixture_path);
    const separator = if (std.mem.endsWith(u8, fixture_path[0..length], std.fs.path.sep_str))
        "" else std.fs.path.sep_str;
    const suffix = try std.fmt.bufPrint(
        fixture_path[length..], "{s}zbc-storage-alias-query-test.zig", .{separator},
    );
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, fixture_path[0 .. length + suffix.len], source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.module_id = resolver.handle.module;
    var found = false;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "probe")) continue;
        try std.testing.expectEqual(@as(usize, 2), call.ast.params.len);
        try std.testing.expectEqual(expected, try mayShareStorageAt(
            &cache, node, .{ .node = call.ast.params[0], .path = left_path },
            .{ .node = call.ast.params[1], .path = right_path }, domain, .{},
        ));
        found = true;
    }
    try std.testing.expect(found);
}

const map_test_prelude =
    \\const std = @import("std");
    \\const List = std.ArrayList(u8);
    \\const Map = std.AutoArrayHashMapUnmanaged(bool, List);
    \\const State = struct { members: Map };
    \\fn probe(_: Map, _: Map) void {}
    \\
;

test "reachable SDK map storage includes independently constructed list values" {
    try expectTypedProbe(map_test_prelude ++
        \\fn makeFresh(gpa: std.mem.Allocator) !Map {
        \\    var out: Map = .empty;
        \\    errdefer out.deinit(gpa);
        \\    var entry = try List.initCapacity(gpa, 9);
        \\    errdefer entry.deinit(gpa);
        \\    try entry.append(gpa, 'x');
        \\    try out.put(gpa, true, entry);
        \\    return out;
        \\}
        \\fn run(self: *State, gpa: std.mem.Allocator) !void {
        \\    const other = makeFresh(gpa) catch unreachable;
        \\    probe(self.members, other);
        \\}
    , .reachable_storage, false);
}

test "fresh SDK map tables do not prove copied list payloads deeply disjoint" {
    const source = map_test_prelude ++
        \\fn makeBorrowed(gpa: std.mem.Allocator, entry: List) !Map {
        \\    var out: Map = .empty;
        \\    try out.put(gpa, true, entry);
        \\    return out;
        \\}
        \\fn run(self: *State, gpa: std.mem.Allocator, held: List) !void {
        \\    const other = try makeBorrowed(gpa, held);
        \\    probe(self.members, other);
        \\}
    ;
    try expectTypedProbe(source, .backing_storage, false);
    try expectTypedProbe(source, .reachable_storage, true);
}

test "SDK map payload publication after insertion defeats deep disjointness" {
    try expectTypedProbe(map_test_prelude ++
        \\var saved: List = .empty;
        \\fn makePublished(gpa: std.mem.Allocator) !Map {
        \\    var out: Map = .empty;
        \\    const entry = try List.initCapacity(gpa, 9);
        \\    try out.put(gpa, true, entry);
        \\    saved = entry;
        \\    return out;
        \\}
        \\fn run(self: *State, gpa: std.mem.Allocator) !void {
        \\    const other = try makePublished(gpa);
        \\    probe(self.members, other);
        \\}
    , .reachable_storage, true);
}

test "an already executed block defer and nested captures can publish fresh storage" {
    try expectProbe(
        \\fn use(incoming: []const u8) void {
        \\    var other = [_]u8{2};
        \\    { defer publish(&other); }
        \\    probe(incoming, other);
        \\}
    , .reachable_storage, true);
    try expectProbe(
        \\var saved: []const u8 = undefined;
        \\fn use(incoming: []const u8) void {
        \\    var other = [_]u8{2};
        \\    const Nested = struct { fn publish() void { saved = &other; } };
        \\    Nested.publish();
        \\    probe(incoming, other);
        \\}
    , .reachable_storage, true);
}

test "storage query allocation failure propagates without a safe fallback" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "fn use() void { probe(a, b); }", .zig);
    defer tree.deinit(gpa);
    var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = 0 });
    var cache = FileCache.init(failing.allocator(), &tree);
    defer cache.deinit();
    try std.testing.expectError(error.OutOfMemory, mayShareStorageAt(
        &cache, .root, .{ .node = .root }, .{ .node = .root }, .backing_storage, .{},
    ));
}

test "nested multiargument helper stores cannot hide borrowed payload origins" {
    try expectTypedProbe(map_test_prelude ++
        \\const Holder = struct { list: List };
        \\fn fill(target: *Map, input: *const Holder, gpa: std.mem.Allocator) !void {
        \\    try target.put(gpa, true, input.list);
        \\}
        \\fn makeAliased(input: *const Holder, gpa: std.mem.Allocator) !Map {
        \\    var out: Map = .empty;
        \\    try fill(&out, input, gpa);
        \\    return out;
        \\}
        \\fn run(self: *State, held: *const Holder, gpa: std.mem.Allocator) !void {
        \\    const other = try makeAliased(held, gpa);
        \\    probe(self.members, other);
        \\}
    , .reachable_storage, true);
}

test "real SDK lists have independent backing but header copies do not" {
    const prelude =
        \\const std = @import("std");
        \\const List = std.ArrayList(u8);
        \\fn probe(_: List, _: List) void {}
        \\
    ;
    try expectTypedProbe(prelude ++
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    const first = try List.initCapacity(gpa, 1);
        \\    const second = try List.initCapacity(gpa, 1);
        \\    probe(first, second);
        \\}
    , .backing_storage, false);
    try expectTypedProbe(prelude ++
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    const first = try List.initCapacity(gpa, 1);
        \\    const second = first;
        \\    probe(first, second);
        \\}
    , .backing_storage, true);
}

test "static literals and project declaration literals are not private allocations" {
    try expectProbe(
        \\fn use(incoming: []const u8) void {
        \\    const other = "shared";
        \\    probe(incoming, other);
        \\}
    , .reachable_storage, true);
    try expectProbe(
        \\const Header = struct { bytes: []const u8, const empty = Header{ .bytes = "shared" }; };
        \\fn use(incoming: Header) void {
        \\    const other: Header = .empty;
        \\    probe(incoming, other);
        \\}
    , .backing_storage, true);
}

test "projected SDK buffer fields follow actual constructor return storage" {
    const prelude =
        \\const std = @import("std");
        \\const List = std.ArrayList(u8);
        \\fn probe(_: List, _: List) void {}
        \\
    ;
    try expectTypedProbePaths(prelude ++
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    const first = try List.initCapacity(gpa, 2);
        \\    var second = try List.initCapacity(gpa, 2);
        \\    try second.append(gpa, 'x');
        \\    probe(first, second);
        \\}
    , .reachable_storage, false, "items", "items");
    try expectTypedProbePaths(prelude ++
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    const first = try List.initCapacity(gpa, 2);
        \\    const second = first;
        \\    probe(first, second);
        \\}
    , .reachable_storage, true, "items", "items");
}

test "an enclosing query lends the same work counter without a reset" {
    const source: [:0]const u8 =
        \\fn use() void {
        \\    var first = [_]u8{1};
        \\    var second = [_]u8{2};
        \\    probe(first, second);
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var remaining: u32 = work_limit;
    var found = false;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "probe")) continue;
        const left: StorageSelection = .{ .node = call.ast.params[0] };
        const right: StorageSelection = .{ .node = call.ast.params[1] };
        const context: QueryContext = .{ .remaining = &remaining };
        try std.testing.expect(!try mayShareStorageAt(
            &cache, node, left, right, .backing_storage, context,
        ));
        const after_first = remaining;
        try std.testing.expect(after_first < work_limit);
        try std.testing.expect(!try mayShareStorageAt(
            &cache, node, left, right, .backing_storage, context,
        ));
        try std.testing.expect(remaining < after_first);
        remaining = 0;
        budget_mod.clear();
        defer budget_mod.clear();
        try std.testing.expectError(error.AnalysisBudgetExceeded, mayShareStorageAt(
            &cache, node, left, right, .backing_storage, context,
        ));
        found = true;
    }
    try std.testing.expect(found);
}

test "managed SDK headers do not turn allocator contexts into private storage" {
    const prelude =
        \\const std = @import("std");
        \\const List = std.array_list.Managed(u8);
        \\
    ;
    const source = prelude ++
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    const first = try List.initCapacity(gpa, 2);
        \\    const second = try List.initCapacity(gpa, 2);
        \\    probe(first, second);
        \\}
    ;
    try expectTypedProbe(source, .backing_storage, false);
    try expectTypedProbe(source, .reachable_storage, true);
    try expectTypedProbePaths(source, .reachable_storage, false, "items", "items");
    try expectTypedProbePaths(source, .reachable_storage, true, "allocator", "allocator");
}

test "ordinary factory defers publish before the returned storage reaches its caller" {
    try expectTypedProbe(
        \\const std = @import("std");
        \\const List = std.ArrayList(u8);
        \\var held: List = .empty;
        \\fn publish(value: List) void { held = value; }
        \\fn makeFresh(gpa: std.mem.Allocator) !List {
        \\    var out = try List.initCapacity(gpa, 2);
        \\    defer publish(out);
        \\    return out;
        \\}
        \\fn run(incoming: List, gpa: std.mem.Allocator) void {
        \\    const other = makeFresh(gpa) catch unreachable;
        \\    probe(incoming, other);
        \\}
    , .reachable_storage, true);
}

test "readonly literal addresses are not disjoint allocation identities" {
    try expectProbe(
        \\fn use(incoming: []const u8) void {
        \\    const other = &[_]u8{1};
        \\    probe(incoming, other);
        \\}
    , .backing_storage, true);
    try expectProbe(
        \\fn use() void {
        \\    const first = &[_]u8{1};
        \\    const second = &[_]u8{1};
        \\    probe(first, second);
        \\}
    , .reachable_storage, true);
}

test "factory scalar parameters do not own an address stored as payload" {
    try expectTypedProbe(
        \\const std = @import("std");
        \\const Map = std.AutoArrayHashMapUnmanaged(bool, *const u8);
        \\fn makeFresh(gpa: std.mem.Allocator, byte: u8) !Map {
        \\    var out: Map = .empty;
        \\    try out.put(gpa, true, &byte);
        \\    return out;
        \\}
        \\fn run(incoming: Map, gpa: std.mem.Allocator) void {
        \\    const other = makeFresh(gpa, 1) catch unreachable;
        \\    probe(incoming, other);
        \\}
    , .reachable_storage, true);
}

test "taking a readonly declaration address does not lose its literal alias uncertainty" {
    try expectProbe(
        \\fn use(incoming: []const u8) void {
        \\    const other = [_]u8{1};
        \\    probe(incoming, &other);
        \\}
    , .backing_storage, true);
    try expectProbePaths(
        \\fn use(incoming: []const u8) void {
        \\    const holder = .{ .bytes = [_]u8{1} };
        \\    probe(incoming, &holder);
        \\}
    , .reachable_storage, true, "", "bytes");
    try expectProbe(
        \\fn use(incoming: *const u8, byte: u8) void {
        \\    probe(incoming, &byte);
        \\}
    , .reachable_storage, true);
}

test "readonly address uncertainty follows grouping and factory returns" {
    try expectProbe(
        \\fn use(incoming: []const u8) void {
        \\    const other = ([_]u8{1});
        \\    probe(incoming, &other);
        \\}
    , .backing_storage, true);
    try expectTypedProbe(
        \\fn makeConstant() [1]u8 { return .{1}; }
        \\fn run(incoming: []const u8) void {
        \\    const other = makeConstant();
        \\    probe(incoming, &other);
        \\}
    , .backing_storage, true);
}

test "generic SDK key ownership uses the bound type rather than a same-spelled alias" {
    const prelude =
        \\const std = @import("std");
        \\const List = std.ArrayList(u8);
        \\const Namespace = struct { const Key = enum { yes }; };
        \\fn makeFresh(comptime Key: type, gpa: std.mem.Allocator, key: Key) !std.AutoArrayHashMapUnmanaged(Key, List) {
        \\    var out: std.AutoArrayHashMapUnmanaged(Key, List) = .empty;
        \\    var entry = try List.initCapacity(gpa, 2);
        \\    try entry.append(gpa, 'x');
        \\    try out.put(gpa, key, entry);
        \\    return out;
        \\}
        \\
    ;
    try expectTypedProbe(prelude ++
        \\fn run(incoming: std.AutoArrayHashMapUnmanaged(bool, List), gpa: std.mem.Allocator) void {
        \\    const other = makeFresh(bool, gpa, true) catch unreachable;
        \\    probe(incoming, other);
        \\}
    , .reachable_storage, false);
    try expectTypedProbe(prelude ++
        \\fn run(incoming: std.AutoArrayHashMapUnmanaged(*const u8, List), gpa: std.mem.Allocator, key: *const u8) void {
        \\    const other = makeFresh(*const u8, gpa, key) catch unreachable;
        \\    probe(incoming, other);
        \\}
    , .reachable_storage, true);
}

test "another field in the same owner needs its own independent origin proof" {
    try expectTypedProbePaths(
        \\const std = @import("std");
        \\const List = std.ArrayList(u8);
        \\const State = union { first: List, second: List };
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    var state = State{ .first = try List.initCapacity(gpa, 2) };
        \\    probe(&state, &state);
        \\}
    , .reachable_storage, true, "first", "second");
}

fn expectHandoff(source: [:0]const u8, expected: bool) !void {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var found = false;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.nodeTag(node) != .@"return") continue;
        const value = tree.nodeData(node).opt_node.unwrap() orelse continue;
        try std.testing.expectEqual(expected, try allocationSurvivesHandoff(
            &cache, value, tree.firstToken(node), .{},
        ));
        found = true;
    }
    try std.testing.expect(found);
}

test "ordinary pending frees end the returned allocation's handoff" {
    const prelude =
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) ![]u8 {
        \\    const bytes = try gpa.alloc(u8, 2);
        \\
    ;
    try expectHandoff(prelude ++
        \\    defer gpa.free(bytes);
        \\    return bytes;
        \\}
    , false);
    try expectHandoff(prelude ++
        \\    const alias = bytes;
        \\    defer gpa.free(bytes);
        \\    return alias;
        \\}
    , false);
    try expectHandoff(prelude ++
        \\    const alias = bytes;
        \\    defer gpa.free(alias);
        \\    return alias;
        \\}
    , false);
}

test "released before the handoff the allocation does not survive" {
    try expectHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) ![]u8 {
        \\    const bytes = try gpa.alloc(u8, 2);
        \\    gpa.free(bytes);
        \\    return bytes;
        \\}
    , false);
    try expectHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) ![]u8 {
        \\    const bytes = try gpa.alloc(u8, 2);
        \\    const holder = .{ .bytes = bytes };
        \\    defer gpa.free(holder.bytes);
        \\    return bytes;
        \\}
    , false);
}

test "surviving allocations keep a handoff the caller can observe" {
    const prelude =
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) ![]u8 {
        \\    const bytes = try gpa.alloc(u8, 2);
        \\
    ;
    try expectHandoff(prelude ++
        \\    const alias = bytes;
        \\    return alias;
        \\}
    , true);
    try expectHandoff(prelude ++
        \\    errdefer gpa.free(bytes);
        \\    return bytes;
        \\}
    , true);
    try expectHandoff(prelude ++
        \\    const other = try gpa.alloc(u8, 2);
        \\    defer gpa.free(other);
        \\    return bytes;
        \\}
    , true);
}

test "handoff work spends the caller's counter and NULL adds no new meter" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) ![]u8 {
        \\    const bytes = try gpa.alloc(u8, 2);
        \\    return bytes;
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    var value: Ast.Node.Index = undefined;
    var boundary: Ast.TokenIndex = undefined;
    var found = false;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        if (tree.nodeTag(node) != .@"return") continue;
        value = tree.nodeData(node).opt_node.unwrap() orelse continue;
        boundary = tree.firstToken(node);
        found = true;
    }
    try std.testing.expect(found);
    var remaining: u32 = 0;
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, allocationSurvivesHandoff(
        &cache, value, boundary, .{ .remaining = &remaining },
    ));
    budget_mod.clear();
    try std.testing.expect(try allocationSurvivesHandoff(&cache, value, boundary, .{}));
}

test "a null handoff counter seeds no root cap of its own" {
    const gpa = std.testing.allocator;
    var text: std.ArrayList(u8) = .empty;
    defer text.deinit(gpa);
    var scratch: [48]u8 = undefined;
    var index: u32 = 0;
    while (index <= work_limit) : (index += 1) {
        const line = try std.fmt.bufPrint(&scratch, "const padding{d} = 0;\n", .{index});
        try text.appendSlice(gpa, line);
    }
    try text.appendSlice(gpa,
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) ![]u8 {
        \\    const bytes = try gpa.alloc(u8, 2);
        \\    const alias = bytes;
        \\    return alias;
        \\}
    );
    try text.append(gpa, 0);
    const source: [:0]const u8 = text.items[0 .. text.items.len - 1 :0];
    try expectHandoff(source, true);
}

