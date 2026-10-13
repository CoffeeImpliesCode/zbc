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
// Alias queries share the full failure contract of canonical effects and fresh proofs.
const BudgetError = call_summary_mod.Error;
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

const work_limit: u32 = call_summary_mod.actual_query_work_limit;
const max_path = 16;
const max_origins = 32;

/// Optional context of an enclosing semantic query. `frame` borrows the original
/// resolver; all input nodes still belong to `cache.tree`. `remaining` borrows
/// that query's counter, and `declaration` identifies the current function when
/// the caller knows it.
/// `effects_state` borrows the active enclosing call-summary State (`queries`
/// is nonzero), with that state's resolver and counter. It is never owned or
/// deinitialized here. Without a counter, alias queries start one 50,000-step
/// root allowance; handoff queries add no allowance of their own.
pub const QueryContext = struct {
    frame: ?engine.TypeResolver.ResolutionFrame = null,
    remaining: ?*u32 = null,
    declaration: ?Ast.Node.Index = null,
    effects_state: ?*call_summary_mod.State = null,
};

/// What one FileCache keeps for its storage-alias queries: the syntax-only
/// index of each declaration and every completed positive answer.
///
/// A declaration's index is a pure function of its immutable tree, so the cache
/// that owns the tree owns the index for its whole lifetime: every query, root
/// and foreign caller shares it, exactly as they share `FileCache.localBindings`.
/// Entries are heap cells, so a borrowed `*const SyntaxIndex` survives growth.
/// Allocate through the owning cache's allocator and pass it to `deinit`.
pub const FileState = struct {
    indexes: std.AutoHashMapUnmanaged(Ast.Node.Index, *SyntaxIndex) = .empty,
    /// Completed `mayShareStorageAt` verdicts. Only a query that returned
    /// normally publishes; every error, budget cut-off included, publishes none.
    answers: std.HashMapUnmanaged(AnswerKey, bool, AnswerKeyContext, 80) = .empty,
    /// Root questions whose standalone walk exhausted its whole allowance.
    exhausted: std.HashMapUnmanaged(AnswerKey, Exhausted, AnswerKeyContext, 80) = .empty,
    /// Owns the selection paths borrowed by `answers` and `exhausted` keys.
    answer_text: ?std.heap.ArenaAllocator = null,

    pub fn deinit(self: *FileState, gpa: std.mem.Allocator) void {
        var cells = self.indexes.valueIterator();
        while (cells.next()) |cell| {
            cell.*.deinit(gpa);
            gpa.destroy(cell.*);
        }
        self.indexes.deinit(gpa);
        self.exhausted.deinit(gpa);
        self.answers.deinit(gpa);
        if (self.answer_text) |*arena| arena.deinit();
        self.* = .{};
    }

    /// A hit and a first build both charge one lookup: the single linear pass
    /// that builds an index is a cache-owned fact about the file, never
    /// per-query work, and runs once for the cache's lifetime.
    fn indexFor(
        query: *Query,
        cache: *FileCache,
        declaration: Ast.Node.Index,
        bindings: []const bindings_mod.Binding,
    ) BudgetError!*const SyntaxIndex {
        try query.charge();
        const gpa = cache.gpa;
        const gop = try cache.alias_state.indexes.getOrPut(gpa, declaration);
        if (gop.found_existing) return gop.value_ptr.*;
        // Built privately: a failed build leaves no half-filled entry behind.
        errdefer _ = cache.alias_state.indexes.remove(declaration);
        const cell = try gpa.create(SyntaxIndex);
        errdefer gpa.destroy(cell);
        cell.* = try SyntaxIndex.build(cache, declaration, bindings, gpa);
        gop.value_ptr.* = cell;
        return cell;
    }

    fn publish(self: *FileState, cache: *FileCache, key: AnswerKey, shares: bool) BudgetError!void {
        const gpa = cache.gpa;
        if (self.answers.contains(key)) return;
        if (self.answer_text == null) self.answer_text = std.heap.ArenaAllocator.init(gpa);
        const text = self.answer_text.?.allocator();
        var owned = key;
        owned.left_path = try text.dupe(u8, key.left_path);
        owned.right_path = try text.dupe(u8, key.right_path);
        try self.answers.put(gpa, owned, shares);
    }

    /// Remember that the standalone walk of `key` ran `known.budget` out.  The
    /// key's paths are copied; recording is optional, so a refused allocation
    /// only loses the shortcut.
    fn recordExhausted(self: *FileState, cache: *FileCache, key: AnswerKey, known: Exhausted) void {
        if (self.exhausted.getPtr(key)) |existing| {
            existing.* = known;
            return;
        }
        const gpa = cache.gpa;
        if (self.answer_text == null) self.answer_text = std.heap.ArenaAllocator.init(gpa);
        const text = self.answer_text.?.allocator();
        var owned = key;
        owned.left_path = text.dupe(u8, key.left_path) catch return;
        owned.right_path = text.dupe(u8, key.right_path) catch return;
        self.exhausted.put(gpa, owned, known) catch {};
    }
};

/// A root question whose standalone walk ran its whole allowance out.  The
/// walk is a pure function of the key, the allowance it started with and the
/// file's completed answers, which only ever make a later walk cheaper; so a
/// later question of the same key with no more allowance stops the same way.
/// Never an answer: only the failure to give one.
const Exhausted = struct {
    /// The allowance the exhausted walk started with.
    budget: u32,
    diagnostic: budget_mod.Diagnostic,
};

/// Everything a verdict depends on: the cache's own tree is implied, and the
/// resolver context is the complete contextual identity the query ran in. The
/// handoff-only and effects-state inputs never reach a positive answer.
const AnswerKey = struct {
    at: Ast.Node.Index,
    left: Ast.Node.Index,
    left_path: []const u8,
    right: Ast.Node.Index,
    right_path: []const u8,
    domain: Domain,
    declaration: ?Ast.Node.Index,
    /// Without a frame the cache's own resolver answers type questions.
    cache_resolver: ?*anyopaque,
    frame: ?FrameIdentity,

    fn of(
        cache: *const FileCache,
        at_node: Ast.Node.Index,
        left: StorageSelection,
        right: StorageSelection,
        domain: Domain,
        context: QueryContext,
    ) AnswerKey {
        return .{
            .at = at_node,
            .left = left.node,
            .left_path = left.path,
            .right = right.node,
            .right_path = right.path,
            .domain = domain,
            .declaration = context.declaration,
            .cache_resolver = cache.zls,
            .frame = if (context.frame) |frame| .{
                .resolver = frame.resolver,
                .handle = frame.handle,
                .container_type = frame.container_type,
                .actual_type = frame.actual_type,
            } else null,
        };
    }
};

const FrameIdentity = struct {
    resolver: *engine.TypeResolver,
    handle: @FieldType(engine.TypeResolver.ResolutionFrame, "handle"),
    container_type: ?engine.TypeResolver.ActualType,
    actual_type: ?engine.TypeResolver.ActualTypeID,
};

const AnswerKeyContext = struct {
    pub fn hash(_: AnswerKeyContext, key: AnswerKey) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&key.at));
        hasher.update(std.mem.asBytes(&key.left));
        hasher.update(key.left_path);
        hasher.update(std.mem.asBytes(&key.right));
        hasher.update(key.right_path);
        hasher.update(std.mem.asBytes(&key.domain));
        const declared: u64 = if (key.declaration) |declaration| @as(u64, @intFromEnum(declaration)) + 1 else 0;
        hasher.update(std.mem.asBytes(&declared));
        hasher.update(std.mem.asBytes(&key.cache_resolver));
        const present: u8 = @intFromBool(key.frame != null);
        hasher.update(std.mem.asBytes(&present));
        if (key.frame) |frame| {
            hasher.update(std.mem.asBytes(&frame.resolver));
            hasher.update(std.mem.asBytes(&frame.handle.document));
            hasher.update(std.mem.asBytes(&frame.handle.module));
            // Instantiated identities are graphs: hash them structurally, never
            // by address.
            if (frame.container_type) |container| hasher.update(std.mem.asBytes(&container.hash64()));
            if (frame.actual_type) |actual| hasher.update(std.mem.asBytes(&actual.hash64()));
        }
        return hasher.final();
    }

    pub fn eql(_: AnswerKeyContext, a: AnswerKey, b: AnswerKey) bool {
        if (a.at != b.at or a.left != b.left or a.right != b.right or a.domain != b.domain) return false;
        if (!std.mem.eql(u8, a.left_path, b.left_path) or !std.mem.eql(u8, a.right_path, b.right_path)) return false;
        if (a.declaration != b.declaration or a.cache_resolver != b.cache_resolver) return false;
        const left = a.frame orelse return b.frame == null;
        const right = b.frame orelse return false;
        if (left.resolver != right.resolver or !left.handle.eql(right.handle)) return false;
        if (!optionalTypeEql(left.container_type, right.container_type)) return false;
        return optionalTypeEql(left.actual_type, right.actual_type);
    }

    fn optionalTypeEql(a: ?engine.TypeResolver.ActualType, b: ?engine.TypeResolver.ActualType) bool {
        const left = a orelse return b == null;
        const right = b orelse return false;
        return left.eql(right);
    }
};

const ParentMap = std.AutoHashMapUnmanaged(Ast.Node.Index, Ast.Node.Index);
const IdentifierUses = std.StringHashMapUnmanaged(std.ArrayList(Ast.Node.Index));
/// Positions in `FileCache.localBindings(...).items`, by exact binding spelling.
const BindingBuckets = std.StringHashMapUnmanaged(std.ArrayList(u32));

const SyntaxIndex = struct {
    nodes: std.ArrayList(Ast.Node.Index) = .empty,
    /// Return candidates in the same traversal order as `nodes`. Ownership
    /// and boundary checks stay query-local; non-return syntax is irrelevant.
    returns: std.ArrayList(Ast.Node.Index) = .empty,
    parents: ParentMap = .empty,
    /// Completed source facts only. Identifier buckets preserve traversal
    /// order and the binder's exact raw token spelling, including quoted IDs.
    identifier_uses: IdentifierUses = .empty,
    /// The declaration's own bindings, borrowed from the cache's arena-backed
    /// table, bucketed by name so a use scans only same-spelled candidates.
    bindings: []const bindings_mod.Binding = &.{},
    binding_buckets: BindingBuckets = .empty,

    fn deinit(self: *SyntaxIndex, gpa: std.mem.Allocator) void {
        self.nodes.deinit(gpa);
        self.returns.deinit(gpa);
        self.parents.deinit(gpa);
        var uses = self.identifier_uses.valueIterator();
        while (uses.next()) |list| list.deinit(gpa);
        self.identifier_uses.deinit(gpa);
        var buckets = self.binding_buckets.valueIterator();
        while (buckets.next()) |list| list.deinit(gpa);
        self.binding_buckets.deinit(gpa);
    }

    fn recordNode(self: *SyntaxIndex, tree: *const Ast, gpa: std.mem.Allocator, node: Ast.Node.Index) BudgetError!void {
        if (tree.nodeTag(node) == .@"return") try self.returns.append(gpa, node);
        if (tree.nodeTag(node) == .identifier) {
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            const entry = try self.identifier_uses.getOrPut(gpa, name);
            if (!entry.found_existing) entry.value_ptr.* = .empty;
            try entry.value_ptr.append(gpa, node);
        }
    }

    /// One pass over the declaration's syntax and its bindings. The index is
    /// complete or absent; the caller never sees a partial one.
    fn build(
        cache: *FileCache,
        declaration: Ast.Node.Index,
        bindings: []const bindings_mod.Binding,
        gpa: std.mem.Allocator,
    ) BudgetError!SyntaxIndex {
        var index: SyntaxIndex = .{ .bindings = bindings };
        errdefer index.deinit(gpa);
        var stack: std.ArrayList(Traversal) = .empty;
        defer stack.deinit(gpa);
        const tree = cache.tree;
        try index.nodes.append(gpa, declaration);
        try index.recordNode(tree, gpa, declaration);
        try stack.append(gpa, .{
            .node = declaration,
            .children = Iterator.init(tree, declaration),
        });
        while (stack.items.len != 0) {
            const top = stack.items.len - 1;
            const parent = stack.items[top].node;
            const child = stack.items[top].children.next(tree) orelse {
                stack.items.len -= 1;
                continue;
            };
            try index.parents.put(gpa, child, parent);
            try index.nodes.append(gpa, child);
            try index.recordNode(tree, gpa, child);
            try stack.append(gpa, .{
                .node = child,
                .children = Iterator.init(tree, child),
            });
        }
        for (bindings, 0..) |binding, position| {
            const entry = try index.binding_buckets.getOrPut(gpa, binding.name);
            if (!entry.found_existing) entry.value_ptr.* = .empty;
            try entry.value_ptr.append(gpa, @intCast(position));
        }
        return index;
    }
};

const Traversal = struct {
    node: Ast.Node.Index,
    children: Iterator,
};

fn tokenContains(tree: *const Ast, node: Ast.Node.Index, token: Ast.TokenIndex) bool {
    return tree.firstToken(node) <= token and token <= tree.lastToken(node);
}

fn enclosingFunction(
    query: *Query,
    cache: *FileCache,
    position: Ast.Node.Index,
) BudgetError!?Ast.Node.Index {
    const tree = cache.tree;
    const token = tree.firstToken(position);
    const roots = tree.rootDecls();
    var low: usize = 0;
    var high: usize = roots.len;
    while (low < high) {
        try query.charge();
        const middle = low + (high - low) / 2;
        if (tree.lastToken(roots[middle]) < token) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    if (low == roots.len) return null;
    const root = roots[low];
    try query.charge();
    if (!tokenContains(tree, root, token)) return null;

    const gpa = query.root_cache.gpa;
    var stack: std.ArrayList(Traversal) = .empty;
    defer stack.deinit(gpa);
    var found: ?Ast.Node.Index = null;
    var found_depth: usize = 0;
    try query.charge();
    try stack.append(gpa, .{ .node = root, .children = Iterator.init(tree, root) });
    while (stack.items.len != 0) {
        const top = stack.items.len - 1;
        const current = stack.items[top].node;
        if (tree.nodeTag(current) == .fn_decl and top >= found_depth) {
            found = current;
            found_depth = top;
        }
        const child = stack.items[top].children.next(tree) orelse {
            stack.items.len -= 1;
            continue;
        };
        try query.charge();
        if (!tokenContains(tree, child, token)) continue;
        try query.charge();
        try stack.append(gpa, .{
            .node = child,
            .children = Iterator.init(tree, child),
        });
    }
    return found;
}

/// False means a positively proved private construction cannot share the selected
/// storage at this call. Same origins, incoming fields, copies, publication,
/// unsupported writes and cycles answer true. No spelling establishes disjointness.
/// One counter covers this query's AST work and its fresh-producer work; existing
/// canonical type/declaration queries retain their own bounds. A completed answer
/// is kept on `cache` under the complete question and context and a repeat
/// charges one lookup; an error, a budget cut-off included, keeps nothing.
/// The caller owns no result allocation.
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
        .root_cache = cache,
        .at_node = at_node,
        .remaining = context.remaining orelse &remaining,
        .resolution = context.frame,
        .declaration = context.declaration,
        .effects_state = context.effects_state,
    };
    const key = AnswerKey.of(cache, at_node, left, right, domain, context);
    // A failure is a fact about the key only for a question that owns its
    // whole allowance and runs on no stack: no enclosing effect query, no
    // borrowed counter, no open fresh-storage walk of this file.
    const standalone = context.effects_state == null and context.remaining == null and
        cache.fresh_visiting.count() == 0;
    const state = &cache.alias_state;
    if (standalone and !state.answers.contains(key)) {
        if (state.exhausted.get(key)) |known| {
            if (work_limit <= known.budget) return budget_mod.fail(known.diagnostic);
        }
    }
    if (!standalone) return answerRoot(&query, key, left, right, domain);
    const filed = call_summary_mod.filedAnswerCount(cache);
    const guard = call_summary_mod.PendingGuard.begin();
    const result = answerRoot(&query, key, left, right, domain);
    const own = guard.end();
    if (result) |shares| {
        if (state.exhausted.count() != 0) _ = state.exhausted.remove(key);
        return shares;
    } else |err| {
        // Only an allowance run out, by a walk that completed nothing a repeat
        // could reuse, is a failure the key alone explains.
        if (err == error.AnalysisBudgetExceeded and remaining == 0 and
            cache.fresh_visiting.count() == 0 and
            call_summary_mod.filedAnswerCount(cache) == filed)
        {
            if (own) |first| state.recordExhausted(cache, key, .{
                .budget = work_limit,
                .diagnostic = first,
            });
        }
        return err;
    }
}

fn answerRoot(
    query: *Query,
    key: AnswerKey,
    left: StorageSelection,
    right: StorageSelection,
    domain: Domain,
) BudgetError!bool {
    return query.answer(key, left, right, domain) catch |err| {
        if (err == error.AnalysisBudgetExceeded and query.remaining.?.* == 0) {
            return query.failure();
        }
        return err;
    };
}

/// Internal lifetime guard after a producer has proved construction. This does
/// not grant freshness, privacy, or disjointness. Local header aliases retain
/// their actual shared allocation identity through the successful handoff.
/// Every returning catch/orelse outcome keeps its own lifetime dependencies.
/// Typed address-free element writes preserve the payload, not a rebound header.
/// A null counter adds no allowance or cap to the caller's existing fresh walk.
pub fn allocationSurvivesHandoff(
    cache: *FileCache,
    value_node: Ast.Node.Index,
    boundary: Ast.TokenIndex,
    context: QueryContext,
) BudgetError!bool {
    var query: Query = .{
        .root_cache = cache,
        .at_node = value_node,
        .remaining = context.remaining,
        .resolution = context.frame,
        .declaration = context.declaration,
        .lifetime_only = true,
        .effects_state = context.effects_state,
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

const BindingOrigin = enum { local, param, loop_capture };

const BindingFacts = struct {
    name_token: Ast.TokenIndex,
    is_const: bool,
    rhs_first: Ast.TokenIndex,
    rhs_last: Ast.TokenIndex,
    origin: BindingOrigin,

    fn from(binding: *const bindings_mod.Binding) BindingFacts {
        return .{
            .name_token = binding.name_token,
            .is_const = binding.is_const,
            .rhs_first = binding.rhs_first,
            .rhs_last = binding.rhs_last,
            .origin = switch (binding.origin) {
                .param => .param,
                .loop_capture => .loop_capture,
                else => .local,
            },
        };
    }
};

const Root = struct {
    binding: BindingFacts,
    path: Path,
    addressed: bool = false,
};
const Active = struct { cache: *FileCache, token: Ast.TokenIndex, path: Path };

const Frame = struct {
    cache: *FileCache,
    /// The cache-owned syntax facts of `declaration`; complete and immutable.
    index: *const SyntaxIndex,
    declaration: Ast.Node.Index,
    body: Ast.Node.Index,
    proto: Ast.full.FnProto,
    resolution: ?engine.TypeResolver.ResolutionFrame = null,
    return_boundary: ?Ast.TokenIndex = null,

    fn init(
        query: *Query,
        cache: *FileCache,
        position: Ast.Node.Index,
        known_declaration: ?Ast.Node.Index,
    ) BudgetError!?Frame {
        const tree = cache.tree;
        const declaration = known_declaration orelse
            (if (cache == query.root_cache) query.declaration else null) orelse
            (try enclosingFunction(query, cache, position)) orelse return null;
        if (tree.nodeTag(declaration) != .fn_decl) return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, declaration) orelse return null;
        const body = tokens.bodyOf(tree, declaration) orelse return null;
        const bindings = try cache.localBindings(proto, body);
        const index = try FileState.indexFor(query, cache, declaration, bindings.items);
        try query.charge();
        if (position != declaration and !index.parents.contains(position)) return null;
        return .{
            .cache = cache,
            .index = index,
            .declaration = declaration,
            .body = body,
            .proto = proto,
        };
    }

    fn freshWalk(self: Frame, query: *Query, claim: FileCache.TokenRange) fresh.FreshWalk {
        return .{
            .claim = .{ .first = claim.first, .last = claim.last },
            .depth = 0,
            .remaining = query.remaining,
            .frame = self.resolution,
        };
    }

    fn parentOf(self: Frame, node: Ast.Node.Index) ?Ast.Node.Index {
        return self.index.parents.get(node);
    }

    /// The binding a use of this identifier names, with the exact answer and
    /// tie-break of `LocalBindings.findAt`. Only same-spelled candidates are
    /// examined, and exactly those are charged.
    fn bindingAt(
        self: Frame,
        query: *Query,
        node: Ast.Node.Index,
    ) BudgetError!?BindingFacts {
        try query.charge();
        const tree = self.cache.tree;
        const token = tree.nodeMainToken(node);
        const bucket = self.index.binding_buckets.get(tree.tokenSlice(token)) orelse return null;
        var found: ?*const bindings_mod.Binding = null;
        for (bucket.items) |position| {
            try query.charge();
            const binding = &self.index.bindings[position];
            if (binding.name_token > token) continue;
            if (token < binding.scope_open or token > binding.scope_close) continue;
            if (found == null or binding.name_token > found.?.name_token) found = binding;
        }
        return BindingFacts.from(found orelse return null);
    }

    fn bindingNamed(
        self: Frame,
        query: *Query,
        name_token: Ast.TokenIndex,
    ) BudgetError!?BindingFacts {
        try query.charge();
        // A declaration's exact name token selects one same-spelled bucket,
        // not every unrelated binding in the body on each handoff round.
        const bucket = self.index.binding_buckets.get(self.cache.tree.tokenSlice(name_token)) orelse return null;
        for (bucket.items) |position| {
            try query.charge();
            const binding = &self.index.bindings[position];
            if (binding.name_token == name_token) return BindingFacts.from(binding);
        }
        return null;
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
                .grouped_expression, .unwrap_optional => node = tree.nodeData(node).node_and_token[0],
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
        self: Frame,
        query: *Query,
        node: Ast.Node.Index,
        boundary: Ast.TokenIndex,
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
    declaration: ?Ast.Node.Index = null,
    effects_state: ?*call_summary_mod.State = null,
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
        return self.report(.storage_alias_work, work_limit, work_limit);
    }

    /// Record a labelled budget failure at this query's own position.
    fn report(self: *Query, limit: budget_mod.Limit, cap: u32, reached: u32) BudgetError {
        const tree = self.root_cache.tree;
        const token = tree.firstToken(self.at_node);
        return budget_mod.fail(.{
            .limit = limit,
            .limit_value = cap,
            .reached = reached,
            .byte = tree.tokens.items(.start)[token],
            .document = budget_mod.documentForTree(tree),
        });
    }

    fn charge(self: *Query) BudgetError!void {
        const remaining = self.remaining orelse return;
        if (remaining.* == 0) return self.failure();
        remaining.* -= 1;
    }

    /// The cached verdict for `key`, else a fresh proof that publishes its own.
    /// A proof that runs while a fresh-storage walk of this file is still open
    /// may have met that walk's cycle guard, which answers unproved rather than
    /// settled; such a verdict is returned but never kept.
    fn answer(
        self: *Query,
        key: AnswerKey,
        left: StorageSelection,
        right: StorageSelection,
        domain: Domain,
    ) BudgetError!bool {
        const cache = self.root_cache;
        if (cache.alias_state.answers.get(key)) |shares| {
            try self.charge();
            return shares;
        }
        const shares = try self.run(left, right, domain);
        if (cache.fresh_visiting.count() == 0) try cache.alias_state.publish(cache, key, shares);
        return shares;
    }

    fn run(self: *Query, left: StorageSelection, right: StorageSelection, domain: Domain) BudgetError!bool {
        var frame = (try Frame.init(self, self.root_cache, self.at_node, null)) orelse return true;
        frame.resolution = self.resolution;
        if (try frame.deferred(self, self.at_node, frame.cache.tree.firstToken(self.at_node)))
            return true;
        const a = try frame.root(self, left);
        const b = try frame.root(self, right);
        const boundary = frame.cache.tree.firstToken(self.at_node);
        if (a != null and b != null and a.?.binding.name_token == b.?.binding.name_token) {
            if (Path.overlaps(a.?.path, b.?.path)) return true;
            // A resolved address-free pointee graph has no hidden buffer
            // aliases: nonoverlapping fields are distinct object cells.
            if (domain == .reachable_storage and a.?.binding.origin == .param and
                try self.formalObjectAddressFree(&frame, a.?.binding)) return false;
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

    fn nonreturningLiteral(tree: *const Ast, node: Ast.Node.Index) bool {
        return tree.firstToken(node) == tree.lastToken(node) and
            tree.tokenTag(tree.firstToken(node)) == .keyword_unreachable;
    }

    fn lifetimeSeed(self: *Query, frame: *Frame, node: Ast.Node.Index, depth: u8) BudgetError!bool {
        try self.charge();
        if (depth == max_origins) return false;
        // Scalar payloads carry no allocation identity, even when they are
        // computed from a formal rather than written as literals.
        if (try self.expressionAddressFree(frame, node)) return true;
        if (try frame.root(self, .{ .node = node })) |root|
            return self.addLifetimeAlias(root);
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .@"try", .address_of, .deref => return self.lifetimeSeed(frame, tree.nodeData(node).node, depth + 1),
            .grouped_expression, .unwrap_optional => return self.lifetimeSeed(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            .slice, .slice_open, .slice_sentinel => return self.lifetimeSeed(frame, tree.fullSlice(node).?.ast.sliced, depth + 1),
            .@"catch", .@"orelse" => {
                const pair = tree.nodeData(node).node_and_node;
                if (!try self.lifetimeSeed(frame, pair[0], depth + 1)) return false;
                return nonreturningLiteral(tree, pair[1]) or
                    try self.lifetimeSeed(frame, pair[1], depth + 1);
            },
            .call, .call_one, .call_comma, .call_one_comma, .enum_literal, .field_access, .number_literal, .char_literal, .string_literal, .multiline_string_literal => return true,
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
                Path.overlaps(known.path, target.path))
            {
                if (source.binding.name_token >= target.binding.name_token) return false;
                related = true;
                const path = (try self.pathTail(target.path, known.path, source.path)) orelse source.path;
                if (!try self.addLifetimeAlias(.{ .binding = source.binding, .path = path })) return false;
            }
            if (known.binding.name_token == source.binding.name_token and
                Path.overlaps(known.path, source.path))
            {
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
        self: *Query,
        frame: *Frame,
        node: Ast.Node.Index,
        target: Root,
        depth: u8,
    ) BudgetError!bool {
        try self.charge();
        if (depth == max_origins) return false;
        if (try frame.root(self, .{ .node = node })) |source|
            return self.lifetimeLink(target, source);
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .@"try", .address_of, .deref => return self.lifetimeLinks(frame, tree.nodeData(node).node, target, depth + 1),
            .grouped_expression, .unwrap_optional => return self.lifetimeLinks(frame, tree.nodeData(node).node_and_token[0], target, depth + 1),
            .slice, .slice_open, .slice_sentinel => return self.lifetimeLinks(frame, tree.fullSlice(node).?.ast.sliced, target, depth + 1),
            .@"catch", .@"orelse" => {
                const pair = tree.nodeData(node).node_and_node;
                if (!try self.lifetimeLinks(frame, pair[0], target, depth + 1)) return false;
                return nonreturningLiteral(tree, pair[1]) or
                    try self.lifetimeLinks(frame, pair[1], target, depth + 1);
            },
            .call, .call_one, .call_comma, .call_one_comma => return self.lifetimeCallLinks(frame, node, target),
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                // Unrelated declarations do not affect the selected lifetime.
                // A selected computed block needs its effects proved as well.
                for (self.lifetime_aliases[0..self.lifetime_alias_count]) |alias| {
                    try self.charge();
                    if (alias.binding.name_token == target.binding.name_token and
                        Path.overlaps(alias.path, target.path)) return false;
                }
                return true;
            },
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
        var frame = (try Frame.init(self, self.root_cache, value_node, null)) orelse return false;
        frame.resolution = self.resolution;
        if (try self.expressionAddressFree(&frame, value_node)) return true;
        frame.return_boundary = boundary;
        if (!try self.lifetimeSeed(&frame, value_node, 0)) return false;
        const tree = frame.cache.tree;
        var rounds: usize = 0;
        while (true) {
            const before = self.lifetime_alias_count;
            for (frame.index.nodes.items) |node| {
                try self.charge();
                const declaration = tree.fullVarDecl(node) orelse continue;
                const name = declaration.ast.mut_token + 1;
                if (name >= boundary or !try frame.owns(self, node)) continue;
                const initializer_node = declaration.ast.init_node.unwrap() orelse continue;
                const binding = (try frame.bindingNamed(self, name)) orelse continue;
                const target: Root = .{ .binding = binding, .path = .{} };
                if (!try self.lifetimeLinks(&frame, initializer_node, target, 0)) return false;
            }
            // A returned inline aggregate owns its field cells. Track the
            // values installed there as well as the aggregate itself, so a
            // later free through the source header still invalidates handoff.
            for (frame.index.nodes.items) |node| {
                try self.charge();
                if (tree.nodeTag(node) != .assign or tree.firstToken(node) >= boundary) continue;
                const pair = tree.nodeData(node).node_and_node;
                if (!try self.inlineFieldDefinition(&frame, pair[0])) continue;
                const target = (try frame.root(self, .{ .node = pair[0] })) orelse continue;
                var relevant = false;
                for (self.lifetime_aliases[0..self.lifetime_alias_count]) |alias| {
                    try self.charge();
                    if (alias.binding.name_token == target.binding.name_token and
                        Path.overlaps(alias.path, target.path)) relevant = true;
                }
                if (relevant and !try self.lifetimeSeed(&frame, pair[1], 0)) return false;
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
            if (frame.cache.tree.nodeTag(parent) == .assign) {
                const pair = frame.cache.tree.nodeData(parent).node_and_node;
                if (node != pair[1] or !try self.inlineFieldDefinition(frame, pair[0])) return false;
                const target = (try frame.root(self, .{ .node = pair[0] })) orelse return false;
                for (self.lifetime_aliases[0..self.lifetime_alias_count]) |alias| {
                    try self.charge();
                    if (alias.binding.name_token == target.binding.name_token and
                        Path.overlaps(alias.path, target.path)) return true;
                }
                return false;
            }
            switch (frame.cache.tree.nodeTag(parent)) {
                .call, .call_one, .call_comma, .call_one_comma, .block, .block_semicolon, .block_two, .block_two_semicolon, .fn_decl => return false,
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
            fresh.calleeQueryToken(frame.cache.tree, call),
            frame.resolution,
        )) orelse return false;
        const summary = canonical.summary orelse return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration) orelse return false;
        var parameters = proto.iterate(canonical.callee.tree);
        var index: u32 = 0;
        while (parameters.next() != null) : (index += 1) {
            try self.charge();
            const dependency = summary.returnedParamDependency(index) orelse return false;
            if (!dependency) continue;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try canonical.callArgumentFor(frame.cache, &argument_buffer, index)) orelse return false;
            const source = (try frame.root(self, .{ .node = argument })) orelse return false;
            if (!try self.lifetimeLink(target, source)) return false;
        }
        return true;
    }

    /// Only a local struct's own direct field cell is construction storage.
    /// Pointer receivers, nested projections, and whole-header assignments
    /// cannot receive this exemption from a field's spelling.
    fn inlineFieldDefinition(self: *Query, frame: *Frame, use: Ast.Node.Index) BudgetError!bool {
        try self.charge();
        const tree = frame.cache.tree;
        if (!cellDefinition(frame, use) or tree.nodeTag(use) != .field_access) return false;
        const access = tree.nodeData(use).node_and_token;
        if (tree.nodeTag(access[0]) != .identifier) return false;
        const binding = (try frame.bindingAt(self, access[0])) orelse return false;
        if (binding.origin != .local) return false;
        if (frame.resolution orelse if (frame.cache.zls) |resolver| resolver.resolutionFrame() else null) |resolution| {
            try self.charge();
            const ty = (try resolution.typeOfNode(access[0])) orelse return false;
            return resolution.resolver.typeTag(ty) == .@"struct";
        }
        for (frame.index.nodes.items) |node| {
            try self.charge();
            const declaration = tree.fullVarDecl(node) orelse continue;
            if (declaration.ast.mut_token + 1 != binding.name_token) continue;
            const type_node = declaration.ast.type_node.unwrap() orelse return false;
            const name = (try fresh.typePathName(frame.cache, tree.firstToken(type_node), tree.lastToken(type_node), self.remaining)) orelse return false;
            const owner = (try fresh.resolveDeclaredType(frame.cache, name, 0, self.remaining)) orelse return false;
            if (owner.info.kind != .struct_) return false;
            for (owner.info.fields) |field| {
                try self.charge();
                if (std.mem.eql(u8, field.name, tree.tokenSlice(access[1]))) return true;
            }
            return false;
        }
        return false;
    }

    fn expressionAddressFree(self: *Query, frame: *Frame, node: Ast.Node.Index) BudgetError!bool {
        try self.charge();
        const resolution = frame.resolution orelse
            (frame.cache.zls orelse return self.addressFreeValue(frame, node, 0)).resolutionFrame();
        const ty = (try resolution.typeOfNode(node)) orelse return false;
        return fresh.actualTypeAddressFree(resolution, ty, 0, self.remaining);
    }

    fn lifetimeCallSafe(
        self: *Query,
        frame: *Frame,
        canonical: FileCache.ActualCallSummary,
        selected: Root,
    ) BudgetError!bool {
        const tree = frame.cache.tree;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, canonical.callee.call_node) orelse return false;
        const token = fresh.calleeQueryToken(tree, call);
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration) orelse return false;
        var parameters = proto.iterate(canonical.callee.tree);
        var index: u32 = 0;
        var found = false;
        while (parameters.next() != null) : (index += 1) {
            try self.charge();
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try canonical.callArgumentFor(frame.cache, &argument_buffer, index)) orelse continue;
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
                    .param = index,
                    .path = path,
                } }, .{
                    .frame = frame.resolution,
                    .remaining = self.remaining,
                    .declaration = frame.declaration,
                    .effects_state = self.effects_state,
                })) orelse return false;
            };
            switch (effect) {
                .read_only, .writes_without_invalidation => {},
                .may_invalidate, .unknown => return false,
            }
        }
        if (!found) return false;
        const global = (try frame.cache.callEffectAt(token, .unrooted, .{
            .frame = frame.resolution,
            .remaining = self.remaining,
            .declaration = frame.declaration,
            .effects_state = self.effects_state,
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

    fn lifetimeBuiltinWriteSafe(
        self: *Query,
        frame: *Frame,
        use: Ast.Node.Index,
        builtin: Ast.Node.Index,
    ) BudgetError!bool {
        const tree = frame.cache.tree;
        if (!tokens.isWriteFirstArgBuiltin(tree.tokenSlice(tree.nodeMainToken(builtin))))
            return false;
        const data = tree.nodeData(builtin);
        const destination = switch (tree.nodeTag(builtin)) {
            .builtin_call_two, .builtin_call_two_comma => data.opt_node_and_opt_node[0].unwrap() orelse return false,
            .builtin_call, .builtin_call_comma => blk: {
                const operands = tree.extraDataSlice(data.extra_range, Ast.Node.Index);
                if (operands.len == 0) return false;
                break :blk operands[0];
            },
            else => return false,
        };
        if (destination != use) return false;
        const resolution = frame.resolution orelse
            (frame.cache.zls orelse return false).resolutionFrame();
        // The intrinsic mutates pointee cells. A slice or pointer header is
        // still address-bearing; only its actual destination elements matter.
        return self.pointeeAddressFree(resolution, destination);
    }

    fn initializer(self: *Query, frame: *Frame, root: Root) BudgetError!?Ast.Node.Index {
        try self.charge();
        // The shared binding-to-initializer path, `nodeForExactSpan` over the
        // binding's RHS span, finds the node. The span alone cannot tell a
        // declaration's initializer from a parameter's type, a capture's
        // iterable or a destructuring target's shared RHS (the binder gives
        // `const a, const b = x;` a binding `b` with RHS `x`). The parent
        // must be the variable declaration this very name token introduced,
        // with that node as its initializer.
        const binding = root.binding;
        const node = frame.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return null;
        const parent = frame.parentOf(node) orelse return null;
        const var_decl = frame.cache.tree.fullVarDecl(parent) orelse return null;
        if (var_decl.ast.mut_token + 1 != binding.name_token) return null;
        if (var_decl.ast.init_node.unwrap() != node) return null;
        return node;
    }

    fn private(
        self: *Query,
        frame: *Frame,
        root: Root,
        boundary: Ast.TokenIndex,
        domain: Domain,
        allowed_store: ?Ast.Node.Index,
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
            .cache = frame.cache,
            .token = root.binding.name_token,
            .path = root.path,
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
        self: *Query,
        frame: *Frame,
        node: Ast.Node.Index,
        path: Path,
        domain: Domain,
    ) BudgetError!bool {
        if (path.len == 0) return self.value(frame, node, domain);
        try self.charge();
        if (self.value_depth == 64) return false;
        self.value_depth += 1;
        defer self.value_depth -= 1;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .address_of => return false,
            .@"try", .deref => return self.projectedValue(frame, tree.nodeData(node).node, path, domain),
            .grouped_expression, .unwrap_optional => return self.projectedValue(frame, tree.nodeData(node).node_and_token[0], path, domain),
            .call, .call_one, .call_comma, .call_one_comma => return self.callValue(frame, node, domain, path),
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
            .grouped_expression, .unwrap_optional => return self.value(frame, tree.nodeData(expression).node_and_token[0], domain),
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
            .array_init, .array_init_comma, .array_init_dot, .array_init_dot_comma, .array_init_one, .array_init_one_comma, .array_init_dot_two, .array_init_dot_two_comma => {
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
            .call, .call_one, .call_comma, .call_one_comma => return self.callValue(frame, expression, domain, .{}),
            else => {},
        }
        var declared_type: ?Ast.Node.Index = null;
        if (frame.parentOf(expression)) |parent| {
            if (tree.fullVarDecl(parent)) |decl| declared_type = decl.ast.type_node.unwrap();
        }
        try self.charge();
        var walk = frame.freshWalk(self, .{
            .first = tree.firstToken(expression),
            .last = tree.lastToken(expression),
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
                return try resolution.stdCollectionEmptyOf(expression, declared_type);
            }
            const resolver = frame.cache.zls orelse return false;
            return try resolver.stdCollectionEmptyOf(expression, declared_type);
        }
        if (domain == .backing_storage) return !self.readonly_address;
        return false;
    }

    fn callValue(
        self: *Query,
        frame: *Frame,
        node: Ast.Node.Index,
        domain: Domain,
        path: Path,
    ) BudgetError!bool {
        const tree = frame.cache.tree;
        const range: FileCache.TokenRange = .{
            .first = tree.firstToken(node),
            .last = tree.lastToken(node),
        };
        try self.charge();
        // This existing producer owns the SDK constructor identities.
        const list_constructor = try fresh.standardListConstructor(
            frame.cache,
            range,
            frame.freshWalk(self, range),
        );
        if (path.len == 0 and list_constructor) {
            if (domain == .backing_storage) return true;
            // The buffer constructor does not prove that allocator/context
            // fields embedded in a managed header are themselves private.
            try self.charge();
            return try fresh.freshStorageAt(frame.cache, frame.freshWalk(self, .{
                .first = tree.firstToken(node),
                .last = tree.lastToken(node),
            }));
        }
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse return false;
        try self.charge();
        const canonical = (try frame.cache.actualCallSummaryAt(
            fresh.calleeQueryToken(tree, call),
            frame.resolution,
        )) orelse return false;
        if (list_constructor)
            return fresh.listConstructorProjection(
                frame.cache,
                canonical,
                path.fields[0..path.len],
                self.remaining,
            ) catch |err| {
                if (err == error.AnalysisBudgetExceeded) return self.failure();
                return err;
            };
        if (path.len == 0 or domain == .reachable_storage) {
            const resolver = if (frame.resolution) |resolution|
                resolution.resolver
            else
                frame.cache.zls orelse return false;
            try self.charge();
            const allocator = try resolver.declaredInToolchainFile(
                canonical.callee.handle,
                "/std/mem/Allocator.zig",
            );
            if (allocator) {
                // Only the existing producer chooses which actual allocator
                // declarations grant ownership; document identity alone does not.
                if (!try fresh.freshStorageAt(frame.cache, frame.freshWalk(self, range))) return false;
                if (domain == .backing_storage) return true;
                const resolution = frame.resolution orelse resolver.resolutionFrame();
                return self.pointeeAddressFree(resolution, node);
            }
        }
        for (self.calls[0..self.call_len]) |active| {
            try self.charge();
            if (active.tree == canonical.callee.tree and
                active.declaration == canonical.callee.declaration) return false;
        }
        if (self.call_len == max_origins) return false;
        self.calls[self.call_len] = .{
            .tree = canonical.callee.tree,
            .declaration = canonical.callee.declaration,
        };
        self.call_len += 1;
        defer self.call_len -= 1;
        const declaring = (try canonical.declaringCache(frame.cache)) orelse return false;
        // The exact declaration owns its scoped syntax index. Even a callee in
        // the caller's document must not inherit the caller's parent map.
        var callee_frame = (try Frame.init(
            self,
            declaring,
            canonical.callee.declaration,
            canonical.callee.declaration,
        )) orelse return false;
        const resolver = if (canonical.callee.caller_frame) |caller|
            caller.resolver
        else
            frame.cache.zls orelse return false;
        callee_frame.resolution = resolver.frameForFunction(canonical.callee.reference);
        const body = callee_frame.body;
        var saw_return = false;
        for (callee_frame.index.returns.items) |ret| {
            try self.charge();
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

    /// Freshness proves the outer allocation. Its actual pointee type must
    /// separately prove that the reachable graph carries no other addresses.
    fn pointeeAddressFree(
        self: *Query,
        resolution: engine.TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
    ) BudgetError!bool {
        try self.charge();
        var ty = (try resolution.typeOfNode(node)) orelse return false;
        const resolver = resolution.resolver;
        if (resolver.typeTag(ty) == .error_union) {
            ty = (try resolver.normalizedType(resolver.childType(ty) orelse return false)) orelse return false;
        }
        if (resolver.typeTag(ty) != .pointer) return false;
        const child = resolver.childType(ty) orelse return false;
        return fresh.actualTypeAddressFree(resolution, child, 0, self.remaining);
    }

    fn formalObjectAddressFree(
        self: *Query,
        frame: *Frame,
        binding: BindingFacts,
    ) BudgetError!bool {
        const resolution = frame.resolution orelse
            (frame.cache.zls orelse return false).resolutionFrame();
        const node = frame.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
        try self.charge();
        const ty = (try resolution.typeOfNode(node)) orelse return false;
        if (resolution.resolver.pointerSize(ty) != .one) return false;
        return self.pointeeAddressFree(resolution, node);
    }

    fn unpublished(
        self: *Query,
        frame: *Frame,
        selected: Root,
        boundary: Ast.TokenIndex,
        domain: Domain,
        allowed_store: ?Ast.Node.Index,
    ) BudgetError!bool {
        const tree = frame.cache.tree;
        // findAt compares the exact tokenSlice bytes used by these buckets.
        // Shadow/capture qualification and every horizon/path/callback check
        // stay live below; this only omits already-rejected source candidates.
        try self.charge();
        const uses = frame.index.identifier_uses.get(tree.tokenSlice(selected.binding.name_token)) orelse return true;
        for (uses.items) |node| {
            try self.charge();
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
                    .slice, .slice_open, .slice_sentinel => {
                        if (!self.lifetime_only or tree.fullSlice(parent).?.ast.sliced != use) break;
                        use = parent;
                    },
                    .array_access => {
                        if (!self.lifetime_only or tree.nodeData(parent).node_and_node[0] != use) break;
                        use = parent;
                    },
                    .address_of, .deref, .grouped_expression => use = parent,
                    else => break,
                }
            }
            if (!Path.overlaps(selected.path, use_path)) continue;
            if (self.lifetime_only and try self.lifetimeAliasInitialization(frame, use)) continue;
            if (self.lifetime_only and selected.path.len == 0 and
                try self.inlineFieldDefinition(frame, use)) continue;
            if (self.lifetime_only and cellDefinition(frame, use) and
                try self.expressionAddressFree(frame, use)) continue;
            // Initializing an address-free cell cannot publish an address or
            // introduce a borrowed allocation into the private object graph.
            if (!self.lifetime_only and cellDefinition(frame, use) and
                try self.expressionAddressFree(frame, use)) continue;
            if (self.lifetime_only and try self.expressionAddressFree(frame, use)) continue;
            var parent = frame.parentOf(use) orelse return false;
            if (tree.nodeTag(parent) == .field_access) parent = frame.parentOf(parent) orelse return false;
            if (allowed_store != null and parent == allowed_store.?) continue;
            if (self.lifetime_only and
                (tree.nodeTag(parent) == .builtin_call_two or
                    tree.nodeTag(parent) == .builtin_call_two_comma or
                    tree.nodeTag(parent) == .builtin_call or
                    tree.nodeTag(parent) == .builtin_call_comma) and
                try self.lifetimeBuiltinWriteSafe(frame, use, parent)) continue;
            var call_buffer: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buffer, parent) orelse return false;
            try self.charge();
            const canonical = (try frame.cache.actualCallSummaryAt(
                fresh.calleeQueryToken(tree, call),
                frame.resolution,
            )) orelse return false;
            if (self.lifetime_only and canonical.read_only == true) continue;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const receiver = (try canonical.callArgumentFor(frame.cache, &argument_buffer, 0)) orelse {
                if (self.lifetime_only and try self.lifetimeCallSafe(frame, canonical, selected)) continue;
                return false;
            };
            const receiver_root = (try frame.root(self, .{ .node = receiver })) orelse {
                if (self.lifetime_only and try self.lifetimeCallSafe(frame, canonical, selected)) continue;
                return false;
            };
            if (receiver != use or receiver_root.binding.name_token != binding.name_token or
                receiver_root.path.len > selected.path.len or !Path.overlaps(receiver_root.path, selected.path))
            {
                if (self.lifetime_only and try self.lifetimeCallSafe(frame, canonical, selected)) continue;
                return false;
            }
            const resolver = if (frame.resolution) |resolution|
                resolution.resolver
            else
                frame.cache.zls orelse return false;
            try self.charge();
            const append = if (frame.resolution) |resolution|
                try resolution.stdCollectionAppendOf(call.ast.fn_expr, call.ast.params.len)
            else
                try resolver.stdCollectionAppendOf(call.ast.fn_expr, call.ast.params.len);
            if (append != .no) {
                if (self.lifetime_only and try self.lifetimeCopyPredates(selected, tree.firstToken(parent)))
                    return false;
                if (domain == .reachable_storage and call.ast.params.len == 0) return false;
                if (domain == .reachable_storage and !try self.storedValue(
                    frame,
                    call.ast.params[call.ast.params.len - 1],
                    parent,
                    boundary,
                )) return false;
                continue;
            }
            try self.charge();
            const hash_map = try resolver.declaredInToolchainFile(
                canonical.callee.handle,
                "/std/hash_map.zig",
            );
            const array_hash_map = try resolver.declaredInToolchainFile(
                canonical.callee.handle,
                "/std/array_hash_map.zig",
            );
            if (!hash_map and !array_hash_map) {
                if (self.lifetime_only and try self.lifetimeCallSafe(frame, canonical, selected)) continue;
                return false;
            }
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration) orelse return false;
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
                frame.cache,
                &argument_buffer,
                value_formal orelse return false,
            )) orelse return false;
            const key = (try canonical.callArgumentFor(
                frame.cache,
                &argument_buffer,
                key_formal orelse return false,
            )) orelse return false;
            if (domain == .reachable_storage and
                !try self.addressFreeValue(frame, key, 0)) return false;
            if (domain == .reachable_storage and
                !try self.storedValue(frame, payload, parent, boundary)) return false;
        }
        return true;
    }

    fn addressFreeValue(
        self: *Query,
        frame: *Frame,
        node: Ast.Node.Index,
        depth: u8,
    ) BudgetError!bool {
        try self.charge();
        if (depth == max_origins) return false;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .number_literal, .char_literal => return true,
            .grouped_expression => return self.addressFreeValue(frame, tree.nodeData(node).node_and_token[0], depth + 1),
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
        for (frame.index.nodes.items) |candidate| {
            try self.charge();
            const decl = tree.fullVarDecl(candidate) orelse continue;
            if (decl.ast.mut_token + 1 != root.binding.name_token) continue;
            if (decl.ast.type_node.unwrap()) |declared_type| {
                return self.typeAddressFree(
                    frame,
                    tree.firstToken(declared_type),
                    tree.lastToken(declared_type),
                );
            }
            return self.addressFreeValue(
                frame,
                decl.ast.init_node.unwrap() orelse return false,
                depth + 1,
            );
        }
        return false;
    }

    fn typeAddressFree(
        self: *Query,
        frame: *Frame,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) BudgetError!bool {
        try self.charge();
        const tree = frame.cache.tree;
        if (first == last and tree.tokenTag(first) == .identifier and
            type_query.isReservedScalarTypeName(tree.tokenSlice(first))) return true;
        const resolution = frame.resolution orelse
            (frame.cache.zls orelse return false).resolutionFrame();
        const node = frame.cache.nodeForExactSpan(first, last) orelse return false;
        try self.charge();
        const ty = (try resolution.typeOfNode(node)) orelse return false;
        return fresh.actualTypeAddressFree(resolution, ty, 0, self.remaining);
    }

    fn storedValue(
        self: *Query,
        frame: *Frame,
        value_node: Ast.Node.Index,
        store: Ast.Node.Index,
        boundary: Ast.TokenIndex,
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
                .grouped_expression, .unwrap_optional => stored = frame.cache.tree.nodeData(stored).node_and_token[0],
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

// These parse real expressions and exercise the public query, not token echoes.
fn expectProbe(source: [:0]const u8, domain: Domain, expected: bool) !void {
    return expectProbePaths(source, domain, expected, "", "");
}

fn expectProbePaths(
    source: [:0]const u8,
    domain: Domain,
    expected: bool,
    left_path: []const u8,
    right_path: []const u8,
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
            &cache,
            node,
            .{ .node = call.ast.params[0], .path = left_path },
            .{ .node = call.ast.params[1], .path = right_path },
            domain,
            .{},
        ));
        found = true;
    }
    try std.testing.expect(found);
}

const ProbeSite = struct {
    call: Ast.Node.Index,
    declaration: Ast.Node.Index,
    left: Ast.Node.Index,
    right: Ast.Node.Index,
};

fn probeSite(tree: *const Ast) ?ProbeSite {
    var declaration: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .fn_decl) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, node) orelse continue;
        const name = proto.name_token orelse continue;
        if (std.mem.eql(u8, tree.tokenSlice(name), "use")) {
            declaration = node;
            break;
        }
    }
    const fn_decl = declaration orelse return null;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "probe") or
            call.ast.params.len != 2) continue;
        return .{
            .call = node,
            .declaration = fn_decl,
            .left = call.ast.params[0],
            .right = call.ast.params[1],
        };
    }
    return null;
}

const ProbeBudget = struct {
    answer: bool,
    spent: u32,
};

fn probeWithBudget(source: [:0]const u8, budget: u32) !ProbeBudget {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const site = probeSite(&tree) orelse return error.TestUnexpectedResult;
    var remaining = budget;
    const answer = try mayShareStorageAt(
        &cache,
        site.call,
        .{ .node = site.left },
        .{ .node = site.right },
        .backing_storage,
        .{ .remaining = &remaining, .declaration = site.declaration },
    );
    return .{ .answer = answer, .spent = budget - remaining };
}

fn expectSharedProbe(source: [:0]const u8, expected: bool) !void {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const site = probeSite(&tree) orelse return error.TestUnexpectedResult;
    var remaining: u32 = work_limit;
    for (0..2) |_| {
        try std.testing.expectEqual(expected, try mayShareStorageAt(
            &cache,
            site.call,
            .{ .node = site.left },
            .{ .node = site.right },
            .reachable_storage,
            .{ .remaining = &remaining, .declaration = site.declaration },
        ));
    }
}

test "shared syntax candidates preserve qualified quoted shadows" {
    try expectSharedProbe(
        \\fn use(incoming: []u8) void {
        \\    var @"owned bytes" = [_]u8{1};
        \\    {
        \\        var @"owned bytes" = [_]u8{2};
        \\        externalPublish(&@"owned bytes");
        \\    }
        \\    probe(incoming, @"owned bytes");
        \\}
    , false);
}

test "shared syntax candidates retain opaque publication and nested capture" {
    try expectSharedProbe(
        \\fn use(incoming: []u8) void {
        \\    var owned = [_]u8{1};
        \\    externalPublish(&owned);
        \\    probe(incoming, owned);
        \\}
    , true);
    try expectSharedProbe(
        \\fn use(incoming: []u8) void {
        \\    var owned = [_]u8{1};
        \\    const Nested = struct { fn publish() void { externalPublish(&owned); } };
        \\    Nested.publish();
        \\    probe(incoming, owned);
        \\}
    , true);
}

test "shared syntax keeps incoming rebind at its live query horizon" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\fn before() void {}
        \\fn use(gpa: std.mem.Allocator, incoming: []u8) !void {
        \\    var owned = try gpa.alloc(u8, 2);
        \\    before();
        \\    owned = incoming;
        \\    probe(incoming, owned);
        \\}
    ;
    const gpa = std.testing.allocator;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var fixture_path: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const length = try std.Io.Dir.cwd().realPathFile(std.testing.io, ".", &fixture_path);
    const separator = if (std.mem.endsWith(u8, fixture_path[0..length], std.fs.path.sep_str)) "" else std.fs.path.sep_str;
    const suffix = try std.fmt.bufPrint(fixture_path[length..], "{s}zbc-storage-alias-query-test.zig", .{separator});
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, fixture_path[0 .. length + suffix.len], source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.module_id = resolver.handle.module;
    const site = probeSite(tree) orelse return error.TestUnexpectedResult;
    var before: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |_, raw| {
        const node: Ast.Node.Index = @enumFromInt(raw);
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse continue;
        if (std.mem.eql(u8, tree.tokenSlice(tree.lastToken(call.ast.fn_expr)), "before")) before = node;
    }
    var remaining: u32 = work_limit;
    const query_context: QueryContext = .{ .remaining = &remaining, .declaration = site.declaration };
    const left: StorageSelection = .{ .node = site.left };
    const right: StorageSelection = .{ .node = site.right };
    try std.testing.expect(!try mayShareStorageAt(&cache, before orelse return error.TestUnexpectedResult, left, right, .reachable_storage, query_context));
    for (0..2) |_| {
        try std.testing.expect(try mayShareStorageAt(&cache, site.call, left, right, .reachable_storage, query_context));
    }
}

test "shared producer syntax does not borrow the caller release horizon" {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) ![]u8 {
        \\    const bytes = try gpa.alloc(u8, 2);
        \\    return bytes;
        \\}
        \\fn use(gpa: std.mem.Allocator, incoming: []u8) !void {
        \\    const bytes = try make(gpa);
        \\    gpa.free(bytes);
        \\    probe(incoming, bytes);
        \\}
    ;
    const gpa = std.testing.allocator;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var fixture_path: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const length = try std.Io.Dir.cwd().realPathFile(std.testing.io, ".", &fixture_path);
    const separator = if (std.mem.endsWith(u8, fixture_path[0..length], std.fs.path.sep_str)) "" else std.fs.path.sep_str;
    const suffix = try std.fmt.bufPrint(fixture_path[length..], "{s}zbc-storage-alias-query-test.zig", .{separator});
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, fixture_path[0 .. length + suffix.len], source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    cache.module_id = resolver.handle.module;
    const site = probeSite(tree) orelse return error.TestUnexpectedResult;
    var returning: ?Ast.Node.Index = null;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag == .@"return") returning = @enumFromInt(raw);
    }
    const returned = returning orelse return error.TestUnexpectedResult;
    const value = tree.nodeData(returned).opt_node.unwrap() orelse return error.TestUnexpectedResult;
    var remaining: u32 = work_limit;
    const handoff_context: QueryContext = .{ .remaining = &remaining };
    try std.testing.expect(try allocationSurvivesHandoff(&cache, value, tree.firstToken(returned), handoff_context));
    try std.testing.expect(try mayShareStorageAt(
        &cache,
        site.call,
        .{ .node = site.left },
        .{ .node = site.right },
        .reachable_storage,
        .{ .remaining = &remaining, .declaration = site.declaration },
    ));
    try std.testing.expect(try allocationSurvivesHandoff(&cache, value, tree.firstToken(returned), handoff_context));
}

fn expectPaddedHandoff(published: bool) !void {
    const gpa = std.testing.allocator;
    var out: std.Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    try out.writer.writeAll("fn use() []u8 {\n    var owned = [_]u8{1};\n");
    for (0..512) |index| try out.writer.print("    const padding{d} = 0;\n", .{index});
    if (published) try out.writer.writeAll("    const copied = owned;\n    release(copied);\n");
    try out.writer.writeAll("    return owned;\n}\n");
    const source = try gpa.dupeZ(u8, out.written());
    defer gpa.free(source);
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    budget_mod.clear();
    defer budget_mod.clear();
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .@"return") continue;
        const ret: Ast.Node.Index = @enumFromInt(raw);
        const value = tree.nodeData(ret).opt_node.unwrap() orelse return error.TestUnexpectedResult;
        var remaining: u32 = work_limit;
        try std.testing.expectEqual(!published, try allocationSurvivesHandoff(
            &cache,
            value,
            tree.firstToken(ret),
            .{ .remaining = &remaining },
        ));
        try std.testing.expect(remaining != 0);
        return;
    }
    return error.TestUnexpectedResult;
}

test "handoff exact binding lookup skips unrelated declarations within its unchanged allowance" {
    try expectPaddedHandoff(false);
}

test "handoff exact binding lookup retains a released header copy" {
    try expectPaddedHandoff(true);
}

test "unrelated declarations do not consume function alias work" {
    const source: [:0]const u8 =
        \\fn use() void {
        \\    var first = [_]u8{1};
        \\    var second = [_]u8{2};
        \\    probe(first, second);
        \\}
    ;
    const gpa = std.testing.allocator;
    var text: std.ArrayList(u8) = .empty;
    defer text.deinit(gpa);
    var scratch: [48]u8 = undefined;
    var index: u32 = 0;
    while (index < 512) : (index += 1) {
        const line = try std.fmt.bufPrint(&scratch, "const padding{d} = 0;\n", .{index});
        try text.appendSlice(gpa, line);
    }
    try text.appendSlice(gpa, source);
    try text.append(gpa, 0);
    const expanded: [:0]const u8 = text.items[0 .. text.items.len - 1 :0];

    const budget: u32 = 1024;
    const small = try probeWithBudget(source, budget);
    const large = try probeWithBudget(expanded, budget);
    try std.testing.expect(!small.answer);
    try std.testing.expect(!large.answer);
    try std.testing.expectEqual(small.spent, large.spent);
}

test "bucketed binding lookup names exactly what findAt names and charges only candidates" {
    const source: [:0]const u8 =
        \\fn use(x: u8, y: u8) void {
        \\    const a = x;
        \\    {
        \\        const x = a;
        \\        _ = x;
        \\    }
        \\    for ([_]u8{ y, a }) |y| {
        \\        _ = y;
        \\    }
        \\    _ = x;
        \\    _ = undeclared;
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const declaration: Ast.Node.Index = for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag == .fn_decl) break @enumFromInt(raw);
    } else return error.TestUnexpectedResult;
    var remaining: u32 = work_limit;
    var query: Query = .{ .root_cache = &cache, .at_node = declaration, .remaining = &remaining };
    const frame = (try Frame.init(&query, &cache, declaration, declaration)) orelse
        return error.TestUnexpectedResult;
    const table = try cache.localBindings(frame.proto, frame.body);
    var checked: u32 = 0;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .identifier) continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const token = tree.nodeMainToken(node);
        const name = tree.tokenSlice(token);
        const expected = table.findAt(name, token);
        var candidates: u32 = 0;
        for (table.items) |binding| candidates += @intFromBool(std.mem.eql(u8, binding.name, name));
        const before = remaining;
        const actual = try frame.bindingAt(&query, node);
        try std.testing.expectEqual(expected != null, actual != null);
        if (expected) |binding| try std.testing.expectEqual(binding.name_token, actual.?.name_token);
        try std.testing.expect(before - remaining <= 1 + candidates);
        checked += 1;
    }
    try std.testing.expect(checked >= 10);
}

test "initializer lookup names the declaring node for shadowed, nested and non-declaration bindings" {
    const source: [:0]const u8 =
        \\fn use(p: []u8, pair: Pair, cond: bool) void {
        \\    const outer = [_]u8{1};
        \\    {
        \\        const outer = [_]u8{2};
        \\        _ = outer;
        \\    }
        \\    const nested = if (cond) blk: {
        \\        const inner = [_]u8{3};
        \\        break :blk inner;
        \\    } else outer;
        \\    const a, const b = pair;
        \\    for (p) |c| {
        \\        _ = c;
        \\    }
        \\    _ = .{ outer, nested, a, b };
        \\}
    ;
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const declaration: Ast.Node.Index = for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag == .fn_decl) break @enumFromInt(raw);
    } else return error.TestUnexpectedResult;
    var remaining: u32 = work_limit;
    var query: Query = .{ .root_cache = &cache, .at_node = declaration, .remaining = &remaining };
    var frame = (try Frame.init(&query, &cache, declaration, declaration)) orelse
        return error.TestUnexpectedResult;
    const table = try cache.localBindings(frame.proto, frame.body);
    var declared: u32 = 0;
    var undeclared: u32 = 0;
    for (table.items) |*binding| {
        // The independent oracle: the variable declaration this exact name
        // token introduced, and only when it carries an initializer.
        var expected: ?Ast.Node.Index = null;
        for (0..tree.nodes.len) |raw| {
            const var_decl = tree.fullVarDecl(@enumFromInt(raw)) orelse continue;
            if (var_decl.ast.mut_token + 1 != binding.name_token) continue;
            expected = var_decl.ast.init_node.unwrap();
            break;
        }
        const actual = try query.initializer(&frame, .{ .binding = BindingFacts.from(binding), .path = .{} });
        try std.testing.expectEqual(expected, actual);
        if (actual) |node| {
            try std.testing.expectEqual(binding.rhs_first, tree.firstToken(node));
            declared += 1;
        } else undeclared += 1;
    }
    // outer x2, nested, inner; then params p, pair, cond, destructured b
    // and the loop capture c have no initializer of their own.
    try std.testing.expectEqual(@as(u32, 4), declared);
    try std.testing.expect(undeclared >= 5);
}

test "the syntax index is built once per declaration and shared by every query" {
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
    const site = probeSite(&tree) orelse return error.TestUnexpectedResult;
    var cell: ?*const SyntaxIndex = null;
    // Different domains are different questions: each proves afresh, all
    // against the one index this cache owns.
    for ([_]Domain{ .backing_storage, .reachable_storage, .backing_storage }) |domain| {
        var remaining: u32 = work_limit;
        try std.testing.expect(!try mayShareStorageAt(
            &cache,
            site.call,
            .{ .node = site.left },
            .{ .node = site.right },
            domain,
            .{ .remaining = &remaining, .declaration = site.declaration },
        ));
        try std.testing.expectEqual(@as(u32, 1), cache.alias_state.indexes.count());
        const current = cache.alias_state.indexes.get(site.declaration).?;
        if (cell) |known| try std.testing.expect(known == current);
        cell = current;
    }
    try std.testing.expectEqual(@as(u32, 2), cache.alias_state.answers.count());
}

test "a completed answer is reused for one lookup and a cut-off keeps nothing" {
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
    const site = probeSite(&tree) orelse return error.TestUnexpectedResult;
    const left: StorageSelection = .{ .node = site.left };
    const right: StorageSelection = .{ .node = site.right };

    budget_mod.clear();
    defer budget_mod.clear();
    var starved: u32 = 3;
    try std.testing.expectError(error.AnalysisBudgetExceeded, mayShareStorageAt(
        &cache,
        site.call,
        left,
        right,
        .backing_storage,
        .{ .remaining = &starved, .declaration = site.declaration },
    ));
    try std.testing.expectEqual(@as(u32, 0), cache.alias_state.answers.count());
    budget_mod.clear();

    var first: u32 = work_limit;
    try std.testing.expect(!try mayShareStorageAt(&cache, site.call, left, right, .backing_storage, .{
        .remaining = &first,
        .declaration = site.declaration,
    }));
    try std.testing.expect(work_limit - first > 1);
    try std.testing.expectEqual(@as(u32, 1), cache.alias_state.answers.count());

    var repeat: u32 = work_limit;
    try std.testing.expect(!try mayShareStorageAt(&cache, site.call, left, right, .backing_storage, .{
        .remaining = &repeat,
        .declaration = site.declaration,
    }));
    try std.testing.expectEqual(@as(u32, 1), work_limit - repeat);

    // A hit still honours an exhausted allowance.
    var empty: u32 = 0;
    try std.testing.expectError(error.AnalysisBudgetExceeded, mayShareStorageAt(
        &cache,
        site.call,
        left,
        right,
        .backing_storage,
        .{ .remaining = &empty, .declaration = site.declaration },
    ));
    budget_mod.clear();

    // The selection path is part of the question.
    var other: u32 = work_limit;
    _ = try mayShareStorageAt(&cache, site.call, .{ .node = site.left, .path = "x" }, right, .backing_storage, .{
        .remaining = &other,
        .declaration = site.declaration,
    });
    try std.testing.expectEqual(@as(u32, 2), cache.alias_state.answers.count());
}

/// `a` is used after the probe more often than one allowance pays for, so the
/// privacy proof of `a` runs its whole allowance out.
fn exhaustingAliasSource(gpa: std.mem.Allocator) ![:0]u8 {
    var out: std.Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    try out.writer.writeAll("fn use(incoming: []u8) void {\n    var a = [_]u8{1};\n    probe(incoming, a);\n");
    for (0..work_limit + work_limit / 5) |_| try out.writer.writeAll("    _ = a;\n");
    try out.writer.writeAll("}\n");
    return gpa.dupeZ(u8, out.written());
}

fn dropIndexes(cache: *FileCache) void {
    var cells = cache.alias_state.indexes.valueIterator();
    while (cells.next()) |cell| {
        cell.*.deinit(cache.gpa);
        cache.gpa.destroy(cell.*);
    }
    cache.alias_state.indexes.clearAndFree(cache.gpa);
}

test "an exhausted standalone question fails again at once with the same diagnostic" {
    const gpa = std.testing.allocator;
    const source = try exhaustingAliasSource(gpa);
    defer gpa.free(source);
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var cache = FileCache.init(gpa, &tree);
    defer cache.deinit();
    const site = probeSite(&tree) orelse return error.TestUnexpectedResult;
    const left: StorageSelection = .{ .node = site.left };
    const right: StorageSelection = .{ .node = site.right };
    const context: QueryContext = .{ .declaration = site.declaration };
    budget_mod.clear();
    defer budget_mod.clear();

    try std.testing.expectError(error.AnalysisBudgetExceeded, mayShareStorageAt(&cache, site.call, left, right, .backing_storage, context));
    const first = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.storage_alias_work, first.limit);
    try std.testing.expectEqual(@as(u32, 1), cache.alias_state.exhausted.count());
    try std.testing.expectEqual(@as(u32, 0), cache.alias_state.answers.count());
    try std.testing.expectEqual(@as(u32, 1), cache.alias_state.indexes.count());

    // A repeat does no walk: the syntax index a walk needs is not rebuilt.
    dropIndexes(&cache);
    try std.testing.expectError(error.AnalysisBudgetExceeded, mayShareStorageAt(&cache, site.call, left, right, .backing_storage, context));
    try std.testing.expectEqual(@as(u32, 0), cache.alias_state.indexes.count());
    const second = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(first.limit, second.limit);
    try std.testing.expectEqual(first.limit_value, second.limit_value);
    try std.testing.expectEqual(first.reached, second.reached);
    try std.testing.expectEqual(first.byte, second.byte);
    try std.testing.expectEqual(first.line, second.line);
    try std.testing.expectEqual(first.column, second.column);
    try std.testing.expectEqualStrings(first.document, second.document);
    try std.testing.expectEqual(@as(u32, 1), cache.alias_state.exhausted.count());

    // Another selection path, and another domain, are other questions that
    // walk and fail on their own.
    try std.testing.expectError(error.AnalysisBudgetExceeded, mayShareStorageAt(&cache, site.call, .{ .node = site.left, .path = "x" }, right, .backing_storage, context));
    try std.testing.expectEqual(@as(u32, 1), cache.alias_state.indexes.count());
    try std.testing.expectEqual(@as(u32, 2), cache.alias_state.exhausted.count());
    try std.testing.expectError(error.AnalysisBudgetExceeded, mayShareStorageAt(&cache, site.call, left, right, .reachable_storage, context));
    try std.testing.expectEqual(@as(u32, 3), cache.alias_state.exhausted.count());
    _ = budget_mod.take();

    // A borrowed allowance is a consumer's own and is never recorded.
    var cache_other = FileCache.init(gpa, &tree);
    defer cache_other.deinit();
    var starved: u32 = 8;
    try std.testing.expectError(error.AnalysisBudgetExceeded, mayShareStorageAt(&cache_other, site.call, left, right, .backing_storage, .{
        .remaining = &starved,
        .declaration = site.declaration,
    }));
    try std.testing.expectEqual(@as(u32, 0), cache_other.alias_state.exhausted.count());
}

test "a recorded alias failure never replaces a completed answer and a completed walk removes it" {
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
    const site = probeSite(&tree) orelse return error.TestUnexpectedResult;
    const left: StorageSelection = .{ .node = site.left };
    const right: StorageSelection = .{ .node = site.right };
    const context: QueryContext = .{ .declaration = site.declaration };
    const key = AnswerKey.of(&cache, site.call, left, right, .backing_storage, context);
    const stale: Exhausted = .{
        .budget = work_limit,
        .diagnostic = .{
            .limit = .storage_alias_work,
            .limit_value = work_limit,
            .reached = work_limit,
        },
    };
    budget_mod.clear();
    defer budget_mod.clear();

    // A record with a smaller allowance than the question owns does not stop
    // it; the proof completes and the record is dropped.
    cache.alias_state.recordExhausted(&cache, key, .{ .budget = 1, .diagnostic = stale.diagnostic });
    try std.testing.expectEqual(@as(u32, 1), cache.alias_state.exhausted.count());
    try std.testing.expect(!try mayShareStorageAt(&cache, site.call, left, right, .backing_storage, context));
    try std.testing.expectEqual(@as(u32, 0), cache.alias_state.exhausted.count());
    try std.testing.expectEqual(@as(u32, 1), cache.alias_state.answers.count());

    // A record that would stop the question loses to the completed answer.
    cache.alias_state.recordExhausted(&cache, key, stale);
    try std.testing.expect(!try mayShareStorageAt(&cache, site.call, left, right, .backing_storage, context));
    try std.testing.expect(budget_mod.take() == null);
    try std.testing.expectEqual(@as(u32, 1), cache.alias_state.answers.count());
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
    var query: Query = .{
        .root_cache = &cache,
        .at_node = .root,
        .remaining = &remaining,
    };
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
    source: [:0]const u8,
    domain: Domain,
    expected: bool,
    left_path: []const u8,
    right_path: []const u8,
) !void {
    return expectTypedProbePathsBudget(source, domain, expected, left_path, right_path, null);
}

fn expectTypedProbePathsBudget(
    source: [:0]const u8,
    domain: Domain,
    expected: bool,
    left_path: []const u8,
    right_path: []const u8,
    allowance: ?u32,
) !void {
    const gpa = std.testing.allocator;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var fixture_path: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const length = try std.Io.Dir.cwd().realPathFile(std.testing.io, ".", &fixture_path);
    const separator = if (std.mem.endsWith(u8, fixture_path[0..length], std.fs.path.sep_str))
        ""
    else
        std.fs.path.sep_str;
    const suffix = try std.fmt.bufPrint(
        fixture_path[length..],
        "{s}zbc-storage-alias-query-test.zig",
        .{separator},
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
        var remaining = allowance orelse work_limit;
        try std.testing.expectEqual(expected, try mayShareStorageAt(
            &cache,
            node,
            .{ .node = call.ast.params[0], .path = left_path },
            .{ .node = call.ast.params[1], .path = right_path },
            domain,
            if (allowance != null) .{ .remaining = &remaining } else .{},
        ));
        found = true;
    }
    try std.testing.expect(found);
}

fn expectPaddedFactory(borrowed: bool) !void {
    const gpa = std.testing.allocator;
    var out: std.Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    try out.writer.writeAll(if (borrowed)
        "fn make(incoming: []u8) []u8 {\n"
    else
        "fn make(incoming: []u8) [1]u8 {\n");
    for (0..512) |index| try out.writer.print("    const padding{d} = 0;\n", .{index});
    try out.writer.writeAll(if (borrowed) "    return incoming;\n}\n" else "    return [_]u8{1};\n}\n");
    try out.writer.writeAll("fn use(incoming: []u8) void { var owned = make(incoming); probe(incoming, owned); }\n");
    const source = try gpa.dupeZ(u8, out.written());
    defer gpa.free(source);
    budget_mod.clear();
    defer budget_mod.clear();
    try expectTypedProbePathsBudget(source, .backing_storage, borrowed, "", "", 512);
}

test "storage factory return candidates skip unrelated body nodes within a bounded query" {
    try expectPaddedFactory(false);
}

test "storage factory return candidates keep incoming storage borrowed" {
    try expectPaddedFactory(true);
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
    const source: [:0]const u8 =
        \\fn use() void {
        \\    var first = [_]u8{1};
        \\    var second = [_]u8{2};
        \\    probe(first, second);
        \\}
    ;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = 0 });
    var cache = FileCache.init(failing.allocator(), &tree);
    defer cache.deinit();
    const site = probeSite(&tree) orelse return error.TestUnexpectedResult;
    try std.testing.expectError(error.OutOfMemory, mayShareStorageAt(
        &cache,
        site.call,
        .{ .node = site.left },
        .{ .node = site.right },
        .backing_storage,
        .{ .declaration = site.declaration },
    ));
}

test "storage query allocation failures permit a sound retry" {
    const gpa = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn use() void {
        \\    var first = [_]u8{1};
        \\    var second = [_]u8{2};
        \\    probe(first, second);
        \\}
    ;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    const site = probeSite(&tree) orelse return error.TestUnexpectedResult;
    var fail_index: usize = 0;
    while (true) : (fail_index += 1) {
        var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = fail_index });
        var cache = FileCache.init(failing.allocator(), &tree);
        defer cache.deinit();
        const context: QueryContext = .{
            .declaration = site.declaration,
        };
        const shares = mayShareStorageAt(
            &cache,
            site.call,
            .{ .node = site.left },
            .{ .node = site.right },
            .backing_storage,
            context,
        ) catch |err| {
            try std.testing.expectEqual(error.OutOfMemory, err);
            try std.testing.expect(failing.has_induced_failure);
            failing.fail_index = std.math.maxInt(usize);
            try std.testing.expect(!try mayShareStorageAt(
                &cache,
                site.call,
                .{ .node = site.left },
                .{ .node = site.right },
                .backing_storage,
                context,
            ));
            continue;
        };
        try std.testing.expect(!shares);
        break;
    }
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

test "fresh allocations with address-free pointees are deeply disjoint" {
    const prelude =
        \\const std = @import("std");
        \\const Cell = struct { value: u32 };
        \\fn probe(_: *Cell, _: *Cell) void {}
        \\
    ;
    try expectTypedProbe(prelude ++
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    const first = try gpa.create(Cell);
        \\    defer gpa.destroy(first);
        \\    const second = try gpa.create(Cell);
        \\    defer gpa.destroy(second);
        \\    first.* = .{ .value = 1 };
        \\    second.* = .{ .value = 2 };
        \\    probe(first, second);
        \\}
    , .reachable_storage, false);
    try expectTypedProbe(prelude ++
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    const first = try gpa.create(Cell);
        \\    defer gpa.destroy(first);
        \\    first.* = .{ .value = 1 };
        \\    const second = first;
        \\    probe(first, second);
        \\}
    , .reachable_storage, true);
}

test "fresh allocations do not prove pointer-bearing pointees deeply disjoint" {
    try expectTypedProbe(
        \\const std = @import("std");
        \\const Cell = struct { value: *u32 };
        \\fn probe(_: *Cell, _: *Cell) void {}
        \\fn run(gpa: std.mem.Allocator) !void {
        \\    var shared: u32 = 1;
        \\    const first = try gpa.create(Cell);
        \\    defer gpa.destroy(first);
        \\    const second = try gpa.create(Cell);
        \\    defer gpa.destroy(second);
        \\    first.* = .{ .value = &shared };
        \\    second.* = .{ .value = &shared };
        \\    probe(first, second);
        \\}
    , .reachable_storage, true);
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
            &cache,
            node,
            left,
            right,
            .backing_storage,
            context,
        ));
        const after_first = remaining;
        try std.testing.expect(after_first < work_limit);
        try std.testing.expect(!try mayShareStorageAt(
            &cache,
            node,
            left,
            right,
            .backing_storage,
            context,
        ));
        try std.testing.expect(remaining < after_first);
        remaining = 0;
        budget_mod.clear();
        defer budget_mod.clear();
        try std.testing.expectError(error.AnalysisBudgetExceeded, mayShareStorageAt(
            &cache,
            node,
            left,
            right,
            .backing_storage,
            context,
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
            &cache,
            value,
            tree.firstToken(node),
            .{},
        ));
        found = true;
    }
    try std.testing.expect(found);
}

fn expectTypedHandoff(source: [:0]const u8, expected: bool) !void {
    const gpa = std.testing.allocator;
    var context: engine.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var fixture_path: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const length = try std.Io.Dir.cwd().realPathFile(std.testing.io, ".", &fixture_path);
    const separator = if (std.mem.endsWith(u8, fixture_path[0..length], std.fs.path.sep_str)) "" else std.fs.path.sep_str;
    const suffix = try std.fmt.bufPrint(fixture_path[length..], "{s}zbc-storage-handoff-test.zig", .{separator});
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
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .@"return") continue;
        const node: Ast.Node.Index = @enumFromInt(raw);
        const value = tree.nodeData(node).opt_node.unwrap() orelse continue;
        try std.testing.expectEqual(expected, try allocationSurvivesHandoff(&cache, value, tree.firstToken(node), .{}));
        found = true;
    }
    try std.testing.expect(found);
}

test "computed handoff outcomes retain every returning allocation lifetime" {
    try expectHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) []u8 {
        \\    return gpa.alloc(u8, 2) catch unreachable;
        \\}
    , true);
    try expectHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) []u8 {
        \\    return gpa.alloc(u8, 1) catch (gpa.alloc(u8, 2) catch unreachable);
        \\}
    , true);
    try expectHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) []u8 {
        \\    const maybe: ?[]u8 = gpa.alloc(u8, 1) catch unreachable;
        \\    return maybe orelse (gpa.alloc(u8, 2) catch unreachable);
        \\}
    , true);
    try expectHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) []u8 {
        \\    const fallback = gpa.alloc(u8, 2) catch unreachable;
        \\    defer gpa.free(fallback);
        \\    return gpa.alloc(u8, 1) catch fallback;
        \\}
    , false);
    try expectHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator, maybe: ?[]u8) []u8 {
        \\    const fallback = gpa.alloc(u8, 2) catch unreachable;
        \\    defer gpa.free(fallback);
        \\    return maybe orelse fallback;
        \\}
    , false);
    try expectHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator) []u8 {
        \\    return gpa.alloc(u8, 2) catch blk: { break :blk unreachable; };
        \\}
    , false);
}

test "typed nested byte copy destinations preserve the owned handoff" {
    const prelude =
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator, bytes: []const u8, offset: usize) []u8 {
        \\    const own = gpa.alloc(u8, offset + bytes.len) catch unreachable;
        \\
    ;
    try expectTypedHandoff(prelude ++
        \\    @memcpy(own[offset..][0..bytes.len], bytes);
        \\    return own;
        \\}
    , true);
    try expectTypedHandoff(prelude ++
        \\    @memset(own[offset..][0..bytes.len], 0);
        \\    return own;
        \\}
    , true);
    try expectTypedHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator, bytes: []const []const u8) [][]const u8 {
        \\    const own = gpa.alloc([]const u8, bytes.len) catch unreachable;
        \\    @memcpy(own[0..][0..bytes.len], bytes);
        \\    return own;
        \\}
    , false);
    try expectTypedHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator, bytes: []u8) []u8 {
        \\    var own = gpa.alloc(u8, bytes.len) catch unreachable;
        \\    own = bytes;
        \\    return own;
        \\}
    , false);
    try expectTypedHandoff(
        \\const std = @import("std");
        \\fn make(gpa: std.mem.Allocator, mutate: *const fn ([]u8) void) []u8 {
        \\    const own = gpa.alloc(u8, 2) catch unreachable;
        \\    mutate(own[0..][0..1]);
        \\    return own;
        \\}
    , false);
    try expectTypedHandoff(
        \\const std = @import("std");
        \\var escaped: ?*[]u8 = null;
        \\fn make(gpa: std.mem.Allocator) []u8 {
        \\    var own = gpa.alloc(u8, 2) catch unreachable;
        \\    escaped = &own;
        \\    return own;
        \\}
    , false);
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
        &cache,
        value,
        boundary,
        .{ .remaining = &remaining },
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
