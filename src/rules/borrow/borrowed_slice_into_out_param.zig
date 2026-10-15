//! Borrowed-slice-into-out-param detector — `defer <X>.deinit()`
//! (or `defer alloc.free(<X>)`) registers cleanup for a local
//! buffer / arena, and a later write `<out>.* = ...<X>...` (or
//! `<out>.field = ...<X>...`) pushes a view of `<X>` into a
//! caller-visible out-parameter.  When the defer fires on
//! function return, the out-param holds a dangling slice.
//! Canonical returned-storage proofs distinguish independently owned snapshots
//! from fresh outer allocations that still retain deferred storage.
//!
//! Real-world: oven-sh/bun#30151 (`query_string.* =
//! ZigString.init(result.query_string)` where
//! `result.query_string` was sliced from `specifier_utf8`, which
//! `defer specifier_utf8.deinit()` would free on return),
//! #30223 (same fn, sibling out-param), #25563 (`install.ca = .{
//! .str = str }` borrowing parser-arena memory freed by
//! `defer parser.deinit()`).

const std = @import("std");
const Ast = std.zig.Ast;

const tokens = @import("../../ast/tokens.zig");
const query = @import("../../ast/token_query.zig");
const problem_mod = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const return_storage = @import("../../cache/return_storage.zig");
const call_summary = @import("../../cache/call_summary.zig");
const bindings_mod = @import("../../model/local_bindings.zig");
const resolver_mod = @import("../../type_resolver.zig");
const Iterator = @import("type_engine").AstIterator;
const budget_mod = @import("../../budget.zig");

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const Atom = query.Atom;
const R = "borrowed-slice-into-out-param";

// `defer <X>.<deinit|close>(...)` — $0 = X (the cleanup receiver,
// which is what becomes invalid after the defer fires).
const defer_cleanup = &[_]Atom{
    .{ .tok = .keyword_defer },
    .{ .capture = 0 },
    .{ .tok = .period },
    .{ .pred = isDeinitOrClose },
    .{ .tok = .l_paren },
};

// `defer <_>.free(<X>...)` — the freed thing is the FIRST ARG,
// not the receiver.  $0 = the freed name.
const defer_free = &[_]Atom{
    .{ .tok = .keyword_defer },
    .{ .tok = .identifier },
    .{ .tok = .period },
    .{ .text = "free" },
    .{ .tok = .l_paren },
    .{ .capture = 0 },
};

// `<out>.* = ...` OR `<out>.<field> = ...` — $0 = out.
const write_via_out = &[_]Atom{
    .{ .capture = 0 },
    .{ .any_of = &[_][]const Atom{
        &[_]Atom{ .{ .tok = .period_asterisk }, .{ .tok = .equal } },
        &[_]Atom{ .{ .tok = .period }, .{ .tok = .identifier }, .{ .tok = .equal } },
    } },
};

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .borrowed_slice_into_out_param)) return;
    var proto_buf: [1]Ast.Node.Index = undefined;
    var fns = tokens.iterFnDecls(tree);
    while (fns.next(&proto_buf)) |fn_entry| {
        try checkFn(gpa, tree, cache, fn_entry.proto, fn_entry.body, problems);
    }
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    proto: Ast.full.FnProto,
    body: Ast.Node.Index,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(body);
    const last = tree.lastToken(body);

    // Cheap pre-scan: any `defer` keyword at all?  Without one the
    // rule can never fire, so skip the binding-walk cost.
    if (!tokens.hasTokenInRange(tags, first, last, .keyword_defer)) return;

    const bindings = try cache.localBindings(proto, body);

    var pointer_params: std.ArrayListUnmanaged(PointerParam) = .empty;
    defer pointer_params.deinit(gpa);
    for (bindings.items) |b| {
        if (b.origin != .param) continue;
        if (!isPointerType(tags, b.rhs_first, b.rhs_last)) continue;
        try pointer_params.append(gpa, .{
            .name = b.name,
        });
    }
    if (pointer_params.items.len == 0) return;

    // Deferred names registered for cleanup, with their lexical
    // scope.  A `defer X.deinit()` in `else { ... }` does NOT
    // register when control passes through the sibling `if` branch
    // — pairing it with a write in that branch is a false alarm.
    // Track each defer's enclosing scope so writes outside that
    // scope are excluded.  Skips nested fn bodies so a `defer`
    // inside `const f = struct { fn g() void { defer ... } }`
    // doesn't pollute the outer fn's deferred-name set.
    var deferred: std.ArrayListUnmanaged(DeferredItem) = .empty;
    defer deferred.deinit(gpa);
    var t: Ast.TokenIndex = first;
    while (t <= last) {
        if (tags[t] == .keyword_fn) {
            t = tokens.skipNestedFn(tags, t, last);
            t = if (t < last) t + 1 else last + 1;
            continue;
        }
        if (tags[t] != .keyword_defer) {
            t += 1;
            continue;
        }
        if (query.matchAt(tree, defer_cleanup, t, last, null)) |m| {
            const name = m.captureText(tree, 0).?;
            // Skip module/namespace identifiers (e.g. `defer posix.close(fd)`
            // where `posix` is `std.posix`) — they are not local variables.
            if (bindings.findAt(name, m.captures[0].?)) |binding| {
                const range = enclosingScope(tags, t, first, last);
                try deferred.append(gpa, .{
                    .name = name,
                    .binding_token = binding.name_token,
                    .token = t,
                    .cleanup_token = t + 2,
                    .scope_open = range.open,
                    .scope_close = range.close,
                });
            }
            t = m.end + 1;
            continue;
        }
        if (query.matchAt(tree, defer_free, t, last, null)) |m| {
            const name = m.captureText(tree, 0).?;
            if (bindings.findAt(name, m.captures[0].?)) |binding| {
                const range = enclosingScope(tags, t, first, last);
                try deferred.append(gpa, .{
                    .name = name,
                    .binding_token = binding.name_token,
                    .token = t,
                    .cleanup_token = t + 2,
                    .scope_open = range.open,
                    .scope_close = range.close,
                });
            }
            t = m.end + 1;
            continue;
        }
        t += 1;
    }
    if (deferred.items.len == 0) return;

    // Canonical expression provenance owns every positive loan, including
    // aliases and call-valued payloads. Names select lexical declarations only.
    try scanWrites(gpa, tree, cache, body, write_via_out, first, last, pointer_params.items, deferred.items, problems);
}

fn scanWrites(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    body: Ast.Node.Index,
    atoms: []const Atom,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    pointer_params: []const PointerParam,
    deferred: []const DeferredItem,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    const tags = tree.tokens.items(.tag);
    const writes = try query.findAllInBody(gpa, tree, atoms, first, last);
    defer gpa.free(writes);
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const retained = try arena.allocator().alloc(Ast.TokenIndex, deferred.len);
    for (deferred, retained) |cleanup, *token| token.* = cleanup.binding_token;
    var loans = return_storage.ExpressionLoanQuery.init(.{
        .cache = cache,
        .body = body,
        .scratch = &arena,
    });
    var cleanup_proof: CleanupProof = .{ .arena = &arena };
    for (writes) |w| {
        const out_name = w.captureText(tree, 0).?;
        _ = findPointerParam(out_name, pointer_params) orelse continue;
        const sc = tokens.findStmtSemicolon(tags, w.end + 1, last) orelse continue;
        if (sc <= w.end + 1) continue;
        const rhs = cache.nodeForExactSpan(w.end + 1, sc - 1) orelse continue;
        const answer = try loans.expressionLoansAt(.{
            .selection = .{ .node = rhs },
            .horizon = tree.firstToken(rhs),
            .retained_bindings = retained,
        });
        for (answer.loans) |loan| {
            if (!loan.proved) continue;
            for (deferred) |cleanup| {
                if (cleanup.binding_token != loan.binding_token) continue;
                if (w.start < cleanup.scope_open or w.start > cleanup.scope_close) continue;
                if (clearedBeforeCleanup(tree, cleanup, w.start, w.end, sc, first, last)) continue;
                if (loan.origin == .retained_value and !try cleanup_proof.releases(cache, body, cleanup, loan.payload_path, sc, rhs)) continue;
                try report(gpa, problems, tree, w.start, out_name, cleanup.name);
                break;
            } else continue;
            break;
        }
    }
}

/// Retained header provenance is only an alias coordinate. A definite
/// lifetime report also requires source-proved release of that exact payload.
const CleanupProof = struct {
    arena: *std.heap.ArenaAllocator,
    remaining: u32 = call_summary.actual_query_work_limit,

    const Frame = struct {
        cache: *file_cache_mod.FileCache,
        resolution: resolver_mod.TypeResolver.ResolutionFrame,
        bindings: bindings_mod.LocalBindings,
        selected: Ast.TokenIndex,
        body: Ast.Node.Index,
        root: ?*const Root = null,
        root_path: []const u8 = "",
        exit_cleanup: ?Ast.TokenIndex = null,
        publication_rhs: bool = false,
    };

    const Root = struct {
        frame: Frame,
        use_token: Ast.TokenIndex,
        rhs: Ast.Node.Index,
    };

    fn charge(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, depth: u8) file_cache_mod.SummaryError!void {
        if (depth >= 64 or self.remaining == 0) {
            const pos = try Pos.fromTokenStart(frame.cache.tree, frame.cache.tree.firstToken(node));
            var function_name: budget_mod.NameBuf = .{};
            if (tokens.enclosingFnDecl(frame.cache.tree, frame.cache.tree.firstToken(node))) |declaration| {
                var buffer: [1]Ast.Node.Index = undefined;
                if (tokens.fnProto(frame.cache.tree, &buffer, declaration)) |proto| {
                    if (proto.name_token) |name| function_name.set(frame.cache.tree.tokenSlice(name));
                }
            }
            return budget_mod.fail(.{
                .limit = if (depth >= 64) .normal_cleanup_depth else .normal_cleanup_nodes,
                .limit_value = if (depth >= 64) 64 else call_summary.actual_query_work_limit,
                .reached = if (depth >= 64) depth else call_summary.actual_query_work_limit,
                .byte = pos.byte, .line = pos.line, .column = pos.column,
                .document = budget_mod.documentForTree(frame.cache.tree),
                .function = function_name,
            });
        }
        self.remaining -= 1;
    }

    fn releases(self: *CleanupProof, cache: *file_cache_mod.FileCache, body: Ast.Node.Index, cleanup: DeferredItem, path: []const u8, use_token: Ast.TokenIndex, rhs: Ast.Node.Index) file_cache_mod.SummaryError!bool {
        const resolver = cache.zls orelse return false;
        const declaration = tokens.enclosingFnDecl(cache.tree, cleanup.token) orelse return false;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(cache.tree, &buffer, declaration) orelse return false;
        var resolution = resolver.resolutionFrame();
        const callable = (try resolution.resolveValueOfNode(declaration)) orelse return false;
        if (callable.is_type_val or callable.data != .function) return false;
        const function = callable.data.function;
        if (function.fn_token != proto.ast.fn_token or
            &function.handle.document.tree != cache.tree or function.handle.module != cache.module_id) return false;
        resolution = resolver.frameForFunction(.{
            .tree = cache.tree, .fn_token = proto.ast.fn_token,
            .handle = function.handle, .actual_type = callable,
        });
        var frame: Frame = .{
            .cache = cache, .resolution = resolution,
            .bindings = (try cache.localBindings(proto, body)).*,
            .selected = cleanup.binding_token, .body = body,
            .exit_cleanup = cleanup.token,
        };
        const root: Root = .{ .frame = frame, .use_token = use_token, .rhs = rhs };
        frame.root = &root;
        const actual = (try cache.actualCallSummaryAt(cleanup.cleanup_token, frame.resolution)) orelse return false;
        // The publication expression can transfer and clear the old header
        // before its returned value is stored in the out-parameter.
        var producing = frame;
        producing.publication_rhs = true;
        if (try self.redirectedIn(producing, rhs, path, 0, cache.tree.lastToken(rhs) + 1, 0)) return false;
        if (try self.redirectedIn(frame, body, path, use_token, cleanup.scope_close, 0)) return false;
        return self.callReleases(frame, actual, path, 0);
    }

    fn calleeFrame(self: *CleanupProof, caller: Frame, actual: file_cache_mod.FileCache.ActualCallSummary, parameter: u32, prefix: []const u8, track_release: bool) file_cache_mod.SummaryError!?Frame {
        const cache = (try actual.declaringCache(caller.cache)) orelse return null;
        const resolver = cache.zls orelse return null;
        const body = tokens.bodyOf(cache.tree, actual.callee.declaration) orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(cache.tree, &buffer, actual.callee.declaration) orelse return null;
        var parameters = proto.iterate(cache.tree);
        var index: u32 = 0;
        while (parameters.next()) |formal| : (index += 1) {
            if (index != parameter) continue;
            return .{
                .cache = cache, .resolution = resolver.frameForFunction(actual.callee.reference),
                .bindings = (try cache.localBindings(proto, body)).*,
                .selected = formal.name_token orelse return null, .body = body,
                .root = if (track_release) caller.root else null,
                .root_path = if (track_release and caller.root != null) try self.join(caller.root_path, prefix) else "",
                .publication_rhs = caller.publication_rhs,
            };
        }
        return null;
    }

    fn callReleases(self: *CleanupProof, frame: Frame, actual: file_cache_mod.FileCache.ActualCallSummary, wanted: []const u8, depth: u8) file_cache_mod.SummaryError!bool {
        try self.charge(frame, actual.callee.call_node, depth);
        const tree = actual.callee.tree;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, actual.callee.declaration) orelse return false;
        const sdk_free = std.mem.eql(u8, tree.tokenSlice(proto.name_token orelse return false), "free") and
            try frame.resolution.resolver.declaredInToolchainFile(actual.callee.reference.handle, "/std/mem/Allocator.zig");
        if (sdk_free) {
            var buffer: [2]Ast.Node.Index = undefined;
            const argument = (try actual.callArgumentFor(frame.cache, &buffer, 1)) orelse return false;
            const released = (try self.pathOf(frame, argument, depth + 1)) orelse return false;
            if (!std.mem.eql(u8, released, wanted) and !try self.samePayload(frame, wanted, released, depth + 1)) return false;
            const before = frame.cache.tree.firstToken(actual.callee.call_node);
            if (try self.redirectedBefore(frame, wanted, before, depth + 1)) return false;
            return std.mem.eql(u8, released, wanted) or
                !try self.redirectedBefore(frame, released, before, depth + 1);
        }
        if (std.mem.eql(u8, tree.tokenSlice(proto.name_token orelse return false), "deinit") and
            try frame.resolution.resolver.declaredInToolchainFile(actual.callee.reference.handle, "/std/heap/ArenaAllocator.zig"))
        {
            var buffer: [2]Ast.Node.Index = undefined;
            const receiver = (try actual.callArgumentFor(frame.cache, &buffer, 0)) orelse return false;
            const prefix = (try self.pathOf(frame, receiver, depth + 1)) orelse return false;
            return self.arenaAllocation(frame, try self.join(frame.root_path, prefix), depth + 1);
        }
        var parameter: u32 = 0;
        while (true) : (parameter += 1) {
            var buffer: [2]Ast.Node.Index = undefined;
            const argument = (try actual.callArgumentFor(frame.cache, &buffer, parameter)) orelse break;
            const prefix = (try self.pathOf(frame, argument, depth + 1)) orelse continue;
            const suffix = relativePath(prefix, wanted) orelse continue;
            const callee = (try self.calleeFrame(frame, actual, parameter, prefix, true)) orelse continue;
            if (try self.bodyReleases(callee, callee.body, suffix, depth + 1)) return true;
        }
        return false;
    }

    /// The SDK destructor invalidates allocations made through this exact
    /// arena's allocator factory, not copies of its parent allocator/header.
    fn arenaAllocation(self: *CleanupProof, frame: Frame, owner: []const u8, depth: u8) file_cache_mod.SummaryError!bool {
        const root = frame.root orelse return false;
        const cache = root.frame.cache;
        const tree = cache.tree;
        var node = root.rhs;
        for (0..64) |_| {
            try self.charge(root.frame, node, depth);
            switch (tree.nodeTag(node)) {
                .@"try" => node = tree.nodeData(node).node,
                .grouped_expression => node = tree.nodeData(node).node_and_token[0],
                else => break,
            }
        } else return false;
        var buffer: [2]Ast.Node.Index = undefined;
        const call = resolver_mod.TypeResolver.CallOperands.full(tree, &buffer, node) orelse return false;
        const allocation = (try cache.actualCallSummaryAt(call.queryToken(tree, node), root.frame.resolution)) orelse return false;
        if (!try root.frame.resolution.resolver.declaredInToolchainFile(allocation.callee.reference.handle, "/std/mem/Allocator.zig")) return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(allocation.callee.tree, &proto_buffer, allocation.callee.declaration) orelse return false;
        const name = allocation.callee.tree.tokenSlice(proto.name_token orelse return false);
        if (!std.mem.eql(u8, name, "alloc") and !std.mem.eql(u8, name, "allocSentinel") and
            !std.mem.eql(u8, name, "alignedAlloc") and !std.mem.eql(u8, name, "dupe") and
            !std.mem.eql(u8, name, "dupeZ")) return false;
        const allocator = (try allocation.callArgumentFor(cache, &buffer, 0)) orelse return false;
        const factory_call = resolver_mod.TypeResolver.CallOperands.full(tree, &buffer, allocator) orelse return false;
        const factory = (try cache.actualCallSummaryAt(factory_call.queryToken(tree, allocator), root.frame.resolution)) orelse return false;
        if (!try root.frame.resolution.resolver.declaredInToolchainFile(factory.callee.reference.handle, "/std/heap/ArenaAllocator.zig")) return false;
        const factory_proto = tokens.fnProto(factory.callee.tree, &proto_buffer, factory.callee.declaration) orelse return false;
        if (!std.mem.eql(u8, factory.callee.tree.tokenSlice(factory_proto.name_token orelse return false), "allocator")) return false;
        const receiver = (try factory.callArgumentFor(cache, &buffer, 0)) orelse return false;
        const path = (try self.pathOf(root.frame, receiver, depth + 1)) orelse return false;
        return std.mem.eql(u8, path, owner);
    }

    fn bodyReleases(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, wanted: []const u8, depth: u8) file_cache_mod.SummaryError!bool {
        try self.charge(frame, node, depth);
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) == .fn_decl) return false;
        if (tree.fullIf(node)) |conditional| {
            if (tree.nodeTag(conditional.ast.cond_expr) != .identifier) return false;
            const value = tree.tokenSlice(tree.nodeMainToken(conditional.ast.cond_expr));
            if (std.mem.eql(u8, value, "true")) return self.bodyReleases(frame, conditional.ast.then_expr, wanted, depth + 1);
            if (std.mem.eql(u8, value, "false")) {
                const other = conditional.ast.else_expr.unwrap() orelse return false;
                return self.bodyReleases(frame, other, wanted, depth + 1);
            }
            return false;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (resolver_mod.TypeResolver.CallOperands.full(tree, &buffer, node)) |call| {
            const token = call.queryToken(tree, node);
            if (try frame.cache.actualCallSummaryAt(token, frame.resolution)) |actual| {
                if (try self.callReleases(frame, actual, wanted, depth + 1)) return true;
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            if (try self.bodyReleases(frame, child, wanted, depth + 1)) return true;
        }
        return false;
    }

    fn pathOf(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, depth: u8) file_cache_mod.SummaryError!?[]const u8 {
        try self.charge(frame, node, depth);
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                const binding = frame.bindings.findAt(tree.tokenSlice(token), token) orelse return null;
                if (binding.name_token == frame.selected) return "";
                if (binding.origin == .param) return null;
                const rhs = frame.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return null;
                if (rhs == node) return null;
                return self.pathOf(frame, rhs, depth + 1);
            },
            .field_access => {
                const base, const field = tree.nodeData(node).node_and_token;
                const prefix = (try self.pathOf(frame, base, depth + 1)) orelse return null;
                const name = tree.tokenSlice(field);
                if (std.mem.eql(u8, name, "ptr")) {
                    if (try frame.resolution.typeOfNode(base)) |ty| {
                        if (frame.resolution.resolver.pointerSize(ty) == .slice) return prefix;
                    }
                }
                return if (prefix.len == 0) name else try std.fmt.allocPrint(self.arena.allocator(), "{s}.{s}", .{ prefix, name });
            },
            .deref, .address_of, .@"try" => return self.pathOf(frame, tree.nodeData(node).node, depth + 1),
            .grouped_expression, .unwrap_optional => return self.pathOf(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            .slice, .slice_open, .slice_sentinel => return self.pathOf(frame, tree.fullSlice(node).?.ast.sliced, depth + 1),
            .array_access => return self.pathOf(frame, tree.nodeData(node).node_and_node[0], depth + 1),
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const call = resolver_mod.TypeResolver.CallOperands.full(tree, &buffer, node) orelse return null;
        const token = call.queryToken(tree, node);
        const actual = (try frame.cache.actualCallSummaryAt(token, frame.resolution)) orelse return null;
        var parameter: u32 = 0;
        while (true) : (parameter += 1) {
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try actual.callArgumentFor(frame.cache, &argument_buffer, parameter)) orelse break;
            const prefix = (try self.pathOf(frame, argument, depth + 1)) orelse continue;
            const callee = (try self.calleeFrame(frame, actual, parameter, prefix, false)) orelse continue;
            const suffix = (try self.returnedPath(callee, callee.body, depth + 1)) orelse continue;
            return if (prefix.len == 0) suffix else if (suffix.len == 0) prefix else
                try std.fmt.allocPrint(self.arena.allocator(), "{s}.{s}", .{ prefix, suffix });
        }
        return null;
    }

    fn join(self: *CleanupProof, prefix: []const u8, suffix: []const u8) error{OutOfMemory}![]const u8 {
        if (prefix.len == 0) return suffix;
        if (suffix.len == 0) return prefix;
        return std.fmt.allocPrint(self.arena.allocator(), "{s}.{s}", .{ prefix, suffix });
    }

    /// A cleanup can free a child of a copied aggregate, or the same immutable
    /// scalar buffer stored under a different field. Header names alone prove
    /// neither relation. Unknown calls, indexed selections and changed roots
    /// withhold this additional certificate.
    fn samePayload(self: *CleanupProof, frame: Frame, wanted: []const u8, released: []const u8, depth: u8) file_cache_mod.SummaryError!bool {
        const root = frame.root orelse return false;
        const selected = try self.join(frame.root_path, wanted);
        const freed = try self.join(frame.root_path, released);
        if (relativePath(selected, freed) != null) {
            if (try self.pathOf(root.frame, root.rhs, depth + 1)) |path| {
                if (std.mem.eql(u8, path, selected) and !try self.containsIndex(root.frame, root.rhs, depth + 1))
                    return true;
            }
        }
        const binding = for (root.frame.bindings.items) |*candidate| {
            if (candidate.name_token == root.frame.selected) break candidate;
        } else return false;
        // This fallback reads the constructor, so both projections must still
        // have that exact value at publication, not an earlier captured value.
        const tags = root.frame.cache.tree.tokens.items(.tag);
        for (tags[binding.rhs_last + 1 .. root.use_token]) |tag| {
            if (tag == .keyword_for or tag == .keyword_while) return false;
        }
        if (try self.redirectedIn(root.frame, root.frame.body, selected, binding.rhs_last, root.use_token, depth + 1) or
            try self.redirectedIn(root.frame, root.frame.body, freed, binding.rhs_last, root.use_token, depth + 1) or
            try self.redirectedIn(root.frame, root.frame.body, freed, root.use_token, root.frame.cache.tree.lastToken(root.frame.body), depth + 1)) return false;
        const initializer = root.frame.cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
        const released_value = (try self.literalProjection(root.frame, initializer, freed, depth + 1)) orelse return false;
        const origin = (try self.scalarBufferOrigin(root.frame, released_value, depth + 1)) orelse return false;
        const selected_value = (try self.literalProjection(root.frame, initializer, selected, depth + 1)) orelse return false;
        return self.containsBufferOrigin(root.frame, selected_value, origin, depth + 1);
    }

    fn containsIndex(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, depth: u8) file_cache_mod.SummaryError!bool {
        try self.charge(frame, node, depth);
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) == .array_access) return true;
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            if (try self.containsIndex(frame, child, depth + 1)) return true;
        }
        return false;
    }

    fn literalProjection(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, path: []const u8, depth: u8) file_cache_mod.SummaryError!?Ast.Node.Index {
        try self.charge(frame, node, depth);
        if (path.len == 0) return node;
        const tree = frame.cache.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = tree.fullStructInit(&buffer, node) orelse return null;
        const end = std.mem.indexOfScalar(u8, path, '.') orelse path.len;
        for (literal.ast.fields) |field| {
            const first = tree.firstToken(field);
            if (first < 2 or tree.tokenTag(first - 2) != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(first - 2), path[0..end])) continue;
            return self.literalProjection(frame, field, if (end == path.len) "" else path[end + 1 ..], depth + 1);
        }
        return null;
    }

    fn scalarBufferOrigin(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, depth: u8) file_cache_mod.SummaryError!?Ast.TokenIndex {
        try self.charge(frame, node, depth);
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                const binding = frame.bindings.findAt(tree.tokenSlice(token), token) orelse return null;
                if (!binding.is_const or binding.origin == .param or binding.origin == .loop_capture) return null;
                const ty = (try frame.resolution.typeOfNode(node)) orelse return null;
                const actual = (try frame.resolution.resolver.normalizedType(ty)) orelse return null;
                if (frame.resolution.resolver.typeTag(actual) != .pointer) return null;
                const child = frame.resolution.resolver.childType(actual) orelse return null;
                // The type walk counts type layers, not this AST/helper depth.
                if (!try @import("../../cache/fresh_storage.zig").actualTypeAddressFree(frame.resolution, child, 0, &self.remaining)) return null;
                // Even a const header is no longer private after its address
                // escapes. Addressing its elements is not a header escape.
                for (tree.nodes.items(.tag), 0..) |tag, raw| {
                    if (tag != .address_of) continue;
                    const address: Ast.Node.Index = @enumFromInt(raw);
                    if (tree.firstToken(address) < binding.rhs_last or tree.firstToken(address) > tree.lastToken(frame.body)) continue;
                    try self.charge(frame, address, depth + 1);
                    const operand = tree.nodeData(address).node;
                    if (tree.nodeTag(operand) != .identifier) continue;
                    const use = tree.nodeMainToken(operand);
                    const target = frame.bindings.findAt(tree.tokenSlice(use), use) orelse continue;
                    if (target.name_token == binding.name_token) return null;
                }
                return binding.name_token;
            },
            .field_access => {
                const base, const field = tree.nodeData(node).node_and_token;
                if (!std.mem.eql(u8, tree.tokenSlice(field), "ptr")) return null;
                return self.scalarBufferOrigin(frame, base, depth + 1);
            },
            .address_of => return self.scalarBufferOrigin(frame, tree.nodeData(node).node, depth + 1),
            .array_access => return self.scalarBufferOrigin(frame, tree.nodeData(node).node_and_node[0], depth + 1),
            .grouped_expression => return self.scalarBufferOrigin(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            else => return null,
        }
    }

    fn containsBufferOrigin(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, origin: Ast.TokenIndex, depth: u8) file_cache_mod.SummaryError!bool {
        try self.charge(frame, node, depth);
        if (try self.scalarBufferOrigin(frame, node, depth + 1)) |found| return found == origin;
        const tree = frame.cache.tree;
        switch (tree.nodeTag(node)) {
            .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma,
            .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma,
            .array_init, .array_init_comma, .array_init_one, .array_init_one_comma,
            .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma,
            => {
                var children = Iterator.init(tree, node);
                while (children.next(tree)) |child| {
                    if (try self.containsBufferOrigin(frame, child, origin, depth + 1)) return true;
                }
            },
            else => {},
        }
        return false;
    }

    fn returnedPath(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, depth: u8) file_cache_mod.SummaryError!?[]const u8 {
        var result: ReturnedPath = .{};
        try self.collectReturnedPath(frame, node, &result, depth);
        return if (result.complete) result.path else null;
    }

    const ReturnedPath = struct { path: ?[]const u8 = null, complete: bool = true };

    fn collectReturnedPath(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, result: *ReturnedPath, depth: u8) file_cache_mod.SummaryError!void {
        try self.charge(frame, node, depth);
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) == .fn_decl) return;
        if (tree.nodeTag(node) == .@"return") {
            const value = tree.nodeData(node).opt_node.unwrap() orelse {
                result.complete = false;
                return;
            };
            const path = (try self.pathOf(frame, value, depth + 1)) orelse {
                result.complete = false;
                return;
            };
            if (result.path) |previous| {
                if (!std.mem.eql(u8, previous, path)) result.complete = false;
            } else result.path = path;
            return;
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| try self.collectReturnedPath(frame, child, result, depth + 1);
    }

    fn redirectedBefore(self: *CleanupProof, frame: Frame, wanted: []const u8, before: Ast.TokenIndex, depth: u8) file_cache_mod.SummaryError!bool {
        return self.redirectedIn(frame, frame.body, wanted, 0, before, depth);
    }

    /// Errdefer needs an error transfer from its scope after publication.
    /// An error after a nested scope has completed cannot run its errdefers.
    fn errorExitIn(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, first: Ast.TokenIndex, last: Ast.TokenIndex, after: Ast.TokenIndex, depth: u8) file_cache_mod.SummaryError!bool {
        try self.charge(frame, node, depth);
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) == .fn_decl or tree.firstToken(node) >= last or tree.lastToken(node) <= @max(first, after)) return false;
        switch (tree.nodeTag(node)) {
            .@"try" => return true,
            .@"return" => {
                const value = tree.nodeData(node).opt_node.unwrap() orelse return false;
                if (tree.nodeTag(value) == .error_value) return true;
                const actual = (try frame.resolution.typeOfNode(value)) orelse return true;
                const tag = frame.resolution.resolver.typeTag(actual) orelse return true;
                return tag == .error_set or tag == .error_union;
            },
            else => {},
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child|
            if (try self.errorExitIn(frame, child, first, last, after, depth + 1)) return true;
        return false;
    }

    fn redirectedIn(self: *CleanupProof, frame: Frame, node: Ast.Node.Index, wanted: []const u8, after: Ast.TokenIndex, before: Ast.TokenIndex, depth: u8) file_cache_mod.SummaryError!bool {
        try self.charge(frame, node, depth);
        const tree = frame.cache.tree;
        if (tree.nodeTag(node) == .fn_decl) return false;
        if (tree.nodeTag(node) == .@"defer" or tree.nodeTag(node) == .@"errdefer") {
            const token = tree.firstToken(node);
            const scope = enclosingScope(tree.tokens.items(.tag), token, tree.firstToken(frame.body), tree.lastToken(frame.body));
            const completed = scope.close > after and scope.close < before;
            const precedes_cleanup = scope.close == before and
                token > (frame.exit_cleanup orelse return false);
            if (!completed and !precedes_cleanup) return false;
            if (tree.nodeTag(node) == .@"errdefer" and
                !try self.errorExitIn(frame, frame.body, scope.open, scope.close, after, depth + 1)) return false;
            // Registration order differs from execution order. A later defer
            // runs before this cleanup even if registered before publication.
            var deferred_body = Iterator.init(tree, node);
            while (deferred_body.next(tree)) |child|
                if (try self.redirectedIn(frame, child, wanted, 0, tree.lastToken(child) + 1, depth + 1)) return true;
            return false;
        }
        if (tree.firstToken(node) >= before or tree.lastToken(node) <= after) return false;
        switch (tree.nodeTag(node)) {
            .assign, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
            .assign_bit_and, .assign_bit_or, .assign_bit_xor, .assign_shl, .assign_shr,
            => {
                const destination = tree.nodeData(node).node_and_node[0];
                if (try self.pathOf(frame, destination, depth + 1)) |path| {
                    if (relativePath(path, wanted) != null or relativePath(wanted, path) != null) return true;
                }
            },
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (resolver_mod.TypeResolver.CallOperands.full(tree, &buffer, node)) |call| {
            const token = call.queryToken(tree, node);
            if (try frame.cache.actualCallSummaryAt(token, frame.resolution)) |actual| {
                var parameter: u32 = 0;
                while (true) : (parameter += 1) {
                    var argument_buffer: [2]Ast.Node.Index = undefined;
                    const argument = (try actual.callArgumentFor(frame.cache, &argument_buffer, parameter)) orelse break;
                    const path = (try self.pathOf(frame, argument, depth + 1)) orelse continue;
                    if (relativePath(path, wanted) == null and relativePath(wanted, path) == null) continue;
                    if (frame.publication_rhs) {
                        // By-value slice payloads do not pass their source
                        // header's address. An implicit *Self receiver does.
                        const function = actual.callee.reference.actual_type.data.function;
                        if (parameter >= function.parameters.len) return true;
                        const formal = (try frame.resolution.resolver.normalizedType(function.parameters[parameter].type)) orelse return true;
                        const size = frame.resolution.resolver.pointerSize(formal);
                        if (size == .slice) continue;
                        // Other by-value aggregates can transport an alias;
                        // their header reach is not certified here.
                        if (size != .one) return true;
                        const selected_path = relativePath(path, wanted) orelse "";
                        const callee = (try self.calleeFrame(frame, actual, parameter, path, false)) orelse return true;
                        if (try self.redirectedIn(callee, callee.body, selected_path, 0, callee.cache.tree.lastToken(callee.body) + 1, depth + 1)) return true;
                        continue;
                    }
                    const effect = try frame.cache.callEffectAt(token, .{ .whole = actual.callee }, .{ .frame = frame.resolution, .remaining = &self.remaining });
                    if (effect != .read_only) return true;
                }
            } else {
                if (tree.nodeTag(call.ast.fn_expr) == .field_access) {
                    const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
                    if (try self.pathOf(frame, receiver, depth + 1)) |path| {
                        if (relativePath(path, wanted) != null or relativePath(wanted, path) != null) return true;
                    }
                }
                for (call.ast.params) |argument| {
                    if (try self.pathOf(frame, argument, depth + 1)) |path| {
                        if (relativePath(path, wanted) != null or relativePath(wanted, path) != null) return true;
                    }
                }
            }
        }
        var children = Iterator.init(tree, node);
        while (children.next(tree)) |child| {
            if (try self.redirectedIn(frame, child, wanted, after, before, depth + 1)) return true;
        }
        return false;
    }

    fn relativePath(prefix: []const u8, path: []const u8) ?[]const u8 {
        if (prefix.len == 0) return path;
        if (std.mem.eql(u8, prefix, path)) return "";
        if (path.len > prefix.len and std.mem.startsWith(u8, path, prefix) and path[prefix.len] == '.')
            return path[prefix.len + 1 ..];
        return null;
    }
};

const PointerParam = struct { name: []const u8 };

/// A `defer X.deinit()` / `defer alloc.free(X)` paired with the
/// lexical `{ ... }` it was declared inside.  Writes outside that
/// scope cannot see the registered cleanup — the defer hasn't
/// executed when control passes a sibling branch.
const DeferredItem = struct {
    name: []const u8,
    binding_token: Ast.TokenIndex,
    /// The `defer` keyword that registered the cleanup.
    token: Ast.TokenIndex,
    cleanup_token: Ast.TokenIndex,
    scope_open: Ast.TokenIndex,
    scope_close: Ast.TokenIndex,
};

const ScopeRange = struct { open: Ast.TokenIndex, close: Ast.TokenIndex };

/// Walk braces around `tok` to find the immediate enclosing
/// `{ ... }` pair.  Fall back to the fn body range when the defer
/// sits at the function-top scope.
fn enclosingScope(
    tags: []const std.zig.Token.Tag,
    tok: Ast.TokenIndex,
    fn_first: Ast.TokenIndex,
    fn_last: Ast.TokenIndex,
) ScopeRange {
    var open: Ast.TokenIndex = fn_first;
    var depth: i32 = 0;
    var t: Ast.TokenIndex = tok;
    while (t > fn_first) {
        t -= 1;
        switch (tags[t]) {
            .r_brace => depth += 1,
            .l_brace => {
                if (depth == 0) {
                    open = t;
                    break;
                }
                depth -= 1;
            },
            else => {},
        }
    }
    var close: Ast.TokenIndex = fn_last;
    depth = 1;
    t = open + 1;
    while (t <= fn_last) : (t += 1) {
        switch (tags[t]) {
            .l_brace => depth += 1,
            .r_brace => {
                depth -= 1;
                if (depth == 0) {
                    close = t;
                    break;
                }
            },
            else => {},
        }
    }
    return .{ .open = open, .close = close };
}

fn findPointerParam(name: []const u8, params: []const PointerParam) ?PointerParam {
    for (params) |p| if (std.mem.eql(u8, p.name, name)) return p;
    return null;
}

/// True iff the type expression starts with a pointer, including the
/// lexer's combined `**` token and an optional pointer qualifier.
fn isPointerType(tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    if (first > last) return false;
    var t: Ast.TokenIndex = first;
    if (tags[t] == .question_mark) {
        if (t + 1 > last) return false;
        t += 1;
    }
    return tags[t] == .asterisk or tags[t] == .asterisk_asterisk;
}

fn isDeinitOrClose(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or std.mem.eql(u8, name, "close");
}

/// True when the written place is reset by a `defer <place> = <literal>;`
/// that runs before the cleanup `cleanup` registered.  Defers unwind
/// last-in-first-out, so a clearing defer in the cleanup's own scope and
/// registered after it runs first; the out-param never holds the freed
/// storage when the cleanup fires.  The clearing defer must be in force on
/// every exit that follows the write: registered before the write, or as
/// the statement right after it (no `try`/`return` can run in between).
/// The reset value must be a literal, which names no local and so
/// borrows nothing.
fn clearedBeforeCleanup(
    tree: *const Ast,
    cleanup: DeferredItem,
    write_first: Ast.TokenIndex,
    write_eq: Ast.TokenIndex,
    stmt_end: Ast.TokenIndex,
    fn_first: Ast.TokenIndex,
    fn_last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    const place_len = write_eq - write_first;
    const write_scope = enclosingScope(tags, write_first, fn_first, fn_last);
    const write_in_cleanup_scope = write_scope.open == cleanup.scope_open and write_scope.close == cleanup.scope_close;
    var t: Ast.TokenIndex = cleanup.token + 1;
    while (t + place_len + 2 <= cleanup.scope_close) : (t += 1) {
        if (tags[t] != .keyword_defer) continue;
        // After the write only the very next statement is guaranteed to
        // be registered on every path that leaves the scope.
        if (t > write_first and !(write_in_cleanup_scope and t == stmt_end + 1)) continue;
        var i: Ast.TokenIndex = 0;
        while (i < place_len) : (i += 1) {
            if (tags[t + 1 + i] != tags[write_first + i]) break;
            if (!std.mem.eql(u8, tree.tokenSlice(t + 1 + i), tree.tokenSlice(write_first + i))) break;
        }
        if (i != place_len or tags[t + 1 + place_len] != .equal) continue;
        const clearing_scope = enclosingScope(tags, t, fn_first, fn_last);
        if (clearing_scope.open != cleanup.scope_open or clearing_scope.close != cleanup.scope_close) continue;
        var value = t + 2 + place_len;
        var literal = value <= cleanup.scope_close;
        while (literal and tags[value] != .semicolon) : (value += 1) {
            literal = value < cleanup.scope_close and switch (tags[value]) {
                .period, .l_brace, .r_brace, .ampersand, .string_literal, .number_literal => true,
                .identifier => tags[value - 1] == .period or std.mem.eql(u8, tree.tokenSlice(value), "null"),
                else => false,
            };
        }
        if (literal) return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    write_tok: Ast.TokenIndex,
    out_name: []const u8,
    deferred_name: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "write into out-param `{s}` uses `{s}` — `{s}` is registered for cleanup via `defer ... .deinit()`/`.free()`, so the out-param holds a dangling slice once the fn returns and the defer fires.  Clone the value with the caller's allocator before assigning",
        .{ out_name, deferred_name, deferred_name },
    );
    errdefer gpa.free(msg);

    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, write_tok),
        .end = try Pos.fromTokenEnd(tree, write_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "defer arena.deinit + out-param write using arena fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const ZigString = struct {
        \\    raw: *std.heap.ArenaAllocator,
        \\    pub fn init(s: *std.heap.ArenaAllocator) ZigString { return .{ .raw = s }; }
        \\};
        \\pub fn parse(out: *ZigString, gpa_alloc: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(gpa_alloc);
        \\    defer arena.deinit();
        \\    out.* = ZigString.init(&arena);
        \\}
    );
}

test "defer alloc.free(X) + out-param write using X fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Str = struct { ptr: usize };
        \\pub fn parse(install: *Str, alloc: std.mem.Allocator) !void {
        \\    const str = try alloc.alloc(u8, 4);
        \\    defer alloc.free(str);
        \\    install.* = .{ .ptr = @intFromPtr(str.ptr) };
        \\}
    );
}

test "out-param not pointer doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn parse(name: []const u8) !void {
        \\    var buf = name;
        \\    defer _ = buf;
        \\}
    );
}

test "no defer doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\pub fn parse(out: *[]const u8, src: []const u8) !void {
        \\    out.* = src;
        \\}
    );
}

test "primitive-typed out field doesn't fire" {
    // `this.count = fn(deferred, ...)` — count is usize, can't hold
    // a borrowed slice.  The deferred name appears in args only.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Outer = struct {
        \\    count: u32 = 0,
        \\    pub fn doIt(this: *Outer, alloc: std.mem.Allocator) !void {
        \\        const buf = try alloc.alloc(u8, 4);
        \\        defer alloc.free(buf);
        \\        this.count = doWork(buf);
        \\    }
        \\};
        \\fn doWork(_: []u8) u32 { return 0; }
    );
}

test "RHS with toOwnedSlice copy doesn't fire" {
    // `out.* = blk: { ... break :blk try tmp.toOwnedSlice(allocator); };`
    // The break value is OWNED via toOwnedSlice using the caller's
    // allocator.  defer tmp.deref() doesn't invalidate the copy.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Wrapper = struct {
        \\    pub fn deref(_: Wrapper) void {}
        \\    pub fn toOwnedSlice(_: Wrapper, _: std.mem.Allocator) ![]const u8 {
        \\        return "";
        \\    }
        \\};
        \\fn makeTmp() Wrapper { return .{}; }
        \\pub fn parse(out: *[]const u8, allocator: std.mem.Allocator) !void {
        \\    const tmp = makeTmp();
        \\    defer tmp.deref();
        \\    out.* = try tmp.toOwnedSlice(allocator);
        \\}
    );
}

test "*@This() pointer param resolves field type via containing struct" {
    // The declared parameter scope binds `@This()` to its container.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const PI = struct {
        \\    file_count: u32 = 0,
        \\    pub fn install(this: *@This(), alloc: std.mem.Allocator) !void {
        \\        var subdir: std.fs.Dir = undefined;
        \\        defer subdir.close();
        \\        this.file_count = copyFiles(subdir, alloc);
        \\    }
        \\};
        \\fn copyFiles(_: std.fs.Dir, _: std.mem.Allocator) u32 { return 0; }
    );
}

test "self-recursive fn: param only in recursive return — does NOT fire" {
    // Mirrors the ghostty/bun pattern where a fn like `transpileSourceCode`
    // tail-recurses passing `referrer` along:
    //   `return transpileSourceCode(... referrer ...)`
    // The non-recursive returns don't embed `referrer` in the result.
    // `result_independent_of_args` used to return false because it saw
    // `referrer` in the recursive-return expression; now self-recursive
    // returns are skipped, so the rule correctly suppresses the finding.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Result = struct { code: []const u8 };
        \\pub fn transpile(
        \\    allocator: std.mem.Allocator,
        \\    source: []const u8,
        \\    referrer: []const u8,
        \\    ret: *Result,
        \\) error{Invalid}!void {
        \\    var slice = std.ArrayList(u8).init(allocator);
        \\    defer slice.deinit();
        \\    if (source.len == 0) {
        \\        return transpile(allocator, referrer, referrer, ret);
        \\    }
        \\    ret.* = Result{ .code = "ok" };
        \\}
    );
}

test "deferred arg not embedded even when other param is — does NOT fire" {
    // The retained parameter is disjoint from the private copied buffer.
    // Canonical returned-storage facts, not scalar dependencies, own this proof.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Result = struct { label: []const u8 };
        \\fn transpile(
        \\    referrer: []const u8,
        \\    other: []const u8,
        \\) Result {
        \\    _ = referrer;
        \\    return Result{ .label = other };
        \\}
        \\pub fn caller(
        \\    alloc: std.mem.Allocator,
        \\    raw: []const u8,
        \\    other: []const u8,
        \\    ret: *Result,
        \\) !void {
        \\    const slice = try alloc.dupe(u8, raw);
        \\    defer alloc.free(slice);
        \\    ret.* = transpile(slice, other);
        \\}
    );
}

test "deferred arg IS the embedded param — fires" {
    // Sanity check: when the deferred arg maps to a param that IS
    // embedded in the called function's return, we must still fire.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Result = struct { label: []const u8 };
        \\fn transpile(
        \\    referrer: []const u8,
        \\    other: []const u8,
        \\) Result {
        \\    _ = other;
        \\    // `referrer` IS embedded in the return.
        \\    return Result{ .label = referrer };
        \\}
        \\pub fn caller(
        \\    alloc: std.mem.Allocator,
        \\    other: []const u8,
        \\    ret: *Result,
        \\) !void {
        \\    const slice = try alloc.dupe(u8, "borrowed");
        \\    defer alloc.free(slice);
        \\    ret.* = transpile(slice, other);
        \\}
    );
}

test "namespace defer (defer posix.close) is not tracked as local — does NOT fire" {
    // `posix` is `std.posix` (module namespace), not a local variable.
    // `defer posix.close(fd)` must not register `posix` as a deferred name.
    try testing.expectNoFire(check,
        \\const posix = std.posix;
        \\pub fn setupSocket(client: *posix.socket_t) !void {
        \\    const listener = posix.socket(posix.AF.INET, posix.SOCK.STREAM, 0) catch unreachable;
        \\    defer posix.close(listener);
        \\    client.* = posix.socket(posix.AF.INET, posix.SOCK.STREAM, 0) catch unreachable;
        \\}
        \\
    );
}

test "typed optional aggregate out copy retains no address" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const budget_mod = struct {
        \\    pub const Limit = enum { nodes, time };
        \\    pub const Stop = struct { limit: Limit, cap: u32 };
        \\};
        \\const Stop = budget_mod.Stop;
        \\const Oracle = struct {
        \\    stopped: ?Stop = null,
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Oracle) void { self.allocator.free(self.bytes); }
        \\    fn merge(o: *Oracle, seed: Stop) !void {
        \\        var child: Oracle = .{ .stopped = seed, .allocator = o.allocator, .bytes = try o.allocator.alloc(u8, 1) };
        \\        defer child.deinit();
        \\        o.stopped = o.stopped orelse child.stopped;
        \\    }
        \\};
    );
}

test "typed optional aggregate out copy retains nullable pointer" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const budget_mod = struct {
        \\    pub const Limit = enum { nodes, time };
        \\    pub const Stop = struct { limit: Limit, cap: u32, detail: ?*u8 };
        \\};
        \\const Stop = budget_mod.Stop;
        \\const Oracle = struct {
        \\    stopped: ?Stop = null,
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Oracle) void { self.allocator.free(self.bytes); }
        \\    fn merge(o: *Oracle) !void {
        \\        const bytes = try o.allocator.alloc(u8, 1);
        \\        var child: Oracle = .{
        \\            .stopped = .{ .limit = .nodes, .cap = 1, .detail = &bytes[0] },
        \\            .allocator = o.allocator,
        \\            .bytes = bytes,
        \\        };
        \\        defer child.deinit();
        \\        o.stopped = o.stopped orelse child.stopped;
        \\    }
        \\};
    );
}

test "typed numeric union returned from deferred state retains no address" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const ranges = struct {
        \\    pub const Range = union(enum) {
        \\        unknown,
        \\        integer: struct { min: i128, max: i128 },
        \\        floating: struct { min: f64, max: f64 },
        \\    };
        \\};
        \\const Range = ranges.Range;
        \\const State = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *State) void { self.allocator.free(self.bytes); }
        \\    fn rangeOf(self: *const State, name: []const u8) ?Range {
        \\        _ = name;
        \\        return .{ .integer = .{ .min = 0, .max = @intCast(self.bytes.len) } };
        \\    }
        \\};
        \\const Output = struct { range: Range = .unknown };
        \\pub fn copy(out: *Output, allocator: std.mem.Allocator) !void {
        \\    var state: State = .{ .allocator = allocator, .bytes = try allocator.alloc(u8, 1) };
        \\    defer state.deinit();
        \\    out.range = state.rangeOf("") orelse .unknown;
        \\}
    );
}

test "typed slice-bearing union returned from deferred state retains an address" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const ranges = struct {
        \\    pub const Range = union(enum) {
        \\        unknown,
        \\        integer: struct { min: i128, max: i128 },
        \\        floating: struct { min: f64, max: f64, bytes: []const u8 },
        \\    };
        \\};
        \\const Range = ranges.Range;
        \\const State = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *State) void { self.allocator.free(self.bytes); }
        \\    fn rangeOf(self: *const State, name: []const u8) ?Range {
        \\        _ = name;
        \\        return .{ .floating = .{ .min = 0, .max = 1, .bytes = self.bytes } };
        \\    }
        \\};
        \\const Output = struct { range: Range = .unknown };
        \\pub fn copy(out: *Output, allocator: std.mem.Allocator) !void {
        \\    var state: State = .{ .allocator = allocator, .bytes = try allocator.alloc(u8, 1) };
        \\    defer state.deinit();
        \\    out.range = state.rangeOf("") orelse .unknown;
        \\}
    );
}

test "typed nested address-bearing aggregate is not a scalar suffix" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Payload = struct { data: []const u8 };
        \\const Status = struct { tag: u32, nested: [1]Payload };
        \\const Scratch = struct {
        \\    width: Status,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.width.nested[0].data); }
        \\};
        \\const Output = struct { value: Status };
        \\pub fn copy(out: *Output, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    var scratch: Scratch = .{ .allocator = allocator, .width = .{ .tag = 1, .nested = .{.{ .data = bytes }} } };
        \\    defer scratch.deinit();
        \\    out.value = scratch.width;
        \\}
    );
}

test "typed scalar projection of address-bearing source retains no address" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Scratch = struct {
        \\    score: ?u32,
        \\    bytes: []const u8,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.bytes); }
        \\};
        \\pub fn copy(out: *?u32, allocator: std.mem.Allocator) !void {
        \\    var scratch: Scratch = .{ .score = 7, .bytes = try allocator.alloc(u8, 1), .allocator = allocator };
        \\    defer scratch.deinit();
        \\    out.* = scratch.score;
        \\}
    );
}

test "typed scalar graph does not erase explicit address bits" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Output = struct { value: usize };
        \\pub fn copy(out: *Output, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    defer allocator.free(bytes);
        \\    out.value = @intFromPtr(bytes.ptr);
        \\}
    );
}

test "typed address of deferred slice header still escapes" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Scratch = struct {
        \\    bytes: []u8,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.bytes); }
        \\};
        \\pub fn copy(out: **[]u8, allocator: std.mem.Allocator) !void {
        \\    var scratch: Scratch = .{ .bytes = try allocator.alloc(u8, 1), .allocator = allocator };
        \\    defer scratch.deinit();
        \\    out.* = &scratch.bytes;
        \\}
    );
}

test "typed double pointer can retain an independent slice header" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\pub fn copy(out: **[]u8, stable: *[]u8, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    defer allocator.free(bytes);
        \\    out.* = stable;
        \\}
    );
}

test "typed array copy retains borrowed element pointers" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Scratch = struct {
        \\    slots: [1]*u8,
        \\    bytes: []u8,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.bytes); }
        \\};
        \\pub fn copy(out: *[1]*u8, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.alloc(u8, 1);
        \\    var scratch: Scratch = .{ .slots = .{&bytes[0]}, .bytes = bytes, .allocator = allocator };
        \\    defer scratch.deinit();
        \\    out.* = scratch.slots[0..1].*;
        \\}
    );
}

test "later defer clearing the out-param before the cleanup doesn't fire" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Capture) void { _ = self; }
        \\};
        \\const Oracle = struct { capture: ?*Capture = null };
        \\pub fn after(o: *Oracle, gpa: std.mem.Allocator) !void {
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    o.capture = &exits;
        \\    defer o.capture = null;
        \\}
        \\pub fn before(o: *Oracle, gpa: std.mem.Allocator) !void {
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    defer o.capture = null;
        \\    o.capture = &exits;
        \\}
    );
}

test "clearing defer registered before the cleanup still fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Capture) void { _ = self; }
        \\};
        \\const Oracle = struct { capture: ?*Capture = null };
        \\pub fn run(o: *Oracle, gpa: std.mem.Allocator) !void {
        \\    defer o.capture = null;
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    o.capture = &exits;
        \\}
    );
}

test "clearing defer registered after a possible early exit still fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Capture) void { _ = self; }
        \\};
        \\const Oracle = struct { capture: ?*Capture = null };
        \\fn step() !void {}
        \\pub fn run(o: *Oracle, gpa: std.mem.Allocator) !void {
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    o.capture = &exits;
        \\    try step();
        \\    defer o.capture = null;
        \\}
    );
}

test "defer resetting the out-param to a local doesn't count as clearing" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Capture = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn deinit(self: *Capture) void { _ = self; }
        \\};
        \\const Oracle = struct { capture: ?*Capture = null };
        \\pub fn run(o: *Oracle, gpa: std.mem.Allocator, other: *Capture) !void {
        \\    var exits: Capture = .{ .gpa = gpa };
        \\    defer exits.deinit();
        \\    o.capture = &exits;
        \\    defer o.capture = other;
        \\}
    );
}

test "deferred module owning snapshot is independent of its source storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Snapshot = struct { bytes: []u8 };
        \\const Module = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Module) void { self.allocator.free(self.bytes); }
        \\    fn snapshotData(self: *const Module, gpa: std.mem.Allocator) !*Snapshot {
        \\        const snapshot = try gpa.create(Snapshot);
        \\        errdefer gpa.destroy(snapshot);
        \\        snapshot.* = .{ .bytes = try gpa.dupe(u8, self.bytes) };
        \\        return snapshot;
        \\    }
        \\};
        \\const Fixture = struct { data: ?*Snapshot = null };
        \\pub fn init(out: *Fixture, gpa: std.mem.Allocator) !void {
        \\    var module: Module = .{
        \\        .allocator = gpa, .bytes = try gpa.dupe(u8, "owned"),
        \\    };
        \\    defer module.deinit();
        \\    out.data = try module.snapshotData(gpa);
        \\}
    );
}

test "fresh snapshot allocation retaining deferred module bytes still escapes" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Snapshot = struct { bytes: []u8 };
        \\const Module = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Module) void { self.allocator.free(self.bytes); }
        \\    fn snapshotData(self: *const Module, gpa: std.mem.Allocator) !*Snapshot {
        \\        const snapshot = try gpa.create(Snapshot);
        \\        snapshot.* = .{ .bytes = self.bytes };
        \\        return snapshot;
        \\    }
        \\};
        \\const Fixture = struct { data: ?*Snapshot = null };
        \\pub fn init(out: *Fixture, gpa: std.mem.Allocator) !void {
        \\    var module: Module = .{
        \\        .allocator = gpa, .bytes = try gpa.dupe(u8, "borrowed"),
        \\    };
        \\    defer module.deinit();
        \\    out.data = try module.snapshotData(gpa);
        \\}
    );
}

test "deferred module borrowed return cannot inherit a same named owning summary" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Owning = struct {
        \\    fn snapshotData(gpa: std.mem.Allocator) ![]u8 {
        \\        return gpa.dupe(u8, "independent");
        \\    }
        \\};
        \\const Module = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Module) void { self.allocator.free(self.bytes); }
        \\    fn snapshotData(self: *const Module) []u8 { return self.bytes; }
        \\};
        \\pub fn init(out: *[]u8, gpa: std.mem.Allocator) !void {
        \\    var module: Module = .{
        \\        .allocator = gpa, .bytes = try gpa.dupe(u8, "borrowed"),
        \\    };
        \\    defer module.deinit();
        \\    out.* = module.snapshotData();
        \\}
    );
}

test "callee-local arena escape is not attributed to the deferred caller module" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Module = struct {
        \\    allocator: std.mem.Allocator,
        \\    bytes: []u8,
        \\    fn deinit(self: *Module) void { self.allocator.free(self.bytes); }
        \\    fn snapshotData(self: *const Module, gpa: std.mem.Allocator) ![]u8 {
        \\        var arena = std.heap.ArenaAllocator.init(gpa);
        \\        defer arena.deinit();
        \\        return arena.allocator().dupe(u8, self.bytes);
        \\    }
        \\};
        \\pub fn init(out: *[]u8, gpa: std.mem.Allocator) !void {
        \\    var module: Module = .{
        \\        .allocator = gpa, .bytes = try gpa.dupe(u8, "borrowed"),
        \\    };
        \\    defer module.deinit();
        \\    out.* = try module.snapshotData(gpa);
        \\}
    );
}

test "opaque deferred receiver result is not a proved out-param loan" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\    extern fn view(self: *const Buffer) []const u8;
        \\};
        \\pub fn publish(out: *[]const u8, allocator: std.mem.Allocator) !void {
        \\    var buffer: Buffer = .{
        \\        .bytes = try allocator.dupe(u8, "opaque"), .allocator = allocator,
        \\    };
        \\    defer buffer.deinit();
        \\    out.* = buffer.view();
        \\}
    );
}

test "one proved borrowed return arm survives an opaque sibling" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\extern fn unknownView() []const u8;
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\    fn view(self: *const Buffer, borrow: bool) []const u8 {
        \\        if (borrow) return self.bytes;
        \\        return unknownView();
        \\    }
        \\};
        \\pub fn publish(out: *[]const u8, allocator: std.mem.Allocator, borrow: bool) !void {
        \\    var buffer: Buffer = .{
        \\        .bytes = try allocator.dupe(u8, "borrowed"), .allocator = allocator,
        \\    };
        \\    defer buffer.deinit();
        \\    out.* = buffer.view(borrow);
        \\}
    );
}

test "opaque call inside an out-param literal is not a proved loan" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\extern fn unknownView(bytes: []const u8) []const u8;
        \\const Output = struct { bytes: []const u8 };
        \\pub fn publish(out: *Output, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.dupe(u8, "opaque");
        \\    defer allocator.free(bytes);
        \\    out.* = .{ .bytes = unknownView(bytes) };
        \\}
    );
}

test "direct literal payload preserves a proved loan beside an opaque sibling" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\extern fn unknownView(bytes: []const u8) []const u8;
        \\const Output = struct { bytes: []const u8, other: []const u8 };
        \\pub fn publish(out: *Output, allocator: std.mem.Allocator) !void {
        \\    const bytes = try allocator.dupe(u8, "borrowed");
        \\    defer allocator.free(bytes);
        \\    out.* = .{ .bytes = bytes, .other = unknownView(bytes) };
        \\}
    );
}

test "out-param allocation from its deferred local arena retains the provider loan" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\pub fn publish(out: *[]u8, allocator: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(allocator);
        \\    defer arena.deinit();
        \\    out.* = try arena.allocator().dupe(u8, "borrowed");
        \\}
    );
}

test "a borrowed clone spelling cannot erase its source loan" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\    fn clone(self: *const Buffer) []const u8 { return self.bytes; }
        \\};
        \\pub fn publish(out: *[]const u8, allocator: std.mem.Allocator) !void {
        \\    var buffer: Buffer = .{
        \\        .bytes = try allocator.dupe(u8, "borrowed"), .allocator = allocator,
        \\    };
        \\    defer buffer.deinit();
        \\    out.* = buffer.clone();
        \\}
    );
}

test "deferred no-op header does not own an external payload loan" {
    try testing.expectNoFireTyped(check,
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn deinit(_: *Buffer) void {}
        \\    fn view(self: *Buffer) []u8 { return self.bytes; }
        \\};
        \\fn publish(out: *[]u8, input: []u8) void {
        \\    var buffer: Buffer = .{ .bytes = input };
        \\    defer buffer.deinit();
        \\    out.* = buffer.view();
        \\}
    );
}

test "deferred sibling cleanup does not invalidate an independent pointer field" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, other: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.other); }
        \\    fn view(self: *Buffer) []u8 { return self.bytes; }
        \\};
        \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) !void {
        \\    var buffer: Buffer = .{
        \\        .bytes = input, .other = try allocator.dupe(u8, "other"), .allocator = allocator,
        \\    };
        \\    defer buffer.deinit();
        \\    out.* = buffer.view();
        \\}
    );
}

test "rebound deferred payload does not release its former external value" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void {
        \\        self.bytes = &.{};
        \\        self.allocator.free(self.bytes);
        \\    }
        \\    fn view(self: *Buffer) []u8 { return self.bytes; }
        \\};
        \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) void {
        \\    var buffer: Buffer = .{ .bytes = input, .allocator = allocator };
        \\    defer buffer.deinit();
        \\    out.* = buffer.view();
        \\}
    );
}

test "selected metadata does not alias a different freed allocation" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Status = struct { detail: ?*u8 };
        \\const Scratch = struct {
        \\    released: []u8, status: Status, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.released); }
        \\};
        \\fn publish(out: *Status, allocator: std.mem.Allocator) !void {
        \\    const released = try allocator.alloc(u8, 1);
        \\    const retained = try allocator.alloc(u8, 1);
        \\    var scratch: Scratch = .{
        \\        .released = released, .status = .{ .detail = &retained[0] }, .allocator = allocator,
        \\    };
        \\    defer scratch.deinit();
        \\    out.* = scratch.status;
        \\}
    );
}

test "selected indexed sibling does not inherit another element cleanup" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Payload = struct { data: []const u8 };
        \\const Scratch = struct {
        \\    nested: [2]Payload, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Scratch) void { self.allocator.free(self.nested[0].data); }
        \\};
        \\fn publish(out: *Payload, input: []const u8, allocator: std.mem.Allocator) !void {
        \\    const owned = try allocator.alloc(u8, 1);
        \\    var scratch: Scratch = .{ .nested = .{.{ .data = owned }, .{ .data = input }}, .allocator = allocator };
        \\    defer scratch.deinit();
        \\    out.* = scratch.nested[1];
        \\}
    );
}

test "deferred arena does not own allocations from its parent allocator" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn publish(out: *[]u8, allocator: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(allocator);
        \\    defer arena.deinit();
        \\    out.* = try arena.child_allocator.dupe(u8, "parent-owned");
        \\}
    );
}

test "copying an empty deferred arena does not free its incoming allocator" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn publish(out: *std.heap.ArenaAllocator, allocator: std.mem.Allocator) void {
        \\    var arena = std.heap.ArenaAllocator.init(allocator);
        \\    defer arena.deinit();
        \\    out.* = arena;
        \\}
    );
}

test "later registered deferred payload rebinding does not release the published input" {
    for ([_]bool{ false, true }) |before_publication| {
        const source = try std.fmt.allocPrint(std.testing.allocator,
            \\const std = @import("std");
            \\const Buffer = struct {{
            \\    bytes: []u8, allocator: std.mem.Allocator,
            \\    fn deinit(self: *Buffer) void {{ self.allocator.free(self.bytes); }}
            \\}};
            \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) void {{
            \\    var buffer: Buffer = .{{ .bytes = input, .allocator = allocator }};
            \\    defer buffer.deinit();
            \\    {s}
            \\    out.* = buffer.bytes;
            \\    {s}
            \\}}
        , .{
            if (before_publication) "defer buffer.bytes = &.{};" else "",
            if (before_publication) "" else "defer buffer.bytes = &.{};",
        });
        defer std.testing.allocator.free(source);
        try testing.expectNoFireTyped(check, source);
    }
}

test "earlier registered deferred rebinding does not prevent selected cleanup" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\};
        \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) void {
        \\    var buffer: Buffer = .{ .bytes = input, .allocator = allocator };
        \\    defer buffer.bytes = &.{};
        \\    defer buffer.deinit();
        \\    out.* = buffer.bytes;
        \\}
    );
}

test "rebinding a released sibling inside cleanup does not free the published alias" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Child = struct {
        \\    detail: *const u8, released: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Child) void {
        \\        self.released = &.{};
        \\        self.allocator.free(self.released);
        \\    }
        \\};
        \\fn publish(out: **const u8, input: []u8, allocator: std.mem.Allocator) void {
        \\    const shared = input;
        \\    var child: Child = .{ .detail = &shared[0], .released = shared, .allocator = allocator };
        \\    defer child.deinit();
        \\    out.* = child.detail;
        \\}
    );
}

test "completed inner deferred payload rebinding precedes outer cleanup" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\};
        \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) void {
        \\    var buffer: Buffer = .{ .bytes = input, .allocator = allocator };
        \\    defer buffer.deinit();
        \\    {
        \\        defer buffer.bytes = &.{};
        \\        out.* = buffer.bytes;
        \\    }
        \\}
    );
}

test "completed inner errdefer does not rebind a payload on normal exhaustion" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\};
        \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) !void {
        \\    var buffer: Buffer = .{ .bytes = input, .allocator = allocator };
        \\    defer buffer.deinit();
        \\    {
        \\        errdefer buffer.bytes = &.{};
        \\        out.* = buffer.bytes;
        \\    }
        \\}
    );
}

test "error exit deferred payload rebinding precedes normal cleanup" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\};
        \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) !void {
        \\    var buffer: Buffer = .{ .bytes = input, .allocator = allocator };
        \\    defer buffer.deinit();
        \\    errdefer buffer.bytes = &.{};
        \\    out.* = buffer.bytes;
        \\    return error.Failed;
        \\}
    );
}

test "error-valued normal break does not run an inner errdefer" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\};
        \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) !void {
        \\    var buffer: Buffer = .{ .bytes = input, .allocator = allocator };
        \\    defer buffer.deinit();
        \\    const rejected: anyerror!void = block: {
        \\        errdefer buffer.bytes = &.{};
        \\        out.* = buffer.bytes;
        \\        break :block error.Failed;
        \\    };
        \\    rejected catch {};
        \\}
    );
}
test "publication RHS transfers backing storage before deferred cleanup" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\fn publish(out: *[]u32, allocator: std.mem.Allocator) !void {
        \\    var values: std.ArrayList(u32) = .empty;
        \\    defer values.deinit(allocator);
        \\    try values.append(allocator, 7);
        \\    out.* = try values.toOwnedSlice(allocator);
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\    fn handoff(self: *Buffer) []u8 {
        \\        const result = self.bytes;
        \\        self.bytes = &.{};
        \\        return result;
        \\    }
        \\};
        \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) void {
        \\    var buffer: Buffer = .{ .bytes = input, .allocator = allocator };
        \\    defer buffer.deinit();
        \\    out.* = buffer.handoff();
        \\}
    );
}

test "publication RHS unrelated scalar mutation does not transfer its payload" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8, counter: u32 = 0, allocator: std.mem.Allocator,
        \\    fn deinit(self: *Buffer) void { self.allocator.free(self.bytes); }
        \\    fn view(self: *Buffer) []u8 { self.counter += 1; return self.bytes; }
        \\};
        \\fn publish(out: *[]u8, input: []u8, allocator: std.mem.Allocator) void {
        \\    var buffer: Buffer = .{ .bytes = input, .allocator = allocator };
        \\    defer buffer.deinit();
        \\    out.* = buffer.view();
        \\}
    );
}
