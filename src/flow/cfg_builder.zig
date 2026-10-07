//! AST → CFG lowering — the `Builder` struct and the public
//! `lowerFunction*` entry points.  See cfg.zig for the CFG data types
//! produced.

const std = @import("std");
const Ast = std.zig.Ast;
const abstract_state = @import("abstract_state.zig");
const config_mod = @import("../config.zig");
const file_cache = @import("../cache/file_cache.zig");
// `type_engine` is a build-module name (engine.zig), so ModuleId has to be
// reached through it rather than through a relative path to the directory.
const type_engine = @import("type_engine");
const fn_summary = @import("../model/fn_summary.zig");
const fresh_storage = @import("../cache/fresh_storage.zig");
const tokens = @import("../ast/tokens.zig");
// Comptime static-constant evaluation and lexical scope resolution.
// Owned there, not here: it answers "what does this name MEAN" and
// "how MANY of these are there", which are questions CFG construction
// never asks, and it carries the one declaration index this lowering
// used to build inline.  Called through [comptime_fill.Resolver];
// the lowering itself stays private to this file.
const comptime_fill = @import("comptime_fill.zig");
const receiver_mod = @import("../model/method_names.zig");
const model_mod = @import("../model/file_model.zig");
const type_query = @import("../model/type_query.zig");
const zls_resolver_mod = @import("../type_resolver.zig");
const budget_mod = @import("../budget.zig");
const return_storage = @import("../cache/return_storage.zig");
const SourcePolicy = @import("type_engine").SourcePolicy;

// CFG types re-bound for local convenience.
const cfg_types = @import("cfg.zig");
const Config = cfg_types.Config;
const BlockId = cfg_types.BlockId;
const LocalId = cfg_types.LocalId;
const SrcPos = cfg_types.SrcPos;
const StmtKind = cfg_types.StmtKind;
const Stmt = cfg_types.Stmt;
const ExprKind = cfg_types.ExprKind;
const StackLoanProof = cfg_types.StackLoanProof;
const BasicBlock = cfg_types.BasicBlock;
const Cfg = cfg_types.Cfg;
const LocalInfo = cfg_types.LocalInfo;
const InitHint = cfg_types.InitHint;
const LoweringError = file_cache.SummaryError;
const bounded_prefix = @import("bounded_prefix.zig");

/// Bounds on the per-expression walks below.  Named so the recorded
/// diagnostic and the enforced check cannot drift apart.
const max_classify_depth = 64;
const max_boolean_unwind = 64;

// ── Lowering ───────────────────────────────────────────────

/// Lower a single Zig function body (block_two or block_two_semicolon
/// for short, block / block_semicolon for longer) into a CFG.  Returns
/// null when the function has no body (extern, etc.).
pub fn lowerFunction(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    fn_decl: Ast.Node.Index,
) !?Cfg {
    return lowerFunctionFull(gpa, tree, fn_decl, &config_mod.Default, null);
}

/// Main entry point.  Generalizes the per-project knobs into Config
/// (phase 42).  `cache` is the per-file FileCache for FnSummary /
/// FileModel queries — required for cross-fn inference; pass null only
/// in narrow test helpers that exercise single-fn flow analysis.
pub fn lowerFunctionFull(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    fn_decl: Ast.Node.Index,
    config: *const Config,
    cache: ?*file_cache.FileCache,
) !?Cfg {
    return lowerFunctionFullWithZls(gpa, tree, fn_decl, config, cache, null);
}

/// Variant that also accepts a ZLS-backed type resolver.  When
/// provided, `receiverTypeOfNode` / `inferTypeNameFromInit` fall back
/// to ZLS for cross-module + generic-instantiation type queries that
/// zbc's own AST-only tracking can't answer.
pub fn lowerFunctionFullWithZls(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    fn_decl: Ast.Node.Index,
    config: *const Config,
    cache: ?*file_cache.FileCache,
    zls: ?*zls_resolver_mod.TypeResolver,
) !?Cfg {
    // Establish the source-width bound before token queries, line scans,
    // allocations, or narrowing any source position.
    if (!SourcePolicy.admitsSourceLength(tree.source.len)) return error.SourceTooWide;

    var buf: [1]Ast.Node.Index = undefined;
    const fn_proto = tokens.fnProto(tree, &buf, fn_decl) orelse return null;
    const body_node = tokens.bodyOf(tree, fn_decl) orelse return null;

    // Comptime-only functions (every parameter is `comptime`) are
    // evaluated entirely at comptime — their stack locals are
    // comptime constants embedded in the binary, not runtime stack
    // frames.  Skip analysis to avoid FPs like `return &local_array`
    // where the array is actually a comptime-known slice.
    if (fnAllParamsAreComptime(tree, fn_proto)) return null;

    // Pre-classify the fn's return type.  Only borrowed-shape returns
    // (slice/pointer) can leak a borrowed origin to the caller; value
    // returns move the value and are exempt from the escape check.
    const is_borrowed_ret = if (fn_proto.ast.return_type.unwrap()) |rt|
        returnTypeIsBorrowed(tree, rt)
    else
        false;
    // Noreturn fn (`!noreturn` / `noreturn`): the fn never returns
    // normally — Global.exit / @panic / infinite loops.  Any
    // stack-escape via out-param-write is unobservable: the
    // caller never resumes to read the dangling pointer.  Skip
    // the entire stack-escape analysis for these fns.
    const is_noreturn_fn = if (fn_proto.ast.return_type.unwrap()) |rt|
        returnTypeIsNoreturn(tree, rt)
    else
        false;

    // `owns_locals` was an annotation-comment opt-out that suppressed
    // composite-borrow detection inside a fn body.  With annotation
    // parsing retired, no fn opts out — inference always runs.
    const suppress_cb = false;

    // Use line offsets from FileCache when available (built once per file);
    // otherwise build fresh and transfer ownership to the builder.
    const cached_offsets: ?[]const u32 = if (cache) |c| try c.getLineOffsets() else null;
    const line_offsets = cached_offsets orelse try buildLineOffsets(gpa, tree.source);
    // Both numbers the borrow-walk budget diagnostic reports — the
    // bound in force and the value the counter reached — are the
    // whole-file AST node count in the `u32` that schema uses.  Convert
    // it once, here where lowering can still return an error, so the
    // walk never narrows unchecked: a tree with more than `maxInt(u32)`
    // nodes cannot be described by that schema at all — it would need
    // more source than the `u32` byte offsets `std.zig.Ast` addresses a
    // file with — so the count saturates at `maxInt(u32)` and lowering
    // gives up naming that ceiling as both bound and reached value.
    var fn_name: budget_mod.NameBuf = .{};
    if (fn_proto.name_token) |name_tok| fn_name.set(tree.tokenSlice(name_tok));
    const node_budget = std.math.cast(u32, tree.nodes.len) orelse
        return budget_mod.fail(.{
            .limit = .borrow_walk_nodes,
            .limit_value = std.math.maxInt(u32),
            .reached = std.math.maxInt(u32),
            .function = fn_name,
        });
    // The scope/extent resolver the fill proofs ask.  It owns the ONE
    // declaration index this lowering needs; there is no second copy,
    // and nothing here has to be freed for it — [Builder.tempDeinit]
    // releases it with the rest of the builder's storage.
    var loan_scratch = std.heap.ArenaAllocator.init(gpa);
    defer loan_scratch.deinit();
    var builder: Builder = .{
        .gpa = gpa,
        .tree = tree,
        .cache = cache,
        .fill = comptime_fill.Resolver.init(gpa, tree, cache, fn_proto),
        .zls = zls,
        .config = config,
        .is_borrowed_return_type = is_borrowed_ret,
        .is_noreturn_fn = is_noreturn_fn,
        .suppress_composite_borrow = suppress_cb,
        .fn_proto = fn_proto,
        .fn_name = fn_name,
        .fn_body_last = tree.lastToken(body_node),
        .fn_body_first = tree.firstToken(body_node),
        .fn_body_node = body_node,
        .self_type = null,
        .line_offsets = line_offsets,
        .owns_line_offsets = cached_offsets == null,
        .node_budget = node_budget,
    };
    defer builder.tempDeinit();
    if (cache) |c| {
        if (c.tree == tree) {
            builder.expression_loan_scratch = loan_scratch.allocator();
            builder.expression_loan_query = return_storage.ExpressionLoanQuery.init(.{
                .cache = c,
                .body = body_node,
                .scratch = &loan_scratch,
                .context = .{ .frame = c.cleanup_frame },
            });
        }
    }

    // The resolver answers about the lowering's own local table, and
    // that table belongs to the builder — so it is bound here, once the
    // builder has an address to point at, rather than at
    // construction.  Both pointers are to STORAGE, not a snapshot: a
    // local declared later is registered later and every later scope
    // question has to see it.
    builder.fill.bindLocals(&builder.name_to_local, &builder.locals);

    // Pull the containing type via the FileCache's FileModel so
    // `Self` / `*@This()` resolve inside param types and receiver-type
    // lookups have a starting scope.  Read after the builder exists so
    // an unreadable model is recorded like every other classification
    // query: `self_type` stays unset, the declared / syntactic
    // fallbacks take over, and the failure still leaves the builder
    // for the entry point below to re-raise instead of being filed as
    // "this fn is not a method".
    if (cache) |c| {
        builder.self_type = blk: {
            const model = c.fileModel() catch |err| {
                builder.noteResolutionError(err);
                break :blk null;
            };
            const ti = model.containingTypeOf(fn_decl) orelse break :blk null;
            break :blk ti.qualified_name;
        };
    }

    const entry_id = try builder.newBlock();
    var cur_block = entry_id;
    builder.lowerFunctionBody(body_node, &cur_block) catch |err| {
        // A walk that gave up has already recorded WHICH bound it hit; the
        // error alone carries no such record, so publish it before the
        // error leaves the lowering.
        if (err == error.AnalysisBudgetExceeded) {
            if (builder.budget_failure) |failure| return budget_mod.fail(failure);
        }
        return err;
    };
    if (builder.budget_failure) |failure| return budget_mod.fail(failure);
    // A failed type resolution is not an answer, so it leaves the
    // builder rather than silently weakening the escape check.
    if (builder.resolution_error) |err| return err;

    return try builder.finalize(tree, fn_decl, entry_id);
}

/// Build a sorted list of byte offsets where each line starts.
/// line_offsets[i] = byte offset of the first character on line i.
/// Used by posOfToken / endPosOf for O(log lines) position lookups.
pub fn buildLineOffsets(gpa: std.mem.Allocator, source: [:0]const u8) ![]u32 {
    if (!SourcePolicy.admitsSourceLength(source.len)) return error.SourceTooWide;
    var offsets: std.ArrayListUnmanaged(u32) = .empty;
    errdefer offsets.deinit(gpa);
    try offsets.append(gpa, 0);
    for (source, 0..) |c, i| {
        if (c == '\n') try offsets.append(gpa, @intCast(i + 1));
    }
    return offsets.toOwnedSlice(gpa);
}

test "source width: line offsets refuse before allocation or scanning" {
    for ([_]usize{ SourcePolicy.max_source_bytes, std.math.maxInt(usize) }) |length| {
        var source: [:0]const u8 = "";
        // Only the length is inspected; the guard must not access this
        // intentionally inaccessible range.
        source.len = length;
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{ .fail_index = 0 });
        try std.testing.expectError(error.SourceTooWide, buildLineOffsets(failing.allocator(), source));
        try std.testing.expect(!failing.has_induced_failure);
    }
}

test "source width: lowering refuses before AST and position queries" {
    const gpa = std.testing.allocator;
    var tree = try Ast.parse(gpa, "", .zig);
    defer tree.deinit(gpa);
    const original_source = tree.source;
    defer tree.source = original_source;
    tree.source.len = SourcePolicy.max_source_bytes;
    var failing = std.testing.FailingAllocator.init(gpa, .{ .fail_index = 0 });
    try std.testing.expectError(error.SourceTooWide, lowerFunctionFullWithZls(
        failing.allocator(),
        &tree,
        @enumFromInt(0),
        &config_mod.Default,
        null,
        null,
    ));
    try std.testing.expect(!failing.has_induced_failure);
}

// Consume the published domains, rather than checking metadata wiring alone.
test "integer domains: declared widths and inferred copies bound index reads" {
    const gpa = std.testing.allocator;
    const source =
        \\fn index(n: u1, wide: u64, huge: u128, signed: i1, signed_wide: i64, signed_huge: i128, zero: u0, size: usize, offset: isize) void {
        \\    const copy = n;
        \\    const widened: u64 = n;
        \\    const masked: u64 = wide & 1;
        \\    const shifted: u64 = wide >> 63;
        \\    _ = huge; _ = signed; _ = zero;
        \\    _ = copy; _ = widened; _ = masked; _ = shifted;
        \\}
    ;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var graph = (try lowerFunction(gpa, &tree, tree.rootDecls()[0])).?;
    defer graph.deinit(gpa);
    var state: abstract_state.AbstractState = .{ .integer_domains = graph.integer_domains };
    defer state.deinit(gpa);
    for (graph.locals, 0..) |local, index| {
        const term: cfg_types.IndexTerm = .{ .local = .{ .local = @enumFromInt(index) } };
        if (std.mem.eql(u8, local.name, "n") or std.mem.eql(u8, local.name, "copy")) {
            try std.testing.expect(state.provesIndexInBounds(term, 2));
            try std.testing.expect(!state.provesIndexInBounds(term, 1));
        } else if (std.mem.eql(u8, local.name, "zero")) {
            try std.testing.expect(state.provesIndexInBounds(term, 1));
        } else {
            try std.testing.expect(!state.provesIndexInBounds(term, 2));
        }
        if (std.mem.eql(u8, local.name, "huge")) {
            try std.testing.expect(state.provesNonNegative(term));
            try std.testing.expect(!state.provesLessThan(term, .{ .constant = std.math.maxInt(u64) }));
            try std.testing.expect(!state.provesComparison(.{
                .lhs = term,
                .rhs = .{ .constant = std.math.maxInt(u64) },
                .op = .le,
            }));
        } else if (std.mem.eql(u8, local.name, "size")) {
            try std.testing.expect(state.provesNonNegative(term));
            try std.testing.expect(!state.provesComparison(.{
                .lhs = term,
                .rhs = .{ .constant = std.math.maxInt(u64) },
                .op = .le,
            }));
        } else if (std.mem.eql(u8, local.name, "offset")) {
            try std.testing.expect(!state.provesLessThan(term, .{ .constant = std.math.maxInt(u64) }));
        } else if (std.mem.eql(u8, local.name, "wide") or
            std.mem.eql(u8, local.name, "widened") or
            std.mem.eql(u8, local.name, "masked") or
            std.mem.eql(u8, local.name, "shifted"))
        {
            try std.testing.expect(state.provesComparison(.{
                .lhs = term,
                .rhs = .{ .constant = std.math.maxInt(u64) },
                .op = .le,
            }));
        } else if (std.mem.eql(u8, local.name, "signed") or
            std.mem.eql(u8, local.name, "signed_wide"))
        {
            try std.testing.expect(!state.provesNonNegative(term));
            try std.testing.expect(state.provesLessThan(term, .{ .constant = std.math.maxInt(u64) }));
        } else if (std.mem.eql(u8, local.name, "signed_huge")) {
            try std.testing.expect(!state.provesNonNegative(term));
            try std.testing.expect(!state.provesLessThan(term, .{ .constant = std.math.maxInt(u64) }));
        }
    }
}

fn integerDomainLoweringAllocationFailures(gpa: std.mem.Allocator) !void {
    const source =
        \\fn index(n: u1, pick: bool) u16 {
        \\    var a: [2]u16 = if (pick) .{ 1, 2 } else .{ 3, 4 };
        \\    a = .{ 5, 6 };
        \\    var other = a;
        \\    a = other;
        \\    const selected: u1 = @intFromBool(false and pick);
        \\    const copy = n;
        \\    return other[copy] + a[selected];
        \\}
    ;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var graph = (try lowerFunction(gpa, &tree, tree.rootDecls()[0])).?;
    defer graph.deinit(gpa);
    var state: abstract_state.AbstractState = .{ .integer_domains = graph.integer_domains };
    defer state.deinit(gpa);
    for (graph.locals, 0..) |local, index| {
        if (!std.mem.eql(u8, local.name, "copy") and !std.mem.eql(u8, local.name, "selected")) continue;
        try std.testing.expect(state.provesIndexInBounds(.{
            .local = .{ .local = @enumFromInt(index) },
        }, 2));
    }
}

test "integer domains: lowering publication and teardown survive allocation failures" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        integerDomainLoweringAllocationFailures,
        .{},
    );
}

fn integerDomainSemanticLoweringAllocationFailures(gpa: std.mem.Allocator) !void {
    var context: zls_resolver_mod.TypeContext = undefined;
    try context.init(gpa, std.testing.io);
    defer context.deinit();
    var resolver: zls_resolver_mod.TypeResolver = undefined;
    try resolver.init(&context, gpa, "/tmp/zbc-integer-domain-lift.zig",
        \\const Small = u1;
        \\const Wide = u64;
        \\fn index(n: Small, size: usize, offset: isize) void {
        \\    const Local = u2;
        \\    const narrow: Local = 0;
        \\    const widened: Wide = n;
        \\    const copied = n;
        \\    const result = @as(Small, n);
        \\    const returned = identity(Small, n);
        \\    const type_value = Small;
        \\    _ = narrow; _ = widened; _ = copied; _ = result; _ = type_value;
        \\}
        \\fn identity(comptime T: type, value: T) T { return value; }
    );
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.zls = &resolver;
    var graph = (try lowerFunctionFullWithZls(
        gpa,
        tree,
        tree.rootDecls()[2],
        &config_mod.Default,
        &cache,
        &resolver,
    )).?;
    defer graph.deinit(gpa);
    var state: abstract_state.AbstractState = .{ .integer_domains = graph.integer_domains };
    defer state.deinit(gpa);
    for (graph.locals, 0..) |local, index| {
        const term: cfg_types.IndexTerm = .{ .local = .{ .local = @enumFromInt(index) } };
        if (std.mem.eql(u8, local.name, "n") or
            std.mem.eql(u8, local.name, "copied") or std.mem.eql(u8, local.name, "result") or
            std.mem.eql(u8, local.name, "returned"))
        {
            try std.testing.expect(state.provesIndexInBounds(term, 2));
        } else if (std.mem.eql(u8, local.name, "narrow")) {
            try std.testing.expect(state.provesIndexInBounds(term, 4));
            try std.testing.expect(!state.provesIndexInBounds(term, 2));
        } else if (std.mem.eql(u8, local.name, "size")) {
            try std.testing.expect(state.provesNonNegative(term));
            try std.testing.expect(state.provesComparison(.{
                .lhs = term,
                .rhs = .{ .constant = std.math.maxInt(u64) },
                .op = .le,
            }));
        } else if (std.mem.eql(u8, local.name, "offset")) {
            try std.testing.expect(state.provesLessThan(term, .{ .constant = std.math.maxInt(u64) }));
        } else {
            try std.testing.expect(!state.provesIndexInBounds(term, 4));
        }
    }
}

test "integer domains: semantic aliases retain destination types and reject metatypes" {
    try integerDomainSemanticLoweringAllocationFailures(std.testing.allocator);
}

test "integer domains: semantic type-query errors preserve allocation failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        integerDomainSemanticLoweringAllocationFailures,
        .{},
    );
}

test "integer domains: computed builtin preflight respects expression depth" {
    const Case = struct {
        fn run(depth: usize, exceeds: bool) !void {
            const gpa = std.testing.allocator;
            var source: std.ArrayList(u8) = .empty;
            defer source.deinit(gpa);
            try source.appendSlice(gpa, "fn index(flag: bool) u8 { const value: u8 = ");
            for (0..depth) |_| try source.appendSlice(gpa, "@as(u8, ");
            try source.appendSlice(gpa, "if (flag) 1 else 2");
            for (0..depth) |_| try source.appendSlice(gpa, ")");
            try source.appendSlice(gpa, "; return value; }\x00");
            var tree = try Ast.parse(gpa, source.items[0 .. source.items.len - 1 :0], .zig);
            defer tree.deinit(gpa);
            if (exceeds) {
                try std.testing.expectError(error.AnalysisBudgetExceeded, lowerFunction(gpa, &tree, tree.rootDecls()[0]));
            } else {
                var graph = (try lowerFunction(gpa, &tree, tree.rootDecls()[0])).?;
                defer graph.deinit(gpa);
                var state: abstract_state.AbstractState = .{ .integer_domains = graph.integer_domains };
                defer state.deinit(gpa);
                for (graph.locals, 0..) |local, index| {
                    if (!std.mem.eql(u8, local.name, "value")) continue;
                    try std.testing.expect(state.provesIndexInBounds(.{
                        .local = .{ .local = @enumFromInt(index) },
                    }, 256));
                }
            }
        }
    };
    try Case.run(8, false);
    try Case.run(max_classify_depth + 1, true);
}

test "integer domains: deferred index never borrows a sibling narrow binding" {
    const gpa = std.testing.allocator;
    const source =
        \\fn index(wide: u64, narrow: u1) void {
        \\    const a = [2]u16{ 1, 2 };
        \\    defer _ = a[wide];
        \\    { const wide: u1 = narrow; _ = a[wide]; }
        \\}
    ;
    var tree = try Ast.parse(gpa, source, .zig);
    defer tree.deinit(gpa);
    var graph = (try lowerFunction(gpa, &tree, tree.rootDecls()[0])).?;
    defer graph.deinit(gpa);
    var state: abstract_state.AbstractState = .{ .integer_domains = graph.integer_domains };
    defer state.deinit(gpa);
    var saw_deferred = false;
    var saw_narrow = false;
    for (graph.blocks) |block| {
        for (block.stmts) |statement| {
            if (statement.kind != .indexed_read) continue;
            if (statement.pos.line == 3) {
                saw_deferred = true;
                try std.testing.expect(!state.provesIndexInBounds(statement.kind.indexed_read.index, 2));
            } else {
                saw_narrow = true;
                try std.testing.expect(state.provesIndexInBounds(statement.kind.indexed_read.index, 2));
            }
        }
    }
    try std.testing.expect(saw_deferred and saw_narrow);
}

/// Binary-search line_offsets for the line containing `byte_offset`.
/// Returns 0-based line index and 0-based column.
inline fn byteToLineCol(line_offsets: []const u32, byte_offset: u32) struct { line: u32, col: u32 } {
    var lo: usize = 0;
    var hi: usize = line_offsets.len;
    // Find last index where line_offsets[i] <= byte_offset.
    while (lo + 1 < hi) {
        const mid = lo + (hi - lo) / 2;
        if (line_offsets[mid] <= byte_offset) lo = mid else hi = mid;
    }
    return .{ .line = @intCast(lo), .col = byte_offset - line_offsets[lo] };
}

/// Does `text` contain any of `patterns` as a substring?  Used by
/// the classifier + lowerCallStmt to dispatch on
/// project-configurable text matches (phase 42).
fn anyPatternMatches(text: []const u8, patterns: []const []const u8) bool {
    for (patterns) |p| {
        if (std.mem.indexOf(u8, text, p) != null) return true;
    }
    return false;
}

/// True iff every parameter in `fn_proto` is declared `comptime`.
/// A function with all-comptime params is only callable at comptime
/// (its body is evaluated by the compiler, not at runtime), so its
/// "stack" locals are comptime constants — not real stack frames.
fn fnAllParamsAreComptime(tree: *const Ast, fn_proto: Ast.full.FnProto) bool {
    if (fn_proto.ast.params.len == 0) return false;
    var it = fn_proto.iterate(tree);
    while (it.next()) |param| {
        const cn = param.comptime_noalias orelse return false;
        if (tree.tokenTag(cn) != .keyword_comptime) return false;
    }
    return true;
}

/// Return the base type identifier of a field's declared type —
/// strips `?`/`const`/`[]`/`*`/`[N]` wrappers and returns the last
/// dotted-chain identifier.  Used to descend through field-type
/// chains (`outer.foo: Inner` → "Inner", `outer.bar: *lib.Bar` →
/// "Bar").  Returns null on unparseable shapes.
fn baseTypeNameOfField(tree: *const Ast, field: *const model_mod.FieldInfo) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = field.type_first;
    while (t <= field.type_last) : (t += 1) {
        switch (tags[t]) {
            .question_mark, .asterisk, .keyword_const => continue,
            .l_bracket => {
                // Skip the bracket group `[...]`.
                var d: u32 = 1;
                t += 1;
                while (t <= field.type_last and d > 0) : (t += 1) {
                    if (tags[t] == .l_bracket) d += 1;
                    if (tags[t] == .r_bracket) d -= 1;
                }
                if (t > field.type_last) return null;
                t -= 1; // re-step into the next-iteration `t += 1`
            },
            .identifier, .builtin => break,
            else => return null,
        }
    }
    if (t > field.type_last) return null;
    // Walk dotted-chain identifiers; return the LAST.
    var last_name: ?[]const u8 = null;
    var expecting_ident: bool = true;
    while (t <= field.type_last) : (t += 1) {
        if (expecting_ident) {
            if (tags[t] != .identifier and tags[t] != .builtin) return last_name;
            last_name = tree.tokenSlice(t);
            expecting_ident = false;
        } else {
            if (tags[t] != .period) break;
            expecting_ident = true;
        }
    }
    return last_name;
}

/// How far a wrapper peel may go before it stops describing the
/// bound value.
const PeelDepth = enum {
    /// Stop at anything that changes the value's TYPE.
    declared_type,
    /// Look through the optional unwrap too, answering "what type is
    /// the value that ends up bound?".
    optional_payload,
};

/// The node whose value an initializer or scrutinee yields.  `try e`,
/// `e.?` and `(e)` all evaluate to `e` — or, for the payload view, to
/// the value `e` produces — so a question asked ABOUT that value has
/// to ask about `e`, not the wrapper.  Returns `init_node` itself when
/// it is not wrapped.
///
/// `catch` / `orelse` are peeled only past a VACUOUS fallback.  The
/// bound value is the fallback's whenever the fallback can produce
/// one: `const p = get() orelse &local` really does hold this frame's
/// storage on the fallback path.  `try` has no such arm — its error
/// path leaves the function, so the value is unconditionally the
/// inner expression's.
///
/// Origin classification stays with `classifyExpr`'s own (narrower)
/// unwrap: this helper answers typing questions only and asserts
/// nothing about where the value's storage lives.
fn initValueNode(self: *Builder, init_node: Ast.Node.Index) Ast.Node.Index {
    return initPeelNode(self, init_node, .optional_payload).node;
}

/// The TYPE-PRESERVING peel: what a wrapper leaves behind when the
/// bound value keeps the inner expression's type.  `.unwrap_optional`
/// is the one wrapper that is NOT crossed, because `f().?` does not
/// bind `f()` — it binds f's optional PAYLOAD, and nothing about the
/// callee's spelling reveals whether that payload is a pointer.
/// `b.parent()` may return `?Box` by value just as well as `?*Box`.
///
/// Use this view for the syntactic pointer-shape proofs in
/// `lowerVarDecl`; a semantic type query wants `initValueNode`,
/// which resolves the payload type properly.
fn initShapeNode(self: *Builder, init_node: Ast.Node.Index) Ast.Node.Index {
    return initPeelNode(self, init_node, .declared_type).node;
}

/// What a wrapper peel leaves behind, and whether getting there
/// ACCEPTED an error on the way.
///
/// `try e` and `e catch <vacuous>` bind the callee's error-union
/// SUCCESS PAYLOAD, not the `E!T` the callee declared — so a question
/// about what the binding holds has to be asked about the payload, and
/// a question about the callee's DECLARATION has to read the payload
/// of its declared `E!T`.  That is what `accepted_error` reports, and
/// `declaredCallYieldsPointer` is what acts on it.  `orelse` answers
/// an optional and unwraps no error, so it never sets the flag.
const Peeled = struct {
    node: Ast.Node.Index,
    accepted_error: bool,
};

fn initPeelNode(
    self: *Builder,
    init_node: Ast.Node.Index,
    depth: PeelDepth,
) Peeled {
    const tree = self.tree;
    var node = init_node;
    var accepted_error = false;
    while (true) {
        switch (tree.nodeTag(node)) {
            .grouped_expression => node = tree.nodeData(node).node_and_token[0],
            .unwrap_optional => {
                if (depth == .declared_type) return .{ .node = node, .accepted_error = accepted_error };
                node = tree.nodeData(node).node_and_token[0];
            },
            .@"try" => {
                node = tree.nodeData(node).node;
                accepted_error = true;
            },
            .@"catch" => {
                const data = tree.nodeData(node).node_and_node;
                if (!fallbackYieldsNothing(self, data[1])) return .{ .node = node, .accepted_error = accepted_error };
                node = data[0];
                accepted_error = true;
            },
            .@"orelse" => {
                const data = tree.nodeData(node).node_and_node;
                if (!fallbackYieldsNothing(self, data[1])) return .{ .node = node, .accepted_error = accepted_error };
                node = data[0];
            },
            else => return .{ .node = node, .accepted_error = accepted_error },
        }
    }
}

/// True when a `catch` / `orelse` fallback cannot yield a value, so the
/// wrapper's value is unconditionally its left operand's. `catch return e`,
/// `orelse unreachable`, and a call whose resolved result type is noreturn
/// qualify, including a block ending in such a call. Any value-yielding or
/// unresolved fallback remains conservative.
fn fallbackYieldsNothing(self: *Builder, node: Ast.Node.Index) bool {
    return fallbackDiverges(self, node, 0);
}

/// How deeply a fallback may nest its own value expressions before the
/// walk stops trusting itself.  Each level consumes source, so this
/// bounds pathological nesting rather than acting as an analysis budget.
const max_fallback_nesting: u8 = 16;

/// True when `node` cannot produce a value on ANY path: it returns,
/// continues, breaks without a label, is unreachable, or calls a typed noreturn callee.
///
/// The wrapper question is about the fallback as a whole, not about one
/// spelling of it, so a fallback that leaves on every path counts however
/// many wrappers it is written through.  That is what makes
///
///     const h = ctx.load(path) catch |err| switch (err) {
///         error.OutOfMemory => return error.OutOfMemory,
///         else => return error.Unavailable,
///     };
///
/// peel to `ctx.load(path)`: every prong returns, so the binding is
/// unconditionally the call's success payload.  A single value-yielding
/// prong keeps the fallback binding, exactly as a bare `catch &local`
/// does — the prong's own body is then the thing to look at.
fn fallbackDiverges(self: *Builder, node: Ast.Node.Index, depth: u8) bool {
    const tree = self.tree;
    if (depth >= max_fallback_nesting) return false;
    const tags = tree.tokens.items(.tag);
    var cur = node;
    while (true) switch (tree.nodeTag(cur)) {
        .grouped_expression => cur = tree.nodeData(cur).node_and_token[0],
        .block, .block_semicolon, .block_two, .block_two_semicolon => {
            const Iterator = @import("type_engine").AstIterator;
            var statements = Iterator.init(tree, cur);
            var last: ?Ast.Node.Index = null;
            while (statements.next(tree)) |current| last = current;
            const tail = last orelse return false;
            cur = tail;
        },
        // `target_expr` is the prong's BODY (`values` holds the labels).
        .@"switch", .switch_comma => {
            const switch_node = tree.fullSwitch(cur) orelse return false;
            if (switch_node.ast.cases.len == 0) return false;
            for (switch_node.ast.cases) |case_node| {
                const case_full = tree.fullSwitchCase(case_node) orelse return false;
                if (!fallbackDiverges(self, case_full.ast.target_expr, depth + 1)) return false;
            }
            return true;
        },
        // Every possible branch must leave before a value can be bound.
        .@"if", .if_simple => {
            const branch = tree.fullIf(cur) orelse return false;
            if (!fallbackDiverges(self, branch.ast.then_expr, depth + 1)) return false;
            const else_expr = branch.ast.else_expr.unwrap() orelse return false;
            if (!fallbackDiverges(self, else_expr, depth + 1)) return false;
            return true;
        },
        // `break;` leaves the enclosing loop / switch and hands back
        // nothing, but `break :blk value` IS that label's value.
        .@"break" => {
            const after = tree.nodeMainToken(cur) + 1;
            if (after < tags.len and tags[after] == .colon) return false;
            return true;
        },
        .@"continue", .@"return", .unreachable_literal => return true,
        .call, .call_one, .call_comma, .call_one_comma => return self.callReturnsNoreturn(cur),
        else => return false,
    };
}

/// later in the body.  Used by `lowerVarDecl` to infer `is_pointer`
/// for opaque-init locals (`var p = pool.get(); p.* = …;`) so
/// `&p.field` later doesn't fire stack-escape.
fn localIsDereferencedAfter(
    tree: *const Ast,
    name: []const u8,
    name_tok: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    if (name_tok + 1 > last) return false;
    var t: Ast.TokenIndex = name_tok + 1;
    while (t + 1 <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        // Must NOT be a field access (`x.name.*` — `name` here is a
        // field, not the local).  The preceding token is `.` in
        // that case.
        if (t > 0 and tags[t - 1] == .period) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        if (tags[t + 1] == .period_asterisk) return true;
    }
    return false;
}

/// True when the outer collection type stores pointer elements.
///
/// This deliberately inspects only the element position of a slice, array,
/// or known ArrayList spelling. A pointer elsewhere in a generic type does
/// not make an indexed element a pointer.
fn typeRangeHasPointerElement(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    if (first > last) return false;

    var t = first;
    while (t <= last and
        (tags[t] == .question_mark or
            tags[t] == .keyword_const or
            tags[t] == .keyword_var)) : (t += 1)
    {}

    if (t <= last and tags[t] == .l_bracket) {
        const close = tokens.matchBracket(tags, t, last) orelse return false;
        return typeRangeStartsWithPointer(tags, close + 1, last);
    }

    while (t + 1 <= last) : (t += 1) {
        if (tags[t] != .identifier or tags[t + 1] != .l_paren) continue;
        const name = tree.tokenSlice(t);
        if (!std.mem.eql(u8, name, "ArrayList") and
            !std.mem.eql(u8, name, "ArrayListUnmanaged") and
            !std.mem.eql(u8, name, "Managed"))
        {
            continue;
        }
        const close = tokens.matchParen(tags, t + 1, last) orelse return false;
        return typeRangeStartsWithPointer(tags, t + 2, close -| 1);
    }
    return false;
}

fn typeRangeStartsWithPointer(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (first > last) return false;
    var t = first;
    while (t <= last and
        (tags[t] == .question_mark or
            tags[t] == .keyword_const or
            tags[t] == .keyword_var)) : (t += 1)
    {}
    return t <= last and tags[t] == .asterisk;
}

/// True when a declared type is spelled `?` + (`const`/`var`)* + `*` —
/// an optional whose payload is a pointer.  Unwrapping such an
/// optional hands out the pointer, so `if (recv.field) |cap|` binds a
/// pointer BY VALUE.  The `?` is required: a bare `*T` field has no
/// payload to capture and never reaches this path.
fn typeRangeIsOptionalPointer(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    if (first > last or tags[first] != .question_mark) return false;
    var t = first + 1;
    while (t <= last and
        (tags[t] == .keyword_const or tags[t] == .keyword_var)) : (t += 1)
    {}
    return t <= last and tags[t] == .asterisk;
}

/// True when a declared type names a POINTER itself — `*T`, `*const T`,
/// `*var T`.  A `?*T` declares an OPTIONAL whose payload is a pointer:
/// the optional still occupies its field slot, and only the `?.` that
/// unwraps it reaches the pointer.  So unlike
/// `typeRangeStartsWithPointer`, this does NOT peel a leading `?` —
/// it answers "does the value of this field live somewhere else",
/// which only means anything for a field some further access reads
/// THROUGH.  The access an address-of itself names is a slot, and
/// `&x.f` never dereferences `f` whatever `f` is declared as.
fn typeRangeIsPointerValue(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    if (first > last) return false;
    var t = first;
    while (t <= last and
        (tags[t] == .keyword_const or tags[t] == .keyword_var)) : (t += 1)
    {}
    return t <= last and tags[t] == .asterisk;
}

/// True when a declared type is an ERROR UNION whose SUCCESS payload is a
/// pointer — `!*T`, `anyerror!*const T`.
///
/// Only meaningful to a binding that accepted the error (`try` / `catch`),
/// because that is what binds the payload.  Without one the binding holds
/// the whole `E!T`, which is not a pointer, so the same declaration must
/// not answer the other way.  The `!` is what separates the two sides, so
/// the payload is read from just past it; a leading error-set name
/// (`anyerror`, `MyError`) sits before the `!` and does not shift it.
fn errorUnionPayloadIsPointer(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    var t = first;
    while (t <= last) : (t += 1) {
        if (tags[t] != .bang) continue;
        var payload = t + 1;
        while (payload <= last and
            (tags[payload] == .keyword_const or tags[payload] == .keyword_var)) : (payload += 1)
        {}
        return payload <= last and tags[payload] == .asterisk;
    }
    return false;
}

/// The first token of a declared type's SUCCESS PAYLOAD — the token
/// just past its `!` — or null when the range holds no `!` at all.
/// A leading error-set name (`anyerror`, `MyError`) sits before the
/// `!` and does not shift it, and `const` / `var` before the payload
/// are part of what the payload IS, so both are stepped over.
fn errorUnionPayloadFirst(
    tags: []const std.zig.Token.Tag,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) ?Ast.TokenIndex {
    var t = first;
    while (t <= last) : (t += 1) {
        // A `{` opens a body, and an error union's `!` is always in
        // the type head: a `!` inside a struct or tuple literal is a
        // FIELD's error union, not this type's.
        if (tags[t] == .l_brace) return null;
        if (tags[t] != .bang) continue;
        var payload = t + 1;
        while (payload <= last and
            (tags[payload] == .keyword_const or tags[payload] == .keyword_var)) : (payload += 1)
        {}
        return payload;
    }
    return null;
}

/// True when a declared type is an error set — spelled `anyerror` or
/// `error{ … }`.  A payload of such a type IS an error value, so a
/// switch prong that captures it (`switch (r) { .err => |e| …
/// return e }` over `union(enum) { ok: u8, err: anyerror }`) makes
/// `return <cap>` an error return, and Zig replays `errdefer` frees
/// not be treated that way.  Compared on source text: `anyerror` is
/// unambiguous, and the token tag it lexes to is not worth pinning.
fn typeRangeIsErrorSet(
    tree: *const Ast,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    if (first > last) return false;
    if (tags[first] == .keyword_error) return true;
    return std.mem.eql(u8, tree.tokenSlice(first), "anyerror");
}

/// Inclusive token ranges live with the scope resolver that produces
/// them — the module that answers "where does this declaration begin
/// and end" is the one place that answer may exist, so a second
/// definition here would be a second answer to the same question.
const TokenSpan = comptime_fill.TokenSpan;

/// Identity of a re-tested `if` condition — see [GuardId] in
/// abstract_state.zig, re-exported by cfg.zig so the CFG and its
/// builder name the same type.
const GuardId = cfg_types.GuardId;

// ── Builder ────────────────────────────────────────────────

const LoopCtx = struct {
    continue_to: BlockId,
    merge: BlockId,
    defer_depth: usize,
    /// Label slice on the source (no colon), or null for unlabeled
    /// loops.  `break :name` walks the loop stack from inside out
    /// matching this field.
    label: ?[]const u8 = null,
};

/// Selected values retain their error channel and array mask before merging.
/// These locals exist only in the CFG; source writes cannot change them.
const ValueOutcomeFrame = struct {
    error_local: ?LocalId = null,
    array_local: ?LocalId = null,
    scalar_local: ?LocalId = null,
    scalar_guard: ?LocalId = null,
    return_kind: ?*ExprKind = null,
};

/// Labeled non-loop blocks — `blk: { ... break :blk val; }`.  Only
/// labeled break can target these; continue is invalid (compiler
/// catches at parse time, but defensively ignored here).
const BlockLabelCtx = struct {
    label: []const u8,
    merge: BlockId,
    defer_depth: usize,
    result_frame: ?ValueOutcomeFrame = null,
};

const DeferKind = enum { normal, err };
const DeferEntry = struct { kind: DeferKind, body: Ast.Node.Index };

const Builder = struct {
    gpa: std.mem.Allocator,
    tree: *const Ast,
    /// Per-file FileCache for FnSummary / FileModel queries — the
    /// per-file shared model + inference cache.
    cache: ?*file_cache.FileCache = null,
    address_cache: ?file_cache.FileCache = null,
    expression_loan_query: ?return_storage.ExpressionLoanQuery = null,
    expression_loan_scratch: ?std.mem.Allocator = null,
    /// Nesting depth of the current `classifyExpr` recursion.
    classify_depth: u8 = 0,
    /// Set by whichever bounded walk gave up first, naming the limit,
    /// its bound, and the expression that tripped it.  `null` until a
    /// walk exhausts, so "lowering completed" and "lowering gave up"
    /// are distinguishable without a second flag.
    budget_failure: ?budget_mod.Diagnostic = null,
    /// Whole-file AST node count as the `u32` the budget diagnostic
    /// reports.  Converted once, where the Builder is built, so every
    /// walk that bounds itself by it compares against a value already
    /// known to fit instead of narrowing the `usize` count again.
    node_budget: u32,
    /// Set by the first type-resolution query that FAILED (allocation,
    /// cancellation) that a classification depended on — the chain
    /// walk, the address-of direct-LHS check, the local registration's
    /// pointer fallback, and the pointer / ownership / noreturn
    /// classifications fed by the ZLS resolver and by the summary and
    /// file-model lookups underneath them.  An unresolved type is an
    /// answer of "nobody can tell" and is resolved conservatively,
    /// keeping the frame; a failed query is an error the caller has to
    /// see, so it is re-raised by the lowering entry point rather than
    /// being folded into "undecided" or into a conservative verdict the
    /// caller is never told about.  `queryOrUnknown` and `modelOrNull`
    /// are the funnels, so no query can quietly answer for a failure.
    resolution_error: ?anyerror = null,
    /// Enclosing function's name, copied out of the source.  Reported
    /// with a budget failure so the CLI can name the function whose
    /// lowering gave up.
    fn_name: budget_mod.NameBuf = .{},
    /// Optional ZLS-backed type resolver.  When set, `receiverTypeOfNode`
    /// falls back to ZLS when zbc's own type-name tracking can't
    /// resolve a local (cross-module types, generic instantiations,
    /// inferred-from-method-call locals).  null = legacy AST-only path.
    zls: ?*zls_resolver_mod.TypeResolver = null,
    config: *const Config = &config_mod.Default,
    /// The struct/union/enum that contains the fn being lowered.  Set
    /// by the caller of `build` per fn (via `lib.zig`'s walker).
    /// Used to resolve `Self` / `*@This()` in param types and to seed
    /// the lookup namespace for `<recv>.method()` disambiguation.
    self_type: ?[]const u8 = null,
    blocks: std.ArrayListUnmanaged(BasicBlock) = .empty,
    /// Per-block staging — stmts being appended.  Flushed to `blocks[i].stmts`
    /// in finalize().
    block_stmts: std.ArrayListUnmanaged(std.ArrayListUnmanaged(Stmt)) = .empty,
    block_successors: std.ArrayListUnmanaged(std.ArrayListUnmanaged(BlockId)) = .empty,
    locals: std.ArrayListUnmanaged(LocalInfo) = .empty,
    integer_domains: std.ArrayListUnmanaged(abstract_state.IntegerDomain) = .empty,
    /// Parsed fn prototype for the fn being lowered.  Used by
    /// registerFnParams.  Optional only for cfg-builder constructs
    /// outside of normal fn lowering (currently none).
    fn_proto: ?Ast.full.FnProto = null,
    /// Last token of the fn body (the closing `}`).  Set at
    /// construction; used by lowerVarDecl's body-use-signal scan
    /// for is_pointer inference (`var p = call(); p.* = …;`).
    fn_body_last: Ast.TokenIndex = 0,
    /// First token of the fn body (the opening `{`).  Set at
    /// construction; paired with `fn_body_last` for whole-body
    /// token scans (e.g. save-restore-via-defer detection).
    fn_body_first: Ast.TokenIndex = 0,
    fn_body_node: ?Ast.Node.Index = null,
    /// Name → LocalId for the current lexical or capture scope.
    /// Exiting scopes restore the enclosing declaration's binding.
    name_to_local: std.StringHashMapUnmanaged(LocalId) = .empty,
    /// LocalId → the TYPE its binding holds, when that type is a
    /// declaration this file can only reach THROUGH another file's
    /// scope and therefore has no name worth storing.  `&handle.document
    /// .tree` over a `Handle` declared two imports away is such a case:
    /// the name `DocumentStore.Handle` means nothing when asked from
    /// here, while the declaration behind it says everything about the
    /// field walk.  Only bindings whose initializer was a CALL whose
    /// receiver type this file could resolve are recorded, so the table
    /// stays as small as the questions that need it.
    bound_types: std.AutoHashMapUnmanaged(LocalId, file_cache.FileCache.ResolvedType) = .empty,
    /// Immutable interior pointers retain their exact addressed value path.
    pointer_value_sources: std.AutoHashMapUnmanaged(LocalId, ExprKind) = .empty,
    /// File-level `const NAME = @import("path.zig")` aliases, mapped to
    /// their import path.  Built on first use so a file whose calls are
    /// all instance calls pays nothing; keys and values are slices into
    /// `tree.source`, which outlives the builder.  An alias names a
    /// module namespace — a container, never a value — so a call
    /// through one has no receiver slot to skip.
    import_aliases: ?std.StringHashMapUnmanaged([]const u8) = null,
    /// Scope resolution and comptime static-constant evaluation: which
    /// declaration a reference names, and how many elements a written
    /// length says there are.
    ///
    /// Held BY VALUE because the resolver owns the one declaration
    /// index every scope question in this lowering reads, and an index
    /// reachable from two owners is an index that can be freed twice.
    /// Its local-table pointers are bound by the entry point right
    /// after this builder exists; see [comptime_fill.Resolver].
    fill: comptime_fill.Resolver,
    /// Credit for the COUNTER-GUARDED fill, armed by [lowerBlock] just
    /// before it lowers a `while` whose next sibling is the equality
    /// check that closes the counting argument, and consumed by that
    /// check's own [lowerIf].  It exists so the credit lands in a block
    /// reached only when the counter EQUALS the target's length, which
    /// is the whole point of the counting argument — a credit anywhere
    /// else would be a claim about a partially written target.
    counted_fill_credit: ?CountedFillCredit = null,
    checked_differences: std.AutoHashMapUnmanaged(LocalId, CheckedDifference) = .empty,
    immutable_locals: std.AutoHashMapUnmanaged(LocalId, void) = .empty,
    /// The guard every `if` that [establishGuardPairs] proved is one
    /// half of a re-tested condition belongs to, keyed by the `if` node,
    /// together with whether THIS `if` reads that value's negation.
    /// `lowerIf` emits a guard fact for exactly these, which is what
    /// keeps the fact off conditions nothing paired — an unpaired
    /// condition has no second reading to contradict, and a fact about
    /// it could only ever cost precision.
    ///
    /// The polarity is not decoration.  Two `if`s can read one value in
    /// OPPOSITE senses — `if (c) {…} if (!c) {…}` — and that is the
    /// mutual-exclusion shape this exists for: the second arm is
    /// unreachable exactly where the first one ran.  Without the flag
    /// both arms would record the same truth value and the second
    /// `if` would contradict itself instead of the first.
    guard_facts: std.AutoHashMapUnmanaged(Ast.Node.Index, GuardFact) = .empty,

    /// Next [GuardId] to mint.  Function-scoped like every other id
    /// this file mints: two `if`s in DIFFERENT functions are never
    /// compared, because each is lowered into its own CFG.
    next_guard: u32 = 0,
    /// Locals that are FILE-SCOPE bindings rather than storage in this
    /// function's frame — the `const … = undefined` globals
    /// [registerUndefFileConsts] registers.  They are seeded `.undef`
    /// like any other undefined read, but `&x` on one is an address
    /// into static memory that outlives every frame, so the
    /// address-of classification asks here before calling it a stack
    /// borrow.  Keyed by the LocalId, not the name, so a body-local
    /// shadow is a different id and keeps the frame's storage.
    file_scope_storage: std.AutoHashMapUnmanaged(LocalId, bool) = .empty,
    /// Unified declaration-ordered stack of `defer` / `errdefer`
    /// bodies, LIFO.  Replayed at every `return` (normal only) and
    /// at synthetic err-exit sinks (both kinds, interleaved by
    /// declaration order so that Zig's semantics — defers + errdefers
    /// fire in reverse declaration order — are preserved).
    ///
    /// Previously two separate lists (normal/err) caused err-exit
    /// flushing to fire ALL errdefers before ANY defers, which is
    /// wrong: an `errdefer free(p);` followed by a `defer use(p);`
    /// declared later would, on error, run free→use → spurious UAF
    /// inside the synthetic err_exit block.  Single list with kind
    /// tag preserves order.
    deferred: std.ArrayListUnmanaged(DeferEntry) = .empty,
    /// Loop context stack — pushed by lowerWhile/lowerFor before
    /// lowering the body, popped after.  `break` jumps to the
    /// innermost merge; `continue` jumps to the innermost header.
    /// Labels aren't modeled yet (always targets the innermost loop).
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .empty,
    /// Labeled-block stack — pushed by lowerLabeledBlock around the
    /// body; searched before loop_stack on labeled-break resolution.
    block_label_stack: std.ArrayListUnmanaged(BlockLabelCtx) = .empty,
    /// Stack of `errdefer` bodies, LIFO.  Replayed on error-exit paths
    /// only (try/catch — phase 9+).  At a plain `return X` Zig only fires
    /// these when X is an error value, but we can't always tell from
    /// AST, so for now we conservatively SKIP errdefers at returns; this
    /// trades one false-negative class (errdefer killing an arena before
    /// an error return uses it) for elimination of the converse false-
    /// positive class (errdefer kills polluting success returns).
    /// True iff the enclosing fn returns a borrowed-shape type.
    /// Threaded into `Stmt.ret.is_borrowed_return_type`.
    is_borrowed_return_type: bool = false,
    is_noreturn_fn: bool = false,
    /// Set when the enclosing fn carries `@returns owns_locals`.
    /// firstBorrowedLocal returns null when this is set, so the
    /// composite-borrow check stays silent for explicit
    /// ownership-transfer functions (the canonical init() pattern).
    suppress_composite_borrow: bool = false,
    /// Per-function counters for minting ArenaId / HeapId.  Done at
    /// lowering time so worklist re-visits of the same call site
    /// reuse the same id; otherwise loops would grow state.arenas
    /// and state.heaps unboundedly.
    next_arena: u32 = 0,
    next_heap: u32 = 0,
    /// Path strings the builder allocated (currently used for
    /// struct-literal unpacking, where `parent_prefix.field_name`
    /// is non-contiguous in source).  Transferred to Cfg at finalize
    /// and freed in Cfg.deinit.
    owned_paths: std.ArrayListUnmanaged([]u8) = .empty,
    /// Arrays shared by return and fallback statements until CFG publication.
    owned_stack_loans: std.ArrayListUnmanaged([]LocalId) = .empty,
    owned_field_layouts: std.ArrayListUnmanaged([]const []const u8) = .empty,
    diagnostic_fields_mode: bool = false,
    /// Pre-built table of byte offsets where each line starts (line_offsets[i]
    /// = byte offset of the first char on line i).  Built once per file in
    /// lowerFunctionFullWithZls; makes posOfToken / endPosOf O(log lines)
    /// instead of O(source length).
    line_offsets: []const u32 = &.{},
    /// True when Builder owns line_offsets and must free it.  False when
    /// the slice is borrowed from FileCache (which owns and frees it).
    owns_line_offsets: bool = false,
    const CheckedDifference = struct { upper: LocalId, start: LocalId, scale: u64 };

    /// Record that a bounded walk gave up.  First failure wins: a walk
    /// that exhausts keeps unwinding and may trip further limits, but
    /// the site where it first stopped is the one that explains the
    /// rest.  The recorded function name and position let the CLI say
    /// which function and which expression, instead of only that some
    /// limit was hit.
    fn noteBudgetFailure(
        self: *Builder,
        limit: budget_mod.Limit,
        limit_value: u32,
        reached: u32,
        node: Ast.Node.Index,
    ) void {
        if (self.budget_failure != null) return;
        const pos = self.posOf(node);
        self.budget_failure = .{
            .limit = limit,
            .limit_value = limit_value,
            .reached = reached,
            .byte = pos.byte,
            .line = pos.line,
            .column = pos.column,
            .function = self.fn_name,
        };
    }

    /// Record a type-resolution query that failed rather than merely
    /// coming back unresolved.  First failure wins, for the same
    /// reason `noteBudgetFailure` keeps the first.
    fn noteResolutionError(self: *Builder, err: anyerror) void {
        if (self.resolution_error != null) return;
        self.resolution_error = err;
    }

    /// Run a type-resolution query a classification depends on.  A
    /// successful `null` is the resolver's normal "nobody can tell" and
    /// passes through untouched, so the caller's declared/syntactic
    /// fallbacks still run and the classification stays conservative.
    ///
    /// A FAILED query is not that.  An allocation failure or a
    /// cancelled read leaves the question open, and answering `null`
    /// for it is how a swallowed fault surfaces as a confident verdict:
    /// a frame-charged `&local.field`, a missed ownership transfer, a
    /// free bound to the wrong argument, a call through a receiver
    /// whose type was never read.  The failure is recorded so
    /// `lowerFunctionFullWithZls` re-raises it instead of publishing a
    /// classification that leaned on a query that never answered.
    ///
    /// `T` is named at every call site: Zig does no inference for a
    /// type parameter, so a `comptime T: type` is a generic every
    /// caller spells out, and each query names the answer it wants.
    fn queryOrUnknown(self: *Builder, comptime T: type, query: anyerror!?T) ?T {
        const answer: ?T = query catch |err| err_blk: {
            self.noteResolutionError(err);
            break :err_blk null;
        };
        return answer;
    }

    /// Same rule as `queryOrUnknown` for `FileCache.fileModel`, which
    /// answers a pointer rather than an optional.  Null here means the
    /// file's declarations are unreadable, so the caller has to decline
    /// the declared-shape proof it wanted — a conservative answer, but
    /// still a failure, and recorded as one.
    fn modelOrNull(self: *Builder, cache: *file_cache.FileCache) ?*const model_mod.FileModel {
        const model: ?*const model_mod.FileModel = cache.fileModel() catch |err| err_blk: {
            self.noteResolutionError(err);
            break :err_blk null;
        };
        return model;
    }

    const BorrowIterator = struct {
        const Iterator = @import("type_engine").AstIterator;
        builder: *Builder,
        frames: [64]Iterator = undefined,
        depth: usize = 1,
        /// Fallback witnesses follow address values, never call arguments.
        frame_cells_only: bool = false,
        /// Nodes visited by this walk.  Bounded by `Builder.node_budget`,
        /// which is the whole-file node count already in the `u32` the
        /// budget diagnostic uses, so the counter carries that width
        /// and never needs converting to be reported.
        visited: u32 = 0,

        fn one(node: Ast.Node.Index) Iterator {
            return .{ .array = .{ node.toOptional(), .none, .none, .none, .none } };
        }

        fn init(builder: *Builder, expression: Ast.Node.Index) BorrowIterator {
            var result: BorrowIterator = .{ .builder = builder };
            result.frames[0] = one(expression);
            return result;
        }

        fn next(self: *BorrowIterator) ?ExprKind {
            const builder = self.builder;
            const tree = builder.tree;
            while (self.depth != 0) {
                const node = self.frames[self.depth - 1].next(tree) orelse {
                    self.depth -= 1;
                    continue;
                };
                if (self.visited == builder.node_budget) {
                    return self.exhausted(node, .borrow_walk_nodes, builder.node_budget);
                }
                self.visited += 1;
                if (self.children(node)) |child_nodes| {
                    if (self.depth == self.frames.len) return self.exhausted(node, .borrow_walk_depth, self.frames.len);
                    self.frames[self.depth] = child_nodes;
                    self.depth += 1;
                    continue;
                }
                switch (tree.nodeTag(node)) {
                    .address_of, .slice, .slice_open, .slice_sentinel => {
                        if (self.frame_cells_only) {
                            if (builder.directFrameCell(node)) |local| return .{ .stack_ref = local };
                            if (tree.fullSlice(node)) |slice| {
                                if (tree.nodeTag(slice.ast.sliced) == .identifier) {
                                    const token = tree.nodeMainToken(slice.ast.sliced);
                                    if (builder.frameLocalAt(token)) |source| {
                                        if (builder.immutableFrameInitializer(source, token)) |initializer| {
                                            if (self.depth == self.frames.len) return self.exhausted(node, .borrow_walk_depth, self.frames.len);
                                            self.frames[self.depth] = one(initializer);
                                            self.depth += 1;
                                        }
                                    }
                                }
                            }
                            continue;
                        }
                        const kind = builder.classifyExpr(node);
                        if (kind == .stack_ref) return kind;
                        if (kind == .copy_of) return kind;
                    },
                    .identifier => {
                        if (self.frame_cells_only) {
                            const token = tree.nodeMainToken(node);
                            const local = builder.frameLocalAt(token) orelse continue;
                            if (builder.immutableFrameInitializer(local, token)) |initializer| {
                                if (self.depth == self.frames.len) return self.exhausted(node, .borrow_walk_depth, self.frames.len);
                                self.frames[self.depth] = one(initializer);
                                self.depth += 1;
                            }
                            continue;
                        }
                        const local = builder.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(node))) orelse continue;
                        if (builder.locals.items[@intFromEnum(local)].init_hint != .other) continue;
                        return .{ .copy_of = local };
                    },
                    else => {},
                }
            }
            return null;
        }

        fn exhausted(
            self: *BorrowIterator,
            node: Ast.Node.Index,
            limit: budget_mod.Limit,
            limit_value: u32,
        ) ?ExprKind {
            self.builder.noteBudgetFailure(limit, limit_value, self.visited, node);
            self.depth = 0;
            return null;
        }

        fn children(self: *BorrowIterator, node: Ast.Node.Index) ?Iterator {
            const builder = self.builder;
            const tree = builder.tree;
            return switch (tree.nodeTag(node)) {
                .struct_init,
                .struct_init_comma,
                .struct_init_one,
                .struct_init_one_comma,
                .struct_init_dot,
                .struct_init_dot_comma,
                .struct_init_dot_two,
                .struct_init_dot_two_comma,
                .array_init,
                .array_init_comma,
                .array_init_one,
                .array_init_one_comma,
                .array_init_dot,
                .array_init_dot_comma,
                .array_init_dot_two,
                .array_init_dot_two_comma,
                .array_mult,
                .@"catch",
                .@"orelse",
                => Iterator.init(tree, node),
                .grouped_expression, .unwrap_optional => one(tree.nodeData(node).node_and_token[0]),
                .@"try" => one(tree.nodeData(node).node),
                .@"if", .if_simple => blk: {
                    const branch = tree.fullIf(node).?;
                    if (tree.nodeTag(branch.ast.cond_expr) == .identifier) {
                        const condition = tree.tokenSlice(tree.nodeMainToken(branch.ast.cond_expr));
                        if (std.mem.eql(u8, condition, "true")) break :blk one(branch.ast.then_expr);
                        if (std.mem.eql(u8, condition, "false")) {
                            break :blk one(branch.ast.else_expr.unwrap() orelse return null);
                        }
                    }
                    break :blk .{ .array = .{ branch.ast.then_expr.toOptional(), branch.ast.else_expr, .none, .none, .none } };
                },
                .@"switch", .switch_comma => blk: {
                    var cases = Iterator.init(tree, node);
                    const condition = cases.next(tree) orelse unreachable;
                    std.debug.assert(condition == tree.fullSwitch(node).?.ast.condition);
                    break :blk cases;
                },
                .switch_case, .switch_case_one, .switch_case_inline, .switch_case_inline_one => one(tree.fullSwitchCase(node).?.ast.target_expr),
                .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => one(builder.transparentCastSource(node) orelse return null),
                .block, .block_two, .block_semicolon, .block_two_semicolon => blk: {
                    const label = builder.blockLabelToken(node) orelse return null;
                    break :blk one(builder.singleLabeledBreakValue(node, label) orelse return null);
                },
                else => null,
            };
        }
    };

    /// One borrow [emitAdditionalEscapeChecks] has already emitted a
    /// `.composite_escape` for, so the de-dup set can skip it.
    ///
    /// The two members are the two SHAPES those statements come in,
    /// and they are different claims rather than two spellings of one.
    /// `stack_address` is the address of the local's OWN frame
    /// storage: `transferCompositeEscape` resolves it to a `.stack`
    /// origin whatever the local holds, because the frame is what is
    /// escaping.  Without it, the value is a COPY of what the local
    /// holds, and the same transfer resolves it through that origin
    /// instead — so a copied heap pointer and an address of a stack
    /// slot are not the same statement, and collapsing them would
    /// hide the second behind the first.
    ///
    /// `.copy_of` and `.composite_borrow` are ONE member, and that is
    /// a fact about the consumer rather than a guess: `cfg_transfer`'s
    /// `originOfInit` resolves both through the source local's
    /// recorded origin, so two statements differing only in which of
    /// those two names they carry would be checked identically and
    /// report identically.  `.composite_borrow` reaches here as the
    /// SEED only — from `classifyExpr` on the returned value — because
    /// [BorrowIterator.next] yields `.stack_ref` and `.copy_of` and
    /// nothing else; de-duplicating it against an iterator `.copy_of`
    /// for the same local is therefore exactly the merge that is safe.
    const BorrowKey = struct {
        local: LocalId,
        stack_address: bool,

        fn from(kind: ExprKind) BorrowKey {
            return switch (kind) {
                .stack_ref => |local| .{ .local = local, .stack_address = true },
                .copy_of, .composite_borrow => |local| .{ .local = local, .stack_address = false },
                else => unreachable,
            };
        }
    };

    fn tempDeinit(self: *Builder) void {
        if (self.address_cache) |*cache| cache.deinit();
        if (self.owns_line_offsets and self.line_offsets.len > 0) self.gpa.free(self.line_offsets);
        for (self.block_stmts.items) |*s| s.deinit(self.gpa);
        self.block_stmts.deinit(self.gpa);
        for (self.block_successors.items) |*s| s.deinit(self.gpa);
        self.block_successors.deinit(self.gpa);
        self.blocks.deinit(self.gpa);
        // Released before the two tables it was pointed at, so a
        // resolver deinit can never read a table that is already gone.
        self.fill.deinit();
        self.locals.deinit(self.gpa);
        self.integer_domains.deinit(self.gpa);
        self.name_to_local.deinit(self.gpa);
        self.bound_types.deinit(self.gpa);
        self.pointer_value_sources.deinit(self.gpa);
        self.checked_differences.deinit(self.gpa);
        self.immutable_locals.deinit(self.gpa);
        self.guard_facts.deinit(self.gpa);
        self.file_scope_storage.deinit(self.gpa);
        if (self.import_aliases) |*aliases| aliases.deinit(self.gpa);
        self.deferred.deinit(self.gpa);
        self.loop_stack.deinit(self.gpa);
        self.block_label_stack.deinit(self.gpa);
        for (self.owned_paths.items) |p| self.gpa.free(p);
        self.owned_paths.deinit(self.gpa);
        for (self.owned_stack_loans.items) |loans| self.gpa.free(loans);
        self.owned_stack_loans.deinit(self.gpa);
        for (self.owned_field_layouts.items) |fields| self.gpa.free(fields);
        self.owned_field_layouts.deinit(self.gpa);
    }

    fn newBlock(self: *Builder) !BlockId {
        const id: BlockId = @enumFromInt(self.blocks.items.len);
        try self.blocks.append(self.gpa, .{
            .id = id,
            .stmts = &.{},
            .successors = &.{},
        });
        try self.block_stmts.append(self.gpa, .empty);
        try self.block_successors.append(self.gpa, .empty);
        return id;
    }

    fn appendStmt(self: *Builder, block: BlockId, stmt: Stmt) !void {
        try self.block_stmts.items[@intFromEnum(block)].append(self.gpa, stmt);
    }

    fn booleanValue(self: *Builder, expression: Ast.Node.Index) ?cfg_types.BooleanValue {
        var node = expression;
        var inverted = false;
        for (0..max_boolean_unwind) |_| {
            switch (self.tree.nodeTag(node)) {
                .grouped_expression => node = self.tree.nodeData(node).node_and_token[0],
                .bool_not => {
                    inverted = !inverted;
                    node = self.tree.nodeData(node).node;
                },
                .identifier => {
                    const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
                    if (std.mem.eql(u8, name, "true")) return .{ .constant = !inverted };
                    if (std.mem.eql(u8, name, "false")) return .{ .constant = inverted };
                    const local = self.name_to_local.get(name) orelse return null;
                    return if (inverted) .{ .not_local = local } else .{ .local = local };
                },
                .equal_equal, .bang_equal => |tag| {
                    const pair = self.tree.nodeData(node).node_and_node;
                    var operand = pair[0];
                    var literal = pair[1];
                    if (self.booleanLiteral(literal) == null) {
                        operand = pair[1];
                        literal = pair[0];
                    }
                    const value = self.booleanLiteral(literal) orelse return null;
                    inverted = inverted != (if (tag == .equal_equal) !value else value);
                    node = operand;
                },
                else => return null,
            }
        }
        self.noteBudgetFailure(.boolean_unwind, max_boolean_unwind, max_boolean_unwind, expression);
        return null;
    }

    fn booleanLiteral(self: *const Builder, node: Ast.Node.Index) ?bool {
        if (self.tree.nodeTag(node) != .identifier) return null;
        const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
        if (std.mem.eql(u8, name, "true")) return true;
        if (std.mem.eql(u8, name, "false")) return false;
        return null;
    }

    fn assumeCondition(self: *Builder, block: BlockId, node: Ast.Node.Index, condition: ?cfg_types.BooleanValue, expected: bool) !void {
        if (self.classify_depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, self.classify_depth, node);
            return error.AnalysisBudgetExceeded;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        const tag = self.tree.nodeTag(node);
        if (tag == .grouped_expression) {
            return self.assumeCondition(block, self.tree.nodeData(node).node_and_token[0], condition, expected);
        }
        if (tag == .bool_not) {
            const operand = self.tree.nodeData(node).node;
            return self.assumeCondition(block, operand, self.booleanValue(operand), !expected);
        }
        // The call was evaluated before this result-arm assumption.
        try self.emitAddressOutputs(block, node, expected);
        // Both operands hold on a successful conjunction, and neither holds
        // on a failed disjunction. The other outcomes remain alternatives.
        if ((tag == .bool_and and expected) or (tag == .bool_or and !expected)) {
            const pair = self.tree.nodeData(node).node_and_node;
            if (conditionCannotAssign(self.tree, self.tree.firstToken(pair[1]), self.tree.lastToken(pair[1]))) {
                try self.assumeCondition(block, pair[0], self.booleanValue(pair[0]), expected);
            }
            try self.assumeCondition(block, pair[1], self.booleanValue(pair[1]), expected);
            return;
        }
        if (self.comparisonOf(node)) |comparison| {
            var premise = comparison;
            if (!expected) premise.op = switch (premise.op) {
                .eq => .ne,
                .ne => .eq,
                .lt => .ge,
                .le => .gt,
                .gt => .le,
                .ge => .lt,
            };
            try self.appendStmt(block, .{
                .kind = .{ .compare_assume = premise },
                .pos = self.posOf(node),
                .end_pos = self.endPosOf(node),
            });
        }
        const value = condition orelse return;
        try self.appendStmt(block, .{
            .kind = .{ .assume = if (expected) value else value.negate() },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    /// Emit only reads the condition evaluates. The right operand of and/or
    /// runs under the left operand's actual branch assumption.
    fn lowerConditionUses(self: *Builder, node: Ast.Node.Index, cur: *BlockId) LoweringError!void {
        try self.lowerConditionValue(node, cur, null);
    }

    fn lowerConditionValue(self: *Builder, node: Ast.Node.Index, cur: *BlockId, result_frame: ?ValueOutcomeFrame) LoweringError!void {
        if (self.classify_depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, self.classify_depth, node);
            return error.AnalysisBudgetExceeded;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        const tree = self.tree;
        switch (tree.nodeTag(node)) {
            .grouped_expression => try self.lowerConditionValue(tree.nodeData(node).node_and_token[0], cur, result_frame),
            .bool_not => {
                const operand = tree.nodeData(node).node;
                if (result_frame) |frame| {
                    if (frame.scalar_local) |local| {
                        const source = try self.newScalarValue(operand, cur.*);
                        try self.lowerConditionValue(operand, cur, .{ .scalar_local = source, .scalar_guard = frame.scalar_guard });
                        try self.emitBooleanCopy(cur.*, local, source, true, node);
                    } else try self.lowerConditionUses(operand, cur);
                } else try self.lowerConditionUses(operand, cur);
            },
            .bool_and, .bool_or => {
                const pair = tree.nodeData(node).node_and_node;
                const lhs_snapshot = if (result_frame != null and result_frame.?.scalar_local != null)
                    try self.newScalarValue(pair[0], cur.*)
                else
                    null;
                if (lhs_snapshot) |local| {
                    try self.lowerConditionValue(pair[0], cur, .{
                        .scalar_local = local,
                        .scalar_guard = result_frame.?.scalar_guard,
                    });
                } else try self.lowerConditionUses(pair[0], cur);
                const rhs = try self.newBlock();
                const skipped = try self.newBlock();
                const merge = try self.newBlock();
                try self.addEdge(cur.*, rhs);
                try self.addEdge(cur.*, skipped);
                const evaluate_rhs = tree.nodeTag(node) == .bool_and;
                const condition = if (lhs_snapshot) |local|
                    cfg_types.BooleanValue{ .local = local }
                else
                    self.booleanValue(pair[0]);
                try self.assumeCondition(rhs, pair[0], condition, evaluate_rhs);
                try self.assumeCondition(skipped, pair[0], condition, !evaluate_rhs);
                var rhs_cur = rhs;
                var rhs_frame = result_frame;
                if (rhs_frame) |*frame| frame.scalar_guard = lhs_snapshot;
                try self.lowerConditionValue(pair[1], &rhs_cur, rhs_frame);
                if (result_frame) |frame| if (frame.scalar_local) |local| {
                    var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
                    if (lhs_snapshot) |guard| inputs[0] = .{ .local = guard };
                    try self.appendStmt(skipped, .{
                        .kind = .{ .assign = .{
                            .target = local,
                            .rhs_kind = .{ .boolean = .{ .constant = !evaluate_rhs } },
                            .value_defined = true,
                            .value_inputs = inputs,
                        } },
                        .pos = self.posOf(node),
                        .end_pos = self.endPosOf(node),
                    });
                };
                try self.addEdge(rhs_cur, merge);
                try self.addEdge(skipped, merge);
                cur.* = merge;
            },
            else => {
                try self.emitUsesInExpr(node, cur.*, null);
                if (result_frame) |frame| if (frame.scalar_local) |local|
                    try self.emitScalarValue(cur.*, local, node, frame.scalar_guard);
            },
        }
    }

    fn integerValue(self: *Builder, node: Ast.Node.Index) ?u64 {
        return self.fill.comptimeIntTokens(.{ .first = self.tree.firstToken(node), .last = self.tree.lastToken(node) }, 0);
    }

    /// Only a resolved field's declared scalar type can supply this lower bound.
    fn fieldIsUnsigned(self: *Builder, parent: LocalId, name: []const u8) bool {
        const cache = self.cache orelse return false;
        const owner = self.bound_types.get(parent) orelse blk: {
            // Resolve the type written at this binding, not another local
            // or imported declaration that happens to share its leaf name.
            const span = self.paramTypeSpanOfLocal(parent) orelse
                if (self.fill.declaredTypeSpanOfLocal(parent)) |declaration|
                    declaration.type
                else
                    return false;
            const proto = self.fn_proto orelse return false;
            const body = self.fn_body_node orelse return false;
            const bindings = cache.localBindings(proto, body) catch |err| {
                self.noteResolutionError(err);
                return false;
            };
            var token = span.first;
            while (token <= span.last) : (token += 1) {
                if (self.tree.tokenTag(token) != .identifier) continue;
                if (bindings.findAt(self.tree.tokenSlice(token), token) != null) return false;
            }
            const type_name = self.locals.items[@intFromEnum(parent)].type_name orelse return false;
            break :blk cache.resolvedTypePathAcrossImports(type_name) orelse return false;
        };
        if (owner.model.tree != self.tree) return false;
        const field = owner.info.findField(name) orelse return false;
        if (field.type_first != field.type_last) return false;
        const tree = owner.model.tree;
        if (tree.tokenTag(field.type_first) != .identifier) return false;
        return unsignedTypeName(tree.tokenSlice(field.type_first));
    }

    /// A flat spelling is usable only when it names this lexical declaration.
    /// Capture bindings absent from LocalBindings cannot supply a typed term.
    fn indexLocalAt(self: *Builder, token: Ast.TokenIndex) ?LocalId {
        const name = self.tree.tokenSlice(token);
        const local = self.name_to_local.get(name) orelse return null;
        const proto = self.fn_proto orelse return null;
        const body = self.fn_body_node orelse return null;
        if (self.cache == null and self.address_cache == null) {
            self.address_cache = file_cache.FileCache.init(self.gpa, self.tree);
        }
        const cache = self.cache orelse &self.address_cache.?;
        if (cache.tree != self.tree) return null;
        const bindings = cache.localBindings(proto, body) catch |err| {
            self.noteResolutionError(err);
            return null;
        };
        const binding = bindings.findAt(name, token) orelse return null;
        const info = self.locals.items[@intFromEnum(local)];
        if (info.decl_pos.byte != self.tree.tokenStart(binding.name_token)) return null;
        if (info.is_control_local) return null;
        return local;
    }

    fn indexTerm(self: *Builder, node: Ast.Node.Index) cfg_types.IndexTerm {
        if (self.classify_depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, self.classify_depth, node);
            return .unknown;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        const tree = self.tree;
        if (tree.nodeTag(node) == .grouped_expression) return self.indexTerm(tree.nodeData(node).node_and_token[0]);
        if (tree.nodeTag(node) == .identifier) {
            const token = tree.nodeMainToken(node);
            if (self.name_to_local.contains(tree.tokenSlice(token))) {
                const local = self.indexLocalAt(token) orelse return .unknown;
                return .{ .local = .{ .local = local } };
            }
        }
        if (tree.nodeTag(node) == .field_access) {
            const pair = tree.nodeData(node).node_and_token;
            if (tree.nodeTag(pair[0]) == .identifier and std.mem.eql(u8, tree.tokenSlice(pair[1]), "len")) {
                if (self.indexLocalAt(tree.nodeMainToken(pair[0]))) |local| {
                    if (self.locals.items[@intFromEnum(local)].array_extent) |extent| return .{ .constant = extent };
                }
            }
            if (tree.nodeTag(pair[0]) == .identifier) {
                if (self.indexLocalAt(tree.nodeMainToken(pair[0]))) |parent| {
                    const is_unsigned = blk: {
                        if (self.zls) |zls| {
                            if (self.queryOrUnknown(zls_resolver_mod.TypeResolver.IntInfo, zls.intInfo(node))) |info|
                                break :blk !info.signed;
                        }
                        break :blk self.fieldIsUnsigned(parent, tree.tokenSlice(pair[1]));
                    };
                    return .{ .field = .{ .parent = parent, .name = tree.tokenSlice(pair[1]), .is_unsigned = is_unsigned } };
                }
            }
        }
        if (tree.nodeTag(node) == .add or tree.nodeTag(node) == .sub) {
            const pair = tree.nodeData(node).node_and_node;
            const left = self.indexTerm(pair[0]);
            if (left == .local and left.local.offset == 0 and self.integerValue(pair[1]) == 1) {
                return .{ .local = .{ .local = left.local.local, .offset = if (tree.nodeTag(node) == .add) 1 else -1 } };
            }
            if (left == .field and left.field.offset == 0 and self.integerValue(pair[1]) == 1) {
                var field = left.field;
                field.offset = if (tree.nodeTag(node) == .add) 1 else -1;
                return .{ .field = field };
            }
            return .unknown;
        }
        if (self.integerValue(node)) |value| return .{ .constant = value };
        return .unknown;
    }

    fn indexTermTokens(self: *Builder, first: Ast.TokenIndex, last: Ast.TokenIndex) cfg_types.IndexTerm {
        const tree = self.tree;
        if (first > last) return .unknown;
        if (tree.tokenTag(first) == .identifier) {
            if (self.name_to_local.contains(tree.tokenSlice(first))) {
                const local = self.indexLocalAt(first) orelse return .unknown;
                if (first == last) return .{ .local = .{ .local = local } };
                if (last == first + 2 and tree.tokenTag(first + 1) == .period and
                    std.mem.eql(u8, tree.tokenSlice(last), "len"))
                {
                    if (self.locals.items[@intFromEnum(local)].array_extent) |extent| return .{ .constant = extent };
                }
                if ((last == first + 2 or last == first + 4) and
                    tree.tokenTag(first + 1) == .period and tree.tokenTag(first + 2) == .identifier)
                {
                    const offset: i8 = if (last == first + 2) 0 else blk: {
                        if ((tree.tokenTag(first + 3) != .plus and tree.tokenTag(first + 3) != .minus) or
                            self.fill.literalValue(.{ .first = last, .last = last }) != 1) return .unknown;
                        break :blk if (tree.tokenTag(first + 3) == .plus) 1 else -1;
                    };
                    return .{ .field = .{
                        .parent = local,
                        .name = tree.tokenSlice(first + 2),
                        .offset = offset,
                        .is_unsigned = self.fieldIsUnsigned(local, tree.tokenSlice(first + 2)),
                    } };
                }
                if (last == first + 2 and (tree.tokenTag(first + 1) == .plus or tree.tokenTag(first + 1) == .minus) and
                    self.fill.literalValue(.{ .first = last, .last = last }) == 1)
                {
                    return .{ .local = .{ .local = local, .offset = if (tree.tokenTag(first + 1) == .plus) 1 else -1 } };
                }
                return .unknown;
            }
        }
        if (self.fill.comptimeIntTokens(.{ .first = first, .last = last }, 0)) |value| return .{ .constant = value };
        return .unknown;
    }

    /// Keep remainder bounds separate from exact-element index terms.
    fn moduloIndexTokens(
        self: *Builder,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) ?cfg_types.ModuloIndex {
        if (first > last or (last - first != 2 and last - first != 4)) return null;
        const tree = self.tree;
        // A fixed array length is one divisor; trailing arithmetic may bind
        // outside the remainder and must not change the selection certificate.
        if (last - first == 4 and
            (tree.tokenTag(first + 2) != .identifier or tree.tokenTag(first + 3) != .period or
                tree.tokenTag(last) != .identifier or !std.mem.eql(u8, tree.tokenSlice(last), "len")))
            return null;
        if (tree.tokenTag(first) != .identifier or tree.tokenTag(first + 1) != .percent)
            return null;
        const input = self.indexLocalAt(first) orelse return null;
        switch (self.integer_domains.items[@intFromEnum(input)].kind) {
            .unsigned, .unsigned_unbounded => {},
            else => return null,
        }
        const divisor = self.indexTermTokens(first + 2, last);
        const modulus = if (divisor == .constant)
            divisor.constant
        else
            self.fill.comptimeIntTokens(.{ .first = first + 2, .last = last }, 0) orelse return null;
        if (modulus == 0) return null;
        return .{ .input = input, .modulus = modulus };
    }

    fn scaledOutputIndexTokens(self: *Builder, first: Ast.TokenIndex, last: Ast.TokenIndex) ?abstract_state.ScaledElement {
        const tree = self.tree;
        if (last != first + 2 and last != first + 4) return null;
        if (tree.tokenTag(first + 1) != .asterisk) return null;
        const local_token: Ast.TokenIndex = if (tree.tokenTag(first) == .identifier and tree.tokenTag(first + 2) == .number_literal)
            first
        else if (tree.tokenTag(first) == .number_literal and tree.tokenTag(first + 2) == .identifier)
            first + 2
        else
            return null;
        const scale_token = if (local_token == first) first + 2 else first;
        const scale = self.fill.literalValue(.{ .first = scale_token, .last = scale_token }) orelse return null;
        if (scale == 0) return null;
        const index = self.indexLocalAt(local_token) orelse return null;
        if (!self.locals.items[@intFromEnum(index)].is_unsigned) return null;
        const offset = if (last == first + 4) blk: {
            if (tree.tokenTag(first + 3) != .plus) return null;
            break :blk self.fill.literalValue(.{ .first = last, .last = last }) orelse return null;
        } else 0;
        if (offset >= scale) return null;
        return .{ .index = index, .scale = scale, .offset = offset };
    }

    fn comparisonOf(self: *Builder, node: Ast.Node.Index) ?cfg_types.Comparison {
        if (self.classify_depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, self.classify_depth, node);
            return null;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        const op: @TypeOf(@as(cfg_types.Comparison, undefined).op) = switch (self.tree.nodeTag(node)) {
            .equal_equal => .eq,
            .bang_equal => .ne,
            .less_than => .lt,
            .less_or_equal => .le,
            .greater_than => .gt,
            .greater_or_equal => .ge,
            .grouped_expression => return self.comparisonOf(self.tree.nodeData(node).node_and_token[0]),
            .bool_not => {
                var comparison = self.comparisonOf(self.tree.nodeData(node).node) orelse return null;
                comparison.op = switch (comparison.op) {
                    .eq => .ne,
                    .ne => .eq,
                    .lt => .ge,
                    .le => .gt,
                    .gt => .le,
                    .ge => .lt,
                };
                return comparison;
            },
            else => return null,
        };
        const pair = self.tree.nodeData(node).node_and_node;
        const lhs = self.indexTerm(pair[0]);
        const rhs = self.indexTerm(pair[1]);
        if (lhs == .unknown or rhs == .unknown) return null;
        return .{ .lhs = lhs, .rhs = rhs, .op = op };
    }

    const IndexedTarget = struct { array: LocalId, index_node: Ast.Node.Index, field_array: ?[]const u8 = null };

    /// A store through a slice writes the bytes it points at. The descriptor
    /// is never initialized by it, but the write may still change the backing
    /// storage, so keep the pointer-write invalidations.
    /// `&s[i]`, `&s[i].f`, `&s[a..b]`: the address is of an element of the
    /// storage `s` designates, never of the header that designates it.
    fn addressesElementOf(self: *const Builder, address_node: Ast.Node.Index) bool {
        const tree = self.tree;
        if (tree.nodeTag(address_node) != .address_of) return false;
        var node = tree.nodeData(address_node).node;
        while (true) {
            switch (tree.nodeTag(node)) {
                .grouped_expression => node = tree.nodeData(node).node_and_token[0],
                .field_access => node = tree.nodeData(node).node_and_token[0],
                .array_access, .slice_open, .slice, .slice_sentinel => return true,
                else => return false,
            }
        }
    }

    fn appendSliceStoreEffect(self: *Builder, cur: BlockId, write: @TypeOf(@as(StmtKind, undefined).indexed_write), pos: SrcPos, end_pos: SrcPos) !void {
        if (!self.locals.items[@intFromEnum(write.array)].is_slice) return;
        try self.appendStmt(cur, .{
            .kind = .{ .pointer_write = .{
                .target = write.array,
                .initializes = false,
                .payload_only = true,
                .preserves_complete_array = write.defined,
                .preserve_inputs = write.selected_inputs,
                .value_has_undefined_origin = write.rhs_kind == .undef,
                .preserve_whole_payload = true,
            } },
            .pos = pos,
            .end_pos = end_pos,
        });
    }

    fn indexedTarget(self: *Builder, node: Ast.Node.Index) ?IndexedTarget {
        if (self.tree.nodeTag(node) != .array_access) return null;
        const pair = self.tree.nodeData(node).node_and_node;
        if (self.tree.nodeTag(pair[0]) == .identifier) {
            const array = self.name_to_local.get(self.tree.tokenSlice(self.tree.nodeMainToken(pair[0]))) orelse return null;
            const info = self.locals.items[@intFromEnum(array)];
            if (!info.is_array and !info.is_slice) return null;
            return .{ .array = array, .index_node = pair[1] };
        }
        const field = self.fieldLhsFor(pair[0]) orelse return null;
        if (!self.fieldHasFixedArrayType(field.parent, field.name)) return null;
        return .{ .array = field.parent, .index_node = pair[1], .field_array = field.name };
    }

    fn indexedMemberTarget(self: *Builder, node: Ast.Node.Index) ?IndexedTarget {
        var base = node;
        var depth: u32 = 0;
        while (self.tree.nodeTag(base) == .field_access) : (depth += 1) {
            if (depth == max_classify_depth) return null;
            base = self.tree.nodeData(base).node_and_token[0];
        }
        if (base == node) return null;
        const access = self.indexedTarget(base) orelse return null;
        if (access.field_array != null or self.locals.items[@intFromEnum(access.array)].is_slice) return null;
        return access;
    }

    /// A member store can retain an already-covered element, never create it.
    fn emitIndexedMemberWrite(self: *Builder, block: BlockId, lhs: Ast.Node.Index, rhs: Ast.Node.Index, access: IndexedTarget) !void {
        const index = self.indexTerm(access.index_node);
        const changing_index = index != .constant and try self.valueNeedsSnapshot(rhs);
        var write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
            .array = access.array,
            .index = if (changing_index) .unknown else index,
            .rhs_kind = self.classifyExpr(rhs),
            .name = if (changing_index) null else if (self.fieldLhsFor(lhs)) |field| field.name else null,
        };
        write.defined = self.selectedValueInputs(rhs, &write.selected_inputs, false);
        const previous: cfg_types.ValueInput = .{ .indexed = .{
            .array = access.array,
            .index = write.index,
            .modulo = if (changing_index) null else self.moduloIndexTokens(self.tree.firstToken(access.index_node), self.tree.lastToken(access.index_node)),
        } };
        var previous_inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
        previous_inputs[0] = previous;
        write.defined = mergeSelectedValueInputs(&write.selected_inputs, previous_inputs) and write.defined;
        try self.appendStmt(block, .{
            .kind = .{ .indexed_write = write },
            .pos = self.posOf(lhs),
            .end_pos = self.endPosOf(lhs),
        });
    }

    /// Builtin type operands are not runtime dependencies. Share this filter
    /// between the existing whole-local and selected-storage collectors.
    const RuntimeOperandFilter = struct {
        depth: u32 = 0,
        comptime_depth: ?u32 = null,
        type_depth: ?u32 = null,

        fn readsToken(self: *RuntimeOperandFilter, tree: *const Ast, token: Ast.TokenIndex) bool {
            switch (tree.tokenTag(token)) {
                .l_paren, .l_bracket, .l_brace => {
                    self.depth += 1;
                    if (self.comptime_depth == null and self.type_depth == null and
                        tree.tokenTag(token) == .l_paren and token > 0 and
                        tree.tokenTag(token - 1) == .builtin)
                    {
                        const name = tree.tokenSlice(token - 1);
                        if (isComptimeOnlyBuiltin(name) and
                            !std.mem.eql(u8, name, "@fieldParentPtr"))
                        {
                            self.comptime_depth = self.depth;
                        } else if (std.mem.eql(u8, name, "@as") or
                            std.mem.eql(u8, name, "@mulAdd"))
                        {
                            self.type_depth = self.depth;
                        }
                    }
                    return false;
                },
                .r_paren, .r_bracket, .r_brace => {
                    if (self.comptime_depth == self.depth) self.comptime_depth = null;
                    if (self.type_depth == self.depth) self.type_depth = null;
                    if (self.depth != 0) self.depth -= 1;
                    return false;
                },
                .comma => {
                    if (self.type_depth == self.depth and self.comptime_depth == null)
                        self.type_depth = null;
                    return false;
                },
                else => return self.comptime_depth == null and self.type_depth == null,
            }
        }
    };

    fn valueInputs(self: *Builder, node: Ast.Node.Index, inputs: *[8]?LocalId) bool {
        const tree = self.tree;
        const first = tree.firstToken(node);
        const last = tree.lastToken(node);
        var count: usize = 0;
        var token = first;
        var runtime: RuntimeOperandFilter = .{};
        while (token <= last) : (token += 1) {
            if (!runtime.readsToken(tree, token)) continue;
            if (tree.tokenTag(token) == .period_asterisk) return false;
            if (tree.tokenTag(token) == .builtin and !pureScalarBuiltin(tree.tokenSlice(token))) return false;
            if (tree.tokenTag(token) == .builtin and
                std.mem.eql(u8, tree.tokenSlice(token), "@field")) return false;
            if (tree.tokenTag(token) == .identifier and token < last and
                tree.tokenTag(token + 1) == .l_paren) return false;
            if (tree.tokenTag(token) == .identifier and std.mem.eql(u8, tree.tokenSlice(token), "undefined")) return false;
            if (tree.tokenTag(token) != .identifier or (token > first and tree.tokenTag(token - 1) == .period)) continue;
            const local = self.name_to_local.get(tree.tokenSlice(token)) orelse continue;
            if (token + 2 <= last and tree.tokenTag(token + 1) == .period and
                tree.tokenTag(token + 2) == .identifier)
            {
                if (self.locals.items[@intFromEnum(local)].is_pointer) return false;
                const field = tree.tokenSlice(token + 2);
                if (self.locals.items[@intFromEnum(local)].is_array and
                    (std.mem.eql(u8, field, "len") or std.mem.eql(u8, field, "ptr"))) continue;
                const method = token + 3 <= last and tree.tokenTag(token + 3) == .l_paren;
                // A whole projection has an ExprKind field origin. Arithmetic
                // over a field needs a dependency we do not encode here.
                if (!method and tree.nodeTag(node) != .field_access) return false;
                if (self.indexLocalAt(token) != local) return false;
                const path = self.fieldChainPath(token, last) orelse return false;
                if (std.mem.indexOf(u8, path, "@\"") != null) return false;
                var end = token + 2;
                while (end + 2 <= last and tree.tokenTag(end + 1) == .period and
                    tree.tokenTag(end + 2) == .identifier) end += 2;
                if (end < last and (tree.tokenTag(end + 1) == .l_bracket or
                    tree.tokenTag(end + 1) == .period or
                    tree.tokenTag(end + 1) == .period_asterisk)) return false;
                if (!self.scalarFieldStorage(local, path, node, false)) return false;
            }
            if (token < last and
                (tree.tokenTag(token + 1) == .l_bracket or
                    tree.tokenTag(token + 1) == .period_asterisk)) return false;
            if (self.locals.items[@intFromEnum(local)].is_array) return false;
            var present = false;
            for (inputs[0..count]) |entry| {
                if (entry.? == local) present = true;
            }
            if (present) continue;
            if (count == inputs.len) return false;
            inputs[count] = local;
            count += 1;
        }
        return true;
    }

    /// Literal selectors borrow source bytes unless decoding is necessary.
    /// Decoded names follow the same CFG-owned path lifetime as composed paths.
    fn fieldLiteralName(self: *Builder, token: Ast.TokenIndex, comptime scalar_path: bool) ?[]const u8 {
        return self.fieldLiteralNameInTree(self.tree, token, scalar_path);
    }

    fn fieldLiteralNameInTree(self: *Builder, tree: *const Ast, token: Ast.TokenIndex, comptime scalar_path: bool) ?[]const u8 {
        const raw = tree.tokenSlice(token);
        const literal = switch (tree.tokenTag(token)) {
            .string_literal => raw,
            .identifier => if (std.mem.startsWith(u8, raw, "@\"")) raw[1..] else return null,
            else => return null,
        };
        if (literal.len < 2) return null;
        const allocated = if (std.mem.indexOfScalar(u8, literal, '\\') != null)
            std.zig.string_literal.parseAlloc(self.gpa, literal) catch |err| {
                if (err == error.OutOfMemory) self.noteResolutionError(err);
                return null;
            }
        else
            null;
        const name: []const u8 = if (allocated) |bytes| bytes else literal[1 .. literal.len - 1];
        // Dotted/index delimiters inside one field cannot use this path
        // grammar. Keep legacy quoted keys, but grant no scalar certificate.
        if (std.mem.indexOfAny(u8, name, ".[]") != null) {
            if (allocated) |bytes| self.gpa.free(bytes);
            return if (scalar_path) null else raw;
        }
        if (allocated) |bytes| {
            self.owned_paths.append(self.gpa, bytes) catch |err| {
                self.gpa.free(bytes);
                self.noteResolutionError(err);
                return null;
            };
        }
        return name;
    }

    fn normalizedFieldComponent(self: *Builder, token: Ast.TokenIndex) ?[]const u8 {
        const raw = self.tree.tokenSlice(token);
        if (std.mem.startsWith(u8, raw, "@\"")) return self.fieldLiteralName(token, false);
        return raw;
    }

    fn normalizedFieldPath(self: *Builder, first: Ast.TokenIndex, last: Ast.TokenIndex) ?[]const u8 {
        const tree = self.tree;
        const begin = tree.tokenStart(first);
        const finish = tree.tokenStart(last) + tree.tokenSlice(last).len;
        const raw = tree.source[begin..finish];
        if (first == last) return self.normalizedFieldComponent(first);
        var path: std.ArrayListUnmanaged(u8) = .empty;
        defer path.deinit(self.gpa);
        var cursor: usize = begin;
        var token = first;
        while (token <= last) : (token += 1) {
            if (tree.tokenTag(token) != .identifier or
                !std.mem.startsWith(u8, tree.tokenSlice(token), "@\"")) continue;
            const component = self.normalizedFieldComponent(token) orelse return null;
            if (path.capacity == 0 and std.mem.eql(u8, component, tree.tokenSlice(token))) continue;
            if (path.capacity == 0) {
                path.ensureTotalCapacity(self.gpa, raw.len) catch |err| {
                    self.noteResolutionError(err);
                    return null;
                };
            }
            path.appendSliceAssumeCapacity(tree.source[cursor..tree.tokenStart(token)]);
            path.appendSliceAssumeCapacity(component);
            cursor = tree.tokenStart(token) + tree.tokenSlice(token).len;
        }
        if (path.capacity == 0) return raw;
        path.appendSliceAssumeCapacity(tree.source[cursor..finish]);
        // Own the allocation capacity; consumers borrow only initialized bytes.
        self.owned_paths.append(self.gpa, path.items.ptr[0..path.capacity]) catch |err| {
            self.noteResolutionError(err);
            return null;
        };
        const result = path.items;
        path = .empty;
        return result;
    }

    /// Language-reserved operators only. Initialized arguments do not prove
    /// memory loads, pointer/header conversions, or other builtin effects.
    fn pureScalarBuiltin(name: []const u8) bool {
        if (isComptimeOnlyBuiltin(name) and !std.mem.eql(u8, name, "@fieldParentPtr")) return true;
        const builtin = std.zig.BuiltinFn.list.get(name) orelse return false;
        return switch (builtin.tag) {
            .as,
            .bit_cast,
            .int_cast,
            .float_cast,
            .truncate,
            .int_from_float,
            .float_from_int,
            .int_from_bool,
            .int_from_enum,
            .enum_from_int,
            .int_from_error,
            .error_from_int,
            .error_cast,
            .byte_swap,
            .bit_reverse,
            .clz,
            .ctz,
            .pop_count,
            .div_exact,
            .div_floor,
            .div_trunc,
            .mod,
            .rem,
            .mul_add,
            .max,
            .min,
            .shl_exact,
            .shr_exact,
            .add_with_overflow,
            .sub_with_overflow,
            .mul_with_overflow,
            .shl_with_overflow,
            .sqrt,
            .sin,
            .cos,
            .tan,
            .exp,
            .exp2,
            .log,
            .log2,
            .log10,
            .abs,
            .floor,
            .ceil,
            .trunc,
            .round,
            => true,
            else => false,
        };
    }

    /// Reuse the declaration walk; this selector has no index or unwrap steps.
    fn scalarFieldStorage(self: *Builder, parent: LocalId, path: []const u8, node: Ast.Node.Index, primitive_leaf: bool) bool {
        if (self.locals.items[@intFromEnum(parent)].is_pointer) return false;
        if (self.locals.items[@intFromEnum(parent)].is_slice and std.mem.eql(u8, path, "len")) return true;
        if (self.locals.items[@intFromEnum(parent)].is_enum_field_capture and
            std.mem.eql(u8, path, "value")) return true;
        // LocalBindings already owns this cache in AST-only lowering.
        const saved_cache = self.cache;
        if (self.cache == null) self.cache = if (self.address_cache) |*cache| cache else return false;
        defer self.cache = saved_cache;
        if (self.modelOrNull(self.cache.?) == null) return false;
        var chain: AddrChain = .{ .steps = undefined, .count = 0, .truncated = false, .root = parent };
        chain.primitive_leaf = primitive_leaf;
        var fields = std.mem.splitScalar(u8, path, '.');
        while (fields.next()) |field| {
            if (field.len == 0 or chain.count == chain.steps.len) return false;
            chain.steps[chain.count] = .{ .node = node, .field = field, .kind = .field };
            chain.count += 1;
        }
        std.mem.reverse(AddrStep, chain.steps[0..chain.count]);
        if (self.declaredChainStorage(parent, chain) != .inside) return false;
        self.locals.items[@intFromEnum(parent)].tracks_array_payload = true;
        return true;
    }

    fn sliceHeaderSource(self: *Builder, node: Ast.Node.Index) ?LocalId {
        var shape = initShapeNode(self, node);
        if (self.tree.nodeTag(shape) == .@"orelse") {
            const operand, const fallback = self.tree.nodeData(shape).node_and_node;
            if (!fallbackDiverges(self, fallback, 0)) return null;
            shape = initShapeNode(self, operand);
        }
        const base = if (self.tree.fullSlice(shape)) |slice|
            initShapeNode(self, slice.ast.sliced)
        else
            shape;
        const value = if (self.tree.nodeTag(base) == .address_of)
            initShapeNode(self, self.tree.nodeData(base).node)
        else
            base;
        if (self.tree.nodeTag(value) != .identifier) return null;
        return self.indexLocalAt(self.tree.nodeMainToken(value));
    }

    fn isFullSlice(self: *Builder, node: Ast.Node.Index) bool {
        const slice = self.tree.fullSlice(initShapeNode(self, node)) orelse return false;
        return slice.ast.end == .none and slice.ast.sentinel == .none and
            self.tree.nodeTag(slice.ast.start) == .number_literal and self.integerValue(slice.ast.start) == 0;
    }

    /// Header formation reads bounds, not the fixed array's element payload.
    fn emitSliceHeader(self: *Builder, block: BlockId, local: LocalId, node: Ast.Node.Index, source: ?LocalId, snapshot: ?LocalId, pointer_snapshot: ?LocalId) LoweringError!void {
        if (!self.locals.items[@intFromEnum(local)].is_slice) return;
        if (self.arrayCallSource(node)) |projection| {
            if (projection == .field_copy_of) {
                const field = projection.field_copy_of;
                const pointer_path = try self.allocDottedPath(field.name, "ptr");
                const length_path = try self.allocDottedPath(field.name, "len");
                try self.emitDescriptorFields(block, local, null, .{ .field_copy_of = .{ .parent = field.parent, .name = pointer_path } }, .{ .field_copy_of = .{ .parent = field.parent, .name = length_path } }, .{ .field = .{ .parent = field.parent, .name = length_path, .is_unsigned = true } }, node);
                return;
            }
        }
        if (source == local and (self.isFullSlice(node) or
            self.tree.nodeTag(initShapeNode(self, node)) == .identifier)) return;
        var kind: ExprKind = .unknown;
        const descriptor_undefined = self.classifyExpr(node) == .undef;
        var inputs: [8]?LocalId = .{null} ** 8;
        var shape = initShapeNode(self, node);
        if (self.tree.nodeTag(shape) == .@"orelse") {
            const operand, const fallback = self.tree.nodeData(shape).node_and_node;
            if (fallbackDiverges(self, fallback, 0)) shape = initShapeNode(self, operand);
        }
        // A view of storage this frame does not own (`p.items`, `f()`,
        // `&.{...}`) has a defined pointer to initialized bytes. Its length
        // stays uncertified; only the literal `undefined` leaves the pointer open.
        const external = source == null and self.tree.fullVarDecl(shape) == null and
            !(self.tree.nodeTag(shape) == .identifier and
                std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(shape)), "undefined"));
        var defined = false;
        if (self.tree.nodeTag(shape) == .identifier) {
            if (source) |parent| if (self.locals.items[@intFromEnum(parent)].is_slice) {
                kind = .{ .field_copy_of = .{ .parent = parent, .name = "len" } };
                defined = true;
            };
        } else if (self.tree.fullSlice(shape)) |slice| {
            // Its exact lexical source was captured before registration/store.
            if (source) |parent| {
                const info = self.locals.items[@intFromEnum(parent)];
                if (info.is_array and !info.is_pointer) {
                    defined = true;
                } else if (info.is_slice) {
                    kind = if (snapshot) |value|
                        .{ .copy_of = value }
                    else
                        .{ .field_copy_of = .{ .parent = parent, .name = "len" } };
                    defined = true;
                }
            }
            const bounds = [_]?Ast.Node.Index{
                slice.ast.start, slice.ast.end.unwrap(), slice.ast.sentinel.unwrap(),
            };
            var count: usize = 0;
            for (bounds) |bound_optional| {
                const bound = bound_optional orelse continue;
                // Without selected-value snapshots, later effects cannot
                // repair an earlier evaluated operand.
                if (try self.isComputedValue(bound)) {
                    defined = false;
                    continue;
                }
                var call_buffer: [2]Ast.Node.Index = undefined;
                if (zls_resolver_mod.TypeResolver.CallOperands.full(self.tree, &call_buffer, bound) != null) {
                    defined = false;
                    continue;
                }
                var values: [8]?cfg_types.ValueInput = .{null} ** 8;
                defined = self.selectedValueInputs(bound, &values, true) and defined;
                for (values) |value_optional| {
                    const value = value_optional orelse continue;
                    if (value != .local) {
                        defined = false;
                        continue;
                    }
                    var duplicate = false;
                    for (inputs[0..count]) |input| {
                        if (input == value.local) duplicate = true;
                    }
                    if (duplicate) continue;
                    if (count == inputs.len) {
                        defined = false;
                        continue;
                    }
                    inputs[count] = value.local;
                    count += 1;
                }
            }
        }
        if (self.tree.nodeTag(shape) == .address_of) {
            if (source) |parent| {
                const info = self.locals.items[@intFromEnum(parent)];
                defined = info.is_array and !info.is_pointer;
            }
        }
        // A zero-start view retains the actual selected backing identity.
        // An interior offset is unsupported here, not a certificate for byte zero.
        var pointer_kind: ExprKind = if (external) .plain else .unknown;
        var interior_view = false;
        if (source) |parent| {
            const info = self.locals.items[@intFromEnum(parent)];
            const zero_start = if (self.tree.fullSlice(shape)) |slice|
                self.integerValue(slice.ast.start) == 0
            else
                self.tree.nodeTag(shape) == .identifier or self.tree.nodeTag(shape) == .address_of;
            if (!zero_start and info.is_slice) {
                // Elements of the view are elements of the source's storage.
                // The transfer withholds this for frame-local backing.
                interior_view = true;
                pointer_kind = if (pointer_snapshot) |value|
                    .{ .copy_of = value }
                else
                    .{ .field_copy_of = .{ .parent = parent, .name = "ptr" } };
            }
            if (!zero_start and info.is_array and !info.is_pointer) {
                interior_view = true;
                pointer_kind = .{ .stack_ref = parent };
            }
            if (zero_start) {
                if (info.is_array and !info.is_pointer) {
                    pointer_kind = .{ .stack_ref = parent };
                } else if (info.is_slice) {
                    pointer_kind = if (pointer_snapshot) |value|
                        .{ .copy_of = value }
                    else
                        .{ .field_copy_of = .{ .parent = parent, .name = "ptr" } };
                }
            }
        }
        if (descriptor_undefined) {
            kind = .undef;
            pointer_kind = .undef;
            defined = false;
        }
        try self.appendStmt(block, .{
            .kind = .{ .field_assign = .{
                .parent = local,
                .name = "ptr",
                .rhs_kind = pointer_kind,
                .defined = pointer_kind != .undef and pointer_kind != .unknown,
                .interior_view = interior_view,
            } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
        try self.appendStmt(block, .{
            .kind = .{ .field_assign = .{
                .parent = local,
                .name = "len",
                .rhs_kind = kind,
                .defined = defined,
                .inputs = inputs,
            } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
        var length: cfg_types.IndexTerm = .unknown;
        if (self.tree.fullSlice(shape)) |slice| {
            if (self.integerValue(slice.ast.start)) |start| {
                if (slice.ast.end.unwrap()) |end| {
                    if (self.integerValue(end)) |finish| {
                        if (finish >= start) length = .{ .constant = finish - start };
                    }
                } else if (source) |parent| {
                    const info = self.locals.items[@intFromEnum(parent)];
                    if (info.is_array and !info.is_pointer) {
                        if (info.array_extent) |extent| {
                            if (extent >= start) length = .{ .constant = extent - start };
                        }
                    } else if (info.is_slice and start == 0 and parent != local) {
                        length = .{ .field = .{ .parent = parent, .name = "len", .is_unsigned = true } };
                    }
                }
            }
        } else if (source) |parent| {
            const info = self.locals.items[@intFromEnum(parent)];
            if (info.is_slice and parent != local) {
                length = .{ .field = .{ .parent = parent, .name = "len", .is_unsigned = true } };
            } else if (info.is_array and !info.is_pointer and self.tree.nodeTag(shape) == .address_of) {
                if (info.array_extent) |extent| length = .{ .constant = extent };
            }
        }
        if (length != .unknown) try self.appendStmt(block, .{
            .kind = .{ .compare_assume = .{
                .lhs = .{ .field = .{ .parent = local, .name = "len", .is_unsigned = true } },
                .rhs = length,
                .op = .eq,
            } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    /// Descriptor bits and backing coverage are separate from resource origin.
    /// Only an authenticated copying primitive can mint a literal payload proof.
    fn emitDescriptorFields(self: *Builder, block: BlockId, parent: LocalId, prefix: ?[]const u8, pointer: ExprKind, length_kind: ExprKind, length: cfg_types.IndexTerm, node: Ast.Node.Index) LoweringError!void {
        const pointer_path = if (prefix) |path| try self.allocDottedPath(path, "ptr") else "ptr";
        const length_path = if (prefix) |path| try self.allocDottedPath(path, "len") else "len";
        try self.appendStmt(block, .{
            .kind = .{ .field_assign = .{ .parent = parent, .name = pointer_path, .rhs_kind = pointer, .defined = true } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
        try self.appendStmt(block, .{
            .kind = .{ .field_assign = .{ .parent = parent, .name = length_path, .rhs_kind = length_kind, .defined = true } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
        try self.appendStmt(block, .{
            .kind = .{ .compare_assume = .{
                .lhs = .{ .field = .{ .parent = parent, .name = length_path, .is_unsigned = true } },
                .rhs = length,
                .op = .eq,
            } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    fn emitCopiedLiteralDescriptor(self: *Builder, block: BlockId, parent: LocalId, prefix: ?[]const u8, node: Ast.Node.Index) LoweringError!void {
        const shape = initShapeNode(self, node);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = zls_resolver_mod.TypeResolver.CallOperands.full(self.tree, &buffer, shape) orelse return;
        const cache = self.cache orelse return;
        const frame = self.integerResolutionFrame();
        const actual = (try cache.actualCallSummaryAt(call.queryToken(self.tree, shape), frame)) orelse return;
        var remaining: u32 = 50000;
        const primitive = (try fresh_storage.allocatorPrimitive(cache, actual, .{
            .claim = .{ .first = self.tree.firstToken(shape), .last = self.tree.lastToken(shape) },
            .depth = 0,
            .remaining = &remaining,
            .frame = frame,
        })) orelse return;
        if (primitive.operation != .allocate or !primitive.copies_elements) return;
        var arguments: [2]Ast.Node.Index = undefined;
        const input = (try actual.callArgumentFor(cache, &arguments, 2)) orelse return;
        if (self.tree.nodeTag(input) != .string_literal) return;
        const raw = self.tree.tokenSlice(self.tree.nodeMainToken(input));
        var decoded: ?[]u8 = null;
        defer if (decoded) |bytes| self.gpa.free(bytes);
        const length = if (std.mem.indexOfScalar(u8, raw, '\\') != null) value: {
            decoded = std.zig.string_literal.parseAlloc(self.gpa, raw) catch |err| {
                if (err == error.OutOfMemory) return error.OutOfMemory;
                return;
            };
            break :value decoded.?.len;
        } else raw.len - 2;
        try self.emitDescriptorFields(block, parent, prefix, .plain, .plain, .{ .constant = length }, node);
    }

    /// Constructor payloads must be proved operand by operand. In particular,
    /// opaque calls and omitted undefined defaults cannot disappear into an
    /// aggregate's token scan.
    fn selectedReturnValueInputs(
        self: *Builder,
        node: Ast.Node.Index,
        inputs: *[8]?cfg_types.ValueInput,
        depth: u32,
    ) bool {
        if (depth >= max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, depth, node);
            return false;
        }
        const shape = initShapeNode(self, node);
        // `null` is an initialized optional value, with no selected payload.
        if (self.tree.nodeTag(shape) == .identifier and
            std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(shape)), "null")) return true;
        const value_type = self.bindingValueType(null, node, self.classifyExpr(node));
        if (value_type.pointer_header or value_type.slice_header) return false;
        var buffer: [2]Ast.Node.Index = undefined;
        var values: []const Ast.Node.Index = &.{};
        if (self.tree.fullArrayInit(&buffer, shape)) |literal| {
            values = literal.ast.elements;
        } else if (self.tree.fullStructInit(&buffer, shape)) |literal| {
            values = literal.ast.fields;
            const actual = value_type.container orelse context: {
                const frame = self.integerResolutionFrame() orelse return false;
                var expected = self.queryOrUnknown(
                    zls_resolver_mod.TypeResolver.ActualType,
                    frame.expectedTypeOfNode(node),
                ) orelse return false;
                // `slot = .{ ... }` into `?T` coerces the literal to `T`.
                var layers: u8 = 0;
                while (expected.data != .container) : (layers += 1) {
                    if (layers == 4) return false;
                    if (frame.resolver.typeTag(expected) != .optional) return false;
                    const child = frame.resolver.childType(expected) orelse return false;
                    expected = self.queryOrUnknown(
                        zls_resolver_mod.TypeResolver.ActualType,
                        frame.resolver.normalizedType(child),
                    ) orelse return false;
                }
                break :context expected.data.container;
            };
            const scope = actual.scope_handle;
            const owner_tree = &scope.handle.document.tree;
            var declaration_buffer: [2]Ast.Node.Index = undefined;
            const declaration = owner_tree.fullContainerDecl(&declaration_buffer, scope.toNode()) orelse return false;
            const is_union = owner_tree.tokenTag(declaration.ast.main_token) == .keyword_union;
            if (is_union and values.len != 1) return false;
            for (declaration.ast.members) |member| {
                const field = owner_tree.fullContainerField(member) orelse continue;
                if (field.ast.tuple_like) return false;
                const name = owner_tree.tokenSlice(field.ast.main_token);
                var supplied = false;
                for (values) |value| {
                    if (self.fieldInitName(value)) |provided| if (std.mem.eql(u8, name, provided)) {
                        supplied = true;
                        break;
                    };
                }
                if (supplied) continue;
                if (is_union) continue;
                const default = field.ast.value_expr.unwrap() orelse return false;
                var dependencies: [8]?cfg_types.ValueInput = .{null} ** 8;
                if (!self.selectedValueInputsAtDepth(owner_tree, default, &dependencies, false, depth + 1, true)) return false;
            }
        } else {
            if (value_type.runtime_scalar)
                return self.selectedValueInputsAtDepth(self.tree, node, inputs, true, depth + 1, false);
            if (self.tree.nodeTag(shape) == .identifier and
                self.indexLocalAt(self.tree.nodeMainToken(shape)) == null) return false;
            return self.selectedValueInputsAtDepth(self.tree, node, inputs, false, depth + 1, false);
        }
        for (values) |value| {
            var dependencies: [8]?cfg_types.ValueInput = .{null} ** 8;
            if (!self.selectedReturnValueInputs(value, &dependencies, depth + 1)) return false;
            for (dependencies) |dependency| {
                const selected = dependency orelse continue;
                var added = false;
                for (inputs) |*slot| if (slot.* == null) {
                    slot.* = selected;
                    added = true;
                    break;
                };
                if (!added) return false;
            }
        }
        return true;
    }

    /// Record the storage actually read, rather than rejecting every member
    /// or subscript in an explicit initializer. Unsupported chains fail closed.
    fn selectedValueInputs(
        self: *Builder,
        node: Ast.Node.Index,
        inputs: *[8]?cfg_types.ValueInput,
        comptime scalar_value: bool,
    ) bool {
        const defined = self.selectedValueInputsAtDepth(self.tree, node, inputs, scalar_value, 0, false);
        if (!defined) {
            self.selectedDiagnosticPointerInputs(node, inputs);
            self.selectedDiagnosticValueInputs(node, inputs, 0);
        }
        return defined;
    }

    fn selectedDiagnosticValueInputs(self: *Builder, node: Ast.Node.Index, inputs: *[8]?cfg_types.ValueInput, depth: u32) void {
        if (depth == max_classify_depth) return;
        const tree = self.tree;
        if (self.arrayCallSourceFor(node, true)) |source| {
            const input: cfg_types.ValueInput = switch (source) {
                .copy_of => |local| .{ .local = local },
                .field_copy_of => |field| .{ .field = .{ .parent = field.parent, .name = field.name } },
                else => return,
            };
            for (inputs) |*entry| {
                if (entry.* == null) {
                    entry.* = input;
                    break;
                }
            }
            return;
        }
        if (tree.nodeTag(node) == .array_access) {
            const access = self.indexedTarget(node) orelse return;
            const first = tree.firstToken(access.index_node);
            const last = tree.lastToken(access.index_node);
            const input: cfg_types.ValueInput = .{ .indexed = .{
                .array = access.array,
                .index = self.indexTerm(access.index_node),
                .modulo = self.moduloIndexTokens(first, last),
                .scaled = self.scaledOutputIndexTokens(first, last),
            } };
            for (inputs) |*entry| {
                if (entry.* == null) {
                    entry.* = input;
                    return;
                }
            }
            return;
        }
        switch (tree.nodeTag(node)) {
            .add, .add_wrap, .add_sat, .sub, .sub_wrap, .sub_sat,
            .mul, .mul_wrap, .mul_sat, .div, .mod, .shl, .shl_sat, .shr,
            .bit_and, .bit_or, .bit_xor,
            .equal_equal, .bang_equal, .less_than, .less_or_equal, .greater_than, .greater_or_equal,
            .assign_add, .assign_add_wrap, .assign_add_sat,
            .assign_sub, .assign_sub_wrap, .assign_sub_sat,
            .assign_mul, .assign_mul_wrap, .assign_mul_sat, .assign_div, .assign_mod,
            .assign_shl, .assign_shl_sat, .assign_shr,
            .assign_bit_and, .assign_bit_or, .assign_bit_xor,
            => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                self.selectedDiagnosticValueInputs(lhs, inputs, depth + 1);
                self.selectedDiagnosticValueInputs(rhs, inputs, depth + 1);
                return;
            },
            else => {},
        }
        if (tree.nodeTag(node) == .identifier) {
            const local = self.indexLocalAt(tree.nodeMainToken(node)) orelse return;
            for (inputs) |*entry| {
                if (entry.*) |value| {
                    if (value == .local and value.local == local) return;
                } else {
                    entry.* = .{ .local = local };
                    return;
                }
            }
            return;
        }
        if (tree.nodeTag(node) == .grouped_expression) {
            self.selectedDiagnosticValueInputs(tree.nodeData(node).node_and_token[0], inputs, depth + 1);
            return;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const arguments = tree.builtinCallParams(&buffer, node) orelse return;
        const name = tree.tokenSlice(tree.nodeMainToken(node));
        if (!pureScalarBuiltin(name) and !std.mem.eql(u8, name, "@reduce")) return;
        const builtin = std.zig.BuiltinFn.list.get(name) orelse return;
        for (arguments, 0..) |argument, ordinal| {
            if (ordinal == 0 and (builtin.tag == .as or builtin.tag == .mul_add or builtin.tag == .reduce)) continue;
            self.selectedDiagnosticValueInputs(argument, inputs, depth + 1);
        }
    }

    fn selectedDiagnosticPointerInputs(self: *Builder, node: Ast.Node.Index, inputs: *[8]?cfg_types.ValueInput) void {
        var runtime: RuntimeOperandFilter = .{};
        var token = self.tree.firstToken(node);
        const last = self.tree.lastToken(node);
        while (token <= last) : (token += 1) {
            if (!runtime.readsToken(self.tree, token) or self.tree.tokenTag(token) != .identifier) continue;
            const local = self.indexLocalAt(token) orelse continue;
            const source = self.pointer_value_sources.get(local) orelse blk: {
                if (!self.locals.items[@intFromEnum(local)].is_pointer) continue;
                break :blk @as(ExprKind, .{ .field_copy_of = .{ .parent = local, .name = "" } });
            };
            if (token + 1 > last) continue;
            const owner = if (source == .copy_of) source.copy_of else source.field_copy_of.parent;
            var input: cfg_types.ValueInput = undefined;
            if (self.tree.tokenTag(token + 1) == .period_asterisk) {
                input = if (source == .copy_of)
                    .{ .local = owner }
                else
                    .{ .field = .{ .parent = owner, .name = source.field_copy_of.name } };
            } else if (self.tree.tokenTag(token + 1) == .period) {
                const suffix = self.fieldChainPath(token, last) orelse continue;
                const path = self.allocDottedPath(
                    if (source == .field_copy_of) source.field_copy_of.name else null,
                    suffix,
                ) catch |err| {
                    self.noteResolutionError(err);
                    return;
                };
                input = .{ .field = .{ .parent = owner, .name = path } };
            } else continue;
            for (inputs) |*entry| {
                if (entry.* == null) {
                    entry.* = input;
                    break;
                }
            }
        }
    }

    fn selectedValueInputsAtDepth(
        self: *Builder,
        tree: *const Ast,
        node: Ast.Node.Index,
        inputs: *[8]?cfg_types.ValueInput,
        comptime scalar_value: bool,
        depth: u32,
        comptime owner_default: bool,
    ) bool {
        if (depth == max_classify_depth) {
            if (owner_default) return false;
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, depth, node);
            return false;
        }
        if (!scalar_value and !owner_default and tree == self.tree) {
            if (self.arrayCallSource(node)) |source| {
                inputs[0] = switch (source) {
                    .copy_of => |local| .{ .local = local },
                    .field_copy_of => |field| .{ .field = .{ .parent = field.parent, .name = field.name } },
                    else => return false,
                };
                return true;
            }
        }
        var call_buffer: [2]Ast.Node.Index = undefined;
        if (zls_resolver_mod.TypeResolver.CallOperands.full(tree, &call_buffer, node)) |call| {
            if (owner_default) return false;
            const cache = self.cache orelse return false;
            const frame = self.integerResolutionFrame();
            // Forwarding identifies the caller value, but still supplies no
            // definedness of its own.
            if (scalar_value) {
                if (self.queryOrUnknown(file_cache.FileCache.ArrayReturnSource, cache.arrayReturnSourceAt(
                    call.queryToken(tree, node),
                    frame,
                    &.{},
                ))) |source| {
                    if (source.projection_count == 0) {
                        for (call.ast.params) |argument| if (self.valueNeedsSnapshot(argument) catch return false) return false;
                        return self.selectedValueInputsAtDepth(tree, source.argument, inputs, true, depth + 1, owner_default);
                    }
                }
            }
            if (!(cache.callResultDefinedAt(call.queryToken(tree, node), frame) catch |err| {
                self.noteResolutionError(err);
                return false;
            })) return false;
            const canonical = self.queryOrUnknown(file_cache.FileCache.ActualCallSummary, cache.actualCallSummaryAt(
                call.queryToken(tree, node),
                frame,
            )) orelse return false;
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(canonical.callee.tree, &proto_buffer, canonical.callee.declaration) orelse return false;
            var parameters = proto.iterate(canonical.callee.tree);
            var ordinal: u32 = 0;
            while (parameters.next()) |parameter| : (ordinal += 1) {
                if (parameter.comptime_noalias) |modifier| {
                    if (canonical.callee.tree.tokenTag(modifier) == .keyword_comptime) continue;
                }
                var argument_buffer: [2]Ast.Node.Index = undefined;
                const argument = self.queryOrUnknown(Ast.Node.Index, canonical.callArgumentFor(cache, &argument_buffer, ordinal)) orelse return false;
                // Later operand effects cannot retroactively certify values.
                if ((self.valueNeedsSnapshot(argument) catch return false) and
                    !self.effectFreeValueLiteral(argument)) return false;
                const argument_type = self.bindingValueType(null, argument, self.classifyExpr(argument));
                var dependencies: [8]?cfg_types.ValueInput = .{null} ** 8;
                const defined = if (argument_type.runtime_scalar)
                    self.selectedValueInputsAtDepth(tree, argument, &dependencies, true, depth + 1, owner_default)
                else
                    self.selectedReturnValueInputs(argument, &dependencies, depth + 1);
                if (!defined) return false;
                for (dependencies) |dependency| {
                    const value = dependency orelse continue;
                    var added = false;
                    for (inputs) |*slot| if (slot.* == null) {
                        slot.* = value;
                        added = true;
                        break;
                    };
                    if (!added) return false;
                }
            }
            return true;
        }
        if (!owner_default and tree == self.tree and self.immutableLiteralPayload(node)) {
            return self.literalPayloadSelectorInputs(node, inputs, depth + 1);
        }
        // Explicit aggregate elements can mix immutable declarations and
        // tracked local values. Resolve each element in its own AST context.
        if (!scalar_value) {
            var literal_buffer: [2]Ast.Node.Index = undefined;
            if (tree.fullArrayInit(&literal_buffer, node)) |literal| {
                for (literal.ast.elements) |element| {
                    var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
                    if (!self.selectedValueInputsAtDepth(tree, element, &selected, false, depth + 1, owner_default)) return false;
                    if (!mergeSelectedValueInputs(inputs, selected)) return false;
                }
                return true;
            }
            if (!owner_default and tree == self.tree and
                tree.fullStructInit(&literal_buffer, node) != null)
                return self.selectedReturnValueInputs(node, inputs, depth + 1);
        }
        switch (tree.nodeTag(node)) {
            .@"try" => return self.selectedValueInputsAtDepth(
                tree,
                tree.nodeData(node).node,
                inputs,
                scalar_value,
                depth + 1,
                owner_default,
            ),
            .grouped_expression => return self.selectedValueInputsAtDepth(
                tree,
                tree.nodeData(node).node_and_token[0],
                inputs,
                scalar_value,
                depth + 1,
                owner_default,
            ),
            .negation, .bit_not, .bool_not => return self.selectedValueInputsAtDepth(
                tree,
                tree.nodeData(node).node,
                inputs,
                scalar_value,
                depth + 1,
                owner_default,
            ),
            .add,
            .add_wrap,
            .add_sat,
            .sub,
            .sub_wrap,
            .sub_sat,
            .mul,
            .mul_wrap,
            .mul_sat,
            .div,
            .mod,
            .shl,
            .shl_sat,
            .shr,
            .bit_and,
            .bit_or,
            .bit_xor,
            .bool_and,
            .bool_or,
            .equal_equal,
            .bang_equal,
            .less_than,
            .less_or_equal,
            .greater_than,
            .greater_or_equal,
            => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
                if (!self.selectedValueInputsAtDepth(tree, lhs, &selected, scalar_value, depth + 1, owner_default) or
                    !mergeSelectedValueInputs(inputs, selected)) return false;
                selected = .{null} ** 8;
                return self.selectedValueInputsAtDepth(tree, rhs, &selected, scalar_value, depth + 1, owner_default) and
                    mergeSelectedValueInputs(inputs, selected);
            },
            else => {},
        }
        if (tree.nodeTag(node) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "null")) return true;
        const last = tree.lastToken(node);
        var token = tree.firstToken(node);
        var count: usize = 0;
        var runtime: RuntimeOperandFilter = .{};
        var bit_cast_depth: ?u32 = null;
        while (token <= last) : (token += 1) {
            if (bit_cast_depth) |depth_at_cast| if (runtime.depth < depth_at_cast) {
                bit_cast_depth = null;
            };
            if (scalar_value and tree.tokenTag(token) == .l_brace and
                runtime.comptime_depth == null and runtime.type_depth == null) return false;
            if (!runtime.readsToken(tree, token)) continue;
            if (tree.tokenTag(token) == .builtin and
                !(scalar_value and std.mem.eql(u8, tree.tokenSlice(token), "@field")) and
                !pureScalarBuiltin(tree.tokenSlice(token))) return false;
            if (scalar_value and tree.tokenTag(token) == .builtin and
                std.mem.eql(u8, tree.tokenSlice(token), "@bitCast") and bit_cast_depth == null)
                bit_cast_depth = runtime.depth + 1;
            if (scalar_value and tree.tokenTag(token) == .builtin and
                std.mem.eql(u8, tree.tokenSlice(token), "@field"))
            {
                if (owner_default) return false;
                if (token + 4 > last or tree.tokenTag(token + 1) != .l_paren or
                    tree.tokenTag(token + 2) != .identifier) return false;
                const root = token + 2;
                const local = self.indexLocalAt(root) orelse return false;
                if (self.locals.items[@intFromEnum(local)].is_pointer) return false;
                var end = root;
                while (end + 2 <= last and tree.tokenTag(end + 1) == .period and
                    tree.tokenTag(end + 2) == .identifier) end += 2;
                if (end + 2 > last or tree.tokenTag(end + 1) != .comma) return false;
                const name = self.fieldLiteralName(end + 2, true) orelse return false;
                var close = end + 3;
                if (close <= last and tree.tokenTag(close) == .comma) close += 1;
                if (close > last or tree.tokenTag(close) != .r_paren) return false;
                if (close < last and (tree.tokenTag(close + 1) == .l_bracket or
                    tree.tokenTag(close + 1) == .period or
                    tree.tokenTag(close + 1) == .period_asterisk)) return false;
                const prefix: ?[]const u8 = if (end == root)
                    null
                else
                    self.fieldChainPath(root, end) orelse return false;
                if (prefix) |p| if (std.mem.indexOf(u8, p, "@\"") != null) return false;
                const path = self.allocDottedPath(
                    prefix,
                    name,
                ) catch |err| {
                    self.noteResolutionError(err);
                    return false;
                };
                if (!self.scalarFieldStorage(local, path, node, bit_cast_depth != null)) return false;
                if (count == inputs.len) return false;
                inputs[count] = .{ .field = .{ .parent = local, .name = path } };
                count += 1;
                token = close;
                continue;
            }
            // An initialized pointer does not prove that its payload was written.
            if (tree.tokenTag(token) == .period_asterisk) return false;
            if (tree.tokenTag(token) != .identifier) continue;
            if (std.mem.eql(u8, tree.tokenSlice(token), "undefined")) return false;
            // Arguments do not prove that an opaque scalar call returned data.
            if (scalar_value and token + 1 <= last and
                tree.tokenTag(token + 1) == .l_paren) return false;
            if (token > 0 and tree.tokenTag(token - 1) == .period) continue;
            // Container defaults never resolve against the caller's locals,
            // including a same-tree container nested inside this function.
            if (owner_default and !std.mem.eql(u8, tree.tokenSlice(token), "true") and
                !std.mem.eql(u8, tree.tokenSlice(token), "false")) return false;
            const local = self.name_to_local.get(tree.tokenSlice(token)) orelse {
                if (!std.mem.eql(u8, tree.tokenSlice(token), "true") and
                    !std.mem.eql(u8, tree.tokenSlice(token), "false")) return false;
                continue;
            };
            if (scalar_value and self.indexLocalAt(token) != local) return false;
            var input: cfg_types.ValueInput = .{ .local = local };
            if (token + 2 <= last and tree.tokenTag(token + 1) == .period and tree.tokenTag(token + 2) == .identifier) {
                if (scalar_value and self.locals.items[@intFromEnum(local)].is_pointer) return false;
                const path = self.fieldChainPath(token, last) orelse return false;
                if (scalar_value and std.mem.indexOf(u8, path, "@\"") != null) return false;
                var end = token + 2;
                while (end + 2 <= last and tree.tokenTag(end + 1) == .period and tree.tokenTag(end + 2) == .identifier) end += 2;
                if (end + 1 <= last and tree.tokenTag(end + 1) == .l_paren) return false;
                if (scalar_value and end < last and
                    (tree.tokenTag(end + 1) == .l_bracket or
                        tree.tokenTag(end + 1) == .period or
                        tree.tokenTag(end + 1) == .period_asterisk)) return false;
                if (self.locals.items[@intFromEnum(local)].is_array and std.mem.eql(u8, path, "len")) {
                    token = end;
                    continue;
                }
                if (scalar_value and !self.scalarFieldStorage(local, path, node, bit_cast_depth != null) and
                    !self.inlineScalarFieldChain(token, end)) return false;
                if (scalar_value) self.locals.items[@intFromEnum(local)].tracks_array_payload = true;
                input = .{ .field = .{ .parent = local, .name = path } };
                token = end;
            } else if (token + 1 <= last and tree.tokenTag(token + 1) == .l_bracket) {
                var end = token + 2;
                while (end <= last and tree.tokenTag(end) != .r_bracket) : (end += 1) {
                    if (tree.tokenTag(end) == .l_bracket or tree.tokenTag(end) == .colon or tree.tokenTag(end) == .ellipsis2) return false;
                }
                if (end > last) return false;
                if (scalar_value and end < last and
                    (tree.tokenTag(end + 1) == .period or
                        tree.tokenTag(end + 1) == .period_asterisk or
                        tree.tokenTag(end + 1) == .l_bracket)) return false;
                input = .{ .indexed = .{
                    .array = local,
                    .index = self.indexTermTokens(token + 2, end - 1),
                    .modulo = self.moduloIndexTokens(token + 2, end - 1),
                    .scaled = self.scaledOutputIndexTokens(token + 2, end - 1),
                } };
                if (input.indexed.index == .unknown and input.indexed.modulo == null) return false;
                token = end;
            } else if (scalar_value) {
                if (token + 1 <= last and tree.tokenTag(token + 1) == .period) return false;
                if (!self.locals.items[@intFromEnum(local)].tracks_scalar_value and
                    self.integer_domains.items[@intFromEnum(local)].kind == .unknown)
                {
                    // Capture registration has no initializer type node.
                    // Resolve this exact lexical value, never the enclosing
                    // scalar expression, and retain its live value dependency.
                    if (!self.inlineScalarFieldChain(token, token)) return false;
                    self.locals.items[@intFromEnum(local)].tracks_scalar_value = true;
                }
            }
            if (count == inputs.len) return false;
            inputs[count] = input;
            count += 1;
        }
        return true;
    }

    fn immutableLiteralPayload(self: *Builder, node: Ast.Node.Index) bool {
        const frame = self.integerResolutionFrame() orelse return false;
        return frame.immutableLiteralPayloadOfNode(node) catch |err| {
            self.noteResolutionError(err);
            return false;
        };
    }

    fn mergeSelectedValueInputs(inputs: *[8]?cfg_types.ValueInput, selected: [8]?cfg_types.ValueInput) bool {
        for (selected) |maybe_input| {
            const input = maybe_input orelse continue;
            for (inputs) |*slot| {
                if (slot.* == null) {
                    slot.* = input;
                    break;
                }
            } else return false;
        }
        return true;
    }

    /// A table's immutable bytes do not initialize its runtime selector.
    /// Keep all selector reads, including nested table selections, separate.
    fn literalPayloadSelectorInputs(
        self: *Builder,
        node: Ast.Node.Index,
        inputs: *[8]?cfg_types.ValueInput,
        depth: u32,
    ) bool {
        if (depth >= max_classify_depth) return false;
        switch (self.tree.nodeTag(node)) {
            .array_access => {
                const base, const index = self.tree.nodeData(node).node_and_node;
                if (!self.literalPayloadSelectorInputs(base, inputs, depth + 1)) return false;
                const frame = self.integerResolutionFrame() orelse return false;
                const resolver = frame.resolver;
                const ty = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(base)) orelse return false;
                switch (ty.data) {
                    .array => {},
                    .ip_index => switch (resolver.ctx.ip.indexToKey(ty.ipIndex() orelse return false)) {
                        .array_type => {},
                        else => return false,
                    },
                    else => return false,
                }
                // Every literal element is defined, so any defined selector reads
                // initialized bytes. Bounds are a separate runtime safety check.
                var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
                return self.selectedValueInputsAtDepth(self.tree, index, &selected, true, depth + 1, false) and
                    mergeSelectedValueInputs(inputs, selected);
            },
            .grouped_expression => return self.literalPayloadSelectorInputs(
                self.tree.nodeData(node).node_and_token[0],
                inputs,
                depth + 1,
            ),
            .negation, .bit_not, .bool_not => return self.literalPayloadSelectorInputs(
                self.tree.nodeData(node).node,
                inputs,
                depth + 1,
            ),
            .array_mult => {
                const pattern, const count = self.tree.nodeData(node).node_and_node;
                return self.literalPayloadSelectorInputs(pattern, inputs, depth + 1) and
                    self.literalPayloadSelectorInputs(count, inputs, depth + 1);
            },
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        if (self.tree.fullArrayInit(&buffer, node)) |literal| {
            for (literal.ast.elements) |element|
                if (!self.literalPayloadSelectorInputs(element, inputs, depth + 1)) return false;
        } else if (self.tree.builtinCallParams(&buffer, node)) |arguments| {
            const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
            if (std.mem.eql(u8, name, "@as") and arguments.len == 2)
                return self.literalPayloadSelectorInputs(arguments[1], inputs, depth + 1);
            if (std.mem.eql(u8, name, "@splat") and arguments.len == 1)
                return self.literalPayloadSelectorInputs(arguments[0], inputs, depth + 1);
        }
        // Authenticated aliases contain only literal selectors. Their owner
        // document cannot contribute caller-local value inputs.
        return true;
    }

    fn addEdge(self: *Builder, from: BlockId, to: BlockId) !void {
        try self.block_successors.items[@intFromEnum(from)].append(self.gpa, to);
    }

    /// Reserve both rows before publishing either, including synthetic locals.
    fn appendLocal(self: *Builder, info: LocalInfo) error{OutOfMemory}!LocalId {
        std.debug.assert(self.locals.items.len == self.integer_domains.items.len);
        const id: LocalId = @enumFromInt(try self.localsLen());
        try self.locals.ensureUnusedCapacity(self.gpa, 1);
        try self.integer_domains.ensureUnusedCapacity(self.gpa, 1);
        self.locals.appendAssumeCapacity(info);
        self.integer_domains.appendAssumeCapacity(.{});
        return id;
    }

    fn registerLocal(self: *Builder, name: []const u8, pos: SrcPos) !LocalId {
        return self.registerLocalWithType(name, pos, false, .other, null, null);
    }

    fn registerLocalWithPointerHint(
        self: *Builder,
        name: []const u8,
        pos: SrcPos,
        is_array: bool,
        init_hint: InitHint,
        bound_fn_name: ?[]const u8,
        type_name: ?[]const u8,
        is_pointer: bool,
    ) !LocalId {
        const id = try self.appendLocal(.{
            .name = name,
            .decl_pos = pos,
            .is_array = is_array,
            .init_hint = init_hint,
            .bound_fn_name = bound_fn_name,
            .type_name = type_name,
            .is_pointer = is_pointer,
        });
        try self.name_to_local.put(self.gpa, name, id);
        return id;
    }

    fn registerLocalFull(
        self: *Builder,
        name: []const u8,
        pos: SrcPos,
        is_array: bool,
        init_hint: InitHint,
        bound_fn_name: ?[]const u8,
    ) !LocalId {
        return self.registerLocalWithType(name, pos, is_array, init_hint, bound_fn_name, null);
    }

    fn registerLocalWithType(
        self: *Builder,
        name: []const u8,
        pos: SrcPos,
        is_array: bool,
        init_hint: InitHint,
        bound_fn_name: ?[]const u8,
        type_name: ?[]const u8,
    ) !LocalId {
        const id = try self.appendLocal(.{
            .name = name,
            .decl_pos = pos,
            .is_array = is_array,
            .init_hint = init_hint,
            .bound_fn_name = bound_fn_name,
            .type_name = type_name,
        });
        try self.name_to_local.put(self.gpa, name, id);
        return id;
    }

    /// A fixed array reserves stack storage even when its length is named.
    /// Slice and many/C-pointer spellings do not reserve that storage.
    fn typeIsStackArray(self: *Builder, type_node: Ast.Node.Index) bool {
        const tree = self.tree;
        const first = tree.firstToken(type_node);
        const tags = tree.tokens.items(.tag);
        if (tags[first] != .l_bracket) return false;
        if (first + 1 >= tree.tokens.len) return false;
        return tags[first + 1] != .r_bracket and tags[first + 1] != .asterisk and tags[first + 1] != .colon;
    }

    fn inferredUnsignedCall(self: *Builder, initializer: Ast.Node.Index) bool {
        const tree = self.tree;
        const peel = initPeelNode(self, initializer, .optional_payload);
        var node = initializer;
        var accepted_optional = false;
        while (node != peel.node) {
            switch (tree.nodeTag(node)) {
                .grouped_expression => node = tree.nodeData(node).node_and_token[0],
                .unwrap_optional => {
                    accepted_optional = true;
                    node = tree.nodeData(node).node_and_token[0];
                },
                .@"try" => node = tree.nodeData(node).node,
                .@"catch" => node = tree.nodeData(node).node_and_node[0],
                .@"orelse" => {
                    accepted_optional = true;
                    node = tree.nodeData(node).node_and_node[0];
                },
                else => return false,
            }
        }
        switch (tree.nodeTag(peel.node)) {
            .call, .call_one, .call_comma, .call_one_comma => {},
            else => return false,
        }
        const declaration = self.calleeDeclOfCall(peel.node) orelse return false;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = declaration.tree.fullFnProto(&buffer, declaration.fn_decl) orelse return false;
        const result = proto.ast.return_type.unwrap() orelse return false;
        var first = declaration.tree.firstToken(result);
        const last = declaration.tree.lastToken(result);
        if (errorUnionPayloadFirst(declaration.tree.tokens.items(.tag), first, last)) |payload| {
            if (!peel.accepted_error) return false;
            first = payload;
        }
        if (first < last and declaration.tree.tokenTag(first) == .question_mark) {
            if (!accepted_optional) return false;
            first += 1;
        }
        return first == last and declaration.tree.tokenTag(first) == .identifier and
            unsignedTypeName(declaration.tree.tokenSlice(first));
    }

    fn checkedDifference(self: *Builder, initializer: Ast.Node.Index) ?CheckedDifference {
        const shape = bounded_prefix.scaledDifference(self.tree, initializer) orelse return null;
        const upper = self.name_to_local.get(self.tree.tokenSlice(shape.upper_token)) orelse return null;
        const start = self.name_to_local.get(self.tree.tokenSlice(shape.start_token)) orelse return null;
        const upper_info = self.locals.items[@intFromEnum(upper)];
        const start_info = self.locals.items[@intFromEnum(start)];
        if (!upper_info.is_unsigned or !start_info.is_unsigned or
            upper_info.address_taken or start_info.address_taken or !self.immutable_locals.contains(start)) return null;
        return .{ .upper = upper, .start = start, .scale = shape.scale };
    }

    fn emitScaledIndex(self: *Builder, block: BlockId, index: LocalId, difference: CheckedDifference, declaration: Ast.Node.Index) !void {
        const info = self.locals.items[@intFromEnum(index)];
        if (!self.immutable_locals.contains(index) or !info.is_unsigned or info.address_taken) return;
        var candidates = self.checked_differences.iterator();
        while (candidates.next()) |entry| {
            const count = entry.key_ptr.*;
            const bound = entry.value_ptr.*;
            if (bound.start != difference.start or bound.scale != difference.scale or
                !self.immutable_locals.contains(bound.upper) or !self.immutable_locals.contains(count)) continue;
            if (self.locals.items[@intFromEnum(count)].address_taken or
                self.locals.items[@intFromEnum(bound.upper)].address_taken or
                self.locals.items[@intFromEnum(bound.start)].address_taken or
                self.locals.items[@intFromEnum(difference.upper)].address_taken) continue;
            try self.appendStmt(block, .{
                .kind = .{ .scaled_index = .{
                    .index = index,
                    .count = count,
                    .cursor = difference.upper,
                    .upper = bound.upper,
                    .start = bound.start,
                    .scale = bound.scale,
                } },
                .pos = self.posOf(declaration),
                .end_pos = self.endPosOf(declaration),
            });
        }
    }

    fn emitBoundedRangePrefix(self: *Builder, natural_exit: BlockId, loop: Ast.full.For) !void {
        const shape = bounded_prefix.rangeFill(self.tree, loop) orelse return;
        const array = self.name_to_local.get(self.tree.tokenSlice(shape.array_token)) orelse return;
        const count = self.name_to_local.get(self.tree.tokenSlice(shape.count_token)) orelse return;
        const capture = self.name_to_local.get(self.tree.tokenSlice(shape.capture_token)) orelse return;
        if (array == count or array == capture or count == capture) return;
        const array_info = self.locals.items[@intFromEnum(array)];
        const count_info = self.locals.items[@intFromEnum(count)];
        if (array_info.array_extent == null or array_info.address_taken or
            !count_info.is_unsigned or count_info.address_taken or !self.immutable_locals.contains(count)) return;
        const declaration = self.fill.declaredTypeSpanOfLocal(array) orelse return;
        if (declaration.is_const or !declaration.init_is_undefined or declaration.name_tok >= loop.ast.for_token) return;
        if (!self.rhsIsDefined(shape.rhs)) return;
        var inputs: [8]?LocalId = .{null} ** 8;
        if (!self.valueInputs(shape.rhs, &inputs)) {
            var call_buffer: [2]Ast.Node.Index = undefined;
            if (zls_resolver_mod.TypeResolver.CallOperands.full(self.tree, &call_buffer, shape.rhs) == null) return;
            var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
            if (!self.selectedValueInputs(shape.rhs, &selected, false)) return;
            inputs = .{null} ** 8;
            for (selected, 0..) |dependency, index| {
                const value = dependency orelse continue;
                if (value != .local) return;
                inputs[index] = value.local;
            }
        }
        try self.appendStmt(natural_exit, .{
            .kind = .{ .array_prefix = .{ .array = array, .count = count, .inputs = inputs } },
            .pos = self.posOfToken(loop.ast.for_token),
            .end_pos = self.endPosOf(loop.ast.then_expr),
        });
    }

    fn unsignedType(tree: *const Ast, node: Ast.Node.Index) bool {
        if (tree.nodeTag(node) != .identifier) return false;
        return unsignedTypeName(tree.tokenSlice(tree.nodeMainToken(node)));
    }

    fn unsignedTypeName(name: []const u8) bool {
        if (std.mem.eql(u8, name, "usize")) return true;
        if (name.len < 2 or name[0] != 'u') return false;
        _ = std.fmt.parseInt(u16, name[1..], 10) catch return false;
        return true;
    }

    fn integerDomain(info: zls_resolver_mod.TypeResolver.IntInfo) abstract_state.IntegerDomain {
        if (info.bits > 64) return if (info.signed)
            .{ .kind = .signed_unbounded }
        else
            .{ .kind = .unsigned_unbounded };
        return .{ .kind = if (info.signed) .signed else .unsigned, .bits = @intCast(info.bits) };
    }

    /// Only reserved integer syntax is a type proof without a semantic provider.
    fn primitiveIntegerDomain(tree: *const Ast, node: Ast.Node.Index) ?abstract_state.IntegerDomain {
        if (tree.nodeTag(node) != .identifier) return null;
        const name = tree.tokenSlice(tree.nodeMainToken(node));
        if (std.mem.eql(u8, name, "usize")) return .{ .kind = .unsigned_unbounded };
        if (std.mem.eql(u8, name, "isize")) return .{ .kind = .signed_unbounded };
        if (name.len < 2 or (name[0] != 'u' and name[0] != 'i')) return null;
        for (name[1..]) |character| {
            if (character < '0' or character > '9') return null;
        }
        const bits = std.fmt.parseInt(u16, name[1..], 10) catch return null;
        return integerDomain(.{ .signed = name[0] == 'i', .bits = bits });
    }

    const BindingValueType = struct {
        domain: abstract_state.IntegerDomain = .{},
        runtime_scalar: bool = false,
        pointer_header: bool = false,
        slice_header: bool = false,
        aggregate_value: bool = false,
        container: ?zls_resolver_mod.TypeResolver.ActualType.Data.Container = null,
    };

    /// Inferred copies have the source type only for a bare value reference.
    fn copiedValueType(
        self: *Builder,
        initializer: ?Ast.Node.Index,
        init_kind: ExprKind,
    ) ?BindingValueType {
        if (init_kind == .field_copy_of and
            std.mem.eql(u8, init_kind.field_copy_of.name, "len"))
        {
            const info = self.locals.items[@intFromEnum(init_kind.field_copy_of.parent)];
            if (!info.is_pointer and (info.is_slice or info.is_array))
                return .{ .domain = .{ .kind = .unsigned_unbounded }, .runtime_scalar = true };
        }
        if (init_kind != .copy_of) return null;
        var node = initializer orelse return null;
        for (0..max_classify_depth) |_| {
            if (self.tree.nodeTag(node) != .grouped_expression) {
                if (self.tree.nodeTag(node) != .identifier) return null;
                if (self.indexLocalAt(self.tree.nodeMainToken(node)) != init_kind.copy_of) return null;
                const source = @intFromEnum(init_kind.copy_of);
                return .{
                    .domain = self.integer_domains.items[source],
                    .runtime_scalar = self.locals.items[source].tracks_scalar_value,
                    .aggregate_value = self.locals.items[source].tracks_array_payload,
                    .pointer_header = self.locals.items[source].is_pointer,
                    .slice_header = self.locals.items[source].is_slice,
                };
            }
            node = self.tree.nodeData(node).node_and_token[0];
        }
        return null;
    }

    fn integerResolutionFrame(self: *Builder) ?zls_resolver_mod.TypeResolver.ResolutionFrame {
        if (self.cache) |cache| {
            if (cache.tree == self.tree) {
                if (cache.cleanup_frame) |frame| {
                    if (&frame.handle.document.tree == self.tree) return frame;
                }
            }
        }
        const resolver = self.zls orelse
            (if (self.cache) |cache| cache.zls else null) orelse return null;
        if (&resolver.handle.document.tree != self.tree) return null;
        return resolver.resolutionFrame();
    }

    /// A declaration's destination type outranks its initializer's type.
    /// Numeric values and operators never supply permanent type bounds here.
    fn bindingValueType(
        self: *Builder,
        type_node: ?Ast.Node.Index,
        initializer: ?Ast.Node.Index,
        init_kind: ExprKind,
    ) BindingValueType {
        const frame = self.integerResolutionFrame();
        if (type_node) |declared| {
            if (self.tree.fullPtrType(declared)) |pointer| {
                if (pointer.size == .slice) return .{ .slice_header = true };
            }
            const primitive = primitiveIntegerDomain(self.tree, declared);
            if (self.tree.nodeTag(declared) == .identifier) {
                const name = self.tree.tokenSlice(self.tree.nodeMainToken(declared));
                if (primitive) |domain| {
                    if (!std.mem.eql(u8, name, "usize") and
                        !std.mem.eql(u8, name, "isize"))
                        return .{ .domain = domain, .runtime_scalar = true };
                } else if (std.mem.eql(u8, name, "bool") or std.mem.eql(u8, name, "anyerror") or
                    std.mem.eql(u8, name, "f16") or std.mem.eql(u8, name, "f32") or
                    std.mem.eql(u8, name, "f64") or std.mem.eql(u8, name, "f80") or
                    std.mem.eql(u8, name, "f128"))
                {
                    return .{ .runtime_scalar = true };
                }
            }
            if (frame) |actual| return self.resolvedBindingValueType(actual, declared, true);
            return .{ .domain = primitive orelse .{}, .runtime_scalar = primitive != null };
        }
        if (self.copiedValueType(initializer, init_kind)) |source| return source;
        const init = initializer orelse return .{};
        if (self.booleanLiteral(init) != null or self.tree.nodeTag(init) == .bool_and or
            self.tree.nodeTag(init) == .bool_or) return .{ .runtime_scalar = true };
        // Negation also accepts boolean vectors. Only an intrinsic constant
        // result supplies the scalar identity without an actual type provider.
        if (self.tree.nodeTag(init) == .bool_not) {
            if (self.booleanValue(init)) |value| {
                if (value == .constant) return .{ .runtime_scalar = true };
            }
        }
        const actual = frame orelse return .{};
        return self.resolvedBindingValueType(actual, init, false);
    }

    fn resolvedBindingValueType(
        self: *Builder,
        frame: zls_resolver_mod.TypeResolver.ResolutionFrame,
        node: Ast.Node.Index,
        declared_type: bool,
    ) BindingValueType {
        const value = self.queryOrUnknown(
            zls_resolver_mod.TypeResolver.ActualType,
            frame.resolveValueOfNode(node),
        ) orelse return .{};
        if (value.is_type_val != declared_type) return .{};
        const ty = self.queryOrUnknown(
            zls_resolver_mod.TypeResolver.ActualType,
            frame.resolver.normalizedType(value),
        ) orelse return .{};
        const tag = frame.resolver.typeTag(ty) orelse return .{};
        switch (tag) {
            .int, .comptime_int => {
                const info = self.queryOrUnknown(
                    zls_resolver_mod.TypeResolver.IntInfo,
                    frame.intInfo(node),
                ) orelse return .{ .runtime_scalar = true };
                return .{ .domain = integerDomain(info), .runtime_scalar = true };
            },
            .float, .comptime_float, .bool, .@"enum", .error_set => return .{ .runtime_scalar = true },
            .pointer => return .{
                .pointer_header = if (frame.resolver.pointerSize(ty)) |size|
                    switch (size) {
                        .one, .many, .c => true,
                        .slice => false,
                    }
                else
                    false,
                .slice_header = if (frame.resolver.pointerSize(ty)) |size| size == .slice else false,
            },
            // An optional slice carries the same descriptor payload on its
            // non-null arm. Preserve its source identity when an `orelse`
            // binding selects that payload; type shape grants no backing bytes.
            .optional => return blk: {
                const payload = frame.resolver.childType(ty) orelse break :blk .{};
                if (frame.resolver.typeTag(payload) != .pointer) break :blk .{};
                const size = frame.resolver.pointerSize(payload) orelse break :blk .{};
                break :blk .{ .slice_header = size == .slice };
            },
            else => return .{
                .container = if (ty.data == .container) ty.data.container else null,
            },
        }
    }

    /// True iff `type_node` begins with `*` (possibly preceded by
    /// `?` or `const`) — the shape of a pointer.  Used to gate the
    /// `&local.field` → `.stack_ref(local)` extension so we don't
    /// FP on `&self.field` where `self` is a pointer parameter.
    fn typeIsPointer(self: *Builder, type_node: Ast.Node.Index) bool {
        const tree = self.tree;
        const first = tree.firstToken(type_node);
        const last = tree.lastToken(type_node);
        const tags = tree.tokens.items(.tag);
        var t: Ast.TokenIndex = first;
        while (t <= last) : (t += 1) {
            switch (tags[t]) {
                .question_mark, .keyword_const => continue,
                .asterisk => return true,
                else => return false,
            }
        }
        return false;
    }

    /// Keep the complete declaration path; resolve local names in lexical scope.
    fn extractTypeName(self: *Builder, type_node: Ast.Node.Index, self_type: ?[]const u8) ?[]const u8 {
        const tree = self.tree;
        const first = tree.firstToken(type_node);
        const last = tree.lastToken(type_node);
        const name = tokens.typeNameFromTokens(tree, first, last) orelse {
            if (last >= first + 2 and tree.tokenTag(last - 2) == .builtin and
                std.mem.eql(u8, tree.tokenSlice(last - 2), "@This")) return self_type;
            return null;
        };
        if (self_type) |enclosing| {
            if (std.mem.eql(u8, name, "Self")) return enclosing;
            if (self.cache) |cache| {
                const model = self.modelOrNull(cache) orelse return null;
                if (model.findType(enclosing)) |owner| {
                    if (model.resolveTypeNameInScope(name, owner)) |resolved| return resolved.qualified_name;
                }
            }
        }
        return name;
    }

    /// Register `|x|` / `|x, y|` / `|*x, idx|` capture identifiers
    /// starting at `payload_token` (which points at the first capture
    /// after the opening `|`).  Stops at the closing `|`.  Each
    /// capture becomes a tracked local with .unknown origin — we don't
    /// model per-element borrow shape yet, but subsequent uses inside
    /// the body now resolve via name_to_local rather than falling
    /// through to .unknown identifier classification.
    fn registerCaptures(self: *Builder, payload_token: Ast.TokenIndex) !void {
        _ = try self.registerCapturesImpl(payload_token, null, false);
    }

    /// Error-capture variant of `registerCaptures`: each registered
    /// capture is marked `is_error_capture` so `return <cap>` is treated
    /// as an error return.  Used for `catch |err|`.
    fn registerErrorCaptures(self: *Builder, payload_token: Ast.TokenIndex) !void {
        _ = try self.registerCapturesImpl(payload_token, null, true);
    }

    /// For an optional scrutinee, prefer the type engine's instantiated
    /// payload type: `HashMapUnmanaged(*Entry).get(key)` is `?*Entry`, so
    /// its capture points into the entry allocation rather than this frame.
    /// A declared optional-pointer return or field also proves the payload
    /// without semantic resolution. Unknown declarations remain conservative.
    fn inferPointerCapture(self: *Builder, payload_token: Ast.TokenIndex, cond_expr: Ast.Node.Index) void {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        // Find the capture identifier — track whether `*` precedes
        // it (by-pointer capture).
        var t: Ast.TokenIndex = payload_token;
        var saw_star = false;
        while (t < tags.len and tags[t] != .identifier) : (t += 1) {
            if (tags[t] == .asterisk) saw_star = true;
            if (tags[t] == .pipe and t != payload_token) return;
        }
        if (t >= tags.len) return;
        const cap_name = tree.tokenSlice(t);
        if (std.mem.eql(u8, cap_name, "_")) return;
        const lid = self.name_to_local.get(cap_name) orelse return;
        // Inspect the scrutinee — peel the success-path wrappers so the
        // query below sees the expression that actually produced the
        // optional.
        const node = initValueNode(self, cond_expr);

        // Prefer the type engine's instantiated generic result.  A call
        // such as `HashMapUnmanaged(*Entry).get(key)` returns `?*Entry`;
        // only that semantic payload proof may mark the capture as a
        // pointer. Unknown result types do not imply a pointer.
        if (self.zls) |zls| {
            if (self.queryOrUnknown(bool, zls.optionalPayloadIsPointer(node))) |is_pointer| {
                if (is_pointer) {
                    self.locals.items[@intFromEnum(lid)].is_pointer = true;
                    return;
                }
            }
        }
        if (self.callReturnsOptionalPointer(node)) {
            self.locals.items[@intFromEnum(lid)].is_pointer = true;
            return;
        }
        // `if (recv.field) |*cap|` where recv is a pointer-typed
        // local.  The capture points into recv's storage, not the
        // current fn's frame.
        if (saw_star and tree.nodeTag(node) == .field_access) {
            if (self.fieldLhsFor(node)) |fref| {
                const parent_info = self.locals.items[@intFromEnum(fref.parent)];
                if (parent_info.is_pointer or parent_info.init_hint == .heap_local) {
                    self.locals.items[@intFromEnum(lid)].is_pointer = true;
                }
            }
        }

        // `if (recv.optional_ptr_field) |cap|` binds the payload BY
        // VALUE, so the `|cap|` form above never applies.  The semantic
        // proof at the top of this function is the right one, but the
        // type engine cannot resolve a payload spelled
        // `?*@import("some_module").T` across a named-module boundary —
        // it answers null, and the capture stays a stack value.  The
        // DECLARATION settles it without the resolver: a field spelled
        // `?*T` (optionally `?*const T`) carries a pointer payload, and
        // unwrapping an optional pointer hands out the pointer.
        //
        // Losing this is not cosmetic.  In
        //   const handle = context.sourceHandle(path) catch |err| …;
        //   return .{ .borrowed = &handle.tree };
        // `context` is never marked pointer, so `handle` inherits
        // nothing, `&handle.tree` classifies as `.stack_ref(handle)`,
        // and a borrow of the document store's own storage is reported
        // as an escape from this frame.
        if (!saw_star) {
            if (self.optionalPointerPayloadField(node)) |payload_field| {
                const captured = &self.locals.items[@intFromEnum(lid)];
                captured.is_pointer = true;
                // The capture HOLDS that pointer, so the declaration
                // that proved it also names what its uses read through
                // — `<cap>.method()` and the address-chain field walk
                // start from it without the resolver having to retype
                // the whole condition.  Only a payload spelled as a
                // plain named path HAS such a name: `?*@import("mod").T`
                // names a type in another file and this one cannot look
                // it up.  That costs the typing, never the proof —
                // `&cap.field` reads `is_pointer`, which is what the
                // declaration settled above, and the chain walk falls
                // back to its own question rather than to a guess.
                // Never overwritten: a name the capture already carries
                // came from a closer source.
                if (captured.type_name == null) {
                    captured.type_name = tokens.typeNameFromTokens(
                        tree,
                        payload_field.type_first,
                        payload_field.type_last,
                    );
                }
                return;
            }
            // `if (map.get(key)) |entry|` over a map declared
            // `HashMap(K, *V)`.  Same by-value capture as the `?*T`
            // field above and settled the same way — from the
            // DECLARATION — because the scrutinee is a call into the
            // standard library whose result type is only bound at the
            // instantiation this file spells.  Without it the capture
            // stays a stack value, `&entry.model` classifies as
            // `.stack_ref(entry)`, and a borrow of the map's own
            // entries is charged to this frame as an escape.
            if (self.mapPointerValuePayload(node)) {
                self.locals.items[@intFromEnum(lid)].is_pointer = true;
                return;
            }
        }
    }

    /// The field `expr_node` reads when that field's DECLARED type is an
    /// optional whose payload is a POINTER — `?*T` / `?*const T` — so
    /// `if (recv.field) |cap|` binds a pointer by value.  Null for every
    /// other shape, including a field whose payload is a value (`?Ctx`),
    /// which stays this frame's storage.
    ///
    /// Declaration-driven on purpose: it must work exactly where the type
    /// engine does not.  And it is deliberately the VERDICT alone — the
    /// `?` and the `*` are the whole answer, and both are tokens of the
    /// declaring file, so a payload spelled `?*@import("some_module").T`
    /// is settled exactly as a plain `?*Ctx` is.  Nothing about naming
    /// the payload's type enters here: a payload this file cannot name is
    /// still a pointer, and folding the two questions together let an
    /// unnamed payload read as a by-value one and charged the frame for a
    /// borrow of the pointee.  Reading the capture's TYPE NAME off the
    /// same declaration is the caller's separate step, and declines
    /// honestly when there is no name to give.
    fn optionalPointerPayloadField(self: *Builder, expr_node: Ast.Node.Index) ?*const model_mod.FieldInfo {
        const tree = self.tree;
        const field = self.receiverField(expr_node) orelse return null;
        // Same-file owner, so the field's token range indexes THIS tree —
        // which is also what makes the `?*` spelling readable with no
        // resolver at all.
        if (!typeRangeIsOptionalPointer(tree, field.type_first, field.type_last)) return null;
        return field;
    }

    /// The DECLARED field a `<recv>.<field>` expression names, resolved
    /// through the receiver's own declared type.  Null for any other
    /// shape — a bare identifier, a chained receiver, a receiver with no
    /// tracked type, or a field the owner's declaration does not have.
    fn receiverField(self: *Builder, expr_node: Ast.Node.Index) ?*const model_mod.FieldInfo {
        const tree = self.tree;
        if (tree.nodeTag(expr_node) != .field_access) return null;
        const recv, const field_tok = tree.nodeData(expr_node).node_and_token;
        if (tree.nodeTag(recv) != .identifier) return null;
        const recv_name = tree.tokenSlice(tree.nodeMainToken(recv));
        const owner_type: ?[]const u8 = if (std.mem.eql(u8, recv_name, "self") or
            std.mem.eql(u8, recv_name, "this"))
            self.self_type
        else if (self.name_to_local.get(recv_name)) |local|
            self.locals.items[@intFromEnum(local)].type_name
        else
            null;
        const type_name = owner_type orelse return null;
        const cache = self.cache orelse return null;
        const model = self.modelOrNull(cache) orelse return null;
        const owner = model.findType(type_name) orelse return null;
        return owner.findField(tree.tokenSlice(field_tok)) orelse null;
    }

    /// True when `expr_node` is `<map>.get(…)` over a map whose
    /// DECLARED value type is a POINTER, so `get` hands back `?*T` and
    /// `if (m.get(k)) |entry|` binds that pointer BY VALUE.
    ///
    /// This is the shape `optionalPointerPayloadField` cannot reach and
    /// the type engine does not answer: the scrutinee is a CALL, not a
    /// field, so there is no `?*T` field declaration to read; and
    /// `std.StringHashMapUnmanaged(*Entry).get` lives in the standard
    /// library, whose `get` is declared generically (`?V`) with `V`
    /// bound only at the instantiation this file spells.  The receiver's
    /// own declaration carries that binding — `*Entry` is written out
    /// there — and `get` is declared to return `?V`, so the two together
    /// say what the payload is.
    ///
    /// Declaration-driven, and only for `get`: a map shaped
    /// `HashMap(K, *V)` read through `get` is exactly `?*V`, and no
    /// other accessor is claimed.  The VALUE-typed sibling
    /// (`HashMap(K, Entry)`) fails the pointer test on its declared
    /// value type and keeps its capture as a stack value, which is the
    /// discrimination this has to make.
    fn mapPointerValuePayload(self: *Builder, expr_node: Ast.Node.Index) bool {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buf, expr_node) orelse return false;
        const callee = call.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return false;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeData(callee).node_and_token[1]), "get")) return false;
        const recv = tree.nodeData(callee).node_and_token[0];
        const field = self.receiverField(recv) orelse return false;
        return self.typeRangeIsMapWithPointerValue(field.type_first, field.type_last);
    }

    /// True when a declared type is a std hash-map instantiation whose
    /// VALUE parameter is spelled as a pointer — `HashMap(K, *V)`,
    /// `StringHashMapUnmanaged(*Entry)`, `AutoArrayHashMapUnmanaged(K, *const V)`.
    ///
    /// Textual on the container NAME because that is the whole contract:
    /// every `*HashMap` / `*HashMapUnmanaged` in std returns `?V` from
    /// `get`, and nothing else spells its name that way.  The KEY
    /// parameter is skipped by depth so a `HashMap([]const u8, *V)` is
    /// read correctly; only the segment AFTER the top-level comma can
    /// be the value, and it has to begin with `*`.
    fn typeRangeIsMapWithPointerValue(
        self: *const Builder,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (first > last) return false;
        // The container's own name is the last identifier before its
        // parameter list.  Zig spells generic instantiations with
        // PARENS — `StringHashMapUnmanaged(*Entry)` — so `(` is the
        // opener, and the loop has to stop there or it walks on into
        // the parameters and reads `Entry` as the container's name.
        var name_tok: ?Ast.TokenIndex = null;
        var t = first;
        while (t <= last and tags[t] != .l_paren) : (t += 1) {
            if (tags[t] == .identifier) name_tok = t;
        }
        const name = if (name_tok) |n| tree.tokenSlice(n) else return false;
        if (!std.mem.endsWith(u8, name, "HashMap") and
            !std.mem.endsWith(u8, name, "HashMapUnmanaged")) return false;
        if (t > last) return false;
        // The value parameter is whatever follows the top-level comma, or
        // — for the single-parameter spelling every `StringHashMapUnmanaged(V)`
        // uses — everything just past the `(`.
        var value_first: Ast.TokenIndex = t + 1;
        var depth: u32 = 0;
        var i = t;
        while (i <= last) : (i += 1) {
            switch (tags[i]) {
                .l_paren, .l_bracket, .angle_bracket_left => depth += 1,
                .r_paren, .r_bracket, .angle_bracket_right => depth -|= 1,
                // A comma inside the KEY (`HashMap([]const u8, *V)`) sits
                // at depth 2, so only this one separates the parameters.
                .comma => if (depth == 1) {
                    value_first = i + 1;
                    break;
                },
                else => {},
            }
        }
        if (value_first > last) return false;
        return typeRangeStartsWithPointer(tags, value_first, @min(last, value_first + 2));
    }

    /// True when `init_node` unwraps an optional (`e.?`) over a field
    /// whose DECLARED type is `?*T` / `?*const T` — the one optional
    /// unwrap whose payload is knowable to be a pointer without a
    /// resolver.  The callee-spelling proofs cannot make this call
    /// (`parent` may return `?Box` by value), and the type engine cannot
    /// resolve a payload spelled `?*@import("some_module").T` across a
    /// module boundary.  The declaration settles both.
    fn initUnwrapsOptionalPointerField(self: *Builder, init_node: Ast.Node.Index) bool {
        const tree = self.tree;
        const value = initShapeNode(self, init_node);
        if (tree.nodeTag(value) != .unwrap_optional) return false;
        return self.optionalPointerPayloadField(tree.nodeData(value).node_and_token[0]) != null;
    }

    /// Prove an optional pointer from the callee's declared return type.
    fn callReturnsOptionalPointer(self: *Builder, expr_node: Ast.Node.Index) bool {
        const decl = self.calleeDeclOfCall(expr_node) orelse return false;
        var buf: [1]Ast.Node.Index = undefined;
        const proto = decl.tree.fullFnProto(&buf, decl.fn_decl) orelse return false;
        const return_type = proto.ast.return_type.unwrap() orelse return false;
        return typeRangeIsOptionalPointer(
            decl.tree,
            decl.tree.firstToken(return_type),
            decl.tree.lastToken(return_type),
        );
    }

    /// Restore bindings registered before this lexical or capture scope.
    /// Call only after lowering the scope's defers, which still need its
    /// inner bindings. Capture scopes also retain their names until any
    /// post-body fill proof has inspected the body.
    fn restoreLocalNames(self: *Builder, pre_len: u32, boundary: Ast.TokenIndex) void {
        const cache = self.cache orelse &self.address_cache.?;
        const bindings = cache.bindings.getPtr(@intFromEnum(self.fn_body_node.?)).?;
        var j = pre_len;
        while (j < self.locals.items.len) : (j += 1) {
            const name = self.locals.items[j].name;
            const current = self.name_to_local.getPtr(name) orelse continue;
            if (@intFromEnum(current.*) < pre_len) continue;
            // Historical sibling locals are not enclosing bindings.
            const binding = bindings.findAt(name, boundary);
            var prev: ?LocalId = null;
            var k: u32 = 0;
            while (k < pre_len) : (k += 1) {
                const info = &self.locals.items[k];
                if (!std.mem.eql(u8, info.name, name)) continue;
                if (binding) |outer| {
                    if (info.decl_pos.byte != self.tree.tokenStart(outer.name_token)) continue;
                } else if (!self.file_scope_storage.contains(@enumFromInt(k))) {
                    continue;
                }
                prev = @enumFromInt(k);
            }
            if (prev) |pl| {
                current.* = pl;
            } else {
                _ = self.name_to_local.remove(name);
            }
        }
    }

    /// Number of locals registered so far, as the `u32` `LocalId`
    /// indexes them by.  A body that declares more locals than a `u32`
    /// can address has a local table larger than any allocator hands
    /// out, so the count is checked rather than narrowed — the same
    /// bound `LocalId` itself imposes on every access.
    fn localsLen(self: *Builder) !u32 {
        return std.math.cast(u32, self.locals.items.len) orelse error.OutOfMemory;
    }

    fn registerCapturesWith(self: *Builder, payload_token: Ast.TokenIndex, reset_into: ?BlockId) !void {
        _ = try self.registerCapturesImpl(payload_token, reset_into, false);
    }

    /// Error-capture variant of `registerCapturesWith`: marks each
    /// registered capture `is_error_capture`.  Used for `else |err|`.
    fn registerErrorCapturesWith(self: *Builder, payload_token: Ast.TokenIndex, reset_into: ?BlockId) !void {
        _ = try self.registerCapturesImpl(payload_token, reset_into, true);
    }

    /// Shared body for the capture-registration wrappers.  When
    /// `mark_error` is set, every registered capture local gets
    /// `is_error_capture = true` (see LocalInfo).
    fn registerCapturesImpl(self: *Builder, payload_token: Ast.TokenIndex, reset_into: ?BlockId, mark_error: bool) !void {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var t: Ast.TokenIndex = payload_token;
        while (t < tags.len) : (t += 1) {
            switch (tags[t]) {
                .pipe => return, // closing `|`
                .identifier => {
                    const name = tree.tokenSlice(t);
                    if (std.mem.eql(u8, name, "_")) continue;
                    const lid = try self.registerLocal(name, self.posOfToken(t));
                    if (mark_error) self.locals.items[@intFromEnum(lid)].is_error_capture = true;
                    if (reset_into) |blk| {
                        try self.appendStmt(blk, .{
                            .kind = .{ .reset_capture = .{ .local = lid } },
                            .pos = self.posOfToken(t),
                            .end_pos = self.posOfToken(t),
                        });
                    }
                },
                else => {}, // `,`, `*`, `|` (opening): skip
            }
        }
    }

    /// Lower one lexical block and replay its normal defers at fallthrough.
    fn lowerBlock(self: *Builder, block_node: Ast.Node.Index, cur: *BlockId) !void {
        if (self.cache == null and self.address_cache == null) {
            self.address_cache = file_cache.FileCache.init(self.gpa, self.tree);
        }
        const cache = self.cache orelse &self.address_cache.?;
        // Warm the existing lexical table before any scope mutation.
        // Cleanup only reads it, including allocation-error exits.
        _ = try cache.localBindings(self.fn_proto.?, self.fn_body_node.?);
        const pre_len = try self.localsLen();
        defer self.restoreLocalNames(pre_len, self.tree.firstToken(block_node));
        try self.lowerBlockContents(block_node, cur);
    }

    /// The caller can retain body bindings until a post-body proof finishes.
    /// Ordinary blocks restore them only after this lowers their defers.
    fn lowerBlockContents(self: *Builder, block_node: Ast.Node.Index, cur: *BlockId) LoweringError!void {
        const tree = self.tree;
        var stmt_buf: [2]Ast.Node.Index = undefined;
        const stmts = blockStmts(tree, block_node, &stmt_buf);

        // Scope-bound defer handling.  Zig defers fire at the
        // enclosing BLOCK's exit, not just at return.  We snapshot
        // the unified defer stack here; any defer/errdefer pushed
        // inside this block is fired (LIFO) at fallthrough exit,
        // then popped so a later return doesn't re-fire it from an
        // already-exited scope.
        const save = self.deferred.items.len;
        defer self.deferred.shrinkRetainingCapacity(save);
        errdefer self.counted_fill_credit = null;

        // Re-tested conditions have to be known BEFORE the list is
        // lowered: the `if` that establishes one comes long before the
        // one that re-reads it, and only the whole list says which two
        // are the same condition.
        try self.establishGuardPairs(stmts);

        // Each statement arms the counter-guarded fill credit for ITSELF
        // from the statement BEFORE it: that proof is about a `while`
        // and the equality check which closes its counting argument,
        // and the two have to be siblings in ONE block for that check
        // to dominate everything below.  Arming from (current, next)
        // instead arms the credit one statement too early — the next
        // iteration overwrites it with its own answer, almost always
        // null, before the `if` that is meant to claim it ever runs,
        // so the counting argument could never fire at all.
        for (stmts, 0..) |stmt_idx, index| {
            self.counted_fill_credit = if (index > 0)
                self.countedFillGuard(stmts[index - 1], stmt_idx)
            else
                null;
            try self.lowerStmt(stmt_idx, cur);
        }
        self.counted_fill_credit = null;

        try self.flushScopeDefers(cur, save);
    }

    /// Lower the top-level function body.  lowerBlock now flushes
    /// its own defers at fallthrough exit, so no separate flush is
    /// needed here.
    fn lowerFunctionBody(self: *Builder, body_node: Ast.Node.Index, cur: *BlockId) !void {
        // Register function parameters as locals so the body can
        // reference them (e.g. `b.foo` where `b` is a `*Bar` param).
        // Params get .other init_hint and .plain origin — they're
        // caller-owned; the analysis only flags state changes that
        // happen INSIDE this function.  Without registration,
        // inter-procedural patterns like `b.foo.dispose()` can't
        // resolve `b` to a LocalId, so .field_heap_free / .field_use
        // emissions silently drop.
        try self.registerFnParams(cur.*);
        // A file-scope `const … = undefined` the body can read.  It is
        // registered AFTER the parameters — so a parameter of the same
        // name wins the flat map and is not overwritten — and BEFORE the
        // body lowers, so a use of the name resolves at all.
        try self.registerUndefFileConsts(cur.*);
        // Leaky-destructor check: when this fn is a destructor
        // (finalize / deinit / destroy) on type T AND another fn
        // on T heap-allocates an instance (`<x>.create(T)`) AND
        // this fn doesn't have inferred @takes(self), the
        // destructor LEAKS instances of T.  Catches oven-sh/bun#29840
        // class.  Emits a leak_warning stmt at body start;
        // transferLeakWarning fires the diagnostic.
        if (self.leakyDestructorTypeName()) |type_name| {
            try self.appendStmt(cur.*, .{
                .kind = .{ .leak_warning = .{ .type_name = type_name } },
                .pos = self.posOfToken(self.tree.firstToken(body_node)),
                .end_pos = self.posOfTokenEnd(self.tree.firstToken(body_node)),
            });
        }
        try self.lowerBlock(body_node, cur);
        // Synthetic implicit-return at fn-body end.  Void fns that
        // fall through without an explicit `return` still need
        // transferRet to fire so post-defer checks (e.g. dangling
        // out-param heap pointers) run.  Cheap idempotent emit —
        // when the body already returned explicitly, cur is in a
        // fresh dead block and this stmt sits unreached.
        const last = self.tree.lastToken(body_node);
        try self.appendStmt(cur.*, .{
            .kind = .{ .ret = .{
                .value_kind = .plain,
                .is_borrowed_return_type = false,
                .is_literal_undef = false,
            } },
            .pos = self.posOfToken(last),
            .end_pos = self.posOfTokenEnd(last),
        });
    }

    fn registerFnParams(self: *Builder, cur: BlockId) !void {
        const tree = self.tree;
        const proto = self.fn_proto orelse return;
        var it = proto.iterate(tree);
        var parameter_index: usize = 0;
        while (it.next()) |param| {
            const ordinal = parameter_index;
            parameter_index += 1;
            const name_tok = param.name_token orelse continue;
            const name = tree.tokenSlice(name_tok);
            if (std.mem.eql(u8, name, "_")) continue;
            // Extract the param's declared base type (e.g. "Foo" from
            // `*const Foo`), resolving Self / @This() to the enclosing
            // type so methods inside `pub const Foo = struct { fn f(
            // self: *Self) ... }` get a type_name of "Foo".
            const type_name: ?[]const u8 = if (param.type_expr) |te|
                self.extractTypeName(te, self.self_type)
            else
                null;
            const is_pointer = if (param.type_expr) |te|
                self.typeIsPointer(te)
            else
                false;
            const local = try self.registerLocalWithPointerHint(
                name,
                self.posOfToken(name_tok),
                false,
                .other,
                null,
                type_name,
                is_pointer,
            );
            var value_type = self.bindingValueType(param.type_expr, null, .unknown);
            var undefined_parameter = false;
            if (param.type_expr == null) {
                if (self.integerResolutionFrame()) |frame| {
                    if (frame.actual_type) |actual| {
                        if (actual.data == .function and ordinal < actual.data.function.parameters.len) {
                            const parameter_type = actual.data.function.parameters[ordinal].type;
                            if (self.queryOrUnknown(
                                zls_resolver_mod.TypeResolver.ActualType,
                                frame.resolver.normalizedType(parameter_type),
                            )) |ty| {
                                switch (frame.resolver.typeTag(ty) orelse .@"opaque") {
                                    .pointer => {
                                        const size = frame.resolver.pointerSize(ty);
                                        value_type.pointer_header = size != null and size.? != .slice;
                                        value_type.slice_header = size == .slice;
                                    },
                                    .int, .comptime_int, .float, .comptime_float, .bool, .@"enum", .error_set => {
                                        value_type.runtime_scalar = true;
                                    },
                                    .undefined => undefined_parameter = true,
                                    else => {
                                        value_type.aggregate_value = ty.data == .array;
                                        value_type.container = if (ty.data == .container) ty.data.container else null;
                                    },
                                }
                            }
                        }
                    }
                }
            }
            self.integer_domains.items[@intFromEnum(local)] = value_type.domain;
            self.locals.items[@intFromEnum(local)].tracks_scalar_value = value_type.runtime_scalar;
            self.locals.items[@intFromEnum(local)].is_pointer =
                !value_type.slice_header and (is_pointer or value_type.pointer_header);
            self.locals.items[@intFromEnum(local)].is_slice = value_type.slice_header;
            self.locals.items[@intFromEnum(local)].tracks_array_payload =
                value_type.aggregate_value or value_type.container != null;
            if (undefined_parameter) {
                try self.appendStmt(cur, .{
                    .kind = .{ .decl = .{ .local = local, .init_kind = .undef } },
                    .pos = self.posOfToken(name_tok),
                    .end_pos = self.posOfTokenEnd(name_tok),
                });
            }
            if (param.type_expr) |type_node| {
                self.locals.items[@intFromEnum(local)].is_unsigned = unsignedType(tree, type_node);
                if (!is_pointer and self.typeIsStackArray(type_node)) {
                    const info = &self.locals.items[@intFromEnum(local)];
                    info.is_array = true;
                    if (self.fill.declaredExtent(.{ .first = tree.firstToken(type_node), .last = tree.lastToken(type_node) })) |extent| {
                        info.array_extent = extent.number;
                    }
                    // A by-value argument has already been read by its caller.
                    // This says nothing about storage behind pointer parameters.
                    try self.appendStmt(cur, .{
                        .kind = .{ .array_complete = .{ .array = local } },
                        .pos = self.posOfToken(name_tok),
                        .end_pos = self.posOfTokenEnd(name_tok),
                    });
                }
            }
            if (value_type.slice_header) {
                try self.appendStmt(cur, .{
                    .kind = .{ .field_assign = .{
                        .parent = local,
                        .name = "ptr",
                        .rhs_kind = .plain,
                        .defined = true,
                    } },
                    .pos = self.posOfToken(name_tok),
                    .end_pos = self.posOfTokenEnd(name_tok),
                });
                try self.appendStmt(cur, .{
                    .kind = .{ .field_assign = .{
                        .parent = local,
                        .name = "len",
                        .rhs_kind = .unknown,
                        .defined = true,
                    } },
                    .pos = self.posOfToken(name_tok),
                    .end_pos = self.posOfTokenEnd(name_tok),
                });
            }
            try self.immutable_locals.put(self.gpa, local, {});
        }
    }

    /// Register static storage initialized to undefined. Reads retain that
    /// origin until a concrete write, without inventing a stack lifetime.
    /// The map also records whether each static binding can be written.
    fn registerUndefFileConsts(self: *Builder, cur: BlockId) !void {
        const tree = self.tree;
        // Null is the index declining, not an empty file: a walk that
        // gave up has not proved any name absent, and registering
        // locals from half an index would silently drop every
        // file-scope table it had not reached yet.
        _ = self.fill.declarations() orelse return;
        for (tree.rootDecls()) |node| {
            const variable = tree.fullVarDecl(node) orelse continue;
            const name_token = variable.ast.mut_token + 1;
            const name = tree.tokenSlice(name_token);
            if (self.name_to_local.contains(name)) continue;
            const init = variable.ast.init_node.unwrap() orelse continue;
            if (tree.nodeTag(init) != .identifier or
                !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(init)), "undefined")) continue;
            const local = try self.registerLocalWithPointerHint(
                name,
                self.posOfToken(name_token),
                false,
                .other,
                null,
                null,
                false,
            );
            try self.file_scope_storage.put(self.gpa, local, tree.tokenTag(variable.ast.mut_token) == .keyword_var);
            try self.appendStmt(cur, .{
                .kind = .{ .decl = .{ .local = local, .init_kind = .undef } },
                .pos = self.posOfToken(name_token),
                .end_pos = self.posOfTokenEnd(name_token),
            });
        }
    }

    /// Can anything STORE into this local?
    ///
    /// A FILE-SCOPE `const` cannot, and that is the whole of it: the
    /// binding is immutable for the whole program, so its bytes are
    /// undefined from the moment it is declared until the program ends.
    /// Three separate heuristics in the expression walk would otherwise
    /// clear that state on the strength of a NAME rather than a
    /// declaration — an address handed to a callee that may write
    /// through it, an out-parameter write, a MUTATOR-NAMED method
    /// spelled on the local — and each of them turns a read of genuinely
    /// undefined bytes into silence.  `address_taken` is still recorded:
    /// the address IS taken, and what it says about the storage is what
    /// this vetoes.
    fn localCanBeStored(self: *const Builder, id: LocalId) bool {
        return self.file_scope_storage.get(id) orelse true;
    }

    fn pushDefer(self: *Builder, body_node: Ast.Node.Index) !void {
        try self.deferred.append(self.gpa, .{ .kind = .normal, .body = body_node });
    }

    fn pushErrdefer(self: *Builder, body_node: Ast.Node.Index) !void {
        try self.deferred.append(self.gpa, .{ .kind = .err, .body = body_node });
    }

    /// Replay normal defers for the scopes crossed by a control-flow edge.
    /// Keep registrations intact for other exits from the same lexical scope.
    fn flushScopeDefers(self: *Builder, cur: *BlockId, first: usize) LoweringError!void {
        var i = self.deferred.items.len;
        std.debug.assert(first <= i);
        while (i > first) {
            i -= 1;
            const entry = self.deferred.items[i];
            if (entry.kind == .normal) try self.lowerStmt(entry.body, cur);
        }
    }

    /// Error-path flush: walk the unified defer stack LIFO, firing
    /// BOTH errdefers and defers in declaration-reverse order.  This
    /// matches Zig's semantics — a `defer use(p)` declared AFTER
    /// an `errdefer free(p)` runs FIRST on error exit, avoiding a
    /// spurious UAF in the synthetic err_exit sink.  Used at
    /// synthetic try-error-exit blocks.
    fn flushErrAndNormalDefers(self: *Builder, cur: *BlockId) (LoweringError)!void {
        var i = self.deferred.items.len;
        while (i > 0) {
            i -= 1;
            try self.lowerStmt(self.deferred.items[i].body, cur);
        }
    }

    /// Dispatch on statement node tag.  v1: handle decls, assigns,
    /// expression-statement calls, returns, if/while; everything else
    /// becomes a `.lowering_gap` placeholder.
    fn lowerStmt(self: *Builder, stmt_node: Ast.Node.Index, cur: *BlockId) LoweringError!void {
        const tree = self.tree;
        const tag = tree.nodeTag(stmt_node);
        switch (tag) {
            .simple_var_decl, .local_var_decl, .aligned_var_decl, .global_var_decl => {
                try self.lowerVarDecl(stmt_node, cur);
            },
            .assign, .assign_destructure => {
                try self.lowerAssign(stmt_node, cur);
            },
            .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod, .assign_shl, .assign_shr, .assign_shl_sat, .assign_bit_and, .assign_bit_xor, .assign_bit_or, .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap, .assign_add_sat, .assign_sub_sat, .assign_mul_sat => {
                const pair = tree.nodeData(stmt_node).node_and_node;
                try self.emitUsesInExpr(stmt_node, cur.*, null);
                if ((tag == .assign_add or tag == .assign_sub) and
                    tree.nodeTag(pair[0]) == .identifier and self.integerValue(pair[1]) == 1)
                {
                    if (self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(pair[0])))) |local| {
                        try self.appendStmt(cur.*, .{
                            .kind = .{ .counter_step = .{ .local = local, .step = if (tag == .assign_add) 1 else -1 } },
                            .pos = self.posOf(stmt_node),
                            .end_pos = self.endPosOf(stmt_node),
                        });
                    }
                } else if (tree.nodeTag(pair[0]) == .identifier) {
                    if (self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(pair[0])))) |local| {
                        // A compound assignment reads the old value and the
                        // operand; both must be defined for the result to be.
                        var value_inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
                        const value_defined = self.locals.items[@intFromEnum(local)].tracks_scalar_value and
                            self.selectedValueInputs(stmt_node, &value_inputs, true);
                        try self.appendStmt(cur.*, .{
                            .kind = .{ .assign = .{
                                .target = local,
                                .rhs_kind = .unknown,
                                .value_defined = value_defined,
                                .value_inputs = value_inputs,
                            } },
                            .pos = self.posOf(stmt_node),
                            .end_pos = self.endPosOf(stmt_node),
                        });
                    }
                } else if (self.indexedTarget(pair[0])) |access| {
                    var write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
                        .array = access.array,
                        .index = self.indexTerm(access.index_node),
                        .rhs_kind = .plain,
                        .field_array = access.field_array,
                    };
                    // Compound assignment reads its old slot as well as its
                    // RHS. An undefined operand cannot initialize that slot.
                    write.defined = self.selectedValueInputs(stmt_node, &write.selected_inputs, false);
                    try self.appendStmt(cur.*, .{
                        .kind = .{ .indexed_write = write },
                        .pos = self.posOf(pair[0]),
                        .end_pos = self.endPosOf(pair[0]),
                    });
                    try self.appendSliceStoreEffect(cur.*, write, self.posOf(pair[0]), self.endPosOf(pair[0]));
                } else if (self.indexedMemberTarget(pair[0])) |access| {
                    try self.emitIndexedMemberWrite(cur.*, pair[0], pair[1], access);
                } else if (self.fieldLhsFor(pair[0])) |field| {
                    if (self.fieldIsUnsigned(field.parent, field.name) or
                        self.bindingValueType(null, pair[0], .unknown).runtime_scalar)
                    {
                        // A scalar compound store consumes only this field's
                        // previous value and the RHS, not sibling payloads.
                        var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
                        const defined = self.selectedValueInputs(pair[1], &inputs, true);
                        try self.appendStmt(cur.*, .{
                            .kind = .{ .field_assign = .{
                                .parent = field.parent,
                                .name = field.name,
                                .rhs_kind = .unknown,
                                .defined = defined,
                                .selected_inputs = inputs,
                                .reads_old_value = true,
                            } },
                            .pos = self.posOf(pair[0]),
                            .end_pos = self.endPosOf(pair[0]),
                        });
                    } else try self.emitWritesInLhs(pair[0], cur.*);
                } else {
                    try self.emitWritesInLhs(pair[0], cur.*);
                }
            },
            .@"return" => {
                // lowerReturn handles its own defer-flush ordering —
                // it has to interleave with try-error-exit / catch
                // forking when the return value has those at top level.
                try self.lowerReturn(stmt_node, cur);
            },
            .call, .call_one, .call_comma, .call_one_comma => {
                try self.lowerCallStmt(stmt_node, cur);
            },
            .@"defer" => {
                const body = tree.nodeData(stmt_node).node;
                try self.pushDefer(body);
            },
            .@"errdefer" => {
                const body = tree.nodeData(stmt_node).opt_token_and_node[1];
                try self.pushErrdefer(body);
            },
            .if_simple, .@"if" => try self.lowerIf(stmt_node, cur),
            .while_simple, .while_cont, .@"while" => try self.lowerWhile(stmt_node, cur),
            .for_simple, .@"for" => try self.lowerFor(stmt_node, cur),
            .@"switch", .switch_comma => try self.lowerSwitch(stmt_node, cur, null),
            .@"try" => try self.lowerTryStmt(stmt_node, cur),
            .@"catch" => try self.lowerCatchStmt(stmt_node, cur),
            // The one position that has not already walked the operand:
            // `lowerOrelseStmt` emits the lhs reads here so a discarded
            // `touch(p) orelse unreachable;` reads `p` the way the
            // declaration, assignment and `_ =` spellings do.
            .@"orelse" => try self.lowerOrelseStmt(stmt_node, cur),
            .@"break" => try self.lowerBreakOrContinue(cur, .@"break", stmt_node),
            .@"continue" => try self.lowerBreakOrContinue(cur, .@"continue", stmt_node),
            // Divergent stmts: replace cur with a fresh dead block so
            // any caller-added edge from cur to a successor (e.g.
            // emitCatchFork wiring catch-body→merge after `catch
            // unreachable`) flows from an unreachable block.  Without
            // this, the diverged path's stale state pollutes the
            // merge join — e.g. `const buf = alloc(...) catch
            // unreachable; free(buf);` would lose buf's .heap origin
            // at the merge because the catch arm collapses to .plain.
            .unreachable_literal => cur.* = try self.newBlock(),
            .builtin_call, .builtin_call_two, .builtin_call_two_comma, .builtin_call_comma => {
                if (self.builtinIsDivergent(stmt_node)) {
                    cur.* = try self.newBlock();
                } else {
                    try self.lowerCallStmt(stmt_node, cur);
                }
            },
            // Nested blocks: recurse so empty blocks DON'T trigger
            // the conservative .plain collapse via lowering_gap.
            // Labeled forms (`blk: { ... break :blk; }`) get the
            // block-label scaffolding so `break :blk` can resolve.
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                if (self.blockLabelToken(stmt_node)) |lt| {
                    try self.lowerLabeledBlock(stmt_node, lt, cur, null);
                } else {
                    try self.lowerBlock(stmt_node, cur);
                }
            },
            else => {
                try self.appendStmt(cur.*, .{
                    .kind = .{ .lowering_gap = .{ .note = @tagName(tag) } },
                    .pos = self.posOf(stmt_node),
                    .end_pos = self.endPosOf(stmt_node),
                });
            },
        }
    }

    /// `if (cond) THEN [else ELSE]` → fork into two successor blocks,
    /// lower each branch into its own block, then join into a fresh
    /// merge block.  Subsequent statements emit into the merge block.
    fn lowerIf(self: *Builder, if_node: Ast.Node.Index, cur: *BlockId) !void {
        // Taken by the COUNTER-GUARDED fill proof, which [lowerBlock]
        // arms on the statement right before this one.  Cleared on the
        // way in either way, so a credit can never be claimed by an
        // `if` that is not the one it was established for.
        const counted_credit = self.counted_fill_credit;
        self.counted_fill_credit = null;
        const branch = self.tree.fullIf(if_node).?;
        try self.lowerConditionUses(branch.ast.cond_expr, cur);
        const condition = if (branch.payload_token == null) self.booleanValue(branch.ast.cond_expr) else null;
        const then_block = try self.newBlock();
        const else_block = try self.newBlock();
        const merge = try self.newBlock();
        try self.addEdge(cur.*, then_block);
        try self.addEdge(cur.*, else_block);
        try self.assumeCondition(then_block, branch.ast.cond_expr, condition, true);
        try self.assumeCondition(else_block, branch.ast.cond_expr, condition, false);
        // A condition this function proved is one half of a RE-TESTED
        // pair records which way it read.  Both arms emit: the fact
        // that matters is the one recording FALSE, which is what lets
        // a later test of the same condition cut this path off — and
        // cutting it is what leaves a local initialized under that
        // condition readable under the second test of it.
        if (self.guard_facts.get(if_node)) |fact| {
            const at = self.posOf(if_node);
            const end_at = self.endPosOf(if_node);
            try self.appendStmt(then_block, .{
                .kind = .{ .guard_fact = .{ .guard = fact.guard, .holds = !fact.negated } },
                .pos = at,
                .end_pos = end_at,
            });
            try self.appendStmt(else_block, .{
                .kind = .{ .guard_fact = .{ .guard = fact.guard, .holds = fact.negated } },
                .pos = at,
                .end_pos = end_at,
            });
        }
        const pre_capture_len = try self.localsLen();
        if (branch.payload_token) |token| {
            try self.registerCapturesWith(token, then_block);
            self.inferPointerCapture(token, branch.ast.cond_expr);
        }
        var then_cur = then_block;
        try self.lowerStmt(branch.ast.then_expr, &then_cur);
        // The counting argument holds only on the arm where the
        // counter EQUALLED the length, and that is the arm the credit
        // goes to.  The arm that leaves the function cannot reach the
        // code below, so it gets no edge to the merge — routing it
        // there would carry a state the program never reaches into the
        // read, and a real partial fill would read as undefined.
        if (counted_credit == null) try self.addEdge(then_cur, merge);
        self.restoreLocalNames(pre_capture_len, self.tree.firstToken(if_node));
        var else_cur = else_block;
        if (branch.ast.else_expr.unwrap()) |else_expr| {
            if (branch.error_token) |token| try self.registerErrorCapturesWith(token, else_block);
            try self.lowerStmt(else_expr, &else_cur);
            self.restoreLocalNames(pre_capture_len, self.tree.firstToken(if_node));
        }
        if (counted_credit) |credit| {
            try self.appendStmt(else_cur, .{
                .kind = .{ .array_complete = .{ .array = credit.local } },
                .pos = credit.pos,
                .end_pos = credit.end_pos,
            });
        }
        try self.addEdge(else_cur, merge);
        cur.* = merge;
    }

    /// `while (cond) BODY [else ELSE]` → produces a header block (where
    /// the condition is evaluated each iteration), a body block, and a
    /// merge block (post-loop).  Back-edge from body → header creates
    /// the loop — the analyzer's worklist iterates body's state into
    /// header until fixed point.
    ///
    /// We model the simplest valid loop CFG:
    ///   cur ─→ header ─→ body ─→ header (back-edge)
    ///                  ↘ merge (loop exit / else)
    fn lowerWhile(self: *Builder, while_node: Ast.Node.Index, cur: *BlockId) !void {
        const loop = self.tree.fullWhile(while_node).?;
        const condition = if (loop.payload_token == null) self.booleanValue(loop.ast.cond_expr) else null;
        const header = try self.newBlock();
        const body = try self.newBlock();
        const merge = try self.newBlock();
        const natural_exit = try self.newBlock();
        const continuation = if (loop.ast.cont_expr != .none) try self.newBlock() else header;
        try self.addEdge(cur.*, header);
        var condition_cur = header;
        try self.lowerConditionUses(loop.ast.cond_expr, &condition_cur);
        try self.addEdge(condition_cur, body);
        try self.addEdge(condition_cur, natural_exit);
        try self.assumeCondition(body, loop.ast.cond_expr, condition, true);
        try self.assumeCondition(natural_exit, loop.ast.cond_expr, condition, false);
        try self.loop_stack.append(self.gpa, .{
            .continue_to = continuation,
            .merge = merge,
            .defer_depth = self.deferred.items.len,
            .label = if (loop.label_token) |token| self.tree.tokenSlice(token) else null,
        });
        const pre_capture_len = try self.localsLen();
        if (loop.payload_token) |token| try self.registerCapturesWith(token, body);
        var body_cur = body;
        try self.lowerStmt(loop.ast.then_expr, &body_cur);
        const ended_loop = self.loop_stack.pop().?;
        std.debug.assert(ended_loop.merge == merge);
        try self.addEdge(body_cur, continuation);
        if (loop.ast.cont_expr.unwrap()) |expression| {
            var continuation_cur = continuation;
            try self.lowerStmt(expression, &continuation_cur);
            try self.addEdge(continuation_cur, header);
        }
        self.restoreLocalNames(pre_capture_len, self.tree.firstToken(while_node));
        try self.emitNaturalWhileFill(natural_exit, body_cur, while_node);
        if (natural_exit != merge) {
            var else_cur = natural_exit;
            if (loop.ast.else_expr.unwrap()) |else_expr| {
                if (loop.error_token) |token| try self.registerErrorCapturesWith(token, natural_exit);
                try self.lowerStmt(else_expr, &else_cur);
                self.restoreLocalNames(pre_capture_len, self.tree.firstToken(while_node));
            }
            try self.addEdge(else_cur, merge);
        }
        cur.* = merge;
    }

    /// Natural exhaustion is separate from break/error exits. A successful
    /// store followed by a unit step visits every slot in its proved range.
    fn emitNaturalWhileFill(self: *Builder, exit: BlockId, body_exit: BlockId, node: Ast.Node.Index) !void {
        const tree = self.tree;
        const loop = tree.fullWhile(node) orelse return;
        if (loop.label_token != null or loop.payload_token != null) return;
        const reverse = tree.nodeTag(loop.ast.cond_expr) == .greater_than;
        if (!reverse and tree.nodeTag(loop.ast.cond_expr) != .less_than) return;
        const condition = tree.nodeData(loop.ast.cond_expr).node_and_node;
        if (tree.nodeTag(condition[0]) != .identifier) return;
        const counter_name = tree.tokenSlice(tree.nodeMainToken(condition[0]));
        const counter = self.name_to_local.get(counter_name) orelse return;
        if (self.locals.items[@intFromEnum(counter)].address_taken) return;
        var buffer: [2]Ast.Node.Index = undefined;
        var single: [1]Ast.Node.Index = undefined;
        const statements = self.blockStmtList(loop.ast.then_expr, &buffer, &single) orelse return;
        const first = tree.firstToken(loop.ast.then_expr);
        const last = tree.lastToken(loop.ast.then_expr);
        var token = first;
        while (token <= last) : (token += 1) {
            switch (tree.tokenTag(token)) {
                .keyword_break, .keyword_continue, .keyword_defer, .keyword_errdefer => return,
                else => {},
            }
        }
        var start: ?LocalId = null;
        if (reverse) {
            if (self.integerValue(condition[1]) != 0 or loop.ast.cont_expr != .none or statements.len < 2) return;
            if (!unitCounterStep(tree, statements[0], counter_name, .assign_sub)) return;
            const seed = precedingCounterSeed(tree, node, counter_name) orelse return;
            if (tree.nodeTag(seed) != .identifier) return;
            start = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(seed))) orelse return;
            const info = self.locals.items[@intFromEnum(start.?)];
            if (info.address_taken or start.? == counter or
                (self.paramTypeSpanOfLocal(start.?) == null and !self.immutable_locals.contains(start.?))) return;
            if (!info.is_unsigned) {
                const declaration = self.fill.visibleConstDecl(tree.nodeMainToken(seed), info.name) orelse return;
                const initializer = declaration.spans.?.init;
                if (initializer.last != initializer.first + 2 or
                    tree.tokenTag(initializer.first) != .identifier or
                    tree.tokenTag(initializer.first + 1) != .period or
                    !std.mem.eql(u8, tree.tokenSlice(initializer.last), "len")) return;
                const owner = self.name_to_local.get(tree.tokenSlice(initializer.first)) orelse return;
                const owner_info = self.locals.items[@intFromEnum(owner)];
                if (!owner_info.is_slice and owner_info.array_extent == null) return;
            }
            if (self.identifierMentions(info.name, first, last) != 0) return;
        } else {
            if (statements.len != 1) return;
            const continuation = loop.ast.cont_expr.unwrap() orelse return;
            if (!unitCounterStep(tree, continuation, counter_name, .assign_add)) return;
            const declaration = self.fill.declaredTypeSpanOfLocal(counter) orelse return;
            if (declaration.is_const or declaration.init_is_undefined) return;
            if (self.fill.comptimeIntTokens(declaration.init orelse return, 0) != 0) return;
            // A previous mutation invalidates the zero seed.
            var before = declaration.name_tok + 1;
            while (before < tree.firstToken(node)) : (before += 1) {
                if (tree.tokenTag(before) != .identifier or
                    !std.mem.eql(u8, tree.tokenSlice(before), counter_name)) continue;
                if (before > 0 and tree.tokenTag(before - 1) == .ampersand) return;
                // Only an errdefer prefix read may occur between seed and loop.
                if (tree.tokenTag(before + 1) != .r_bracket) return;
            }
        }
        // The only writes to the counter must be the proved unit step.
        token = first;
        while (token <= last) : (token += 1) {
            if (tree.tokenTag(token) != .identifier or
                !std.mem.eql(u8, tree.tokenSlice(token), counter_name)) continue;
            if (token > 0 and (tree.tokenTag(token - 1) == .ampersand or
                tree.tokenTag(token - 1) == .keyword_var or tree.tokenTag(token - 1) == .keyword_const)) return;
            if (reverse and token == tree.firstToken(statements[0])) continue;
            switch (tree.tokenTag(token + 1)) {
                .r_bracket, .r_paren, .comma, .equal_equal, .bang_equal => {},
                else => return,
            }
        }
        for (0..tree.nodes.len) |raw| {
            const expression: Ast.Node.Index = @enumFromInt(raw);
            if (tree.firstToken(expression) < first or tree.lastToken(expression) > last) continue;
            switch (tree.nodeTag(expression)) {
                .assign, .assign_add, .assign_sub, .assign_mul, .assign_div => {
                    if (!self.rhsIsDefined(tree.nodeData(expression).node_and_node[1])) return;
                },
                else => {},
            }
        }
        for (statements, 0..) |statement, ordinal| {
            if (reverse and ordinal == 0) continue;
            if (reverse and (tree.nodeTag(statement) == .assign or tree.nodeTag(statement) == .assign_mul)) {
                const operands = tree.nodeData(statement).node_and_node;
                if (!self.rhsIsDefined(operands[1])) return;
            }
            const write = self.indexedFillAssignWrite(statement, counter_name) orelse continue;
            const name = tree.tokenSlice(write.base_tok);
            const array = self.name_to_local.get(name) orelse continue;
            const info = self.locals.items[@intFromEnum(array)];
            const extent = info.array_extent orelse continue;
            if (array == counter or info.address_taken or self.identifierMentions(name, first, last) != 1) continue;
            const declaration = self.fill.declaredTypeSpanOfLocal(array) orelse continue;
            if (declaration.is_const or !declaration.init_is_undefined or
                declaration.name_tok >= tree.firstToken(node) or !self.rhsIsDefined(write.rhs)) continue;
            if (!reverse) {
                const bound = self.integerValue(condition[1]) orelse blk: {
                    const term = self.indexTerm(condition[1]);
                    if (term == .constant) break :blk term.constant;
                    continue;
                };
                if (bound != extent) continue;
                var inputs: [8]?LocalId = .{null} ** 8;
                var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
                if (!self.fillProofInputs(write.rhs, &inputs, &selected)) continue;
                if (!self.creditLoopFillStore(body_exit, write, inputs, selected)) continue;
                try self.appendStmt(exit, .{
                    .kind = .{ .array_complete = .{
                        .array = array,
                        .inputs = inputs,
                        .selected_inputs = selected,
                    } },
                    .pos = self.posOf(node),
                    .end_pos = self.endPosOf(node),
                });
            } else {
                var inputs: [8]?LocalId = .{null} ** 8;
                if (!self.valueInputs(write.rhs, &inputs)) continue;
                try self.appendStmt(exit, .{
                    .kind = .{ .array_prefix = .{ .array = array, .count = start.?, .inputs = inputs } },
                    .pos = self.posOf(node),
                    .end_pos = self.endPosOf(node),
                });
            }
        }
    }

    fn unitCounterStep(tree: *const Ast, node: Ast.Node.Index, name: []const u8, tag: Ast.Node.Tag) bool {
        if (tree.nodeTag(node) != tag) return false;
        const operands = tree.nodeData(node).node_and_node;
        if (tree.nodeTag(operands[0]) != .identifier or tree.nodeTag(operands[1]) != .number_literal) return false;
        return std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(operands[0])), name) and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(operands[1])), "1");
    }

    /// Require the immediately preceding sibling to seed the countdown.
    fn precedingCounterSeed(tree: *const Ast, loop_node: Ast.Node.Index, name: []const u8) ?Ast.Node.Index {
        for (0..tree.nodes.len) |raw| {
            const block: Ast.Node.Index = @enumFromInt(raw);
            switch (tree.nodeTag(block)) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => {},
                else => continue,
            }
            var buffer: [2]Ast.Node.Index = undefined;
            const statements = blockStmts(tree, block, &buffer);
            for (statements, 0..) |statement, ordinal| {
                if (statement != loop_node or ordinal == 0) continue;
                const previous = statements[ordinal - 1];
                if (tree.fullVarDecl(previous)) |declaration| {
                    if (!std.mem.eql(u8, tree.tokenSlice(declaration.ast.mut_token + 1), name)) return null;
                    return declaration.ast.init_node.unwrap();
                }
                if (tree.nodeTag(previous) != .assign) return null;
                const operands = tree.nodeData(previous).node_and_node;
                if (tree.nodeTag(operands[0]) != .identifier or
                    !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(operands[0])), name)) return null;
                return operands[1];
            }
        }
        return null;
    }

    /// A canonical countdown helper defines only [0, source.len). This hook
    /// runs after successful calls; it never certifies an error/early exit.
    fn emitSuccessfulCountdownPrefix(self: *Builder, block: BlockId, call: Ast.Node.Index) !void {
        const tree = self.tree;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const full_call = tree.fullCall(&call_buffer, call) orelse return;
        const cache = self.cache orelse return;
        const actual = self.queryOrUnknown(file_cache.FileCache.ActualCallSummary, cache.actualCallSummaryAt(fresh_storage.calleeQueryToken(tree, full_call), self.integerResolutionFrame())) orelse return;
        const source_tree = actual.callee.tree;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = source_tree.fullFnProto(&proto_buffer, actual.callee.declaration) orelse return;
        const body = tokens.bodyOf(source_tree, actual.callee.declaration) orelse return;
        var statement_buffer: [2]Ast.Node.Index = undefined;
        const statements = blockStmts(source_tree, body, &statement_buffer);
        var parameters = proto.iterate(source_tree);
        var output_index: u32 = 0;
        while (parameters.next()) |output| : (output_index += 1) {
            const output_token = output.name_token orelse continue;
            const output_type = output.type_expr orelse continue;
            const type_first = source_tree.firstToken(output_type);
            const type_last = source_tree.lastToken(output_type);
            if (source_tree.tokenTag(type_first) != .asterisk or
                type_first + 4 > type_last or source_tree.tokenTag(type_first + 1) != .l_bracket or
                source_tree.tokenTag(type_last) != .identifier or
                !unsignedTypeName(source_tree.tokenSlice(type_last))) continue;
            const output_name = source_tree.tokenSlice(output_token);
            var loop_node: ?Ast.Node.Index = null;
            for (statements) |statement| {
                if (source_tree.fullWhile(statement) == null) continue;
                if (loop_node != null) {
                    loop_node = null;
                    break;
                }
                loop_node = statement;
            }
            // Only two scalar declarations and an optional rejecting guard may
            // precede the loop; successful early returns cannot qualify.
            if (statements.len < 3 or statements.len > 4 or
                statements[statements.len - 1] != (loop_node orelse continue)) continue;
            const node = loop_node orelse continue;
            const loop = source_tree.fullWhile(node).?;
            if (loop.label_token != null or loop.payload_token != null or loop.ast.cont_expr != .none or
                loop.ast.else_expr != .none or source_tree.nodeTag(loop.ast.cond_expr) != .greater_than) continue;
            const condition = source_tree.nodeData(loop.ast.cond_expr).node_and_node;
            if (source_tree.nodeTag(condition[0]) != .identifier or source_tree.nodeTag(condition[1]) != .number_literal or
                !std.mem.eql(u8, source_tree.tokenSlice(source_tree.nodeMainToken(condition[1])), "0")) continue;
            const axis = source_tree.tokenSlice(source_tree.nodeMainToken(condition[0]));
            const seed = precedingCounterSeed(source_tree, node, axis) orelse continue;
            const seed_first = source_tree.firstToken(seed);
            if (source_tree.lastToken(seed) != seed_first + 2 or source_tree.tokenTag(seed_first) != .identifier or
                source_tree.tokenTag(seed_first + 1) != .period or
                !std.mem.eql(u8, source_tree.tokenSlice(seed_first + 2), "len")) continue;
            const source_name = source_tree.tokenSlice(seed_first);
            var source_parameters = proto.iterate(source_tree);
            var source_index: u32 = 0;
            var found_source = false;
            while (source_parameters.next()) |parameter| : (source_index += 1) {
                const name_token = parameter.name_token orelse continue;
                if (!std.mem.eql(u8, source_tree.tokenSlice(name_token), source_name)) continue;
                const parameter_type = parameter.type_expr orelse break;
                const parameter_first = source_tree.firstToken(parameter_type);
                if (source_tree.tokenTag(parameter_first) != .l_bracket or
                    source_tree.tokenTag(parameter_first + 1) != .r_bracket or
                    source_tree.tokenTag(parameter_first + 2) != .keyword_const or
                    !unsignedTypeName(source_tree.tokenSlice(source_tree.lastToken(parameter_type)))) break;
                found_source = true;
                break;
            }
            if (!found_source) continue;
            var inner_buffer: [2]Ast.Node.Index = undefined;
            const inner = blockStmts(source_tree, loop.ast.then_expr, &inner_buffer);
            if (inner.len != 3 or !unitCounterStep(source_tree, inner[0], axis, .assign_sub)) continue;
            const write = counterFillAssignWriteIn(source_tree, inner[1]) orelse continue;
            if (!std.mem.eql(u8, source_tree.tokenSlice(write.base_tok), output_name) or
                !std.mem.eql(u8, source_tree.tokenSlice(write.base_tok + 2), axis) or
                source_tree.nodeTag(write.rhs) != .identifier) continue;
            const stride = source_tree.tokenSlice(source_tree.nodeMainToken(write.rhs));
            // The scalar recurrence cannot modify the counter or output.
            const update_tag = source_tree.nodeTag(inner[2]);
            if (update_tag != .assign and update_tag != .assign_mul) continue;
            const update = source_tree.nodeData(inner[2]).node_and_node;
            if (source_tree.nodeTag(update[0]) != .identifier or
                !std.mem.eql(u8, source_tree.tokenSlice(source_tree.nodeMainToken(update[0])), stride)) continue;
            var seeded_stride = false;
            var safe = true;
            var output_mentions: usize = 0;
            var axis_mentions: usize = 0;
            var token = source_tree.firstToken(body);
            const body_last = source_tree.lastToken(body);
            while (token <= body_last) : (token += 1) {
                switch (source_tree.tokenTag(token)) {
                    .keyword_break, .keyword_continue, .keyword_defer, .keyword_errdefer => {
                        safe = false;
                        break;
                    },
                    .keyword_return => {
                        if (token + 2 > body_last or source_tree.tokenTag(token + 1) != .keyword_error or
                            source_tree.tokenTag(token + 2) != .period)
                        {
                            safe = false;
                            break;
                        }
                    },
                    .identifier => {
                        const name = source_tree.tokenSlice(token);
                        if (std.mem.eql(u8, name, "undefined")) {
                            safe = false;
                            break;
                        }
                        if (std.mem.eql(u8, name, output_name)) output_mentions += 1;
                        if (std.mem.eql(u8, name, axis)) {
                            axis_mentions += 1;
                            if (token > 0 and source_tree.tokenTag(token - 1) == .ampersand) safe = false;
                        }
                        if (std.mem.eql(u8, name, source_name) and token > 0 and
                            source_tree.tokenTag(token - 1) == .ampersand) safe = false;
                    },
                    else => {},
                }
            }
            // Declaration, comparison, decrement, store and recurrence read.
            if (!safe or output_mentions != 1 or axis_mentions != 5) continue;
            for (statements) |statement| {
                const declaration = source_tree.fullVarDecl(statement) orelse continue;
                if (!std.mem.eql(u8, source_tree.tokenSlice(declaration.ast.mut_token + 1), stride)) continue;
                const init = declaration.ast.init_node.unwrap() orelse continue;
                seeded_stride = source_tree.nodeTag(init) == .number_literal and
                    source_tree.firstToken(statement) < source_tree.firstToken(node);
            }
            if (!seeded_stride) continue;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const source_argument = self.queryOrUnknown(Ast.Node.Index, actual.callArgumentFor(cache, &argument_buffer, source_index)) orelse continue;
            const output_argument = self.queryOrUnknown(Ast.Node.Index, actual.callArgumentFor(cache, &argument_buffer, output_index)) orelse continue;
            if (tree.nodeTag(source_argument) != .identifier or tree.nodeTag(output_argument) != .address_of) continue;
            const source_local = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(source_argument))) orelse continue;
            if (!self.locals.items[@intFromEnum(source_local)].is_slice) continue;
            const destination = tree.nodeData(output_argument).node;
            if (tree.nodeTag(destination) != .identifier) continue;
            const array = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(destination))) orelse continue;
            const extent = self.locals.items[@intFromEnum(array)].array_extent orelse continue;
            const count = try self.appendLocal(.{
                .name = "$countdown-prefix",
                .decl_pos = self.posOf(call),
                .is_unsigned = true,
            });
            try self.appendStmt(block, .{
                .kind = .{ .decl = .{ .local = count, .init_kind = .plain } },
                .pos = self.posOf(call),
                .end_pos = self.endPosOf(call),
            });
            try self.appendStmt(block, .{
                .kind = .{ .compare_assume = .{
                    .lhs = .{ .local = .{ .local = count } },
                    .rhs = .{ .field = .{ .parent = source_local, .name = "len", .is_unsigned = true } },
                    .op = .eq,
                } },
                .pos = self.posOf(call),
                .end_pos = self.endPosOf(call),
            });
            // A successful exhaustive countdown performed every indexed store.
            // Its source count therefore fits the actual destination; this
            // bounds later selections without certifying any suffix bytes.
            try self.appendStmt(block, .{
                .kind = .{ .compare_assume = .{
                    .lhs = .{ .field = .{ .parent = source_local, .name = "len", .is_unsigned = true } },
                    .rhs = .{ .constant = extent },
                    .op = .le,
                } },
                .pos = self.posOf(call),
                .end_pos = self.endPosOf(call),
            });
            var inputs: [8]?LocalId = .{null} ** 8;
            inputs[0] = source_local;
            try self.appendStmt(block, .{
                .kind = .{ .array_prefix = .{ .array = array, .count = count, .inputs = inputs } },
                .pos = self.posOf(call),
                .end_pos = self.endPosOf(call),
            });
        }
    }

    /// `for (input) |x| BODY [else ELSE]` — structurally identical to a
    /// while loop for our purposes (header decides each iteration, body
    /// back-edges to header).  We don't model the iteration variable's
    /// origin (would need to track input's element-lifetime per item);
    /// the iterator binding gets registered as a fresh local with .plain
    /// init so subsequent uses are conservative.
    /// If the fn being lowered is a destructor (finalize / deinit
    /// / destroy) of a type that has a heap-creator method
    /// elsewhere in the same file AND this fn's @takes annotation
    /// doesn't claim it frees self, return the type's name.  Used
    /// by `lowerFunctionBody` to emit a leak_warning stmt at body
    /// start.  Returns null in all other cases.
    /// True iff the destructor body is empty (`{}`) or contains
    /// only discard statements (`_ = self;`).  Such bodies can't
    /// free `self` regardless — the leak warning is meaningless.
    /// Used by `leakyDestructorTypeName` to suppress on no-op
    /// finalize callbacks registered with JSC.
    fn destructorBodyIsTrivial(self: *const Builder) bool {
        if (self.fn_body_first == 0) return true;
        const tags = self.tree.tokens.items(.tag);
        const first = self.fn_body_first;
        const last = self.fn_body_last;
        if (first >= last) return true;
        // body_first is `{`, body_last is `}`.  Empty body: nothing
        // between (just `{` immediately followed by `}`).
        if (first + 1 == last) return true;
        // Walk statements; require each to be `_ = <expr>;`.
        var t: Ast.TokenIndex = first + 1;
        while (t < last) {
            if (tags[t] != .identifier) return false;
            if (!std.mem.eql(u8, self.tree.tokenSlice(t), "_")) return false;
            if (t + 1 >= last or tags[t + 1] != .equal) return false;
            var depth: u32 = 0;
            var k = t + 2;
            while (k < last) : (k += 1) {
                switch (tags[k]) {
                    .l_paren, .l_brace, .l_bracket => depth += 1,
                    .r_paren, .r_brace, .r_bracket => {
                        if (depth == 0) return false;
                        depth -= 1;
                    },
                    .semicolon => if (depth == 0) break,
                    else => {},
                }
            }
            if (k >= last or tags[k] != .semicolon) return false;
            t = k + 1;
        }
        return true;
    }

    /// True iff the destructor's own body releases an `arena`-named
    /// field via `<self|this>.arena.deinit(...)`.  Heuristic for
    /// "self is housed in the arena it manages" — the arena's
    /// release transitively frees `self`, so the leak rule's
    /// `allocator.destroy(self)` requirement is moot.
    fn destructorReleasesOwnArena(self: *const Builder) bool {
        if (self.fn_body_first == 0) return false;
        const tags = self.tree.tokens.items(.tag);
        var t: Ast.TokenIndex = self.fn_body_first;
        while (t + 4 <= self.fn_body_last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            const s = self.tree.tokenSlice(t);
            if (!std.mem.eql(u8, s, "self") and !std.mem.eql(u8, s, "this")) continue;
            if (tags[t + 1] != .period) continue;
            if (tags[t + 2] != .identifier) continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(t + 2), "arena")) continue;
            if (tags[t + 3] != .period) continue;
            if (tags[t + 4] != .identifier) continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(t + 4), "deinit")) continue;
            return true;
        }
        return false;
    }

    /// True iff the first parameter of this fn is a `*const T` receiver
    /// (possibly with a leading `?`).  Such a receiver CANNOT call
    /// `alloc.destroy(self)` — the function only cleans up owned fields;
    /// the caller must call `alloc.destroy(instance)` itself.
    fn destructorIsConstReceiver(self: *const Builder) bool {
        const proto = self.fn_proto orelse return false;
        var it = proto.iterate(self.tree);
        const p0 = it.next() orelse return false;
        const te = p0.type_expr orelse return false;
        const tags = self.tree.tokens.items(.tag);
        const first = self.tree.firstToken(te);
        const last = self.tree.lastToken(te);
        var t: Ast.TokenIndex = first;
        while (t + 1 <= last) : (t += 1) {
            switch (tags[t]) {
                .question_mark => continue,
                .asterisk => return t + 1 <= last and tags[t + 1] == .keyword_const,
                else => return false,
            }
        }
        return false;
    }

    /// True iff the destructor body contains `<param0>.* = undefined;`
    /// — the canonical Zig value-type deinit pattern.  Such structs are
    /// not heap-allocated by their caller; the heap-leak rule's
    /// `allocator.destroy(self)` requirement doesn't apply.
    fn destructorHasSelfUndefined(self: *const Builder) bool {
        const proto = self.fn_proto orelse return false;
        const first = self.fn_body_first;
        const last = self.fn_body_last;
        if (first == 0 or last == 0) return false;
        var it = proto.iterate(self.tree);
        const p0 = it.next() orelse return false;
        const name_tok = p0.name_token orelse return false;
        const param_name = self.tree.tokenSlice(name_tok);
        const tags = self.tree.tokens.items(.tag);
        // Scan for: <param_name> .* = undefined
        // `.*` is a SINGLE period_asterisk token in the Zig tokenizer.
        var t = first;
        while (t + 4 <= last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(t), param_name)) continue;
            if (tags[t + 1] != .period_asterisk) continue;
            if (tags[t + 2] != .equal) continue;
            if (tags[t + 3] != .identifier) continue;
            if (!std.mem.eql(u8, self.tree.tokenSlice(t + 3), "undefined")) continue;
            return true;
        }
        return false;
    }

    /// True iff `type_name`'s body declares a bun refcount mixin
    /// — `RefCount(...)` or `ThreadSafeRefCount(...)`.  Used by
    /// `leakyDestructorTypeName` to suppress the leak fire on
    /// types whose destruction goes through `deref()` rather than
    /// the finalize callback.  Token-scans the type body for the
    /// canonical declaration shape.
    /// True iff the type has a method with the canonical
    /// singleton-accessor shape:
    ///   `pub [inline] fn get() *Self`        (or `*<TypeName>`)
    ///   `pub [inline] fn instance() *Self`
    ///   `pub [inline] fn getOrNull() ?*Self`
    /// — zero-parameter methods that return a pointer to the type.
    /// Detection is purely token-walk over the type's body so it
    /// works for file-as-struct types too.
    fn typeHasSingletonAccessor(self: *Builder, type_name: []const u8) bool {
        const cache = self.cache orelse return false;
        const model = self.modelOrNull(cache) orelse return false;
        const ti = model.findType(type_name) orelse return false;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        // The last token index is already a `u32` (`Ast.TokenIndex`), so
        // the method-scan bound needs no conversion of its own.
        const last_tok = tree.lastToken(.root);
        for (ti.methods) |m| {
            // Canonical accessors are parameterless.  Other names
            // (\`initGlobal\`, \`init<X>\`) may take args but still
            // return \`*Self\` and stash into a top-level var — they
            // signal singleton ownership too.  We accept any method
            // whose name matches the singleton convention AND whose
            // return type is \`*Self\` / \`*<TypeName>\` / \`*@This()\`.
            const is_singleton_name =
                std.mem.eql(u8, m.name, "get") or
                std.mem.eql(u8, m.name, "getOrNull") or
                std.mem.eql(u8, m.name, "instance") or
                std.mem.eql(u8, m.name, "initGlobal") or
                std.mem.eql(u8, m.name, "getInstance") or
                std.mem.eql(u8, m.name, "global");
            if (!is_singleton_name) continue;
            // Walk past the method's param list to find the return type.
            const name_tok = m.name_token;
            if (name_tok + 2 >= tags.len) continue;
            if (tags[name_tok + 1] != .l_paren) continue;
            // Find the matching `)`.
            const close = tokens.matchParen(tags, name_tok + 1, last_tok) orelse continue;
            var t: Ast.TokenIndex = close + 1;
            if (t < tags.len and tags[t] == .question_mark) t += 1;
            if (t >= tags.len or tags[t] != .asterisk) continue;
            t += 1;
            if (t >= tags.len) continue;
            switch (tags[t]) {
                .identifier => {
                    const ret_name = tree.tokenSlice(t);
                    if (std.mem.eql(u8, ret_name, type_name)) return true;
                    if (std.mem.eql(u8, ret_name, "Self")) return true;
                },
                .builtin => {
                    if (std.mem.eql(u8, tree.tokenSlice(t), "@This")) return true;
                },
                else => {},
            }
        }
        return false;
    }

    fn typeBodyHasRefCountMixin(self: *Builder, type_name: []const u8) bool {
        const cache = self.cache orelse return false;
        const model = self.modelOrNull(cache) orelse return false;
        const ti = model.findType(type_name) orelse return false;
        const tags = self.tree.tokens.items(.tag);
        if (ti.body_first >= ti.body_last) return false;
        var t: Ast.TokenIndex = ti.body_first;
        while (t + 1 <= ti.body_last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (tags[t + 1] != .l_paren) continue;
            const s = self.tree.tokenSlice(t);
            if (std.mem.eql(u8, s, "RefCount") or
                std.mem.eql(u8, s, "ThreadSafeRefCount")) return true;
        }
        return false;
    }

    fn leakyDestructorTypeName(self: *Builder) ?[]const u8 {
        const tree = self.tree;
        const proto = self.fn_proto orelse return null;
        const name_tok = proto.name_token orelse return null;
        const fn_name = tree.tokenSlice(name_tok);
        const is_destructor = std.mem.eql(u8, fn_name, "finalize") or
            std.mem.eql(u8, fn_name, "deinit") or
            std.mem.eql(u8, fn_name, "destroy");
        if (!is_destructor) return null;

        // Must have a containing type (self-typed first param resolved
        // by Builder.self_type at fn lowering setup).
        const ct = self.self_type orelse return null;

        // A create spelling alone does not imply self-owned heap storage:
        // the cached summary must authenticate SDK create and exclude known
        // arena/buffer backing, independently of the instance's field graph.
        const cache = self.cache orelse return null;
        const creator_found = cache.anyMethodAllocatesSelf(ct) catch |err| {
            self.noteResolutionError(err);
            return null;
        };
        if (!creator_found) return null;

        // Two-stage cleanup pattern: when fn is `deinit` / `finalize`
        // AND the type ALSO defines a separate `destroy` method,
        // the convention is `destroy()` does `deinit(); alloc.destroy(self);`.
        // Don't fire on the inner `deinit` — it's deliberately
        // partial.  The leak check naturally targets `destroy` (if
        // even there) instead.
        if (!std.mem.eql(u8, fn_name, "destroy")) {
            const has_destroy = cache.typeHasMethod(ct, "destroy") catch |err| err_blk: {
                self.noteResolutionError(err);
                break :err_blk false;
            };
            if (has_destroy) return null;
        }
        // Refcount-managed lifecycle: types with bun's refcount
        // mixin follow `ref()` / `deref()`; the destructor is
        // chained from `deref()` when the count hits zero, not
        // from `deinit` / `finalize`.  Detect via the mixin's
        // canonical declaration tokens (`RefCount(` /
        // `ThreadSafeRefCount(`) in the type body.  Methods are
        // declared as `pub const ref = RefCount.ref;` aliases —
        // not `fn` decls — so `hasMethod` misses them.
        if (self.typeBodyHasRefCountMixin(ct)) return null;
        // Self-housed-in-arena: when the destructor body calls
        // `<self>.arena.deinit()`, the type instance very likely
        // lives inside that arena (a Bun-wide pattern: parser, FS
        // router, number renamer).  Arena.deinit releases the
        // entire arena pool, so `self` is freed transitively —
        // no explicit `allocator.destroy(self)` needed.
        if (self.destructorReleasesOwnArena()) return null;
        // Empty / discard-only destructor: `pub fn finalize(_:
        // *T) callconv(.c) void {}` is a no-op intentionally —
        // the type's cleanup happens via a different path (JSC
        // GC, manual destroy at a different site, etc.).  An
        // empty body can't free `self` because it can't do
        // anything; the rule firing is shoutness without
        // value.
        if (self.destructorBodyIsTrivial()) return null;
        // Const-receiver pattern: `pub fn deinit(self: *const T, …)`.
        // A `*const` receiver cannot call `alloc.destroy(self)` in the
        // conventional way — such destructors only clean up owned FIELDS;
        // the caller is expected to call `alloc.destroy(instance)` itself.
        // This is the two-step cleanup pattern (deinit fields → caller
        // destroys allocation).  The heap-leak diagnostic does not apply.
        if (self.destructorIsConstReceiver()) return null;
        // Singleton-accessor pattern: types with `pub [inline] fn
        // get() *Self` (or `instance()` / `getOrNull()`) returning a
        // pointer to the type are conventional process-global
        // singletons (the canonical `VirtualMachine.get()` shape).
        // Such types are heap-allocated ONCE at startup and live
        // until process exit; the destructor exists for orderly
        // subsystem teardown but doesn't free `self` because there's
        // no place to return memory TO.  The rule's prescription
        // ("add bun.destroy(self)") doesn't apply.
        if (self.typeHasSingletonAccessor(ct)) return null;

        // The destructor must NOT have @takes(self) — that would
        // mean it does free self, no leak.
        if (self.cache) |c| {
            if (self.queryOrUnknown(*const fn_summary.FnSummary, c.summaryByMethod(ct, fn_name))) |s| {
                if (s.takes_ownership_of) |idx| if (idx == 0) return null;
            }
        }
        // Value-type deinit: `self.* = undefined;` (or `this.* =
        // undefined;`) at any point in the body is the canonical Zig
        // idiom for a stack-allocated (or externally-owned) struct that
        // zeroes itself in debug builds.  Such types are never freed via
        // `allocator.destroy(self)` — deallocation happens at the call
        // site or not at all.  The heap-leak rule fires because another
        // method uses `alloc.create(T)` for sub-instances (like Set's
        // leader sub-sets), but the outer struct is a value type.
        if (self.destructorHasSelfUndefined()) return null;
        // Summary lookup misses comptime-generated types (anonymous
        // structs returned from type-factory fns).  Fall back to a
        // direct body scan: if the body calls `.destroy(first-param)`
        // or `.free(first-param)`, the destructor does free self.
        if (self.bodyFreesFirstParam()) return null;
        return ct;
    }

    /// Returns true iff the fn body contains a direct
    /// `.free(<p0>)` / `.destroy(<p0>)` call where `p0` is the
    /// first parameter's name.  Used as a fallback when the
    /// summary-lookup path can't find the type (comptime-generated
    /// types not present in the file model).
    fn bodyFreesFirstParam(self: *Builder) bool {
        const proto = self.fn_proto orelse return false;
        const first = self.fn_body_first;
        const last = self.fn_body_last;
        if (first == 0 or last == 0) return false;
        // Get the first parameter's name.
        var it = proto.iterate(self.tree);
        const p0 = it.next() orelse return false;
        const name_tok = p0.name_token orelse return false;
        const param_name = self.tree.tokenSlice(name_tok);
        const tags = self.tree.tokens.items(.tag);
        var t = first;
        while (t + 3 <= last) : (t += 1) {
            if (tags[t] != .period) continue;
            if (tags[t + 1] != .identifier) continue;
            const method = self.tree.tokenSlice(t + 1);
            const is_free = std.mem.eql(u8, method, "free") or
                std.mem.eql(u8, method, "destroy");
            if (!is_free) continue;
            if (tags[t + 2] != .l_paren) continue;
            if (tags[t + 3] != .identifier) continue;
            // Guard: arg followed by `.` means it's a field access —
            // not freeing the param itself.
            if (t + 4 <= last and tags[t + 4] == .period) continue;
            if (std.mem.eql(u8, self.tree.tokenSlice(t + 3), param_name)) return true;
        }
        return false;
    }

    /// For each `for (input_i) |capture_i|` pair, if input_i is
    /// `<container_ident>.<field>` AND capture_i is by-pointer
    /// (preceded by `*` inside the payload), set
    /// `capture.from_container = container_local`.
    ///
    /// Pure token-walk: payload tokens are `|`, optional `*`,
    /// ident, [optional `,` and second ident pair], `|`.  Walk
    /// these alongside `for_data.ast.inputs` to align pairs.
    fn markInteriorCaptures(self: *Builder, for_data: Ast.full.For, body: BlockId) void {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        // Walk payload tokens collecting (is_pointer, capture_name)
        // pairs in input order.  Two passes happen here:
        //   1. for-loop interior-pointer marker (from_container) —
        //      `for (entries.items) |*r|` records that `r` borrows
        //      from `entries`.  Used by interior_pointer_destroy.
        //   2. ZLS-derived capture type — `for (xs) |x|` resolves
        //      `x`'s container type via ZLS on the input.  Without
        //      this, captures get type_name=null and method-on-
        //      capture lookups fall back to bare-name.
        var pt = for_data.payload_token;
        var input_idx: usize = 0;
        var is_ptr = false;
        while (pt < tags.len) : (pt += 1) {
            switch (tags[pt]) {
                .pipe => return, // closing `|`
                .asterisk => is_ptr = true,
                .identifier => {
                    if (input_idx >= for_data.ast.inputs.len) return;
                    const input = for_data.ast.inputs[input_idx];
                    const name = tree.tokenSlice(pt);
                    input_idx += 1;
                    const is_underscore = std.mem.eql(u8, name, "_");
                    const was_ptr = is_ptr;
                    is_ptr = false;
                    if (is_underscore) continue;
                    const capture_local = self.name_to_local.get(name) orelse continue;
                    if (!was_ptr) {
                        const capture = &self.locals.items[@intFromEnum(capture_local)];
                        if (for_data.inline_token != null and capture.decl_pos.byte == self.posOfToken(pt).byte) {
                            if (self.fill.enumMetaFieldsTypeSpan(.{
                                .first = tree.firstToken(input),
                                .last = tree.lastToken(input),
                            })) |enum_type| {
                                if (self.fill.enumFieldsCount(enum_type, 0) != null) {
                                    capture.is_enum_field_capture = true;
                                    capture.tracks_array_payload = true;
                                }
                            }
                        }
                        const is_range = tree.nodeTag(input) == .for_range;
                        if (is_range) {
                            capture.is_unsigned = true;
                            capture.tracks_scalar_value = true;
                            self.integer_domains.items[@intFromEnum(capture_local)] = .{ .kind = .unsigned_unbounded };
                        } else if (self.integerResolutionFrame()) |frame| {
                            var element = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(input));
                            if (element) |ty| {
                                if (frame.resolver.pointerSize(ty) == .one) {
                                    element = frame.resolver.childType(ty);
                                }
                            }
                            if (element) |ty| element = frame.resolver.childType(ty);
                            if (element) |ty| {
                                const normalized = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(ty));
                                if (normalized) |actual| switch (frame.resolver.typeTag(actual) orelse .@"opaque") {
                                    .int => {
                                        const index = actual.ipIndex() orelse continue;
                                        const info = frame.resolver.ctx.ip.intInfo(index, @import("builtin").target);
                                        capture.is_unsigned = info.signedness == .unsigned;
                                        capture.tracks_scalar_value = true;
                                        self.integer_domains.items[@intFromEnum(capture_local)] =
                                            integerDomain(.{ .signed = info.signedness == .signed, .bits = info.bits });
                                    },
                                    .float, .bool, .@"enum", .comptime_int, .comptime_float => capture.tracks_scalar_value = true,
                                    .@"struct", .@"union", .array => capture.tracks_array_payload = true,
                                    else => {},
                                };
                            }
                        }
                        var source = input;
                        if (tree.nodeTag(source) == .address_of) source = tree.nodeData(source).node;
                        if (!is_range and tree.nodeTag(source) == .identifier) {
                            if (self.indexLocalAt(tree.nodeMainToken(source))) |owner| {
                                const info = self.locals.items[@intFromEnum(owner)];
                                if (!info.is_pointer and (info.is_array or info.is_slice)) {
                                    for (self.block_stmts.items[@intFromEnum(body)].items) |*statement| {
                                        if (statement.kind == .reset_capture and statement.kind.reset_capture.local == capture_local)
                                            statement.kind.reset_capture.value_source = owner;
                                    }
                                }
                            }
                        }
                    }

                    // An immutable pointer capture addresses one element,
                    // not the whole array. Keep its storage owner so later
                    // opaque writes (including copied aliases) revoke it.
                    if (was_ptr and tree.nodeTag(input) == .address_of) {
                        const operand = tree.nodeData(input).node;
                        if (tree.nodeTag(operand) == .identifier) {
                            const owner = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(operand)));
                            if (owner) |array| {
                                const info = self.locals.items[@intFromEnum(array)];
                                if (info.is_array and !info.is_pointer and !info.is_slice) {
                                    const capture = &self.locals.items[@intFromEnum(capture_local)];
                                    capture.is_pointer = true;
                                    capture.frame_borrow_origin = array;
                                    capture.array_element_owner = array;
                                    self.locals.items[@intFromEnum(array)].address_taken = true;
                                }
                            }
                        }
                    }

                    // (1) Interior-pointer marker (by-pointer capture
                    // over `<container>.<field>`).
                    if (was_ptr and tree.nodeTag(input) == .field_access) {
                        const fa = tree.nodeData(input).node_and_token;
                        const recv = fa[0];
                        if (tree.nodeTag(recv) == .identifier) {
                            const recv_name = tree.tokenSlice(tree.nodeMainToken(recv));
                            if (self.name_to_local.get(recv_name)) |container| {
                                self.locals.items[@intFromEnum(capture_local)].from_container = container;
                            }
                        }
                    }

                    // (2) ZLS-derived capture type.  resolveTypeOfNode
                    // on the input gives the slice/array; the helper
                    // strips pointer/optional/array wrappers down to
                    // the container — for `[]Item` we get "Item",
                    // which is the right type for both `|x|` and
                    // `|*x|` captures (the `*` is just a borrow modifier).
                    if (self.zls) |z| {
                        if (self.queryOrUnknown([]const u8, z.typeReferenceOfNode(input))) |ty| {
                            const li = &self.locals.items[@intFromEnum(capture_local)];
                            if (li.type_name == null) li.type_name = ty;
                        }
                    }
                },
                .comma => {}, // separator between captures
                else => {},
            }
        }
    }

    /// Iteration selects a defined usize in the evaluated input's extent.
    /// Mutable runtime bounds need a snapshot, so they cannot supply facts here.
    fn immutableIterationTerm(self: *Builder, term: cfg_types.IndexTerm) bool {
        const local = switch (term) {
            .constant => return true,
            .local => |value| value.local,
            .field => |value| value.parent,
            .unknown => return false,
        };
        const info = self.locals.items[@intFromEnum(local)];
        return !info.address_taken and
            (self.immutable_locals.contains(local) or self.paramTypeSpanOfLocal(local) != null);
    }

    fn iterationLength(self: *Builder, node: Ast.Node.Index) cfg_types.IndexTerm {
        if (self.tree.nodeTag(node) == .address_of)
            return self.iterationLength(self.tree.nodeData(node).node);
        if (self.tree.nodeTag(node) != .identifier) return .unknown;
        const local = self.indexLocalAt(self.tree.nodeMainToken(node)) orelse return .unknown;
        const info = self.locals.items[@intFromEnum(local)];
        if (info.array_extent) |extent| return .{ .constant = extent };
        if (!info.is_slice or !self.immutableIterationTerm(.{ .local = .{ .local = local } })) return .unknown;
        return .{ .field = .{ .parent = local, .name = "len", .is_unsigned = true } };
    }

    fn emitForIndexBounds(self: *Builder, loop: Ast.full.For, body: BlockId) !void {
        const tree = self.tree;
        var capture = loop.payload_token;
        for (loop.ast.inputs) |input| {
            if (tree.tokenTag(capture) == .asterisk) capture += 1;
            if (tree.tokenTag(capture) != .identifier) return;
            const token = capture;
            capture += 1;
            if (tree.tokenTag(capture) == .comma) capture += 1;
            if (self.staticScalarArrayInput(input)) {
                if (self.indexLocalAt(token)) |local|
                    self.locals.items[@intFromEnum(local)].tracks_scalar_value = true;
            }
            if (tree.nodeTag(input) != .for_range) continue;
            const counter = self.indexLocalAt(token) orelse continue;
            const range = tree.nodeData(input).node_and_opt_node;
            const start = self.indexTerm(range[0]);
            var end: cfg_types.IndexTerm = .unknown;
            if (range[1].unwrap()) |bound| {
                end = self.indexTerm(bound);
            } else {
                for (loop.ast.inputs) |collection| {
                    if (tree.nodeTag(collection) == .for_range) continue;
                    end = self.iterationLength(collection);
                    if (end != .unknown) break;
                }
            }
            const index: cfg_types.IndexTerm = .{ .local = .{ .local = counter } };
            if (self.immutableIterationTerm(start)) try self.appendStmt(body, .{
                .kind = .{ .compare_assume = .{ .lhs = index, .rhs = start, .op = .ge } },
                .pos = self.posOfToken(token),
                .end_pos = self.posOfTokenEnd(token),
            });
            if (self.immutableIterationTerm(end)) try self.appendStmt(body, .{
                .kind = .{ .compare_assume = .{ .lhs = index, .rhs = end, .op = .lt } },
                .pos = self.posOfToken(token),
                .end_pos = self.posOfTokenEnd(token),
            });
        }
    }

    fn lowerFor(self: *Builder, for_node: Ast.Node.Index, cur: *BlockId) !void {
        const loop = self.tree.fullFor(for_node).?;
        for (loop.ast.inputs) |input| try self.emitUsesInExpr(input, cur.*, null);
        const header = try self.newBlock();
        const body = try self.newBlock();
        const merge = try self.newBlock();
        const natural_exit = if (loop.ast.else_expr != .none) try self.newBlock() else merge;
        try self.addEdge(cur.*, header);
        try self.addEdge(header, body);
        try self.addEdge(header, natural_exit);
        try self.loop_stack.append(self.gpa, .{
            .continue_to = header,
            .merge = merge,
            .defer_depth = self.deferred.items.len,
            .label = if (loop.label_token) |token| self.tree.tokenSlice(token) else null,
        });
        const pre_capture_len = try self.localsLen();
        errdefer self.restoreLocalNames(pre_capture_len, self.tree.firstToken(for_node));
        try self.registerCapturesWith(loop.payload_token, body);
        self.markInteriorCaptures(loop, body);
        try self.emitForIndexBounds(loop, body);
        var body_cur = body;
        switch (self.tree.nodeTag(loop.ast.then_expr)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                if (self.blockLabelToken(loop.ast.then_expr) == null) {
                    try self.lowerBlockContents(loop.ast.then_expr, &body_cur);
                } else {
                    try self.lowerStmt(loop.ast.then_expr, &body_cur);
                }
            },
            else => try self.lowerStmt(loop.ast.then_expr, &body_cur),
        }
        // Resolved after the body has been lowered, so every binding the
        // body introduces — the payload capture AND any local declared
        // inside it — is live in `name_to_local`.  That is what lets the
        // proof see a body-local shadow, or a body-local `undefined`
        // seed on the value being stored, as the same binding the write
        // actually reaches, instead of resolving both against an outer
        // name. Still ahead of `restoreLocalNames`, so the capture is
        // in scope and can't be mistaken for the written local.
        const field_fill = self.exhaustiveAggregateFill(loop);
        try self.emitBoundedRangePrefix(natural_exit, loop);
        try self.emitConstantForFillCoverage(natural_exit, body_cur, loop);
        const ended_loop = self.loop_stack.pop().?;
        std.debug.assert(ended_loop.merge == merge);
        try self.addEdge(body_cur, header);
        self.restoreLocalNames(pre_capture_len, self.tree.firstToken(for_node));
        if (loop.ast.else_expr.unwrap()) |else_expr| {
            var else_cur = natural_exit;
            try self.lowerStmt(else_expr, &else_cur);
            try self.addEdge(else_cur, merge);
        }
        cur.* = merge;
        // Verified comptime-exhaustive aggregate fill: on every path
        // that reaches the merge, the unrolled loop ran to exhaustion
        // and therefore wrote every field / every element of the
        // target. Arrays commit complete coverage without changing their
        // storage origin; structs retain their existing whole-write form.
        // It sits in the merge block (after the else arm), so it
        // dominates what follows the loop and can never reach a path
        // that returned from inside the body.
        if (field_fill) |fill| {
            try self.appendStmt(merge, .{
                .kind = if (self.locals.items[@intFromEnum(fill.local)].is_array)
                    .{ .array_complete = .{
                        .array = fill.local,
                        .inputs = fill.inputs,
                        .selected_inputs = fill.selected_inputs,
                    } }
                else
                    .{ .assign = .{ .target = fill.local, .rhs_kind = .plain, .value_defined = true } },
                .pos = fill.pos,
                .end_pos = fill.end_pos,
            });
        }
    }

    /// Static scalar literals need no caller storage, but every element must
    /// have its own source value. Array extent alone never proves payload.
    fn staticScalarArrayInput(self: *Builder, input: Ast.Node.Index) bool {
        if (self.tree.nodeTag(input) != .identifier) return false;
        const token = self.tree.nodeMainToken(input);
        const name = self.tree.tokenSlice(token);
        if (self.name_to_local.contains(name)) return false;
        const declaration = self.fill.visibleConstDecl(token, name) orelse return false;
        var elements = comptime_fill.ElementIterator.init(self.tree, declaration.spans.?.init) orelse return false;
        while (elements.next()) |element| {
            if (self.fill.comptimeIntTokens(element, 0) != null) continue;
            if (element.first != element.last) return false;
            switch (self.tree.tokenTag(element.first)) {
                .char_literal => {},
                .identifier => {
                    const value = self.tree.tokenSlice(element.first);
                    if (!std.mem.eql(u8, value, "true") and !std.mem.eql(u8, value, "false")) return false;
                },
                else => return false,
            }
        }
        return true;
    }

    /// Constant fragments extend existing prefix and sparse-store coverage
    /// through one natural-exit certificate, without expanding the CFG.
    fn emitConstantForFillCoverage(self: *Builder, block: BlockId, body_block: BlockId, loop: Ast.full.For) !void {
        const tree = self.tree;
        if (loop.label_token != null or self.blockLabelToken(loop.ast.then_expr) != null) return;
        var body_token = tree.firstToken(loop.ast.then_expr);
        const body_last = tree.lastToken(loop.ast.then_expr);
        while (body_token <= body_last) : (body_token += 1) {
            switch (tree.tokenTag(body_token)) {
                .keyword_break, .keyword_continue => return,
                else => {},
            }
        }
        var statement_buffer: [2]Ast.Node.Index = undefined;
        var single_buffer: [1]Ast.Node.Index = undefined;
        const statements = self.blockStmtList(loop.ast.then_expr, &statement_buffer, &single_buffer) orelse return;
        if (statements.len != 1) return;
        const store = self.subscriptFillAssignWrite(statements[0]) orelse return;
        var value_defined = self.rhsIsDefined(store.rhs);
        const value_has_undefined_origin = self.hasRuntimeUndefinedLiteral(store.rhs);
        const name = tree.tokenSlice(store.base_tok);
        if (self.identifierMentions(name, tree.firstToken(loop.ast.then_expr), tree.lastToken(loop.ast.then_expr)) != 1) return;
        const target = self.name_to_local.get(name) orelse return;
        const info = self.locals.items[@intFromEnum(target)];
        if (!info.is_array or info.is_pointer or info.is_slice) return;
        const extent = info.array_extent orelse return;
        const declaration = self.fill.declaredTypeSpanOfLocal(target) orelse return;
        if (declaration.is_const or !declaration.init_is_undefined or declaration.name_tok >= loop.ast.for_token) return;

        var first: u64 = 0;
        var end: u64 = 0;
        var index_name: []const u8 = undefined;
        var payload: ?LocalId = null;
        var source_inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
        if (loop.ast.inputs.len == 1) {
            const input = loop.ast.inputs[0];
            if (tree.nodeTag(input) != .for_range) return;
            const range = tree.nodeData(input).node_and_opt_node;
            first = self.integerValue(range[0]) orelse return;
            const bound = range[1].unwrap() orelse return;
            end = self.integerValue(bound) orelse bound_value: {
                if (tree.nodeTag(bound) != .field_access) return;
                const base, const field = tree.nodeData(bound).node_and_token;
                if (tree.nodeTag(base) != .identifier or !std.mem.eql(u8, tree.tokenSlice(field), "len")) return;
                const local = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(base))) orelse return;
                break :bound_value self.locals.items[@intFromEnum(local)].array_extent orelse return;
            };
            index_name = self.forCaptureName(loop) orelse return;
        } else if (loop.ast.inputs.len == 2 and self.zeroBasedRangeInput(loop.ast.inputs[1])) {
            const captures = self.forIndexedCaptureNames(loop) orelse return;
            const input = loop.ast.inputs[0];
            end = self.fill.iteratedFixedCount(input) orelse return;
            index_name = captures.index;
            payload = self.name_to_local.get(captures.value) orelse return;
            if (!self.rhsIsDefined(input) or
                (!self.selectedValueInputs(input, &source_inputs, false) and !self.staticScalarArrayInput(input))) return;
            // File constants are not locals in the transfer state. Reject an
            // explicitly undefined element before dropping the value capture.
            if (tree.nodeTag(input) == .identifier) {
                if (self.fill.visibleConstDecl(tree.nodeMainToken(input), tree.tokenSlice(tree.nodeMainToken(input)))) |decl| {
                    const init = (decl.spans orelse return).init;
                    var token = init.first;
                    while (token <= init.last) : (token += 1) {
                        if (tree.tokenTag(token) == .identifier and std.mem.eql(u8, tree.tokenSlice(token), "undefined")) return;
                    }
                }
            }
        } else return;
        if (end <= first) return;
        const counter = self.name_to_local.get(index_name) orelse return;
        if (counter == target or payload == target) return;
        const subscript = tree.nodeData(store.lhs).node_and_node[1];
        const offset = self.constantForIndexOffset(subscript, index_name) orelse return;
        const range_start = std.math.add(u64, first, offset) catch return;
        const range_end = std.math.add(u64, end, offset) catch return;
        if (range_end > extent) return;
        var dependencies: [8]?cfg_types.ValueInput = .{null} ** 8;
        var call_inputs: [8]?LocalId = .{null} ** 8;
        if (!self.selectedValueInputs(store.rhs, &dependencies, false)) {
            if (value_defined and tree.nodeTag(store.rhs) == .@"try" and
                self.callResultInputs(tree.nodeData(store.rhs).node, &call_inputs))
            {
                dependencies = .{null} ** 8;
                const body_call_inputs = call_inputs;
                for (&call_inputs) |*entry| {
                    const local = entry.* orelse continue;
                    if (local == counter or payload == local) entry.* = null;
                }
                if (!self.creditLoopFillStore(body_block, store, body_call_inputs, .{null} ** 8)) return;
            } else {
                call_inputs = .{null} ** 8;
                value_defined = false;
            }
        }
        var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
        var count: usize = 0;
        for (dependencies) |entry| {
            var input = entry orelse continue;
            switch (input) {
                .local => |local| if (local == counter or payload == local) {
                    continue;
                },
                .field => |field| if (payload == field.parent) {
                    continue;
                },
                .indexed => |indexed| {
                    if (payload == indexed.array) return;
                    switch (indexed.index) {
                        .local => |term| if (term.local == counter) {
                            // Without per-slot expansion, require the whole
                            // RHS source rather than invent indexed intervals.
                            input = .{ .local = indexed.array };
                        } else if (payload == term.local) return,
                        else => {},
                    }
                },
            }
            inputs[count] = input;
            count += 1;
        }
        for (source_inputs) |entry| {
            const input = entry orelse continue;
            if (count == inputs.len) return;
            inputs[count] = input;
            count += 1;
        }
        try self.appendStmt(block, .{
            .kind = .{ .array_range_complete = .{
                .array = target,
                .start = range_start,
                .end = range_end,
                .selected_inputs = inputs,
                .inputs = call_inputs,
                .value_defined = value_defined,
                .value_has_undefined_origin = value_has_undefined_origin,
            } },
            .pos = self.posOf(store.lhs),
            .end_pos = self.endPosOf(store.lhs),
        });
    }

    /// Attach a proven successful RHS to its exact existing store event.
    /// Callers prove RHS dependencies and a stable bare counter before
    /// restoring an index snapshot lost to computed RHS evaluation.
    fn creditLoopFillStore(
        self: *Builder,
        block: BlockId,
        store: FieldFillWrite,
        inputs: [8]?LocalId,
        selected: [8]?cfg_types.ValueInput,
    ) bool {
        const target = self.name_to_local.get(self.tree.tokenSlice(store.base_tok)) orelse return false;
        const byte = self.posOfToken(store.base_tok).byte;
        for (self.block_stmts.items[@intFromEnum(block)].items) |*statement| {
            if (statement.pos.byte != byte) continue;
            switch (statement.kind) {
                .indexed_write => |*write| {
                    if (write.array != target) continue;
                    if (write.index == .unknown and store.lhs == .root) {
                        const counter = self.indexLocalAt(store.base_tok + 2) orelse return false;
                        write.index = .{ .local = .{ .local = counter } };
                    }
                    write.defined = true;
                    write.inputs = inputs;
                    write.selected_inputs = selected;
                    return true;
                },
                else => {},
            }
        }
        return false;
    }

    /// The counter alone, or addition of an independently constant offset.
    fn constantForIndexOffset(self: *Builder, node: Ast.Node.Index, counter: []const u8) ?u64 {
        const tree = self.tree;
        if (tree.nodeTag(node) == .identifier) {
            if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), counter)) return 0;
            return null;
        }
        if (tree.nodeTag(node) != .add) return null;
        const lhs, const rhs = tree.nodeData(node).node_and_node;
        const operands = [_]Ast.Node.Index{ lhs, rhs };
        for (operands, 0..) |operand, side| {
            if (tree.nodeTag(operand) != .identifier or !std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(operand)), counter)) continue;
            return self.integerValue(operands[1 - side]);
        }
        return null;
    }

    /// Pick whichever exhaustive aggregate-fill proof this loop
    /// satisfies.  Each asks the same question — does this loop leave
    /// every element of the target written? — over a different shape
    /// of enumeration and a different way of establishing the count:
    ///
    ///   - `exhaustiveFieldFill` — an `inline for` over
    ///     `@typeInfo(T).@"struct".fields` writing `@field(x, f.name)`,
    ///     one field per iteration;
    ///   - `exhaustiveIndexedFill` — a fixed-count `for (xs, 0..)`
    ///     writing `x[i]`, one element per iteration;
    ///   - `exhaustiveTiledFill` — a `for` over fixed-size storage
    ///     writing SEVERAL elements per iteration, at indices affine in
    ///     the counter whose residues together tile the target;
    ///   - `exhaustivePointerCaptureFill` — a `for (&x, 0..)` with a
    ///     by-pointer capture writing through it;
    ///   - `exhaustiveCounterFill` — a nested PAIR of `for` loops
    ///     filling a flat target through a manual counter advanced once
    ///     per inner iteration.
    ///
    /// Field reflection and unresolved collection identities require comptime
    /// enumeration. Independently fixed counts and an immediately preceding
    /// canonical length assertion also prove runtime enumeration cardinality.
    /// Each complete-array certificate retains the RHS dependencies whose
    /// current definedness must still hold on natural exit.
    ///
    /// The dispatch is on the loop's SHAPE, so at most one of the
    /// two-input proofs reaches any given loop: the indexed one wants a
    /// single `x[i]` store, the tiled one wants at least two, and the
    /// pointer one wants a `&x` enumeration with a by-pointer payload.
    /// The counter proof wants a single-input outer loop whose entire
    /// body is another loop, which no other proof's shape admits.
    fn exhaustiveAggregateFill(self: *Builder, loop: Ast.full.For) ?FieldFillProof {
        if (loop.label_token != null) return null;
        return self.exhaustiveFieldFill(loop) orelse
            self.exhaustiveEnumValueFill(loop) orelse
            self.exhaustiveIndexedFill(loop) orelse
            self.exhaustiveTiledFill(loop) orelse
            self.exhaustivePointerCaptureFill(loop) orelse
            self.exhaustiveCounterFill(loop) orelse
            self.exhaustiveRangeFill(loop);
    }

    /// Enum descriptors cover an array only when their actual tag values form
    /// the zero-based contiguous ordinal sequence and every store is mandatory.
    fn exhaustiveEnumValueFill(self: *Builder, loop: Ast.full.For) ?FieldFillProof {
        if (loop.inline_token == null or loop.label_token != null or loop.ast.inputs.len != 1)
            return null;
        const tree = self.tree;
        const input = loop.ast.inputs[0];
        const type_span = self.fill.enumMetaFieldsTypeSpan(.{
            .first = tree.firstToken(input),
            .last = tree.lastToken(input),
        }) orelse return null;
        const count = self.fill.contiguousEnumValueCount(type_span) orelse return null;
        const capture = self.forCaptureName(loop) orelse return null;
        const body = loop.ast.then_expr;
        const first = tree.firstToken(body);
        const last = tree.lastToken(body);
        if (self.bodyHasUnlabeledLoopExit(first, last)) return null;
        var buffer: [2]Ast.Node.Index = undefined;
        var single: [1]Ast.Node.Index = undefined;
        const statements = self.blockStmtList(body, &buffer, &single) orelse return null;
        var store: ?FieldFillWrite = null;
        for (statements) |statement| {
            if (tree.nodeTag(statement) != .assign) continue;
            const lhs, const rhs = tree.nodeData(statement).node_and_node;
            const start = tree.firstToken(lhs);
            const end = tree.lastToken(lhs);
            // Exactly `result[field.value]`, not a shifted or repeated index.
            if (end != start + 5 or tree.tokenTag(start) != .identifier or
                tree.tokenTag(start + 1) != .l_bracket or
                tree.tokenTag(start + 2) != .identifier or
                !std.mem.eql(u8, tree.tokenSlice(start + 2), capture) or
                tree.tokenTag(start + 3) != .period or
                tree.tokenTag(start + 4) != .identifier or
                !std.mem.eql(u8, tree.tokenSlice(start + 4), "value") or
                tree.tokenTag(end) != .r_bracket) continue;
            const binding = self.fill.visibleDeclAt(start + 2, capture) orelse return null;
            if (binding.name_tok != loop.payload_token) return null;
            if (store != null or !self.rhsIsDefined(rhs)) return null;
            store = .{ .base_tok = start, .rhs = rhs };
        }
        const write = store orelse return null;
        const name = tree.tokenSlice(write.base_tok);
        if (std.mem.eql(u8, name, capture) or self.identifierMentions(name, first, last) != 1)
            return null;
        const local = self.name_to_local.get(name) orelse return null;
        if (!self.locals.items[@intFromEnum(local)].is_array) return null;
        const decl = self.fill.declaredTypeSpanOfLocal(local) orelse return null;
        if (decl.is_const or !decl.init_is_undefined or decl.name_tok >= loop.ast.for_token)
            return null;
        const extent = self.fill.declaredExtent(decl.type) orelse return null;
        if (count != (extent.number orelse return null)) return null;
        var inputs: [8]?LocalId = .{null} ** 8;
        var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
        if (!self.fillProofInputs(write.rhs, &inputs, &selected)) return null;
        for (&inputs) |*entry| {
            if (entry.*) |dependency| {
                if (self.enumValueDerivedLocal(dependency, loop, statements)) entry.* = null;
            }
        }
        for (&selected) |*entry| {
            const dependency = entry.* orelse continue;
            const derived = switch (dependency) {
                .local => |source| self.enumValueDerivedLocal(source, loop, statements),
                .field => |field| std.mem.eql(u8, field.name, "value") and
                    self.locals.items[@intFromEnum(field.parent)].decl_pos.byte ==
                        tree.tokenStart(loop.payload_token),
                .indexed => false,
            };
            if (derived) entry.* = null;
        }
        return .{
            .local = local,
            .pos = self.posOfToken(loop.ast.for_token),
            .end_pos = self.endPosOf(body),
            .inputs = inputs,
            .selected_inputs = selected,
        };
    }

    /// Only this immutable compiler-enumeration conversion can be absent from
    /// the natural-exit dependency state; ordinary runtime sources stay checked.
    fn enumValueDerivedLocal(
        self: *Builder,
        local: LocalId,
        loop: Ast.full.For,
        statements: []const Ast.Node.Index,
    ) bool {
        const tree = self.tree;
        const decl = self.fill.declaredTypeSpanOfLocal(local) orelse return false;
        if (!decl.is_const or decl.name_tok <= tree.firstToken(loop.ast.then_expr))
            return false;
        var mandatory = false;
        for (statements) |statement| {
            const declaration = tree.fullVarDecl(statement) orelse continue;
            if (declaration.ast.mut_token + 1 == decl.name_tok) {
                mandatory = true;
                break;
            }
        }
        if (!mandatory) return false;
        const init = decl.init orelse return false;
        if (init.last - init.first != 5 or
            tree.tokenTag(init.first) != .builtin or
            !std.mem.eql(u8, tree.tokenSlice(init.first), "@enumFromInt") or
            tree.tokenTag(init.first + 1) != .l_paren or
            tree.tokenTag(init.first + 2) != .identifier or
            tree.tokenTag(init.first + 3) != .period or
            tree.tokenTag(init.first + 4) != .identifier or
            !std.mem.eql(u8, tree.tokenSlice(init.first + 4), "value") or
            tree.tokenTag(init.last) != .r_paren) return false;
        const binding = self.fill.visibleDeclAt(
            init.first + 2,
            tree.tokenSlice(init.first + 2),
        ) orelse return false;
        return binding.name_tok == loop.payload_token;
    }

    /// Commit only a zero-based bounded enumeration's unconditional store.
    fn exhaustiveRangeFill(self: *Builder, loop: Ast.full.For) ?FieldFillProof {
        if (loop.label_token != null or loop.ast.inputs.len != 1) return null;
        const tree = self.tree;
        const input = loop.ast.inputs[0];
        if (tree.nodeTag(input) != .for_range) return null;
        const range = tree.nodeData(input).node_and_opt_node;
        if (self.integerValue(range[0]) != 0) return null;
        const bound = range[1].unwrap() orelse return null;
        const capture = self.forCaptureName(loop) orelse return null;
        const first = tree.firstToken(loop.ast.then_expr);
        const last = tree.lastToken(loop.ast.then_expr);
        if (self.bodyHasUnlabeledLoopExit(first, last)) return null;
        var buffer: [2]Ast.Node.Index = undefined;
        var single: [1]Ast.Node.Index = undefined;
        const statements = self.blockStmtList(loop.ast.then_expr, &buffer, &single) orelse return null;
        var store: ?FieldFillWrite = null;
        for (statements) |statement| {
            const write = self.indexedFillAssignWrite(statement, capture) orelse continue;
            var dependencies: [8]?cfg_types.ValueInput = .{null} ** 8;
            if (!self.selectedValueInputs(write.rhs, &dependencies, false)) return null;
            for (dependencies) |dependency| {
                const value = dependency orelse continue;
                if (value != .local) return null;
                if (self.locals.items[@intFromEnum(value.local)].is_array) return null;
            }
            if (store != null or !self.rhsIsDefined(write.rhs)) return null;
            store = write;
        }
        const write = store orelse return null;
        const name = tree.tokenSlice(write.base_tok);
        if (self.identifierMentions(name, first, last) != 1) return null;
        const local = self.name_to_local.get(name) orelse return null;
        const decl = self.fill.declaredTypeSpanOfLocal(local) orelse return null;
        if (decl.is_const or !decl.init_is_undefined or decl.name_tok >= loop.ast.for_token) return null;
        const extent = self.locals.items[@intFromEnum(local)].array_extent orelse return null;
        const count = self.integerValue(bound) orelse blk: {
            if (tree.nodeTag(bound) != .field_access) return null;
            const base, const field = tree.nodeData(bound).node_and_token;
            if (tree.nodeTag(base) != .identifier or !std.mem.eql(u8, tree.tokenSlice(field), "len")) return null;
            if (self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(base))) != local) return null;
            break :blk extent;
        };
        if (count != extent) return null;
        var inputs: [8]?LocalId = .{null} ** 8;
        var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
        if (!self.fillProofInputs(write.rhs, &inputs, &selected)) return null;
        return .{
            .local = local,
            .pos = self.posOfToken(loop.ast.for_token),
            .end_pos = self.endPosOf(loop.ast.then_expr),
            .inputs = inputs,
            .selected_inputs = selected,
        };
    }

    /// A COUNTER-GUARDED fill: a `while` that walks a local one
    /// element at a time through a counter, followed — as the next
    /// sibling statement — by the equality check that closes the
    /// counting argument.  `local` holds a fully initialized value by
    /// the time that check's FALL-THROUGH arm is reached.
    const CountedFillCredit = struct {
        local: LocalId,
        pos: SrcPos,
        end_pos: SrcPos,
    };

    /// True when [first, last] holds a `break` / `continue` that is
    /// NOT followed by a `:` label.  Either would leave the loop, or
    /// skip the rest of an iteration, before every element was
    /// written.  A LABELED one is safe by construction: the proof only
    /// ever runs on an UNLABELED loop, so `break :blk` binds an
    /// enclosing labeled block or switch — which is what the packed
    /// `=> blk: { … break :blk … }` arms depend on.
    ///
    /// A `defer`/`errdefer` needs no rule of its own: it fires at
    /// scope exit, and it could only reach the target by naming it,
    /// which the single-mention check rejects.
    fn bodyHasUnlabeledLoopExit(
        self: *const Builder,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var scan: Ast.TokenIndex = first;
        while (scan <= last) : (scan += 1) {
            const tag = tags[scan];
            if (tag != .keyword_break and tag != .keyword_continue) continue;
            if (scan + 1 >= tags.len or tags[scan + 1] != .colon) return true;
        }
        return false;
    }

    /// Complete coverage from a mandatory store and an exact enumeration
    /// extent. Only the natural exit may receive this certificate. Array
    /// consumers also check the retained source dependencies at transfer time.
    const FieldFillProof = struct {
        local: LocalId,
        pos: SrcPos,
        end_pos: SrcPos,
        inputs: [8]?LocalId = .{null} ** 8,
        selected_inputs: [8]?cfg_types.ValueInput = .{null} ** 8,
    };

    fn addFillStorageInput(inputs: *[8]?LocalId, local: LocalId) bool {
        for (inputs) |entry| if (entry == local) return true;
        for (inputs) |*entry| {
            if (entry.* == null) {
                entry.* = local;
                return true;
            }
        }
        return false;
    }

    /// Carry source storage and selected scalar dependencies to natural exit.
    /// Body-backed call results still depend on every referenced caller slot.
    fn fillProofInputs(
        self: *Builder,
        rhs: Ast.Node.Index,
        storage: *[8]?LocalId,
        selected: *[8]?cfg_types.ValueInput,
    ) bool {
        if (!self.selectedValueInputs(rhs, selected, false)) {
            selected.* = .{null} ** 8;
            if (!self.callResultInputs(initShapeNode(self, rhs), storage)) return false;
        }
        for (selected) |*entry| {
            const input = entry.* orelse continue;
            if (input == .indexed) {
                if (!addFillStorageInput(storage, input.indexed.array)) return false;
                entry.* = null;
            }
        }
        return true;
    }

    /// The one top-level store of the loop body: the token naming the
    /// written local and the value expression stored into the field /
    /// element this iteration owns.  Shared by both fill proofs —
    /// `fieldFillAssignWrite` produces `@field(<base>, <capture>.name)`
    /// and `indexedFillAssignWrite` produces `<base>[<index capture>]`.
    const FieldFillWrite = struct {
        base_tok: Ast.TokenIndex,
        rhs: Ast.Node.Index,
        /// The lvalue node, for a proof that has to take the SUBSCRIPT
        /// apart rather than accept the whole `name [ … ]` shape.  A
        /// tiled fill reads the index expression, and the token span of
        /// `out[i * 2]` is not the four tokens `out[i]` is.  Producers
        /// that never need it leave it at zero.
        lhs: Ast.Node.Index = .root,
    };

    /// Sound comptime-exhaustive-field-initialization proof.
    ///
    ///   var result: T = undefined;
    ///   inline for (@typeInfo(T).@"struct".fields) |field| { … }
    ///   return result;
    ///
    /// `inline for` unrolls at comptime, so after the loop every
    /// semantic field of `T` has been assigned — valid Zig only
    /// guarantees that if the body really writes each one.  The generic
    /// CFG can't see it: the loop may run zero times, so `result` still
    /// reads as `.undef` at the `return`.  This narrows exactly that
    /// gap, and nothing else — in particular it does NOT treat a
    /// single field write as defining the whole struct.
    ///
    /// Each clause below is load-bearing; any one missing would let the
    /// loop finish with a field still unwritten:
    ///   - the loop is `inline` (comptime-unrolled) and unlabelled,
    ///     over exactly `@typeInfo(<T>).@"struct".fields`;
    ///   - the descriptor's type argument is a bare identifier that
    ///     names THIS function's `comptime <T>: type` parameter, and
    ///     that parameter is still the binding the name resolves to
    ///     here — so no body-level `T` (`const T = …`, `comptime var T
    ///     = …`, a capture) shadows it.  Same source text is NOT the
    ///     same type; this is the only accepted way to tie the two
    ///     sites to one immutable binding.  The target's declared type
    ///     must then be that same bare parameter name, so the fields
    ///     enumerated are the target's fields and not another type's;
    ///   - the payload is a by-value `|<ident>|` capture, and the
    ///     body's single top-level `@field` lvalue selects through
    ///     that exact capture as `.<ident>.name` — any other selector
    ///     writes a field the loop never enumerates;
    ///   - the target has exactly ONE mention in the whole body: that
    ///     lvalue.  A read, a nested write, or a write behind a
    ///     conditional each leave fields undefined on some path;
    ///   - the body holds no UNLABELED `break` / `continue`.  Either
    ///     would leave the loop, or skip the rest of an iteration,
    ///     before the remaining fields were written.  A LABELED one is
    ///     safe by construction: this loop is unlabeled, so `break :blk`
    ///     binds an enclosing labeled block or switch — which is what
    ///     the packed `=> blk: { … break :blk … }` arms depend on.
    ///     `defer` needs no rule of its own: it fires at scope exit and
    ///     can only reach the target by naming it, which the
    ///     single-mention clause above already forbids.
    ///   - the target is a `var` seeded with the `undefined` keyword —
    ///     that seed is the only thing the loop clears — and the
    ///     written value is not itself `undefined`.  Writing
    ///     `undefined`, or copying a local that was seeded `undefined`,
    ///     leaves every field exactly as uninitialized as it was, and a
    ///     synthetic "the whole value is now defined" claim would hide
    ///     that real use-undefined behind a loop that provably wrote
    ///     nothing of substance.
    ///
    /// A `return` inside the body is neither rejected nor credited: the
    /// effect lands in the loop's merge block, so an early return is
    /// still analysed on its own path with only the fields it wrote.
    /// Zero-field `T` is zero-sized — nothing to read — so the unrolled
    /// loop writing nothing is safe.
    fn exhaustiveFieldFill(self: *Builder, loop: Ast.full.For) ?FieldFillProof {
        if (loop.inline_token == null) return null;
        if (loop.label_token != null) return null;
        if (loop.ast.inputs.len != 1) return null;
        const arg = typeInfoStructFieldsArg(self.tree, loop.ast.inputs[0]) orelse return null;
        const capture = self.forCaptureName(loop) orelse return null;
        // A bare identifier is the only argument shape this accepts:
        // anything else (`Key.Pointer`, `Self`, `@This()`, a call) is a
        // type EXPRESSION whose identity needs real resolution.
        if (arg.first != arg.last) return null;
        const type_name = self.tree.tokenSlice(arg.first);
        const param_tok = self.fill.comptimeTypeParamToken(type_name) orelse return null;
        if (!self.fill.bindingIsParam(type_name, param_tok)) return null;

        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const body_node = loop.ast.then_expr;
        const body_first = tree.firstToken(body_node);
        const body_last = tree.lastToken(body_node);
        if (body_first > body_last or body_last >= tags.len) return null;

        if (self.bodyHasUnlabeledLoopExit(body_first, body_last)) return null;

        var stmt_buf: [2]Ast.Node.Index = undefined;
        var single_buf: [1]Ast.Node.Index = undefined;
        const stmts: []const Ast.Node.Index = switch (tree.nodeTag(body_node)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => blockStmts(tree, body_node, &stmt_buf),
            else => blk: {
                single_buf[0] = body_node;
                break :blk single_buf[0..];
            },
        };

        var base_tok: Ast.TokenIndex = 0;
        var found = false;
        for (stmts) |stmt| {
            const w = self.fieldFillAssignWrite(stmt, capture) orelse continue;
            // A second `@field` lvalue means the body isn't the single
            // unconditional enumeration this proof is about.
            if (found) return null;
            const write_name = tree.tokenSlice(w.base_tok);
            if (std.mem.eql(u8, write_name, capture)) return null;
            if (self.name_to_local.get(write_name) == null) return null;
            if (!self.rhsIsDefined(w.rhs)) return null;
            base_tok = w.base_tok;
            found = true;
        }
        if (!found) return null;
        const local = self.name_to_local.get(tree.tokenSlice(base_tok)).?;

        const name = self.locals.items[@intFromEnum(local)].name;
        if (self.identifierMentions(name, body_first, body_last) != 1) return null;

        const decl = self.fill.declaredTypeSpanOfLocal(local) orelse return null;
        // `@field` through a `const` doesn't compile, and the loop is
        // only what defines the value if the seed really was `undefined`.
        if (decl.is_const) return null;
        if (!decl.init_is_undefined) return null;
        if (decl.name_tok >= loop.ast.for_token) return null;
        // The declared type must be that same bare parameter name.
        if (decl.type.first != decl.type.last) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(decl.type.first), type_name)) return null;
        return .{
            .local = local,
            .pos = self.posOfToken(loop.ast.for_token),
            .end_pos = self.endPosOf(body_node),
        };
    }

    /// The by-value capture identifier of `|<ident>|`.  Null for a
    /// by-pointer capture (`|*x|`), for `_`, for a destructuring
    /// payload (`|a, b|`), and for a loop with no payload at all —
    /// none of which name a field descriptor.
    ///
    /// `full.For.payload_token` is the token AFTER the opening `|`
    /// (`Ast.fullForComponents` sets it to `last_cond_token + 3`), the
    /// convention `registerCapturesImpl` scans from — so the name is
    /// AT it, with `|` on both sides.  A loop carrying no payload at
    /// all still lands somewhere past its input expression, so the
    /// opening `|` is what makes this a payload rather than the first
    /// token of an unbraced body.
    fn forCaptureName(self: *const Builder, loop: Ast.full.For) ?[]const u8 {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const pt = loop.payload_token;
        if (pt >= tags.len or pt + 1 >= tags.len) return null;
        if (tags[pt] != .identifier) return null;
        if (pt == 0 or tags[pt - 1] != .pipe) return null;
        if (tags[pt + 1] != .pipe) return null;
        const name = tree.tokenSlice(pt);
        if (std.mem.eql(u8, name, "_")) return null;
        return name;
    }

    /// The top-level `@field(<base>, <capture>.name) = <rhs>` statement
    /// of the loop body.  The selector must be exactly
    /// `<capture>.name`: `.name` is what the loop's descriptor yields,
    /// and any other path would write a different field than the one
    /// being enumerated.
    fn fieldFillAssignWrite(
        self: *const Builder,
        stmt: Ast.Node.Index,
        capture: []const u8,
    ) ?FieldFillWrite {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (tree.nodeTag(stmt) != .assign) return null;
        const data = tree.nodeData(stmt).node_and_node;
        const lhs = data[0];
        switch (tree.nodeTag(lhs)) {
            .builtin_call_two, .builtin_call_two_comma => {},
            else => return null,
        }
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(lhs)), "@field")) return null;
        const args = tree.nodeData(lhs).opt_node_and_opt_node;
        const base = args[0].unwrap() orelse return null;
        const selector = args[1].unwrap() orelse return null;
        if (tree.nodeTag(base) != .identifier) return null;
        const sel_first = tree.firstToken(selector);
        const sel_last = tree.lastToken(selector);
        if (sel_first >= tags.len or sel_last >= tags.len) return null;
        if (sel_last != sel_first + 2) return null;
        if (tags[sel_first] != .identifier or tags[sel_first + 1] != .period) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(sel_first), capture)) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(sel_last), "name")) return null;
        return .{ .base_tok = tree.nodeMainToken(base), .rhs = data[1] };
    }

    // ── Comptime-exhaustive INDEXED aggregate fill ──────────────

    /// The `| value , index |` payload of a two-input `inline for`.
    const IndexedPayload = struct {
        value: []const u8,
        index: []const u8,
    };

    /// Sound comptime-exhaustive INDEXED-initialization proof.
    ///
    ///   var out: [N]E = undefined;
    ///   inline for (xs, 0..) |v, i| { …; out[i] = …; }
    ///   return out;
    ///
    /// `inline for` unrolls at comptime, so `i` runs `0 … xs.len-1`
    /// with no bound to get wrong — the generic CFG models the loop as
    /// possibly running zero times, so `out` still reads as `.undef` at
    /// the `return`.  This closes exactly that gap, and only when the
    /// enumeration provably covers the whole target.
    ///
    /// Load-bearing clauses, each of which would otherwise leave an
    /// element unwritten on some path:
    ///   - the loop runs a FIXED number of times at comptime and is
    ///     unlabelled: either it is `inline`, or it is an ordinary
    ///     `for` inside a `comptime` block (or a `comptime label:` one)
    ///     with its target declared in that same block — comptime code
    ///     cannot reach a runtime frame's slots, and every statement of
    ///     such a block is evaluated at comptime, so the loop still
    ///     walks its whole collection;
    ///   - it has TWO inputs and the second is exactly `0..`.  A `1..`
    ///     start shifts every write off index 0; a bounded `0..n`
    ///     truncates the enumeration.  Only a from-zero open range
    ///     walks 0, 1, 2, … over the whole collection;
    ///   - the payload is `| value , index |` — two by-value captures,
    ///     neither `_`, and not the same name.  A by-pointer payload
    ///     (`|*xs|`) or a bare `|x|` names storage the index count
    ///     says nothing about;
    ///   - the body's ONE top-level lvalue is exactly
    ///     `<target>[<index capture>]`, so the store lands on the slot
    ///     this iteration owns.  A nested or conditional lvalue lets
    ///     an iteration skip the write entirely;
    ///   - the target has exactly ONE mention in the whole body: that
    ///     lvalue.  A read, a second write through an alias, or a
    ///     write behind a conditional each leave elements undefined on
    ///     some path.  (An alias is what `&out` / `out[i]` copies out
    ///     of the body look like, and both are rejected here.)
    ///   - the body holds no UNLABELED `break` / `continue` — the same
    ///     rule the field proof uses, for the same reason;
    ///   - the target is a `var` seeded with the `undefined` keyword,
    ///     declared before the loop, and the written value is not
    ///     itself `undefined` (`rhsIsDefined`).  Writing `undefined`,
    ///     or copying a local seeded `undefined`, leaves every element
    ///     exactly as uninitialized as it was;
    ///   - the two element counts are EQUAL, established as described
    ///     on `Resolver.declaredExtent` / `Resolver.iteratedExtent`.
    ///
    /// A `return` or a `try` inside the body is neither rejected nor
    /// credited: neither reaches the loop's merge block, so an early
    /// exit is still analysed on its own path with only the elements it
    /// wrote.  A zero-length array or tuple is vacuously filled, and
    /// that is sound rather than merely tolerated: `undefined` for a
    /// zero-length aggregate has no bytes, so there is nothing to read.
    fn exhaustiveIndexedFill(self: *Builder, loop: Ast.full.For) ?FieldFillProof {
        if (loop.label_token != null) return null;
        if (loop.ast.inputs.len != 2) return null;
        if (!self.zeroBasedRangeInput(loop.ast.inputs[1])) return null;
        const payload = self.forIndexedCaptureNames(loop) orelse return null;

        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const body_node = loop.ast.then_expr;
        const body_first = tree.firstToken(body_node);
        const body_last = tree.lastToken(body_node);
        if (body_first > body_last or body_last >= tags.len) return null;
        if (self.bodyHasUnlabeledLoopExit(body_first, body_last)) return null;

        var stmt_buf: [2]Ast.Node.Index = undefined;
        var single_buf: [1]Ast.Node.Index = undefined;
        const stmts: []const Ast.Node.Index = switch (tree.nodeTag(body_node)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => blockStmts(tree, body_node, &stmt_buf),
            else => blk: {
                single_buf[0] = body_node;
                break :blk single_buf[0..];
            },
        };

        var base_tok: Ast.TokenIndex = 0;
        var found = false;
        var inputs: [8]?LocalId = .{null} ** 8;
        var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
        for (stmts) |stmt| {
            const w = self.indexedFillAssignWrite(stmt, payload.index) orelse continue;
            // A second index lvalue means the body isn't the single
            // unconditional enumeration this proof is about.
            if (found) return null;
            const write_name = tree.tokenSlice(w.base_tok);
            if (std.mem.eql(u8, write_name, payload.value)) return null;
            if (std.mem.eql(u8, write_name, payload.index)) return null;
            if (self.name_to_local.get(write_name) == null) return null;
            if (!self.rhsIsDefined(w.rhs)) return null;
            if (!self.fillProofInputs(w.rhs, &inputs, &selected)) return null;
            base_tok = w.base_tok;
            found = true;
        }
        if (!found) return null;
        const local = self.name_to_local.get(tree.tokenSlice(base_tok)).?;

        const name = self.locals.items[@intFromEnum(local)].name;
        if (self.identifierMentions(name, body_first, body_last) != 1) return null;

        const decl = self.fill.declaredTypeSpanOfLocal(local) orelse return null;
        // An index store through a `const` doesn't compile, and the
        // loop only defines the value if the seed really was `undefined`.
        if (decl.is_const) return null;
        if (!decl.init_is_undefined) return null;
        if (decl.name_tok >= loop.ast.for_token) return null;
        // Runtime enumeration is equally exhaustive when both extents are
        // independently fixed counts. Reflection identities without a known
        // count remain restricted to comptime enumeration.

        const target = self.fill.declaredExtent(decl.type) orelse return null;
        var iterated: comptime_fill.Extent = self.fill.iteratedExtent(loop.ast.inputs[0]) orelse .{};
        if (!comptime_fill.extentsAgree(target, iterated)) {
            iterated = self.queryOrUnknown(comptime_fill.Extent, self.fill.assertedEnumerationExtent(loop, decl.name_tok, target)) orelse return null;
        }
        if (loop.inline_token == null and (target.number == null or iterated.number == null)) {
            const block = self.fill.comptimeBlockEnclosing(loop.ast.for_token) orelse return null;
            if (decl.name_tok <= block) return null;
        }
        // Capture values are supplied by the complete enumerated source. Check
        // that whole source, not a representative slot that could miss a hole.
        const capture = self.name_to_local.get(payload.value);
        for (&selected) |*entry| {
            const dependency = entry.* orelse continue;
            const owner: ?LocalId = switch (dependency) {
                .local => |id| id,
                .field => |field| field.parent,
                .indexed => null,
            };
            if (owner != null and owner == capture) entry.* = null;
        }
        for (&inputs) |*entry| {
            if (entry.* != null and entry.* == capture) entry.* = null;
        }
        const source = loop.ast.inputs[0];
        const root = tree.firstToken(source);
        if (tree.tokenTag(root) == .identifier) {
            if (self.name_to_local.get(tree.tokenSlice(root))) |source_local| {
                if (!addFillStorageInput(&inputs, source_local)) return null;
            } else if (self.fill.visibleConstDecl(root, tree.tokenSlice(root))) |source_decl| {
                const init = source_decl.spans.?.init;
                var token = init.first;
                while (token <= init.last) : (token += 1) {
                    if (tree.tokenTag(token) == .identifier and
                        std.mem.eql(u8, tree.tokenSlice(token), "undefined")) return null;
                }
            }
        }

        return .{
            .local = local,
            .pos = self.posOfToken(loop.ast.for_token),
            .end_pos = self.endPosOf(body_node),
            .inputs = inputs,
            .selected_inputs = selected,
        };
    }

    // ── Manual-counter fill over a nested pair of enumerations ──

    /// Sound exhaustive fill driven by a MANUAL COUNTER rather than
    /// by the loop's own index capture:
    ///
    ///     var slots: [rows.len * cols.len]T = undefined;
    ///     var at: usize = 0;
    ///     for (rows) |row| {
    ///         for (cols) |col| {
    ///             …
    ///             slots[at] = …;
    ///             at += 1;
    ///         }
    ///     }
    ///     return slots;
    ///
    /// The counter is the whole point: it is what lets a loop whose
    /// enumeration says nothing about the target's layout (a
    /// single-input `for` over a collection of rows) still write a
    /// FLAT target.  The generic CFG models every loop as possibly
    /// running zero times, so `slots` reaches the `return` as
    /// `.undef`.
    ///
    /// Each clause below is load-bearing; dropping any one leaves an
    /// element unwritten on some path:
    ///   - the OUTER loop is unlabelled, takes one input, and captures
    ///     a single BY-VALUE name.  A second input would carry an
    ///     index this proof does not model, and a by-pointer payload
    ///     names storage the counter's writes are unrelated to;
    ///   - the outer body's ONE statement is the inner loop, so every
    ///     counted iteration is an inner iteration and nothing else
    ///     writes at the counter between them;
    ///   - BOTH loops enumerate FIXED-SIZE storage whose length this
    ///     analysis can read ([iteratedFixedCount]), and the product
    ///     equals the target's declared element count.  Both are
    ///     numbers resolved from declarations — the product included,
    ///     which is why `comptimeIntTokens` evaluates `*` and `.len` —
    ///     so no name is being matched for a length it never stated.
    ///     The counts are exactly equal, not "at least": a loop that
    ///     walks MORE than the target holds writes out of bounds, and
    ///     crediting the fill would bless that;
    ///   - the inner body holds exactly one top-level
    ///     `<target>[<counter>] = <rhs>` store with a DEFINED rhs
    ///     ([rhsIsDefined]), and exactly one top-level
    ///     `<counter> += 1`.  Anything conditional, or a second
    ///     advance, would let iterations desynchronise from the
    ///     counter and the written prefix would stop matching it;
    ///   - the target is named ONCE in the whole inner body and the
    ///     counter TWICE — once in the subscript, once in the
    ///     increment.  Any other mention is a read, a second store,
    ///     or an alias that could write outside the counting
    ///     discipline;
    ///   - neither body holds an UNLABELED `break` / `continue`: one
    ///     would end the enumeration, or skip the increment, before
    ///     the counter caught up with the stores;
    ///   - the target is a `var` seeded with the `undefined` keyword
    ///     and declared before the outer loop, and the counter is a
    ///     `var` whose initializer is the literal `0`.  A counter
    ///     seeded at anything else starts the written prefix away
    ///     from index 0, leaving the head unwritten.
    ///
    /// A `return` or a `try` inside the body is neither rejected nor
    /// credited: neither reaches the outer loop's merge, so an early
    /// exit is still analysed on its own path with only the elements
    /// it wrote.
    fn exhaustiveCounterFill(self: *Builder, loop: Ast.full.For) ?FieldFillProof {
        if (loop.label_token != null) return null;
        if (loop.ast.inputs.len != 1) return null;
        if (self.forCaptureName(loop) == null) return null;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);

        const outer_first = tree.firstToken(loop.ast.then_expr);
        const outer_last = tree.lastToken(loop.ast.then_expr);
        if (outer_first > outer_last or outer_last >= tags.len) return null;
        if (self.bodyHasUnlabeledLoopExit(outer_first, outer_last)) return null;

        var inner_stmts: [2]Ast.Node.Index = undefined;
        const outer_stmts = self.blockStmtList(loop.ast.then_expr, &inner_stmts, null) orelse return null;
        if (outer_stmts.len != 1) return null;
        const inner_node = outer_stmts[0];
        if (tree.nodeTag(inner_node) != .@"for" and tree.nodeTag(inner_node) != .for_simple) return null;
        const inner = tree.fullFor(inner_node) orelse return null;
        if (inner.label_token != null) return null;
        if (inner.ast.inputs.len != 1) return null;
        if (self.forCaptureName(inner) == null) return null;

        const outer_count = self.fill.iteratedFixedCount(loop.ast.inputs[0]) orelse return null;
        const inner_count = self.fill.iteratedFixedCount(inner.ast.inputs[0]) orelse return null;
        const written = std.math.mul(u64, outer_count, inner_count) catch return null;

        const body_node = inner.ast.then_expr;
        const body_first = tree.firstToken(body_node);
        const body_last = tree.lastToken(body_node);
        if (body_first > body_last or body_last >= tags.len) return null;
        if (self.bodyHasUnlabeledLoopExit(body_first, body_last)) return null;

        var body_stmt_buf: [2]Ast.Node.Index = undefined;
        const stmts = self.blockStmtList(body_node, &body_stmt_buf, null) orelse return null;
        var target_tok: Ast.TokenIndex = 0;
        var counter_tok: Ast.TokenIndex = 0;
        var stored = false;
        var advanced = false;
        for (stmts) |stmt| {
            if (self.counterIncrementToken(stmt)) |tok| {
                if (advanced) return null;
                counter_tok = tok;
                advanced = true;
                continue;
            }
            const w = self.counterFillAssignWrite(stmt) orelse continue;
            // A second counter lvalue means the body isn't the single
            // unconditional store this proof is about.
            if (stored) return null;
            if (!self.rhsIsDefined(w.rhs)) return null;
            target_tok = w.base_tok;
            stored = true;
        }
        if (!stored or !advanced) return null;
        const target_name = tree.tokenSlice(target_tok);
        const counter_name = tree.tokenSlice(counter_tok);
        if (std.mem.eql(u8, target_name, counter_name)) return null;
        if (self.identifierMentions(target_name, body_first, body_last) != 1) return null;
        if (self.identifierMentions(counter_name, body_first, body_last) != 2) return null;

        const target = self.name_to_local.get(target_name) orelse return null;
        if (self.name_to_local.get(counter_name) == null) return null;
        const target_decl = self.fill.declaredTypeSpanOfLocal(target) orelse return null;
        if (target_decl.is_const) return null;
        if (!target_decl.init_is_undefined) return null;
        if (target_decl.name_tok >= loop.ast.for_token) return null;
        const target_extent = self.fill.declaredExtent(target_decl.type) orelse return null;
        // Only a count that was EVALUATED can be multiplied against
        // the loops' trip counts; a `.vec` or `.collection` extent
        // names a declaration instead of stating a number.
        if (target_extent.number != written) return null;

        const counter = self.name_to_local.get(counter_name).?;
        const counter_decl = self.fill.declaredTypeSpanOfLocal(counter) orelse return null;
        if (counter_decl.is_const) return null;
        if (counter_decl.init_is_undefined) return null;
        if (counter_decl.name_tok >= loop.ast.for_token) return null;
        // The counting argument starts at 0.  Anything else leaves
        // the head of the target unwritten.
        const init = counter_decl.init orelse return null;
        if (init.first != init.last) return null;
        if (tags[init.first] != .number_literal) return null;
        const seed = std.fmt.parseInt(u64, tree.tokenSlice(init.first), 0) catch return null;
        if (seed != 0) return null;

        return .{
            .local = target,
            .pos = self.posOfToken(loop.ast.for_token),
            .end_pos = self.endPosOf(body_node),
        };
    }

    /// Statement list of a body that is written as a block, or the
    /// single statement of an unbraced body wrapped in `single`.
    /// Null for a body that is neither — the caller is answering
    /// "what does this loop's body execute", and an expression body
    /// executed per iteration is not a statement list this proof can
    /// take apart.
    fn blockStmtList(
        self: *const Builder,
        body_node: Ast.Node.Index,
        buf: *[2]Ast.Node.Index,
        single: ?*[1]Ast.Node.Index,
    ) ?[]const Ast.Node.Index {
        const tree = self.tree;
        return switch (tree.nodeTag(body_node)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => blockStmts(tree, body_node, buf),
            else => blk: {
                const slot = single orelse return null;
                slot[0] = body_node;
                break :blk slot[0..1];
            },
        };
    }

    /// `<local> += <literal 1>` written as a single top-level
    /// statement, returning the token naming the advanced local.
    /// Null for any other shape: a second counter, a `-=`, a `+=` of
    /// something that is not exactly one, or a compound assignment
    /// nested where an iteration could skip it.
    fn counterIncrementToken(self: *const Builder, stmt: Ast.Node.Index) ?Ast.TokenIndex {
        return counterIncrementTokenIn(self.tree, stmt);
    }

    fn counterIncrementTokenIn(tree: *const Ast, stmt: Ast.Node.Index) ?Ast.TokenIndex {
        const tags = tree.tokens.items(.tag);
        const tag = tree.nodeTag(stmt);
        if (tag != .assign_add and tag != .assign_add_wrap) return null;
        const lhs = tree.nodeData(stmt).node_and_node[0];
        const rhs = tree.nodeData(stmt).node_and_node[1];
        if (tree.nodeTag(lhs) != .identifier) return null;
        const tok = tree.nodeMainToken(lhs);
        const rhs_first = tree.firstToken(rhs);
        const rhs_last = tree.lastToken(rhs);
        if (rhs_first > rhs_last or rhs_last >= tags.len) return null;
        if (rhs_first != rhs_last) return null;
        if (tags[rhs_first] != .number_literal) return null;
        const step = std.fmt.parseInt(u64, tree.tokenSlice(rhs_first), 0) catch return null;
        if (step != 1) return null;
        return tok;
    }

    /// The top-level `<target>[<counter>] = <rhs>` statement of the
    /// inner body.  Exactly `name [ name ]` — a field chain, a
    /// pointer, or a range would name storage whose extent the
    /// counter's arithmetic does not describe.
    fn counterFillAssignWrite(
        self: *const Builder,
        stmt: Ast.Node.Index,
    ) ?FieldFillWrite {
        return counterFillAssignWriteIn(self.tree, stmt);
    }

    fn counterFillAssignWriteIn(tree: *const Ast, stmt: Ast.Node.Index) ?FieldFillWrite {
        const tags = tree.tokens.items(.tag);
        if (tree.nodeTag(stmt) != .assign) return null;
        const data = tree.nodeData(stmt).node_and_node;
        const lhs = data[0];
        const first = tree.firstToken(lhs);
        const last = tree.lastToken(lhs);
        if (first >= tags.len or last >= tags.len or first > last) return null;
        if (last != first + 3) return null;
        if (tags[first] != .identifier) return null;
        if (tags[first + 1] != .l_bracket) return null;
        if (tags[first + 2] != .identifier) return null;
        if (tags[first + 3] != .r_bracket) return null;
        return .{ .base_tok = first, .rhs = data[1] };
    }

    /// A returned count is a must-write certificate only when its complete
    /// canonical body maintains [0,count): seed zero, guarded adjacent
    /// store/push pairs, and positive-guarded pops. Calls and aliases decline.
    const CounterOutputProof = struct {
        tree: *const Ast,
        counter: []const u8,
        output: []const u8,
        /// For an array-pointer output, the one token spelling its element
        /// count. A guard against it is a guard against `output.len`.
        extent: ?Ast.TokenIndex = null,
        counter_declaration: Ast.Node.Index,
        scalars: [16][]const u8 = undefined,
        scalar_count: usize = 0,
        seeded: bool = false,
        pushed: bool = false,
        /// A `if (c < N) out[c] = v; c += 1;` pair lets `c` run past `N`, so
        /// the covered prefix is [0, min(c, N)). A returned count is then a
        /// certificate only after an `if (c > N) return null;` guard.
        capped: bool = false,
        strict_returns: bool = false,
        bounded: bool = false,

        fn names(self: *const CounterOutputProof, node: Ast.Node.Index, name: []const u8) bool {
            return self.tree.nodeTag(node) == .identifier and
                std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(node)), name);
        }

        fn scalar(self: *const CounterOutputProof, name: []const u8) bool {
            for (self.scalars[0..self.scalar_count]) |known| {
                if (std.mem.eql(u8, known, name)) return true;
            }
            return false;
        }

        fn addScalar(self: *CounterOutputProof, name: []const u8) bool {
            if (self.scalar_count == self.scalars.len or self.scalar(name)) return false;
            self.scalars[self.scalar_count] = name;
            self.scalar_count += 1;
            return true;
        }

        fn literal(self: *const CounterOutputProof, node: Ast.Node.Index, value: u64) bool {
            if (self.tree.nodeTag(node) != .number_literal) return false;
            const parsed = std.fmt.parseInt(u64, self.tree.tokenSlice(self.tree.nodeMainToken(node)), 0) catch return false;
            return parsed == value;
        }

        fn outputLen(self: *const CounterOutputProof, node: Ast.Node.Index) bool {
            if (self.extent) |token| {
                const tree = self.tree;
                if (tree.nodeTag(node) == .identifier and tree.tokenTag(token) == .identifier and
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), tree.tokenSlice(token))) return true;
                if (tree.tokenTag(token) == .number_literal) {
                    const wanted = std.fmt.parseInt(u64, tree.tokenSlice(token), 0) catch return false;
                    if (self.literal(node, wanted)) return true;
                }
            }
            if (self.tree.nodeTag(node) != .field_access) return false;
            const pair = self.tree.nodeData(node).node_and_token;
            return self.names(pair[0], self.output) and std.mem.eql(u8, self.tree.tokenSlice(pair[1]), "len");
        }

        fn positiveGuard(self: *const CounterOutputProof, node: Ast.Node.Index) bool {
            const tag = self.tree.nodeTag(node);
            if (tag != .greater_than and tag != .less_than and tag != .bang_equal) return false;
            const pair = self.tree.nodeData(node).node_and_node;
            return (self.names(pair[0], self.counter) and self.literal(pair[1], 0) and tag != .less_than) or
                (self.literal(pair[0], 0) and self.names(pair[1], self.counter) and tag != .greater_than);
        }

        fn capacityGuard(self: *const CounterOutputProof, node: Ast.Node.Index, full: bool) bool {
            const tag = self.tree.nodeTag(node);
            if (tag != .equal_equal and tag != .greater_or_equal and tag != .less_or_equal and
                tag != .less_than and tag != .greater_than) return false;
            const pair = self.tree.nodeData(node).node_and_node;
            if (self.names(pair[0], self.counter) and self.outputLen(pair[1])) {
                return if (full) tag == .equal_equal or tag == .greater_or_equal else tag == .less_than;
            }
            if (self.outputLen(pair[0]) and self.names(pair[1], self.counter)) {
                return if (full) tag == .equal_equal or tag == .less_or_equal else tag == .greater_than;
            }
            return false;
        }

        /// `c > N` / `N < c`: the returned-null arm leaves `c <= N`.
        fn overflowGuard(self: *const CounterOutputProof, node: Ast.Node.Index) bool {
            const tag = self.tree.nodeTag(node);
            if (tag != .greater_than and tag != .less_than) return false;
            const pair = self.tree.nodeData(node).node_and_node;
            return (self.names(pair[0], self.counter) and self.outputLen(pair[1]) and tag == .greater_than) or
                (self.outputLen(pair[0]) and self.names(pair[1], self.counter) and tag == .less_than);
        }

        /// `if (c < N) out[c] = rhs;`, with the store bare or alone in a block.
        fn guardedStore(self: *const CounterOutputProof, statement: Ast.Node.Index) ?FieldFillWrite {
            const branch = self.tree.fullIf(statement) orelse return null;
            if (branch.payload_token != null or branch.ast.else_expr != .none or
                !self.capacityGuard(branch.ast.cond_expr, false)) return null;
            var body = branch.ast.then_expr;
            var buffer: [2]Ast.Node.Index = undefined;
            switch (self.tree.nodeTag(body)) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => {
                    const inner = blockStmts(self.tree, body, &buffer);
                    if (inner.len != 1) return null;
                    body = inner[0];
                },
                else => {},
            }
            return counterFillAssignWriteIn(self.tree, body);
        }

        fn returnsNull(self: *const CounterOutputProof, node: Ast.Node.Index) bool {
            if (self.tree.nodeTag(node) != .@"return") return false;
            const value = self.tree.nodeData(node).opt_node.unwrap() orelse return false;
            return self.names(value, "null");
        }

        fn mutationToken(tag: std.zig.Token.Tag) bool {
            return switch (tag) {
                .equal, .ampersand, .keyword_asm => true,
                inline else => |known| comptime std.mem.endsWith(u8, @tagName(known), "_equal") and
                    !std.mem.eql(u8, @tagName(known), "equal_equal") and
                    !std.mem.eql(u8, @tagName(known), "bang_equal") and
                    !std.mem.eql(u8, @tagName(known), "angle_bracket_left_equal") and
                    !std.mem.eql(u8, @tagName(known), "angle_bracket_right_equal"),
            };
        }

        fn pure(self: *const CounterOutputProof, node: Ast.Node.Index, payload: bool) bool {
            const tree = self.tree;
            var token = tree.firstToken(node);
            const last = tree.lastToken(node);
            while (token <= last) : (token += 1) {
                const tag = tree.tokenTag(token);
                if (mutationToken(tag)) return false;
                switch (tag) {
                    .identifier => {
                        if (token > 0 and tree.tokenTag(token - 1) == .period) continue;
                        const name = tree.tokenSlice(token);
                        if (std.mem.eql(u8, name, "undefined")) return false;
                        if (std.mem.eql(u8, name, self.output)) {
                            if (payload or token + 2 > last or tree.tokenTag(token + 1) != .period or
                                !std.mem.eql(u8, tree.tokenSlice(token + 2), "len")) return false;
                        } else if (payload and !self.scalar(name) and
                            !std.mem.eql(u8, name, "true") and !std.mem.eql(u8, name, "false")) return false;
                    },
                    else => {},
                }
            }
            return true;
        }

        fn walk(self: *CounterOutputProof, node: Ast.Node.Index, capacity: bool, positive: bool, depth: usize) bool {
            if (depth == max_classify_depth) return false;
            const tree = self.tree;
            switch (tree.nodeTag(node)) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => {
                    const saved_scalars = self.scalar_count;
                    defer self.scalar_count = saved_scalars;
                    const saved_bounded = self.bounded;
                    defer self.bounded = saved_bounded;
                    var buffer: [2]Ast.Node.Index = undefined;
                    const statements = blockStmts(tree, node, &buffer);
                    var room = capacity;
                    var above_zero = positive;
                    var index: usize = 0;
                    while (index < statements.len) : (index += 1) {
                        const statement = statements[index];
                        if (tree.fullIf(statement)) |branch| {
                            if (branch.payload_token == null and branch.ast.else_expr == .none and
                                self.capacityGuard(branch.ast.cond_expr, true) and self.returnsNull(branch.ast.then_expr))
                            {
                                room = true;
                                continue;
                            }
                            if (branch.payload_token == null and branch.ast.else_expr == .none and
                                self.overflowGuard(branch.ast.cond_expr) and self.returnsNull(branch.ast.then_expr))
                            {
                                self.bounded = true;
                                continue;
                            }
                        }
                        if (counterFillAssignWriteIn(tree, statement)) |write| {
                            if (std.mem.eql(u8, tree.tokenSlice(write.base_tok), self.output)) {
                                if (!self.seeded or !room or index + 1 == statements.len or
                                    !std.mem.eql(u8, tree.tokenSlice(write.base_tok + 2), self.counter) or
                                    !self.pure(write.rhs, true)) return false;
                                const increment = counterIncrementTokenIn(tree, statements[index + 1]) orelse return false;
                                if (!std.mem.eql(u8, tree.tokenSlice(increment), self.counter)) return false;
                                self.pushed = true;
                                self.bounded = false;
                                room = false;
                                above_zero = false;
                                index += 1;
                                continue;
                            }
                        }
                        if (self.guardedStore(statement)) |write| {
                            if (std.mem.eql(u8, tree.tokenSlice(write.base_tok), self.output)) {
                                if (!self.seeded or index + 1 == statements.len or
                                    !std.mem.eql(u8, tree.tokenSlice(write.base_tok + 2), self.counter) or
                                    !self.pure(write.rhs, true)) return false;
                                const increment = counterIncrementTokenIn(tree, statements[index + 1]) orelse return false;
                                if (!std.mem.eql(u8, tree.tokenSlice(increment), self.counter)) return false;
                                self.pushed = true;
                                self.capped = true;
                                self.bounded = false;
                                room = false;
                                above_zero = false;
                                index += 1;
                                continue;
                            }
                        }
                        if (tree.nodeTag(statement) != .@"return") self.bounded = false;
                        if (!self.walk(statement, room, above_zero, depth + 1)) return false;
                        room = false;
                        above_zero = false;
                    }
                    return true;
                },
                .simple_var_decl, .local_var_decl, .aligned_var_decl, .global_var_decl => {
                    const declaration = tree.fullVarDecl(node).?;
                    const name = tree.tokenSlice(declaration.ast.mut_token + 1);
                    if (std.mem.eql(u8, name, self.output)) return false;
                    const value = declaration.ast.init_node.unwrap() orelse return false;
                    if (std.mem.eql(u8, name, self.counter)) {
                        const type_node = declaration.ast.type_node.unwrap() orelse return false;
                        if (node != self.counter_declaration or self.seeded or tree.tokenTag(declaration.ast.mut_token) != .keyword_var or
                            !self.names(type_node, "usize") or !self.literal(value, 0)) return false;
                        self.seeded = true;
                    }
                    if (!self.pure(value, true)) return false;
                    return self.addScalar(name);
                },
                .if_simple, .@"if" => {
                    const branch = tree.fullIf(node).?;
                    if (branch.payload_token != null or !self.pure(branch.ast.cond_expr, false)) return false;
                    const saved_scalars = self.scalar_count;
                    if (!self.walk(branch.ast.then_expr, capacity or self.capacityGuard(branch.ast.cond_expr, false), positive or self.positiveGuard(branch.ast.cond_expr), depth + 1)) return false;
                    self.scalar_count = saved_scalars;
                    if (branch.ast.else_expr.unwrap()) |other| {
                        if (!self.walk(other, capacity, positive, depth + 1)) return false;
                    }
                    self.scalar_count = saved_scalars;
                    return true;
                },
                .while_simple, .while_cont, .@"while" => {
                    const loop = tree.fullWhile(node).?;
                    if (loop.payload_token != null or !self.pure(loop.ast.cond_expr, false)) return false;
                    if (!self.walk(loop.ast.then_expr, capacity, positive or self.positiveGuard(loop.ast.cond_expr), depth + 1)) return false;
                    if (loop.ast.cont_expr.unwrap()) |continuation| {
                        if (!self.walk(continuation, false, false, depth + 1)) return false;
                    }
                    if (loop.ast.else_expr.unwrap()) |other| {
                        if (!self.walk(other, false, false, depth + 1)) return false;
                    }
                    return true;
                },
                .@"switch", .switch_comma => {
                    const selection = tree.fullSwitch(node).?;
                    if (!self.pure(selection.ast.condition, false)) return false;
                    for (selection.ast.cases) |case| {
                        const arm = tree.fullSwitchCase(case).?;
                        if (arm.payload_token != null or !self.walk(arm.ast.target_expr, capacity, positive, depth + 1)) return false;
                    }
                    return true;
                },
                .assign_add, .assign_add_wrap, .assign_sub, .assign_sub_wrap => {
                    const pair = tree.nodeData(node).node_and_node;
                    if (self.names(pair[0], self.counter)) {
                        return self.seeded and positive and self.literal(pair[1], 1) and
                            (tree.nodeTag(node) == .assign_sub or tree.nodeTag(node) == .assign_sub_wrap);
                    }
                    return tree.nodeTag(pair[0]) == .identifier and
                        self.scalar(tree.tokenSlice(tree.nodeMainToken(pair[0]))) and self.pure(pair[1], true);
                },
                .assign => {
                    const pair = tree.nodeData(node).node_and_node;
                    if (self.names(pair[0], self.counter) or tree.nodeTag(pair[0]) != .identifier) return false;
                    const name = tree.tokenSlice(tree.nodeMainToken(pair[0]));
                    return (std.mem.eql(u8, name, "_") or self.scalar(name)) and self.pure(pair[1], true);
                },
                .@"return" => {
                    const value = tree.nodeData(node).opt_node.unwrap() orelse return false;
                    return self.names(value, "null") or
                        (self.seeded and self.names(value, self.counter) and (!self.strict_returns or self.bounded));
                },
                else => return self.pure(node, false),
            }
        }
    };

    fn emitSuccessfulOutPrefix(self: *Builder, block: BlockId, count: LocalId, initializer: Ast.Node.Index) !void {
        const tree = self.tree;
        var value = initializer;
        while (tree.nodeTag(value) == .grouped_expression) value = tree.nodeData(value).node_and_token[0];
        if (tree.nodeTag(value) != .@"orelse") return;
        const operands = tree.nodeData(value).node_and_node;
        if (!fallbackYieldsNothing(self, operands[1])) return;
        const call = initShapeNode(self, operands[0]);
        var call_buffer: [1]Ast.Node.Index = undefined;
        const full_call = tree.fullCall(&call_buffer, call) orelse return;
        const cache = self.cache orelse return;
        const actual = self.queryOrUnknown(file_cache.FileCache.ActualCallSummary, cache.actualCallSummaryAt(fresh_storage.calleeQueryToken(tree, full_call), null)) orelse return;
        const declaring_cache = self.queryOrUnknown(*file_cache.FileCache, actual.declaringCache(cache)) orelse return;
        if (declaring_cache != cache) return;
        const source_tree = actual.callee.tree;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = source_tree.fullFnProto(&proto_buffer, actual.callee.declaration) orelse return;
        const return_type = proto.ast.return_type.unwrap() orelse return;
        const first_return = source_tree.firstToken(return_type);
        if (source_tree.lastToken(return_type) != first_return + 1 or source_tree.tokenTag(first_return) != .question_mark or
            !std.mem.eql(u8, source_tree.tokenSlice(first_return + 1), "usize")) return;
        const body = tokens.bodyOf(source_tree, actual.callee.declaration) orelse return;
        if (!self.calleeBodySpellsEveryStore(.{ .tree = source_tree, .fn_decl = actual.callee.declaration, .paths = &.{} })) return;
        var statement_buffer: [2]Ast.Node.Index = undefined;
        const statements = blockStmts(source_tree, body, &statement_buffer);
        if (statements.len == 0 or source_tree.nodeTag(statements[statements.len - 1]) != .@"return") return;
        const returned = source_tree.nodeData(statements[statements.len - 1]).opt_node.unwrap() orelse return;
        if (source_tree.nodeTag(returned) != .identifier) return;
        const counter_name = source_tree.tokenSlice(source_tree.nodeMainToken(returned));
        var counter_declaration: ?Ast.Node.Index = null;
        for (statements) |statement| {
            const declaration = source_tree.fullVarDecl(statement) orelse continue;
            if (!std.mem.eql(u8, source_tree.tokenSlice(declaration.ast.mut_token + 1), counter_name)) continue;
            if (counter_declaration != null) return;
            counter_declaration = statement;
        }
        const seed_declaration = counter_declaration orelse return;
        var parameters = proto.iterate(source_tree);
        var parameter_index: u32 = 0;
        while (parameters.next()) |parameter| : (parameter_index += 1) {
            const output_token = parameter.name_token orelse continue;
            const output_type = parameter.type_expr orelse continue;
            const first_type = source_tree.firstToken(output_type);
            const last_type = source_tree.lastToken(output_type);
            // `[]T` (its length is the capacity) or `*[N]T` with one token for N.
            const slice_output = last_type >= first_type + 2 and source_tree.tokenTag(first_type) == .l_bracket and
                source_tree.tokenTag(first_type + 1) == .r_bracket and source_tree.tokenTag(first_type + 2) != .keyword_const;
            const array_output = last_type >= first_type + 4 and source_tree.tokenTag(first_type) == .asterisk and
                source_tree.tokenTag(first_type + 1) == .l_bracket and source_tree.tokenTag(first_type + 3) == .r_bracket and
                (source_tree.tokenTag(first_type + 2) == .identifier or source_tree.tokenTag(first_type + 2) == .number_literal) and
                source_tree.tokenTag(first_type + 4) != .keyword_const;
            if (!slice_output and !array_output) continue;
            const output_name = source_tree.tokenSlice(output_token);
            var proof: CounterOutputProof = .{
                .tree = source_tree,
                .counter = counter_name,
                .output = output_name,
                .extent = if (array_output) first_type + 2 else null,
                .counter_declaration = seed_declaration,
            };
            var scalar_parameters = proto.iterate(source_tree);
            while (scalar_parameters.next()) |scalar_parameter| {
                const name_token = scalar_parameter.name_token orelse continue;
                const type_node = scalar_parameter.type_expr orelse continue;
                if (unsignedType(source_tree, type_node) and !proof.addScalar(source_tree.tokenSlice(name_token))) return;
            }
            const parameter_scalars = proof.scalar_count;
            if (!proof.walk(body, false, false, 0) or !proof.seeded or !proof.pushed) continue;
            if (proof.capped) {
                // A capped counter may exceed the output. The first pass found
                // such a push; the second requires every returned count to follow
                // an `if (count > capacity) return null;` guard.
                proof.strict_returns = true;
                proof.seeded = false;
                proof.pushed = false;
                proof.bounded = false;
                proof.scalar_count = parameter_scalars;
                if (!proof.walk(body, false, false, 0) or !proof.seeded or !proof.pushed) continue;
            }
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = self.queryOrUnknown(Ast.Node.Index, actual.callArgumentFor(cache, &argument_buffer, parameter_index)) orelse return;
            if (tree.nodeTag(argument) != .address_of) continue;
            const operand = tree.nodeData(argument).node;
            if (tree.nodeTag(operand) != .identifier) continue;
            const array = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(operand))) orelse continue;
            if (self.locals.items[@intFromEnum(array)].array_extent == null) continue;
            var inputs: [8]?LocalId = .{null} ** 8;
            var all_parameters = proto.iterate(source_tree);
            var input_parameter: u32 = 0;
            var supported = true;
            while (all_parameters.next()) |_| : (input_parameter += 1) {
                if (input_parameter == parameter_index) continue;
                const input = self.queryOrUnknown(Ast.Node.Index, actual.callArgumentFor(cache, &argument_buffer, input_parameter)) orelse return;
                supported = self.valueInputs(input, &inputs) and supported;
            }
            if (!supported) continue;
            self.locals.items[@intFromEnum(count)].is_unsigned = true;
            try self.appendStmt(block, .{
                .kind = .{ .array_prefix = .{ .array = array, .count = count, .inputs = inputs } },
                .pos = self.posOf(call),
                .end_pos = self.endPosOf(call),
            });
        }
    }

    /// Credit only the storage supplied to a resolved callee on its successful
    /// edge. The untouched suffix is not a whole-array store.
    fn emitSuccessfulSliceOutputs(self: *Builder, block: BlockId, call_node: Ast.Node.Index) LoweringError!void {
        const tree = self.tree;
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = zls_resolver_mod.TypeResolver.CallOperands.full(tree, &call_buffer, call_node) orelse return;
        const cache = self.cache orelse return;
        const actual = self.queryOrUnknown(file_cache.FileCache.ActualCallSummary, cache.actualCallSummaryAt(call.queryToken(tree, call_node), null)) orelse return;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(actual.callee.tree, &proto_buffer, actual.callee.declaration) orelse return;
        var parameters = proto.iterate(actual.callee.tree);
        var parameter_index: u32 = 0;
        while (parameters.next() != null) : (parameter_index += 1) {
            const argument = self.queryOrUnknown(Ast.Node.Index, actual.callArgumentFor(cache, &call_buffer, parameter_index)) orelse continue;
            const slice = tree.fullSlice(initShapeNode(self, argument)) orelse continue;
            if (slice.ast.sentinel != .none or self.integerValue(slice.ast.start) != 0) continue;
            const base = initShapeNode(self, slice.ast.sliced);
            if (tree.nodeTag(base) != .identifier) continue;
            const array = self.indexLocalAt(tree.nodeMainToken(base)) orelse continue;
            const extent = self.locals.items[@intFromEnum(array)].array_extent orelse continue;
            if (!self.localCanBeStored(array)) continue;
            const end = slice.ast.end.unwrap();
            const scaled = if (end) |value|
                self.scaledOutputIndexTokens(tree.firstToken(value), tree.lastToken(value))
            else
                null;
            const bound: cfg_types.IndexTerm = if (scaled) |element|
                .{ .local = .{ .local = element.index } }
            else if (end) |value|
                self.indexTerm(value)
            else
                .{ .constant = extent };
            if (bound == .unknown or (scaled != null and scaled.?.offset != 0)) continue;
            const initialized = cache.definiteCallParameterWrite(call_node, parameter_index) catch |err| {
                self.noteResolutionError(err);
                continue;
            };
            if (!initialized) continue;
            if (bound == .constant and bound.constant == extent) {
                try self.appendStmt(block, .{
                    .kind = .{ .array_complete = .{ .array = array } },
                    .pos = self.posOf(argument),
                    .end_pos = self.endPosOf(argument),
                });
                continue;
            }
            const count: LocalId = switch (bound) {
                .local => |local| blk: {
                    if (local.offset != 0 or !self.locals.items[@intFromEnum(local.local)].is_unsigned) continue;
                    // A live local is not the slice length evaluated before
                    // a call that can write through an escaped address.
                    if (self.locals.items[@intFromEnum(local.local)].address_taken) continue;
                    break :blk local.local;
                },
                .constant => |value| blk: {
                    if (value > extent) continue;
                    const local = try self.appendLocal(.{
                        .name = "<successful output slice length>",
                        .decl_pos = self.posOf(argument),
                        .is_control_local = true,
                        .is_unsigned = true,
                    });
                    try self.appendStmt(block, .{
                        .kind = .{ .decl = .{
                            .local = local,
                            .init_kind = .plain,
                            .integer_value = value,
                            .value_defined = true,
                        } },
                        .pos = self.posOf(argument),
                        .end_pos = self.endPosOf(argument),
                    });
                    break :blk local;
                },
                else => continue,
            };
            try self.appendStmt(block, .{
                .kind = .{ .array_prefix = .{ .array = array, .count = count, .scale = if (scaled) |element| element.scale else 1 } },
                .pos = self.posOf(argument),
                .end_pos = self.endPosOf(argument),
            });
        }
    }

    /// The top-level `<target>[<index expr>] = <rhs>` statement of a
    /// body whose index expression is ARITHMETIC rather than a bare
    /// capture.  The base still has to be a bare identifier — a field
    /// chain, a pointer or a deref names storage whose extent the
    /// index's arithmetic says nothing about — but the subscript may be
    /// any expression, because it is the caller that has to place it.
    fn subscriptFillAssignWrite(
        self: *const Builder,
        stmt: Ast.Node.Index,
    ) ?FieldFillWrite {
        const tree = self.tree;
        if (tree.nodeTag(stmt) != .assign) return null;
        const data = tree.nodeData(stmt).node_and_node;
        if (tree.nodeTag(data[0]) != .array_access) return null;
        if (tree.nodeTag(tree.nodeData(data[0]).node_and_node[0]) != .identifier) return null;
        return .{
            .base_tok = tree.nodeMainToken(tree.nodeData(data[0]).node_and_node[0]),
            .rhs = data[1],
            .lhs = data[0],
        };
    }

    /// The counting argument a counter-driven `while` plus the check
    /// that closes it makes:
    ///
    ///     var fields: [N]E = undefined;
    ///     var count: usize = 0;
    ///     while (cond) |field| {
    ///         if (count == N) return false;
    ///         fields[count] = field;
    ///         count += 1;
    ///     }
    ///     if (count != N) return false;
    ///     use(fields);            // ← fully initialized here
    ///
    /// The counter starts at zero and advances by exactly one per
    /// iteration, so its value IS the number of elements written.  The
    /// check inside the body keeps the counter below `N`, so those
    /// writes stay in range; and the check after the loop means the
    /// ONLY way to reach the use is `count == N` — that is, exactly
    /// `N` iterations, that is, all of `[0, N)`.  The generic CFG sees
    /// a loop that may run zero times and a `while` whose exit leaves
    /// the target as `.undef`, which is why it needs saying.
    ///
    /// Load-bearing clauses; dropping any one leaves a path that reads
    /// a partially written target:
    ///   - the `if` is the IMMEDIATE next sibling of the `while` in
    ///     one statement list, so it dominates everything below it;
    ///   - its condition is `<counter> != <N>` and its other arm is a
    ///     bare `return`.  Anything that falls through instead would
    ///     reach the use with `count != N`, and the count would say
    ///     nothing about how much was written;
    ///   - `N` resolves to a NUMBER, the same number at both sites,
    ///     and it is the target's declared element count — so "the
    ///     counter reached the length" and "the array has that many
    ///     elements" are the same statement, not two spellings;
    ///   - the body is exactly those three statements: the guard, the
    ///     store at the counter, and the increment.  An extra mention
    ///     of either name, or any other way to advance or skip the
    ///     counter, would break "the counter's value is the number of
    ///     elements written";
    ///   - the counter is a `var` seeded with the literal `0` and the
    ///     target a `var` seeded with `undefined`, both declared
    ///     before the `while`;
    ///   - the body holds no UNLABELED `break` / `continue`: one would
    ///     end the loop, or skip the increment, and the counter would
    ///     stop describing what was written.
    ///
    /// `try` and `return` INSIDE the body are neither rejected nor
    /// credited — they leave the function, so they never reach the
    /// post-loop check at all.
    fn countedFillGuard(self: *Builder, while_node: Ast.Node.Index, if_node: Ast.Node.Index) ?CountedFillCredit {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const while_tag = tree.nodeTag(while_node);
        if (while_tag != .while_simple and while_tag != .while_cont and while_tag != .@"while") return null;
        const if_tag = tree.nodeTag(if_node);
        if (if_tag != .if_simple and if_tag != .@"if") return null;
        const branch = tree.fullIf(if_node) orelse return null;
        if (branch.payload_token != null) return null;
        // Only the FALL-THROUGH arm is credited, so the arm that
        // leaves the function must leave it.
        if (tree.nodeTag(branch.ast.then_expr) != .@"return") return null;
        // `count != N` is what makes the fall-through mean `count == N`;
        // the opposite spelling would credit the `count == N` arm.
        if (tree.nodeTag(branch.ast.cond_expr) != .bang_equal) return null;
        const post = self.counterCompare(branch.ast.cond_expr) orelse return null;

        const counter_name = tree.tokenSlice(post.counter);
        const counter = self.name_to_local.get(counter_name) orelse return null;
        const counter_decl = self.fill.declaredTypeSpanOfLocal(counter) orelse return null;
        if (counter_decl.is_const or counter_decl.init_is_undefined) return null;
        if (counter_decl.name_tok >= tree.firstToken(while_node)) return null;
        const seed = counter_decl.init orelse return null;
        if (seed.first != seed.last or seed.first >= tags.len) return null;
        if (tags[seed.first] != .number_literal) return null;
        const seed_value = std.fmt.parseInt(u64, tree.tokenSlice(seed.first), 0) catch return null;
        if (seed_value != 0) return null;

        const loop = tree.fullWhile(while_node) orelse return null;
        if (loop.label_token != null) return null;
        const body = loop.ast.then_expr;
        const body_first = tree.firstToken(body);
        const body_last = tree.lastToken(body);
        if (body_first > body_last or body_last >= tags.len) return null;
        if (self.bodyHasUnlabeledLoopExit(body_first, body_last)) return null;

        var stmt_buf: [2]Ast.Node.Index = undefined;
        var single_buf: [1]Ast.Node.Index = undefined;
        const stmts = self.blockStmtList(body, &stmt_buf, &single_buf) orelse return null;
        var guarded = false;
        var stored = false;
        var advanced = false;
        var target: ?LocalId = null;
        for (stmts) |stmt| {
            if (self.counterIncrementToken(stmt)) |tok| {
                if (advanced or !std.mem.eql(u8, tree.tokenSlice(tok), counter_name)) return null;
                advanced = true;
                continue;
            }
            if (self.counterFillAssignWrite(stmt)) |w| {
                if (stored) return null;
                const name = tree.tokenSlice(w.base_tok);
                if (std.mem.eql(u8, name, counter_name)) return null;
                // `counterFillAssignWrite` already fixed the shape at
                // exactly `name [ name ]`, so `base_tok + 2` IS the
                // subscript; anything else is not a store at the
                // counter.
                if (!std.mem.eql(u8, tree.tokenSlice(w.base_tok + 2), counter_name)) return null;
                if (!self.rhsIsDefined(w.rhs)) return null;
                const local = self.name_to_local.get(name) orelse return null;
                const decl = self.fill.declaredTypeSpanOfLocal(local) orelse return null;
                if (decl.is_const or !decl.init_is_undefined) return null;
                if (decl.name_tok >= tree.firstToken(while_node)) return null;
                const extent = self.fill.declaredExtent(decl.type) orelse return null;
                // "The counter reached N" and "the target has N
                // elements" have to be the same number.
                if (extent.number != post.value) return null;
                target = local;
                stored = true;
                continue;
            }
            const guard_tag = tree.nodeTag(stmt);
            if (guard_tag != .if_simple and guard_tag != .@"if") return null;
            const guard = tree.fullIf(stmt) orelse return null;
            if (guard.payload_token != null) return null;
            if (tree.nodeTag(guard.ast.then_expr) != .@"return") return null;
            if (tree.nodeTag(guard.ast.cond_expr) != .equal_equal) return null;
            const inner = self.counterCompare(guard.ast.cond_expr) orelse return null;
            // The two comparisons are two source SITES, so their
            // identifier tokens are two different token indices.  What
            // has to be the same counter is the BINDING the two spell,
            // and that is the name — comparing the indices instead can
            // never be equal, which silently refuses every counting
            // loop this proof exists for.
            if (!std.mem.eql(u8, tree.tokenSlice(inner.counter), counter_name)) return null;
            if (inner.value != post.value) return null;
            guarded = true;
        }
        if (!guarded or !stored or !advanced) return null;
        const local = target.?;
        const target_name = self.locals.items[@intFromEnum(local)].name;
        if (self.identifierMentions(target_name, body_first, body_last) != 1) return null;
        // Guard compare, subscript, increment: three and no more.
        if (self.identifierMentions(counter_name, body_first, body_last) != 3) return null;
        return .{
            .local = local,
            .pos = self.posOf(while_node),
            .end_pos = self.endPosOf(if_node),
        };
    }

    /// One side of a `<counter> == <n>` comparison: the token naming
    /// the mutable local being counted, and the value the other side
    /// states.  Null unless exactly one side is an identifier this
    /// evaluator cannot read as a comptime integer — which is what
    /// makes it a counter rather than another const — and the other
    /// side does evaluate.  `a == b` with both sides comptime has no
    /// counter at all and does not answer.
    fn counterCompare(self: *const Builder, cond: Ast.Node.Index) ?struct { counter: Ast.TokenIndex, value: u64 } {
        const tree = self.tree;
        const pair = tree.nodeData(cond).node_and_node;
        var counter: ?Ast.TokenIndex = null;
        var value: ?u64 = null;
        inline for (pair) |side| {
            const first = tree.firstToken(side);
            const last = tree.lastToken(side);
            if (first > last) return null;
            const resolved = self.fill.comptimeIntTokens(.{ .first = first, .last = last }, 0);
            if (tree.nodeTag(side) == .identifier and resolved == null) {
                if (counter != null) return null;
                counter = tree.nodeMainToken(side);
            } else {
                const n = resolved orelse return null;
                if (value != null) return null;
                value = n;
            }
        }
        return .{ .counter = counter orelse return null, .value = value orelse return null };
    }

    // ── Defined-under-guard: the same condition, tested twice ─────

    /// Ceiling on how many rooted paths one guard condition may read.
    /// A condition over a handful of locals and their fields is a
    /// condition; one walking a data structure is not.
    const max_guard_operands = 8;

    /// Longest field path one guard operand may walk.  A condition
    /// reads what a hand-built descriptor takes — a handful of steps
    /// like `self.grammar.stack.len` — and a longer chain is a data
    /// structure walked at runtime, not a rooted path two conditions
    /// can be compared by.  Past the bound a path is DECLINED rather
    /// than truncated, so a guard over a deeper chain loses its
    /// pairing instead of pairing on a shortened one.  The same
    /// ceiling `comptime_fill` puts on the field paths it walks.
    const max_fill_path_fields = 8;

    /// A rooted path a guard condition reads: the root identifier and
    /// the field names walked from it.  For
    /// `saved_top < self.grammar.stack.len` the two operands are
    /// `saved_top` and `self.grammar.stack.len` — and the second is
    /// what makes the pair interesting, because `self.grammar` is
    /// assigned between the two tests.
    const OperandPath = struct {
        /// The NAME the root is written with, not its token.  Two
        /// conditions are compared by reading the same binding, and
        /// each condition spells that binding at its own source site —
        /// so `self` in `self.nextCore()` and `self` in the condition
        /// are different tokens naming one thing.  A token index
        /// compares positions, which never match across two sites and
        /// so would silently refuse every pairing through a field.
        root_name: []const u8,
        fields: [max_fill_path_fields][]const u8,
        field_count: u8,
    };

    /// One re-tested condition, as seen by one of the `if`s reading it.
    const GuardFact = struct {
        guard: GuardId,
        /// True when this `if`'s condition is the value's NEGATION —
        /// spelled as a `!` prefix or as the complementary equality.
        negated: bool,
    };

    /// Do two `if` conditions read ONE value, and is the second the
    /// first's negation?  Null when they are two different values,
    /// `false` when they are the same expression and `true` when the
    /// second holds exactly where the first does not.  Every clause
    /// below is about identity rather than appearance:
    ///   - the token streams MATCH, with at most ONE differing token
    ///     and that token a place the two spell opposite things.  The
    ///     lowering has no name resolution for `self.grammar.stack.len`
    ///     and inventing one would be a second, weaker notion of "the
    ///     same condition", so the comparison is over spelling.
    ///
    ///     A `!` PREFIX is not a differing token: `if (already_recorded)`
    ///     and `if (!already_recorded)` are the same value read two
    ///     ways, and the branch that tests one while the other names
    ///     the other is the mutual-exclusion shape this whole mechanism
    ///     exists for.  It is peeled as a `bool_not` NODE rather than as
    ///     a leading token, because `!a == b` is `(!a) == b`: taking the
    ///     token would rewrite it to `a == b`, which is a different
    ///     condition entirely.
    ///
    ///     Nothing declared BETWEEN the two may shadow a name either
    ///     reads; a block-local `const top` would make the second
    ///     condition a different value entirely.
    ///   - neither condition CALLS anything, raises `try`, or reads a
    ///     subscript.  A condition with effects is not a value that
    ///     can be read twice and compared; a subscript condition is
    ///     load-bearing storage this scan cannot reason about.
    fn guardConditionPolarity(self: *const Builder, a: Ast.Node.Index, b: Ast.Node.Index) ?bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const sa = stripNots(tree, a);
        const sb = stripNots(tree, b);
        const a_first = tree.firstToken(sa.expr);
        const a_last = tree.lastToken(sa.expr);
        const b_first = tree.firstToken(sb.expr);
        const b_last = tree.lastToken(sb.expr);
        if (a_first > a_last or b_first > b_last) return null;
        if (a_last - a_first != b_last - b_first) return null;
        if (!self.conditionIsPure(tree, a_first, a_last)) return null;
        if (!self.conditionIsPure(tree, b_first, b_last)) return null;
        // A swapped operator only counts at the expression's OWN level:
        // `a == (b != c)` compares two values and the `!=` inside the
        // parens is not a negation of anything this walk can place.
        var depth: u32 = 0;
        var swapped = false;
        var t = a_first;
        while (t <= a_last and t < tags.len) : (t += 1) {
            const at = b_first + (t - a_first);
            switch (tags[t]) {
                .l_paren, .l_bracket, .l_brace => depth += 1,
                .r_paren, .r_bracket, .r_brace => {
                    if (depth > 0) depth -= 1;
                },
                else => {},
            }
            if (std.mem.eql(u8, tree.tokenSlice(t), tree.tokenSlice(at))) continue;
            if (swapped or depth != 0) return null;
            if (!tokensAreComplementary(tags[t], tags[at])) return null;
            swapped = true;
        }
        // A `!` parity difference and a swapped operator are each ONE
        // flip of the value, and both together are no flip at all.
        if (self.rangeDeclaresAnyOf(tree, a_last + 1, b_first - 1, a_first, a_last)) return null;
        return (sa.negated != sb.negated) != swapped;
    }

    /// Do these two token tags say opposite things about one value?
    ///
    /// ONLY EQUALITY IS OFFERED.  `==` and `!=` are each other's
    /// negation for every type the language has, NaN included.  The
    /// ORDER comparisons are not: `NaN < x` and `NaN >= x` are both
    /// false, so they are not each other's negation and pairing them
    /// would cut a path the program really can take.
    fn tokensAreComplementary(a: std.zig.Token.Tag, b: std.zig.Token.Tag) bool {
        return (a == .equal_equal and b == .bang_equal) or
            (a == .bang_equal and b == .equal_equal);
    }

    /// The expression a chain of `bool_not` nodes wraps, and whether it
    /// took an odd number of negations to get there.
    fn stripNots(tree: *const Ast, node: Ast.Node.Index) struct { expr: Ast.Node.Index, negated: bool } {
        var cur = node;
        var negated = false;
        while (tree.nodeTag(cur) == .bool_not) {
            cur = tree.nodeData(cur).node;
            negated = !negated;
        }
        return .{ .expr = cur, .negated = negated };
    }

    /// Can evaluating [first, last] assign to a local? Calls, `try`, blocks and
    /// `catch`/`orelse` handlers can; a subscript read cannot (an index that
    /// calls still contains a paren). Used to keep the left operand of `and` /
    /// `or` assumed after the right operand ran, unlike [conditionIsPure],
    /// which also guards against changed array contents between two tests.
    fn conditionCannotAssign(tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
        const tags = tree.tokens.items(.tag);
        var t = first;
        while (t <= last and t < tags.len) : (t += 1) {
            switch (tags[t]) {
                .l_paren,
                .l_brace,
                .question_mark,
                .keyword_try,
                .keyword_catch,
                .keyword_orelse,
                => return false,
                else => {},
            }
        }
        return true;
    }

    /// A condition built only from reads: no calls, no `try`, no
    /// subscripts, no blocks.  Every one of those is a place the value
    /// of the expression can change without anything being assigned.
    fn conditionIsPure(self: *const Builder, tree: *const Ast, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
        const tags = tree.tokens.items(.tag);
        _ = self;
        var t = first;
        while (t <= last and t < tags.len) : (t += 1) {
            switch (tags[t]) {
                .l_paren,
                .l_bracket,
                .l_brace,
                .question_mark,
                .keyword_try,
                .keyword_catch,
                .keyword_orelse,
                => return false,
                else => {},
            }
        }
        return true;
    }

    /// Does [first, last] declare any name the condition [cond_first,
    /// cond_last] reads?  A `const`/`var`/capture between two tests of
    /// "the same" condition would shadow one of its operands.
    fn rangeDeclaresAnyOf(
        self: *const Builder,
        tree: *const Ast,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
        cond_first: Ast.TokenIndex,
        cond_last: Ast.TokenIndex,
    ) bool {
        _ = self;
        const tags = tree.tokens.items(.tag);
        if (first > last or last >= tags.len) return false;
        var t = first;
        while (t <= last) : (t += 1) {
            switch (tags[t]) {
                .keyword_const, .keyword_var => {
                    if (t + 1 <= last and tags[t + 1] == .identifier and
                        nameIsReadBy(tree, tree.tokenSlice(t + 1), cond_first, cond_last)) return true;
                },
                .pipe => {
                    var u = t + 1;
                    var want_name = true;
                    var steps: usize = 0;
                    while (u <= last and steps < 8) : (steps += 1) {
                        switch (tags[u]) {
                            .asterisk, .keyword_noalias => u += 1,
                            .comma => {
                                u += 1;
                                want_name = true;
                            },
                            .identifier => {
                                if (want_name and nameIsReadBy(tree, tree.tokenSlice(u), cond_first, cond_last)) return true;
                                u += 1;
                                want_name = false;
                            },
                            else => break,
                        }
                    }
                },
                else => {},
            }
        }
        return false;
    }

    /// The rooted paths a condition reads, or null when it reads more
    /// than [max_guard_operands] of them or any of them through a
    /// subscript (which [conditionIsPure] already rejects).
    fn guardOperandPaths(self: *const Builder, cond: Ast.Node.Index, out: *[max_guard_operands]OperandPath) ?usize {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const first = tree.firstToken(cond);
        const last = tree.lastToken(cond);
        if (first > last or last >= tags.len) return null;
        var count: usize = 0;
        var t = first;
        while (t <= last) {
            if (tags[t] != .identifier or (t > first and tags[t - 1] == .period)) {
                t += 1;
                continue;
            }
            if (count == max_guard_operands) return null;
            var path = OperandPath{ .root_name = tree.tokenSlice(t), .fields = undefined, .field_count = 0 };
            var u = t + 1;
            while (u + 1 <= last and tags[u] == .period and tags[u + 1] == .identifier) {
                if (path.field_count == max_fill_path_fields) return null;
                path.fields[path.field_count] = tree.tokenSlice(u + 1);
                path.field_count += 1;
                u += 2;
            }
            out[count] = path;
            count += 1;
            t = u;
        }
        return count;
    }

    /// Could any operand of `est`'s condition read DIFFERENTLY at
    /// `use`'s?
    ///
    /// The claim being made is that two tests of one expression agree,
    /// and an assignment to anything they read is the obvious way that
    /// breaks.  So every statement between them is read as an event on
    /// the operands, and each operand keeps a `pinned` flag saying
    /// whether the value it would read is still the one the first test
    /// saw.  Two things move that flag:
    ///
    ///   - an ordinary store, or a call that reaches the storage an
    ///     operand reads, CLEARS it.  What a call reaches is read from
    ///     the callee's own declaration — [callWritesOperand] — rather
    ///     than from the spelling of the call, because the spelling
    ///     says which handle was used and not what was done with it;
    ///   - a SAVE-RESTORE — `const saved = <path>;` before the first
    ///     test, then `<path> = saved;` — SETS it again.  That is the
    ///     whole of the idiom this exists for:
    ///
    ///         const saved_grammar = self.grammar;   // save
    ///         if (top < self.grammar.stack.len) { … }
    ///         self.nextEventCore() catch |err| { … };
    ///         self.grammar = saved_grammar;           // restore
    ///         if (top < self.grammar.stack.len) { use(saved_frame); }
    ///
    ///     The call in the middle really can resize the stack; what
    ///     makes the second test agree with the first is that the
    ///     restore puts `self.grammar` back exactly as the save found
    ///     it, so everything the call did to it is undone.  A restore
    ///     is only accepted when the saved `const` really is a copy of
    ///     that path, was declared before the first test, and nothing
    ///     wrote the path between the save and the test.
    ///
    /// Two things are deliberately not events, because neither can
    /// change a value an expression reads:
    ///
    ///   - a store into an ELEMENT, `path[i] = …`.  Assigning a slot of
    ///     an array or slice changes its contents, not its length and
    ///     not any scalar field;
    ///   - a store into a path that DIVERGES from every operand —
    ///     `self.grammar.failure_offset` beside an operand
    ///     `self.grammar.stack.len` share a root and nothing else.
    ///
    /// A `defer` or `errdefer` between the two tests makes the answer
    /// "nobody knows": the body runs at scope exit, which may be after
    /// the second test, and nothing here orders the two.
    fn guardOperandsStable(self: *Builder, est: Ast.Node.Index, use: Ast.Node.Index) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var operands: [max_guard_operands]OperandPath = undefined;
        const branch = tree.fullIf(est) orelse return false;
        const count = self.guardOperandPaths(branch.ast.cond_expr, &operands) orelse return false;
        if (count == 0) return false;
        var pinned: [max_guard_operands]bool = [_]bool{true} ** max_guard_operands;

        // THE ESTABLISHING `if` SCANS TOO, both arms of it.  Its body
        // runs between the two tests on the arm that took it, and a
        // store there moves exactly what the second test reads:
        //
        //     if (cache.slot != null) { cache.destroy(); }  // slot = null
        //     if (cache.slot != null) { … }
        //
        // Starting after the closing brace left that release
        // invisible, so the pair read as stable on the one path where
        // it is least true: the second test could not fail where the
        // first one held.  #55 is that shape — a `destroy` that writes
        // `slot` sits inside the very branch the second test claims to
        // contradict.
        const est_first = tree.firstToken(est);
        const est_last = tree.lastToken(est);
        const use_first = tree.firstToken(use);
        if (est_first >= use_first) return false;
        var t = est_first + 1;
        while (t < use_first and t < tags.len) : (t += 1) {
            const tag = tags[t];
            if (tag == .keyword_defer or tag == .keyword_errdefer) return false;
            const is_store = tag == .equal or isCompoundAssign(tag);
            // Only a `(` directly after a name is a call; after a
            // keyword (`if (`) or an operator it is grouping, and
            // treating that as a mutation would make the scan refuse
            // the very `if (COND)` it is scanning past.
            const is_call = tag == .l_paren and t > 0 and tags[t - 1] == .identifier;
            if (!is_store and !is_call) continue;
            const chain = self.lhsChainBefore(t) orelse return false;
            const base = guardOperandOf(tree, chain.span) orelse return false;
            // Once per call site, not once per operand: pinning a
            // method is a file-model lookup and reading its body is a
            // token scan, and every operand of this condition is asking
            // the same question of it.
            const writes = if (is_call) self.resolvedCalleeWrites(base) else null;
            var i: usize = 0;
            while (i < count) : (i += 1) {
                if (is_call) {
                    if (self.callWritesOperand(t, base, writes, operands[i])) pinned[i] = false;
                    continue;
                }
                // An element store moves no value a condition reads.
                if (chain.indexed) continue;
                // A restore INSIDE either arm puts back what the FIRST
                // test saw, not what the second will: that condition
                // was read before the arm ran.  Only a restore after
                // the whole `if` can make the two tests agree, so the
                // save-restore idiom keeps its scope and the arm does
                // not borrow it.
                if (t > est_last and tag == .equal and self.isSaveRestore(tree, base, t, est_first)) {
                    if (pathIsPrefix(base, operands[i])) pinned[i] = true;
                    continue;
                }
                if (pathsTouch(base, operands[i])) pinned[i] = false;
            }
        }
        for (pinned[0..count]) |flag| {
            if (!flag) return false;
        }
        return true;
    }

    /// A call site's own write paths, or null when it has to be treated
    /// as reaching everything it was handed.  Taken once per call site
    /// by [resolvedCalleeWrites] and shared by every operand.
    const CalleeWrites = struct {
        paths: []const fn_summary.ParamPath,
        tree: *const Ast,
        fn_decl: Ast.Node.Index,
    };

    /// Could the call whose `(` is `paren` write the storage `operand`
    /// reads?  `writes` is that call site's [CalleeWrites], or null.
    ///
    /// THE RECEIVER AND THE ARGUMENTS ARE DIFFERENT HANDLES, and only
    /// the first one is named by the callee expression.  Reading the
    /// call as "whatever shares a root with the callee" covered the
    /// receiver and nothing else, so a call that was handed the
    /// operand's storage as an ordinary argument — `consume(cache)`,
    /// `self.reset(holder)` — moved nothing on the record, and the
    /// operand stayed pinned across a write it could not survive.  So
    /// each top-level argument is a site of its own here, rooted at
    /// the chain that argument spells.
    fn callWritesOperand(
        self: *const Builder,
        paren: Ast.TokenIndex,
        callee: OperandPath,
        writes: ?CalleeWrites,
        operand: OperandPath,
    ) bool {
        // The receiver: `cache.destroy()` hands the callee the storage
        // `cache` names, and the last field of the callee path is the
        // method name rather than a step of that walk.
        if (callee.field_count > 0 and std.mem.eql(u8, callee.root_name, operand.root_name)) {
            var recv: OperandPath = .{
                .root_name = callee.root_name,
                .fields = undefined,
                .field_count = @intCast(callee.field_count - 1),
            };
            var k: usize = 0;
            while (k < recv.field_count) : (k += 1) recv.fields[k] = callee.fields[k];
            if (calleeWritesThrough(writes, recv, 0, operand)) return true;
        }
        // The arguments, read only when there is something to read:
        // without `writes`, an argument sharing the operand's root is
        // an event on it outright — the answer a callee of unknown
        // effect has to give.
        var args: [max_guard_operands]GuardArg = undefined;
        const argc = self.guardCallArgs(paren, &args) orelse return true;
        for (args[0..argc]) |arg| {
            if (!std.mem.eql(u8, arg.chain.root_name, operand.root_name)) continue;
            if (calleeWritesThrough(writes, arg.chain, arg.param, operand)) return true;
        }
        return false;
    }

    /// One top-level argument of a call, in the parameter index the
    /// callee names its writes in.
    const GuardArg = struct { chain: OperandPath, param: u32 };

    /// The chains the call whose `(` is `paren` hands over, each with
    /// the parameter index it is passed at, counting the receiver as
    /// parameter 0 the way a method's own declaration does.  An
    /// argument that is not a plain dotted chain is left out — it
    /// cannot name an operand's root — and the index is only read when
    /// the callee resolved AS THAT METHOD; otherwise the caller keeps
    /// the argument's root and drops the index.
    fn guardCallArgs(self: *const Builder, paren: Ast.TokenIndex, out: *[max_guard_operands]GuardArg) ?usize {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const last = std.math.cast(Ast.TokenIndex, tree.tokens.len -| 1) orelse return null;
        const rp = tokens.matchParen(tags, paren, last) orelse return null;
        var count: usize = 0;
        var ordinal: usize = 0;
        var t = paren + 1;
        while (t < rp) {
            var depth: u32 = 0;
            var end = t;
            while (end < rp) : (end += 1) {
                switch (tags[end]) {
                    // SENTINEL BRACKETS ARE NOT COUNTED, and cannot
                    // need to be: `[:0]T` is a type, and a type is not
                    // an argument of a call.  Leaving them out keeps
                    // the open/close set to the delimiters an
                    // expression can actually contain.
                    .l_paren, .l_brace, .l_bracket => depth += 1,
                    .r_paren, .r_brace, .r_bracket => {
                        if (depth == 0) return null;
                        depth -= 1;
                    },
                    .comma => if (depth == 0) break,
                    else => {},
                }
            }
            // An argument that runs to the last token before `)` ends
            // AT that token, not at `rp` — reading the closing paren as
            // part of the chain would drop the final argument of every
            // single-argument call, which is the common case.
            const span_last = @min(rp - 1, if (end < rp and tags[end] == .comma) end - 1 else end);
            if (t <= span_last) {
                if (count == max_guard_operands) return null;
                const chain = guardOperandOf(tree, .{ .first = t, .last = span_last });
                if (chain) |arg| {
                    out[count] = .{ .chain = arg, .param = @intCast(ordinal + 1) };
                    count += 1;
                }
            }
            ordinal += 1;
            t = end + 1;
        }
        return count;
    }

    /// Could a call write what `operand` reads, given that the caller
    /// handed it `site` as parameter `param`?
    ///
    /// NO `writes` IS "YES".  A call site that could not pin its callee
    /// to a declaration, or whose declaration does not spell out every
    /// store it can do, or that declares no write at all, is treated
    /// as reaching the storage it was handed, so the guard is refused
    /// rather than credited.
    fn calleeWritesThrough(writes: ?CalleeWrites, site: OperandPath, param: u32, operand: OperandPath) bool {
        const w = writes orelse return true;
        var tail: [max_fill_path_fields][]const u8 = undefined;
        var mapped: OperandPath = .{ .root_name = site.root_name, .fields = undefined, .field_count = 0 };
        for (w.paths) |p| {
            if (p.param != param) continue;
            // `self.* = other` stores the WHOLE object the parameter
            // names, so every field below it moves and no narrower
            // answer exists.
            if (p.path.len == 0) return true;
            const n = guardPathFieldNames(p.path, &tail) orelse return true;
            mapped.field_count = 0;
            var k: usize = 0;
            while (k < site.field_count) : (k += 1) {
                if (mapped.field_count == max_fill_path_fields) return true;
                mapped.fields[mapped.field_count] = site.fields[k];
                mapped.field_count += 1;
            }
            k = 0;
            while (k < n) : (k += 1) {
                if (mapped.field_count == max_fill_path_fields) return true;
                mapped.fields[mapped.field_count] = tail[k];
                mapped.field_count += 1;
            }
            if (pathsTouch(mapped, operand)) return true;
        }
        return false;
    }

    /// The write paths of the method `callee` names, read from the
    /// declaration it resolves to — or null, which is the call site's
    /// answer "it may write anything it was handed".
    ///
    /// NULL COVERS SEVERAL ABSENCES and none of them is an answer that
    /// nothing moves: a callee no declaration was found for; a body
    /// that CALLS anything, which can write through the call and whose
    /// direct list therefore does not say it does not; a body that
    /// declares no write, where an empty list is the absence of an
    /// OBSERVED effect rather than a proof of purity; and a receiver
    /// this function does not track or cannot type.
    ///
    /// What it hands back stays readable for as long as this Builder's
    /// cache does: `FileCache` copies a foreign declaration's paths
    /// into an arena that outlives the analysis that read them, and a
    /// same-file declaration's are borrowed from that file's own
    /// source.
    fn resolvedCalleeWrites(self: *Builder, callee: OperandPath) ?CalleeWrites {
        if (callee.field_count == 0) return null;
        const cache = self.cache orelse return null;
        const lid = self.name_to_local.get(callee.root_name) orelse return null;
        const type_name = self.locals.items[@intFromEnum(lid)].type_name orelse return null;
        const method_name = callee.fields[@as(usize, callee.field_count) - 1];
        const resolved = cache.findMethodAcrossImports(type_name, method_name) orelse return null;
        const summary = self.queryOrUnknown(
            fn_summary.FnSummary,
            cache.summaryByMethodCrossFile(type_name, method_name),
        ) orelse return null;
        if (summary.written_paths.len == 0) return null;
        const w: CalleeWrites = .{
            .paths = summary.written_paths,
            .tree = resolved.tree,
            .fn_decl = resolved.method.fn_decl,
        };
        if (!self.calleeBodySpellsEveryStore(w)) return null;
        return w;
    }

    /// Does this declaration spell out every store it can perform?
    ///
    /// `FnSummary.written_paths` is DIRECT: a body that calls anything
    /// writes through that call, and nothing in the list follows it.
    /// So a body with a call in it can only be read as "writes what it
    /// spells and whatever the call reaches" — never as "writes what it
    /// spells".  The test is the ABSENCE of any call rather than a
    /// roster of the calls that count, because a callee this build
    /// could not resolve is precisely the one whose effects are
    /// unknown, and a roster would have to name it to exclude it.
    fn calleeBodySpellsEveryStore(self: *const Builder, w: CalleeWrites) bool {
        _ = self;
        const tree = w.tree;
        const tags = tree.tokens.items(.tag);
        const body = tokens.bodyOf(tree, w.fn_decl) orelse return false;
        const first = tree.firstToken(body);
        const last = tree.lastToken(body);
        if (first > last or last >= tags.len) return false;
        var t = first + 1;
        while (t <= last) : (t += 1) {
            if (tags[t] != .l_paren) continue;
            if (!tagOpensControlParen(tags[t - 1])) return false;
        }
        return true;
    }

    /// May this token be the one immediately before a `(` that is NOT
    /// the open of a call?  Every construct that owns a bracketed
    /// header spells the header's open paren itself, and anything the
    /// header contains is a call of its own that this still sees.
    fn tagOpensControlParen(tag: std.zig.Token.Tag) bool {
        return switch (tag) {
            .keyword_if,
            .keyword_while,
            .keyword_for,
            .keyword_switch,
            .keyword_catch,
            .keyword_orelse,
            .keyword_defer,
            .keyword_errdefer,
            .keyword_inline,
            .keyword_suspend,
            .keyword_asm,
            .keyword_comptime,
            .keyword_test,
            .colon,
            => true,
            else => false,
        };
    }

    /// The field names in a callee-side path text — `"inner . count"`
    /// as the file spelled it, `"slot"` — or null when the text is not
    /// a dotted walk of names.  The producer keeps the source's own
    /// spacing, so this reads it as text and is strict about it: a
    /// shape it cannot place answers conservatively at the call site
    /// rather than being guessed into a field that might be the wrong
    /// one.
    fn guardPathFieldNames(path: []const u8, out: [][]const u8) ?usize {
        var count: usize = 0;
        var t: usize = 0;
        while (true) {
            while (t < path.len and std.ascii.isWhitespace(path[t])) t += 1;
            const name_first = t;
            while (t < path.len and (std.ascii.isAlphanumeric(path[t]) or path[t] == '_')) t += 1;
            if (t == name_first) return null;
            if (count == out.len) return null;
            out[count] = path[name_first..t];
            count += 1;
            while (t < path.len and std.ascii.isWhitespace(path[t])) t += 1;
            if (t >= path.len) return count;
            if (path[t] != '.') return null;
            t += 1;
        }
    }

    /// Is `<path> = <rhs>` at `eq_tok` a restore of a copy taken
    /// before the establishing `if`?  The `const` must have been
    /// initialized from exactly that path, and nothing may have
    /// written the path between the save and the first test.
    fn isSaveRestore(self: *const Builder, tree: *const Ast, path: OperandPath, eq_tok: Ast.TokenIndex, est_first: Ast.TokenIndex) bool {
        const tags = tree.tokens.items(.tag);
        if (eq_tok + 2 >= tags.len) return false;
        if (tags[eq_tok + 1] != .identifier) return false;
        if (tags[eq_tok + 2] != .semicolon and tags[eq_tok + 2] != .comma) return false;
        const name_tok = eq_tok + 1;
        const decl = self.fill.visibleConstDecl(name_tok, tree.tokenSlice(name_tok)) orelse return false;
        if (decl.name_tok >= est_first) return false;
        const spans = decl.spans orelse return false;
        if (spans.type != null) return false;
        // The copy has to be of THIS path.  The save and the restore
        // are two different source sites, so the root cannot be
        // compared by token index — only by the binding it names and
        // the field walk written after it.  `root_name` is that name,
        // read from whichever site spelled it, and the initializer's
        // own first token is this site's spelling of the same root.
        const init = spans.init;
        if (!std.mem.eql(u8, tree.tokenSlice(init.first), path.root_name)) return false;
        if (init.last != init.first + 2 * @as(usize, path.field_count)) return false;
        var k: usize = 0;
        while (k < path.field_count) : (k += 1) {
            const field_token = init.first + 2 * @as(Ast.TokenIndex, @intCast(k)) + 1;
            if (field_token >= tags.len or tags[field_token] != .period) return false;
            if (!std.mem.eql(u8, tree.tokenSlice(field_token + 1), path.fields[k])) return false;
        }
        return !self.pathWrittenBefore(tree, path, init.last, est_first);
    }

    /// Did anything write `path` in [first, last]?  The same event
    /// rules [guardOperandsStable] applies, restricted to this one
    /// path and with no restore escape — the point of the check is
    /// that the saved copy is still current at the first test.
    fn pathWrittenBefore(self: *const Builder, tree: *const Ast, path: OperandPath, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
        const tags = tree.tokens.items(.tag);
        if (first > last or last >= tags.len) return false;
        var t = first;
        while (t <= last) : (t += 1) {
            const tag = tags[t];
            if (tag == .keyword_defer or tag == .keyword_errdefer) return true;
            const is_store = tag == .equal or isCompoundAssign(tag);
            const is_call = tag == .l_paren and t > 0 and tags[t - 1] == .identifier;
            if (!is_store and !is_call) continue;
            const chain = self.lhsChainBefore(t) orelse return true;
            const base = guardOperandOf(tree, chain.span) orelse return true;
            if (is_call) {
                if (std.mem.eql(u8, base.root_name, path.root_name)) return true;
                continue;
            }
            if (chain.indexed) continue;
            // Only a store that REPLACES the saved path, or something
            // containing it, invalidates the copy: `saved = self`
            // followed by `self.stack_top = 1` still leaves `saved`
            // holding what `self` held at the save.  A store deeper
            // than the saved path mutates the original, not the copy.
            if (pathIsPrefix(base, path)) return true;
        }
        return false;
    }

    /// The postfix chain that ends immediately before an assignment's
    /// operator token, and whether its rightmost step is a subscript.
    /// Only the shapes a condition's operands can be written through
    /// are recognised; anything else is null, which the callers treat
    /// as "nobody knows" rather than "nothing happened".
    fn lhsChainBefore(self: *const Builder, op_tok: Ast.TokenIndex) ?struct { span: TokenSpan, indexed: bool } {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (op_tok == 0 or op_tok >= tags.len) return null;
        var end = op_tok - 1;
        var indexed = false;
        // `p.*` — the `.deref` lvalue is `p` followed by a single
        // `.period_asterisk` token, so the chain continues from the
        // `p`.  Looking for a separate `.period` and `.asterisk` here
        // never matches, which left every `p.* = X` store invisible to
        // the guard-stability scan below.
        if (end >= 1 and tags[end] == .period_asterisk) end -= 1;
        if (tags[end] == .r_bracket) {
            const open = openDelimiterAt(tree, end) orelse return null;
            indexed = true;
            if (open == 0) return null;
            end = open - 1;
        }
        if (end == 0 or tags[end] != .identifier) return null;
        var first = end;
        while (first >= 2 and tags[first - 1] == .period and tags[first - 2] == .identifier) {
            first -= 2;
        }
        if (first > 0 and tags[first - 1] == .period) return null;
        return .{ .span = .{ .first = first, .last = end }, .indexed = indexed };
    }

    /// The rooted path a dotted chain token span names, or null when
    /// the span is not `ident (. ident)*`.
    fn guardOperandOf(tree: *const Ast, span: TokenSpan) ?OperandPath {
        const tags = tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        if (tags[span.first] != .identifier) return null;
        var path = OperandPath{ .root_name = tree.tokenSlice(span.first), .fields = undefined, .field_count = 0 };
        var t = span.first + 1;
        while (t <= span.last) : (t += 1) {
            if (t + 1 > span.last) return null;
            if (tags[t] != .period or tags[t + 1] != .identifier) return null;
            if (path.field_count == max_fill_path_fields) return null;
            path.fields[path.field_count] = tree.tokenSlice(t + 1);
            path.field_count += 1;
            t += 1;
        }
        return path;
    }

    /// Is `a` a prefix of `b` — the same root NAME and a field walk no
    /// longer than `b`'s?  A store through `a` can then change what
    /// reading `b` yields.
    fn pathIsPrefix(a: OperandPath, b: OperandPath) bool {
        if (!std.mem.eql(u8, a.root_name, b.root_name)) return false;
        if (a.field_count > b.field_count) return false;
        var k: usize = 0;
        while (k < a.field_count) : (k += 1) {
            if (!std.mem.eql(u8, a.fields[k], b.fields[k])) return false;
        }
        return true;
    }

    /// Could a store through either path change what reading the other
    /// yields?  True when either is a prefix of the other: replacing
    /// `self.grammar` reaches `self.grammar.stack.len`, and replacing
    /// `self.grammar.stack.len` certainly reaches itself.
    fn pathsTouch(a: OperandPath, b: OperandPath) bool {
        return pathIsPrefix(a, b) or pathIsPrefix(b, a);
    }

    /// Is `name` read as a non-field identifier in [first, last]?
    /// A name after `.` is a field selector, not a reference.
    fn nameIsReadBy(tree: *const Ast, name: []const u8, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
        const tags = tree.tokens.items(.tag);
        if (first > last or last >= tags.len) return false;
        var t = first;
        while (t <= last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (t > 0 and tags[t - 1] == .period) continue;
            if (std.mem.eql(u8, tree.tokenSlice(t), name)) return true;
        }
        return false;
    }

    /// Index of the `[`, `(` or `{` that closes at `close_tok`, or null
    /// when the text before it does not balance.  `close_tok` IS the
    /// closer, so the level it closes is open the moment the walk
    /// begins: the counter starts one deep with that token already
    /// counted and only what precedes it moves the counter.  Starting it
    /// at zero made the first token examined — the closer itself —
    /// subtract from nothing, which is the underflow this shape must not
    /// have, and it is reachable on ordinary Zig: any element store
    /// between two tests of one condition puts a `]` where this scan
    /// begins.
    ///
    /// Reaching token 0 with the level still open is "nobody knows", the
    /// same answer every other undecided span here returns, and what a
    /// nesting that closes with a different delimiter gets too.  Neither
    /// is an abort, and neither is a claim that nothing was written.
    fn openDelimiterAt(tree: *const Ast, close_tok: Ast.TokenIndex) ?Ast.TokenIndex {
        const tags = tree.tokens.items(.tag);
        if (close_tok == 0 or close_tok >= tags.len) return null;
        const opener: std.zig.Token.Tag = switch (tags[close_tok]) {
            .r_bracket => .l_bracket,
            .r_paren => .l_paren,
            .r_brace => .l_brace,
            else => return null,
        };
        var depth: u32 = 1;
        var t = close_tok - 1;
        while (true) {
            switch (tags[t]) {
                .r_bracket, .r_paren, .r_brace => depth += 1,
                .l_bracket, .l_paren, .l_brace => {
                    depth -= 1;
                    if (depth == 0) return if (tags[t] == opener) t else null;
                },
                else => {},
            }
            if (t == 0) return null;
            t -= 1;
        }
    }

    /// A compound-assignment operator — anything of the `x op= y`
    /// family.  Each reads its target AND writes it, and none of them
    /// has a saved copy to restore from.
    fn isCompoundAssign(tag: std.zig.Token.Tag) bool {
        return switch (tag) {
            .pipe_equal,
            .percent_equal,
            .caret_equal,
            .plus_equal,
            .plus_percent_equal,
            .plus_pipe_equal,
            .minus_equal,
            .minus_percent_equal,
            .minus_pipe_equal,
            .asterisk_equal,
            .asterisk_percent_equal,
            .asterisk_pipe_equal,
            .slash_equal,
            .ampersand_equal,
            .angle_bracket_left_equal,
            .angle_bracket_angle_bracket_left_equal,
            .angle_bracket_angle_bracket_left_pipe_equal,
            .angle_bracket_right_equal,
            .angle_bracket_angle_bracket_right_equal,
            => true,
            else => false,
        };
    }

    /// Ceiling on how far back one `if` looks for the test it re-uses.
    /// A pairing across a hundred statements is a stretch no reader of
    /// the code would recognise, and the scan is quadratic.
    const max_guard_pair_scan = 48;

    /// Mint a [GuardId] for every `if` in this statement list that is
    /// one half of a RE-TESTED condition — an earlier `if` reading the
    /// same expression, with nothing between them able to change what
    /// it reads.  Both halves get the SAME id, so the transfer can
    /// tell that the second test is a second reading of one value.
    ///
    /// "THE SAME VALUE" INCLUDES ITS NEGATION, and which sense each
    /// `if` read is recorded with the id: `if (C) {…} if (!C) {…}` and
    /// `if (x == 0) {…} if (x != 0) {…}` are two readings of one value
    /// in opposite senses, and the branches really are mutually
    /// exclusive.  That is the whole of issue #55 — a release under one
    /// branch and an insertion under the other, which the program can
    /// never do both of.  See [guardConditionPolarity] for exactly
    /// which spellings that covers and why an order comparison is not
    /// among them.
    ///
    /// Running before the list is lowered is what makes the pairing
    /// possible at all: [lowerIf] meets the ESTABLISHING `if` long
    /// before it meets the one that re-reads it, and a fact emitted
    /// there can only be minted once the whole list is known.
    ///
    /// Sibling pairs are found nearest-first and each `if` is used at
    /// most once. A returning catch handler can share that pair's id
    /// when its straight-line prefix restores the same tested value.
    fn establishGuardPairs(self: *Builder, stmts: []const Ast.Node.Index) !void {
        const tree = self.tree;
        const ifs: usize = blk: {
            var n: usize = 0;
            for (stmts) |stmt| {
                const tag = tree.nodeTag(stmt);
                if (tag == .if_simple or tag == .@"if") n += 1;
            }
            break :blk n;
        };
        if (ifs < 2) {
            try self.establishCatchGuardPairs(stmts);
            return;
        }
        var paired = try self.gpa.alloc(bool, stmts.len);
        defer self.gpa.free(paired);
        @memset(paired, false);

        for (stmts, 0..) |use_node, index| {
            if (paired[index]) continue;
            const use_branch = tree.fullIf(use_node) orelse continue;
            // A payload makes the arm a destructuring, and the
            // condition's own value is not what the arm is about.
            if (use_branch.payload_token != null) continue;
            var back = index;
            var steps: usize = 0;
            while (back > 0 and steps < max_guard_pair_scan) : (steps += 1) {
                back -= 1;
                if (paired[back]) continue;
                const est_node = stmts[back];
                const est_branch = tree.fullIf(est_node) orelse continue;
                if (est_branch.payload_token != null) continue;
                const polarity = self.guardConditionPolarity(est_branch.ast.cond_expr, use_branch.ast.cond_expr) orelse continue;
                if (!self.guardOperandsStable(est_node, use_node)) continue;
                if (self.next_guard == std.math.maxInt(u32)) return;
                const guard: GuardId = @enumFromInt(self.next_guard);
                self.next_guard += 1;
                // The ESTABLISHING `if` defines the sense; the re-test
                // records whether it read that sense or its negation.
                try self.guard_facts.put(self.gpa, est_node, .{ .guard = guard, .negated = false });
                try self.guard_facts.put(self.gpa, use_node, .{ .guard = guard, .negated = polarity });
                paired[index] = true;
                paired[back] = true;
                break;
            }
        }
        try self.establishCatchGuardPairs(stmts);
    }

    /// A catch following the establishing test has two continuations:
    /// its returning handler and the ordinary success path. The handler
    /// re-test needs the establishing fact too, not a fresh guard id.
    /// Limit the extra pairing to a straight-line assignment prefix,
    /// one re-test and an unconditional return. Conditional restores,
    /// nested control flow and deferred writes cannot certify this path.
    fn establishCatchGuardPairs(self: *Builder, stmts: []const Ast.Node.Index) !void {
        const tree = self.tree;
        for (stmts, 0..) |catch_node, index| {
            if (index == 0 or tree.nodeTag(catch_node) != .@"catch") continue;
            const est_node = stmts[index - 1];
            const est_branch = tree.fullIf(est_node) orelse continue;
            if (est_branch.payload_token != null) continue;

            const catch_data = tree.nodeData(catch_node).node_and_node;
            // The operand runs once before the handler. Wrappers could
            // carry another restore on a path this prefix never takes.
            var call_buf: [1]Ast.Node.Index = undefined;
            if (tree.fullCall(&call_buf, catch_data[0]) == null) continue;
            const body = catch_data[1];
            switch (tree.nodeTag(body)) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => {},
                else => continue,
            }
            var stmt_buf: [2]Ast.Node.Index = undefined;
            const handler = blockStmts(tree, body, &stmt_buf);
            if (handler.len < 2 or handler.len > max_guard_pair_scan) continue;
            const use_node = handler[handler.len - 2];
            const use_branch = tree.fullIf(use_node) orelse continue;
            if (use_branch.payload_token != null or tree.nodeTag(handler[handler.len - 1]) != .@"return") continue;

            var straight = true;
            for (handler[0 .. handler.len - 2]) |prefix| {
                if (tree.nodeTag(prefix) != .assign) {
                    straight = false;
                    break;
                }
                const rhs = tree.nodeData(prefix).node_and_node[1];
                if (!self.conditionIsPure(tree, tree.firstToken(rhs), tree.lastToken(rhs))) {
                    straight = false;
                    break;
                }
            }
            if (!straight) continue;
            const polarity = self.guardConditionPolarity(est_branch.ast.cond_expr, use_branch.ast.cond_expr) orelse continue;
            if (!self.guardOperandsStable(est_node, use_node)) continue;
            const fact = if (self.guard_facts.get(est_node)) |existing|
                existing
            else fresh: {
                if (self.next_guard == std.math.maxInt(u32)) return;
                const fresh = GuardFact{ .guard = @enumFromInt(self.next_guard), .negated = false };
                self.next_guard += 1;
                try self.guard_facts.put(self.gpa, est_node, fresh);
                break :fresh fresh;
            };
            try self.guard_facts.put(self.gpa, use_node, .{
                .guard = fact.guard,
                .negated = fact.negated != polarity,
            });
        }
    }

    /// Sound exhaustive fill whose per-iteration writes TILE the
    /// target instead of hitting one element each:
    ///
    ///     var out: [2 * digest.len]u8 = undefined;
    ///     for (digest, 0..) |byte, i| {
    ///         out[i * 2]     = hex(byte >> 4);
    ///         out[i * 2 + 1] = hex(byte & 0x0f);
    ///     }
    ///     return out;
    ///
    /// The general claim is about the SET of indices the body writes,
    /// not about any particular stride: read each subscript as an
    /// affine function of the loop counter, `k * i + m` with `k >= 1`.
    /// If every write shares one multiplier `k` and their offsets are
    /// exactly `0 … k-1`, each element once and no element twice, then
    /// the union over `i = 0 … trips-1` is the CONTIGUOUS range
    /// `[0, k * trips)` — which is the target exactly when
    /// `k * trips` is its declared length.  That is what "the writes
    /// tile the target range" means here, and no `2` or `+1` is
    /// special-cased anywhere in it.
    ///
    /// Load-bearing clauses; any one missing leaves a hole:
    ///   - the loop is unlabelled, has TWO inputs, the second exactly
    ///     `0..`, and a `| value , index |` pair of by-value captures;
    ///   - the trip count is READABLE ([iteratedFixedCount]).  Unlike
    ///     the single-write proof this loop may be an ordinary runtime
    ///     `for`: over a FIXED-SIZE array the language guarantees it
    ///     walks all of it, so a resolved length is a resolved trip
    ///     count.  A slice, whose length is data, is declined;
    ///   - every top-level lvalue in the body is a store into the SAME
    ///     target, at an index this can read as `k * i + m`, with a
    ///     DEFINED rhs ([rhsIsDefined]).  A write behind a conditional
    ///     would punch a hole in exactly the range being tiled;
    ///   - the target has exactly ONE mention in the whole body, and
    ///     the counter capture none: a read, a second store through an
    ///     alias, or the counter appearing in the offset would each
    ///     break the tiling argument;
    ///   - the body holds no UNLABELED `break` / `continue`, which
    ///     would end the enumeration or skip a write before the tiles
    ///     closed;
    ///   - the target is a `var` seeded with the `undefined` keyword,
    ///     declared before the loop;
    ///   - `k * trips` EQUALS the target's declared element count.
    ///     Exactly, not "at least": a longer tiling means the loop
    ///     stores past the end, and crediting the fill would bless that.
    fn exhaustiveTiledFill(self: *Builder, loop: Ast.full.For) ?FieldFillProof {
        if (loop.label_token != null) return null;
        if (loop.ast.inputs.len != 2) return null;
        if (!self.zeroBasedRangeInput(loop.ast.inputs[1])) return null;
        const payload = self.forIndexedCaptureNames(loop) orelse return null;

        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const body_node = loop.ast.then_expr;
        const body_first = tree.firstToken(body_node);
        const body_last = tree.lastToken(body_node);
        if (body_first > body_last or body_last >= tags.len) return null;
        if (self.bodyHasUnlabeledLoopExit(body_first, body_last)) return null;

        var stmt_buf: [2]Ast.Node.Index = undefined;
        var single_buf: [1]Ast.Node.Index = undefined;
        const stmts: []const Ast.Node.Index = self.blockStmtList(body_node, &stmt_buf, &single_buf) orelse return null;
        if (stmts.len == 0) return null;
        // More than one store per iteration is what makes this a
        // TILING rather than the single-write case [exhaustiveIndexedFill]
        // already owns.  A one-store body writes `k * i + m` with `m`
        // fixed, so its "residues" are one residue and the union
        // argument says nothing that proof has not already decided —
        // including deciding not to credit a runtime loop.  Admitting
        // it here would quietly widen that proof.
        if (stmts.len < 2) return null;

        // Ceiling on how many tiles one iteration may write.  A body
        // that writes hundreds of slots per iteration is not a tiling
        // anybody wrote by hand, and the offset table below is a fixed
        // buffer.
        const max_tiles = 16;
        var offsets: [max_tiles]u64 = [_]u64{0} ** max_tiles;
        var stride: u64 = 0;
        var base_tok: Ast.TokenIndex = 0;
        var seen = false;
        for (stmts) |stmt| {
            const w = self.subscriptFillAssignWrite(stmt) orelse return null;
            if (!self.rhsIsDefined(w.rhs)) return null;
            const name = tree.tokenSlice(w.base_tok);
            if (std.mem.eql(u8, name, payload.value)) return null;
            if (std.mem.eql(u8, name, payload.index)) return null;
            if (seen) {
                // A store into a DIFFERENT array in the same body is
                // not a tile of this target; nothing here would put it
                // back in the union.
                //
                // Compared by NAME, not by token index.  `base_tok` is
                // the token of ONE occurrence of the base identifier,
                // and two statements writing the same array spell it at
                // two different tokens — so an index comparison
                // rejects every body with two or more subscript
                // stores, which is exactly the tiling this proof
                // exists to credit.  What has to be the same is the
                // BINDING, and the spelling is the only identity
                // available before the name is resolved.  A body-local
                // shadow is still rejected below, where the name
                // resolves to a local declared after the loop.
                if (!std.mem.eql(u8, name, tree.tokenSlice(base_tok))) return null;
            } else {
                base_tok = w.base_tok;
            }
            const tile = self.affineIndexOf(w.lhs, payload.index) orelse return null;
            if (!seen) {
                stride = tile.scale;
            } else if (tile.scale != stride) return null;
            // An offset at or past the stride would not be this
            // iteration's residue, and a stride of zero or one past
            // the table would not have a slot for it.
            if (tile.offset >= stride or tile.offset >= max_tiles) return null;
            offsets[tile.offset] = 1;
            seen = true;
        }
        if (!seen or stride == 0 or stride >= max_tiles) return null;
        // Every residue modulo the stride exactly once: a repeated
        // offset leaves some element of each stride-block written
        // twice and another never.
        for (offsets[0..stride]) |hit| {
            if (hit == 0) return null;
        }

        const name = tree.tokenSlice(base_tok);
        if (self.identifierMentions(name, body_first, body_last) != stmts.len) return null;
        if (self.identifierMentions(payload.index, body_first, body_last) != stmts.len) return null;

        const trips = self.fill.iteratedFixedCount(loop.ast.inputs[0]) orelse return null;
        const local = self.name_to_local.get(name) orelse return null;
        const decl = self.fill.declaredTypeSpanOfLocal(local) orelse return null;
        if (decl.is_const) return null;
        if (!decl.init_is_undefined) return null;
        if (decl.name_tok >= loop.ast.for_token) return null;
        const extent = self.fill.declaredExtent(decl.type) orelse return null;
        const target_len = extent.number orelse return null;
        const tiled = std.math.mul(u64, stride, trips) catch return null;
        if (tiled != target_len) return null;

        return .{
            .local = local,
            .pos = self.posOfToken(loop.ast.for_token),
            .end_pos = self.endPosOf(body_node),
        };
    }

    const AffineIndex = struct { scale: u64, offset: u64 };

    /// One `k * i + m` write index, read off the subscript of a
    /// `target[...] = …` lvalue whose counter is `index`.  Null for any
    /// shape the union argument cannot place: a field chain, a
    /// pointer, a range, or an expression whose dependence on the
    /// counter is not a single multiply plus an addend.
    fn affineIndexOf(self: *const Builder, lhs: Ast.Node.Index, index: []const u8) ?AffineIndex {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (tree.nodeTag(lhs) != .array_access) return null;
        const data = tree.nodeData(lhs).node_and_node;
        // The base must be a bare identifier.  `holder.rows[i]` and
        // `ptr[i]` both name storage whose extent this proof does not
        // describe, whatever arithmetic the index carries.
        if (tree.nodeTag(data[0]) != .identifier) return null;
        // The subscript is bounded by ITS BRACKETS, not by the index
        // expression node's own token range.  An infix operator stores
        // the operator as that node's main token, so
        // `firstToken(index * 2)` is the `*` — the span would start one
        // token past the counter and every `k * i` write would read as
        // a malformed expression and be declined.  What sits between
        // the `[` after the base and this node's own last token is the
        // whole subscript, whatever expression shape wrote it.
        const base_last = tree.lastToken(data[0]);
        const open = base_last + 1;
        const close = tree.lastToken(lhs);
        if (open >= tags.len or close >= tags.len) return null;
        if (tags[open] != .l_bracket or tags[close] != .r_bracket) return null;
        if (close < open + 2) return null;
        return self.affineWrite(.{ .first = open + 1, .last = close - 1 }, index);
    }

    /// `k * <index> + m` and the spellings that mean it:
    /// `<index> * k + m`, `k * <index>`, `<index> + m`, and a bare
    /// literal subscript (which tiles nothing — the caller rejects a
    /// scale of zero).
    ///
    /// The form is `[<stride>] [+ <addend>]` rather than one flat scan
    /// for "at most one operator": `index * 2 + 1` is the ordinary
    /// spelling of the doubled target this exists for, and a scan that
    /// refuses a second operator declines every one of them.  What has
    /// to be refused instead is a shape that is NOT one multiply plus
    /// one addend, and that is decided where it is read.
    fn affineWrite(self: *const Builder, span: TokenSpan, index: []const u8) ?AffineIndex {
        if (span.first > span.last) return null;
        const plus = self.singleOperator(span, .plus) orelse
            return self.affineStride(span, index);
        const stride_span = TokenSpan{ .first = span.first, .last = plus.at - 1 };
        const addend_span = TokenSpan{ .first = plus.at + 1, .last = span.last };
        if (stride_span.first > stride_span.last) return null;
        if (addend_span.first > addend_span.last) return null;
        const offset = self.fill.literalValue(addend_span) orelse return null;
        // `<index> + m` is stride one; anything else has to be a
        // multiply, which the `+` has to sit outside of.
        if (self.spanIsIndex(stride_span, index)) return .{ .scale = 1, .offset = offset };
        const stride = self.affineStride(stride_span, index) orelse return null;
        if (stride.offset != 0) return null;
        return .{ .scale = stride.scale, .offset = offset };
    }

    /// The `k * <index>` / `<index> * k` product, or — when there is
    /// no multiply at all — the constant subscript itself.
    ///
    /// Exactly one operand of the multiply has to NAME the counter.
    /// Both naming it makes the subscript quadratic in the counter,
    /// which is not affine at all; neither naming it makes it a
    /// constant, and reading that constant as a stride is how
    /// `out[2 * 2] = …` would come to look like `out[2 * index]`.
    /// A zero multiplier collapses every iteration onto one element,
    /// so it is refused here too.
    fn affineStride(self: *const Builder, span: TokenSpan, index: []const u8) ?AffineIndex {
        if (span.first > span.last) return null;
        const star = self.singleOperator(span, .asterisk) orelse
            return .{ .scale = 0, .offset = self.fill.literalValue(span) orelse return null };
        const left = TokenSpan{ .first = span.first, .last = star.at - 1 };
        const right = TokenSpan{ .first = star.at + 1, .last = span.last };
        if (left.first > left.last or right.first > right.last) return null;
        const left_is_index = self.spanIsIndex(left, index);
        const right_is_index = self.spanIsIndex(right, index);
        if (left_is_index == right_is_index) return null;
        const scale = self.fill.literalValue(if (left_is_index) right else left) orelse return null;
        if (scale == 0) return null;
        return .{ .scale = scale, .offset = 0 };
    }

    /// The one `tag` token in `span`, or null when there is none or
    /// more than one.  Two operators of one kind are as far from
    /// `k * i + m` as a division is.
    fn singleOperator(
        self: *const Builder,
        span: TokenSpan,
        tag: std.zig.Token.Tag,
    ) ?struct { at: Ast.TokenIndex } {
        const tags = self.tree.tokens.items(.tag);
        if (span.first > span.last or span.last >= tags.len) return null;
        var found: ?Ast.TokenIndex = null;
        var t = span.first;
        while (t <= span.last) : (t += 1) {
            if (tags[t] != tag) continue;
            if (found != null) return null;
            found = t;
        }
        return if (found) |at| .{ .at = at } else null;
    }

    /// True when `span` is exactly the loop's counter capture.
    fn spanIsIndex(self: *const Builder, span: TokenSpan, index: []const u8) bool {
        if (span.first != span.last) return false;
        const tree = self.tree;
        if (tree.tokenTag(span.first) != .identifier) return false;
        return std.mem.eql(u8, tree.tokenSlice(span.first), index);
    }

    /// Sound exhaustive fill driven by a BY-POINTER enumeration of the
    /// target itself:
    ///
    ///     var out: [16]u8 = undefined;
    ///     for (&out, 0..) |*byte, i| { byte.* = …; }
    ///     return out;
    ///
    /// The loop walks the target's OWN storage, so its trip count is
    /// the target's own declared length and every iteration writes the
    /// one element the pointer names.  There is no index arithmetic to
    /// check at all — which is exactly why the proof is not the
    /// single-write indexed one: that one has to establish that the
    /// index lands in range, and here nothing in the body chooses an
    /// index.
    ///
    /// Load-bearing clauses:
    ///   - the loop is unlabelled, has TWO inputs, the second exactly
    ///     `0..`, and a `| * ptr , index |` payload: a by-value first
    ///     capture would name a COPY, and the body would be writing
    ///     through a pointer to something else;
    ///   - the enumerated expression is EXACTLY `& <target>` — the
    ///     address of the target being filled.  A different array, a
    ///     slice, or a field of something else is a trip count this
    ///     does not describe;
    ///   - the body's ONE top-level statement is `<ptr>.* = <rhs>`
    ///     with a DEFINED rhs.  Any other lvalue, or a conditional
    ///     store, would leave elements unwritten;
    ///   - the target is not mentioned anywhere in the body (the `&`
    ///     that enumerated it is in the loop header), and the pointer
    ///     capture is mentioned exactly once;
    ///   - the body holds no UNLABELED `break` / `continue`;
    ///   - the target is a `var` seeded with the `undefined` keyword,
    ///     declared before the loop.
    fn exhaustivePointerCaptureFill(self: *Builder, loop: Ast.full.For) ?FieldFillProof {
        if (loop.label_token != null) return null;
        if (loop.ast.inputs.len != 2) return null;
        if (!self.zeroBasedRangeInput(loop.ast.inputs[1])) return null;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);

        const target_tok = self.addressOfTargetInput(loop.ast.inputs[0]) orelse return null;
        const target_name = tree.tokenSlice(target_tok);
        if (self.name_to_local.get(target_name) == null) return null;
        const payload = self.forPointerIndexedCaptureNames(loop) orelse return null;

        const body_node = loop.ast.then_expr;
        const body_first = tree.firstToken(body_node);
        const body_last = tree.lastToken(body_node);
        if (body_first > body_last or body_last >= tags.len) return null;
        if (self.bodyHasUnlabeledLoopExit(body_first, body_last)) return null;

        var stmt_buf: [2]Ast.Node.Index = undefined;
        var single_buf: [1]Ast.Node.Index = undefined;
        const stmts: []const Ast.Node.Index = self.blockStmtList(body_node, &stmt_buf, &single_buf) orelse return null;
        if (stmts.len != 1) return null;
        const rhs = self.pointerCaptureStore(stmts[0], payload.pointer) orelse return null;
        if (!self.rhsIsDefined(rhs)) return null;
        if (self.identifierMentions(target_name, body_first, body_last) != 0) return null;
        if (self.identifierMentions(payload.pointer, body_first, body_last) != 1) return null;

        const local = self.name_to_local.get(target_name).?;
        const decl = self.fill.declaredTypeSpanOfLocal(local) orelse return null;
        if (decl.is_const) return null;
        if (!decl.init_is_undefined) return null;
        if (decl.name_tok >= loop.ast.for_token) return null;
        const extent = self.fill.declaredExtent(decl.type) orelse return null;
        // Nothing to compare against: the enumeration IS the target,
        // so the trip count is this number by construction.
        if (extent.number == null) return null;

        return .{
            .local = local,
            .pos = self.posOfToken(loop.ast.for_token),
            .end_pos = self.endPosOf(body_node),
        };
    }

    /// The token naming the local a `for` input is the address of —
    /// exactly `& <identifier>`, and nothing else.  A field path, a
    /// deref, or a parenthesised expression all walk through storage
    /// whose extent this proof does not describe.
    fn addressOfTargetInput(self: *const Builder, input: Ast.Node.Index) ?Ast.TokenIndex {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const first = tree.firstToken(input);
        const last = tree.lastToken(input);
        if (first >= tags.len or last >= tags.len) return null;
        // `& out` is TWO tokens, so the name is one past the `&`.  The
        // node's own span is what bounds this: `first + 1 == last` is
        // what "exactly `& <identifier>`" means, and anything longer
        // walks through storage this proof does not describe.
        if (last != first + 1) return null;
        if (tags[first] != .ampersand) return null;
        if (tags[first + 1] != .identifier) return null;
        return first + 1;
    }

    /// The `* ptr , index` capture names of a two-input loop.  Null for
    /// a by-value first capture, for `_`, and for anything that is not
    /// exactly two names.
    fn forPointerIndexedCaptureNames(self: *const Builder, loop: Ast.full.For) ?struct { pointer: []const u8, index: []const u8 } {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const pt = loop.payload_token;
        if (pt == 0 or pt + 4 >= tags.len) return null;
        if (tags[pt - 1] != .pipe) return null;
        if (tags[pt] != .asterisk) return null;
        if (tags[pt + 1] != .identifier) return null;
        if (tags[pt + 2] != .comma) return null;
        if (tags[pt + 3] != .identifier) return null;
        if (tags[pt + 4] != .pipe) return null;
        const pointer = tree.tokenSlice(pt + 1);
        const index = tree.tokenSlice(pt + 3);
        if (std.mem.eql(u8, pointer, "_")) return null;
        if (std.mem.eql(u8, index, "_")) return null;
        if (std.mem.eql(u8, pointer, index)) return null;
        return .{ .pointer = pointer, .index = index };
    }

    /// The `<ptr>.* = <rhs>` statement of a pointer-capture body,
    /// returning the stored value.  The deref has to be of the
    /// capture: writing through any other pointer says nothing about
    /// which element of the target this iteration owns.
    fn pointerCaptureStore(self: *const Builder, stmt: Ast.Node.Index, pointer: []const u8) ?Ast.Node.Index {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (tree.nodeTag(stmt) != .assign) return null;
        const data = tree.nodeData(stmt).node_and_node;
        const first = tree.firstToken(data[0]);
        const last = tree.lastToken(data[0]);
        // `.*` is ONE token — `.period_asterisk` — so `byte.*` is two
        // tokens and the node's last token is one past its first, not
        // two.  Reading the `.*` as a `.period` followed by an
        // `.asterisk` makes every `byte.* = …` store fail this shape
        // check and silently declines the whole proof.
        if (last != first + 1) return null;
        if (first >= tags.len or last >= tags.len) return null;
        if (tags[first] != .identifier) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(first), pointer)) return null;
        if (tags[first + 1] != .period_asterisk) return null;
        return data[1];
    }

    /// True iff the loop's second input is exactly `0..`.
    ///
    /// A from-zero open range is what makes the index capture run
    /// 0, 1, … over the WHOLE collection; `1..` shifts every write off
    /// index 0 and `0..n` truncates it, so neither enumerates the
    /// target's elements.
    fn zeroBasedRangeInput(self: *const Builder, input: Ast.Node.Index) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const first = tree.firstToken(input);
        const last = tree.lastToken(input);
        if (first > last or last >= tags.len) return false;
        if (last != first + 1) return false;
        if (tags[first] != .number_literal) return false;
        if (!std.mem.eql(u8, tree.tokenSlice(first), "0")) return false;
        return tags[first + 1] == .ellipsis2;
    }

    /// The `| value , index |` capture names of a two-input loop.
    /// Null for a by-pointer capture (`|*xs, i|`), for `_`, for a
    /// destructuring or single-capture payload, and for a loop with no
    /// payload at all — none of which bind a distinct index.
    fn forIndexedCaptureNames(self: *const Builder, loop: Ast.full.For) ?IndexedPayload {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const pt = loop.payload_token;
        if (pt == 0 or pt + 3 >= tags.len) return null;
        if (tags[pt - 1] != .pipe) return null;
        if (tags[pt] != .identifier) return null;
        if (tags[pt + 1] != .comma) return null;
        if (tags[pt + 2] != .identifier) return null;
        if (tags[pt + 3] != .pipe) return null;
        const value = tree.tokenSlice(pt);
        const index = tree.tokenSlice(pt + 2);
        if (std.mem.eql(u8, value, "_")) return null;
        if (std.mem.eql(u8, index, "_")) return null;
        if (std.mem.eql(u8, value, index)) return null;
        return .{ .value = value, .index = index };
    }

    /// The top-level `<target>[<index capture>] = <rhs>` statement of
    /// the loop body: the token naming the written local and the value
    /// stored into this iteration's slot.
    fn indexedFillAssignWrite(
        self: *const Builder,
        stmt: Ast.Node.Index,
        index: []const u8,
    ) ?FieldFillWrite {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (tree.nodeTag(stmt) != .assign) return null;
        const data = tree.nodeData(stmt).node_and_node;
        const lhs = data[0];
        const first = tree.firstToken(lhs);
        const last = tree.lastToken(lhs);
        if (first >= tags.len or last >= tags.len or first > last) return null;
        // EXACTLY `name [ name ]`.  A field chain (`a.b[i]`), a
        // pointer (`p[i]` where `p` is a `*T`), a slice index range, or
        // `@field` all name storage whose extent the loop's element
        // count does not describe, so the token shape is checked
        // rather than a node tag — `Node.Data` churns between Zig
        // versions, and this file already prefers source text for
        // that reason.
        if (last != first + 3) return null;
        if (tags[first] != .identifier) return null;
        if (tags[first + 1] != .l_bracket) return null;
        if (tags[first + 2] != .identifier) return null;
        if (tags[first + 3] != .r_bracket) return null;
        if (!std.mem.eql(u8, tree.tokenSlice(first + 2), index)) return null;
        return .{ .base_tok = first, .rhs = data[1] };
    }

    /// Lowering-time "this value is not `undefined`" test for the
    /// value stored into every field.
    ///
    /// Assigning `undefined` — or copying a local that was itself
    /// seeded `undefined` — writes the same uninitialized bytes the
    /// field already held.  Claiming the whole struct is then defined
    /// would suppress a real use-undefined on exactly the code the
    /// proof describes, so only values the lowering can already vouch
    /// for are accepted: no `undefined` identifier anywhere in the
    /// expression, and no read of a local whose declaration seeded it
    /// with `undefined`.
    ///
    /// The lexical `undefined` scan is strictly wider than asking
    /// `classifyExpr` for `.undef` (its only `.undef` producer is that
    /// same identifier, and it misses `undefined` nested inside an
    /// aggregate like `@as(u32, undefined)`), and running `classifyExpr`
    /// here would spend lowering budget on a value that is only ever
    /// discarded.  A seed that is later assigned still reads as
    /// unprovable — over-rejecting is the safe direction.
    fn rhsIsDefined(self: *const Builder, rhs: Ast.Node.Index) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const first = tree.firstToken(rhs);
        const last = tree.lastToken(rhs);
        var t = first;
        while (t < tags.len and t <= last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            const name = tree.tokenSlice(t);
            if (std.mem.eql(u8, name, "undefined")) return false;
            if (t > 0 and tags[t - 1] == .period) continue;
            const lid = self.name_to_local.get(name) orelse continue;
            const decl = self.fill.declaredTypeSpanOfLocal(lid) orelse continue;
            if (decl.init_is_undefined) return false;
        }
        return true;
    }

    /// How many times `name` is referenced as a non-field identifier
    /// token in [first, last].  Names after `.` are field/method
    /// selectors, not references to the binding, so they don't count.
    fn identifierMentions(
        self: *const Builder,
        name: []const u8,
        first: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) usize {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var n: usize = 0;
        var t = first;
        while (t < tags.len and t <= last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (t > 0 and tags[t - 1] == .period) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
            n += 1;
        }
        return n;
    }

    /// `switch (cond) { CASE => EXPR, ... }` — N-way fork.  Each case
    /// becomes a successor of `cur`; all cases join into a fresh merge
    /// block.  We don't model case-pattern matching or exhaustiveness;
    /// every case is treated as reachable from cur.
    fn lowerSwitch(self: *Builder, sw_node: Ast.Node.Index, cur: *BlockId, result_frame: ?ValueOutcomeFrame) LoweringError!void {
        const tree = self.tree;
        const sw = tree.fullSwitch(sw_node) orelse {
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "switch-extract" } },
                .pos = self.posOf(sw_node),
                .end_pos = self.endPosOf(sw_node),
            });
            if (result_frame) |frame| try self.recordValueOutcome(frame, sw_node, cur, null);
            return;
        };

        // Walk the discriminant expression before any case branch.
        try self.emitUsesInExpr(sw.ast.condition, cur.*, null);
        const selector = if (result_frame != null and result_frame.?.scalar_local != null)
            try self.newScalarValue(sw.ast.condition, cur.*)
        else
            null;
        if (selector) |local|
            try self.emitScalarValue(cur.*, local, sw.ast.condition, result_frame.?.scalar_guard);
        var branch_frame = result_frame;
        if (branch_frame) |*frame| frame.scalar_guard = selector;

        const merge = try self.newBlock();

        if (sw.ast.cases.len == 0) {
            if (result_frame) |frame| try self.recordValueOutcome(frame, sw_node, cur, null);
            try self.addEdge(cur.*, merge);
            cur.* = merge;
            return;
        }

        // Pre-resolve the scrutinee's union TypeInfo (if any) so we
        // can mark by-value pointer-payload captures as is_pointer.
        // Pattern: `switch (<local>) { .tag => |cap| ... }` where the
        // union variant's declared type is `*T` — the capture is the
        // pointer, and `&cap.field` is a borrow into the pointee
        // (caller / heap), not a stack-frame escape.
        const sw_union_ti: ?*const model_mod.TypeInfo = self.scrutineeUnionType(sw.ast.condition);

        for (sw.ast.cases) |case_node| {
            const case_full = tree.fullSwitchCase(case_node) orelse continue;
            const scope = try self.localsLen();
            const case_block = try self.newBlock();
            try self.addEdge(cur.*, case_block);
            // `.tag => |val| ...` capture binds inside this case only.
            // Emit reset_capture into case_block so that stale field
            // state from a prior iteration (when the switch is inside
            // a loop) doesn't cause spurious double-free / UAF.
            // Mirrors the reset_into=body approach used by while/for.
            if (case_full.payload_token) |pt| {
                try self.registerSwitchCaptures(pt, case_block, sw_union_ti, case_full.ast.values);
            }
            var case_cur = case_block;
            try self.lowerValueExpr(case_full.ast.target_expr, &case_cur, branch_frame);
            try self.addEdge(case_cur, merge);
            self.restoreLocalNames(scope, tree.firstToken(sw_node));
        }

        cur.* = merge;
    }

    /// If `scrut_node` is a single identifier naming a known local
    /// whose declared type is a tagged-union (or plain union) in the
    /// file model, return that union's TypeInfo.  Used by switch
    /// lowering to type-check arm captures against the union's
    /// variant fields.
    fn scrutineeUnionType(self: *Builder, scrut_node: Ast.Node.Index) ?*const model_mod.TypeInfo {
        const tree = self.tree;
        if (tree.nodeTag(scrut_node) != .identifier) return null;
        const name_tok = tree.nodeMainToken(scrut_node);
        const name = tree.tokenSlice(name_tok);
        const lid = self.name_to_local.get(name) orelse return null;
        const local = self.locals.items[@intFromEnum(lid)];
        const type_name = local.type_name orelse return null;
        const cache = self.cache orelse return null;
        const model = self.modelOrNull(cache) orelse return null;
        const ti = model.findType(type_name) orelse return null;
        if (ti.kind != .union_) return null;
        return ti;
    }

    /// Register a switch prong's `|cap|` payload and type it from the
    /// scrutinee's union when that union is known: a `*T` field makes
    /// the capture a pointer, an error-set field makes it an error
    /// value whose `return` replays `errdefer`.  `reset_into` emits
    /// the `.reset_capture` loop guard (null in `return switch (…)`,
    /// whose arms are forked once and never looped back).
    fn registerSwitchCaptures(
        self: *Builder,
        payload_token: Ast.TokenIndex,
        reset_into: ?BlockId,
        un_ti: ?*const model_mod.TypeInfo,
        prong_values: []const Ast.Node.Index,
    ) !void {
        // Registration first: it creates the capture local the
        // marking below looks up by name.
        if (reset_into) |blk| {
            try self.registerCapturesWith(payload_token, blk);
        } else {
            try self.registerCaptures(payload_token);
        }
        const un = un_ti orelse return;
        self.markPointerCapturesFromUnion(payload_token, un, prong_values);
        self.markErrorCapturesFromUnion(payload_token, un, prong_values);
    }

    /// The local a switch prong's `|cap|` payload binds.  `payload_token`
    /// is the first token AFTER the opening `|` (matching
    /// registerCapturesImpl semantics); a leading `*` (by-pointer
    /// capture) and `_` yield nothing to type.
    fn switchCaptureLocal(self: *Builder, payload_token: Ast.TokenIndex) ?LocalId {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        var t: Ast.TokenIndex = payload_token;
        var cap_name: ?[]const u8 = null;
        while (t < tags.len) : (t += 1) {
            switch (tags[t]) {
                .pipe => break,
                .identifier => {
                    cap_name = tree.tokenSlice(t);
                    break;
                },
                else => {},
            }
        }
        const name = cap_name orelse return null;
        if (std.mem.eql(u8, name, "_")) return null;
        return self.name_to_local.get(name);
    }

    /// For each case-prong `.<tag>` in `prong_values`, if the union's
    /// `<tag>` field is declared as `*T`, mark the corresponding
    /// payload capture's LocalInfo with `is_pointer = true`.
    fn markPointerCapturesFromUnion(
        self: *Builder,
        payload_token: Ast.TokenIndex,
        un_ti: *const model_mod.TypeInfo,
        prong_values: []const Ast.Node.Index,
    ) void {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const lid = self.switchCaptureLocal(payload_token) orelse return;
        // Walk each prong value `.<tag>` and check the union's
        // field type starts with `*`.  All prongs in one arm must
        // agree (same payload type), so checking ANY is enough.
        for (prong_values) |v| {
            const field = self.unionFieldForProng(un_ti, v) orelse continue;
            if (field.type_first > field.type_last) continue;
            if (tags[field.type_first] == .asterisk) {
                self.locals.items[@intFromEnum(lid)].is_pointer = true;
                return;
            }
        }
    }

    /// Mark the prong capture `is_error_capture` when the union field
    /// it binds is an error set.  `switch (r) { .err => |e| { free(p);
    /// return e; } }` over `union(enum) { ok: u8, err: anyerror }` is a
    /// real double free: Zig runs `errdefer` on `return e`, so the
    /// free inside the arm is the SECOND one.  `is_error_capture` is
    /// the only thing that picks `flushErrAndNormalDefers` over
    /// `flushScopeDefers` in `lowerReturn`, so without this the replay
    /// never happens and the bug is invisible.
    ///
    /// Only an error-set payload qualifies.  A `u8` prong binds an
    /// ordinary value and returning it must NOT replay errdefers —
    /// marking every capture would report a double free on every
    /// switch that captures a success payload.
    fn markErrorCapturesFromUnion(
        self: *Builder,
        payload_token: Ast.TokenIndex,
        un_ti: *const model_mod.TypeInfo,
        prong_values: []const Ast.Node.Index,
    ) void {
        const lid = self.switchCaptureLocal(payload_token) orelse return;
        for (prong_values) |v| {
            const field = self.unionFieldForProng(un_ti, v) orelse continue;
            if (field.type_first > field.type_last) continue;
            if (typeRangeIsErrorSet(self.tree, field.type_first, field.type_last)) {
                self.locals.items[@intFromEnum(lid)].is_error_capture = true;
                return;
            }
        }
    }

    /// The union field a `.<tag>` switch prong selects, if `un_ti`
    /// declares one by that name.
    fn unionFieldForProng(
        self: *const Builder,
        un_ti: *const model_mod.TypeInfo,
        prong_value: Ast.Node.Index,
    ) ?*const model_mod.FieldInfo {
        const tree = self.tree;
        if (tree.nodeTag(prong_value) != .enum_literal) return null;
        const tags = tree.tokens.items(.tag);
        const tag_name_tok = tree.nodeMainToken(prong_value);
        if (tag_name_tok >= tags.len) return null;
        if (tags[tag_name_tok] != .identifier) return null;
        return un_ti.findField(tree.tokenSlice(tag_name_tok));
    }

    /// `try expr` at statement position.  Lower `expr` on the success
    /// path (cur continues forward); add an error-exit edge to a sink
    /// block that replays errdefers + defers and terminates.  The sink
    /// has no successor — it represents the implicit `return error.X`.
    fn lowerTryStmt(self: *Builder, try_node: Ast.Node.Index, cur: *BlockId) !void {
        _ = try self.lowerComputedValue(try_node, cur);
    }

    /// Is this block node labeled (`blk: { ... }`)?  Returns the
    /// label-identifier token if so.  Block labels live at
    /// `main_token - 2` (identifier) + `main_token - 1` (`:`).
    fn blockLabelToken(self: *Builder, block_node: Ast.Node.Index) ?Ast.TokenIndex {
        const tree = self.tree;
        const main = tree.nodeMainToken(block_node);
        if (main < 2) return null;
        const tags = tree.tokens.items(.tag);
        if (tags[main - 1] != .colon) return null;
        if (tags[main - 2] != .identifier) return null;
        return main - 2;
    }

    /// If `expr` is a top-level labeled block at an expression
    /// position (`const x = blk: { ... }`, `return blk: {...}`,
    /// `x = blk: {...}`), lower its body in-place — advancing cur
    /// to the post-merge — and return true.  The caller then
    /// emits its decl/ret/assign on the post-merge cur, with an
    /// .unknown classification since we don't track which break
    /// path's value was taken.  Returns false for non-block exprs.
    /// If the labeled block has exactly one `break :label X` with
    /// a value, return X for classification.  Multiple distinct
    /// break values or none → null.
    fn singleLabeledBreakValue(
        self: *Builder,
        block_node: Ast.Node.Index,
        label_token: Ast.TokenIndex,
    ) ?Ast.Node.Index {
        const tree = self.tree;
        const label = tree.tokenSlice(label_token);
        const block_first = tree.firstToken(block_node);
        const block_last = tree.lastToken(block_node);

        var found: ?Ast.Node.Index = null;
        var node_idx: u32 = 1;
        while (node_idx < tree.nodes.len) : (node_idx += 1) {
            const node: Ast.Node.Index = @enumFromInt(node_idx);
            if (tree.nodeTag(node) != .@"break") continue;
            const ft = tree.firstToken(node);
            const lt = tree.lastToken(node);
            if (ft < block_first or lt > block_last) continue;
            const data = tree.nodeData(node).opt_token_and_opt_node;
            const lbl_tok = data[0].unwrap() orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(lbl_tok), label)) continue;
            const val = data[1].unwrap() orelse continue; // bare `break :blk;`
            if (found != null) return null; // multiple breaks — ambiguous
            found = val;
        }
        return found;
    }

    fn isComputedValue(self: *Builder, node: Ast.Node.Index) LoweringError!bool {
        if (self.classify_depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, self.classify_depth, node);
            return error.AnalysisBudgetExceeded;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        return switch (self.tree.nodeTag(node)) {
            .grouped_expression => try self.isComputedValue(self.tree.nodeData(node).node_and_token[0]),
            .@"comptime" => try self.isComputedValue(self.tree.nodeData(node).node),
            .if_simple, .@"if", .@"switch", .switch_comma, .block, .block_semicolon, .block_two, .block_two_semicolon, .@"try", .@"catch", .@"orelse", .bool_and, .bool_or, .bool_not => true,
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => try self.builtinHasComputedOperand(node),
            else => false,
        };
    }

    fn builtinHasComputedOperand(self: *Builder, node: Ast.Node.Index) LoweringError!bool {
        const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
        if (!pureScalarBuiltin(name) or isComptimeOnlyBuiltin(name)) return false;
        const builtin = std.zig.BuiltinFn.list.get(name) orelse return false;
        var buffer: [2]Ast.Node.Index = undefined;
        const arguments = self.tree.builtinCallParams(&buffer, node) orelse return false;
        for (arguments, 0..) |argument, ordinal| {
            if (ordinal == 0 and (builtin.tag == .as or builtin.tag == .mul_add)) continue;
            if (try self.isComputedValue(argument)) return true;
        }
        return false;
    }

    /// Constructors need no evaluation snapshot when all of their operands
    /// are reads. Blocks, control flow, calls and impure builtins abstain.
    fn effectFreeValueLiteral(self: *Builder, node: Ast.Node.Index) bool {
        var buffer: [2]Ast.Node.Index = undefined;
        if (self.tree.fullArrayInit(&buffer, node) == null and
            self.tree.fullStructInit(&buffer, node) == null) return false;
        const last = self.tree.lastToken(node);
        var token = self.tree.firstToken(node);
        while (token <= last) : (token += 1) {
            switch (self.tree.tokenTag(token)) {
                .semicolon,
                .keyword_if,
                .keyword_switch,
                .keyword_while,
                .keyword_for,
                .keyword_try,
                .keyword_catch,
                .keyword_orelse,
                .keyword_break,
                .keyword_return,
                .keyword_const,
                .keyword_var,
                => return false,
                .builtin => if (!pureScalarBuiltin(self.tree.tokenSlice(token))) return false,
                .identifier => if (token < last and self.tree.tokenTag(token + 1) == .l_paren) return false,
                else => {},
            }
        }
        return true;
    }

    /// Runtime-operand shape abstention also covers effects nested in an arg.
    fn valueNeedsSnapshot(self: *Builder, node: Ast.Node.Index) LoweringError!bool {
        if (try self.isComputedValue(node)) return true;
        var runtime: RuntimeOperandFilter = .{};
        const last = self.tree.lastToken(node);
        var token = self.tree.firstToken(node);
        while (token <= last) : (token += 1) {
            const tag = self.tree.tokenTag(token);
            if (tag == .l_brace and runtime.comptime_depth == null and runtime.type_depth == null) return true;
            if (!runtime.readsToken(self.tree, token)) continue;
            if (tag == .identifier and token < last and self.tree.tokenTag(token + 1) == .l_paren) return true;
            if (tag == .builtin and !pureScalarBuiltin(self.tree.tokenSlice(token))) return true;
        }
        return false;
    }

    /// Reserved pure scalar operations evaluate their operands once, in order.
    /// Each value is retained before later operand effects run.
    fn lowerScalarBuiltin(self: *Builder, node: Ast.Node.Index, cur: *BlockId, frame: ValueOutcomeFrame) LoweringError!bool {
        const target = frame.scalar_local orelse return false;
        if (!(try self.builtinHasComputedOperand(node))) return false;
        const name = self.tree.tokenSlice(self.tree.nodeMainToken(node));
        const builtin = std.zig.BuiltinFn.list.get(name) orelse return false;
        var buffer: [2]Ast.Node.Index = undefined;
        const arguments = self.tree.builtinCallParams(&buffer, node) orelse return false;
        var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
        var count: usize = 0;
        var defined = true;
        for (arguments, 0..) |argument, ordinal| {
            if (ordinal == 0 and (builtin.tag == .as or builtin.tag == .mul_add)) continue;
            // A bit cast's scalar result does not establish its operand's
            // category. Only intrinsic boolean selection proves this here.
            const scalar_operand = builtin.tag != .bit_cast or
                self.booleanLiteral(argument) != null or
                self.tree.nodeTag(argument) == .bool_and or self.tree.nodeTag(argument) == .bool_or;
            if (!scalar_operand or count == inputs.len) {
                defined = false;
                try self.lowerValueExpr(argument, cur, null);
                continue;
            }
            const snapshot = try self.newScalarValue(argument, cur.*);
            try self.lowerValueExpr(argument, cur, .{ .scalar_local = snapshot });
            inputs[count] = .{ .local = snapshot };
            count += 1;
        }
        if (frame.scalar_guard) |guard| {
            if (count == inputs.len) {
                defined = false;
            } else {
                inputs[count] = .{ .local = guard };
            }
        }
        // Keep the existing pure-call gap, but do not flatten operand reads
        // after their selected CFG paths and value-time snapshots.
        try self.appendStmt(cur.*, .{
            .kind = .{ .lowering_gap = .{ .note = "call-untracked", .may_assign_locals = false } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
        try self.appendStmt(cur.*, .{
            .kind = .{ .assign = .{
                .target = target,
                .rhs_kind = .unknown,
                .value_defined = defined,
                .value_inputs = inputs,
            } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
        if (frame.error_local != null) try self.recordValueOutcome(frame, node, cur, self.valueIsError(node, false));
        if (frame.array_local) |array| try self.emitArrayValue(cur.*, array, node);
        return true;
    }

    /// Lower computed values once, without flattening selected arm reads.
    fn lowerComputedValue(self: *Builder, node: Ast.Node.Index, cur: *BlockId) LoweringError!bool {
        if (self.classify_depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, self.classify_depth, node);
            return error.AnalysisBudgetExceeded;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        switch (self.tree.nodeTag(node)) {
            .grouped_expression => return self.lowerComputedValue(self.tree.nodeData(node).node_and_token[0], cur),
            .@"comptime" => return self.lowerComputedValue(self.tree.nodeData(node).node, cur),
            .if_simple, .@"if", .@"switch", .switch_comma, .block, .block_semicolon, .block_two, .block_two_semicolon, .@"try", .@"catch", .@"orelse", .bool_and, .bool_or, .bool_not => {
                try self.lowerValueExpr(node, cur, null);
                return true;
            },
            else => return false,
        }
    }

    fn newScalarValue(self: *Builder, node: Ast.Node.Index, cur: BlockId) LoweringError!LocalId {
        const local = try self.appendLocal(.{
            .name = "<selected scalar value>",
            .decl_pos = self.posOf(node),
            .is_control_local = true,
            .tracks_scalar_value = true,
        });
        try self.appendStmt(cur, .{
            .kind = .{ .decl = .{ .local = local, .init_kind = .undef } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
        return local;
    }

    fn emitBooleanCopy(self: *Builder, cur: BlockId, target: LocalId, source: LocalId, invert: bool, node: Ast.Node.Index) LoweringError!void {
        var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
        inputs[0] = .{ .local = source };
        try self.appendStmt(cur, .{
            .kind = .{ .assign = .{
                .target = target,
                .rhs_kind = .{ .boolean = if (invert) .{ .not_local = source } else .{ .local = source } },
                .value_defined = true,
                .value_inputs = inputs,
            } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    fn emitScalarValue(self: *Builder, cur: BlockId, local: LocalId, node: Ast.Node.Index, guard: ?LocalId) LoweringError!void {
        var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
        var defined = self.selectedValueInputs(node, &inputs, true);
        if (guard) |source| {
            var added = false;
            for (&inputs) |*input| {
                if (input.* == null) {
                    input.* = .{ .local = source };
                    added = true;
                    break;
                }
            }
            defined = defined and added;
        }
        // An unproved value is unknown, not undefined: value_defined carries
        // the certificate, and only a proved undefined input may report.
        const kind: ExprKind = if (self.booleanValue(node)) |value|
            .{ .boolean = value }
        else
            self.classifyExpr(node);
        try self.appendStmt(cur, .{
            .kind = .{ .assign = .{
                .target = local,
                .rhs_kind = kind,
                .integer_value = self.integerValue(node),
                .value_defined = defined,
                .value_inputs = inputs,
                .array_copy = self.arrayCopyIsElementwise(node),
            } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    fn newValueOutcomeFrame(self: *Builder, node: Ast.Node.Index, cur: BlockId) LoweringError!ValueOutcomeFrame {
        const pos = self.posOf(node);
        const local = try self.appendLocal(.{
            .name = "<computed error outcome>",
            .decl_pos = pos,
            .is_control_local = true,
        });
        try self.appendStmt(cur, .{
            .kind = .{ .decl = .{ .local = local, .init_kind = .plain } },
            .pos = pos,
            .end_pos = self.endPosOf(node),
        });
        return .{ .error_local = local };
    }

    fn setValueOutcome(self: *Builder, frame: ValueOutcomeFrame, node: Ast.Node.Index, cur: BlockId, is_error: bool) LoweringError!void {
        const error_local = frame.error_local orelse return;
        try self.appendStmt(cur, .{
            .kind = .{ .assign = .{
                .target = error_local,
                .rhs_kind = .{ .boolean = .{ .constant = is_error } },
            } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    fn assumeValueOutcome(self: *Builder, frame: ValueOutcomeFrame, node: Ast.Node.Index, cur: BlockId, is_error: bool) LoweringError!void {
        const error_local = frame.error_local orelse return;
        try self.appendStmt(cur, .{
            .kind = .{ .assume = if (is_error)
                .{ .local = error_local }
            else
                .{ .not_local = error_local } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    /// An opaque payload is not proof of success. Keep both channels and
    /// the existing gap contract, without evaluating the expression again.
    fn recordValueOutcome(self: *Builder, frame: ValueOutcomeFrame, node: Ast.Node.Index, cur: *BlockId, known: ?bool) LoweringError!void {
        if (frame.error_local == null) return;
        if (known) |is_error| {
            try self.setValueOutcome(frame, node, cur.*, is_error);
            return;
        }
        try self.appendStmt(cur.*, .{
            .kind = .{ .lowering_gap = .{ .note = "computed-error-outcome-opaque", .may_assign_locals = false } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
        const normal = try self.newBlock();
        const failure = try self.newBlock();
        const merge = try self.newBlock();
        try self.addEdge(cur.*, normal);
        try self.addEdge(cur.*, failure);
        try self.setValueOutcome(frame, node, normal, false);
        try self.setValueOutcome(frame, node, failure, true);
        try self.addEdge(normal, merge);
        try self.addEdge(failure, merge);
        cur.* = merge;
    }

    fn valueIsError(self: *Builder, node: Ast.Node.Index, unwrap_payload: bool) ?bool {
        if (self.classify_depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, self.classify_depth, node);
            return null;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        const tree = self.tree;
        switch (tree.nodeTag(node)) {
            .grouped_expression => return self.valueIsError(tree.nodeData(node).node_and_token[0], unwrap_payload),
            .@"comptime" => return self.valueIsError(tree.nodeData(node).node, unwrap_payload),
            .call, .call_one, .call_comma, .call_one_comma => {
                const frame = self.integerResolutionFrame() orelse return null;
                var result = self.queryOrUnknown(
                    zls_resolver_mod.TypeResolver.ActualType,
                    frame.typeOfNode(node),
                ) orelse return null;
                if (unwrap_payload) {
                    const tag = frame.resolver.typeTag(result) orelse return null;
                    if (tag != .error_union and tag != .optional) return null;
                    const child = frame.resolver.childType(result) orelse return null;
                    result = self.queryOrUnknown(
                        zls_resolver_mod.TypeResolver.ActualType,
                        frame.resolver.normalizedType(child),
                    ) orelse return null;
                }
                return switch (frame.resolver.typeTag(result) orelse return null) {
                    .error_union => null,
                    .error_set => true,
                    else => false,
                };
            },
            .if_simple, .@"if" => {
                const branch = tree.fullIf(node) orelse return null;
                const other = branch.ast.else_expr.unwrap() orelse return null;
                const then_error = self.valueIsError(branch.ast.then_expr, unwrap_payload) orelse return null;
                const else_error = self.valueIsError(other, unwrap_payload) orelse return null;
                return if (then_error == else_error) then_error else null;
            },
            .@"switch", .switch_comma => {
                const sw = tree.fullSwitch(node) orelse return null;
                var result: ?bool = null;
                for (sw.ast.cases) |case_node| {
                    const case = tree.fullSwitchCase(case_node) orelse return null;
                    const is_error = self.valueIsError(case.ast.target_expr, unwrap_payload) orelse return null;
                    if (result) |prior| if (prior != is_error) return null;
                    result = is_error;
                }
                return result;
            },
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                const label = self.blockLabelToken(node) orelse return null;
                const value = self.singleLabeledBreakValue(node, label) orelse return null;
                return self.valueIsError(value, unwrap_payload);
            },
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                if (unwrap_payload) return null;
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "@memset") or std.mem.eql(u8, name, "@memcpy")) return false;
                if (self.transparentCastSource(node)) |source| {
                    return self.valueIsError(source, false);
                }
                return null;
            },
            else => {},
        }
        if (unwrap_payload) return null;
        if (self.returnExprIsError(node)) return true;
        switch (tree.nodeTag(node)) {
            .number_literal, .char_literal, .string_literal, .multiline_string_literal, .enum_literal, .address_of, .struct_init_one, .struct_init_one_comma, .struct_init_dot_two, .struct_init_dot_two_comma, .struct_init_dot, .struct_init_dot_comma, .struct_init, .struct_init_comma, .array_init_one, .array_init_one_comma, .array_init_dot_two, .array_init_dot_two_comma, .array_init_dot, .array_init_dot_comma, .array_init, .array_init_comma => return false,
            .identifier => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if (std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false") or
                    std.mem.eql(u8, name, "null")) return false;
                if (self.name_to_local.get(name)) |local| {
                    const info = self.locals.items[@intFromEnum(local)];
                    if (info.is_pointer or info.is_unsigned) return false;
                }
                return null;
            },
            else => return null,
        }
    }

    /// Leaf call certificates run on their own return channel, before a
    /// value block's normal defers and before its enclosing try or catch.
    fn lowerOutcomeCall(self: *Builder, node: Ast.Node.Index, cur: *BlockId, frame: ValueOutcomeFrame) LoweringError!void {
        const known = self.valueIsError(node, false);
        if (known == false or frame.error_local == null) {
            try self.lowerStmt(node, cur);
            try self.setValueOutcome(frame, node, cur.*, false);
            return;
        }
        try self.emitUsesInExpr(node, cur.*, null);
        try self.invalidateCallAliases(node, cur.*);
        const normal = try self.newBlock();
        const failure = try self.newBlock();
        const merge = try self.newBlock();
        if (known != true) try self.addEdge(cur.*, normal);
        try self.addEdge(cur.*, failure);
        var normal_cur = normal;
        _ = try self.applyFieldEffects(node, .normal_success, &normal_cur);
        try self.emitSuccessfulCallOutputs(normal_cur, node);
        try self.setValueOutcome(frame, node, normal_cur, false);
        try self.addEdge(normal_cur, merge);
        var failure_cur = failure;
        _ = try self.applyFieldEffects(node, .error_return, &failure_cur);
        try self.setValueOutcome(frame, node, failure_cur, true);
        try self.addEdge(failure_cur, merge);
        cur.* = if (self.callReturnsNoreturn(node)) try self.newBlock() else merge;
    }

    fn directValueCall(self: *const Builder, node: Ast.Node.Index) ?Ast.Node.Index {
        return switch (self.tree.nodeTag(node)) {
            .grouped_expression => self.directValueCall(self.tree.nodeData(node).node_and_token[0]),
            .@"comptime" => self.directValueCall(self.tree.nodeData(node).node),
            .call, .call_one, .call_comma, .call_one_comma => node,
            else => null,
        };
    }

    fn lowerWrappedValue(self: *Builder, node: Ast.Node.Index, cur: *BlockId, result_frame: ?ValueOutcomeFrame) LoweringError!void {
        const tag = self.tree.nodeTag(node);
        const operand = if (tag == .@"try")
            self.tree.nodeData(node).node
        else
            self.tree.nodeData(node).node_and_node[0];
        if (tag == .@"orelse") {
            // Optional presence is not the error outcome of its payload.
            try self.lowerValueExpr(operand, cur, null);
            try self.emitOrelseFork(node, cur, result_frame);
            return;
        }
        var operand_frame: ?ValueOutcomeFrame = null;
        const direct_operand = self.directValueCall(operand);
        if (direct_operand) |call| {
            try self.emitUsesInExpr(call, cur.*, null);
            if (tag == .@"try") try self.invalidateCallAliases(call, cur.*);
        } else {
            operand_frame = try self.newValueOutcomeFrame(operand, cur.*);
            try self.lowerValueExpr(operand, cur, operand_frame);
        }
        if (tag == .@"catch") {
            try self.emitCatchFork(node, cur, operand_frame, result_frame);
        } else {
            const cleanup_operand = direct_operand orelse operand;
            try self.emitTryErrorExit(cur, self.posOf(node), cleanup_operand, operand_frame);
            if (operand_frame == null) try self.applyTopLevelCallEffects(cleanup_operand, cur, true);
            if (result_frame) |frame| {
                try self.recordValueOutcome(frame, node, cur, self.valueIsError(operand, true));
                if (frame.array_local) |local| try self.emitArrayValue(cur.*, local, operand);
                if (frame.scalar_local) |local| try self.emitScalarValue(cur.*, local, operand, frame.scalar_guard);
            }
        }
    }

    fn lowerValueExpr(self: *Builder, node: Ast.Node.Index, cur: *BlockId, result_frame: ?ValueOutcomeFrame) LoweringError!void {
        if (self.classify_depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, self.classify_depth, node);
            return error.AnalysisBudgetExceeded;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        const tree = self.tree;
        switch (tree.nodeTag(node)) {
            .bool_and, .bool_or, .bool_not => {
                try self.lowerConditionValue(node, cur, result_frame);
                if (result_frame) |frame| try self.setValueOutcome(frame, node, cur.*, false);
            },
            .if_simple, .@"if" => {
                const branch = tree.fullIf(node).?;
                const selector = if (result_frame != null and result_frame.?.scalar_local != null)
                    try self.newScalarValue(branch.ast.cond_expr, cur.*)
                else
                    null;
                if (selector) |local| {
                    try self.lowerConditionValue(branch.ast.cond_expr, cur, .{
                        .scalar_local = local,
                        .scalar_guard = result_frame.?.scalar_guard,
                    });
                } else try self.lowerConditionUses(branch.ast.cond_expr, cur);
                var branch_frame = result_frame;
                if (branch_frame) |*frame| frame.scalar_guard = selector;
                const then_block = try self.newBlock();
                const else_block = try self.newBlock();
                const merge = try self.newBlock();
                try self.addEdge(cur.*, then_block);
                try self.addEdge(cur.*, else_block);
                const condition = if (branch.payload_token == null) self.booleanValue(branch.ast.cond_expr) else null;
                try self.assumeCondition(then_block, branch.ast.cond_expr, condition, true);
                try self.assumeCondition(else_block, branch.ast.cond_expr, condition, false);
                const save = try self.localsLen();
                if (branch.payload_token) |token| try self.registerCapturesWith(token, then_block);
                var then_cur = then_block;
                try self.lowerValueExpr(branch.ast.then_expr, &then_cur, branch_frame);
                try self.addEdge(then_cur, merge);
                self.restoreLocalNames(save, tree.firstToken(node));
                var else_cur = else_block;
                if (branch.ast.else_expr.unwrap()) |expression| {
                    if (branch.error_token) |token| try self.registerErrorCapturesWith(token, else_block);
                    try self.lowerValueExpr(expression, &else_cur, branch_frame);
                    self.restoreLocalNames(save, tree.firstToken(node));
                } else if (result_frame) |frame| {
                    try self.recordValueOutcome(frame, node, &else_cur, null);
                }
                try self.addEdge(else_cur, merge);
                cur.* = merge;
            },
            .@"switch", .switch_comma => try self.lowerSwitch(node, cur, result_frame),
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                if (self.blockLabelToken(node)) |label| {
                    try self.lowerLabeledBlock(node, label, cur, result_frame);
                } else {
                    try self.lowerBlock(node, cur);
                    // A completing unlabeled block yields void, not an
                    // opaque error union. Its statements do not own the frame.
                    if (result_frame) |frame| try self.setValueOutcome(frame, node, cur.*, false);
                }
            },
            .call, .call_one, .call_comma, .call_one_comma => {
                if (result_frame) |frame| {
                    try self.lowerOutcomeCall(node, cur, frame);
                } else {
                    try self.lowerStmt(node, cur);
                }
                if (result_frame) |frame| if (frame.array_local) |local|
                    try self.emitArrayValue(cur.*, local, node);
                if (result_frame) |frame| if (frame.scalar_local) |local|
                    try self.emitScalarValue(cur.*, local, node, frame.scalar_guard);
            },
            .assign, .assign_destructure, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod, .assign_shl, .assign_shr, .assign_shl_sat, .assign_bit_and, .assign_bit_xor, .assign_bit_or, .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap, .assign_add_sat, .assign_sub_sat, .assign_mul_sat => {
                try self.lowerStmt(node, cur);
                if (result_frame) |frame| try self.setValueOutcome(frame, node, cur.*, false);
            },
            .@"return", .@"break", .@"continue", .unreachable_literal => try self.lowerStmt(node, cur),
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                if (result_frame) |frame| {
                    if (try self.lowerScalarBuiltin(node, cur, frame)) return;
                }
                try self.lowerStmt(node, cur);
                if (result_frame) |frame| {
                    try self.recordValueOutcome(frame, node, cur, self.valueIsError(node, false));
                }
                if (result_frame) |frame| if (frame.array_local) |local|
                    try self.emitArrayValue(cur.*, local, node);
                if (result_frame) |frame| if (frame.scalar_local) |local|
                    try self.emitScalarValue(cur.*, local, node, frame.scalar_guard);
            },
            .grouped_expression => try self.lowerValueExpr(tree.nodeData(node).node_and_token[0], cur, result_frame),
            .@"comptime" => try self.lowerValueExpr(tree.nodeData(node).node, cur, result_frame),
            .@"try", .@"catch", .@"orelse" => try self.lowerWrappedValue(node, cur, result_frame),
            else => {
                try self.emitUsesInExpr(node, cur.*, null);
                try self.applyTopLevelCallEffects(node, cur, false);
                if (result_frame) |frame| {
                    try self.recordValueOutcome(frame, node, cur, self.valueIsError(node, false));
                }
                if (result_frame) |frame| if (frame.array_local) |local|
                    try self.emitArrayValue(cur.*, local, node);
                if (result_frame) |frame| if (frame.scalar_local) |local|
                    try self.emitScalarValue(cur.*, local, node, frame.scalar_guard);
            },
        }
    }

    /// `blk: { ... }` at statement position — push label context,
    /// lower body normally, pop, then sew the natural fallthrough
    /// edge cur → merge and continue from merge.  Any `break :blk`
    /// inside the body adds its own edge to merge via
    /// lowerBreakOrContinue.
    fn lowerLabeledBlock(
        self: *Builder,
        block_node: Ast.Node.Index,
        label_token: Ast.TokenIndex,
        cur: *BlockId,
        result_frame: ?ValueOutcomeFrame,
    ) LoweringError!void {
        const tree = self.tree;
        const label = tree.tokenSlice(label_token);
        const merge = try self.newBlock();
        try self.block_label_stack.append(self.gpa, .{
            .label = label,
            .merge = merge,
            .defer_depth = self.deferred.items.len,
            .result_frame = result_frame,
        });
        try self.lowerBlock(block_node, cur);
        _ = self.block_label_stack.pop();
        // Natural fallthrough yields void. Selected value breaks already
        // recorded their own channel before their normal defer replay.
        if (result_frame) |frame| try self.setValueOutcome(frame, block_node, cur.*, false);
        try self.addEdge(cur.*, merge);
        cur.* = merge;
    }

    /// `break`/`continue` — add an edge from cur to the innermost
    /// loop's merge (break) or header (continue), then redirect cur
    /// to a fresh dead block so any statements emitted after the
    /// break/continue don't leak into the actual flow.  Labeled
    /// break first searches the block-label stack, then loops.
    fn lowerBreakOrContinue(
        self: *Builder,
        cur: *BlockId,
        kind: enum { @"break", @"continue" },
        node: Ast.Node.Index,
    ) !void {
        const tree = self.tree;

        // `break/continue :name` — Ast data is opt_token_and_opt_node;
        // the OptionalTokenIndex points at the bare identifier (no
        // colon).  For labeled break, search block_label_stack first
        // (since blocks can only be break targets, never continue),
        // then fall through to loop_stack.  Done BEFORE the "no
        // loops" check so `break :blk` inside a labeled block (which
        // doesn't push onto loop_stack) still resolves correctly.
        const data = tree.nodeData(node).opt_token_and_opt_node;
        const opt_label_tok = data[0];
        const opt_value_node = data[1];
        // Resolve the target before evaluating its value. Only the target
        // value block owns the frame; intervening statement blocks do not.
        if (opt_label_tok.unwrap()) |lt| {
            const wanted = tree.tokenSlice(lt);
            // Block labels: break only.  Continue to a block label is
            // a compile error in Zig; defensively skip if encountered.
            if (kind == .@"break") {
                var i = self.block_label_stack.items.len;
                while (i > 0) {
                    i -= 1;
                    const ctx = self.block_label_stack.items[i];
                    if (std.mem.eql(u8, ctx.label, wanted)) {
                        if (opt_value_node.unwrap()) |value| {
                            try self.lowerValueExpr(value, cur, ctx.result_frame);
                            if (ctx.result_frame) |frame| if (frame.return_kind) |output| {
                                // The selected break has completed lowering while its
                                // lexical bindings still exist. Never classify it later
                                // against the enclosing block's restored name table.
                                output.* = self.classifyExpr(value);
                                const loans = try self.returnStackLoans(value, tree.firstToken(value), .normal);
                                switch (output.*) {
                                    .stack_ref, .copy_of, .composite_borrow => try self.emitAdditionalEscapeChecks(value, cur.*, output.*, loans),
                                    else => {},
                                }
                            };
                        } else if (ctx.result_frame) |frame| {
                            try self.recordValueOutcome(frame, node, cur, null);
                        }
                        // A break carrying an error union is still a normal
                        // block exit. Replay normal defers after leaf cleanup.
                        try self.flushScopeDefers(cur, ctx.defer_depth);
                        try self.addEdge(cur.*, ctx.merge);
                        cur.* = try self.newBlock();
                        return;
                    }
                }
            }
            // Loop labels: walk inside-out.
            var i = self.loop_stack.items.len;
            while (i > 0) {
                i -= 1;
                const ctx = self.loop_stack.items[i];
                if (ctx.label) |lbl| {
                    if (std.mem.eql(u8, lbl, wanted)) {
                        if (opt_value_node.unwrap()) |value| try self.lowerValueExpr(value, cur, null);
                        const target = switch (kind) {
                            .@"break" => ctx.merge,
                            .@"continue" => ctx.continue_to,
                        };
                        try self.flushScopeDefers(cur, ctx.defer_depth);
                        try self.addEdge(cur.*, target);
                        cur.* = try self.newBlock();
                        return;
                    }
                }
            }
            // No match in either stack.
            if (opt_value_node.unwrap()) |value| try self.lowerValueExpr(value, cur, null);
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "labeled-break-no-loop" } },
                .pos = self.posOf(node),
                .end_pos = self.endPosOf(node),
            });
            return;
        }

        // Unlabeled: innermost loop.  Now `loop_stack` may be empty
        // (we don't pre-check anymore so labeled-break can resolve
        // via block_label_stack first); a truly unlabeled break
        // outside any loop is a Zig compile error, so handle
        // defensively with a gap.
        if (opt_value_node.unwrap()) |value| try self.lowerValueExpr(value, cur, null);
        if (self.loop_stack.items.len == 0) {
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "break-outside-loop" } },
                .pos = self.posOf(node),
                .end_pos = self.endPosOf(node),
            });
            return;
        }
        const ctx = self.loop_stack.items[self.loop_stack.items.len - 1];
        const target = switch (kind) {
            .@"break" => ctx.merge,
            .@"continue" => ctx.continue_to,
        };
        try self.flushScopeDefers(cur, ctx.defer_depth);
        try self.addEdge(cur.*, target);
        cur.* = try self.newBlock();
    }

    /// Build the synthetic error-exit sink for an in-expression `try`.
    /// Used by both `lowerTryStmt` and `lowerVarDecl` (when init is a
    /// top-level `.@"try"`).  The sink is a new block reachable from
    /// `from` with errdefer + defer replayed, terminated by a ret.
    fn emitTryErrorExit(self: *Builder, cur: *BlockId, pos: SrcPos, operand: Ast.Node.Index, operand_frame: ?ValueOutcomeFrame) LoweringError!void {
        // Split: success path continues in a FRESH block.  Without
        // this, subsequent stmts emitted into the original `cur`
        // would propagate their post-state into the err_exit sink
        // (via the cur→err_exit edge), causing the sink to see e.g.
        // post-defer-free state and fire spurious double-free.
        const err_exit = try self.newBlock();
        const post_try = try self.newBlock();
        try self.addEdge(cur.*, err_exit);
        try self.addEdge(cur.*, post_try);

        var err_cur = err_exit;
        if (operand_frame) |frame| {
            try self.assumeValueOutcome(frame, operand, err_exit, true);
            try self.assumeValueOutcome(frame, operand, post_try, false);
        } else {
            _ = try self.applyFieldEffects(operand, .error_return, &err_cur);
        }
        try self.flushErrAndNormalDefers(&err_cur);
        try self.appendStmt(err_cur, .{
            .kind = .{ .ret = .{
                .value_kind = .unknown,
                .is_borrowed_return_type = self.is_borrowed_return_type,
            } },
            .pos = pos,
            // Synthetic ret — no source extent to highlight; fall back
            // to a single-column range via end_pos = pos.
            .end_pos = pos,
        });

        cur.* = post_try;
    }

    /// `lhs catch BODY` at statement position — forks into two paths:
    /// success (lhs's side effects only) and error (BODY runs).  Both
    /// join into a fresh merge block.  Unlike `try`, catch consumes
    /// the error; errdefers do NOT fire on the error edge.
    fn lowerCatchStmt(self: *Builder, catch_node: Ast.Node.Index, cur: *BlockId) !void {
        _ = try self.lowerComputedValue(catch_node, cur);
    }

    /// `lhs orelse BODY` — the optional's success path continues in
    /// `cur` (any nested try / catch / orelse the lhs carries is
    /// lowered there first, so evaluation order holds), the null path
    /// lowers BODY in its own block, and both join at a fresh merge.
    /// The shape mirrors `lowerCatchStmt`; orelse has no payload to
    /// register.
    ///
    /// Every kill the fallback performs belongs in the CFG.  A body
    /// that frees, deinits an arena or transfers ownership changes the
    /// state the merge sees, and dropping it makes the orelse invisible
    /// to the dataflow — the kill simply never happens, so the double
    /// free it causes is reported for the `catch` spelling of the same
    /// program and missed for `orelse`.
    ///
    /// Statement and value positions share selected fallback lowering.
    fn lowerOrelseStmt(self: *Builder, orelse_node: Ast.Node.Index, cur: *BlockId) LoweringError!void {
        _ = try self.lowerComputedValue(orelse_node, cur);
    }

    /// Append a catch-body fork to `cur`: one edge straight to merge
    /// (success), one through a new block where the catch body lowers,
    /// then both join.  `cur` advances to merge.  Used by
    /// `lowerCatchStmt`, `lowerVarDecl`, `lowerReturn`, `lowerAssign`
    /// — every position where `expr catch BODY` can appear at top
    /// level of an expression.
    ///
    /// `catch_node` is the `.@"catch"` Ast node itself (not its rhs)
    /// so we can also resolve the optional `|err|` payload — Zig
    /// AST doesn't surface it through a struct helper.
    fn emitCatchFork(self: *Builder, catch_node: Ast.Node.Index, cur: *BlockId, operand_frame: ?ValueOutcomeFrame, result_frame: ?ValueOutcomeFrame) LoweringError!void {
        const tree = self.tree;
        const body_node = tree.nodeData(catch_node).node_and_node[1];
        const operand = tree.nodeData(catch_node).node_and_node[0];
        const cleanup_operand = self.directValueCall(operand) orelse operand;
        if (operand_frame == null) try self.invalidateCallAliases(cleanup_operand, cur.*);
        const success_block = try self.newBlock();

        const catch_block = try self.newBlock();
        const merge = try self.newBlock();

        try self.addEdge(cur.*, catch_block);
        try self.addEdge(cur.*, success_block);
        var success_cur = success_block;
        if (operand_frame) |frame| {
            try self.assumeValueOutcome(frame, operand, success_block, false);
            try self.assumeValueOutcome(frame, operand, catch_block, true);
        } else {
            try self.applyTopLevelCallEffects(cleanup_operand, &success_cur, true);
        }
        if (result_frame) |frame| {
            try self.recordValueOutcome(frame, catch_node, &success_cur, self.valueIsError(operand, true));
            if (frame.scalar_local) |local| try self.emitScalarValue(success_cur, local, operand, frame.scalar_guard);
        }
        try self.addEdge(success_cur, merge);

        // `catch |err| BODY` — payload is `main_token + 2` when the
        // token immediately following `catch` is `|`.  Scope: body only.
        const scope = try self.localsLen();
        if (self.catchPayloadToken(catch_node)) |pt| {
            try self.registerErrorCaptures(pt);
        }

        var catch_cur = catch_block;
        if (operand_frame == null) _ = try self.applyFieldEffects(cleanup_operand, .error_return, &catch_cur);
        try self.lowerValueExpr(body_node, &catch_cur, result_frame);
        try self.addEdge(catch_cur, merge);
        self.restoreLocalNames(scope, tree.firstToken(catch_node));

        cur.* = merge;
    }

    fn catchPayloadToken(self: *Builder, catch_node: Ast.Node.Index) ?Ast.TokenIndex {
        const tree = self.tree;
        const main = tree.nodeMainToken(catch_node);
        const tags = tree.tokens.items(.tag);
        if (main + 1 >= tags.len) return null;
        if (tags[main + 1] != .pipe) return null;
        return main + 2;
    }

    fn lowerVarDecl(self: *Builder, decl_node: Ast.Node.Index, cur: *BlockId) !void {
        const tree = self.tree;
        const var_decl = tree.fullVarDecl(decl_node) orelse {
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "var_decl-extract" } },
                .pos = self.posOf(decl_node),
                .end_pos = self.endPosOf(decl_node),
            });
            return;
        };
        const name_tok = var_decl.ast.mut_token + 1;
        if (tree.tokens.items(.tag)[name_tok] != .identifier) {
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "var_decl-no-name" } },
                .pos = self.posOf(decl_node),
                .end_pos = self.endPosOf(decl_node),
            });
            return;
        }
        const name = tree.tokenSlice(name_tok);
        const declared_array = if (var_decl.ast.type_node.unwrap()) |tn|
            self.typeIsStackArray(tn)
        else
            false;
        var is_pointer = if (var_decl.ast.type_node.unwrap()) |tn|
            self.typeIsPointer(tn)
        else
            false;

        const init_opt = var_decl.ast.init_node.unwrap();
        const computed_type: ?BindingValueType = if (init_opt) |init|
            if (try self.isComputedValue(init))
                self.bindingValueType(var_decl.ast.type_node.unwrap(), init_opt, .unknown)
            else
                null
        else
            null;

        // Capture each selected array value before its arm merges and before
        // block-local names leave scope. The source binding is registered later.
        var init_was_lowered = false;
        var selected_array: ?LocalId = null;
        var selected_scalar: ?LocalId = null;
        if (init_opt) |init| {
            // An unannotated computed initializer can still yield a fixed
            // array: `const t = comptime blk: { ...; break :blk array; };`.
            const inferred_extent: ?u64 = if (declared_array or var_decl.ast.type_node != .none or
                !(try self.isComputedValue(init))) null else inferred: {
                const frame = self.integerResolutionFrame() orelse break :inferred null;
                const ty = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(init)) orelse break :inferred null;
                if (frame.resolver.typeTag(ty) != .array) break :inferred null;
                break :inferred if (ty.data == .array)
                    ty.data.array.elem_count
                else
                    self.queryOrUnknown(u64, frame.resolver.fixedArrayLen(init));
            };
            if ((declared_array or inferred_extent != null) and (try self.isComputedValue(init))) {
                const selected = try self.appendLocal(.{
                    .name = "<selected array value>",
                    .decl_pos = self.posOf(init),
                    .is_array = true,
                    .array_extent = if (var_decl.ast.type_node.unwrap()) |type_node|
                        if (self.fill.declaredExtent(.{ .first = tree.firstToken(type_node), .last = tree.lastToken(type_node) })) |extent|
                            extent.number
                        else
                            null
                    else
                        inferred_extent,
                    .is_control_local = true,
                });
                try self.appendStmt(cur.*, .{
                    .kind = .{ .decl = .{ .local = selected, .init_kind = .undef } },
                    .pos = self.posOf(init),
                    .end_pos = self.endPosOf(init),
                });
                try self.lowerValueExpr(init, cur, .{ .array_local = selected });
                selected_array = selected;
                init_was_lowered = true;
            } else if (computed_type != null and computed_type.?.runtime_scalar) {
                const selected = try self.newScalarValue(init, cur.*);
                try self.lowerValueExpr(init, cur, .{ .scalar_local = selected });
                selected_scalar = selected;
                init_was_lowered = true;
            } else {
                init_was_lowered = try self.lowerComputedValue(init, cur);
            }
        }

        const init_kind: ExprKind = if (selected_array) |selected|
            .{ .copy_of = selected }
        else if (init_opt) |init|
            self.classifyExpr(init)
        else
            .plain;

        // Pointer inference asks two different questions of the init.
        // `init_shape` is the TYPE-PRESERVING peel (`try f()`, `f()
        // catch …`, `f() orelse …`, `(f())` all bind `f()`'s result,
        // and the init-shape proofs below only recognise a call node);
        // `init_value` looks through an optional unwrap as well and so
        // names the value that is really bound.  The syntactic proofs
        // must use the first: `b.parent().?` binds `parent`'s optional
        // PAYLOAD, which `parent`'s name and receiver say nothing
        // about, so proving "pointer" through the unwrap hides the
        // stack escape of a by-value payload.  The semantic query at
        // the bottom resolves that payload's real type instead.
        // The same peel, keeping whether it crossed an error-accepting
        // wrapper.  A declaration-driven proof has to know that the
        // binding holds the callee's success PAYLOAD before it may read
        // an `E!T` declaration as handing out a pointer.
        const init_shape_peel: ?Peeled = if (init_opt) |init|
            initPeelNode(self, init, .declared_type)
        else
            null;
        const init_value: ?Ast.Node.Index = if (init_opt) |init|
            initValueNode(self, init)
        else
            null;

        // Infer is_pointer from the init expression when there's no
        // explicit type annotation.  Catches the common shapes:
        //   - `const p = &x.field;` — literal address-of
        //   - `const p = gpa.create(T);` — heap-alloc returns *T
        //   - `const p = &x;` aliasing a known pointer local (copy_of)
        //   - `var p = pool.get(); p.* = …;` — `p.*` use proves
        //     pointer-ness when the call's return type is opaque
        // Prevents stack-escape FPs on `&p.subfield` later, since p
        // is itself a pointer into caller-owned (or heap) storage.
        if (!is_pointer) {
            if (init_value) |value| {
                if (tree.nodeTag(value) == .address_of) is_pointer = true;
            }
            if (init_kind == .heap_alloc) is_pointer = true;
            if (init_kind == .copy_of) {
                const src = init_kind.copy_of;
                if (self.locals.items[@intFromEnum(src)].is_pointer) is_pointer = true;
            }
            // Body-use signal: scan forward from the var_decl for
            // `<name>.*` — if the local is ever dereferenced, it must
            // be a pointer.  Cheap: O(remaining_tokens) per opaque-
            // init decl; many decls get short-circuited by the
            // cheaper checks above.  Scan bounded to the fn body's
            // last token (the closing `}` of the fn).
            // Also runs for `copy_of(arena_src)` — `arena_alloc.create(T)`
            // produces a copy_of the arena local, but the result IS a
            // pointer (*T); the deref scan catches it correctly.
            if (!is_pointer and (init_kind == .unknown or
                (init_kind == .copy_of and blk: {
                    const src = init_kind.copy_of;
                    const h = self.locals.items[@intFromEnum(src)].init_hint;
                    break :blk h == .arena_local or h == .arena_allocator;
                })))
            {
                if (localIsDereferencedAfter(self.tree, name, name_tok, self.fn_body_last)) {
                    is_pointer = true;
                }
            }
            // An indexed `.items` expression copies an element. When the
            // collection's declared element type is a pointer, the copy is
            // also a pointer into non-stack storage.
            if (!is_pointer) {
                if (init_value) |value| {
                    if (self.initArrayElementIsPointer(value)) is_pointer = true;
                }
            }
            // The callee's own DECLARED result type settles the same
            // question with no name and no receiver spelling in it:
            // `fn sourceHandle(self: *Ctx, p: []const u8) !*Handle`
            // hands back a `*Handle` after `catch`, so the binding is a
            // pointer into storage the context owns and `&handle.<f>`
            // is not a borrow of this frame.  Runs before the resolver
            // because a declaration answers on its own, and because the
            // resolver's node-level query has to retype the whole call
            // chain — receiver, field, method — to reach the same one.
            //
            // A callee this file cannot read answers nothing, so the
            // syntactic proofs above and the resolver below still
            // decide those; nothing is retired here.
            if (!is_pointer and init_kind == .unknown) {
                if (init_shape_peel) |peel| {
                    if (self.declaredCallYieldsPointer(peel.node, peel.accepted_error)) is_pointer = true;
                }
            }
            // `self.handle.?` — the unwrapped payload is a pointer
            // exactly when the FIELD is declared `?*T`.  Neither the
            // callee spelling above nor the resolver can settle this
            // (`?*@import("mod").Doc` is unresolvable across the
            // module boundary), so read the declaration.
            if (!is_pointer and init_kind == .unknown) {
                if (init_opt) |init| {
                    if (self.initUnwrapsOptionalPointerField(init)) is_pointer = true;
                }
            }
            // ZLS fallback: if the init expression resolves to a
            // pointer type at the outermost level, the local is a
            // pointer.  Catches opaque-pointer-returning calls whose
            // receiver isn't a locally-tracked pointer.
            //
            // A successful `null` is the resolver's normal "nobody can
            // tell": no proof and no error, so `is_pointer` stays what
            // the syntactic proofs above left it.  A FAILED query is
            // not that — an allocation failure or a cancelled read
            // leaves the question open, and filing it as "not a
            // pointer" under-proves the local and charges its
            // `&local.field` addresses to the frame without saying so.
            // It is recorded for the lowering entry point to raise.
            if (!is_pointer and init_kind == .unknown) {
                if (init_value) |value| {
                    if (self.zls) |z| {
                        if (self.queryOrUnknown(bool, z.resolvedTypeIsPointer(value)) == true) {
                            is_pointer = true;
                        } else if (init_opt) |init| {
                            // Either spelling can be the one the
                            // resolver can type: the peeled plain call
                            // is the easy node, while for `catch` the
                            // WRAPPER's own type is the payload the
                            // binding holds.  Asking both keeps either
                            // one a proof, so a shape this pass now
                            // peels never costs an answer the wrapper
                            // spelling used to give.
                            if (init != value and
                                self.queryOrUnknown(bool, z.resolvedTypeIsPointer(init)) == true)
                            {
                                is_pointer = true;
                            }
                        }
                    }
                }
            }
        }

        // Derive init_hint from the classification — avoids a second
        // classifyExpr call (which would double-mint Arena/Heap ids).
        var effective_init_kind = init_kind;
        const init_hint: InitHint = blk: {
            switch (init_kind) {
                .arena_init => break :blk .arena_local,
                .heap_alloc => break :blk .heap_local,
                // Allocator-provenance: when init_kind is .copy_of(src)
                // (set by classifyExpr's .allocator()-detection path,
                // or by simple aliasing `const a2 = a;`), inherit
                // .arena_allocator from the source if it's arena-bound.
                // Lets `.alloc()` calls through any depth of allocator
                // alias produce arena memory.
                .copy_of => |src| {
                    const src_hint = self.locals.items[@intFromEnum(src)].init_hint;
                    if (src_hint == .arena_local or src_hint == .arena_allocator) {
                        break :blk .arena_allocator;
                    }
                },
                else => {},
            }
            // Type alias: `const X = struct {...};` / `enum` / `union`
            // / `opaque`.  X has no runtime storage; `X.<id>` is a
            // static (comptime / data-segment) lookup, not a stack
            // borrow.  Without this, `&X.<static_var>` fires
            // stack-escape on the canonical fn-local singleton
            // pattern.
            if (init_opt) |i| if (self.initIsContainerDecl(i)) break :blk .type_alias;
            // `const X = comptime <expr>;` — X lives in static
            // / data-segment memory.  `&X` is NOT a stack borrow.
            // Common in vtable-construction patterns.
            if (init_opt) |i| if (tree.nodeTag(i) == .@"comptime") break :blk .type_alias;
            // `comptime var X = ...;` — comptime-storage variable.
            // Lives in static memory; `&X` is safe to return.
            if (var_decl.comptime_token != null) break :blk .type_alias;
            // Struct-wrap propagation: `var ma = Wrapper{ .inner =
            // arena };` — ma carries arena via its field.  Override
            // init_kind to .copy_of(wrapper) so transferDecl
            // propagates arena's origin to ma at state-tracking time
            // (the hint alone only affects classify-time decisions).
            if (init_opt) |i| if (self.initWrapsResourceLocalRef(i)) |hit| {
                effective_init_kind = .{ .copy_of = hit.local };
                break :blk hit.hint;
            };
            break :blk .other;
        };
        // Function-pointer binding: `const op = some_fn;` where
        // some_fn is in our annotation DB.  Records the binding so
        // call sites `op(args)` resolve through to some_fn's
        // annotation / takes / is_noreturn.
        const bound_fn_name: ?[]const u8 = if (init_opt) |i| self.boundFnName(i) else null;
        // Type annotation on the decl (`var x: Foo = ...`) — extracted
        // for receiver-type tracking.  When absent, fall back to
        // inferring the type from the init expression — recognises
        // `T.init(...)` / `try T.init(...)` and `T{...}` shapes so
        // `var owner = try Owner.init(...)` still resolves to "Owner".
        // Implicit-typed decls without a recognisable constructor
        // leave type_name null; the lookup falls back to bare-name.
        //
        // What the callee declared it returns, read once: the NAME of
        // that type is only meaningful when this file can look it up
        // again, and the declaration behind it is not — see
        // [ownerScopedResultType].
        const declared_result: ?DeclaredResult = if (init_opt) |init|
            self.declaredResultOfInit(init)
        else
            null;
        const decl_type_name: ?[]const u8 = blk: {
            if (var_decl.ast.type_node.unwrap()) |tn| {
                break :blk self.extractTypeName(tn, self.self_type);
            }
            if (init_opt) |init| {
                break :blk self.inferTypeNameFromInit(init, declared_result);
            }
            break :blk null;
        };
        // Resolve arithmetic operands before registering the new binding,
        // so a shadowing declaration cannot capture its own initializer.
        const checked_difference = if (init_opt) |init| self.checkedDifference(init) else null;
        const value_type = computed_type orelse self.bindingValueType(
            var_decl.ast.type_node.unwrap(),
            init_opt,
            init_kind,
        );
        const header_source = if (value_type.slice_header and init_opt != null)
            self.sliceHeaderSource(init_opt.?)
        else
            null;
        var init_inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
        const init_defined = if (selected_scalar) |selected| selected: {
            init_inputs[0] = .{ .local = selected };
            effective_init_kind = .{ .copy_of = selected };
            break :selected true;
        } else if (init_opt) |init|
            if (!value_type.runtime_scalar)
                self.selectedValueInputs(init, &init_inputs, false)
            else
                self.selectedValueInputs(init, &init_inputs, true)
        else
            true;
        const local = try self.registerLocalWithPointerHint(
            name,
            self.posOfToken(name_tok),
            declared_array,
            init_hint,
            bound_fn_name,
            decl_type_name,
            is_pointer,
        );
        self.integer_domains.items[@intFromEnum(local)] = value_type.domain;
        self.locals.items[@intFromEnum(local)].tracks_scalar_value = value_type.runtime_scalar;
        self.locals.items[@intFromEnum(local)].is_pointer =
            !value_type.slice_header and (is_pointer or value_type.pointer_header);
        self.locals.items[@intFromEnum(local)].is_slice = value_type.slice_header;
        self.locals.items[@intFromEnum(local)].tracks_array_payload =
            value_type.aggregate_value or value_type.container != null;
        if (init_kind == .undef and !value_type.pointer_header and !value_type.slice_header)
            try self.recordDiagnosticStructLayout(local, value_type.container);
        if (init_kind == .copy_of and !value_type.pointer_header and !value_type.slice_header)
            self.locals.items[@intFromEnum(local)].runtime_fields = self.locals.items[@intFromEnum(init_kind.copy_of)].runtime_fields;
        if (init_kind == .copy_of and var_decl.ast.type_node == .none and
            init_value != null and tree.nodeTag(init_value.?) == .identifier)
        {
            const source_info = self.locals.items[@intFromEnum(init_kind.copy_of)];
            if (source_info.is_array) {
                self.locals.items[@intFromEnum(local)].is_array = true;
                self.locals.items[@intFromEnum(local)].array_extent = source_info.array_extent;
            }
        }
        if (var_decl.ast.type_node.unwrap()) |type_node| {
            const info = &self.locals.items[@intFromEnum(local)];
            info.is_unsigned = unsignedType(tree, type_node);
            if (self.fill.declaredExtent(.{ .first = tree.firstToken(type_node), .last = tree.lastToken(type_node) })) |extent| {
                info.array_extent = extent.number;
                if (extent.number != null) info.is_array = true;
            }
        } else if (init_opt) |init| {
            if (self.integerValue(init) != null) self.locals.items[@intFromEnum(local)].is_unsigned = true;
            if (init_value) |value| {
                if (tree.nodeTag(value) == .identifier) {
                    if (self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(value)))) |source| {
                        const source_info = self.locals.items[@intFromEnum(source)];
                        const info = &self.locals.items[@intFromEnum(local)];
                        info.is_array = source_info.is_array;
                        info.array_extent = source_info.array_extent;
                        info.is_unsigned = source_info.is_unsigned;
                    }
                }
            }
        }
        if (init_value) |value| {
            const can_infer_array = switch (tree.nodeTag(value)) {
                .address_of => false,
                else => true,
            };
            if (!self.locals.items[@intFromEnum(local)].is_array and can_infer_array) {
                if (self.integerResolutionFrame()) |frame| {
                    const shape = var_decl.ast.type_node.unwrap() orelse value;
                    const actual = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(shape));
                    if (actual) |ty| {
                        if (frame.resolver.typeTag(ty) == .array) {
                            const info = &self.locals.items[@intFromEnum(local)];
                            info.is_array = true;
                            info.array_extent = if (ty.data == .array)
                                ty.data.array.elem_count
                            else
                                self.queryOrUnknown(u64, frame.resolver.fixedArrayLen(shape));
                        }
                    }
                }
            }
            if (var_decl.ast.type_node == .none and !self.locals.items[@intFromEnum(local)].is_array) {
                if (self.literalArrayExtent(value)) |extent| {
                    const info = &self.locals.items[@intFromEnum(local)];
                    info.is_array = true;
                    info.array_extent = extent;
                }
            }
        }
        if (var_decl.ast.type_node == .none) {
            if (init_opt) |init| {
                if (self.inferredUnsignedCall(init)) self.locals.items[@intFromEnum(local)].is_unsigned = true;
            }
            if (checked_difference != null) self.locals.items[@intFromEnum(local)].is_unsigned = true;
        }
        if (tree.tokenTag(var_decl.ast.mut_token) == .keyword_const) {
            try self.immutable_locals.put(self.gpa, local, {});
        }
        // A declared type whose NAME cannot be looked up from this file
        // is still a declaration, and it is the only thing the field
        // walk behind `&<binding>.<field>…` can read.  Kept beside the
        // local rather than in place of `type_name`, which every
        // name-based consumer reads.
        if (declared_result) |result| {
            if (result.owner) |owner| {
                if (self.cache) |cache| {
                    if (cache.typeInOwnerScope(owner, result.name)) |bound| {
                        try self.bound_types.put(self.gpa, local, bound);
                    }
                }
            }
        }

        // A binding whose initializer produced an address of this
        // frame hands that address out under its own name from here
        // on — `const alias = &local;` makes `alias` and `&local`
        // interchangeable, which is what a `catch alias` /
        // `orelse alias` fallback needs the builder to be able to
        // follow.
        switch (effective_init_kind) {
            .stack_ref, .composite_borrow => |src| {
                self.locals.items[@intFromEnum(local)].frame_borrow_origin = src;
            },
            .copy_of => |source| {
                if (tree.tokenTag(var_decl.ast.mut_token) == .keyword_const and
                    self.locals.items[@intFromEnum(local)].is_pointer)
                {
                    if (self.locals.items[@intFromEnum(source)].frame_borrow_origin) |owner| {
                        const info = self.locals.items[@intFromEnum(owner)];
                        if (info.is_array and !info.is_pointer and !info.is_slice)
                            self.locals.items[@intFromEnum(local)].frame_borrow_origin = owner;
                    }
                }
            },
            else => {},
        }
        if (self.immutable_locals.contains(local) and self.locals.items[@intFromEnum(local)].is_pointer) {
            if (init_opt) |init| {
                const shape = initShapeNode(self, init);
                if (tree.nodeTag(shape) == .address_of) {
                    const addressed = tree.nodeData(shape).node;
                    if (self.classifySourceProjection(addressed, 0)) |source|
                        try self.pointer_value_sources.put(self.gpa, local, source);
                } else if (tree.nodeTag(shape) == .identifier) {
                    const source = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(shape)));
                    if (source) |id| if (self.pointer_value_sources.get(id)) |projection|
                        try self.pointer_value_sources.put(self.gpa, local, projection);
                }
            }
        }

        // Emit .use stmts for every local read by the init expression
        // (before the .decl so the read is checked against pre-decl state).
        // Computed values already emitted each selected arm. A second flat
        // walk would read assignment targets and untaken value branches.
        if (!init_was_lowered) {
            if (init_opt) |init| try self.emitUsesInExpr(init, cur.*, null);
        }
        // Complete normal-return stores before copying the result projection.
        if (init_opt) |init| {
            if (!init_was_lowered) try self.applyTopLevelCallEffects(init, cur, false);
        }

        const decl_index = self.block_stmts.items[@intFromEnum(cur.*)].items.len;
        try self.appendStmt(cur.*, .{
            .kind = .{ .decl = .{
                .local = local,
                .init_kind = effective_init_kind,
                .integer_value = if (init_opt) |init| self.integerValue(init) else null,
                .value_defined = init_defined,
                .value_inputs = init_inputs,
                .array_copy = selected_array != null or
                    (if (init_opt) |init| self.arrayCopyIsElementwise(init) else true),
            } },
            .pos = self.posOf(decl_node),
            .end_pos = self.endPosOf(decl_node),
        });
        // Returned storage can be identified even when its value/type remains
        // uncertified. Record its byte origin independently of init_defined
        // and inferred array metadata; this never grants a value certificate.
        if (init_opt) |init| if (self.arrayCallSourceFor(init, true)) |source| {
            const input: cfg_types.ValueInput = switch (source) {
                .copy_of => |owner| .{ .local = owner },
                .field_copy_of => |field| .{ .field = .{ .parent = field.parent, .name = field.name } },
                else => unreachable,
            };
            try self.appendStmt(cur.*, .{
                .kind = .{ .array_value = .{
                    .target = local,
                    .source = .unknown,
                    .selected_inputs = .{ input, null, null, null, null, null, null, null },
                } },
                .pos = self.posOf(init),
                .end_pos = self.endPosOf(init),
            });
        };
        try self.emitSliceHeader(cur.*, local, init_opt orelse decl_node, header_source, null, null);
        if (selected_array == null) {
            if (init_opt) |init| try self.emitArrayValue(cur.*, local, init);
        }
        if (init_opt) |init| try self.emitSuccessfulOutPrefix(cur.*, local, init);
        if (checked_difference) |difference| {
            try self.emitScaledIndex(cur.*, local, difference, decl_node);
            if (self.immutable_locals.contains(local) and self.locals.items[@intFromEnum(local)].is_unsigned)
                try self.checked_differences.put(self.gpa, local, difference);
        }

        // Struct-literal RHS: unpack so aliased fields buried in the
        // literal get their own field_assign keyed by name.  Symmetric
        // with lowerAssign — `var c: T = .{ .data = buf }` registers
        // `(c, "data") → buf's origin` so a later `c.data` read sees
        // buf's freed state. The unpackers recognize only their own shapes,
        // so lowered blocks do not get walked again.
        if (init_opt) |init| {
            const complete = try self.unpackStructInitFields(cur.*, local, null, init, self.posOf(decl_node), self.endPosOf(decl_node), value_type.container);
            self.block_stmts.items[@intFromEnum(cur.*)].items[decl_index].kind.decl.value_defined =
                init_defined and complete;
            // Constructor-call result with heap fields: when init is
            // `T.constructor(...)` and that fn's body returned
            // `.{ .X = <heap_alloc> }`, emit a synthetic
            // `field_assign(local, X, .heap_alloc(fresh))` so
            // downstream field-use machinery sees the right state
            // (e.g. `var u = toUtf8(a); use(u.bytes);` tracks
            // u.bytes's heap allocation).
            try self.emitConstructorResultHeapFields(cur.*, local, init, self.posOf(decl_node), self.endPosOf(decl_node));
        }

        if (init_opt) |init| try self.emitBooleanOutResult(cur, local, init);
    }

    /// Translate a canonical result dependency into existing local/field
    /// storage keys. A pointer header never proves its pointee initialized.
    fn arrayCallSource(self: *Builder, node: Ast.Node.Index) ?ExprKind {
        return self.arrayCallSourceFor(node, false);
    }

    fn recordDiagnosticStructLayout(self: *Builder, local: LocalId, actual: ?zls_resolver_mod.TypeResolver.ActualType.Data.Container) LoweringError!void {
        const container = actual orelse return;
        const scope = container.scope_handle;
        const tree = &scope.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = tree.fullContainerDecl(&buffer, scope.toNode()) orelse return;
        if (tree.tokenTag(declaration.ast.main_token) != .keyword_struct) return;
        var names: std.ArrayListUnmanaged([]const u8) = .empty;
        defer names.deinit(self.gpa);
        for (declaration.ast.members) |member| {
            const field = tree.fullContainerField(member) orelse continue;
            if (field.comptime_token != null) continue;
            if (field.ast.tuple_like) return;
            const raw = tree.tokenSlice(field.ast.main_token);
            const name = if (std.mem.startsWith(u8, raw, "@\""))
                self.fieldLiteralNameInTree(tree, field.ast.main_token, false) orelse return
            else raw;
            try names.append(self.gpa, name);
        }
        const fields = try names.toOwnedSlice(self.gpa);
        errdefer self.gpa.free(fields);
        try self.owned_field_layouts.append(self.gpa, fields);
        self.locals.items[@intFromEnum(local)].runtime_fields = fields;
    }

    /// A direct local tail return names the actual post-call storage even
    /// without a semantic frame. It is not a returned-value certificate.
    fn directDiagnosticReturnSource(self: *Builder, call_node: Ast.Node.Index, selected: []const []const u8) ?ExprKind {
        var operands_buffer: [1]Ast.Node.Index = undefined;
        const operands = self.tree.fullCall(&operands_buffer, call_node) orelse return null;
        // Instance receiver offsets require the canonical semantic boundary.
        if (self.tree.nodeTag(operands.ast.fn_expr) != .identifier) return null;
        const callee = self.calleeDeclOfCall(call_node) orelse callee: {
            const name = self.tree.tokenSlice(self.tree.nodeMainToken(operands.ast.fn_expr));
            if (self.name_to_local.contains(name)) return null;
            var found: ?Ast.Node.Index = null;
            for (self.tree.rootDecls()) |declaration| {
                if (self.tree.nodeTag(declaration) != .fn_decl) continue;
                var proto_buffer: [1]Ast.Node.Index = undefined;
                const proto = tokens.fnProto(self.tree, &proto_buffer, declaration) orelse continue;
                if (!std.mem.eql(u8, self.tree.tokenSlice(proto.name_token orelse continue), name)) continue;
                if (found != null) return null;
                found = declaration;
            }
            break :callee CalleeDecl{ .tree = self.tree, .fn_decl = found orelse return null, .module = if (self.cache) |cache| cache.module_id else @enumFromInt(0) };
        };
        if (callee.tree != self.tree) return null;
        const tree = self.tree;
        const body = tokens.bodyOf(tree, callee.fn_decl) orelse return null;
        var body_buffer: [2]Ast.Node.Index = undefined;
        const statements = blockStmts(tree, body, &body_buffer);
        if (statements.len == 0) return null;
        for (statements[0 .. statements.len - 1]) |statement| {
            if (tree.nodeTag(statement) != .assign) return null;
            const lhs = initShapeNode(self, tree.nodeData(statement).node_and_node[0]);
            // A rebound formal no longer names the caller's original storage.
            if (tree.nodeTag(lhs) != .field_access and tree.nodeTag(lhs) != .deref) return null;
            const rhs = tree.nodeData(statement).node_and_node[1];
            var token = tree.firstToken(rhs);
            const last = tree.lastToken(rhs);
            while (token <= last) : (token += 1) {
                switch (tree.tokenTag(token)) {
                    .l_paren, .keyword_return, .keyword_break, .keyword_continue, .keyword_try => return null,
                    else => {},
                }
            }
        }
        const returned = statements[statements.len - 1];
        if (tree.nodeTag(returned) != .@"return") return null;
        var source = initShapeNode(self, tree.nodeData(returned).opt_node.unwrap() orelse return null);
        var fields: [64][]const u8 = undefined;
        var count: usize = 0;
        var dereferenced = false;
        while (true) {
            switch (tree.nodeTag(source)) {
                .field_access => {
                    if (count == fields.len) return null;
                    const base, const token = tree.nodeData(source).node_and_token;
                    const raw = tree.tokenSlice(token);
                    fields[count] = if (std.mem.startsWith(u8, raw, "@\""))
                        self.fieldLiteralName(token, false) orelse return null
                    else raw;
                    count += 1;
                    source = initShapeNode(self, base);
                },
                .deref => { dereferenced = true; source = initShapeNode(self, tree.nodeData(source).node); },
                else => break,
            }
        }
        if (tree.nodeTag(source) != .identifier) return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, callee.fn_decl) orelse return null;
        const parameter = file_cache.paramIndexFor(tree, proto, tree.tokenSlice(tree.nodeMainToken(source))) orelse return null;
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, call_node) orelse return null;
        if (parameter >= call.ast.params.len) return null;
        var actual = initShapeNode(self, call.ast.params[parameter]);
        if (tree.nodeTag(actual) == .address_of) {
            if (count == 0 and !dereferenced) return null;
            actual = initShapeNode(self, tree.nodeData(actual).node);
        }
        const origin = self.classifySourceProjection(actual, 0) orelse return null;
        const parent = if (origin == .copy_of) origin.copy_of else origin.field_copy_of.parent;
        var path: ?[]const u8 = if (origin == .field_copy_of) origin.field_copy_of.name else null;
        while (count != 0) {
            count -= 1;
            path = self.allocDottedPath(path, fields[count]) catch |err| { self.noteResolutionError(err); return null; };
        }
        for (selected) |field| {
            path = self.allocDottedPath(path, field) catch |err| { self.noteResolutionError(err); return null; };
        }
        return if (path) |field| .{ .field_copy_of = .{ .parent = parent, .name = field } } else .{ .copy_of = parent };
    }

    fn arrayCallSourceFor(self: *Builder, node: Ast.Node.Index, diagnostic: bool) ?ExprKind {
        var selected: [64][]const u8 = undefined;
        var selected_count: usize = 0;
        var call_node = node;
        while (self.tree.nodeTag(call_node) == .field_access) {
            if (selected_count == selected.len) return null;
            const base, const field = self.tree.nodeData(call_node).node_and_token;
            selected[selected_count] = self.tree.tokenSlice(field);
            selected_count += 1;
            call_node = base;
        }
        std.mem.reverse([]const u8, selected[0..selected_count]);
        var buffer: [2]Ast.Node.Index = undefined;
        const call = zls_resolver_mod.TypeResolver.CallOperands.full(self.tree, &buffer, call_node) orelse return null;
        if (diagnostic) if (self.directDiagnosticReturnSource(call_node, selected[0..selected_count])) |source| return source;
        const cache = self.cache orelse
            return if (diagnostic) self.directDiagnosticReturnSource(call_node, selected[0..selected_count]) else null;
        // The cache's resolver answers the same call even when this lowering
        // was started without its own.
        const resolver = self.zls orelse cache.zls orelse
            return if (diagnostic) self.directDiagnosticReturnSource(call_node, selected[0..selected_count]) else null;
        var selected_node = node;
        while (self.tree.nodeTag(selected_node) == .field_access) {
            const base = self.tree.nodeData(selected_node).node_and_token[0];
            const pointer = resolver.resolvedTypeIsPointer(base) catch |err| {
                self.noteResolutionError(err);
                return null;
            };
            if (pointer != false) return null;
            selected_node = base;
        }
        const frame = self.integerResolutionFrame() orelse return null;
        if (diagnostic and selected_count == 0) {
            const actual = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(call_node)) orelse return null;
            const normalized = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, resolver.normalizedType(actual)) orelse return null;
            switch (resolver.typeTag(normalized) orelse return null) {
                .array, .vector, .@"struct", .@"union" => {},
                // Scalar/header results have no aggregate storage projection
                // to replay. Their negative callee verdict is queried separately.
                else => return null,
            }
        }
        const result = self.queryOrUnknown(file_cache.FileCache.ArrayReturnSource, if (diagnostic)
            cache.arrayDiagnosticReturnSourceAt(call.queryToken(self.tree, call_node), frame, selected[0..selected_count])
        else
            cache.arrayReturnSourceAt(call.queryToken(self.tree, call_node), frame, selected[0..selected_count])) orelse return null;
        var actual = result.argument;
        var addressed = false;
        if (self.tree.nodeTag(actual) == .address_of) {
            addressed = true;
            actual = self.tree.nodeData(actual).node;
        }
        // Method coercion can address a by-value receiver without an `&` node.
        // Authenticate that view against the reached formal and actual argument.
        if (!addressed and result.projection_count != 0 and result.projections[0] == .deref) {
            const canonical = self.queryOrUnknown(file_cache.FileCache.ActualCallSummary, cache.actualCallSummaryAt(call.queryToken(self.tree, call_node), frame)) orelse return null;
            if (canonical.argument_offset == 1) {
                var argument_buffer: [2]Ast.Node.Index = undefined;
                const arguments = self.queryOrUnknown(zls_resolver_mod.TypeResolver.CallArguments, frame.callArgumentsOf(&argument_buffer, call_node)) orelse return null;
                const parameters = canonical.callee.reference.actual_type.data.function.parameters;
                if (arguments.receiver == actual and parameters.len != 0) {
                    const formal = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, resolver.normalizedType(parameters[0].type)) orelse return null;
                    addressed = resolver.pointerSize(formal) == .one and
                        self.queryOrUnknown(bool, resolver.resolvedTypeIsPointer(actual)) == false;
                }
            }
        }
        var source = self.classifySourceProjection(actual, 0) orelse return null;
        const parent = switch (source) {
            .copy_of => |local| local,
            .field_copy_of => |field| field.parent,
            else => return null,
        };
        for (result.projections[0..result.projection_count]) |projection| {
            switch (projection) {
                .deref => {
                    if (!addressed) return null;
                    addressed = false;
                },
                .field => |field| {
                    if (!addressed and self.locals.items[@intFromEnum(parent)].is_pointer) return null;
                    const prefix: ?[]const u8 = if (source == .field_copy_of) source.field_copy_of.name else null;
                    const path = self.allocDottedPath(prefix, field) catch |err| {
                        self.noteResolutionError(err);
                        return null;
                    };
                    source = .{ .field_copy_of = .{ .parent = parent, .name = path } };
                    addressed = false;
                },
                .index => return null,
            }
        }
        return source;
    }

    /// A returned payload requires a body-definedness certificate. Actual
    /// storage dependencies still have to be covered in the caller; initialized
    /// argument headers alone never certify bytes copied by the callee.
    fn callResultInputs(self: *Builder, node: Ast.Node.Index, inputs: *[8]?LocalId) bool {
        const tree = self.tree;
        const resolver = self.zls orelse return false;
        var call_node = node;
        while (true) {
            switch (tree.nodeTag(call_node)) {
                .grouped_expression => call_node = tree.nodeData(call_node).node_and_token[0],
                .field_access => {
                    const base = tree.nodeData(call_node).node_and_token[0];
                    const pointer = resolver.resolvedTypeIsPointer(base) catch |err| {
                        self.noteResolutionError(err);
                        return false;
                    };
                    if (pointer != false) return false;
                    call_node = base;
                },
                else => break,
            }
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const call = zls_resolver_mod.TypeResolver.CallOperands.full(tree, &buffer, call_node) orelse return false;
        const cache = self.cache orelse return false;
        const frame = self.integerResolutionFrame() orelse return false;
        if (!(cache.callResultDefinedAt(call.queryToken(tree, call_node), frame) catch |err| {
            self.noteResolutionError(err);
            return false;
        })) return false;
        var count: usize = 0;
        var token = tree.firstToken(call_node);
        const last = tree.lastToken(call_node);
        while (token <= last) : (token += 1) {
            if (tree.tokenTag(token) != .identifier) continue;
            if (token > 0 and tree.tokenTag(token - 1) == .period) continue;
            const local = self.name_to_local.get(tree.tokenSlice(token)) orelse continue;
            var present = false;
            for (inputs[0..count]) |entry| {
                if (entry.? == local) present = true;
            }
            if (present) continue;
            if (count == inputs.len) return false;
            inputs[count] = local;
            count += 1;
        }
        return true;
    }

    fn classifySourceProjection(self: *Builder, node: Ast.Node.Index, depth: usize) ?ExprKind {
        if (depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, @intCast(depth), node);
            return null;
        }
        switch (self.tree.nodeTag(node)) {
            .identifier => {
                const local = self.name_to_local.get(self.tree.tokenSlice(self.tree.nodeMainToken(node))) orelse return null;
                return .{ .copy_of = local };
            },
            .grouped_expression => return self.classifySourceProjection(self.tree.nodeData(node).node_and_token[0], depth + 1),
            .field_access => {
                const base, const field = self.tree.nodeData(node).node_and_token;
                const resolver = self.zls orelse return null;
                const pointer = resolver.resolvedTypeIsPointer(base) catch |err| {
                    self.noteResolutionError(err);
                    return null;
                };
                if (pointer != false) return null;
                const source = self.classifySourceProjection(base, depth + 1) orelse return null;
                const parent = if (source == .copy_of) source.copy_of else source.field_copy_of.parent;
                if (self.locals.items[@intFromEnum(parent)].is_pointer) return null;
                const path = self.allocDottedPath(if (source == .field_copy_of) source.field_copy_of.name else null, self.tree.tokenSlice(field)) catch |err| {
                    self.noteResolutionError(err);
                    return null;
                };
                return .{ .field_copy_of = .{ .parent = parent, .name = path } };
            },
            else => return null,
        }
    }

    /// A bitcast preserves lifetime origin, not one-to-one array slot coverage.
    fn arrayCopyIsElementwise(self: *Builder, node: Ast.Node.Index) bool {
        var current = node;
        for (0..max_classify_depth) |_| {
            if (self.tree.nodeTag(current) == .grouped_expression) {
                current = self.tree.nodeData(current).node_and_token[0];
                continue;
            }
            var buffer: [2]Ast.Node.Index = undefined;
            const args = self.tree.builtinCallParams(&buffer, current) orelse return true;
            const name = self.tree.tokenSlice(self.tree.nodeMainToken(current));
            if (std.mem.eql(u8, name, "@bitCast")) return false;
            if (!std.mem.eql(u8, name, "@as") or args.len != 2) return true;
            current = args[1];
        }
        self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, max_classify_depth, node);
        return false;
    }

    /// Resolve the value itself: pointer headers never stand for their payload.
    fn fixedArrayPayloadType(self: *Builder, node: Ast.Node.Index) bool {
        const resolver = self.zls orelse return false;
        const ty = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, resolver.resolutionFrame().typeOfNode(node)) orelse return false;
        if (resolver.typeTag(ty) != .array) return false;
        const sentinel = switch (ty.data) {
            .array => |array| array.sentinel,
            .ip_index => switch (resolver.ctx.ip.indexToKey(ty.ipIndex() orelse return false)) {
                .array_type => |array| array.sentinel,
                else => return false,
            },
            else => return false,
        };
        // Logical element coverage excludes a sentinel's extra storage.
        if (sentinel != .none) return false;
        if (self.queryOrUnknown(u64, resolver.fixedArrayLen(node)) == null) return false;
        const child = resolver.childType(ty) orelse return false;
        const index = child.ipIndex() orelse return false;
        // These scalar representations contain no padding bytes. Full
        // element coverage of an aggregate with padding is not a byte proof.
        const bits: u16 = switch (resolver.typeTag(child) orelse return false) {
            .int => resolver.ctx.ip.intInfo(index, @import("builtin").target).bits,
            .float => resolver.ctx.ip.floatBits(index, @import("builtin").target),
            else => return false,
        };
        return bits == 8 or bits == 16 or bits == 32 or bits == 64 or bits == 128;
    }

    /// A whole-payload certificate still reads the source's live storage
    /// facts in transfer; its resolved shape alone grants no initialization.
    fn emitArrayPayloadCast(self: *Builder, cur: BlockId, local: LocalId, node: Ast.Node.Index) LoweringError!bool {
        const tree = self.tree;
        var payload = node;
        var bit_cast = false;
        var depth: usize = 0;
        while (depth < max_classify_depth) : (depth += 1) {
            switch (tree.nodeTag(payload)) {
                .grouped_expression => payload = tree.nodeData(payload).node_and_token[0],
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    var buffer: [2]Ast.Node.Index = undefined;
                    const args = tree.builtinCallParams(&buffer, payload) orelse break;
                    const name = tree.tokenSlice(tree.nodeMainToken(payload));
                    if (std.mem.eql(u8, name, "@as") and args.len == 2) {
                        payload = args[1];
                        continue;
                    }
                    if (!std.mem.eql(u8, name, "@bitCast") or args.len != 1) break;
                    bit_cast = true;
                    payload = args[0];
                },
                else => break,
            }
        }
        if (depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, @intCast(depth), node);
            return bit_cast;
        }
        const resolver = self.zls orelse return bit_cast;
        const ty = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, resolver.resolutionFrame().typeOfNode(payload)) orelse return bit_cast;
        if (bit_cast) {
            if (!self.fixedArrayPayloadType(payload)) return true;
            if (self.immutableLiteralPayload(payload)) {
                var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
                if (!self.literalPayloadSelectorInputs(payload, &selected, 0)) return true;
                try self.appendStmt(cur, .{
                    .kind = .{ .array_value = .{ .target = local, .source = .plain, .selected_inputs = selected } },
                    .pos = self.posOf(node),
                    .end_pos = self.endPosOf(node),
                });
                return true;
            }
        } else if (resolver.typeTag(ty) != .vector) {
            return false;
        }
        const source = self.classifyExpr(payload);
        switch (source) {
            .copy_of => |owner| {
                if (self.locals.items[@intFromEnum(owner)].is_pointer) return true;
                self.locals.items[@intFromEnum(owner)].tracks_array_payload = true;
            },
            .field_copy_of => |field| {
                const info = &self.locals.items[@intFromEnum(field.parent)];
                // Only the caller's pointer field starts with a storage
                // contract. A frame-local pointer's header proves no bytes.
                if (info.is_pointer and self.paramTypeSpanOfLocal(field.parent) == null) return true;
                info.tracks_array_payload = true;
            },
            else => return bit_cast,
        }
        try self.appendStmt(cur, .{
            .kind = .{ .array_value = .{ .target = local, .source = source, .whole_payload = true } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
        return true;
    }

    /// Record the actual selected value, never re-test its earlier selector.
    fn emitArrayValue(self: *Builder, cur: BlockId, local: LocalId, node: Ast.Node.Index) LoweringError!void {
        try self.emitArrayInitializerWrites(cur, local, node);
        if (!self.locals.items[@intFromEnum(local)].is_array) return;
        if (self.tree.nodeTag(node) == .field_access and self.returnedFieldHasUndefinedOrigin(node)) {
            try self.appendStmt(cur, .{
                .kind = .{ .array_value = .{ .target = local, .source = .undef } },
                .pos = self.posOf(node),
                .end_pos = self.endPosOf(node),
            });
            return;
        }
        if (self.immutableLiteralPayload(node)) {
            var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
            if (!self.literalPayloadSelectorInputs(node, &selected, 0)) return;
            try self.appendStmt(cur, .{
                .kind = .{ .array_value = .{ .target = local, .source = .plain, .selected_inputs = selected } },
                .pos = self.posOf(node),
                .end_pos = self.endPosOf(node),
            });
            return;
        }
        if (try self.emitArrayPayloadCast(cur, local, node)) return;
        if (self.tree.nodeTag(node) == .array_access) {
            if (!self.fixedArrayPayloadType(node)) return;
            var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
            if (!self.selectedValueInputs(node, &selected, false) or selected[0] == null) return;
            try self.appendStmt(cur, .{
                .kind = .{ .array_value = .{
                    .target = local,
                    .source = .plain,
                    .selected_inputs = selected,
                } },
                .pos = self.posOf(node),
                .end_pos = self.endPosOf(node),
            });
            return;
        }
        const call_source = self.arrayCallSource(node);
        const source = call_source orelse self.classifyExpr(node);
        if (call_source == null and source != .copy_of and source != .field_copy_of) {
            var inputs: [8]?LocalId = .{null} ** 8;
            if (self.callResultInputs(node, &inputs)) {
                try self.appendStmt(cur, .{
                    .kind = .{ .array_value = .{ .target = local, .source = .plain, .inputs = inputs } },
                    .pos = self.posOf(node),
                    .end_pos = self.endPosOf(node),
                });
            }
            return;
        }
        if (source != .copy_of and source != .field_copy_of) return;
        switch (source) {
            .copy_of => |owner| self.locals.items[@intFromEnum(owner)].tracks_array_payload = true,
            .field_copy_of => |field| self.locals.items[@intFromEnum(field.parent)].tracks_array_payload = true,
            else => unreachable,
        }
        // The callee's single return reads this actual payload even when
        // the caller passed its address rather than its value.
        if (call_source != null and source == .copy_of and
            self.locals.items[@intFromEnum(source.copy_of)].is_array)
        {
            try self.appendStmt(cur, .{
                .kind = .{ .use = .{ .local = source.copy_of } },
                .pos = self.posOf(node),
                .end_pos = self.endPosOf(node),
            });
        }
        try self.appendStmt(cur, .{
            .kind = .{ .array_value = .{ .target = local, .source = source } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    fn literalArrayExtent(self: *Builder, node: Ast.Node.Index) ?u64 {
        const shape = initShapeNode(self, node);
        if (self.tree.nodeTag(shape) == .array_mult) {
            const pattern, const repeat = self.tree.nodeData(shape).node_and_node;
            var buffer: [2]Ast.Node.Index = undefined;
            const literal = self.tree.fullArrayInit(&buffer, pattern) orelse return null;
            const count = self.integerValue(repeat) orelse return null;
            return std.math.mul(u64, @intCast(literal.ast.elements.len), count) catch null;
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = self.tree.fullArrayInit(&buffer, shape) orelse return null;
        return @intCast(literal.ast.elements.len);
    }

    /// A literal initializes each selected element, not an unknown whole
    /// array. Keep undefined elements as holes in the same region model used
    /// for subsequent indexed stores.
    fn emitArrayInitializerWrites(self: *Builder, cur: BlockId, local: LocalId, init_node: Ast.Node.Index) !void {
        if (self.tree.nodeTag(init_node) == .builtin_call_two or self.tree.nodeTag(init_node) == .builtin_call_two_comma) {
            if (std.mem.eql(u8, self.tree.tokenSlice(self.tree.nodeMainToken(init_node)), "@splat")) {
                const value = self.tree.nodeData(init_node).opt_node_and_opt_node[0].unwrap() orelse return;
                var write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
                    .array = local,
                    .index = .{ .constant = 0 },
                    .rhs_kind = self.classifyExpr(value),
                    .all_elements = true,
                };
                write.defined = self.selectedValueInputs(value, &write.selected_inputs, false);
                try self.appendStmt(cur, .{ .kind = .{ .indexed_write = write }, .pos = self.posOf(value), .end_pos = self.endPosOf(value) });
                return;
            }
        }
        if (self.tree.nodeTag(init_node) == .array_mult) {
            // `.{v} ** N` / `[_]T{v} ** N` stores `v` in every slot. A longer
            // pattern would need per-slot coverage, so only one element counts.
            var pattern_buffer: [2]Ast.Node.Index = undefined;
            const pattern = self.tree.fullArrayInit(&pattern_buffer, self.tree.nodeData(init_node).node_and_node[0]) orelse return;
            if (pattern.ast.elements.len != 1) return;
            const value = pattern.ast.elements[0];
            var write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
                .array = local,
                .index = .{ .constant = 0 },
                .rhs_kind = self.classifyExpr(value),
                .all_elements = true,
            };
            write.defined = self.selectedValueInputs(value, &write.selected_inputs, false);
            try self.appendStmt(cur, .{ .kind = .{ .indexed_write = write }, .pos = self.posOf(value), .end_pos = self.endPosOf(value) });
            return;
        }
        var buf: [2]Ast.Node.Index = undefined;
        const init = self.tree.fullArrayInit(&buf, init_node) orelse return;
        const info = &self.locals.items[@intFromEnum(local)];
        info.is_array = true;
        if (info.array_extent == null) info.array_extent = @intCast(init.ast.elements.len);
        for (init.ast.elements, 0..) |element, index| {
            var write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
                .array = local,
                .index = .{ .constant = @intCast(index) },
                .rhs_kind = self.classifyExpr(element),
            };
            write.defined = self.selectedValueInputs(element, &write.selected_inputs, false);
            try self.appendStmt(cur, .{
                .kind = .{ .indexed_write = write },
                .pos = self.posOf(element),
                .end_pos = self.endPosOf(element),
            });
        }
    }

    /// Infer pointer-ness for an indexed collection element from its
    /// declared element type. This covers receiver fields such as
    /// `self.handles.items[index]` and direct slice parameters.
    fn initArrayElementIsPointer(self: *Builder, init: Ast.Node.Index) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const first = tree.firstToken(init);
        const last = tree.lastToken(init);

        var items_tok: ?Ast.TokenIndex = null;
        var t = first;
        while (t + 2 <= last) : (t += 1) {
            if (tags[t] != .period or tags[t + 1] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t + 1), "items")) continue;
            if (tags[t + 2] != .l_bracket) continue;
            items_tok = t + 1;
            break;
        }

        if (items_tok) |items| {
            if (items < first + 2) return false;
            const field_tok = items - 2;
            if (field_tok != first + 2 or tags[first] != .identifier or
                tags[field_tok] != .identifier) return false;
            const root = tree.tokenSlice(first);
            const owner_type: ?[]const u8 = if (std.mem.eql(u8, root, "self") or
                std.mem.eql(u8, root, "this"))
                self.self_type
            else if (self.name_to_local.get(root)) |local|
                self.locals.items[@intFromEnum(local)].type_name
            else
                null;

            const type_name = owner_type orelse return false;
            const cache = self.cache orelse return false;
            const model = self.modelOrNull(cache) orelse return false;
            const owner = model.findType(type_name) orelse return false;
            const field = owner.findField(tree.tokenSlice(field_tok)) orelse return false;
            return typeRangeHasPointerElement(tree, field.type_first, field.type_last);
        }

        if (first + 1 > last or tags[first] != .identifier or
            tags[first + 1] != .l_bracket) return false;
        const root = tree.tokenSlice(first);
        const proto = self.fn_proto orelse return false;
        var params = proto.iterate(tree);
        while (params.next()) |param| {
            const name_tok = param.name_token orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(name_tok), root)) continue;
            const type_node = param.type_expr orelse return false;
            return typeRangeHasPointerElement(
                tree,
                tree.firstToken(type_node),
                tree.lastToken(type_node),
            );
        }
        return false;
    }

    /// Optional presence is a separate fork from an error-valued payload.
    fn emitOrelseFork(self: *Builder, orelse_node: Ast.Node.Index, cur: *BlockId, result_frame: ?ValueOutcomeFrame) LoweringError!void {
        const data = self.tree.nodeData(orelse_node).node_and_node;
        const orelse_block = try self.newBlock();
        const present_block = try self.newBlock();
        const merge = try self.newBlock();
        try self.addEdge(cur.*, orelse_block);
        try self.addEdge(cur.*, present_block);
        var present_cur = present_block;
        if (result_frame) |frame| {
            try self.recordValueOutcome(frame, orelse_node, &present_cur, self.valueIsError(data[0], true));
            if (frame.array_local) |local| try self.emitArrayValue(present_cur, local, data[0]);
            if (frame.scalar_local) |local| try self.emitScalarValue(present_cur, local, data[0], frame.scalar_guard);
        }
        try self.addEdge(present_cur, merge);
        var fallback_cur = orelse_block;
        try self.lowerValueExpr(data[1], &fallback_cur, result_frame);
        try self.addEdge(fallback_cur, merge);
        cur.* = merge;
    }

    /// `LHS = RHS;` — when LHS is a known simple-identifier local, emit
    /// a real `.assign` so the analyzer can update origin tracking.
    /// Otherwise (field access, deref, destructuring) fall back to a
    /// lowering_gap so locals collapse conservatively to .plain.
    ///
    /// Either way, if the RHS has a top-level `try`, `catch` or
    /// `orelse`, lower it the way the matching var-decl would — those
    /// error / null-path CFG edges are independent of whether we
    /// successfully tracked the target.
    fn lowerAssign(self: *Builder, assign_node: Ast.Node.Index, cur: *BlockId) !void {
        const tree = self.tree;
        const tag = tree.nodeTag(assign_node);

        // Destructuring (`a, b = pair` / `const a, const b = pair()`).
        // Multi-target — we can't classify per-slot, so each target
        // gets .unknown.  But registering the locals (in the var-decl
        // form) and emitting per-target .assign / .decl beats one big
        // gap that collapsed everything to .plain.
        if (tag == .assign_destructure) {
            try self.lowerAssignDestructure(assign_node, cur);
            return;
        }

        const data = tree.nodeData(assign_node).node_and_node;
        const lhs = data[0];
        const rhs = data[1];

        // Resolve target: only simple identifier LHS for now.
        const target_local: ?LocalId = if (tree.nodeTag(lhs) == .identifier)
            self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(lhs)))
        else
            null;
        const header_source = if (target_local != null and self.locals.items[@intFromEnum(target_local.?)].is_slice)
            self.sliceHeaderSource(rhs)
        else
            null;
        var header_rhs_kind: ?ExprKind = null;
        var header_snapshot: ?LocalId = null;
        var pointer_snapshot: ?LocalId = null;
        if (target_local != null and header_source == target_local and
            tree.fullSlice(initShapeNode(self, rhs)) != null)
        {
            const kind = self.classifyExpr(rhs);
            header_rhs_kind = kind;
            if (kind != .copy_of or kind.copy_of != target_local.?) {
                // Only erased self-sources need a pre-overwrite certificate.
                // Retain initializedness, not a numerical length.
                const value = try self.newScalarValue(rhs, cur.*);
                var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
                inputs[0] = .{ .field = .{ .parent = target_local.?, .name = "len" } };
                try self.appendStmt(cur.*, .{
                    .kind = .{ .assign = .{
                        .target = value,
                        .rhs_kind = .unknown,
                        .value_defined = true,
                        .value_inputs = inputs,
                    } },
                    .pos = self.posOf(rhs),
                    .end_pos = self.endPosOf(rhs),
                });
                header_snapshot = value;
                const pointer = try self.newScalarValue(rhs, cur.*);
                try self.appendStmt(cur.*, .{
                    .kind = .{ .assign = .{
                        .target = pointer,
                        .rhs_kind = .{ .field_copy_of = .{ .parent = target_local.?, .name = "ptr" } },
                        .value_defined = true,
                    } },
                    .pos = self.posOf(rhs),
                    .end_pos = self.endPosOf(rhs),
                });
                pointer_snapshot = pointer;
            }
        }
        const indexed_target = self.indexedTarget(lhs);
        if (indexed_target) |access| try self.emitUsesInExpr(access.index_node, cur.*, null);

        // Match declaration ordering: computed values lower selected paths;
        // ordinary RHS values emit their reads and direct call effects once.
        var selected_scalar: ?LocalId = null;
        const rhs_was_lowered = if (target_local != null and
            self.locals.items[@intFromEnum(target_local.?)].tracks_scalar_value and
            (try self.isComputedValue(rhs)))
        lowered: {
            const selected = try self.newScalarValue(rhs, cur.*);
            try self.lowerValueExpr(rhs, cur, .{ .scalar_local = selected });
            selected_scalar = selected;
            break :lowered true;
        } else try self.lowerComputedValue(rhs, cur);
        if (!rhs_was_lowered) {
            try self.emitUsesInExpr(rhs, cur.*, null);
            try self.applyTopLevelCallEffects(rhs, cur, false);
        }

        if (target_local) |t| {
            // Evaluate literal inputs before rebinding the old array value.
            var rhs_kind = header_rhs_kind orelse self.classifyExpr(rhs);
            var literal_buf: [2]Ast.Node.Index = undefined;
            if (tree.fullArrayInit(&literal_buf, rhs) != null) {
                var info = self.locals.items[@intFromEnum(t)];
                info.name = "";
                info.decl_pos = self.posOf(rhs);
                const temporary = try self.appendLocal(info);
                try self.appendStmt(cur.*, .{
                    .kind = .{ .decl = .{ .local = temporary, .init_kind = rhs_kind } },
                    .pos = self.posOf(rhs),
                    .end_pos = self.endPosOf(rhs),
                });
                try self.emitArrayInitializerWrites(cur.*, temporary, rhs);
                rhs_kind = .{ .copy_of = temporary };
            }
            var value_inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
            const value_defined = if (selected_scalar) |selected| selected: {
                value_inputs[0] = .{ .local = selected };
                rhs_kind = .{ .copy_of = selected };
                break :selected true;
            } else if (!self.locals.items[@intFromEnum(t)].tracks_scalar_value)
                self.selectedValueInputs(rhs, &value_inputs, false)
            else
                self.selectedValueInputs(rhs, &value_inputs, true);
            const array_copy = self.arrayCopyIsElementwise(rhs);
            const store_index = self.block_stmts.items[@intFromEnum(cur.*)].items.len;
            try self.appendStmt(cur.*, .{
                .kind = .{ .assign = .{
                    .target = t,
                    .rhs_kind = rhs_kind,
                    .integer_value = self.integerValue(rhs),
                    .value_defined = value_defined,
                    .value_inputs = value_inputs,
                    .array_copy = array_copy,
                } },
                .pos = self.posOf(assign_node),
                .end_pos = self.endPosOf(assign_node),
            });
            try self.emitSliceHeader(cur.*, t, rhs, header_source, header_snapshot, pointer_snapshot);
            // Struct-literal RHS: unpack so aliased fields buried in
            // the literal get their own field_assign keyed by name.
            // `container = .{ .ptr = buf }` registers
            // `(container, "ptr") → buf's origin` so a later
            // `container.ptr` read sees buf's freed state.
            const complete = try self.unpackStructInitFields(cur.*, t, null, rhs, self.posOf(assign_node), self.endPosOf(assign_node), null);
            self.block_stmts.items[@intFromEnum(cur.*)].items[store_index].kind.assign.value_defined =
                value_defined and complete;
            if (rhs_kind != .copy_of) try self.emitArrayInitializerWrites(cur.*, t, rhs);
            if (!array_copy and self.locals.items[@intFromEnum(t)].is_array)
                _ = try self.emitArrayPayloadCast(cur.*, t, rhs);
            try self.emitBooleanOutResult(cur, t, rhs);
        } else if (indexed_target) |access| {
            var write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
                .array = access.array,
                // A computed RHS can change a dynamic LHS index after its
                // evaluation. Without a snapshot, do not credit that new slot.
                .index = if (rhs_was_lowered and self.indexTerm(access.index_node) == .local)
                    .unknown
                else
                    self.indexTerm(access.index_node),
                .rhs_kind = self.classifyExpr(rhs),
                .name = if (self.fieldLhsFor(lhs)) |field| field.name else null,
                .field_array = access.field_array,
            };
            write.defined = self.selectedValueInputs(rhs, &write.selected_inputs, false);
            try self.appendStmt(cur.*, .{
                .kind = .{ .indexed_write = write },
                .pos = self.posOf(lhs),
                .end_pos = self.endPosOf(lhs),
            });
            try self.appendSliceStoreEffect(cur.*, write, self.posOf(lhs), self.endPosOf(lhs));
        } else if (self.indexedMemberTarget(lhs)) |access| {
            try self.emitIndexedMemberWrite(cur.*, lhs, rhs, access);
        } else if (self.fieldLhsFor(lhs)) |fref| {
            // `obj.field = RHS` where obj is a known local — emit
            // .field_assign so the field's origin is tracked
            // separately.  Catches store-then-free-then-use of a
            // struct field.
            var inputs: [8]?LocalId = .{null} ** 8;
            const defined = self.valueInputs(rhs, &inputs);
            var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
            if (!defined) _ = self.selectedValueInputs(rhs, &selected, false);
            const store_index = self.block_stmts.items[@intFromEnum(cur.*)].items.len;
            try self.appendStmt(cur.*, .{
                .kind = .{ .field_assign = .{
                    .parent = fref.parent,
                    .name = fref.name,
                    .rhs_kind = self.classifyExpr(rhs),
                    .defined = defined,
                    .inputs = inputs,
                    .selected_inputs = selected,
                } },
                .pos = self.posOf(assign_node),
                .end_pos = self.endPosOf(assign_node),
            });
            // Nested struct-literal unpack for the field LHS, e.g.
            // `install.ca = .{ .str = buf }` → field_assign on
            // `(install, "ca.str")`.  oven-sh/bun#25563 shape.
            const complete = try self.unpackStructInitFields(cur.*, fref.parent, fref.name, rhs, self.posOf(assign_node), self.endPosOf(assign_node), null);
            self.block_stmts.items[@intFromEnum(cur.*)].items[store_index].kind.field_assign.defined =
                defined and complete;
            try self.emitCopiedLiteralDescriptor(cur.*, fref.parent, fref.name, rhs);
            // oven-sh/bun#29422: `obj.field = .{ .tag = try ... }` leaves
            // the union with the new tag and garbage payload on the
            // error path.  Fire only on field assignments through a
            // pointer-typed parent — pure-local field writes don't
            // outlive the frame and aren't observable.
            if (self.locals.items[@intFromEnum(fref.parent)].is_pointer) {
                try self.maybePartialUnionWrite(cur.*, rhs, fref.parent, fref.name, self.posOf(assign_node), self.endPosOf(assign_node));
            }
            // Escape-via-out-param: `out.field = X` where `out` is a
            // pointer-typed parameter writes through to caller
            // storage.  If X's origin is a function-local arena /
            // stack reference, that lifetime now reaches the caller
            // — fire the same escape diagnostics as a borrowed-shape
            // return.
            //
            // Save-restore-via-defer skip: when the fn body has a
            // `defer <recv>.<path> = ...` that targets the SAME
            // field, the temporary stack borrow is bounded by the
            // defer — by the time the fn returns the prior value
            // has been restored.  Don't emit the escape stmt for
            // that case.
            if (self.locals.items[@intFromEnum(fref.parent)].is_pointer) {
                const recv_name = self.locals.items[@intFromEnum(fref.parent)].name;
                const assign_tok = tree.firstToken(assign_node);
                if (!self.fieldPathRestoredByDefer(recv_name, fref.name) and
                    !self.is_noreturn_fn and
                    !self.installIsScopeBoundedByCall(recv_name, fref.name, assign_tok) and
                    !self.installIsConsumedByCrossFnRead(recv_name, fref.name, assign_tok))
                {
                    try self.appendStmt(cur.*, .{
                        .kind = .{ .out_param_write = .{
                            .out = fref.parent,
                            .value_kind = self.classifyExpr(rhs),
                        } },
                        .pos = self.posOf(assign_node),
                        .end_pos = self.endPosOf(assign_node),
                    });
                }
            }
        } else if (self.derefOfPointerLocal(lhs)) |out_local| {
            // `<local>.* = RHS` — when local is pointer-typed, this
            // writes through the pointer to caller-visible storage.
            // Mirror the field-of-pointer case above: emit a
            // pointer_write to clear .undef on the pointer and an
            // out_param_write for the escape check.
            if (self.locals.items[@intFromEnum(out_local)].array_element_owner) |array| {
                // This capture denotes one unplaced element. A defined whole
                // store can retain complete coverage; it cannot fill a hole.
                var write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
                    .array = array,
                    .index = .unknown,
                    .rhs_kind = self.classifyExpr(rhs),
                };
                write.defined = tree.nodeTag(assign_node) == .assign and
                    self.selectedValueInputs(rhs, &write.selected_inputs, false);
                for (write.selected_inputs) |entry| {
                    const input = entry orelse continue;
                    switch (input) {
                        .local => |source| self.locals.items[@intFromEnum(source)].tracks_array_payload = true,
                        .field => |field| self.locals.items[@intFromEnum(field.parent)].tracks_array_payload = true,
                        .indexed => {},
                    }
                }
                try self.appendStmt(cur.*, .{
                    .kind = .{ .indexed_write = write },
                    .pos = self.posOf(assign_node),
                    .end_pos = self.endPosOf(assign_node),
                });
            } else {
                try self.appendStmt(cur.*, .{
                    .kind = .{ .pointer_write = .{ .target = out_local } },
                    .pos = self.posOf(assign_node),
                    .end_pos = self.endPosOf(assign_node),
                });
            }
            if (self.locals.items[@intFromEnum(out_local)].array_element_owner == null) {
                var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
                _ = self.selectedValueInputs(rhs, &selected, false);
                const kind = self.classifyExpr(rhs);
                const pointee = self.pointer_value_sources.get(out_local);
                if (pointee) |source| {
                    switch (source) {
                        .copy_of => |owner| try self.appendStmt(cur.*, .{
                            .kind = .{ .assign = .{ .target = owner, .rhs_kind = kind, .value_inputs = selected } },
                            .pos = self.posOf(assign_node),
                            .end_pos = self.endPosOf(assign_node),
                        }),
                        .field_copy_of => |field| try self.appendStmt(cur.*, .{
                            .kind = .{ .field_assign = .{ .parent = field.parent, .name = field.name, .rhs_kind = kind, .selected_inputs = selected } },
                            .pos = self.posOf(assign_node),
                            .end_pos = self.endPosOf(assign_node),
                        }),
                        else => {},
                    }
                } else {
                    try self.appendStmt(cur.*, .{
                        .kind = .{ .field_assign = .{ .parent = out_local, .name = "", .rhs_kind = kind, .selected_inputs = selected } },
                        .pos = self.posOf(assign_node),
                        .end_pos = self.endPosOf(assign_node),
                    });
                }
            }
            try self.appendStmt(cur.*, .{
                .kind = .{ .out_param_write = .{
                    .out = out_local,
                    .value_kind = self.classifyExpr(rhs),
                } },
                .pos = self.posOf(assign_node),
                .end_pos = self.endPosOf(assign_node),
            });
            // oven-sh/bun#29422: `this.* = .{ .tag = try ... }` — same
            // partial-write hazard as the field case above, but
            // ONLY when the deref target is itself a tagged union
            // (not a plain 1-field struct masquerading with `.{ .x
            // = ... }` syntax — `ErrorResponse.zig` / `NoticeResponse.zig`
            // FP).  We approximate "tagged union" with a substring
            // scan of the file for `<type_name> = union(` — cheap,
            // accurate for canonical Zig idiom, and only used to
            // suppress FPs on the deref case (the field-of-pointer
            // case above has no symmetric FP class because most
            // observed field LHSs ARE unions).
            const tn = self.locals.items[@intFromEnum(out_local)].type_name;
            if (tn != null and self.typeIsTaggedUnion(tn.?)) {
                try self.maybePartialUnionWrite(cur.*, rhs, out_local, null, self.posOf(assign_node), self.endPosOf(assign_node));
            }
            // Unpack struct-literal fields so arena/heap-field origins
            // are tracked per-field.  Needed for the "object owns its
            // own arena" pattern (`ptr.* = .{ .arena = arena, ... }`) —
            // the arena field_assign marks the arena as heap-moved,
            // suppressing the spurious arena-escape on `return ptr`.
            _ = try self.unpackStructInitFields(cur.*, out_local, null, rhs, self.posOf(assign_node), self.endPosOf(assign_node), null);
        } else if (tree.nodeTag(lhs) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(lhs)), "_"))
        {
            // Discard reads and call effects were lowered with the RHS.
        } else {
            // An unsupported target can mutate only its storage root.
            // Selected indices remain reads and receive no fill credit.
            try self.emitWritesInLhs(lhs, cur.*);
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "assign-target", .may_assign_locals = false } },
                .pos = self.posOf(assign_node),
                .end_pos = self.endPosOf(assign_node),
            });
        }
    }

    /// `a, b = pair()` or `const a, const b = pair()`.  Per-variable:
    /// pure-identifier targets emit `.assign` against the resolved
    /// local; var-decl targets (`const x`) register a new local and
    /// emit `.decl`.  All rhs classifications are .unknown — we don't
    /// match tuple slots to types.  The rhs's top-level try / catch /
    /// orelse / labeled-block side-effects ARE lowered (once, before
    /// the per-target emissions), matching plain-assign semantics.
    fn lowerAssignDestructure(
        self: *Builder,
        assign_node: Ast.Node.Index,
        cur: *BlockId,
    ) !void {
        const tree = self.tree;
        const full = tree.assignDestructure(assign_node);
        const rhs = full.ast.value_expr;

        if (!try self.lowerComputedValue(rhs, cur)) {
            try self.emitUsesInExpr(rhs, cur.*, null);
            try self.applyTopLevelCallEffects(rhs, cur, false);
        }

        for (full.ast.variables) |var_node| {
            const vtag = tree.nodeTag(var_node);
            switch (vtag) {
                .identifier => {
                    const name = tree.tokenSlice(tree.nodeMainToken(var_node));
                    if (self.name_to_local.get(name)) |t| {
                        try self.appendStmt(cur.*, .{
                            .kind = .{ .assign = .{ .target = t, .rhs_kind = .unknown } },
                            .pos = self.posOf(var_node),
                            .end_pos = self.endPosOf(var_node),
                        });
                    } else {
                        try self.appendStmt(cur.*, .{
                            .kind = .{ .lowering_gap = .{ .note = "destructure-unresolved" } },
                            .pos = self.posOf(var_node),
                            .end_pos = self.endPosOf(var_node),
                        });
                    }
                },
                .simple_var_decl,
                .local_var_decl,
                .aligned_var_decl,
                .global_var_decl,
                => {
                    const vd = tree.fullVarDecl(var_node) orelse continue;
                    const name_tok = vd.ast.mut_token + 1;
                    if (tree.tokens.items(.tag)[name_tok] != .identifier) continue;
                    const name = tree.tokenSlice(name_tok);
                    const local = try self.registerLocal(name, self.posOfToken(name_tok));
                    try self.appendStmt(cur.*, .{
                        .kind = .{ .decl = .{ .local = local, .init_kind = .unknown } },
                        .pos = self.posOf(var_node),
                        .end_pos = self.endPosOf(var_node),
                    });
                },
                else => {
                    try self.appendStmt(cur.*, .{
                        .kind = .{ .lowering_gap = .{ .note = "destructure-target" } },
                        .pos = self.posOf(var_node),
                        .end_pos = self.endPosOf(var_node),
                    });
                },
            }
        }
    }

    fn lowerReturn(self: *Builder, ret_node: Ast.Node.Index, cur: *BlockId) LoweringError!void {
        try self.lowerReturnValue(ret_node, self.tree.nodeData(ret_node).opt_node.unwrap(), cur);
    }

    /// Split `return if (c) A else B;` into a fork whose arms are each
    /// lowered by [Builder.lowerReturnValue] — the same routine an
    /// unnested return uses, so an arm gets its reads, the ownership
    /// its call took, its defer flush and its `.ret` with the return's
    /// OWN span rather than a synthesised one.  Nothing is emitted
    /// through `lowerStmt` and the whole conditional is never re-walked
    /// as one expression, which is what would duplicate the reads and
    /// run both arms' effects unconditionally.
    ///
    /// Returns false when the node is not a complete `if`, leaving the
    /// caller to lower it as an ordinary value.
    fn lowerReturnIfArms(
        self: *Builder,
        ret_node: Ast.Node.Index,
        if_node: Ast.Node.Index,
        cur: *BlockId,
    ) LoweringError!bool {
        const tree = self.tree;
        const branch = tree.fullIf(if_node) orelse return false;
        // A payload makes the arm a DESTRUCTURING: `if (opt) |x|` tests
        // PRESENCE, so the condition's Boolean value is not what the
        // arms assume.  Classifying it anyway records `opt`'s own truth
        // as the arm's, which contradicts the fact its initializer
        // established and leaves the arm infeasible before its first
        // statement — a read the program performs goes unreported.
        // `lowerIf` and `lowerWhile` guard exactly this.
        const condition = if (branch.payload_token == null) self.booleanValue(branch.ast.cond_expr) else null;
        try self.lowerConditionUses(branch.ast.cond_expr, cur);
        try self.applyTopLevelCallEffects(branch.ast.cond_expr, cur, false);

        const then_blk = try self.newBlock();
        const else_blk = try self.newBlock();
        const merge = try self.newBlock();
        try self.addEdge(cur.*, then_blk);
        try self.addEdge(cur.*, else_blk);
        try self.assumeCondition(then_blk, branch.ast.cond_expr, condition, true);
        try self.assumeCondition(else_blk, branch.ast.cond_expr, condition, false);

        // ARM CURSORS, NOT BLOCK IDS.  [lowerReturnValue] takes the
        // cursor it is handed and ADVANCES it — a call in an arm forks
        // and merges, so the arm's last block is rarely the one it
        // started in — and it is that advanced cursor the edge out of
        // the arm has to leave from.  Naming the block `const` and
        // handing its address to a `*BlockId` parameter is not a cursor
        // at all: the address is of a constant, and reading the value
        // back would route every arm's edge out of the block the fork
        // made rather than the one the arm finished in.
        var then_cur = then_blk;
        var else_cur = else_blk;

        const pre_capture_len = try self.localsLen();
        if (branch.payload_token) |token| {
            try self.registerCapturesWith(token, then_blk);
            // `|value|` off a `?*S` IS a pointer, and the arm takes its
            // address; registering it without this makes `&value.field`
            // read as a borrow of the frame the capture was invented in.
            self.inferPointerCapture(token, branch.ast.cond_expr);
        }
        try self.lowerReturnValue(ret_node, branch.ast.then_expr, &then_cur);
        self.restoreLocalNames(pre_capture_len, tree.firstToken(if_node));
        try self.addEdge(then_cur, merge);

        // A conditional return with NO else arm still needs a return on
        // that path, or the merge is entered with nothing having
        // returned.  `lowerReturnValue` with a null value is exactly
        // that: `value_kind` `.plain`, no error flush, and — the part
        // that matters — `is_literal_undef` FALSE.  The implicit else
        // value of a Zig `if` expression IS `undefined`, but the
        // literal-`undefined` sentinel rule is about `return
        // undefined;` WRITTEN literally, and reporting this arm as an
        // undef leak would invent a bug the language does not have.
        //
        // The error capture is registered HERE, after the then arm's
        // names are restored, exactly where `lowerIf` registers it.
        // Registered up front it sits inside the range the restore
        // removes, so the else arm lowered a `|err|` that no longer
        // existed: `returnExprIsError` could not see an error capture,
        // chose the normal-only flush, and the errdefer's real second
        // free on the error path was never run.
        if (branch.ast.else_expr.unwrap()) |else_expr| {
            if (branch.error_token) |token| try self.registerErrorCapturesWith(token, else_blk);
            try self.lowerReturnValue(ret_node, else_expr, &else_cur);
        } else {
            try self.lowerReturnValue(ret_node, null, &else_cur);
        }
        self.restoreLocalNames(pre_capture_len, tree.firstToken(if_node));
        try self.addEdge(else_cur, merge);
        cur.* = merge;
        return true;
    }

    /// The conditional a returned value IS, with the grouping that only
    /// parenthesises it peeled off.  Null for an ordinary value.
    fn returnedConditionalNode(self: *const Builder, expr: Ast.Node.Index) ?Ast.Node.Index {
        const tree = self.tree;
        var node = expr;
        while (tree.nodeTag(node) == .grouped_expression) {
            node = tree.nodeData(node).node_and_token[0];
        }
        return switch (tree.nodeTag(node)) {
            .@"if", .if_simple => node,
            else => null,
        };
    }

    /// Lower ONE returned expression as a complete return: the reads
    /// its evaluation performs, the ownership a call in it takes, the
    /// defers that fire after it, and the `.ret` itself.
    ///
    /// Zig semantics: the return value is EVALUATED FIRST, then
    /// defers fire, then the function actually exits.  Emit .use
    /// stmts for the return value's reads BEFORE flushing defers
    /// so a `defer free(buf); return use(buf);` pattern doesn't
    /// see buf as already-freed at .use time.
    fn lowerReturnValue(
        self: *Builder,
        ret_node: Ast.Node.Index,
        value_opt: ?Ast.Node.Index,
        cur: *BlockId,
    ) LoweringError!void {
        const tree = self.tree;
        // A NESTED CONDITIONAL is the same question one level down.  An
        // arm of this one can itself be `if (c) A else B`, and then
        // exactly one of ITS arms runs: flat-walking both inner arms
        // emits the dead one's reads into the block that survives, so a
        // read the program never performs is diagnosed on it.  Only
        // re-entering [lowerReturnIfArms] builds the two assumptions
        // that separate them, so that is what this does — grouping is
        // transparent, because `(if (c) …)` is the conditional written
        // with parentheses.
        if (value_opt) |expr| {
            if (self.returnedConditionalNode(expr)) |nested| {
                if (try self.lowerReturnIfArms(ret_node, nested, cur)) return;
            }
        }
        var value_kind: ExprKind = .plain;
        const value_is_error = if (value_opt) |expr|
            self.returnExprIsError(expr)
        else
            false;
        if (value_opt) |expr| {
            const shape = initShapeNode(self, expr);
            const label = switch (tree.nodeTag(shape)) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => self.blockLabelToken(shape),
                else => null,
            };
            if (label != null and self.singleLabeledBreakValue(shape, label.?) != null) {
                value_kind = .unknown;
                try self.lowerValueExpr(expr, cur, .{ .return_kind = &value_kind });
            } else {
                if (!try self.lowerComputedValue(expr, cur)) {
                    try self.emitUsesInExpr(expr, cur.*, null);
                    try self.applyTopLevelCallEffects(expr, cur, false);
                }
                value_kind = self.classifyExpr(expr);
            }
        }
        var return_inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
        var return_defined = false;
        var diagnostic_source: ?LocalId = null;
        if (self.cache) |cache| if (cache.return_defined_mode) {
            if (value_opt) |expr| {
                return_defined = self.selectedReturnValueInputs(expr, &return_inputs, 0);
                var literal_buffer: [2]Ast.Node.Index = undefined;
                if ((self.hasRuntimeUndefinedLiteral(expr) and
                    (tree.fullArrayInit(&literal_buffer, expr) != null or
                        tree.fullStructInit(&literal_buffer, expr) != null)) or
                    self.returnConstructorHasUndefinedDefault(expr))
                    value_kind = .undef;
                if (!return_defined) self.selectedDiagnosticPointerInputs(expr, &return_inputs);
                if (tree.fullStructInit(&literal_buffer, initShapeNode(self, expr)) != null) {
                    const snapshot = try self.appendLocal(.{
                        .name = "",
                        .decl_pos = self.posOf(expr),
                        .is_control_local = true,
                    });
                    try self.appendStmt(cur.*, .{
                        .kind = .{ .decl = .{ .local = snapshot, .init_kind = .unknown, .value_defined = false } },
                        .pos = self.posOf(expr),
                        .end_pos = self.endPosOf(expr),
                    });
                    const saved_mode = self.diagnostic_fields_mode;
                    self.diagnostic_fields_mode = true;
                    defer self.diagnostic_fields_mode = saved_mode;
                    _ = try self.unpackStructInitFields(cur.*, snapshot, null, initShapeNode(self, expr), self.posOf(expr), self.endPosOf(expr), null);
                    diagnostic_source = snapshot;
                }
                if (self.deferred.items.len != 0) {
                    const snapshot = try self.newScalarValue(expr, cur.*);
                    const original: ?cfg_types.ValueInput = switch (value_kind) {
                        .copy_of => |local| .{ .local = local },
                        .field_copy_of => |field| .{ .field = .{ .parent = field.parent, .name = field.name } },
                        else => null,
                    };
                    if (original) |input| {
                        for (&return_inputs) |*entry| if (entry.* == null) {
                            entry.* = input;
                            break;
                        };
                    }
                    try self.appendStmt(cur.*, .{
                        .kind = .{ .assign = .{
                            .target = snapshot,
                            .rhs_kind = value_kind,
                            .value_defined = return_defined,
                            .value_inputs = return_inputs,
                        } },
                        .pos = self.posOf(expr),
                        .end_pos = self.endPosOf(expr),
                    });
                    value_kind = .{ .copy_of = snapshot };
                    return_inputs = .{ .{ .local = snapshot }, null, null, null, null, null, null, null };
                }
            }
        };
        // Expression lowering registers block-local declarations and captures.
        // Map canonical tokens only after that table is ready, before defers.
        // Value replay consumes bytes and certificates, not physical loans.
        // Do not spend its shared budget constructing unused lifetime proofs.
        const values_only = if (self.cache) |cache| cache.return_defined_mode else false;
        const stack_loans: StackLoanProof = if (values_only) .{} else if (value_opt) |expr|
            try self.returnStackLoans(expr, tree.firstToken(expr), if (value_is_error) .failure else .normal)
        else
            .{};

        // Now flush defers — fires after the .use's, before the .ret.
        //
        // Zig fires errdefers only on returns that yield an ERROR value.
        // `returnExprIsError` recognises the statically-decidable error
        // shapes — a literal `error.X` and a returned error-capture
        // identifier (`catch |err| { ...; return err; }`) — and uses the
        // error-path flush for them; everything else uses normal-only.
        //
        // This is a sound under-approximation: `return foo()` where
        // `foo()` returns an error UNION (`!T`) may or may not be an
        // error at runtime, so it is NOT classified here — flushing
        // errdefers unconditionally would false-positive on the success
        // path, and deciding it needs callee return-type resolution.
        // Both caught shapes are common double-free sources, e.g.
        // `errdefer free(p); something() catch |err| { free(p); return err; }`.
        if (value_is_error) {
            try self.flushErrAndNormalDefers(cur);
        } else {
            try self.flushScopeDefers(cur, 0);
        }

        switch (value_kind) {
            .stack_ref, .copy_of, .composite_borrow => {
                if (!values_only) if (value_opt) |expr| try self.emitAdditionalEscapeChecks(expr, cur.*, value_kind, stack_loans);
            },
            else => {},
        }

        // Detect `return undefined;` — a literal sentinel return,
        // not an undef-leak through a variable.
        const is_literal_undef = if (value_opt) |expr| blk: {
            if (tree.nodeTag(expr) != .identifier) break :blk false;
            const tok = tree.nodeMainToken(expr);
            break :blk std.mem.eql(u8, tree.tokenSlice(tok), "undefined");
        } else false;

        try self.appendStmt(cur.*, .{
            .kind = .{ .ret = .{
                .value_kind = value_kind,
                .is_borrowed_return_type = self.is_borrowed_return_type,
                .is_literal_undef = is_literal_undef,
                .stack_loans = stack_loans,
                .value_defined = return_defined,
                .value_inputs = return_inputs,
                .diagnostic_source = diagnostic_source,
            } },
            .pos = self.posOf(ret_node),
            .end_pos = self.endPosOf(ret_node),
        });
        // Return terminates the block — advance cur to a fresh dead
        // block so any addEdge our caller does (e.g. lowerIf wiring
        // an else-branch into the merge) flows from an unreachable
        // block, not the live ret block.  Without this, the pre-
        // return state leaks into the merge join and causes false
        // positives on locals that were only set on the non-return
        // branches.
        cur.* = try self.newBlock();
    }

    /// True for builtin calls that don't return — these terminate
    /// the basic block.  `unreachable` is already handled as a
    /// literal one level up in lowerStmt.
    /// For builtin calls that produce a value aliasing one of their
    /// args' underlying storage (`@ptrCast(x)`, `@bitCast(x)`,
    /// `@alignCast(x)`, `@constCast(x)`, `@volatileCast(x)`,
    /// `@addrSpaceCast(x)`, `@as(T, x)`, `@fieldParentPtr(name, p)`),
    /// return the AST node of the SOURCE argument so classifyExpr
    /// can recursively classify it.  The result's origin is
    /// whatever the source's was — alloc tracking flows through.
    fn transparentCastSource(self: *Builder, call_node: Ast.Node.Index) ?Ast.Node.Index {
        const tree = self.tree;
        const tok = tree.nodeMainToken(call_node);
        const name = tree.tokenSlice(tok);

        const SingleArg = enum { last };
        const LastArg = enum { last };
        const kind: union(enum) {
            single: SingleArg,
            last: LastArg,
            none,
        } = blk: {
            // Single-arg casts (arg 0 is the source).
            if (std.mem.eql(u8, name, "@ptrCast") or
                std.mem.eql(u8, name, "@bitCast") or
                std.mem.eql(u8, name, "@alignCast") or
                std.mem.eql(u8, name, "@constCast") or
                std.mem.eql(u8, name, "@volatileCast") or
                std.mem.eql(u8, name, "@addrSpaceCast"))
                break :blk .{ .single = .last };
            // Two-arg builtins where the source/pointer is the LAST arg:
            //   @as(T, x), @fieldParentPtr(name, ptr).
            if (std.mem.eql(u8, name, "@as") or
                std.mem.eql(u8, name, "@fieldParentPtr"))
                break :blk .{ .last = .last };
            break :blk .none;
        };

        if (kind == .none) return null;

        // Extract the LAST arg, which is the source/pointer for all
        // patterns we care about.  Two AST shapes to handle:
        //   .builtin_call_two[_comma]   — up to 2 args inline
        //   .builtin_call[_comma]       — N args via extra_range
        switch (tree.nodeTag(call_node)) {
            .builtin_call_two, .builtin_call_two_comma => {
                const d = tree.nodeData(call_node).opt_node_and_opt_node;
                if (d[1].unwrap()) |a| return a;
                if (d[0].unwrap()) |a| return a;
                return null;
            },
            .builtin_call, .builtin_call_comma => {
                const d = tree.nodeData(call_node).extra_range;
                const s: u32 = @intFromEnum(d.start);
                const e: u32 = @intFromEnum(d.end);
                if (e == s) return null;
                return @as(Ast.Node.Index, @enumFromInt(tree.extra_data[e - 1])); // zbc-disable-line: index-minus-one-without-zero-guard — e > s proven by `if (e == s) return null` above
            },
            else => return null,
        }
    }

    fn builtinIsDivergent(self: *Builder, call_node: Ast.Node.Index) bool {
        const tree = self.tree;
        const tok = tree.nodeMainToken(call_node);
        const slice = tree.tokenSlice(tok);
        return std.mem.eql(u8, slice, "@panic") or std.mem.eql(u8, slice, "@trap");
    }

    const WrapHit = struct { local: LocalId, hint: InitHint };

    /// If `init_node` is a struct-literal whose field values include
    /// a known arena_local or heap_local, return the strongest hit
    /// (source local + its hint).  Caller overrides init_kind to
    /// `.copy_of(hit.local)` so transferDecl propagates the wrapped
    /// resource's origin to the new local — composite-borrow
    /// checks then fire correctly on methods called on the wrapper.
    fn initWrapsResourceLocalRef(self: *Builder, init_node: Ast.Node.Index) ?WrapHit {
        const tree = self.tree;
        switch (tree.nodeTag(init_node)) {
            .struct_init,
            .struct_init_comma,
            .struct_init_one,
            .struct_init_one_comma,
            .struct_init_dot,
            .struct_init_dot_comma,
            .struct_init_dot_two,
            .struct_init_dot_two_comma,
            => {},
            else => return null,
        }
        const first = tree.firstToken(init_node);
        const last = tree.lastToken(init_node);
        const tags = tree.tokens.items(.tag);
        var result: ?WrapHit = null;
        var t: Ast.TokenIndex = first;
        while (t <= last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (t > 0 and tags[t - 1] == .period) continue; // field name
            const name = tree.tokenSlice(t);
            const id = self.name_to_local.get(name) orelse continue;
            const hint = self.locals.items[@intFromEnum(id)].init_hint;
            switch (hint) {
                .arena_local => return .{ .local = id, .hint = .arena_local },
                .heap_local => result = .{ .local = id, .hint = .heap_local },
                else => {},
            }
        }
        return result;
    }

    /// If `name` matches a local with a function-pointer binding,
    /// return the bound fn's name.  Otherwise return `name` unchanged.
    /// Lets `const op = some_fn; op(args)` resolve to some_fn's
    /// annotation at call sites.
    fn resolveBoundCallee(self: *Builder, name: []const u8) []const u8 {
        const id = self.name_to_local.get(name) orelse return name;
        return self.locals.items[@intFromEnum(id)].bound_fn_name orelse name;
    }

    /// If `init_node` is a bare identifier that names an annotated
    /// fn (or any fn present in our DB — annotation can be null
    /// when only `@takes`/`is_noreturn` is set), return the fn's
    /// name slice.  Used to record function-pointer bindings so
    /// call sites via the local resolve to the original fn.
    fn boundFnName(self: *Builder, init_node: Ast.Node.Index) ?[]const u8 {
        const tree = self.tree;
        if (tree.nodeTag(init_node) != .identifier) return null;
        const name = tree.tokenSlice(tree.nodeMainToken(init_node));
        // Existence check — does the file declare a fn with this name?
        if (self.cache) |c| {
            const model = self.modelOrNull(c) orelse return null;
            if (model.findFn(name) != null) return name;
        }
        return null;
    }

    /// True iff `init_node` is a container declaration —
    /// `struct {...}` / `enum {...}` / `union {...}` / `opaque {}`
    /// / `extern struct {...}` / `packed union {...}`.  Used to
    /// recognise `const Name = struct {...};` type aliases so the
    /// stack-escape analysis doesn't treat `&Name.static_field`
    /// as a stack borrow.
    fn initIsContainerDecl(self: *const Builder, init_node: Ast.Node.Index) bool {
        const tree = self.tree;
        // Peel `extern`/`packed` modifiers — they wrap the
        // container_decl identifier in a `container_decl_*` AST
        // node tag the same way as the bare form.
        const tag = tree.nodeTag(init_node);
        return switch (tag) {
            .container_decl,
            .container_decl_trailing,
            .container_decl_two,
            .container_decl_two_trailing,
            .container_decl_arg,
            .container_decl_arg_trailing,
            .tagged_union,
            .tagged_union_trailing,
            .tagged_union_two,
            .tagged_union_two_trailing,
            .tagged_union_enum_tag,
            .tagged_union_enum_tag_trailing,
            => true,
            else => false,
        };
    }

    /// Apply free / arena-kill side effects of a top-level call
    /// expression appearing in any context that's not a bare-stmt
    /// (var-decl init, assign RHS, return value, discard RHS).
    /// Returns true if anything was emitted; caller may use this to
    /// decide whether to additionally emit a use/gap.  Does NOT
    /// terminate the block for noreturn — callers handle that.
    /// If `init_expr` resolves to a call whose callee FnSummary has
    /// `result_heap_fields` set, emit one
    /// `field_assign(local, field_name, .heap_alloc(fresh))` per
    /// recorded field.  Handles `try` / `catch` wrappers.
    fn emitConstructorResultHeapFields(
        self: *Builder,
        cur: BlockId,
        local: LocalId,
        init_expr: Ast.Node.Index,
        pos: SrcPos,
        end_pos: SrcPos,
    ) LoweringError!void {
        const tree = self.tree;
        var node = init_expr;
        while (true) switch (tree.nodeTag(node)) {
            .@"try" => node = tree.nodeData(node).node,
            .@"catch" => node = tree.nodeData(node).node_and_node[0],
            else => break,
        };
        switch (tree.nodeTag(node)) {
            .call, .call_one, .call_comma, .call_one_comma => {},
            else => return,
        }
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, node) orelse return;
        const callee = call_full.ast.fn_expr;
        const method_tok = switch (tree.nodeTag(callee)) {
            .identifier => tree.nodeMainToken(callee),
            .field_access => tree.nodeData(callee).node_and_token[1],
            else => return,
        };
        const callee_name = tree.tokenSlice(method_tok);

        // Resolve type-aware first when the receiver is a known
        // namespace (e.g. `Utf8.init(...)`), then bare-name.
        const heap_fields: []const []const u8 = blk: {
            if (tree.nodeTag(callee) == .field_access) {
                const recv = tree.nodeData(callee).node_and_token[0];
                if (tree.nodeTag(recv) == .identifier) {
                    const recv_name = tree.tokenSlice(tree.nodeMainToken(recv));
                    if (self.cache) |c| {
                        if (self.queryOrUnknown(*const fn_summary.FnSummary, c.summaryByMethod(recv_name, callee_name))) |s| {
                            if (s.result_heap_fields.len > 0) break :blk s.result_heap_fields;
                        }
                    }
                }
            }
            if (self.cache) |c| {
                if (self.queryOrUnknown(*const fn_summary.FnSummary, c.summaryByName(callee_name))) |s| {
                    if (s.result_heap_fields.len > 0) break :blk s.result_heap_fields;
                }
            }
            break :blk &[_][]const u8{};
        };
        if (heap_fields.len == 0) return;
        for (heap_fields) |fname| {
            const hid: abstract_state.HeapId = @enumFromInt(self.next_heap);
            self.next_heap += 1;
            try self.appendStmt(cur, .{
                .kind = .{ .field_assign = .{
                    .parent = local,
                    .name = fname,
                    .rhs_kind = .{ .heap_alloc = .{ .id = hid } },
                } },
                .pos = pos,
                .end_pos = end_pos,
            });
        }
    }

    /// Only the actual standard-library declaration certifies a permutation.
    /// Cross-array swaps and indirect pointers retain ordinary mutation effects.
    fn callPermutesArray(
        self: *Builder,
        cache: *file_cache.FileCache,
        call_node: Ast.Node.Index,
        argument: Ast.Node.Index,
        array: LocalId,
        diagnostic_inputs: *[2]?cfg_types.ValueInput,
    ) LoweringError!bool {
        if (!self.locals.items[@intFromEnum(array)].is_array) return false;
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = zls_resolver_mod.TypeResolver.CallOperands.full(
            self.tree,
            &call_buffer,
            call_node,
        ) orelse return false;
        const frame = self.integerResolutionFrame();
        const actual = (try cache.actualCallSummaryAt(
            call.queryToken(self.tree, call_node),
            frame,
        )) orelse return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(
            actual.callee.tree,
            &proto_buffer,
            actual.callee.declaration,
        ) orelse return false;
        const name = proto.name_token orelse return false;
        if (!std.mem.eql(u8, actual.callee.tree.tokenSlice(name), "swap")) return false;
        const resolver = if (actual.callee.caller_frame) |caller|
            caller.resolver
        else
            cache.zls orelse return false;
        if (!try resolver.declaredInToolchainFile(actual.callee.handle, "/std/mem.zig"))
            return false;
        var selected = false;
        var same_array = true;
        for ([_]u32{ 1, 2 }, 0..) |parameter, ordinal| {
            const mapped = (try actual.callArgumentFor(
                cache,
                &call_buffer,
                parameter,
            )) orelse return false;
            if (mapped == argument) selected = true;
            var node = mapped;
            while (self.tree.nodeTag(node) == .grouped_expression)
                node = self.tree.nodeData(node).node_and_token[0];
            if (self.tree.nodeTag(node) != .address_of) return false;
            node = self.tree.nodeData(node).node;
            while (self.tree.nodeTag(node) == .grouped_expression)
                node = self.tree.nodeData(node).node_and_token[0];
            if (self.tree.nodeTag(node) != .array_access) return false;
            const base = self.tree.nodeData(node).node_and_node[0];
            if (self.tree.nodeTag(base) != .identifier) return false;
            const local = self.name_to_local.get(
                self.tree.tokenSlice(self.tree.nodeMainToken(base)),
            ) orelse return false;
            same_array = same_array and local == array;
            diagnostic_inputs[ordinal] = .{ .indexed = .{
                .array = local,
                .index = self.indexTerm(self.tree.nodeData(node).node_and_node[1]),
            } };
        }
        return selected and same_array;
    }

    /// A preserving helper transports only its source-proven value inputs.
    /// Its caller's complete certificate, not the helper, supplies old bytes.
    fn callPreservesArray(
        self: *Builder,
        cache: *file_cache.FileCache,
        call_node: Ast.Node.Index,
        argument: Ast.Node.Index,
        array: LocalId,
        inputs: *[8]?cfg_types.ValueInput,
        whole_payload: *bool,
        may_literal_undefined: *bool,
    ) LoweringError!bool {
        if (!self.locals.items[@intFromEnum(array)].is_array) return false;
        var node = argument;
        while (self.tree.nodeTag(node) == .grouped_expression)
            node = self.tree.nodeData(node).node_and_token[0];
        if (self.tree.nodeTag(node) != .address_of) return false;
        node = self.tree.nodeData(node).node;
        while (self.tree.nodeTag(node) == .grouped_expression)
            node = self.tree.nodeData(node).node_and_token[0];
        const base = if (self.tree.nodeTag(node) == .array_access)
            self.tree.nodeData(node).node_and_node[0]
        else
            node;
        if (self.tree.nodeTag(base) != .identifier) return false;
        const local = self.name_to_local.get(
            self.tree.tokenSlice(self.tree.nodeMainToken(base)),
        ) orelse return false;
        if (local != array) return false;

        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = zls_resolver_mod.TypeResolver.CallOperands.full(
            self.tree,
            &call_buffer,
            call_node,
        ) orelse return false;
        // Effects in any argument can invalidate earlier value dependencies.
        for (call.ast.params) |actual| {
            var literal_buffer: [2]Ast.Node.Index = undefined;
            if (self.tree.fullStructInit(&literal_buffer, actual)) |literal| {
                for (literal.ast.fields) |field_value| {
                    if (try self.valueNeedsSnapshot(field_value)) return false;
                }
            } else if (try self.valueNeedsSnapshot(actual)) return false;
        }
        const frame = self.integerResolutionFrame();
        const actual = (try cache.actualCallSummaryAt(
            call.queryToken(self.tree, call_node),
            frame,
        )) orelse return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(
            actual.callee.tree,
            &proto_buffer,
            actual.callee.declaration,
        ) orelse return false;
        var parameters = proto.iterate(actual.callee.tree);
        var parameter_index: u32 = 0;
        var selected = false;
        var count: usize = 0;
        var certified = true;
        while (parameters.next() != null) : (parameter_index += 1) {
            const mapped = (try actual.callArgumentFor(
                cache,
                &call_buffer,
                parameter_index,
            )) orelse continue;
            if (mapped != argument) continue;
            const strict_proof = try cache.preservingCallParameterWrite(call_node, parameter_index, frame);
            const proof = strict_proof orelse (try cache.diagnosticWholePayloadWriteInputs(
                call_node,
                parameter_index,
                frame,
            )) orelse return false;
            if (strict_proof == null) certified = false;
            whole_payload.* = whole_payload.* or proof.whole_payload;
            for (proof.dependencies) |dependency| {
                const expression = dependency orelse continue;
                var values: [8]?cfg_types.ValueInput = .{null} ** 8;
                const defined = if (proof.whole_payload)
                    self.selectedReturnValueInputs(expression, &values, 0)
                else
                    self.selectedValueInputs(expression, &values, true);
                if (!defined) {
                    certified = false;
                    var operand = expression;
                    while (self.tree.nodeTag(operand) == .grouped_expression)
                        operand = self.tree.nodeData(operand).node_and_token[0];
                    if (self.tree.nodeTag(operand) == .address_of) {
                        _ = self.selectedValueInputs(self.tree.nodeData(operand).node, &values, false);
                    } else self.selectedDiagnosticValueInputs(expression, &values, 0);
                }
                may_literal_undefined.* = may_literal_undefined.* or self.hasRuntimeUndefinedLiteral(expression) or
                    self.returnConstructorHasUndefinedDefault(expression);
                for (values) |value| {
                    const input = value orelse continue;
                    if (count == inputs.len) return false;
                    inputs[count] = input;
                    count += 1;
                }
            }
            selected = true;
        }
        return selected and certified;
    }

    /// Preserve payload coverage only when every formal receiving this actual
    /// is proven read-only by its body or toolchain identity. Unknown effects
    /// still invalidate storage.
    fn callArgumentReadOnly(
        self: *Builder,
        cache: *file_cache.FileCache,
        call_node: Ast.Node.Index,
        argument: Ast.Node.Index,
    ) LoweringError!bool {
        var call_buffer: [2]Ast.Node.Index = undefined;
        const call = zls_resolver_mod.TypeResolver.CallOperands.full(self.tree, &call_buffer, call_node) orelse return false;
        const token = call.queryToken(self.tree, call_node);
        const frame = if (self.zls) |resolver| resolver.resolutionFrame() else null;
        const actual = (try cache.actualCallSummaryAt(token, frame)) orelse return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(actual.callee.tree, &proto_buffer, actual.callee.declaration) orelse return false;
        var parameters = proto.iterate(actual.callee.tree);
        var parameter_index: u32 = 0;
        var selected = false;
        while (parameters.next() != null) : (parameter_index += 1) {
            const mapped = (try actual.callArgumentFor(cache, &call_buffer, parameter_index)) orelse continue;
            if (mapped != argument) continue;
            const optimization_barrier = barrier: {
                if (parameter_index != 0) break :barrier false;
                const name = proto.name_token orelse break :barrier false;
                if (!std.mem.eql(u8, actual.callee.tree.tokenSlice(name), "doNotOptimizeAway"))
                    break :barrier false;
                const resolver = if (actual.callee.caller_frame) |caller| caller.resolver else cache.zls orelse break :barrier false;
                // The assembly memory clobber does not write through the
                // input pointer; the C fallback only copies from it.
                // A project declaration with this name gets no such credit.
                break :barrier try resolver.declaredInToolchainFile(actual.callee.handle, "/std/mem.zig");
            };
            if (!optimization_barrier) {
                const effect = (try cache.callEffectAt(token, .{ .parameter = .{ .param = parameter_index, .read_only_only = true } }, .{ .frame = frame })) orelse return false;
                if (effect != .read_only) return false;
            }
            selected = true;
        }
        return selected;
    }

    fn invalidateCallAliases(self: *Builder, call_node: Ast.Node.Index, block: BlockId) !void {
        var buffer: [1]Ast.Node.Index = undefined;
        const call = self.tree.fullCall(&buffer, call_node) orelse return;
        for (call.ast.params) |argument| {
            const tree = self.tree;
            const base = switch (tree.nodeTag(argument)) {
                .identifier => argument,
                .slice_open => tree.nodeData(argument).node_and_node[0],
                .slice, .slice_sentinel => tree.nodeData(argument).node_and_extra[0],
                else => continue,
            };
            if (tree.nodeTag(base) != .identifier) continue;
            const alias = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(base))) orelse continue;
            const info = self.locals.items[@intFromEnum(alias)];
            if (argument == base and !info.is_pointer and info.frame_borrow_origin == null) continue;
            if (argument != base and !info.is_array) continue;
            if (self.cache) |cache| {
                if (try self.callArgumentReadOnly(cache, call_node, argument)) continue;
            }
            // Transfer follows the alias's current origin, not its original
            // binding, so a pointer rebind cannot leave stale coverage live.
            try self.appendStmt(block, .{
                .kind = .{ .pointer_write = .{ .target = alias, .initializes = false } },
                .pos = self.posOf(argument),
                .end_pos = self.endPosOf(argument),
            });
        }
        // Method syntax passes the receiver outside ast.params, and a value
        // receiver can be auto-addressed for a pointer formal. Unknown bindings
        // stay conservative; a resolved by-value formal does not expose storage.
        const tree = self.tree;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access) return;
        const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
        if (tree.nodeTag(receiver) != .identifier) return;
        const alias = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(receiver))) orelse return;
        const info = self.locals.items[@intFromEnum(alias)];
        if (!info.is_pointer) {
            receiver_borrow: {
                const cache = self.cache orelse break :receiver_borrow;
                var call_buffer: [2]Ast.Node.Index = undefined;
                const operands = zls_resolver_mod.TypeResolver.CallOperands.full(tree, &call_buffer, call_node) orelse
                    break :receiver_borrow;
                const frame = if (self.zls) |resolver| resolver.resolutionFrame() else null;
                const actual = (try cache.actualCallSummaryAt(operands.queryToken(tree, call_node), frame)) orelse
                    break :receiver_borrow;
                const argument = (try actual.callArgumentFor(cache, &call_buffer, 0)) orelse return;
                if (argument != receiver) return;
                const resolver = if (actual.callee.caller_frame) |caller|
                    caller.resolver
                else
                    self.zls orelse break :receiver_borrow;
                const formals = actual.callee.reference.actual_type.data.function.parameters;
                if (formals.len == 0) return;
                const formal = (try resolver.normalizedType(formals[0].type)) orelse
                    break :receiver_borrow;
                if (resolver.pointerSize(formal) != .one) return;
            }
        }
        if (self.cache) |cache| {
            if (try self.callArgumentReadOnly(cache, call_node, receiver)) return;
        }
        try self.appendStmt(block, .{
            .kind = .{ .pointer_write = .{ .target = alias, .initializes = false } },
            .pos = self.posOf(receiver),
            .end_pos = self.endPosOf(receiver),
        });
    }

    fn emitFieldRelease(
        self: *Builder,
        cur: *BlockId,
        release: CalleeFieldFree,
        pos: SrcPos,
        end_pos: SrcPos,
    ) LoweringError!void {
        const forget_current = Stmt{
            .kind = if (release.field.len == 0)
                .{ .assign = .{ .target = release.parent, .rhs_kind = .unknown } }
            else
                .{ .field_assign = .{
                    .parent = release.parent,
                    .name = release.field,
                    .rhs_kind = .unknown,
                } },
            .pos = pos,
            .end_pos = end_pos,
        };
        if (release.invalidate_only) {
            try self.appendStmt(cur.*, forget_current);
            return;
        }
        const heap: abstract_state.HeapId = @enumFromInt(self.next_heap);
        self.next_heap += 1;
        const free = Stmt{
            .kind = if (release.field.len == 0)
                .{ .heap_free = .{ .freed_local = release.parent, .fallback_hid = heap } }
            else
                .{ .field_heap_free = .{
                    .parent = release.parent,
                    .name = release.field,
                    .fallback_hid = heap,
                } },
            .pos = pos,
            .end_pos = end_pos,
        };
        if (release.certainty == .definite) {
            try self.appendStmt(cur.*, free);
            if (release.entry_only) {
                // The entry payload is dead, but an incomplete callee trace
                // cannot identify the field's current payload. Forget only
                // that field binding; caller aliases retain the killed heap.
                try self.appendStmt(cur.*, forget_current);
            }
            return;
        }
        // A possible release on this return channel has both outcomes. Rebinding
        // this site-local choice on each visit permits fresh loop outcomes.
        // Boolean partitions retain the live and freed resource states.
        const choice = try self.appendLocal(.{
            .name = "<possible field release>",
            .decl_pos = pos,
            .is_control_local = true,
        });
        try self.appendStmt(cur.*, .{
            .kind = .{ .decl = .{ .local = choice, .init_kind = .plain } },
            .pos = pos,
            .end_pos = end_pos,
        });
        const released = try self.newBlock();
        const retained = try self.newBlock();
        const merge = try self.newBlock();
        try self.addEdge(cur.*, released);
        try self.addEdge(cur.*, retained);
        try self.appendStmt(released, .{
            .kind = .{ .assume = .{ .local = choice } },
            .pos = pos,
            .end_pos = end_pos,
        });
        try self.appendStmt(retained, .{
            .kind = .{ .assume = .{ .not_local = choice } },
            .pos = pos,
            .end_pos = end_pos,
        });
        try self.appendStmt(released, free);
        try self.addEdge(released, merge);
        try self.addEdge(retained, merge);
        cur.* = merge;
    }

    const CleanupOutcome = enum { normal_success, error_return };

    const CalleeStorageOperation = struct {
        parent: LocalId,
        field: []const u8,
        kind: @FieldType(fn_summary.StorageOperation, "kind"),
        allocator: ?cfg_types.ValueInput = null,
        version: ?usize = null,
    };

    const SavedEntryStorage = struct {
        parent: LocalId,
        field: []const u8,
        local: LocalId,
        version: usize,
    };

    /// Replay a complete exit alternative, not independent MAY releases and
    /// stores. Saved entry payloads keep their allocation identity when the
    /// caller's current field is rebound to a new allocation.
    fn emitStorageOutcome(
        self: *Builder,
        call_node: Ast.Node.Index,
        operations: []const CalleeStorageOperation,
        block: BlockId,
        pos: SrcPos,
        end_pos: SrcPos,
    ) LoweringError!void {
        const cache = self.cache.?;
        var saved: std.ArrayListUnmanaged(SavedEntryStorage) = .empty;
        defer saved.deinit(self.gpa);
        for (operations, 0..) |operation, index| {
            try cache.normalCleanupStorageWork(call_node, 1);
            var version: usize = 0;
            for (operations[0..index]) |previous| {
                try cache.normalCleanupStorageWork(call_node, 1 + @min(previous.field.len, operation.field.len));
                if (previous.kind == .replace and previous.parent == operation.parent and
                    std.mem.eql(u8, previous.field, operation.field)) version += 1;
            }
            const released_version = if (operation.kind == .release_entry) 0 else
                operation.version orelse version;
            var entry: ?LocalId = null;
            for (saved.items) |snapshot| {
                try cache.normalCleanupStorageWork(call_node, 1 + @min(snapshot.field.len, operation.field.len));
                if (snapshot.parent == operation.parent and
                    snapshot.version == (if (operation.kind == .replace) version else released_version) and
                    std.mem.eql(u8, snapshot.field, operation.field))
                {
                    entry = snapshot.local;
                    break;
                }
            }
            switch (operation.kind) {
                .replace => {
                    const needs_entry = needs_entry: {
                        var later_version = version + 1;
                        for (operations[index + 1 ..]) |later| {
                            try cache.normalCleanupStorageWork(call_node, 1 + @min(later.field.len, operation.field.len));
                            if (later.parent != operation.parent or
                                !std.mem.eql(u8, later.field, operation.field)) continue;
                            if (later.kind == .replace) {
                                later_version += 1;
                            } else {
                                const selected = if (later.kind == .release_entry) 0 else
                                    later.version orelse later_version;
                                if (selected == version) break :needs_entry true;
                            }
                        }
                        break :needs_entry false;
                    };
                    if (entry == null and needs_entry) {
                        try cache.normalCleanupStorageWork(call_node, 3 + if (saved.items.len == saved.capacity) saved.items.len else @as(usize, 0));
                        const local = try self.appendLocal(.{
                            .name = "<callee entry payload>",
                            .decl_pos = pos,
                        });
                        try self.appendStmt(block, .{
                            .kind = .{ .decl = .{
                                .local = local,
                                .init_kind = if (operation.field.len == 0)
                                    .{ .copy_of = operation.parent }
                                else
                                    .{ .field_copy_of = .{ .parent = operation.parent, .name = operation.field } },
                            } },
                            .pos = pos,
                            .end_pos = end_pos,
                        });
                        try saved.append(self.gpa, .{
                            .parent = operation.parent,
                            .field = operation.field,
                            .local = local,
                            .version = version,
                        });
                    }
                    const heap: abstract_state.HeapId = @enumFromInt(self.next_heap);
                    self.next_heap += 1;
                    const allocation: ExprKind = .{ .heap_alloc = .{
                        .id = heap,
                        .allocator_local = if (operation.allocator) |source| switch (source) {
                            .local => |local| local,
                            .field, .indexed => null,
                        } else null,
                        .allocator_source = operation.allocator,
                    } };
                    try self.appendStmt(block, .{
                        .kind = if (operation.field.len == 0)
                            .{ .assign = .{ .target = operation.parent, .rhs_kind = allocation } }
                        else
                            .{ .field_assign = .{
                                .parent = operation.parent,
                                .name = operation.field,
                                .rhs_kind = allocation,
                            } },
                        .pos = pos,
                        .end_pos = end_pos,
                    });
                },
                .release_entry, .release_current => {
                    if (entry != null) {
                        const heap: abstract_state.HeapId = @enumFromInt(self.next_heap);
                        self.next_heap += 1;
                        try self.appendStmt(block, .{
                            .kind = .{ .heap_free = .{ .freed_local = entry.?, .fallback_hid = heap } },
                            .pos = pos,
                            .end_pos = end_pos,
                        });
                    } else {
                        var current = block;
                        try self.emitFieldRelease(&current, .{
                            .parent = operation.parent,
                            .field = operation.field,
                            .certainty = .definite,
                        }, pos, end_pos);
                    }
                },
            }
        }
    }

    /// Null means no exact identity certificate. Map every operand before
    /// emitting anything, so an unresolved argument cannot leave a partial
    /// replacement in the caller's graph.
    fn applyStorageEffects(
        self: *Builder,
        call_node: Ast.Node.Index,
        outcome: CleanupOutcome,
        cur: *BlockId,
    ) LoweringError!?bool {
        const cache = self.cache orelse return null;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = self.tree.fullCall(&buffer, call_node) orelse return null;
        cache.beginNormalCleanup();
        defer cache.endNormalCleanup();
        try cache.enterNormalCleanup(call_node);
        defer cache.leaveNormalCleanup();
        const frame = if (self.zls) |resolver| resolver.resolutionFrame() else null;
        const actual = (try cache.actualCallSummaryAt(fresh_storage.calleeQueryToken(self.tree, call), frame)) orelse return null;
        const summary = (try cache.summaryOfResolvedMethod(actual.callee)) orelse return null;
        const complete = switch (outcome) {
            .normal_success => summary.normal_success_storage_effects_complete,
            .error_return => summary.error_storage_effects_complete,
        };
        if (!complete) return null;
        const outcomes = switch (outcome) {
            .normal_success => summary.normal_success_storage_outcomes,
            .error_return => summary.error_storage_outcomes,
        };
        if (outcomes.len == 0) return null;
        var operations: std.ArrayListUnmanaged(CalleeStorageOperation) = .empty;
        defer operations.deinit(self.gpa);
        var offsets: std.ArrayListUnmanaged(usize) = .empty;
        defer offsets.deinit(self.gpa);
        try cache.normalCleanupStorageWork(call_node, 1);
        try offsets.append(self.gpa, 0);
        for (outcomes) |alternative| {
            try cache.normalCleanupStorageWork(call_node, 1);
            for (alternative.operations, 0..) |operation, source_index| {
                try cache.normalCleanupStorageWork(call_node, 1);
                var arguments: [2]Ast.Node.Index = undefined;
                const argument = (try actual.callArgumentFor(cache, &arguments, operation.path.param)) orelse return null;
                const path = self.actualLocalPath(argument) orelse return null;
                try cache.normalCleanupStorageWork(call_node, 1 + path.prefix_len + operation.path.path.len +
                    if (operations.items.len == operations.capacity) operations.items.len else @as(usize, 0));
                const allocator = if (operation.kind == .replace)
                    try self.storageAllocatorSource(actual, operation.allocator orelse return null, call_node) orelse return null
                else
                    null;
                const field = try self.allocActualDottedPath(path, operation.path.path);
                const start = offsets.items[offsets.items.len - 1];
                for (operations.items[start..], 0..) |previous, index| {
                    const source = alternative.operations[index].path;
                    try cache.normalCleanupStorageWork(call_node, 1 +
                        @min(previous.field.len, field.len) +
                        @min(source.path.len, operation.path.path.len));
                    if ((previous.kind == .replace or operation.kind == .replace) and
                        previous.parent == path.local and std.mem.eql(u8, previous.field, field) and
                        (source.param != operation.path.param or !std.mem.eql(u8, source.path, operation.path.path)))
                        return null;
                }
                std.debug.assert(operations.items.len - start == source_index);
                try operations.append(self.gpa, .{
                    .parent = path.local,
                    .field = field,
                    .kind = operation.kind,
                    .allocator = allocator,
                    .version = operation.version,
                });
            }
            try cache.normalCleanupStorageWork(call_node, 1 +
                if (offsets.items.len == offsets.capacity) offsets.items.len else @as(usize, 0));
            try offsets.append(self.gpa, operations.items.len);
        }
        if (operations.items.len == 0) return false;
        const pos = self.posOf(call_node);
        const end_pos = self.endPosOf(call_node);
        if (outcomes.len == 1) {
            try self.emitStorageOutcome(call_node, operations.items, cur.*, pos, end_pos);
            return true;
        }
        try cache.normalCleanupStorageWork(call_node, 1);
        const merge = try self.newBlock();
        var remaining = cur.*;
        for (0..outcomes.len) |index| {
            try cache.normalCleanupStorageWork(call_node, 8);
            const selected = if (index + 1 == outcomes.len) remaining else selected: {
                const choice = try self.appendLocal(.{
                    .name = "<callee storage outcome>",
                    .decl_pos = pos,
                    .is_control_local = true,
                });
                try self.appendStmt(remaining, .{
                    .kind = .{ .decl = .{ .local = choice, .init_kind = .plain } },
                    .pos = pos,
                    .end_pos = end_pos,
                });
                const taken = try self.newBlock();
                const other = try self.newBlock();
                try self.addEdge(remaining, taken);
                try self.addEdge(remaining, other);
                try self.appendStmt(taken, .{
                    .kind = .{ .assume = .{ .local = choice } },
                    .pos = pos,
                    .end_pos = end_pos,
                });
                try self.appendStmt(other, .{
                    .kind = .{ .assume = .{ .not_local = choice } },
                    .pos = pos,
                    .end_pos = end_pos,
                });
                remaining = other;
                break :selected taken;
            };
            try self.emitStorageOutcome(call_node, operations.items[offsets.items[index]..offsets.items[index + 1]], selected, pos, end_pos);
            try self.addEdge(selected, merge);
        }
        cur.* = merge;
        return true;
    }

    fn storageAllocatorSource(
        self: *Builder,
        actual: file_cache.FileCache.ActualCallSummary,
        allocator: fn_summary.ParamPath,
        call_node: Ast.Node.Index,
    ) LoweringError!?cfg_types.ValueInput {
        const cache = self.cache.?;
        try cache.normalCleanupStorageWork(call_node, 1 + allocator.path.len);
        var arguments: [2]Ast.Node.Index = undefined;
        const argument = (try actual.callArgumentFor(cache, &arguments, allocator.param)) orelse return null;
        if (allocator.path.len == 0) {
            if (self.argResolvesToArenaBound(argument)) |local| return .{ .local = local };
        }
        const path = self.actualLocalPath(argument) orelse return null;
        if (path.prefix_len == 0 and allocator.path.len == 0) return .{ .local = path.local };
        try cache.normalCleanupStorageWork(call_node, 1 + path.prefix_len);
        return .{ .field = .{
            .parent = path.local,
            .name = try self.allocActualDottedPath(path, allocator.path),
        } };
    }

    fn applyFieldEffects(self: *Builder, call_node: Ast.Node.Index, outcome: CleanupOutcome, cur: *BlockId) LoweringError!bool {
        if (self.tree.nodeTag(call_node) == .grouped_expression)
            return self.applyFieldEffects(self.tree.nodeData(call_node).node_and_token[0], outcome, cur);
        if (try self.applyStorageEffects(call_node, outcome, cur)) |applied| return applied;
        var emissions: std.ArrayListUnmanaged(CalleeFieldFree) = .empty;
        defer emissions.deinit(self.gpa);
        const collected_complete = try self.collectCalleeFieldFrees(call_node, outcome, self.gpa, &emissions);
        const pos = self.posOf(call_node);
        const end_pos = self.endPosOf(call_node);
        for (emissions.items) |release| try self.emitFieldRelease(cur, release, pos, end_pos);
        if (!collected_complete) {
            // Partial positive evidence is not a certificate of no further
            // effects. Retain the existing opaque-call fallback contract.
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "call-effects-incomplete", .may_assign_locals = false } },
                .pos = pos,
                .end_pos = end_pos,
            });
        }
        return emissions.items.len != 0;
    }

    /// An unselected error union cannot carry success-only memory effects.
    fn callReturnsWithoutError(self: *Builder, call_node: Ast.Node.Index) bool {
        if (self.valueIsError(call_node, false)) |is_error| return !is_error;
        const frame = self.integerResolutionFrame() orelse return false;
        const result = self.queryOrUnknown(
            zls_resolver_mod.TypeResolver.ActualType,
            frame.typeOfNode(call_node),
        ) orelse return false;
        const tag = frame.resolver.typeTag(result) orelse return false;
        return tag != .error_union and tag != .error_set;
    }

    fn applyTopLevelCallEffects(self: *Builder, expr_node: Ast.Node.Index, cur: *BlockId, success_selected: bool) (LoweringError)!void {
        const tree = self.tree;
        // Error-accepting wrappers route their normal effects in the
        // success block created by lowerWrappedValue. An optional
        // result, including null, is still a successful normal return.
        var node = expr_node;
        while (true) switch (tree.nodeTag(node)) {
            .@"try", .@"catch" => return,
            .grouped_expression => node = tree.nodeData(node).node_and_token[0],
            .@"orelse" => node = tree.nodeData(node).node_and_node[0],
            else => break,
        };
        switch (tree.nodeTag(node)) {
            .call, .call_one, .call_comma, .call_one_comma => {},
            else => return,
        }
        try self.invalidateCallAliases(node, cur.*);
        if (!success_selected and !self.callReturnsWithoutError(node)) return;
        // Exact normal-return certificates include whole-local and field effects.
        _ = try self.applyFieldEffects(node, .normal_success, cur);
        try self.emitSuccessfulCallOutputs(cur.*, node);
    }

    /// Memory credits are success-return effects, never argument reads.
    fn emitSuccessfulCallOutputs(self: *Builder, block: BlockId, call_node: Ast.Node.Index) LoweringError!void {
        try self.emitAddressOutputs(block, call_node, null);
        try self.emitSuccessfulSliceOutputs(block, call_node);
        try self.emitSuccessfulCountdownPrefix(block, call_node);
    }

    fn emitAddressOutputs(self: *Builder, block: BlockId, call_node: Ast.Node.Index, success_bool: ?bool) LoweringError!void {
        const cache = self.cache orelse return;
        const tree = self.tree;
        var token = tree.firstToken(call_node);
        const last = tree.lastToken(call_node);
        while (token <= last) : (token += 1) {
            if (tree.tokenTag(token) != .identifier) continue;
            var use = (if (success_bool) |expected|
                try cache.addressUseOnBooleanAt(token, expected)
            else
                try cache.addressUseAt(token)) orelse
                self.queryOrUnknown(file_cache.FileCache.AddressUse, cache.undefinedAddressUseAt(token, success_bool)) orelse continue;
            if (use.call_node != call_node) continue;
            if (use.undefined_field_count == 0)
                cache.populateUndefinedAddressStores(&use) catch |err| self.noteResolutionError(err);
            try self.emitAddressCredit(block, use);
        }
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, call_node) orelse return;
        for (call.ast.params) |argument| {
            if (tree.nodeTag(argument) == .address_of) continue;
            const use = self.queryOrUnknown(file_cache.FileCache.AddressUse, cache.pointerArgumentUndefinedUseAt(
                call_node,
                argument,
                success_bool,
            )) orelse continue;
            try self.emitAddressCredit(block, use);
        }
    }

    fn emitAddressCredit(self: *Builder, block: BlockId, use: file_cache.FileCache.AddressUse) LoweringError!void {
        if (self.indexedTarget(use.operand)) |target| {
            const call_node = use.call_node orelse return;
            const pos = self.posOf(call_node);
            const end = self.endPosOf(call_node);
            if (use.location_written or use.definite_write) {
                const write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
                    .array = target.array,
                    .index = self.indexTerm(target.index_node),
                    .field_array = target.field_array,
                    .rhs_kind = .plain,
                    .defined = use.definite_write,
                };
                try self.appendStmt(block, .{ .kind = .{ .indexed_write = write }, .pos = pos, .end_pos = end });
                try self.appendSliceStoreEffect(block, write, pos, end);
            }
            for (use.undefined_fields[0..use.undefined_field_count]) |path| {
                if (path.len != 0) continue;
                const write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
                    .array = target.array,
                    .index = self.indexTerm(target.index_node),
                    .field_array = target.field_array,
                    .rhs_kind = .undef,
                    .defined = false,
                };
                try self.appendStmt(block, .{ .kind = .{ .indexed_write = write }, .pos = pos, .end_pos = end });
                try self.appendSliceStoreEffect(block, write, pos, end);
            }
            return;
        }
        var diagnostic_address_only = false;
        const source = self.classifySourceProjection(use.operand, 0) orelse place: {
            if (use.receiver and self.tree.nodeTag(use.operand) == .identifier) {
                const parent = self.indexLocalAt(self.tree.nodeMainToken(use.operand)) orelse return;
                if (self.locals.items[@intFromEnum(parent)].is_pointer)
                    break :place ExprKind{ .copy_of = parent };
            }
            // A proved store can target inline storage behind a pointer.
            // An output place is not a value-copy or pointee-input premise.
            if (self.tree.nodeTag(use.operand) != .field_access) return;
            const base, const field = self.tree.nodeData(use.operand).node_and_token;
            if (self.tree.nodeTag(base) != .identifier) return;
            const parent = self.name_to_local.get(self.tree.tokenSlice(self.tree.nodeMainToken(base))) orelse return;
            if (!self.locals.items[@intFromEnum(parent)].is_pointer) return;
            const frame = self.integerResolutionFrame() orelse return;
            const base_type = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(base)) orelse return;
            const pointer = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(base_type)) orelse return;
            if (frame.resolver.pointerSize(pointer) != .one) return;
            const child = frame.resolver.childType(pointer) orelse return;
            const owner = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(child)) orelse return;
            if (frame.resolver.typeTag(owner) != .@"struct") return;
            const field_type = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(use.operand)) orelse return;
            const aggregate = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(field_type)) orelse return;
            if (frame.resolver.typeTag(aggregate) != .@"struct") {
                if (!use.definite_write and !use.location_written and use.undefined_field_count == 0) return;
                diagnostic_address_only = true;
            }
            const name = self.normalizedFieldPath(field, field) orelse return;
            break :place ExprKind{ .field_copy_of = .{ .parent = parent, .name = name } };
        };
        const id = switch (source) {
            .copy_of => |local| local,
            .field_copy_of => |field| field.parent,
            else => return,
        };
        const prefix: ?[]const u8 = if (source == .field_copy_of) source.field_copy_of.name else null;
        if (!self.localCanBeStored(id)) return;
        const pos = self.posOf(use.call_node.?);
        const end = self.endPosOf(use.call_node.?);
        var diagnostic_id = id;
        var diagnostic_prefix = prefix;
        if (self.pointer_value_sources.get(id)) |pointee| {
            switch (pointee) {
                .copy_of => |owner| diagnostic_id = owner,
                .field_copy_of => |field| {
                    diagnostic_id = field.parent;
                    diagnostic_prefix = if (prefix) |suffix|
                        try self.allocDottedPath(field.name, suffix)
                    else
                        field.name;
                },
                else => {},
            }
        }
        if (use.definite_write and !diagnostic_address_only) {
            if (prefix) |path| {
                try self.appendStmt(block, .{
                    .kind = .{ .field_assign = .{ .parent = id, .name = path, .rhs_kind = .plain, .defined = true } },
                    .pos = pos,
                    .end_pos = end,
                });
            } else {
                try self.appendStmt(block, .{
                    .kind = .{ .pointer_write = .{ .target = id, .initializes = true } },
                    .pos = pos,
                    .end_pos = end,
                });
                if (self.locals.items[@intFromEnum(id)].is_array) try self.appendStmt(block, .{
                    .kind = .{ .array_complete = .{ .array = id } },
                    .pos = pos,
                    .end_pos = end,
                });
            }
        }
        if ((use.location_written and !use.definite_write) or (diagnostic_address_only and use.definite_write)) {
            var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
            var kind: ExprKind = .unknown;
            for (use.written_inputs) |entry| {
                const argument = entry orelse continue;
                if (self.hasRuntimeUndefinedLiteral(argument)) kind = .undef;
                var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
                _ = self.selectedValueInputs(argument, &selected, false);
                _ = mergeSelectedValueInputs(&inputs, selected);
            }
            for (use.written_reads) |entry| {
                const read = entry orelse continue;
                try self.selectedWrittenRead(read, &inputs, &kind);
            }
            if (prefix) |path| {
                try self.appendStmt(block, .{
                    .kind = .{ .field_assign = .{ .parent = diagnostic_id, .name = diagnostic_prefix orelse path, .rhs_kind = kind, .selected_inputs = inputs, .diagnostic_only = true } },
                    .pos = pos,
                    .end_pos = end,
                });
            } else {
                try self.appendStmt(block, .{
                    .kind = .{ .field_assign = .{ .parent = diagnostic_id, .name = diagnostic_prefix orelse "", .rhs_kind = kind, .selected_inputs = inputs, .diagnostic_only = true } },
                    .pos = pos,
                    .end_pos = end,
                });
            }
        }
        // Parents precede descendants so parent assignment invalidation cannot
        // erase a child certificate just emitted from the same definite store.
        for (if (diagnostic_address_only) use.fields[0..0] else use.fields[0..use.field_count]) |field| {
            const path = if (prefix != null) try self.allocDottedPath(prefix, field) else field;
            try self.appendStmt(block, .{
                .kind = .{ .field_assign = .{ .parent = id, .name = path, .rhs_kind = .plain, .defined = true } },
                .pos = pos,
                .end_pos = end,
            });
        }
        for (use.undefined_fields[0..use.undefined_field_count]) |field| {
            const path = if (field.len == 0) diagnostic_prefix orelse "" else
                if (diagnostic_prefix != null) try self.allocDottedPath(diagnostic_prefix, field) else field;
            try self.appendStmt(block, .{
                .kind = .{ .field_assign = .{
                    .parent = diagnostic_id,
                    .name = path,
                    .rhs_kind = .undef,
                    .diagnostic_only = true,
                } },
                .pos = pos,
                .end_pos = end,
            });
        }
    }

    /// Substitute projected reads without certifying pointer pointees.
    fn selectedWrittenRead(self: *Builder, read: file_cache.FileCache.WrittenRead, inputs: *[8]?cfg_types.ValueInput, kind: *ExprKind) LoweringError!void {
        var operations: [32]Ast.Node.Index = undefined;
        var count: usize = 0;
        var node = read.node;
        while (true) {
            const base: Ast.Node.Index = switch (read.tree.nodeTag(node)) {
                .grouped_expression => read.tree.nodeData(node).node_and_token[0],
                .deref => read.tree.nodeData(node).node,
                .field_access => read.tree.nodeData(node).node_and_token[0],
                .array_access => read.tree.nodeData(node).node_and_node[0],
                else => break,
            };
            if (read.tree.nodeTag(node) != .grouped_expression) {
                if (count == operations.len) return;
                operations[count] = node;
                count += 1;
            }
            node = base;
        }
        var actual = initShapeNode(self, read.argument);
        var source: ?ExprKind = null;
        var addressed = false;
        var offset: u64 = 0;
        while (count != 0) {
            count -= 1;
            const operation = operations[count];
            const tag = read.tree.nodeTag(operation);
            if (source == null) {
                if (tag == .deref and self.tree.nodeTag(actual) == .address_of) {
                    actual = initShapeNode(self, self.tree.nodeData(actual).node);
                    continue;
                }
                if (tag == .field_access) {
                    const token = read.tree.nodeData(operation).node_and_token[1];
                    const raw = read.tree.tokenSlice(token);
                    const name = if (std.mem.startsWith(u8, raw, "@\""))
                        self.fieldLiteralNameInTree(read.tree, token, false) orelse return
                    else raw;
                    if (self.tree.fullSlice(actual) != null and
                        (std.mem.eql(u8, name, "ptr") or std.mem.eql(u8, name, "len"))) return;
                    var buffer: [2]Ast.Node.Index = undefined;
                    if (self.tree.fullStructInit(&buffer, actual)) |literal| {
                        var selected: ?Ast.Node.Index = null;
                        for (literal.ast.fields) |value| {
                            const field = self.fieldInitName(value) orelse continue;
                            if (std.mem.eql(u8, field, name)) {
                                selected = value;
                                break;
                            }
                        }
                        actual = selected orelse {
                            if (self.constructorHasUndefinedDefault(actual, name)) kind.* = .undef;
                            return;
                        };
                        continue;
                    }
                }
                if (self.tree.nodeTag(actual) == .address_of) {
                    actual = initShapeNode(self, self.tree.nodeData(actual).node);
                    addressed = true;
                }
                if (self.tree.fullSlice(actual)) |slice| {
                    offset = self.integerValue(slice.ast.start) orelse 0;
                    actual = slice.ast.sliced;
                }
                source = self.classifySourceProjection(actual, 0);
                if (source == null) {
                    if (self.hasRuntimeUndefinedLiteral(actual)) kind.* = .undef;
                    return;
                }
            }
            const current = source.?;
            const parent = switch (current) {
                .copy_of => |local| local,
                .field_copy_of => |field| field.parent,
                else => return,
            };
            if (tag == .deref) {
                if (addressed) {
                    addressed = false;
                } else {
                    source = .{ .field_copy_of = .{
                        .parent = parent,
                        .name = if (current == .field_copy_of)
                            try self.allocDottedPath(current.field_copy_of.name, "*")
                        else "",
                    } };
                }
            } else if (tag == .field_access) {
                const token = read.tree.nodeData(operation).node_and_token[1];
                const raw = read.tree.tokenSlice(token);
                const name = if (std.mem.startsWith(u8, raw, "@\""))
                    self.fieldLiteralNameInTree(read.tree, token, false) orelse return
                else raw;
                source = .{ .field_copy_of = .{
                    .parent = parent,
                    .name = try self.allocDottedPath(
                        if (current == .field_copy_of and current.field_copy_of.name.len != 0) current.field_copy_of.name else null,
                        name,
                    ),
                } };
            } else {
                const index_node = read.tree.nodeData(operation).node_and_node[1];
                const index: ?u64 = if (read.tree.nodeTag(index_node) == .number_literal)
                    std.fmt.parseInt(u64, read.tree.tokenSlice(read.tree.nodeMainToken(index_node)), 0) catch null
                else null;
                if (current == .copy_of) {
                    const selected: cfg_types.ValueInput = .{ .indexed = .{
                        .array = parent,
                        .index = if (index) |value| .{ .constant = value +| offset } else .unknown,
                    } };
                    for (inputs) |*entry| if (entry.* == null) {
                        entry.* = selected;
                        break;
                    };
                    return;
                }
                if (index) |value| {
                    const path = try std.fmt.allocPrint(self.gpa, "{s}[{d}]", .{ current.field_copy_of.name, value +| offset });
                    errdefer self.gpa.free(path);
                    try self.owned_paths.append(self.gpa, path);
                    source = .{ .field_copy_of = .{ .parent = parent, .name = path } };
                }
            }
        }
        if (source) |value| {
            const selected: cfg_types.ValueInput = switch (value) {
                .copy_of => |local| .{ .local = local },
                .field_copy_of => |field| .{ .field = .{ .parent = field.parent, .name = field.name } },
                else => return,
            };
            for (inputs) |*entry| if (entry.* == null) {
                entry.* = selected;
                break;
            };
        } else {
            if (self.hasRuntimeUndefinedLiteral(actual)) kind.* = .undef;
            var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
            _ = self.selectedValueInputs(actual, &selected, false);
            _ = mergeSelectedValueInputs(inputs, selected);
        }
    }

    /// Preserve the callee result and its stores in the same CFG partition.
    /// Later assignments to the result then invalidate the relation naturally.
    fn emitBooleanOutResult(self: *Builder, cur: *BlockId, result: LocalId, expression: Ast.Node.Index) LoweringError!void {
        const cache = self.cache orelse return;
        const tree = self.tree;
        var call_node = expression;
        while (tree.nodeTag(call_node) == .grouped_expression) call_node = tree.nodeData(call_node).node_and_token[0];
        var buffer: [2]Ast.Node.Index = undefined;
        _ = zls_resolver_mod.TypeResolver.CallOperands.full(tree, &buffer, call_node) orelse return;
        var proved = false;
        var token = tree.firstToken(call_node);
        const last = tree.lastToken(call_node);
        while (token <= last) : (token += 1) {
            if (tree.tokenTag(token) != .identifier) continue;
            for ([_]bool{ true, false }) |expected| {
                const use = (try cache.addressUseOnBooleanAt(token, expected)) orelse continue;
                if (use.call_node != call_node) continue;
                const root = tokens.rootIdentifier(tree, use.operand) orelse continue;
                const id = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(root))) orelse continue;
                if (self.localCanBeStored(id)) proved = true;
            }
        }
        if (!proved) return;
        const success = try self.newBlock();
        const failure = try self.newBlock();
        const merge = try self.newBlock();
        try self.addEdge(cur.*, success);
        try self.addEdge(cur.*, failure);
        for ([_]BlockId{ success, failure }, [_]bool{ true, false }) |block, value| {
            try self.appendStmt(block, .{
                .kind = .{ .assign = .{ .target = result, .rhs_kind = .{ .boolean = .{ .constant = value } }, .value_defined = true } },
                .pos = self.posOf(expression),
                .end_pos = self.endPosOf(expression),
            });
        }
        try self.emitAddressOutputs(success, call_node, true);
        try self.emitAddressOutputs(failure, call_node, false);
        try self.addEdge(success, merge);
        try self.addEdge(failure, merge);
        cur.* = merge;
    }

    fn lowerCallStmt(self: *Builder, call_node: Ast.Node.Index, cur: *BlockId) !void {
        // Detect arena.deinit() patterns; otherwise emit nothing
        // (call has no side-effect from our pov).
        const tree = self.tree;
        try self.invalidateCallAliases(call_node, cur.*);
        const first = tree.firstToken(call_node);
        const last = tree.lastToken(call_node);
        const start = tree.tokens.items(.start)[first];
        const last_start = tree.tokens.items(.start)[last];
        const last_len = tree.tokenSlice(last).len;
        const end: usize = last_start + last_len;
        const text = tree.source[start..end];

        // Interior-pointer destructor check.  When the receiver is
        // a local registered as a for-loop pointer-capture into a
        // container (`for (entries.items) |*r|`), calling a
        // destructor-shape method on it is UB under typical
        // allocators — the pointer isn't a fresh allocation.
        // Emits a diagnostic in transfer; the rest of lowerCallStmt
        // continues to fire (heap_free, etc.) so cascading
        // diagnostics still surface.
        if (self.interiorPointerDestructor(call_node)) |info| {
            try self.appendStmt(cur.*, .{
                .kind = .{ .interior_pointer_destroy = .{
                    .receiver = info.receiver,
                    .container = info.container,
                } },
                .pos = self.posOf(call_node),
                .end_pos = self.endPosOf(call_node),
            });
        }

        if (anyPatternMatches(text, self.config.arena_kill_patterns)) {
            const recv_local = self.firstIdentifierLocal(text) orelse {
                try self.appendStmt(cur.*, .{
                    .kind = .{ .lowering_gap = .{ .note = "deinit-no-receiver", .may_assign_locals = false } },
                    .pos = self.posOf(call_node),
                    .end_pos = self.endPosOf(call_node),
                });
                return;
            };
            try self.appendStmt(cur.*, .{
                .kind = .{ .arena_kill = .{ .arena_local = recv_local } },
                .pos = self.posOf(call_node),
                .end_pos = self.endPosOf(call_node),
            });
            // For value-typed receivers with their own `deinit`
            // (e.g. `Utf8.deinit` annotated `@takes ownership(self)`),
            // fall through so the @takes / R10 checks below get a
            // chance.  The arena_kill emitted above is a no-op at
            // transfer time when the receiver's origin isn't .arena.
            const hint = self.locals.items[@intFromEnum(recv_local)].init_hint;
            if (hint == .arena_local or hint == .arena_allocator) {
                return;
            }
        }

        if (anyPatternMatches(text, self.config.heap_free_patterns)) {
            // `<recv>.destroy(<allocator>)` — struct-method shape
            // where the method frees the receiver and takes the
            // allocator as an arg.  Inverse of `allocator.destroy(p)`.
            // Must check before the standard `.destroy(p)` path so we
            // don't misinterpret the allocator-arg as the freed thing.
            if (self.destroyReceiverFreed(call_node)) |target| {
                switch (target) {
                    .local => |freed| {
                        try self.appendStmt(cur.*, .{
                            .kind = .{ .heap_free = .{ .freed_local = freed, .fallback_hid = blk_h: {
                                const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                                self.next_heap += 1;
                                break :blk_h h;
                            } } },
                            .pos = self.posOf(call_node),
                            .end_pos = self.endPosOf(call_node),
                        });
                    },
                    .field => |fref| {
                        try self.appendStmt(cur.*, .{
                            .kind = .{ .field_heap_free = .{ .parent = fref.parent, .name = fref.name, .fallback_hid = blk_hid: {
                                const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                                self.next_heap += 1;
                                break :blk_hid h;
                            } } },
                            .pos = self.posOf(call_node),
                            .end_pos = self.endPosOf(call_node),
                        });
                    },
                }
                return;
            }
            if (self.heapFreedLocal(call_node)) |freed| {
                try self.appendStmt(cur.*, .{
                    .kind = .{ .heap_free = .{
                        .freed_local = freed,
                        .fallback_hid = blk_h: {
                            const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                            self.next_heap += 1;
                            break :blk_h h;
                        },
                        .allocator_local = self.allocReceiverLocal(call_node),
                    } },
                    .pos = self.posOf(call_node),
                    .end_pos = self.endPosOf(call_node),
                });
                return;
            }
            // `g.free(obj.field)` — field-level free.
            if (self.heapFreedField(call_node)) |fref| {
                try self.appendStmt(cur.*, .{
                    .kind = .{ .field_heap_free = .{ .parent = fref.field.parent, .name = fref.field.name, .fallback_hid = blk_hid: {
                        const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                        self.next_heap += 1;
                        break :blk_hid h;
                    } } },
                    .pos = self.posOf(fref.argument),
                    .end_pos = self.endPosOf(fref.argument),
                });
                return;
            }
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "free-untracked-arg", .may_assign_locals = false } },
                .pos = self.posOf(call_node),
                .end_pos = self.endPosOf(call_node),
            });
            return;
        }

        // Whole-local and field releases share the exact normal-return channel.
        const success_selected = self.callReturnsWithoutError(call_node);
        if (success_selected and try self.applyFieldEffects(call_node, .normal_success, cur)) {
            try self.emitSuccessfulCallOutputs(cur.*, call_node);
            return;
        }

        // THE SOURCE SIDE IS READ, and the credit for the destination
        // must not swallow that read.  Crediting first made
        // `@memcpy(buf[0..], buf[0..])` the INITIALISATION of a defined
        // array — a copy of bytes nothing wrote turned into a definition
        // — and lost a `@memcpy` whose source had already been freed,
        // because the early return skipped the walk entirely.  The reads
        // go out first, against the state as it stands, and the
        // destination is initialised after them.
        try self.emitUsesInExpr(call_node, cur.*, null);
        if (success_selected) try self.emitSuccessfulCallOutputs(cur.*, call_node);
        try self.emitBuiltinPayloadWrite(cur.*, call_node);

        // A WRITE-FIRST BUILTIN THAT FILLS THE WHOLE ARRAY is not an
        // untracked call: `@memset(buf[0..], 0)` and `@memcpy(buf[0..],
        // src)` store every element of `buf`, so the array is defined
        // from here on and a later element read of it is a read of
        // initialized storage. Explicit prefix fills carry narrower coverage;
        // they must not credit elements beyond their count.
        if (self.builtinArrayMemsetPrefix(call_node)) |prefix| {
            if (prefix.count == .local) {
                try self.appendStmt(cur.*, .{
                    .kind = .{ .use = .{ .local = prefix.count.local.local } },
                    .pos = self.posOf(call_node),
                    .end_pos = self.endPosOf(call_node),
                });
            }
            try self.appendStmt(cur.*, .{
                .kind = .{ .array_memset_prefix = prefix },
                .pos = self.posOf(call_node),
                .end_pos = self.endPosOf(call_node),
            });
        } else if (self.builtinWholeArrayFill(call_node)) |filled| {
            try self.appendStmt(cur.*, .{
                .kind = .{ .array_complete = .{ .array = filled } },
                .pos = self.posOf(call_node),
                .end_pos = self.endPosOf(call_node),
            });
        } else {
            // Untracked calls preserve unexposed locals. Address and alias
            // operands already emitted targeted mutation invalidation.
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "call-untracked", .may_assign_locals = false } },
                .pos = self.posOf(call_node),
                .end_pos = self.endPosOf(call_node),
            });
        }

        // If the callee is annotated/inferred `noreturn`, the call
        // diverges — terminate this block (matches the treatment of
        // `unreachable` / `@panic`).
        if (self.callReturnsNoreturn(call_node)) {
            cur.* = try self.newBlock();
        }
    }

    /// Only a resolved noreturn type proves that a call cannot resume.
    /// Unknown types and error unions with a noreturn payload remain conservative.
    fn callReturnsNoreturn(self: *Builder, call_node: Ast.Node.Index) bool {
        const frame = self.integerResolutionFrame() orelse return false;
        if (self.queryOrUnknown(
            zls_resolver_mod.TypeResolver.ActualType,
            frame.typeOfNode(call_node),
        )) |result| return frame.resolver.typeTag(result) == .noreturn;
        // Generic argument inference can fail without making the reached
        // function's declared result unknown. Resolve that declaration, not
        // a same-spelled callable, and retain its container bindings.
        var call_buffer: [1]Ast.Node.Index = undefined;
        const call = self.tree.fullCall(&call_buffer, call_node) orelse return false;
        const resolution = frame.functionReference(call.ast.fn_expr) catch |err| {
            self.noteResolutionError(err);
            return false;
        };
        const reference = switch (resolution) {
            .function => |reference| reference,
            else => return false,
        };
        const declaration = tokens.enclosingFnDecl(reference.tree, reference.fn_token) orelse return false;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(reference.tree, &proto_buffer, declaration) orelse return false;
        if (proto.ast.fn_token != reference.fn_token) return false;
        const return_node = proto.ast.return_type.unwrap() orelse return false;
        const first = reference.tree.firstToken(return_node);
        // Inferred !T is not T: an error union may still return an error.
        if (first > 0 and reference.tree.tokenTag(first - 1) == .bang) return false;
        const callee_frame = frame.resolver.frameForFunction(reference);
        const result = self.queryOrUnknown(
            zls_resolver_mod.TypeResolver.ActualType,
            callee_frame.typeOfNode(return_node),
        ) orelse return false;
        return callee_frame.resolver.typeTag(result) == .noreturn;
    }

    /// Does the callee's declared parameter 0 name the receiver — i.e.
    /// is this an instance call (`holder.dispose(gpa, item)`)?
    ///
    /// `<recv>.<method>(...)` alone can't answer it: `lib.dispose(gpa,
    /// b)` spells a top-level fn of an imported file, and `lib` is a
    /// container, not a value.  The receiver's own DECLARATION answers
    /// it — a tracked local is a value, an `@import` alias or a type
    /// declared in this file is a container.  Null when the receiver is
    /// neither, so the caller keeps its existing mapping.
    fn receiverSpendsParamZero(self: *Builder, recv_node: Ast.Node.Index) ?bool {
        const tree = self.tree;
        if (tree.nodeTag(recv_node) != .identifier) return null;
        const name = tree.tokenSlice(tree.nodeMainToken(recv_node));
        // A local in this function is a value: `holder.dispose(...)`
        // spends param 0 on `holder`, and a local that shadows an
        // import alias is a value too.
        if (self.name_to_local.get(name) != null) return true;
        if (self.importAliasPath(name) != null) return false;
        if (self.self_type) |owner| {
            if (std.mem.eql(u8, owner, name)) return false;
        }
        const cache = self.cache orelse return null;
        const model = self.modelOrNull(cache) orelse return null;
        if (model.hasType(name)) return false;
        return null;
    }

    /// Import path of the file-level `@import` alias `alias`, or null
    /// when this file declares no such alias.  Builds the alias table
    /// on first use.
    fn importAliasPath(self: *Builder, alias: []const u8) ?[]const u8 {
        // `.{}` on an optional is null, not an empty map — the table
        // has to be spelled out or the lookup below unwraps nothing.
        if (self.import_aliases == null) {
            self.import_aliases = std.StringHashMapUnmanaged([]const u8){};
            self.collectImportAliases() catch |err| self.noteResolutionError(err);
        }
        return self.import_aliases.?.get(alias);
    }

    /// Record every file-level `const NAME = @import("path")`.
    fn collectImportAliases(self: *Builder) !void {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        for (tree.rootDecls()) |node| {
            const decl = tree.fullVarDecl(node) orelse continue;
            const name_tok = decl.ast.mut_token + 1;
            if (name_tok >= tags.len or tags[name_tok] != .identifier) continue;
            const init = decl.ast.init_node.unwrap() orelse continue;
            // Read by the one reader every caller uses, over the
            // initializer's ACTUAL AST span: a trailing-comma import
            // is read like the plain one, and only a call carrying a
            // SECOND argument spells no single path here — naming one
            // from its head alone would invent it.
            const path = tokens.importLiteralFromTokens(tree, tree.nodeMainToken(init), tree.lastToken(init)) orelse continue;
            try self.import_aliases.?.put(self.gpa, tree.tokenSlice(name_tok), path);
        }
    }

    /// Return a receiver whose storage is released on a normal-return path.
    /// Sub-field cleanup and error-only cleanup do not destroy its storage.
    fn normalFreedReceiver(self: *Builder, call_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const full = tree.fullCall(&buf, call_node) orelse return null;
        const callee = full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const receiver = tree.nodeData(callee).node_and_token[0];
        if (tree.nodeTag(receiver) != .identifier) return null;
        const local = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(receiver))) orelse return null;
        const cache = self.cache orelse return null;
        const summary = self.actualCallSummaryForCallee(cache, full) orelse return null;
        for (summary.normal_success_definite_freed_paths) |path| {
            if (path.param == 0 and path.path.len == 0) return local;
        }
        for (summary.normal_success_may_freed_paths) |path| {
            if (path.param == 0 and path.path.len == 0) return local;
        }
        return null;
    }

    /// Certainty for a cleanup path on the selected function outcome.
    const FreeCertainty = enum { definite, possible };

    fn containsFreeField(fields: []const fn_summary.FieldFree, candidate: fn_summary.FieldFree) bool {
        for (fields) |field| {
            if (field.param == candidate.param and std.mem.eql(u8, field.field, candidate.field)) return true;
        }
        return false;
    }

    fn containsParamPath(paths: []const fn_summary.ParamPath, candidate: fn_summary.ParamPath) bool {
        for (paths) |path| {
            if (path.param == candidate.param and std.mem.eql(u8, path.path, candidate.path)) return true;
        }
        return false;
    }

    /// Resolve the exact call declaration and its summary. Method/type-name
    /// lookups are not sufficient across imports or same-named declarations.
    fn actualCallSummaryForCallee(
        self: *Builder,
        cache: *file_cache.FileCache,
        call: Ast.full.Call,
    ) ?fn_summary.FnSummary {
        const token = fresh_storage.calleeQueryToken(self.tree, call);
        const frame = if (self.zls) |resolver| resolver.resolutionFrame() else null;
        const actual = cache.actualCallSummaryAt(token, frame) catch |err| {
            self.noteResolutionError(err);
            return null;
        };
        const resolved = actual orelse return null;
        return cache.summaryOfResolvedMethod(resolved.callee) catch |err| {
            self.noteResolutionError(err);
            return null;
        };
    }

    const ActualLocalPath = struct {
        local: LocalId,
        expression: Ast.Node.Index,
        prefix_len: usize,
    };

    /// Resolve a caller-side local actual without allocating its field prefix.
    fn actualLocalPath(self: *Builder, node: Ast.Node.Index) ?ActualLocalPath {
        const tree = self.tree;
        return switch (tree.nodeTag(node)) {
            .identifier => blk: {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                const local = self.name_to_local.get(name) orelse return null;
                break :blk .{ .local = local, .expression = node, .prefix_len = 0 };
            },
            .grouped_expression => blk: {
                var actual = self.actualLocalPath(tree.nodeData(node).node_and_token[0]) orelse return null;
                actual.expression = node;
                break :blk actual;
            },
            .address_of, .deref => blk: {
                var actual = self.actualLocalPath(tree.nodeData(node).node) orelse return null;
                actual.expression = node;
                break :blk actual;
            },
            .field_access => blk: {
                const pair = tree.nodeData(node).node_and_token;
                var actual = self.actualLocalPath(pair[0]) orelse return null;
                if (actual.prefix_len != 0) actual.prefix_len += 1;
                actual.prefix_len += tree.tokenSlice(pair[1]).len;
                actual.expression = node;
                break :blk actual;
            },
            else => null,
        };
    }

    fn writeActualPathPrefix(
        self: *Builder,
        node: Ast.Node.Index,
        bytes: []u8,
        offset: *usize,
    ) void {
        const tree = self.tree;
        switch (tree.nodeTag(node)) {
            .identifier => {},
            .grouped_expression => self.writeActualPathPrefix(tree.nodeData(node).node_and_token[0], bytes, offset),
            .address_of, .deref => self.writeActualPathPrefix(tree.nodeData(node).node, bytes, offset),
            .field_access => {
                const pair = tree.nodeData(node).node_and_token;
                self.writeActualPathPrefix(pair[0], bytes, offset);
                if (offset.* != 0) {
                    bytes[offset.*] = '.';
                    offset.* += 1;
                }
                const field = tree.tokenSlice(pair[1]);
                @memcpy(bytes[offset.*..][0..field.len], field);
                offset.* += field.len;
            },
            else => unreachable,
        }
    }

    /// Compose an actual's field prefix and callee path into CFG-owned storage.
    fn allocActualDottedPath(
        self: *Builder,
        actual: ActualLocalPath,
        leaf: []const u8,
    ) LoweringError![]const u8 {
        if (actual.prefix_len == 0) return leaf;
        const separator_len: usize = if (leaf.len == 0) 0 else 1;
        const bytes = try self.gpa.alloc(u8, actual.prefix_len + separator_len + leaf.len);
        errdefer self.gpa.free(bytes);
        var offset: usize = 0;
        self.writeActualPathPrefix(actual.expression, bytes, &offset);
        std.debug.assert(offset == actual.prefix_len);
        if (leaf.len != 0) {
            bytes[offset] = '.';
            offset += 1;
            @memcpy(bytes[offset..][0..leaf.len], leaf);
        }
        try self.owned_paths.append(self.gpa, bytes);
        return bytes;
    }

    /// Best-effort type name for a node used as a method-call
    /// receiver.  Looks up the node's identifier in name_to_local to
    /// get a known local's declared type.  Returns null when the
    /// node isn't a tracked local or doesn't have a type annotation
    /// — callers fall back to bare-name lookup.
    fn receiverTypeOfNode(self: *Builder, node: Ast.Node.Index) ?[]const u8 {
        const tree = self.tree;
        // Fast path: bare-identifier locals with a known declared type.
        if (tree.nodeTag(node) == .identifier) {
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            if (self.name_to_local.get(name)) |lid| {
                if (self.locals.items[@intFromEnum(lid)].type_name) |t| return t;
                // ZLS fallback for this identifier — resolve and STORE the
                // result in the local so every subsequent call on the same
                // receiver skips ZLS entirely.
                if (self.zls) |z| {
                    if (self.queryOrUnknown([]const u8, z.typeReferenceOfNode(node))) |ty| {
                        self.locals.items[@intFromEnum(lid)].type_name = ty;
                        return ty;
                    }
                }
                return null;
            }
        }
        // Fallback: ask ZLS to resolve the node's type.  Catches
        // for-loop captures (`for (xs) |*x| x.method(...)`), locals
        // init'd from method-call returns (`var w = makeWalker()`),
        // and cross-module aliases (`const W = ns.factory.Type`)
        // where zbc's AST-only tracking can't see the type.
        if (self.zls) |z| {
            return self.queryOrUnknown([]const u8, z.typeReferenceOfNode(node));
        }
        return null;
    }

    /// Where a call's callee is DECLARED, in which file, and in which
    /// compilation.  Null when the declaration cannot be pinned down —
    /// which includes the ambiguous case: a free function whose name
    /// this file declares twice has no single signature, so no single
    /// answer can be attributed to it.
    ///
    /// The module is part of the identity, not decoration: the same
    /// source file compiled in two environments is two declarations,
    /// and anything that resolves FURTHER from here has to ask in the
    /// environment the declaration belongs to.  Carrying the tree
    /// without it is what makes a later lookup quietly answer about
    /// this file's own imports instead.
    const CalleeDecl = struct {
        tree: *const Ast,
        fn_decl: Ast.Node.Index,
        module: type_engine.ModuleId,
        /// The type the callee is declared ON, when the call site named
        /// it as a method of a receiver this file could resolve.  It is
        /// what a result type named `DocumentStore.Handle` has to be
        /// read against: that name means nothing from the analysed
        /// file's scope and everything from the file the declaration
        /// was written in.  Null for a free function, which has no
        /// owner to read a name against.
        owner: ?file_cache.FileCache.ResolvedType = null,
    };

    fn calleeDeclOfCall(self: *Builder, call_node: Ast.Node.Index) ?CalleeDecl {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buf, call_node) orelse return null;
        const callee = call.ast.fn_expr;
        switch (tree.nodeTag(callee)) {
            .field_access => {
                const recv = tree.nodeData(callee).node_and_token[0];
                const method = tree.tokenSlice(tree.nodeData(callee).node_and_token[1]);
                // The receiver's TYPE is what says which declaration is
                // being called, so an unreadable receiver type answers
                // nothing rather than guessing from the method name.
                // Asked as the DECLARATION itself, not as its name: a
                // receiver reached through another file's fields has no
                // name this file could look up again, and the name that
                // did resolve would answer about the wrong scope.
                const owner = self.receiverResolvedType(recv) orelse return null;
                const decl = owner.info.findMethod(method) orelse return null;
                return .{
                    .tree = owner.model.tree,
                    .fn_decl = decl.fn_decl,
                    .module = owner.module,
                    .owner = owner,
                };
            },
            .identifier => {
                // A local or parameter can shadow a declaration of this name.
                // Its callable value needs semantic resolution, not a lookup
                // of an unrelated same-spelled function in the file.
                if (self.name_to_local.contains(tree.tokenSlice(tree.nodeMainToken(callee)))) return null;
                const name = self.resolveBoundCallee(tree.tokenSlice(tree.nodeMainToken(callee)));
                const cache = self.cache orelse return null;
                const model = self.modelOrNull(cache) orelse return null;
                var found: ?Ast.Node.Index = null;
                for (model.fns) |info| {
                    if (!std.mem.eql(u8, info.name, name)) continue;
                    if (found != null) return null;
                    found = info.fn_decl;
                }
                const fn_decl = found orelse return null;
                return .{ .tree = model.tree, .fn_decl = fn_decl, .module = cache.module_id };
            },
            else => return null,
        }
    }

    /// The type a method receiver expression HAS, as the DECLARATION
    /// itself rather than as a name.
    ///
    /// [receiverTypeOfNode] answers a name, which is only usable while
    /// that name means the same thing from here as it did where it was
    /// read.  For `resolver.ctx` it does not: the field's declared type
    /// is named in the file the FIELD was declared in, so the bare name
    /// either fails to resolve from here or — worse — resolves to an
    /// unrelated type this file does declare.  Every question that has
    /// to resolve FURTHER than the receiver asks this instead, because a
    /// declaration carries the file, path and module the further lookup
    /// has to be asked in.
    ///
    /// Both receiver spellings start from a tracked local's declared
    /// type, and the field hop goes through `fieldType`, so the answer
    /// keeps its declaring file.  An untracked name, a local with no
    /// type and an unsupported shape are all plain misses: the caller
    /// stays unresolved, exactly as before.
    fn receiverResolvedType(self: *Builder, recv: Ast.Node.Index) ?file_cache.FileCache.ResolvedType {
        const tree = self.tree;
        const cache = self.cache orelse return null;
        const base: Ast.TokenIndex = switch (tree.nodeTag(recv)) {
            .identifier => tree.nodeMainToken(recv),
            .field_access => hop: {
                const fa = tree.nodeData(recv).node_and_token;
                if (tree.nodeTag(fa[0]) != .identifier) return null;
                break :hop tree.nodeMainToken(fa[0]);
            },
            else => return null,
        };
        const lid = self.name_to_local.get(tree.tokenSlice(base)) orelse return null;
        const type_name = self.locals.items[@intFromEnum(lid)].type_name orelse return null;
        const owner = cache.resolvedTypePathAcrossImports(type_name) orelse return null;
        if (tree.nodeTag(recv) != .field_access) return owner;
        const field_tok = tree.nodeData(recv).node_and_token[1];
        return cache.fieldType(owner, tree.tokenSlice(field_tok));
    }

    /// True when `call_node` is a call whose CALLEE'S OWN DECLARATION
    /// says it hands back a pointer, and the binding therefore holds one.
    ///
    /// This is the proof that needs no callee NAME and no receiver
    /// spelling: `fn sourceHandle(self: *Ctx, p: []const u8) !*Handle`
    /// binds a `*Handle` after `catch`, so `&handle.tree` addresses the
    /// handle's own storage — the context's — and not this frame.
    /// The declaration, not a method name or the receiver's pointer type,
    /// proves the result type.
    ///
    /// Two constraints keep it sound:
    ///
    ///  - It only ever answers TRUE.  A callee whose declared return
    ///    type is a type parameter, an opaque generic, or anything this
    ///    file cannot read answers nothing, so the questions below it —
    ///    and the frame attribution — keep their say.
    ///  - An error union counts only when the binding ACCEPTED the
    ///    error.  `const h = try f();` holds the payload, and the
    ///    payload of `!*Handle` is a pointer; a binding that took the
    ///    whole `E!T` holds an error union, which is not a pointer and
    ///    whose `&h.tree` would not compile.  zbc reads source that
    ///    need not compile, so that distinction is carried rather than
    ///    assumed away — `accepted_error` is what carries it, and
    ///    without it an `!*T` declaration would read as a pointer for a
    ///    binding that holds no pointer at all.
    ///
    /// A `*T` return stays a pointer under every instantiation of `T`,
    /// so a generic callee is decided by its declaration too; the
    /// converse — a `T` return instantiated as a pointer — is one this
    /// deliberately does not claim.
    fn declaredCallYieldsPointer(self: *Builder, call_node: Ast.Node.Index, accepted_error: bool) bool {
        const decl = self.calleeDeclOfCall(call_node) orelse return false;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = decl.tree.fullFnProto(&proto_buf, decl.fn_decl) orelse return false;
        const return_node = proto.ast.return_type.unwrap() orelse return false;
        const first = decl.tree.firstToken(return_node);
        const last = decl.tree.lastToken(return_node);
        const tags = decl.tree.tokens.items(.tag);
        if (typeRangeIsPointerValue(tags, first, last)) return true;
        if (!accepted_error) return false;
        return errorUnionPayloadIsPointer(tags, first, last);
    }

    /// What a callee's own DECLARATION says a call's result holds: the
    /// type spelled as that declaration writes it, together with the
    /// type the callee was declared ON.  This is what makes an inferred
    /// binding's field chain readable without the resolver — `const
    /// handle = ctx.sourceHandle(path) catch …;` writes no type at the
    /// declaration, so nothing about `&handle.document.tree` can be
    /// read off the source; every question about it starts from what
    /// `sourceHandle` declared it hands back and from the fields
    /// written in that type's own body.
    ///
    /// The two constraints are the ones `declaredCallYieldsPointer`
    /// already works under, inherited rather than restated:
    ///
    ///  - It answers only what a declaration in reach SAYS.  A callee
    ///    this file cannot read, or a return type that names nothing, is
    ///    null, and the field walk and the resolver keep their say.
    ///  - `E!T` counts only when the binding ACCEPTED the error, since
    ///    that is the only reading in which the binding holds `T` at
    ///    all.  A binding that took the whole union stays untyped,
    ///    which is where it was before.
    ///
    /// `owner` is what makes the `name` usable at all: `DocumentStore
    /// .Handle` is spelled in one file and has to be READ in that same
    /// file's scope, which is not the scope `name` alone would be
    /// resolved in.
    const DeclaredResult = struct {
        name: []const u8,
        owner: ?file_cache.FileCache.ResolvedType,
    };

    fn declaredResultOfInit(self: *Builder, init_node: Ast.Node.Index) ?DeclaredResult {
        const tree = self.tree;
        const peel = initPeelNode(self, init_node, .declared_type);
        switch (tree.nodeTag(peel.node)) {
            .call, .call_one, .call_comma, .call_one_comma => {},
            else => return null,
        }
        const decl = self.calleeDeclOfCall(peel.node) orelse return null;
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = decl.tree.fullFnProto(&proto_buf, decl.fn_decl) orelse return null;
        const return_node = proto.ast.return_type.unwrap() orelse return null;
        const first = decl.tree.firstToken(return_node);
        const last = decl.tree.lastToken(return_node);
        const payload = errorUnionPayloadFirst(decl.tree.tokens.items(.tag), first, last) orelse
            return .{
                .name = tokens.typeNameFromTokens(decl.tree, first, last) orelse return null,
                .owner = decl.owner,
            };
        if (!peel.accepted_error) return null;
        return .{
            .name = tokens.typeNameFromTokens(decl.tree, payload, last) orelse return null,
            .owner = decl.owner,
        };
    }

    /// One mapped callee field release for the selected cleanup outcome.
    const CalleeFieldFree = struct {
        parent: LocalId,
        field: []const u8,
        certainty: FreeCertainty,
        entry_only: bool = false,
        invalidate_only: bool = false,
    };

    /// Map selected-outcome frees to caller locals. The return value says
    /// whether every effect was understood; an empty list is not evidence
    /// of no effect when it returns false.
    fn collectCalleeFieldFrees(
        self: *Builder,
        call_node: Ast.Node.Index,
        outcome: CleanupOutcome,
        gpa: std.mem.Allocator,
        out: *std.ArrayListUnmanaged(CalleeFieldFree),
    ) LoweringError!bool {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return false;

        const cache = self.cache orelse return false;
        const frame = if (self.zls) |resolver| resolver.resolutionFrame() else null;
        const actual = (try cache.actualCallSummaryAt(fresh_storage.calleeQueryToken(tree, call_full), frame)) orelse return false;
        const summary = (try cache.summaryOfResolvedMethod(actual.callee)) orelse return false;

        const definite_paths: []const fn_summary.ParamPath = switch (outcome) {
            .normal_success => summary.normal_success_definite_freed_paths,
            .error_return => summary.error_definite_freed_paths,
        };
        // MAY projections also include releases of old payloads after an
        // uncertified store. They do not identify the allocation currently
        // held at this path. Only a definite release can mint a dead identity;
        // exact conditional releases are replayed by applyStorageEffects.
        const may_paths: []const fn_summary.ParamPath = switch (outcome) {
            .normal_success => summary.normal_success_may_freed_paths,
            .error_return => summary.error_may_freed_paths,
        };
        const definite_fields: []const fn_summary.FieldFree = switch (outcome) {
            .normal_success => summary.normal_success_definite_free_fields,
            .error_return => summary.error_definite_free_fields,
        };
        const may_fields: []const fn_summary.FieldFree = switch (outcome) {
            .normal_success => summary.normal_success_may_free_fields,
            .error_return => summary.error_may_free_fields,
        };
        var complete = switch (outcome) {
            .normal_success => summary.normal_success_effects_complete,
            .error_return => summary.error_effects_complete,
        };

        for (definite_paths) |free| {
            try self.appendMappedCalleeFieldFree(
                actual,
                free.param,
                free.path,
                .definite,
                gpa,
                out,
                &complete,
            );
        }
        // A payload-only builtin can make the general cleanup summary
        // incomplete without changing a by-value pointer/slice header.
        // Recover an unconditional final release only when the source body
        // proves that every preceding statement is such a payload write and
        // every authenticated trace releases the same entry allocation.
        payload_release: {
            if (outcome != .normal_success or complete) break :payload_release;
            const callee_tree = actual.callee.tree;
            const body = tokens.bodyOf(callee_tree, actual.callee.declaration) orelse break :payload_release;
            var statements_buffer: [2]Ast.Node.Index = undefined;
            const statements = callee_tree.blockStatements(&statements_buffer, body) orelse break :payload_release;
            if (statements.len < 2) break :payload_release;
            var final_buffer: [1]Ast.Node.Index = undefined;
            const final_call = callee_tree.fullCall(&final_buffer, statements[statements.len - 1]) orelse break :payload_release;
            if (final_call.ast.params.len != 1) break :payload_release;
            const operand = final_call.ast.params[0];
            if (callee_tree.nodeTag(operand) != .identifier) break :payload_release;
            const formal_name = callee_tree.tokenSlice(callee_tree.nodeMainToken(operand));
            var proto_buffer: [1]Ast.Node.Index = undefined;
            const proto = tokens.fnProto(callee_tree, &proto_buffer, actual.callee.declaration) orelse break :payload_release;
            const parameter = fn_summary.paramIndex(callee_tree, proto, formal_name) orelse break :payload_release;
            for (statements[0 .. statements.len - 1]) |statement| {
                try cache.normalCleanupStorageWork(call_node, 1);
                var builtin_buffer: [2]Ast.Node.Index = undefined;
                const arguments = callee_tree.builtinCallParams(&builtin_buffer, statement) orelse break :payload_release;
                const builtin = callee_tree.tokenSlice(callee_tree.nodeMainToken(statement));
                if (!std.mem.eql(u8, builtin, "@memset") and !std.mem.eql(u8, builtin, "@memcpy")) break :payload_release;
                if (arguments.len != 2 or callee_tree.nodeTag(arguments[0]) != .identifier) break :payload_release;
                if (!std.mem.eql(u8, callee_tree.tokenSlice(callee_tree.nodeMainToken(arguments[0])), formal_name)) break :payload_release;
                switch (callee_tree.nodeTag(arguments[1])) {
                    .identifier, .number_literal => {},
                    else => break :payload_release,
                }
            }
            const alternatives = summary.normal_success_storage_outcomes;
            if (alternatives.len == 0) break :payload_release;
            for (alternatives) |alternative| {
                try cache.normalCleanupStorageWork(call_node, 1);
                if (alternative.operations.len != 1) break :payload_release;
                const operation = alternative.operations[0];
                if (operation.kind != .release_entry or operation.path.param != parameter or
                    operation.path.path.len != 0) break :payload_release;
            }
            try self.appendMappedCalleeFieldFree(actual, parameter, "", .definite, gpa, out, &complete);
        }
        for (may_paths) |free| {
            if (!containsParamPath(definite_paths, free)) complete = false;
        }
        for (definite_fields) |free| {
            try self.appendMappedCalleeFieldFree(
                actual,
                free.param,
                free.field,
                .definite,
                gpa,
                out,
                &complete,
            );
        }
        // Incomplete traces still retain positively observed entry releases.
        // Intersect exact identities across every exit, not the MAY union.
        const traces = switch (outcome) {
            .normal_success => summary.normal_success_storage_outcomes,
            .error_return => summary.error_storage_outcomes,
        };
        if (traces.len != 0) for (traces[0].operations) |candidate| {
            try cache.normalCleanupStorageWork(call_node, 1);
            if (candidate.kind != .release_entry or !candidate.identity_proved) continue;
            var every_exit = true;
            for (traces[1..]) |trace| {
                var found = false;
                for (trace.operations) |operation| {
                    try cache.normalCleanupStorageWork(call_node, 1 + @min(candidate.path.path.len, operation.path.path.len));
                    if (operation.kind == .release_entry and operation.identity_proved and
                        operation.path.param == candidate.path.param and
                        std.mem.eql(u8, operation.path.path, candidate.path.path)) found = true;
                }
                if (!found) every_exit = false;
            }
            if (!every_exit) continue;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try actual.callArgumentFor(cache, &argument_buffer, candidate.path.param)) orelse continue;
            const path = self.actualLocalPath(argument) orelse continue;
            try appendCalleeFieldFree(gpa, out, .{
                .parent = path.local,
                .field = try self.allocActualDottedPath(path, candidate.path.path),
                .certainty = .definite,
                .entry_only = candidate.path.path.len != 0,
            });
        };
        // A proved store invalidates the caller's current field binding
        // independently of whether any entry release can be credited.
        // Union stores across exits: retaining the old identity requires
        // proof that no reachable outcome replaces it.
        for (traces) |trace| {
            for (trace.operations) |operation| {
                try cache.normalCleanupStorageWork(call_node, 1);
                if (operation.kind != .replace) continue;
                var argument_buffer: [2]Ast.Node.Index = undefined;
                const argument = (try actual.callArgumentFor(cache, &argument_buffer, operation.path.param)) orelse continue;
                const path = self.actualLocalPath(argument) orelse continue;
                try appendCalleeFieldFree(gpa, out, .{
                    .parent = path.local,
                    .field = try self.allocActualDottedPath(path, operation.path.path),
                    .certainty = .definite,
                    .entry_only = true,
                    .invalidate_only = true,
                });
            }
        }
        for (may_fields) |free| {
            if (!containsFreeField(definite_fields, free)) complete = false;
        }
        return complete;
    }

    fn appendMappedCalleeFieldFree(
        self: *Builder,
        actual: file_cache.FileCache.ActualCallSummary,
        param: u32,
        field: []const u8,
        certainty: FreeCertainty,
        gpa: std.mem.Allocator,
        out: *std.ArrayListUnmanaged(CalleeFieldFree),
        complete: *bool,
    ) LoweringError!void {
        var buffer: [2]Ast.Node.Index = undefined;
        const arg_node = (try actual.callArgumentFor(self.cache.?, &buffer, param)) orelse {
            complete.* = false;
            return;
        };
        const actual_path = self.actualLocalPath(arg_node) orelse {
            complete.* = false;
            return;
        };
        const mapped_field = try self.allocActualDottedPath(actual_path, field);
        try appendCalleeFieldFree(gpa, out, .{
            .parent = actual_path.local,
            .field = mapped_field,
            .certainty = certainty,
        });
    }

    fn appendCalleeFieldFree(
        gpa: std.mem.Allocator,
        out: *std.ArrayListUnmanaged(CalleeFieldFree),
        release: CalleeFieldFree,
    ) error{OutOfMemory}!void {
        for (out.items) |*existing| {
            if (existing.parent != release.parent or !std.mem.eql(u8, existing.field, release.field)) continue;
            const invalidate_only = existing.invalidate_only and release.invalidate_only;
            const forget_current = existing.invalidate_only or release.invalidate_only;
            if (existing.invalidate_only and !release.invalidate_only) existing.* = release;
            if (release.certainty == .definite) existing.certainty = .definite;
            existing.invalidate_only = invalidate_only;
            existing.entry_only = forget_current or (existing.entry_only and release.entry_only);
            return;
        }
        try out.append(gpa, release);
    }

    /// For `<allocator>.free(p)` / `<allocator>.destroy(p)`, return the
    /// LocalId of `p` if it's a known local.  Null on any other shape.
    fn heapFreedLocal(self: *Builder, call_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        // Standard allocator.free(ptr) has exactly one argument.  Two-arg forms
        // like `alloc.free(backing_memory, slice)` (custom allocators) pass the
        // backing store as arg[0] — treating it as the freed thing is wrong.
        if (call_full.ast.params.len != 1) return null;
        // The callee must be a field-access call.  Guard against `obj.destroy(alloc)`
        // (receiver-freed pattern) falling through here when destroyReceiverFreed
        // can't resolve `obj` — without this check we'd wrongly mark the allocator
        // arg as the freed thing.  Same allocator-name / type_name logic as heapFreedField.
        const callee = call_full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const recv = tree.nodeData(callee).node_and_token[0];
        if (!self.exprLooksLikeAllocator(recv)) {
            const should_suppress: bool = if (tree.nodeTag(recv) == .identifier) blk: {
                const recv_name = tree.tokenSlice(tree.nodeMainToken(recv));
                if (self.name_to_local.get(recv_name)) |lid| {
                    const tn = self.locals.items[@intFromEnum(lid)].type_name;
                    if (tn) |t| {
                        break :blk !std.mem.endsWith(u8, t, "Allocator");
                    }
                    // Inferred type, non-allocator name: almost certainly not an
                    // allocator call — suppress to avoid false positives.
                    break :blk true;
                }
                // Receiver identifier not in scope (e.g. an if-capture that
                // destroyReceiverFreed couldn't resolve): don't treat the arg
                // as the freed value — the receiver is more likely the freed thing.
                break :blk true;
            } else false;
            if (should_suppress) return null;
        }
        const arg = call_full.ast.params[0];
        if (tree.nodeTag(arg) != .identifier) return null;
        const name = tree.tokenSlice(tree.nodeMainToken(arg));
        return self.name_to_local.get(name);
    }

    /// Retain the freed operand's span, not the allocator call's span.
    fn heapFreedField(self: *Builder, call_node: Ast.Node.Index) ?struct { field: FieldRef, argument: Ast.Node.Index } {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        // Standard allocator.free(ptr) has exactly one argument.  Two-arg forms
        // like `alloc.free(backing_memory, slice)` (custom allocators) pass the
        // backing store as arg[0] — treating it as the freed thing is wrong.
        if (call_full.ast.params.len != 1) return null;
        // The callee must be a field access (receiver.method).  Only treat
        // arg as the freed field when the receiver looks like an allocator.
        // Check by name first (fast); then by type_name ("Allocator" suffix) for
        // locals with known types (e.g. `g: std.mem.Allocator` where name is `g`).
        // When neither matches AND type is known → likely `obj.free(backing_store)`,
        // not an allocator free; suppress.  Unknown type → conservative, allow.
        const callee = call_full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const recv = tree.nodeData(callee).node_and_token[0];
        if (!self.exprLooksLikeAllocator(recv)) {
            const should_suppress: bool = if (tree.nodeTag(recv) == .identifier) blk: {
                const recv_name = tree.tokenSlice(tree.nodeMainToken(recv));
                if (self.name_to_local.get(recv_name)) |lid| {
                    const tn = self.locals.items[@intFromEnum(lid)].type_name;
                    if (tn) |t| {
                        // Known type: suppress unless it ends with "Allocator".
                        break :blk !std.mem.endsWith(u8, t, "Allocator");
                    }
                    // Unknown type AND non-allocator name: the pattern
                    // `obj.free(field)` where obj is an inferred-type
                    // value is more likely `obj` is freed (custom .free
                    // method) than an allocator — suppress to avoid FP.
                    break :blk true;
                }
                break :blk false; // local not found — conservative, allow
            } else false;
            if (should_suppress) return null;
        }
        const arg = call_full.ast.params[0];
        return .{ .field = self.fieldLhsFor(arg) orelse return null, .argument = arg };
    }

    const looksLikeAllocatorName = receiver_mod.isAllocatorishName;

    /// True iff `node` is an expression whose surface name suggests an
    /// allocator: bare identifier with an allocator-looking name, or a
    /// field access whose terminal field is allocator-looking.
    fn exprLooksLikeAllocator(self: *Builder, node: Ast.Node.Index) bool {
        const tree = self.tree;
        switch (tree.nodeTag(node)) {
            .identifier => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                return looksLikeAllocatorName(name);
            },
            .field_access => {
                const fa = tree.nodeData(node).node_and_token;
                const field = tree.tokenSlice(fa[1]);
                return looksLikeAllocatorName(field);
            },
            else => return false,
        }
    }

    /// `<recv>.destroy(<allocator_arg>)` shape — return what's freed.
    /// The struct-method `destroy` convention takes an allocator and
    /// frees the receiver, the inverse of `allocator.destroy(p)`.
    /// Distinguished from `allocator.destroy(p)` by the first arg
    /// looking like an allocator (and the method being literally
    /// `destroy`, not `free`).
    const DestroyTarget = union(enum) {
        local: LocalId,
        field: FieldRef,
    };
    fn destroyReceiverFreed(self: *Builder, call_node: Ast.Node.Index) ?DestroyTarget {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        const callee = call_full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const fa = tree.nodeData(callee).node_and_token;
        const method = tree.tokenSlice(fa[1]);
        if (!std.mem.eql(u8, method, "destroy")) return null;
        if (call_full.ast.params.len == 0) return null;
        const arg = call_full.ast.params[0];
        if (!self.exprLooksLikeAllocator(arg)) return null;
        const recv = fa[0];
        // Receiver is the freed thing.  Bare ident → local; field
        // access shape `parent.field` → FieldRef.
        switch (tree.nodeTag(recv)) {
            .identifier => {
                const name = tree.tokenSlice(tree.nodeMainToken(recv));
                // Skip allocator-named receivers (`allocator.destroy`)
                // — those are the canonical Allocator.destroy shape,
                // and our pattern matched only because the *arg* also
                // looked allocator-ish (rare, but possible).
                if (looksLikeAllocatorName(name)) return null;
                const id = self.name_to_local.get(name) orelse return null;
                return .{ .local = id };
            },
            .field_access => {
                const fref = self.fieldLhsFor(recv) orelse return null;
                return .{ .field = fref };
            },
            else => return null,
        }
    }

    /// The borrow of THIS frame that a `catch` / `orelse` fallback
    /// binds, if it binds one.  `&local` is only the easiest spelling
    /// — a fallback also hands out frame storage through a grouped
    /// address (`catch (&local)`), a labeled block (`catch blk: {
    /// break :blk &local }`), a slice of a local array (`catch
    /// local[0..]`) and a switch whose fallback prong binds it
    /// (`catch switch (v) { .a => other, else => &local }`).  All of
    /// them make the declared local point into this frame on that
    /// path, so matching the address-of node tag alone diagnosed the
    /// bare spelling and stayed silent on the rest.
    ///
    /// A fallback that binds nothing yields null, and so does one that
    /// binds a value with no frame storage (`catch other_heap_slice`).
    /// Both keep the lhs origin — the success path must not lose its
    /// tracked heap / arena allocation.
    fn fallbackFrameBorrow(self: *Builder, fallback: Ast.Node.Index) ?ExprKind {
        if (fallbackYieldsNothing(self, fallback)) return null;
        switch (self.tree.nodeTag(fallback)) {
            .@"switch", .switch_comma => {
                // A switch fallback yields whichever value its prong
                // takes; find the one that borrows the frame.  Only
                // classify here — the fork that runs the fallback
                // lowers the prong bodies.
                const sw = self.tree.fullSwitch(fallback) orelse return null;
                for (sw.ast.cases) |case_node| {
                    const case_full = self.tree.fullSwitchCase(case_node) orelse continue;
                    const kind = self.frameBorrowOfExpr(case_full.ast.target_expr) orelse continue;
                    return kind;
                }
                return null;
            },
            else => {},
        }
        return self.frameBorrowOfExpr(fallback);
    }

    /// The frame borrow `expr` hands out, following a binding hop when
    /// the expression NAMES one rather than spelling the address.
    ///
    /// `const alias = &local;` binds exactly what `&local` binds, so a
    /// fallback written `catch alias` / `orelse alias` puts the declared
    /// value into this frame on exactly the path `catch &local` does.
    /// Classifying the identifier on its own yields `.copy_of(alias)` —
    /// a copy of something whose own lifetime this says nothing about
    /// — so the hop is taken here, against the frame borrow the alias's
    /// own initializer recorded.
    ///
    /// The hop is one deep by construction: [LocalInfo.
    /// frame_borrow_origin] is only ever set from a `.stack_ref` /
    /// `.composite_borrow` initializer, which names the frame local
    /// directly rather than another alias.  A fallback that names a
    /// binding with no frame borrow behind it falls through to
    /// [classifyExpr] and is accepted or declined exactly as before,
    /// which is what keeps the success path's heap / arena origin.
    fn frameBorrowOfExpr(self: *Builder, expr: Ast.Node.Index) ?ExprKind {
        const tree = self.tree;
        if (tree.nodeTag(expr) == .identifier) {
            const name = tree.tokenSlice(tree.nodeMainToken(expr));
            if (std.mem.eql(u8, name, "undefined")) return null;
            const id = self.name_to_local.get(name) orelse return null;
            const origin = self.locals.items[@intFromEnum(id)].frame_borrow_origin orelse return null;
            return .{ .stack_ref = origin };
        }
        const kind = self.classifyExpr(expr);
        return switch (kind) {
            .stack_ref, .composite_borrow => kind,
            else => null,
        };
    }

    /// A runtime binding cannot name a namespace declaration. Avoid evaluating
    /// its value (and a getter chain behind it) just to search for constants.
    fn namespaceOwnerIsRuntime(self: *Builder, tree: *const Ast, node: Ast.Node.Index) bool {
        if (tree != self.tree) return false;
        var root = node;
        while (tree.nodeTag(root) == .field_access)
            root = tree.nodeData(root).node_and_token[0];
        if (tree.nodeTag(root) != .identifier) return false;
        return self.indexLocalAt(tree.nodeMainToken(root)) != null;
    }

    fn namespaceSelectionMayBeUndefined(self: *Builder, node: Ast.Node.Index) bool {
        var selectors: [8]Ast.Node.Index = undefined;
        var count: usize = 0;
        var root = node;
        while (self.tree.nodeTag(root) == .array_access) {
            if (count == selectors.len) return false;
            const base, const index = self.tree.nodeData(root).node_and_node;
            selectors[count] = index;
            count += 1;
            root = initShapeNode(self, base);
        }
        if (self.tree.nodeTag(root) != .field_access) return false;
        const base, const field = self.tree.nodeData(root).node_and_token;
        if (self.namespaceOwnerIsRuntime(self.tree, base)) return false;
        const frame = self.integerResolutionFrame() orelse return false;
        const owner = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolveValueOfNode(base)) orelse return false;
        if (!owner.is_type_val or owner.data != .container) return false;
        const scope = owner.data.container.scope_handle;
        const tree = &scope.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const container = tree.fullContainerDecl(&buffer, scope.toNode()) orelse return false;
        const name = self.tree.tokenSlice(field);
        for (container.ast.members) |member| {
            const variable = tree.fullVarDecl(member) orelse continue;
            if (tree.tokenTag(variable.ast.mut_token) != .keyword_const or
                !std.mem.eql(u8, tree.tokenSlice(variable.ast.mut_token + 1), name)) continue;
            const value = variable.ast.init_node.unwrap() orelse return false;
            return self.literalSelectionMayBeUndefined(tree, value, selectors[0..count], container.ast.members);
        }
        return false;
    }

    fn literalSelectionMayBeUndefined(self: *Builder, tree: *const Ast, node: Ast.Node.Index, selectors: []const Ast.Node.Index, members: []const Ast.Node.Index) bool {
        if (selectors.len == 0) return sourceUndefinedLiteral(tree, node, members, 0);
        var buffer: [2]Ast.Node.Index = undefined;
        const literal = tree.fullArrayInit(&buffer, node) orelse return sourceUndefinedLiteral(tree, node, members, 0);
        const selector = selectors[selectors.len - 1];
        if (self.tree.nodeTag(selector) == .number_literal) {
            const index = self.integerValue(selector) orelse return false;
            if (index >= literal.ast.elements.len) return false;
            return self.literalSelectionMayBeUndefined(tree, literal.ast.elements[@intCast(index)], selectors[0 .. selectors.len - 1], members);
        }
        for (literal.ast.elements) |element| {
            if (self.literalSelectionMayBeUndefined(tree, element, selectors[0 .. selectors.len - 1], members)) return true;
        }
        return false;
    }

    fn sourceUndefinedLiteral(tree: *const Ast, node: Ast.Node.Index, members: []const Ast.Node.Index, depth: u32) bool {
        if (depth == max_classify_depth) return false;
        // A namespace/type value does not evaluate declarations inside it.
        // In particular, selecting a method address does not read its body.
        var owner = node;
        while (tree.nodeTag(owner) == .field_access)
            owner = tree.nodeData(owner).node_and_token[0];
        var container_buffer: [2]Ast.Node.Index = undefined;
        if (tree.fullContainerDecl(&container_buffer, owner) != null) return false;
        if (tree.nodeTag(node) == .identifier) {
            const name = tree.tokenSlice(tree.nodeMainToken(node));
            if (std.mem.eql(u8, name, "undefined")) return true;
            for (members) |member| {
                const variable = tree.fullVarDecl(member) orelse continue;
                if (tree.tokenTag(variable.ast.mut_token) != .keyword_const or
                    !std.mem.eql(u8, tree.tokenSlice(variable.ast.mut_token + 1), name)) continue;
                return sourceUndefinedLiteral(tree, variable.ast.init_node.unwrap() orelse return false, members, depth + 1);
            }
            return false;
        }
        var runtime: RuntimeOperandFilter = .{};
        var token = tree.firstToken(node);
        const last = tree.lastToken(node);
        while (token <= last) : (token += 1) {
            if (!runtime.readsToken(tree, token)) continue;
            if (tree.tokenTag(token) == .identifier and
                std.mem.eql(u8, tree.tokenSlice(token), "undefined")) return true;
        }
        return false;
    }

    fn sourceUndefinedInFrame(self: *Builder, frame: zls_resolver_mod.TypeResolver.ResolutionFrame, node: Ast.Node.Index, depth: u32) bool {
        if (depth == max_classify_depth) return false;
        const tree = &frame.handle.document.tree;
        if (sourceUndefinedLiteral(tree, node, &.{}, 0)) return true;
        var declaration_frame = frame;
        const declaration = switch (tree.nodeTag(node)) {
            .identifier => blk: {
                const token = tree.nodeMainToken(node);
                break :blk frame.resolver.analyser.lookupSymbolGlobal(frame.handle, tree.tokenSlice(token), tree.tokenStart(token)) catch |err| {
                    self.noteResolutionError(err);
                    return false;
                };
            },
            .field_access => blk: {
                const owner_node, const token = tree.nodeData(node).node_and_token;
                if (self.namespaceOwnerIsRuntime(tree, owner_node)) return false;
                const owner = frame.resolveValueOfNode(owner_node) catch |err| {
                    self.noteResolutionError(err);
                    return false;
                } orelse return false;
                if (!owner.is_type_val or owner.data != .container) return false;
                declaration_frame = frame.resolver.frameForContainer(owner.data.container);
                break :blk owner.lookupSymbol(&frame.resolver.analyser, tree.tokenSlice(token)) catch |err| {
                    self.noteResolutionError(err);
                    return false;
                };
            },
            .grouped_expression => return self.sourceUndefinedInFrame(frame, tree.nodeData(node).node_and_token[0], depth + 1),
            else => return false,
        } orelse return false;
        if (!declaration.isConst()) return false;
        const declaration_node = switch (declaration.decl) {
            .ast_node => |value| value,
            else => return false,
        };
        declaration_frame.handle = declaration.handle;
        const variable = declaration.handle.document.tree.fullVarDecl(declaration_node) orelse return false;
        return self.sourceUndefinedInFrame(declaration_frame, variable.ast.init_node.unwrap() orelse return false, depth + 1);
    }

    fn returnedFieldHasUndefinedOrigin(self: *Builder, expression: Ast.Node.Index) bool {
        var fields: [64][]const u8 = undefined;
        var count: usize = 0;
        var root = expression;
        while (self.tree.nodeTag(root) == .field_access) {
            if (count == fields.len) return false;
            const base, const token = self.tree.nodeData(root).node_and_token;
            const raw = self.tree.tokenSlice(token);
            fields[count] = if (std.mem.startsWith(u8, raw, "@\""))
                self.fieldLiteralName(token, false) orelse return false
            else raw;
            count += 1;
            root = initShapeNode(self, base);
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const call = zls_resolver_mod.TypeResolver.CallOperands.full(self.tree, &buffer, root) orelse return false;
        const frame = self.integerResolutionFrame() orelse return false;
        if (count != 0 and std.mem.eql(u8, fields[0], "len")) {
            const owner = self.tree.nodeData(expression).node_and_token[0];
            const raw = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(owner)) orelse return false;
            const actual = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(raw)) orelse return false;
            if (frame.resolver.typeTag(actual) == .array) return false;
            if (frame.resolver.pointerSize(actual) == .one) {
                const child = frame.resolver.childType(actual) orelse return false;
                const normalized = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(child)) orelse return false;
                if (frame.resolver.typeTag(normalized) == .array) return false;
            }
        }
        var path: ?[]const u8 = null;
        while (count != 0) {
            count -= 1;
            path = self.allocDottedPath(path, fields[count]) catch |err| {
                self.noteResolutionError(err);
                return false;
            };
        }
        return (self.cache orelse return false).callResultFieldMayBeUndefinedAt(
            call.queryToken(self.tree, root),
            frame,
            path orelse return false,
        ) catch |err| {
            self.noteResolutionError(err);
            return false;
        };
    }

    fn returnConstructorHasUndefinedDefault(self: *Builder, node: Ast.Node.Index) bool {
        return self.constructorHasUndefinedDefault(node, null);
    }

    fn constructorHasUndefinedDefault(self: *Builder, node: Ast.Node.Index, selected_field: ?[]const u8) bool {
        var literal_buffer: [2]Ast.Node.Index = undefined;
        const literal = self.tree.fullStructInit(&literal_buffer, initShapeNode(self, node)) orelse return false;
        const value_type = self.bindingValueType(null, node, .unknown);
        const actual = value_type.container orelse context: {
            const frame = self.integerResolutionFrame() orelse return false;
            var expected = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.expectedTypeOfNode(node)) orelse return false;
            var layers: u8 = 0;
            while (expected.data != .container) : (layers += 1) {
                if (layers == 4 or frame.resolver.typeTag(expected) != .optional) return false;
                const child = frame.resolver.childType(expected) orelse return false;
                expected = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(child)) orelse return false;
            }
            break :context expected.data.container;
        };
        const scope = actual.scope_handle;
        const owner_tree = &scope.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const declaration = owner_tree.fullContainerDecl(&buffer, scope.toNode()) orelse return false;
        if (owner_tree.tokenTag(declaration.ast.main_token) == .keyword_union) return false;
        for (declaration.ast.members) |member| {
            const field = owner_tree.fullContainerField(member) orelse continue;
            const name = owner_tree.tokenSlice(field.ast.main_token);
            if (selected_field) |selected| if (!std.mem.eql(u8, selected, name)) continue;
            var supplied = false;
            for (literal.ast.fields) |value| {
                if (self.fieldInitName(value)) |provided| if (std.mem.eql(u8, provided, name)) {
                    supplied = true;
                    break;
                };
            }
            if (!supplied) {
                const default = field.ast.value_expr.unwrap() orelse continue;
                const frame = (self.zls orelse return false).frameForContainer(actual);
                if (self.sourceUndefinedInFrame(frame, default, 0)) return true;
            }
        }
        return false;
    }

    fn hasRuntimeUndefinedLiteral(self: *Builder, node: Ast.Node.Index) bool {
        return self.runtimeUndefinedLiteralAtDepth(node, 0);
    }

    fn runtimeUndefinedLiteralAtDepth(self: *Builder, node: Ast.Node.Index, depth: u32) bool {
        if (depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, depth, node);
            return false;
        }
        const tree = self.tree;
        switch (tree.nodeTag(node)) {
            .identifier => {
                const token = tree.nodeMainToken(node);
                if (std.mem.eql(u8, tree.tokenSlice(token), "undefined")) return true;
                if (self.indexLocalAt(token) != null) return false;
                const frame = self.integerResolutionFrame() orelse return false;
                return self.sourceUndefinedInFrame(frame, node, depth + 1);
            },
            .field_access => {
                if (self.returnedFieldHasUndefinedOrigin(node)) return true;
                const frame = self.integerResolutionFrame() orelse return false;
                return self.sourceUndefinedInFrame(frame, node, depth + 1);
            },
            .grouped_expression => return self.runtimeUndefinedLiteralAtDepth(tree.nodeData(node).node_and_token[0], depth + 1),
            .negation, .bit_not, .bool_not, .@"try" => return self.runtimeUndefinedLiteralAtDepth(tree.nodeData(node).node, depth + 1),
            .bool_and, .bool_or => {
                const lhs, const rhs = tree.nodeData(node).node_and_node;
                if (self.runtimeUndefinedLiteralAtDepth(lhs, depth + 1)) return true;
                if (self.booleanValue(lhs)) |value| {
                    if (value == .constant and
                        (if (tree.nodeTag(node) == .bool_and) !value.constant else value.constant)) return false;
                }
                return self.runtimeUndefinedLiteralAtDepth(rhs, depth + 1);
            },
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodeMainToken(node));
                if ((!pureScalarBuiltin(name) and !std.mem.eql(u8, name, "@splat")) or isComptimeOnlyBuiltin(name)) return false;
                const builtin = std.zig.BuiltinFn.list.get(name) orelse return false;
                var buffer: [2]Ast.Node.Index = undefined;
                const arguments = tree.builtinCallParams(&buffer, node) orelse return false;
                for (arguments, 0..) |argument, ordinal| {
                    if (ordinal == 0 and (builtin.tag == .as or builtin.tag == .mul_add)) continue;
                    if (self.runtimeUndefinedLiteralAtDepth(argument, depth + 1)) return true;
                }
                return false;
            },
            .call, .call_one, .call_comma, .call_one_comma => return self.classifyExpr(node) == .undef,
            else => {},
        }
        var buffer: [2]Ast.Node.Index = undefined;
        const values = if (tree.fullArrayInit(&buffer, node)) |literal|
            literal.ast.elements
        else if (tree.fullStructInit(&buffer, node)) |literal|
            literal.ast.fields
        else
            null;
        if (values) |elements| {
            for (elements) |element| if (self.runtimeUndefinedLiteralAtDepth(element, depth + 1)) return true;
            return false;
        }
        var runtime: RuntimeOperandFilter = .{};
        var token = tree.firstToken(node);
        const last = tree.lastToken(node);
        while (token <= last) : (token += 1) {
            if (!runtime.readsToken(tree, token)) continue;
            if (tree.tokenTag(token) == .identifier and
                std.mem.eql(u8, tree.tokenSlice(token), "undefined")) return true;
        }
        return false;
    }

    fn classifyExpr(self: *Builder, expr_node: Ast.Node.Index) ExprKind {
        if (self.classify_depth == max_classify_depth) {
            self.noteBudgetFailure(.expr_classify_depth, max_classify_depth, self.classify_depth, expr_node);
            return .unknown;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        const tree = self.tree;
        const tag = tree.nodeTag(expr_node);
        if (tag == .identifier and self.indexLocalAt(tree.nodeMainToken(expr_node)) == null and
            self.hasRuntimeUndefinedLiteral(expr_node)) return .undef;
        if (tag == .field_access and self.hasRuntimeUndefinedLiteral(expr_node)) return .undef;
        if (tag == .array_access and self.namespaceSelectionMayBeUndefined(expr_node)) return .undef;
        var literal_buffer: [2]Ast.Node.Index = undefined;
        if ((tag == .array_mult or tree.fullArrayInit(&literal_buffer, expr_node) != null or
            tree.fullStructInit(&literal_buffer, expr_node) != null) and
            (self.hasRuntimeUndefinedLiteral(expr_node) or self.returnConstructorHasUndefinedDefault(expr_node))) return .undef;
        if (tag == .grouped_expression) {
            return self.classifyExpr(tree.nodeData(expr_node).node_and_token[0]);
        }
        if (self.booleanLiteral(expr_node)) |value| return .{ .boolean = .{ .constant = value } };
        if (tag == .bool_not or tag == .equal_equal or tag == .bang_equal) {
            if (self.booleanValue(expr_node)) |value| return .{ .boolean = value };
        }

        // `try expr` — unwrap and classify the inner expression.  The
        // error-exit edge isn't modeled yet (phase 9); for success-path
        // analysis the wrapped value has the same origin as the inner
        // call's return.
        if (tag == .@"try") {
            return self.classifyExpr(tree.nodeData(expr_node).node);
        }

        // `lhs catch rhs` / `lhs orelse rhs` — with a vacuous fallback
        // (`catch return`, `orelse unreachable`, a block ending in one)
        // the bound value is the lhs's, so the origin propagates into
        // the declaring local instead of collapsing to .unknown
        // (`gpa.alloc(...) catch return &.{}` still produces a tracked
        // heap allocation).  The error path itself is modeled separately
        // via emitCatchFork / emitOrelseFork at statement level.
        //
        // A fallback that DOES bind a value is a second origin for the
        // same local.  When it binds a borrow of THIS frame, peeling
        // would erase a real escape: `const p = fallible() catch
        // &local; return p;` reports nothing at all otherwise.  That
        // holds for every spelling of the borrow, so ask the fallback
        // what it produces rather than matching one node tag — see
        // `fallbackFrameBorrow`.  Keep the lhs origin otherwise, so a
        // value-yielding fallback never costs the success path its
        // heap / arena identity.
        if (tag == .@"catch" or tag == .@"orelse") {
            const data = tree.nodeData(expr_node).node_and_node;
            if (self.fallbackFrameBorrow(data[1])) |borrow| return borrow;
            return self.classifyExpr(data[0]);
        }

        // `ArenaAllocator.init(...)` → .arena_init
        // Match arena_init patterns against the CALLEE text only —
        // the function name being called — not the full call
        // expression.  Without this, a wrapping call whose args
        // happen to mention "ArenaAllocator.init" (e.g. `bun.new(T,
        // .{ .arena = ArenaAllocator.init(alloc) })`) would
        // accidentally classify as arena_init, then `return this`
        // would flag a bogus arena-escape.
        const first = tree.firstToken(expr_node);
        const last = tree.lastToken(expr_node);
        const start = tree.tokens.items(.start)[first];
        const last_start = tree.tokens.items(.start)[last];
        const last_len = tree.tokenSlice(last).len;
        const end: usize = last_start + last_len;
        const text = tree.source[start..end];

        const callee_text = self.calleeText(expr_node) orelse text;
        if (anyPatternMatches(callee_text, self.config.arena_init_patterns)) {
            const aid: abstract_state.ArenaId = @enumFromInt(self.next_arena);
            self.next_arena += 1;
            return .{ .arena_init = .{ .id = aid } };
        }
        // Heap-allocated arena: `gpa.create(ArenaAllocator)` returns a
        // pointer to a fresh arena.  The pointer itself is heap, but
        // the arena identity is what matters for UAK tracking — its
        // .deinit() kills the underlying bump memory regardless of
        // where the descriptor lives.  Treat as arena_init so
        // arena_kill propagation works.  Detected by combining
        // heap_alloc pattern match with "ArenaAllocator" in the call
        // text (the type passed to `.create`).
        // Heap-alloc / arena-via-create patterns: only fire when the
        // expression itself is a call.  Without this gate, a struct
        // literal whose field initializer is `alloc.alloc(...)` would
        // text-match the heap pattern, accidentally tagging the whole
        // literal as a fresh heap allocation and binding the parent
        // local's origin to the matched cell — breaking subsequent
        // @takes-ownership / field-use checks on the local.
        const is_call_node = switch (tree.nodeTag(expr_node)) {
            .call, .call_one, .call_comma, .call_one_comma => true,
            else => false,
        };
        if (is_call_node) if (self.cache) |cache| {
            var buffer: [2]Ast.Node.Index = undefined;
            const call = zls_resolver_mod.TypeResolver.CallOperands.full(tree, &buffer, expr_node) orelse return .unknown;
            const frame = self.integerResolutionFrame();
            if (cache.callResultMayBeUndefinedAt(call.queryToken(tree, expr_node), frame) catch |err| blk: {
                self.noteResolutionError(err);
                break :blk false;
            }) return .undef;
            if (frame) |scope| {
                if (self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, scope.typeOfNode(expr_node))) |actual| {
                    if (scope.resolver.typeTag(actual) == .array) {
                        const returned_source = cache.arrayReturnSourceAt(call.queryToken(tree, expr_node), frame, &.{}) catch |err| blk: {
                            self.noteResolutionError(err);
                            break :blk null;
                        };
                        if (returned_source) |source| {
                            if (source.projection_count == 0 and self.hasRuntimeUndefinedLiteral(source.argument)) return .undef;
                        }
                    }
                }
            }
        };
        if (is_call_node) {
            if (anyPatternMatches(text, self.config.heap_alloc_patterns) and
                std.mem.indexOf(u8, text, "ArenaAllocator") != null and
                std.mem.indexOf(u8, text, ".create(") != null)
            {
                const aid: abstract_state.ArenaId = @enumFromInt(self.next_arena);
                self.next_arena += 1;
                return .{ .arena_init = .{ .id = aid, .is_heap_allocated = true } };
            }
            if (anyPatternMatches(text, self.config.heap_alloc_patterns)) {
                // Allocator-provenance check: if the call's immediate
                // receiver is a local known to be an arena_allocator
                // (or the arena itself, for direct
                // `arena.allocator().alloc()` is handled via
                // .allocator() classification below), the result is
                // arena-bound memory, NOT a fresh heap allocation.
                // Catches the canonical pattern
                //   const a = arena.allocator(); buf = a.alloc(...);
                //   arena.deinit(); use(buf);  // UAK
                if (self.arenaBoundReceiverOfCall(expr_node)) |arena_src| {
                    return .{ .copy_of = arena_src };
                }
                const hid: abstract_state.HeapId = @enumFromInt(self.next_heap);
                self.next_heap += 1;
                // Record the allocator local — the leftmost ident
                // of the callee chain (e.g. `gpa` in
                // `gpa.alloc(...)`).  Null when the receiver isn't
                // a known local (stdlib reference, dotted chain,
                // etc.); the matching free site will skip the
                // mismatch check.
                const allocator_local = self.allocReceiverLocal(expr_node);
                return .{ .heap_alloc = .{ .id = hid, .allocator_local = allocator_local } };
            }
        }

        // `<arena_local>.allocator()` — return an Allocator value
        // bound to the arena's lifetime.  Returning .copy_of(arena)
        // gives the receiving local the arena's origin; lowerVarDecl
        // additionally sets init_hint = .arena_allocator so .alloc
        // calls through the alias also produce arena memory.
        if (std.mem.indexOf(u8, text, ".allocator(") != null) {
            if (self.arenaLocalDotAllocatorReceiver(expr_node)) |arena_local| {
                return .{ .copy_of = arena_local };
            }
        }

        // Constructor-style call taking an arena-bound allocator as
        // its first arg: `Type.init(arena_alloc, ...)`,
        // `Type.create(arena_alloc, ...)`, etc.  The returned value
        // very likely embeds storage from that allocator, so its
        // lifetime is bound to the arena.  Heuristic R7-lite for
        // user-defined types we have no annotation for — without it,
        // canonical patterns like
        //   var log = Log.init(arena.allocator());
        //   arena.deinit();
        //   log.toJS();   // UAK — log's internals were arena-backed
        // would never fire.  Trigger only on conventional constructor
        // method names so we don't propagate arena origin to e.g.
        // `globalThis.throwValue(alloc, ...)` which doesn't embed.
        if (self.constructorWithArenaArg(expr_node)) |arena_src| {
            return .{ .copy_of = arena_src };
        }

        if (self.arrayCallSource(expr_node)) |source| {
            // Source projection transports descriptor state; it must not
            // replace the independent borrowed-return lifetime route.
            if (self.sliceCallValue(expr_node)) return self.classifyCall(expr_node);
            return source;
        }
        // `obj.field` where obj is a known local → .field_copy_of.
        // Lets free / use of a field be tracked against its own
        // origin separately from the parent local.
        //
        // EXCEPTION: `.ptr` on a slice is the raw data pointer of the
        // slice descriptor itself — it points into the SAME allocation
        // as the slice.  Inherit the parent's origin (.copy_of) so
        // `@ptrCast(raw.ptr)` correctly carries raw's heap/arena.
        if (tag == .field_access) {
            const fa = tree.nodeData(expr_node).node_and_token;
            const recv = fa[0];
            const field_tok = fa[1];
            if (tree.nodeTag(recv) == .identifier) {
                const recv_name = tree.tokenSlice(tree.nodeMainToken(recv));
                if (self.name_to_local.get(recv_name)) |id| {
                    const fname = self.normalizedFieldComponent(field_tok) orelse return .unknown;
                    if (std.mem.eql(u8, fname, "ptr") and self.locals.items[@intFromEnum(id)].is_slice) {
                        return .{ .copy_of = id };
                    }
                    return .{ .field_copy_of = .{ .parent = id, .name = fname } };
                }
            }
        }

        // Identifier reference → .undef / .copy_of(local) if known
        if (tag == .identifier) {
            const name = tree.tokenSlice(tree.nodeMainToken(expr_node));
            if (std.mem.eql(u8, name, "undefined")) return .undef;
            if (self.name_to_local.get(name)) |id| {
                return .{ .copy_of = id };
            }
        }

        // `&<local>` — address-of of a known local.  Produces a
        // pointer bound to that local's stack frame.  Also accept
        // `&<local>.<field>(.<f2>...)` — a borrow into the local's
        // storage; same lifetime semantics, since taking the address
        // of a field is taking a pointer into the parent.
        if (tag == .address_of) {
            var inner = tree.nodeData(expr_node).node;
            while (tree.nodeTag(inner) == .grouped_expression) {
                inner = tree.nodeData(inner).node_and_token[0];
            }
            if (tree.nodeTag(inner) == .identifier) {
                const name = tree.tokenSlice(tree.nodeMainToken(inner));
                if (self.name_to_local.get(name)) |id| {
                    // Comptime-initialized locals (`const X = comptime
                    // .{...};`), type aliases and FILE-SCOPE consts live
                    // in static memory.  `&X` borrows into static
                    // storage — not a stack escape.  The last of those
                    // is `registerUndefFileConsts`'s bindings: the
                    // `init_hint` says nothing about where the bytes
                    // live, and no `InitHint` variant means "a
                    // container-scope global", so the set it files them
                    // in is what answers this.
                    const info = self.locals.items[@intFromEnum(id)];
                    if (info.init_hint == .type_alias) return .unknown;
                    if (self.file_scope_storage.contains(id)) return .unknown;
                    return .{ .stack_ref = id };
                }
            }
            // `&x.f`, `&x.f.g`, `&x.f.?`, `&x.f.?.g`: the operand's
            // access chain decides where the address lives, so walk the
            // chain instead of matching a spelling of it.
            const operand_tag = tree.nodeTag(inner);
            if (operand_tag == .field_access or operand_tag == .unwrap_optional) {
                const chain = self.addressOperandChain(inner);
                if (chain.root) |root| {
                    // Pointer-typed parent: the pointee lives in the
                    // caller, not this fn's stack frame.  `&self.field`
                    // where `self: *Self` is a borrow from caller-owned
                    // storage — not a stack escape candidate.
                    const parent_info = self.locals.items[@intFromEnum(root)];
                    if (parent_info.is_pointer) {
                        return .unknown;
                    }
                    // Heap-allocated parent: same logic.  `&prealloc.f`
                    // where `prealloc = gpa.create(T)` is a heap-field
                    // pointer, not a stack ref.  init_hint covers
                    // implicit-typed locals that weren't caught by
                    // is_pointer (no explicit type annotation).
                    if (parent_info.init_hint == .heap_local) {
                        return .unknown;
                    }
                    // Type-alias parent: `const X = struct {...};`
                    // declares X as a comptime type, not a stack
                    // value.  `&X.<static_var>` addresses a static
                    // / data-segment slot whose lifetime is the
                    // whole program — not a stack escape.
                    if (parent_info.init_hint == .type_alias) {
                        return .unknown;
                    }
                    // Type engine: check if the direct LHS of this
                    // operand resolves to a pointer type.  Covers
                    // `&ptr_local.field` where the local's type
                    // wasn't annotated as a pointer (e.g. a capture
                    // from a HashMap.get call whose return type is
                    // `?*V`).  A field NAMED like a pointer proves
                    // nothing: `value_ptr` / `key_ptr` / `ptr` are a
                    // stdlib spelling convention, not a declaration,
                    // and honouring the name lets a by-value field of
                    // that name hide a real frame escape.  So the
                    // answer comes from the type or not at all.
                    //
                    // Unresolved storage stays unknown. Query errors still
                    // propagate through the lowering entry point.
                    if (self.zls) |zls| {
                        const child = tree.nodeData(inner).node_and_token[0];
                        const lhs_pointer = zls.resolvedTypeIsPointer(child) catch |err| {
                            self.noteResolutionError(err);
                            return .unknown;
                        };
                        if (lhs_pointer == true) return .unknown;
                    }
                    // Past the first access every further one READS
                    // what the earlier one produced, so a pointer
                    // anywhere on the way puts the address in the
                    // pointee rather than in this frame.
                    if (chain.count >= 2 and !self.chainHasInlineStorage(root, chain)) {
                        return .unknown;
                    }
                    // A field of a FILE-SCOPE const is static storage
                    // too, for the same reason the bare identifier
                    // case above is: the address outlives the frame
                    // whatever it is taken of.
                    if (self.file_scope_storage.contains(root)) return .unknown;
                    return .{ .stack_ref = root };
                }
            }
            if (tree.nodeTag(inner) == .array_access) {
                if (tokens.rootIdentifier(tree, inner)) |root| {
                    const id = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(root))) orelse return .unknown;
                    if (self.locals.items[@intFromEnum(id)].is_array) return .{ .stack_ref = id };
                }
            }
        }

        // `<local>[..]` / `<local>[a..b]` / `<local>[a..b :s]` —
        // slicing a `[N]T` local produces a fat pointer into the
        // local's stack storage.  For escape purposes that's
        // identical to &local: returning the slice past the frame
        // is UB.  Only fires when the sliced local was declared
        // with an array type — slicing a local that already holds
        // a slice or pointer just makes another view of caller-
        // owned storage.
        const slicee_opt: ?Ast.Node.Index = switch (tag) {
            .slice_open => tree.nodeData(expr_node).node_and_node[0],
            .slice, .slice_sentinel => tree.nodeData(expr_node).node_and_extra[0],
            else => null,
        };
        // Labeled-block expression (`blk: { ... break :blk X; }`):
        // body was already lowered by lowerComputedValue in
        // the caller.  Classify the break value here so the .ret /
        // assign sees the right origin.  If exactly one `break :blk`
        // with a value exists, use that; multiple distinct break
        // values fall through to .unknown.
        switch (tag) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                if (self.blockLabelToken(expr_node)) |lt| {
                    if (self.singleLabeledBreakValue(expr_node, lt)) |v| {
                        return self.classifyExpr(v);
                    }
                }
            },
            else => {},
        }

        if (slicee_opt) |slicee| {
            if (tree.nodeTag(slicee) == .identifier) {
                const name = tree.tokenSlice(tree.nodeMainToken(slicee));
                if (self.name_to_local.get(name)) |id| {
                    const info = self.locals.items[@intFromEnum(id)];
                    if (info.is_array) {
                        return .{ .stack_ref = id };
                    }
                    // Only the exact full span preserves the slice value.
                    // Truncation must not become a whole-value copy.
                    if (info.is_slice and self.isFullSlice(expr_node)) return .{ .copy_of = id };
                    // Slice of a heap/arena-bearing local — the
                    // sub-slice aliases the same allocation, so
                    // propagate the local's origin via .copy_of.
                    // `const view = buf[0..n]; free(buf); return view;`
                    // then correctly fires UAF.
                    if (info.init_hint == .heap_local or info.init_hint == .arena_local) {
                        return .{ .copy_of = id };
                    }
                }
            }
        }

        // Transparent cast builtins: `@ptrCast(x)`, `@bitCast(x)`,
        // `@alignCast(x)`, `@constCast(x)`, `@volatileCast(x)`,
        // `@addrSpaceCast(x)`, `@as(T, x)`, `@fieldParentPtr(name, p)`.
        // Each produces a value that aliases the underlying storage
        // of its source arg — propagate the source's origin so
        // free-then-use through a cast is caught.
        //
        // For ANY OTHER builtin call (`@truncate(...)`, `@intCast(...)`,
        // `@hash(...)` etc.), the result's lifetime is unrelated to
        // its args — return .unknown so the composite-fallback walker
        // doesn't pick up address-of-args buried inside the builtin's
        // arguments as if they were the return value's shape.
        switch (tag) {
            .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma => {
                if ((pureScalarBuiltin(tree.tokenSlice(tree.nodeMainToken(expr_node))) or
                    std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(expr_node)), "@splat")) and
                    self.hasRuntimeUndefinedLiteral(expr_node)) return .undef;
                if (self.transparentCastSource(expr_node)) |src| {
                    return self.classifyExpr(src);
                }
                return .unknown;
            },
            else => {},
        }

        // Annotated method/function call: `<recv>.<method>(args)` or
        // bare `<fn>(args)`.  Look up the callee in the annotation DB
        // and use its @returns to classify the result.
        const is_call = switch (tag) {
            .call, .call_one, .call_comma, .call_one_comma => true,
            else => false,
        };
        if (is_call) {
            return self.classifyCall(expr_node);
        }

        // Only value-position children can carry a borrow out of an aggregate.
        const is_composite_literal = switch (tag) {
            .struct_init,
            .struct_init_comma,
            .struct_init_one,
            .struct_init_one_comma,
            .struct_init_dot,
            .struct_init_dot_comma,
            .struct_init_dot_two,
            .struct_init_dot_two_comma,
            .array_init,
            .array_init_comma,
            .array_init_one,
            .array_init_one_comma,
            .array_init_dot,
            .array_init_dot_comma,
            .array_init_dot_two,
            .array_init_dot_two_comma,
            .array_mult,
            => true,
            else => false,
        };
        if (is_composite_literal) {
            const borrow = self.firstCompositeBorrow(expr_node);
            if (borrow) |kind| if (kind == .stack_ref) return kind;
            if (!self.suppress_composite_borrow) {
                if (self.firstResourceMethodBorrow(expr_node)) |id| {
                    return .{ .composite_borrow = id };
                }
            }
            if (borrow) |kind| return kind;
        }

        return .unknown;
    }

    /// Check every value-position borrow except the one checked by `.ret`.
    fn emitAdditionalEscapeChecks(
        self: *Builder,
        expr_node: Ast.Node.Index,
        cur: BlockId,
        primary_kind: ExprKind,
        stack_loans: StackLoanProof,
    ) !void {
        // A complete canonical proof is the sole stack decision. An incomplete
        // proof permits only origins independently named by legacy_locals;
        // the transfer also drops every cell the canonical proof already names.
        if (stack_loans.complete) return;
        var seen: std.AutoArrayHashMapUnmanaged(BorrowKey, void) = .empty;
        defer seen.deinit(self.gpa);
        try seen.put(self.gpa, BorrowKey.from(primary_kind), {});
        var borrows = BorrowIterator.init(self, expr_node);
        while (borrows.next()) |kind| {
            const key = BorrowKey.from(kind);
            const entry = try seen.getOrPut(self.gpa, key);
            if (entry.found_existing) continue;
            // A borrow of a local whose DECLARED type cannot denote an
            // address is not an escape, and emitting it costs a
            // statement in every plain by-value aggregate return — the
            // `return .{ .a = a, .b = b }` over two integers, where the
            // transfer then resolves both through `.plain` origins and
            // reports nothing.  The gate is a TYPE, not a name, and it
            // never fires for an unknown type; see
            // [localHoldsNoAddress].
            if (!key.stack_address and self.localHoldsNoAddress(key.local)) continue;
            try self.appendStmt(cur, .{
                .kind = .{ .composite_escape = .{
                    .value_kind = kind,
                    .stack_loans = stack_loans,
                } },
                .pos = self.posOf(expr_node),
                .end_pos = self.endPosOf(expr_node),
            });
        }
    }

    fn frameBindingAt(self: *Builder, token: Ast.TokenIndex) ?*const @import("../model/local_bindings.zig").Binding {
        const cache = self.cache orelse if (self.address_cache) |*cached| cached else return null;
        const bindings = cache.localBindings(self.fn_proto orelse return null, self.fn_body_node orelse return null) catch |err| {
            self.noteResolutionError(err);
            return null;
        };
        return bindings.findAt(self.tree.tokenSlice(token), token);
    }

    /// Expression-local bindings remain physical cells after their names have
    /// been removed from the builder's current scope.
    fn frameLocalAt(self: *Builder, token: Ast.TokenIndex) ?LocalId {
        const binding = self.frameBindingAt(token) orelse return null;
        const byte = self.tree.tokenStart(binding.name_token);
        for (self.locals.items, 0..) |info, index| {
            if (info.decl_pos.byte != byte or info.is_control_local) continue;
            const local: LocalId = @enumFromInt(index);
            if (self.file_scope_storage.contains(local) or info.init_hint == .type_alias) return null;
            return local;
        }
        return null;
    }

    fn directFrameCell(self: *Builder, expression: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        if (tree.fullSlice(expression)) |slice| {
            if (tree.nodeTag(slice.ast.sliced) != .identifier) return null;
            const local = self.frameLocalAt(tree.nodeMainToken(slice.ast.sliced)) orelse return null;
            const info = self.locals.items[@intFromEnum(local)];
            return if (info.is_array and !info.is_pointer and !info.is_slice) local else null;
        }
        if (tree.nodeTag(expression) != .address_of) return null;
        var operand = tree.nodeData(expression).node;
        for (0..max_classify_depth) |_| {
            if (tree.nodeTag(operand) != .grouped_expression) break;
            operand = tree.nodeData(operand).node_and_token[0];
        }
        if (tree.nodeTag(operand) == .identifier) {
            return self.frameLocalAt(tree.nodeMainToken(operand));
        }
        // Existing chain classification is usable only for the same lexical
        // root; an inner scope must not substitute a same-named frame cell.
        const root = tokens.rootIdentifier(tree, operand) orelse return null;
        const local = self.frameLocalAt(tree.nodeMainToken(root)) orelse return null;
        const kind = self.classifyExpr(expression);
        return if (kind == .stack_ref and kind.stack_ref == local) local else null;
    }

    /// Resolve only an immutable alias's actual lexical initializer. A call
    /// initializer remains opaque to the value-position borrow iterator.
    fn immutableFrameInitializer(self: *Builder, local: LocalId, use_token: Ast.TokenIndex) ?Ast.Node.Index {
        const info = self.locals.items[@intFromEnum(local)];
        if (self.file_scope_storage.contains(local)) return null;
        const binding = self.frameBindingAt(use_token) orelse return null;
        if (!binding.is_const or self.tree.tokenStart(binding.name_token) != info.decl_pos.byte) return null;
        if (binding.rhs_last >= use_token) return null;
        const cache = self.cache orelse if (self.address_cache) |*cached| cached else return null;
        return cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last);
    }

    /// This gate applies only to coarse origins. Canonical integer-address
    /// loans remain positive even when the declared return type is scalar.
    fn returnTypeHoldsNoAddress(self: *Builder) bool {
        const proto = self.fn_proto orelse return false;
        var node = proto.ast.return_type.unwrap() orelse return false;
        for (0..max_classify_depth) |_| {
            if (typeSpanIsPrimitiveScalar(self.tree, .{
                .first = self.tree.firstToken(node), .last = self.tree.lastToken(node),
            })) return true;
            if (self.tree.fullArrayType(node)) |array| {
                node = array.ast.elem_type;
                continue;
            }
            switch (self.tree.nodeTag(node)) {
                .optional_type => node = self.tree.nodeData(node).node,
                .error_union => node = self.tree.nodeData(node).node_and_node[1],
                .grouped_expression => node = self.tree.nodeData(node).node_and_token[0],
                else => break,
            }
        }
        const frame = self.integerResolutionFrame() orelse return false;
        var actual = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(node)) orelse return false;
        for (0..max_classify_depth) |_| {
            actual = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(actual)) orelse return false;
            switch (frame.resolver.typeTag(actual) orelse return false) {
                .int, .comptime_int, .float, .comptime_float, .bool, .@"enum", .enum_literal, .void, .noreturn, .error_set => return true,
                .array, .vector, .optional, .error_union => actual = frame.resolver.childType(actual) orelse return false,
                else => return fresh_storage.actualTypeAddressFree(frame, actual, 0, null) catch |err| {
                    self.noteResolutionError(err);
                    return false;
                },
            }
        }
        return false;
    }

    fn returnStackLoans(
        self: *Builder,
        expression: Ast.Node.Index,
        horizon: Ast.TokenIndex,
        domain: return_storage.Domain,
    ) LoweringError!StackLoanProof {
        var proof = try self.canonicalReturnStackLoans(expression, horizon, domain);
        if (proof.complete or self.returnTypeHoldsNoAddress()) return proof;
        var cells: std.ArrayListUnmanaged(LocalId) = .empty;
        defer cells.deinit(self.gpa);
        var borrows = BorrowIterator.init(self, expression);
        borrows.frame_cells_only = true;
        while (borrows.next()) |kind| {
            const local = switch (kind) {
                .stack_ref => |cell| cell,
                else => continue,
            };
            if (std.mem.indexOfScalar(LocalId, proof.locals, local) != null or
                std.mem.indexOfScalar(LocalId, cells.items, local) != null) continue;
            try cells.append(self.gpa, local);
        }
        if (cells.items.len == 0) return proof;
        const locals = try cells.toOwnedSlice(self.gpa);
        errdefer self.gpa.free(locals);
        try self.owned_stack_loans.append(self.gpa, locals);
        proof.legacy_locals = locals;
        return proof;
    }

    fn canonicalReturnStackLoans(
        self: *Builder,
        expression: Ast.Node.Index,
        horizon: Ast.TokenIndex,
        domain: return_storage.Domain,
    ) LoweringError!StackLoanProof {
        const query = if (self.expression_loan_query) |*session| session else return .{};
        const result = try query.expressionLoansAt(.{
            .selection = .{ .node = expression },
            .horizon = horizon,
            .domain = domain,
        });
        var complete = result.complete;
        var mapped: std.ArrayListUnmanaged(LocalId) = .empty;
        const scratch = self.expression_loan_scratch.?;
        defer mapped.deinit(scratch);
        try mapped.ensureTotalCapacity(scratch, result.loans.len);
        for (result.loans) |loan| {
            if (!loan.proved) {
                complete = false;
                continue;
            }
            if (loan.origin != .frame_cell) {
                complete = false;
                continue;
            }
            if (loan.binding_token >= self.tree.tokens.len or
                self.tree.tokenTag(loan.binding_token) != .identifier)
            {
                complete = false;
                continue;
            }
            const byte = self.tree.tokenStart(loan.binding_token);
            var match: ?LocalId = null;
            var ambiguous = false;
            for (self.locals.items, 0..) |local, index| {
                if (local.decl_pos.byte != byte) continue;
                const id: LocalId = @enumFromInt(index);
                if (local.is_control_local or self.file_scope_storage.contains(id)) continue;
                if (match != null) {
                    ambiguous = true;
                    break;
                }
                match = id;
            }
            if (ambiguous) {
                complete = false;
                continue;
            }
            const id = match orelse missing: {
                // A frame_cell witness certifies a real lexical binding in
                // this query's source. Reserve only its physical identity:
                // no scope binding, value origin, or initialized state.
                complete = false;
                if (loan.binding_token < self.fn_body_first or
                    loan.binding_token > self.fn_body_last) continue;
                const reserved = try self.appendLocal(.{
                    .name = self.tree.tokenSlice(loan.binding_token),
                    .decl_pos = self.posOfToken(loan.binding_token),
                });
                break :missing reserved;
            };
            if (std.mem.indexOfScalar(LocalId, mapped.items, id) == null) {
                mapped.appendAssumeCapacity(id);
            }
        }
        if (mapped.items.len == 0) return .{ .complete = complete };
        const locals = try self.gpa.dupe(LocalId, mapped.items);
        errdefer self.gpa.free(locals);
        try self.owned_stack_loans.append(self.gpa, locals);
        return .{ .complete = complete, .locals = locals };
    }

    /// Primitive type names that are addresses rather than values.
    /// `anyframe` is already ruled out by [type_query.
    /// isReservedScalarTypeName]; these two are not, because that
    /// helper's callers resolve the declared TYPE before asking it and
    /// this caller has only the spelling.  `var x: anyopaque = &local;`
    /// is legal and does carry an address, so answering "scalar" for
    /// it would drop a real escape.
    const address_holding_primitives = [_][]const u8{
        "anyopaque",
        "type",
    };

    /// True when the source states `local`'s declared type to be a
    /// primitive SCALAR — an integer, a float, a bool, a C scalar —
    /// so no value read from the local can be an address of anything.
    ///
    /// This is a type-level claim read from the declared type, not a
    /// judgement about the binding's name or its initializer.  A
    /// name-based test would call `p`, `buf` and `items` pointers and
    /// `x`, `n` and `count` not, which is precisely the guess the rest
    /// of this lowering refuses to make, and it would be wrong about
    /// `struct { p: *T }` either way.  A named struct, a slice, an
    /// array, an optional or a generic parameter all ANSWER NO: their
    /// contents are not visible from the spelling, so a value read
    /// through one may still be a pointer.
    ///
    /// Every answer that is not a positive proof leaves the local
    /// TRACKED.  A local with no declared type at all — a capture, a
    /// switch prong, an inferred binding — is unknown, and unknown
    /// keeps its `.composite_escape` statement, because that statement
    /// is the only thing that can still report an escape.  Dropping it
    /// would trade a measurable cost for a silent false negative, which
    /// is the one direction this analysis may not move in.
    fn localHoldsNoAddress(self: *const Builder, local: LocalId) bool {
        // Two ways a local can state a type, because there are two
        // ways it can have one: a `var|const <name>: <T>` annotation
        // and a prototype parameter's own `name: <T>`.  The second is
        // reached by the DECLARING TOKEN's byte offset, which is the
        // identity test [comptime_fill.Resolver.bindingIsParam] uses —
        // matching on the name alone would answer for a capture that
        // merely shares it.
        const tree = self.tree;
        if (self.paramTypeSpanOfLocal(local)) |param_type| {
            return typeSpanIsPrimitiveScalar(tree, param_type);
        }
        const decl = self.fill.declaredTypeSpanOfLocal(local) orelse return false;
        return typeSpanIsPrimitiveScalar(tree, decl.type);
    }


    fn paramTypeSpanOfLocal(self: *const Builder, local: LocalId) ?TokenSpan {
        const proto = self.fn_proto orelse return null;
        if (@intFromEnum(local) >= self.locals.items.len) return null;
        const decl_byte = self.locals.items[@intFromEnum(local)].decl_pos.byte;
        const tree = self.tree;
        var it = proto.iterate(tree);
        while (it.next()) |param| {
            const param_tok = param.name_token orelse continue;
            if (tree.tokens.items(.start)[param_tok] != decl_byte) continue;
            const type_expr = param.type_expr orelse return null;
            return .{ .first = tree.firstToken(type_expr), .last = tree.lastToken(type_expr) };
        }
        return null;
    }

    /// True when `span` is exactly one primitive scalar type name.
    ///
    /// The spelling question is [type_query.isReservedScalarTypeName]'s
    /// — it already owns "which reserved primitive name is a scalar
    /// type" — and this adds only [address_holding_primitives].
    /// Restating the spelling test here would give "narrow primitive"
    /// one meaning in the growth summary and another here, and the two
    /// would drift exactly as the two brace-literal walks did.
    ///
    /// One token, because `u32` is a NAME: `[2]u32`, `u32` inside an
    /// `anyerror` set, or a `comptime`-qualified spelling are none of
    /// them statements that no pointer is reachable through.
    fn typeSpanIsPrimitiveScalar(tree: *const Ast, span: TokenSpan) bool {
        if (span.first != span.last) return false;
        if (span.last >= tree.tokens.len) return false;
        if (tree.tokenTag(span.first) != .identifier) return false;
        const name = tree.tokenSlice(span.first);
        if (!type_query.isReservedScalarTypeName(name)) return false;
        for (address_holding_primitives) |held| {
            if (std.mem.eql(u8, name, held)) return false;
        }
        return true;
    }

    fn firstCompositeBorrow(self: *Builder, expr_node: Ast.Node.Index) ?ExprKind {
        var borrows = BorrowIterator.init(self, expr_node);
        var alias: ?ExprKind = null;
        while (borrows.next()) |kind| {
            if (kind == .stack_ref) return kind;
            if (alias == null) alias = kind;
        }
        return alias;
    }

    /// Walk `expr_node`'s tokens looking for any
    ///   `<local> ( . <id> )* . <method> (`
    /// Find a resource-owned method borrow inside a composite value.
    /// The call's exact summary must return a borrow from its receiver.
    fn firstResourceMethodBorrow(self: *Builder, expr_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        const cache = self.cache orelse return null;
        const first = tree.firstToken(expr_node);
        const last = tree.lastToken(expr_node);
        const tags = tree.tokens.items(.tag);

        var t: Ast.TokenIndex = first;
        while (t + 3 <= last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (t > 0 and tags[t - 1] == .period) continue;
            if (tags[t + 1] != .period) continue;

            const recv_name = tree.tokenSlice(t);
            const local = self.name_to_local.get(recv_name) orelse continue;
            const hint = self.locals.items[@intFromEnum(local)].init_hint;
            if (hint == .other) continue;

            // The last identifier before `(` is the call's exact callee token.
            var k: Ast.TokenIndex = t + 1;
            var method_tok: Ast.TokenIndex = 0;
            while (k + 1 <= last and tags[k] == .period and tags[k + 1] == .identifier) {
                method_tok = k + 1;
                k += 2;
                if (k > last or tags[k] == .l_paren) break;
                if (tags[k] != .period) {
                    method_tok = 0;
                    break;
                }
            }
            if (method_tok == 0 or k > last or tags[k] != .l_paren) continue;

            const index = self.queryOrUnknown(*const file_cache.FileCache.CallIndex, cache.getCallIndex()) orelse continue;
            const call_node = index.by_callee_token.get(method_tok - 1) orelse continue;
            var call_buf: [1]Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, call_node) orelse continue;
            const frame = if (self.zls) |resolver| resolver.resolutionFrame() else null;
            const actual = self.queryOrUnknown(
                file_cache.FileCache.ActualCallSummary,
                cache.actualCallSummaryAt(fresh_storage.calleeQueryToken(tree, call), frame),
            ) orelse continue;
            const summary = actual.summary orelse continue;
            switch (summary.returns) {
                .borrowed_from => |idx| if (idx == 0) return local,
                else => {},
            }
        }
        return null;
    }

    /// A container pointer-capture cannot have its own storage released.
    /// Require an exact normal-return certificate for the receiver root;
    /// sub-field cleanup and error-only cleanup do not satisfy this check.
    /// A missing declaration supplies no proof; method names imply no release.
    const InteriorPtrDestructor = struct { receiver: LocalId, container: LocalId };
    fn interiorPointerDestructor(self: *Builder, call_node: Ast.Node.Index) ?InteriorPtrDestructor {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        const callee = call_full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const fa = tree.nodeData(callee).node_and_token;
        const recv = fa[0];
        if (tree.nodeTag(recv) != .identifier) return null;
        const recv_name = tree.tokenSlice(tree.nodeMainToken(recv));
        const recv_local = self.name_to_local.get(recv_name) orelse return null;
        const container = self.locals.items[@intFromEnum(recv_local)].from_container orelse return null;

        const freed = self.normalFreedReceiver(call_node) orelse return null;
        if (freed != recv_local) return null;
        return .{ .receiver = recv_local, .container = container };
    }

    /// For a call like `<recv>.alloc(...)`, `<recv>.free(...)`,
    /// `<recv>.destroy(...)`, return the LocalId of `<recv>` when
    /// it's a bare identifier resolving to a known local.  Walks
    /// through `.allocator()` chains so `arena.allocator().alloc(...)`
    /// returns `arena`.  Returns null when the receiver is itself
    /// a call (other than `.allocator()`), a stdlib namespace
    /// (`std.heap.page_allocator`), or anything else not resolvable
    /// to a single local.
    fn allocReceiverLocal(self: *Builder, call_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        const callee = call_full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const fa = tree.nodeData(callee).node_and_token;
        const cur = fa[0];
        switch (tree.nodeTag(cur)) {
            .identifier => {
                const name = tree.tokenSlice(tree.nodeMainToken(cur));
                return self.name_to_local.get(name);
            },
            .call, .call_one, .call_comma, .call_one_comma => {
                return self.arenaLocalDotAllocatorReceiver(cur);
            },
            else => return null,
        }
    }

    fn arenaBoundReceiverOfCall(self: *Builder, call_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        const callee = call_full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const fa = tree.nodeData(callee).node_and_token;
        var cur = fa[0];
        while (true) {
            switch (tree.nodeTag(cur)) {
                .identifier => {
                    const name = tree.tokenSlice(tree.nodeMainToken(cur));
                    const id = self.name_to_local.get(name) orelse return null;
                    const hint = self.locals.items[@intFromEnum(id)].init_hint;
                    if (hint == .arena_local or hint == .arena_allocator) return id;
                    return null;
                },
                .field_access => {
                    cur = tree.nodeData(cur).node_and_token[0];
                },
                // Chained call: `arena.allocator().alloc(...)`.  If
                // the inner call is `<arena_local>.allocator()`,
                // treat the outer call's receiver as arena_local.
                .call, .call_one, .call_comma, .call_one_comma => {
                    if (self.arenaLocalDotAllocatorReceiver(cur)) |arena_local| {
                        return arena_local;
                    }
                    return null;
                },
                else => return null,
            }
        }
    }

    /// Constructor-style call (method `init` / `create` / etc.) on a
    /// type, whose first argument is an arena-bound local.  Treats
    /// the return value as bound to that arena's lifetime — covers
    /// user-defined types like `Log.init(arena.allocator())` where
    /// the constructed value embeds storage from the allocator.
    ///
    /// Triggered only on conventional constructor names so we don't
    /// misclassify ordinary calls that happen to take an allocator
    /// for transient internal use (e.g. `vm.execute(allocator, src)`
    /// which returns a value unrelated to allocator's arena).
    fn constructorWithArenaArg(self: *Builder, call_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        const callee = call_full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const fa = tree.nodeData(callee).node_and_token;
        const method = tree.tokenSlice(fa[1]);
        if (!isConstructorName(method)) return null;
        const args = call_full.ast.params;
        if (args.len == 0) return null;
        // Walk the first arg: bare ident, or `arena.allocator()` chain.
        return self.argResolvesToArenaBound(args[0]);
    }

    /// True iff `expr` is syntactically a literal error return value
    /// (`error.X`).  Used by lowerReturn to decide whether to flush
    /// errdefers along with normal defers.  Conservative — only the
    /// directly-recognisable case; `return foo()` returning an error
    /// type stays as normal-only flush to avoid speculation.
    ///
    /// Also handles `try expr` wrapping a literal error (rare but
    /// possible: `return try error.X`).
    fn isLiteralErrorReturn(tree: *const Ast, expr: Ast.Node.Index) bool {
        switch (tree.nodeTag(expr)) {
            .error_value => return true,
            .@"try" => {
                const inner = tree.nodeData(expr).node;
                return isLiteralErrorReturn(tree, inner);
            },
            else => return false,
        }
    }

    /// True iff the returned expression is statically known to be an
    /// error value, so Zig fires errdefers on this return.  Covers:
    ///   - literal `error.X` (and `try`-wrapped) — `isLiteralErrorReturn`
    ///   - a bare identifier naming an in-scope error capture
    ///     (`catch |err|` / `else |err|`), marked `is_error_capture`.
    /// Sound under-approximation: returns of error UNIONS (`return foo()`
    /// yielding `!T`) are deliberately NOT classified here — see the
    /// rationale at the call site in `lowerReturn`.
    fn returnExprIsError(self: *const Builder, expr: Ast.Node.Index) bool {
        const tree = self.tree;
        if (isLiteralErrorReturn(tree, expr)) return true;
        if (tree.nodeTag(expr) == .identifier) {
            const name = tree.tokenSlice(tree.nodeMainToken(expr));
            if (self.name_to_local.get(name)) |lid| {
                return self.locals.items[@intFromEnum(lid)].is_error_capture;
            }
        }
        return false;
    }

    fn isConstructorName(name: []const u8) bool {
        const list = [_][]const u8{
            "init",           "create",    "new", "open",
            "fromOwnedSlice", "fromSlice",
        };
        for (list) |n| if (std.mem.eql(u8, n, name)) return true;
        return false;
    }

    /// Infer the declared type of `var x = <init>` for the case where
    /// the var_decl has no explicit type annotation.  Lets call sites
    /// later resolve `x.method()` / `x.<borrowed_field>` via the type
    /// of the constructor's receiver, even when the user wrote no
    /// `: T` annotation.
    ///
    /// Recognises:
    ///   - `T.init(...)` / `T.create(...)` / `T.new(...)` / `T.open(...)`
    ///     and the other constructor-method names.
    ///   - `try <constructor-call>` — recurses past `try`.
    ///   - `T{ ... }` and `T.{ ... }` struct literals — but NOT
    ///     anonymous `.{ ... }`, which needs the surrounding context's
    ///     type that we don't have.
    ///   - Any other call, through the callee's OWN DECLARED result type
    ///     (see [DeclaredResult]) — `const h = ctx.load(p) catch …;`
    ///     binds what `load` declared it returns, which is the only
    ///     thing on hand when the method is neither a constructor nor
    ///     spelled with a type at the call site.  Read by the caller and
    ///     passed in, so the same declaration walk serves the name below
    ///     and the binding type kept beside it.
    /// Preserve namespace qualification for method dispatch.
    fn inferTypeNameFromInit(
        self: *Builder,
        init_node: Ast.Node.Index,
        declared_result: ?DeclaredResult,
    ) ?[]const u8 {
        const tree = self.tree;
        var node = init_node;
        // Unwrap `try` and `<lhs> catch <fallback>` — both leave the
        // success-path value with the inner call's identity.
        while (true) {
            switch (tree.nodeTag(node)) {
                .@"try" => node = tree.nodeData(node).node,
                .@"catch" => node = tree.nodeData(node).node_and_node[0],
                else => break,
            }
        }
        const token_inferred: ?[]const u8 = switch (tree.nodeTag(node)) {
            .call, .call_one, .call_comma, .call_one_comma => blk: {
                var buf: [1]Ast.Node.Index = undefined;
                const call = tree.fullCall(&buf, node) orelse break :blk null;
                const callee = call.ast.fn_expr;
                if (tree.nodeTag(callee) != .field_access) break :blk null;
                const fa = tree.nodeData(callee).node_and_token;
                const method_name = tree.tokenSlice(fa[1]);
                if (!isConstructorName(method_name)) break :blk null;
                break :blk self.extractTypeName(fa[0], self.self_type);
            },
            .struct_init,
            .struct_init_comma,
            .struct_init_one,
            .struct_init_one_comma,
            => blk: {
                var buf: [2]Ast.Node.Index = undefined;
                const si = tree.fullStructInit(&buf, node) orelse break :blk null;
                const type_expr = si.ast.type_expr.unwrap() orelse break :blk null;
                break :blk self.extractTypeName(type_expr, self.self_type);
            },
            else => null,
        };
        if (token_inferred) |t| return t;
        // The callee's own DECLARED result type names what an inferred
        // binding holds, with nothing written at the declaration to
        // read: `const handle = ctx.sourceHandle(path) catch …;`
        // binds the payload of `!DocumentStore.Handle`, so
        // `&handle.document.tree` is a field chain the declarations can
        // answer even where the type engine cannot retype the call.
        // Null for a callee or a result type this file cannot read, so
        // the resolver below still decides those.
        if (declared_result) |result| return result.name;
        // ZLS fallback: handles `var x = makeThing()`, `var x =
        // some_var.method()`, `var x = ns.factory(...)` — shapes the
        // token-pattern match above can't classify because the type
        // isn't syntactically visible at the call site.
        if (self.zls) |z| {
            return self.queryOrUnknown([]const u8, z.typeReferenceOfNode(init_node));
        }
        return null;
    }

    /// Resolve an expression node to an arena-bound LocalId if
    /// possible: bare identifier whose init_hint is arena_local /
    /// arena_allocator, OR a call `<arena_local>.allocator()`.
    fn argResolvesToArenaBound(self: *Builder, arg_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        switch (tree.nodeTag(arg_node)) {
            .identifier => {
                const name = tree.tokenSlice(tree.nodeMainToken(arg_node));
                const id = self.name_to_local.get(name) orelse return null;
                const hint = self.locals.items[@intFromEnum(id)].init_hint;
                if (hint == .arena_local or hint == .arena_allocator) return id;
                return null;
            },
            .call, .call_one, .call_comma, .call_one_comma => {
                return self.arenaLocalDotAllocatorReceiver(arg_node);
            },
            else => return null,
        }
    }

    /// Specifically detect `<arena_local>.allocator()` — receiver
    /// must be a bare identifier resolving to an arena_local.  Used
    /// to mint the .arena_allocator alias.
    fn arenaLocalDotAllocatorReceiver(self: *Builder, call_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        const callee = call_full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const fa = tree.nodeData(callee).node_and_token;
        const method = tree.tokenSlice(fa[1]);
        if (!std.mem.eql(u8, method, "allocator")) return null;
        const recv = fa[0];
        if (tree.nodeTag(recv) != .identifier) return null;
        const name = tree.tokenSlice(tree.nodeMainToken(recv));
        const id = self.name_to_local.get(name) orelse return null;
        if (self.locals.items[@intFromEnum(id)].init_hint != .arena_local) return null;
        return id;
    }

    fn sliceCallValue(self: *Builder, node: Ast.Node.Index) bool {
        switch (self.tree.nodeTag(node)) {
            .call, .call_one, .call_comma, .call_one_comma => {},
            else => return false,
        }
        const frame = self.integerResolutionFrame() orelse return false;
        return self.resolvedBindingValueType(frame, node, false).slice_header;
    }

    fn classifyCall(self: *Builder, call_node: Ast.Node.Index) ExprKind {
        const tree = self.tree;
        const projected = self.arrayCallSource(call_node);
        if (!self.sliceCallValue(call_node)) if (projected) |source| return source;

        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return .unknown;
        const callee_node = call_full.ast.fn_expr;
        const args = call_full.ast.params;

        switch (tree.nodeTag(callee_node)) {
            .field_access => {
                const fa_data = tree.nodeData(callee_node);
                const recv_node = fa_data.node_and_token[0];
                const method_tok = fa_data.node_and_token[1];
                const method_name = tree.tokenSlice(method_tok);

                // Distinguish method-style (`obj.f(args)` where
                // `obj` is a local — receiver IS arg 0) from
                // same-file namespace-style (`Type.f(args)` where
                // `Type` is the containing struct's name —
                // receiver IS the namespace, not a logical arg).
                // Without this, an inferred
                // `@returns borrowed_from(0)` on `Type.init(slice)`
                // would resolve param 0 to `Type` itself, missing
                // the actual borrow source.
                const recv_is_local = blk: {
                    if (tree.nodeTag(recv_node) != .identifier) break :blk false;
                    const recv_name = tree.tokenSlice(tree.nodeMainToken(recv_node));
                    break :blk self.name_to_local.contains(recv_name);
                };

                // 1. Same-file FnSummary hit — typed lookup only.
                if (self.cache) |c| {
                    if (self.receiverTypeOfNode(recv_node)) |ty| {
                        if (self.queryOrUnknown(*const fn_summary.FnSummary, c.summaryByMethod(ty, method_name))) |s| {
                            if (self.applySummaryReturnsToCall(s.returns, recv_node, args, recv_is_local)) |k| return k;
                        }
                    }
                }

                return projected orelse .unknown;
            },
            .identifier => {
                const raw_name = tree.tokenSlice(tree.nodeMainToken(callee_node));
                const fn_name = self.resolveBoundCallee(raw_name);
                if (self.cache) |c| {
                    if (self.queryOrUnknown(*const fn_summary.FnSummary, c.summaryByName(fn_name))) |s| {
                        if (self.applySummaryReturnsToCall(s.returns, callee_node, args, false)) |k| return k;
                    }
                }
                return projected orelse .unknown;
            },
            else => return .unknown,
        }
    }

    /// Walk every token in `expr_node` and emit a `.use` stmt for each
    /// identifier that resolves to a known local.  Skips identifiers
    /// preceded by `.` (field/method names) or `&` (address-of doesn't
    /// read the value).  Optional `skip_local` is excluded — used by
    /// assign to avoid emitting a use for the LHS target.  Dedupes so
    /// repeated mentions of the same local only emit one `.use`.
    const FieldRef = struct { parent: LocalId, name: []const u8 };

    /// Return a `{ parent, name }` ref for a LHS expression
    /// anchored at a known local.  Walks through `field_access`
    /// AND `array_access` nodes to find the leftmost identifier;
    /// the `name` is the source-slice of everything to the right.
    ///
    /// Handles:
    ///   `obj.f`              → { obj, "f" }
    ///   `obj.f.g`            → { obj, "f.g" }
    ///   `arr[0].field`       → { arr, "[0].field" }
    ///   `arr[i].field`       → { arr, "[i].field" }
    ///   `obj.array[0].field` → { obj, "array[0].field" }
    ///
    /// Index expressions are kept as source-text (preserving
    /// literal indices like `[0]`, variable indices like `[i]`,
    /// even compound expressions like `[i+1]`).  This means
    /// reads/writes with IDENTICAL index source-text share a
    /// state-key — `arr[0].f` matches `arr[0].f` but NOT
    /// `arr[1].f`, and `arr[i].f` matches another `arr[i].f` only
    /// when both spell `i` the same way.  Conservative for
    /// precision, intentional miss for "same logical index via
    /// different expression" patterns.
    ///
    /// Returns null when the chain doesn't bottom out at a bare
    /// known-local ident (`Type.field` namespace, deref, etc.).
    ///
    /// Used by lowerAssign to dispatch field-target writes to
    /// .field_assign — symmetric with the field_use prefix
    /// emission on reads — so deep-path reassignments
    /// (`o.inner.handle = fresh()`) correctly RESET the freed
    /// state recorded by R10's N-level chain inference.
    fn fieldLhsFor(self: *Builder, lhs: Ast.Node.Index) ?FieldRef {
        const tree = self.tree;
        // Walk down field_access / array_access nodes to the root.
        // Array_access nodes are only accepted when the index is a
        // LITERAL CONSTANT (`arr[0]`, not `arr[i]`).  Variable
        // indices would mean the same source expression refers to
        // different elements on different evaluations — keying
        // state by literal source would FP across loop iterations.
        var cur = lhs;
        while (true) {
            switch (tree.nodeTag(cur)) {
                .field_access => {
                    cur = tree.nodeData(cur).node_and_token[0];
                },
                .array_access => {
                    const idx_node = tree.nodeData(cur).node_and_node[1];
                    if (tree.nodeTag(idx_node) != .number_literal) return null;
                    cur = tree.nodeData(cur).node_and_node[0];
                },
                .identifier => break,
                else => return null,
            }
        }
        // Must have actually descended from at least one
        // field_access / array_access — a bare identifier LHS
        // (`x = ...`) goes through a different path.
        if (cur == lhs) return null;
        const recv_name = tree.tokenSlice(tree.nodeMainToken(cur));
        const parent = self.name_to_local.get(recv_name) orelse return null;
        // Build the path: everything in source between the end of
        // the root ident and the end of the LHS.  If the next
        // char after the root is `.` (field access), skip it so
        // the path doesn't have a leading dot.  If it's `[`
        // (array access), include it — `[0].f` is the canonical
        // form.
        const root_tok = tree.nodeMainToken(cur);
        var first_path = root_tok + 1;
        if (tree.tokenTag(first_path) == .period) first_path += 1;
        const path = self.normalizedFieldPath(first_path, tree.lastToken(lhs)) orelse return null;
        return .{ .parent = parent, .name = path };
    }

    /// Where an access chain's address lands relative to the frame slot
    /// of the local it starts from.  `undecided` is "nobody can tell",
    /// NOT "safe": the caller must not read it as a frame borrow.
    const StorageVerdict = enum { inside, outside, undecided };

    /// One access of an address-of operand.  `node` is the
    /// sub-expression the access produces, so its resolved type is what
    /// a LATER access reads through.  `field` names the field selected,
    /// for the declaration walk; null for `?` and `[i]`.
    const AddrStep = struct {
        node: Ast.Node.Index,
        field: ?[]const u8,
        kind: enum { field, unwrap, index },
    };

    /// The access chain of an address-of operand, outermost step first,
    /// with the root local it bottoms out at.
    const AddrChain = struct {
        steps: [8]AddrStep,
        count: usize,
        /// The operand has more accesses than `steps` holds: the
        /// recorded prefix stops short of the root, so the storage
        /// walks must not answer from it.  `root` is still the local
        /// the chain bottoms out at.
        truncated: bool,
        /// Null when the walk hit a construct this pass does not model,
        /// or names no local — the chain is then undescribed.
        root: ?LocalId,
        /// Strict bit-cast input proof also needs the selected value's type.
        primitive_leaf: bool = false,
    };

    /// Split `&x.a.b` / `&x.a.?` / `&x.items[0].field` into its access
    /// steps.  Mirrors `fieldLhsFor`'s descent (field accesses and
    /// literal index steps) so the chain this describes is one the
    /// caller already accepted, plus the `?.` unwrap.  Anything else —
    /// a method call, a computed index, a deref — leaves `root` null:
    /// the pass cannot say where such an operand's address lives, and
    /// must not claim it lives in a frame slot.
    ///
    /// A chain deeper than `steps` keeps descending with `truncated`
    /// set rather than stopping at the cap.  The steps past it are not
    /// recorded, but the root is: that local is what the caller charges
    /// the address to, and abandoning the walk at the cap would drop a
    /// real stack origin without recording why.
    fn addressOperandChain(self: *Builder, operand: Ast.Node.Index) AddrChain {
        const tree = self.tree;
        var chain: AddrChain = .{ .steps = undefined, .count = 0, .truncated = false, .root = null };
        var cur = operand;
        while (true) {
            switch (tree.nodeTag(cur)) {
                .grouped_expression => cur = tree.nodeData(cur).node_and_token[0],
                .field_access => {
                    const data = tree.nodeData(cur).node_and_token;
                    if (chain.count < chain.steps.len) {
                        chain.steps[chain.count] = .{
                            .node = cur,
                            .field = tree.tokenSlice(data[1]),
                            .kind = .field,
                        };
                        chain.count += 1;
                    } else {
                        chain.truncated = true;
                    }
                    cur = data[0];
                },
                .unwrap_optional => {
                    if (chain.count < chain.steps.len) {
                        chain.steps[chain.count] = .{ .node = cur, .field = null, .kind = .unwrap };
                        chain.count += 1;
                    } else {
                        chain.truncated = true;
                    }
                    cur = tree.nodeData(cur).node_and_token[0];
                },
                .array_access => {
                    const data = tree.nodeData(cur).node_and_node;
                    if (tree.nodeTag(data[1]) != .number_literal) return chain;
                    if (chain.count < chain.steps.len) {
                        chain.steps[chain.count] = .{ .node = cur, .field = null, .kind = .index };
                        chain.count += 1;
                    } else {
                        chain.truncated = true;
                    }
                    cur = data[0];
                },
                .identifier => {
                    const name = tree.tokenSlice(tree.nodeMainToken(cur));
                    chain.root = self.name_to_local.get(name);
                    return chain;
                },
                else => return chain,
            }
        }
    }

    /// Declarations answer "does an access of `chain` leave `root`'s own
    /// storage?", from the root outward through the file model.  This
    /// is the resolver-free half of the question: it still answers when
    /// the type engine cannot see across a module boundary or through a
    /// descriptor type with no declaration to look into.
    fn declaredChainStorage(self: *Builder, root: LocalId, chain: AddrChain) StorageVerdict {
        // A truncated chain's recorded steps stop before the root, so
        // they describe no hop out of it and can prove nothing.
        if (chain.truncated) return .undecided;
        const cache = self.cache orelse return .undecided;
        // A binding whose type this file cannot NAME still names its
        // own fields: `const handle = ctx.sourceHandle(…) catch …;`
        // over a `Handle` declared in another file, read from there.
        // The name-based walk below cannot reach that declaration — the
        // spelling means nothing in this file's scope — so the type kept
        // beside the binding answers first, and the name is what the
        // walk falls back to.
        var current: file_cache.FileCache.ResolvedType = if (self.bound_types.get(root)) |bound| bound else blk: {
            const type_name = self.locals.items[@intFromEnum(root)].type_name orelse return .undecided;
            break :blk cache.resolvedTypePathAcrossImports(type_name) orelse return .undecided;
        };
        var i: usize = chain.count;
        while (i > 0) {
            i -= 1;
            const step = chain.steps[i];
            // Where an indexed element lives is the dedicated
            // `&<local>[i]` handling's question, and this walk has no
            // element type to descend into.  Stop rather than guess.
            if (step.kind == .index) return .inside;
            // The OUTERMOST access is the address itself: `&x.a.b` is
            // the slot `b` occupies inside whatever `x.a` produced,
            // so `b`'s own declared type cannot move that slot
            // anywhere.  Nothing outward of it asks anything, so stop
            // before reading a type no later step reads.
            if (i == 0) {
                if (chain.primitive_leaf) {
                    const field = current.info.findField(step.field orelse return .undecided) orelse return .undecided;
                    if (!typeSpanIsPrimitiveScalar(current.model.tree, .{ .first = field.type_first, .last = field.type_last }))
                        return .undecided;
                }
                break;
            }
            // `?.` reads the optional in place; the payload's own type
            // is the type this walk already descended into.
            if (step.kind == .unwrap) continue;
            const field_name = step.field orelse return .undecided;
            const field = current.info.findField(field_name) orelse return .undecided;
            if (field.type_first > field.type_last) return .undecided;
            const tags = current.model.tree.tokens.items(.tag);
            // A pointer field: the next access reads THROUGH it, so the
            // address lands in the pointee — caller, heap or static
            // storage — and not in the slot holding the pointer.
            if (typeRangeIsPointerValue(tags, field.type_first, field.type_last)) return .outside;
            // `?*T`: the optional is in place, but the `?.` that
            // unwraps it yields the pointer, and an access PAST that
            // unwrap reads through it.  `&x.opt.?` stops at the
            // payload slot, which is still this frame's own storage,
            // so the outside verdict needs `i >= 2`: the unwrap must
            // not itself be the outermost access.
            if (typeRangeIsOptionalPointer(current.model.tree, field.type_first, field.type_last) and
                i >= 2 and chain.steps[i - 1].kind == .unwrap)
            {
                return .outside;
            }
            current = cache.fieldType(current, field_name) orelse blk: {
                // A field spelled through an optional or a qualified
                // path has no name `fieldType` can resolve; the base
                // type name of its declaration still names the hop.
                const next = baseTypeNameOfField(current.model.tree, field) orelse
                    return .undecided;
                break :blk cache.resolvedTypeAcrossImports(next) orelse return .undecided;
            };
        }
        return .inside;
    }

    /// Type engine half of the same question: for every access past the
    /// first, the value it reads is a pointer exactly when the chain
    /// has left the root's storage.  Null answers (unresolved types)
    /// stay undecided rather than counting as by value.
    fn resolvedChainStorage(self: *Builder, chain: AddrChain) StorageVerdict {
        // Same reason: the recorded prefix stops short of the root.
        if (chain.truncated) return .undecided;
        const zls = self.zls orelse return .undecided;
        var i: usize = 0;
        while (i + 1 < chain.count) : (i += 1) {
            const base = chain.steps[i + 1];
            // An indexed element is addressed by the dedicated
            // `&<local>[i]` handling; its type says nothing about
            // whether the element lives in this frame.
            if (base.kind == .index) return .inside;
            const pointer = zls.resolvedTypeIsPointer(base.node) catch |err| {
                // A failed query is NOT a proved "not a pointer": an
                // allocation failure or a cancelled read must not be
                // filed as an answer.  Keep it for the lowering entry
                // point to raise instead of dropping it here.
                self.noteResolutionError(err);
                return .undecided;
            };
            const answer = pointer orelse return .undecided;
            if (answer) return .outside;
        }
        return .inside;
    }

    /// A positive inline-storage proof, not merely an absence of a known
    /// pointer traversal. Unknown or truncated chains cannot justify a report.
    /// The final selected field's type is irrelevant to its own slot address.
    fn chainHasInlineStorage(self: *Builder, root: LocalId, chain: AddrChain) bool {
        const declared = self.declaredChainStorage(root, chain);
        if (declared == .outside) return false;
        const resolved = self.resolvedChainStorage(chain);
        if (resolved == .outside) return false;
        return declared == .inside or resolved == .inside;
    }

    /// True if `lhs_node` is `<local>.*` where `local` is pointer-
    /// typed.  Returns the local id when it matches.  Used to
    /// dispatch deref-writes to `out_param_write` for escape checks.
    fn derefOfPointerLocal(self: *Builder, lhs_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        if (tree.nodeTag(lhs_node) != .deref) return null;
        const inner = tree.nodeData(lhs_node).node;
        if (tree.nodeTag(inner) != .identifier) return null;
        const name = tree.tokenSlice(tree.nodeMainToken(inner));
        const id = self.name_to_local.get(name) orelse return null;
        if (!self.locals.items[@intFromEnum(id)].is_pointer) return null;
        return id;
    }

    /// Save-restore-via-defer guard: the fn body has a defer that
    /// restores the same field path that this out-param write is
    /// touching.  Canonical pattern in Bun's parser:
    ///     const prev = p.field;
    ///     defer p.field = prev;
    ///     p.field = &stack_local;
    /// The stack borrow is bounded by the defer — by the time the
    /// fn returns the field has been restored to `prev`, so the
    /// stack-local pointer never escapes the frame.  Tokens after
    /// the matched `defer` are compared byte-for-byte against the
    /// source slice for `<recv>.<path>` to honour multi-segment
    /// paths (`p.fn_only_data_visit.class_name_ref`).
    fn fieldPathRestoredByDefer(
        self: *const Builder,
        recv_name: []const u8,
        path: []const u8,
    ) bool {
        if (self.fieldPathRestoredViaDeferKw(recv_name, path)) return true;
        if (self.fieldPathSaveRestoredDirectly(recv_name, path)) return true;
        return self.fieldPathOverwrittenByNonBorrow(recv_name, path);
    }

    /// Scope-bounded-install detection via tail-position consumer call.
    ///
    /// Recognise the canonical pattern:
    ///   recv.field = &local;
    ///   recv.method(...);   // synchronous consumer; uses install
    ///   return;             // fn ends within K stmts of install
    ///
    /// Specifically, after the install at `install_tok`:
    ///   1. Within K_SCAN tokens, a call `recv.<m>(...)` on the SAME
    ///      receiver appears at the same brace depth as the install.
    ///   2. The fn's CLOSING brace (`fn_body_last`) is within
    ///      K_TAIL_TOKENS of the matched call's `)`.
    /// Both bounds are deliberately tight — this is the
    /// "install-then-run-then-return" idiom (e.g. test_command.zig's
    /// `vm_.arena = &arena; vm_.runWithAPILock(...);`), NOT the
    /// "install-then-process-then-return" pattern which has too much
    /// code between the call and fn end to be confidently bounded.
    fn installIsScopeBoundedByCall(
        self: *const Builder,
        recv_name: []const u8,
        path: []const u8,
        install_tok: Ast.TokenIndex,
    ) bool {
        _ = path;
        if (self.fn_body_last == 0) return false;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const last = self.fn_body_last;
        // Scan forward from after the install for `<recv> . <ident> (`.
        var t: Ast.TokenIndex = install_tok;
        // Skip the install's own statement (find next `;`).
        while (t <= last and tags[t] != .semicolon) : (t += 1) {}
        if (t > last) return false;
        t += 1;
        // Bounded scan.
        const k_scan: u32 = 200;
        const scan_end: Ast.TokenIndex = if (t + k_scan <= last) t + k_scan else last;
        while (t + 3 <= scan_end) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t), recv_name)) continue;
            if (tags[t + 1] != .period) continue;
            if (tags[t + 2] != .identifier) continue;
            if (tags[t + 3] != .l_paren) continue;
            // Found `recv.<method>(`.  Find matching `)`.
            const close = tokens.matchParen(tags, t + 3, last) orelse continue;
            // Require fn end (closing `}` of fn body) within K_TAIL
            // tokens after the call's `)`.  In source: typically `;`
            // then `}` or `;` then a 1-2 stmt tail then `}`.
            const k_tail: u32 = 32;
            const tail_end: Ast.TokenIndex = if (close + k_tail <= last) close + k_tail else last;
            // The fn_body_last token IS the closing `}`.  Check it's
            // within tail_end.
            if (last <= tail_end) return true;
            return false;
        }
        return false;
    }

    /// Scope-bounded-install detection via cross-fn (same-file)
    /// read/clear summary.
    ///
    /// At the install `recv.field = &local`, look forward in the fn
    /// body for a call to a SAME-FILE fn whose summary records a
    /// write to `<arg>.field` for some arg position — where `recv`
    /// (or a field path through it) is passed at that arg position.
    /// If found, the install is consumed by that call: the borrow's
    /// lifetime is bounded by the call's execution.
    ///
    /// Conservative — only matches direct `<fn>(recv, ...)` /
    /// `<recv>.<method>(...)` shapes against summaries known in our
    /// file model.  Cross-file calls (the bun install/plugin cases)
    /// require ZLS or external summary infrastructure and remain
    /// uncovered by this path.
    fn installIsConsumedByCrossFnRead(
        self: *Builder,
        recv_name: []const u8,
        path: []const u8,
        install_tok: Ast.TokenIndex,
    ) bool {
        const cache = self.cache orelse return false;
        const model = self.modelOrNull(cache) orelse return false;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const last = self.fn_body_last;
        if (last == 0) return false;
        // Receiver's type — required for cross-file method lookup.
        const recv_lid = self.name_to_local.get(recv_name) orelse return false;
        const recv_type_name = self.locals.items[@intFromEnum(recv_lid)].type_name;
        // Walk forward from the install for the next 200 tokens
        // looking for a call `<fn>(<args>)` or `<recv>.<method>(<args>)`.
        var t: Ast.TokenIndex = install_tok;
        while (t <= last and tags[t] != .semicolon) : (t += 1) {}
        if (t > last) return false;
        t += 1;
        const k_scan: u32 = 200;
        const scan_end: Ast.TokenIndex = if (t + k_scan <= last) t + k_scan else last;
        while (t + 1 <= scan_end) : (t += 1) {
            if (tags[t] != .identifier) continue;
            // Resolve fn name: either bare `<fn>(` or `<recv>.<m>(`.
            // For the method form, track the call's receiver's name
            // so we can resolve its type for cross-file method lookup.
            var fn_name: []const u8 = "";
            var call_recv_name: ?[]const u8 = null;
            var is_method_on_recv: bool = false;
            if (t + 1 <= scan_end and tags[t + 1] == .l_paren) {
                fn_name = tree.tokenSlice(t);
            } else if (t + 3 <= scan_end and
                tags[t + 1] == .period and
                tags[t + 2] == .identifier and
                tags[t + 3] == .l_paren)
            {
                fn_name = tree.tokenSlice(t + 2);
                call_recv_name = tree.tokenSlice(t);
                if (std.mem.eql(u8, tree.tokenSlice(t), recv_name)) is_method_on_recv = true;
            } else {
                continue;
            }
            // Find paren args.
            var lp: Ast.TokenIndex = t;
            while (lp <= scan_end and tags[lp] != .l_paren) : (lp += 1) {}
            if (lp > scan_end) continue;
            const close = tokens.matchParen(tags, lp, last) orelse continue;
            // Cheap check: recv_name appears as a bare identifier in args
            // (no `.` before it), OR the call IS a method on recv.
            var has_recv: bool = is_method_on_recv;
            if (!has_recv) {
                var k: Ast.TokenIndex = lp + 1;
                while (k < close) : (k += 1) {
                    if (tags[k] != .identifier) continue;
                    if (!std.mem.eql(u8, tree.tokenSlice(k), recv_name)) continue;
                    if (k > 0 and tags[k - 1] == .period) continue;
                    has_recv = true;
                    break;
                }
            }
            if (!has_recv) continue;
            // Try same-file lookup first.  Top-level fn or method on
            // any type defined here.
            const local_decl: ?Ast.Node.Index = blk: {
                for (model.fns) |f| {
                    if (std.mem.eql(u8, f.name, fn_name)) break :blk f.fn_decl;
                }
                for (model.types) |ti| {
                    if (ti.findMethod(fn_name)) |m| break :blk m.fn_decl;
                }
                break :blk null;
            };
            if (local_decl) |fn_decl| {
                if (calledFnTouchesParamField(self.tree, fn_decl, path)) return true;
                t = close;
                continue;
            }
            // Cross-file: method call on some receiver whose type we
            // can resolve.  Two cases:
            //   1. The method IS on the install's receiver: type = recv's type
            //   2. The method is on a DIFFERENT local (e.g.
            //      `plugin.callOnBeforeParsePlugins(this, ...)`)
            //      — type = that local's declared type.
            // Foreign tree from findMethodAcrossImports is used for
            // the body walk; its token indices are distinct from ours.
            if (call_recv_name) |crn| {
                const call_recv_type: ?[]const u8 = blk: {
                    if (is_method_on_recv) break :blk recv_type_name;
                    const lid = self.name_to_local.get(crn) orelse break :blk null;
                    break :blk self.locals.items[@intFromEnum(lid)].type_name;
                };
                if (call_recv_type) |tn| {
                    if (cache.findMethodAcrossImports(tn, fn_name)) |rm| {
                        if (calledFnTouchesParamField(rm.tree, rm.method.fn_decl, path)) return true;
                    }
                }
            }
            t = close;
        }
        return false;
    }

    /// Variant 3 — any later overwrite to `<recv>.<path>` with a
    /// non-stack-borrow RHS bounds the stack-escape: the borrowed
    /// pointer is replaced before the fn returns.  Detect a
    /// `<recv>.<path> = <ident>;` (identifier RHS, not preceded by
    /// `&` or `.{`) anywhere in the fn body.  The if-expr capture
    /// save form (`const parent = if (this.ctx) |c| ... else null;`
    /// → `this.ctx = parent;`) doesn't match the structured
    /// save-restore detector but still bounds the borrow.
    fn fieldPathOverwrittenByNonBorrow(
        self: *const Builder,
        recv_name: []const u8,
        path: []const u8,
    ) bool {
        if (self.fn_body_last == 0) return false;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const expected_lhs_len = recv_name.len + 1 + path.len;
        var t: Ast.TokenIndex = self.fn_body_first;
        while (t + 4 <= self.fn_body_last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t), recv_name)) continue;
            const lhs_start = tree.tokens.items(.start)[t];
            if (lhs_start + expected_lhs_len > tree.source.len) continue;
            const got_lhs = tree.source[lhs_start .. lhs_start + expected_lhs_len];
            if (!std.mem.startsWith(u8, got_lhs, recv_name)) continue;
            if (got_lhs[recv_name.len] != '.') continue;
            if (!std.mem.eql(u8, got_lhs[recv_name.len + 1 ..], path)) continue;
            // Walk past whitespace to `=`.
            var b: usize = lhs_start + expected_lhs_len;
            while (b < tree.source.len and (tree.source[b] == ' ' or tree.source[b] == '\t')) : (b += 1) {}
            if (b >= tree.source.len or tree.source[b] != '=') continue;
            // Reject compound assignment (`==`/`<=`).  `=` next char.
            if (b + 1 < tree.source.len) {
                const next = tree.source[b + 1];
                if (next == '=') continue;
            }
            b += 1;
            while (b < tree.source.len and (tree.source[b] == ' ' or tree.source[b] == '\t')) : (b += 1) {}
            if (b >= tree.source.len) continue;
            // Reject `&<ident>` (would still be stack-borrow) and
            // `.{...}` struct-init forms.  Accept a bare identifier-
            // start char.
            const c = tree.source[b];
            if (c == '&' or c == '.') continue;
            if (!(c == '_' or (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z'))) continue;
            return true;
        }
        return false;
    }

    /// True iff the body of `fn_decl` reads or writes the field path
    /// `path` through ANY of its parameters: i.e. `<param>.<path>`
    /// appears anywhere in the body.  Conservative: any reference
    /// (read OR write) is treated as "consumed during the call",
    /// since at minimum the install's value is observed and the
    /// borrow lifetime is bounded by the call's execution.
    fn calledFnTouchesParamField(
        tree: *const Ast,
        fn_decl: Ast.Node.Index,
        path: []const u8,
    ) bool {
        var proto_buf: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buf, fn_decl) orelse return false;
        const body = tokens.bodyOf(tree, fn_decl) orelse return false;
        const tags = tree.tokens.items(.tag);
        const body_first = tree.firstToken(body);
        const body_last = tree.lastToken(body);
        // Collect param names.
        var param_names_buf: [16][]const u8 = undefined;
        var n: usize = 0;
        var it = proto.iterate(tree);
        while (it.next()) |param| {
            if (n == param_names_buf.len) break;
            const name_tok = param.name_token orelse continue;
            param_names_buf[n] = tree.tokenSlice(name_tok);
            n += 1;
        }
        const param_names = param_names_buf[0..n];
        if (param_names.len == 0) return false;
        // Walk body tokens for `<param>.<path-first-ident>` shapes.
        // `path` may itself be dotted (`a.b.c`); we only need the FIRST
        // segment to confirm a match into the field chain.
        const first_seg_end: usize = blk: {
            for (path, 0..) |c, i| if (c == '.') break :blk i;
            break :blk path.len;
        };
        const first_seg = path[0..first_seg_end];
        var t: Ast.TokenIndex = body_first;
        while (t + 2 <= body_last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            const id = tree.tokenSlice(t);
            var matches_param: bool = false;
            for (param_names) |p| if (std.mem.eql(u8, p, id)) {
                matches_param = true;
                break;
            };
            if (!matches_param) continue;
            if (tags[t + 1] != .period) continue;
            if (tags[t + 2] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t + 2), first_seg)) continue;
            return true;
        }
        return false;
    }

    /// Variant 1 — `defer <recv>.<path> = <ident>;` matches the LHS.
    /// Canonical form: explicit defer with the save-local on the RHS.
    fn fieldPathRestoredViaDeferKw(
        self: *const Builder,
        recv_name: []const u8,
        path: []const u8,
    ) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const starts = tree.tokens.items(.start);
        if (self.fn_body_last == 0) return false;
        var t: Ast.TokenIndex = self.fn_body_first;
        while (t <= self.fn_body_last) : (t += 1) {
            if (tags[t] != .keyword_defer) continue;
            if (t + 1 > self.fn_body_last) continue;
            const after = starts[t + 1];
            const expected_len = recv_name.len + 1 + path.len;
            if (after + expected_len > tree.source.len) continue;
            const got = tree.source[after .. after + expected_len];
            if (!std.mem.startsWith(u8, got, recv_name)) continue;
            if (got[recv_name.len] != '.') continue;
            if (!std.mem.eql(u8, got[recv_name.len + 1 ..], path)) continue;
            var b: usize = after + expected_len;
            while (b < tree.source.len and (tree.source[b] == ' ' or tree.source[b] == '\t')) : (b += 1) {}
            if (b >= tree.source.len) continue;
            if (tree.source[b] != '=') continue;
            return true;
        }
        return false;
    }

    /// Variant 2 — direct save-restore (no `defer`):
    ///     const old_X = <recv>.<path>;
    ///     <recv>.<path> = &stack_local;
    ///     ...
    ///     <recv>.<path> = old_X;   ← restore (identifier RHS)
    ///
    /// Detect via two passes over the fn body:
    ///   - any `const <ident> = <recv>.<path>;` (the save).
    ///   - any `<recv>.<path> = <ident>;` (a restore, identifier RHS).
    /// Both present anywhere in the body is a strong signal of the
    /// save-restore-by-direct-assignment idiom, so the offending
    /// stack-escape write is bounded.
    fn fieldPathSaveRestoredDirectly(
        self: *const Builder,
        recv_name: []const u8,
        path: []const u8,
    ) bool {
        if (self.fn_body_last == 0) return false;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const expected_lhs_len = recv_name.len + 1 + path.len;
        // Pass 1: look for the save `const <ident> = <recv>.<path>;`.
        var saw_save = false;
        var t: Ast.TokenIndex = self.fn_body_first;
        while (t + 4 <= self.fn_body_last) : (t += 1) {
            if (tags[t] != .keyword_const) continue;
            if (tags[t + 1] != .identifier) continue;
            if (tags[t + 2] != .equal) continue;
            // RHS source bytes must start with `<recv>.<path>` and
            // be followed by `;` (or whitespace then `;`).
            const rhs_start = tree.tokens.items(.start)[t + 3];
            if (rhs_start + expected_lhs_len > tree.source.len) continue;
            const got = tree.source[rhs_start .. rhs_start + expected_lhs_len];
            if (!std.mem.startsWith(u8, got, recv_name)) continue;
            if (got[recv_name.len] != '.') continue;
            if (!std.mem.eql(u8, got[recv_name.len + 1 ..], path)) continue;
            var b: usize = rhs_start + expected_lhs_len;
            while (b < tree.source.len and (tree.source[b] == ' ' or tree.source[b] == '\t' or tree.source[b] == '\n')) : (b += 1) {}
            if (b >= tree.source.len) continue;
            if (tree.source[b] != ';') continue;
            saw_save = true;
            break;
        }
        if (!saw_save) return false;
        // Pass 2: look for the restore `<recv>.<path> = <ident>;`.
        // The fn-body source contains the LHS substring followed by
        // ` = <ident>;`.  Scan tokens for the pattern.
        t = self.fn_body_first;
        while (t + 5 <= self.fn_body_last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(t), recv_name)) continue;
            const lhs_start = tree.tokens.items(.start)[t];
            if (lhs_start + expected_lhs_len > tree.source.len) continue;
            const got_lhs = tree.source[lhs_start .. lhs_start + expected_lhs_len];
            if (!std.mem.startsWith(u8, got_lhs, recv_name)) continue;
            if (got_lhs[recv_name.len] != '.') continue;
            if (!std.mem.eql(u8, got_lhs[recv_name.len + 1 ..], path)) continue;
            // Walk past whitespace to find `= <ident> ;`.
            var b: usize = lhs_start + expected_lhs_len;
            while (b < tree.source.len and (tree.source[b] == ' ' or tree.source[b] == '\t')) : (b += 1) {}
            if (b >= tree.source.len or tree.source[b] != '=') continue;
            b += 1;
            while (b < tree.source.len and (tree.source[b] == ' ' or tree.source[b] == '\t')) : (b += 1) {}
            // Next must be an identifier-start.
            if (b >= tree.source.len) continue;
            const c = tree.source[b];
            if (!(c == '_' or (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z'))) continue;
            // Walk the identifier and then expect `;` (ignoring whitespace).
            var e: usize = b + 1;
            while (e < tree.source.len) : (e += 1) {
                const cc = tree.source[e];
                if (cc == '_' or (cc >= 'a' and cc <= 'z') or
                    (cc >= 'A' and cc <= 'Z') or (cc >= '0' and cc <= '9')) continue;
                break;
            }
            while (e < tree.source.len and (tree.source[e] == ' ' or tree.source[e] == '\t')) : (e += 1) {}
            if (e < tree.source.len and tree.source[e] == ';') return true;
        }
        return false;
    }

    /// `.field_name = <value>` field initializer in a struct literal:
    /// return the field name token's slice.  Recognises the canonical
    /// shape (a value preceded by `.name =`), returns null on
    /// positional inits (tuples) or shapes we don't expect.
    fn fieldInitName(self: *Builder, field_value: Ast.Node.Index) ?[]const u8 {
        const tree = self.tree;
        const first = tree.firstToken(field_value);
        if (first < 3) return null;
        const tags = tree.tokens.items(.tag);
        if (tags[first - 1] != .equal) return null;
        if (tags[first - 2] != .identifier) return null;
        if (tags[first - 3] != .period) return null;
        return self.normalizedFieldComponent(first - 2);
    }

    /// Decompose default bytes in their declaring frame. This adds no
    /// definedness certificate and never resolves against caller locals.
    fn emitDiagnosticDefaultFields(self: *Builder, cur: BlockId, parent: LocalId, prefix: []const u8, frame: zls_resolver_mod.TypeResolver.ResolutionFrame, node: Ast.Node.Index, pos: SrcPos, end_pos: SrcPos, depth: u32) LoweringError!void {
        if (depth == max_classify_depth) return;
        const tree = &frame.handle.document.tree;
        var buffer: [2]Ast.Node.Index = undefined;
        const initializer = tree.fullStructInit(&buffer, node) orelse {
            try self.appendStmt(cur, .{
                .kind = .{ .field_assign = .{
                    .parent = parent,
                    .name = prefix,
                    .rhs_kind = if (self.sourceUndefinedInFrame(frame, node, 0)) .undef else .unknown,
                    .diagnostic_only = true,
                } },
                .pos = pos,
                .end_pos = end_pos,
            });
            return;
        };
        var supplied: std.StringHashMapUnmanaged(void) = .empty;
        defer supplied.deinit(self.gpa);
        for (initializer.ast.fields) |value| {
            const first = tree.firstToken(value);
            if (first < 3 or tree.tokenTag(first - 1) != .equal or tree.tokenTag(first - 2) != .identifier or tree.tokenTag(first - 3) != .period) return;
            const raw = tree.tokenSlice(first - 2);
            const name = if (std.mem.startsWith(u8, raw, "@\""))
                self.fieldLiteralNameInTree(tree, first - 2, false) orelse return
            else raw;
            try supplied.put(self.gpa, name, {});
            const path = try self.allocDottedPath(prefix, name);
            try self.emitDiagnosticDefaultFields(cur, parent, path, frame, value, pos, end_pos, depth + 1);
        }
        const actual_type = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.expectedTypeOfNode(node)) orelse return;
        const actual = if (actual_type.data == .container) actual_type.data.container else return;
        const owner_frame = frame.resolver.frameForContainer(actual);
        const owner_tree = &owner_frame.handle.document.tree;
        const declaration = owner_tree.fullContainerDecl(&buffer, actual.scope_handle.toNode()) orelse return;
        if (owner_tree.tokenTag(declaration.ast.main_token) != .keyword_struct) return;
        for (declaration.ast.members) |member| {
            const field = owner_tree.fullContainerField(member) orelse continue;
            if (field.ast.tuple_like or field.comptime_token != null) continue;
            const raw = owner_tree.tokenSlice(field.ast.main_token);
            const name = if (std.mem.startsWith(u8, raw, "@\""))
                self.fieldLiteralNameInTree(owner_tree, field.ast.main_token, false) orelse return
            else raw;
            if (supplied.contains(name)) continue;
            const value = field.ast.value_expr.unwrap() orelse continue;
            const path = try self.allocDottedPath(prefix, name);
            try self.emitDiagnosticDefaultFields(cur, parent, path, owner_frame, value, pos, end_pos, depth + 1);
        }
    }

    /// Heuristic: scan the file source for `<type_name> = union(`
    /// to detect that the named type is declared as a tagged union
    /// (`union(enum)` or `union(SomeEnum)`).  Used by
    /// `maybePartialUnionWrite` to suppress FPs on 1-field plain
    /// structs (`const NoticeResponse = struct { messages: ... };`
    /// — `this.* = .{ .messages = try ... }` looks identical to a
    /// union literal but is just a struct init, no tag-write
    /// hazard).  Substring match is accurate for canonical Zig
    /// idiom; misses cross-file decls and unusual forms like
    /// `const T: type = union(enum) { ... }` — false negatives,
    /// not positives, which is the safer side.
    fn typeIsTaggedUnion(self: *const Builder, type_name: []const u8) bool {
        const src = self.tree.source;
        var buf: [256]u8 = undefined;
        const suffix = " = union(";
        if (type_name.len + suffix.len > buf.len) return true;
        @memcpy(buf[0..type_name.len], type_name);
        @memcpy(buf[type_name.len..][0..suffix.len], suffix);
        return std.mem.indexOf(u8, src, buf[0 .. type_name.len + suffix.len]) != null;
    }

    /// True iff the token range of `node` contains a control-flow
    /// early-exit that would skip past a surrounding tagged-union
    /// literal's payload evaluation AND let the partial-write be
    /// observed — i.e. `try` (which exits via the enclosing fn's
    /// error path and runs errdefers between tag-write and return),
    /// or `catch` whose arm body contains a `return` (same: any
    /// errdefer / side-effect-in-catch-body observes the partial
    /// state).  `catch unreachable` is excluded — it aborts the
    /// process immediately, so the partial state is never read.
    /// Pure token scan; matches conservatively across nested
    /// expressions, which is fine because anonymous struct-literal
    /// payloads almost never contain unrelated `return`s.
    fn fieldValueHasEarlyExit(self: *Builder, node: Ast.Node.Index) bool {
        const tree = self.tree;
        const first = tree.firstToken(node);
        const last = tree.lastToken(node);
        const tags = tree.tokens.items(.tag);
        var catch_seen: bool = false;
        var t: Ast.TokenIndex = first;
        while (t <= last) : (t += 1) {
            // Skip past nested fn bodies — `try` inside a nested
            // dispatch closure runs at CALL TIME, not during the
            // surrounding assignment.  Without this, anonymous fn
            // values (`&struct { fn dispatch(...) !void { try ... }
            // }.dispatch`) used as payload fields trip the rule.
            if (tags[t] == .keyword_fn) {
                t = tokens.skipNestedFn(tags, t, last);
                continue;
            }
            switch (tags[t]) {
                .keyword_try => return true,
                .keyword_catch => catch_seen = true,
                .keyword_return => {
                    if (catch_seen) return true;
                },
                else => {},
            }
        }
        return false;
    }

    /// oven-sh/bun#29422: scan a struct-literal RHS for top-level fields
    /// whose payload contains an early-exit, and emit
    /// `partial_union_write` for each.  Only called from
    /// `lowerAssign` for LHS shapes that reach long-lived storage
    /// (`x.*` or `obj.field`) — pure-local writes don't have the
    /// same observable-on-error problem because the local dies
    /// with the frame.
    fn maybePartialUnionWrite(
        self: *Builder,
        cur: BlockId,
        rhs: Ast.Node.Index,
        lhs_local: LocalId,
        lhs_field: ?[]const u8,
        pos: SrcPos,
        end_pos: SrcPos,
    ) !void {
        const tree = self.tree;
        var buf: [2]Ast.Node.Index = undefined;
        const init = tree.fullStructInit(&buf, rhs) orelse return;
        // Tagged-union literals always have EXACTLY ONE field — a
        // union has one active variant per value, so the syntactic
        // shape `.{ .tag = expr }` always has a single initializer.
        // Multi-field anonymous literals are regular struct inits,
        // not unions; the tag-then-payload write-order hazard does
        // not apply to them.  This single-field gate is what
        // separates real catches from FPs like `header.* = .{ .a =
        // x, .b = y, ... };`.
        if (init.ast.fields.len != 1) return;
        const field_value = init.ast.fields[0];
        const tag_name = self.fieldInitName(field_value) orelse return;
        if (!self.fieldValueHasEarlyExit(field_value)) return;
        // Observability gate: the partial-write hazard only matters
        // if SOMEONE reads the partial-written field on the error
        // path.  In practice that means an `errdefer` in the same
        // fn that EITHER:
        //   (a) reads `<lhs>.<field>` directly (interpreting the
        //       stale union state), OR
        //   (b) calls a destructor on `<lhs>` that's known to
        //       dispatch on union tags (`<lhs>.deinit()` /
        //       `.destroy()` / `.finalize()` / `.dispose()`).
        // Errdefers that touch `<lhs>` but only OTHER fields don't
        // observe the partial state — skip.
        const lhs_name = self.locals.items[@intFromEnum(lhs_local)].name;
        if (!self.anyErrdeferObservesField(lhs_name, lhs_field)) return;
        try self.appendStmt(cur, .{
            .kind = .{ .partial_union_write = .{ .tag_name = tag_name } },
            .pos = pos,
            .end_pos = end_pos,
        });
    }

    /// True iff any `errdefer` keyword in the fn body has a body
    /// (inline statement or `{...}` block) that mentions `<name>`
    /// as an identifier.
    /// True iff some errdefer in this fn body observes the partial
    /// union state on `<lhs_name>[.lhs_field]`:
    ///   (a) reads `<lhs_name>.<lhs_field>` directly (when
    ///       `lhs_field` is non-null), OR
    ///   (b) calls a destructor on `<lhs_name>` known to dispatch
    ///       on union state — `<lhs_name>.deinit()` /
    ///       `.destroy()` / `.finalize()` / `.dispose()`, OR
    ///   (c) `lhs_field` is null (whole-struct write via `<x>.*`):
    ///       any mention of `<lhs_name>` counts (we can't be
    ///       precise about the field being partial-written).
    fn anyErrdeferObservesField(
        self: *Builder,
        lhs_name: []const u8,
        lhs_field: ?[]const u8,
    ) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const last = self.fn_body_last;
        if (last == 0) return false;
        // Start at fn_body_first, not 0 — scanning from the file start
        // would pick up errdefers from other functions defined earlier
        // in the same file and produce false positives.
        var t: Ast.TokenIndex = self.fn_body_first;
        while (t <= last) : (t += 1) {
            if (tags[t] != .keyword_errdefer) continue;
            var b = t + 1;
            if (b <= last and tags[b] == .pipe) {
                b += 1;
                while (b <= last and tags[b] != .pipe) : (b += 1) {}
                if (b > last) continue;
                b += 1;
            }
            if (b > last) continue;
            const body_end: Ast.TokenIndex = if (tags[b] == .l_brace)
                tokens.matchBrace(tags, b, last) orelse continue
            else
                tokens.findStmtSemicolon(tags, b, last) orelse continue;
            var k = b;
            while (k + 2 <= body_end) : (k += 1) {
                if (tags[k] != .identifier) continue;
                if (!std.mem.eql(u8, tree.tokenSlice(k), lhs_name)) continue;
                // Word-boundary: not a field access from elsewhere.
                if (k > 0 and tags[k - 1] == .period) continue;
                // Whole-struct write: any bare mention counts.
                if (lhs_field == null) return true;
                // Otherwise need `<lhs_name>.<follow>` where follow
                // is either the same field OR a known destructor.
                if (tags[k + 1] != .period) continue;
                if (tags[k + 2] != .identifier) continue;
                const follow = tree.tokenSlice(k + 2);
                if (std.mem.eql(u8, follow, lhs_field.?)) return true;
                if (std.mem.eql(u8, follow, "deinit") or
                    std.mem.eql(u8, follow, "destroy") or
                    std.mem.eql(u8, follow, "finalize") or
                    std.mem.eql(u8, follow, "dispose"))
                {
                    return true;
                }
            }
            t = body_end;
        }
        return false;
    }

    /// Build a dotted path `prefix.leaf` and stash the allocated bytes
    /// in `owned_paths` so the resulting slice outlives the lowering
    /// pass.  If `prefix` is null, returns `leaf` unchanged (no
    /// allocation).
    fn allocDottedPath(self: *Builder, prefix: ?[]const u8, leaf: []const u8) ![]const u8 {
        const p = prefix orelse return leaf;
        const bytes = try std.fmt.allocPrint(self.gpa, "{s}.{s}", .{ p, leaf });
        errdefer self.gpa.free(bytes);
        try self.owned_paths.append(self.gpa, bytes);
        return bytes;
    }

    /// Keep omitted values in their actual declaration namespace. The caller
    /// contributes only the destination identity, path, and diagnostic span.
    fn structDefaultFields(
        self: *Builder,
        cur: BlockId,
        parent: LocalId,
        prefix: ?[]const u8,
        supplied: *const std.StringHashMapUnmanaged(void),
        actual_container: ?zls_resolver_mod.TypeResolver.ActualType.Data.Container,
        pos: SrcPos,
        end_pos: SrcPos,
        anonymous: bool,
    ) LoweringError!bool {
        if (actual_container) |actual| {
            const scope = actual.scope_handle;
            const owner_tree = &scope.handle.document.tree;
            var buffer: [2]Ast.Node.Index = undefined;
            const declaration = owner_tree.fullContainerDecl(&buffer, scope.toNode()) orelse return false;
            const is_union = owner_tree.tokenTag(declaration.ast.main_token) == .keyword_union;
            if (is_union and supplied.count() != 1) return false;
            var active_variant = false;
            var complete = true;
            for (declaration.ast.members) |member| {
                const field = owner_tree.fullContainerField(member) orelse continue;
                if (field.ast.tuple_like) return false;
                const raw = owner_tree.tokenSlice(field.ast.main_token);
                const name = if (std.mem.startsWith(u8, raw, "@\""))
                    self.fieldLiteralNameInTree(owner_tree, field.ast.main_token, false) orelse return false
                else
                    raw;
                if (supplied.contains(name)) {
                    active_variant = true;
                    continue;
                }
                if (is_union) continue;
                const value = field.ast.value_expr.unwrap() orelse {
                    complete = false;
                    continue;
                };
                var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
                const defined = self.selectedValueInputsAtDepth(owner_tree, value, &inputs, false, 0, true);
                complete = complete and defined;
                const path = try self.allocDottedPath(prefix, name);
                const frame = (self.zls orelse return false).frameForContainer(actual);
                var initializer_buffer: [2]Ast.Node.Index = undefined;
                const nested = owner_tree.fullStructInit(&initializer_buffer, value) != null;
                const kind: ExprKind = if (!nested and self.sourceUndefinedInFrame(frame, value, 0)) .undef else .unknown;
                // Source evaluation uses the owner AST above; emitted identities
                // and positions still belong to the caller's constructor/store.
                try self.appendStmt(cur, .{
                    .kind = .{ .field_assign = .{
                        .parent = parent,
                        .name = path,
                        .rhs_kind = kind,
                        .defined = defined,
                        .diagnostic_only = self.diagnostic_fields_mode,
                    } },
                    .pos = pos,
                    .end_pos = end_pos,
                });
                if (nested) try self.emitDiagnosticDefaultFields(cur, parent, path, frame, value, pos, end_pos, 0);
            }
            return complete and (!is_union or active_variant);
        }
        const cache = self.cache orelse
            (if (self.address_cache) |*cached| cached else return anonymous);
        if (self.modelOrNull(cache) == null) return false;
        var owner = self.bound_types.get(parent) orelse owner: {
            const name = self.locals.items[@intFromEnum(parent)].type_name orelse return anonymous;
            break :owner cache.resolvedTypePathAcrossImports(name) orelse return false;
        };
        if (prefix) |path| {
            var fields = std.mem.splitScalar(u8, path, '.');
            while (fields.next()) |name| owner = cache.fieldType(owner, name) orelse return false;
        }
        if (owner.info.kind == .union_) {
            if (supplied.count() != 1) return false;
            for (owner.info.fields) |field| {
                const raw = owner.model.tree.tokenSlice(field.name_token);
                const name = if (std.mem.startsWith(u8, raw, "@\""))
                    self.fieldLiteralNameInTree(owner.model.tree, field.name_token, false) orelse return false
                else
                    raw;
                if (supplied.contains(name)) return true;
            }
            return false;
        }
        // No actual default node/context exists here. Fully explicit named
        // fields retain their certificate; every omitted remainder abstains.
        for (owner.info.fields) |field| {
            const raw = owner.model.tree.tokenSlice(field.name_token);
            const name = if (std.mem.startsWith(u8, raw, "@\""))
                self.fieldLiteralNameInTree(owner.model.tree, field.name_token, false) orelse return false
            else
                raw;
            if (!supplied.contains(name)) return false;
        }
        return true;
    }

    /// Unpack a struct-literal RHS into per-field `field_assign`
    /// statements so that aliases buried inside the literal are
    /// tracked by name.  Example: for `install.ca = .{ .str = buf }`
    /// (`parent = install`, `prefix = "ca"`), emit
    /// `field_assign(install, "ca.str", copy_of(buf))`.
    ///
    /// Recurses into nested struct literals so deeper aliases
    /// (`outer.inner = .{ .a = .{ .b = ptr } }`) are flattened too.
    /// This is purely additive — the existing `assign` /
    /// `field_assign` for the whole RHS is still emitted by the
    /// caller and remains the source of truth for the local /
    /// outermost field's own origin.
    fn unpackStructInitFields(
        self: *Builder,
        cur: BlockId,
        parent: LocalId,
        prefix: ?[]const u8,
        rhs_node: Ast.Node.Index,
        pos: SrcPos,
        end_pos: SrcPos,
        actual_container: ?zls_resolver_mod.TypeResolver.ActualType.Data.Container,
    ) LoweringError!bool {
        const tree = self.tree;
        var buf: [2]Ast.Node.Index = undefined;
        const init = tree.fullStructInit(&buf, rhs_node) orelse return true;
        var container = actual_container;
        if (container == null) if (self.integerResolutionFrame()) |frame| {
            container = self.resolvedBindingValueType(frame, rhs_node, false).container;
            if (container == null) {
                if (self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.expectedTypeOfNode(rhs_node))) |expected| {
                    if (expected.data == .container) container = expected.data.container;
                }
            }
        };
        var supplied: std.StringHashMapUnmanaged(void) = .empty;
        defer supplied.deinit(self.gpa);
        const field_count = std.math.cast(u32, init.ast.fields.len) orelse return error.SourceTooWide;
        try supplied.ensureTotalCapacity(self.gpa, field_count);
        for (init.ast.fields) |field_value| {
            const leaf = self.fieldInitName(field_value) orelse continue;
            try supplied.put(self.gpa, leaf, {});
            const path = try self.allocDottedPath(prefix, leaf);
            var rhs_kind = self.classifyExpr(field_value);
            var array_buffer: [2]Ast.Node.Index = undefined;
            if (tree.fullArrayInit(&array_buffer, field_value)) |array| {
                // Reuse the existing field/index path keys. Decomposition
                // records each hole, so the parent is not a whole-array grant.
                try self.appendStmt(cur, .{
                    .kind = .{ .field_assign = .{ .parent = parent, .name = path, .rhs_kind = .plain, .defined = true } },
                    .pos = pos,
                    .end_pos = end_pos,
                });
                for (array.ast.elements, 0..) |element, index| {
                    const element_path = path_block: {
                        const bytes = try std.fmt.allocPrint(self.gpa, "{s}[{d}]", .{ path, index });
                        errdefer self.gpa.free(bytes);
                        try self.owned_paths.append(self.gpa, bytes);
                        break :path_block bytes;
                    };
                    var assignment: @TypeOf(@as(StmtKind, undefined).field_assign) = .{
                        .parent = parent,
                        .name = element_path,
                        .rhs_kind = self.classifyExpr(element),
                        .diagnostic_only = self.diagnostic_fields_mode,
                    };
                    assignment.defined = if (self.diagnostic_fields_mode) false else self.valueInputs(element, &assignment.inputs);
                    if (self.diagnostic_fields_mode) self.selectedDiagnosticValueInputs(element, &assignment.selected_inputs, 0);
                    try self.appendStmt(cur, .{ .kind = .{ .field_assign = assignment }, .pos = self.posOf(element), .end_pos = self.endPosOf(element) });
                }
                continue;
            }
            // Fixed-array undef skip: when the field's declared type
            // is `[N]T` (a fixed-size array, not a slice), `<field>
            // = undefined` leaves the array's CONTENTS undef but
            // `.len`/`.ptr` are comptime-defined.  Reading `.len`
            // (`if (arr.len > X) ...`) is therefore safe.
            // Reclassify the rhs from `.undef` → `.plain` so the
            // field doesn't get tracked as undef.
            const undefined_array = rhs_kind == .undef and self.fieldHasFixedArrayType(parent, path);
            if (undefined_array and !self.diagnostic_fields_mode) rhs_kind = .plain;
            var inputs: [8]?LocalId = .{null} ** 8;
            var selected: [8]?cfg_types.ValueInput = .{null} ** 8;
            const defined = if (self.diagnostic_fields_mode) false else self.valueInputs(field_value, &inputs);
            if (self.diagnostic_fields_mode) self.selectedDiagnosticValueInputs(field_value, &selected, 0);
            const store_index = self.block_stmts.items[@intFromEnum(cur)].items.len;
            try self.appendStmt(cur, .{
                .kind = .{ .field_assign = .{
                    .parent = parent,
                    .name = path,
                    .rhs_kind = rhs_kind,
                    .defined = defined,
                    .inputs = inputs,
                    .selected_inputs = selected,
                    .diagnostic_only = self.diagnostic_fields_mode,
                } },
                .pos = pos,
                .end_pos = end_pos,
            });
            if (undefined_array and !self.diagnostic_fields_mode) try self.appendStmt(cur, .{
                .kind = .{ .field_assign = .{ .parent = parent, .name = path, .rhs_kind = .undef, .diagnostic_only = true } },
                .pos = pos,
                .end_pos = end_pos,
            });
            const complete = try self.unpackStructInitFields(cur, parent, path, field_value, pos, end_pos, null);
            self.block_stmts.items[@intFromEnum(cur)].items[store_index].kind.field_assign.defined =
                defined and complete;
        }
        const anonymous = prefix == null and init.ast.type_expr == .none and
            self.locals.items[@intFromEnum(parent)].type_name == null and
            self.fill.declaredTypeSpanOfLocal(parent) == null and self.paramTypeSpanOfLocal(parent) == null;
        return self.structDefaultFields(cur, parent, prefix, &supplied, container, pos, end_pos, anonymous);
    }

    /// True iff the field at the dotted `path` (under `parent`'s type)
    /// has a declared type of the shape `[N]T` (fixed-size array).
    /// Resolves the path through the file model + cross-file index
    /// (via the cache).  Returns false when any step fails — caller
    /// then keeps the original `.undef` classification.
    fn fieldHasFixedArrayType(
        self: *Builder,
        parent: LocalId,
        path: []const u8,
    ) bool {
        const cache = self.cache orelse return false;
        const parent_ty = self.locals.items[@intFromEnum(parent)].type_name orelse return false;
        var current = cache.resolvedTypePathAcrossImports(parent_ty) orelse return false;
        var rest = path;
        // Walk the dotted path one segment at a time, descending
        // into nested field types as we go.
        while (rest.len > 0) {
            const tags = current.model.tree.tokens.items(.tag);
            const dot_at = std.mem.indexOfScalar(u8, rest, '.');
            const seg = if (dot_at) |i| rest[0..i] else rest;
            const field = current.info.findField(seg) orelse return false;
            const remainder = if (dot_at) |i| rest[i + 1 ..] else "";
            if (remainder.len == 0) {
                // Last segment: check the field's type tokens for
                // a leading `[` followed by a non-`]` (i.e. fixed
                // array, NOT a `[]` slice).
                if (field.type_first > field.type_last) return false;
                var t: Ast.TokenIndex = field.type_first;
                // Peel `?`/`const` wrappers.
                while (t <= field.type_last) : (t += 1) {
                    switch (tags[t]) {
                        .question_mark, .keyword_const => continue,
                        else => break,
                    }
                }
                if (t > field.type_last) return false;
                if (tags[t] != .l_bracket) return false;
                if (t + 1 > field.type_last) return false;
                // Slice `[]` / `[*]` / `[*c]` etc. — the next token
                // is `]` (slice) or `*` (many-item pointer).  We
                // want literal arrays: `[N]` / `[N:S]` where N is a
                // number / identifier (not `]` or `*`).
                return tags[t + 1] != .r_bracket and tags[t + 1] != .asterisk;
            }
            current = cache.fieldType(current, seg) orelse return false;
            rest = remainder;
        }
        return false;
    }

    /// Write only the storage root. Index operands are inputs, not targets.
    ///
    /// `@field(<root>, <selector>) = v` names ONE field of `<root>`, chosen
    /// by a comptime selector the builder cannot resolve.  It writes the
    /// root's storage and reads the selector (the root is not read), but
    /// no single such store defines the whole value, so it grants no fill
    /// credit (`initializes = false`).  Only `exhaustiveFieldFill`'s
    /// complete-enumeration proof may clear the undefined seed.
    fn emitWritesInLhs(
        self: *Builder,
        lhs_node: Ast.Node.Index,
        cur: BlockId,
    ) !void {
        const tree = self.tree;
        var node = lhs_node;
        var through_index = false;
        var through_field_builtin = false;
        while (true) {
            switch (tree.nodeTag(node)) {
                .array_access => {
                    const pair = tree.nodeData(node).node_and_node;
                    try self.emitUsesInExpr(pair[1], cur, null);
                    node = pair[0];
                    through_index = true;
                },
                .field_access => node = tree.nodeData(node).node_and_token[0],
                .deref => node = tree.nodeData(node).node,
                .grouped_expression => node = tree.nodeData(node).node_and_token[0],
                .builtin_call_two, .builtin_call_two_comma => {
                    if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), "@field")) {
                        try self.emitUsesInExpr(node, cur, null);
                        return;
                    }
                    const args = tree.nodeData(node).opt_node_and_opt_node;
                    const root = args[0].unwrap() orelse {
                        try self.emitUsesInExpr(node, cur, null);
                        return;
                    };
                    const selector = args[1].unwrap() orelse {
                        try self.emitUsesInExpr(node, cur, null);
                        return;
                    };
                    try self.emitUsesInExpr(selector, cur, null);
                    through_field_builtin = true;
                    node = root;
                },
                .identifier => {
                    const local = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(node))) orelse return;
                    try self.appendStmt(cur, .{
                        .kind = .{ .pointer_write = .{
                            .target = local,
                            .initializes = !through_field_builtin,
                            .payload_only = through_index,
                        } },
                        .pos = self.posOf(lhs_node),
                        .end_pos = self.endPosOf(lhs_node),
                    });
                    return;
                },
                else => {
                    try self.emitUsesInExpr(node, cur, null);
                    return;
                },
            }
        }
    }

    fn emitUsesInExpr(
        self: *Builder,
        expr_node: Ast.Node.Index,
        cur: BlockId,
        skip_local: ?LocalId,
    ) !void {
        const tree = self.tree;
        const first = tree.firstToken(expr_node);
        const last = tree.lastToken(expr_node);
        const tags = tree.tokens.items(.tag);
        if (self.cache == null and self.address_cache == null) {
            self.address_cache = file_cache.FileCache.init(self.gpa, tree);
        }
        const address_cache = self.cache orelse &self.address_cache.?;

        // Use the whole-expression pos for every emitted stmt.  Per-
        // token positions (posOfToken) are O(byte_offset) — calling
        // that once per identifier turns analysis quadratic on large
        // files.  Coarser diagnostic, but cheap.
        const pos = self.posOf(expr_node);
        const end_pos = self.endPosOf(expr_node);

        var used: std.AutoArrayHashMapUnmanaged(LocalId, void) = .empty;
        defer used.deinit(self.gpa);
        var aw: std.AutoArrayHashMapUnmanaged(LocalId, void) = .empty;
        defer aw.deinit(self.gpa);

        // Comptime-only builtin parens: `@TypeOf(local)`, `@sizeOf`,
        // `@alignOf`, `@typeInfo`, etc. don't EVALUATE their argument
        // at runtime — they query the type.  Idents inside such a
        // paren range must NOT be treated as runtime reads, or
        // `var x: T = undefined; @sizeOf(@TypeOf(x))` trips use_undefined.
        var paren_depth: u32 = 0;
        var comptime_skip_active: bool = false;
        var comptime_skip_until: u32 = 0;
        // Track the destination-arg region of write-through builtins
        // (`@memcpy(dest, src)`, `@memset(dest, val)`).  The first
        // argument is WRITTEN, not READ — emitting a .use / .field_use
        // for tokens in that region would fire spurious use-undefined
        // on the common `var buf: [N]u8 = undefined; @memcpy(buf, …)`
        // shape.  Active from the `(` after `@memcpy`/`@memset` until
        // the comma that separates the first arg from the rest.
        var write_dest_skip_active: bool = false;
        // The SOURCE side of those same builtins, which is the
        // mirror image: past the first comma every argument is an
        // input, and `@memcpy(ptr[0..out.len], out[0..])` moves the
        // whole contents of `out` out of it — the elements no store
        // wrote included.
        var memcpy_src_active: bool = false;
        var write_dest_skip_depth: u32 = 0;
        // The paren depth the SOURCE region opened at, so it closes on
        // its own scope instead of borrowing the destination's flag.
        var memcpy_src_depth: u32 = 0;

        var t: Ast.TokenIndex = first;
        while (t <= last) : (t += 1) {
            const tag = tags[t];
            if (tag == .l_paren) {
                paren_depth += 1;
                if (!comptime_skip_active and t > 0 and tags[t - 1] == .builtin and
                    isComptimeOnlyBuiltin(tree.tokenSlice(t - 1)))
                {
                    comptime_skip_active = true;
                    comptime_skip_until = paren_depth - 1;
                }
                if (!write_dest_skip_active and t > 0 and tags[t - 1] == .builtin and
                    tokens.isWriteFirstArgBuiltin(tree.tokenSlice(t - 1)))
                {
                    write_dest_skip_active = true;
                    write_dest_skip_depth = paren_depth;
                    memcpy_src_active = false;
                }
                continue;
            }
            if (tag == .r_paren) {
                if (paren_depth > 0) paren_depth -= 1;
                if (comptime_skip_active and paren_depth == comptime_skip_until) {
                    comptime_skip_active = false;
                }
                // THE SOURCE REGION CLOSES ON ITS OWN DEPTH.  Resetting
                // it required `write_dest_skip_active`, which the comma
                // that opened the source region had already cleared — so
                // `memcpy_src_active` stayed on for the rest of the walk,
                // and the first `..` after `@memcpy(a, b)` anywhere later
                // in the same expression was read as a whole-array read
                // of storage nothing had read.
                if (write_dest_skip_active and paren_depth < write_dest_skip_depth) {
                    write_dest_skip_active = false;
                }
                if (memcpy_src_active and paren_depth < memcpy_src_depth) {
                    memcpy_src_active = false;
                }
                continue;
            }
            if (tag == .comma and write_dest_skip_active and paren_depth == write_dest_skip_depth) {
                // Comma at the same depth as the builtin's args ends
                // the destination region and opens the source one;
                // subsequent args are inputs.
                write_dest_skip_active = false;
                memcpy_src_active = true;
                memcpy_src_depth = paren_depth;
                continue;
            }
            if (comptime_skip_active) continue;
            // SHORT-CIRCUIT.  `false and expr` never evaluates `expr`,
            // and `true or expr` never evaluates it either, so a read
            // inside the right operand is not a read the program
            // performs and diagnosing it is a false positive on a
            // branch that does not exist.  Only those two constant
            // shapes are recognised: a real left operand's value is not
            // something a token walk can know, so those operands are
            // still read — the warning survives wherever the right side
            // really can run.
            if (tag == .keyword_and or tag == .keyword_or) {
                if (operandDecidesShortCircuit(tree, tags, t)) t = shortCircuitRhsEnd(tags, t, last);
                continue;
            }
            if (tag != .identifier) continue;
            // Supported value blocks are lowered structurally. A target in
            // an unsupported nested expression is not a speculative read or
            // a definite write.
            if (t + 1 <= last and tags[t + 1] == .equal and
                (t == 0 or tags[t - 1] != .period))
            {
                continue;
            }
            // A source-proven pointer method can read only scalar metadata
            // of a partially defined aggregate. Do not materialize its other
            // fields merely to form the implicit receiver address.
            if (t == first or tags[t - 1] != .period) {
                if (try address_cache.methodScalarReadsAt(t)) |reads| {
                    const id = self.name_to_local.get(tree.tokenSlice(t)) orelse continue;
                    if (skip_local) |s| if (id == s) continue;
                    var receiver_fields: [128]Ast.TokenIndex = undefined;
                    var receiver_field_count: usize = 0;
                    var receiver = reads.receiver;
                    while (tree.nodeTag(receiver) == .field_access) {
                        const base, const selector = tree.nodeData(receiver).node_and_token;
                        std.debug.assert(receiver_field_count < receiver_fields.len);
                        receiver_fields[receiver_field_count] = selector;
                        receiver_field_count += 1;
                        receiver = base;
                    }
                    var prefix: ?[]const u8 = null;
                    while (receiver_field_count != 0) {
                        receiver_field_count -= 1;
                        const field = tree.tokenSlice(receiver_fields[receiver_field_count]);
                        prefix = try self.allocDottedPath(prefix, field);
                    }
                    for (reads.fields[0..reads.field_count]) |field| {
                        const path = try self.allocDottedPath(prefix, field);
                        // Prefix storage still has lifetime checks. Only the
                        // deepest scalar requires a defined payload.
                        for (path, 0..) |byte, index| {
                            if (byte != '.') continue;
                            try self.appendStmt(cur, .{
                                .kind = .{ .field_use = .{
                                    .parent = id,
                                    .name = path[0..index],
                                    .lifetime_only = true,
                                } },
                                .pos = pos,
                                .end_pos = end_pos,
                            });
                        }
                        try self.appendStmt(cur, .{
                            .kind = .{ .field_use = .{ .parent = id, .name = path } },
                            .pos = pos,
                            .end_pos = end_pos,
                        });
                    }
                    continue;
                }
            }
            // Taking an address is not a value read. Only an address passed
            // into a call can act as an out-parameter write.
            if (try address_cache.addressUseAt(t)) |address| {
                const name = tree.tokenSlice(t);
                const id = self.name_to_local.get(name) orelse continue;
                self.locals.items[@intFromEnum(id)].address_taken = true;
                if (!address.may_write or address.call_node == null) continue;
                if (try self.callArgumentReadOnly(address_cache, address.call_node.?, address.address_node)) continue;
                if (skip_local) |s| if (id == s) continue;
                // A FILE-SCOPE `const` cannot be stored into at all —
                // the binding is immutable for the whole program — so
                // handing out its address cannot fill a byte of it, and
                // clearing `.undef` on the strength of a callee this
                // analysis cannot resolve is what loses the read that
                // follows.
                if (!self.localCanBeStored(id)) continue;
                var diagnostic_inputs: [2]?cfg_types.ValueInput = .{null} ** 2;
                const permutation = try self.callPermutesArray(
                    address_cache,
                    address.call_node.?,
                    address.address_node,
                    id,
                    &diagnostic_inputs,
                );
                var preserve_inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
                var preserve_whole_payload = false;
                var may_literal_undefined = false;
                const preserving = permutation or try self.callPreservesArray(
                    address_cache,
                    address.call_node.?,
                    address.address_node,
                    id,
                    &preserve_inputs,
                    &preserve_whole_payload,
                    &may_literal_undefined,
                );
                // Do not coalesce a preserving mutation with an opaque write
                // to the same root elsewhere in this expression.
                if (!preserving) {
                    const gop = try aw.getOrPut(self.gpa, id);
                    if (gop.found_existing) continue;
                }
                // `&id` handed to a callee that may write it is a
                // WRITE THROUGH the local, not a rebinding of it.
                // `.assign` would run `locals.put(target, .plain)`
                // (transferAssign) and so erase the local's resource
                // identity — an arena-typed `local` would look like a
                // plain stack value to the `return` that follows, and
                // the borrow handed back to the caller would stop
                // being an escape.  `.pointer_write` clears only
                // `.undef` → `.plain` and leaves `.heap` / `.arena`
                // alone, which is exactly the out-parameter shape.
                if (may_literal_undefined) {
                    try self.appendStmt(cur, .{
                        .kind = .{ .indexed_write = .{
                            .array = id,
                            .index = .unknown,
                            .rhs_kind = .undef,
                            .defined = false,
                        } },
                        .pos = pos,
                        .end_pos = end_pos,
                    });
                }
                try self.appendStmt(cur, .{
                    .kind = .{ .pointer_write = .{
                        .target = id,
                        .initializes = false,
                        .payload_only = self.addressesElementOf(address.address_node),
                        .preserves_complete_array = preserving,
                        .preserve_inputs = preserve_inputs,
                        .diagnostic_inputs = diagnostic_inputs,
                        .preserve_whole_payload = preserve_whole_payload,
                    } },
                    .pos = pos,
                    .end_pos = end_pos,
                });
                continue;
            }
            if (write_dest_skip_active) continue;
            // Field/method access: `.method` — skip; it's not a local.
            if (t > 0 and tags[t - 1] == .period) continue;
            // Attribute source reads to the source, not the builtin or
            // destination. Keep these spans outside the lookahead so a
            // bare source identifier and a source subscript both use them.
            const use_pos = if (memcpy_src_active) self.posOfToken(t) else pos;
            const use_end = if (memcpy_src_active) self.posOfTokenEnd(t) else end_pos;
            // Structural / comptime access on the next token that
            // doesn't actually read the local's contents:
            //   `id[..]` `id[i]`  — slice / index (creates pointer)
            //   `id.len`          — comptime length on an array
            //   `id.ptr`          — pointer-of on a slice/array
            //   `id: T`           — struct-field declaration shape;
            //                       `id` is a NAME, not a value read.
            //                       (Same for loop / block labels.)
            // Treating these as value reads produces noisy false
            // positives on stack buffers declared `= undefined` and
            // on identifiers that shadow an outer local inside an
            // anonymous struct type.
            var ident_in_method_recv_pos = false;
            if (t + 1 <= last) {
                const next = tags[t + 1];
                if (next == .l_bracket) {
                    if (self.name_to_local.get(tree.tokenSlice(t))) |array| {
                        if ((self.locals.items[@intFromEnum(array)].is_array or self.locals.items[@intFromEnum(array)].is_slice) and
                            !isRangeSubscript(tags, t + 1, last))
                        {
                            var close = t + 2;
                            var depth: u32 = 1;
                            while (close <= last) : (close += 1) {
                                if (tags[close] == .l_bracket) depth += 1;
                                if (tags[close] == .r_bracket) {
                                    depth -= 1;
                                    if (depth == 0) break;
                                }
                            }
                            if (close < last and tags[close + 1] == .equal) continue;
                            const index: cfg_types.IndexTerm = if (close <= last and close > t + 2)
                                self.indexTermTokens(t + 2, close - 1)
                            else
                                .unknown;
                            const modulo = if (close <= last and close > t + 2)
                                self.moduloIndexTokens(t + 2, close - 1)
                            else
                                null;
                            const name: ?[]const u8 = if (close == t + 3 and tags[t + 2] == .number_literal) blk: {
                                if (self.subscriptFieldPath(t, last)) |field| break :blk field.path;
                                const begin = tree.tokens.items(.start)[t + 1];
                                const finish = tree.tokens.items(.start)[close] + tree.tokenSlice(close).len;
                                break :blk tree.source[begin..finish];
                            } else null;
                            try self.appendStmt(cur, .{
                                .kind = .{ .indexed_read = .{
                                    .array = array,
                                    .index = index,
                                    .modulo = modulo,
                                    .name = name,
                                    .scaled = if (close <= last and close > t + 2) self.scaledOutputIndexTokens(t + 2, close - 1) else null,
                                } },
                                .pos = self.posOfToken(t),
                                .end_pos = if (close <= last) self.posOfTokenEnd(close) else use_end,
                            });
                            // Selecting an element also reads its selected field.
                            // Coverage and the field's resource lifetime are separate.
                            if (self.subscriptFieldPath(t, last)) |field| {
                                try self.appendStmt(cur, .{
                                    .kind = .{ .field_use = .{ .parent = array, .name = field.path } },
                                    .pos = use_pos,
                                    .end_pos = use_end,
                                });
                            }
                            // Index locals remain real reads in this walk.
                            continue;
                        }
                    }
                    // `id[…].<field>` — subscript followed by field
                    // access.  Emit a field_use with the subscript-
                    // prefixed path so the read matches what
                    // `fieldLhsFor` records on writes / frees.
                    // Scan past the matched `]` and require a `.<ident>`
                    // immediately after.
                    if (self.subscriptFieldPath(t, last)) |info| {
                        const name = tree.tokenSlice(t);
                        if (self.name_to_local.get(name)) |id| {
                            try self.appendStmt(cur, .{
                                .kind = .{ .field_use = .{ .parent = id, .name = info.path } },
                                .pos = use_pos,
                                .end_pos = use_end,
                            });
                        }
                        continue;
                    }
                    // A subscript READS what it selects.  `table[i]`
                    // is the contents of one element, and a local
                    // seeded `undefined` — or one already freed — has
                    // no contents at all.  The old arm skipped every
                    // subscript as "structural", which is why both
                    // `return out[1];` and
                    // `@memcpy(ptr[0..out.len], out[0..])` were silent
                    // over storage nobody wrote.
                    //
                    // `id[a..b]` is the one shape that reads nothing BY
                    // ITSELF: building a slice over the storage is not
                    // a read of it, so a bare range stays silent.  A
                    // single `id[i]` falls through to the shared `.use`
                    // tail below.
                    //
                    // A range on the SOURCE side of a write-first
                    // builtin IS a whole-array read:
                    // `@memcpy(ptr[0..out.len], out[0..])` moves every
                    // element, the ones no store wrote included.
                    // `memcpy_src_active` is exactly that region — open
                    // only past the comma — so a destination-side
                    // `@memcpy(buf[0..], src)` is still silent.
                    //
                    // Which ARM of a conditional value is evaluated is
                    // settled before this walk runs:
                    // [Builder.lowerReturnIfArms] gives each arm its
                    // own block under its own assumption, so a read
                    // only the dead arm has never enters a state where
                    // it happens.
                    // The `[` is what the discriminator starts INSIDE:
                    // handed the identifier it counts that bracket as an
                    // opener, so the slice's own `..` sat at depth one
                    // and no `id[a..b]` was ever recognised as a range
                    // — building a slice over undefined storage was
                    // reported as reading it.
                    if (!memcpy_src_active and isRangeSubscript(tags, t + 1, last)) continue;
                    // Fall through to the shared `.use` tail below,
                    // which reads the base identifier and emits the
                    // read once per local.
                }
                if (next == .colon) continue;
                if (next == .period and t + 2 <= last and tags[t + 2] == .identifier) {
                    const field = tree.tokenSlice(t + 2);
                    if ((std.mem.eql(u8, field, "len") or std.mem.eql(u8, field, "ptr")) and
                        !self.inlineScalarFieldChain(t, t + 2)) continue;
                    // A method name does not establish a storage write.
                    // Without a source certificate its receiver is read.
                    const is_method_call = t + 3 <= last and tags[t + 3] == .l_paren;
                    ident_in_method_recv_pos = false;
                    const name = tree.tokenSlice(t);
                    if (self.name_to_local.get(name)) |id| {
                        if (is_method_call) {
                            if (try address_cache.actualCallSummaryAt(t + 2, self.integerResolutionFrame())) |actual| {
                                const parameters = actual.callee.reference.actual_type.data.function.parameters;
                                if (actual.argument_offset == 1 and parameters.len != 0) {
                                    if (self.integerResolutionFrame()) |frame| {
                                        if (try frame.resolver.normalizedType(parameters[0].type)) |formal| {
                                            ident_in_method_recv_pos = frame.resolver.pointerSize(formal) != null;
                                        }
                                    }
                                }
                            }
                        }
                        if (!is_method_call) {
                            // Field-access read.  Emit a field_use
                            // for EVERY prefix of the dotted-chain
                            // path so:
                            //   - If `obj.f1` is freed, reading
                            //     `obj.f1.f2.f3` still fires UAF
                            //     (the "f1" prefix matches).
                            //   - If `obj.f1.f2` is freed (via R10
                            //     chain inference), reading
                            //     `obj.f1.f2.f3` ALSO fires (the
                            //     "f1.f2" prefix matches).
                            // Trailing-method idents (`obj.f1.f2.m(`)
                            // are excluded from the path by
                            // `fieldChainPath`.
                            try self.emitFieldUsePrefixes(cur, id, t, last, use_pos, use_end);
                            continue;
                        }
                    } else if (!is_method_call) {
                        continue;
                    }
                }
            }
            const name = tree.tokenSlice(t);
            const id = self.name_to_local.get(name) orelse continue;
            if (skip_local) |s| if (id == s) continue;
            const gop = try used.getOrPut(self.gpa, id);
            if (gop.found_existing) continue;
            try self.appendStmt(cur, .{
                .kind = .{ .use = .{ .local = id, .from_method_call = ident_in_method_recv_pos } },
                .pos = use_pos,
                .end_pos = use_end,
            });
        }
        try self.invalidateBuiltinAliasDestination(expr_node, cur);
    }

    /// Write-first memory builtins mutate their destination, never their
    /// source. A pointer alias can address one captured element, so an
    /// unsupported fill/copy must revoke its backing array's prior coverage.
    fn invalidateBuiltinAliasDestination(self: *Builder, node: Ast.Node.Index, block: BlockId) !void {
        const tree = self.tree;
        const token = tree.nodeMainToken(node);
        if (tree.tokenTag(token) != .builtin or
            !tokens.isWriteFirstArgBuiltin(tree.tokenSlice(token))) return;
        var destination = self.builtinFirstArgument(node) orelse return;
        while (true) {
            if (self.transparentCastSource(destination)) |source| {
                destination = source;
                continue;
            }
            switch (tree.nodeTag(destination)) {
                .array_access, .slice_open => destination = tree.nodeData(destination).node_and_node[0],
                .slice, .slice_sentinel => destination = tree.nodeData(destination).node_and_extra[0],
                else => break,
            }
        }
        const actual = self.actualLocalPath(destination) orelse return;
        if (!self.locals.items[@intFromEnum(actual.local)].is_pointer) return;
        try self.appendStmt(block, .{
            .kind = .{ .pointer_write = .{ .target = actual.local, .initializes = false } },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    /// Map a FnSummary's inferred return shape to the ExprKind we
    /// emit at the call site.  Body-shape driven; `.unknown` and
    /// `.plain` produce null (caller's existing ExprKind stands).
    fn applySummaryReturnsToCall(
        self: *Builder,
        ret: fn_summary.Returns,
        receiver_or_callee: Ast.Node.Index,
        args: []const Ast.Node.Index,
        receiver_is_arg0: bool,
    ) ?ExprKind {
        switch (ret) {
            .owned => return .owned,
            .borrowed_from => |target_idx| {
                if (receiver_is_arg0 and target_idx == 0) {
                    return self.borrowedArgumentKind(receiver_or_callee);
                }
                const explicit_idx = if (receiver_is_arg0) target_idx - 1 else target_idx;
                if (explicit_idx >= args.len) return .unknown;
                return self.borrowedArgumentKind(args[explicit_idx]);
            },
            // `.heap` — mint a HeapId at THIS call site so downstream
            // free/use tracking fires.  Same shape as a direct
            // `.heap_alloc` from the heap_alloc_patterns text match.
            .heap => {
                const hid: abstract_state.HeapId = @enumFromInt(self.next_heap);
                self.next_heap += 1;
                return .{ .heap_alloc = .{ .id = hid } };
            },
            .plain, .unknown => return null,
        }
    }

    /// A borrowed result keeps the argument's address provenance, not the
    /// payload stored at that address. In particular, `&array` supplies a
    /// defined header even when the array's elements are still undefined.
    fn borrowedArgumentKind(self: *Builder, node: Ast.Node.Index) ExprKind {
        const value = initValueNode(self, node);
        if (self.tree.nodeTag(value) == .address_of) return self.classifyExpr(value);
        return self.identifierToCopyOrUnknown(value);
    }

    /// If `node` resolves to a known local, return .copy_of(that
    /// local).  Looks through `&id` (address-of) so call args like
    /// `wrap(&local)` propagate the local's origin to the wrapper's
    /// inferred `borrowed_from`.
    fn identifierToCopyOrUnknown(self: *Builder, node: Ast.Node.Index) ExprKind {
        const tree = self.tree;
        const target = switch (tree.nodeTag(node)) {
            .identifier => node,
            .address_of => blk: {
                const inner = tree.nodeData(node).node;
                if (tree.nodeTag(inner) != .identifier) return .unknown;
                break :blk inner;
            },
            else => return .unknown,
        };
        const name = tree.tokenSlice(tree.nodeMainToken(target));
        if (self.name_to_local.get(name)) |id| return .{ .copy_of = id };
        return .unknown;
    }

    fn firstIdentifierLocal(self: *Builder, text: []const u8) ?LocalId {
        var i: usize = 0;
        // Skip leading whitespace
        while (i < text.len and (text[i] == ' ' or text[i] == '\t')) i += 1;
        const start = i;
        while (i < text.len) : (i += 1) {
            const c = text[i];
            if (!tokens.isIdentByte(c)) break;
        }
        if (i == start) return null;
        const name = text[start..i];
        return self.name_to_local.get(name);
    }

    /// Type-introspection / size-query builtins whose argument is
    /// evaluated at comptime and never read at runtime.  Idents inside
    /// these builtin parens must not count as runtime uses.
    fn isComptimeOnlyBuiltin(name: []const u8) bool {
        // `name` includes the leading `@`.
        const candidates = [_][]const u8{
            "@TypeOf",   "@sizeOf",      "@alignOf",        "@bitSizeOf",
            "@typeInfo", "@typeName",    "@hasField",       "@hasDecl",
            "@offsetOf", "@bitOffsetOf", "@fieldParentPtr",
        };
        for (candidates) |c| if (std.mem.eql(u8, name, c)) return true;
        return false;
    }

    /// Explicit zero-based fixed-array fills keep count and value dependencies.
    fn builtinArrayMemsetPrefix(
        self: *Builder,
        call_node: Ast.Node.Index,
    ) ?@TypeOf(@as(StmtKind, undefined).array_memset_prefix) {
        const tree = self.tree;
        const builtin_token = tree.nodeMainToken(call_node);
        if (tree.tokenTag(builtin_token) != .builtin or
            !std.mem.eql(u8, tree.tokenSlice(builtin_token), "@memset")) return null;
        var buffer: [2]Ast.Node.Index = undefined;
        const arguments = tree.builtinCallParams(&buffer, call_node) orelse return null;
        if (arguments.len != 2) return null;
        const slice = tree.fullSlice(arguments[0]) orelse return null;
        if (slice.ast.sentinel != .none or self.integerValue(slice.ast.start) != 0)
            return null;
        const end = slice.ast.end.unwrap() orelse return null;
        const base = slice.ast.sliced;
        if (tree.nodeTag(base) != .identifier) return null;
        const array = self.indexLocalAt(tree.nodeMainToken(base)) orelse return null;
        const info = self.locals.items[@intFromEnum(array)];
        if (!info.is_array or info.is_pointer or info.array_extent == null) return null;
        if (!self.localCanBeStored(array)) return null;
        const count = self.indexTerm(end);
        switch (count) {
            .constant => {},
            .local => |term| {
                if (term.offset != 0 or
                    !self.locals.items[@intFromEnum(term.local)].is_unsigned) return null;
            },
            else => return null,
        }
        var prefix: @TypeOf(@as(StmtKind, undefined).array_memset_prefix) = .{
            .array = array,
            .count = count,
            .rhs_kind = self.classifyExpr(arguments[1]),
        };
        prefix.defined = self.selectedValueInputs(arguments[1], &prefix.selected_inputs, false);
        return prefix;
    }

    /// Record written payload bytes independently of their value certificate.
    fn emitBuiltinPayloadWrite(self: *Builder, block: BlockId, node: Ast.Node.Index) LoweringError!void {
        const tree = self.tree;
        const token = tree.nodeMainToken(node);
        if (tree.tokenTag(token) != .builtin) return;
        const name = tree.tokenSlice(token);
        const copy = std.mem.eql(u8, name, "@memcpy");
        if (!copy and !std.mem.eql(u8, name, "@memset")) return;
        if (self.builtinArrayMemsetPrefix(node) != null) return;
        var buffer: [2]Ast.Node.Index = undefined;
        const arguments = tree.builtinCallParams(&buffer, node) orelse return;
        if (arguments.len != 2) return;
        var destination = arguments[0];
        while (tree.nodeTag(destination) == .grouped_expression)
            destination = tree.nodeData(destination).node_and_token[0];
        const slice = tree.fullSlice(destination);
        if (slice) |range| {
            if (self.integerValue(range.ast.start) != 0) return;
            destination = range.ast.sliced;
        } else if (tree.nodeTag(destination) == .address_of) {
            destination = tree.nodeData(destination).node;
        }
        if (tree.nodeTag(destination) != .identifier) return;
        const target = self.indexLocalAt(tree.nodeMainToken(destination)) orelse return;
        if (slice) |range| if (range.ast.end.unwrap()) |end| {
            const extent = self.locals.items[@intFromEnum(target)].array_extent orelse return;
            if (self.integerValue(end) != extent) return;
        };
        if (copy and self.builtinFillSourceIsDestination(node, destination)) return;
        var source = arguments[1];
        while (tree.nodeTag(source) == .grouped_expression)
            source = tree.nodeData(source).node_and_token[0];
        if (copy and tree.nodeTag(source) == .address_of) source = tree.nodeData(source).node;
        if (copy and tree.nodeTag(source) == .identifier) {
            if (self.indexLocalAt(tree.nodeMainToken(source))) |origin| {
                const source_info = self.locals.items[@intFromEnum(origin)];
                const target_info = self.locals.items[@intFromEnum(target)];
                if (!source_info.is_pointer and !target_info.is_pointer and
                    source_info.is_array and target_info.is_array and
                    source_info.array_extent != null and source_info.array_extent == target_info.array_extent)
                {
                    if (origin == target) return;
                    var inputs: [8]?cfg_types.ValueInput = .{null} ** 8;
                    inputs[0] = .{ .local = origin };
                    try self.appendStmt(block, .{
                        .kind = .{ .array_value = .{ .target = target, .source = .{ .copy_of = origin }, .selected_inputs = inputs } },
                        .pos = self.posOf(node),
                        .end_pos = self.endPosOf(node),
                    });
                    return;
                }
            }
        }
        var write: @TypeOf(@as(StmtKind, undefined).indexed_write) = .{
            .array = target,
            .index = .{ .constant = 0 },
            .rhs_kind = self.classifyExpr(source),
            .all_elements = true,
        };
        write.defined = self.selectedValueInputs(source, &write.selected_inputs, false);
        if (copy) {
            write.defined = false;
            self.selectedDiagnosticPointerInputs(source, &write.selected_inputs);
            if (tree.nodeTag(source) == .identifier) {
                if (self.indexLocalAt(tree.nodeMainToken(source))) |local| {
                    const info = self.locals.items[@intFromEnum(local)];
                    const input: ?cfg_types.ValueInput = if (info.is_slice)
                        .{ .field = .{ .parent = local, .name = "[]" } }
                    else if (info.is_pointer) selected: {
                        const value = self.pointer_value_sources.get(local) orelse
                            break :selected .{ .field = .{ .parent = local, .name = "" } };
                        break :selected switch (value) {
                            .copy_of => |owner| .{ .local = owner },
                            .field_copy_of => |field| .{ .field = .{ .parent = field.parent, .name = field.name } },
                            else => null,
                        };
                    } else null;
                    if (input) |selected| for (&write.selected_inputs) |*slot| {
                        if (slot.* != null) continue;
                        slot.* = selected;
                        break;
                    };
                }
            }
        }
        try self.appendStmt(block, .{
            .kind = .{ .indexed_write = write },
            .pos = self.posOf(node),
            .end_pos = self.endPosOf(node),
        });
    }

    /// The tracked array a write-first builtin fills ENTIRELY, or null
    /// when it fills less than all of it.
    ///
    /// `@memset(buf[0..], 0)` and `@memcpy(buf[0..], src)` store every
    /// element of a declared array, and the array's own LENGTH is what
    /// makes that provable rather than assumed: an open-ended `0..`
    /// covers `[0, len)` only for an array, because a slice's length is
    /// data and `buf[0..]` over a slice covers whatever it happens to
    /// hold.  So the destination has to be an indexed read of a local
    /// declared as an array of known extent, with the range starting at
    /// the literal zero and running either to the closing bracket or to
    /// that extent.  Anything narrower — `buf[a..b]`, `buf[i]`, a
    /// computed index — leaves elements unwritten, and crediting that
    /// would silence the read of storage nothing ever stored into.
    fn builtinWholeArrayFill(self: *const Builder, call_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const builtin_tok = tree.nodeMainToken(call_node);
        if (builtin_tok >= tags.len or tags[builtin_tok] != .builtin) return null;
        if (!tokens.isWriteFirstArgBuiltin(tree.tokenSlice(builtin_tok))) return null;
        const dest = self.builtinFirstArgument(call_node) orelse return null;
        // `buf[0..]` is a `slice_open` node, NOT an `array_access` —
        // the array is not indexed, it is Sliced, and the range is the
        // whole of it.  Only `buf[i]` parses as an indexed access, and
        // that is exactly the shape that writes ONE element and must
        // not be credited.  `slice` (`buf[0..len]`) and
        // `slice_sentinel` (`buf[0..len : sentinel]`) are the other
        // two spellings of a bounded range, and all four carry the
        // sliced expression in their first data field.
        const base: Ast.Node.Index = switch (tree.nodeTag(dest)) {
            .array_access, .slice_open => tree.nodeData(dest).node_and_node[0],
            .slice, .slice_sentinel => tree.nodeData(dest).node_and_extra[0],
            else => return null,
        };
        if (tree.nodeTag(base) != .identifier) return null;
        const id = self.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(base))) orelse return null;
        if (!self.locals.items[@intFromEnum(id)].is_array) return null;
        const decl = self.fill.declaredTypeSpanOfLocal(id) orelse return null;
        if (decl.is_const) return null;
        const extent = self.fill.declaredExtent(decl.type) orelse return null;
        const length = extent.number orelse return null;
        const open = tree.lastToken(base) + 1;
        if (open + 3 >= tags.len) return null;
        if (tags[open] != .l_bracket) return null;
        const zero = self.fill.literalValue(.{ .first = open + 1, .last = open + 1 }) orelse return null;
        if (zero != 0) return null;
        if (tags[open + 2] != .ellipsis2) return null;
        // `buf[0..]` — open-ended over a declared array, which is the
        // whole of it.  `buf[0..len]` — the same range written out, and
        // checked against the declared length rather than trusted.
        const whole: bool = if (tags[open + 3] == .r_bracket) true else blk: {
            if (open + 4 >= tags.len or tags[open + 4] != .r_bracket) return null;
            const written = self.fill.literalValue(.{ .first = open + 3, .last = open + 3 }) orelse return null;
            break :blk written == length;
        };
        if (!whole) return null;
        // The fill is only an INITIALISATION if the bytes it writes
        // came from somewhere that had them.  `@memcpy(buf[0..],
        // buf[0..])` reads the very storage it stores into — copying
        // bytes nothing ever wrote back over bytes nothing ever wrote
        // defines nothing, and crediting it silences both the read the
        // call performs and every read after it.  Any other source
        // (`@memset`'s fill value, a different array, a parameter) is
        // real data, so the credit stands.
        if (self.builtinFillSourceIsDestination(call_node, base)) return null;
        return id;
    }

    /// The FIRST argument of a builtin call — the destination of a
    /// write-first builtin.  Both spellings: `.builtin_call_two`
    /// carries its operands inline, `.builtin_call` keeps them in the
    /// extra range.
    fn builtinFirstArgument(self: *const Builder, call_node: Ast.Node.Index) ?Ast.Node.Index {
        const tree = self.tree;
        switch (tree.nodeTag(call_node)) {
            .builtin_call_two, .builtin_call_two_comma => {
                return tree.nodeData(call_node).opt_node_and_opt_node[0].unwrap();
            },
            .builtin_call, .builtin_call_comma => {
                const range = tree.nodeData(call_node).extra_range;
                const start: u32 = @intFromEnum(range.start);
                const end: u32 = @intFromEnum(range.end);
                if (end == start) return null;
                return @as(Ast.Node.Index, @enumFromInt(tree.extra_data[end - 1])); // zbc-disable-line: index-minus-one-without-zero-guard — end > start proven by `if (end == start) return null` above
            },
            else => return null,
        }
    }

    /// True when the SOURCE region of a write-first builtin names the
    /// very local its destination fills — the `@memcpy(a[0..], a[0..])`
    /// self-copy.  Both node spellings (`builtin_call_two`'s inline
    /// operands and `builtin_call`'s extra range) are covered by walking
    /// TOKENS from the comma that ends the destination to the closing
    /// paren, the same region [Builder.emitUsesInExpr] calls the source
    /// side.  An identifier there is compared against the destination
    /// local; a `.field` suffix or a subsumed argument makes it some
    /// OTHER storage and is not a self-copy.
    fn builtinFillSourceIsDestination(self: *const Builder, call_node: Ast.Node.Index, base: Ast.Node.Index) bool {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        const dest_name = tree.tokenSlice(tree.nodeMainToken(base));
        var t = tree.firstToken(call_node);
        var depth: u32 = 0;
        var in_source = false;
        const last = tree.lastToken(call_node);
        while (t <= last) : (t += 1) {
            switch (tags[t]) {
                .l_paren => depth += 1,
                .r_paren => {
                    if (in_source) return false;
                    depth -|= 1;
                },
                // The comma at the builtin's own argument depth ends the
                // destination region and opens the source one.
                .comma => if (depth == 1) {
                    in_source = true;
                },
                // A field or method name is not the storage itself.
                .identifier => if (in_source and (t == 0 or tags[t - 1] != .period)) {
                    if (std.mem.eql(u8, tree.tokenSlice(t), dest_name)) return true;
                },
                else => {},
            }
        }
        return false;
    }

    /// Authenticate every inline prefix and the scalar leaf against exact
    /// source nodes. Pointer/array descriptors and unresolved types abstain.
    fn inlineScalarFieldChain(self: *Builder, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
        return self.inlineValueFieldChain(first, last, false);
    }

    /// Broader selected-value classification is only for ancestor lifetime
    /// checks. The final aggregate field still needs a payload certificate.
    fn inlineValueFieldChain(self: *Builder, first: Ast.TokenIndex, last: Ast.TokenIndex, comptime aggregate_leaf: bool) bool {
        const cache = self.cache orelse if (self.address_cache) |*address| address else return false;
        const frame = self.integerResolutionFrame() orelse return false;
        var token = first;
        var count: usize = 0;
        while (token <= last) : (token += 2) {
            if (count == 128) return false;
            count += 1;
            if (token != first and std.mem.startsWith(u8, self.tree.tokenSlice(token), "@\"")) return false;
            const node = cache.nodeForExactSpan(first, token) orelse return false;
            if (token != first and self.tree.nodeTag(node) != .field_access) return false;
            const actual = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(node)) orelse return false;
            const normalized = self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(actual)) orelse return false;
            const tag = frame.resolver.typeTag(normalized) orelse return false;
            if (token == last) {
                return switch (tag) {
                    .int, .comptime_int, .float, .comptime_float, .bool, .@"enum" => true,
                    .@"struct" => aggregate_leaf,
                    else => false,
                };
            }
            if (aggregate_leaf and token == first and frame.resolver.pointerSize(normalized) == .one) continue;
            if (tag != .@"struct") return false;
        }
        return false;
    }

    /// Emit a `.field_use` for every PREFIX of the dotted chain
    /// starting at `obj` (token `t`): "f1", "f1.f2", "f1.f2.f3",
    /// etc.  This way a free recorded at any depth (e.g.
    /// `field_heap_free(obj, "f1")` from a shallow R8b match) and
    /// a free at the deepest path (from R10's N-level inference)
    /// both fire when the caller reads the deep access.
    fn emitFieldUsePrefixes(
        self: *Builder,
        cur: BlockId,
        parent: LocalId,
        t: Ast.TokenIndex,
        last: Ast.TokenIndex,
        pos: SrcPos,
        end_pos: SrcPos,
    ) (LoweringError)!void {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        // Caller verified tags[t+1] == `.`, tags[t+2] = ident.
        const first_field: Ast.TokenIndex = t + 2;
        var chain_end: Ast.TokenIndex = first_field;
        while (chain_end + 2 <= last and tags[chain_end + 1] == .period and tags[chain_end + 2] == .identifier) {
            chain_end += 2;
        }
        const ends_in_call = chain_end + 1 <= last and tags[chain_end + 1] == .l_paren;
        const value_projection = !ends_in_call and self.inlineValueFieldChain(t, chain_end, true);
        var borrowed_receiver = false;
        if (ends_in_call) {
            const cache = self.cache orelse if (self.address_cache) |*address| address else null;
            if (cache) |address| {
                if (try address.actualCallSummaryAt(chain_end, self.integerResolutionFrame())) |actual| {
                    const parameters = actual.callee.reference.actual_type.data.function.parameters;
                    if (actual.argument_offset == 1 and parameters.len != 0) {
                        if (self.integerResolutionFrame()) |frame| {
                            if (try frame.resolver.normalizedType(parameters[0].type)) |formal| {
                                borrowed_receiver = frame.resolver.pointerSize(formal) == .one;
                            }
                        }
                    }
                }
            }
        }
        // True when the chain terminates in `.len` or `.ptr`:
        //   `obj.iter_state.directory.path.len`
        // Reading `.len`/`.ptr` on a fixed-size array field (`[N]T`) does
        // not access the field's memory — `.len` is a comptime constant.
        // We stop the prefix chain two fields early to avoid spurious
        // use-undefined on the parent.  (For slices, `slice.len` IS a
        // runtime read; but firing on an undefined slice's `.len`-parent
        // is rare enough that the false-positive reduction is worth it.)
        const terminal = tree.tokenSlice(chain_end);
        const ends_in_len_or_ptr = !ends_in_call and !value_projection and
            (std.mem.eql(u8, terminal, "len") or std.mem.eql(u8, terminal, "ptr"));
        // Last ident to INCLUDE in the field portion.  If the chain
        // ends with `(`, the final ident is a method name — skip it.
        // If the chain ends with `.len`/`.ptr`, skip both the terminal
        // and its parent (two steps back) to suppress the common FP
        // from `fixed_array_field.len` when the array is `undefined`.
        const last_field: ?Ast.TokenIndex = if (ends_in_call)
            (if (chain_end > first_field) chain_end - 2 else null)
        else if (ends_in_len_or_ptr)
            (if (chain_end > first_field + 4) chain_end - 4 else null)
        else
            chain_end;
        if (last_field == null) return;
        if (borrowed_receiver and self.locals.items[@intFromEnum(parent)].is_pointer) {
            // Computing an inline field address still reads the pointer header.
            try self.appendStmt(cur, .{
                .kind = .{ .use = .{ .local = parent, .from_method_call = true } },
                .pos = pos,
                .end_pos = end_pos,
            });
        }
        // Emit one prefix per inclusive field ident.
        // Use the same component codec as field writes and literal unpacking.
        var f: Ast.TokenIndex = first_field;
        while (f <= last_field.?) : (f += 2) {
            const path = self.normalizedFieldPath(first_field, f) orelse continue;
            var lifetime_only = value_projection and f < last_field.?;
            if (borrowed_receiver) {
                const cache = self.cache orelse if (self.address_cache) |*address| address else null;
                if (cache) |address| {
                    if (address.nodeForExactSpan(t, f)) |receiver| {
                        if (self.integerResolutionFrame()) |frame| {
                            if (self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.typeOfNode(receiver))) |ty| {
                                if (self.queryOrUnknown(zls_resolver_mod.TypeResolver.ActualType, frame.resolver.normalizedType(ty))) |actual| {
                                    // Borrowing inline aggregate storage reads no
                                    // payload. An intervening pointer field does.
                                    if (frame.resolver.typeTag(actual) == .@"struct") lifetime_only = true;
                                }
                            }
                        }
                    }
                }
            }
            try self.appendStmt(cur, .{
                .kind = .{ .field_use = .{
                    .parent = parent,
                    .name = path,
                    .lifetime_only = lifetime_only,
                } },
                .pos = pos,
                .end_pos = end_pos,
            });
        }
    }

    /// `<id>[<literal>].<f>(.<g>)*` — return the path slice
    /// starting at `[` and extending through the final field
    /// ident.  Only LITERAL-CONSTANT subscripts are recognised
    /// (`arr[0]`, `arr[1]`) — variable indices (`arr[i]`, `arr[i+1]`)
    /// are skipped to avoid loop-iteration FPs where the same
    /// source expression refers to different elements on each
    /// iteration (most painful symptom: a loop that frees
    /// `arr[j].x` then increments `j` looks like a double-free
    /// to zbc).
    fn subscriptFieldPath(
        self: *Builder,
        t: Ast.TokenIndex,
        last: Ast.TokenIndex,
    ) ?struct { path: []const u8 } {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        if (t + 3 > last) return null;
        if (tags[t + 1] != .l_bracket) return null;
        if (tags[t + 2] != .number_literal) return null;
        if (tags[t + 3] != .r_bracket) return null;
        const pos: Ast.TokenIndex = t + 3; // `]`
        // pos now indexes the matching `]`.
        // Require `.<ident>` immediately after.
        if (pos + 2 > last) return null;
        if (tags[pos + 1] != .period) return null;
        if (tags[pos + 2] != .identifier) return null;
        // Extend the chain through further `.<ident>` segments.
        var chain_end: Ast.TokenIndex = pos + 2;
        while (chain_end + 2 <= last and tags[chain_end + 1] == .period and tags[chain_end + 2] == .identifier) {
            chain_end += 2;
        }
        // If chain ends with `(`, the last ident is a method.
        const ends_in_call = chain_end + 1 <= last and tags[chain_end + 1] == .l_paren;
        const last_field: ?Ast.TokenIndex = if (ends_in_call)
            (if (chain_end > pos + 2) chain_end - 2 else null)
        else
            chain_end;
        if (last_field == null) return null;
        // Path starts at the `[` token, ends at the last_field's end.
        const first_byte = tree.tokens.items(.start)[t + 1];
        const last_start = tree.tokens.items(.start)[last_field.?];
        const last_len = tree.tokenSlice(last_field.?).len;
        return .{ .path = tree.source[first_byte..(last_start + last_len)] };
    }

    /// Build the field-path source slice for a chain starting at
    /// `obj` (token `t`).  Token sequence: `<obj>` `.` `<f1>` (`.`
    /// `<f2>`)* [`(` …].  Returns the dotted source slice of the
    /// field segment (e.g. "f1.f2") — a single field for 1-deep,
    /// multi-segment for deeper.  When the trailing token after the
    /// final ident is `(`, that final ident is the method name and
    /// is excluded from the path.  Falls back to the immediate
    /// field name for any unexpected shape.
    fn fieldChainPath(self: *Builder, t: Ast.TokenIndex, last: Ast.TokenIndex) ?[]const u8 {
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
        // Caller has already verified tags[t+1] == `.`, tags[t+2] = ident.
        const first_field: Ast.TokenIndex = t + 2;
        var chain_end: Ast.TokenIndex = first_field;
        while (chain_end + 2 <= last and tags[chain_end + 1] == .period and tags[chain_end + 2] == .identifier) {
            chain_end += 2;
        }
        // If the chain ends with `<ident>(`, exclude that ident
        // (it's the method).
        const ends_in_call = chain_end + 1 <= last and tags[chain_end + 1] == .l_paren;
        const last_field: Ast.TokenIndex = if (ends_in_call) blk: {
            // The chain has at least 2 idents (the param's first
            // field + the method) only if chain_end > first_field.
            // If they're equal, there are NO field idents — just a
            // method call directly on the param.  Fall back to the
            // immediate ident (still emits the single field; though
            // realistically the caller's `is_method_call` branch
            // handles this path).
            if (chain_end <= first_field) break :blk first_field;
            break :blk chain_end - 2;
        } else chain_end;
        return self.normalizedFieldPath(first_field, last_field);
    }

    /// For a call-like node, return the source-text slice covering
    /// just the callee expression (the `f` in `f(...)`).  Lets pattern
    /// matches that should target the function being called avoid
    /// accidentally matching identifiers buried in the args.  Returns
    /// null when `expr_node` is not a call shape.
    fn calleeText(self: *Builder, expr_node: Ast.Node.Index) ?[]const u8 {
        const tree = self.tree;
        switch (tree.nodeTag(expr_node)) {
            .call, .call_one, .call_comma, .call_one_comma => {},
            else => return null,
        }
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, expr_node) orelse return null;
        const callee = call_full.ast.fn_expr;
        const first = tree.firstToken(callee);
        const last = tree.lastToken(callee);
        const start = tree.tokens.items(.start)[first];
        const last_start = tree.tokens.items(.start)[last];
        const last_len = tree.tokenSlice(last).len;
        return tree.source[start..(last_start + last_len)];
    }

    fn posOf(self: *Builder, node: Ast.Node.Index) SrcPos {
        return self.posOfToken(self.tree.firstToken(node));
    }

    /// End position (exclusive) — one past the last token of `node`.
    /// Used together with posOf to give diagnostics a real span the
    /// editor can highlight.
    fn endPosOf(self: *Builder, node: Ast.Node.Index) SrcPos {
        return self.posOfTokenEnd(self.tree.lastToken(node));
    }

    fn posOfToken(self: *Builder, tok: Ast.TokenIndex) SrcPos {
        const start = self.tree.tokens.items(.start)[tok];
        const lc = byteToLineCol(self.line_offsets, start);
        return .{
            .byte = start,
            .line = lc.line + 1,
            .column = lc.col + 1,
        };
    }

    /// End-of-token (exclusive) position.  Single-token analog of
    /// endPosOf.
    /// `tokenSlice` returns a window of `tree.source` that begins at
    /// `start`, so the token's own length is at most what is left of
    /// the source after `start`.  Taking the length from the slice and
    /// the end from those two `u32`s keeps the span in the width
    /// `SrcPos` records with nothing left to narrow; the start offset
    /// comes from the token table rather than from the slice pointer,
    /// so the window's own length is all that has to be converted.
    ///
    /// The bound that makes the sum safe is checked where the Builder
    /// is built — `tree.source.len` must fit `u32` with a byte of
    /// headroom under `maxInt(u32)` — so there is nothing to re-check
    /// here and nothing stored to keep in step with it.
    fn posOfTokenEnd(self: *Builder, tok: Ast.TokenIndex) SrcPos {
        const tree = self.tree;
        const start = tree.tokens.items(.start)[tok];
        const token_len = std.math.cast(u32, tree.tokenSlice(tok).len) orelse unreachable;
        const end_byte: u32 = start + token_len;
        const lc = byteToLineCol(self.line_offsets, start);
        return .{
            .byte = end_byte,
            .line = lc.line + 1,
            // The end's column on the start's line: both are offsets
            // into the same buffer, so their difference is a column.
            .column = lc.col + 1 + token_len,
        };
    }

    const PayloadCopy = struct { destination: LocalId, source: LocalId };

    fn payloadCopy(stmt: *const Stmt) ?PayloadCopy {
        const destination, const expression: *const ExprKind = switch (stmt.kind) {
            .decl => |*value| .{ value.local, &value.init_kind },
            .assign => |*value| .{ value.target, &value.rhs_kind },
            .field_assign => |*value| .{ value.parent, &value.rhs_kind },
            else => return null,
        };
        const source = switch (expression.*) {
            .copy_of => |local| local,
            .field_copy_of => |field| field.parent,
            else => return null,
        };
        return .{ .destination = destination, .source = source };
    }

    /// Select only the existing payload roots' exact staged copy lineage.
    /// The temporary destination-to-source runs die before CFG publication.
    fn selectPayloadLineage(self: *Builder) !void {
        var seed_count: usize = 0;
        for (self.locals.items) |*local| {
            if (local.tracks_array_payload) seed_count += 1;
        }
        if (seed_count == 0) return;
        var edge_count: usize = 0;
        for (self.block_stmts.items) |*block| {
            for (block.items) |*stmt| {
                if (payloadCopy(stmt) != null)
                    edge_count = std.math.add(usize, edge_count, 1) catch return error.OutOfMemory;
            }
        }
        if (edge_count == 0) return;
        const count = self.locals.items.len;
        const offset_count = std.math.add(usize, count, 1) catch return error.OutOfMemory;
        const offsets = try self.gpa.alloc(usize, offset_count);
        defer self.gpa.free(offsets);
        @memset(offsets, 0);
        for (self.block_stmts.items) |*block| {
            for (block.items) |*stmt| {
                const edge = payloadCopy(stmt) orelse continue;
                const destination: usize = @intFromEnum(edge.destination);
                std.debug.assert(destination < count and @intFromEnum(edge.source) < count);
                offsets[destination + 1] += 1;
            }
        }
        for (1..offset_count) |i| offsets[i] += offsets[i - 1];
        std.debug.assert(offsets[count] == edge_count);
        const sources = try self.gpa.alloc(LocalId, edge_count);
        defer self.gpa.free(sources);
        for (self.block_stmts.items) |*block| {
            for (block.items) |*stmt| {
                const edge = payloadCopy(stmt) orelse continue;
                const destination: usize = @intFromEnum(edge.destination);
                sources[offsets[destination]] = edge.source;
                offsets[destination] += 1;
            }
        }
        // Filling advanced each row's start to its end. Restore the starts.
        var i = count;
        while (i != 0) : (i -= 1) offsets[i] = offsets[i - 1];
        offsets[0] = 0;
        const pending = try self.gpa.alloc(LocalId, count);
        defer self.gpa.free(pending);
        var pending_count: usize = 0;
        for (self.locals.items, 0..) |*local, id| {
            if (!local.tracks_array_payload) continue;
            pending[pending_count] = @enumFromInt(id);
            pending_count += 1;
        }
        while (pending_count != 0) {
            pending_count -= 1;
            const destination: usize = @intFromEnum(pending[pending_count]);
            for (sources[offsets[destination]..offsets[destination + 1]]) |source| {
                const local = &self.locals.items[@intFromEnum(source)];
                if (local.tracks_array_payload) continue;
                local.tracks_array_payload = true;
                pending[pending_count] = source;
                pending_count += 1;
            }
        }
    }

    fn finalize(
        self: *Builder,
        tree: *const Ast,
        fn_decl: Ast.Node.Index,
        entry: BlockId,
    ) !Cfg {
        std.debug.assert(self.locals.items.len == self.integer_domains.items.len);
        try self.selectPayloadLineage();
        const blocks = try self.gpa.alloc(BasicBlock, self.blocks.items.len);
        var published_blocks: usize = 0;
        errdefer {
            for (blocks[0..published_blocks]) |block| {
                self.gpa.free(block.stmts);
                self.gpa.free(block.successors);
            }
            self.gpa.free(blocks);
        }
        for (self.blocks.items, 0..) |bb, i| {
            const stmts = try self.block_stmts.items[i].toOwnedSlice(self.gpa);
            errdefer self.gpa.free(stmts);
            const successors = try self.block_successors.items[i].toOwnedSlice(self.gpa);
            blocks[i] = .{ .id = bb.id, .stmts = stmts, .successors = successors };
            published_blocks += 1;
        }
        const locals = try self.locals.toOwnedSlice(self.gpa);
        errdefer self.gpa.free(locals);
        const integer_domains = try self.integer_domains.toOwnedSlice(self.gpa);
        errdefer self.gpa.free(integer_domains);
        const owned_paths = try self.owned_paths.toOwnedSlice(self.gpa);
        errdefer {
            for (owned_paths) |path| self.gpa.free(path);
            self.gpa.free(owned_paths);
        }
        const owned_stack_loans = try self.owned_stack_loans.toOwnedSlice(self.gpa);
        errdefer {
            for (owned_stack_loans) |loans| self.gpa.free(loans);
            self.gpa.free(owned_stack_loans);
        }
        const owned_field_layouts = try self.owned_field_layouts.toOwnedSlice(self.gpa);
        errdefer {
            for (owned_field_layouts) |fields| self.gpa.free(fields);
            self.gpa.free(owned_field_layouts);
        }
        const start = tree.tokens.items(.start)[tree.firstToken(fn_decl)];
        return .{
            .blocks = blocks,
            .entry = entry,
            // The span's end is the same exclusive token-end offset
            // `endPosOf` computes for every other position, so the
            // checked conversion lives there instead of here.
            .fn_span = .{ .start = start, .end = self.endPosOf(fn_decl).byte },
            .locals = locals,
            .integer_domains = integer_domains,
            .owned_paths = owned_paths,
            .owned_stack_loans = owned_stack_loans,
            .owned_field_layouts = owned_field_layouts,
        };
    }
};

/// True iff the return type is `noreturn` (or `!noreturn` /
/// `Errors!noreturn`).  Such fns never return normally, so any
/// stack-escape via out-param-write isn't observable by a
/// (non-existent) returning caller.  Used to skip the entire
/// stack-escape analysis on `pub fn run(...) !noreturn { ... }`
/// CLI entry points.
fn returnTypeIsNoreturn(tree: *const Ast, node: Ast.Node.Index) bool {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(node);
    const last = tree.lastToken(node);
    var t: Ast.TokenIndex = first;
    while (t <= last) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(t), "noreturn")) return true;
    }
    return false;
}

/// True iff the return-type node text starts with `*` or `[` after
/// stripping leading `?` / `E!`.  Same heuristic the Layer-1 rule uses
/// (require_borrowed_from.zig) — Node.Data variant churn between Zig
/// versions makes source-text inspection more robust than the typed
/// API.
fn returnTypeIsBorrowed(tree: *const Ast, node: Ast.Node.Index) bool {
    const first = tree.firstToken(node);
    const last = tree.lastToken(node);
    const start = tree.tokens.items(.start)[first];
    const last_start = tree.tokens.items(.start)[last];
    const last_len = tree.tokenSlice(last).len;
    const end: usize = last_start + last_len;
    var text = tree.source[start..end];
    while (text.len > 0) {
        switch (text[0]) {
            '?', '!', ' ', '\t' => text = text[1..],
            else => break,
        }
    }
    if (std.mem.indexOfScalar(u8, text, '!')) |bang| {
        text = std.mem.trimStart(u8, text[bang + 1 ..], " \t");
    }
    return text.len > 0 and (text[0] == '*' or text[0] == '[');
}

/// Returns the statements of a block node.  Zig's AST has 4 block variants
/// depending on statement count + trailing semicolon.
fn blockStmts(
    tree: *const Ast,
    block_node: Ast.Node.Index,
    buf: *[2]Ast.Node.Index,
) []const Ast.Node.Index {
    return switch (tree.nodeTag(block_node)) {
        .block, .block_semicolon => tree.extraDataSlice(tree.nodeData(block_node).extra_range, Ast.Node.Index),
        .block_two, .block_two_semicolon => blk: {
            const data = tree.nodeData(block_node);
            buf[0] = data.opt_node_and_opt_node[0].unwrap() orelse break :blk &.{};
            if (data.opt_node_and_opt_node[1].unwrap()) |second| {
                buf[1] = second;
                break :blk buf[0..2];
            }
            break :blk buf[0..1];
        },
        else => &.{},
    };
}

/// Token span of the type argument in a `@typeInfo(<T>).@"struct".fields`
/// input expression, or null unless the input's tokens are EXACTLY
/// that descriptor.  `.@"struct"` is a field of `std.builtin.Type`
/// only on the `Struct` variant, so a successful match means valid Zig
/// types the loop's element set as precisely `<T>`'s field tuple —
/// empty for a zero-field struct, which is zero-sized.
fn typeInfoStructFieldsArg(tree: *const Ast, input: Ast.Node.Index) ?TokenSpan {
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(input);
    const last = tree.lastToken(input);
    if (first >= tags.len or last >= tags.len or first > last) return null;
    if (tags[first] != .builtin or !std.mem.eql(u8, tree.tokenSlice(first), "@typeInfo")) return null;
    const lparen = first + 1;
    if (lparen >= tags.len or tags[lparen] != .l_paren) return null;

    // Balanced-paren scan for the argument list's closing paren.
    var t: Ast.TokenIndex = lparen;
    var depth: u32 = 0;
    while (t <= last) : (t += 1) {
        if (tags[t] == .l_paren) depth += 1;
        if (tags[t] == .r_paren) {
            depth -= 1;
            if (depth == 0) break;
        }
    }
    if (depth != 0) return null;
    const close = t;
    const arg_first = lparen + 1;
    if (arg_first >= close) return null;

    // `)` `.` `@"struct"` `.` `fields` — four tokens after the closing
    // paren, with no room for a further selector or index.  Zig lexes
    // `@"…"` as ONE string-identifier token (tokenizer `.saw_at_sign`),
    // so `.@"struct"` is a `.period` plus a single `.identifier`.
    if (close + 4 != last) return null;
    if (tags[close + 1] != .period) return null;
    if (tags[close + 2] != .identifier or !std.mem.eql(u8, tree.tokenSlice(close + 2), "@\"struct\"")) return null;
    if (tags[close + 3] != .period) return null;
    if (tags[close + 4] != .identifier or !std.mem.eql(u8, tree.tokenSlice(close + 4), "fields")) return null;
    return .{ .first = arg_first, .last = close - 1 };
}

/// Does the operand immediately left of the `and`/`or` at `op_tok`
/// decide the whole expression, so that nothing after the operator
/// evaluates?  Only the two constant shapes do — `false and …` and
/// `true or …` — and only when the word is a BARE literal: a name after
/// a `.` is a field selector and one inside a call is an argument, and
/// neither is the boolean this is about.
fn operandDecidesShortCircuit(tree: *const Ast, tags: []const std.zig.Token.Tag, op_tok: Ast.TokenIndex) bool {
    if (op_tok == 0) return false;
    const at = op_tok - 1;
    if (tags[at] != .identifier) return false;
    if (at > 0 and (tags[at - 1] == .period or tags[at - 1] == .l_paren)) return false;
    const word = tree.tokenSlice(at);
    return switch (tags[op_tok]) {
        .keyword_and => std.mem.eql(u8, word, "false"),
        .keyword_or => std.mem.eql(u8, word, "true"),
        else => false,
    };
}

/// Where the operand following the `and`/`or` at `op_tok` ends, given
/// the expression ends at `last`.
///
/// IT RUNS TO THE END OF THE ENCLOSING OPERAND, not to the next
/// operator: once an operand has decided the result, everything beside
/// it is dead as well, which is what makes `false and a[i] == 0 or b`
/// a shape with no read in it at all.  Nesting inside `()` / `[]` /
/// `{}` is counted so a separator that belongs to an inner expression
/// does not end it early.
fn shortCircuitRhsEnd(tags: []const std.zig.Token.Tag, op_tok: Ast.TokenIndex, last: Ast.TokenIndex) Ast.TokenIndex {
    var depth: u32 = 0;
    var t = op_tok + 1;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket, .l_brace => depth += 1,
            .r_paren, .r_bracket, .r_brace => {
                if (depth == 0) return t - 1;
                depth -= 1;
            },
            .comma, .semicolon => if (depth == 0) return t - 1,
            else => {},
        }
    }
    return last;
}

/// Is the subscript whose `[` is `open_tok` a RANGE — `id[a..b]`,
/// `id[0..]`, `id[..]` — rather than a single element `id[i]`?
///
/// The two are different evaluations.  `id[i]` reads the element it
/// names, which is undefined memory when nothing wrote it; `id[a..b]`
/// builds a slice over the storage and reads nothing at all.  Only a
/// `..` at the SUBSCRIPT's own depth counts: one nested inside
/// `id[tbl[i..j]]` is part of the index expression, not a range over
/// `id`.
fn isRangeSubscript(tags: []const std.zig.Token.Tag, open_tok: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    var depth: u32 = 0;
    var t = open_tok + 1;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            // The closers of the delimiters counted above.  Without them
            // an index expression's `(` is counted for ever and a `..`
            // after it can never sit at depth zero: in `id[tbl[0..1]..]`
            // the `..` inside the index belongs to the index, and the one
            // that follows it is the range over `id`.
            .r_paren, .r_brace => {
                if (depth == 0) return false;
                depth -= 1;
            },
            .r_bracket => {
                if (depth == 0) return false;
                depth -= 1;
            },
            .ellipsis2, .ellipsis3 => if (depth == 0) return true,
            else => {},
        }
    }
    return false;
}

// ── Tests ──────────────────────────────────────────────────

// `cfg.zig` keeps its test bodies in `cfg_tests.zig`, and the lowering
// BUDGET tests stay here instead.  They read `max_classify_depth`, the
// limits `classifyExpr` and `booleanValue` enforce, and asserting
// against a copy of those numbers would test the copy.  Moving them
// would mean exporting the limits — widening this module's public
// surface to satisfy a placement rule, which is the opposite of what
// the rule is for.  The rule holds for everything that does not have
// to name a private limit.

/// Build `depth` nested parentheses around `inner`.  Paren nesting is the
/// cheapest expression shape that drives `classifyExpr`'s recursion
/// depth, so a depth test can isolate the limit it names.
fn nestedParens(gpa: std.mem.Allocator, depth: usize, inner: []const u8) ![]u8 {
    var text: std.ArrayListUnmanaged(u8) = .empty;
    errdefer text.deinit(gpa);
    for (0..depth) |_| try text.appendSlice(gpa, "(");
    try text.appendSlice(gpa, inner);
    for (0..depth) |_| try text.appendSlice(gpa, ")");
    return text.toOwnedSlice(gpa);
}

/// Lower every fn in `src` and report which budget (if any) stopped it.
/// Returns null when the whole source lowered cleanly.
///
/// ONE cache for the whole source, the way production lowers a file,
/// and for the same reason: without it each `lowerFunction` builds its
/// own private whole-file index and N functions cost N of them.  The
/// tests read `expr_classify_depth` and `boolean_unwind`, neither of
/// which consults the cache, so attaching one cannot move the limit a
/// budget failure names — it only stops the helper from paying for the
/// same index once per function it lowers.
fn lowerAllBudgetFailure(gpa: std.mem.Allocator, src: []const u8) !?budget_mod.Diagnostic {
    const src_z = try gpa.dupeSentinel(u8, src, 0);
    defer gpa.free(src_z);
    var tree = try Ast.parse(gpa, src_z, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = file_cache.FileCache.init(gpa, &tree);
    defer cache.deinit();
    budget_mod.clear();
    var node_idx: u32 = 1;
    // Stop at the first fn whose lowering gave up: its record is the one
    // worth reporting, and later fns are never reached.
    lower: while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        var cfg = (lowerFunctionFull(gpa, &tree, node, &config_mod.Default, &cache) catch |err| switch (err) {
            error.AnalysisBudgetExceeded => break :lower,
            else => return err,
        }) orelse continue;
        cfg.deinit(gpa);
    }
    return budget_mod.take();
}

test "expressions just under every lowering budget still lower" {
    const gpa = std.testing.allocator;
    const expression = try nestedParens(gpa, max_classify_depth - 4, "flag");
    defer gpa.free(expression);
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    try source.appendSlice(gpa, "fn shallowParenWrapped(flag: bool) bool {\n    return ");
    try source.appendSlice(gpa, expression);
    try source.appendSlice(gpa, ";\n}\n");
    // Below the cap the walk must complete and leave no failure record —
    // an exhaustion that silently poisoned ordinary code would hide
    // every finding in the file.
    try std.testing.expect((try lowerAllBudgetFailure(gpa, source.items)) == null);

    var chain: std.ArrayListUnmanaged(u8) = .empty;
    defer chain.deinit(gpa);
    for (0..max_boolean_unwind - 4) |_| try chain.appendSlice(gpa, "!");
    try chain.appendSlice(gpa, "flag");
    var short_source: std.ArrayListUnmanaged(u8) = .empty;
    defer short_source.deinit(gpa);
    try short_source.appendSlice(gpa, "fn shortNotChain(flag: bool) bool {\n    if (");
    try short_source.appendSlice(gpa, chain.items);
    try short_source.appendSlice(gpa, ") return true;\n    return false;\n}\n");
    try std.testing.expect((try lowerAllBudgetFailure(gpa, short_source.items)) == null);
}

test "classifyExpr depth budget names the expression-depth limit and the function" {
    const gpa = std.testing.allocator;
    const expression = try nestedParens(gpa, max_classify_depth + 4, "flag");
    defer gpa.free(expression);
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    try source.appendSlice(gpa, "fn deeplyParenWrapped(flag: bool) bool {\n    return ");
    try source.appendSlice(gpa, expression);
    try source.appendSlice(gpa, ";\n}\n");

    const failure = (try lowerAllBudgetFailure(gpa, source.items)) orelse
        return error.TestExpectedBudgetFailure;
    try std.testing.expectEqual(budget_mod.Limit.expr_classify_depth, failure.limit);
    try std.testing.expectEqual(@as(u32, max_classify_depth), failure.limit_value);
    try std.testing.expectEqual(@as(u32, max_classify_depth), failure.reached);
    try std.testing.expectEqualStrings("deeplyParenWrapped", failure.function.slice());
    // The failure points at the expression that stopped the walk.
    try std.testing.expect(failure.line > 0);
    try std.testing.expect(failure.byte > 0);
}

test "booleanValue unwind budget names the boolean-unwind limit" {
    const gpa = std.testing.allocator;
    // A chain of `!` longer than the unwind cap: each `!` peels one
    // level, so the walk runs out of steps before reaching `flag`.
    var condition: std.ArrayListUnmanaged(u8) = .empty;
    defer condition.deinit(gpa);
    for (0..max_boolean_unwind + 4) |_| try condition.appendSlice(gpa, "!");
    try condition.appendSlice(gpa, "flag");
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    // Bound to a `const` rather than tested by an `if`: an `if` condition is
    // also walked by `assumeCondition`, whose own recursion trips the
    // expression-depth limit before the unwind loop runs out of steps.
    try source.appendSlice(gpa, "fn longNotChain(flag: bool) bool {\n    const negated = ");
    try source.appendSlice(gpa, condition.items);
    try source.appendSlice(gpa, ";\n    return negated;\n}\n");

    const failure = (try lowerAllBudgetFailure(gpa, source.items)) orelse
        return error.TestExpectedBudgetFailure;
    try std.testing.expectEqual(budget_mod.Limit.boolean_unwind, failure.limit);
    try std.testing.expectEqual(@as(u32, max_boolean_unwind), failure.limit_value);
    try std.testing.expectEqual(@as(u32, max_boolean_unwind), failure.reached);
    try std.testing.expectEqualStrings("longNotChain", failure.function.slice());
    try std.testing.expect(failure.line > 0);
}

test "a lowering budget failure names the fn whose body gave up" {
    const gpa = std.testing.allocator;
    const expression = try nestedParens(gpa, max_classify_depth + 4, "flag");
    defer gpa.free(expression);
    var source: std.ArrayListUnmanaged(u8) = .empty;
    defer source.deinit(gpa);
    // A well-formed fn ahead of the failing one proves the recorded name
    // is the failing function's, not simply the first one lowered.
    try source.appendSlice(gpa, "fn fine(flag: bool) bool {\n    return flag;\n}\n");
    try source.appendSlice(gpa, "fn theFailingOne(flag: bool) bool {\n    return ");
    try source.appendSlice(gpa, expression);
    try source.appendSlice(gpa, ";\n}\n");

    const failure = (try lowerAllBudgetFailure(gpa, source.items)) orelse
        return error.TestExpectedBudgetFailure;
    try std.testing.expectEqualStrings("theFailingOne", failure.function.slice());
}

/// Lower `fn_name` in `src` and report whether its returned value was
/// attributed to a frame slot of `local_name`.  That attribution is the
/// builder's own lifetime decision — the stack-escape rule only
/// consumes it — so an address that really lives in caller or heap
/// storage and one that really sits in this frame are told apart here,
/// before any diagnostic text exists.
fn returnBorrowsLocalFrame(
    gpa: std.mem.Allocator,
    src: []const u8,
    fn_name: []const u8,
    local_name: []const u8,
) !bool {
    const src_z = try gpa.dupeSentinel(u8, src, 0);
    defer gpa.free(src_z);
    var tree = try Ast.parse(gpa, src_z, .zig);
    defer tree.deinit(gpa);
    if (tree.errors.len != 0) return error.InvalidSyntax;
    var cache = file_cache.FileCache.init(gpa, &tree);
    defer cache.deinit();
    var buf: [1]Ast.Node.Index = undefined;
    var node_idx: u32 = 1;
    const target: Ast.Node.Index = while (node_idx < tree.nodes.len) : (node_idx += 1) {
        const node: Ast.Node.Index = @enumFromInt(node_idx);
        if (tree.nodeTag(node) != .fn_decl) continue;
        const proto = tokens.fnProto(&tree, &buf, node) orelse continue;
        const name_tok = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_tok), fn_name)) continue;
        break node;
    } else return error.TestUnexpectedResult;
    var cfg = (try lowerFunctionFull(gpa, &tree, target, &config_mod.Default, &cache)) orelse
        return error.TestUnexpectedResult;
    defer cfg.deinit(gpa);
    for (cfg.blocks) |block| {
        for (block.stmts) |stmt| {
            const escaped: ?ExprKind = switch (stmt.kind) {
                .ret => |r| r.value_kind,
                .composite_escape => |c| c.value_kind,
                else => null,
            };
            const owner: ?LocalId = switch (escaped orelse continue) {
                .stack_ref => |id| id,
                .copy_of => |id| id,
                else => null,
            };
            const id = owner orelse continue;
            if (std.mem.eql(u8, cfg.locals[@intFromEnum(id)].name, local_name)) return true;
        }
    }
    return false;
}

test "addressing through a pointer field leaves the frame, a by-value chain does not" {
    const gpa = std.testing.allocator;
    const source =
        \\const Leaf = struct { count: u32 };
        \\const Branch = struct { leaf: Leaf };
        \\const Trunk = struct { branch: Branch };
        \\const Descriptor = struct { doc: *Branch };
        \\fn throughPointer(descriptor: Descriptor) *const u32 {
        \\    return &descriptor.doc.leaf.count;
        \\}
        \\fn throughValues(trunk: Trunk) *const u32 {
        \\    return &trunk.branch.leaf.count;
        \\}
    ;
    // `descriptor` is a by-value parameter, but `doc` is a pointer, so
    // the address names the branch the pointer owns.
    try std.testing.expect(!try returnBorrowsLocalFrame(gpa, source, "throughPointer", "descriptor"));
    // Every access on the other path is a by-value field of this
    // parameter's own storage, so its address really does die here.
    try std.testing.expect(try returnBorrowsLocalFrame(gpa, source, "throughValues", "trunk"));
}

test "an optional value payload keeps its address in the frame, an optional pointer does not" {
    const gpa = std.testing.allocator;
    const source =
        \\const Leaf = struct { count: u32 };
        \\const Boxed = struct { leaf: ?Leaf };
        \\const Linked = struct { leaf: ?*Leaf };
        \\fn optionalValue(boxed: Boxed) *const u32 {
        \\    return &boxed.leaf.?.count;
        \\}
        \\fn optionalPointer(linked: Linked) *const u32 {
        \\    return &linked.leaf.?.count;
        \\}
    ;
    try std.testing.expect(try returnBorrowsLocalFrame(gpa, source, "optionalValue", "boxed"));
    try std.testing.expect(!try returnBorrowsLocalFrame(gpa, source, "optionalPointer", "linked"));
}

test "a chain no type can settle does not prove a frame escape" {
    const gpa = std.testing.allocator;
    // An unresolved generic field chain can cross a pointer boundary.
    // Neither an inside nor an outside storage claim is proved.
    const source =
        \\const Leaf = struct { count: u32 };
        \\fn fromOpaque(payload: anytype) *const u32 {
        \\    const descriptor = payload.inner;
        \\    return &descriptor.doc.leaf.count;
        \\}
    ;
    try std.testing.expect(!try returnBorrowsLocalFrame(gpa, source, "fromOpaque", "descriptor"));
}

test "addressing a single field stays a frame borrow whatever the field is declared as" {
    const gpa = std.testing.allocator;
    // `&` never auto-derefs: `holder.handle` is the SLOT inside the
    // parameter, so its address dies with the frame even though the
    // value stored there is itself a pointer.
    const source =
        \\const Handle = struct { id: u32 };
        \\const Holder = struct { handle: *Handle };
        \\fn singleField(holder: Holder) *const *Handle {
        \\    return &holder.handle;
        \\}
    ;
    try std.testing.expect(try returnBorrowsLocalFrame(gpa, source, "singleField", "holder"));
}

fn checkHeapIdentityFixture(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(@import("../problem.zig").Problem),
) !void {
    try cache.resolveTransitiveTakes();
    for (1..tree.nodes.len) |index| {
        const node: Ast.Node.Index = @enumFromInt(index);
        if (tree.nodeTag(node) != .fn_decl) continue;
        var graph = (try lowerFunctionFullWithZls(gpa, tree, node, config, cache, cache.zls)) orelse continue;
        defer graph.deinit(gpa);
        try @import("worklist.zig").check(gpa, &graph, .{ .path = "<heap-identity>", .config = config }, problems);
    }
}

test "heap identity: freeing shelves preserves the directory allocation" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\const Shelves = struct {
        \\    dirs: [][]u8,
        \\    fn freeElements(self: *Shelves, a: std.mem.Allocator) void {
        \\        for (self.dirs) |shelf| a.free(shelf);
        \\    }
        \\};
        \\fn cleanup(a: std.mem.Allocator, dirs: [][]u8) void {
        \\    var shelves = Shelves{ .dirs = dirs };
        \\    shelves.freeElements(a);
        \\    a.free(shelves.dirs);
        \\}
    );
}

test "heap identity: freeing shelves still diagnoses a repeated directory free" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-double-free",
        \\const std = @import("std");
        \\const Shelves = struct {
        \\    dirs: [][]u8,
        \\    fn freeElements(self: *Shelves, a: std.mem.Allocator) void {
        \\        for (self.dirs) |shelf| a.free(shelf);
        \\    }
        \\};
        \\fn cleanup(a: std.mem.Allocator, dirs: [][]u8) void {
        \\    var shelves = Shelves{ .dirs = dirs };
        \\    shelves.freeElements(a);
        \\    a.free(shelves.dirs);
        \\    a.free(shelves.dirs);
        \\}
    );
}

test "heap identity: optional lookup invalidation does not free the cleared slot twice" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\const Tree = struct {
        \\    a: std.mem.Allocator,
        \\    lookup: ?[]u32,
        \\    fn invalidate(self: *Tree) void {
        \\        if (self.lookup) |lookup| {
        \\            self.a.free(lookup);
        \\            self.lookup = null;
        \\        }
        \\    }
        \\};
        \\fn appendTwice(tree: *Tree) void {
        \\    tree.invalidate();
        \\    tree.invalidate();
        \\}
    );
}

test "heap identity: callee definite field release still diagnoses a repeated free" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-double-free",
        \\const std = @import("std");
        \\const Tree = struct {
        \\    a: std.mem.Allocator,
        \\    lookup: []u32,
        \\    fn invalidate(self: *Tree) void {
        \\        self.a.free(self.lookup);
        \\    }
        \\};
        \\fn appendTwice(tree: *Tree) void {
        \\    tree.invalidate();
        \\    tree.invalidate();
        \\}
    );
}

test "heap identity: callee replacement leaves the current buffer usable" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\const Parser = struct {
        \\    a: std.mem.Allocator,
        \\    indexes: []u32,
        \\    fn reserve(self: *Parser, n: usize) !void {
        \\        const next = try self.a.alloc(u32, n);
        \\        self.a.free(self.indexes);
        \\        self.indexes = next;
        \\    }
        \\};
        \\fn prepare(parser: *Parser) !usize {
        \\    try parser.reserve(8);
        \\    return parser.indexes.len;
        \\}
    );
}

test "heap identity: callee definite release still diagnoses use after free" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-use-after-free",
        \\const std = @import("std");
        \\const Parser = struct {
        \\    a: std.mem.Allocator,
        \\    indexes: []u32,
        \\    fn release(self: *Parser) void {
        \\        self.a.free(self.indexes);
        \\    }
        \\};
        \\fn prepare(parser: *Parser) u32 {
        \\    parser.release();
        \\    return parser.indexes[0];
        \\}
    );
}

test "heap identity: direct repeated local free remains diagnosed" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-double-free",
        \\const std = @import("std");
        \\fn cleanup(a: std.mem.Allocator, p: []u8) void {
        \\    a.free(p);
        \\    a.free(p);
        \\}
    );
}

test "heap identity: direct local use after free remains diagnosed" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-use-after-free",
        \\const std = @import("std");
        \\fn cleanup(a: std.mem.Allocator, p: []u8) u8 {
        \\    a.free(p);
        \\    return p[0];
        \\}
    );
}

test "heap identity: direct element frees leave the directory live" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\fn cleanup(a: std.mem.Allocator, dirs: [][]u8) void {
        \\    for (dirs) |shelf| a.free(shelf);
        \\    a.free(dirs);
        \\}
    );
}

test "heap identity: repeated free of one loop element remains diagnosed" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-double-free",
        \\const std = @import("std");
        \\fn cleanup(a: std.mem.Allocator, dirs: [][]u8) void {
        \\    for (dirs) |shelf| {
        \\        a.free(shelf);
        \\        a.free(shelf);
        \\    }
        \\    a.free(dirs);
        \\}
    );
}

test "heap identity: a nested callee field release leaves its sibling live" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\const Inner = struct {
        \\    bytes: []u8,
        \\    fn release(self: *Inner, a: std.mem.Allocator) void {
        \\        a.free(self.bytes);
        \\    }
        \\};
        \\const Owner = struct { inner: Inner, bytes: []u8 };
        \\fn cleanup(owner: *Owner, a: std.mem.Allocator) void {
        \\    owner.inner.release(a);
        \\    a.free(owner.bytes);
        \\}
    );
}

test "heap identity: a repeated nested callee field free remains diagnosed" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-double-free",
        \\const std = @import("std");
        \\const Inner = struct {
        \\    bytes: []u8,
        \\    fn release(self: *Inner, a: std.mem.Allocator) void {
        \\        a.free(self.bytes);
        \\    }
        \\};
        \\const Owner = struct { inner: Inner, bytes: []u8 };
        \\fn cleanup(owner: *Owner, a: std.mem.Allocator) void {
        \\    owner.inner.release(a);
        \\    a.free(owner.inner.bytes);
        \\}
    );
}

test "heap identity: payload initialization before an unconditional release remains definite" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-use-after-free",
        \\const std = @import("std");
        \\fn dispose(a: std.mem.Allocator, p: []u8) void {
        \\    @memset(p, 0);
        \\    a.free(p);
        \\}
        \\fn cleanup(a: std.mem.Allocator, p: []u8) u8 {
        \\    dispose(a, p);
        \\    return p[0];
        \\}
    );
}

test "heap identity: payload initialization without release leaves the allocation live" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\fn initialize(p: []u8) void {
        \\    @memset(p, 0);
        \\}
        \\fn cleanup(a: std.mem.Allocator, p: []u8) void {
        \\    initialize(p);
        \\    a.free(p);
        \\}
    );
}

test "heap identity: aggregate entry snapshot release preserves old alias hazards" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-use-after-free",
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn replace(self: *Buffer, a: std.mem.Allocator) !void {
        \\        const old = self.*;
        \\        self.bytes = try a.alloc(u8, 8);
        \\        a.free(old.bytes);
        \\    }
        \\};
        \\fn use(a: std.mem.Allocator) !u8 {
        \\    var buffer = Buffer{ .bytes = try a.alloc(u8, 4) };
        \\    const saved = buffer.bytes;
        \\    try buffer.replace(a);
        \\    return saved[0];
        \\}
    );
}

test "heap identity: aggregate entry snapshot release leaves replacement live" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn replace(self: *Buffer, a: std.mem.Allocator) !void {
        \\        const old = self.*;
        \\        self.bytes = try a.alloc(u8, 8);
        \\        a.free(old.bytes);
        \\    }
        \\};
        \\fn use(a: std.mem.Allocator) !void {
        \\    var buffer = Buffer{ .bytes = try a.alloc(u8, 4) };
        \\    try buffer.replace(a);
        \\    a.free(buffer.bytes);
        \\}
    );
}

test "heap identity: opaque tail preserves a proved entry release" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-use-after-free",
        \\const std = @import("std");
        \\extern fn opaqueValue() void;
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn replace(self: *Buffer, a: std.mem.Allocator) !void {
        \\        const old = self.bytes;
        \\        self.bytes = try a.alloc(u8, 8);
        \\        a.free(old);
        \\        opaqueValue();
        \\    }
        \\};
        \\fn use(a: std.mem.Allocator) !u8 {
        \\    var buffer = Buffer{ .bytes = try a.alloc(u8, 4) };
        \\    const saved = buffer.bytes;
        \\    try buffer.replace(a);
        \\    return saved[0];
        \\}
    );
}

test "heap identity: conditional entry release before opaque tail remains unproved" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\extern fn opaqueValue() void;
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn replace(self: *Buffer, a: std.mem.Allocator, release: bool) !void {
        \\        const old = self.bytes;
        \\        self.bytes = try a.alloc(u8, 8);
        \\        if (release) a.free(old);
        \\        opaqueValue();
        \\    }
        \\};
        \\fn use(a: std.mem.Allocator, release: bool) !u8 {
        \\    var buffer = Buffer{ .bytes = try a.alloc(u8, 4) };
        \\    const saved = buffer.bytes;
        \\    try buffer.replace(a, release);
        \\    return saved[0];
        \\}
    );
}

test "heap identity: a snapshot after an unproved store cannot certify entry release" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\extern fn opaqueValue() void;
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn replace(self: *Buffer, a: std.mem.Allocator, other: []u8) !void {
        \\        self.bytes = other;
        \\        const old = self.*;
        \\        self.bytes = try a.alloc(u8, 8);
        \\        a.free(old.bytes);
        \\        opaqueValue();
        \\    }
        \\};
        \\fn use(a: std.mem.Allocator) !void {
        \\    var buffer = Buffer{ .bytes = try a.alloc(u8, 4) };
        \\    const saved = buffer.bytes;
        \\    const other = try a.alloc(u8, 4);
        \\    try buffer.replace(a, other);
        \\    a.free(saved);
        \\    a.free(buffer.bytes);
        \\}
    );
}

test "heap identity: incomplete replacement forgets the field without killing its old alias" {
    try @import("../testing.zig").expectNoFireTyped(checkHeapIdentityFixture,
        \\const std = @import("std");
        \\extern fn opaqueValue() void;
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn replace(self: *Buffer, a: std.mem.Allocator) !void {
        \\        self.bytes = try a.alloc(u8, 8);
        \\        opaqueValue();
        \\    }
        \\};
        \\fn use(a: std.mem.Allocator) !void {
        \\    var buffer = Buffer{ .bytes = try a.alloc(u8, 4) };
        \\    const saved = buffer.bytes;
        \\    try buffer.replace(a);
        \\    a.free(saved);
        \\    a.free(buffer.bytes);
        \\}
    );
}

test "heap identity: incomplete replacement retains a proved old alias double free" {
    try @import("../testing.zig").expectFiresTyped(checkHeapIdentityFixture, "heap-double-free",
        \\const std = @import("std");
        \\extern fn opaqueValue() void;
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn replace(self: *Buffer, a: std.mem.Allocator) !void {
        \\        const old = self.bytes;
        \\        self.bytes = try a.alloc(u8, 8);
        \\        a.free(old);
        \\        opaqueValue();
        \\    }
        \\};
        \\fn use(a: std.mem.Allocator) !void {
        \\    var buffer = Buffer{ .bytes = try a.alloc(u8, 4) };
        \\    const saved = buffer.bytes;
        \\    try buffer.replace(a);
        \\    a.free(saved);
        \\    a.free(buffer.bytes);
        \\}
    );
}

fn expectReturnedStackEscapes(src: [:0]const u8, fn_name: []const u8, expected: usize, typed: bool) !void {
    const gpa = std.testing.allocator;
    var context: zls_resolver_mod.TypeContext = undefined;
    if (typed) try context.init(gpa, std.testing.io);
    defer if (typed) context.deinit();
    var resolver: zls_resolver_mod.TypeResolver = undefined;
    if (typed) try resolver.init(&context, gpa, "/tmp/zbc-stack-return.zig", src);
    defer if (typed) resolver.deinit();
    var parsed: Ast = undefined;
    if (!typed) parsed = try Ast.parse(gpa, src, .zig);
    defer if (!typed) parsed.deinit(gpa);
    const tree = if (typed) &resolver.handle.document.tree else &parsed;
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var cache = file_cache.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(if (typed) &resolver else null);
    var buffer: [1]Ast.Node.Index = undefined;
    for (tree.rootDecls()) |node| {
        const proto = tokens.fnProto(tree, &buffer, node) orelse continue;
        const name = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name), fn_name)) continue;
        var graph = (try lowerFunctionFullWithZls(
            gpa, tree, node, &config_mod.Default, &cache, if (typed) &resolver else null,
        )) orelse return error.TestUnexpectedResult;
        defer graph.deinit(gpa);
        var problems: std.ArrayListUnmanaged(@import("../problem.zig").Problem) = .empty;
        defer {
            for (problems.items) |*problem| problem.deinit(gpa);
            problems.deinit(gpa);
        }
        try @import("worklist.zig").check(gpa, &graph, .{ .path = "<test>" }, &problems);
        var count: usize = 0;
        for (problems.items) |problem| {
            if (std.mem.eql(u8, problem.rule_id, "stack-escape")) count += 1;
        }
        try std.testing.expectEqual(expected, count);
        return;
    }
    return error.TestUnexpectedResult;
}

test "S-LOAN: scalar outparam results are not frame addresses, direct addresses escape" {
    const source =
        \\fn sum(x: f64, y: f64, out: *f64) f64 { out.* = y; return x + y; }
        \\fn safe(x: f64, y: f64) f64 {
        \\    var low: f64 = 0;
        \\    const high = sum(x, y, &low);
        \\    return high;
        \\}
        \\fn unsafe(x: f64) *const f64 {
        \\    var local = x;
        \\    return &local;
        \\}
    ;
    for ([_]bool{ false, true }) |typed| {
        try expectReturnedStackEscapes(source, "safe", 0, typed);
        try expectReturnedStackEscapes(source, "unsafe", 1, typed);
    }
}

test "S-LOAN: scratch indices do not own tree slices, local array slices escape" {
    const source =
        \\const Tree = struct {
        \\    source: []const u8,
        \\    fn tokenSlice(tree: Tree, index: usize) []const u8 { return tree.source[index..]; }
        \\};
        \\fn index(out: *usize) usize { out.* = 0; return out.*; }
        \\fn safe(tree: Tree) []const u8 {
        \\    var scratch: usize = 0;
        \\    const slice = tree.tokenSlice(index(&scratch));
        \\    return slice;
        \\}
        \\fn direct(tree: Tree) []const u8 {
        \\    var scratch: usize = 0;
        \\    return tree.tokenSlice(index(&scratch));
        \\}
        \\fn unsafe(n: usize) []const u8 {
        \\    var buf: [4]u8 = @splat(0);
        \\    const slice = buf[0..@min(n, buf.len)];
        \\    return slice;
        \\}
        \\fn directArray(n: usize) []const u8 {
        \\    var buf: [4]u8 = @splat(0);
        \\    return buf[0..@min(n, buf.len)];
        \\}
    ;
    for ([_]bool{ false, true }) |typed| {
        try expectReturnedStackEscapes(source, "safe", 0, typed);
        try expectReturnedStackEscapes(source, "direct", 0, typed);
        try expectReturnedStackEscapes(source, "unsafe", 1, typed);
        try expectReturnedStackEscapes(source, "directArray", 1, typed);
    }
}

test "S-LOAN: aggregate address aliases and canonical integer address loans still escape" {
    const source =
        \\const Wrapper = struct { pointer: *const u32 };
        \\fn aggregate() Wrapper {
        \\    var local: u32 = 7;
        \\    const pointer = &local;
        \\    const result = Wrapper{ .pointer = pointer };
        \\    return result;
        \\}
        \\fn encoded() usize {
        \\    var local: u32 = 7;
        \\    return @intFromPtr(&local);
        \\}
    ;
    for ([_]bool{ false, true }) |typed| {
        try expectReturnedStackEscapes(source, "aggregate", 1, typed);
    }
    try expectReturnedStackEscapes(source, "encoded", 1, true);
}

test "S-LOAN: returned block-local address aliases retain lexical frame identity" {
    const source =
        \\fn select(source: []const u8, scratch: *u8) []const u8 {
        \\    scratch.* = 0;
        \\    return source;
        \\}
        \\fn safe(source: []const u8) []const u8 {
        \\    return value: {
        \\        var scratch: u8 = 0;
        \\        break :value select(source, &scratch);
        \\    };
        \\}
        \\fn unsafe() *const u8 {
        \\    return value: {
        \\        const cell: u8 = 1;
        \\        const pointer = &cell;
        \\        break :value pointer;
        \\    };
        \\}
    ;
    for ([_]bool{ false, true }) |typed| {
        try expectReturnedStackEscapes(source, "safe", 0, typed);
        try expectReturnedStackEscapes(source, "unsafe", 1, typed);
    }
}

test "S-LOAN: AST scalar projections discard scratch loans but full views escape" {
    const source =
        \\const std = @import("std");
        \\const Ast = std.zig.Ast;
        \\fn scalar(tree: *const Ast, node: Ast.Node.Index) ?Ast.TokenIndex {
        \\    var buffer: [1]Ast.Node.Index = undefined;
        \\    const proto = tree.fullFnProto(&buffer, node) orelse return null;
        \\    return proto.name_token;
        \\}
        \\fn text(tree: *const Ast, node: Ast.Node.Index) []const u8 {
        \\    var buffer: [1]Ast.Node.Index = undefined;
        \\    const proto = tree.fullFnProto(&buffer, node) orelse return "";
        \\    return tree.tokenSlice(proto.name_token orelse return "");
        \\}
        \\fn view(tree: *const Ast, node: Ast.Node.Index) ?Ast.full.FnProto {
        \\    var buffer: [1]Ast.Node.Index = undefined;
        \\    return tree.fullFnProto(&buffer, node);
        \\}
    ;
    try expectReturnedStackEscapes(source, "scalar", 0, true);
    try expectReturnedStackEscapes(source, "text", 0, true);
    try expectReturnedStackEscapes(source, "view", 1, true);
}

test "S-LOAN: opaque results are not proved argument loans, known aliases escape" {
    const source =
        \\extern fn unknown(value: *const u32) *const u32;
        \\fn identity(value: *const u32) *const u32 { return value; }
        \\fn safe() *const u32 {
        \\    var local: u32 = 7;
        \\    return unknown(&local);
        \\}
        \\fn unsafe() *const u32 {
        \\    var local: u32 = 7;
        \\    return identity(&local);
        \\}
    ;
    try expectReturnedStackEscapes(source, "safe", 0, true);
    try expectReturnedStackEscapes(source, "unsafe", 1, true);
}

test "S-LOAN: returned allocator copies do not borrow copied stack bytes" {
    const source =
        \\const std = @import("std");
        \\fn safe(allocator: std.mem.Allocator) ![]u8 {
        \\    var buffer: [4]u8 = @splat(0);
        \\    return allocator.dupe(u8, &buffer);
        \\}
        \\fn unsafe() []const u8 {
        \\    var buffer: [4]u8 = @splat(0);
        \\    return &buffer;
        \\}
    ;
    try expectReturnedStackEscapes(source, "safe", 0, true);
    try expectReturnedStackEscapes(source, "unsafe", 1, true);
}

test "S-LOAN: addresses through inferred store handles do not name the handle frame" {
    const source =
        \\const Document = struct { value: u32 };
        \\const Handle = struct { document: *Document };
        \\const Store = struct {
        \\    document: *Document,
        \\    fn load(store: *Store) !Handle { return .{ .document = store.document }; }
        \\};
        \\fn safe(store: *Store, cache: **u32) !*u32 {
        \\    const handle = try store.load();
        \\    cache.* = &handle.document.value;
        \\    return &handle.document.value;
        \\}
        \\fn unsafe(store: *Store) !*const *Document {
        \\    const handle = try store.load();
        \\    return &handle.document;
        \\}
    ;
    try expectReturnedStackEscapes(source, "safe", 0, true);
    try expectReturnedStackEscapes(source, "unsafe", 1, true);
}

test "S-LOAN: proved outparam address writes remain positive, scalar stores do not" {
    const source =
        \\fn set(bits: *usize, pointer: *u8) void { bits.* = @intFromPtr(pointer); }
        \\fn scalar(bits: *usize, value: usize) void { bits.* = value; }
        \\fn unsafe() usize {
        \\    var local: u8 = 1;
        \\    var bits: usize = 0;
        \\    set(&bits, &local);
        \\    return bits + 0;
        \\}
        \\fn safe() usize {
        \\    var bits: usize = 0;
        \\    scalar(&bits, 7);
        \\    return bits + 0;
        \\}
    ;
    try expectReturnedStackEscapes(source, "unsafe", 1, true);
    try expectReturnedStackEscapes(source, "safe", 0, true);
}

test "S-LOAN: mapped cell paths retain pointee loans rather than descriptor slots" {
    const source =
        \\const Value = struct { number: u32 };
        \\const Box = struct { pointer: *Value };
        \\fn field(box: *Box) *u32 { return &box.pointer.number; }
        \\fn safe(value: *Value) *u32 {
        \\    var box: Box = .{ .pointer = value };
        \\    return field(&box);
        \\}
        \\fn unsafe() *u32 {
        \\    var value: Value = .{ .number = 1 };
        \\    var box: Box = .{ .pointer = &value };
        \\    return field(&box);
        \\}
    ;
    try expectReturnedStackEscapes(source, "safe", 0, true);
    try expectReturnedStackEscapes(source, "unsafe", 1, true);
}
