//! Detects two or more `.field = try <expr>` inside the same struct literal (or
//! initializer).  If the first `try` succeeds but the second `try` propagates an
//! error, the allocation made by the first `try` leaks — `errdefer` cannot be
//! placed inside a struct literal expression.
//!
//! Real-world instance:
//!   - ziglang/zig#23285 (std.zig.Ast.parse):
//!       return Ast{
//!           .extra_data = try parser.extra_data.toOwnedSlice(gpa),  // succeeds
//!           .errors     = try parser.errors.toOwnedSlice(gpa),       // fails → leak
//!       };
//!     Fix: bind each to a local with `errdefer`, then build the struct literal
//!     from the locals.
//!
//! Detection (Tier 1, token walk with paren-skip):
//!   Pattern: `. identifier = keyword_try ... , . identifier = keyword_try`
//!   — find the first `.field = try` 4-token prefix, skip to the next `,` at
//!   depth 0, then check whether the following tokens are `. identifier = try`.
//!   Fire at the second `.` token (the start of the second field assignment).
//!
//!   The leak only matters if the FIRST `try` actually allocates an owned
//!   resource (the second `try` failing is what leaks the first's allocation).
//!   So the first try-expression must contain an allocation signal —
//!   `alloc`, `dupe`, `clone`, `create`, or `toOwnedSlice`.  Decoder/parser
//!   tries (`read_int`, `read_enum`, `parseUnsigned`) return value types and
//!   leak nothing, so they are suppressed.
//! Resolved value-only results also own nothing, including types reached
//! through imported aliases. Unknown types and results with owning fields
//! remain conservative; allocations retained in an existing owner do not
//! become owned by a scalar range returned from the helper.
//! Arena exemptions follow this allocation's operands to the SDK declaration:
//! direct arena allocators, immutable aliases, closed private-helper arguments,
//! and accessors whose every resolved return supplies an arena allocator.
//! SDK map clones bind their result to the supplied allocator. Source helpers
//! are checked in their actual declaring frame, including recursive owning
//! calls and nested operands; opaque or general-allocator edges stay unproved.
//! Nearby arenas and allocator names alone never prove reclamation.

const std = @import("std");
const Ast = std.zig.Ast;

const problem_mod = @import("../../problem.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const testing = @import("../../testing.zig");
const file_model = @import("../../model/file_model.zig");
const std_types = @import("../../model/std_type_query.zig");
const resolver_mod = @import("../../type_resolver.zig");
const method_names = @import("../../model/method_names.zig");
const tokens = @import("../../ast/tokens.zig");
const fresh_storage = @import("../../cache/fresh_storage.zig");
const grow_analysis = @import("../../cache/grow_analysis.zig");
const call_summary = @import("../../cache/call_summary.zig");
const call_effects = @import("../../cache/call_effects.zig");
const budget_mod = @import("../../budget.zig");

const ProofError = file_cache_mod.SummaryError;

const Problem = problem_mod.Problem;
const Pos = problem_mod.Pos;
const R = "struct-literal-multiple-try";

pub fn check(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    config: *const config_mod.Config,
    problems: *std.ArrayListUnmanaged(Problem),
) !void {
    if (!config_mod.isEnabled(config, .struct_literal_multiple_try)) return;

    const tags = tree.tokens.items(.tag);
    if (tree.tokens.len < 8) return;
    const last_tok = tree.lastToken(.root);

    // Map identifier-reference nodes by main token, so the first-try
    // expression's operands can be resolved to their types (e.g. is an operand
    // a `std.mem.Allocator`?).  Empty/unused when the type engine is absent.
    var ident_nodes: std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index) = .empty;
    defer ident_nodes.deinit(gpa);
    {
        var ni: u32 = 0;
        while (ni < tree.nodes.len) : (ni += 1) {
            const node: Ast.Node.Index = @enumFromInt(ni);
            if (tree.nodeTag(node) == .identifier) {
                try ident_nodes.put(gpa, tree.nodeMainToken(node), node);
            }
        }
    }

    var t: Ast.TokenIndex = 0;
    var last_reported: ?Ast.TokenIndex = null;
    while (t + 7 <= last_tok) : (t += 1) {
        // First field: . identifier = try
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .equal) continue;
        if (tags[t + 3] != .keyword_try) continue;

        const i = initializerEnd(tree, t + 4, last_tok) orelse continue;
        if (tags[i] != .comma) continue; // hit a closing delimiter — skip

        // The first try-expression (t+4 .. comma) must allocate an owned
        // resource — otherwise nothing leaks when a later try fails.  The
        // SEMANTIC signal (`firstTryUsesAllocator`) recognizes that the call
        // takes/uses a `std.mem.Allocator` value (the type-based ownership
        // signal — `gpa.alloc`, `list.toOwnedSlice(gpa)`, `el.deepClone(alloc)`
        // all reference an Allocator; a borrowed `getView()` does not).  The
        // syntactic name proxy still catches internal-alloc calls with no
        // visible allocator operand (`x.clone()`).
        if (!firstTryUsesAllocator(cache, &ident_nodes, tags, t + 4, i) and
            !tryExprAllocates(tree, tags, t + 4, i)) continue;
        if (try firstTryReturnsValue(tree, cache, t + 4, i)) continue;
        if (try zeroLengthSdkAllocation(cache, t + 4, i)) continue;
        var ownership: ArenaOwnershipWalk = .{};
        defer ownership.effects.deinit(gpa);
        if (cache.zls) |resolver| {
            if (cache.nodeForExactSpan(t + 4, i - 1)) |expression| {
                if (try zeroStorageResult(cache, resolver.resolutionFrame(), expression, 0, &ownership, 0)) continue;
            }
        }
        if (firstTryUsesScopedArena(tree, cache, t + 4, i)) continue;

        if (try firstTryUsesProvedArena(tree, cache, t + 4, i, &ownership)) continue;

        // A zero-byte SDK allocation cannot fail. Keep the earlier owning
        // field live across it: a later fallible field can still leak it.
        var next = i + 1;
        while (next + 3 <= last_tok) {
            if (tags[next] != .period or tags[next + 1] != .identifier or
                tags[next + 2] != .equal or tags[next + 3] != .keyword_try) break;
            const next_end = initializerEnd(tree, next + 4, last_tok) orelse break;
            if (try zeroLengthSdkAllocation(cache, next + 4, next_end)) {
                if (tags[next_end] != .comma) break;
                next = next_end + 1;
                continue;
            }
            if (last_reported != next) {
                try report(gpa, problems, tree, next, tree.tokenSlice(t + 1), tree.tokenSlice(next + 1));
                last_reported = next;
            }
            break;
        }
    }
    // The lexical type-name adapter has a nullable API. A budget failure
    // recorded there is still incomplete, not evidence for a leak.
    if (budget_mod.peek() != null) return error.AnalysisBudgetExceeded;
}

fn initializerEnd(tree: *const Ast, start: Ast.TokenIndex, last: Ast.TokenIndex) ?Ast.TokenIndex {
    var depth: u32 = 0;
    var token = start;
    while (token <= last) : (token += 1) {
        switch (tree.tokenTag(token)) {
            .l_paren, .l_brace, .l_bracket => depth += 1,
            .r_paren, .r_brace, .r_bracket => {
                if (depth == 0) return token;
                depth -= 1;
            },
            .comma => if (depth == 0) return token,
            else => {},
        }
    }
    return null;
}

/// Only the authenticated SDK alloc(T, 0) fast path has this certificate.
/// A project allocator can charge or fail even for zero elements. Nested
/// `try` operands can fail before the SDK call and invalidate the certificate.
fn zeroLengthSdkAllocation(cache: *file_cache_mod.FileCache, first: Ast.TokenIndex, end: Ast.TokenIndex) ProofError!bool {
    const resolver = cache.zls orelse return false;
    if (first >= end) return false;
    const tree = cache.tree;
    for (tree.tokens.items(.tag)[first..end]) |tag| {
        if (tag == .keyword_try) return false;
    }
    const node = cache.nodeForExactSpan(first, end - 1) orelse return false;
    var call_buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, node) orelse return false;
    const callee = (try grow_analysis.actualCalleeOf(cache, fresh_storage.calleeQueryToken(tree, call), null)) orelse return false;
    if (!std.mem.eql(u8, callee.tree.tokenSlice(callee.fn_token + 1), "alloc") or
        !try resolver.declaredInToolchainFile(callee.handle, "/std/mem/Allocator.zig")) return false;
    const canonical: file_cache_mod.FileCache.ActualCallSummary = .{
        .callee = callee,
        .summary = null,
        .argument_offset = null,
        .read_only = null,
    };
    var argument_buffer: [2]Ast.Node.Index = undefined;
    const count = (try canonical.callArgumentFor(cache, &argument_buffer, 2)) orelse return false;
    return zeroCount(cache, count, 0);
}

fn zeroCount(cache: *file_cache_mod.FileCache, node: Ast.Node.Index, depth: u8) ProofError!bool {
    const tree = cache.tree;
    if (depth >= 16) return ownershipBudgetFailure(tree, tree.firstToken(node), .arena_proof_depth, 16);
    switch (tree.nodeTag(node)) {
        .number_literal => return (std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(node)), 0) catch return false) == 0,
        .grouped_expression => return zeroCount(cache, tree.nodeData(node).node_and_token[0], depth + 1),
        .identifier => {
            const init = std_types.aliasInitializer(cache, tree, tree.nodeMainToken(node)) orelse return false;
            return zeroCount(cache, cache.nodeForExactSpan(init.first, init.last) orelse return false, depth + 1);
        },
        else => return false,
    }
}

fn firstTryReturnsValue(tree: *const Ast, cache: *file_cache_mod.FileCache, start: Ast.TokenIndex, end: Ast.TokenIndex) ProofError!bool {
    if (cache.zls) |resolver| {
        if (start >= end) return false;
        const node = cache.nodeForExactSpan(start, end - 1) orelse return false;
        var result = (try resolver.resolutionFrame().typeOfNode(node)) orelse return false;
        if (resolver.typeTag(result) == .error_union) {
            result = (try resolver.normalizedType(resolver.childType(result) orelse return false)) orelse return false;
        }
        return resolvedValueOnlyType(resolver, result, 0);
    }
    if (start + 1 >= end or tree.tokenTag(start) != .identifier or tree.tokenTag(start + 1) != .l_paren) return false;
    const model = try cache.fileModel();
    const function = model.findFn(tree.tokenSlice(start)) orelse return false;
    var buffer: [1]Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&buffer, function.fn_decl) orelse return false;
    var result_type = proto.ast.return_type.unwrap() orelse return false;
    if (tree.nodeTag(result_type) == .error_union) result_type = tree.nodeData(result_type).node_and_node[1];
    if (tree.nodeTag(result_type) != .identifier) return false;
    return isValueOnlyType(tree, cache, model, tree.nodeMainToken(result_type), 0);
}

/// Inspect the declaration the type engine reached, not an alias's spelling.
/// Each field is resolved in its own document and instantiated container.
fn resolvedValueOnlyType(
    resolver: *resolver_mod.TypeResolver,
    actual: resolver_mod.TypeResolver.ActualType,
    depth: u8,
) ProofError!bool {
    if (depth >= 16) return false;
    const tag = resolver.typeTag(actual) orelse return false;
    switch (tag) {
        .bool, .void, .int, .float, .comptime_int, .comptime_float => return true,
        .@"enum", .@"struct" => {},
        else => return false,
    }
    if (actual.data != .container) return false;
    const scope = actual.data.container.scope_handle;
    const tree = &scope.handle.document.tree;
    var buffer: [2]Ast.Node.Index = undefined;
    const container = tree.fullContainerDecl(&buffer, scope.toNode()) orelse return false;
    const frame = resolver.frameForContainer(actual.data.container);
    var fields: usize = 0;
    for (container.ast.members) |member| {
        var proto_buffer: [1]Ast.Node.Index = undefined;
        if (tree.fullFnProto(&proto_buffer, member)) |proto| {
            const name = tree.tokenSlice(proto.name_token orelse return false);
            if (method_names.isCleanupMethodName(name)) return false;
        }
        if (tag == .@"enum") continue;
        const field = tree.fullContainerField(member) orelse continue;
        const type_node = field.ast.type_expr.unwrap() orelse return false;
        const field_type = (try frame.typeOfNode(type_node)) orelse return false;
        if (!try resolvedValueOnlyType(resolver, field_type, depth + 1)) return false;
        fields += 1;
    }
    return tag == .@"enum" or fields != 0;
}

/// True iff the type expression written at `type_token` owns nothing that has
/// to be released: a primitive, an enum, or a struct whose every field is
/// itself value-only.  The unit of context is a token, not a bare name — an
/// unresolved name is followed through the `const` initializer it is bound
/// to, and each field keeps the tokens it was written with.
fn isValueOnlyType(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    model: *const file_model.FileModel,
    type_token: Ast.TokenIndex,
    depth: u8,
) bool {
    if (depth >= 16) return false;
    if (type_token >= tree.tokens.len or tree.tokenTag(type_token) != .identifier) return false;
    const name = tree.tokenSlice(type_token);
    if (std.mem.eql(u8, name, "bool") or std.mem.eql(u8, name, "void") or
        std.mem.eql(u8, name, "usize") or std.mem.eql(u8, name, "isize")) return true;
    if (name.len > 1 and (name[0] == 'u' or name[0] == 'i' or name[0] == 'f')) {
        if (std.fmt.parseInt(u16, name[1..], 10)) |_| return true else |_| {}
    }
    const info = model.findType(name) orelse {
        // A `const A = B;` alias declares no fields of its own: its value is
        // whatever the bound initializer names.  Only a bare name can answer
        // that question; any other initializer stays unknown.
        const alias = std_types.aliasInitializer(cache, tree, type_token) orelse return false;
        if (alias.last != alias.first) return false;
        return isValueOnlyType(tree, cache, model, alias.first, depth + 1);
    };
    for (info.methods) |method| {
        if (method_names.isCleanupMethodName(method.name)) return false;
    }
    if (info.kind == .enum_) return true;
    if (info.kind != .struct_ or info.fields.len == 0) return false;
    for (info.fields) |field| {
        if (field.type_first != field.type_last or tree.tokenTag(field.type_first) != .identifier) return false;
        if (!isValueOnlyType(tree, cache, model, field.type_first, depth + 1)) return false;
    }
    return true;
}

/// Prove every newly owned call result in this expression, including nested
/// operands. An arena-backed outer header cannot reclaim a general-allocator
/// payload constructed while evaluating its arguments.
fn firstTryUsesProvedArena(tree: *const Ast, cache: *file_cache_mod.FileCache, start: Ast.TokenIndex, end: Ast.TokenIndex, walk: *ArenaOwnershipWalk) ProofError!bool {
    if (start >= end) return false;
    const node = cache.nodeForExactSpan(start, end - 1) orelse return false;
    if (cache.zls == null) {
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse return false;
        if (tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
        return allocatorExprComesFromArena(tree, cache, tree.nodeData(call.ast.fn_expr).node_and_token[0], 0);
    }
    return callsUseArena(cache, null, start, end - 1, null, walk);
}

const ArenaOwnershipWalk = struct {
    active: [16]BoundArenaCall = undefined,
    len: usize = 0,
    completed: [16]resolver_mod.TypeResolver.ActualType = undefined,
    completed_len: usize = 0,
    effects: call_summary.State = .{},
    remaining: u32 = call_summary.actual_query_work_limit,

    fn charge(self: *ArenaOwnershipWalk, tree: *const Ast, token: Ast.TokenIndex) ProofError!void {
        if (self.remaining == 0)
            return ownershipBudgetFailure(tree, token, .arena_proof_steps, call_summary.actual_query_work_limit);
        self.remaining -= 1;
    }
};

/// Runtime allocator values are operands, not part of the callable's type.
/// Retain the caller frame until every use of the formal has been proved.
const BoundArenaCall = struct {
    actual_type: resolver_mod.TypeResolver.ActualType,
    caller_cache: *file_cache_mod.FileCache,
    caller_frame: resolver_mod.TypeResolver.ResolutionFrame,
    call_node: Ast.Node.Index,
};

fn ownershipBudgetFailure(tree: *const Ast, token: Ast.TokenIndex, limit: budget_mod.Limit, cap: u32) ProofError {
    var name: budget_mod.NameBuf = .{};
    if (tokens.enclosingFnDecl(tree, token)) |decl| {
        var buffer: [1]Ast.Node.Index = undefined;
        if (tokens.fnProto(tree, &buffer, decl)) |proto| {
            if (proto.name_token) |name_token| name.set(tree.tokenSlice(name_token));
        }
    }
    const site = try Pos.fromTokenStart(tree, token);
    return budget_mod.fail(.{
        .limit = limit,
        .limit_value = cap,
        .reached = cap,
        .byte = site.byte,
        .document = budget_mod.documentForTree(tree),
        .line = site.line,
        .column = site.column,
        .function = name,
    });
}

/// An active callable is a graph edge, not a completed certificate. Its
/// caller still checks every other owning call before the proof can succeed.
/// Callable identity includes the actual generic/container bindings.
fn callsUseArena(
    cache: *file_cache_mod.FileCache,
    supplied: ?resolver_mod.TypeResolver.ResolutionFrame,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    function: ?Ast.Node.Index,
    walk: *ArenaOwnershipWalk,
) ProofError!bool {
    const frame = supplied orelse (cache.zls orelse return false).resolutionFrame();
    const tree = cache.tree;
    for (tree.nodes.items(.tag), 0..) |tag, raw| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma,
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma,
            => {},
            else => continue,
        }
        const node: Ast.Node.Index = @enumFromInt(raw);
        const start = tree.firstToken(node);
        if (start < first or tree.lastToken(node) > last) continue;
        if (function) |declaration| {
            if (tokens.enclosingFnDecl(tree, start) != declaration) continue;
        }
        try walk.charge(tree, start);
        // Allocation capability is independent of the result type or mutation
        // effects. Operands, including calls inside them, are scanned separately.
        if (tree.tokenTag(tree.nodeMainToken(node)) == .builtin) {
            if (builtinDoesNotAllocate(tree.tokenSlice(tree.nodeMainToken(node)))) continue;
            return false;
        }
        // A scalar result is not an effect certificate: a void helper may
        // allocate through an out-parameter or mutate captured storage.
        var result = (try frame.typeOfNode(node)) orelse return false;
        if (frame.resolver.typeTag(result) == .error_union) {
            result = (try frame.resolver.normalizedType(frame.resolver.childType(result) orelse return false)) orelse return false;
        }
        const scalar = try resolvedValueOnlyType(frame.resolver, result, 0);
        if (frame.resolver.typeTag(result) == .noreturn) continue;
        if (try allocatorInFrame(cache, frame, node, 0, walk, walk.len)) continue;
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, node) orelse return false;
        // Ownership needs declaration identity, not the broad normal-cleanup
        // summary. Loading that summary couples this proof to other consumers'
        // failed demands and can spend their allowance before this walk begins.
        const callee = (try grow_analysis.actualCalleeOf(cache, fresh_storage.calleeQueryToken(tree, call), supplied)) orelse return false;
        const canonical: file_cache_mod.FileCache.ActualCallSummary = .{
            .callee = callee,
            .summary = null,
            .argument_offset = null,
            .read_only = null,
        };
        if (scalar and (try cache.callEffectAt(
            fresh_storage.calleeQueryToken(tree, call),
            .{ .whole = canonical.callee },
            .{ .frame = supplied, .effects_state = &walk.effects, .remaining = &walk.remaining },
        )) == .read_only) continue;
        if (try sdkCallUsesArena(cache, frame, canonical, walk)) |arena| {
            if (arena) continue;
            // This SDK result is tied to its allocator formal. Inspecting the
            // allocator's callback implementation cannot improve that fact.
            return false;
        }
        const body = tokens.bodyOf(callee.tree, callee.declaration) orelse return false;
        const operands_proved = try allocatorFormalsUseArena(cache, frame, node, canonical, walk);
        var recursive = false;
        if (operands_proved) {
            for (walk.completed[0..walk.completed_len]) |completed| {
                if (completed.eql(callee.reference.actual_type)) {
                    recursive = true;
                    break;
                }
            }
        }
        for (walk.active[0..walk.len]) |active| {
            if (active.actual_type.eql(callee.reference.actual_type)) {
                if (!operands_proved) return false;
                recursive = true;
                break;
            }
        }
        if (recursive) continue;
        if (walk.len == walk.active.len)
            return ownershipBudgetFailure(tree, start, .arena_proof_depth, walk.active.len);
        const declaring = (try canonical.declaringCache(cache)) orelse return false;
        walk.active[walk.len] = .{
            .actual_type = callee.reference.actual_type,
            .caller_cache = cache,
            .caller_frame = frame,
            .call_node = node,
        };
        walk.len += 1;
        const proved = try callsUseArena(
            declaring,
            frame.resolver.frameForFunction(callee.reference),
            callee.tree.firstToken(body),
            callee.tree.lastToken(body),
            callee.declaration,
            walk,
        );
        walk.len -= 1;
        if (!proved) return false;
        if (operands_proved and walk.completed_len < walk.completed.len) {
            walk.completed[walk.completed_len] = callee.reference.actual_type;
            walk.completed_len += 1;
        }
    }
    return true;
}

/// Compiler intrinsics that cannot acquire fresh runtime storage or invoke a
/// function. Mutating atomics and memory copies are not read-only, but they
/// cannot allocate. A @field projection cannot invoke the projected function;
/// its enclosing call still requires the normal callee proof.
fn builtinDoesNotAllocate(name: []const u8) bool {
    const builtin = std.zig.BuiltinFn.list.get(name) orelse return false;
    return switch (builtin.tag) {
        .atomic_load, .atomic_store, .atomic_rmw, .cmpxchg_strong, .cmpxchg_weak,
        .memcpy, .memset, .memmove,
        .add_with_overflow, .sub_with_overflow, .mul_with_overflow,
        .div_exact, .div_floor, .div_trunc, .mod, .rem, .min, .max,
        .shl_exact, .shl_with_overflow, .shr_exact,
        .clz, .ctz, .pop_count, .byte_swap, .bit_reverse, .mul_add,
        .sqrt, .sin, .cos, .tan, .exp, .exp2, .log, .log2, .log10,
        .abs, .floor, .ceil, .trunc, .round,
        .as, .bit_cast, .align_cast, .addrspace_cast, .const_cast, .volatile_cast,
        .ptr_cast, .ptr_from_int, .int_from_ptr, .int_cast, .truncate,
        .float_cast, .float_from_int, .int_from_float, .int_from_bool,
        .int_from_enum, .enum_from_int, .int_from_error, .error_from_int, .error_cast,
        .bit_offset_of, .offset_of, .bit_size_of, .size_of, .align_of,
        .has_field, .has_decl, .field, .field_parent_ptr, .FieldType,
        .type_info, .type_name, .TypeOf, .This, .EnumLiteral,
        .Int, .Tuple, .Pointer, .Fn, .Struct, .Union, .Enum, .Vector,
        .union_init, .select, .shuffle, .splat, .reduce,
        .error_name, .error_return_trace, .tag_name, .src,
        .c_define, .c_import, .c_include, .c_undef,
        .c_va_arg, .c_va_copy, .c_va_end, .c_va_start,
        .import, .embed_file, .@"export", .in_comptime, .compile_error, .compile_log,
        .set_eval_branch_quota, .set_float_mode, .set_runtime_safety,
        .branch_hint, .disable_instrumentation, .disable_intrinsics,
        .breakpoint, .trap, .panic, .prefetch, .return_address, .frame_address,
        .wasm_memory_size, .work_item_id, .work_group_size, .work_group_id,
        => true,
        // @call invokes a function; @extern supplies external storage or a
        // function; @wasmMemoryGrow acquires linear-memory pages. Unknown and
        // frame intrinsics also remain unproved.
        else => false,
    };
}

/// SDK result ownership is bound to one formal allocator, not to any arena
/// appearing in the argument list. Managed map clone() has no such formal.
fn sdkCallUsesArena(
    cache: *file_cache_mod.FileCache,
    frame: resolver_mod.TypeResolver.ResolutionFrame,
    canonical: file_cache_mod.FileCache.ActualCallSummary,
    walk: *ArenaOwnershipWalk,
) ProofError!?bool {
    const callee = canonical.callee;
    const resolver = frame.resolver;
    const name = callee.tree.tokenSlice(callee.fn_token + 1);
    const allocator_method = try resolver.declaredInToolchainFile(callee.handle, "/std/mem/Allocator.zig");
    const list = std.mem.eql(u8, name, "toOwnedSlice") and
        (try resolver.declaredInToolchainFile(callee.handle, "/std/array_list.zig"));
    const printed = std.mem.eql(u8, name, "allocPrint") and
        (try resolver.declaredInToolchainFile(callee.handle, "/std/fmt.zig"));
    const map = (std.mem.eql(u8, name, "clone") or std.mem.eql(u8, name, "cloneContext")) and
        (try resolver.declaredInToolchainFile(callee.handle, "/std/array_hash_map.zig"));
    if (!allocator_method and !list and !printed and !map) return null;
    if (map) {
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(callee.tree, &proto_buffer, callee.declaration) orelse return false;
        var parameters = proto.iterate(callee.tree);
        var count: usize = 0;
        while (parameters.next() != null) count += 1;
        if (count != (if (std.mem.eql(u8, name, "clone")) @as(usize, 2) else 3)) return false;
    }
    var argument_buffer: [2]Ast.Node.Index = undefined;
    const argument = (try canonical.callArgumentFor(cache, &argument_buffer, if (list or map) 1 else 0)) orelse return false;
    return try allocatorInFrame(cache, frame, argument, 0, walk, walk.len);
}

/// Memo and recursive-edge reuse require every SDK allocator formal to have
/// proved operands. A callable type alone cannot distinguish an arena from a
/// general allocator passed to the same runtime parameter.
fn allocatorFormalsUseArena(
    cache: *file_cache_mod.FileCache,
    frame: resolver_mod.TypeResolver.ResolutionFrame,
    node: Ast.Node.Index,
    canonical: file_cache_mod.FileCache.ActualCallSummary,
    walk: *ArenaOwnershipWalk,
) ProofError!bool {
    for (canonical.callee.reference.actual_type.data.function.parameters, 0..) |parameter, index| {
        const actual = (try frame.resolver.normalizedType(parameter.type)) orelse return false;
        if (actual.data != .container) continue;
        if (!try frame.resolver.declaredInToolchainFile(actual.data.container.scope_handle.handle, "/std/mem/Allocator.zig")) continue;
        var buffer: [2]Ast.Node.Index = undefined;
        const argument = (try frame.callArgumentIn(&buffer, node, index)) orelse return false;
        if (!try allocatorInFrame(cache, frame, argument, 0, walk, walk.len)) return false;
    }
    return true;
}

fn allocatorInFrame(
    cache: *file_cache_mod.FileCache,
    frame: resolver_mod.TypeResolver.ResolutionFrame,
    node: Ast.Node.Index,
    depth: u8,
    walk: *ArenaOwnershipWalk,
    bindings_len: usize,
) ProofError!bool {
    if (depth >= 16) return ownershipBudgetFailure(cache.tree, cache.tree.firstToken(node), .arena_proof_depth, 16);
    const tree = cache.tree;
    // Ordinary caller queries retain the existing closed-call/accessor
    // proofs. Foreign callable frames must never use the root document.
    if (frame.actual_type == null and cache.zls == frame.resolver) {
        return try allocatorExprComesFromArena(tree, cache, node, depth) or
            try localAllocatorFieldUsesArena(cache, frame, node, depth, walk);
    }
    switch (tree.nodeTag(node)) {
        .grouped_expression => return allocatorInFrame(cache, frame, tree.nodeData(node).node_and_token[0], depth + 1, walk, bindings_len),
        .identifier => {
            const use = tree.nodeMainToken(node);
            if (std_types.aliasInitializer(cache, tree, use)) |init| {
                const initializer = cache.nodeForExactSpan(init.first, init.last) orelse return false;
                return allocatorInFrame(cache, frame, initializer, depth + 1, walk, bindings_len);
            }
            const argument = (try boundFormalArgument(cache, frame, node, walk, bindings_len)) orelse return false;
            return allocatorInFrame(argument.cache, argument.frame, argument.node, depth + 1, walk, argument.bindings_len);
        },
        else => {},
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return false;
    if (call.ast.params.len != 0 or tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
    const receiver, const method = tree.nodeData(call.ast.fn_expr).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(method), "allocator")) return false;
    const actual = (try frame.containerOfNode(receiver)) orelse return false;
    return try frame.resolver.declaredInToolchainFile(actual.scope_handle.handle, "/std/heap/ArenaAllocator.zig") or
        try frame.resolver.declaredInToolchainFile(actual.scope_handle.handle, "/std/heap/FixedBufferAllocator.zig");
}

const BoundArgument = struct {
    cache: *file_cache_mod.FileCache,
    frame: resolver_mod.TypeResolver.ResolutionFrame,
    node: Ast.Node.Index,
    bindings_len: usize,
};

/// Runtime values use the same canonical formal/actual binding for both proofs.
fn boundFormalArgument(
    cache: *file_cache_mod.FileCache,
    frame: resolver_mod.TypeResolver.ResolutionFrame,
    node: Ast.Node.Index,
    walk: *ArenaOwnershipWalk,
    bindings_len: usize,
) ProofError!?BoundArgument {
    const tree = cache.tree;
    if (tree.nodeTag(node) != .identifier) return null;
    const actual = frame.actual_type orelse return null;
    const use = tree.nodeMainToken(node);
    var bound_index = bindings_len;
    while (bound_index != 0) {
        try walk.charge(tree, use);
        bound_index -= 1;
        const bound = walk.active[bound_index];
        if (!bound.actual_type.eql(actual)) continue;
        const declaration = tokens.enclosingFnDecl(tree, use) orelse return null;
        var proto_buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return null;
        const body = tokens.bodyOf(tree, declaration) orelse return null;
        const bindings = try cache.localBindings(proto, body);
        const binding = bindings.findAt(tree.tokenSlice(use), use) orelse return null;
        if (binding.origin != .param) return null;
        var params = proto.iterate(tree);
        var index: usize = 0;
        while (params.next()) |param| : (index += 1) {
            try walk.charge(tree, param.name_token orelse use);
            if (param.name_token != binding.name_token) continue;
            var argument_buffer: [2]Ast.Node.Index = undefined;
            const argument = (try bound.caller_frame.callArgumentIn(&argument_buffer, bound.call_node, index)) orelse return null;
            return .{
                .cache = bound.caller_cache,
                .frame = bound.caller_frame,
                .node = argument,
                .bindings_len = bound_index,
            };
        }
        return null;
    }
    return null;
}

/// This certifies returned storage, not infallibility. A helper can reject a
/// zero count before reaching the SDK, so this proof never skips a later try.
fn zeroStorageResult(
    cache: *file_cache_mod.FileCache,
    frame: resolver_mod.TypeResolver.ResolutionFrame,
    node: Ast.Node.Index,
    depth: u8,
    walk: *ArenaOwnershipWalk,
    bindings_len: usize,
) ProofError!bool {
    const tree = cache.tree;
    try walk.charge(tree, tree.firstToken(node));
    if (depth >= 16) return ownershipBudgetFailure(tree, tree.firstToken(node), .arena_proof_depth, 16);
    switch (tree.nodeTag(node)) {
        .error_value, .unreachable_literal => return true,
        .@"try" => return zeroStorageResult(cache, frame, tree.nodeData(node).node, depth + 1, walk, bindings_len),
        .grouped_expression => return zeroStorageResult(cache, frame, tree.nodeData(node).node_and_token[0], depth + 1, walk, bindings_len),
        .@"return" => return zeroStorageResult(cache, frame, tree.nodeData(node).opt_node.unwrap() orelse return false, depth + 1, walk, bindings_len),
        .@"catch" => {
            const pair = tree.nodeData(node).node_and_node;
            return try zeroStorageResult(cache, frame, pair[0], depth + 1, walk, bindings_len) and
                try zeroStorageResult(cache, frame, pair[1], depth + 1, walk, bindings_len);
        },
        .block, .block_semicolon, .block_two, .block_two_semicolon => {
            // A labelled break can supply a value before the final return.
            for (tree.tokens.items(.tag)[tree.firstToken(node)..tree.lastToken(node)]) |tag| {
                try walk.charge(tree, tree.firstToken(node));
                if (tag == .keyword_break) return false;
            }
            var buffer: [2]Ast.Node.Index = undefined;
            const statements = tree.blockStatements(&buffer, node) orelse return false;
            if (statements.len == 0 or tree.nodeTag(statements[statements.len - 1]) != .@"return") return false;
            return zeroStorageResult(cache, frame, statements[statements.len - 1], depth + 1, walk, bindings_len);
        },
        .identifier => {
            const use = tree.nodeMainToken(node);
            if (std_types.aliasInitializer(cache, tree, use)) |init| {
                if (!try localHeaderStable(cache, node, false, .{}, walk)) return false;
                const initializer = cache.nodeForExactSpan(init.first, init.last) orelse return false;
                return zeroStorageResult(cache, frame, initializer, depth + 1, walk, bindings_len);
            }
            return false;
        },
        else => {},
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return false;
    // The outer result cannot account for owning nested try operands.
    for (tree.tokens.items(.tag)[tree.firstToken(node)..tree.lastToken(node)]) |tag| {
        try walk.charge(tree, tree.firstToken(node));
        if (tag == .keyword_try) return false;
    }
    const callee = (try grow_analysis.actualCalleeOf(cache, fresh_storage.calleeQueryToken(tree, call), frame)) orelse return false;
    if (try frame.resolver.declaredInToolchainFile(callee.handle, "/std/mem/Allocator.zig")) {
        if (!std.mem.eql(u8, callee.tree.tokenSlice(callee.fn_token + 1), "alloc")) return false;
        var argument_buffer: [2]Ast.Node.Index = undefined;
        const count = (try frame.callArgumentIn(&argument_buffer, node, 2)) orelse return false;
        return zeroCountInFrame(cache, frame, count, depth + 1, walk, bindings_len);
    }
    for (walk.active[0..walk.len]) |active| {
        if (active.actual_type.eql(callee.reference.actual_type)) return false;
    }
    if (walk.len == walk.active.len)
        return ownershipBudgetFailure(tree, tree.firstToken(node), .arena_proof_depth, walk.active.len);
    const canonical: file_cache_mod.FileCache.ActualCallSummary = .{
        .callee = callee, .summary = null, .argument_offset = null, .read_only = null,
    };
    const declaring = (try canonical.declaringCache(cache)) orelse return false;
    const body = tokens.bodyOf(callee.tree, callee.declaration) orelse return false;
    walk.active[walk.len] = .{
        .actual_type = callee.reference.actual_type,
        .caller_cache = cache,
        .caller_frame = frame,
        .call_node = node,
    };
    walk.len += 1;
    defer walk.len -= 1;
    const declaring_frame = frame.resolver.frameForFunction(callee.reference);
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(callee.tree, &proto_buffer, callee.declaration) orelse return false;
    // Nested result queries can grow the cache's binding map. Keep a shallow
    // read-only view; its arena-backed items remain owned by the cache.
    const bindings = (try declaring.localBindings(proto, body)).*;
    var scan = call_effects.Scan.init(callee.tree, callee.declaration, &bindings);
    var returns: usize = 0;
    while (try scan.next()) |event| {
        if (event != .node) continue;
        const returned = event.node;
        try walk.charge(callee.tree, callee.tree.firstToken(returned));
        if (callee.tree.nodeTag(returned) != .@"return") continue;
        returns += 1;
        if (!try zeroStorageResult(declaring, declaring_frame, returned, depth + 1, walk, walk.len)) return false;
    }
    return returns != 0;
}

fn zeroCountInFrame(
    cache: *file_cache_mod.FileCache,
    frame: resolver_mod.TypeResolver.ResolutionFrame,
    node: Ast.Node.Index,
    depth: u8,
    walk: *ArenaOwnershipWalk,
    bindings_len: usize,
) ProofError!bool {
    const tree = cache.tree;
    try walk.charge(tree, tree.firstToken(node));
    if (depth >= 16) return ownershipBudgetFailure(tree, tree.firstToken(node), .arena_proof_depth, 16);
    switch (tree.nodeTag(node)) {
        .number_literal => return (std.fmt.parseInt(u64, tree.tokenSlice(tree.nodeMainToken(node)), 0) catch return false) == 0,
        .grouped_expression => return zeroCountInFrame(cache, frame, tree.nodeData(node).node_and_token[0], depth + 1, walk, bindings_len),
        .identifier => {
            if (std_types.aliasInitializer(cache, tree, tree.nodeMainToken(node))) |init| {
                if (!try localHeaderStable(cache, node, false, .{}, walk)) return false;
                return zeroCountInFrame(cache, frame, cache.nodeForExactSpan(init.first, init.last) orelse return false, depth + 1, walk, bindings_len);
            }
            const argument = (try boundFormalArgument(cache, frame, node, walk, bindings_len)) orelse return false;
            return zeroCountInFrame(argument.cache, argument.frame, argument.node, depth + 1, walk, argument.bindings_len);
        },
        else => return false,
    }
}

/// A local literal can preserve an allocator header without making all values
/// of its public type arena-backed. Pointer parameters and constructor results
/// require the shared contextual source proof and do not enter this certificate.
fn localAllocatorFieldUsesArena(
    cache: *file_cache_mod.FileCache,
    frame: resolver_mod.TypeResolver.ResolutionFrame,
    node: Ast.Node.Index,
    depth: u8,
    walk: *ArenaOwnershipWalk,
) ProofError!bool {
    const tree = cache.tree;
    if (tree.nodeTag(node) != .field_access) return false;
    const receiver, const field = tree.nodeData(node).node_and_token;
    if (tree.nodeTag(receiver) != .identifier) return false;
    const receiver_type = (try frame.typeOfNode(receiver)) orelse return false;
    if (frame.resolver.typeTag(receiver_type) != .@"struct") return false;
    if (!try localHeaderStable(cache, receiver, true, .{}, walk)) return false;
    const use = tree.nodeMainToken(receiver);
    const declaration = tokens.enclosingFnDecl(tree, use) orelse return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
    const bindings = try cache.localBindings(proto, tokens.bodyOf(tree, declaration) orelse return false);
    const binding = bindings.findAt(tree.tokenSlice(use), use) orelse return false;
    if (binding.origin != .literal) return false;
    const initializer = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
    var literal_buffer: [2]Ast.Node.Index = undefined;
    const literal = tree.fullStructInit(&literal_buffer, initializer) orelse return false;
    for (literal.ast.fields) |value| {
        try walk.charge(tree, tree.firstToken(value));
        const first = tree.firstToken(value);
        if (first < 2 or !std.mem.eql(u8, tree.tokenSlice(first - 2), tree.tokenSlice(field))) continue;
        return localFixedBufferHeaderLive(cache, frame, value, use, depth + 1, walk);
    }
    return false;
}

/// The allocator header keeps a live context pointer. Authenticate both SDK
/// operations and keep that actual local receiver stable through allocation.
fn localFixedBufferHeaderLive(
    cache: *file_cache_mod.FileCache,
    frame: resolver_mod.TypeResolver.ResolutionFrame,
    accessor: Ast.Node.Index,
    through: Ast.TokenIndex,
    depth: u8,
    walk: *ArenaOwnershipWalk,
) ProofError!bool {
    const tree = cache.tree;
    try walk.charge(tree, tree.firstToken(accessor));
    if (depth >= 16) return ownershipBudgetFailure(tree, tree.firstToken(accessor), .arena_proof_depth, 16);
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, accessor) orelse return false;
    if (call.ast.params.len != 0 or tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
    const receiver, const method = tree.nodeData(call.ast.fn_expr).node_and_token;
    if (tree.nodeTag(receiver) != .identifier or !std.mem.eql(u8, tree.tokenSlice(method), "allocator")) return false;
    const callee = (try grow_analysis.actualCalleeOf(cache, fresh_storage.calleeQueryToken(tree, call), frame)) orelse return false;
    if (!try frame.resolver.declaredInToolchainFile(callee.handle, "/std/heap/FixedBufferAllocator.zig")) return false;
    const use = tree.nodeMainToken(receiver);
    const declaration = tokens.enclosingFnDecl(tree, use) orelse return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
    const bindings = try cache.localBindings(proto, tokens.bodyOf(tree, declaration) orelse return false);
    const binding = bindings.findAt(tree.tokenSlice(use), use) orelse return false;
    if (binding.origin == .param or binding.origin == .loop_capture) return false;
    const initializer = cache.nodeForExactSpan(binding.rhs_first, binding.rhs_last) orelse return false;
    const constructor = tree.fullCall(&buffer, initializer) orelse return false;
    const initialized = (try grow_analysis.actualCalleeOf(cache, fresh_storage.calleeQueryToken(tree, constructor), frame)) orelse return false;
    if (!std.mem.eql(u8, initialized.tree.tokenSlice(initialized.fn_token + 1), "init") or
        !try frame.resolver.declaredInToolchainFile(initialized.handle, "/std/heap/FixedBufferAllocator.zig")) return false;
    return localHeaderStable(cache, receiver, true, .{ .through = through, .accessor = accessor }, walk);
}

fn rangeMentionsBinding(
    cache: *file_cache_mod.FileCache,
    bindings: *const @import("../../model/local_bindings.zig").LocalBindings,
    node: Ast.Node.Index,
    binding_token: Ast.TokenIndex,
    walk: *ArenaOwnershipWalk,
) ProofError!bool {
    const tree = cache.tree;
    var token = tree.firstToken(node);
    while (token <= tree.lastToken(node)) : (token += 1) {
        try walk.charge(tree, token);
        if (tree.tokenTag(token) != .identifier) continue;
        const binding = bindings.findAt(tree.tokenSlice(token), token) orelse continue;
        if (binding.name_token == binding_token) return true;
    }
    return false;
}

const LocalHeaderWindow = struct {
    through: ?Ast.TokenIndex = null,
    accessor: ?Ast.Node.Index = null,
};

/// Use the existing complete body scanner and lexical bindings. No field value
/// is inferred from a type name, a nearby allocator, or a subset of callers.
/// Enclosing loops extend the horizon through their later iterations.
fn localHeaderStable(
    cache: *file_cache_mod.FileCache,
    identifier: Ast.Node.Index,
    projection_only: bool,
    window: LocalHeaderWindow,
    walk: *ArenaOwnershipWalk,
) ProofError!bool {
    const tree = cache.tree;
    if (tree.nodeTag(identifier) != .identifier) return false;
    const use = tree.nodeMainToken(identifier);
    const declaration = tokens.enclosingFnDecl(tree, use) orelse return false;
    var proto_buffer: [1]Ast.Node.Index = undefined;
    const proto = tokens.fnProto(tree, &proto_buffer, declaration) orelse return false;
    const body = tokens.bodyOf(tree, declaration) orelse return false;
    // Callee resolution below can populate another body's cached bindings.
    // The immutable items outlive map growth; the borrowed map entry does not.
    const bindings = (try cache.localBindings(proto, body)).*;
    const selected = bindings.findAt(tree.tokenSlice(use), use) orelse return false;
    if (selected.origin == .param or selected.origin == .loop_capture or
        selected.name_token < tree.firstToken(body)) return false;
    const anchor = window.through orelse use;
    var horizon = anchor;
    var scan = call_effects.Scan.init(tree, declaration, &bindings);
    while (try scan.next()) |event| {
        const node = switch (event) {
            .node, .call, .write_or_unknown => |value| value,
            .write => |value| value.node,
        };
        try walk.charge(tree, tree.firstToken(node));
        const first = tree.firstToken(node);
        const last = tree.lastToken(node);
        if (event == .node and first <= anchor and last >= anchor and
            (tree.fullFor(node) != null or tree.fullWhile(node) != null))
            horizon = @max(horizon, last);
        if (last <= selected.rhs_last or first > horizon) {
            if (event == .node) scan.pending_children = .{ .array = @splat(.none) };
            continue;
        }
        switch (event) {
            .node => switch (tree.nodeTag(node)) {
                .identifier => {
                    const token = tree.nodeMainToken(node);
                    const binding = bindings.findAt(tree.tokenSlice(token), token) orelse continue;
                    if (binding.name_token != selected.name_token) continue;
                    if (projection_only) {
                        // A copied Allocator exposes its mutable context pointer.
                        // Only the one authenticated provider accessor and SDK
                        // member-call receiver positions can keep this proof.
                        if (window.accessor != null and token == use) continue;
                        if (token + 5 >= tree.tokens.len or
                            tree.tokenTag(token + 1) != .period or
                            tree.tokenTag(token + 3) != .period or
                            tree.tokenTag(token + 5) != .l_paren) return false;
                    }
                },
                .address_of => {
                    if (try rangeMentionsBinding(cache, &bindings, node, selected.name_token, walk)) return false;
                },
                .assign, .assign_mul, .assign_div, .assign_mod, .assign_add, .assign_sub,
                .assign_shl, .assign_shl_sat, .assign_shr, .assign_bit_and, .assign_bit_xor,
                .assign_bit_or, .assign_mul_wrap, .assign_add_wrap, .assign_sub_wrap,
                .assign_mul_sat, .assign_add_sat, .assign_sub_sat,
                => if (try rangeMentionsBinding(cache, &bindings, tree.nodeData(node).node_and_node[0], selected.name_token, walk)) return false,
                else => {},
            },
            .call => {
                if (window.accessor == node) continue;
                var call_buffer: [1]Ast.Node.Index = undefined;
                const call = tree.fullCall(&call_buffer, node) orelse return false;
                if (projection_only) {
                    if (!try rangeMentionsBinding(cache, &bindings, node, selected.name_token, walk)) continue;
                    const resolver = cache.zls orelse return false;
                    const callee = (try grow_analysis.actualCalleeOf(cache, fresh_storage.calleeQueryToken(tree, call), null)) orelse return false;
                    if (!try resolver.declaredInToolchainFile(callee.handle, "/std/mem/Allocator.zig")) return false;
                    continue;
                }
                if (tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
                const receiver = tree.nodeData(call.ast.fn_expr).node_and_token[0];
                if (tree.nodeTag(receiver) != .identifier) continue;
                const token = tree.nodeMainToken(receiver);
                const binding = bindings.findAt(tree.tokenSlice(token), token) orelse continue;
                if (binding.name_token == selected.name_token) return false;
            },
            .write_or_unknown => return false,
            .write => {},
        }
    }
    return true;
}

fn nodeIsAllocator(cache: *file_cache_mod.FileCache, node: Ast.Node.Index) ProofError!bool {
    const resolver = cache.zls orelse return false;
    const actual = (try resolver.containerOfNode(node)) orelse return false;
    return resolver.declaredInToolchainFile(actual.scope_handle.handle, "/std/mem/Allocator.zig");
}

fn allocatorExprComesFromArena(tree: *const Ast, cache: *file_cache_mod.FileCache, node: Ast.Node.Index, depth: u8) ProofError!bool {
    if (depth >= 16) return ownershipBudgetFailure(tree, tree.firstToken(node), .arena_proof_depth, 16);
    if (tree.nodeTag(node) == .grouped_expression) {
        return allocatorExprComesFromArena(tree, cache, tree.nodeData(node).node_and_token[0], depth + 1);
    }
    if (tree.nodeTag(node) == .identifier) {
        const use = tree.nodeMainToken(node);
        if (std_types.aliasInitializer(cache, tree, use)) |init| {
            const initializer = cache.nodeForExactSpan(init.first, init.last) orelse return false;
            return allocatorExprComesFromArena(tree, cache, initializer, depth + 1);
        }
        const resolver = cache.zls orelse return false;
        const fn_decl = (try resolver.enclosingFunctionAt(use)) orelse return false;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tokens.fnProto(tree, &buffer, fn_decl) orelse return false;
        const body = tokens.bodyOf(tree, fn_decl) orelse return false;
        const bindings = try cache.localBindings(proto, body);
        const binding = bindings.findAt(tree.tokenSlice(use), use) orelse return false;
        if (binding.origin != .param) return false;
        var params = proto.iterate(tree);
        var parameter: usize = 0;
        while (params.next()) |param| : (parameter += 1) {
            if (param.name_token != binding.name_token) continue;
            const calls = (try cache.closedLocalCalls(fn_decl)) orelse return false;
            if (calls.len == 0) return false;
            for (calls) |call_node| {
                var call_buffer: [2]Ast.Node.Index = undefined;
                const argument = (try resolver.resolutionFrame().callArgumentIn(&call_buffer, call_node, parameter)) orelse return false;
                if (!try allocatorExprComesFromArena(tree, cache, argument, depth + 1)) return false;
            }
            return true;
        }
        return false;
    }
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return false;
    if (call.ast.params.len != 0 or tree.nodeTag(call.ast.fn_expr) != .field_access)
        return resolvedCallReturnsArena(cache, node);
    const receiver, const method = tree.nodeData(call.ast.fn_expr).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(method), "allocator"))
        return resolvedCallReturnsArena(cache, node);
    if (cache.zls) |resolver| {
        if (try resolver.containerOfNode(receiver)) |actual| {
            if (try resolver.declaredInToolchainFile(actual.scope_handle.handle, "/std/heap/ArenaAllocator.zig") or
                try resolver.declaredInToolchainFile(actual.scope_handle.handle, "/std/heap/FixedBufferAllocator.zig"))
                return true;
        }
        return resolvedCallReturnsArena(cache, node);
    }
    // The syntax-only pass still needs declaration identity, never a name
    // containing "arena". Parameters and standard `.init` expressions suffice.
    if (tree.nodeTag(receiver) != .identifier) return false;
    const use = tree.nodeMainToken(receiver);
    const fn_decl = tokens.enclosingFnDecl(tree, use) orelse return false;
    const body = tokens.bodyOf(tree, fn_decl) orelse return false;
    const proto = tokens.fnProto(tree, &buffer, fn_decl) orelse return false;
    const bindings = try cache.localBindings(proto, body);
    const binding = bindings.findAt(tree.tokenSlice(use), use) orelse return false;
    if (binding.origin == .param) {
        var params = proto.iterate(tree);
        while (params.next()) |param| {
            if (param.name_token != binding.name_token) continue;
            const type_node = param.type_expr orelse return false;
            return std_types.isType(cache, tree, tree.firstToken(type_node), tree.lastToken(type_node), "heap", "ArenaAllocator", .{ .allow_pointer = true });
        }
        return false;
    }
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const decl = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
        if (decl.ast.mut_token + 1 != binding.name_token) continue;
        const init = decl.ast.init_node.unwrap() orelse return false;
        const init_call = tree.fullCall(&buffer, init) orelse return false;
        if (tree.nodeTag(init_call.ast.fn_expr) != .field_access) return false;
        const type_node, const init_method = tree.nodeData(init_call.ast.fn_expr).node_and_token;
        if (!std.mem.eql(u8, tree.tokenSlice(init_method), "init")) return false;
        return std_types.isType(cache, tree, tree.firstToken(type_node), tree.lastToken(type_node), "heap", "ArenaAllocator", .{});
    }
    return false;
}

/// An allocator accessor can initialize an arena lazily and then return its
/// allocator. Read every return in the resolved declaration and its frame;
/// an accessor returning a general allocator field never supplies this proof.
fn resolvedCallReturnsArena(cache: *file_cache_mod.FileCache, node: Ast.Node.Index) ProofError!bool {
    const resolver = cache.zls orelse return false;
    if (!try nodeIsAllocator(cache, node)) return false;
    const tree = cache.tree;
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, node) orelse return false;
    const callee = (try grow_analysis.actualCalleeOf(cache, fresh_storage.calleeQueryToken(tree, call), null)) orelse return false;
    const declaring_tree = callee.tree;
    const body = tokens.bodyOf(declaring_tree, callee.declaration) orelse return false;
    const frame = resolver.frameForFunction(callee.reference);
    var returns: usize = 0;
    for (declaring_tree.nodes.items(.tag), 0..) |tag, raw| {
        if (tag != .@"return") continue;
        const returned: Ast.Node.Index = @enumFromInt(raw);
        const first = declaring_tree.firstToken(returned);
        if (first < declaring_tree.firstToken(body) or first > declaring_tree.lastToken(body)) continue;
        if (tokens.enclosingFnDecl(declaring_tree, first) != callee.declaration) continue;
        const value = declaring_tree.nodeData(returned).opt_node.unwrap() orelse return false;
        const allocator_call = declaring_tree.fullCall(&buffer, value) orelse return false;
        if (allocator_call.ast.params.len != 0 or declaring_tree.nodeTag(allocator_call.ast.fn_expr) != .field_access) return false;
        const receiver, const method = declaring_tree.nodeData(allocator_call.ast.fn_expr).node_and_token;
        if (!std.mem.eql(u8, declaring_tree.tokenSlice(method), "allocator")) return false;
        const actual = (try frame.containerOfNode(receiver)) orelse return false;
        if (!try resolver.declaredInToolchainFile(actual.scope_handle.handle, "/std/heap/ArenaAllocator.zig") and
            !try resolver.declaredInToolchainFile(actual.scope_handle.handle, "/std/heap/FixedBufferAllocator.zig")) return false;
        returns += 1;
    }
    return returns != 0;
}
fn firstTryUsesScopedArena(tree: *const Ast, cache: *file_cache_mod.FileCache, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    // Typed checks use the declaration-bound caller census above.
    if (cache.zls != null) return false;
    if (start + 2 >= end or tree.tokenTag(start) != .identifier or tree.tokenTag(start + 1) != .period) return false;
    const model = cache.fileModel() catch return false;
    for (model.fns) |function| {
        if (start < function.body_first or start > function.body_last) continue;
        if (function.is_pub) return false;
        if (function.name_token >= 2 and tree.tokenTag(function.name_token - 2) == .keyword_export) return false;
        var buffer: [1]Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buffer, function.fn_decl) orelse return false;
        var params = proto.iterate(tree);
        var index: usize = 0;
        while (params.next()) |param| : (index += 1) {
            const name_token = param.name_token orelse continue;
            if (std.mem.eql(u8, tree.tokenSlice(name_token), tree.tokenSlice(start))) {
                return allCallsUseScopedArena(tree, cache, function, index);
            }
        }
        return false;
    }
    return false;
}

fn allCallsUseScopedArena(tree: *const Ast, cache: *file_cache_mod.FileCache, function: file_model.FnInfo, parameter: usize) bool {
    var references: usize = 0;
    for (tree.tokens.items(.tag), 0..) |tag, index| {
        const token: Ast.TokenIndex = @intCast(index);
        if (tag == .builtin and (std.mem.eql(u8, tree.tokenSlice(token), "@field") or
            std.mem.eql(u8, tree.tokenSlice(token), "@export"))) return false;
        if (tag != .identifier or token == function.name_token) continue;
        if (std.mem.eql(u8, tree.tokenSlice(token), function.name)) references += 1;
    }
    var calls: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => {},
            else => continue,
        }
        var buffer: [1]Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(index)) orelse continue;
        if (tree.nodeTag(call.ast.fn_expr) != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(call.ast.fn_expr)), function.name)) continue;
        if (parameter >= call.ast.params.len or !argumentHasArenaCleanup(tree, cache, call.ast.params[parameter])) return false;
        calls += 1;
    }
    return calls != 0 and calls == references;
}

fn argumentHasArenaCleanup(tree: *const Ast, cache: *file_cache_mod.FileCache, argument: Ast.Node.Index) bool {
    var buffer: [1]Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, argument) orelse return false;
    if (call.ast.params.len != 0 or tree.nodeTag(call.ast.fn_expr) != .field_access) return false;
    const access = tree.nodeData(call.ast.fn_expr).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(access[1]), "allocator") or tree.nodeTag(access[0]) != .identifier) return false;
    const receiver = tree.tokenSlice(tree.nodeMainToken(access[0]));
    const anchor = tree.firstToken(argument);
    const body_start = enclosingBodyStart(tree, anchor) orelse return false;
    var declaration: ?Ast.full.VarDecl = null;
    for (tree.nodes.items(.tag), 0..) |_, index| {
        const candidate = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
        const name_token = candidate.ast.mut_token + 1;
        if (name_token < body_start or name_token >= anchor) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), receiver)) continue;
        if (declaration) |previous| {
            if (previous.ast.mut_token > candidate.ast.mut_token) continue;
        }
        declaration = candidate;
    }
    const decl = declaration orelse return false;
    const initializer = decl.ast.init_node.unwrap() orelse return false;
    const init_call = tree.fullCall(&buffer, initializer) orelse return false;
    if (tree.nodeTag(init_call.ast.fn_expr) != .field_access) return false;
    const init_access = tree.nodeData(init_call.ast.fn_expr).node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(init_access[1]), "init")) return false;
    const receiver_type = init_access[0];
    // Identity, not spelling: the receiver expression names the declaration,
    // so a namespace alias or a `const` alias of the same arena answers the
    // same way, and a project type that merely shares the name does not.
    if (!std_types.isType(
        cache,
        tree,
        tree.firstToken(receiver_type),
        tree.lastToken(receiver_type),
        "heap",
        "ArenaAllocator",
        .{},
    )) return false;
    return hasImmediateCleanup(tree, tree.lastToken(initializer) + 1, anchor, receiver);
}

fn enclosingBodyStart(tree: *const Ast, anchor: Ast.TokenIndex) ?Ast.TokenIndex {
    var result: ?Ast.TokenIndex = null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .fn_decl) continue;
        const body = tree.nodeData(@enumFromInt(index)).node_and_node[1];
        const start = tree.firstToken(body);
        if (start > anchor or tree.lastToken(body) < anchor) continue;
        if (result == null or start > result.?) result = start;
    }
    return result;
}

fn hasImmediateCleanup(tree: *const Ast, start: Ast.TokenIndex, anchor: Ast.TokenIndex, receiver: []const u8) bool {
    const tags = tree.tokens.items(.tag);
    if (start + 7 >= anchor) return false;
    if (tags[start] != .semicolon or tags[start + 1] != .keyword_defer or
        tags[start + 2] != .identifier or tags[start + 3] != .period or
        tags[start + 4] != .identifier or tags[start + 5] != .l_paren or
        tags[start + 6] != .r_paren or tags[start + 7] != .semicolon) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(start + 2), receiver) or
        !std.mem.eql(u8, tree.tokenSlice(start + 4), "deinit")) return false;
    var token = start + 8;
    while (token < anchor) : (token += 1) {
        if (tags[token] == .l_brace or tags[token] == .r_brace) return false;
        if (tags[token] == .identifier and std.mem.eql(u8, tree.tokenSlice(token), receiver)) return false;
    }
    return true;
}

/// SEMANTIC allocation signal: returns true iff some identifier operand in the
/// first-try expression `[start, end)` resolves to type `std.mem.Allocator`
/// AND is in receiver position (followed by `.`).  Requiring receiver position
/// avoids signalling on pool/builder patterns like `pool.put(allocator, bytes)`
/// where the allocator is passed as an argument — the allocation goes into
/// the pool's internal buffer, not directly to the caller, so there is no
/// individual per-field leak from the struct-literal failure.
/// No-op (false) when the type engine is absent.
fn firstTryUsesAllocator(
    cache: *file_cache_mod.FileCache,
    ident_nodes: *const std.AutoHashMapUnmanaged(Ast.TokenIndex, Ast.Node.Index),
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    var t = start;
    while (t < end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        const node = ident_nodes.get(t) orelse continue;
        const tyname = cache.typeNameOfNode(node) orelse continue;
        if (!std.mem.eql(u8, tyname, "Allocator")) continue;
        // Allocator must be in receiver position (followed by '.') — e.g.
        // `gpa.alloc(T, n)`.  If followed by ',' or ')' the allocator is
        // an argument to a pool/builder and does not individually leak.
        if (t + 1 < end and tags[t + 1] == .period) return true;
    }
    return false;
}

/// Returns true iff the token range [start, end) contains an identifier or
/// builtin whose slice (case-insensitively) contains an allocation signal:
/// `alloc`, `dupe`, `clone`, `create`, or `ownedslice` (covers
/// `toOwnedSlice`).  These are the calls that hand back an owned resource a
/// failing later `try` would leak.  Decoders/parsers (`read_*`, `parse*`)
/// return value types and match no signal, so they are suppressed.
///
/// Precision rules to avoid over-signalling:
///   - "alloc" in any form (the common allocator variable name, allocPrint,
///     allocate, …) only signals when in method-call position (preceded by
///     `.`) or direct-call position (followed by `(`).  Bare `allocator`
///     passed as an argument to a pool or builder — e.g.
///     `pool.put(allocator, bytes)` — does NOT signal because the
///     allocation goes into the pool's internal buffer, not to the caller.
///   - "create" only signals for method calls (preceded by `.`).
///   - "dupe", "clone", "ownedslice" signal in any position.
fn tryExprAllocates(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    var t = start;
    while (t < end) : (t += 1) {
        if (tags[t] != .identifier and tags[t] != .builtin) continue;
        const s = tree.tokenSlice(t);
        if (containsIgnoreCase(s, "dupe") or
            containsIgnoreCase(s, "clone") or
            containsIgnoreCase(s, "ownedslice")) return true;
        // "alloc" in any form: require method-call (preceded by '.') or
        // direct-call (followed by '(') position to exclude allocator
        // variable names passed as arguments.
        if (containsIgnoreCase(s, "alloc")) {
            const before_is_dot = t > start and tags[t - 1] == .period;
            const after_is_paren = t + 1 < end and tags[t + 1] == .l_paren;
            if (before_is_dot or after_is_paren) return true;
        }
        // "create": only signal for method calls (preceded by '.')
        if (containsIgnoreCase(s, "create") and t > start and tags[t - 1] == .period) return true;
    }
    return false;
}


/// Case-insensitive substring test (`needle` must be lowercase).
fn containsIgnoreCase(haystack: []const u8, needle: []const u8) bool {
    if (needle.len == 0 or haystack.len < needle.len) return false;
    var i: usize = 0;
    outer: while (i + needle.len <= haystack.len) : (i += 1) {
        var j: usize = 0;
        while (j < needle.len) : (j += 1) {
            if (std.ascii.toLower(haystack[i + j]) != needle[j]) continue :outer;
        }
        return true;
    }
    return false;
}

fn report(
    gpa: std.mem.Allocator,
    problems: *std.ArrayListUnmanaged(Problem),
    tree: *const Ast,
    second_tok: Ast.TokenIndex,
    field1: []const u8,
    field2: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        gpa,
        "`.{s} = try ...` followed by `.{s} = try ...` in the same initializer — if the second `try` fails, the allocation from the first leaks because `errdefer` cannot appear inside a struct literal; bind each to a local with `errdefer` first",
        .{ field1, field2 },
    );
    errdefer gpa.free(msg);
    try problems.append(gpa, .{
        .rule_id = R,
        .severity = .@"error",
        .start = try Pos.fromTokenStart(tree, second_tok),
        .end = try Pos.fromTokenEnd(tree, second_tok + 3),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "struct-literal-multiple-try: fires on two try fields" {
    try testing.expectFires(check, R,
        \\fn parse(gpa: Allocator, parser: *Parser) !Ast {
        \\    return Ast{
        \\        .extra_data = try parser.extra_data.toOwnedSlice(gpa),
        \\        .errors     = try parser.errors.toOwnedSlice(gpa),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: single try field does not fire" {
    try testing.expectNoFire(check,
        \\fn parse(gpa: Allocator, parser: *Parser) !Ast {
        \\    return Ast{
        \\        .extra_data = try parser.extra_data.toOwnedSlice(gpa),
        \\        .errors     = &.{},
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: non-try second field does not fire" {
    try testing.expectNoFire(check,
        \\fn build() Foo {
        \\    return Foo{
        \\        .a = compute(),
        \\        .b = 42,
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: fires in return with named init" {
    try testing.expectFires(check, R,
        \\fn makeNode(gpa: Allocator) !Node {
        \\    return Node{
        \\        .name  = try gpa.dupe(u8, "hello"),
        \\        .value = try gpa.dupe(u8, "world"),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: decoder tries (no allocation) do not fire" {
    try testing.expectNoFire(check,
        \\fn readHeader(self: *Decoder) !FrameHeader {
        \\    return .{
        \\        .type = try self.read_enum(FrameType),
        \\        .channel = try self.read_enum(Channel),
        \\        .size = try self.read_int(u32),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: parseUnsigned tries do not fire" {
    try testing.expectNoFire(check,
        \\fn parseVersion(arg_major: []const u8, arg_minor: []const u8) !Version {
        \\    return .{
        \\        .major = try std.fmt.parseUnsigned(u8, arg_major, 10),
        \\        .minor = try std.fmt.parseUnsigned(u8, arg_minor, 10),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: alloc.alloc tries fire" {
    try testing.expectFires(check, R,
        \\fn makeLexer(alloc: Allocator, n_words: usize) !Lexer {
        \\    return .{
        \\        .ident      = try alloc.alloc(u64, n_words),
        \\        .newline    = try alloc.alloc(u64, n_words),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: deepClone tries fire" {
    try testing.expectFires(check, R,
        \\fn cloneIf(allocator: Allocator, el: *If) !If {
        \\    return .{
        \\        .test_ = try el.test_.deepClone(allocator),
        \\        .yes = try el.yes.deepClone(allocator),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: try in nested call args does not fire" {
    try testing.expectNoFire(check,
        \\fn callFn(a: u8, b: u8) void {
        \\    process(a, b);
        \\}
        \\
    );
}

test "struct-literal-multiple-try: factory fn (create prefix) does not fire" {
    try testing.expectNoFire(check,
        \\fn buildStep(b: *Build) !GhosttyI18n {
        \\    return .{
        \\        .update_step = try createUpdateStep(b),
        \\        .steps = try steps.toOwnedSlice(b.allocator),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: arena allocator does not fire" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator) !Pair {
        \\    const memory = storage.allocator();
        \\    return .{ .a = try memory.dupe(u8, "a"), .b = try memory.dupe(u8, "b") };
        \\}
    );
}

test "struct-literal-multiple-try: method .create fires" {
    try testing.expectFires(check, R,
        \\fn makeNode(gpa: Allocator) !Node {
        \\    return .{
        \\        .left  = try gpa.create(LeftNode),
        \\        .right = try gpa.create(RightNode),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: allocator named arena passed to toOwnedSlice still fires" {
    // An Allocator parameter does not acquire arena provenance from its name.
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Result = struct { bytes: []u8, source_offsets: []u32 };
        \\pub fn writeRecord(arena: std.mem.Allocator, out: *std.ArrayList(u8), map: *std.ArrayList(u32)) !Result {
        \\    return Result{
        \\        .bytes = try out.toOwnedSlice(arena),
        \\        .source_offsets = try map.toOwnedSlice(arena),
        \\    };
        \\}
    );
}

test "struct-literal-multiple-try: pool.put(allocator, bytes) does not fire" {
    // pool.put(allocator, bytes) passes the allocator as an ARGUMENT to a
    // pool/builder — all puts go into the pool's internal buffer and are freed
    // as a unit when the pool is destroyed.  The `allocator` variable name
    // contains "alloc" but is NOT in receiver position, so neither the
    // type-based nor name-based allocation signals should fire.
    try testing.expectNoFire(check,
        \\fn writeRecord(allocator: Allocator, pool: *PoolBuilder, ln: Line) !Record {
        \\    return Record{
        \\        .source = try pool.put(allocator, ln.source),
        \\        .tokens = try pool.put(allocator, ln.tokens),
        \\    };
        \\}
        \\
    );
}

test "struct-literal-multiple-try: errdefer arena.deinit() in enclosing fn suppresses" {
    // Provenance follows the allocator alias, independent of token distance
    // from the arena's initialization and cleanup.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const ArenaAllocator = std.heap.ArenaAllocator;
        \\const ArrayList = std.ArrayListUnmanaged;
        \\fn buildModel(gpa: std.mem.Allocator, count: usize) !Model {
        \\    var arena = ArenaAllocator.init(gpa);
        \\    errdefer arena.deinit();
        \\    const a = arena.allocator();
        \\    var names: ArrayList([]const u8) = .empty;
        \\    var fns: ArrayList([]const u8) = .empty;
        \\    var i: usize = 0;
        \\    while (i < count) : (i += 1) {
        \\        try names.append(a, "x");
        \\        try fns.append(a, "y");
        \\    }
        \\    return .{
        \\        .names = try names.toOwnedSlice(a),
        \\        .fns = try fns.toOwnedSlice(a),
        \\    };
        \\}
        \\const Model = struct { names: [][]const u8, fns: [][]const u8 };
        \\
    );
}

test "struct-literal-multiple-try: no errdefer arena still fires" {
    // Control: without errdefer arena.deinit(), the rule must still fire
    // so the suppressor is not inadvertently always-true.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\fn buildPair(gpa: std.mem.Allocator) !Pair {
        \\    return Pair{
        \\        .a = try gpa.alloc(u8, 4),
        \\        .b = try gpa.alloc(u8, 4),
        \\    };
        \\}
        \\const Pair = struct { a: []u8, b: []u8 };
        \\
    );
}

test "skript residual: private copy helper uses caller-owned arena" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn run(gpa: std.mem.Allocator) !void {
        \\    var scope = std.heap.ArenaAllocator.init(gpa);
        \\    defer scope.deinit();
        \\    const pair = try duplicate(scope.allocator());
        \\    _ = pair;
        \\}
    );
}

test "skript residual: private copy helper also called with owned allocator" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn run(gpa: std.mem.Allocator) !Pair {
        \\    var scope = std.heap.ArenaAllocator.init(gpa);
        \\    defer scope.deinit();
        \\    _ = try duplicate(scope.allocator());
        \\    return duplicate(gpa);
        \\}
    );
}

test "skript residual: cloned range values do not own allocations" {
    try testing.expectNoFire(check,
        \\const Range = struct { start: u32, len: u32 };
        \\const RangeAlias = Range;
        \\const Pair = struct { first: Range, second: Range };
        \\fn cloneRange(start: u32) !RangeAlias {
        \\    return .{ .start = start, .len = 1 };
        \\}
        \\pub fn run() !Pair {
        \\    return .{
        \\        .first = try cloneRange(0),
        \\        .second = try cloneRange(1),
        \\    };
        \\}
    );
}

test "skript residual: cloned buffer values still own allocations" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Buffer = struct { bytes: []u8 };
        \\const Pair = struct { first: Buffer, second: Buffer };
        \\fn cloneBuffer(memory: std.mem.Allocator) !Buffer {
        \\    return .{ .bytes = try memory.dupe(u8, "buffer") };
        \\}
        \\pub fn run(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try cloneBuffer(memory),
        \\        .second = try cloneBuffer(memory),
        \\    };
        \\}
    );
}

test "struct-literal-multiple-try: imported range handles retain storage in their owner" {
    try expectImportedRangeCount("pub const Range = struct { start: u32, len: u32 };", 0);
}

test "struct-literal-multiple-try: imported owning result still leaks on the second try" {
    try expectImportedRangeCount("pub const Range = struct { start: u32, len: u32, bytes: []u8 };", 1);
}

test "struct-literal-multiple-try: unresolved imported result remains conservative" {
    try expectImportedRangeCount("pub const Range = Missing;", 1);
}

test "struct-literal-multiple-try: imported scalar handle with dispose still owns an allocation" {
    try expectImportedRuleCount(
        \\const std = @import("std");
        \\pub const Handle = struct {
        \\    address: usize,
        \\    pub fn dispose(self: Handle, gpa: std.mem.Allocator) void {
        \\        gpa.destroy(@as(*u8, @ptrFromInt(self.address)));
        \\    }
        \\};
        \\pub fn clone(gpa: std.mem.Allocator) !Handle {
        \\    const ptr = try gpa.create(u8);
        \\    ptr.* = 0;
        \\    return .{ .address = @intFromPtr(ptr) };
        \\}
    ,
        \\const std = @import("std");
        \\const handles = @import("ranges.zig");
        \\const Pair = struct { first: handles.Handle, second: u32 };
        \\fn fail(should_fail: bool) !u32 {
        \\    if (should_fail) return error.Bad;
        \\    return 0;
        \\}
        \\pub fn clonePair(gpa: std.mem.Allocator, should_fail: bool) !Pair {
        \\    return .{
        \\        .first = try handles.clone(gpa),
        \\        .second = try fail(should_fail),
        \\    };
        \\}
    , 1);
}

test "struct-literal-multiple-try: local scalar handle with dispose still owns an allocation" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Handle = struct {
        \\    address: usize,
        \\    fn dispose(self: Handle, gpa: std.mem.Allocator) void {
        \\        gpa.destroy(@as(*u8, @ptrFromInt(self.address)));
        \\    }
        \\};
        \\const Pair = struct { first: Handle, second: u32 };
        \\fn cloneHandle(gpa: std.mem.Allocator) !Handle {
        \\    const ptr = try gpa.create(u8);
        \\    ptr.* = 0;
        \\    return .{ .address = @intFromPtr(ptr) };
        \\}
        \\fn fail(should_fail: bool) !u32 {
        \\    if (should_fail) return error.Bad;
        \\    return 0;
        \\}
        \\pub fn clonePair(gpa: std.mem.Allocator, should_fail: bool) !Pair {
        \\    return .{
        \\        .first = try cloneHandle(gpa),
        \\        .second = try fail(should_fail),
        \\    };
        \\}
    );
}

fn expectImportedRangeCount(range_source: []const u8, expected: usize) !void {
    const source: [:0]const u8 =
        \\const std = @import("std");
        \\const ranges = @import("ranges.zig");
        \\const Range = ranges.Range;
        \\const Node = struct { labels: Range, values: Range };
        \\const Storage = struct {
        \\    allocator: std.mem.Allocator,
        \\    labels: std.ArrayList(u32) = .empty,
        \\    edges: std.ArrayList(u32) = .empty,
        \\    fn deinit(self: *Storage) void {
        \\        self.labels.deinit(self.allocator);
        \\        self.edges.deinit(self.allocator);
        \\    }
        \\};
        \\fn cloneLabels(destination: *Storage) !Range {
        \\    const start: u32 = @intCast(destination.labels.items.len);
        \\    try destination.labels.append(destination.allocator, 1);
        \\    if (@hasField(Range, "bytes")) return .{
        \\        .start = start, .len = 1,
        \\        .bytes = try destination.allocator.dupe(u8, "label"),
        \\    };
        \\    return .{ .start = start, .len = 1 };
        \\}
        \\fn cloneEdges(destination: *Storage) !Range {
        \\    const start: u32 = @intCast(destination.edges.items.len);
        \\    try destination.edges.append(destination.allocator, 2);
        \\    if (@hasField(Range, "bytes")) return .{
        \\        .start = start, .len = 1,
        \\        .bytes = try destination.allocator.dupe(u8, "edge"),
        \\    };
        \\    return .{ .start = start, .len = 1 };
        \\}
        \\fn cloneNode(destination: *Storage) !Node {
        \\    return .{
        \\        .labels = try cloneLabels(destination),
        \\        .values = try cloneEdges(destination),
        \\    };
        \\}
        \\pub fn snapshot(allocator: std.mem.Allocator) !Storage {
        \\    var result: Storage = .{ .allocator = allocator };
        \\    errdefer result.deinit();
        \\    _ = try cloneNode(&result);
        \\    return result;
        \\}
    ;
    try expectImportedRuleCount(range_source, source, expected);
}

fn expectImportedRuleCount(range_source: []const u8, source: [:0]const u8, expected: usize) !void {
    const gpa = std.testing.allocator;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "ranges.zig", .data = range_source });
    const directory = try tmp.dir.realPathFileAlloc(io, ".", gpa);
    defer gpa.free(directory);
    const path = try std.fs.path.join(gpa, &.{ directory, "main.zig" });
    defer gpa.free(path);
    try tmp.dir.writeFile(io, .{ .sub_path = "main.zig", .data = source });
    const engine = @import("../../type_resolver.zig");
    var context: engine.TypeContext = undefined;
    try context.init(gpa, io);
    defer context.deinit();
    context.store.source_policy = .{ .roots = &.{directory} };
    var resolver: engine.TypeResolver = undefined;
    try resolver.init(&context, gpa, path, source);
    defer resolver.deinit();
    const tree = &resolver.handle.document.tree;
    var cache = file_cache_mod.FileCache.init(gpa, tree);
    defer cache.deinit();
    cache.setZls(&resolver);
    var problems: std.ArrayListUnmanaged(Problem) = .empty;
    defer testing.freeProblems(gpa, &problems);
    try check(gpa, tree, &cache, &config_mod.Default, &problems);
    var count: usize = 0;
    for (problems.items) |problem| {
        if (std.mem.eql(u8, problem.rule_id, R)) count += 1;
    }
    try std.testing.expectEqual(expected, count);
}

test "struct-literal-multiple-try: a std heap namespace alias is still the std arena" {
    // The arena is named through `const heap_namespace = std.heap;`, so the
    // suppression cannot come from a source spelling of `std.heap`.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const heap_namespace = std.heap;
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn buildPair(gpa: std.mem.Allocator) !Pair {
        \\    var scope = heap_namespace.ArenaAllocator.init(gpa);
        \\    defer scope.deinit();
        \\    return duplicate(scope.allocator());
        \\}
    );
}

test "struct-literal-multiple-try: a const alias of the std arena is still the std arena" {
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Arena = std.heap.ArenaAllocator;
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn buildPair(gpa: std.mem.Allocator) !Pair {
        \\    var scope = Arena.init(gpa);
        \\    defer scope.deinit();
        \\    return duplicate(scope.allocator());
        \\}
    );
}

test "struct-literal-multiple-try: a project ArenaAllocator with owning fields still fires" {
    // Same shape, same cleanup, pointer-owning storage — but the declaration
    // is the project's, so nothing is freed as a unit when it dies.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const ArenaAllocator = struct {
        \\    buffer: [*]u8,
        \\    end: usize,
        \\    child: std.mem.Allocator,
        \\    pub fn init(gpa: std.mem.Allocator) ArenaAllocator {
        \\        return .{ .buffer = undefined, .end = 0, .child = gpa };
        \\    }
        \\    pub fn deinit(self: *ArenaAllocator) void {
        \\        self.end = 0;
        \\    }
        \\    pub fn allocator(self: *ArenaAllocator) std.mem.Allocator {
        \\        return self.child;
        \\    }
        \\};
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn buildPair(gpa: std.mem.Allocator) !Pair {
        \\    var scope = ArenaAllocator.init(gpa);
        \\    defer scope.deinit();
        \\    return duplicate(scope.allocator());
        \\}
    );
}

test "struct-literal-multiple-try: a custom namespace alias for ArenaAllocator still fires" {
    // `const heap = struct { pub const ArenaAllocator = ... };` mirrors the
    // standard path segment for segment and still owns its own storage.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const heap = struct {
        \\    pub const ArenaAllocator = struct {
        \\        buffer: [*]u8,
        \\        end: usize,
        \\        child: std.mem.Allocator,
        \\        pub fn init(gpa: std.mem.Allocator) @This() {
        \\            return .{ .buffer = undefined, .end = 0, .child = gpa };
        \\        }
        \\        pub fn deinit(self: *@This()) void {
        \\            self.end = 0;
        \\        }
        \\        pub fn allocator(self: *@This()) std.mem.Allocator {
        \\            return self.child;
        \\        }
        \\    };
        \\};
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn buildPair(gpa: std.mem.Allocator) !Pair {
        \\    var scope = heap.ArenaAllocator.init(gpa);
        \\    defer scope.deinit();
        \\    return duplicate(scope.allocator());
        \\}
    );
}

test "struct-literal-multiple-try: a parameter shadowing the std namespace still fires" {
    // `std` here is a generic parameter of the caller's own, so
    // `std.heap.ArenaAllocator` is not the standard-library arena even though
    // it is spelled exactly so.
    try testing.expectFires(check, R,
        \\const library = @import("std");
        \\const Heap = struct {
        \\    pub const heap = struct {
        \\        pub const ArenaAllocator = struct {
        \\            buffer: [*]u8,
        \\            end: usize,
        \\            child: library.mem.Allocator,
        \\            pub fn init(gpa: library.mem.Allocator) @This() {
        \\                return .{ .buffer = undefined, .end = 0, .child = gpa };
        \\            }
        \\            pub fn deinit(self: *@This()) void {
        \\                self.end = 0;
        \\            }
        \\            pub fn allocator(self: *@This()) library.mem.Allocator {
        \\                return self.child;
        \\            }
        \\        };
        \\    };
        \\};
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: library.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn buildPair(comptime std: type, gpa: library.mem.Allocator) !Pair {
        \\    var scope = std.heap.ArenaAllocator.init(gpa);
        \\    defer scope.deinit();
        \\    return duplicate(scope.allocator());
        \\}
    );
}

test "struct-literal-multiple-try: a local declaration shadowing the std namespace still fires" {
    // A local type namespace spelled `std` does not inherit the file's
    // standard-library import.
    try testing.expectFires(check, R,
        \\const library = @import("std");
        \\const Heap = struct {
        \\    pub const heap = struct {
        \\        pub const ArenaAllocator = struct {
        \\            buffer: [*]u8,
        \\            end: usize,
        \\            child: library.mem.Allocator,
        \\            pub fn init(gpa: library.mem.Allocator) @This() {
        \\                return .{ .buffer = undefined, .end = 0, .child = gpa };
        \\            }
        \\            pub fn deinit(self: *@This()) void {
        \\                self.end = 0;
        \\            }
        \\            pub fn allocator(self: *@This()) library.mem.Allocator {
        \\                return self.child;
        \\            }
        \\        };
        \\    };
        \\};
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: library.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\pub fn buildPair(gpa: library.mem.Allocator) !Pair {
        \\    const std = Heap;
        \\    var scope = std.heap.ArenaAllocator.init(gpa);
        \\    defer scope.deinit();
        \\    return duplicate(scope.allocator());
        \\}
    );
}

test "skript residual: a type alias to an owning type still owns allocations" {
    // `BufferAlias` declares no fields; it is `Buffer`, whose `bytes` slice
    // still has to be released per field.
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const Buffer = struct { bytes: []u8 };
        \\const BufferAlias = Buffer;
        \\const Pair = struct { first: BufferAlias, second: BufferAlias };
        \\fn cloneBuffer(memory: std.mem.Allocator) !BufferAlias {
        \\    return .{ .bytes = try memory.dupe(u8, "buffer") };
        \\}
        \\pub fn run(memory: std.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try cloneBuffer(memory),
        \\        .second = try cloneBuffer(memory),
        \\    };
        \\}
    );
}

test "struct-literal-multiple-try: a container capturing a comptime namespace parameter still fires" {
    // The factory's returned container captures `std`, so the arena written
    // inside it is the project's. Reading the spelling as the standard
    // library's would suppress a leak that this arena does not prevent.
    try testing.expectFires(check, R,
        \\const library = @import("std");
        \\const Heap = struct {
        \\    pub const heap = struct {
        \\        pub const ArenaAllocator = struct {
        \\            buffer: [*]u8,
        \\            end: usize,
        \\            child: library.mem.Allocator,
        \\            pub fn init(gpa: library.mem.Allocator) @This() {
        \\                return .{ .buffer = undefined, .end = 0, .child = gpa };
        \\            }
        \\            pub fn deinit(self: *@This()) void {
        \\                self.end = 0;
        \\            }
        \\            pub fn allocator(self: *@This()) library.mem.Allocator {
        \\                return self.child;
        \\            }
        \\        };
        \\    };
        \\};
        \\const Pair = struct { first: []u8, second: []u8 };
        \\fn duplicate(memory: library.mem.Allocator) !Pair {
        \\    return .{
        \\        .first = try memory.dupe(u8, "first"),
        \\        .second = try memory.dupe(u8, "second"),
        \\    };
        \\}
        \\fn Factory(comptime std: type) type {
        \\    return struct {
        \\        pub fn buildPair(gpa: library.mem.Allocator) !Pair {
        \\            var scope = std.heap.ArenaAllocator.init(gpa);
        \\            defer scope.deinit();
        \\            return duplicate(scope.allocator());
        \\        }
        \\    };
        \\}
        \\const Namespace = Factory(Heap);
        \\comptime { _ = Namespace; }
    );
}

test "struct-literal-multiple-try: resolved arena field allocator alias is reclaimed" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Context = struct {
        \\    storage: std.heap.ArenaAllocator,
        \\    pub fn duplicate(self: *Context) !Pair {
        \\        const memory = self.storage.allocator();
        \\        return .{ .a = try memory.dupe(u8, "a"), .b = try memory.dupe(u8, "b") };
        \\    }
        \\};
    );
}

test "struct-literal-multiple-try: arena named general allocator still leaks" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(arena: std.mem.Allocator) !Pair {
        \\    return .{ .a = try arena.dupe(u8, "a"), .b = try arena.dupe(u8, "b") };
        \\}
    );
}

test "struct-literal-multiple-try: resolved arena parameter allocator is reclaimed" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator) !Pair {
        \\    return .{ .a = try storage.allocator().dupe(u8, "a"), .b = try storage.allocator().dupe(u8, "b") };
        \\}
    );
}

test "struct-literal-multiple-try: unrelated arena does not reclaim general allocations" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(gpa: std.mem.Allocator) !Pair {
        \\    var arena = std.heap.ArenaAllocator.init(gpa);
        \\    defer arena.deinit();
        \\    const unrelated = arena.allocator();
        \\    _ = unrelated;
        \\    return .{ .a = try gpa.dupe(u8, "a"), .b = try gpa.dupe(u8, "b") };
        \\}
    );
}

test "struct-literal-multiple-try: local resolved arena allocation is reclaimed" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(gpa: std.mem.Allocator) !void {
        \\    var storage = std.heap.ArenaAllocator.init(gpa);
        \\    defer storage.deinit();
        \\    const memory = storage.allocator();
        \\    const pair: Pair = .{ .a = try memory.dupe(u8, "a"), .b = try memory.dupe(u8, "b") };
        \\    _ = pair;
        \\}
    );
}

test "struct-literal-multiple-try: mixed allocator helper does not prove arena ownership" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn cloneBytes(memory: std.mem.Allocator, other: std.mem.Allocator) ![]u8 {
        \\    _ = memory;
        \\    return other.dupe(u8, "a");
        \\}
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator, gpa: std.mem.Allocator) !Pair {
        \\    return .{ .a = try cloneBytes(storage.allocator(), gpa), .b = try gpa.dupe(u8, "b") };
        \\}
    );
}

test "struct-literal-multiple-try: lazy resolved arena accessor preserves provenance" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const State = struct {
        \\    storage: ?std.heap.ArenaAllocator = null,
        \\    fn memory(self: *State, gpa: std.mem.Allocator) std.mem.Allocator {
        \\        if (self.storage == null) self.storage = .init(gpa);
        \\        return self.storage.?.allocator();
        \\    }
        \\    pub fn duplicate(self: *State, gpa: std.mem.Allocator) !Pair {
        \\        const memory = self.memory(gpa);
        \\        return .{ .a = try memory.dupe(u8, "a"), .b = try memory.dupe(u8, "b") };
        \\    }
        \\};
    );
}

test "struct-literal-multiple-try: resolved general accessor does not prove arena provenance" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const State = struct {
        \\    storage: std.mem.Allocator,
        \\    fn memory(self: *State) std.mem.Allocator { return self.storage; }
        \\    pub fn duplicate(self: *State) !Pair {
        \\        const memory = self.memory();
        \\        return .{ .a = try memory.dupe(u8, "a"), .b = try memory.dupe(u8, "b") };
        \\    }
        \\};
    );
}

test "struct-literal-multiple-try: ignored arena argument does not reclaim hidden general allocation" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn cloneBytes(memory: std.mem.Allocator) ![]u8 {
        \\    _ = memory;
        \\    return std.heap.page_allocator.dupe(u8, "a");
        \\}
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator) !Pair {
        \\    const memory = storage.allocator();
        \\    return .{ .a = try cloneBytes(memory), .b = try memory.dupe(u8, "b") };
        \\}
    );
}

test "struct-literal-multiple-try: explicit borrowed arena fields retain partial allocations" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { first: []u8, second: []u8 };
        \\const Query = struct {
        \\    scratch: *std.heap.ArenaAllocator,
        \\    fn collect(self: *Query) !Pair {
        \\        return .{
        \\            .first = try self.scratch.allocator().dupe(u8, "first"),
        \\            .second = try self.scratch.allocator().dupe(u8, "second"),
        \\        };
        \\    }
        \\};
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { first: []u8, second: []u8 };
        \\const Query = struct {
        \\    scratch: std.mem.Allocator,
        \\    fn collect(self: *Query) !Pair {
        \\        return .{
        \\            .first = try self.scratch.dupe(u8, "first"),
        \\            .second = try self.scratch.dupe(u8, "second"),
        \\        };
        \\    }
        \\};
    );
}

test "struct-literal-multiple-try: SDK map clones use the supplied arena" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Map = std.array_hash_map.Auto(u32, u32);
        \\const Pair = struct { a: Map, b: Map };
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator, source: Map) !Pair {
        \\    return .{ .a = try source.clone(storage.allocator()), .b = try source.clone(storage.allocator()) };
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Map = std.array_hash_map.Auto(u32, u32);
        \\const Pair = struct { a: Map, b: Map };
        \\pub fn duplicate(memory: std.mem.Allocator, source: Map) !Pair {
        \\    return .{ .a = try source.clone(memory), .b = try source.clone(memory) };
        \\}
    );
}

test "struct-literal-multiple-try: arena helper bodies preserve nested recursive arena allocations" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Value = struct {
        \\    bytes: []u8,
        \\    fn typeOf(self: Value, context: *Context, depth: usize) !Value {
        \\        if (depth != 0) return self.typeOf(context, depth - 1);
        \\        return .{ .bytes = try context.storage.allocator().dupe(u8, self.bytes) };
        \\    }
        \\};
        \\const Pair = struct { a: *Value, b: *Value };
        \\const Context = struct {
        \\    storage: *std.heap.ArenaAllocator,
        \\    fn allocType(self: *Context, value: Value) !*Value {
        \\        const pointer = try self.storage.allocator().create(Value);
        \\        pointer.* = value;
        \\        return pointer;
        \\    }
        \\    pub fn duplicate(self: *Context, value: Value) !Pair {
        \\        return .{ .a = try self.allocType(try value.typeOf(self, 1)), .b = try self.allocType(try value.typeOf(self, 1)) };
        \\    }
        \\};
    );
}

test "struct-literal-multiple-try: same named helper allocating generally still leaks" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: *u8, b: *u8 };
        \\const Context = struct {
        \\    storage: *std.heap.ArenaAllocator,
        \\    memory: std.mem.Allocator,
        \\    fn allocType(self: *Context, value: u8) !*u8 {
        \\        const pointer = try self.memory.create(u8);
        \\        pointer.* = value;
        \\        return pointer;
        \\    }
        \\    pub fn duplicate(self: *Context) !Pair {
        \\        return .{ .a = try self.allocType(1), .b = try self.allocType(2) };
        \\    }
        \\};
    );
}

test "struct-literal-multiple-try: nested general allocation defeats arena helper ownership" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Value = struct { bytes: []u8 };
        \\const Pair = struct { a: *Value, b: *Value };
        \\const Context = struct {
        \\    storage: *std.heap.ArenaAllocator,
        \\    fn allocType(self: *Context, value: []u8) !*Value {
        \\        const pointer = try self.storage.allocator().create(Value);
        \\        pointer.* = .{ .bytes = value };
        \\        return pointer;
        \\    }
        \\    pub fn duplicate(self: *Context, memory: std.mem.Allocator) !Pair {
        \\        return .{ .a = try self.allocType(try memory.dupe(u8, "a")), .b = try self.allocType(try memory.dupe(u8, "b")) };
        \\    }
        \\};
    );
}

test "struct-literal-multiple-try: opaque helper result does not prove arena ownership" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: *u8, b: *u8 };
        \\extern fn allocType(storage: *std.heap.ArenaAllocator) *u8;
        \\fn cloneType(storage: *std.heap.ArenaAllocator) !*u8 { return allocType(storage); }
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator) !Pair {
        \\    return .{ .a = try cloneType(storage), .b = try cloneType(storage) };
        \\}
    );
}

test "struct-literal-multiple-try: SDK cloneContext binds its allocator formal" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Context = struct {
        \\    salt: u32,
        \\    pub fn hash(self: Context, key: u32) u32 { return key ^ self.salt; }
        \\    pub fn eql(self: Context, a: u32, b: u32, index: usize) bool { _ = self; _ = index; return a == b; }
        \\};
        \\const Map = std.array_hash_map.Custom(u32, u32, Context, true);
        \\const Pair = struct { a: Map, b: Map };
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator, source: Map, context: Context) !Pair {
        \\    return .{ .a = try source.cloneContext(storage.allocator(), context), .b = try source.cloneContext(storage.allocator(), context) };
        \\}
    );
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Map = std.array_hash_map.Auto(u32, u32);
        \\const Pair = struct { a: Map, b: Map };
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator, source: Map, memory: std.mem.Allocator) !Pair {
        \\    _ = storage;
        \\    return .{ .a = try Map.clone(source, memory), .b = try Map.clone(source, memory) };
        \\}
    );
}

test "struct-literal-multiple-try: project clone identity does not grant SDK ownership" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Buffer = struct {
        \\    bytes: []u8,
        \\    fn clone(self: Buffer, ignored: std.mem.Allocator) !Buffer {
        \\        _ = ignored;
        \\        return .{ .bytes = try std.heap.page_allocator.dupe(u8, self.bytes) };
        \\    }
        \\};
        \\const Pair = struct { a: Buffer, b: Buffer };
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator, source: Buffer) !Pair {
        \\    return .{ .a = try source.clone(storage.allocator()), .b = try source.clone(storage.allocator()) };
        \\}
    );
}

test "struct-literal-multiple-try: recursive helper cannot hide a general allocation edge" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Value = struct { bytes: []u8 };
        \\const Pair = struct { a: *Value, b: *Value };
        \\const Context = struct {
        \\    storage: *std.heap.ArenaAllocator,
        \\    memory: std.mem.Allocator,
        \\    fn cloneValue(self: *Context, depth: usize) !Value {
        \\        if (depth != 0) return self.cloneValue(depth - 1);
        \\        return .{ .bytes = try self.memory.dupe(u8, "value") };
        \\    }
        \\    fn allocType(self: *Context, value: Value) !*Value {
        \\        const pointer = try self.storage.allocator().create(Value);
        \\        pointer.* = value;
        \\        return pointer;
        \\    }
        \\    pub fn duplicate(self: *Context) !Pair {
        \\        return .{ .a = try self.allocType(try self.cloneValue(1)), .b = try self.allocType(try self.cloneValue(1)) };
        \\    }
        \\};
    );
}

test "struct-literal-multiple-try: scalar out-param helper can acquire general storage" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn fill(memory: std.mem.Allocator, out: *[]u8) !void {
        \\    out.* = try memory.dupe(u8, "value");
        \\}
        \\fn cloneBytes(memory: std.mem.Allocator) ![]u8 {
        \\    var out: []u8 = undefined;
        \\    try fill(memory, &out);
        \\    return out;
        \\}
        \\pub fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{ .a = try cloneBytes(memory), .b = try cloneBytes(memory) };
        \\}
    );
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn fill(storage: *std.heap.ArenaAllocator, out: *[]u8) !void {
        \\    out.* = try storage.allocator().dupe(u8, "value");
        \\}
        \\fn cloneBytes(storage: *std.heap.ArenaAllocator) ![]u8 {
        \\    var out: []u8 = undefined;
        \\    try fill(storage, &out);
        \\    return out;
        \\}
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator) !Pair {
        \\    return .{ .a = try cloneBytes(storage), .b = try cloneBytes(storage) };
        \\}
    );
}

fn arenaForwardingSource(gpa: std.mem.Allocator, helpers: usize) !std.ArrayListUnmanaged(u8) {
    var source: std.ArrayListUnmanaged(u8) = .empty;
    errdefer source.deinit(gpa);
    try source.appendSlice(gpa, "const std = @import(\"std\");\nconst Pair = struct { a: []u8, b: []u8 };\n");
    for (0..helpers) |i| {
        try source.print(gpa, "fn clone{d}(storage: *std.heap.ArenaAllocator) ![]u8 {{ ", .{i});
        if (i + 1 == helpers) {
            try source.appendSlice(gpa, "return storage.allocator().dupe(u8, \"value\"); }\n");
        } else {
            try source.print(gpa, "return clone{d}(storage); }}\n", .{i + 1});
        }
    }
    try source.appendSlice(gpa,
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator) !Pair {
        \\    return .{ .a = try clone0(storage), .b = try clone0(storage) };
        \\}
        \\
    );
    return source;
}

test "struct-literal-multiple-try: bounded arena helper graph still proves ownership" {
    const gpa = std.testing.allocator;
    var source = try arenaForwardingSource(gpa, 4);
    defer source.deinit(gpa);
    try testing.expectNoFireTyped(check, source.items);
}

test "struct-literal-multiple-try: exhausted helper graph is incomplete not a finding" {
    const gpa = std.testing.allocator;
    var source = try arenaForwardingSource(gpa, 20);
    defer source.deinit(gpa);
    budget_mod.clear();
    defer budget_mod.clear();
    try std.testing.expectError(error.AnalysisBudgetExceeded, testing.runRuleTyped(gpa, check, source.items));
    const diagnostic = budget_mod.take() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(budget_mod.Limit.arena_proof_depth, diagnostic.limit);
    try std.testing.expectEqual(@as(u32, 16), diagnostic.limit_value);
}

test "struct-literal-multiple-try: ownership ignores an unrelated exhausted cleanup allowance" {
    const gpa = std.testing.allocator;
    const Runner = struct {
        fn run(
            allocator: std.mem.Allocator,
            tree: *const Ast,
            cache: *file_cache_mod.FileCache,
            config: *const config_mod.Config,
            problems: *std.ArrayListUnmanaged(Problem),
        ) !void {
            const node = tree.rootDecls()[2];
            cache.beginNormalCleanup();
            defer cache.endNormalCleanup();
            try cache.enterNormalCleanup(node);
            defer cache.leaveNormalCleanup();
            try cache.normalCleanupStorageWork(node, 50_000);
            try check(allocator, tree, cache, config, problems);
        }
    };
    const safe =
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn cloneBytes(storage: *std.heap.ArenaAllocator) ![]u8 {
        \\    return storage.allocator().dupe(u8, "value");
        \\}
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator) !Pair {
        \\    return .{ .a = try cloneBytes(storage), .b = try cloneBytes(storage) };
        \\}
    ;
    try testing.expectNoFireTyped(Runner.run, safe);
    const general_type = try std.mem.replaceOwned(u8, gpa, safe, "*std.heap.ArenaAllocator", "std.mem.Allocator");
    defer gpa.free(general_type);
    const unsafe_source = try std.mem.replaceOwned(u8, gpa, general_type, "storage.allocator()", "storage");
    defer gpa.free(unsafe_source);
    try testing.expectFiresTyped(Runner.run, R, unsafe_source);
}

test "struct-literal-multiple-try: atomic lock operations preserve arena ownership" {
    const safe =
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Lock = struct {
        \\    state: usize = 0,
        \\    fn touch(self: *Lock) usize {
        \\        @atomicStore(usize, &self.state, 1, .seq_cst);
        \\        _ = @atomicRmw(usize, &self.state, .Add, 1, .seq_cst);
        \\        _ = @cmpxchgWeak(usize, &self.state, 2, 3, .seq_cst, .seq_cst);
        \\        _ = @cmpxchgStrong(usize, &self.state, 3, 4, .seq_cst, .seq_cst);
        \\        return @atomicLoad(usize, &self.state, .seq_cst);
        \\    }
        \\};
        \\fn cloneBytes(storage: *std.heap.ArenaAllocator, lock: *Lock) ![]u8 {
        \\    _ = lock.touch();
        \\    const bytes = try storage.allocator().dupe(u8, "abcdefgh");
        \\    @memset(bytes, 0);
        \\    @memcpy(bytes, "abcdefgh");
        \\    @memmove(bytes[0..4], bytes[4..8]);
        \\    return bytes;
        \\}
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator, lock: *Lock) !Pair {
        \\    return .{ .a = try cloneBytes(storage, lock), .b = try cloneBytes(storage, lock) };
        \\}
    ;
    try testing.expectNoFireTyped(check, safe);
    const gpa = std.testing.allocator;
    const general_type = try std.mem.replaceOwned(u8, gpa, safe, "*std.heap.ArenaAllocator", "std.mem.Allocator");
    defer gpa.free(general_type);
    const unsafe_source = try std.mem.replaceOwned(u8, gpa, general_type, "storage.allocator()", "storage");
    defer gpa.free(unsafe_source);
    try testing.expectFiresTyped(check, R, unsafe_source);
}


test "struct-literal-multiple-try: zero-length SDK allocations own no field storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(gpa: std.mem.Allocator) !Pair {
        \\    return .{ .a = try gpa.alloc(u8, 0), .b = try gpa.alloc(u8, 16) };
        \\}
    );
}

test "struct-literal-multiple-try: zero-length SDK second field cannot propagate error" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(gpa: std.mem.Allocator) !Pair {
        \\    return .{ .a = try gpa.alloc(u8, 16), .b = try gpa.alloc(u8, 0) };
        \\}
    );
}

test "struct-literal-multiple-try: zero-length intervening field retains later error leak" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Triple = struct { a: []u8, b: []u8, c: []u8 };
        \\pub fn duplicate(gpa: std.mem.Allocator) !Triple {
        \\    return .{ .a = try gpa.alloc(u8, 16), .b = try gpa.alloc(u8, 0), .c = try gpa.alloc(u8, 16) };
        \\}
    );
}

test "struct-literal-multiple-try: nested fallible operand defeats zero-length error proof" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn memory(gpa: std.mem.Allocator, fail: bool) !std.mem.Allocator {
        \\    if (fail) return error.Bad;
        \\    return gpa;
        \\}
        \\pub fn duplicate(gpa: std.mem.Allocator, fail: bool) !Pair {
        \\    return .{ .a = try gpa.alloc(u8, 16), .b = try (try memory(gpa, fail)).alloc(u8, 0) };
        \\}
    );
}

test "struct-literal-multiple-try: project zero-count allocator can fail" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Memory = struct {
        \\    gpa: std.mem.Allocator,
        \\    fn alloc(self: *Memory, comptime T: type, n: usize) ![]T {
        \\        if (n == 0) return error.Bad;
        \\        return self.gpa.alloc(T, n);
        \\    }
        \\};
        \\pub fn duplicate(memory: *Memory) !Pair {
        \\    return .{ .a = try memory.alloc(u8, 16), .b = try memory.alloc(u8, 0) };
        \\}
    );
}

test "struct-literal-multiple-try: fixed-buffer allocator retains partial initializer storage" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(storage: *std.heap.FixedBufferAllocator) !Pair {
        \\    const memory = storage.allocator();
        \\    return .{ .a = try memory.dupe(u8, "one"), .b = try memory.dupe(u8, "two") };
        \\}
    );
}

test "struct-literal-multiple-try: helper binds its arena allocator operand" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn cloneBytes(memory: std.mem.Allocator) ![]u8 {
        \\    return memory.dupe(u8, "value");
        \\}
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator) !Pair {
        \\    return .{ .a = try cloneBytes(storage.allocator()), .b = try cloneBytes(storage.allocator()) };
        \\}
    );
}

test "struct-literal-multiple-try: helper binds the owning allocator not alternate arena" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn cloneBytes(memory: std.mem.Allocator, alternate: std.mem.Allocator) ![]u8 {
        \\    _ = alternate;
        \\    return memory.dupe(u8, "value");
        \\}
        \\pub fn duplicate(gpa: std.mem.Allocator, storage: *std.heap.ArenaAllocator) !Pair {
        \\    return .{ .a = try cloneBytes(gpa, storage.allocator()), .b = try cloneBytes(gpa, storage.allocator()) };
        \\}
    );
}

test "struct-literal-multiple-try: escaped allocator helper remains caller-dependent" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn clonePair(memory: std.mem.Allocator) !Pair {
        \\    return .{ .a = try memory.dupe(u8, "one"), .b = try memory.dupe(u8, "two") };
        \\}
        \\pub const callback = clonePair;
        \\pub fn duplicate(storage: *std.heap.ArenaAllocator) !Pair {
        \\    return clonePair(storage.allocator());
        \\}
    );
}

test "struct-literal-multiple-try: fallible zero-storage helper has no first field to leak" {
    try expectImportedRuleCount(
        \\const std = @import("std");
        \\pub const Memory = struct {
        \\    allocator: std.mem.Allocator,
        \\    cancelled: bool,
        \\    pub fn alloc(self: *Memory, comptime T: type, count: usize) ![]T {
        \\        if (self.cancelled) return error.Cancelled;
        \\        const items = self.allocator.alloc(T, count) catch return error.OutOfMemory;
        \\        return items;
        \\    }
        \\};
    ,
        \\const std = @import("std");
        \\const Memory = @import("ranges.zig").Memory;
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(memory: *Memory) !Pair {
        \\    return .{ .a = try memory.alloc(u8, 0), .b = try memory.alloc(u8, 16) };
        \\}
    , 0);

    // Seven nested bodies grow the binding map while the outer scanner is
    // suspended. Its later assignment must still read the original bindings.
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn zero6(memory: std.mem.Allocator) ![]u8 { return memory.alloc(u8, 0); }
        \\fn zero5(memory: std.mem.Allocator) ![]u8 { return zero6(memory); }
        \\fn zero4(memory: std.mem.Allocator) ![]u8 { return zero5(memory); }
        \\fn zero3(memory: std.mem.Allocator) ![]u8 { return zero4(memory); }
        \\fn zero2(memory: std.mem.Allocator) ![]u8 { return zero3(memory); }
        \\fn zero1(memory: std.mem.Allocator) ![]u8 { return zero2(memory); }
        \\fn zero0(memory: std.mem.Allocator, choose: bool) ![]u8 {
        \\    if (choose) return zero1(memory);
        \\    var scratch: usize = 0;
        \\    scratch = 1;
        \\    _ = scratch;
        \\    return memory.alloc(u8, 0);
        \\}
        \\pub fn duplicate(memory: std.mem.Allocator, choose: bool) !Pair {
        \\    return .{ .a = try zero0(memory, choose), .b = try memory.alloc(u8, 16) };
        \\}
    );
}

test "struct-literal-multiple-try: nonzero helper result still owns storage" {
    try expectImportedRuleCount(
        \\const std = @import("std");
        \\pub const Memory = struct {
        \\    allocator: std.mem.Allocator,
        \\    cancelled: bool,
        \\    pub fn alloc(self: *Memory, comptime T: type, count: usize) ![]T {
        \\        if (self.cancelled) return error.Cancelled;
        \\        const items = self.allocator.alloc(T, count) catch return error.OutOfMemory;
        \\        return items;
        \\    }
        \\};
    ,
        \\const std = @import("std");
        \\const Memory = @import("ranges.zig").Memory;
        \\const Pair = struct { a: []u8, b: []u8 };
        \\pub fn duplicate(memory: *Memory) !Pair {
        \\    return .{ .a = try memory.alloc(u8, 16), .b = try memory.alloc(u8, 0) };
        \\}
    , 1);
}

test "struct-literal-multiple-try: zero-count helper with owning alternate return still fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn alloc(memory: std.mem.Allocator, count: usize, alternate: bool) ![]u8 {
        \\    if (alternate) return memory.alloc(u8, 16);
        \\    return memory.alloc(u8, count);
        \\}
        \\pub fn duplicate(memory: std.mem.Allocator, alternate: bool) !Pair {
        \\    return .{ .a = try alloc(memory, 0, alternate), .b = try alloc(memory, 16, alternate) };
        \\}
    );
}

test "struct-literal-multiple-try: zero-count catch fallback can return owned storage" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn alloc(memory: std.mem.Allocator, count: usize) ![]u8 {
        \\    return memory.alloc(u8, count) catch memory.alloc(u8, 16);
        \\}
        \\pub fn duplicate(memory: std.mem.Allocator) !Pair {
        \\    return .{ .a = try alloc(memory, 0), .b = try alloc(memory, 16) };
        \\}
    );
}

test "struct-literal-multiple-try: unescaped local allocator field retains fixed-buffer identity" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Engine = struct { allocator: std.mem.Allocator };
        \\pub fn duplicate() !Pair {
        \\    var bytes: [128]u8 = undefined;
        \\    var pool = std.heap.FixedBufferAllocator.init(&bytes);
        \\    var engine: Engine = .{ .allocator = pool.allocator() };
        \\    return .{ .a = try engine.allocator.dupe(u8, "one"), .b = try engine.allocator.dupe(u8, "two") };
        \\}
    );
}

test "struct-literal-multiple-try: overwritten local allocator field still fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Engine = struct { allocator: std.mem.Allocator };
        \\pub fn duplicate(gpa: std.mem.Allocator) !Pair {
        \\    var bytes: [128]u8 = undefined;
        \\    var pool = std.heap.FixedBufferAllocator.init(&bytes);
        \\    var engine: Engine = .{ .allocator = pool.allocator() };
        \\    engine.allocator = gpa;
        \\    return .{ .a = try engine.allocator.dupe(u8, "one"), .b = try engine.allocator.dupe(u8, "two") };
        \\}
    );
}

test "struct-literal-multiple-try: escaped local allocator field remains caller-dependent" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Engine = struct { allocator: std.mem.Allocator };
        \\pub fn duplicate(change: *const fn (*Engine) void) !Pair {
        \\    var bytes: [128]u8 = undefined;
        \\    var pool = std.heap.FixedBufferAllocator.init(&bytes);
        \\    var engine: Engine = .{ .allocator = pool.allocator() };
        \\    change(&engine);
        \\    return .{ .a = try engine.allocator.dupe(u8, "one"), .b = try engine.allocator.dupe(u8, "two") };
        \\}
    );
}

test "struct-literal-multiple-try: loop-carried allocator field replacement still fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Engine = struct { allocator: std.mem.Allocator };
        \\pub fn duplicate(gpa: std.mem.Allocator, out: []Pair) !void {
        \\    var bytes: [128]u8 = undefined;
        \\    var pool = std.heap.FixedBufferAllocator.init(&bytes);
        \\    var engine: Engine = .{ .allocator = pool.allocator() };
        \\    for (out) |*pair| {
        \\        pair.* = .{ .a = try engine.allocator.dupe(u8, "one"), .b = try engine.allocator.dupe(u8, "two") };
        \\        engine.allocator = gpa;
        \\    }
        \\}
    );
}

test "struct-literal-multiple-try: local allocator provider header must remain live" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Engine = struct { allocator: std.mem.Allocator };
        \\pub fn duplicate() !Pair {
        \\    var bytes: [128]u8 = undefined;
        \\    var pool = std.heap.FixedBufferAllocator.init(&bytes);
        \\    var engine: Engine = .{ .allocator = pool.allocator() };
        \\    pool = undefined;
        \\    return .{ .a = try engine.allocator.dupe(u8, "one"), .b = try engine.allocator.dupe(u8, "two") };
        \\}
    );
}

test "struct-literal-multiple-try: escaped local provider cannot lend an old header proof" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Engine = struct { allocator: std.mem.Allocator };
        \\pub fn duplicate(change: *const fn (*std.heap.FixedBufferAllocator) void) !Pair {
        \\    var bytes: [128]u8 = undefined;
        \\    var pool = std.heap.FixedBufferAllocator.init(&bytes);
        \\    var engine: Engine = .{ .allocator = pool.allocator() };
        \\    change(&pool);
        \\    return .{ .a = try engine.allocator.dupe(u8, "one"), .b = try engine.allocator.dupe(u8, "two") };
        \\}
    );
}

test "struct-literal-multiple-try: branch-conditional local field replacement still fires" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Engine = struct { allocator: std.mem.Allocator };
        \\pub fn duplicate(gpa: std.mem.Allocator, replace: bool) !Pair {
        \\    var bytes: [128]u8 = undefined;
        \\    var pool = std.heap.FixedBufferAllocator.init(&bytes);
        \\    var engine: Engine = .{ .allocator = pool.allocator() };
        \\    if (replace) engine.allocator = gpa;
        \\    return .{ .a = try engine.allocator.dupe(u8, "one"), .b = try engine.allocator.dupe(u8, "two") };
        \\}
    );
}

test "struct-literal-multiple-try: escaped zero result header can become owning" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\fn alloc(memory: std.mem.Allocator, count: usize, change: *const fn (*[]u8) void) ![]u8 {
        \\    const items = try memory.alloc(u8, count);
        \\    change(@constCast(&items));
        \\    return items;
        \\}
        \\pub fn duplicate(memory: std.mem.Allocator, change: *const fn (*[]u8) void) !Pair {
        \\    return .{ .a = try alloc(memory, 0, change), .b = try alloc(memory, 16, change) };
        \\}
    );
}

test "struct-literal-multiple-try: local fixed-buffer header stays valid through an initializer loop" {
    try testing.expectNoFireTyped(check,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Engine = struct { allocator: std.mem.Allocator };
        \\fn tick(index: usize) !void {
        \\    if (index == std.math.maxInt(usize)) return error.Bad;
        \\}
        \\pub fn duplicate(storage: []u8, out: []Pair) !void {
        \\    var pool = std.heap.FixedBufferAllocator.init(storage);
        \\    var engine: Engine = .{ .allocator = pool.allocator() };
        \\    for (out, 0..) |*pair, index| {
        \\        try tick(index);
        \\        pair.* = .{ .a = try engine.allocator.dupe(u8, "one"), .b = try engine.allocator.dupe(u8, "two") };
        \\    }
        \\}
    );
}

test "struct-literal-multiple-try: copied allocator header can expose its mutable provider" {
    try testing.expectFiresTyped(check, R,
        \\const std = @import("std");
        \\const Pair = struct { a: []u8, b: []u8 };
        \\const Engine = struct { allocator: std.mem.Allocator };
        \\pub fn duplicate(change: *const fn (std.mem.Allocator) void) !Pair {
        \\    var bytes: [128]u8 = undefined;
        \\    var pool = std.heap.FixedBufferAllocator.init(&bytes);
        \\    var engine: Engine = .{ .allocator = pool.allocator() };
        \\    const leaked = engine.allocator;
        \\    change(leaked);
        \\    return .{ .a = try engine.allocator.dupe(u8, "one"), .b = try engine.allocator.dupe(u8, "two") };
        \\}
    );
}
