//! AST → CFG lowering — the `Builder` struct and the public
//! `lowerFunction*` entry points.  See cfg.zig for the CFG data types
//! produced.

const std = @import("std");
const Ast = std.zig.Ast;
const abstract_state = @import("abstract_state.zig");
const config_mod = @import("../config.zig");
const file_cache = @import("../cache/file_cache.zig");
const fn_summary = @import("../model/fn_summary.zig");
const tokens = @import("../ast/tokens.zig");
const receiver_mod = @import("../model/method_names.zig");
const model_mod = @import("../model/file_model.zig");
const zls_resolver_mod = @import("../type_resolver.zig");

// CFG types re-bound for local convenience.
const cfg_types = @import("cfg.zig");
const Config = cfg_types.Config;
const BlockId = cfg_types.BlockId;
const LocalId = cfg_types.LocalId;
const SrcPos = cfg_types.SrcPos;
const StmtKind = cfg_types.StmtKind;
const Stmt = cfg_types.Stmt;
const ExprKind = cfg_types.ExprKind;
const BasicBlock = cfg_types.BasicBlock;
const Cfg = cfg_types.Cfg;
const LocalInfo = cfg_types.LocalInfo;
const InitHint = cfg_types.InitHint;
const LoweringError = error{ OutOfMemory, AnalysisBudgetExceeded };

/// Known-stdlib noreturn callee chains.  Hoisted so both the
/// call-site detector (calleeIsNoreturn) and the alias detector
/// (initIsNoreturnAlias) share a single list.  Builtins like
/// `@panic` and `@trap` go through builtinIsDivergent, not here.
const known_noreturn_chains = [_][]const u8{
    "process.exit",
    "posix.exit",
    "os.abort",
    "process.abort",
    // Bun's process-exit wrapper.  Used after fatal-script teardown:
    //   this.deinit();
    //   Global.exit(exit.code);
    // — anything textually after this call is unreachable.  Without
    // the noreturn signal, the analyzer joins the post-deinit state
    // into the next basic block and fires heap-use-after-free on
    // sibling branches that read `this`.
    "Global.exit",
};

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

    // Pull the containing type via the FileCache's FileModel so
    // Self / @This() resolve inside param types and receiver-type
    // lookups have a starting scope.
    const self_type: ?[]const u8 = blk: {
        const c = cache orelse break :blk null;
        const model = c.fileModel() catch break :blk null;
        const ti = model.containingTypeOf(fn_decl) orelse break :blk null;
        break :blk ti.qualified_name;
    };

    // Use line offsets from FileCache when available (built once per file);
    // otherwise build fresh and transfer ownership to the builder.
    const cached_offsets: ?[]const u32 = if (cache) |c| c.getLineOffsets() catch null else null;
    const line_offsets = cached_offsets orelse try buildLineOffsets(gpa, tree.source);
    var builder: Builder = .{
        .gpa = gpa,
        .tree = tree,
        .cache = cache,
        .zls = zls,
        .config = config,
        .is_borrowed_return_type = is_borrowed_ret,
        .is_noreturn_fn = is_noreturn_fn,
        .suppress_composite_borrow = suppress_cb,
        .fn_proto = fn_proto,
        .fn_body_last = tree.lastToken(body_node),
        .fn_body_first = tree.firstToken(body_node),
        .self_type = self_type,
        .line_offsets = line_offsets,
        .owns_line_offsets = cached_offsets == null,
    };
    defer builder.tempDeinit();

    const entry_id = try builder.newBlock();
    var cur_block = entry_id;
    try builder.lowerFunctionBody(body_node, &cur_block);
    if (builder.budget_exhausted) return error.AnalysisBudgetExceeded;

    return try builder.finalize(tree, fn_decl, entry_id);
}

/// Build a sorted list of byte offsets where each line starts.
/// line_offsets[i] = byte offset of the first character on line i.
/// Used by posOfToken / endPosOf for O(log lines) position lookups.
pub fn buildLineOffsets(gpa: std.mem.Allocator, source: [:0]const u8) ![]u32 {
    var offsets: std.ArrayListUnmanaged(u32) = .empty;
    try offsets.append(gpa, 0);
    for (source, 0..) |c, i| {
        if (c == '\n') try offsets.append(gpa, @intCast(i + 1));
    }
    return offsets.toOwnedSlice(gpa);
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

/// True iff `path` (a dotted field chain like "value_ptr.field" or
/// just "ptr") starts with a segment whose name ends in `_ptr` (or
/// is exactly `ptr`).  Pointer-name convention — stdlib's
/// `GetOrPutResult.value_ptr: *V` / `.key_ptr: *K`, ArrayList's
/// `.ptr`, etc.  A field chain whose head is such a name guarantees
/// the borrow lifts out of any auto-deref, so `&local.<ptr_name>.X`
/// is a borrow into caller- or heap-owned storage rather than a
/// stack ref.
fn fieldPathHasPointerName(path: []const u8) bool {
    // Take the first dotted segment.
    var end: usize = 0;
    while (end < path.len and path[end] != '.') : (end += 1) {}
    const seg = path[0..end];
    if (std.mem.eql(u8, seg, "ptr")) return true;
    if (std.mem.endsWith(u8, seg, "_ptr")) return true;
    return false;
}

/// True iff the body tokens `[name_tok+1 .. last]` contain `<name>.*`
/// somewhere — i.e. the local declared at `name_tok` is dereferenced
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

/// True iff `init_node` is a call expression whose final method
/// name is one of the conventional pointer-yielding cast/accessor
/// names — `as`, `cast`, `ptrCast`, `getPtr`, `getParent`,
/// `parent`.  Used by `lowerVarDecl` to infer `is_pointer` from
/// the init shape so `var x = recv.as(Ty); return &x.field;`
/// doesn't fire stack-escape (the underlying pointee lives in
/// caller / heap storage, not this frame).
fn initCallNameIsPointerReturning(tree: *const Ast, init_node: Ast.Node.Index) bool {
    const tag = tree.nodeTag(init_node);
    const is_call = switch (tag) {
        .call,
        .call_comma,
        .call_one,
        .call_one_comma,
        => true,
        else => false,
    };
    if (!is_call) return false;
    // The call's callee is at the node's main_token-1 or so; the
    // method name is the LAST identifier before the `(`.  Walk the
    // call's source tokens from firstToken to lastToken, find the
    // first `(`, and grab the preceding identifier.
    const tags = tree.tokens.items(.tag);
    const first = tree.firstToken(init_node);
    const last = tree.lastToken(init_node);
    var t: Ast.TokenIndex = first;
    var name_tok: ?Ast.TokenIndex = null;
    while (t <= last) : (t += 1) {
        switch (tags[t]) {
            .identifier => name_tok = t,
            .l_paren => break,
            else => {},
        }
    }
    const nt = name_tok orelse return false;
    const name = tree.tokenSlice(nt);
    return std.mem.eql(u8, name, "as") or
        std.mem.eql(u8, name, "cast") or
        std.mem.eql(u8, name, "ptrCast") or
        std.mem.eql(u8, name, "getPtr") or
        std.mem.eql(u8, name, "getParent") or
        std.mem.eql(u8, name, "parent");
}

/// True iff `init_node` is a method call on a known pointer local.
/// Catches factory/builder patterns like `b.addUpdateSourceFiles()` where
/// the receiver `b` is a `*std.Build` parameter — the call returns a
/// `*Step.T` but ZLS can't resolve it cross-file.  Suppresses FPs like
/// `return &usf.step` where `usf` is actually a pointer.
fn initCallReceiverIsPointerLocal(builder: *const Builder, tree: *const Ast, init_node: Ast.Node.Index) bool {
    const tag = tree.nodeTag(init_node);
    switch (tag) {
        .call, .call_comma, .call_one, .call_one_comma => {},
        else => return false,
    }
    var buf: [1]Ast.Node.Index = undefined;
    const call_full = tree.fullCall(&buf, init_node) orelse return false;
    const callee = call_full.ast.fn_expr;
    if (tree.nodeTag(callee) != .field_access) return false;
    const recv = tree.nodeData(callee).node_and_token[0];
    if (tree.nodeTag(recv) != .identifier) return false;
    const recv_name = tree.tokenSlice(tree.nodeMainToken(recv));
    const lid = builder.name_to_local.get(recv_name) orelse return false;
    return builder.locals.items[@intFromEnum(lid)].is_pointer;
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

/// Labeled non-loop blocks — `blk: { ... break :blk val; }`.  Only
/// labeled break can target these; continue is invalid (compiler
/// catches at parse time, but defensively ignored here).
const BlockLabelCtx = struct {
    label: []const u8,
    merge: BlockId,
    defer_depth: usize,
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
    classify_depth: u8 = 0,
    budget_exhausted: bool = false,
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
    /// name → LocalId for current scope.  v1 doesn't handle nested scopes;
    /// names are flat per-function.
    name_to_local: std.StringHashMapUnmanaged(LocalId) = .empty,
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
    /// Pre-built table of byte offsets where each line starts (line_offsets[i]
    /// = byte offset of the first char on line i).  Built once per file in
    /// lowerFunctionFullWithZls; makes posOfToken / endPosOf O(log lines)
    /// instead of O(source_len).
    line_offsets: []const u32 = &.{},
    /// True when Builder owns line_offsets and must free it.  False when
    /// the slice is borrowed from FileCache (which owns and frees it).
    owns_line_offsets: bool = false,

    const BorrowIterator = struct {
        const Iterator = @import("type_engine").AstIterator;
        builder: *Builder,
        frames: [64]Iterator = undefined,
        depth: usize = 1,
        visited: usize = 0,

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
                if (self.visited == tree.nodes.len) return self.exhausted();
                self.visited += 1;
                if (self.children(node)) |child_nodes| {
                    if (self.depth == self.frames.len) return self.exhausted();
                    self.frames[self.depth] = child_nodes;
                    self.depth += 1;
                    continue;
                }
                switch (tree.nodeTag(node)) {
                    .address_of, .slice, .slice_open, .slice_sentinel => {
                        const kind = builder.classifyExpr(node);
                        if (kind == .stack_ref or kind == .copy_of) return kind;
                    },
                    .identifier => {
                        const local = builder.name_to_local.get(tree.tokenSlice(tree.nodeMainToken(node))) orelse continue;
                        if (builder.locals.items[@intFromEnum(local)].init_hint != .other) continue;
                        return .{ .copy_of = local };
                    },
                    else => {},
                }
            }
            return null;
        }

        fn exhausted(self: *BorrowIterator) ?ExprKind {
            self.builder.budget_exhausted = true;
            self.depth = 0;
            return null;
        }

        fn children(self: *BorrowIterator, node: Ast.Node.Index) ?Iterator {
            const builder = self.builder;
            const tree = builder.tree;
            return switch (tree.nodeTag(node)) {
                .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma,
                .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma,
                .array_init, .array_init_comma, .array_init_one, .array_init_one_comma,
                .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma,
                .array_mult, .@"catch", .@"orelse", => Iterator.init(tree, node),
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
                .switch_case, .switch_case_one, .switch_case_inline, .switch_case_inline_one =>
                    one(tree.fullSwitchCase(node).?.ast.target_expr),
                .builtin_call, .builtin_call_two, .builtin_call_comma, .builtin_call_two_comma =>
                    one(builder.transparentCastSource(node) orelse return null),
                .block, .block_two, .block_semicolon, .block_two_semicolon => blk: {
                    const label = builder.blockLabelToken(node) orelse return null;
                    break :blk one(builder.singleLabeledBreakValue(node, label) orelse return null);
                },
                else => null,
            };
        }
    };

    const BorrowKey = struct {
        local: LocalId,
        address: bool,

        fn from(kind: ExprKind) BorrowKey {
            return switch (kind) {
                .stack_ref => |local| .{ .local = local, .address = true },
                .copy_of, .composite_borrow => |local| .{ .local = local, .address = false },
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
        self.locals.deinit(self.gpa);
        self.name_to_local.deinit(self.gpa);
        self.deferred.deinit(self.gpa);
        self.loop_stack.deinit(self.gpa);
        self.block_label_stack.deinit(self.gpa);
        for (self.owned_paths.items) |p| self.gpa.free(p);
        self.owned_paths.deinit(self.gpa);
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
        for (0..64) |_| {
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
        self.budget_exhausted = true;
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
        const value = condition orelse return;
        try self.appendStmt(block, .{
            .kind = .{ .assume = if (expected) value else value.negate() },
            .pos = self.posOf(node), .end_pos = self.endPosOf(node),
        });
    }

    fn addEdge(self: *Builder, from: BlockId, to: BlockId) !void {
        try self.block_successors.items[@intFromEnum(from)].append(self.gpa, to);
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
        const id: LocalId = @enumFromInt(self.locals.items.len);
        try self.locals.append(self.gpa, .{
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
        const id: LocalId = @enumFromInt(self.locals.items.len);
        try self.locals.append(self.gpa, .{
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

    /// True iff `type_node`'s first two tokens are `[<number>` —
    /// the shape of `[N]T`.  Conservatively returns false for
    /// `[*]T` (many-pointer), `[]T` (slice), `[*c]T` (C pointer).
    fn typeIsStackArray(self: *Builder, type_node: Ast.Node.Index) bool {
        const tree = self.tree;
        const first = tree.firstToken(type_node);
        const tags = tree.tokens.items(.tag);
        if (tags[first] != .l_bracket) return false;
        if (first + 1 >= tree.tokens.len) return false;
        return tags[first + 1] == .number_literal;
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
                const model = cache.fileModel() catch return null;
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
    /// If type resolution is unavailable, retain the narrow Bun convention
    /// fallback for known pointer-yielding calls.  A by-pointer field capture
    /// is also accepted when its receiver is already known to be non-local.
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
        // Inspect the scrutinee — peel `try`/`catch` wrappers.
        var node = cond_expr;
        while (true) {
            switch (tree.nodeTag(node)) {
                .@"try" => node = tree.nodeData(node).node,
                .@"catch" => node = tree.nodeData(node).node_and_node[0],
                else => break,
            }
        }

        // Prefer the type engine's instantiated generic result.  A call
        // such as `HashMapUnmanaged(*Entry).get(key)` returns `?*Entry`;
        // only that semantic payload proof may mark the capture as a
        // pointer.  If the resolver is unavailable, retain the existing
        // narrow Bun convention fallback.  An unresolved result must not
        // masquerade as a proven pointer type.
        if (self.zls) |zls| {
            if (zls.optionalPayloadIsPointer(node) catch null) |is_pointer| {
                if (is_pointer) {
                    self.locals.items[@intFromEnum(lid)].is_pointer = true;
                    return;
                }
            }
        } else if (self.callReturnsOptionalPointer(node)) {
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
    }

    /// True iff `expr_node` is a call whose method name is a
    /// known-returns-`?*T` convention (`fromJS`, `as`).  Used only
    /// when semantic type resolution is unavailable, to preserve the
    /// existing fallback for `if (X.fromJS(value)) |v|`.
    fn callReturnsOptionalPointer(self: *const Builder, expr_node: Ast.Node.Index) bool {
        const tree = self.tree;
        const tag = tree.nodeTag(expr_node);
        const is_call = switch (tag) {
            .call, .call_one, .call_comma, .call_one_comma => true,
            else => false,
        };
        if (!is_call) return false;
        // The first token of the call is the receiver chain; the
        // LAST token before the `(` is the method name.  Walk back
        // from the call's main token to find the method ident.
        const main_tok = tree.nodeMainToken(expr_node);
        // For a call like `X.Y.fromJS(args)`, main_tok is the `(`.
        // The token immediately before is the method ident.
        const tags = tree.tokens.items(.tag);
        if (main_tok == 0) return false;
        const m = main_tok - 1;
        if (tags[m] != .identifier) return false;
        const name = tree.tokenSlice(m);
        return std.mem.eql(u8, name, "fromJS") or
            std.mem.eql(u8, name, "as");
    }

    /// Variant that, when `reset_into` is non-null, emits a
    /// .reset_capture stmt for each registered capture into the
    /// given block.  Used by loop lowerers so each iteration starts
    /// with a fresh .plain origin for the capture (back-edge state
    /// would otherwise propagate across iterations — the capture
    /// refers to a different element each time).
    /// After lowering a for/while loop body whose captures were registered
    /// starting at `pre_len`, restore any `name_to_local` entries that were
    /// overwritten by the capture registration.  Capture variables are
    /// scoped to the loop body — they must NOT pollute the outer scope's
    /// name resolution.  Without this, a for-loop inside a `defer` body
    /// clobbers the binding of the same name in the enclosing scope: when
    /// `flushErrAndNormalDefers` replays defers in sequence, the first
    /// defer's for-loop capture overwrites `name_to_local`, and subsequent
    /// defer bodies resolve the same name to the wrong LocalId.  That
    /// causes double-free FPs: the inner defer's `free(item.path)` emits
    /// `field_heap_free {L_capture, "path"}` instead of `{L_item, "path"}`,
    /// so `transferDecl` for `const item = pop()` clears the wrong local's
    /// field state and the dead-field persists across loop iterations.
    fn restoreCaptureNames(self: *Builder, pre_len: u32) !void {
        var j = pre_len;
        while (j < self.locals.items.len) : (j += 1) {
            const name = self.locals.items[j].name;
            const current = self.name_to_local.get(name) orelse continue;
            if (@intFromEnum(current) < pre_len) continue; // not overwritten by this capture
            // Find the most-recent prior binding for this name.
            var prev: ?LocalId = null;
            var k: u32 = 0;
            while (k < pre_len) : (k += 1) {
                if (std.mem.eql(u8, self.locals.items[k].name, name)) {
                    prev = @enumFromInt(k);
                }
            }
            if (prev) |pl| {
                try self.name_to_local.put(self.gpa, name, pl);
            } else {
                _ = self.name_to_local.remove(name);
            }
        }
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

        for (stmts) |stmt_idx| {
            try self.lowerStmt(stmt_idx, cur);
        }

        try self.flushScopeDefers(cur, save);
        self.deferred.shrinkRetainingCapacity(save);
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
        try self.registerFnParams();
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

    fn registerFnParams(self: *Builder) !void {
        const tree = self.tree;
        const proto = self.fn_proto orelse return;
        var it = proto.iterate(tree);
        while (it.next()) |param| {
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
            _ = try self.registerLocalWithPointerHint(
                name,
                self.posOfToken(name_tok),
                false,
                .other,
                null,
                type_name,
                is_pointer,
            );
        }
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
            .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod,
            .assign_shl, .assign_shr, .assign_shl_sat,
            .assign_bit_and, .assign_bit_xor, .assign_bit_or,
            .assign_add_wrap, .assign_sub_wrap, .assign_mul_wrap,
            .assign_add_sat, .assign_sub_sat, .assign_mul_sat => {
                try self.emitUsesInExpr(stmt_node, cur.*, null);
                try self.emitWritesInLhs(tree.nodeData(stmt_node).node_and_node[0], cur.*);
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
            .@"switch", .switch_comma => try self.lowerSwitch(stmt_node, cur),
            .@"try" => try self.lowerTryStmt(stmt_node, cur),
            .@"catch" => try self.lowerCatchStmt(stmt_node, cur),
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
                    try self.lowerLabeledBlock(stmt_node, lt, cur);
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
        const branch = self.tree.fullIf(if_node).?;
        try self.emitUsesInExpr(branch.ast.cond_expr, cur.*, null);
        const condition = if (branch.payload_token == null) self.booleanValue(branch.ast.cond_expr) else null;
        const then_block = try self.newBlock();
        const else_block = try self.newBlock();
        const merge = try self.newBlock();
        try self.addEdge(cur.*, then_block);
        try self.addEdge(cur.*, else_block);
        try self.assumeCondition(then_block, branch.ast.cond_expr, condition, true);
        try self.assumeCondition(else_block, branch.ast.cond_expr, condition, false);
        const pre_capture_len: u32 = @intCast(self.locals.items.len);
        if (branch.payload_token) |token| {
            try self.registerCapturesWith(token, then_block);
            self.inferPointerCapture(token, branch.ast.cond_expr);
        }
        var then_cur = then_block;
        try self.lowerStmt(branch.ast.then_expr, &then_cur);
        try self.addEdge(then_cur, merge);
        try self.restoreCaptureNames(pre_capture_len);
        var else_cur = else_block;
        if (branch.ast.else_expr.unwrap()) |else_expr| {
            if (branch.error_token) |token| try self.registerErrorCapturesWith(token, else_block);
            try self.lowerStmt(else_expr, &else_cur);
            try self.restoreCaptureNames(pre_capture_len);
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
        const natural_exit = if (loop.ast.else_expr != .none or condition != null) try self.newBlock() else merge;
        const continuation = if (loop.ast.cont_expr != .none) try self.newBlock() else header;
        try self.addEdge(cur.*, header);
        try self.emitUsesInExpr(loop.ast.cond_expr, header, null);
        try self.addEdge(header, body);
        try self.addEdge(header, natural_exit);
        try self.assumeCondition(body, loop.ast.cond_expr, condition, true);
        try self.assumeCondition(natural_exit, loop.ast.cond_expr, condition, false);
        try self.loop_stack.append(self.gpa, .{
            .continue_to = continuation, .merge = merge, .defer_depth = self.deferred.items.len,
            .label = if (loop.label_token) |token| self.tree.tokenSlice(token) else null,
        });
        const pre_capture_len: u32 = @intCast(self.locals.items.len);
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
        try self.restoreCaptureNames(pre_capture_len);
        if (natural_exit != merge) {
            var else_cur = natural_exit;
            if (loop.ast.else_expr.unwrap()) |else_expr| {
                if (loop.error_token) |token| try self.registerErrorCapturesWith(token, natural_exit);
                try self.lowerStmt(else_expr, &else_cur);
                try self.restoreCaptureNames(pre_capture_len);
            }
            try self.addEdge(else_cur, merge);
        }
        cur.* = merge;
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
        const model = cache.fileModel() catch return false;
        const ti = model.findType(type_name) orelse return false;
        const tree = self.tree;
        const tags = tree.tokens.items(.tag);
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
            const close = tokens.matchParen(tags, name_tok + 1, @intCast(tags.len - 1)) orelse continue;
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
        const model = cache.fileModel() catch return false;
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

        // Find any method on type `ct` whose body allocates a heap
        // instance of the type (`<x>.create(<ct>)` / `.create(Self)`).
        const cache = self.cache orelse return null;
        const creator_found = cache.anyMethodAllocatesSelf(ct) catch false;
        if (!creator_found) return null;

        // Two-stage cleanup pattern: when fn is `deinit` / `finalize`
        // AND the type ALSO defines a separate `destroy` method,
        // the convention is `destroy()` does `deinit(); alloc.destroy(self);`.
        // Don't fire on the inner `deinit` — it's deliberately
        // partial.  The leak check naturally targets `destroy` (if
        // even there) instead.
        if (!std.mem.eql(u8, fn_name, "destroy")) {
            const has_destroy = cache.typeHasMethod(ct, "destroy") catch false;
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
            if (c.summaryByMethod(ct, fn_name) catch null) |s| {
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
        _ = body;
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
                        if (z.typeReferenceOfNode(input) catch null) |ty| {
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
            .continue_to = header, .merge = merge, .defer_depth = self.deferred.items.len,
            .label = if (loop.label_token) |token| self.tree.tokenSlice(token) else null,
        });
        const pre_capture_len: u32 = @intCast(self.locals.items.len);
        try self.registerCapturesWith(loop.payload_token, body);
        self.markInteriorCaptures(loop, body);
        var body_cur = body;
        try self.lowerStmt(loop.ast.then_expr, &body_cur);
        const ended_loop = self.loop_stack.pop().?;
        std.debug.assert(ended_loop.merge == merge);
        try self.addEdge(body_cur, header);
        try self.restoreCaptureNames(pre_capture_len);
        if (loop.ast.else_expr.unwrap()) |else_expr| {
            var else_cur = natural_exit;
            try self.lowerStmt(else_expr, &else_cur);
            try self.addEdge(else_cur, merge);
        }
        cur.* = merge;
    }

    /// `switch (cond) { CASE => EXPR, ... }` — N-way fork.  Each case
    /// becomes a successor of `cur`; all cases join into a fresh merge
    /// block.  We don't model case-pattern matching or exhaustiveness;
    /// every case is treated as reachable from cur.
    fn lowerSwitch(self: *Builder, sw_node: Ast.Node.Index, cur: *BlockId) !void {
        const tree = self.tree;
        const sw = tree.fullSwitch(sw_node) orelse {
            try self.appendStmt(cur.*, .{
                .kind = .{ .lowering_gap = .{ .note = "switch-extract" } },
                .pos = self.posOf(sw_node),
                .end_pos = self.endPosOf(sw_node),
            });
            return;
        };

        // Walk the discriminant expression before any case branch.
        try self.emitUsesInExpr(sw.ast.condition, cur.*, null);

        const merge = try self.newBlock();

        if (sw.ast.cases.len == 0) {
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
            const case_block = try self.newBlock();
            try self.addEdge(cur.*, case_block);
            // `.tag => |val| ...` capture binds inside this case only.
            // Emit reset_capture into case_block so that stale field
            // state from a prior iteration (when the switch is inside
            // a loop) doesn't cause spurious double-free / UAF.
            // Mirrors the reset_into=body approach used by while/for.
            if (case_full.payload_token) |pt| {
                try self.registerCapturesWith(pt, case_block);
                if (sw_union_ti) |un_ti| self.markPointerCapturesFromUnion(pt, un_ti, case_full.ast.values);
            }
            var case_cur = case_block;
            try self.lowerStmt(case_full.ast.target_expr, &case_cur);
            try self.addEdge(case_cur, merge);
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
        const model = cache.fileModel() catch return null;
        const ti = model.findType(type_name) orelse return null;
        if (ti.kind != .union_) return null;
        return ti;
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
        // payload_token is the start of the payload region (first
        // token AFTER the opening `|`, matching registerCapturesWith
        // semantics).  Walk forward to the first `.identifier`,
        // bailing on the closing `.pipe`.  Skip leading `*` for
        // by-pointer capture form.
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
        const name = cap_name orelse return;
        if (std.mem.eql(u8, name, "_")) return;
        const lid = self.name_to_local.get(name) orelse return;
        // Walk each prong value `.<tag>` and check the union's
        // field type starts with `*`.  All prongs in one arm must
        // agree (same payload type), so checking ANY is enough.
        for (prong_values) |v| {
            if (tree.nodeTag(v) != .enum_literal) continue;
            const tag_name_tok = tree.nodeMainToken(v);
            if (tag_name_tok >= tags.len) continue;
            if (tags[tag_name_tok] != .identifier) continue;
            const tag_name = tree.tokenSlice(tag_name_tok);
            const field = un_ti.findField(tag_name) orelse continue;
            if (field.type_first > field.type_last) continue;
            if (tags[field.type_first] == .asterisk) {
                self.locals.items[@intFromEnum(lid)].is_pointer = true;
                return;
            }
        }
    }

    /// `try expr` at statement position.  Lower `expr` on the success
    /// path (cur continues forward); add an error-exit edge to a sink
    /// block that replays errdefers + defers and terminates.  The sink
    /// has no successor — it represents the implicit `return error.X`.
    ///
    /// Phase 9 v1: we DON'T attach this error-exit edge to every
    /// `try` buried inside an expression (e.g. `const x = try foo()`).
    /// That would require expression-tree walks and would explode the
    /// CFG with sink blocks that don't enrich downstream analysis.
    /// Statement-position try alone is enough to model the common
    /// pattern `try foo();` for side-effect calls.
    fn lowerTryStmt(self: *Builder, try_node: Ast.Node.Index, cur: *BlockId) !void {
        const tree = self.tree;
        const inner = tree.nodeData(try_node).node;
        // Success path: side-effects of the wrapped expression.
        try self.lowerStmt(inner, cur);
        // Error path: synthetic sink.
        try self.emitTryErrorExit(cur, self.posOf(try_node));
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

    fn maybeLowerLabeledBlockExpr(
        self: *Builder,
        expr: Ast.Node.Index,
        cur: *BlockId,
    ) !bool {
        const tree = self.tree;
        switch (tree.nodeTag(expr)) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {},
            else => return false,
        }
        const lt = self.blockLabelToken(expr) orelse return false;
        try self.lowerLabeledBlock(expr, lt, cur);
        return true;
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
    ) !void {
        const tree = self.tree;
        const label = tree.tokenSlice(label_token);
        const merge = try self.newBlock();
        try self.block_label_stack.append(self.gpa, .{ .label = label, .merge = merge, .defer_depth = self.deferred.items.len });
        try self.lowerBlock(block_node, cur);
        _ = self.block_label_stack.pop();
        // Natural fallthrough — body completed without breaking.
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
        // Process the break's value expression FIRST so any
        // address-of args (`&local`) clear .undef state before
        // the edge to merge is taken.  Without this, code like
        //     var x = undefined;
        //     const rc = blk: {
        //         break :blk fn_call(&x);
        //     };
        //     return x;
        // never clears x's .undef — the &x is never lowered.
        //
        // Restricted to CALL value-expressions: walking arbitrary
        // value expressions (slices, field reads) also fires
        // use-undef on legitimate slice reads after partial array
        // writes (`field[0] = 0; break :blk field[0..0:0];`).  The
        // only payoff we actually want here is by-ref arg clearing
        // — which is a call-expr shape by construction.
        if (opt_value_node.unwrap()) |v| {
            const vt = tree.nodeTag(v);
            const is_call_value = switch (vt) {
                .call,
                .call_one,
                .call_comma,
                .call_one_comma,
                .builtin_call,
                .builtin_call_two,
                .builtin_call_comma,
                .builtin_call_two_comma,
                .@"switch",
                .switch_comma,
                => true,
                else => false,
            };
            if (is_call_value) {
                try self.emitUsesInExpr(v, cur.*, null);
            }
        }
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
    fn emitTryErrorExit(self: *Builder, cur: *BlockId, pos: SrcPos) !void {
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
        const tree = self.tree;
        const data = tree.nodeData(catch_node).node_and_node;
        // Success path: lhs's side effects emit into cur.
        try self.lowerStmt(data[0], cur);
        try self.emitCatchFork(catch_node, cur);
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
    fn emitCatchFork(self: *Builder, catch_node: Ast.Node.Index, cur: *BlockId) !void {
        const tree = self.tree;
        const body_node = tree.nodeData(catch_node).node_and_node[1];

        const catch_block = try self.newBlock();
        const merge = try self.newBlock();

        try self.addEdge(cur.*, catch_block);
        try self.addEdge(cur.*, merge);

        // `catch |err| BODY` — payload is `main_token + 2` when the
        // token immediately following `catch` is `|`.  Scope: body only.
        if (self.catchPayloadToken(catch_node)) |pt| {
            try self.registerErrorCaptures(pt);
        }

        var catch_cur = catch_block;
        try self.lowerStmt(body_node, &catch_cur);
        try self.addEdge(catch_cur, merge);

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
        const is_array = if (var_decl.ast.type_node.unwrap()) |tn|
            self.typeIsStackArray(tn)
        else
            false;
        var is_pointer = if (var_decl.ast.type_node.unwrap()) |tn|
            self.typeIsPointer(tn)
        else
            false;

        const init_opt = var_decl.ast.init_node.unwrap();

        // Top-level labeled-block init (`const x = blk: { ... };`) —
        // lower the body FIRST so its side effects + break paths run
        // before the binding takes effect.  cur advances to the
        // post-merge; the .decl emits there with .unknown init_kind.
        var init_was_labeled_block = false;
        if (init_opt) |init| {
            init_was_labeled_block = try self.maybeLowerLabeledBlockExpr(init, cur);
        }

        const init_kind: ExprKind = if (init_opt) |init|
            self.classifyExpr(init)
        else
            .plain;

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
            if (init_opt) |init| {
                if (tree.nodeTag(init) == .address_of) is_pointer = true;
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
                if (init_opt) |init| {
                    if (self.initArrayElementIsPointer(init)) is_pointer = true;
                }
            }
            // Init-shape signal: `<recv>.<method>(...)` where
            // `<method>` is one of the conventional pointer-yielding
            // cast/accessor names (`as`, `cast`, `ptrCast`,
            // `getPtr`, `getParent`, `parent`).  These reliably
            // return `*T` in Zig idioms (`@ptrCast`, tagged-union
            // `.as(Ty)`, `@fieldParentPtr`-wrapping helpers).
            // Suppresses stack-escape FPs on `&casted.<field>`
            // shapes (interpreter.zig:1552 etc.).
            if (!is_pointer and init_kind == .unknown) {
                if (init_opt) |init| {
                    if (initCallNameIsPointerReturning(tree, init)) is_pointer = true;
                }
            }
            // Receiver-pointer heuristic: if the init call's direct
            // receiver is a known pointer local, the factory/builder
            // call likely returns a pointer too — e.g. `b.addStep()`
            // where `b: *std.Build` → result is `*Step.*`.  O(1)
            // hash lookup — run before ZLS to avoid expensive
            // cross-file resolution when the answer is already known.
            if (!is_pointer and init_kind == .unknown) {
                if (init_opt) |init| {
                    if (initCallReceiverIsPointerLocal(self, tree, init)) is_pointer = true;
                }
            }
            // ZLS fallback: if the init expression resolves to a
            // pointer type at the outermost level, the local is a
            // pointer.  Catches opaque-pointer-returning calls whose
            // receiver isn't a locally-tracked pointer.
            if (!is_pointer and init_kind == .unknown) {
                if (init_opt) |init| {
                    if (self.zls) |z| {
                        if ((z.resolvedTypeIsPointer(init) catch null) == true) is_pointer = true;
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
            // Aliased noreturn fn: `const exit = std.process.exit;`
            // Lets later call sites that use the alias terminate
            // their block.
            if (init_opt) |i| if (self.initIsNoreturnAlias(i)) break :blk .noreturn_alias;
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
        const decl_type_name: ?[]const u8 = blk: {
            if (var_decl.ast.type_node.unwrap()) |tn| {
                break :blk self.extractTypeName(tn, self.self_type);
            }
            if (init_opt) |init| {
                break :blk self.inferTypeNameFromInit(init);
            }
            break :blk null;
        };
        const local = try self.registerLocalWithPointerHint(
            name,
            self.posOfToken(name_tok),
            is_array,
            init_hint,
            bound_fn_name,
            decl_type_name,
            is_pointer,
        );

        // Emit .use stmts for every local read by the init expression
        // (before the .decl so the read is checked against pre-decl state).
        // Skip emitUsesInExpr when init was a labeled block — the
        // block's body already lowered each inner stmt (with its
        // own .use/.assign emissions).  Walking the whole init
        // expression's tokens would incorrectly emit .use for LHS
        // identifiers of inner assigns.
        if (!init_was_labeled_block) {
            if (init_opt) |init| try self.emitUsesInExpr(init, cur.*, null);
        }

        try self.appendStmt(cur.*, .{
            .kind = .{ .decl = .{ .local = local, .init_kind = effective_init_kind } },
            .pos = self.posOf(decl_node),
            .end_pos = self.endPosOf(decl_node),
        });

        // Struct-literal RHS: unpack so aliased fields buried in the
        // literal get their own field_assign keyed by name.  Symmetric
        // with lowerAssign — `var c: T = .{ .data = buf }` registers
        // `(c, "data") → buf's origin` so a later `c.data` read sees
        // buf's freed state.  Skipped for labeled-block inits (the
        // inner stmts already lowered themselves).
        if (init_opt) |init| if (!init_was_labeled_block) {
            try self.unpackStructInitFields(cur.*, local, null, init, self.posOf(decl_node), self.endPosOf(decl_node));
            // Constructor-call result with heap fields: when init is
            // `T.constructor(...)` and that fn's body returned
            // `.{ .X = <heap_alloc> }`, emit a synthetic
            // `field_assign(local, X, .heap_alloc(fresh))` so
            // downstream field-use machinery sees the right state
            // (e.g. `var u = toUtf8(a); use(u.bytes);` tracks
            // u.bytes's heap allocation).
            try self.emitConstructorResultHeapFields(cur.*, local, init, self.posOf(decl_node), self.endPosOf(decl_node));
        };

        // Init-position try/catch: now that the decl has emitted, model
        // the same CFG side-effects we'd get if the init had appeared
        // at statement position.  We don't walk arbitrarily-nested try
        // inside larger expressions — only top-level forms.  These
        // cover the common cases (`const x = try foo()`, `const x =
        // foo() catch ...`); buried try inside arithmetic etc. is rare
        // and unmodeled (yields a sink-less success-only path).
        if (init_opt) |init| {
            try self.lowerInitSideEffects(init, cur);
        }
    }

    /// Infer pointer-ness for an indexed collection element from its
    /// declared element type. This covers receiver fields such as
    /// `self.handles.items[index]` and direct slice parameters.
    fn initArrayElementIsPointer(self: *const Builder, init: Ast.Node.Index) bool {
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
            const model = cache.fileModel() catch return false;
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

    /// Walk an init / rhs expression for top-level catch / try / orelse
    /// forms whose bodies have side effects (defers fire, locals
    /// initialize, arena.deinit() runs).  Without lowering these, the
    /// abstract state at the decl's post-position reflects only the
    /// success path — a catch body that does `arena.deinit(); return
    /// throwValue(log.toJS());` would never be seen, hiding a UAK.
    ///
    /// Handles:
    ///   - `expr catch BODY` → emitCatchFork
    ///   - `try expr`        → emitTryErrorExit
    ///   - `expr orelse BODY` → recurse into lhs (catch may live there),
    ///     plus lower orelse-BODY as a fork of its own
    ///
    /// Recursion bounded by AST depth; cheap.
    fn lowerInitSideEffects(self: *Builder, init: Ast.Node.Index, cur: *BlockId) (LoweringError)!void {
        const tree = self.tree;
        switch (tree.nodeTag(init)) {
            .@"try" => try self.emitTryErrorExit(cur, self.posOf(init)),
            .@"catch" => try self.emitCatchFork(init, cur),
            .@"orelse" => {
                const data = tree.nodeData(init).node_and_node;
                // lhs may itself contain a top-level catch/try whose
                // body has side effects (the common
                // `expr catch {...} orelse {...}` shape).
                try self.lowerInitSideEffects(data[0], cur);
                // Fork the orelse body: success edge (optional was
                // non-null) and orelse-body edge.  Body is BODY=data[1].
                try self.emitOrelseFork(data[1], cur);
            },
            else => {},
        }
    }

    /// Like emitCatchFork but for an `orelse BODY`.  The body runs
    /// when the optional resolves to null.  Same join shape.
    fn emitOrelseFork(self: *Builder, body_node: Ast.Node.Index, cur: *BlockId) !void {
        const orelse_block = try self.newBlock();
        const merge = try self.newBlock();
        try self.addEdge(cur.*, orelse_block);
        try self.addEdge(cur.*, merge);
        var ob_cur = orelse_block;
        try self.lowerStmt(body_node, &ob_cur);
        try self.addEdge(ob_cur, merge);
        cur.* = merge;
    }

    /// `LHS = RHS;` — when LHS is a known simple-identifier local, emit
    /// a real `.assign` so the analyzer can update origin tracking.
    /// Otherwise (field access, deref, destructuring) fall back to a
    /// lowering_gap so locals collapse conservatively to .plain.
    ///
    /// Either way, if the RHS has a top-level `try` or `catch`, emit
    /// the same error-exit / fork helpers we use in init/return
    /// positions — those error-path CFG edges are independent of
    /// whether we successfully tracked the target.
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

        // Top-level labeled-block rhs (`x = blk: { ... };`) — lower
        // its body in-place, advancing cur, before the .assign emits.
        // When this fires, the body's inner stmts already emitted
        // their own .use / .assign / .free; walking the same rhs again
        // via emitUsesInExpr would double-count those tokens and, e.g.
        // emit a .use(host) at the labeled-block's opening AFTER the
        // body already lowered an `allocator.free(host)`.  Symmetric
        // to the same guard in lowerVarDecl.
        if (!try self.maybeLowerLabeledBlockExpr(rhs, cur)) {
            try self.emitUsesInExpr(rhs, cur.*, null);
            try self.applyTopLevelCallEffects(rhs, cur);
            switch (tree.nodeTag(rhs)) {
                .@"try" => try self.emitTryErrorExit(cur, self.posOf(rhs)),
                .@"catch" => try self.emitCatchFork(rhs, cur),
                else => {},
            }
        }

        if (target_local) |t| {
            try self.appendStmt(cur.*, .{
                .kind = .{ .assign = .{
                    .target = t,
                    .rhs_kind = self.classifyExpr(rhs),
                } },
                .pos = self.posOf(assign_node),
                .end_pos = self.endPosOf(assign_node),
            });
            // Struct-literal RHS: unpack so aliased fields buried in
            // the literal get their own field_assign keyed by name.
            // `container = .{ .ptr = buf }` registers
            // `(container, "ptr") → buf's origin` so a later
            // `container.ptr` read sees buf's freed state.
            try self.unpackStructInitFields(cur.*, t, null, rhs, self.posOf(assign_node), self.endPosOf(assign_node));
        } else if (self.fieldLhsFor(lhs)) |fref| {
            // `obj.field = RHS` where obj is a known local — emit
            // .field_assign so the field's origin is tracked
            // separately.  Catches store-then-free-then-use of a
            // struct field.
            try self.appendStmt(cur.*, .{
                .kind = .{ .field_assign = .{
                    .parent = fref.parent,
                    .name = fref.name,
                    .rhs_kind = self.classifyExpr(rhs),
                } },
                .pos = self.posOf(assign_node),
                .end_pos = self.endPosOf(assign_node),
            });
            // Nested struct-literal unpack for the field LHS, e.g.
            // `install.ca = .{ .str = buf }` → field_assign on
            // `(install, "ca.str")`.  oven-sh/bun#25563 shape.
            try self.unpackStructInitFields(cur.*, fref.parent, fref.name, rhs, self.posOf(assign_node), self.endPosOf(assign_node));
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
            try self.appendStmt(cur.*, .{
                .kind = .{ .pointer_write = .{ .target = out_local } },
                .pos = self.posOf(assign_node),
                .end_pos = self.endPosOf(assign_node),
            });
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
            try self.unpackStructInitFields(cur.*, out_local, null, rhs, self.posOf(assign_node), self.endPosOf(assign_node));
        } else if (tree.nodeTag(lhs) == .identifier and
            std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(lhs)), "_"))
        {
            // Discard reads and call effects were lowered with the RHS.
        } else {
            // Untracked target (e.g. `@field(obj, ...) = X`,
            // `arr[i] = X`).  For any known local mentioned anywhere in
            // the LHS expression, treat the assignment as a write to
            // that local — `obj.field = X` only type-checks if `obj` is
            // initialized, so clearing its .undef state is sound.
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
    /// match tuple slots to types.  The rhs's top-level try/catch /
    /// labeled-block side-effects ARE lowered (once, before the
    /// per-target emissions), matching plain-assign semantics.
    fn lowerAssignDestructure(
        self: *Builder,
        assign_node: Ast.Node.Index,
        cur: *BlockId,
    ) !void {
        const tree = self.tree;
        const full = tree.assignDestructure(assign_node);
        const rhs = full.ast.value_expr;

        if (!try self.maybeLowerLabeledBlockExpr(rhs, cur)) {
            try self.emitUsesInExpr(rhs, cur.*, null);
            try self.applyTopLevelCallEffects(rhs, cur);
            switch (tree.nodeTag(rhs)) {
                .@"try" => try self.emitTryErrorExit(cur, self.posOf(rhs)),
                .@"catch" => try self.emitCatchFork(rhs, cur),
                else => {},
            }
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

    fn lowerReturn(self: *Builder, ret_node: Ast.Node.Index, cur: *BlockId) !void {
        const tree = self.tree;
        const data = tree.nodeData(ret_node);
        const value_opt = data.opt_node.unwrap();

        // Top-level try/catch in the returned expression — model the
        // error path BEFORE flushing defers (so the synthetic sink and
        // the merge block both get the right view of state).  The
        // err-exit sink does its own flushErrAndNormalDefers; the
        // catch fork advances cur to a merge where we continue the
        // success-path return.
        if (value_opt) |expr| {
            switch (tree.nodeTag(expr)) {
                .@"try" => try self.emitTryErrorExit(cur, self.posOf(expr)),
                .@"catch" => try self.emitCatchFork(expr, cur),
                else => {},
            }
            // Top-level labeled-block return (`return blk: { ... };`)
            // — lower body in-place so side effects + breaks run
            // before the return.  cur advances to post-merge; the
            // ret then emits there.
            if (try self.maybeLowerLabeledBlockExpr(expr, cur)) {}

            // Top-level switch return (`return switch (x) { ... .err
            // => { free; return error.Y } ... };`) — fork each arm's
            // body off `cur` as its own basic block so diverging arms
            // (those whose bodies `return` / `unreachable`) get their
            // errdefer/defer flushes and any UAF/double-free in their
            // statements modeled.  The outer .ret still emits from
            // `cur`, but arm-side-effects no longer hide inside an
            // unwalked expression.
            try self.maybeLowerReturnSwitchArms(expr, cur);
        }

        // Zig semantics: the return value is EVALUATED FIRST, then
        // defers fire, then the function actually exits.  Emit .use
        // stmts for the return value's reads BEFORE flushing defers
        // so a `defer free(buf); return use(buf);` pattern doesn't
        // see buf as already-freed at .use time.
        const value_kind: ExprKind = if (value_opt) |expr|
            self.classifyExpr(expr)
        else
            .plain;
        if (value_opt) |expr| try self.emitUsesInExpr(expr, cur.*, null);

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
        const value_is_error = if (value_opt) |expr|
            self.returnExprIsError(expr)
        else
            false;
        if (value_is_error) {
            try self.flushErrAndNormalDefers(cur);
        } else {
            try self.flushScopeDefers(cur, 0);
        }

        switch (value_kind) {
            .stack_ref, .copy_of, .composite_borrow => {
                if (value_opt) |expr| try self.emitAdditionalEscapeChecks(expr, cur.*, value_kind);
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
            const model = c.fileModel() catch null;
            if (model) |m| if (m.findFn(name) != null) return name;
        }
        return null;
    }

    /// True iff `init_node`'s source text ends with one of the
    /// known-noreturn callee chains — set on the declaring local's
    /// init_hint so subsequent calls through the alias terminate.
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

    fn initIsNoreturnAlias(self: *Builder, init_node: Ast.Node.Index) bool {
        const tree = self.tree;
        const first = tree.firstToken(init_node);
        const last = tree.lastToken(init_node);
        const start = tree.tokens.items(.start)[first];
        const last_start = tree.tokens.items(.start)[last];
        const last_len = tree.tokenSlice(last).len;
        const text = tree.source[start .. last_start + last_len];
        for (known_noreturn_chains) |pat| {
            if (std.mem.endsWith(u8, text, pat)) return true;
        }
        return false;
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
                        if (c.summaryByMethod(recv_name, callee_name) catch null) |s| {
                            if (s.result_heap_fields.len > 0) break :blk s.result_heap_fields;
                        }
                    }
                }
            }
            if (self.cache) |c| {
                if (c.summaryByName(callee_name) catch null) |s| {
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

    fn applyTopLevelCallEffects(self: *Builder, expr_node: Ast.Node.Index, cur: *BlockId) (LoweringError)!void {
        const tree = self.tree;
        // Walk through `try` / `catch` wrappers — they don't change
        // which call's effects fire on success path.
        var node = expr_node;
        while (true) switch (tree.nodeTag(node)) {
            .@"try" => node = tree.nodeData(node).node,
            .@"catch" => node = tree.nodeData(node).node_and_node[0],
            else => break,
        };
        switch (tree.nodeTag(node)) {
            .call, .call_one, .call_comma, .call_one_comma => {},
            else => return,
        }
        // Re-use the same dispatch logic as lowerCallStmt.  Pattern-
        // matched arena/heap kills already detected by lowerCallStmt
        // for bare-stmt calls — here we ALSO need @takes effects.
        if (self.takesOwnershipFreedLocal(node)) |freed| {
            try self.appendStmt(cur.*, .{
                .kind = .{ .heap_free = .{ .freed_local = freed, .fallback_hid = blk_h: {
                    const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                    self.next_heap += 1;
                    break :blk_h h;
                } } },
                .pos = self.posOf(node),
                .end_pos = self.endPosOf(node),
            });
            return;
        }
        if (self.takesOwnershipFreedField(node)) |fref| {
            try self.appendStmt(cur.*, .{
                .kind = .{ .field_heap_free = .{ .parent = fref.parent, .name = fref.name, .fallback_hid = blk_hid: {
                    const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                    self.next_heap += 1;
                    break :blk_hid h;
                } } },
                .pos = self.posOf(node),
                .end_pos = self.endPosOf(node),
            });
            return;
        }
        {
            var emissions: std.ArrayListUnmanaged(CalleeFieldFree) = .empty;
            defer emissions.deinit(self.gpa);
            try self.collectCalleeFieldFrees(node, self.gpa, &emissions);
            if (emissions.items.len > 0) {
                for (emissions.items) |em| {
                    try self.appendStmt(cur.*, .{
                        .kind = .{ .field_heap_free = .{ .parent = em.parent, .name = em.field, .fallback_hid = blk_hid: {
                            const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                            self.next_heap += 1;
                            break :blk_hid h;
                        } } },
                        .pos = self.posOf(node),
                        .end_pos = self.endPosOf(node),
                    });
                }
                return;
            }
        }
    }

    fn lowerCallStmt(self: *Builder, call_node: Ast.Node.Index, cur: *BlockId) !void {
        // Detect arena.deinit() patterns; otherwise emit nothing
        // (call has no side-effect from our pov).
        const tree = self.tree;
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
                    .kind = .{ .field_heap_free = .{ .parent = fref.parent, .name = fref.name, .fallback_hid = blk_hid: {
                        const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                        self.next_heap += 1;
                        break :blk_hid h;
                    } } },
                    .pos = self.posOf(call_node),
                    .end_pos = self.endPosOf(call_node),
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

        // `@takes ownership(p)` — annotated free-wrapper.  Look up
        // the callee in the same-file DB; if it carries the
        // annotation, treat this call as a heap_free for the matched
        // arg.  Doesn't return: a single call can both take
        // ownership of `self` AND have `may_free_fields` describing
        // additional field frees (e.g.
        // `Utf8.deinit(self, alloc) { alloc.free(self.bytes); }`).
        var fired_any = false;
        if (self.takesOwnershipFreedLocal(call_node)) |freed| {
            try self.appendStmt(cur.*, .{
                .kind = .{ .heap_free = .{ .freed_local = freed, .fallback_hid = blk_h: {
                    const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                    self.next_heap += 1;
                    break :blk_h h;
                } } },
                .pos = self.posOf(call_node),
                .end_pos = self.endPosOf(call_node),
            });
            fired_any = true;
        }
        // Same but for `<local>.<field>.method(...)` where method has
        // @takes ownership(0) (R9 inference: callee frees its receiver).
        // The freed thing is the FIELD of the caller's local.  Without
        // this, inter-procedural UAF through struct fields (oven-sh/bun#30176
        // class) is invisible: takesOwnershipFreedLocal returns null
        // because the receiver is a field_access, not a bare ident.
        if (self.takesOwnershipFreedField(call_node)) |fref| {
            try self.appendStmt(cur.*, .{
                .kind = .{ .field_heap_free = .{ .parent = fref.parent, .name = fref.name, .fallback_hid = blk_hid: {
                    const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                    self.next_heap += 1;
                    break :blk_hid h;
                } } },
                .pos = self.posOf(call_node),
                .end_pos = self.endPosOf(call_node),
            });
            fired_any = true;
        }
        // Callee's `may_free_fields` (R10 field-chain inference) —
        // each entry says "the call frees param[N]'s field F".
        // Resolve each to the caller-side local and emit a
        // `.field_heap_free`.  Catches the wrapper-method-frees-
        // field pattern, single or multiple fields, receiver or
        // non-receiver params.
        {
            var emissions: std.ArrayListUnmanaged(CalleeFieldFree) = .empty;
            defer emissions.deinit(self.gpa);
            try self.collectCalleeFieldFrees(call_node, self.gpa, &emissions);
            if (emissions.items.len > 0) {
                for (emissions.items) |em| {
                    try self.appendStmt(cur.*, .{
                        .kind = .{ .field_heap_free = .{ .parent = em.parent, .name = em.field, .fallback_hid = blk_hid: {
                            const h: abstract_state.HeapId = @enumFromInt(self.next_heap);
                            self.next_heap += 1;
                            break :blk_hid h;
                        } } },
                        .pos = self.posOf(call_node),
                        .end_pos = self.endPosOf(call_node),
                    });
                }
                fired_any = true;
            }
        }
        if (fired_any) return;

        // Untracked call at stmt position — emit uses for everything
        // it references so UAF on call args still fires before the
        // conservative gap erases tracked origins.
        try self.emitUsesInExpr(call_node, cur.*, null);
        try self.appendStmt(cur.*, .{
            .kind = .{ .lowering_gap = .{ .note = "call-untracked", .may_assign_locals = false } },
            .pos = self.posOf(call_node),
            .end_pos = self.endPosOf(call_node),
        });

        // If the callee is annotated/inferred `noreturn`, the call
        // diverges — terminate this block (matches the treatment of
        // `unreachable` / `@panic`).
        if (self.calleeIsNoreturn(call_node)) {
            cur.* = try self.newBlock();
        }
    }

    /// True iff the call's callee resolves to a fn whose DB entry
    /// carries is_noreturn=true, OR the call's source text matches
    /// a known-stdlib noreturn pattern (`std.process.exit`,
    /// `std.os.abort`, `std.posix.exit`, etc.).  The stdlib list
    /// avoids needing zbc to parse std itself — these signatures
    /// don't change.
    fn calleeIsNoreturn(self: *Builder, call_node: Ast.Node.Index) bool {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return false;
        const callee = call_full.ast.fn_expr;
        const method_tok = switch (tree.nodeTag(callee)) {
            .identifier => tree.nodeMainToken(callee),
            .field_access => tree.nodeData(callee).node_and_token[1],
            else => return false,
        };
        const raw_name = tree.tokenSlice(method_tok);
        const name = if (tree.nodeTag(callee) == .identifier)
            self.resolveBoundCallee(raw_name)
        else
            raw_name;
        if (self.cache) |c| {
            if (c.summaryByName(name) catch null) |s| if (s.is_noreturn) return true;
        }
        // Aliased noreturn local: `const exit = std.process.exit;`
        // then `exit(1)`.  Bare-identifier callee referencing a
        // local whose init was a known noreturn chain.
        if (tree.nodeTag(callee) == .identifier) {
            if (self.name_to_local.get(name)) |local| {
                if (self.locals.items[@intFromEnum(local)].init_hint == .noreturn_alias) {
                    return true;
                }
            }
        }

        // Known-stdlib noreturn callees.  Match against the leading
        // tokens of the callee chain (not the full call text) so an
        // arg shape like `(exitcode)` doesn't pull patterns from
        // arbitrary user text into the match window.
        const first = tree.firstToken(call_node);
        const callee_last = tree.lastToken(callee);
        const start = tree.tokens.items(.start)[first];
        const end_tok_start = tree.tokens.items(.start)[callee_last];
        const end_tok_len = tree.tokenSlice(callee_last).len;
        const callee_text = tree.source[start .. end_tok_start + end_tok_len];
        for (known_noreturn_chains) |pat| {
            if (std.mem.endsWith(u8, callee_text, pat)) return true;
        }
        return false;
    }

    /// If the callee has `@takes ownership(p)`, return the LocalId
    /// of the actual arg that maps to p.  Consults the same-file
    /// annotation DB AND (when remote context is available) the
    /// imported file's DB for cross-file wrappers.  Null on miss.
    fn takesOwnershipFreedLocal(self: *Builder, call_node: Ast.Node.Index) ?LocalId {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        const callee = call_full.ast.fn_expr;

        const method_tok = switch (tree.nodeTag(callee)) {
            .identifier => tree.nodeMainToken(callee),
            .field_access => tree.nodeData(callee).node_and_token[1],
            else => return null,
        };
        const raw_callee_name = tree.tokenSlice(method_tok);
        const callee_name = if (tree.nodeTag(callee) == .identifier)
            self.resolveBoundCallee(raw_callee_name)
        else
            raw_callee_name;
        const receiver_is_arg0 = tree.nodeTag(callee) == .field_access;
        const recv_node: ?Ast.Node.Index = if (receiver_is_arg0)
            tree.nodeData(callee).node_and_token[0]
        else
            null;
        // Receiver's type name — used to disambiguate methods that
        // share a name across container types.  Null when the recv
        // isn't a known local with type info, in which case the DB
        // falls back to bare-name lookup.
        const recv_ty: ?[]const u8 = if (recv_node) |rn|
            self.receiverTypeOfNode(rn)
        else
            null;

        // Look up @takes annotation.  Try same-file first; then
        // cross-file by recv's type (when the type is defined in an
        // imported file); then the remote-namespace path (for
        // `lib.method(...)` where recv IS the namespace).
        const target_idx: u32 = blk: {
            // Try FnSummary (cache) — TYPED lookup only.  Bare-name
            // fallback (summaryByName) would cross-pollute methods
            // between unrelated types when the receiver's type isn't
            // declared in this file (e.g. external PathOrFileDescriptor.
            // deinit getting matched against local Blob.deinit's
            // inferred takes).  When recv_ty is null or external,
            // fall through to db's typed lookup (which correctly
            // returns null for cross-file types) and then to the
            // cross-file paths.
            if (self.cache) |c| {
                if (recv_ty) |ty| {
                    if (c.summaryByMethod(ty, callee_name) catch null) |s| {
                        if (s.takes_ownership_of) |i| break :blk i;
                    }
                }
                if (!receiver_is_arg0) {
                    if (c.summaryByName(callee_name) catch null) |s| {
                        if (s.takes_ownership_of) |i| break :blk i;
                    }
                }
                // Cross-file fallback: callee is defined in an @import'd
                // file.  Direct-takes inference only — resolveTransitiveTakes
                // has already propagated intra-file chains; what's left are
                // callees whose destructor lives in a foreign file.
                if (recv_ty) |ty| {
                    if (c.summaryByMethodCrossFile(ty, callee_name) catch null) |xf| {
                        if (xf.takes_ownership_of) |i| break :blk i;
                    }
                }
            }
            return null;
        };

        // For cross-file namespace calls (`lib.dispose(g, buf)`), the
        // receiver IS the imported namespace — not part of the
        // callee's logical arg list.  ast.params already holds the
        // full explicit-arg list; don't subtract for the namespace.
        // Cross-file detection retired with remote_resolver; receiver
        // is now always treated as arg 0 for field-access callees.
        const effective_recv_is_arg0 = receiver_is_arg0;

        const candidate = if (effective_recv_is_arg0 and target_idx == 0)
            recv_node.?
        else blk: {
            const explicit_idx = if (effective_recv_is_arg0) target_idx - 1 else target_idx;
            if (explicit_idx >= call_full.ast.params.len) return null;
            break :blk call_full.ast.params[explicit_idx];
        };

        if (tree.nodeTag(candidate) != .identifier) return null;
        const name = tree.tokenSlice(tree.nodeMainToken(candidate));
        return self.name_to_local.get(name);
    }

    /// Companion to `takesOwnershipFreedLocal`: when the call is
    /// `<local>.<field>.method(...)` and method has @takes
    /// ownership(0) (receiver-freeing — R8b inferred or annotated),
    /// the freed entity is the FIELD of caller's local.
    /// Returns the (local, field-name) pair for emission as
    /// .field_heap_free.
    fn takesOwnershipFreedField(self: *Builder, call_node: Ast.Node.Index) ?FieldRef {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return null;
        const callee = call_full.ast.fn_expr;
        if (tree.nodeTag(callee) != .field_access) return null;
        const fa = tree.nodeData(callee).node_and_token;
        const recv = fa[0];
        // Receiver must be `<local>.<field>` exactly (one level of
        // field access).  Deeper chains (`a.b.c.method()`) are out of
        // scope for now — they need full field-aliasing.
        if (tree.nodeTag(recv) != .field_access) return null;
        const recv_fa = tree.nodeData(recv).node_and_token;
        const recv_recv = recv_fa[0];
        if (tree.nodeTag(recv_recv) != .identifier) return null;
        const recv_name = tree.tokenSlice(tree.nodeMainToken(recv_recv));
        const parent = self.name_to_local.get(recv_name) orelse return null;
        const field_name = tree.tokenSlice(recv_fa[1]);
        const method_name = tree.tokenSlice(fa[1]);

        const cache = self.cache orelse return null;
        const parent_name = self.locals.items[@intFromEnum(parent)].type_name orelse return null;
        const owner = cache.findTypeAcrossImports(parent_name) orelse return null;
        const child = cache.fieldType(owner, field_name) orelse return null;
        const summary = (cache.summaryForType(child, method_name) catch null) orelse return null;
        if (summary.takes_ownership_of != 0) return null;
        return .{ .parent = parent, .name = field_name };
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
                    if (z.typeReferenceOfNode(node) catch null) |ty| {
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
            return z.typeReferenceOfNode(node) catch null;
        }
        return null;
    }

    /// A single (parent_local, field) emission triggered by a
    /// callee's `may_free_fields` entry at the call site.
    /// `lowerCallStmt`/`applyTopLevelCallEffects` emit one
    /// `.field_heap_free` per slot.
    const CalleeFieldFree = struct {
        parent: LocalId,
        field: []const u8,
    };

    /// Walk the callee's `may_free_fields` list, resolve each
    /// `{param, field}` to the corresponding caller-side arg local,
    /// and call `cb` with the resolved `(parent, field)` pair.
    /// Entries whose param maps to an unresolvable arg (non-ident,
    /// out of bounds) are silently skipped.
    ///
    /// Handles method-call form (`recv.method(a, b)` — param 0 =
    /// recv, param N = call's args[N-1]) and bare call form
    /// (`fn(a, b, c)` — param N = call's args[N]).  Imported-
    /// namespace prefixes (`bun.method(p)`) don't consume a param
    /// slot — `bun` isn't a logical argument.
    fn collectCalleeFieldFrees(
        self: *Builder,
        call_node: Ast.Node.Index,
        gpa: std.mem.Allocator,
        out: *std.ArrayListUnmanaged(CalleeFieldFree),
    ) !void {
        const tree = self.tree;
        var buf: [1]Ast.Node.Index = undefined;
        const call_full = tree.fullCall(&buf, call_node) orelse return;
        const callee = call_full.ast.fn_expr;

        const method_tok = switch (tree.nodeTag(callee)) {
            .identifier => tree.nodeMainToken(callee),
            .field_access => tree.nodeData(callee).node_and_token[1],
            else => return,
        };
        const raw_callee_name = tree.tokenSlice(method_tok);
        const callee_name = if (tree.nodeTag(callee) == .identifier)
            self.resolveBoundCallee(raw_callee_name)
        else
            raw_callee_name;
        const receiver_is_arg0 = tree.nodeTag(callee) == .field_access;
        const recv_node: ?Ast.Node.Index = if (receiver_is_arg0)
            tree.nodeData(callee).node_and_token[0]
        else
            null;
        const recv_ty: ?[]const u8 = if (recv_node) |rn|
            self.receiverTypeOfNode(rn)
        else
            null;

        // Resolve callee's may_free_fields via the FnSummary cache.
        // The filter only fires when the field's actual type has the
        // exact matched method declared locally.
        const Free = struct { param: u32, field: []const u8 };
        var free_buf: [16]Free = undefined;
        const frees: []const Free = blk: {
            if (self.cache) |c| {
                if (recv_ty) |ty| {
                    if (c.summaryByMethod(ty, callee_name) catch null) |s| {
                        if (s.may_free_fields.len > 0) {
                            const n = @min(s.may_free_fields.len, free_buf.len);
                            for (s.may_free_fields[0..n], 0..) |ff, i| {
                                free_buf[i] = .{ .param = ff.param, .field = ff.field };
                            }
                            break :blk free_buf[0..n];
                        }
                    }
                }
                // Identifier-style call (e.g. `cleanup(x, y)`): no
                // receiver type, look up the top-level fn by name.
                if (!receiver_is_arg0) {
                    if (c.summaryByName(callee_name) catch null) |s| {
                        if (s.may_free_fields.len > 0) {
                            const n = @min(s.may_free_fields.len, free_buf.len);
                            for (s.may_free_fields[0..n], 0..) |ff, i| {
                                free_buf[i] = .{ .param = ff.param, .field = ff.field };
                            }
                            break :blk free_buf[0..n];
                        }
                    }
                }
            }
            return;
        };

        // Receiver is param 0 for field-access callees.  Cross-file
        // namespace detection retired with remote_resolver.
        const effective_recv_is_arg0 = receiver_is_arg0 and recv_node != null;

        for (frees) |ff| {
            // Map the callee's param index to the caller's arg node.
            const arg_node: Ast.Node.Index = if (effective_recv_is_arg0 and ff.param == 0)
                recv_node.?
            else blk: {
                const explicit_idx = if (effective_recv_is_arg0) ff.param - 1 else ff.param;
                if (explicit_idx >= call_full.ast.params.len) continue;
                break :blk call_full.ast.params[explicit_idx];
            };
            // The arg local must be a bare identifier known to the
            // caller — that's the only shape we can rebind a field
            // origin on.
            if (tree.nodeTag(arg_node) != .identifier) continue;
            const arg_name = tree.tokenSlice(tree.nodeMainToken(arg_node));
            const parent = self.name_to_local.get(arg_name) orelse continue;
            try out.append(gpa, .{ .parent = parent, .field = ff.field });
        }
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

    /// For `<allocator>.free(obj.field)` shape, return the FieldRef.
    fn heapFreedField(self: *Builder, call_node: Ast.Node.Index) ?FieldRef {
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
        return self.fieldLhsFor(arg);
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

    fn classifyExpr(self: *Builder, expr_node: Ast.Node.Index) ExprKind {
        if (self.classify_depth == 64) {
            self.budget_exhausted = true;
            return .unknown;
        }
        self.classify_depth += 1;
        defer self.classify_depth -= 1;
        const tree = self.tree;
        const tag = tree.nodeTag(expr_node);
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

        // `lhs catch rhs` — the success-path value has the lhs's
        // origin (e.g. `gpa.alloc(...) catch return &.{}` produces a
        // heap allocation on success).  The error path is modeled
        // separately via emitCatchFork at statement level; here we
        // just unwrap to lhs so the origin propagates into the
        // declaring local instead of collapsing to .unknown.
        if (tag == .@"catch") {
            return self.classifyExpr(tree.nodeData(expr_node).node_and_node[0]);
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
                    const fname = tree.tokenSlice(field_tok);
                    if (std.mem.eql(u8, fname, "ptr")) {
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
                    // .{...};`) and type aliases live in static memory.
                    // `&X` borrows into static storage — not a stack
                    // escape.
                    const info = self.locals.items[@intFromEnum(id)];
                    if (info.init_hint == .type_alias) return .unknown;
                    return .{ .stack_ref = id };
                }
            }
            if (tree.nodeTag(inner) == .field_access) {
                if (self.fieldLhsFor(inner)) |fref| {
                    // Pointer-typed parent: the pointee lives in the
                    // caller, not this fn's stack frame.  `&self.field`
                    // where `self: *Self` is a borrow from caller-owned
                    // storage — not a stack escape candidate.
                    const parent_info = self.locals.items[@intFromEnum(fref.parent)];
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
                    // Pointer-named field in the chain: e.g.
                    // `&entry.value_ptr.field` where `value_ptr` is a
                    // `*V` (stdlib HashMap GetOrPutResult convention).
                    // The address-of borrows V's interior — not a
                    // stack ref.  Same for `*.key_ptr.*` / `*.ptr.*`
                    // and any field name ending in `_ptr`.
                    if (fieldPathHasPointerName(fref.name)) {
                        return .unknown;
                    }
                    // Type engine: check if the direct LHS of this
                    // field_access resolves to a pointer type.  Covers
                    // two cases the syntactic checks above miss:
                    //   1. `&ptr_local.field` where the local's type
                    //      wasn't annotated as a pointer (e.g. a capture
                    //      from a HashMap.get call whose return type is
                    //      `?*V`).
                    //   2. `&local.ptr_field.sub` where an intermediate
                    //      field in the chain is `*T` — the address-of
                    //      borrows through the heap pointer, not the stack.
                    if (self.zls) |zls| {
                        const child = tree.nodeData(inner).node_and_token[0];
                        if ((zls.resolvedTypeIsPointer(child) catch null) == true) {
                            return .unknown;
                        }
                    }
                    return .{ .stack_ref = fref.parent };
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
        // body was already lowered by maybeLowerLabeledBlockExpr in
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
    ) !void {
        var seen: std.AutoArrayHashMapUnmanaged(BorrowKey, void) = .empty;
        defer seen.deinit(self.gpa);
        try seen.put(self.gpa, BorrowKey.from(primary_kind), {});
        var borrows = BorrowIterator.init(self, expr_node);
        while (borrows.next()) |kind| {
            const entry = try seen.getOrPut(self.gpa, BorrowKey.from(kind));
            if (entry.found_existing) continue;
            try self.appendStmt(cur, .{
                .kind = .{ .composite_escape = kind },
                .pos = self.posOf(expr_node),
                .end_pos = self.endPosOf(expr_node),
            });
        }
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
    /// shape — i.e. a known local at the head, optional field-chain,
    /// then a method call.  Fires when:
    ///   - `local` has an arena/heap init_hint
    ///   - `method`'s annotation (in the same-file DB) is
    ///     `@returns borrowed_from(self)`
    /// Caller propagates as `.composite_borrow` so transferRet fires
    /// escape checks even on value-shape returns.
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

            // Walk the dot-chain.  Track each intermediate identifier
            // as a field segment so we can walk `local.f1.f2.method()`
            // through the model.fieldType chain to find the type that
            // owns `method`.  Last ident before `(` is the method.
            var k: Ast.TokenIndex = t + 1;
            var method_tok: Ast.TokenIndex = 0;
            var field_first: Ast.TokenIndex = 0;
            var field_last: Ast.TokenIndex = 0;
            while (k + 1 <= last and tags[k] == .period and tags[k + 1] == .identifier) {
                // The ident at k+1 might be a field or the method.  We
                // can't tell yet — record it provisionally as method;
                // if a following `.` shows up, demote to field segment.
                if (method_tok != 0) {
                    if (field_first == 0) field_first = method_tok;
                    field_last = method_tok;
                }
                method_tok = k + 1;
                k += 2;
                if (k > last) break;
                if (tags[k] == .l_paren) break;
                if (tags[k] != .period) {
                    method_tok = 0;
                    break;
                }
            }
            if (method_tok == 0) continue;
            if (k > last or tags[k] != .l_paren) continue;

            const method_name = tree.tokenSlice(method_tok);
            const recv_ty = self.locals.items[@intFromEnum(local)].type_name orelse continue;

            var owner = cache.findTypeAcrossImports(recv_ty) orelse continue;
            var field = field_first;
            var resolved = true;
            if (field_first != 0) {
                while (field <= field_last) : (field += 2) {
                    owner = cache.fieldType(owner, tree.tokenSlice(field)) orelse {
                        resolved = false;
                        break;
                    };
                }
            }
            if (!resolved) continue;
            const summary = (cache.summaryForType(owner, method_name) catch null) orelse continue;
            switch (summary.returns) {
                .borrowed_from => |idx| if (idx == 0) return local,
                else => {},
            }
        }
        return null;
    }

    /// For a call expression `<recv>.method(...)`, if `recv` resolves
    /// to a known local whose init_hint marks it as arena-bound
    /// (.arena_local or .arena_allocator), return that local.
    /// Receiver may itself be a chained field access (`x.y.method()`),
    /// in which case we walk to the head identifier.
    /// If `call_node` is `<recv>.<method>(...)` where `recv` is a
    /// local with `from_container` set (a for-loop pointer-capture
    /// into a container) AND the callee provably takes ownership of
    /// its receiver (i.e. `takes_ownership_of == 0` inferred from
    /// the body), return the receiver + container pair.
    ///
    /// "Provably" means: the method body contains
    /// `<allocator>.destroy(self)` or `<allocator>.free(self)` — the
    /// shapes fn_summary's R8b inference recognizes.  Methods named
    /// `deinit`/`close`/`deref`/etc. that merely release sub-fields
    /// (the common case in Bun and most Zig code) do NOT fire,
    /// because they're safe to call on interior pointers — the
    /// container still owns the storage.
    ///
    /// Cross-module destructors (callee in another file) are not
    /// inferred today; the rule conservatively no-fires rather than
    /// guessing from the name.  Worst case: a real interior-pointer
    /// destroy in a third-party type goes undetected — but the
    /// inverse (firing 200+ FPs on every for-loop with a cleanup
    /// call) is far worse for usability.  See FP audit 2026-05-23.
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

        const freed = self.takesOwnershipFreedLocal(call_node) orelse return null;
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

    /// `return switch (x) { ... }` — fork each arm's body off `cur`
    /// as its own basic block.  Diverging arms (those whose body
    /// `return` / `unreachable`) emit their own .ret with the right
    /// defer/errdefer flushes.  Non-diverging arms still produce a
    /// value that the outer .ret consumes; we don't try to thread
    /// that value back (the goal is bug detection, not type-check),
    /// so we just leak the forked block — it has no successor.
    ///
    /// No-op when `expr` isn't a switch.  Idempotent — called from
    /// lowerReturn after the try/catch/labeled-block dispatch.
    fn maybeLowerReturnSwitchArms(
        self: *Builder,
        expr: Ast.Node.Index,
        cur: *BlockId,
    ) (LoweringError)!void {
        const tree = self.tree;
        switch (tree.nodeTag(expr)) {
            .@"switch", .switch_comma => {},
            else => return,
        }
        const sw = tree.fullSwitch(expr) orelse return;

        // Edges inherit the final state of their predecessor block. Keep
        // switch evaluation in a predecessor that cannot also contain the
        // outer return's deferred cleanup.
        const eval_block = cur.*;
        const continuation = try self.newBlock();
        try self.emitUsesInExpr(sw.ast.condition, eval_block, null);

        for (sw.ast.cases) |case_node| {
            const case_full = tree.fullSwitchCase(case_node) orelse continue;
            const case_block = try self.newBlock();
            try self.addEdge(eval_block, case_block);
            if (case_full.payload_token) |payload_token| {
                try self.registerCaptures(payload_token);
            }
            var case_cur = case_block;
            try self.lowerStmt(case_full.ast.target_expr, &case_cur);
        }
        try self.addEdge(eval_block, continuation);
        cur.* = continuation;
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
    /// Preserve namespace qualification for method dispatch.
    fn inferTypeNameFromInit(self: *Builder, init_node: Ast.Node.Index) ?[]const u8 {
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
        // ZLS fallback: handles `var x = makeThing()`, `var x =
        // some_var.method()`, `var x = ns.factory(...)` — shapes the
        // token-pattern match above can't classify because the type
        // isn't syntactically visible at the call site.
        if (self.zls) |z| {
            return z.typeReferenceOfNode(init_node) catch null;
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

    fn classifyCall(self: *Builder, call_node: Ast.Node.Index) ExprKind {
        const tree = self.tree;

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
                        if (c.summaryByMethod(ty, method_name) catch null) |s| {
                            if (self.applySummaryReturnsToCall(s.returns, recv_node, args, recv_is_local)) |k| return k;
                        }
                    }
                }

                return .unknown;
            },
            .identifier => {
                const raw_name = tree.tokenSlice(tree.nodeMainToken(callee_node));
                const fn_name = self.resolveBoundCallee(raw_name);
                if (self.cache) |c| {
                    if (c.summaryByName(fn_name) catch null) |s| {
                        if (self.applySummaryReturnsToCall(s.returns, callee_node, args, false)) |k| return k;
                    }
                }
                return .unknown;
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
        const root_start = tree.tokens.items(.start)[root_tok];
        const root_len = tree.tokenSlice(root_tok).len;
        var first_path_byte: usize = root_start + root_len;
        if (first_path_byte < tree.source.len and tree.source[first_path_byte] == '.') {
            first_path_byte += 1;
        }
        const last_tok = tree.lastToken(lhs);
        const last_start = tree.tokens.items(.start)[last_tok];
        const last_len = tree.tokenSlice(last_tok).len;
        const path = tree.source[first_path_byte..(last_start + last_len)];
        return .{ .parent = parent, .name = path };
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
        self: *const Builder,
        recv_name: []const u8,
        path: []const u8,
        install_tok: Ast.TokenIndex,
    ) bool {
        const cache = self.cache orelse return false;
        const model = cache.fileModel() catch return false;
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
                        if (calledFnTouchesParamField(rm.tree, rm.fn_decl, path)) return true;
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
        return tree.tokenSlice(first - 2);
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
    ) LoweringError!void {
        const tree = self.tree;
        var buf: [2]Ast.Node.Index = undefined;
        const init = tree.fullStructInit(&buf, rhs_node) orelse return;
        for (init.ast.fields) |field_value| {
            const leaf = self.fieldInitName(field_value) orelse continue;
            const path = try self.allocDottedPath(prefix, leaf);
            var rhs_kind = self.classifyExpr(field_value);
            // Fixed-array undef skip: when the field's declared type
            // is `[N]T` (a fixed-size array, not a slice), `<field>
            // = undefined` leaves the array's CONTENTS undef but
            // `.len`/`.ptr` are comptime-defined.  Reading `.len`
            // (`if (arr.len > X) ...`) is therefore safe.
            // Reclassify the rhs from `.undef` → `.plain` so the
            // field doesn't get tracked as undef.
            if (rhs_kind == .undef and self.fieldHasFixedArrayType(parent, path)) {
                rhs_kind = .plain;
            }
            try self.appendStmt(cur, .{
                .kind = .{ .field_assign = .{
                    .parent = parent,
                    .name = path,
                    .rhs_kind = rhs_kind,
                } },
                .pos = pos,
                .end_pos = end_pos,
            });
            try self.unpackStructInitFields(cur, parent, path, field_value, pos, end_pos);
        }
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
        var current = cache.findTypeAcrossImports(parent_ty) orelse return false;
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

    /// Walk LHS tokens of an assignment with a non-identifier target
    /// and emit one assign(id, .unknown) per distinct known-local
    /// mentioned.  Used to clear .undef on locals written through
    /// field access, indexing, or builtin pseudo-LHS like @field.
    fn emitWritesInLhs(
        self: *Builder,
        lhs_node: Ast.Node.Index,
        cur: BlockId,
    ) !void {
        const tree = self.tree;
        const first = tree.firstToken(lhs_node);
        const last = tree.lastToken(lhs_node);
        const tags = tree.tokens.items(.tag);
        const pos = self.posOf(lhs_node);
        const end_pos = self.endPosOf(lhs_node);

        var seen: std.AutoArrayHashMapUnmanaged(LocalId, void) = .empty;
        defer seen.deinit(self.gpa);

        var t: Ast.TokenIndex = first;
        while (t <= last) : (t += 1) {
            if (tags[t] != .identifier) continue;
            if (t > 0 and tags[t - 1] == .period) continue;
            const name = tree.tokenSlice(t);
            const id = self.name_to_local.get(name) orelse continue;
            const gop = try seen.getOrPut(self.gpa, id);
            if (gop.found_existing) continue;
            // `arena.* = X` / `obj.field = X` — writes THROUGH the
            // local, doesn't rebind it.  The local's resource
            // identity (.heap / .arena / .arena_borrow) is unchanged;
            // only an .undef may have been initialized.  Emit
            // assign-via-pointer-write that only clears .undef →
            // .plain in transferAssign, preserving resource origins.
            try self.appendStmt(cur, .{
                .kind = .{ .pointer_write = .{ .target = id } },
                .pos = pos,
                .end_pos = end_pos,
            });
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
        var write_dest_skip_depth: u32 = 0;

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
                    isWriteFirstArgBuiltin(tree.tokenSlice(t - 1)))
                {
                    write_dest_skip_active = true;
                    write_dest_skip_depth = paren_depth;
                }
                continue;
            }
            if (tag == .r_paren) {
                if (paren_depth > 0) paren_depth -= 1;
                if (comptime_skip_active and paren_depth == comptime_skip_until) {
                    comptime_skip_active = false;
                }
                if (write_dest_skip_active and paren_depth < write_dest_skip_depth) {
                    write_dest_skip_active = false;
                }
                continue;
            }
            if (tag == .comma and write_dest_skip_active and paren_depth == write_dest_skip_depth) {
                // Comma at the same depth as the builtin's args ends
                // the destination region; subsequent args are sources.
                write_dest_skip_active = false;
                continue;
            }
            if (comptime_skip_active) continue;
            if (tag != .identifier) continue;
            // LHS of a plain `=` assignment inside a sub-expression
            // (e.g. a switch arm body or labeled block being used as
            // the init of an outer var_decl).  Those inner assignments
            // are NOT lowered as their own .assign statements (the
            // whole containing expression is one node from the
            // var_decl lowerer's perspective), so without recording
            // the write here a later read of the same local inside
            // the same expression spuriously sees .undef.  Emit
            // .assign(.unknown) — rhs origin is opaque from a token
            // walk, but clearing undef is what matters.
            if (t + 1 <= last and tags[t + 1] == .equal and
                (t == 0 or tags[t - 1] != .period))
            {
                const lhs_name = tree.tokenSlice(t);
                if (self.name_to_local.get(lhs_name)) |lid| {
                    if (skip_local == null or skip_local.? != lid) {
                        const gop_w = try aw.getOrPut(self.gpa, lid);
                        if (!gop_w.found_existing) {
                            try self.appendStmt(cur, .{
                                .kind = .{ .assign = .{ .target = lid, .rhs_kind = .unknown } },
                                .pos = pos,
                                .end_pos = end_pos,
                            });
                        }
                    }
                }
                continue;
            }
            // Taking an address is not a value read. Only an address passed
            // into a call can act as an out-parameter write.
            if (try address_cache.addressUseAt(t)) |address| {
                const name = tree.tokenSlice(t);
                const id = self.name_to_local.get(name) orelse continue;
                self.locals.items[@intFromEnum(id)].address_taken = true;
                if (!address.may_write) continue;
                if (skip_local) |s| if (id == s) continue;
                const hint = self.locals.items[@intFromEnum(id)].init_hint;
                if (hint != .other) continue;
                // `&id.field` — also clear the FIELD's state (out-param
                // write through pointer-to-field).  Catches the
                // canonical `var w = T{.ret = undefined}; fn(&w.ret, ...);
                // use(w.ret);` shape — without this, w.ret stays .undef
                // and the use fires use-undefined.
                if (t + 2 <= last and tags[t + 1] == .period and tags[t + 2] == .identifier) {
                    const field = tree.tokenSlice(t + 2);
                    try self.appendStmt(cur, .{
                        .kind = .{ .field_assign = .{ .parent = id, .name = field, .rhs_kind = .unknown } },
                        .pos = pos,
                        .end_pos = end_pos,
                    });
                }
                const gop = try aw.getOrPut(self.gpa, id);
                if (gop.found_existing) continue;
                try self.appendStmt(cur, .{
                    .kind = .{ .assign = .{ .target = id, .rhs_kind = .unknown } },
                    .pos = pos,
                    .end_pos = end_pos,
                });
                continue;
            }
            if (write_dest_skip_active) continue;
            // Field/method access: `.method` — skip; it's not a local.
            if (t > 0 and tags[t - 1] == .period) continue;
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
                                .pos = pos,
                                .end_pos = end_pos,
                            });
                        }
                    }
                    continue;
                }
                if (next == .colon) continue;
                if (next == .period and t + 2 <= last and tags[t + 2] == .identifier) {
                    const field = tree.tokenSlice(t + 2);
                    if (std.mem.eql(u8, field, "len") or std.mem.eql(u8, field, "ptr")) continue;
                    // Distinguish field access (`x.f`), accessor
                    // method (`x.f()` reads x), and mutator method
                    // (`x.init(...)` writes x — common pattern is
                    // `var s: T = undefined; s.init(...);`).
                    const is_method_call = t + 3 <= last and tags[t + 3] == .l_paren;
                    ident_in_method_recv_pos = is_method_call;
                    const name = tree.tokenSlice(t);
                    if (self.name_to_local.get(name)) |id| {
                        if (is_method_call) {
                            if (isMutatorMethodName(field)) {
                                // Treat as write: clear undef.  Same
                                // shape as &<local> address-of write.
                                if (skip_local == null or skip_local.? != id) {
                                    const hint = self.locals.items[@intFromEnum(id)].init_hint;
                                    if (hint == .other) {
                                        const gop = try aw.getOrPut(self.gpa, id);
                                        if (!gop.found_existing) {
                                            try self.appendStmt(cur, .{
                                                .kind = .{ .assign = .{ .target = id, .rhs_kind = .unknown } },
                                                .pos = pos,
                                                .end_pos = end_pos,
                                            });
                                        }
                                    }
                                }
                                continue;
                            }
                            // Accessor: fall through to .use emission.
                        } else {
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
                            try self.emitFieldUsePrefixes(cur, id, t, last, pos, end_pos);
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
                .pos = pos,
                .end_pos = end_pos,
            });
        }
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
                    return self.identifierToCopyOrUnknown(receiver_or_callee);
                }
                const explicit_idx = if (receiver_is_arg0) target_idx - 1 else target_idx;
                if (explicit_idx >= args.len) return .unknown;
                return self.identifierToCopyOrUnknown(args[explicit_idx]);
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

    /// Method names that conventionally MUTATE the receiver via
    /// `&self` pointer — `init`/`reset` initialize, `deinit`/`destroy`
    /// invalidate, etc.  These don't READ the receiver's current
    /// contents (init explicitly overwrites garbage), so emitting
    /// .use on them would spuriously fire `use of x while still
    /// undefined` for the canonical pattern:
    ///   var s: T = undefined;
    ///   s.init(...);
    fn isMutatorMethodName(name: []const u8) bool {
        // Prefix conventions: `init*` initializes, `set*` writes,
        // `reset*` reinitializes.  Covers `initEmpty`, `initBuffer`,
        // `initCapacity`, `setValue`, `resetState`, etc.
        if (std.mem.startsWith(u8, name, "init")) return true;
        if (std.mem.startsWith(u8, name, "set")) return true;
        if (std.mem.startsWith(u8, name, "reset")) return true;
        const list = [_][]const u8{
            "clear",         "clearRetainingCapacity", "clearAndFree",
            "deinit",        "destroy",                "close",
            "open",          "load",                   "loadFromDisk",
            "loadFromBytes", "fillFromPackageJSON",
        };
        for (list) |n| if (std.mem.eql(u8, n, name)) return true;
        return false;
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

    /// True for builtins whose FIRST argument is the destination (a
    /// write-through pointer or slice).  Used by `emitUsesInExpr` to
    /// suppress spurious .use / .field_use emission on the dest in
    /// the canonical `var buf: [N]u8 = undefined; @memcpy(buf, src);`
    /// shape — the dest is written, not read.
    fn isWriteFirstArgBuiltin(name: []const u8) bool {
        // `name` includes the leading `@`.
        return std.mem.eql(u8, name, "@memcpy") or
            std.mem.eql(u8, name, "@memset") or
            std.mem.eql(u8, name, "@memmove");
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
        // True when the chain terminates in `.len` or `.ptr`:
        //   `obj.iter_state.directory.path.len`
        // Reading `.len`/`.ptr` on a fixed-size array field (`[N]T`) does
        // not access the field's memory — `.len` is a comptime constant.
        // We stop the prefix chain two fields early to avoid spurious
        // use-undefined on the parent.  (For slices, `slice.len` IS a
        // runtime read; but firing on an undefined slice's `.len`-parent
        // is rare enough that the false-positive reduction is worth it.)
        const terminal = tree.tokenSlice(chain_end);
        const ends_in_len_or_ptr = !ends_in_call and
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
        // Mutator-method handling: when the chain ends in
        // `<deepest>.<method>(` and `<method>` is a mutator
        // (`init` / `setup` / `reset`-prefix etc.), the deepest
        // field is WRITTEN through implicit `&self`.  Emit a
        // field_assign for it (clears .undef) and field_use for
        // the strictly-shorter prefixes only (those are reads of
        // intermediate path components).
        const is_mutator_call = ends_in_call and
            isMutatorMethodName(tree.tokenSlice(chain_end));
        // Emit one prefix per inclusive field ident.
        const start_byte = tree.tokens.items(.start)[first_field];
        var f: Ast.TokenIndex = first_field;
        while (f <= last_field.?) : (f += 2) {
            const f_start = tree.tokens.items(.start)[f];
            const f_len = tree.tokenSlice(f).len;
            const path = tree.source[start_byte..(f_start + f_len)];
            // Deepest field of a mutator call: emit a write, not a read.
            if (is_mutator_call and f == last_field.?) {
                try self.appendStmt(cur, .{
                    .kind = .{ .field_assign = .{ .parent = parent, .name = path, .rhs_kind = .unknown } },
                    .pos = pos,
                    .end_pos = end_pos,
                });
            } else {
                try self.appendStmt(cur, .{
                    .kind = .{ .field_use = .{ .parent = parent, .name = path } },
                    .pos = pos,
                    .end_pos = end_pos,
                });
            }
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
    fn fieldChainPath(tree: *const Ast, t: Ast.TokenIndex, last: Ast.TokenIndex) []const u8 {
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
        const start_byte = tree.tokens.items(.start)[first_field];
        const last_start = tree.tokens.items(.start)[last_field];
        const last_len = tree.tokenSlice(last_field).len;
        return tree.source[start_byte..(last_start + last_len)];
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
    /// Walks lastToken's start + slice length.  Used together with
    /// posOf to give diagnostics a real span the editor can highlight.
    fn endPosOf(self: *Builder, node: Ast.Node.Index) SrcPos {
        const tree = self.tree;
        const last = tree.lastToken(node);
        const start = tree.tokens.items(.start)[last];
        const slice = tree.tokenSlice(last);
        const end_byte: u32 = @intCast(start + slice.len);
        const lc = byteToLineCol(self.line_offsets, start);
        return .{
            .byte = end_byte,
            .line = lc.line + 1,
            .column = lc.col + 1 + @as(u32, @intCast(slice.len)),
        };
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
    fn posOfTokenEnd(self: *Builder, tok: Ast.TokenIndex) SrcPos {
        const tree = self.tree;
        const start = tree.tokens.items(.start)[tok];
        const slice = tree.tokenSlice(tok);
        const end_byte: u32 = @intCast(start + slice.len);
        const lc = byteToLineCol(self.line_offsets, start);
        return .{
            .byte = end_byte,
            .line = lc.line + 1,
            .column = lc.col + 1 + @as(u32, @intCast(slice.len)),
        };
    }

    fn finalize(
        self: *Builder,
        tree: *const Ast,
        fn_decl: Ast.Node.Index,
        entry: BlockId,
    ) !Cfg {
        const blocks = try self.gpa.alloc(BasicBlock, self.blocks.items.len);
        for (self.blocks.items, 0..) |bb, i| {
            const stmts = try self.block_stmts.items[i].toOwnedSlice(self.gpa);
            errdefer self.gpa.free(stmts);
            const successors = try self.block_successors.items[i].toOwnedSlice(self.gpa);
            blocks[i] = .{ .id = bb.id, .stmts = stmts, .successors = successors };
        }
        const locals = try self.locals.toOwnedSlice(self.gpa);
        const owned_paths = try self.owned_paths.toOwnedSlice(self.gpa);
        const start = tree.tokens.items(.start)[tree.firstToken(fn_decl)];
        const end_tok = tree.lastToken(fn_decl);
        const end = tree.tokens.items(.start)[end_tok] + tree.tokenSlice(end_tok).len;
        return .{
            .blocks = blocks,
            .entry = entry,
            .fn_span = .{ .start = start, .end = @intCast(end) },
            .locals = locals,
            .owned_paths = owned_paths,
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
