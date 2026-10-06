//! Borrowed-slice-into-out-param detector — `defer <X>.deinit()`
//! (or `defer alloc.free(<X>)`) registers cleanup for a local
//! buffer / arena, and a later write `<out>.* = ...<X>...` (or
//! `<out>.field = ...<X>...`) pushes a view of `<X>` into a
//! caller-visible out-parameter.  When the defer fires on
//! function return, the out-param holds a dangling slice.
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
const local_bindings = @import("../../model/local_bindings.zig");
const query = @import("../../ast/token_query.zig");
const file_model = @import("../../model/file_model.zig");
const problem_mod = @import("../../problem.zig");
const testing = @import("../../testing.zig");
const config_mod = @import("../../config.zig");
const file_cache_mod = @import("../../cache/file_cache.zig");
const fn_summary_mod = @import("../../model/fn_summary.zig");

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
        try checkFn(gpa, tree, cache, fn_entry.node, fn_entry.proto, fn_entry.body, problems);
    }
}

fn checkFn(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    fn_decl: Ast.Node.Index,
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

    // Pointer params — bindings with .param origin whose declared
    // type starts with `*` or `?*`.  We also record each pointer
    // param's CONTAINER TYPE NAME (e.g. "PackageInstall" for
    // `this: *PackageInstall`) so writes through it can be
    // type-checked against the file model — a write to a primitive
    // field (`this.file_count: usize = ...`) can't carry a borrowed
    // slice and must not fire.
    const model = try cache.fileModel();
    // Containing type for `*@This()` / `*Self` resolution.
    const self_type: ?[]const u8 = if (model.containingTypeOf(fn_decl)) |ti| ti.qualified_name else null;

    var pointer_params: std.ArrayListUnmanaged(PointerParam) = .empty;
    defer pointer_params.deinit(gpa);
    for (bindings.items) |b| {
        if (b.origin != .param) continue;
        if (!isPointerType(tags, b.rhs_first, b.rhs_last)) continue;
        try pointer_params.append(gpa, .{
            .name = b.name,
            .type_name = extractTypeName(tree, model, b.rhs_first, b.rhs_last, self_type),
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
            if (bindings.find(name) != null) {
                const range = enclosingScope(tags, t, first, last);
                try deferred.append(gpa, .{
                    .name = name,
                    .scope_open = range.open,
                    .scope_close = range.close,
                });
            }
            t = m.end + 1;
            continue;
        }
        if (query.matchAt(tree, defer_free, t, last, null)) |m| {
            const range = enclosingScope(tags, t, first, last);
            try deferred.append(gpa, .{
                .name = m.captureText(tree, 0).?,
                .scope_open = range.open,
                .scope_close = range.close,
            });
            t = m.end + 1;
            continue;
        }
        t += 1;
    }
    if (deferred.items.len == 0) return;

    // Find writes through pointer params; check RHS for any deferred name.
    try scanWrites(gpa, tree, cache, write_via_out, first, last, pointer_params.items, deferred.items, problems);
}

fn scanWrites(
    gpa: std.mem.Allocator,
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
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
    for (writes) |w| {
        const out_name = w.captureText(tree, 0).?;
        const pp = findPointerParam(out_name, pointer_params) orelse continue;
        // Type-aware LHS check: when the write is `<out>.<field> = ...`
        // and we can resolve <field>'s declared type via the FileModel,
        // skip primitive-typed fields (`usize` / `u32` / `bool` /
        // etc.) — those can't hold a borrowed slice.  The audit
        // showed many FPs of the form `this.file_count =
        // FileCopier.copy(subdir, ...);` where the RHS just mentions
        // a deferred name as a CALL ARG (the call returns a primitive).
        if (w.start + 2 <= last and tags[w.start + 1] == .period and tags[w.start + 2] == .identifier) {
            const field_name = tree.tokenSlice(w.start + 2);
            if (pp.type_name) |ty| {
                if (cache.findTypeAcrossImports(ty)) |owner| {
                    if (owner.model.fieldType(owner.info.qualified_name, field_name)) |name| {
                        if (isPrimitiveTypeName(name)) continue;
                    }
                    if (cache.fieldType(owner, field_name)) |leaf| {
                        if (leaf.info.kind == .enum_) continue;
                        if (leaf.info.kind == .struct_ and structOnlyHoldsPrimitivesOrPointers(leaf.model.tree, leaf.info)) continue;
                    }
                }
            }
        }
        // RHS-shape check: when the assigned value comes from a
        // `*.toOwnedSlice(*)` / `*.dupe(*)` / `*.clone(*)` call, the
        // value is OWNED (newly-allocated by the call's allocator
        // arg), not a borrow of the deferred local.  The deferred
        // cleanup happens AFTER the copy is made; out-param holds
        // a valid allocation.
        const sc = tokens.findStmtSemicolon(tags, w.end + 1, last) orelse continue;
        if (sc <= w.end + 1) continue;
        if (rhsContainsCopyingCall(tree, w.end + 1, sc - 1)) continue;
        // RHS ending in `].*` — array dereference produces a
        // by-value array copy.  Common pattern:
        //   `.salt = salt_data.slice()[0..4].*`
        // After the copy the field holds independent bytes; the
        // deferred local's storage going away doesn't dangle it.
        if (rhsEndsWithArrayDeref(tree, w.end + 1, sc - 1)) continue;
        // RHS contains `<X>.create(... allocator ... <slice> ...)`
        // — the call is an allocator-backed constructor that
        // canonically dupes its non-allocator args (Bun's
        // `Type.create(global, allocator, ..., slice)` pattern,
        // body does `allocator.dupe(u8, slice)`).  The out-param
        // receives the new owned copy, not a borrow.
        if (rhsContainsAllocatorConstructor(tree, w.end + 1, sc - 1)) continue;
        // Cross-fn dupe inference: if the RHS is a single same-file
        // fn call whose body's returns NEVER mention any of its
        // params, the result can't carry a borrow back from any
        // arg.  Resolves the `this.x = makePlaceholder(decoded.rgba,
        // decoded.width, decoded.height)` shape where makePlaceholder
        // builds a new heap allocation and returns it independently
        // of its args.
        if (rhsCallIsResultIndependent(tree, cache, w.end + 1, sc - 1)) continue;
        const dn = rhsMentionsDeferred(tree, w.end + 1, sc - 1, deferred) orelse continue;
        // Switch-scrutinee-only skip: when the RHS is
        // `switch (<expr-mentioning-deferred>) { <arms-not-mentioning-it> }`,
        // the deferred slice is consumed by the expression that the
        // switch is BRANCHING on; the arms build the result from the
        // unpacked union payloads, not from the slice.  Common shape
        // around connect/dispatch APIs:
        //   `this.socket = switch (group.connect(..., hostz, ...)) {
        //        .failed => return error..., .socket => |s| ..., }`
        // Net effect: the deferred slice is transient (lives only
        // through the call), and the out-param holds independent
        // bytes (the unpacked Socket).
        if (deferredOnlyInSwitchScrutinee(tree, w.end + 1, sc - 1, dn)) continue;
        // Per-arg suppression: the deferred variable appears in the
        // RHS as an argument to some call, but the called function
        // provably doesn't embed THAT SPECIFIC param in its returns
        // (even if it embeds other params).  Handles the shape:
        //   `ret.* = ok(transpileSourceCode(..., referrer_slice.slice(), ...))`
        // where `input_specifier` (a different param) appears in
        // transpileSourceCode's returns but `referrer` (param at the
        // deferred-arg position) does not.
        if (rhsCallArgNotEmbeddedInResult(tree, cache, w.end + 1, sc - 1, dn)) continue;
        try report(gpa, problems, tree, w.start, out_name, dn);
    }
}

const PointerParam = struct { name: []const u8, type_name: ?[]const u8 };

/// A `defer X.deinit()` / `defer alloc.free(X)` paired with the
/// lexical `{ ... }` it was declared inside.  Writes outside that
/// scope cannot see the registered cleanup — the defer hasn't
/// executed when control passes a sibling branch.
const DeferredItem = struct {
    name: []const u8,
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


/// Preserve namespace qualification and the enclosing type's lexical scope.
fn extractTypeName(
    tree: *const Ast,
    model: *const file_model.FileModel,
    first: Ast.TokenIndex,
    last: Ast.TokenIndex,
    self_type: ?[]const u8,
) ?[]const u8 {
    const name = tokens.typeNameFromTokens(tree, first, last) orelse {
        if (last >= first + 2 and tree.tokenTag(last - 2) == .builtin and
            std.mem.eql(u8, tree.tokenSlice(last - 2), "@This")) return self_type;
        return null;
    };
    if (self_type) |scope_name| {
        if (std.mem.eql(u8, name, "Self")) return scope_name;
        if (model.findType(scope_name)) |scope| {
            if (model.resolveTypeNameInScope(name, scope)) |resolved| return resolved.qualified_name;
        }
    }
    return name;
}

fn isPrimitiveTypeName(name: []const u8) bool {
    // Zig primitives that can't hold a slice / borrow.  Slices and
    // pointers are excluded — those CAN hold borrowed memory.  Bool
    // and ints are sufficient to cover the common FP shape
    // (`this.count: usize = fn(deferred, ...)`).
    if (name.len == 0) return false;
    // Numeric types: bool, void, type, anyerror, anyopaque, comptime_*,
    // u<N>, i<N>, f<N>, c_*, usize, isize.
    if (std.mem.eql(u8, name, "bool")) return true;
    if (std.mem.eql(u8, name, "void")) return true;
    if (std.mem.eql(u8, name, "type")) return true;
    if (std.mem.eql(u8, name, "anyerror")) return true;
    if (std.mem.eql(u8, name, "anyopaque")) return true;
    if (std.mem.eql(u8, name, "usize")) return true;
    if (std.mem.eql(u8, name, "isize")) return true;
    if (std.mem.startsWith(u8, name, "comptime_")) return true;
    if (std.mem.startsWith(u8, name, "c_")) return true;
    // u<digits> / i<digits> / f<digits>.
    if ((name[0] == 'u' or name[0] == 'i' or name[0] == 'f') and name.len >= 2) {
        for (name[1..]) |c| if (c < '0' or c > '9') return false;
        return true;
    }
    // Bitset/packed-flag naming convention: protocol-parsing code
    // routinely declares packed-struct types named `*Flags`,
    // `*Status`, `*Mode`, `*Kind`, `*Capabilities`, `*Bits`,
    // `*Mask`.  These can be assumed to hold no slice/pointer
    // fields (they're bit-flag wrappers around an integer base
    // type), so a field of this shape can't carry a borrow.
    // Imported across files, the structural check can't see this —
    // the suffix is the next-best signal.
    if (std.mem.endsWith(u8, name, "Flags")) return true;
    if (std.mem.endsWith(u8, name, "Status")) return true;
    if (std.mem.endsWith(u8, name, "Mode")) return true;
    if (std.mem.endsWith(u8, name, "Kind")) return true;
    if (std.mem.endsWith(u8, name, "Capabilities")) return true;
    if (std.mem.endsWith(u8, name, "Bits")) return true;
    if (std.mem.endsWith(u8, name, "Mask")) return true;
    return false;
}

/// True iff `[start, end]` contains a `.<copy_method>(` shape where
/// `<copy_method>` is a known copying call (returns owned, doesn't
/// borrow from args).
/// Token-level check for an `].*` suffix anywhere in the RHS — an
/// array-value dereference.  When the assignment's value is the
/// result of `<slice>[N..M].*` (or `<arr>[N..M].*`), the LHS gets
/// a fresh stack-copied array, not a borrow into the slice's
/// allocation.  The local's `defer .deinit()` freeing the slice
/// doesn't dangle the copied bytes.
fn rhsEndsWithArrayDeref(tree: *const Ast, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    if (start + 1 > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 1 <= end) : (t += 1) {
        if (tags[t] != .r_bracket) continue;
        if (tags[t + 1] != .period_asterisk) continue;
        return true;
    }
    return false;
}

fn rhsContainsCopyingCall(tree: *const Ast, start: Ast.TokenIndex, end: Ast.TokenIndex) bool {
    const tags = tree.tokens.items(.tag);
    if (start + 2 > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        const m = tree.tokenSlice(t + 1);
        if (isCopyingMethodName(m)) return true;
        // Singleton-store .append pattern: `<X>.<...>.instance.append(`
        // — Bun's `FileSystem.DirnameStore.instance.append(T, slice)`
        // dupes the slice into the static store.  Recognising the
        // `.instance.append(` shape catches the canonical case
        // without broadening `.append` (which is also used by
        // ArrayList for non-duping appends).
        if (std.mem.eql(u8, m, "append") and t >= 2 and
            tags[t - 2] == .period and
            tags[t - 1] == .identifier and
            std.mem.eql(u8, tree.tokenSlice(t - 1), "instance")) return true;
    }
    return false;
}

/// True iff every field of `ti` is a primitive (`u32`/`bool`/etc.)
/// or a pointer (`*T` / `?*T`).  Such structs hold no slice fields
/// and can't carry a borrowed slice from a deferred local — the
/// out-param write through `<out>.<field> = <call>` where `<field>`
/// has this shape can't dangle into a deferred local.
fn structOnlyHoldsPrimitivesOrPointers(tree: *const Ast, ti: *const file_model.TypeInfo) bool {
    const tags = tree.tokens.items(.tag);
    if (ti.fields.len == 0) return false;
    for (ti.fields) |f| {
        // TypeInfo may have been built from a foreign tree — token indices
        // out of range for this tree means we can't inspect safely.
        if (f.type_first >= tags.len or f.type_last >= tags.len) return false;
        var t = f.type_first;
        while (t <= f.type_last and tags[t] == .question_mark) : (t += 1) {}
        if (t > f.type_last) return false;
        // Pointer field: `*T` / `?*T` — already past `?` strip.
        if (tags[t] == .asterisk) continue;
        // Slice or array: leak risk if contents are bytes.
        if (tags[t] == .l_bracket) return false;
        if (tags[t] != .identifier) return false;
        const name = tree.tokenSlice(t);
        if (!isPrimitiveTypeName(name)) return false;
    }
    return true;
}

fn isCopyingMethodName(name: []const u8) bool {
    return std.mem.eql(u8, name, "toOwnedSlice") or
        std.mem.eql(u8, name, "toOwnedSliceSentinel") or
        std.mem.eql(u8, name, "toOwned") or
        std.mem.eql(u8, name, "intoOwned") or
        std.mem.eql(u8, name, "dupe") or
        std.mem.eql(u8, name, "dupeZ") or
        std.mem.eql(u8, name, "clone") or
        std.mem.eql(u8, name, "cloneZ") or
        std.mem.eql(u8, name, "copyFrom") or
        std.mem.eql(u8, name, "copyForwards") or
        std.mem.eql(u8, name, "copyBackwards");
}

/// Find which 0-based argument index in a balanced call argument list
/// (`arg_start..arg_end`, i.e. tokens between `(` and `)` exclusive)
/// contains `deferred_name` as an unqualified identifier.  Commas at
/// depth 0 delimit arguments; nested parens/brackets/braces are
/// balanced.  Returns null when not found.
fn findDeferredArgIdx(
    tree: *const Ast,
    tags: []const std.zig.Token.Tag,
    arg_start: Ast.TokenIndex,
    arg_end: Ast.TokenIndex,
    deferred_name: []const u8,
) ?u32 {
    var arg_idx: u32 = 0;
    var depth: i32 = 0;
    var t: Ast.TokenIndex = arg_start;
    while (t <= arg_end) : (t += 1) {
        switch (tags[t]) {
            .l_paren, .l_bracket, .l_brace => depth += 1,
            .r_paren, .r_bracket, .r_brace => depth -= 1,
            .comma => if (depth == 0) {
                arg_idx += 1;
            },
            .identifier => if (depth == 0 and
                std.mem.eql(u8, tree.tokenSlice(t), deferred_name))
            {
                return arg_idx;
            },
            else => {},
        }
    }
    return null;
}

/// True iff the RHS at `[start, end]` is a call (or wrapper call)
/// where `deferred_name` is passed as an argument at a position whose
/// corresponding parameter is provably NOT embedded in any of the
/// called function's non-recursive return expressions.  Uses the
/// per-param `result_params_in_return` bitmask from FnSummary.
///
/// Handles the shape:
///   `ret.* = ok(transpileSourceCode(..., referrer_slice.slice(), ...))`
/// where `transpileSourceCode` stores `input_specifier` (a different
/// param) in its returns but NOT `referrer` — the deferred arg's param.
fn rhsCallArgNotEmbeddedInResult(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    deferred_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var t: Ast.TokenIndex = start;
    if (t <= end and tags[t] == .keyword_try) t += 1;
    if (t + 2 > end) return false;
    var p: Ast.TokenIndex = t;
    var last_ident: ?Ast.TokenIndex = null;
    while (p <= end) : (p += 1) {
        switch (tags[p]) {
            .identifier => last_ident = p,
            .period, .builtin => {},
            .l_paren => break,
            else => return false,
        }
    }
    if (p > end or tags[p] != .l_paren) return false;
    const name_tok = last_ident orelse return false;
    const fn_name = tree.tokenSlice(name_tok);
    // Wrapper passthrough: `ok(inner_call)` — recurse into the arg.
    if (isWrapperCtorName(fn_name)) {
        const arg_start = p + 1;
        const arg_end = matchParenEnd(tags, p, end) orelse return false;
        return rhsCallArgNotEmbeddedInResult(tree, cache, arg_start, arg_end - 1, deferred_name);
    }
    // Look up the called function's summary.
    const model = cache.fileModel() catch return false;
    const fn_decl = findFnDeclByName(model, fn_name) orelse return false;
    const summary = cache.summaryOfFn(fn_decl) catch return false;
    const mask = summary.result_params_in_return;
    // If no return statements were seen, we can't confirm independence.
    if ((mask & fn_summary_mod.SAW_RETURN_BIT) == 0) return false;
    // Find which arg position contains deferred_name.
    const paren_end = matchParenEnd(tags, p, end) orelse return false;
    const arg_idx = findDeferredArgIdx(tree, tags, p + 1, paren_end - 1, deferred_name) orelse return false;
    if (arg_idx >= 31) return false;
    // True when the specific param's bit is clear (not in any return).
    return (mask >> @intCast(arg_idx)) & 1 == 0;
}

/// True iff the RHS contains a `<X>.create(...)` or `<X>.init(...)`
/// or `<X>.new(...)` call whose args include an allocator token —
/// strong heuristic that the constructor dupes its non-allocator
/// args via that allocator (canonical Bun pattern:
/// `ResolveMessage.create(global, allocator, msg, slice)` does
/// `allocator.dupe(u8, slice)` internally).  Cross-fn dupe
/// inference without an actual cross-fn lookup: the presence of
/// an allocator in the call shape is the signal.
/// Cross-fn dupe inference: the RHS is a single call `<X>(args...)`
/// (optionally wrapped in `try`/`catch`); look up the fn by name in
/// the file model, check its FnSummary's
/// `result_independent_of_args`.  Returns true when the call's
/// result demonstrably can't carry a borrow from any arg.
///
/// Conservative — only fires when the RHS shape is a SINGLE call
/// expression (not a chain or struct-init wrapper) AND the called
/// fn is in the local model.  Cross-file calls are unhandled
/// (would need a project-wide model).
fn rhsCallIsResultIndependent(
    tree: *const Ast,
    cache: *file_cache_mod.FileCache,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    // Peel optional leading `try`.
    var t: Ast.TokenIndex = start;
    if (t <= end and tags[t] == .keyword_try) t += 1;
    if (t + 2 > end) return false;
    // RHS shape: [`<recv>`,`.`]* `<id>` `(` ... `)` [`catch` ...].
    // Walk to the FIRST `(` collecting the immediately-preceding
    // identifier as the method/fn name.
    var p: Ast.TokenIndex = t;
    var last_ident: ?Ast.TokenIndex = null;
    while (p <= end) : (p += 1) {
        switch (tags[p]) {
            .identifier => last_ident = p,
            .period, .builtin => {},
            .l_paren => break,
            else => return false,
        }
    }
    if (p > end or tags[p] != .l_paren) return false;
    const name_tok = last_ident orelse return false;
    const fn_name = tree.tokenSlice(name_tok);
    const model = cache.fileModel() catch return false;
    // Direct hit: the outer call is itself result-independent.
    if (findFnDeclByName(model, fn_name)) |fn_decl| {
        const summary = cache.summaryOfFn(fn_decl) catch return false;
        if (summary.result_independent_of_args) return true;
    }
    // Wrapper passthrough: outer call is a wrapper constructor
    // (`Errorable.ok(...)`, `Result.ok(...)`, `Maybe.success(...)`)
    // — recurse into the FIRST arg, which is the wrapped value.
    // If the inner call's result is independent of its args, the
    // wrapped value's borrow lifetime is the inner call's, not the
    // outer wrapper's.
    if (isWrapperCtorName(fn_name)) {
        const arg_start = p + 1;
        const arg_end = matchParenEnd(tags, p, end) orelse return false;
        return rhsCallIsResultIndependent(tree, cache, arg_start, arg_end - 1);
    }
    return false;
}

/// True iff the call name is a known wrapper constructor that
/// boxes its first arg into an Ok/Success variant without
/// changing the borrow lifetime.  Recursing through wrappers lets
/// us inspect the underlying call.
fn isWrapperCtorName(name: []const u8) bool {
    return std.mem.eql(u8, name, "ok") or
        std.mem.eql(u8, name, "Ok") or
        std.mem.eql(u8, name, "success") or
        std.mem.eql(u8, name, "Success") or
        std.mem.eql(u8, name, "result");
}

/// True iff the RHS at `[start..end]` is a `switch (...) { ... }`
/// expression whose `<deferred_name>` mentions appear ONLY inside
/// the switch's scrutinee `(...)` — i.e., never inside the arms
/// block `{ ... }`.  When the deferred slice is consumed by the
/// expression the switch branches on, and the arms build the
/// result from unpacked union payloads (not from the slice), the
/// slice is transient and can't reach the out-param.
fn deferredOnlyInSwitchScrutinee(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    deferred_name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    // Peel optional leading `try`.
    var t: Ast.TokenIndex = start;
    if (t <= end and tags[t] == .keyword_try) t += 1;
    if (t > end or tags[t] != .keyword_switch) return false;
    // Scrutinee starts at the next `(`.
    var p = t + 1;
    while (p <= end and tags[p] != .l_paren) : (p += 1) {}
    if (p > end or tags[p] != .l_paren) return false;
    const scrut_end = matchParenEnd(tags, p, end) orelse return false;
    if (scrut_end + 1 > end or tags[scrut_end + 1] != .l_brace) return false;
    const arms_open: Ast.TokenIndex = scrut_end + 1;
    const arms_close = matchBraceEnd(tags, arms_open, end) orelse return false;
    // Walk RHS; ensure all deferred-name mentions land in
    // (p, scrut_end) and NONE land in (arms_open, arms_close].
    var saw_in_scrut = false;
    var k: Ast.TokenIndex = start;
    while (k <= end) : (k += 1) {
        if (tags[k] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(k), deferred_name)) continue;
        if (k > p and k < scrut_end) {
            saw_in_scrut = true;
        } else if (k > arms_open and k <= arms_close) {
            // Mention in the arm block — slice CAN reach the result.
            return false;
        } else {
            // Mention outside both — unexpected shape, bail.
            return false;
        }
    }
    return saw_in_scrut;
}

const matchBraceEnd = tokens.matchBrace;
const matchParenEnd = tokens.matchParen;

/// Find a fn_decl AST node by name — top-level OR a method of
/// any type.  Conservative: returns null on the FIRST match;
/// multiple methods with the same name across types collapse to
/// the first.  Acceptable because the borrowed-slice analysis
/// is opportunistic (false-negative is fine).
fn findFnDeclByName(model: *const file_model.FileModel, name: []const u8) ?Ast.Node.Index {
    for (model.fns) |f| {
        if (std.mem.eql(u8, f.name, name)) return f.fn_decl;
    }
    for (model.types) |ti| {
        for (ti.methods) |m| {
            if (std.mem.eql(u8, m.name, name)) return m.fn_decl;
        }
    }
    return null;
}

fn rhsContainsAllocatorConstructor(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
) bool {
    const tags = tree.tokens.items(.tag);
    if (start + 2 > end) return false;
    var t: Ast.TokenIndex = start;
    while (t + 2 <= end) : (t += 1) {
        if (tags[t] != .period) continue;
        if (tags[t + 1] != .identifier) continue;
        if (tags[t + 2] != .l_paren) continue;
        const m = tree.tokenSlice(t + 1);
        const is_ctor = std.mem.eql(u8, m, "create") or
            std.mem.eql(u8, m, "init") or
            std.mem.eql(u8, m, "new") or
            std.mem.eql(u8, m, "from") or
            std.mem.eql(u8, m, "fromJS") or
            std.mem.eql(u8, m, "fromUTF8") or
            std.mem.eql(u8, m, "make");
        if (!is_ctor) continue;
        // Walk arg tokens balanced to the matching `)`, checking
        // for an allocator name.
        var depth: u32 = 1;
        var u: Ast.TokenIndex = t + 3;
        while (u <= end and depth > 0) : (u += 1) {
            switch (tags[u]) {
                .l_paren => depth += 1,
                .r_paren => {
                    depth -= 1;
                    if (depth == 0) break;
                },
                .identifier => {
                    const id = tree.tokenSlice(u);
                    if (std.mem.eql(u8, id, "allocator") or
                        std.mem.eql(u8, id, "alloc") or
                        std.mem.eql(u8, id, "gpa") or
                        std.mem.endsWith(u8, id, "_allocator") or
                        std.mem.endsWith(u8, id, "Allocator"))
                        return true;
                },
                else => {},
            }
        }
    }
    return false;
}

/// True iff the type expression at `[first, last]` starts with `*`
/// or `?*` — the conservative "this looks like an out-pointer param" check.
fn isPointerType(tags: []const std.zig.Token.Tag, first: Ast.TokenIndex, last: Ast.TokenIndex) bool {
    if (first > last) return false;
    var t: Ast.TokenIndex = first;
    if (tags[t] == .question_mark) {
        if (t + 1 > last) return false;
        t += 1;
    }
    return tags[t] == .asterisk;
}

fn isDeinitOrClose(name: []const u8) bool {
    return std.mem.eql(u8, name, "deinit") or std.mem.eql(u8, name, "close");
}

/// True iff `[start, end]` mentions one of the deferred names as
/// a VALUE — i.e. NOT preceded by `&` (by-reference pass).
/// Returns the matched name on hit.
///
/// Rationale: `out.* = ZigString.init(arena)` passes `arena` by
/// value; ZigString stores a borrow into arena's memory.  But
/// `this.scripts = createList(buf, &top_level_dir, ...)` passes
/// `&top_level_dir` by reference; createList typically reads from
/// the pointer transiently rather than retaining it.  Skipping
/// `&deferred` references trades a few FNs for many fewer FPs.
fn rhsMentionsDeferred(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    deferred: []const DeferredItem,
) ?[]const u8 {
    const tags = tree.tokens.items(.tag);
    if (start > end) return null;
    var t: Ast.TokenIndex = start;
    while (t <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        // Skip `&deferred` — by-reference pass; the fn doesn't
        // necessarily retain the borrow.
        if (t > 0 and tags[t - 1] == .ampersand) continue;
        // Skip `<recv>.<deferred>` — a field/method named the
        // same as a deferred local isn't the local itself.
        // Without this, `ctx.body` matches a `body` local on the
        // post-`.` identifier.
        if (t > 0 and tags[t - 1] == .period) continue;
        const name = tree.tokenSlice(t);
        for (deferred) |d| {
            if (!std.mem.eql(u8, d.name, name)) continue;
            // A defer in a sibling branch (or any block that doesn't
            // contain the write) hasn't executed when the write
            // runs — it can't have registered cleanup.  Only count
            // defers whose enclosing scope encloses this write.
            if (t < d.scope_open or t > d.scope_close) continue;
            // Scalar-field-access skip: `<deferred>.<scalar-field>`
            // where the field is well-known to be scalar (width,
            // height, len, count, etc.).  The borrow is into the
            // scalar value, not into `<deferred>`'s allocation —
            // the field's bytes already sit in the local's stack
            // frame copy when accessed.  Conservative: only skip
            // if the FIRST occurrence after `<deferred>` is a
            // scalar-named field AND there are no other (more
            // suspicious) mentions of `<deferred>` in the RHS.
            if (allDeferredMentionsAreScalarFields(tree, start, end, d.name)) continue;
            return d.name;
        }
    }
    return null;
}

/// True iff every occurrence of `name` in `[start, end]` is
/// `<name>.<scalar-field>` form — the deferred local is only
/// accessed for primitive-named fields, never as the whole value
/// or via slice-bearing fields.  When this holds, no slice borrow
/// is taken from the deferred.
fn allDeferredMentionsAreScalarFields(
    tree: *const Ast,
    start: Ast.TokenIndex,
    end: Ast.TokenIndex,
    name: []const u8,
) bool {
    const tags = tree.tokens.items(.tag);
    var any_mention = false;
    var t: Ast.TokenIndex = start;
    while (t <= end) : (t += 1) {
        if (tags[t] != .identifier) continue;
        if (t > 0 and tags[t - 1] == .ampersand) continue;
        if (t > 0 and tags[t - 1] == .period) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(t), name)) continue;
        any_mention = true;
        // Must be followed by `.<field>` where `<field>` is scalar.
        if (t + 2 > end) return false;
        if (tags[t + 1] != .period) return false;
        if (tags[t + 2] != .identifier) return false;
        if (!isScalarFieldName(tree.tokenSlice(t + 2))) return false;
    }
    return any_mention;
}

fn isScalarFieldName(name: []const u8) bool {
    const known = [_][]const u8{
        "width",   "height", "depth",    "len",      "size",
        "count",   "cap",    "capacity", "num",      "n",
        "w",       "h",      "x",        "y",        "z",
        "x1",      "y1",     "x2",       "y2",       "rows",
        "cols",    "fd",     "tag",      "kind",     "id",
        "version", "flags",  "level",    "priority",
    };
    for (known) |k| {
        if (std.mem.eql(u8, k, name)) return true;
    }
    // Suffix shapes.
    if (std.mem.endsWith(u8, name, "_len") or
        std.mem.endsWith(u8, name, "_count") or
        std.mem.endsWith(u8, name, "_size") or
        std.mem.endsWith(u8, name, "_bytes") or
        std.mem.endsWith(u8, name, "_ms") or
        std.mem.endsWith(u8, name, "_ns") or
        std.mem.endsWith(u8, name, "_id")) return true;
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
        .start = Pos.fromTokenStart(tree, write_tok),
        .end = Pos.fromTokenEnd(tree, write_tok),
        .message = msg,
    });
}

// ── Tests ──────────────────────────────────────────────────

test "defer arena.deinit + out-param write using arena fires" {
    try testing.expectFires(check, R,
        \\const std = @import("std");
        \\const ZigString = struct {
        \\    raw: u64 = 0,
        \\    // Returns a borrow of `s` — captures it into the
        \\    // result, so the result's lifetime is tied to `s`.
        \\    pub fn init(s: anytype) ZigString { return .{ .raw = s }; }
        \\};
        \\pub fn parse(out: *ZigString, gpa_alloc: std.mem.Allocator) !void {
        \\    var arena = std.heap.ArenaAllocator.init(gpa_alloc);
        \\    defer arena.deinit();
        \\    out.* = ZigString.init(arena);
        \\}
    );
}

test "defer alloc.free(X) + out-param write using X fires" {
    try testing.expectFires(check, R,
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
    // Param uses `*@This()` — extractTypeName must resolve to the
    // containing type so the FileModel lookup hits.
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
    // Mirrors bun's Bun__transpileFile / Bun__transpileVirtualModule:
    //   `referrer_slice` is passed as `referrer` to `transpileSourceCode`,
    //   but `transpileSourceCode` embeds `other` (a different param) in its
    //   returns, not `referrer`.  The old code misfired because
    //   `result_independent_of_args` was false (because `other` appeared in
    //   returns); the per-param bitmask now correctly distinguishes which
    //   specific arg is embedded.
    try testing.expectNoFire(check,
        \\const std = @import("std");
        \\const Result = struct { label: []const u8 };
        \\fn transpile(
        \\    referrer: []const u8,
        \\    other: []const u8,
        \\) Result {
        \\    // `other` appears in the return — makes function NOT
        \\    // result-independent overall — but `referrer` does NOT.
        \\    return Result{ .label = other };
        \\}
        \\pub fn caller(
        \\    alloc: std.mem.Allocator,
        \\    raw: []const u8,
        \\    other: []const u8,
        \\    ret: *Result,
        \\) void {
        \\    var slice = std.ArrayList(u8).init(alloc);
        \\    defer slice.deinit();
        \\    // slice.items is passed as `referrer` — which is NOT embedded
        \\    // in transpile's return (only `other` is).
        \\    ret.* = transpile(slice.items, other);
        \\}
    );
}

test "deferred arg IS the embedded param — fires" {
    // Sanity check: when the deferred arg maps to a param that IS
    // embedded in the called function's return, we must still fire.
    try testing.expectFires(check, R,
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
        \\) void {
        \\    var slice = std.ArrayList(u8).init(alloc);
        \\    defer slice.deinit();
        \\    // slice.items is passed as `referrer` — which IS embedded
        \\    // in transpile's return — so this must fire.
        \\    ret.* = transpile(slice.items, other);
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
